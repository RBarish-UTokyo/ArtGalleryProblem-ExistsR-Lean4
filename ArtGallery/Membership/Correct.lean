module

public import ArtGallery.Membership.Simple
public import ArtGallery.Membership.Guards
public import ArtGallery.Vis.API

/-!
# The reduction from AGP to ETR (paper §3, Theorem 13)

`agpToETR w` decodes `w` into a vertex list `V` (with `n` vertices) and a number of guards `g`
(`decodeAGP`); if decoding fails or a denominator is `0`, it outputs `1 < 0`.  Otherwise its
variables are laid out as follows:

* `x_{2k}, x_{2k+1}` (`k < n`): the coordinates of vertex `k`, fixed by the equations
  `xDen · x_{2k} = xNum`, `yDen · x_{2k+1} = yNum` (`coordF`; the integers are written by
  Horner's rule from their binary digits);
* `simpleF n (2n)`: the polygon is simple (`3n²` separating-line variables);
* if `n ≤ g + 2`, nothing else: a simple polygon has a guard set of cardinality `n - 2`, hence of
  every larger cardinality;
* otherwise `guardsF n g (2n + 3n²)`: `g` guards that see all witness points (centroids of
  triples of vertices of the arrangement of edge lines and guard–vertex lines).

The main theorem is `agpToETR_correct : AGP w ↔ (agpToETR w).Satisfiable`.  The construction is
built from lists (`List.range`, `map`, `flatMap`, `foldr`), natural-number arithmetic and `if`;
with `m = n + g n`, it has `O(m⁶ · g · n³)` atomic formulas (each of constant size, apart from the
`O(n)` coordinate equations of size linear in the bit length of the input).
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR Complexity

/-! ## The formula -/

/-- The coordinate equations of the vertices `V`, starting with vertex number `k`:
`xDen · x_{2k} = xNum` and `yDen · x_{2k+1} = yNum`. -/
def coordF : List FracPoint → ℕ → Formula
  | [], _ => fTrue
  | p :: V, k =>
    .and (.and (.eq (.mul (natTerm p.xDen) (.var (2 * k))) (intTerm p.xNum))
        (.eq (.mul (natTerm p.yDen) (.var (2 * k + 1))) (intTerm p.yNum)))
      (coordF V (k + 1))

/-- All denominators are positive (a computable test). -/
def validB (V : List FracPoint) : Bool :=
  V.all fun p => decide (0 < p.xDen) && decide (0 < p.yDen)

/-- The formula of a decoded instance `(V, g)`. -/
def agpFormula (V : List FracPoint) (g : ℕ) : Formula :=
  if validB V then
    if V.length ≤ g + 2 then .and (coordF V 0) (simpleF V.length (2 * V.length))
    else .and (coordF V 0) (.and (simpleF V.length (2 * V.length))
      (guardsF V.length g (2 * V.length + simpleSize V.length)))
  else fFalse

/-- **The reduction from the art gallery problem to ETR.** -/
def agpToETR (w : Word) : Formula :=
  match decodeAGP w with
  | none => fFalse
  | some (V, g) => agpFormula V g

/-! ## Coordinates -/

theorem validB_iff (V : List FracPoint) : validB V = true ↔ ∀ p ∈ V, p.Valid := by
  simp [validB, FracPoint.Valid]

theorem holds_coordF_cons {x : ℕ → ℝ} {p : FracPoint} (hp : p.Valid) (k : ℕ) :
    (Formula.and (.eq (.mul (natTerm p.xDen) (.var (2 * k))) (intTerm p.xNum))
        (.eq (.mul (natTerm p.yDen) (.var (2 * k + 1))) (intTerm p.yNum))).Holds x ↔
      (x (2 * k), x (2 * k + 1)) = p.toPoint := by
  have hx0 : (p.xDen : ℝ) ≠ 0 := by have := hp.1; positivity
  have hy0 : (p.yDen : ℝ) ≠ 0 := by have := hp.2; positivity
  simp only [holds_and, holds_eq, eval_mul, eval_natTerm, eval_var, eval_intTerm,
    FracPoint.toPoint, Prod.ext_iff]
  rw [eq_div_iff hx0, eq_div_iff hy0, mul_comm (x (2 * k)), mul_comm (x (2 * k + 1))]

theorem holds_coordF {x : ℕ → ℝ} : ∀ (V : List FracPoint) (k : ℕ), (∀ p ∈ V, p.Valid) →
    ((coordF V k).Holds x ↔ ∀ i < V.length,
      (x (2 * (k + i)), x (2 * (k + i) + 1)) = (V.map FracPoint.toPoint).getD i (0, 0))
  | [], k, _ => by simp [coordF]
  | p :: V, k, hV => by
    have hp := hV p (by simp)
    have ih := holds_coordF (x := x) V (k + 1) (fun q hq => hV q (by simp [hq]))
    rw [coordF, holds_and, holds_coordF_cons hp, ih]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h i (by simpa using hi)
        rw [show k + 1 + i = k + (i + 1) by omega] at this
        simpa using this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      rw [show k + (i + 1) = k + 1 + i by omega] at this
      simpa using this

/-- The polygon of a vertex list. -/
noncomputable def polyOf (V : List FracPoint) : Polygon := Polygon.mk (V.map FracPoint.toPoint)

theorem polyOf_n (V : List FracPoint) : (polyOf V).n = V.length := by
  simp [polyOf, Polygon.n]

theorem holds_coordF_iff {x : ℕ → ℝ} {V : List FracPoint} (hV : ∀ p ∈ V, p.Valid) :
    (coordF V 0).Holds x ↔ VtxOK (polyOf V) x := by
  rw [holds_coordF V 0 hV, VtxOK, polyOf_n]
  simp only [Nat.zero_add, vt, pvar_eval]
  rfl

/-! ## Correctness -/

theorem agpFormula_complete {V : List FracPoint} {g : ℕ} (hV : ∀ p ∈ V, p.Valid)
    (hS : (polyOf V).Simple) (hG : (polyOf V).HasGuardSetOfCard g) :
    (agpFormula V g).Satisfiable := by
  set P := polyOf V with hP
  have hn : P.n = V.length := polyOf_n V
  let x0 : ℕ → ℝ := fun v => if v % 2 = 0 then (P.vtx (v / 2)).1 else (P.vtx (v / 2)).2
  have hx0 : VtxOK P x0 := by
    intro k hk
    have e1 : 2 * k % 2 = 0 := by omega
    have e2 : ¬ (2 * k + 1) % 2 = 0 := by omega
    have e3 : 2 * k / 2 = k := by omega
    have e4 : (2 * k + 1) / 2 = k := by omega
    simp only [vt, pvar_eval, x0, e1, e2, e3, e4, ite_true, ite_false]
  have hcoord : ∀ y : ℕ → ℝ, VtxOK P y → (coordF V 0).Holds y := fun y hy =>
    (holds_coordF_iff hV).2 hy
  obtain ⟨x1, hx1a, hx1⟩ := exists_simple_holds hS hx0 (base := 2 * P.n) le_rfl
  have hx1v : VtxOK P x1 := hx0.congr fun v hv => hx1a v hv
  unfold agpFormula
  rw [ite_eq_left ((validB_iff V).2 hV)]
  rw [hn] at hx1
  split_ifs with hng
  · exact ⟨x1, hcoord x1 hx1v, hx1⟩
  · obtain ⟨x2, hx2a, hx2⟩ := exists_guards_holds hS hx1v (g := g)
      (base := 2 * P.n + simpleSize P.n) (by omega) hG
    have hx2v : VtxOK P x2 := hx1v.congr fun v hv => hx2a v (by omega)
    refine ⟨x2, hcoord x2 hx2v, ?_, ?_⟩
    · have hF : FVars (· < 2 * V.length + simpleSize V.length) (simpleF V.length (2 * V.length)) :=
        FVars_simpleF (vtxVars_lt (by omega)) (fun v _ h2 => h2)
      rw [hn] at hx2a
      exact (holds_congr_lt hx2a hF).2 hx1
    · rw [hn] at hx2
      exact hx2

theorem agpFormula_sound {V : List FracPoint} {g : ℕ} (h : (agpFormula V g).Satisfiable) :
    (∀ p ∈ V, p.Valid) ∧ (polyOf V).Simple ∧ (polyOf V).HasGuardSetOfCard g := by
  obtain ⟨x, hx⟩ := h
  unfold agpFormula at hx
  by_cases hv : validB V = true
  · rw [ite_eq_left hv] at hx
    have hV := (validB_iff V).1 hv
    have hn : (polyOf V).n = V.length := polyOf_n V
    split_ifs at hx with hng
    · obtain ⟨hc, hs⟩ := hx
      have hxv := (holds_coordF_iff hV).1 hc
      rw [← hn] at hs
      have hS := simple_of_holds hxv hs
      refine ⟨hV, hS, ?_⟩
      exact (Polygon.hasGuardSetOfCard_n_sub_two hS).mono hS (by omega)
    · obtain ⟨hc, hs, hgd⟩ := hx
      have hxv := (holds_coordF_iff hV).1 hc
      rw [← hn] at hs hgd
      have hS := simple_of_holds hxv hs
      refine ⟨hV, hS, ?_⟩
      obtain ⟨hΓ, hsees⟩ := guards_of_holds hS hxv hgd
      set Γ := guardList x g (2 * (polyOf V).n + simpleSize (polyOf V).n)
      have hcard : Γ.toFinset.card ≤ g := by
        have := List.toFinset_card_le Γ
        simpa [Γ, guardList] using this
      have hGS : (polyOf V).IsGuardSet (Γ.toFinset : Set Point) := by
        refine ⟨fun γ hγ => hΓ γ (List.mem_toFinset.1 hγ), fun p hp => ?_⟩
        obtain ⟨γ, hγ, hs⟩ := hsees p hp
        exact ⟨γ, List.mem_toFinset.2 hγ, hs⟩
      exact Polygon.HasGuardSetOfCard.mono hS ⟨Γ.toFinset, rfl, hGS⟩ hcard
  · rw [ite_eq_right hv] at hx
    exact absurd hx (not_holds_fFalse x)

/-- **Correctness of the reduction** (paper, Theorem 13): an instance is a yes-instance of the
art gallery problem iff its formula is satisfiable. -/
theorem agpToETR_correct (w : Word) : AGP w ↔ (agpToETR w).Satisfiable := by
  rw [AGP_iff_decode]
  unfold agpToETR
  cases hd : decodeAGP w with
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, false_iff]
    rintro ⟨x, hx⟩
    exact not_holds_fFalse x hx
  | some r =>
    obtain ⟨V, g⟩ := r
    constructor
    · rintro ⟨V', g', h', hval, hS, hG⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact agpFormula_complete hval hS hG
    · intro h
      exact ⟨V, g, rfl, agpFormula_sound h⟩

end ArtGallery.Membership

end
