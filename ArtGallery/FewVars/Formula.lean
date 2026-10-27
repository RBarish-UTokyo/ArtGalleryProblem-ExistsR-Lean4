module

public import ArtGallery.FewVars.Simple
public import ArtGallery.FewVars.Guards
public import ArtGallery.PTime.AGPinER

/-!
# The reduction from AGP to ETR with only the guard coordinates as variables

For an instance with vertex digits `D` (`n` vertices) and `g` guards, the corners are the
rational points `cornerD d` (numerators and denominators written by Horner's rule) and

* `fvFormulaD D g` is `1 < 0` if a denominator is zero, the variable-free formula SIMPLE if
  `n ≤ g + 2` (a simple polygon has a guard set of cardinality `n - 2`), and SIMPLE ∧ GUARDS
  otherwise; its variables are `x₀, …, x_{2g-1}` (`FVars_fvFormulaD`);
* `fvToETR w` decodes `w` (`ArtGallery.decodeAGP`) and clamps `g` to `min g (n + 3)` (as in
  `agpToETRD`).

Main results: `fvFormulaD_satisfiable_iff`, `fvToETR_correct : AGP w ↔ (fvToETR w).Satisfiable`
and `fvToETR_encodeAGP_varsLt`.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry Complexity

/-! ## Corners -/

/-- The rational point of a vertex given by its digits. -/
def cornerD (d : FracDigits) : RPt :=
  ((intTermD d.1, bitsTerm d.2.1), (intTermD d.2.2.1, bitsTerm d.2.2.2))

/-- The corner list of an instance. -/
def cornersD (D : List FracDigits) : List RPt := D.map cornerD

theorem eval_intTermD_intDigits (x : ℕ → ℝ) (z : ℤ) :
    (intTermD (intDigits z)).eval x = (z : ℝ) := by
  rw [← intTerm_eq_intTermD, eval_intTerm]

theorem eval_bitsTerm_bits (x : ℕ → ℝ) (n : ℕ) : (bitsTerm n.bits).eval x = (n : ℝ) := by
  rw [eval_bitsTerm, ofBits_bits]

theorem prep_cornerD (x : ℕ → ℝ) {p : FracPoint} (hp : p.Valid) :
    PRep x (cornerD p.digits) p.toPoint := by
  have h1 : 0 < (bitsTerm p.xDen.bits).eval x := by
    rw [eval_bitsTerm_bits]; exact_mod_cast hp.1
  have h2 : 0 < (bitsTerm p.yDen.bits).eval x := by
    rw [eval_bitsTerm_bits]; exact_mod_cast hp.2
  refine ⟨(Rep.frac h1).congr ?_, (Rep.frac h2).congr ?_⟩
  · simp only [FracPoint.toPoint, FracPoint.digits, eval_intTermD_intDigits, eval_bitsTerm_bits]
  · simp only [FracPoint.toPoint, FracPoint.digits, eval_intTermD_intDigits, eval_bitsTerm_bits]

theorem cornersRep_of_valid (x : ℕ → ℝ) {V : List FracPoint} (hV : ∀ p ∈ V, p.Valid) :
    CornersRep x (polyOf V) (cornersD (V.map FracPoint.digits)) := by
  refine ⟨by simp [cornersD, polyOf_n], fun k hk => ?_⟩
  rw [polyOf_n] at hk
  have e1 : cr (cornersD (V.map FracPoint.digits)) k = cornerD V[k].digits := by
    simp [cr, cornersD, List.getD_eq_getElem?_getD, hk]
  have e2 : (polyOf V).vtx k = V[k].toPoint := by
    simp [polyOf, Polygon.vtx, List.getD_eq_getElem?_getD, hk]
  rw [e1, e2]
  exact prep_cornerD x (hV _ (List.getElem_mem hk))

theorem TVars_intTermD (S : ℕ → Prop) (p : Bool × Word) : TVars S (intTermD p) := by
  unfold intTermD
  split_ifs
  · exact ⟨trivial, TVars_bitsTerm S _⟩
  · exact TVars_bitsTerm S _

theorem cornersV_cornersD (S : ℕ → Prop) (D : List FracDigits) : CornersV S (cornersD D) := by
  intro k
  rw [cr, List.getD_eq_getElem?_getD]
  cases h : (cornersD D)[k]? with
  | none => exact PV.r0
  | some c =>
    have hc := List.mem_of_getElem? h
    obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
    exact ⟨⟨TVars_intTermD S _, TVars_bitsTerm S _⟩, ⟨TVars_intTermD S _, TVars_bitsTerm S _⟩⟩

/-! ## The formula -/

/-- **The formula of an instance** with vertex digits `D` and `g` guards. -/
def fvFormulaD (D : List FracDigits) (g : ℕ) : Formula :=
  if validBD D then
    if D.length ≤ g + 2 then rsimpleF (cornersD D)
    else .and (rsimpleF (cornersD D)) (rguardsF (cornersD D) g)
  else fFalse

/-- **The reduction from AGP to ETR with only guard variables.** -/
def fvToETR (w : Word) : Formula :=
  match ArtGallery.decodeAGP w with
  | none => fFalse
  | some (D, gd) => fvFormulaD D (min (SAT.binaryValue gd) (D.length + 3))

/-! ## Correctness -/

theorem fvFormulaD_complete {V : List FracPoint} {g : ℕ} (hV : ∀ p ∈ V, p.Valid)
    (hS : (polyOf V).Simple) (hG : (polyOf V).HasGuardSetOfCard g) :
    (fvFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable := by
  set P := polyOf V with hP
  have hn : P.n = V.length := polyOf_n V
  unfold fvFormulaD
  rw [ite_eq_left (by rw [← validB_eq_validBD]; exact (validB_iff V).2 hV), List.length_map]
  split_ifs with hng
  · exact ⟨fun _ => 0, (holds_rsimpleF (cornersRep_of_valid _ hV)).2 hS⟩
  · have hg : min g (V.length + 3) = g := by omega
    rw [hg]
    obtain ⟨G, hcard, hGsub, hGsees⟩ := hG
    have hlen : G.toList.length = g := by rw [Finset.length_toList, hcard]
    let γv : ℕ → Point := fun a => if h : a < G.toList.length then G.toList[a] else 0
    have hγG : ∀ a < g, γv a ∈ G := fun a ha => by
      have ha' : a < G.toList.length := by omega
      simp only [γv, dite_eq_left ha']
      exact Finset.mem_toList.1 (List.getElem_mem ha')
    let x : ℕ → ℝ := fun v => if v % 2 = 0 then (γv (v / 2)).1 else (γv (v / 2)).2
    have hx : ∀ a, guardPt x a = γv a := fun a => by
      have e1 : 2 * a % 2 = 0 := by omega
      have e2 : ¬ (2 * a + 1) % 2 = 0 := by omega
      have e3 : 2 * a / 2 = a := by omega
      have e4 : (2 * a + 1) / 2 = a := by omega
      simp only [guardPt, x, e1, e2, e3, e4, ite_true, ite_false]
    have hC := cornersRep_of_valid x hV
    refine ⟨x, (holds_rsimpleF hC).2 hS, holds_rguardsF_of_guards hS hC ?_ ?_⟩
    · intro a ha
      rw [hx]; exact hGsub (hγG a ha)
    · intro p hp
      obtain ⟨γ, hγ, hs⟩ := hGsees p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hγ)
      refine ⟨a, by omega, ?_⟩
      rw [hx]
      simp only [γv, dite_eq_left ha]
      exact hs

theorem fvFormulaD_sound {V : List FracPoint} {g : ℕ}
    (h : (fvFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable) :
    (∀ p ∈ V, p.Valid) ∧ (polyOf V).Simple ∧ (polyOf V).HasGuardSetOfCard g := by
  obtain ⟨x, hx⟩ := h
  unfold fvFormulaD at hx
  by_cases hv : validBD (V.map FracPoint.digits) = true
  · rw [ite_eq_left hv, List.length_map] at hx
    have hV : ∀ p ∈ V, p.Valid := (validB_iff V).1 (by rw [validB_eq_validBD]; exact hv)
    have hn : (polyOf V).n = V.length := polyOf_n V
    have hC := cornersRep_of_valid x hV
    split_ifs at hx with hng
    · have hS := (holds_rsimpleF hC).1 hx
      exact ⟨hV, hS, (Polygon.hasGuardSetOfCard_n_sub_two hS).mono hS (by omega)⟩
    · obtain ⟨hs, hgd⟩ := hx
      have hS := (holds_rsimpleF hC).1 hs
      have hg : min g (V.length + 3) = g := by omega
      rw [hg] at hgd
      refine ⟨hV, hS, ?_⟩
      obtain ⟨hΓ, hsees⟩ := guards_of_holds_rguardsF hS hC hgd
      set Γ := guardPts x g
      have hcard : Γ.toFinset.card ≤ g := by
        have := List.toFinset_card_le Γ
        simpa [Γ, guardPts] using this
      have hGS : (polyOf V).IsGuardSet (Γ.toFinset : Set Point) := by
        refine ⟨fun γ hγ => hΓ γ (List.mem_toFinset.1 hγ), fun p hp => ?_⟩
        obtain ⟨γ, hγ, hs⟩ := hsees p hp
        exact ⟨γ, List.mem_toFinset.2 hγ, hs⟩
      exact Polygon.HasGuardSetOfCard.mono hS ⟨Γ.toFinset, rfl, hGS⟩ hcard
  · rw [ite_eq_right hv] at hx
    exact absurd hx (not_holds_fFalse x)

theorem fvFormulaD_satisfiable_iff (V : List FracPoint) (g : ℕ) :
    (fvFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable ↔
      (∀ p ∈ V, p.Valid) ∧ (polyOf V).Simple ∧ (polyOf V).HasGuardSetOfCard g :=
  ⟨fvFormulaD_sound, fun ⟨hV, hS, hG⟩ => fvFormulaD_complete hV hS hG⟩

theorem fvToETR_encodeAGP (V : List FracPoint) (g : ℕ) :
    fvToETR (encodeAGP V g) = fvFormulaD (V.map FracPoint.digits) (min g (V.length + 3)) := by
  simp [fvToETR, ArtGallery.decodeAGP_encodeAGP, binaryValue_bits]

/-- **Correctness of the reduction.** -/
theorem fvToETR_correct (w : Word) : AGP w ↔ (fvToETR w).Satisfiable := by
  cases h : ArtGallery.decodeAGP w with
  | none =>
    have hfalse : fvToETR w = fFalse := by simp [fvToETR, h]
    rw [hfalse]
    constructor
    · rintro ⟨V, g, rfl, -⟩
      rw [ArtGallery.decodeAGP_encodeAGP] at h
      exact absurd h (by simp)
    · rintro ⟨x, hx⟩
      exact absurd hx (not_holds_fFalse x)
  | some r =>
    obtain ⟨D, gd⟩ := r
    obtain ⟨V, g, rfl, rfl, rfl⟩ := ArtGallery.decodeAGP_sound h
    rw [fvToETR_encodeAGP, fvFormulaD_satisfiable_iff]
    constructor
    · rintro ⟨V', g', h', hval, hS, hG⟩
      obtain ⟨rfl, rfl⟩ := encodeAGP_inj h'
      exact ⟨hval, hS, hG⟩
    · rintro ⟨hval, hS, hG⟩
      exact ⟨V, g, rfl, hval, hS, hG⟩

/-! ## Variables -/

theorem tvars_varsLt {N : ℕ} {t : Term} (h : TVars (· < N) t) : t.VarsLt N := by
  induction t with
  | var i => exact h
  | zero => trivial
  | one => trivial
  | add s t ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | sub s t ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | mul s t ihs iht => exact ⟨ihs h.1, iht h.2⟩

theorem fvars_varsLt {N : ℕ} {φ : Formula} (h : FVars (· < N) φ) : φ.VarsLt N := by
  induction φ with
  | eq s t => exact ⟨tvars_varsLt h.1, tvars_varsLt h.2⟩
  | lt s t => exact ⟨tvars_varsLt h.1, tvars_varsLt h.2⟩
  | le s t => exact ⟨tvars_varsLt h.1, tvars_varsLt h.2⟩
  | not φ ih => exact ih h
  | and φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩

/-- The variables of the formula are guard coordinates. -/
theorem FVars_fvFormulaD (D : List FracDigits) (g : ℕ) :
    FVars (· < 2 * g) (fvFormulaD D g) := by
  unfold fvFormulaD
  split_ifs
  · exact FVars_rsimpleF (cornersV_cornersD _ D)
  · exact ⟨FVars_rsimpleF (cornersV_cornersD _ D), FVars_rguardsF (cornersV_cornersD _ D)⟩
  · exact FVars_fFalse _

/-- **Only the guard coordinates are variables.** -/
theorem fvToETR_encodeAGP_varsLt (V : List FracPoint) (g : ℕ) :
    (fvToETR (encodeAGP V g)).VarsLt (2 * g) := by
  rw [fvToETR_encodeAGP]
  refine fvars_varsLt ((FVars_fvFormulaD _ _).mono fun v hv => ?_)
  have : min g (V.length + 3) ≤ g := min_le_left _ _
  show v < 2 * g
  have : v < 2 * min g (V.length + 3) := hv
  omega

end ArtGallery.FewVars

end
