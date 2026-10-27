module

public import ArtGallery.Hardness.Sec5.ConstraintCopy

/-!
# Section 5, constraints: the guards of one unit

The positions of a unit (`Count.uSys`) in its working frame: corridor stationary guards and the
template positions `(tsysOf κ).spot X`.  This file

* identifies the template position of the receiver `τ` (`recvIdx κ τ`) and checks, for the four
  template kinds, that its spot is the receiver segment `[D T_τ, D (T_τ + (3/2, 0))]`
  (`recvOK`), and that every other template position is far from the strip of `τ` (`farOK`, the
  hypothesis `FarTmpl` of the copy lemma);
* states the hypotheses `UnitG` on a guard set seen from one unit (in the working frame) and
  proves the **copy statement for the unit** (`UnitG.recv_eq`): the guard of the receiver of pair
  `k` is the receiver point with the offset of the base guard of slot `σ_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon Tmpl Vis.Cert
open Corridor (Input CorridorAt CopyPair c0 c1 d0 d1 place Oc xiOf Xis RecvHyp)
open Corridor.Input
open ArtGallery.Sec5.Count (unitBox tsysOf uφ unitPoly)

/-! ### The receivers among the template positions -/

/-- The template position of receiver `τ`. -/
def recvIdx : (κ : Kind) → ℕ → Fin (tsysOf κ).r
  | .orient, 0 => ⟨2, by decide⟩
  | .orient, _ => ⟨3, by decide⟩
  | .ge, 0 => ⟨3, by decide⟩
  | .ge, 1 => ⟨1, by decide⟩
  | .ge, _ => ⟨2, by decide⟩
  | .le, 0 => ⟨3, by decide⟩
  | .le, 1 => ⟨1, by decide⟩
  | .le, _ => ⟨2, by decide⟩
  | .inv, 0 => ⟨2, by decide⟩
  | .inv, _ => ⟨1, by decide⟩

/-- The spot `L` is the receiver segment `[D T, D (T + (3/2, 0))]`. -/
def recvSpotB (D : ℕ) (T : Q2) (L : List IPt) : Bool :=
  match L with
  | [A, B] => decide ((A.1 : ℚ) = D * T.1 ∧ (A.2 : ℚ) = D * T.2 ∧ 2 * B.1 = 2 * A.1 + 3 * D ∧
      B.2 = A.2)
  | _ => false

/-- The receivers of kind `κ` are template positions. -/
def recvOK (κ : Kind) : Bool :=
  (List.range (tmplT κ).length).all fun τ =>
    recvSpotB (tmplD κ) ((tmplT κ).getD τ (0, 0)) ((tsysOf κ).spot (recvIdx κ τ))

/-- The receiver check holds for all kinds. -/
theorem recvOK_true (κ : Kind) : recvOK κ = true := by
  cases κ <;> decide +kernel

/-- All points of `L` have coordinate sum `≥ D (s + 5)` or all have `≤ D (s − 4)`. -/
def sumFarB (D : ℕ) (s : ℚ) (L : List IPt) : Bool :=
  L.all (fun q => decide ((D : ℚ) * (s + 5) ≤ ((q.1 + q.2 : ℤ) : ℚ))) ||
    L.all (fun q => decide (((q.1 + q.2 : ℤ) : ℚ) ≤ (D : ℚ) * (s - 4)))

/-- The coordinate sum `T_0.x + T_0.y − 27τ/2` of the receiver `τ`. -/
def recvSum (κ : Kind) (τ : ℕ) : ℚ :=
  ((tmplT κ).getD 0 (0, 0)).1 + ((tmplT κ).getD 0 (0, 0)).2 - 27 * (τ : ℚ) / 2

/-- Every template position other than the receiver `τ` is far from its strip. -/
def farOK (κ : Kind) : Bool :=
  (List.range (tmplT κ).length).all fun τ => (List.finRange (tsysOf κ).r).all fun X =>
    decide (X = recvIdx κ τ) || sumFarB (tmplD κ) (recvSum κ τ) ((tsysOf κ).spot X)

/-- The far check holds for all kinds. -/
theorem farOK_true (κ : Kind) : farOK κ = true := by
  cases κ <;> decide +kernel

/-! ### Soundness of the checks -/

/-- A point of the hull of two integer points is a point of the segment. -/
theorem mem_hull_two {A B : IPt} {x : Point} (hx : x ∈ convexHull ℝ (intSet [A, B])) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ x = Geometry.lerp (intPoint A) (intPoint B) r := by
  have e : intSet [A, B] = {intPoint A, intPoint B} := by simp
  rw [e, convexHull_pair] at hx
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  refine ⟨b, hb, by linarith, ?_⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  ext <;> simp [Geometry.lerp] <;> ring

/-- **Receiver positions** are the receiver segments (template coordinates `D · T`). -/
theorem recv_spot (κ : Kind) {τ : ℕ} (hτ : τ < (tmplT κ).length) {x : Point}
    (hx : x ∈ convexHull ℝ (intSet ((tsysOf κ).spot (recvIdx κ τ)))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 3 / 2 ∧
      x = ((tmplD κ : ℝ) * ((((tmplT κ).getD τ (0, 0)).1 : ℚ) + t),
        (tmplD κ : ℝ) * ((((tmplT κ).getD τ (0, 0)).2 : ℚ) : ℝ)) := by
  have h := recvOK_true κ
  simp only [recvOK, List.all_eq_true, List.mem_range] at h
  have h' := h τ hτ
  generalize (tsysOf κ).spot (recvIdx κ τ) = L at h' hx
  generalize (tmplT κ).getD τ (0, 0) = T at h' ⊢
  generalize tmplD κ = D at h' ⊢
  match L, h' with
  | [A, B], h' =>
    simp only [recvSpotB, decide_eq_true_eq] at h'
    obtain ⟨e1, e2, e3, e4⟩ := h'
    obtain ⟨r, hr0, hr1, rfl⟩ := mem_hull_two hx
    refine ⟨3 / 2 * r, by positivity, by linarith, ?_⟩
    have e1' : (A.1 : ℝ) = (D : ℝ) * (T.1 : ℝ) := by exact_mod_cast e1
    have e2' : (A.2 : ℝ) = (D : ℝ) * (T.2 : ℝ) := by exact_mod_cast e2
    have e3' : (2 : ℝ) * B.1 = 2 * A.1 + 3 * D := by exact_mod_cast e3
    have e4' : (B.2 : ℝ) = A.2 := by exact_mod_cast e4
    simp only [Geometry.lerp, intPoint]
    ext
    · simp only
      have hb : (B.1 : ℝ) - A.1 = 3 / 2 * D := by linarith
      rw [hb, e1']; ring
    · simp only; rw [e4', e2']; ring

/-- **Other positions are far from the strip of the receiver `τ`.** -/
theorem far_spot (κ : Kind) {τ : ℕ} (hτ : τ < (tmplT κ).length) {X : Fin (tsysOf κ).r}
    (hX : X ≠ recvIdx κ τ) {x : Point} (hx : x ∈ convexHull ℝ (intSet ((tsysOf κ).spot X))) :
    (tmplD κ : ℝ) * ((recvSum κ τ : ℚ) + 5) ≤ x.1 + x.2 ∨
      x.1 + x.2 ≤ (tmplD κ : ℝ) * ((recvSum κ τ : ℚ) - 4) := by
  have h := farOK_true κ
  simp only [farOK, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h τ hτ X with h | h
  · exact absurd h hX
  generalize (tsysOf κ).spot X = L at h hx
  generalize recvSum κ τ = s at h ⊢
  generalize tmplD κ = D at h ⊢
  simp only [sumFarB, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · left
    have hc : Convex ℝ {y : Point | (D : ℝ) * ((s : ℝ) + 5) ≤ y.1 + y.2} := by
      intro u hu v hv a b ha hb hab
      simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hu hv ⊢
      calc (D : ℝ) * ((s : ℝ) + 5) = a * ((D : ℝ) * ((s : ℝ) + 5)) + b * ((D : ℝ) * ((s : ℝ) + 5)) := by
            rw [← add_mul, hab, one_mul]
        _ ≤ a * (u.1 + u.2) + b * (v.1 + v.2) :=
            add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
        _ = _ := by ring
    refine convexHull_min (fun y hy => ?_) hc hx
    obtain ⟨q, hq, rfl⟩ := hy
    have := h q hq
    have : ((D : ℚ) * (s + 5) : ℝ) ≤ (((q.1 + q.2 : ℤ) : ℚ) : ℝ) := by exact_mod_cast this
    simp only [mem_ofPred_eq, intPoint]
    push_cast at this ⊢; linarith
  · right
    have hc : Convex ℝ {y : Point | y.1 + y.2 ≤ (D : ℝ) * ((s : ℝ) - 4)} := by
      intro u hu v hv a b ha hb hab
      simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hu hv ⊢
      calc _ = a * (u.1 + u.2) + b * (v.1 + v.2) := by ring
        _ ≤ a * ((D : ℝ) * ((s : ℝ) - 4)) + b * ((D : ℝ) * ((s : ℝ) - 4)) :=
            add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
        _ = (D : ℝ) * ((s : ℝ) - 4) := by rw [← add_mul, hab, one_mul]
    refine convexHull_min (fun y hy => ?_) hc hx
    obtain ⟨q, hq, rfl⟩ := hy
    have := h q hq
    have : (((q.1 + q.2 : ℤ) : ℚ) : ℝ) ≤ ((D : ℚ) * (s - 4) : ℝ) := by exact_mod_cast this
    simp only [mem_ofPred_eq, intPoint]
    push_cast at this ⊢; linarith

/-! ### The guards seen from one unit -/

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ

/-- The corner `c1` of the corridor is a vertex of the unit room. -/
theorem side_c1_mem : ratPoint (c1 (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H) ∈
    (unitPoly n k m (us[m]'hm)).filled := by
  obtain ⟨-, -, hV⟩ := Count.side_unitRoom hQ hm
  have h2 : 2 ≤ (unitInput n k m (us[m]'hm)).chainBefore.length := by
    rw [chainBefore_length]; omega
  have hlen : (unitInput n k m (us[m]'hm)).chainBefore.length - 1 <
      (unitChain n k m (us[m]'hm)).length := by
    simp only [unitChain, List.length_append]; omega
  have := hV _ hlen
  rwa [unitChain, List.append_assoc, List.getD_append _ _ _ _ (by omega),
    chainBefore_getD_last] at this

end Unit

/-- **The guards seen from unit `m`** (working frame): `G` sees all of `Q`; every point of `G`
is a base guard `(27σ/2 + off σ, 0)`, a foreign point, a corridor stationary guard of the unit, or
the guard `tg X` of a template position `X` of the unit (`tg X` lies on the position). -/
structure UnitG (Q : Polygon) (n k : ℕ) (us : List UnitSpec) (m : ℕ) (hm : m < us.length)
    (κ : Kind) (G : Set Point) (off : ℕ → ℝ) (tg : Fin (tsysOf κ).r → Point) : Prop where
  kind : (us[m]'hm).kind = κ
  cov : ∀ z ∈ Q.filled, ∃ g ∈ G, Q.Sees g z
  off_mem : ∀ σ < 4 * n, 0 ≤ off σ ∧ off σ ≤ 3 / 2
  tg_mem : ∀ X, tg X ∈ uφ n k m (us[m]'hm) '' convexHull ℝ (intSet ((tsysOf κ).spot X))
  cls : ∀ g ∈ G, (∃ σ < 4 * n, g = (27 * (σ : ℝ) / 2 + off σ, 0)) ∨
    Foreign ((unitInput n k m (us[m]'hm)).S : ℝ) ((unitInput n k m (us[m]'hm)).H : ℝ)
      (((bigN n k : ℚ)) : ℝ) g ∨
    (∃ j < (unitInput n k m (us[m]'hm)).np, g = ratPoint ((unitInput n k m (us[m]'hm)).sgPt j)) ∨
    (∃ X, g = tg X)

section Unit2

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ

omit hQ in
/-- The placement in coordinates. -/
theorem uφ_apply (p : Point) : uφ n k m (us[m]'hm) p =
    (((unitInput n k m (us[m]'hm)).S : ℝ) + 3 +
        p.1 / ((tmplD (us[m]'hm).kind : ℝ) * ((unitInput n k m (us[m]'hm)).S : ℝ)),
      ((unitInput n k m (us[m]'hm)).H : ℝ) - 1 +
        p.2 / ((tmplD (us[m]'hm).kind : ℝ) * ((unitInput n k m (us[m]'hm)).S : ℝ))) :=
  tmplMap_apply _ _ p

omit hQ in
/-- A placed template point is the point `m + T/S` with `T = p / D`. -/
theorem uφ_eq_place (p : Point) : uφ n k m (us[m]'hm) p =
    place ((unitInput n k m (us[m]'hm)).S : ℝ) ((unitInput n k m (us[m]'hm)).H : ℝ)
      (p.1 / (tmplD (us[m]'hm).kind : ℝ), p.2 / (tmplD (us[m]'hm).kind : ℝ)) := by
  rw [uφ_apply]
  simp only [place]
  have hD : (0 : ℝ) < tmplD (us[m]'hm).kind := by exact_mod_cast tmplD_pos _
  have hS := Count.unitS_ge n k m (us[m]'hm)
  have hS0 : ((unitInput n k m (us[m]'hm)).S : ℝ) ≠ 0 := by linarith
  ext <;> simp only <;> field_simp

variable {κ : Kind} {G : Set Point} {off : ℕ → ℝ} {tg : Fin (tsysOf κ).r → Point}

/-- **The copy statement for a unit.**  The guard of the receiver of pair `j` is the receiver
point with the offset of the base guard of slot `σ_j`. -/
theorem UnitG.recv_eq (hU : UnitG Q n k us m hm κ G off tg) {j : ℕ}
    (hj : j < (unitInput n k m (us[m]'hm)).np) :
    tg (recvIdx κ ((unitInput n k m (us[m]'hm)).tau j)) =
      place ((unitInput n k m (us[m]'hm)).S : ℝ) ((unitInput n k m (us[m]'hm)).H : ℝ)
        (((unitInput n k m (us[m]'hm)).Tt ((unitInput n k m (us[m]'hm)).tau j)).1 +
          off ((unitInput n k m (us[m]'hm)).sigma j),
          ((unitInput n k m (us[m]'hm)).Tt ((unitInput n k m (us[m]'hm)).tau j)).2) := by
  obtain hκ := hU.kind
  subst hκ
  set I := unitInput n k m (us[m]'hm) with hI
  have hg := hQ.good hm
  have hok := hQ.ok _ (List.getElem_mem hm)
  have hlenT : I.np = (tmplT (us[m]'hm).kind).length := hok.len
  have hτ : I.tau j < (tmplT (us[m]'hm).kind).length := by rw [← hlenT]; exact hg.tau_lt hj
  have hσ : I.sigma j < 4 * n := by
    apply hok.lt
    have hj' : j < (us[m]'hm).work.length := hj
    show (us[m]'hm).work.getD j 0 ∈ (us[m]'hm).work
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact List.getElem_mem _
  have hTt : ∀ τ, I.Tt τ = (tmplT (us[m]'hm).kind).getD τ (0, 0) := fun τ => rfl
  -- the receiver guard
  obtain ⟨x0, hx0, hx0e⟩ := hU.tg_mem (recvIdx (us[m]'hm).kind (I.tau j))
  obtain ⟨t', ht0', ht1', rfl⟩ := recv_spot (us[m]'hm).kind hτ hx0
  have hD : (0 : ℝ) < tmplD (us[m]'hm).kind := by exact_mod_cast tmplD_pos _
  have hq : tg (recvIdx (us[m]'hm).kind (I.tau j)) = place (I.S : ℝ) (I.H : ℝ)
      (((I.Tt (I.tau j)).1 : ℝ) + t', ((I.Tt (I.tau j)).2 : ℝ)) := by
    rw [← hx0e, uφ_eq_place, hTt]
    congr 1
    ext <;> simp only <;> field_simp
  rw [hq]
  -- the copy lemma
  obtain ⟨hR, hB, -⟩ := Count.side_unitRoom hQ hm
  have ho := hU.off_mem _ hσ
  have heq := Good.copy_eq hg hQ.simple hQ.ccw (hQ.corridorAt hm) (hQ.corridorClear hm) hR hB
    (side_c1_mem hQ hm) hU.cov hj ho.1 ho.2 ht0' ht1' (fun g hgG => ?_)
  · rw [heq]
  -- the classes
  have hN := four_n_le_bigN (n := n) (k := k)
  have hNr : (4 * n : ℝ) ≤ (bigN n k : ℝ) := by exact_mod_cast hN
  rcases hU.cls g hgG with ⟨σ, hσ', rfl⟩ | hf | hsg | ⟨X, rfl⟩
  · refine Or.inl ⟨σ, off σ, (hU.off_mem σ hσ').1, (hU.off_mem σ hσ').2, ?_, rfl,
      fun h => by rw [h]⟩
    have : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ'
    have := (hU.off_mem σ hσ').2
    push_cast
    linarith
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr (Or.inl hsg))
  · by_cases hX : X = recvIdx (us[m]'hm).kind (I.tau j)
    · subst hX; exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      obtain ⟨x, hx, hxe⟩ := hU.tg_mem X
      have hbox := Count.hull_box ((Count.tsysOf_facts (us[m]'hm).kind).box X) x hx
      obtain ⟨b1, b2, b3, b4⟩ := hbox
      have hfar := far_spot (us[m]'hm).kind hτ hX hx
      refine ⟨(x.1 / (tmplD (us[m]'hm).kind : ℝ), x.2 / (tmplD (us[m]'hm).kind : ℝ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only; rw [le_div_iff₀ hD]; push_cast at b1; linarith
      · simp only; rw [div_le_iff₀ hD]; push_cast at b2; linarith
      · simp only; rw [le_div_iff₀ hD]; push_cast at b3; linarith
      · simp only; rw [div_le_iff₀ hD]; push_cast at b4; linarith
      · simp only
        have e : x.1 / (tmplD (us[m]'hm).kind : ℝ) + x.2 / (tmplD (us[m]'hm).kind : ℝ) = (x.1 + x.2) / (tmplD (us[m]'hm).kind : ℝ) := by
          ring
        rw [e]
        have hs : ((recvSum (us[m]'hm).kind (I.tau j) : ℚ) : ℝ) = ((I.T0.1 : ℚ) : ℝ) + ((I.T0.2 : ℚ) : ℝ) -
            27 * (I.tau j : ℝ) / 2 := by
          simp only [recvSum, Input.T0, hTt]; push_cast; ring
        rw [← hs]
        rcases hfar with h | h
        · left; rw [le_div_iff₀ hD]; linarith
        · right; rw [div_le_iff₀ hD]; linarith
      · rw [← hxe, uφ_eq_place]

/-- The placed polygon in the template coordinates of unit `m`. -/
noncomputable abbrev tP (Q : Polygon) (n k m : ℕ) (u : UnitSpec) : Polygon :=
  Hardening.Invariance.mapPoly (uφ n k m u).symm Q

/-- **Template zones are seen only by template positions of the unit.**  Let `Z` be a set of
template points in the box `|x|, |y| ≤ 60 D`, all seen (in the template frame) from the template
vertex `jv`.  Then every point of `Z` is seen by the guard of some template position. -/
theorem UnitG.zone_seen (hU : UnitG Q n k us m hm κ G off tg) {Z : Set Point}
    (hZbox : ∀ z ∈ Z, |z.1| ≤ 60 * (tmplD κ : ℝ) ∧ |z.2| ≤ 60 * (tmplD κ : ℝ))
    {jv : ℕ} (hjv : jv < (tmplV κ).length)
    (hsee : ∀ z ∈ Z, (tP Q n k m (us[m]'hm)).Sees (tpt (tmplV κ) jv) z) :
    ∀ z ∈ Z, ∃ X, (tP Q n k m (us[m]'hm)).Sees ((uφ n k m (us[m]'hm)).symm (tg X)) z := by
  obtain hκ := hU.kind
  subst hκ
  intro z hz
  have hH := Count.side_unitHyp hQ hm
  rw [show tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
    (S_ne_of (hQ.good hm).S_ge_k) = uφ n k m (us[m]'hm) from rfl] at hH
  set φ := uφ n k m (us[m]'hm) with hφ
  set I := unitInput n k m (us[m]'hm) with hI
  have hg := hQ.good hm
  obtain ⟨hS8, hN, hSN, hH1, hH2, hρ0, hρ1⟩ := Good.realFacts hg
  have hD : (0 : ℝ) < tmplD (us[m]'hm).kind := by exact_mod_cast tmplD_pos _
  obtain ⟨hR, hB, -⟩ := Count.side_unitRoom hQ hm
  -- coordinates of placed box points
  have hcoord : ∀ p : Point, |p.1| ≤ 60 * (tmplD (us[m]'hm).kind : ℝ) →
      |p.2| ≤ 60 * (tmplD (us[m]'hm).kind : ℝ) →
      (I.S : ℝ) + 5 / 2 ≤ (φ p).1 ∧ (φ p).2 ≤ (I.H : ℝ) - 1 / 2 := by
    intro p h1 h2
    rw [hφ, uφ_apply]
    rw [abs_le] at h1 h2
    have hDS : (0 : ℝ) < (tmplD (us[m]'hm).kind : ℝ) * I.S := by positivity
    constructor
    · simp only
      have : -(1 / 2 : ℝ) ≤ p.1 / ((tmplD (us[m]'hm).kind : ℝ) * I.S) := by
        rw [le_div_iff₀ hDS]; nlinarith
      linarith
    · simp only
      have : p.2 / ((tmplD (us[m]'hm).kind : ℝ) * I.S) ≤ 1 / 2 := by
        rw [div_le_iff₀ hDS]; nlinarith
      linarith
  obtain ⟨zb1, zb2⟩ := hZbox z hz
  obtain ⟨cz1, cz2⟩ := hcoord z zb1 zb2
  -- the template vertex
  obtain ⟨v1, v2, v3, v4⟩ := hH.vbox jv hjv
  have hvb1 : |(tpt (tmplV (us[m]'hm).kind) jv).1| ≤ 60 * (tmplD (us[m]'hm).kind : ℝ) := by
    simp only [tpt, intPoint_fst, abs_le]
    constructor
    · have : (-(50 * (tmplD (us[m]'hm).kind : ℤ)) : ℝ) ≤ ((cv (tmplV (us[m]'hm).kind) jv).1 : ℝ) := by
        exact_mod_cast v1
      push_cast at this; linarith
    · have : ((cv (tmplV (us[m]'hm).kind) jv).1 : ℝ) ≤ ((50 * (tmplD (us[m]'hm).kind : ℤ)) : ℝ) := by
        exact_mod_cast v2
      push_cast at this; linarith
  have hvb2 : |(tpt (tmplV (us[m]'hm).kind) jv).2| ≤ 60 * (tmplD (us[m]'hm).kind : ℝ) := by
    simp only [tpt, intPoint_snd, abs_le]
    constructor
    · have : (-(50 * (tmplD (us[m]'hm).kind : ℤ)) : ℝ) ≤ ((cv (tmplV (us[m]'hm).kind) jv).2 : ℝ) := by
        exact_mod_cast v3
      push_cast at this; linarith
    · have : ((cv (tmplV (us[m]'hm).kind) jv).2 : ℝ) ≤ ((50 * (tmplD (us[m]'hm).kind : ℤ)) : ℝ) := by
        exact_mod_cast v4
      push_cast at this; linarith
  obtain ⟨cv1, -⟩ := hcoord _ hvb1 hvb2
  have hsz : Q.Sees (φ (tpt (tmplV (us[m]'hm).kind) jv)) (φ z) := by
    rw [hH.sees_iff, AffineEquiv.symm_apply_apply]; exact hsee z hz
  -- `φ z` is in the unit room and in `Q`
  have hzK : φ z ∈ (unitPoly n k m (us[m]'hm)).filled := by
    refine mem_room_of_sees hR (hH.room_mem jv hjv) hsz fun w hw hwE => ?_
    obtain ⟨e1, -, -⟩ := mem_entrance hρ0.le hwE
    have := Irrational.seg_fst_ge hw
    rcases le_total (φ (tpt (tmplV (us[m]'hm).kind) jv)).1 (φ z).1 with h | h
    · rw [min_eq_left h] at this; linarith
    · rw [min_eq_right h] at this; linarith
  have hzQ : φ z ∈ Q.filled := hsz (Geometry.right_mem_segment _ _)
  obtain ⟨g, hgG, hgs⟩ := hU.cov _ hzQ
  rcases hU.cls g hgG with ⟨σ, hσ, rfl⟩ | hf | ⟨j, hj, rfl⟩ | ⟨X, rfl⟩
  · exfalso
    refine Good.foreign_not_sees_tmpl hg hR hB hzK (by linarith) cz2 (Or.inr ⟨rfl, ?_⟩) hgs
    have h1 : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ
    have h2 := (hU.off_mem σ hσ).2
    have h3 : 54 * (n : ℝ) + 100000 ≤ (S n k : ℝ) := by
      have := slots_lt_S (n := n) (k := k)
      have : ((54 * (n : ℚ) + 100000 : ℚ) : ℝ) ≤ ((S n k : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at this; exact this
    have h4 : (I.S : ℝ) = (S n k : ℝ) := by simp [hI, unitInput]
    simp only; rw [h4]; linarith
  · exact absurd hgs (Good.foreign_not_sees_tmpl hg hR hB hzK (by linarith) cz2 (Or.inl hf))
  · exfalso
    have c := (hg.sg_cone hQ.simple hQ.ccw (hQ.corridorAt hm) hj hgs).1
    have := (hH.sg_corridor hj).2.1
    linarith
  · refine ⟨X, ?_⟩
    rwa [hH.sees_iff] at hgs

end Unit2

end ArtGallery.Sec5.Constraint

end
