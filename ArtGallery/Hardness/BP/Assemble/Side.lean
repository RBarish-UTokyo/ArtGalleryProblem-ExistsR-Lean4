module

public import ArtGallery.Hardness.BP.Assemble.Simple
public import ArtGallery.Hardness.Sec5.Assemble.Clear

/-!
# Boundary-point variant: where the units sit in a polygon, clearance

As `Sec5/Assemble/Placement.lean` and `Sec5/Assemble/Clear.lean`, for the boundary-point unit
chains `unitChainBP`.  `SideAtBP Q n k us st`: the working-frame chains of the units `us` occupy
consecutive vertices of the simple counter-clockwise polygon `Q` (unit `m` from index
`unitStartBP … m`), and right of the line `x = S` the boundary of `Q` consists of these chains.
For unit `m` (corridor input `I = unitInputBP n k m u`, template kind `u.kind`):

* `SideAtBP.corridorAt`: `CorridorAt Q I a b` (what the corridor lemmas need);
* `SideAtBP.good`: `I.Good N`;
* `SideAtBP.corridorClear`: `CorridorClear Q I`;
* `SideAtBP.chainAt`: the template chain `tmplVBP u.kind` is the chain of the polygon
  `φ⁻¹(Q)` (template coordinates, `φ = tmplMapBP`) from index `SideAtBP.tStart`
  (`Tmpl.ChainAt`);
* `SideAtBP.sep_walls`: inside the box `|x|, |y| < 60 D` the only points of non-chain edges of
  `φ⁻¹(Q)` lie on the two channel walls `[V₀, φ⁻¹(c1)]`, `[V_l, φ⁻¹(d1)]`.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### Sides -/

/-- The index of the first vertex of unit `m` of a side starting at index `st`. -/
def unitStartBP (n k : ℕ) (us : List UnitSpec) (st m : ℕ) : ℕ :=
  st + (((unitChainsBP n k 0 us).take m).map List.length).sum

theorem unitStartBP_succ {n k : ℕ} {us : List UnitSpec} {st m : ℕ} (hm : m < us.length) :
    unitStartBP n k us st (m + 1) =
      unitStartBP n k us st m + (unitChainBP n k m (us[m]'hm)).length := by
  have hm' : m < (unitChainsBP n k 0 us).length := by rw [length_unitChainsBP]; exact hm
  simp only [unitStartBP, List.take_add_one, List.getElem?_eq_getElem hm', Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, getElem_unitChainsBP, Nat.zero_add]
  omega

theorem unitStartBP_mono {n k : ℕ} {us : List UnitSpec} {st m m' : ℕ} (h : m ≤ m') :
    unitStartBP n k us st m ≤ unitStartBP n k us st m' := by
  simp only [unitStartBP, Nat.add_le_add_iff_left]
  generalize unitChainsBP n k 0 us = l
  have e : (l.take m').take m = l.take m := by rw [List.take_take, Nat.min_eq_left h]
  have := List.sum_take_add_sum_drop ((l.take m').map List.length) m
  rw [← List.map_take, e] at this
  omega

/-- The units `us` of a side are placed in `Q`. -/
structure SideAtBP (Q : Polygon) (n k : ℕ) (us : List UnitSpec) (st : ℕ) : Prop where
  /-- `Q` is simple. -/
  simple : Q.Simple
  /-- `Q` is counter-clockwise. -/
  ccw : Q.InteriorLeft
  /-- The units are admissible. -/
  ok : ∀ u ∈ us, UnitOK n u
  /-- At most `N` units. -/
  len : us.length ≤ bigN n k
  /-- `4n ≤ N`. -/
  four : 4 * n ≤ bigN n k
  /-- The unit chains fit into the vertex list. -/
  fit : unitStartBP n k us st us.length ≤ Q.n
  /-- The vertices of unit `m`. -/
  vtx : ∀ m (hm : m < us.length), ∀ i < (unitChainBP n k m (us[m]'hm)).length,
    Q.vtx (unitStartBP n k us st m + i) = ratPoint ((unitChainBP n k m (us[m]'hm)).getD i 0)
  /-- Right of `x = S` the boundary consists of the unit chains. -/
  bdry : ∀ p ∈ Q.boundary, p.1 ≤ (S n k : ℝ) ∨ ∃ f ∈ sideChainsRBP n k us, p ∈ chainSet f

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

theorem SideAtBP.end_le : unitStartBP n k us st m + (unitChainBP n k m (us[m]'hm)).length ≤ Q.n := by
  rw [← unitStartBP_succ hm]
  exact (unitStartBP_mono (by omega)).trans hQ.fit

theorem SideAtBP.good : (unitInputBP n k m (us[m]'hm)).Good (bigN n k : ℚ) :=
  unitInputBP_good (hQ.ok _ (List.getElem_mem _)) (by have := hQ.len; omega) hQ.four

/-- **The corridor of unit `m` sits in `Q`.** -/
theorem SideAtBP.corridorAt :
    CorridorAt Q (unitInputBP n k m (us[m]'hm)) (unitStartBP n k us st m)
      (unitStartBP n k us st m + (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length) := by
  have hend := hQ.end_le hm
  have hlen : (unitChainBP n k m (us[m]'hm)).length =
      (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length +
        (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChainBP, Nat.add_assoc]
  constructor
  · intro j hj
    rw [Nat.mod_eq_of_lt (by omega), hQ.vtx m hm j (by omega)]
    congr 1
    simp only [unitChainBP, List.append_assoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · intro j hj
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_assoc, Nat.add_assoc, hQ.vtx m hm _ (by omega)]
    congr 1
    simp only [unitChainBP]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]; omega

omit hQ in
/-- The real working-frame chain of unit `m`. -/
theorem SideAtBP.mem_side : (unitChainBP n k m (us[m]'hm)).map ratPoint ∈ sideChainsRBP n k us := by
  simp only [sideChainsRBP]
  have h1 := List.getElem_mem (l := unitChainsBP n k 0 us) (n := m) (by rw [length_unitChainsBP]; exact hm)
  rw [getElem_unitChainsBP] at h1
  simp only [Nat.zero_add] at h1
  exact List.mem_map_of_mem h1

end Side
/-- **The pieces of a unit chain**: floor, lower wall, template, upper wall, upper corridor wall. -/
theorem unit_piecesBP {I : Input} {N : ℚ} (hg : I.Good N) (kd : Kind) {p : Point}
    (hp : p ∈ chainSet ((I.chainBefore ++ placedTmplBP I kd ++ I.chainAfter).map ratPoint)) :
    p ∈ chainSet (I.chainBefore.map ratPoint) ∨
      p ∈ ArtGallery.segment (ratPoint (c1 I.S I.H))
        (tmplMapBP kd I.S I.H (S_ne_of hg.S_ge_k) (intPoint (tmplFstBP kd))) ∨
      p ∈ chainSet (tmplPlacedBP kd I.S I.H (S_ne_of hg.S_ge_k)) ∨
      p ∈ ArtGallery.segment (tmplMapBP kd I.S I.H (S_ne_of hg.S_ge_k) (intPoint (tmplLstBP kd)))
        (ratPoint (d1 I.S I.H)) ∨
      p ∈ chainSet (I.chainAfter.map ratPoint) := by
  have hS := hg.S_ge_k
  have hT0 : tmplPlacedBP kd I.S I.H (S_ne_of hS) ≠ [] := by
    intro h; have := tmplPlacedBP_length kd hS (H := (I.H : ℝ)); rw [h] at this; simp at this
  have hcb : I.chainBefore.map ratPoint ≠ [] := by simp [chainBefore]
  have hca : I.chainAfter.map ratPoint ≠ [] := by simp [chainAfter]
  rw [List.map_append, List.map_append, placedTmplBP_map I kd hS,
    chainSet_append_two (by simp [chainBefore]) hca, chainSet_append_two hcb hT0,
    lstPt_append_ne hT0, tmplPlacedBP_lst kd hS, tmplPlacedBP_fst kd hS] at hp
  have e1 : lstPt (I.chainBefore.map ratPoint) = ratPoint (c1 I.S I.H) := by
    rw [show I.chainBefore.map ratPoint = (ratPoint (c0 I.S I.H) :: I.floor.map ratPoint) ++
      [ratPoint (c1 I.S I.H)] by simp [chainBefore], lstPt_append_single]
  have e2 : fstPt (I.chainAfter.map ratPoint) = ratPoint (d1 I.S I.H) := by simp [chainAfter, fstPt]
  rw [e1, e2] at hp
  rcases hp with (((h | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **Clearance from the boundary near the unit.** -/
theorem corridorClearBP_of {Q : Polygon} {I : Input} {N : ℚ} (hg : I.Good N) (kd : Kind)
    (hon : ∀ w ∈ Q.boundary, (I.S : ℝ) < w.1 → (I.H : ℝ) - 1 / 4 ≤ w.2 → w.2 ≤ (I.H : ℝ) + 3 / 2 →
      w ∈ chainSet ((I.chainBefore ++ placedTmplBP I kd ++ I.chainAfter).map ratPoint)) :
    CorridorClear Q I := by
  have hS := hg.S_ge_k
  have he : 50 / (I.S : ℝ) ≤ 1 / 20 := by rw [div_le_iff₀ (by linarith)]; linarith
  intro w hwQ hwI
  obtain ⟨b1, b2, b3, b4⟩ := hg.poly_filled_box hwI
  by_cases hx : w.1 ≤ (I.S : ℝ)
  · exact I.entrance_subset (hg.filled_left hwI hx)
  push Not at hx
  rcases unit_piecesBP hg kd (hon w hwQ hx b3 b4) with h | h | h | h | h
  · exact chainSet_before_subset h
  · -- the lower wall reaches `x ≤ S + 2` only at `c1`
    have ha := tmplPlacedBP_box kd hS (tmplPlacedBP_fst_mem kd hS (H := (I.H : ℝ)))
    rcases seg_lt_or_left (α := -1) (β := 0) (c := -((I.S : ℝ) + 2))
      (by rw [ratPoint_c1']; simp) (by simp; linarith [ha.1]) h with h' | h'
    · exfalso; linarith
    · rw [h']
      apply chainSet_before_subset
      apply mem_chainSet_of_mem _ (by simp [chainBefore])
      simp [chainBefore]
  · exfalso
    have := (tmplPlacedBP_box kd hS h).1
    linarith
  · have ha := tmplPlacedBP_box kd hS (tmplPlacedBP_lst_mem kd hS (H := (I.H : ℝ)))
    rcases seg_lt_or_right (α := -1) (β := 0) (c := -((I.S : ℝ) + 2))
      (by simp; linarith [ha.1]) (by rw [ratPoint_d1']; simp) h with h' | h'
    · exfalso; linarith
    · rw [h']
      apply chainSet_after_subset
      apply mem_chainSet_of_mem _ (by simp [chainAfter])
      simp [chainAfter]
  · exact chainSet_after_subset h

/-! ### The template in template coordinates -/

theorem tmplFstBP_eq (k : Kind) : tmplFstBP k = (tmplVBP k).getD 0 (0, 0) := by
  cases k <;> rfl

theorem tmplLstBP_eq (k : Kind) : tmplLstBP k = (tmplVBP k).getD ((tmplVBP k).length - 1) (0, 0) := by
  unfold tmplLstBP
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The template chain in template coordinates is a chain of `φ⁻¹(Q)`. -/
theorem chainAtBP_of {Q : Polygon} (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) {aT : ℕ}
    (hfit : aT + (tmplVBP k).length ≤ Q.n)
    (hvtx : ∀ j < (tmplVBP k).length,
      Q.vtx (aT + j) = tmplMapBP k S H (S_ne_of hS) (intPoint ((tmplVBP k).getD j (0, 0)))) :
    Tmpl.ChainAt (Hardening.Invariance.mapPoly (tmplMapBP k S H (S_ne_of hS)).symm Q) (tmplVBP k) aT := by
  intro j hj
  rw [Hardening.Invariance.n_mapPoly, Nat.mod_eq_of_lt (by omega),
    Hardening.Invariance.vtx_mapPoly _ _ (by omega), hvtx j hj, AffineEquiv.symm_apply_apply]

/-- **Separation of the template** (the geometric content of `Tmpl.SepAt`): inside the box
`|x|, |y| < 60 D`, a point of a non-chain edge of `φ⁻¹(Q)` lies on a channel wall. -/
theorem sepWallsBP_of {Q : Polygon} {I : Input} {N : ℚ} (hg : I.Good N) (k : Kind) (hQs : Q.Simple)
    {aT : ℕ} (ha1 : 1 ≤ aT) (hfit : aT + (tmplVBP k).length ≤ Q.n)
    (hvtx : ∀ j < (tmplVBP k).length,
      Q.vtx (aT + j) = tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k) (intPoint ((tmplVBP k).getD j (0, 0))))
    (hon : ∀ z ∈ Q.boundary, (I.S : ℝ) + 2 < z.1 → (I.H : ℝ) - 1 - 1 / 10 < z.2 →
      z.2 < (I.H : ℝ) - 1 + 1 / 10 →
      z ∈ chainSet ((I.chainBefore ++ placedTmplBP I k ++ I.chainAfter).map ratPoint)) :
    ∀ i < (Hardening.Invariance.mapPoly (tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).n,
      (∀ j, j + 1 < (tmplVBP k).length →
        (aT + j) % (Hardening.Invariance.mapPoly (tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).n ≠ i) →
      ∀ x ∈ (Hardening.Invariance.mapPoly (tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).edge i,
        |x.1| < 60 * (tmplDBP k : ℝ) → |x.2| < 60 * (tmplDBP k : ℝ) →
        x ∈ ArtGallery.segment (intPoint (tmplFstBP k))
            ((tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k)).symm (ratPoint (c1 I.S I.H))) ∨
          x ∈ ArtGallery.segment (intPoint (tmplLstBP k))
            ((tmplMapBP k I.S I.H (S_ne_of hg.S_ge_k)).symm (ratPoint (d1 I.S I.H))) := by
  have hS := hg.S_ge_k
  intro i hi hnc x hx hx1 hx2
  rw [Hardening.Invariance.n_mapPoly] at hi hnc
  rw [Hardening.Invariance.edge_mapPoly _ _ hi] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzQ : z ∈ Q.boundary := ⟨i, hi, hz⟩
  -- position of `z`
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : (0 : ℝ) < (I.S : ℝ) := by linarith
  have hzc : z.1 = (I.S : ℝ) + 3 + ((tmplMapBP k I.S I.H (S_ne_of hS)).symm z).1 / ((tmplDBP k : ℝ) * I.S) ∧
      z.2 = (I.H : ℝ) - 1 + ((tmplMapBP k I.S I.H (S_ne_of hS)).symm z).2 / ((tmplDBP k : ℝ) * I.S) := by
    have e := tmplMapBP_apply k (S_ne_of hS) (H := (I.H : ℝ)) ((tmplMapBP k I.S I.H (S_ne_of hS)).symm z)
    rw [AffineEquiv.apply_symm_apply] at e
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have hsmall : ∀ t : ℝ, |t| < 60 * (tmplDBP k : ℝ) → |t / ((tmplDBP k : ℝ) * I.S)| < 1 / 10 := by
    intro t ht
    have hp : (0 : ℝ) < (tmplDBP k : ℝ) * I.S := mul_pos hD hS0
    rw [abs_div, abs_of_pos hp, div_lt_iff₀ hp]
    nlinarith
  have h1 := hsmall _ hx1
  have h2 := hsmall _ hx2
  rw [abs_lt] at h1 h2
  have hzx : (I.S : ℝ) + 2 < z.1 := by linarith [hzc.1]
  have hzu := hon z hzQ hzx (by linarith [hzc.2]) (by linarith [hzc.2])
  have hT : (tmplPlacedBP k I.S I.H (S_ne_of hS)).length = (tmplVBP k).length := by simp [tmplPlacedBP]
  have hTget : ∀ j < (tmplVBP k).length,
      (tmplPlacedBP k I.S I.H (S_ne_of hS)).getD j (0, 0) = Q.vtx (aT + j) := by
    intro j hj
    rw [hvtx j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hT]; exact hj),
      Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    simp [tmplPlacedBP]
  have hinj := hQs.2.1
  rcases unit_piecesBP hg k hzu with h | h | h | h | h
  · exfalso
    have := (hg.poly_filled_box (Or.inl (chainSet_before_subset h))).2.1
    linarith
  · left
    have := Hardening.Invariance.image_segment' (tmplMapBP k I.S I.H (S_ne_of hS)).symm (ratPoint (c1 I.S I.H))
      ((tmplMapBP k I.S I.H (S_ne_of hS)) (intPoint (tmplFstBP k)))
    rw [AffineEquiv.symm_apply_apply] at this
    rw [Geometry.segment_comm, ← this]
    exact ⟨z, h, rfl⟩
  · -- `z` is on the template chain: it must be one of its two ends
    obtain ⟨j, hj, hzj⟩ := mem_chainSet_iff.1 h
    rw [hT] at hj
    have hedge : edgeSeg (tmplPlacedBP k I.S I.H (S_ne_of hS)) j = Q.edge (aT + j) := by
      simp only [edgeSeg, Polygon.edge]
      rw [hTget j (by omega), hTget (j + 1) hj, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
    rw [hedge] at hzj
    have hne : i ≠ aT + j := fun e => hnc j hj (by rw [Nat.mod_eq_of_lt (by omega)]; exact e.symm)
    have hce := hQs.2.2 i (aT + j) hi (by omega) hne
    have hmem : z ∈ Q.edge i ∩ Q.edge (aT + j) := ⟨hz, hzj⟩
    rw [hce] at hmem
    obtain ⟨e1, e2⟩ := hmem
    rw [Nat.mod_eq_of_lt (show aT + j + 1 < Q.n by omega)] at e2
    have hi1 : (i + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
    have fst_case : z = Q.vtx aT → (tmplMapBP k I.S I.H (S_ne_of hS)).symm z ∈ ArtGallery.segment (intPoint (tmplFstBP k))
        ((tmplMapBP k I.S I.H (S_ne_of hS)).symm (ratPoint (c1 I.S I.H))) := by
      intro e
      rw [e, show aT = aT + 0 by rfl, hvtx 0 (by omega), AffineEquiv.symm_apply_apply,
        ← tmplFstBP_eq]
      exact Geometry.left_mem_segment _ _
    have lst_case : z = Q.vtx (aT + ((tmplVBP k).length - 1)) → (tmplMapBP k I.S I.H (S_ne_of hS)).symm z ∈ ArtGallery.segment
        (intPoint (tmplLstBP k)) ((tmplMapBP k I.S I.H (S_ne_of hS)).symm (ratPoint (d1 I.S I.H))) := by
      intro e
      rw [e, hvtx _ (by omega), AffineEquiv.symm_apply_apply, ← tmplLstBP_eq]
      exact Geometry.left_mem_segment _ _
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (hinj _ _ hi (by omega) (e1 ▸ e2)) hne
    · have hi' := hinj _ _ hi (by omega) (e1 ▸ e2)
      by_cases hj2 : j + 1 + 1 < (tmplVBP k).length
      · exact absurd (by rw [Nat.mod_eq_of_lt (by omega)]; omega) (hnc (j + 1) hj2)
      · right
        apply lst_case
        rw [e2]; congr 1; omega
    · have hi' := hinj _ _ hi1 (by omega) (e1 ▸ e2)
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · left; apply fst_case; simpa using e2
      · exfalso
        have hwrap : i + 1 < Q.n := by
          by_contra hc
          have : i + 1 = Q.n := by omega
          rw [this, Nat.mod_self] at hi'; omega
        rw [Nat.mod_eq_of_lt hwrap] at hi'
        exact hnc (j - 1) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
    · exfalso
      have hi' := hinj _ _ hi1 (by omega) (e1 ▸ e2)
      have hwrap : i + 1 < Q.n := by
        by_contra hc
        have : i + 1 = Q.n := by omega
        rw [this, Nat.mod_self] at hi'; omega
      rw [Nat.mod_eq_of_lt hwrap] at hi'
      exact hne (by omega)
  · right
    have := Hardening.Invariance.image_segment' (tmplMapBP k I.S I.H (S_ne_of hS)).symm ((tmplMapBP k I.S I.H (S_ne_of hS)) (intPoint (tmplLstBP k)))
      (ratPoint (d1 I.S I.H))
    rw [AffineEquiv.symm_apply_apply] at this
    rw [← this]
    exact ⟨z, h, rfl⟩
  · exfalso
    have := (hg.poly_filled_box (Or.inl (chainSet_after_subset h))).2.1
    linarith

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

omit hQ hm in
/-- Unit chains of the side are unit chains `m'` of the list. -/
theorem SideAtBP.mem_sideChains {f : List Point} (hf : f ∈ sideChainsRBP n k us) :
    ∃ m', ∃ hm' : m' < us.length, f = (unitChainBP n k m' (us[m']'hm')).map ratPoint := by
  simp only [sideChainsRBP, List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hc
  have hm'' : m' < us.length := by rw [length_unitChainsBP] at hm'; exact hm'
  exact ⟨m', hm'', by rw [getElem_unitChainsBP, Nat.zero_add]⟩

/-- Points of the boundary of `Q` right of `x = S`, at the height of unit `m`
(`|y − (H − 1)| < 1`, or within `[H − 1/4, H + 3/2]`), lie on the chain of unit `m`. -/
theorem SideAtBP.on_unit {z : Point} (hz : z ∈ Q.boundary) (hzx : (S n k : ℝ) < z.1)
    (hzy : (S n k : ℝ) + 3 * m - 0.4 ≤ z.2 ∧ z.2 ≤ (S n k : ℝ) + 3 * m + 2.6) :
    z ∈ chainSet ((unitChainBP n k m (us[m]'hm)).map ratPoint) := by
  rcases hQ.bdry z hz with h | ⟨f, hf, hzf⟩
  · exact absurd h (not_le.2 hzx)
  obtain ⟨m', hm', rfl⟩ := SideAtBP.mem_sideChains hf
  have u := unitChainBP_feature (u := us[m']'hm') (m := m') (hQ.ok _ (List.getElem_mem hm'))
    (by have := hQ.len; omega) hQ.four
  obtain ⟨-, -, b3, b4⟩ := u.box z hzf
  rcases lt_trichotomy m' m with h | rfl | h
  · exfalso
    have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith
  · exact hzf
  · exfalso
    have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
    linarith

set_option linter.unusedSectionVars false in
theorem SideAtBP.cast_S : (((unitInputBP n k m (us[m]'hm)).S : ℚ) : ℝ) = (S n k : ℝ) := by
  simp [unitInputBP]

set_option linter.unusedSectionVars false in
theorem SideAtBP.cast_H : (((unitInputBP n k m (us[m]'hm)).H : ℚ) : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
  simp [unitInputBP, Sec5.unitH]

/-- **Clearance of the corridor of unit `m`** (the hypothesis of `Good.poly_subset`). -/
theorem SideAtBP.corridorClear : CorridorClear Q (unitInputBP n k m (us[m]'hm)) := by
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  refine corridorClearBP_of (hQ.good hm) (us[m]'hm).kind (fun w hw hx hy1 hy2 => ?_)
  rw [eS] at hx
  rw [eH] at hy1 hy2
  exact hQ.on_unit hm hw hx ⟨by linarith, by linarith⟩

/-- The index of the first template vertex of unit `m`. -/
abbrev SideAtBP.tStart (_hQ : SideAtBP Q n k us st) : ℕ :=
  unitStartBP n k us st m + (unitInputBP n k m (us[m]'hm)).chainBefore.length

theorem SideAtBP.tmpl_vtx : ∀ j < (tmplVBP (us[m]'hm).kind).length,
    Q.vtx (hQ.tStart hm + j) = tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
      (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)
      (intPoint ((tmplVBP (us[m]'hm).kind).getD j (0, 0))) := by
  intro j hj
  have hg := hQ.good hm
  have hlp : (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplVBP (us[m]'hm).kind).length := by simp [placedTmplBP]
  have hlen : (unitChainBP n k m (us[m]'hm)).length =
      (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length +
        (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChainBP, Nat.add_assoc]
  rw [SideAtBP.tStart, Nat.add_assoc, hQ.vtx m hm _ (by omega)]
  have e1 : (unitChainBP n k m (us[m]'hm)).getD
      ((unitInputBP n k m (us[m]'hm)).chainBefore.length + j) 0 =
      (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).getD j 0 := by
    simp only [unitChainBP, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by omega)]
  rw [e1]
  have e2 := congrArg (fun l => l.getD j (0, 0)) (placedTmplBP_map (unitInputBP n k m (us[m]'hm))
    (us[m]'hm).kind hg.S_ge_k)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)] at e2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [Option.map_some, Option.getD_some] at e2
  rw [e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [tmplPlacedBP]; omega),
    Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  simp [tmplPlacedBP]

/-- **The template chain of unit `m` in template coordinates** (`Tmpl.ChainAt`). -/
theorem SideAtBP.chainAt :
    Tmpl.ChainAt (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind
      (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k)).symm Q) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm) := by
  have hend := hQ.end_le hm
  have hlen : (unitChainBP n k m (us[m]'hm)).length =
      (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (tmplVBP (us[m]'hm).kind).length + (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChainBP, placedTmplBP, Nat.add_assoc]
  exact chainAtBP_of _ (hQ.good hm).S_ge_k (by simp only [SideAtBP.tStart]; omega) (hQ.tmpl_vtx hm)

/-- **Separation of the template of unit `m`**: inside the box `|x|, |y| < 60 D` the non-chain
edges of `φ⁻¹(Q)` only meet the two channel walls. -/
theorem SideAtBP.sep_walls :
    ∀ i < (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
      (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).n,
      (∀ j, j + 1 < (tmplVBP (us[m]'hm).kind).length → (hQ.tStart hm + j) %
        (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
          (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).n ≠ i) →
      ∀ x ∈ (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
        (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).edge i,
        |x.1| < 60 * (tmplDBP (us[m]'hm).kind : ℝ) → |x.2| < 60 * (tmplDBP (us[m]'hm).kind : ℝ) →
        x ∈ ArtGallery.segment (intPoint (tmplFstBP (us[m]'hm).kind))
            ((tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
              (S_ne_of (hQ.good hm).S_ge_k)).symm
              (ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H))) ∨
          x ∈ ArtGallery.segment (intPoint (tmplLstBP (us[m]'hm).kind))
            ((tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
              (S_ne_of (hQ.good hm).S_ge_k)).symm
              (ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H))) := by
  have hend := hQ.end_le hm
  have hlen : (unitChainBP n k m (us[m]'hm)).length =
      (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (tmplVBP (us[m]'hm).kind).length + (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChainBP, placedTmplBP, Nat.add_assoc]
  have hcb : 2 ≤ (unitInputBP n k m (us[m]'hm)).chainBefore.length := by simp [chainBefore]
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  refine sepWallsBP_of (hQ.good hm) _ hQ.simple (by simp only [SideAtBP.tStart]; omega)
    (by simp only [SideAtBP.tStart]; omega) (hQ.tmpl_vtx hm) (fun z hz hzx hy1 hy2 => ?_)
  rw [eS] at hzx
  rw [eH] at hy1 hy2
  exact hQ.on_unit hm hz (by linarith) ⟨by linarith, by linarith⟩

end Unit

end ArtGallery.BP

end
