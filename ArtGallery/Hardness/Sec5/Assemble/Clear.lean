module

public import ArtGallery.Hardness.Sec5.Assemble.Placement

/-!
# Section 5: clearance of a unit in its polygon

For unit `m` of a side `SideAt Q n k us st` (see `Placement.lean`):

* `SideAt.corridorClear`: `CorridorClear Q I` — the boundary of `Q` meets the corridor region only
  in the corridor polygon's boundary;
* `SideAt.chainAt`: the template chain in template coordinates (`Tmpl.ChainAt` for `φ⁻¹(Q)`);
* `SideAt.sep_walls`: inside the template box `|x|, |y| < 60 D` the non-chain edges of `φ⁻¹(Q)`
  only meet the two channel walls; `sepAt_of_walls`: hence `Tmpl.SepAt` for every region inside
  that box whose zones contain the two walls.

All rest on the boundary description `SideAt.bdry` (right of `x = S` only unit chains), the
separation of different units by height, and the decomposition of a unit chain into floor,
lower wall, template, upper wall, upper corridor wall (`unit_pieces`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input CorridorAt c0 c1 d0 d1)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The closing edge of a polygon is part of its boundary. -/
theorem closing_subset_boundary {V : List Point} (hV : V ≠ []) :
    ArtGallery.segment (lstPt V) (fstPt V) ⊆ (Polygon.mk V).boundary := by
  intro x hx
  have hn : (Polygon.mk V).n = V.length := rfl
  have hl : 0 < V.length := List.length_pos_iff.2 hV
  refine ⟨V.length - 1, by omega, ?_⟩
  simp only [Polygon.edge, hn, show V.length - 1 + 1 = V.length by omega, Nat.mod_self]
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hV
  have e1 : (Polygon.mk (a :: l)).vtx ((a :: l).length - 1) = lstPt (a :: l) := by
    simp only [Polygon.vtx, lstPt]
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp [List.getD_eq_getElem?_getD]
  rw [e1]
  exact hx

/-- The entrance of a corridor is part of the corridor polygon's boundary. -/
theorem Corridor.Input.entrance_subset (I : Input) : I.entrance ⊆ I.poly.boundary := by
  have h := closing_subset_boundary (V := (I.chainBefore ++ I.chainAfter).map ratPoint)
    (by simp [chainBefore])
  have e1 : lstPt ((I.chainBefore ++ I.chainAfter).map ratPoint) = ratPoint (d0 I.S I.H) := by
    rw [List.map_append, chainAfter_map,
      show I.chainBefore.map ratPoint ++ (((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) ::
        (I.upper.map ratPoint ++ [((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR)])) =
        (I.chainBefore.map ratPoint ++ ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) :: I.upper.map ratPoint)
          ++ [((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR)] by simp,
      lstPt_append_single, ratPoint_d0']
  have e2 : fstPt ((I.chainBefore ++ I.chainAfter).map ratPoint) = ratPoint (c0 I.S I.H) := by
    simp [chainBefore, fstPt]
  rw [e1, e2] at h
  exact h


theorem lstPt_append_ne {A B : List Point} (hB : B ≠ []) : lstPt (A ++ B) = lstPt B := by
  obtain ⟨B', b, rfl⟩ : ∃ B' b, B = B' ++ [b] :=
    ⟨B.dropLast, B.getLast hB, (List.dropLast_append_getLast hB).symm⟩
  rw [← List.append_assoc, lstPt_append_single, lstPt_append_single]

theorem fstPt_append_ne {A B : List Point} (hA : A ≠ []) : fstPt (A ++ B) = fstPt A := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  rfl

theorem Corridor.Input.Good.S_ge_k {I : Input} {N : ℚ} (hg : I.Good N) : (1000 : ℝ) ≤ I.S := by
  have := hg.S_ge_real; linarith

/-- **The pieces of a unit chain**: floor, lower wall, template, upper wall, upper corridor wall. -/
theorem unit_pieces {I : Input} {N : ℚ} (hg : I.Good N) (kd : Kind) {p : Point}
    (hp : p ∈ chainSet ((I.chainBefore ++ placedTmpl I kd ++ I.chainAfter).map ratPoint)) :
    p ∈ chainSet (I.chainBefore.map ratPoint) ∨
      p ∈ ArtGallery.segment (ratPoint (c1 I.S I.H))
        (tmplMap kd I.S I.H (S_ne_of hg.S_ge_k) (intPoint (tmplFst kd))) ∨
      p ∈ chainSet (tmplPlaced kd I.S I.H (S_ne_of hg.S_ge_k)) ∨
      p ∈ ArtGallery.segment (tmplMap kd I.S I.H (S_ne_of hg.S_ge_k) (intPoint (tmplLst kd)))
        (ratPoint (d1 I.S I.H)) ∨
      p ∈ chainSet (I.chainAfter.map ratPoint) := by
  have hS := hg.S_ge_k
  have hT0 : tmplPlaced kd I.S I.H (S_ne_of hS) ≠ [] := by
    intro h; have := tmplPlaced_length kd hS (H := (I.H : ℝ)); rw [h] at this; simp at this
  have hcb : I.chainBefore.map ratPoint ≠ [] := by simp [chainBefore]
  have hca : I.chainAfter.map ratPoint ≠ [] := by simp [chainAfter]
  rw [List.map_append, List.map_append, placedTmpl_map I kd hS,
    chainSet_append_two (by simp [chainBefore]) hca, chainSet_append_two hcb hT0,
    lstPt_append_ne hT0, tmplPlaced_lst kd hS, tmplPlaced_fst kd hS] at hp
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
theorem corridorClear_of {Q : Polygon} {I : Input} {N : ℚ} (hg : I.Good N) (kd : Kind)
    (hon : ∀ w ∈ Q.boundary, (I.S : ℝ) < w.1 → (I.H : ℝ) - 1 / 4 ≤ w.2 → w.2 ≤ (I.H : ℝ) + 3 / 2 →
      w ∈ chainSet ((I.chainBefore ++ placedTmpl I kd ++ I.chainAfter).map ratPoint)) :
    CorridorClear Q I := by
  have hS := hg.S_ge_k
  have he : 50 / (I.S : ℝ) ≤ 1 / 20 := by rw [div_le_iff₀ (by linarith)]; linarith
  intro w hwQ hwI
  obtain ⟨b1, b2, b3, b4⟩ := hg.poly_filled_box hwI
  by_cases hx : w.1 ≤ (I.S : ℝ)
  · exact I.entrance_subset (hg.filled_left hwI hx)
  push Not at hx
  rcases unit_pieces hg kd (hon w hwQ hx b3 b4) with h | h | h | h | h
  · exact chainSet_before_subset h
  · -- the lower wall reaches `x ≤ S + 2` only at `c1`
    have ha := tmplPlaced_box kd hS (tmplPlaced_fst_mem kd hS (H := (I.H : ℝ)))
    rcases seg_lt_or_left (α := -1) (β := 0) (c := -((I.S : ℝ) + 2))
      (by rw [ratPoint_c1']; simp) (by simp; linarith [ha.1]) h with h' | h'
    · exfalso; linarith
    · rw [h']
      apply chainSet_before_subset
      apply mem_chainSet_of_mem _ (by simp [chainBefore])
      simp [chainBefore]
  · exfalso
    have := (tmplPlaced_box kd hS h).1
    linarith
  · have ha := tmplPlaced_box kd hS (tmplPlaced_lst_mem kd hS (H := (I.H : ℝ)))
    rcases seg_lt_or_right (α := -1) (β := 0) (c := -((I.S : ℝ) + 2))
      (by simp; linarith [ha.1]) (by rw [ratPoint_d1']; simp) h with h' | h'
    · exfalso; linarith
    · rw [h']
      apply chainSet_after_subset
      apply mem_chainSet_of_mem _ (by simp [chainAfter])
      simp [chainAfter]
  · exact chainSet_after_subset h

/-! ### The template in template coordinates -/

theorem tmplFst_eq (k : Kind) : tmplFst k = (tmplV k).getD 0 (0, 0) := by
  cases k <;> rfl

theorem tmplLst_eq (k : Kind) : tmplLst k = (tmplV k).getD ((tmplV k).length - 1) (0, 0) := by
  unfold tmplLst
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The template chain in template coordinates is a chain of `φ⁻¹(Q)`. -/
theorem chainAt_of {Q : Polygon} (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) {aT : ℕ}
    (hfit : aT + (tmplV k).length ≤ Q.n)
    (hvtx : ∀ j < (tmplV k).length,
      Q.vtx (aT + j) = tmplMap k S H (S_ne_of hS) (intPoint ((tmplV k).getD j (0, 0)))) :
    Tmpl.ChainAt (Hardening.Invariance.mapPoly (tmplMap k S H (S_ne_of hS)).symm Q) (tmplV k) aT := by
  intro j hj
  rw [Hardening.Invariance.n_mapPoly, Nat.mod_eq_of_lt (by omega),
    Hardening.Invariance.vtx_mapPoly _ _ (by omega), hvtx j hj, AffineEquiv.symm_apply_apply]

/-- **Separation of the template** (the geometric content of `Tmpl.SepAt`): inside the box
`|x|, |y| < 60 D`, a point of a non-chain edge of `φ⁻¹(Q)` lies on a channel wall. -/
theorem sepWalls_of {Q : Polygon} {I : Input} {N : ℚ} (hg : I.Good N) (k : Kind) (hQs : Q.Simple)
    {aT : ℕ} (ha1 : 1 ≤ aT) (hfit : aT + (tmplV k).length ≤ Q.n)
    (hvtx : ∀ j < (tmplV k).length,
      Q.vtx (aT + j) = tmplMap k I.S I.H (S_ne_of hg.S_ge_k) (intPoint ((tmplV k).getD j (0, 0))))
    (hon : ∀ z ∈ Q.boundary, (I.S : ℝ) + 2 < z.1 → (I.H : ℝ) - 1 - 1 / 10 < z.2 →
      z.2 < (I.H : ℝ) - 1 + 1 / 10 →
      z ∈ chainSet ((I.chainBefore ++ placedTmpl I k ++ I.chainAfter).map ratPoint)) :
    ∀ i < (Hardening.Invariance.mapPoly (tmplMap k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).n,
      (∀ j, j + 1 < (tmplV k).length →
        (aT + j) % (Hardening.Invariance.mapPoly (tmplMap k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).n ≠ i) →
      ∀ x ∈ (Hardening.Invariance.mapPoly (tmplMap k I.S I.H (S_ne_of hg.S_ge_k)).symm Q).edge i,
        |x.1| < 60 * (tmplD k : ℝ) → |x.2| < 60 * (tmplD k : ℝ) →
        x ∈ ArtGallery.segment (intPoint (tmplFst k))
            ((tmplMap k I.S I.H (S_ne_of hg.S_ge_k)).symm (ratPoint (c1 I.S I.H))) ∨
          x ∈ ArtGallery.segment (intPoint (tmplLst k))
            ((tmplMap k I.S I.H (S_ne_of hg.S_ge_k)).symm (ratPoint (d1 I.S I.H))) := by
  have hS := hg.S_ge_k
  intro i hi hnc x hx hx1 hx2
  rw [Hardening.Invariance.n_mapPoly] at hi hnc
  rw [Hardening.Invariance.edge_mapPoly _ _ hi] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzQ : z ∈ Q.boundary := ⟨i, hi, hz⟩
  -- position of `z`
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : (0 : ℝ) < (I.S : ℝ) := by linarith
  have hzc : z.1 = (I.S : ℝ) + 3 + ((tmplMap k I.S I.H (S_ne_of hS)).symm z).1 / ((tmplD k : ℝ) * I.S) ∧
      z.2 = (I.H : ℝ) - 1 + ((tmplMap k I.S I.H (S_ne_of hS)).symm z).2 / ((tmplD k : ℝ) * I.S) := by
    have e := tmplMap_apply k (S_ne_of hS) (H := (I.H : ℝ)) ((tmplMap k I.S I.H (S_ne_of hS)).symm z)
    rw [AffineEquiv.apply_symm_apply] at e
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have hsmall : ∀ t : ℝ, |t| < 60 * (tmplD k : ℝ) → |t / ((tmplD k : ℝ) * I.S)| < 1 / 10 := by
    intro t ht
    have hp : (0 : ℝ) < (tmplD k : ℝ) * I.S := mul_pos hD hS0
    rw [abs_div, abs_of_pos hp, div_lt_iff₀ hp]
    nlinarith
  have h1 := hsmall _ hx1
  have h2 := hsmall _ hx2
  rw [abs_lt] at h1 h2
  have hzx : (I.S : ℝ) + 2 < z.1 := by linarith [hzc.1]
  have hzu := hon z hzQ hzx (by linarith [hzc.2]) (by linarith [hzc.2])
  have hT : (tmplPlaced k I.S I.H (S_ne_of hS)).length = (tmplV k).length := by simp [tmplPlaced]
  have hTget : ∀ j < (tmplV k).length,
      (tmplPlaced k I.S I.H (S_ne_of hS)).getD j (0, 0) = Q.vtx (aT + j) := by
    intro j hj
    rw [hvtx j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hT]; exact hj),
      Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    simp [tmplPlaced]
  have hinj := hQs.2.1
  rcases unit_pieces hg k hzu with h | h | h | h | h
  · exfalso
    have := (hg.poly_filled_box (Or.inl (chainSet_before_subset h))).2.1
    linarith
  · left
    have := Hardening.Invariance.image_segment' (tmplMap k I.S I.H (S_ne_of hS)).symm (ratPoint (c1 I.S I.H))
      ((tmplMap k I.S I.H (S_ne_of hS)) (intPoint (tmplFst k)))
    rw [AffineEquiv.symm_apply_apply] at this
    rw [Geometry.segment_comm, ← this]
    exact ⟨z, h, rfl⟩
  · -- `z` is on the template chain: it must be one of its two ends
    obtain ⟨j, hj, hzj⟩ := mem_chainSet_iff.1 h
    rw [hT] at hj
    have hedge : edgeSeg (tmplPlaced k I.S I.H (S_ne_of hS)) j = Q.edge (aT + j) := by
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
    have fst_case : z = Q.vtx aT → (tmplMap k I.S I.H (S_ne_of hS)).symm z ∈ ArtGallery.segment (intPoint (tmplFst k))
        ((tmplMap k I.S I.H (S_ne_of hS)).symm (ratPoint (c1 I.S I.H))) := by
      intro e
      rw [e, show aT = aT + 0 by rfl, hvtx 0 (by omega), AffineEquiv.symm_apply_apply,
        ← tmplFst_eq]
      exact Geometry.left_mem_segment _ _
    have lst_case : z = Q.vtx (aT + ((tmplV k).length - 1)) → (tmplMap k I.S I.H (S_ne_of hS)).symm z ∈ ArtGallery.segment
        (intPoint (tmplLst k)) ((tmplMap k I.S I.H (S_ne_of hS)).symm (ratPoint (d1 I.S I.H))) := by
      intro e
      rw [e, hvtx _ (by omega), AffineEquiv.symm_apply_apply, ← tmplLst_eq]
      exact Geometry.left_mem_segment _ _
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (hinj _ _ hi (by omega) (e1 ▸ e2)) hne
    · have hi' := hinj _ _ hi (by omega) (e1 ▸ e2)
      by_cases hj2 : j + 1 + 1 < (tmplV k).length
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
    have := Hardening.Invariance.image_segment' (tmplMap k I.S I.H (S_ne_of hS)).symm ((tmplMap k I.S I.H (S_ne_of hS)) (intPoint (tmplLst k)))
      (ratPoint (d1 I.S I.H))
    rw [AffineEquiv.symm_apply_apply] at this
    rw [← this]
    exact ⟨z, h, rfl⟩
  · exfalso
    have := (hg.poly_filled_box (Or.inl (chainSet_after_subset h))).2.1
    linarith

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

omit hQ hm in
/-- Unit chains of the side are unit chains `m'` of the list. -/
theorem SideAt.mem_sideChains {f : List Point} (hf : f ∈ sideChainsR n k us) :
    ∃ m', ∃ hm' : m' < us.length, f = (unitChain n k m' (us[m']'hm')).map ratPoint := by
  simp only [sideChainsR, List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hc
  have hm'' : m' < us.length := by rw [length_unitChains] at hm'; exact hm'
  exact ⟨m', hm'', by rw [getElem_unitChains, Nat.zero_add]⟩

/-- Points of the boundary of `Q` right of `x = S`, at the height of unit `m`
(`|y − (H − 1)| < 1`, or within `[H − 1/4, H + 3/2]`), lie on the chain of unit `m`. -/
theorem SideAt.on_unit {z : Point} (hz : z ∈ Q.boundary) (hzx : (S n k : ℝ) < z.1)
    (hzy : (S n k : ℝ) + 3 * m - 0.4 ≤ z.2 ∧ z.2 ≤ (S n k : ℝ) + 3 * m + 2.6) :
    z ∈ chainSet ((unitChain n k m (us[m]'hm)).map ratPoint) := by
  rcases hQ.bdry z hz with h | ⟨f, hf, hzf⟩
  · exact absurd h (not_le.2 hzx)
  obtain ⟨m', hm', rfl⟩ := SideAt.mem_sideChains hf
  have u := unitChain_feature (u := us[m']'hm') (m := m') (hQ.ok _ (List.getElem_mem hm'))
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

theorem SideAt.cast_S : (((unitInput n k m (us[m]'hm)).S : ℚ) : ℝ) = (S n k : ℝ) := by
  simp [unitInput]

theorem SideAt.cast_H : (((unitInput n k m (us[m]'hm)).H : ℚ) : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
  simp [unitInput, Sec5.unitH]

/-- **Clearance of the corridor of unit `m`** (the hypothesis of `Good.poly_subset`). -/
theorem SideAt.corridorClear : CorridorClear Q (unitInput n k m (us[m]'hm)) := by
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  refine corridorClear_of (hQ.good hm) (us[m]'hm).kind (fun w hw hx hy1 hy2 => ?_)
  rw [eS] at hx
  rw [eH] at hy1 hy2
  exact hQ.on_unit hm hw hx ⟨by linarith, by linarith⟩

/-- The index of the first template vertex of unit `m`. -/
abbrev SideAt.tStart (_hQ : SideAt Q n k us st) : ℕ :=
  unitStart n k us st m + (unitInput n k m (us[m]'hm)).chainBefore.length

theorem SideAt.tmpl_vtx : ∀ j < (tmplV (us[m]'hm).kind).length,
    Q.vtx (hQ.tStart hm + j) = tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S
      (unitInput n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)
      (intPoint ((tmplV (us[m]'hm).kind).getD j (0, 0))) := by
  intro j hj
  have hg := hQ.good hm
  have hlp : (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplV (us[m]'hm).kind).length := by simp [placedTmpl]
  have hlen : (unitChain n k m (us[m]'hm)).length =
      (unitInput n k m (us[m]'hm)).chainBefore.length +
        (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length +
        (unitInput n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChain, Nat.add_assoc]
  rw [SideAt.tStart, Nat.add_assoc, hQ.vtx m hm _ (by omega)]
  have e1 : (unitChain n k m (us[m]'hm)).getD
      ((unitInput n k m (us[m]'hm)).chainBefore.length + j) 0 =
      (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).getD j 0 := by
    simp only [unitChain, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by omega)]
  rw [e1]
  have e2 := congrArg (fun l => l.getD j (0, 0)) (placedTmpl_map (unitInput n k m (us[m]'hm))
    (us[m]'hm).kind hg.S_ge_k)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)] at e2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [Option.map_some, Option.getD_some] at e2
  rw [e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [tmplPlaced]; omega),
    Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  simp [tmplPlaced]

/-- **The template chain of unit `m` in template coordinates** (`Tmpl.ChainAt`). -/
theorem SideAt.chainAt :
    Tmpl.ChainAt (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind
      (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k)).symm Q) (tmplV (us[m]'hm).kind) (hQ.tStart hm) := by
  have hend := hQ.end_le hm
  have hlen : (unitChain n k m (us[m]'hm)).length =
      (unitInput n k m (us[m]'hm)).chainBefore.length +
        (tmplV (us[m]'hm).kind).length + (unitInput n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChain, placedTmpl, Nat.add_assoc]
  exact chainAt_of _ (hQ.good hm).S_ge_k (by simp only [SideAt.tStart]; omega) (hQ.tmpl_vtx hm)

/-- **Separation of the template of unit `m`**: inside the box `|x|, |y| < 60 D` the non-chain
edges of `φ⁻¹(Q)` only meet the two channel walls. -/
theorem SideAt.sep_walls :
    ∀ i < (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S
      (unitInput n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).n,
      (∀ j, j + 1 < (tmplV (us[m]'hm).kind).length → (hQ.tStart hm + j) %
        (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S
          (unitInput n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).n ≠ i) →
      ∀ x ∈ (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S
        (unitInput n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q).edge i,
        |x.1| < 60 * (tmplD (us[m]'hm).kind : ℝ) → |x.2| < 60 * (tmplD (us[m]'hm).kind : ℝ) →
        x ∈ ArtGallery.segment (intPoint (tmplFst (us[m]'hm).kind))
            ((tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
              (S_ne_of (hQ.good hm).S_ge_k)).symm
              (ratPoint (c1 (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H))) ∨
          x ∈ ArtGallery.segment (intPoint (tmplLst (us[m]'hm).kind))
            ((tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
              (S_ne_of (hQ.good hm).S_ge_k)).symm
              (ratPoint (d1 (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H))) := by
  have hend := hQ.end_le hm
  have hlen : (unitChain n k m (us[m]'hm)).length =
      (unitInput n k m (us[m]'hm)).chainBefore.length +
        (tmplV (us[m]'hm).kind).length + (unitInput n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChain, placedTmpl, Nat.add_assoc]
  have hcb : 2 ≤ (unitInput n k m (us[m]'hm)).chainBefore.length := by simp [chainBefore]
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  refine sepWalls_of (hQ.good hm) _ hQ.simple (by simp only [SideAt.tStart]; omega)
    (by simp only [SideAt.tStart]; omega) (hQ.tmpl_vtx hm) (fun z hz hzx hy1 hy2 => ?_)
  rw [eS] at hzx
  rw [eH] at hy1 hy2
  exact hQ.on_unit hm hz (by linarith) ⟨by linarith, by linarith⟩

end Unit

end ArtGallery.Sec5

end
