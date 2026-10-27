module

public import ArtGallery.Hardness.BP.CoverUnitLocal
public import ArtGallery.Hardness.Sec5.CoverRegion

/-!
# Boundary-point variant, coverage: the vertical lines of the sides, special edges

As `Sec5/CoverSide.lean` and `Sec5/CoverVtx.lean`:

* for a side `SideAtBP Q n k us st` whose chains are preceded by the vertex `(S, S)` and followed
  by the vertex `(S, top)`, every point `(S, y)`, `S ≤ y ≤ top`, lies on the boundary of `Q` or on
  the entrance of a unit (`side_vertical`);
* the hexagon edges `w_r v_r`, `t_r t_l`, `v_l w_l` are edges of `polyCBP` (`diagR_bdry`,
  `top_bdry`, `diagL_bdry`), and the two vertical unit lines satisfy the hypotheses of
  `side_vertical` (`right_vertical` in `polyCBP`, `left_vertical` in the mirrored `polyMBP`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.CoverM

open ArtGallery Set Polygon ArtGallery.Sec5
open ArtGallery.Sec5.CoverM (mem_vertical mem_vertical' sS sTop sXL pwR pvR ptR ptL pvL pwL
  edge_of_vtx edge_of_vtx_last vtx_mem_bdry)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
include hQ

theorem side_c0 {m : ℕ} (hm : m < us.length) :
    Q.vtx (unitStartBP n k us st m) = ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1) := by
  have hl := CoverU.unitChain_len hQ hm
  have hcb := CoverU.cb_pos hQ hm
  have hv := hQ.vtx m hm 0 (by omega)
  rw [Nat.add_zero] at hv
  rw [hv]
  have e : (unitChainBP n k m (us[m]'hm)).getD 0 0 =
      c0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H := by
    simp only [unitChainBP, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by omega), chainBefore_getD_zero]
  rw [e, ratPoint_c0', hQ.cast_S hm, hQ.cast_H hm]

theorem side_d0 {m : ℕ} (hm : m < us.length) :
    Q.vtx (unitStartBP n k us st (m + 1) - 1) = ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1 +
      2 * (unitInputBP n k m (us[m]'hm)).rhoR) := by
  have hl := CoverU.unitChain_len hQ hm
  have hca := CoverU.ca_pos hQ hm
  rw [unitStartBP_succ hm]
  have hv := hQ.vtx m hm ((unitChainBP n k m (us[m]'hm)).length - 1) (by omega)
  rw [show unitStartBP n k us st m + (unitChainBP n k m (us[m]'hm)).length - 1 =
    unitStartBP n k us st m + ((unitChainBP n k m (us[m]'hm)).length - 1) by omega, hv]
  have hlp : (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplVBP (us[m]'hm).kind).length := by simp [placedTmplBP]
  have e : (unitChainBP n k m (us[m]'hm)).getD ((unitChainBP n k m (us[m]'hm)).length - 1) 0 =
      d0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H := by
    rw [hl]
    simp only [unitChainBP]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, hlp]; omega)]
    simp only [List.length_append, hlp]
    rw [show (unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length +
      (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 -
      ((unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length) =
      (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 by omega, chainAfter_getD_last]
  rw [e, ratPoint_d0', hQ.cast_S hm, hQ.cast_H hm]

theorem rhoR_eq' {m m' : ℕ} (hm : m < us.length) (hm' : m' < us.length) :
    (unitInputBP n k m (us[m]'hm)).rhoR = (unitInputBP n k m' (us[m']'hm')).rhoR := by
  simp [rhoR, unitInputBP]

theorem side_start_ge (m : ℕ) : st ≤ unitStartBP n k us st m := by
  simp [unitStartBP]

/-- **The vertical line of a side.** -/
theorem side_vertical (hst : 1 ≤ st) {top : ℝ}
    (hv0 : Q.vtx (st - 1) = ((S n k : ℝ), (S n k : ℝ)))
    (hvt : Q.vtx (unitStartBP n k us st us.length) = ((S n k : ℝ), top))
    (hlt : unitStartBP n k us st us.length < Q.n) {y : ℝ} (hy1 : (S n k : ℝ) ≤ y)
    (hy2 : y ≤ top) :
    ((S n k : ℝ), y) ∈ Q.boundary ∨ ∃ m, ∃ hm : m < us.length,
      ((S n k : ℝ), y) ∈ (unitInputBP n k m (us[m]'hm)).entrance := by
  -- the vertical edge ending at the start of unit `m` (or at `t`)
  set hi : ℕ → ℝ := fun m => if m < us.length then (S n k : ℝ) + 3 * m + 1 else top with hhi
  have hvhi : ∀ m ≤ us.length, Q.vtx (unitStartBP n k us st m) = ((S n k : ℝ), hi m) := by
    intro m hm
    rcases lt_or_eq_of_le hm with h | rfl
    · rw [side_c0 hQ h]; simp [hhi, h]
    · rw [hvt]; simp [hhi]
  have hedge : ∀ m ≤ us.length, ∀ y', ((S n k : ℝ), y') ∈ ArtGallery.segment
      (Q.vtx (unitStartBP n k us st m - 1)) (Q.vtx (unitStartBP n k us st m)) →
      ((S n k : ℝ), y') ∈ Q.boundary := by
    intro m hm y' hy'
    have h1 := side_start_ge hQ (k := k) (n := n) (us := us) m
    have h2 := unitStartBP_mono (n := n) (k := k) (us := us) (st := st) hm
    refine ⟨unitStartBP n k us st m - 1, by omega, ?_⟩
    rw [Polygon.edge, show (unitStartBP n k us st m - 1 + 1) % Q.n = unitStartBP n k us st m by
      rw [Nat.mod_eq_of_lt (by omega)]; omega]
    exact hy'
  -- induction over the units
  have claim : ∀ m ≤ us.length, ∀ y', (S n k : ℝ) ≤ y' → y' ≤ hi m →
      ((S n k : ℝ), y') ∈ Q.boundary ∨ ∃ m', ∃ hm : m' < us.length,
        ((S n k : ℝ), y') ∈ (unitInputBP n k m' (us[m']'hm)).entrance := by
    intro m
    induction m with
    | zero =>
      intro _ y' h1 h2
      left
      refine hedge 0 (Nat.zero_le _) y' ?_
      rw [show unitStartBP n k us st 0 = st by simp [unitStartBP], hv0,
        show st = unitStartBP n k us st 0 by simp [unitStartBP], hvhi 0 (Nat.zero_le _)]
      exact mem_vertical h1 h2
    | succ m ih =>
      intro hm y' h1 h2
      have hmL : m < us.length := by omega
      by_cases h3 : y' ≤ hi m
      · exact ih (by omega) y' h1 h3
      push Not at h3
      have hHm : hi m = (S n k : ℝ) + 3 * m + 1 := by simp [hhi, hmL]
      rw [hHm] at h3
      have hρ := (hQ.good hmL).rhoR_pos
      by_cases h4 : y' ≤ (S n k : ℝ) + 3 * m + 1 + 2 * (unitInputBP n k m (us[m]'hmL)).rhoR
      · right
        refine ⟨m, hmL, ?_⟩
        rw [Corridor.Input.entrance, ratPoint_d0', ratPoint_c0', hQ.cast_S hmL, hQ.cast_H hmL]
        exact mem_vertical' h3.le h4
      · push Not at h4
        left
        refine hedge (m + 1) hm y' ?_
        rw [side_d0 hQ hmL, hvhi (m + 1) hm]
        exact mem_vertical h4.le h2
  exact claim us.length le_rfl y hy1 (by simp [hhi]; exact hy2)

end Side

/-! ### Special vertices and edges of the global polygon -/

variable {Φ : List ETRINV.Constraint} {n : ℕ}

theorem unitStart_end (k st : ℕ) (us : List UnitSpec) :
    unitStartBP n k us st us.length = st + ((unitChainsBP n k 0 us).flatten).length := by
  simp only [unitStartBP]
  rw [show us.length = (unitChainsBP n k 0 us).length from (length_unitChainsBP _ _ _ _).symm,
    List.take_length, List.length_flatten]

section
variable (hn : 0 < n)
include hn

/-- The right flatten of the unit chains. -/
abbrev rFl (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).1).flatten

/-- The left flatten of the unit chains. -/
abbrev lFl (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).2).flatten

theorem polyC_eq_right : polyCBP Φ n = Polygon.mk (((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++
    rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++ [vL n (numC Φ)])).map ratPoint) := by
  rw [polyCBP, constructBP_right hn]

theorem polyC_n : (polyCBP Φ n).n = (bottomWallBP n Φ).length + 2 + (rFl Φ n).length + 2 +
    (leftPartBP n Φ).length + 1 := by
  rw [polyC_eq_right hn]
  simp only [Polygon.n, List.length_map, List.length_append, List.length_cons, List.length_nil]
  omega

theorem vtx_wR : (polyCBP Φ n).vtx (bottomWallBP n Φ).length = pwR n := by
  have := vtx_split (A := bottomWallBP n Φ) (C := [wR n, vR n (numC Φ)])
    (B := rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++ [vL n (numC Φ)]))
    (i := 0) (by simp)
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  rw [Nat.add_zero] at this
  rw [this]; simp [ratPoint, wR, pwR]

theorem vtx_vR : (polyCBP Φ n).vtx ((bottomWallBP n Φ).length + 1) = pvR Φ n := by
  have := vtx_split (A := bottomWallBP n Φ) (C := [wR n, vR n (numC Φ)])
    (B := rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++ [vL n (numC Φ)]))
    (i := 1) (by simp)
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  rw [this]; simp [ratPoint, vR, pvR, sS]

theorem vtx_tRL (i : ℕ) (hi : i < 2) : (polyCBP Φ n).vtx ((bottomWallBP n Φ).length + 2 +
    (rFl Φ n).length + i) = ratPoint ([tR n (numC Φ), tL n (numC Φ)].getD i 0) := by
  have := vtx_split (A := (bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n)
    (C := [tR n (numC Φ), tL n (numC Φ)]) (B := leftPartBP n Φ ++ [vL n (numC Φ)]) (i := i)
    (by simpa using hi)
  have hA : ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n).length =
      (bottomWallBP n Φ).length + 2 + (rFl Φ n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hA] at this
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  exact this

theorem vtx_tR : (polyCBP Φ n).vtx (unitStartBP n (numC Φ) (unitSpecs n Φ).1
    ((bottomWallBP n Φ).length + 2) (unitSpecs n Φ).1.length) = ptR Φ n := by
  rw [unitStart_end, ← Nat.add_zero ((bottomWallBP n Φ).length + 2 + _), vtx_tRL hn 0 (by omega)]
  simp [ratPoint, tR, ptR, sTop, sS]

theorem vtx_tL : (polyCBP Φ n).vtx (unitStartBP n (numC Φ) (unitSpecs n Φ).1
    ((bottomWallBP n Φ).length + 2) (unitSpecs n Φ).1.length + 1) = ptL Φ n := by
  rw [unitStart_end, vtx_tRL hn 1 (by omega)]
  simp [ratPoint, tL, ptL, sTop, sS, XL, xMirror, sXL]

theorem vtx_vL : (polyCBP Φ n).vtx ((polyCBP Φ n).n - 1) = pvL Φ n := by
  have := vtx_split (A := (bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n ++
      ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ)) (C := [vL n (numC Φ)]) (B := [])
    (i := 0) (by simp)
  have hA : ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n ++
      ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ)).length + 0 = (polyCBP Φ n).n - 1 := by
    rw [polyC_n hn]; simp; omega
  rw [hA] at this
  rw [polyC_eq_right hn]
  rw [polyC_eq_right hn] at this
  simp only [List.append_assoc, List.append_nil, List.cons_append, List.nil_append] at this ⊢
  rw [this]; simp [ratPoint, vL, pvL, sS, XL, xMirror, sXL]

theorem bottomWall_ne : bottomWallBP n Φ ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_bottomWallBP, List.length_nil] at this
  have h1 := startBP_succ (n := n) (Φ := Φ) 0
  have h2 := startBP_mono (n := n) (Φ := Φ) (show 0 + 1 ≤ 4 * n by omega)
  have h3 := length_pocketBPRel (slotOne n Φ 0)
  omega

theorem vtx_wL : (polyCBP Φ n).vtx 0 = pwL := by
  have h := bottomBP_fst hn Φ
  obtain ⟨b, B', hB'⟩ := List.exists_cons_of_ne_nil (bottomWall_ne (Φ := Φ) hn)
  rw [hB'] at h
  rw [polyC_eq_right hn, Irrational.vtx_map_ratPoint, hB']
  simp only [List.cons_append, List.getD_cons_zero]
  simp only [List.cons_append, List.map_cons] at h
  exact h

/-- The right diagonal `w_r v_r` is an edge. -/
theorem diagR_bdry : ArtGallery.segment (pwR n) (pvR Φ n) ⊆ (polyCBP Φ n).boundary :=
  edge_of_vtx (by rw [polyC_n hn]; omega) (vtx_wR hn) (vtx_vR hn)

/-- The top `t_r t_l` is an edge. -/
theorem top_bdry : ArtGallery.segment (ptR Φ n) (ptL Φ n) ⊆ (polyCBP Φ n).boundary := by
  refine edge_of_vtx ?_ (vtx_tR hn) (vtx_tL hn)
  rw [unitStart_end, polyC_n hn]; simp only [rFl]; omega

/-- The left diagonal `v_l w_l` is an edge (the closing edge). -/
theorem diagL_bdry : ArtGallery.segment (pvL Φ n) pwL ⊆ (polyCBP Φ n).boundary :=
  edge_of_vtx_last (by rw [polyC_n hn]; omega) (vtx_vL hn) (vtx_wL hn)

/-- **The right vertical line** `x = S`: boundary or an entrance of a right unit. -/
theorem right_vertical (hΦ : ∀ c ∈ Φ, c.VarsLt n) {y : ℝ} (hy1 : sS Φ n ≤ y)
    (hy2 : y ≤ sTop Φ n) :
    (sS Φ n, y) ∈ (polyCBP Φ n).boundary ∨ ∃ m, ∃ hm : m < (unitSpecs n Φ).1.length,
      (sS Φ n, y) ∈ (unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m]'hm)).entrance := by
  have hQ := rightSideBP hΦ hn
  have hv0 : (polyCBP Φ n).vtx ((bottomWallBP n Φ).length + 2 - 1) =
      ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) := by
    rw [show (bottomWallBP n Φ).length + 2 - 1 = (bottomWallBP n Φ).length + 1 by omega, vtx_vR hn]
    rfl
  have hlt : unitStartBP n (numC Φ) (unitSpecs n Φ).1 ((bottomWallBP n Φ).length + 2)
      (unitSpecs n Φ).1.length < (polyCBP Φ n).n := by
    rw [unitStart_end, polyC_n hn]; simp only [rFl]; omega
  exact side_vertical hQ (by omega) hv0 (vtx_tR hn) hlt hy1 hy2

/-! ### The mirrored polygon -/

theorem polyM_eq' : polyMBP Φ n = Polygon.mk ((([mirror n (vL n (numC Φ))] ++ lFl Φ n) ++
    ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
      ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ).reverse.map (mirror n)))).map
        ratPoint) := by
  rw [polyMBP_eq, constructBP_mirror hn]

theorem polyM_n : (polyMBP Φ n).n = (polyCBP Φ n).n := by
  simp [polyMBP, Vis.Cert.mirrorPoly, Vis.Cert.revPoly, Hardening.Invariance.mapPoly, Polygon.n]

theorem polyM_bdry : (polyMBP Φ n).boundary = mirrorR n '' (polyCBP Φ n).boundary := by
  simp only [polyMBP, Vis.Cert.mirrorPoly, Vis.Cert.boundary_revPoly,
    Hardening.Invariance.boundary_mapPoly]
  rfl

theorem polyM_vtx0 : (polyMBP Φ n).vtx 0 = ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) := by
  rw [polyM_eq' hn, Irrational.vtx_map_ratPoint]
  simp [ratPoint, mirror, vL, XL, xMirror]

theorem polyM_vtx_t : (polyMBP Φ n).vtx (1 + (lFl Φ n).length) =
    ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
  have := vtx_split (A := [mirror n (vL n (numC Φ))] ++ lFl Φ n)
    (C := [mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))])
    (B := (bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ).reverse.map (mirror n))
    (i := 0) (by simp)
  have hA : ([mirror n (vL n (numC Φ))] ++ lFl Φ n).length + 0 = 1 + (lFl Φ n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [hA] at this
  rw [polyM_eq' hn]
  simp only [List.append_assoc] at this ⊢
  rw [this]; simp [ratPoint, mirror, tL, XL, xMirror]

/-- **The left vertical line** (working frame of the left units, in `polyMBP`). -/
theorem left_vertical (hΦ : ∀ c ∈ Φ, c.VarsLt n) {y : ℝ} (hy1 : sS Φ n ≤ y)
    (hy2 : y ≤ sTop Φ n) :
    (sS Φ n, y) ∈ (polyMBP Φ n).boundary ∨ ∃ m, ∃ hm : m < (unitSpecs n Φ).2.length,
      (sS Φ n, y) ∈ (unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m]'hm)).entrance := by
  have hQ := leftSideBP hΦ hn
  have hv0 : (polyMBP Φ n).vtx (1 - 1) = ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) :=
    polyM_vtx0 hn
  have hvt : (polyMBP Φ n).vtx (unitStartBP n (numC Φ) (unitSpecs n Φ).2 1 (unitSpecs n Φ).2.length) =
      ((S n (numC Φ) : ℝ), sTop Φ n) := by
    rw [unitStart_end, polyM_vtx_t hn]; rfl
  have hlt : unitStartBP n (numC Φ) (unitSpecs n Φ).2 1 (unitSpecs n Φ).2.length < (polyMBP Φ n).n := by
    rw [unitStart_end, polyM_eq' hn]
    simp only [Polygon.n, List.length_map, List.length_append, List.length_cons, List.length_nil,
      lFl]
    omega
  exact side_vertical hQ le_rfl hv0 hvt hlt hy1 hy2

end

end ArtGallery.BP.CoverM

end
