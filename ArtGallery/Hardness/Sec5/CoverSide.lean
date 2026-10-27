module

public import ArtGallery.Hardness.Sec5.CoverHex

/-!
# Section 5, sufficiency (vi): the vertical line of a side

For a side `SideAt Q n k us st` whose chains are preceded by the vertex `(S, S)` and followed by
the vertex `(S, top)`, every point `(S, y)`, `S ≤ y ≤ top`, lies on the boundary of `Q` (on a
vertical edge between two units) or on the entrance of a unit (`side_vertical`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.CoverM

open ArtGallery Set Polygon
open Corridor (Input CorridorAt c0 c1 d0 d1)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- A point of a vertical segment. -/
theorem mem_vertical {X a b y : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) :
    (X, y) ∈ ArtGallery.segment (X, a) (X, b) := by
  rcases eq_or_lt_of_le (h1.trans h2) with h | h
  · have : y = a := by linarith
    subst this; rw [← h]; exact Geometry.left_mem_segment _ _
  · refine Geometry.mem_segment_iff_lerp.2 ⟨(y - a) / (b - a), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    simp only [Geometry.lerp]
    ext
    · simp
    · simp only; field_simp; ring

theorem mem_vertical' {X a b y : ℝ} (h1 : b ≤ y) (h2 : y ≤ a) :
    (X, y) ∈ ArtGallery.segment (X, a) (X, b) := by
  rw [Geometry.segment_comm]; exact mem_vertical h1 h2

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
include hQ

theorem side_c0 {m : ℕ} (hm : m < us.length) :
    Q.vtx (unitStart n k us st m) = ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1) := by
  have hl := CoverU.unitChain_len hQ hm
  have hcb := CoverU.cb_pos hQ hm
  have hv := hQ.vtx m hm 0 (by omega)
  rw [Nat.add_zero] at hv
  rw [hv]
  have e : (unitChain n k m (us[m]'hm)).getD 0 0 =
      c0 (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H := by
    simp only [unitChain, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by omega), chainBefore_getD_zero]
  rw [e, ratPoint_c0', hQ.cast_S hm, hQ.cast_H hm]

theorem side_d0 {m : ℕ} (hm : m < us.length) :
    Q.vtx (unitStart n k us st (m + 1) - 1) = ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1 +
      2 * (unitInput n k m (us[m]'hm)).rhoR) := by
  have hl := CoverU.unitChain_len hQ hm
  have hca := CoverU.ca_pos hQ hm
  rw [unitStart_succ hm]
  have hv := hQ.vtx m hm ((unitChain n k m (us[m]'hm)).length - 1) (by omega)
  rw [show unitStart n k us st m + (unitChain n k m (us[m]'hm)).length - 1 =
    unitStart n k us st m + ((unitChain n k m (us[m]'hm)).length - 1) by omega, hv]
  have hlp : (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplV (us[m]'hm).kind).length := by simp [placedTmpl]
  have e : (unitChain n k m (us[m]'hm)).getD ((unitChain n k m (us[m]'hm)).length - 1) 0 =
      d0 (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H := by
    rw [hl]
    simp only [unitChain]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, hlp]; omega)]
    simp only [List.length_append, hlp]
    rw [show (unitInput n k m (us[m]'hm)).chainBefore.length + (tmplV (us[m]'hm).kind).length +
      (unitInput n k m (us[m]'hm)).chainAfter.length - 1 -
      ((unitInput n k m (us[m]'hm)).chainBefore.length + (tmplV (us[m]'hm).kind).length) =
      (unitInput n k m (us[m]'hm)).chainAfter.length - 1 by omega, chainAfter_getD_last]
  rw [e, ratPoint_d0', hQ.cast_S hm, hQ.cast_H hm]

theorem rhoR_eq' {m m' : ℕ} (hm : m < us.length) (hm' : m' < us.length) :
    (unitInput n k m (us[m]'hm)).rhoR = (unitInput n k m' (us[m']'hm')).rhoR := by
  simp [rhoR, unitInput]

theorem side_start_ge (m : ℕ) : st ≤ unitStart n k us st m := by
  simp [unitStart]

/-- **The vertical line of a side.** -/
theorem side_vertical (hst : 1 ≤ st) {top : ℝ}
    (hv0 : Q.vtx (st - 1) = ((S n k : ℝ), (S n k : ℝ)))
    (hvt : Q.vtx (unitStart n k us st us.length) = ((S n k : ℝ), top))
    (hlt : unitStart n k us st us.length < Q.n) {y : ℝ} (hy1 : (S n k : ℝ) ≤ y)
    (hy2 : y ≤ top) :
    ((S n k : ℝ), y) ∈ Q.boundary ∨ ∃ m, ∃ hm : m < us.length,
      ((S n k : ℝ), y) ∈ (unitInput n k m (us[m]'hm)).entrance := by
  -- the vertical edge ending at the start of unit `m` (or at `t`)
  set hi : ℕ → ℝ := fun m => if m < us.length then (S n k : ℝ) + 3 * m + 1 else top with hhi
  have hvhi : ∀ m ≤ us.length, Q.vtx (unitStart n k us st m) = ((S n k : ℝ), hi m) := by
    intro m hm
    rcases lt_or_eq_of_le hm with h | rfl
    · rw [side_c0 hQ h]; simp [hhi, h]
    · rw [hvt]; simp [hhi]
  have hedge : ∀ m ≤ us.length, ∀ y', ((S n k : ℝ), y') ∈ ArtGallery.segment
      (Q.vtx (unitStart n k us st m - 1)) (Q.vtx (unitStart n k us st m)) →
      ((S n k : ℝ), y') ∈ Q.boundary := by
    intro m hm y' hy'
    have h1 := side_start_ge hQ (k := k) (n := n) (us := us) m
    have h2 := unitStart_mono (n := n) (k := k) (us := us) (st := st) hm
    refine ⟨unitStart n k us st m - 1, by omega, ?_⟩
    rw [Polygon.edge, show (unitStart n k us st m - 1 + 1) % Q.n = unitStart n k us st m by
      rw [Nat.mod_eq_of_lt (by omega)]; omega]
    exact hy'
  -- induction over the units
  have claim : ∀ m ≤ us.length, ∀ y', (S n k : ℝ) ≤ y' → y' ≤ hi m →
      ((S n k : ℝ), y') ∈ Q.boundary ∨ ∃ m', ∃ hm : m' < us.length,
        ((S n k : ℝ), y') ∈ (unitInput n k m' (us[m']'hm)).entrance := by
    intro m
    induction m with
    | zero =>
      intro _ y' h1 h2
      left
      refine hedge 0 (Nat.zero_le _) y' ?_
      rw [show unitStart n k us st 0 = st by simp [unitStart], hv0,
        show st = unitStart n k us st 0 by simp [unitStart], hvhi 0 (Nat.zero_le _)]
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
      by_cases h4 : y' ≤ (S n k : ℝ) + 3 * m + 1 + 2 * (unitInput n k m (us[m]'hmL)).rhoR
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

end ArtGallery.Sec5.CoverM

end
