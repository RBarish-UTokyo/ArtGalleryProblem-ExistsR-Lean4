module

public import ArtGallery.Hardness.Sec5.MainArea.Witness

/-!
# Section 5: effective cones of the shaft witnesses

The witnesses `u0, u1` (and `q1, q2` with `one` spikes) are seen from the pocket room and from a
*steep cone* above the door (`02_main_area.md`, "witness localisation"): every point seen from
them lies in the pocket room or satisfies `y ≥ 1` and

| witness | steep cone (relative, `y ≥ 1`) | blocking edges |
|---|---|---|
| `u0 = (0, −5)` | `x' ≥ 0`, `8x' ≤ 3(y + 5)` (between `(0,1)` and `(3/2, 4)`) | `u1 → E` |
| `u1 = (3/2, −5)` | `x' ≤ 3/2`, `8(3/2 − x') ≤ 3(y + 5)` | `D → u0` (spikes: see below) |
| `q1 = (−1/2, −4)` | `4x' ≥ y + 2`, `3(x' + 1/2) ≤ 2(y + 4)` | `u1 → E` |
| `q2 = (1/2, −6)` | `x' ≤ 1/2`, `10x' + y + 1 ≥ 0` | see below |

(`sees_u0_steep`, `sees_u1_steep`, `sees_q1_steep`, `sees_q2_steep`).  With the spikes the wall
`x' = 0` has the opening `R0 Q'` of the `q1` spike; a segment from `u1` or `q2` leaving on the
left is then blocked by `Q' → u0`, `R0 → q1` or `D → R0`, or passes through the reflex vertex
`R0` (or, for `q2`, through `u0`), which is excluded by the vertex cones.  Outside the pocket room
these cones are thin: at height `y` their width is `3(y + 5)/8` (`u0`, `u1`), so they never reach
the unit lines `x = S`, `x = X_L` below the top `y = S + 3N` of the main hexagon.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set Polygon
open ArtGallery.Irrational (qdet)

section Tools

variable {P : Polygon} {one : Bool} {σ a : ℕ}

/-- A point leaving the pocket room through the door from a point below the door line ends
above the door line. -/
theorem le_snd_of_not_mem_room (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {w p : Point} (hw : w ∈ (pocketPoly one σ).filled) (hw2 : w.2 < 1) (hs : P.Sees w p)
    (hp : p ∉ (pocketPoly one σ).filled) : 1 ≤ p.2 := by
  obtain ⟨y, hyD, t, ht0, ht1, rfl⟩ := sees_crosses_door (pocket_isRoom hP hL hK) hw hp hs
  have h1 := (mem_door hyD).1
  simp only at h1
  by_contra h
  push Not at h
  rcases le_or_gt p.2 w.2 with h' | h'
  · nlinarith [mul_nonneg ht0 (sub_nonneg.2 h')]
  · nlinarith [mul_le_mul_of_nonneg_right ht1 (sub_pos.2 h').le]

/-- A point of the segment `w p` sees `p` if `w` does. -/
theorem sees_of_mem_segment' {w p r : Point} (hs : P.Sees w p)
    (hr : r ∈ ArtGallery.segment w p) : P.Sees r p :=
  fun _ hz => hs (Geometry.segment_subset_of_convex (Geometry.segment_convex w p) hr
    (Geometry.right_mem_segment w p) hz)

/-- A point `r` on the line `w p` strictly above `w` and weakly below `p` lies on the
segment `w p`. -/
theorem mem_segment_of_det_eq_zero {w p r : Point} (hdet : det w p r = 0) (h1 : w.2 < r.2)
    (h2 : r.2 ≤ p.2) : r ∈ ArtGallery.segment w p := by
  have hpw : 0 < p.2 - w.2 := by linarith
  refine ⟨(r.2 - w.2) / (p.2 - w.2), div_nonneg (by linarith) hpw.le,
    (div_le_one hpw).2 (by linarith), ?_⟩
  unfold det at hdet
  ext
  · simp only
    field_simp
    linarith
  · simp only
    field_simp
    ring

/-- **Vertex cone at a reflex pocket vertex.** -/
theorem pocket_reflex (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {j : ℕ}
    (hj1 : 1 ≤ j) (hjm : j < (pocketRel one).length) {A B C : Q2}
    (hA : (pocketClosedRel one).getD (j - 1) 0 = A) (hB : (pocketClosedRel one).getD j 0 = B)
    (hC : (pocketClosedRel one).getD (j + 1) 0 = C) (hrefl : qdet A B C < 0) {p : Point}
    (h : P.Sees (absPt σ B) p) :
    0 ≤ det (ratPoint A) (ratPoint B) (rel σ p) ∨ 0 ≤ det (ratPoint B) (ratPoint C) (rel σ p) := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hu : P.vtx (((a + j) % P.n + P.n - 1) % P.n) = absPt σ A := by
    have := chain_prev hn a hj1
    unfold Jordan.prevIdx at this
    rw [this, hK.vtx (by omega), hA]
  have hw : P.vtx (((a + j) % P.n + 1) % P.n) = absPt σ C := by
    rw [chain_succ, hK.vtx (by omega), hC]
  have hc : det (absPt σ A) (absPt σ B) (absPt σ C) < 0 := by
    rw [det_absPt_absPt, rel_absPt, Irrational.det_ratPoint]; exact_mod_cast hrefl
  have := sees_vtx_reflex hP hL (Nat.mod_lt _ hn) hu (by rw [hK.vtx hjm.le, hB]) hw hc h
  rwa [det_absPt_absPt, det_absPt_absPt] at this

end Tools

/-- Unfold determinants of explicit relative points. -/
macro "rdet" : tactic =>
  `(tactic| (simp only [det, rel, ratPoint, u0Rel, u1Rel, q1Rel, q2Rel]; norm_num))

section Steep

variable {P : Polygon} {one : Bool} {σ a : ℕ}

theorem u0Pt_mem_room : u0Pt σ ∈ (pocketPoly one σ).filled := by
  cases one
  · exact pocket_vtx_mem_room (one := false) (σ := σ) (j := 6) (by decide)
  · exact pocket_vtx_mem_room (one := true) (σ := σ) (j := 9) (by decide)

theorem u1Pt_mem_room : u1Pt σ ∈ (pocketPoly one σ).filled := by
  cases one
  · exact pocket_vtx_mem_room (one := false) (σ := σ) (j := 7) (by decide)
  · exact pocket_vtx_mem_room (one := true) (σ := σ) (j := 12) (by decide)

theorem u0Pt_snd (σ : ℕ) : (u0Pt σ).2 = -5 := by rw [u0Pt, absPt_eq]; simp [u0Rel]
theorem u1Pt_snd (σ : ℕ) : (u1Pt σ).2 = -5 := by rw [u1Pt, absPt_eq]; simp [u1Rel]
theorem q1Pt_snd (σ : ℕ) : (q1Pt σ).2 = -4 := by rw [q1Pt, absPt_eq]; simp [q1Rel]
theorem q2Pt_snd (σ : ℕ) : (q2Pt σ).2 = -6 := by rw [q2Pt, absPt_eq]; simp [q2Rel]

/-- **Effective cone of `u0`**: a point seen from `u0` lies in the pocket room or in the steep
cone `y ≥ 1`, `0 ≤ x' ≤ 3(y + 5)/8`. -/
theorem sees_u0_steep (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (u0Pt σ) p) :
    p ∈ (pocketPoly one σ).filled ∨
      (1 ≤ p.2 ∧ (slotX σ : ℝ) ≤ p.1 ∧ 8 * (p.1 - slotX σ) ≤ 3 * (p.2 + 5)) := by
  by_cases hp : p ∈ (pocketPoly one σ).filled
  · exact Or.inl hp
  right
  have hy := le_snd_of_not_mem_room hP hL hK u0Pt_mem_room (by rw [u0Pt_snd]; norm_num) h hp
  have hx := (cone_u0 hP hL hK h).1
  refine ⟨hy, hx, ?_⟩
  by_contra hc
  push Not at hc
  refine pocket_not_sees_cross hP hK (j := idxU1 one) (idxU1_lt one) (A := (3/2, -5))
    (B := (3/2, -1)) (by cases one <;> rfl) (by cases one <;> rfl) ?_ ?_ h
  · rw [u0Pt, rel_absPt]
    apply mul_neg_of_pos_of_neg
    · rdet
    · rdet; linarith
  · rw [u0Pt, rel_absPt]
    apply mul_neg_of_neg_of_pos
    · rdet; linarith
    · rdet; linarith

/-- **Effective cone of `u1`**: a point seen from `u1` lies in the pocket room or in the steep
cone `y ≥ 1`, `0 ≤ 3/2 − x' ≤ 3(y + 5)/8`. -/
theorem sees_u1_steep (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (u1Pt σ) p) :
    p ∈ (pocketPoly one σ).filled ∨
      (1 ≤ p.2 ∧ p.1 ≤ slotX σ + 3/2 ∧ 8 * (slotX σ + 3/2 - p.1) ≤ 3 * (p.2 + 5)) := by
  by_cases hp : p ∈ (pocketPoly one σ).filled
  · exact Or.inl hp
  right
  have hy := le_snd_of_not_mem_room hP hL hK u1Pt_mem_room (by rw [u1Pt_snd]; norm_num) h hp
  have hx := (cone_u1 hP hL hK h).1
  refine ⟨hy, hx, ?_⟩
  by_contra hc
  push Not at hc
  cases one
  · -- the segment crosses the wall `D → u0`
    refine pocket_not_sees_cross hP hK (j := 5) (by decide) (A := (0, -1)) (B := (0, -5))
      rfl rfl ?_ ?_ h
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · rdet
      · rdet; linarith
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_neg_of_pos
      · rdet; linarith
      · rdet; linarith
  · -- with spikes: case analysis on where the segment meets the line `x' = 0`
    have eQ : det (rel σ (u1Pt σ)) (rel σ p) (ratPoint (0, -21/5)) =
        (p.1 - slotX σ - 3/2) * (4/5) + 3/2 * (p.2 + 5) := by
      rw [u1Pt, rel_absPt]; simp only [det, rel, ratPoint, u1Rel]; push_cast; ring
    have eR : det (rel σ (u1Pt σ)) (rel σ p) (ratPoint (0, -2)) =
        (p.1 - slotX σ - 3/2) * 3 + 3/2 * (p.2 + 5) := by
      rw [u1Pt, rel_absPt]; simp only [det, rel, ratPoint, u1Rel]; push_cast; ring
    rcases lt_or_ge (det (rel σ (u1Pt σ)) (rel σ p) (ratPoint (0, -21/5))) 0 with hQ | hQ
    · -- crossing `Q' → u0`
      refine pocket_not_sees_cross hP hK (j := 8) (by decide) (A := (0, -21/5)) (B := (0, -5))
        rfl rfl ?_ ?_ h
      · rw [u1Pt, rel_absPt]
        apply mul_neg_of_pos_of_neg
        · rdet
        · rdet; linarith
      · apply mul_neg_of_neg_of_pos hQ
        rw [u1Pt, rel_absPt]; rdet; linarith
    rcases lt_trichotomy (det (rel σ (u1Pt σ)) (rel σ p) (ratPoint (0, -2))) 0 with hR | hR | hR
    · -- crossing `R0 → q1`
      refine pocket_not_sees_cross hP hK (j := 6) (by decide) (A := (0, -2)) (B := (-1/2, -4))
        rfl rfl ?_ ?_ h
      · rw [u1Pt, rel_absPt]
        apply mul_neg_of_pos_of_neg
        · rdet
        · rdet; linarith
      · apply mul_neg_of_neg_of_pos hR
        rw [eQ] at hQ
        rw [u1Pt, rel_absPt]; rdet; linarith
    · -- through the reflex vertex `R0`
      have hmem : absPt σ (0, -2) ∈ ArtGallery.segment (u1Pt σ) p := by
        refine mem_segment_of_det_eq_zero ?_ (by rw [u1Pt_snd, absPt_eq]; norm_num)
          (by rw [absPt_eq]; simp only; push_cast; linarith)
        rw [det_absPt_right]; exact hR
      have hs := sees_of_mem_segment' h hmem
      rcases pocket_reflex hP hL hK (j := 6) (by norm_num) (by decide) (A := (0, -1))
        (B := (0, -2)) (C := (-1/2, -4)) rfl rfl rfl (by norm_num [qdet]) hs with h1 | h1 <;>
        · simp only [det, rel, ratPoint] at h1; norm_num at h1; linarith
    · -- crossing `D → R0`
      refine pocket_not_sees_cross hP hK (j := 5) (by decide) (A := (0, -1)) (B := (0, -2))
        rfl rfl ?_ ?_ h
      · rw [u1Pt, rel_absPt]
        apply mul_neg_of_pos_of_neg
        · rdet
        · rdet; linarith
      · apply mul_neg_of_neg_of_pos _ hR
        rw [u1Pt, rel_absPt]; rdet; linarith

/-- **Effective cone of `q1`**: a point seen from `q1` lies in the pocket room or in the steep
cone `y ≥ 1`, `y + 2 ≤ 4x'`, `3(x' + 1/2) ≤ 2(y + 4)`. -/
theorem sees_q1_steep (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    {p : Point} (h : P.Sees (q1Pt σ) p) :
    p ∈ (pocketPoly true σ).filled ∨
      (1 ≤ p.2 ∧ p.2 + 2 ≤ 4 * (p.1 - slotX σ) ∧ 3 * (p.1 - slotX σ + 1/2) ≤ 2 * (p.2 + 4)) := by
  by_cases hp : p ∈ (pocketPoly true σ).filled
  · exact Or.inl hp
  right
  have hy := le_snd_of_not_mem_room hP hL hK
    (pocket_vtx_mem_room (one := true) (σ := σ) (j := 7) (by decide))
    (by rw [show absPt σ ((pocketClosedRel true).getD 7 0) = q1Pt σ from rfl, q1Pt_snd]; norm_num)
    h hp
  have hx := (cone_q1 hP hL hK h).1
  refine ⟨hy, hx, ?_⟩
  by_contra hc
  push Not at hc
  refine pocket_not_sees_cross hP hK (j := 12) (by decide) (A := (3/2, -5)) (B := (3/2, -1))
    rfl rfl ?_ ?_ h
  · rw [q1Pt, rel_absPt]
    apply mul_neg_of_pos_of_neg
    · rdet
    · rdet; linarith
  · rw [q1Pt, rel_absPt]
    apply mul_neg_of_neg_of_pos
    · rdet; linarith
    · rdet; linarith

/-- **Effective cone of `q2`**: a point seen from `q2` lies in the pocket room or in the steep
cone `y ≥ 1`, `x' ≤ 1/2`, `10x' + y + 1 ≥ 0`. -/
theorem sees_q2_steep (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    {p : Point} (h : P.Sees (q2Pt σ) p) :
    p ∈ (pocketPoly true σ).filled ∨
      (1 ≤ p.2 ∧ p.1 ≤ slotX σ + 1/2 ∧ 0 ≤ 10 * (p.1 - slotX σ) + p.2 + 1) := by
  by_cases hp : p ∈ (pocketPoly true σ).filled
  · exact Or.inl hp
  right
  have hy := le_snd_of_not_mem_room hP hL hK
    (pocket_vtx_mem_room (one := true) (σ := σ) (j := 10) (by decide))
    (by rw [show absPt σ ((pocketClosedRel true).getD 10 0) = q2Pt σ from rfl, q2Pt_snd]; norm_num)
    h hp
  obtain ⟨hx, hc2⟩ := cone_q2 hP hL hK h
  refine ⟨hy, hx, ?_⟩
  by_contra hc
  push Not at hc
  have eQ : det (rel σ (q2Pt σ)) (rel σ p) (ratPoint (0, -21/5)) =
      (p.1 - slotX σ - 1/2) * (9/5) + (p.2 + 6) / 2 := by
    rw [q2Pt, rel_absPt]; simp only [det, rel, ratPoint, q2Rel]; push_cast; ring
  have eU : det (rel σ (q2Pt σ)) (rel σ p) (ratPoint (0, -5)) =
      (p.1 - slotX σ - 1/2) + (p.2 + 6) / 2 := by
    rw [q2Pt, rel_absPt]; simp only [det, rel, ratPoint, q2Rel]; push_cast; ring
  rcases lt_trichotomy (det (rel σ (q2Pt σ)) (rel σ p) (ratPoint (0, -5))) 0 with hU | hU | hU
  · -- excluded by the cone of `q2`
    rw [eU] at hU; linarith
  · -- through `u0`: then `u0` sees `p`, but `p` is left of `u0`
    have hmem : u0Pt σ ∈ ArtGallery.segment (q2Pt σ) p := by
      refine mem_segment_of_det_eq_zero ?_ (by rw [u0Pt_snd, q2Pt_snd]; norm_num)
        (by rw [u0Pt_snd]; linarith)
      rw [u0Pt, det_absPt_right]; exact hU
    have := (cone_u0 hP hL hK (sees_of_mem_segment' h hmem)).1
    linarith
  rcases lt_or_ge (det (rel σ (q2Pt σ)) (rel σ p) (ratPoint (0, -21/5))) 0 with hQ | hQ
  · -- crossing `Q' → u0`
    refine pocket_not_sees_cross hP hK (j := 8) (by decide) (A := (0, -21/5)) (B := (0, -5))
      rfl rfl ?_ ?_ h
    · rw [q2Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · rdet
      · rdet; linarith
    · exact mul_neg_of_neg_of_pos hQ hU
  rcases lt_trichotomy (det (rel σ (q2Pt σ)) (rel σ p) (ratPoint (0, -2))) 0 with hR | hR | hR
  · -- crossing `R0 → q1`
    refine pocket_not_sees_cross hP hK (j := 6) (by decide) (A := (0, -2)) (B := (-1/2, -4))
      rfl rfl ?_ ?_ h
    · rw [q2Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · rdet
      · rdet; linarith
    · apply mul_neg_of_neg_of_pos hR
      rw [eQ] at hQ
      rw [q2Pt, rel_absPt]; rdet; linarith
  · -- through the reflex vertex `R0`
    have hmem : absPt σ (0, -2) ∈ ArtGallery.segment (q2Pt σ) p := by
      refine mem_segment_of_det_eq_zero ?_ (by rw [q2Pt_snd, absPt_eq]; norm_num)
        (by rw [absPt_eq]; simp only; push_cast; linarith)
      rw [det_absPt_right]; exact hR
    have hs := sees_of_mem_segment' h hmem
    rcases pocket_reflex hP hL hK (j := 6) (by norm_num) (by decide) (A := (0, -1))
      (B := (0, -2)) (C := (-1/2, -4)) rfl rfl rfl (by norm_num [qdet]) hs with h1 | h1 <;>
      · simp only [det, rel, ratPoint] at h1; norm_num at h1; linarith
  · -- crossing `D → R0`
    refine pocket_not_sees_cross hP hK (j := 5) (by decide) (A := (0, -1)) (B := (0, -2))
      rfl rfl ?_ ?_ h
    · rw [q2Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · rdet
      · rdet; linarith
    · apply mul_neg_of_neg_of_pos _ hR
      rw [q2Pt, rel_absPt]; rdet; linarith

end Steep

end ArtGallery.Sec5

end
