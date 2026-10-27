module

public import ArtGallery.Stade.GuardDefs

/-!
# The canonical guards see the wedges (proof plan §9)

A wedge (needle) is a counter-clockwise triangle `a, tip, c` whose side `c a` (the *mouth*) is
an opening onto a convex part `A` of the region (the hall, or a room).  A guard lying in the cone
of the wedge, beyond the mouth, sees every point of the wedge: the segment to the point crosses
the mouth (`cross_tri`) — `wedge_sees`.

Concrete instances (real coordinates, `H ≥ 1000`):
* `W1`, `W3` of a segment region at abscissa `s` (ceiling wedges): a guard `(s, y)` with
  `y` in the range of the segment (`[H, H+3]` for variables, `[0, 6]` for inputs);
* `W4`, `W5` of a variable with a constraint `x = 1`: the guard `(s, H + 1)`;
* floor needles `W2` (`needleDownL`, `needleDownR`) hanging from a horizontal line `y = β`:
  a guard `(s, y)` with `y ≥ β`.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

variable {P : Polygon}

/-- **Wedge visibility.**  `a, b, c` counter-clockwise; `g` weakly left of `a b` and `b c` and
weakly right of the mouth `c a`; `g` and the mouth lie in a convex part `A` of the region and the
triangle lies in the region.  Then `g` sees every point of the triangle. -/
theorem wedge_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled) {a b c g : Point}
    (hD : 0 < det a b c) (hg1 : 0 ≤ det a b g) (hg2 : 0 ≤ det b c g) (hg3 : det c a g ≤ 0)
    (hgA : g ∈ A) (hmA : segment c a ⊆ A) (hT : piece (tri a b c) ⊆ P.filled) :
    ∀ z ∈ piece (tri a b c), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_tri hD hg1 hg2 hg3 hz
  have hqT : q ∈ piece (tri a b c) := by
    have := edge_subset_piece (isPiece_tri hD) (j := 2) (by simp [tri_n])
    rw [(tri_edge a b c).2.2] at this
    exact this hq
  exact sees_of_two_convex hA (convex_piece _) hAP hT hgA hz (hmA hq) hqT hqz

/-! ### Ceiling wedges -/

section Ceil

variable {H s y : ℝ}

/-- `W1` with the mouth on the right (`σ = +1`). -/
theorem w1pos_det (hH : 1000 ≤ H) (hy : y ≤ 2 * H) :
    0 < det (s + 1 / 4, 2 * H) (s, 3 * H) (s, 2 * H) ∧
      0 ≤ det (s + 1 / 4, 2 * H) (s, 3 * H) (s, y) ∧ 0 ≤ det (s, 3 * H) (s, 2 * H) (s, y) ∧
      det (s, 2 * H) (s + 1 / 4, 2 * H) (s, y) ≤ 0 := by
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- `W1` with the mouth on the left (`σ = −1`). -/
theorem w1neg_det (hH : 1000 ≤ H) (hy : y ≤ 2 * H) :
    0 < det (s, 2 * H) (s, 3 * H) (s - 1 / 4, 2 * H) ∧
      0 ≤ det (s, 2 * H) (s, 3 * H) (s, y) ∧ 0 ≤ det (s, 3 * H) (s - 1 / 4, 2 * H) (s, y) ∧
      det (s - 1 / 4, 2 * H) (s, 2 * H) (s, y) ≤ 0 := by
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- `W3` with the tip on the left (`σ = +1`), tip height `T`, segment `[2H − T/... ]`: the
guard `(s, y)` is in the cone iff `4H − T ≤ y` and `H (2H − y) ≥ (H − 3)(T − 2H)`. -/
theorem w3pos_det (hH : 1000 ≤ H) {T : ℝ} (hT : 3 * H ≤ T) (hy : y ≤ 2 * H)
    (hlo : 4 * H - T ≤ y) (hhi : (H - 3) * (T - 2 * H) ≤ H * (2 * H - y)) :
    0 < det (s - (H - 3) / (2 * (2 * H - 3)), 2 * H) (s - 1 / 2, T) (s - 1 / 4, 2 * H) ∧
      0 ≤ det (s - (H - 3) / (2 * (2 * H - 3)), 2 * H) (s - 1 / 2, T) (s, y) ∧
      0 ≤ det (s - 1 / 2, T) (s - 1 / 4, 2 * H) (s, y) ∧
      det (s - 1 / 4, 2 * H) (s - (H - 3) / (2 * (2 * H - 3)), 2 * H) (s, y) ≤ 0 := by
  have h3 : 0 < 2 * H - 3 := by linarith
  have h3' : 2 * H - 3 ≠ 0 := ne_of_gt h3
  have e : (H - 3) / (2 * (2 * H - 3)) = 1 / 4 - 3 / (4 * (2 * H - 3)) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (by positivity) (by positivity),
      div_eq_iff (by positivity)]; ring
  have he : 0 < 3 / (4 * (2 * H - 3)) := by positivity
  set ε := 3 / (4 * (2 * H - 3)) with hε
  have hεH : ε * (4 * (2 * H - 3)) = 3 := by rw [hε]; field_simp
  rw [e]
  unfold det; simp only
  refine ⟨by nlinarith, ?_, by nlinarith, by nlinarith⟩
  -- `(1/4 + ε)(2H − y) ≥ (1/4 − ε)(T − 2H)`
  nlinarith

/-- `W3` with the tip on the right (`σ = −1`). -/
theorem w3neg_det (hH : 1000 ≤ H) {T : ℝ} (hT : 3 * H ≤ T) (hy : y ≤ 2 * H)
    (hlo : 4 * H - T ≤ y) (hhi : (H - 3) * (T - 2 * H) ≤ H * (2 * H - y)) :
    0 < det (s + 1 / 4, 2 * H) (s + 1 / 2, T) (s + (H - 3) / (2 * (2 * H - 3)), 2 * H) ∧
      0 ≤ det (s + 1 / 4, 2 * H) (s + 1 / 2, T) (s, y) ∧
      0 ≤ det (s + 1 / 2, T) (s + (H - 3) / (2 * (2 * H - 3)), 2 * H) (s, y) ∧
      det (s + (H - 3) / (2 * (2 * H - 3)), 2 * H) (s + 1 / 4, 2 * H) (s, y) ≤ 0 := by
  have h3 : 0 < 2 * H - 3 := by linarith
  have h3' : 2 * H - 3 ≠ 0 := ne_of_gt h3
  have e : (H - 3) / (2 * (2 * H - 3)) = 1 / 4 - 3 / (4 * (2 * H - 3)) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (by positivity) (by positivity),
      div_eq_iff (by positivity)]; ring
  have he : 0 < 3 / (4 * (2 * H - 3)) := by positivity
  set ε := 3 / (4 * (2 * H - 3)) with hε
  have hεH : ε * (4 * (2 * H - 3)) = 3 := by rw [hε]; field_simp
  rw [e]
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, ?_, by nlinarith⟩
  nlinarith

/-- `W4` (variable with `x = 1`): the guard `(s, H + 1)`. -/
theorem w4_det (hH : 1000 ≤ H) :
    0 < det (s - 3 * (H - 1) / (4 * (2 * H - 1)), 2 * H) (s - 3 / 4, 3 * H) (s - 3 / 8, 2 * H) ∧
      0 ≤ det (s - 3 * (H - 1) / (4 * (2 * H - 1)), 2 * H) (s - 3 / 4, 3 * H) (s, H + 1) ∧
      0 ≤ det (s - 3 / 4, 3 * H) (s - 3 / 8, 2 * H) (s, H + 1) ∧
      det (s - 3 / 8, 2 * H) (s - 3 * (H - 1) / (4 * (2 * H - 1)), 2 * H) (s, H + 1) ≤ 0 := by
  have h1 : 0 < 2 * H - 1 := by linarith
  have h1' : 2 * H - 1 ≠ 0 := ne_of_gt h1
  have e : 3 * (H - 1) / (4 * (2 * H - 1)) = 3 / 8 - 3 / (8 * (2 * H - 1)) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (by positivity) (by positivity),
      div_eq_iff (by positivity)]; ring
  have he : 0 < 3 / (8 * (2 * H - 1)) := by positivity
  set ε := 3 / (8 * (2 * H - 1)) with hε
  have hεH : ε * (8 * (2 * H - 1)) = 3 := by rw [hε]; field_simp
  rw [e]
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- `W5` (variable with `x = 1`): the guard `(s, H + 1)`. -/
theorem w5_det (hH : 1000 ≤ H) :
    0 < det (s - (H - 3) / (2 * H - 3), 2 * H) (s - 1, 3 * H) (s - (H - 1) / (2 * H - 1), 2 * H) ∧
      0 ≤ det (s - (H - 3) / (2 * H - 3), 2 * H) (s - 1, 3 * H) (s, H + 1) ∧
      0 ≤ det (s - 1, 3 * H) (s - (H - 1) / (2 * H - 1), 2 * H) (s, H + 1) ∧
      det (s - (H - 1) / (2 * H - 1), 2 * H) (s - (H - 3) / (2 * H - 3), 2 * H) (s, H + 1) ≤ 0 := by
  have h1 : 0 < 2 * H - 1 := by linarith
  have h3 : 0 < 2 * H - 3 := by linarith
  have h1' : 2 * H - 1 ≠ 0 := ne_of_gt h1
  have h3' : 2 * H - 3 ≠ 0 := ne_of_gt h3
  have e1 : (H - 3) / (2 * H - 3) = 1 / 2 - 3 / (2 * (2 * H - 3)) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (by positivity) (by positivity),
      div_eq_iff (by positivity)]; ring
  have e2 : (H - 1) / (2 * H - 1) = 1 / 2 - 1 / (2 * (2 * H - 1)) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (by positivity) (by positivity),
      div_eq_iff (by positivity)]; ring
  have he1 : 0 < 3 / (2 * (2 * H - 3)) := by positivity
  have he2 : 0 < 1 / (2 * (2 * H - 1)) := by positivity
  set ε := 3 / (2 * (2 * H - 3)) with hε
  set δ := 1 / (2 * (2 * H - 1)) with hδ
  have hεH : ε * (2 * (2 * H - 3)) = 3 := by rw [hε]; field_simp
  have hδH : δ * (2 * (2 * H - 1)) = 1 := by rw [hδ]; field_simp
  have hεδ : δ < ε := by
    rw [hε, hδ, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  rw [e1, e2]
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Ceil

/-! ### Floor needles -/

section Floor

variable {H s β y : ℝ}

/-- A needle hanging from `y = β` with the mouth on the left of `x = s` (`needleDownL`). -/
theorem needleL_det (hH : 0 < H) (hy : β ≤ y) :
    0 < det (s - 1 / 4, β) (s, β - H) (s, β) ∧ 0 ≤ det (s - 1 / 4, β) (s, β - H) (s, y) ∧
      0 ≤ det (s, β - H) (s, β) (s, y) ∧ det (s, β) (s - 1 / 4, β) (s, y) ≤ 0 := by
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- A needle hanging from `y = β` with the mouth on the right of `x = s` (`needleDownR`). -/
theorem needleR_det (hH : 0 < H) (hy : β ≤ y) :
    0 < det (s, β) (s, β - H) (s + 1 / 4, β) ∧ 0 ≤ det (s, β) (s, β - H) (s, y) ∧
      0 ≤ det (s, β - H) (s + 1 / 4, β) (s, y) ∧ det (s + 1 / 4, β) (s, β) (s, y) ≤ 0 := by
  unfold det; simp only
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The needle hanging from `y = β` at `x = s` with the mouth `[s − 1/4, s]` (on the left). -/
noncomputable def needleL (s β H : ℝ) : Polygon := tri (s - 1 / 4, β) (s, β - H) (s, β)

/-- The needle hanging from `y = β` at `x = s` with the mouth `[s, s + 1/4]` (on the right). -/
noncomputable def needleR (s β H : ℝ) : Polygon := tri (s, β) (s, β - H) (s + 1 / 4, β)

/-- **A needle hanging from a horizontal opening** of a convex part `A` of the region (the hall,
or a room) is seen from every point `(s, y)`, `y ≥ β`, of `A`. -/
theorem needleL_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hH : 0 < H)
    (hy : β ≤ y) (hgA : (s, y) ∈ A) (hmA : segment (s, β) (s - 1 / 4, β) ⊆ A)
    (hT : piece (needleL s β H) ⊆ P.filled) : ∀ z ∈ piece (needleL s β H), P.Sees (s, y) z := by
  obtain ⟨h0, h1, h2, h3⟩ := needleL_det (s := s) hH hy
  exact wedge_sees hA hAP h0 h1 h2 h3 hgA hmA hT

/-- **A needle hanging from a horizontal opening** (mouth on the right). -/
theorem needleR_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hH : 0 < H)
    (hy : β ≤ y) (hgA : (s, y) ∈ A) (hmA : segment (s + 1 / 4, β) (s, β) ⊆ A)
    (hT : piece (needleR s β H) ⊆ P.filled) : ∀ z ∈ piece (needleR s β H), P.Sees (s, y) z := by
  obtain ⟨h0, h1, h2, h3⟩ := needleR_det (s := s) hH hy
  exact wedge_sees hA hAP h0 h1 h2 h3 hgA hmA hT

/-- **A needle hanging from the bottom of a room**: if the guard `(s, y)` sees every point of the
mouth `[s, s + 1/4] × {β}`, it sees every point of the needle. -/
theorem needleR_sees_via (hH : 0 < H) (hy : β ≤ y)
    (hgm : ∀ q ∈ segment (s + 1 / 4, β) (s, β), P.Sees (s, y) q)
    (hT : piece (needleR s β H) ⊆ P.filled) : ∀ z ∈ piece (needleR s β H), P.Sees (s, y) z := by
  obtain ⟨h0, h1, h2, h3⟩ := needleR_det (s := s) hH hy
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_tri h0 h1 h2 h3 hz
  have hqT : q ∈ piece (needleR s β H) := by
    have := edge_subset_piece (isPiece_tri h0) (j := 2) (by simp [tri_n])
    rw [(tri_edge _ _ _).2.2] at this
    exact this hq
  exact sees_via (convex_piece _) hT hqz (hgm q hq) hqT hz

end Floor

end ArtGallery.Stade

end
