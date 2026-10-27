module

public import ArtGallery.Hardness.Sec5.Corridor.CoverSlotC

/-!
# Section 5: corridors — interior points below the floor line lie in a slot piece

`Good.classify_lower`: an interior point `z` of the corridor region with `z.y < H` lies in a slot
piece of some pair.  Shoot a ray downwards: of slope `2` (direction `(−1, −2)`, along which
`u₂ = x − (y − H)/2` is constant) unless `z.x` is within `[κ₄ − 1/16, κ₄ + 1/4]` of a slope-4 key,
and of slope `4` (direction `(−1, −4)`, `u₄` constant) otherwise.  The ray meets the boundary below
the floor line, hence on a slot side (`Good.bd_floor_cases`).  A side of the matching type puts `z`
in that slot piece (the lower constraint is monotone in `y`); a side of the other type contradicts
the separation of the keys (`Good.keys`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Lower

variable (hg : I.Good N)
include hg

/-- The sides of a slope-2 slot lie in its slot piece. -/
theorem Good.side2_mem {j : ℕ} {w : Point}
    (h : w ∈ segOf ((I.dentS2 j).A, (I.dentS2 j).T) ∨ w ∈ segOf ((I.dentS2 j).T, (I.dentS2 j).B)) :
    w ∈ hpSet (I.slot2Fs j) := by
  obtain ⟨he, -⟩ := hg.eps_real
  have hA : (I.dentS2 j).A ∈ hpSet (I.slot2Fs j) := by
    rw [mem_slot2_iff]; simp only [dentS2, dent2]
    refine ⟨le_rfl, by linarith, by linarith⟩
  have hT : (I.dentS2 j).T ∈ hpSet (I.slot2Fs j) := by
    rw [mem_slot2_iff]; simp only [dentS2, dent2]
    refine ⟨by linarith, by linarith, by linarith⟩
  have hB : (I.dentS2 j).B ∈ hpSet (I.slot2Fs j) := by
    rw [mem_slot2_iff]; simp only [dentS2, dent2]
    refine ⟨le_rfl, by linarith, by nlinarith⟩
  rcases h with h | h
  · exact Geometry.segment_subset_of_convex (convex_hpSet _) hA hT h
  · exact Geometry.segment_subset_of_convex (convex_hpSet _) hT hB h

/-- The sides of a slope-4 slot lie in its slot piece. -/
theorem Good.side4_mem {j : ℕ} {w : Point}
    (h : w ∈ segOf ((I.dentS4 j).A, (I.dentS4 j).T) ∨ w ∈ segOf ((I.dentS4 j).T, (I.dentS4 j).B)) :
    w ∈ hpSet (I.slot4Fs j) := by
  obtain ⟨he, -⟩ := hg.eps_real
  have hA : (I.dentS4 j).A ∈ hpSet (I.slot4Fs j) := by
    rw [mem_slot4_iff]; simp only [dentS4, dent4]
    refine ⟨le_rfl, by linarith, by nlinarith⟩
  have hT : (I.dentS4 j).T ∈ hpSet (I.slot4Fs j) := by
    rw [mem_slot4_iff]; simp only [dentS4, dent4]
    refine ⟨by linarith, by linarith, by linarith⟩
  have hB : (I.dentS4 j).B ∈ hpSet (I.slot4Fs j) := by
    rw [mem_slot4_iff]; simp only [dentS4, dent4]
    refine ⟨le_rfl, by linarith, by linarith⟩
  rcases h with h | h
  · exact Geometry.segment_subset_of_convex (convex_hpSet _) hA hT h
  · exact Geometry.segment_subset_of_convex (convex_hpSet _) hT hB h

/-- Location of a point of a slope-2 slot piece. -/
theorem Good.slot2_box {j : ℕ} {w : Point} (hw : w ∈ hpSet (I.slot2Fs j)) :
    -(1 / 8 : ℝ) ≤ w.2 - I.H ∧ w.2 ≤ I.H ∧
      (I.kx j 2 : ℝ) - 1 / 16 - (I.ε : ℝ) / 8 ≤ w.1 ∧ w.1 ≤ (I.kx j 2 : ℝ) := by
  obtain ⟨he, -⟩ := hg.eps_real
  rw [mem_slot2_iff] at hw
  obtain ⟨w1, w2, w3⟩ := hw
  have ht : -(1 / 8 : ℝ) ≤ w.2 - I.H := by
    by_contra hc
    have : (I.ε : ℝ) * (w.2 - I.H + 1 / 8) < 0 := mul_neg_of_pos_of_neg he (by linarith)
    linarith
  have hε : (I.ε : ℝ) * (w.2 - I.H + 1 / 8) ≤ (I.ε : ℝ) / 8 := by nlinarith
  exact ⟨ht, w1, by linarith, by linarith⟩

/-- Location of a point of a slope-4 slot piece. -/
theorem Good.slot4_box {j : ℕ} {w : Point} (hw : w ∈ hpSet (I.slot4Fs j)) :
    -(1 / 4 : ℝ) ≤ w.2 - I.H ∧ w.2 ≤ I.H ∧
      (I.kx j 4 : ℝ) - 1 / 16 ≤ w.1 ∧ w.1 ≤ (I.kx j 4 : ℝ) + (I.ε : ℝ) / 8 := by
  obtain ⟨he, -⟩ := hg.eps_real
  rw [mem_slot4_iff] at hw
  obtain ⟨w1, w2, w3⟩ := hw
  have ht : -(1 / 4 : ℝ) ≤ w.2 - I.H := by
    by_contra hc
    have : (I.ε : ℝ) / 2 * (w.2 - I.H + 1 / 4) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have hε : (I.ε : ℝ) / 2 * (w.2 - I.H + 1 / 4) ≤ (I.ε : ℝ) / 8 := by nlinarith
  exact ⟨ht, w1, by linarith, by linarith⟩

/-- **Interior points below the floor line lie in a slot piece.** -/
theorem Good.classify_lower {z : Point} (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hzH : z.2 < I.H) :
    ∃ k < I.np, z ∈ hpSet (I.slot2Fs k) ∨ z ∈ hpSet (I.slot4Fs k) := by
  obtain ⟨he, he1⟩ := hg.eps_real
  by_cases hzone : ∃ j < I.np, (I.kx j 4 : ℝ) - 1 / 16 ≤ z.1 ∧ z.1 ≤ (I.kx j 4 : ℝ) + 1 / 4
  · -- the ray of slope `4`
    obtain ⟨j, hj, hz1, hz2⟩ := hzone
    obtain ⟨s, hs, hb⟩ := exists_boundary_on_ray (d := ((-1 : ℝ), (-4 : ℝ))) (by simp) hzK hzb
    set w := z + s • ((-1 : ℝ), (-4 : ℝ)) with hwdef
    have hw1 : w.1 = z.1 - s := by simp [w]; ring
    have hw2 : w.2 = z.2 - 4 * s := by simp [w]; ring
    rcases hg.bd_floor_cases hb with hy | ⟨i, hi, h⟩
    · exact absurd hy (by linarith)
    rcases h with h | h | h | h
    · have := hg.slot2_box (hg.side2_mem (Or.inl h))
      obtain ⟨hkey, -, -⟩ := hg.keys hi hj
      rcases hkey with h' | h' <;> linarith
    · have := hg.slot2_box (hg.side2_mem (Or.inr h))
      obtain ⟨hkey, -, -⟩ := hg.keys hi hj
      rcases hkey with h' | h' <;> linarith
    all_goals
      have hm := hg.side4_mem (j := i) (by first | exact Or.inl h | exact Or.inr h)
      refine ⟨i, hi, Or.inr ?_⟩
      rw [mem_slot4_iff] at hm ⊢
      obtain ⟨m1, m2, m3⟩ := hm
      have : (I.ε : ℝ) / 2 * (w.2 - I.H + 1 / 4) ≤ (I.ε : ℝ) / 2 * (z.2 - I.H + 1 / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      refine ⟨hzH.le, by linarith, by linarith⟩
  · -- the ray of slope `2`
    push Not at hzone
    obtain ⟨s, hs, hb⟩ := exists_boundary_on_ray (d := ((-1 : ℝ), (-2 : ℝ))) (by simp) hzK hzb
    set w := z + s • ((-1 : ℝ), (-2 : ℝ)) with hwdef
    have hw1 : w.1 = z.1 - s := by simp [w]; ring
    have hw2 : w.2 = z.2 - 2 * s := by simp [w]; ring
    rcases hg.bd_floor_cases hb with hy | ⟨i, hi, h⟩
    · exact absurd hy (by linarith)
    rcases h with h | h | h | h
    rotate_left 2
    · have := hg.slot4_box (hg.side4_mem (Or.inl h))
      have := hzone i hi (by linarith)
      linarith
    · have := hg.slot4_box (hg.side4_mem (Or.inr h))
      have := hzone i hi (by linarith)
      linarith
    all_goals
      have hm := hg.side2_mem (j := i) (by first | exact Or.inl h | exact Or.inr h)
      refine ⟨i, hi, Or.inl ?_⟩
      rw [mem_slot2_iff] at hm ⊢
      obtain ⟨m1, m2, m3⟩ := hm
      have : (I.ε : ℝ) * (w.2 - I.H + 1 / 8) ≤ (I.ε : ℝ) * (z.2 - I.H + 1 / 8) :=
        mul_le_mul_of_nonneg_left (by linarith) he.le
      refine ⟨hzH.le, by linarith, by linarith⟩

end Lower

end Input

end ArtGallery.Sec5.Corridor

end
