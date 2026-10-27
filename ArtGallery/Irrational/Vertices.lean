module

public import ArtGallery.Irrational.Cover

/-!
# Vertices, edges and blocking lemmas for `𝒫`

The coordinates of the 50 corners as real points (`vtx0`, …, `vtx49`), and specialised forms of
the blocking lemmas: a segment is blocked by a vertical (`block_v`) or horizontal (`block_h`)
edge `i → i+1` that it crosses properly, or by a point outside `U` (`not_sees_wit`).
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set

theorem vtx0 : P.vtx 0 = ((0 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 0) (a := 0) (b := 0) rfl]; try norm_num

theorem vtx1 : P.vtx 1 = ((19/10 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 1) (a := 19/10) (b := 0) rfl]; try norm_num

theorem vtx2 : P.vtx 2 = ((2 : ℝ), (-1/2 : ℝ)) := by
  rw [vtx_eq_of (i := 2) (a := 2) (b := -1/2) rfl]; try norm_num

theorem vtx3 : P.vtx 3 = ((2 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 3) (a := 2) (b := 0) rfl]; try norm_num

theorem vtx4 : P.vtx 4 = ((3 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 4) (a := 3) (b := 0) rfl]; try norm_num

theorem vtx5 : P.vtx 5 = ((3 : ℝ), (-3/20 : ℝ)) := by
  rw [vtx_eq_of (i := 5) (a := 3) (b := -3/20) rfl]; try norm_num

theorem vtx6 : P.vtx 6 = ((7/2 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 6) (a := 7/2) (b := 0) rfl]; try norm_num

theorem vtx7 : P.vtx 7 = ((4 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 7) (a := 4) (b := 0) rfl]; try norm_num

theorem vtx8 : P.vtx 8 = ((4 : ℝ), (-12/19 : ℝ)) := by
  rw [vtx_eq_of (i := 8) (a := 4) (b := -12/19) rfl]; try norm_num

theorem vtx9 : P.vtx 9 = ((8 : ℝ), (-18/19 : ℝ)) := by
  rw [vtx_eq_of (i := 9) (a := 8) (b := -18/19) rfl]; try norm_num

theorem vtx10 : P.vtx 10 = ((8 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 10) (a := 8) (b := 0) rfl]; try norm_num

theorem vtx11 : P.vtx 11 = ((12 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 11) (a := 12) (b := 0) rfl]; try norm_num

theorem vtx12 : P.vtx 12 = ((12 : ℝ), (-34/21 : ℝ)) := by
  rw [vtx_eq_of (i := 12) (a := 12) (b := -34/21) rfl]; try norm_num

theorem vtx13 : P.vtx 13 = ((16 : ℝ), (-36/21 : ℝ)) := by
  rw [vtx_eq_of (i := 13) (a := 16) (b := -36/21) rfl]; try norm_num

theorem vtx14 : P.vtx 14 = ((16 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 14) (a := 16) (b := 0) rfl]; try norm_num

theorem vtx15 : P.vtx 15 = ((189/10 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 15) (a := 189/10) (b := 0) rfl]; try norm_num

theorem vtx16 : P.vtx 16 = ((19 : ℝ), (-1/2 : ℝ)) := by
  rw [vtx_eq_of (i := 16) (a := 19) (b := -1/2) rfl]; try norm_num

theorem vtx17 : P.vtx 17 = ((19 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 17) (a := 19) (b := 0) rfl]; try norm_num

theorem vtx18 : P.vtx 18 = ((20 : ℝ), (0 : ℝ)) := by
  rw [vtx_eq_of (i := 18) (a := 20) (b := 0) rfl]; try norm_num

theorem vtx19 : P.vtx 19 = ((20 : ℝ), (1/2 : ℝ)) := by
  rw [vtx_eq_of (i := 19) (a := 20) (b := 1/2) rfl]; try norm_num

theorem vtx20 : P.vtx 20 = ((30 : ℝ), (1/2 : ℝ)) := by
  rw [vtx_eq_of (i := 20) (a := 30) (b := 1/2) rfl]; try norm_num

theorem vtx21 : P.vtx 21 = ((30 : ℝ), (3/5 : ℝ)) := by
  rw [vtx_eq_of (i := 21) (a := 30) (b := 3/5) rfl]; try norm_num

theorem vtx22 : P.vtx 22 = ((20 : ℝ), (3/5 : ℝ)) := by
  rw [vtx_eq_of (i := 22) (a := 20) (b := 3/5) rfl]; try norm_num

theorem vtx23 : P.vtx 23 = ((20 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 23) (a := 20) (b := 4) rfl]; try norm_num

theorem vtx24 : P.vtx 24 = ((191/10 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 24) (a := 191/10) (b := 4) rfl]; try norm_num

theorem vtx25 : P.vtx 25 = ((19 : ℝ), (9/2 : ℝ)) := by
  rw [vtx_eq_of (i := 25) (a := 19) (b := 9/2) rfl]; try norm_num

theorem vtx26 : P.vtx 26 = ((19 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 26) (a := 19) (b := 4) rfl]; try norm_num

theorem vtx27 : P.vtx 27 = ((52/3 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 27) (a := 52/3) (b := 4) rfl]; try norm_num

theorem vtx28 : P.vtx 28 = ((52/3 : ℝ), (83/20 : ℝ)) := by
  rw [vtx_eq_of (i := 28) (a := 52/3) (b := 83/20) rfl]; try norm_num

theorem vtx29 : P.vtx 29 = ((101/6 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 29) (a := 101/6) (b := 4) rfl]; try norm_num

theorem vtx30 : P.vtx 30 = ((16 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 30) (a := 16) (b := 4) rfl]; try norm_num

theorem vtx31 : P.vtx 31 = ((16 : ℝ), (1776/375 : ℝ)) := by
  rw [vtx_eq_of (i := 31) (a := 16) (b := 1776/375) rfl]; try norm_num

theorem vtx32 : P.vtx 32 = ((12 : ℝ), (2486/375 : ℝ)) := by
  rw [vtx_eq_of (i := 32) (a := 12) (b := 2486/375) rfl]; try norm_num

theorem vtx33 : P.vtx 33 = ((12 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 33) (a := 12) (b := 4) rfl]; try norm_num

theorem vtx34 : P.vtx 34 = ((53/5 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 34) (a := 53/5) (b := 4) rfl]; try norm_num

theorem vtx35 : P.vtx 35 = ((53/5 : ℝ), (8 : ℝ)) := by
  rw [vtx_eq_of (i := 35) (a := 53/5) (b := 8) rfl]; try norm_num

theorem vtx36 : P.vtx 36 = ((21/2 : ℝ), (8 : ℝ)) := by
  rw [vtx_eq_of (i := 36) (a := 21/2) (b := 8) rfl]; try norm_num

theorem vtx37 : P.vtx 37 = ((21/2 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 37) (a := 21/2) (b := 4) rfl]; try norm_num

theorem vtx38 : P.vtx 38 = ((8 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 38) (a := 8) (b := 4) rfl]; try norm_num

theorem vtx39 : P.vtx 39 = ((8 : ℝ), (294/47 : ℝ)) := by
  rw [vtx_eq_of (i := 39) (a := 8) (b := 294/47) rfl]; try norm_num

theorem vtx40 : P.vtx 40 = ((4 : ℝ), (280/47 : ℝ)) := by
  rw [vtx_eq_of (i := 40) (a := 4) (b := 280/47) rfl]; try norm_num

theorem vtx41 : P.vtx 41 = ((4 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 41) (a := 4) (b := 4) rfl]; try norm_num

theorem vtx42 : P.vtx 42 = ((21/10 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 42) (a := 21/10) (b := 4) rfl]; try norm_num

theorem vtx43 : P.vtx 43 = ((2 : ℝ), (9/2 : ℝ)) := by
  rw [vtx_eq_of (i := 43) (a := 2) (b := 9/2) rfl]; try norm_num

theorem vtx44 : P.vtx 44 = ((2 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 44) (a := 2) (b := 4) rfl]; try norm_num

theorem vtx45 : P.vtx 45 = ((0 : ℝ), (4 : ℝ)) := by
  rw [vtx_eq_of (i := 45) (a := 0) (b := 4) rfl]; try norm_num

theorem vtx46 : P.vtx 46 = ((0 : ℝ), (9/5 : ℝ)) := by
  rw [vtx_eq_of (i := 46) (a := 0) (b := 9/5) rfl]; try norm_num

theorem vtx49 : P.vtx 49 = ((0 : ℝ), (17/10 : ℝ)) := by
  rw [vtx_eq_of (i := 49) (a := 0) (b := 17/10) rfl]; try norm_num

/-- A point of the segment outside `U` blocks the view (explicit coordinates). -/
theorem not_sees_wit {p q : Point} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hw : ((p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) : Point) ∉ U) : ¬ P.Sees p q :=
  not_sees_of_witness h0 h1 hw

/-- Blocking by the vertical edge `i → i + 1` (with `i + 1 < 50`). -/
theorem block_v {i : ℕ} (hi : i + 1 < 50) {e y₁ y₂ : ℝ} (hv₁ : P.vtx i = (e, y₁))
    (hv₂ : P.vtx (i + 1) = (e, y₂)) {p q : Point} (hp : p.1 < e) (hq : e < q.1)
    (h : (y₁ * (q.1 - p.1) < p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) ∧
          p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) < y₂ * (q.1 - p.1)) ∨
         (y₂ * (q.1 - p.1) < p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) ∧
          p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) < y₁ * (q.1 - p.1))) :
    ¬ P.Sees p q :=
  not_sees_vertical' (by rw [P_n]; omega) hv₁ (by rw [P_n, Nat.mod_eq_of_lt hi]; exact hv₂) hp hq h

/-- Blocking by the horizontal edge `i → i + 1` (with `i + 1 < 50`). -/
theorem block_h {i : ℕ} (hi : i + 1 < 50) {f x₁ x₂ : ℝ} (hv₁ : P.vtx i = (x₁, f))
    (hv₂ : P.vtx (i + 1) = (x₂, f)) {p q : Point} (hp : p.2 < f) (hq : f < q.2)
    (h : (x₁ * (q.2 - p.2) < p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) ∧
          p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) < x₂ * (q.2 - p.2)) ∨
         (x₂ * (q.2 - p.2) < p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) ∧
          p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) < x₁ * (q.2 - p.2))) :
    ¬ P.Sees p q :=
  not_sees_horizontal (by rw [P_n]; omega) hv₁ (by rw [P_n, Nat.mod_eq_of_lt hi]; exact hv₂) hp hq
    h

/-- A point of the edge `i → i + 1` lies in the region. -/
theorem mem_filled_of_edge {i : ℕ} (hi : i + 1 < 50) {u v : Point} (hu : P.vtx i = u)
    (hv : P.vtx (i + 1) = v) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) {q : Point}
    (hq : q = (u.1 + t * (v.1 - u.1), u.2 + t * (v.2 - u.2))) : q ∈ P.filled := by
  refine Or.inl ⟨i, by rw [P_n]; omega, ?_⟩
  simp only [Polygon.edge, P_n, Nat.mod_eq_of_lt hi, hu, hv]
  exact ⟨t, h0, h1, hq⟩

/-- A vertex lies in the region. -/
theorem vtx_mem {i : ℕ} (hi : i < 50) {u : Point} (hu : P.vtx i = u) : u ∈ P.filled := by
  rw [← hu]; exact vtx_mem_filled (by rw [P_n]; exact hi)

end

end ArtGallery.Irrational
