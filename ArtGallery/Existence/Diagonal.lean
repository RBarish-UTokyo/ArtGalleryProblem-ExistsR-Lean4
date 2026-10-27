module

public import ArtGallery.Existence.Convex
public import ArtGallery.Existence.Arc

/-!
# Existence of an interior diagonal

Every simple polygon with at least four vertices has a diagonal (`IsDiagonal`, from
`ArtGallery.Existence.Arc`) whose chord lies in the filled region (`exists_diagonal`).

The argument (after rotating so that vertex `0` is lexicographically smallest, see
`ArtGallery.Existence.Convex`): let `u = vtx (n-1)`, `v = vtx 0`, `w = vtx 1` and
`Δ = convexHull {u, v, w}`; the corner at `v` is strictly convex and the open sector at `v` is
interior.  Write `β = bary₂ u v w` for the barycentric weight at `v`.

* **No crossing** (`bary₂_le_of_mem_edge`): if every vertex of `P` in `Δ` other than `v` has
  `β ≤ c`, then every point of a non-incident edge lying in `Δ` has `β ≤ c`.  (Otherwise the
  edge, whose endpoints are below the level or outside `Δ`, would leave the cap `{β > c} ∩ Δ`
  through a side `u v` or `v w` at a point that is not `u`, `v` or `w`, contradicting
  simplicity; the exit point is found with the intermediate value theorem,
  `exists_zero_of_affine_pair`.)
* If no vertex other than `u, v, w` lies in `Δ`, the chord `w u` is an interior diagonal
  (`chord_base_not_mem_boundary`); otherwise the chord from `v` to a vertex of `Δ` maximising
  `β` is (`chord_apex_not_mem_boundary`).
* The open chord avoids the boundary and is connected, and it is joined to the interior sector
  at `v` (directly, or through the open triangle), so the whole chord lies in `P.filled`
  (`segment_subset_filled_of_open`).
* `isDiagonal_rotate` transfers the conclusion back through the rotation.

Provenance: adapted from `Chazelle/Existence/Diagonal.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`; the lexicographic order is imported from `ArtGallery.Geometry.Lex`.
-/

namespace ArtGallery.Existence
open ArtGallery.Programs (lexLE lexLT)

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan

open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp det_cyclic det_cyclic_right det_swap12
  det_swap13 det_swap23 det_self_left det_self_right det_self_outer exists_lerp_of_det_eq_zero
  det_eq_zero_of_mem_segment lerp_zero lerp_one lerp_injective lerp_mem_segment point_ext
  point_ext_iff mem_segment_iff_lerp ne_of_det_ne_zero continuous_lerp segment_subset_of_convex
  segment_convex convex_triangle vertex_mem_triangle_left vertex_mem_triangle_mid
  vertex_mem_triangle_right bary₁ bary₂ bary₃ bary₁_lerp bary₂_lerp bary₃_lerp
  mem_triangle_iff_bary bary_sum mem_segment_of_bary₁_eq_zero mem_segment_of_bary₃_eq_zero
  bary₁_eq_zero_of_mem_segment bary₃_eq_zero_of_mem_segment bary₁_vertex_left bary₁_vertex_mid
  bary₁_vertex_right bary₂_vertex_left bary₂_vertex_mid bary₂_vertex_right bary₃_vertex_left
  bary₃_vertex_mid bary₃_vertex_right)

/-! ### Affine functions along a segment -/

/-- Composition of `lerp` along one line. -/
theorem lerp_lerp (a b : Point) (s₁ s₂ τ : ℝ) :
    lerp (lerp a b s₁) (lerp a b s₂) τ = lerp a b ((1 - τ) * s₁ + τ * s₂) := by
  apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> ring

/-- A point of a line lying (in parameter) between two points of the line is in their segment. -/
theorem lerp_mem_segment_lerp (a b : Point) {s₁ s₂ s : ℝ} (h1 : s₁ ≤ s) (h2 : s ≤ s₂) :
    lerp a b s ∈ ArtGallery.segment (lerp a b s₁) (lerp a b s₂) := by
  rcases h1.lt_or_eq with h1 | rfl
  · have hd : 0 < s₂ - s₁ := by linarith
    refine mem_segment_iff_lerp.2 ⟨(s - s₁) / (s₂ - s₁), div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith), ?_⟩
    rw [lerp_lerp]
    congr 1
    field_simp
    ring
  · exact left_mem_segment _ _

/-- **Exit point.**  Two affine functions on `[0,1]`, both nonnegative at `0` and at least one
of them negative at `1`, have a common point of `[0,1]` where both are nonnegative and one of
them vanishes. -/
theorem exists_zero_of_affine_pair {α γ : ℝ → ℝ}
    (hα : ∀ t, α t = (1 - t) * α 0 + t * α 1) (hγ : ∀ t, γ t = (1 - t) * γ 0 + t * γ 1)
    (h0 : 0 ≤ α 0) (h0' : 0 ≤ γ 0) (h1 : α 1 < 0 ∨ γ 1 < 0) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ α t ∧ 0 ≤ γ t ∧ (α t = 0 ∨ γ t = 0) := by
  have hαc : Continuous α := by
    have : α = fun t => (1 - t) * α 0 + t * α 1 := funext hα
    rw [this]; fun_prop
  have hγc : Continuous γ := by
    have : γ = fun t => (1 - t) * γ 0 + t * γ 1 := funext hγ
    rw [this]; fun_prop
  have hm : Continuous fun t => min (α t) (γ t) := hαc.min hγc
  have hmem : (0 : ℝ) ∈ Icc (min (α 1) (γ 1)) (min (α 0) (γ 0)) := by
    refine ⟨?_, le_min h0 h0'⟩
    rcases h1 with h1 | h1
    · exact (min_le_left _ _).trans h1.le
    · exact (min_le_right _ _).trans h1.le
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := intermediate_value_Icc' zero_le_one hm.continuousOn hmem
  simp only at ht
  refine ⟨t, ht0, ht1, (le_min_iff.1 ht.ge).1, (le_min_iff.1 ht.ge).2, ?_⟩
  rcases min_eq_iff.1 ht with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ### Leaving a cap of a triangle through a side -/

/-- **Side point.**  Let `p` be a point of the segment `a b` lying in the triangle `u v w` with
`bary₂ p > c ≥ 0`, and let the endpoint `b` have `bary₂ b ≥ bary₂ p`, while `bary₂ b ≤ c`
whenever `b` is in the triangle.  Then between `p` and `b` there is a point of the triangle
with `bary₂ > c` on the side `v w` (`bary₁ = 0`) or on the side `u v` (`bary₃ = 0`). -/
theorem exists_side_point {u v w : Point} (hdet : det u v w ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    {a b p : Point} (hp : p ∈ ArtGallery.segment a b)
    (hpΔ : p ∈ convexHull ℝ ({u, v, w} : Set Point)) (hpc : c < bary₂ u v w p)
    (hb : bary₂ u v w p ≤ bary₂ u v w b)
    (hbΔ : b ∈ convexHull ℝ ({u, v, w} : Set Point) → bary₂ u v w b ≤ c) :
    ∃ y ∈ ArtGallery.segment a b, y ∈ convexHull ℝ ({u, v, w} : Set Point) ∧
      c < bary₂ u v w y ∧ (bary₁ u v w y = 0 ∨ bary₃ u v w y = 0) := by
  have hbΔ' : b ∉ convexHull ℝ ({u, v, w} : Set Point) := fun h => by linarith [hbΔ h]
  have hbneg : bary₁ u v w b < 0 ∨ bary₃ u v w b < 0 := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact hbΔ' ((mem_triangle_iff_bary hdet).2 ⟨hcon.1, by linarith, hcon.2⟩)
  obtain ⟨hp1, -, hp3⟩ := (mem_triangle_iff_bary hdet).1 hpΔ
  obtain ⟨t, ht0, ht1, hαt, hγt, hzero⟩ := exists_zero_of_affine_pair
    (α := fun t => bary₁ u v w (lerp p b t)) (γ := fun t => bary₃ u v w (lerp p b t))
    (fun t => by simp only [lerp_zero, lerp_one, bary₁_lerp])
    (fun t => by simp only [lerp_zero, lerp_one, bary₃_lerp])
    (by simpa using hp1) (by simpa using hp3) (by simpa using hbneg)
  refine ⟨lerp p b t, ?_, ?_, ?_, hzero⟩
  · exact segment_subset_of_convex (segment_convex a b) hp (right_mem_segment a b)
      (lerp_mem_segment p b ht0 ht1)
  · refine (mem_triangle_iff_bary hdet).2 ⟨hαt, ?_, hγt⟩
    rw [bary₂_lerp]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (by linarith : 0 ≤ bary₂ u v w p),
      mul_nonneg ht0 (by linarith : 0 ≤ bary₂ u v w b)]
  · rw [bary₂_lerp]
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hb)]

/-- **No transversal crossing of the base.**  Let `E` be a set (an edge) whose points in the
triangle `u v w` all have `bary₂ ≤ 0`, containing the segment from `q` to `b`, where `q` is a
point of the open base `u w` (`bary₁ q, bary₃ q > 0`, `bary₂ q = 0`) and `b` is outside the
triangle with `bary₂ b > 0`.  This is impossible. -/
theorem no_transversal {u v w : Point} (hdet : det u v w ≠ 0) {E : Set Point}
    (hE : ∀ p ∈ E, p ∈ convexHull ℝ ({u, v, w} : Set Point) → bary₂ u v w p ≤ 0)
    {q b : Point} (hqb : ArtGallery.segment q b ⊆ E)
    (hq1 : 0 < bary₁ u v w q) (hq3 : 0 < bary₃ u v w q) (hq2 : bary₂ u v w q = 0)
    (hb : 0 < bary₂ u v w b) (hbΔ : b ∉ convexHull ℝ ({u, v, w} : Set Point)) : False := by
  have hbneg : bary₁ u v w b < 0 ∨ bary₃ u v w b < 0 := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact hbΔ ((mem_triangle_iff_bary hdet).2 ⟨hcon.1, hb.le, hcon.2⟩)
  obtain ⟨t, ht0, ht1, hαt, hγt, hzero⟩ := exists_zero_of_affine_pair
    (α := fun t => bary₁ u v w (lerp q b t)) (γ := fun t => bary₃ u v w (lerp q b t))
    (fun t => by simp only [lerp_zero, lerp_one, bary₁_lerp])
    (fun t => by simp only [lerp_zero, lerp_one, bary₃_lerp])
    (by simpa using hq1.le) (by simpa using hq3.le) (by simpa using hbneg)
  have ht0' : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · subst h
      rw [lerp_zero] at hzero
      rcases hzero with h | h <;> linarith
  have hy : lerp q b t ∈ E := hqb (lerp_mem_segment q b ht0 ht1)
  have hyΔ : lerp q b t ∈ convexHull ℝ ({u, v, w} : Set Point) := by
    refine (mem_triangle_iff_bary hdet).2 ⟨hαt, ?_, hγt⟩
    rw [bary₂_lerp, hq2]
    nlinarith [mul_pos ht0' hb]
  have := hE _ hy hyΔ
  rw [bary₂_lerp, hq2] at this
  nlinarith [mul_pos ht0' hb]

/-- In the open convex sector at `v`: a point with positive first and third barycentric
coordinates with respect to `u v w` satisfies `0 < σ * det u v x` and `0 < σ * det v w x`
whenever `0 < σ * det u v w`. -/
theorem sector_of_bary_pos {u v w : Point} {σ : ℝ} (hpos : 0 < σ * det u v w) {x : Point}
    (hx1 : 0 < bary₁ u v w x) (hx3 : 0 < bary₃ u v w x) :
    0 < σ * det u v x ∧ 0 < σ * det v w x := by
  have hdet : det u v w ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  constructor
  · have : det u v x = bary₃ u v w x * det u v w := by
      unfold bary₃; rw [div_mul_cancel₀ _ hdet]
    rw [this, mul_left_comm]
    exact mul_pos hx3 hpos
  · have : det v w x = bary₁ u v w x * det u v w := by
      unfold bary₁; rw [div_mul_cancel₀ _ hdet, det_cyclic x v w]
    rw [this, mul_left_comm]
    exact mul_pos hx1 hpos

/-! ### Edges of a simple polygon and the fan triangle at vertex `0`

Throughout, `u = P.vtx (P.n - 1)`, `v = P.vtx 0`, `w = P.vtx 1`, and the triangle is
`convexHull ℝ {u, v, w}`. -/

/-- A point of an edge not incident to vertex `0` that lies on one of the two edges at vertex
`0` is the far endpoint of that edge. -/
theorem eq_of_mem_edge_of_mem_side {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (hi0 : i ≠ 0) (hin : i ≠ P.n - 1) {y : Point} (hy : y ∈ P.edge i)
    (hside : y ∈ ArtGallery.segment (P.vtx 0) (P.vtx 1) ∨
      y ∈ ArtGallery.segment (P.vtx (P.n - 1)) (P.vtx 0)) :
    y = P.vtx 1 ∨ y = P.vtx (P.n - 1) := by
  have hn := simple_three_le hP
  have h0 : 0 < P.n := by omega
  have hv : P.vtx 0 ∉ P.edge i := by
    intro h
    rcases (simple_vtx_mem_edge_iff hP h0 hi).1 h with h | h
    · exact hi0 h
    · rw [prevIdx_zero P h0] at h; exact hin h
  rcases hside with h | h
  · rw [← edge_zero P (by omega)] at h
    rcases simple_endpoint_of_mem_two hP h0 hi (Ne.symm hi0) h hy with h' | h'
    · rw [h'] at hy; exact absurd hy hv
    · rw [succ_zero_mod P (by omega)] at h'; exact Or.inl h'
  · rw [← edge_last P h0] at h
    rcases simple_endpoint_of_mem_two hP (by omega) hi (Ne.symm hin) h hy with h' | h'
    · exact Or.inr h'
    · rw [succ_last_mod P h0] at h'; rw [h'] at hy; exact absurd hy hv

/-- **No crossing.**  Let `c ≥ 0` and suppose every vertex of `P` in the fan triangle
`u v w`, other than `v`, has `bary₂ ≤ c`.  Then every point of an edge not incident to `v`
that lies in the triangle has `bary₂ ≤ c`. -/
theorem bary₂_le_of_mem_edge {P : Polygon} (hP : P.Simple)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hvert : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j) ≤ c)
    {i : ℕ} (hi : i < P.n) (hi0 : i ≠ 0) (hin : i ≠ P.n - 1) {p : Point} (hp : p ∈ P.edge i)
    (hpΔ : p ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point)) :
    bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) p ≤ c := by
  have hn := simple_three_le hP
  by_contra hlt
  rw [not_le] at hlt
  have hsucc : (i + 1) % P.n = i + 1 := Nat.mod_eq_of_lt (by omega)
  have haΔ := hvert i hi hi0
  have hbΔ := hvert ((i + 1) % P.n) (Nat.mod_lt _ (by omega)) (by rw [hsucc]; omega)
  have hpab : p ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) := hp
  have key : ∃ y ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)),
      y ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) ∧
        c < bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) y ∧
        (bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) y = 0 ∨
          bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) y = 0) := by
    obtain ⟨t, ht0, ht1, hpt⟩ := mem_segment_iff_lerp.1 hpab
    rcases le_or_gt (bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx i))
      (bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx ((i + 1) % P.n))) with hab | hab
    · refine exists_side_point hdet hc hpab hpΔ hlt ?_ hbΔ
      rw [hpt, bary₂_lerp]
      nlinarith [mul_le_mul_of_nonneg_left hab (sub_nonneg.2 ht1)]
    · have hpa : bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) p ≤
          bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx i) := by
        rw [hpt, bary₂_lerp]
        nlinarith [mul_le_mul_of_nonneg_left hab.le ht0]
      obtain ⟨y, hy, hyΔ, hyc, hyz⟩ := exists_side_point hdet hc
        (by rw [segment_comm]; exact hpab) hpΔ hlt hpa haΔ
      exact ⟨y, by rw [segment_comm]; exact hy, hyΔ, hyc, hyz⟩
  obtain ⟨y, hy, hyΔ, hyc, hyz⟩ := key
  have hside : y ∈ ArtGallery.segment (P.vtx 0) (P.vtx 1) ∨
      y ∈ ArtGallery.segment (P.vtx (P.n - 1)) (P.vtx 0) := by
    rcases hyz with h | h
    · exact Or.inl (mem_segment_of_bary₁_eq_zero hdet hyΔ h)
    · exact Or.inr (mem_segment_of_bary₃_eq_zero hdet hyΔ h)
  rcases eq_of_mem_edge_of_mem_side hP hi hi0 hin hy hside with h | h
  · rw [h, bary₂_vertex_right] at hyc; linarith
  · rw [h, bary₂_vertex_left] at hyc; linarith

/-- A vertex of `P` in the fan triangle, other than vertices `0` and `1`, is off the edge
`v w`: its first barycentric coordinate is positive. -/
theorem bary₁_vtx_pos {P : Polygon} (hP : P.Simple)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point)) :
    0 < bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k) := by
  have hn := simple_three_le hP
  obtain ⟨h1, -, -⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  refine lt_of_le_of_ne h1 fun h => ?_
  have hmem := mem_segment_of_bary₁_eq_zero hdet hkΔ h.symm
  rw [← edge_zero P (by omega)] at hmem
  rcases eq_endpoint_of_vtx_mem_edge hP hk (by omega) hmem with h' | h'
  · exact hk0 (simple_vtx_inj hP hk (by omega) h')
  · rw [succ_zero_mod P (by omega)] at h'
    exact hk1 (simple_vtx_inj hP hk (by omega) h')

/-- A vertex of `P` in the fan triangle, other than vertices `0` and `n - 1`, is off the edge
`u v`: its third barycentric coordinate is positive. -/
theorem bary₃_vtx_pos {P : Polygon} (hP : P.Simple)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk0 : k ≠ 0) (hkn : k ≠ P.n - 1)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point)) :
    0 < bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k) := by
  have hn := simple_three_le hP
  obtain ⟨-, -, h3⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  refine lt_of_le_of_ne h3 fun h => ?_
  have hmem := mem_segment_of_bary₃_eq_zero hdet hkΔ h.symm
  rw [← edge_last P (by omega)] at hmem
  rcases eq_endpoint_of_vtx_mem_edge hP hk (by omega) hmem with h' | h'
  · exact hkn (simple_vtx_inj hP hk (by omega) h')
  · rw [succ_last_mod P (by omega)] at h'
    exact hk0 (simple_vtx_inj hP hk (by omega) h')

/-- Under the no-crossing hypothesis with level `0`, the open fan triangle avoids the
boundary. -/
theorem interior_fan_not_mem_boundary {P : Polygon} (hP : P.Simple)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0)
    (hvert : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j) ≤ 0)
    {x : Point} (hx1 : 0 < bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) x)
    (hx2 : 0 < bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) x)
    (hx3 : 0 < bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) x) : x ∉ P.boundary := by
  have hn := simple_three_le hP
  rintro ⟨i, hi, hxi⟩
  have hxΔ : x ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) :=
    (mem_triangle_iff_bary hdet).2 ⟨hx1.le, hx2.le, hx3.le⟩
  by_cases hi0 : i = 0
  · subst hi0
    rw [edge_zero P (by omega)] at hxi
    have := bary₁_eq_zero_of_mem_segment (a := P.vtx (P.n - 1)) hxi
    linarith
  by_cases hin : i = P.n - 1
  · subst hin
    rw [edge_last P (by omega)] at hxi
    have := bary₃_eq_zero_of_mem_segment (c := P.vtx 1) hxi
    linarith
  have := bary₂_le_of_mem_edge hP hdet le_rfl hvert hi hi0 hin hxi hxΔ
  linarith

/-! ### The two candidate chords avoid the boundary -/

/-- **The chord to a maximal vertex avoids the boundary.**  Let `vtx k` (`2 ≤ k ≤ n - 2`) be
a vertex in the fan triangle maximising `bary₂` among the vertices of the triangle other than
`v`.  Then the open chord from `v` to `vtx k` avoids the boundary. -/
theorem chord_apex_not_mem_boundary {P : Polygon} (hP : P.Simple)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk2 : 2 ≤ k) (hkn : k + 2 ≤ P.n)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point))
    (hmax : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j) ≤
          bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k)) :
    ∀ q ∈ ArtGallery.segment (P.vtx 0) (P.vtx k), q ≠ P.vtx 0 → q ≠ P.vtx k → q ∉ P.boundary := by
  intro q hq hqv hqz hqB
  have hn := simple_three_le hP
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  have ht0' : 0 < t := lt_of_le_of_ne ht0 fun h => hqv (by rw [← h, lerp_zero])
  have ht1' : t < 1 := lt_of_le_of_ne ht1 fun h => hqz (by rw [h, lerp_one])
  have hz1 := bary₁_vtx_pos hP hdet hk (by omega) (by omega) hkΔ
  have hz3 := bary₃_vtx_pos hP hdet hk (by omega) (by omega) hkΔ
  obtain ⟨-, hz2, -⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  have hzsum := bary_sum hdet (P.vtx k)
  have hqΔ : lerp (P.vtx 0) (P.vtx k) t ∈
      convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) :=
    segment_subset_of_convex (convex_triangle _ _ _) (vertex_mem_triangle_mid _ _ _) hkΔ hq
  have hq2 : bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k) <
      bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (lerp (P.vtx 0) (P.vtx k) t) := by
    rw [bary₂_lerp, bary₂_vertex_mid hdet]
    nlinarith [mul_pos (sub_pos.2 ht1') (add_pos hz1 hz3)]
  obtain ⟨i, hi, hqi⟩ := hqB
  by_cases hi0 : i = 0
  · subst hi0
    rw [edge_zero P (by omega)] at hqi
    have := bary₁_eq_zero_of_mem_segment (a := P.vtx (P.n - 1)) hqi
    rw [bary₁_lerp, bary₁_vertex_mid] at this
    nlinarith
  by_cases hin : i = P.n - 1
  · subst hin
    rw [edge_last P (by omega)] at hqi
    have := bary₃_eq_zero_of_mem_segment (c := P.vtx 1) hqi
    rw [bary₃_lerp, bary₃_vertex_mid] at this
    nlinarith
  have := bary₂_le_of_mem_edge hP hdet hz2 hmax hi hi0 hin hqi hqΔ
  linarith

/-- If no vertex other than `u, v, w` lies in the fan triangle, the no-crossing hypothesis
holds with level `0`. -/
theorem vert_le_zero_of_none {P : Polygon}
    (hnone : ∀ j, j < P.n →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = P.n - 1) :
    ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j) ≤ 0 := by
  intro j hj hj0 hjΔ
  rcases hnone j hj hjΔ with h | h | h
  · exact absurd h hj0
  · rw [h, bary₂_vertex_right]
  · rw [h, bary₂_vertex_left]

/-- **The base chord avoids the boundary.**  If no vertex other than `u, v, w` lies in the fan
triangle (and `n ≥ 4`), the open chord from `w = vtx 1` to `u = vtx (n - 1)` avoids the
boundary. -/
theorem chord_base_not_mem_boundary {P : Polygon} (hP : P.Simple) (h4 : 4 ≤ P.n)
    (hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0)
    (hnone : ∀ j, j < P.n →
      P.vtx j ∈ convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = P.n - 1) :
    ∀ q ∈ ArtGallery.segment (P.vtx 1) (P.vtx (P.n - 1)),
      q ≠ P.vtx 1 → q ≠ P.vtx (P.n - 1) → q ∉ P.boundary := by
  intro q hq hqw hqu hqB
  have hn := simple_three_le hP
  have hvert := vert_le_zero_of_none hnone
  set u := P.vtx (P.n - 1) with hu
  set v := P.vtx 0 with hv
  set w := P.vtx 1 with hw
  set Δ := convexHull ℝ ({u, v, w} : Set Point) with hΔ
  have hwu : w ≠ u := simple_vtx_ne hP (by omega) (by omega) (by omega)
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  have ht0' : 0 < t := lt_of_le_of_ne ht0 fun h => hqw (by rw [← h, lerp_zero])
  have ht1' : t < 1 := lt_of_le_of_ne ht1 fun h => hqu (by rw [h, lerp_one])
  have hq1 : bary₁ u v w (lerp w u t) = t := by
    rw [bary₁_lerp, bary₁_vertex_right, bary₁_vertex_left hdet]; ring
  have hq3 : bary₃ u v w (lerp w u t) = 1 - t := by
    rw [bary₃_lerp, bary₃_vertex_right hdet, bary₃_vertex_left]; ring
  have hq2 : bary₂ u v w (lerp w u t) = 0 := by
    rw [bary₂_lerp, bary₂_vertex_right, bary₂_vertex_left]; ring
  have hqΔ : lerp w u t ∈ Δ :=
    (mem_triangle_iff_bary hdet).2 ⟨by linarith, by linarith, by linarith⟩
  -- `q` is not a vertex
  have hqvtx : ∀ j, j < P.n → lerp w u t ≠ P.vtx j := by
    intro j hj h
    have hjΔ : P.vtx j ∈ Δ := by rw [← h]; exact hqΔ
    rcases hnone j hj hjΔ with h' | h' | h'
    · rw [h'] at h
      have := hq2
      rw [h, bary₂_vertex_mid hdet] at this
      exact one_ne_zero this
    · rw [h'] at h; exact hqw h
    · rw [h'] at h; exact hqu h
  obtain ⟨i, hi, hqi⟩ := hqB
  by_cases hi0 : i = 0
  · subst hi0
    rw [edge_zero P (by omega)] at hqi
    have := bary₁_eq_zero_of_mem_segment (a := u) hqi
    linarith
  by_cases hin : i = P.n - 1
  · subst hin
    rw [edge_last P (by omega)] at hqi
    have := bary₃_eq_zero_of_mem_segment (c := w) hqi
    linarith
  have hD : ∀ p ∈ P.edge i, p ∈ Δ → bary₂ u v w p ≤ 0 := fun p hp hpΔ =>
    bary₂_le_of_mem_edge hP hdet le_rfl hvert hi hi0 hin hp hpΔ
  have hsucc : (i + 1) % P.n = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hqab : lerp w u t ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) := hqi
  -- endpoints in the triangle are `u` or `w`
  have haΔ : P.vtx i ∈ Δ → bary₂ u v w (P.vtx i) = 0 := by
    intro h
    rcases hnone i hi h with h' | h' | h'
    · exact absurd h' hi0
    · rw [h', bary₂_vertex_right]
    · exact absurd h' hin
  have hbΔ : P.vtx ((i + 1) % P.n) ∈ Δ → bary₂ u v w (P.vtx ((i + 1) % P.n)) = 0 := by
    intro h
    rcases hnone _ (Nat.mod_lt _ (by omega)) h with h' | h' | h'
    · omega
    · rw [h', bary₂_vertex_right]
    · rw [h', bary₂_vertex_left]
  -- transversal case
  by_cases hpos : 0 < bary₂ u v w (P.vtx i) ∨ 0 < bary₂ u v w (P.vtx ((i + 1) % P.n))
  · rcases hpos with h | h
    · exact no_transversal hdet hD
        (segment_subset_of_convex (segment_convex _ _) hqab (left_mem_segment _ _))
        (by rw [hq1]; exact ht0') (by rw [hq3]; linarith) hq2 h
        (fun hΔ => by linarith [haΔ hΔ])
    · exact no_transversal hdet hD
        (segment_subset_of_convex (segment_convex _ _) hqab (right_mem_segment _ _))
        (by rw [hq1]; exact ht0') (by rw [hq3]; linarith) hq2 h
        (fun hΔ => by linarith [hbΔ hΔ])
  -- collinear case: the edge lies on the line `w u`
  rw [not_or, not_lt, not_lt] at hpos
  obtain ⟨τ, hτ0, hτ1, hqτ⟩ := mem_segment_iff_lerp.1 hqab
  have hβq : (1 - τ) * bary₂ u v w (P.vtx i) + τ * bary₂ u v w (P.vtx ((i + 1) % P.n)) = 0 := by
    rw [← bary₂_lerp, ← hqτ, hq2]
  have hβa : bary₂ u v w (P.vtx i) = 0 := by
    by_contra hne
    have h1 : (1 - τ) * bary₂ u v w (P.vtx i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hpos.1
    have h2 : τ * bary₂ u v w (P.vtx ((i + 1) % P.n)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hτ0 hpos.2
    have h3 : (1 - τ) * bary₂ u v w (P.vtx i) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · have hτ : τ = 1 := by linarith
      rw [hτ, lerp_one] at hqτ
      exact hqvtx _ (Nat.mod_lt _ (by omega)) hqτ
    · exact hne h
  have hβb : bary₂ u v w (P.vtx ((i + 1) % P.n)) = 0 := by
    by_contra hne
    have h1 : (1 - τ) * bary₂ u v w (P.vtx i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hpos.1
    have h2 : τ * bary₂ u v w (P.vtx ((i + 1) % P.n)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hτ0 hpos.2
    have h3 : τ * bary₂ u v w (P.vtx ((i + 1) % P.n)) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · rw [h, lerp_zero] at hqτ
      exact hqvtx _ hi hqτ
    · exact hne h
  have hcol : ∀ x : Point, bary₂ u v w x = 0 → ∃ s, x = lerp w u s := by
    intro x hx
    unfold bary₂ at hx
    rw [div_eq_zero_iff] at hx
    rcases hx with hx | hx
    · exact exists_lerp_of_det_eq_zero hwu (by rw [det_cyclic_right]; exact hx)
    · exact absurd hx hdet
  obtain ⟨sa, hsa⟩ := hcol _ hβa
  obtain ⟨sb, hsb⟩ := hcol _ hβb
  have hts : t = (1 - τ) * sa + τ * sb := by
    apply lerp_injective hwu
    rw [hqτ, hsa, hsb, lerp_lerp]
  -- the endpoints are not in the open base
  have hsa' : sa ≤ 0 ∨ 1 ≤ sa := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    have haΔ' : P.vtx i ∈ Δ := by
      rw [hsa]
      exact segment_subset_of_convex (convex_triangle _ _ _) (vertex_mem_triangle_right _ _ _)
        (vertex_mem_triangle_left _ _ _) (lerp_mem_segment w u hcon.1.le hcon.2.le)
    rcases hnone i hi haΔ' with h | h | h
    · exact hi0 h
    · have : lerp w u sa = lerp w u 0 := by rw [lerp_zero, ← hsa, h]
      have := lerp_injective hwu this
      linarith
    · exact hin h
  have hsb' : sb ≤ 0 ∨ 1 ≤ sb := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    have hbΔ' : P.vtx ((i + 1) % P.n) ∈ Δ := by
      rw [hsb]
      exact segment_subset_of_convex (convex_triangle _ _ _) (vertex_mem_triangle_right _ _ _)
        (vertex_mem_triangle_left _ _ _) (lerp_mem_segment w u hcon.1.le hcon.2.le)
    rcases hnone _ (Nat.mod_lt _ (by omega)) hbΔ' with h | h | h
    · omega
    · have : lerp w u sb = lerp w u 0 := by rw [lerp_zero, ← hsb, h]
      have := lerp_injective hwu this
      linarith
    · have : lerp w u sb = lerp w u 1 := by rw [lerp_one, ← hsb, h]
      have := lerp_injective hwu this
      linarith
  -- hence both `u` and `w` lie on the edge
  have hboth : u ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) ∧
      w ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) := by
    rcases hsa' with hsa' | hsa' <;> rcases hsb' with hsb' | hsb'
    · exfalso
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - τ) hsa'
      have := mul_nonpos_of_nonneg_of_nonpos hτ0 hsb'
      linarith
    · rw [hsa, hsb]
      have e1 := lerp_mem_segment_lerp w u (s₁ := sa) (s₂ := sb) (s := 1) (by linarith) hsb'
      have e2 := lerp_mem_segment_lerp w u (s₁ := sa) (s₂ := sb) (s := 0) hsa' (by linarith)
      rw [lerp_one] at e1
      rw [lerp_zero] at e2
      exact ⟨e1, e2⟩
    · rw [hsa, hsb, segment_comm]
      have e1 := lerp_mem_segment_lerp w u (s₁ := sb) (s₂ := sa) (s := 1) (by linarith) hsa'
      have e2 := lerp_mem_segment_lerp w u (s₁ := sb) (s₂ := sa) (s := 0) hsb' (by linarith)
      rw [lerp_one] at e1
      rw [lerp_zero] at e2
      exact ⟨e1, e2⟩
    · exfalso
      have := mul_le_mul_of_nonneg_left hsa' (by linarith : (0 : ℝ) ≤ 1 - τ)
      have := mul_le_mul_of_nonneg_left hsb' hτ0
      linarith
  have hu_edge : u = P.vtx i ∨ u = P.vtx ((i + 1) % P.n) :=
    eq_endpoint_of_vtx_mem_edge hP (by omega) hi hboth.1
  have hw_edge : w = P.vtx i ∨ w = P.vtx ((i + 1) % P.n) :=
    eq_endpoint_of_vtx_mem_edge hP (by omega) hi hboth.2
  have hi1 : i = 1 := by
    rcases hw_edge with h | h
    · exact (simple_vtx_inj hP (by omega) hi h).symm
    · have := simple_vtx_inj hP (by omega) (Nat.mod_lt _ (by omega)) h
      omega
  rcases hu_edge with h | h
  · exact hin (simple_vtx_inj hP (by omega) hi h).symm
  · have := simple_vtx_inj hP (by omega) (Nat.mod_lt _ (by omega)) h
    omega

/-! ### From the interior sector to the whole chord -/

/-- If an open segment avoids the boundary of a simple polygon, its endpoints lie in the
filled region and one of its points does, then the whole closed segment lies in the filled
region. -/
theorem segment_subset_filled_of_open {P : Polygon} (hP : P.Simple) {a b : Point}
    (ha : a ∈ P.filled) (hb : b ∈ P.filled)
    (hoff : ∀ t ∈ Ioo (0 : ℝ) 1, lerp a b t ∉ P.boundary)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hin : lerp a b t₀ ∈ P.filled) :
    ArtGallery.segment a b ⊆ P.filled := by
  have hS : IsPreconnected (lerp a b '' Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image _ (continuous_lerp a b).continuousOn
  have hSb : lerp a b '' Ioo (0 : ℝ) 1 ⊆ P.boundaryᶜ := by
    rintro _ ⟨t, ht, rfl⟩; exact hoff t ht
  intro p hp
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hp
  rcases ht0.lt_or_eq with ht0 | rfl
  · rcases ht1.lt_or_eq with ht1 | rfl
    · have hoff' := hoff t ⟨ht0, ht1⟩
      rw [mem_filled_iff hP hoff',
        parity_eq_of_isPreconnected P hS hSb ⟨t, ⟨ht0, ht1⟩, rfl⟩ ⟨t₀, ht₀, rfl⟩]
      exact (mem_filled_iff hP (hoff t₀ ht₀)).1 hin
    · rw [lerp_one]; exact hb
  · rw [lerp_zero]; exact ha

/-- Points close to `v` on the open segment from `v` to a point `x` with positive first and
third barycentric coordinates are interior. -/
theorem exists_near_apex_mem_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1)) {x : Point}
    (hx1 : 0 < bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) x)
    (hx3 : 0 < bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) x) :
    ∃ s ∈ Ioo (0 : ℝ) 1, lerp (P.vtx 0) x s ∈ P.filled \ P.boundary := by
  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hP hmin hσ hpos
  obtain ⟨s, hsb, hs⟩ := (((tendsto_lerp_zero (P.vtx 0) x).eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr))).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have h1 : 0 < bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (lerp (P.vtx 0) x s) := by
    rw [bary₁_lerp, bary₁_vertex_mid]; nlinarith [mul_pos hs.1 hx1]
  have h3 : 0 < bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (lerp (P.vtx 0) x s) := by
    rw [bary₃_lerp, bary₃_vertex_mid]; nlinarith [mul_pos hs.1 hx3]
  exact ⟨s, hs, hsec _ hsb (sector_of_bary_pos hpos h1 h3).1 (sector_of_bary_pos hpos h1 h3).2⟩

/-! ### The main theorem -/

/-- **Interior diagonal at a lexicographically smallest vertex.**  A simple polygon with at
least four vertices whose vertex `0` is lexicographically smallest has a diagonal whose chord
lies in the filled region. -/
theorem exists_diagonal_of_lexMin {P : Polygon} (hP : P.Simple) (h4 : 4 ≤ P.n)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) :
    ∃ s L, IsDiagonal P s L ∧
      ArtGallery.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled := by
  classical
  have hn := simple_three_le hP
  have hdet := det_ne_zero_of_lexMin hP hmin
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  set Δ := convexHull ℝ ({P.vtx (P.n - 1), P.vtx 0, P.vtx 1} : Set Point) with hΔ
  set I : Finset ℕ := (Finset.range P.n).filter (fun j => 2 ≤ j ∧ j + 2 ≤ P.n ∧ P.vtx j ∈ Δ)
    with hI
  by_cases hne : I.Nonempty
  · -- a vertex inside the fan: the chord from `v` to a maximal one
    obtain ⟨k, hkI, hmax⟩ := Finset.exists_max_image I
      (fun j => bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j)) hne
    rw [hI, Finset.mem_filter, Finset.mem_range] at hkI
    obtain ⟨hk, hk2, hkn, hkΔ⟩ := hkI
    have hk20 : 0 ≤ bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k) :=
      ((mem_triangle_iff_bary hdet).1 hkΔ).2.1
    have hmax' : ∀ j, j < P.n → j ≠ 0 → P.vtx j ∈ Δ →
        bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx j) ≤
          bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) (P.vtx k) := by
      intro j hj hj0 hjΔ
      by_cases hj1 : j = 1
      · rw [hj1, bary₂_vertex_right]; exact hk20
      by_cases hjn : j = P.n - 1
      · rw [hjn, bary₂_vertex_left]; exact hk20
      exact hmax j (by rw [hI, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by omega, by omega, hjΔ⟩)
    have hvz : P.vtx 0 ≠ P.vtx k := simple_vtx_ne hP (by omega) hk (by omega)
    have hchord := chord_apex_not_mem_boundary hP hdet hk hk2 hkn hkΔ hmax'
    refine ⟨0, k, ⟨hk2, hkn, ?_⟩, ?_⟩
    · rw [Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hk]
      exact hchord
    · rw [Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hk]
      have hz1 := bary₁_vtx_pos hP hdet hk (by omega) (by omega) hkΔ
      have hz3 := bary₃_vtx_pos hP hdet hk (by omega) (by omega) hkΔ
      obtain ⟨s, hs, hsin⟩ := exists_near_apex_mem_interior hP hmin hσ hpos hz1 hz3
      exact segment_subset_filled_of_open hP
        (boundary_subset_filled P (vtx_mem_boundary P (by omega)))
        (boundary_subset_filled P (vtx_mem_boundary P hk))
        (fun t ht => hchord _ (lerp_mem_segment _ _ ht.1.le ht.2.le) (lerp_ne_left hvz ht.1)
          (lerp_ne_right hvz ht.2)) hs hsin.1
  · -- no vertex inside the fan: the chord from `w` to `u`
    have hnone : ∀ j, j < P.n → P.vtx j ∈ Δ → j = 0 ∨ j = 1 ∨ j = P.n - 1 := by
      intro j hj hjΔ
      by_contra hcon
      apply hne
      refine ⟨j, ?_⟩
      rw [hI, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, by omega, by omega, hjΔ⟩
    have hvert := vert_le_zero_of_none hnone
    have hchord := chord_base_not_mem_boundary hP h4 hdet hnone
    have hwu : P.vtx 1 ≠ P.vtx (P.n - 1) := simple_vtx_ne hP (by omega) (by omega) (by omega)
    have hL : (1 + (P.n - 2)) % P.n = P.n - 1 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have h1 : 1 % P.n = 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨1, P.n - 2, ⟨by omega, by omega, ?_⟩, ?_⟩
    · rw [h1, hL]; exact hchord
    · rw [h1, hL]
      -- the midpoint of the base, joined to the sector at `v` through the open triangle
      set m := lerp (P.vtx 1) (P.vtx (P.n - 1)) (1 / 2) with hm
      have hm1 : bary₁ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) m = 1 / 2 := by
        rw [hm, bary₁_lerp, bary₁_vertex_right, bary₁_vertex_left hdet]; ring
      have hm3 : bary₃ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) m = 1 / 2 := by
        rw [hm, bary₃_lerp, bary₃_vertex_right hdet, bary₃_vertex_left]; ring
      have hm2 : bary₂ (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) m = 0 := by
        rw [hm, bary₂_lerp, bary₂_vertex_right, bary₂_vertex_left]; ring
      have hmB : m ∉ P.boundary :=
        hchord m (lerp_mem_segment _ _ (by norm_num) (by norm_num)) (lerp_ne_left hwu (by norm_num))
          (lerp_ne_right hwu (by norm_num))
      have hmoff : ∀ s ∈ Ioc (0 : ℝ) 1, lerp (P.vtx 0) m s ∉ P.boundary := by
        intro s hs
        rcases hs.2.lt_or_eq with hs1 | rfl
        · apply interior_fan_not_mem_boundary hP hdet hvert
          · rw [bary₁_lerp, bary₁_vertex_mid, hm1]; nlinarith [hs.1]
          · rw [bary₂_lerp, bary₂_vertex_mid hdet, hm2]; nlinarith
          · rw [bary₃_lerp, bary₃_vertex_mid, hm3]; nlinarith [hs.1]
        · rw [lerp_one]; exact hmB
      have hmconn : IsPreconnected (lerp (P.vtx 0) m '' Ioc (0 : ℝ) 1) :=
        isPreconnected_Ioc.image _ (continuous_lerp _ _).continuousOn
      have hmsub : lerp (P.vtx 0) m '' Ioc (0 : ℝ) 1 ⊆ P.boundaryᶜ := by
        rintro _ ⟨s, hs, rfl⟩; exact hmoff s hs
      obtain ⟨s, hs, hsin⟩ := exists_near_apex_mem_interior hP hmin hσ hpos
        (by rw [hm1]; norm_num) (by rw [hm3]; norm_num)
      have hm_filled : m ∈ P.filled := by
        rw [mem_filled_iff hP hmB]
        have := parity_eq_of_isPreconnected P hmconn hmsub (x := lerp (P.vtx 0) m 1)
          (y := lerp (P.vtx 0) m s) ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩ ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩
        rw [lerp_one] at this
        rw [this]
        exact (mem_filled_iff hP hsin.2).1 hsin.1
      exact segment_subset_filled_of_open hP
        (boundary_subset_filled P (vtx_mem_boundary P (by omega)))
        (boundary_subset_filled P (vtx_mem_boundary P (by omega)))
        (fun t ht => hchord _ (lerp_mem_segment _ _ ht.1.le ht.2.le) (lerp_ne_left hwu ht.1)
          (lerp_ne_right hwu ht.2)) (t₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ hm_filled

/-- A diagonal of the rotated polygon `P.rotate m` is a diagonal of `P`, with the start index
shifted by `m`. -/
theorem isDiagonal_rotate {P : Polygon} {m s L : ℕ} (hd : IsDiagonal (P.rotate m) s L) :
    IsDiagonal P (m + s) L := by
  obtain ⟨h2, hn, hch⟩ := hd
  rw [n_rotate] at hn
  have h0 : 0 < P.n := by omega
  refine ⟨h2, hn, ?_⟩
  have e1 : (P.rotate m).vtx (s % (P.rotate m).n) = P.vtx ((m + s) % P.n) := by
    rw [n_rotate, vtx_rotate P m (Nat.mod_lt _ h0), Nat.add_mod_mod]
  have e2 : (P.rotate m).vtx ((s + L) % (P.rotate m).n) = P.vtx ((m + s + L) % P.n) := by
    rw [n_rotate, vtx_rotate P m (Nat.mod_lt _ h0), Nat.add_mod_mod, Nat.add_assoc]
  rw [e1, e2, boundary_rotate] at hch
  exact hch

/-- **Every simple polygon with at least four vertices has an interior diagonal**: a diagonal
`(s, L)` in the sense of `IsDiagonal` (the open chord avoids the boundary) whose closed chord
lies in the filled region. -/
theorem exists_diagonal {P : Polygon} (hP : P.Simple) (h4 : 4 ≤ P.n) :
    ∃ s L, IsDiagonal P s L ∧
      ArtGallery.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled := by
  obtain ⟨m, hm, hmin⟩ := exists_lexMin P (by omega)
  have hQ : (P.rotate m).Simple := simple_rotate P m hP
  have hQ4 : 4 ≤ (P.rotate m).n := by rw [n_rotate]; exact h4
  have hQmin : ∀ i, i < (P.rotate m).n → lexLE ((P.rotate m).vtx 0) ((P.rotate m).vtx i) := by
    rw [n_rotate]; exact rotate_lexMin P hm hmin
  obtain ⟨s, L, hd, hsub⟩ := exists_diagonal_of_lexMin hQ hQ4 hQmin
  refine ⟨m + s, L, isDiagonal_rotate hd, ?_⟩
  have h0 : 0 < P.n := by omega
  have e1 : (P.rotate m).vtx (s % (P.rotate m).n) = P.vtx ((m + s) % P.n) := by
    rw [n_rotate, vtx_rotate P m (Nat.mod_lt _ h0), Nat.add_mod_mod]
  have e2 : (P.rotate m).vtx ((s + L) % (P.rotate m).n) = P.vtx ((m + s + L) % P.n) := by
    rw [n_rotate, vtx_rotate P m (Nat.mod_lt _ h0), Nat.add_mod_mod, Nat.add_assoc]
  rw [e1, e2, filled_rotate] at hsub
  exact hsub

end

end ArtGallery.Existence
