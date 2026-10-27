module

public import ArtGallery.Irrational.Region
public import ArtGallery.Vis.API

/-!
# Visibility in `𝒫`

Tools for seeing and not seeing in the polygon `𝒫`, whose region is `U` (`filled_eq_U`):

* `sees_of_convex`, `sees_through_horizontal`, `sees_through_vertical`: a guard sees a point of
  a pocket when the segment passes through the opening of the pocket (the segment is then the
  union of a part in the basic rectangle and a part in the pocket);
* `not_sees_of_witness`: a point of the segment outside `U` blocks the view;
* `not_sees_vertical`, `not_sees_horizontal`: a segment properly crossing a vertical or
  horizontal edge (black box `Polygon.not_sees_of_proper_cross` of `Vis/API`);
* `sees_of_limit`: the points seen from a guard form a closed set.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set Filter Topology ArtGallery.Geometry

theorem sees_iff {p q : Point} : P.Sees p q ↔ ArtGallery.segment p q ⊆ U := by
  rw [Polygon.Sees, filled_eq_U]

theorem sees_symm {p q : Point} (h : P.Sees p q) : P.Sees q p := by
  rw [Polygon.Sees, Geometry.segment_comm]; exact h

/-- A point of the segment outside `U` blocks the view. -/
theorem not_sees_of_witness {p q : Point} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht : lerp p q t ∉ U) : ¬ P.Sees p q := by
  intro h
  exact ht (sees_iff.1 h (lerp_mem_segment p q h0 h1))

theorem hp_subset_U {pc : List HP} (h : pc ∈ pieces) : hp pc ⊆ U := fun _ hp => ⟨pc, h, hp⟩

/-- Two points of a convex part of `U` see each other. -/
theorem sees_of_convex {A : Set Point} (hA : Convex ℝ A) (hAU : A ⊆ U) {p q : Point}
    (hp : p ∈ A) (hq : q ∈ A) : P.Sees p q :=
  sees_iff.2 ((segment_subset_of_convex hA hp hq).trans hAU)

/-- A point `c` of the segment `u w` splits it into two segments. -/
theorem segment_subset_union_of_mem {u w c : Point} (hc : c ∈ ArtGallery.segment u w) :
    ArtGallery.segment u w ⊆ ArtGallery.segment u c ∪ ArtGallery.segment c w := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hc
  rintro p ⟨s, hs0, hs1, rfl⟩
  rcases le_or_gt s t with hst | hst
  · left
    rcases eq_or_lt_of_le ht0 with rfl | ht
    · have : s = 0 := le_antisymm hst hs0
      subst this
      exact ⟨0, le_rfl, zero_le_one, by simp⟩
    · refine ⟨s / t, div_nonneg hs0 ht.le, (div_le_one ht).2 hst, ?_⟩
      ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring
  · right
    have ht1' : t < 1 := lt_of_lt_of_le hst hs1
    refine ⟨(s - t) / (1 - t), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    have h1t : (1 - t) ≠ 0 := by linarith
    ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring

/-- Seeing through an opening: the segment `u w` meets `A ∩ K` in a point `c`, with `u ∈ A`,
`w ∈ K` and `A, K` convex parts of `U`. -/
theorem sees_of_split {A K : Set Point} (hA : Convex ℝ A) (hK : Convex ℝ K) (hAU : A ⊆ U)
    (hKU : K ⊆ U) {u w c : Point} (hu : u ∈ A) (hw : w ∈ K) (hc : c ∈ ArtGallery.segment u w)
    (hcA : c ∈ A) (hcK : c ∈ K) : P.Sees u w := by
  rw [sees_iff]
  refine (segment_subset_union_of_mem hc).trans (union_subset ?_ ?_)
  · exact (segment_subset_of_convex hA hu hcA).trans hAU
  · exact (segment_subset_of_convex hK hcK hw).trans hKU

/-- **Seeing through a horizontal opening** `[a, b] × {yo}`: `u` below (in `A`), `w` above
(in `K`), and the crossing abscissa `N / D` lies in `[a, b]`. -/
theorem sees_through_horizontal {A K : Set Point} (hA : Convex ℝ A) (hK : Convex ℝ K)
    (hAU : A ⊆ U) (hKU : K ⊆ U) {u w : Point} (hu : u ∈ A) (hw : w ∈ K) {yo a b : ℝ}
    (hopen : ∀ x, a ≤ x → x ≤ b → (x, yo) ∈ A ∧ (x, yo) ∈ K) (h1 : u.2 ≤ yo) (h2 : yo ≤ w.2)
    (hD : u.2 < w.2)
    (ha : a * (w.2 - u.2) ≤ u.1 * (w.2 - yo) + w.1 * (yo - u.2))
    (hb : u.1 * (w.2 - yo) + w.1 * (yo - u.2) ≤ b * (w.2 - u.2)) : P.Sees u w := by
  have hDp : 0 < w.2 - u.2 := by linarith
  set x := (u.1 * (w.2 - yo) + w.1 * (yo - u.2)) / (w.2 - u.2) with hx
  have hxa : a ≤ x := by rw [hx, le_div_iff₀ hDp]; linarith
  have hxb : x ≤ b := by rw [hx, div_le_iff₀ hDp]; linarith
  have hc : ((x, yo) : Point) ∈ ArtGallery.segment u w := by
    refine ⟨(yo - u.2) / (w.2 - u.2), div_nonneg (by linarith) hDp.le,
      (div_le_one hDp).2 (by linarith), ?_⟩
    rw [hx]
    ext <;> simp only <;> field_simp <;> ring
  exact sees_of_split hA hK hAU hKU hu hw hc (hopen x hxa hxb).1 (hopen x hxa hxb).2

/-- **Seeing through a vertical opening** `{xo} × [a, b]`: `u` left (in `A`), `w` right
(in `K`), and the crossing ordinate `N / D` lies in `[a, b]`. -/
theorem sees_through_vertical {A K : Set Point} (hA : Convex ℝ A) (hK : Convex ℝ K)
    (hAU : A ⊆ U) (hKU : K ⊆ U) {u w : Point} (hu : u ∈ A) (hw : w ∈ K) {xo a b : ℝ}
    (hopen : ∀ y, a ≤ y → y ≤ b → (xo, y) ∈ A ∧ (xo, y) ∈ K) (h1 : u.1 ≤ xo) (h2 : xo ≤ w.1)
    (hD : u.1 < w.1)
    (ha : a * (w.1 - u.1) ≤ u.2 * (w.1 - xo) + w.2 * (xo - u.1))
    (hb : u.2 * (w.1 - xo) + w.2 * (xo - u.1) ≤ b * (w.1 - u.1)) : P.Sees u w := by
  have hDp : 0 < w.1 - u.1 := by linarith
  set y := (u.2 * (w.1 - xo) + w.2 * (xo - u.1)) / (w.1 - u.1) with hy
  have hya : a ≤ y := by rw [hy, le_div_iff₀ hDp]; linarith
  have hyb : y ≤ b := by rw [hy, div_le_iff₀ hDp]; linarith
  have hc : ((xo, y) : Point) ∈ ArtGallery.segment u w := by
    refine ⟨(xo - u.1) / (w.1 - u.1), div_nonneg (by linarith) hDp.le,
      (div_le_one hDp).2 (by linarith), ?_⟩
    rw [hy]
    ext <;> simp only <;> field_simp <;> ring
  exact sees_of_split hA hK hAU hKU hu hw hc (hopen y hya hyb).1 (hopen y hya hyb).2

/-! ### Blocking by an edge (black box T1) -/

/-- A segment from `p` (left of the vertical edge `x = e`) to `q` (right of it) that crosses the
line `x = e` strictly inside the edge is blocked. -/
theorem not_sees_vertical {i : ℕ} (hi : i < P.n) {e y₁ y₂ : ℝ} (hv₁ : P.vtx i = (e, y₁))
    (hv₂ : P.vtx ((i + 1) % P.n) = (e, y₂)) {p q : Point} (hp : p.1 < e) (hq : e < q.1)
    (h : (y₁ * (q.1 - p.1) - (p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2))) *
      (y₂ * (q.1 - p.1) - (p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2))) < 0) :
    ¬ P.Sees p q := by
  have hy : y₁ ≠ y₂ := by
    rintro rfl; nlinarith [sq_nonneg (y₁ * (q.1 - p.1) - (p.2 * (q.1 - p.1) +
      (e - p.1) * (q.2 - p.2)))]
  have hy' : 0 < (y₂ - y₁) ^ 2 := by
    have : y₂ - y₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    positivity
  apply Polygon.not_sees_of_proper_cross simple_P hi
  · rw [hv₁, hv₂]; unfold det; simp only
    have : (p.1 - e) * (q.1 - e) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith
  · rw [hv₁, hv₂]; unfold det; simp only
    have e1 : (q.1 - p.1) * (y₁ - p.2) - (e - p.1) * (q.2 - p.2) =
        y₁ * (q.1 - p.1) - (p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2)) := by ring
    have e2 : (q.1 - p.1) * (y₂ - p.2) - (e - p.1) * (q.2 - p.2) =
        y₂ * (q.1 - p.1) - (p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2)) := by ring
    rw [e1, e2]; exact h

/-- Variant of `not_sees_vertical` with the crossing height given by two strict bounds. -/
theorem not_sees_vertical' {i : ℕ} (hi : i < P.n) {e y₁ y₂ : ℝ} (hv₁ : P.vtx i = (e, y₁))
    (hv₂ : P.vtx ((i + 1) % P.n) = (e, y₂)) {p q : Point} (hp : p.1 < e) (hq : e < q.1)
    (h : (y₁ * (q.1 - p.1) < p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) ∧
          p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) < y₂ * (q.1 - p.1)) ∨
         (y₂ * (q.1 - p.1) < p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) ∧
          p.2 * (q.1 - p.1) + (e - p.1) * (q.2 - p.2) < y₁ * (q.1 - p.1))) :
    ¬ P.Sees p q := by
  apply not_sees_vertical hi hv₁ hv₂ hp hq
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- A segment from `p` (below the horizontal edge `y = f`) to `q` (above it) crossing the line
`y = f` strictly inside the edge is blocked. -/
theorem not_sees_horizontal {i : ℕ} (hi : i < P.n) {f x₁ x₂ : ℝ} (hv₁ : P.vtx i = (x₁, f))
    (hv₂ : P.vtx ((i + 1) % P.n) = (x₂, f)) {p q : Point} (hp : p.2 < f) (hq : f < q.2)
    (h : (x₁ * (q.2 - p.2) < p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) ∧
          p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) < x₂ * (q.2 - p.2)) ∨
         (x₂ * (q.2 - p.2) < p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) ∧
          p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1) < x₁ * (q.2 - p.2))) :
    ¬ P.Sees p q := by
  have key : (x₁ * (q.2 - p.2) - (p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1))) *
      (x₂ * (q.2 - p.2) - (p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1))) < 0 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hx : x₁ ≠ x₂ := by
    rintro rfl; nlinarith [sq_nonneg (x₁ * (q.2 - p.2) - (p.1 * (q.2 - p.2) +
      (f - p.2) * (q.1 - p.1)))]
  have hx' : 0 < (x₂ - x₁) ^ 2 := by
    have : x₂ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
    positivity
  apply Polygon.not_sees_of_proper_cross simple_P hi
  · rw [hv₁, hv₂]; unfold det; simp only
    have : (p.2 - f) * (q.2 - f) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith
  · rw [hv₁, hv₂]; unfold det; simp only
    have e1 : (q.1 - p.1) * (f - p.2) - (x₁ - p.1) * (q.2 - p.2) =
        -(x₁ * (q.2 - p.2) - (p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1))) := by ring
    have e2 : (q.1 - p.1) * (f - p.2) - (x₂ - p.1) * (q.2 - p.2) =
        -(x₂ * (q.2 - p.2) - (p.1 * (q.2 - p.2) + (f - p.2) * (q.1 - p.1))) := by ring
    rw [e1, e2, neg_mul_neg]; exact key

/-! ### The seen set is closed -/

theorem sees_iff_lerp {g q : Point} : P.Sees g q ↔ ∀ t ∈ Icc (0 : ℝ) 1, lerp g q t ∈ P.filled := by
  rw [Polygon.Sees, segment_eq_image_lerp, image_subset_iff]
  rfl

theorem isClosed_sees (g : Point) : IsClosed {q | P.Sees g q} := by
  have : {q | P.Sees g q} = ⋂ t ∈ Icc (0 : ℝ) 1, (fun q => lerp g q t) ⁻¹' P.filled := by
    ext q; simp only [mem_ofPred_eq, mem_iInter, mem_preimage, sees_iff_lerp]
  rw [this]
  refine isClosed_biInter fun t _ => (Jordan.isClosed_filled P).preimage ?_
  unfold lerp; fun_prop

/-- **Closure argument**: if `g` sees `f s` for all `s ∈ (L, R)`, it sees `f X` for every
`X ∈ [L, R]`. -/
theorem sees_of_limit {g : Point} {f : ℝ → Point} (hf : Continuous f) {L R X : ℝ} (hLR : L < R)
    (hX : X ∈ Icc L R) (h : ∀ s, L < s → s < R → P.Sees g (f s)) : P.Sees g (f X) := by
  have hc : IsClosed (f ⁻¹' {q | P.Sees g q}) := (isClosed_sees g).preimage hf
  have hsub : Ioo L R ⊆ f ⁻¹' {q | P.Sees g q} := fun s hs => h s hs.1 hs.2
  have := closure_minimal hsub hc
  rw [closure_Ioo hLR.ne] at this
  exact this hX

/-! ### Vertices -/

theorem vtx_eq_of {i : ℕ} {a b : ℚ} (h : paperVerts.getD i 0 = (a, b)) :
    P.vtx i = ((a : ℝ), (b : ℝ)) := by
  rw [P, vtx_map_ratPoint, h]; rfl

theorem vtx_mem_filled {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.filled :=
  Or.inl ⟨i, hi, Geometry.left_mem_segment _ _⟩

end

end ArtGallery.Irrational
