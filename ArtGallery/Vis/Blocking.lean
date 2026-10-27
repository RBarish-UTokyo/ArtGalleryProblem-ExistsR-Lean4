module

public import ArtGallery.Vis.Local

/-!
# Visibility library: blocking

**Blocking (T1).** A segment `p q` that properly crosses an edge `u v` of a simple polygon (the
endpoints of each segment strictly on opposite sides of the line of the other) is not contained
in the region: the two segments meet in a point of the open edge, near which the region is a
closed half-plane of the edge (`local_halfplane_sign`), and the segment `p q` has points strictly
on both sides of the edge arbitrarily close to the crossing point.
-/

namespace ArtGallery.Vis

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan
open ArtGallery.Geometry (lerp det_lerp det_lerp_self lerp_mem_segment continuous_lerp)

/-! ### Two real lemmas -/

/-- An affine function of `t` with values of opposite signs at `0` and `1` vanishes in `(0,1)`. -/
theorem exists_root {x y : ℝ} (h : x * y < 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1 - t) * x + t * y = 0 := by
  have hd : 0 < x * x - x * y := by nlinarith [mul_self_nonneg x]
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  have hxx : 0 < x * x := mul_self_pos.2 hx
  have hd' : x * x - x * y ≠ 0 := hd.ne'
  refine ⟨x * x / (x * x - x * y), div_pos hxx hd, (div_lt_one hd).2 (by linarith), ?_⟩
  have e1 : x * x / (x * x - x * y) * (x * x - x * y) = x * x := div_mul_cancel₀ _ hd'
  have e2 : x * ((1 - x * x / (x * x - x * y)) * x + x * x / (x * x - x * y) * y) = 0 := by
    linear_combination -e1
  rcases mul_eq_zero.1 e2 with h' | h'
  · exact absurd h' hx
  · exact h'

/-- A zero of an affine function with values of opposite signs at `0` and `1` lies in `(0,1)`. -/
theorem root_mem_Ioo {x y s : ℝ} (h : x * y < 0) (hs : (1 - s) * x + s * y = 0) :
    0 < s ∧ s < 1 := by
  constructor
  · by_contra hc
    have hc' : s ≤ 0 := not_lt.1 hc
    have e : x * y = s * (x * y) - s * y ^ 2 := by linear_combination y * hs
    nlinarith [mul_nonneg (neg_nonneg.2 hc') (neg_nonneg.2 h.le),
      mul_nonneg (neg_nonneg.2 hc') (sq_nonneg y)]
  · by_contra hc
    have hc' : 1 ≤ s := not_lt.1 hc
    have e : s * (x * y) = (s - 1) * x ^ 2 := by linear_combination x * hs
    nlinarith [mul_nonneg (sub_nonneg.2 hc') (sq_nonneg x),
      mul_pos (lt_of_lt_of_le one_pos hc') (neg_pos.2 h)]

/-! ### Blocking -/

/-- The core of the blocking lemma: if near the point `lerp u v t` the region is a closed
half-plane of the line `u v`, a segment `p q` through that point with endpoints strictly on
opposite sides of the line is not contained in the region. -/
theorem cross_core {P : Polygon} {u v p q : Point} {t σ r : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hr : 0 < r) (hloc : ∀ z ∈ ball (lerp u v t) r, (z ∈ P.filled ↔ 0 ≤ σ * det u v z))
    (h₁ : det u v p * det u v q < 0) (hpq : p ≠ q) (ht : det p q (lerp u v t) = 0)
    (hsees : ArtGallery.segment p q ⊆ P.filled) : False := by
  obtain ⟨s, hs⟩ := Geometry.exists_lerp_of_det_eq_zero hpq ht
  have hs0eq : (1 - s) * det u v p + s * det u v q = 0 := by
    have h := det_lerp u v p q s
    rw [← hs, det_lerp_self] at h
    linarith
  obtain ⟨hs0, hs1⟩ := root_mem_Ioo h₁ hs0eq
  have hmem : ball (lerp u v t) r ∈ 𝓝 (lerp p q s) := by
    rw [← hs]
    exact isOpen_ball.mem_nhds (mem_ball_self hr)
  have hc₁ : ContinuousAt (fun e : ℝ => lerp p q (s + e)) 0 :=
    ((continuous_lerp p q).comp (continuous_const.add continuous_id)).continuousAt
  have hc₂ : ContinuousAt (fun e : ℝ => lerp p q (s - e)) 0 :=
    ((continuous_lerp p q).comp (continuous_const.sub continuous_id)).continuousAt
  have hev₁ : ∀ᶠ e in 𝓝 (0 : ℝ), lerp p q (s + e) ∈ ball (lerp u v t) r :=
    hc₁.eventually_mem (by show ball _ r ∈ 𝓝 (lerp p q (s + 0)); rw [add_zero]; exact hmem)
  have hev₂ : ∀ᶠ e in 𝓝 (0 : ℝ), lerp p q (s - e) ∈ ball (lerp u v t) r :=
    hc₂.eventually_mem (by show ball _ r ∈ 𝓝 (lerp p q (s - 0)); rw [sub_zero]; exact hmem)
  have hm : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  obtain ⟨e, ⟨he1, he2⟩, he3⟩ := (((hev₁.filter_mono nhdsWithin_le_nhds).and
    (hev₂.filter_mono nhdsWithin_le_nhds)).and (Ioo_mem_nhdsGT hm)).exists
  have he0 : 0 < e := he3.1
  have hes : e < s := lt_of_lt_of_le he3.2 (min_le_left _ _)
  have hes' : e < 1 - s := lt_of_lt_of_le he3.2 (min_le_right _ _)
  have f₁ := (hloc _ he1).1 (hsees (lerp_mem_segment p q (by linarith) (by linarith)))
  have f₂ := (hloc _ he2).1 (hsees (lerp_mem_segment p q (by linarith) (by linarith)))
  rw [det_lerp] at f₁ f₂
  have g₁ : (1 - (s + e)) * det u v p + (s + e) * det u v q =
      e * (det u v q - det u v p) := by linear_combination hs0eq
  have g₂ : (1 - (s - e)) * det u v p + (s - e) * det u v q =
      -(e * (det u v q - det u v p)) := by linear_combination hs0eq
  rw [g₁] at f₁
  rw [g₂, mul_neg] at f₂
  have hX : σ * (e * (det u v q - det u v p)) = 0 := by linarith
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  rcases mul_eq_zero.1 hX with h | h
  · exact hσ0 h
  rcases mul_eq_zero.1 h with h | h
  · linarith
  have hpq' : det u v q = det u v p := by linarith
  rw [hpq'] at h₁
  nlinarith [mul_self_nonneg (det u v p)]

/-- **Blocking (T1).** A segment that properly crosses an edge (the endpoints of each segment
strictly on opposite sides of the line of the other) is not contained in the region. -/
theorem not_sees_of_proper_cross {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {p q : Point}
    (h₁ : det (P.vtx i) (P.vtx ((i + 1) % P.n)) p * det (P.vtx i) (P.vtx ((i + 1) % P.n)) q < 0)
    (h₂ : det p q (P.vtx i) * det p q (P.vtx ((i + 1) % P.n)) < 0) :
    ¬ P.Sees p q := by
  intro hsees
  have hpq : p ≠ q := by
    rintro rfl
    simp only [Geometry.det_self_left, zero_mul] at h₂
    exact lt_irrefl _ h₂
  obtain ⟨t, ht0, ht1, ht⟩ := exists_root h₂
  obtain ⟨σ, hσ, r, hr, hloc⟩ := local_halfplane_sign hP hi ht0 ht1
  refine cross_core hσ hr hloc h₁ hpq ?_ hsees
  rw [det_lerp]
  exact ht

end

end ArtGallery.Vis
