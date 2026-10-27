module

public import ArtGallery.Membership.Combinators

/-!
# When do two segments meet?

`segments_meet_iff`: the segments `[p₁, p₂]` and `[p₃, p₄]` meet iff

* their directions are not parallel (`D = (p₂ - p₁) × (p₄ - p₃) ≠ 0`) and the parameters
  `T = (p₃ - p₁) × (p₄ - p₃) / D`, `U = (p₃ - p₁) × (p₂ - p₁) / D` of the intersection point of
  the two lines lie in `[0, 1]`, or
* the directions are parallel and `p₃` or `p₄` lies on `[p₁, p₂]`, or `p₁` lies on `[p₃, p₄]`.

This is the variable-free replacement for the separating lines of the formula SIMPLE.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.Membership Geometry

/-- The parameter of the intersection point along `[p₁, p₂]`. -/
noncomputable def segParT (p1 p2 p3 p4 : Point) : ℝ := crossR p1 p3 p3 p4 / crossR p1 p2 p3 p4

/-- The parameter of the intersection point along `[p₃, p₄]`. -/
noncomputable def segParU (p1 p2 p3 p4 : Point) : ℝ := crossR p1 p3 p1 p2 / crossR p1 p2 p3 p4

/-- The criterion for two segments to meet. -/
def SegMeet (p1 p2 p3 p4 : Point) : Prop :=
  (crossR p1 p2 p3 p4 ≠ 0 ∧ 0 ≤ segParT p1 p2 p3 p4 ∧ segParT p1 p2 p3 p4 ≤ 1 ∧
      0 ≤ segParU p1 p2 p3 p4 ∧ segParU p1 p2 p3 p4 ≤ 1) ∨
    (crossR p1 p2 p3 p4 = 0 ∧ (p3 ∈ ArtGallery.segment p1 p2 ∨ p4 ∈ ArtGallery.segment p1 p2 ∨
      p1 ∈ ArtGallery.segment p3 p4))

theorem mem_seg_of {a b z : Point} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (e1 : z.1 = a.1 + t * (b.1 - a.1)) (e2 : z.2 = a.2 + t * (b.2 - a.2)) :
    z ∈ ArtGallery.segment a b :=
  ⟨t, h0, h1, Prod.ext e1 e2⟩

theorem meet_of_param {p1 p2 p3 p4 : Point} (hD : crossR p1 p2 p3 p4 ≠ 0)
    (hT0 : 0 ≤ segParT p1 p2 p3 p4) (hT1 : segParT p1 p2 p3 p4 ≤ 1)
    (hU0 : 0 ≤ segParU p1 p2 p3 p4) (hU1 : segParU p1 p2 p3 p4 ≤ 1) :
    (ArtGallery.segment p1 p2 ∩ ArtGallery.segment p3 p4).Nonempty := by
  refine ⟨lerp p1 p2 (segParT p1 p2 p3 p4), ⟨_, hT0, hT1, rfl⟩, ⟨_, hU0, hU1, ?_⟩⟩
  have k1 : crossR p1 p2 p3 p4 * p1.1 + crossR p1 p3 p3 p4 * (p2.1 - p1.1) =
      crossR p1 p2 p3 p4 * p3.1 + crossR p1 p3 p1 p2 * (p4.1 - p3.1) := by unfold crossR; ring
  have k2 : crossR p1 p2 p3 p4 * p1.2 + crossR p1 p3 p3 p4 * (p2.2 - p1.2) =
      crossR p1 p2 p3 p4 * p3.2 + crossR p1 p3 p1 p2 * (p4.2 - p3.2) := by unfold crossR; ring
  unfold segParT segParU lerp
  generalize crossR p1 p2 p3 p4 = D at *
  generalize crossR p1 p3 p3 p4 = A at *
  generalize crossR p1 p3 p1 p2 = B at *
  ext
  · simp only; field_simp; linarith
  · simp only; field_simp; linarith

/-- **Two segments meet iff the criterion holds.** -/
theorem segments_meet_iff (p1 p2 p3 p4 : Point) :
    (ArtGallery.segment p1 p2 ∩ ArtGallery.segment p3 p4).Nonempty ↔ SegMeet p1 p2 p3 p4 := by
  constructor
  · unfold SegMeet segParT segParU crossR
    rintro ⟨z, ⟨t, ht0, ht1, hz⟩, ⟨u, hu0, hu1, hz'⟩⟩
    have z1 := congrArg Prod.fst hz
    have z2 := congrArg Prod.snd hz
    have w1 := congrArg Prod.fst hz'
    have w2 := congrArg Prod.snd hz'
    simp only at z1 z2 w1 w2
    by_cases hD : (p2.1 - p1.1) * (p4.2 - p3.2) - (p2.2 - p1.2) * (p4.1 - p3.1) = 0
    · right
      refine ⟨hD, ?_⟩
      by_cases hd : (p2.1 - p1.1) ^ 2 + (p2.2 - p1.2) ^ 2 = 0
      · -- `p₁ = p₂`, so `z = p₁`
        have a1 : p2.1 - p1.1 = 0 := by nlinarith [sq_nonneg (p2.1 - p1.1), sq_nonneg (p2.2 - p1.2)]
        have a2 : p2.2 - p1.2 = 0 := by nlinarith [sq_nonneg (p2.1 - p1.1), sq_nonneg (p2.2 - p1.2)]
        right; right
        refine mem_seg_of hu0 hu1 ?_ ?_
        · rw [a1, mul_zero, add_zero] at z1; linarith
        · rw [a2, mul_zero, add_zero] at z2; linarith
      · obtain ⟨L, hL⟩ : ∃ L, L = (p2.1 - p1.1) ^ 2 + (p2.2 - p1.2) ^ 2 := ⟨_, rfl⟩
        rw [← hL] at hd
        obtain ⟨μ, hμ⟩ : ∃ μ, μ = ((p4.1 - p3.1) * (p2.1 - p1.1) + (p4.2 - p3.2) * (p2.2 - p1.2)) /
          L := ⟨_, rfl⟩
        have e1 : p4.1 - p3.1 = μ * (p2.1 - p1.1) := by
          rw [hμ, eq_comm, div_mul_eq_mul_div, div_eq_iff hd, hL]
          linear_combination (p2.2 - p1.2) * hD
        have e2 : p4.2 - p3.2 = μ * (p2.2 - p1.2) := by
          rw [hμ, eq_comm, div_mul_eq_mul_div, div_eq_iff hd, hL]
          linear_combination -(p2.1 - p1.1) * hD
        obtain ⟨α, hα⟩ : ∃ α, α = t - u * μ := ⟨_, rfl⟩
        have q1 : p3.1 = p1.1 + α * (p2.1 - p1.1) := by rw [hα]; linear_combination z1 - w1 - u * e1
        have q2 : p3.2 = p1.2 + α * (p2.2 - p1.2) := by rw [hα]; linear_combination z2 - w2 - u * e2
        have q3 : p4.1 = p1.1 + (α + μ) * (p2.1 - p1.1) := by linear_combination q1 + e1
        have q4 : p4.2 = p1.2 + (α + μ) * (p2.2 - p1.2) := by linear_combination q2 + e2
        have ht : t = α + u * μ := by rw [hα]; ring
        by_cases hα0 : 0 ≤ α ∧ α ≤ 1
        · exact Or.inl (mem_seg_of hα0.1 hα0.2 q1 q2)
        by_cases hβ0 : 0 ≤ α + μ ∧ α + μ ≤ 1
        · exact Or.inr (Or.inl (mem_seg_of hβ0.1 hβ0.2 q3 q4))
        right; right
        -- `0` lies strictly between `α` and `α + μ`
        have hμ0 : μ ≠ 0 := by
          intro h0; rw [h0, mul_zero, add_zero] at ht; exact hα0 ⟨ht ▸ ht0, ht ▸ ht1⟩
        have hs : 0 ≤ -α / μ ∧ -α / μ ≤ 1 := by
          rcases lt_or_gt_of_ne hμ0 with hneg | hpos
          · have h1 : u * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 hneg.le
            have h2 : μ ≤ u * μ := by nlinarith
            have hα' : 0 < α := by
              by_contra h
              exact hα0 ⟨by linarith, by linarith⟩
            have hα1 : 1 < α := by
              by_contra h
              exact hα0 ⟨hα'.le, not_lt.1 h⟩
            have hβ' : α + μ < 0 := by
              by_contra h
              have h3 : 1 < α + μ := by
                by_contra h'
                exact hβ0 ⟨not_lt.1 h, not_lt.1 h'⟩
              linarith
            constructor
            · rw [div_nonneg_iff]; right; constructor <;> linarith
            · rw [div_le_one_of_neg hneg]; linarith
          · have h1 : 0 ≤ u * μ := mul_nonneg hu0 hpos.le
            have h2 : u * μ ≤ μ := by nlinarith
            have hα' : α < 0 := by
              by_contra h
              have h3 : 1 < α := by
                by_contra h'
                exact hα0 ⟨not_lt.1 h, not_lt.1 h'⟩
              linarith
            have hβ' : 1 < α + μ := by
              by_contra h
              have h3 : α + μ < 0 := by
                by_contra h'
                exact hβ0 ⟨not_lt.1 h', not_lt.1 h⟩
              linarith
            constructor
            · rw [div_nonneg_iff]; left; constructor <;> linarith
            · rw [div_le_one hpos]; linarith
        refine mem_seg_of hs.1 hs.2 ?_ ?_
        · rw [e1, q1]; field_simp; ring
        · rw [e2, q2]; field_simp; ring
    · left
      refine ⟨hD, ?_⟩
      have eT : ((p3.1 - p1.1) * (p4.2 - p3.2) - (p3.2 - p1.2) * (p4.1 - p3.1)) /
          ((p2.1 - p1.1) * (p4.2 - p3.2) - (p2.2 - p1.2) * (p4.1 - p3.1)) = t := by
        rw [div_eq_iff hD]
        linear_combination (p4.2 - p3.2) * (z1 - w1) - (p4.1 - p3.1) * (z2 - w2)
      have eU : ((p3.1 - p1.1) * (p2.2 - p1.2) - (p3.2 - p1.2) * (p2.1 - p1.1)) /
          ((p2.1 - p1.1) * (p4.2 - p3.2) - (p2.2 - p1.2) * (p4.1 - p3.1)) = u := by
        rw [div_eq_iff hD]
        linear_combination (p2.2 - p1.2) * (z1 - w1) - (p2.1 - p1.1) * (z2 - w2)
      rw [eT, eU]
      exact ⟨ht0, ht1, hu0, hu1⟩
  · unfold SegMeet
    rintro (⟨hD, hT0, hT1, hU0, hU1⟩ | ⟨_, h | h | h⟩)
    · exact meet_of_param hD hT0 hT1 hU0 hU1
    · exact ⟨p3, h, left_mem_segment p3 p4⟩
    · exact ⟨p4, h, right_mem_segment p3 p4⟩
    · exact ⟨p1, left_mem_segment p1 p2, h⟩

end ArtGallery.FewVars

end
