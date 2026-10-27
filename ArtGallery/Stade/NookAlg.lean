module

public import ArtGallery.Geometry.Det

/-!
# Stade construction: algebra of nooks (generic part)

A *nook* is a convex pocket of the polygon whose boundary contains a *nook segment*; the pocket is
entered through a *mouth* (door) `[O₁, O₂]`.  A guard `g` outside the pocket sees a point `s` of
the nook only along a segment `[g, s]` that crosses the mouth (room lemma, `Vis/Rooms.lean`).
This file turns that crossing into algebra:

* `det_mul_det_nonpos_of_cross`: if `[g, s]` meets `[O₁, O₂]` then
  `det g O₁ s * det g O₂ s ≤ 0` (`s` lies in the closed cone of `g` spanned by the mouth);
* `exists_cross_of_det_mul_det_nonpos`: conversely, if `g` and `s` lie strictly on opposite
  sides of the line `O₁ O₂` and `det g O₁ s * det g O₂ s ≤ 0`, then `[g, s]` meets `[O₁, O₂]`;
* `vproj` / `hproj`: the *projection* (shadow) of `g` through a mouth point onto a vertical /
  horizontal nook line, and the factorisations `det_vert`, `det_horiz` of `det g O s` for `s` on
  that line; together with the crossing lemma they give `between_of_cross_vert`,
  `between_of_cross_horiz`: a seen nook point lies between the two shadows of `g`;
* `nonneg_of_mem_segment_beyond`, `det_nonneg_of_beyond`: the *partial visibility region* lemma
  (proof plan L1.4) in algebraic form: an affine functional that is `≤ 0` at the seen nook point
  and `≥ 0` at the crossing point is `≥ 0` at the viewer.
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

/-! ### Guards on segment regions -/

/-- The guard of value `v` on the variable segment `{a} × [H, H+3]` (value map
`v ↦ (a, H + 2v − 1)`). -/
def varPt (H a v : ℝ) : Point := (a, H + 2 * v - 1)

/-- The guard of value `w` on the input segment `{b} × [0, 6]` (value map `w ↦ (b, 4w − 2)`). -/
def inPt (b w : ℝ) : Point := (b, 4 * w - 2)

@[simp] theorem varPt_fst (H a v : ℝ) : (varPt H a v).1 = a := rfl
@[simp] theorem varPt_snd (H a v : ℝ) : (varPt H a v).2 = H + 2 * v - 1 := rfl
@[simp] theorem inPt_fst (b w : ℝ) : (inPt b w).1 = b := rfl
@[simp] theorem inPt_snd (b w : ℝ) : (inPt b w).2 = 4 * w - 2 := rfl

/-! ### Crossing a mouth -/

/-- If the segment `[g, s]` meets the segment `[O₁, O₂]`, then `s` lies in the closed double cone
at `g` spanned by `O₁, O₂`: `det g O₁ s` and `det g O₂ s` do not have the same strict sign. -/
theorem det_mul_det_nonpos_of_cross {g s O₁ O₂ q : Point} (hq : q ∈ segment O₁ O₂)
    (hqs : q ∈ segment g s) : det g O₁ s * det g O₂ s ≤ 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  have h0 : det g s (lerp O₁ O₂ t) = 0 := det_eq_zero_of_mem_segment hqs
  have h1 : det g (lerp O₁ O₂ t) s = 0 := by rw [det_swap23, h0, neg_zero]
  rw [det_lerp_mid] at h1
  set A := det g O₁ s
  set B := det g O₂ s
  -- `(1 - t) A + t B = 0` with `t ∈ [0, 1]`
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h
    have : A = 0 := by linarith
    rw [this, zero_mul]
  · have hB : t * B = -((1 - t) * A) := by linarith
    have : t * (A * B) = -((1 - t) * (A * A)) := by linear_combination A * hB
    have hAA : 0 ≤ A * A := mul_self_nonneg A
    have h1t : 0 ≤ 1 - t := by linarith
    by_contra hpos
    push Not at hpos
    have : 0 < t * (A * B) := mul_pos h hpos
    nlinarith [mul_nonneg h1t hAA]

/-- **Crossing criterion.** If `g` and `s` lie strictly on opposite sides of the line `O₁ O₂` and
`s` lies in the closed double cone at `g` spanned by `O₁, O₂`, the segments `[g, s]` and
`[O₁, O₂]` meet. -/
theorem exists_cross_of_det_mul_det_nonpos {g s O₁ O₂ : Point}
    (hside : det O₁ O₂ g * det O₁ O₂ s < 0) (hcone : det g O₁ s * det g O₂ s ≤ 0) :
    ∃ q ∈ segment O₁ O₂, q ∈ segment g s := by
  set a := det O₁ O₂ g
  set b := det O₁ O₂ s
  have hab : a - b ≠ 0 := by
    intro h
    have : a = b := by linarith
    rw [this] at hside
    nlinarith [mul_self_nonneg b]
  have hane : a ≠ 0 := by intro h; rw [h, zero_mul] at hside; exact lt_irrefl _ hside
  set t := a / (a - b) with ht
  -- `t ∈ (0, 1)`
  have ht0 : 0 ≤ t ∧ t ≤ 1 := by
    rcases lt_or_gt_of_ne hane with ha | ha
    · have hb : 0 < b := by
        by_contra hb; push Not at hb; nlinarith
      have hd : a - b < 0 := by linarith
      constructor
      · exact div_nonneg_of_nonpos ha.le hd.le
      · rw [div_le_one_of_neg hd]; linarith
    · have hb : b < 0 := by
        by_contra hb; push Not at hb; nlinarith
      have hd : 0 < a - b := by linarith
      constructor
      · exact div_nonneg ha.le hd.le
      · rw [div_le_one hd]; linarith
  set q := lerp g s t with hqdef
  refine ⟨q, ?_, lerp_mem_segment g s ht0.1 ht0.2⟩
  -- `q` lies on the line `O₁ O₂`
  have hq0 : det O₁ O₂ q = 0 := by
    rw [hqdef, det_lerp, ht]
    field_simp
    ring
  have hO : O₁ ≠ O₂ := by
    intro h
    apply hane
    show det O₁ O₂ g = 0
    rw [h]
    simp
  obtain ⟨μ, hμ⟩ := exists_lerp_of_det_eq_zero hO hq0
  refine mem_segment_iff_lerp.2 ⟨μ, ?_⟩
  -- the cone condition forces `μ ∈ [0, 1]`
  have e1 : det g O₁ q = t * det g O₁ s := by
    rw [hqdef, det_lerp]; simp
  have e2 : det g O₂ q = t * det g O₂ s := by
    rw [hqdef, det_lerp]; simp
  have f1 : det g O₁ q = μ * det g O₁ O₂ := by
    rw [hμ, det_lerp]; simp
  have f2 : det g O₂ q = (1 - μ) * det g O₂ O₁ := by
    rw [hμ, det_lerp]; simp
  have hD : det g O₁ O₂ = a := det_cyclic_right O₁ O₂ g
  have hD' : det g O₂ O₁ = -a := by rw [det_swap23, hD]
  have key : μ * (1 - μ) * (a * a) = -(t * t) * (det g O₁ s * det g O₂ s) := by
    have := congrArg₂ (· * ·) (e1.symm.trans f1) (e2.symm.trans f2)
    rw [hD, hD'] at this
    linear_combination this
  have hrhs : 0 ≤ μ * (1 - μ) * (a * a) := by
    rw [key]; nlinarith [mul_self_nonneg t]
  have haa : 0 < a * a := mul_self_pos.2 hane
  have hμμ : 0 ≤ μ * (1 - μ) := by
    by_contra h; push Not at h; nlinarith
  refine ⟨?_, ?_, hμ⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

/-! ### Projections onto vertical and horizontal nook lines -/

/-- The ordinate at which the line through `g` and `O` meets the vertical line `x = c` (the
shadow of `g` through `O` on that line). -/
noncomputable def vproj (g O : Point) (c : ℝ) : ℝ :=
  g.2 + (O.2 - g.2) * (c - g.1) / (O.1 - g.1)

/-- The abscissa at which the line through `g` and `O` meets the horizontal line `y = c` (the
shadow of `g` through `O` on that line). -/
noncomputable def hproj (g O : Point) (c : ℝ) : ℝ :=
  g.1 + (O.1 - g.1) * (c - g.2) / (O.2 - g.2)

/-- The shadow formula, given the horizontal offset `X = O.1 − g.1` of the mouth point. -/
theorem vproj_eq_of {g O : Point} {c X : ℝ} (hX : O.1 - g.1 = X) :
    vproj g O c = g.2 + (O.2 - g.2) * (c - g.1) / X := by
  unfold vproj; rw [hX]

/-- The shadow formula, given the vertical offset `Y = O.2 − g.2` of the mouth point. -/
theorem hproj_eq_of {g O : Point} {c Y : ℝ} (hY : O.2 - g.2 = Y) :
    hproj g O c = g.1 + (O.1 - g.1) * (c - g.2) / Y := by
  unfold hproj; rw [hY]

/-- `det g O s` for `s = (c, h)` on a vertical line, factorised through the shadow. -/
theorem det_vert (g O : Point) (c h : ℝ) (hO : O.1 ≠ g.1) :
    det g O (c, h) = (O.1 - g.1) * (h - vproj g O c) := by
  have : O.1 - g.1 ≠ 0 := sub_ne_zero.2 hO
  unfold det vproj
  field_simp
  ring

/-- `det g O s` for `s = (h, c)` on a horizontal line, factorised through the shadow. -/
theorem det_horiz (g O : Point) (c h : ℝ) (hO : O.2 ≠ g.2) :
    det g O (h, c) = (g.2 - O.2) * (h - hproj g O c) := by
  have : O.2 - g.2 ≠ 0 := sub_ne_zero.2 hO
  unfold det hproj
  field_simp
  ring

/-- A real number `h` with `(h - u) (h - w) ≤ 0` lies between `u` and `w`. -/
theorem between_of_mul_nonpos {h u w : ℝ} (hh : (h - u) * (h - w) ≤ 0) :
    min u w ≤ h ∧ h ≤ max u w := by
  rcases le_total u w with huw | huw
  · rw [min_eq_left huw, max_eq_right huw]
    constructor
    · by_contra hc; push Not at hc; nlinarith
    · by_contra hc; push Not at hc; nlinarith
  · rw [min_eq_right huw, max_eq_left huw]
    constructor
    · by_contra hc; push Not at hc; nlinarith
    · by_contra hc; push Not at hc; nlinarith

/-- **Seen nook point, vertical nook line.**  If `[g, s]` with `s = (c, h)` meets the mouth
`[O₁, O₂]` and both mouth ends lie strictly on the same side (left) of the vertical line through
`g`, then `h` lies between the shadows of `g` through `O₁` and `O₂`. -/
theorem between_of_cross_vert {g O₁ O₂ q : Point} {c h : ℝ} (hq : q ∈ segment O₁ O₂)
    (hqs : q ∈ segment g (c, h)) (h₁ : O₁.1 < g.1) (h₂ : O₂.1 < g.1) :
    (h - vproj g O₁ c) * (h - vproj g O₂ c) ≤ 0 := by
  have hc := det_mul_det_nonpos_of_cross hq hqs
  rw [det_vert g O₁ c h h₁.ne, det_vert g O₂ c h h₂.ne] at hc
  have hpos : 0 < (O₁.1 - g.1) * (O₂.1 - g.1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hpos hcon]

/-- **Seen nook point, horizontal nook line.**  If `[g, s]` with `s = (h, c)` meets the mouth
`[O₁, O₂]` and both mouth ends lie strictly below `g`, then `h` lies between the shadows of `g`
through `O₁` and `O₂`. -/
theorem between_of_cross_horiz {g O₁ O₂ q : Point} {c h : ℝ} (hq : q ∈ segment O₁ O₂)
    (hqs : q ∈ segment g (h, c)) (h₁ : O₁.2 < g.2) (h₂ : O₂.2 < g.2) :
    (h - hproj g O₁ c) * (h - hproj g O₂ c) ≤ 0 := by
  have hc := det_mul_det_nonpos_of_cross hq hqs
  rw [det_horiz g O₁ c h h₁.ne, det_horiz g O₂ c h h₂.ne] at hc
  have hpos : 0 < (g.2 - O₁.2) * (g.2 - O₂.2) := mul_pos (by linarith) (by linarith)
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hpos hcon]

/-- **Converse, vertical nook line.**  If `g` and `s = (c, h)` are strictly on opposite sides of
the mouth line and `h` lies between the two shadows of `g`, the segment `[g, s]` meets the
mouth. -/
theorem exists_cross_vert {g O₁ O₂ : Point} {c h : ℝ}
    (hside : det O₁ O₂ g * det O₁ O₂ (c, h) < 0) (h₁ : O₁.1 < g.1) (h₂ : O₂.1 < g.1)
    (hh : (h - vproj g O₁ c) * (h - vproj g O₂ c) ≤ 0) :
    ∃ q ∈ segment O₁ O₂, q ∈ segment g (c, h) := by
  refine exists_cross_of_det_mul_det_nonpos hside ?_
  rw [det_vert g O₁ c h h₁.ne, det_vert g O₂ c h h₂.ne]
  have hpos : 0 < (O₁.1 - g.1) * (O₂.1 - g.1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le hh]

/-- **Converse, horizontal nook line.** -/
theorem exists_cross_horiz {g O₁ O₂ : Point} {c h : ℝ}
    (hside : det O₁ O₂ g * det O₁ O₂ (h, c) < 0) (h₁ : O₁.2 < g.2) (h₂ : O₂.2 < g.2)
    (hh : (h - hproj g O₁ c) * (h - hproj g O₂ c) ≤ 0) :
    ∃ q ∈ segment O₁ O₂, q ∈ segment g (h, c) := by
  refine exists_cross_of_det_mul_det_nonpos hside ?_
  rw [det_horiz g O₁ c h h₁.ne, det_horiz g O₂ c h h₂.ne]
  have hpos : 0 < (g.2 - O₁.2) * (g.2 - O₂.2) := mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le hh]

/-! ### Vertical and horizontal segments -/

/-- A point of a vertical segment `[(c, y₁), (c, y₂)]`, `y₁ ≤ y₂`. -/
theorem mem_segment_vert_iff {c y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) {s : Point} :
    s ∈ segment (c, y₁) (c, y₂) ↔ s.1 = c ∧ y₁ ≤ s.2 ∧ s.2 ≤ y₂ := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    simp only [sub_self, mul_zero, add_zero, true_and]
    constructor <;> nlinarith
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_lt_of_le hy with heq | hlt
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      ext <;> simp only [zero_mul, add_zero] <;> linarith
    · refine ⟨(s.2 - y₁) / (y₂ - y₁), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only [sub_self, mul_zero, add_zero]; exact h1
      · simp only; field_simp; ring

/-- A point of a horizontal segment `[(x₁, c), (x₂, c)]`, `x₁ ≤ x₂`. -/
theorem mem_segment_horiz_iff {c x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) {s : Point} :
    s ∈ segment (x₁, c) (x₂, c) ↔ s.2 = c ∧ x₁ ≤ s.1 ∧ s.1 ≤ x₂ := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    simp only [sub_self, mul_zero, add_zero]
    refine ⟨trivial, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_lt_of_le hx with heq | hlt
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      ext <;> simp only [zero_mul, add_zero] <;> linarith
    · refine ⟨(s.1 - x₁) / (x₂ - x₁), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only; field_simp; ring
      · simp only [sub_self, mul_zero, add_zero]; exact h1

/-! ### The partial-visibility region -/

/-- An affine quantity along a segment: if `q ∈ [s, p]`, `q ≠ s`, the value `f` is affine along
the segment, `f s ≤ 0` and `0 ≤ f q`, then `0 ≤ f p`. -/
theorem nonneg_of_mem_segment_beyond {s p q : Point} (f : Point → ℝ)
    (hf : ∀ t : ℝ, f (lerp s p t) = (1 - t) * f s + t * f p) (hq : q ∈ segment s p) (hqs : q ≠ s)
    (hs : f s ≤ 0) (hqf : 0 ≤ f q) : 0 ≤ f p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  have ht : t ≠ 0 := by rintro rfl; exact hqs (lerp_zero s p)
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  rw [hf] at hqf
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hs), mul_pos htpos (neg_pos.2 h)]

/-- **Partial visibility (L1.4), determinant form.** If the viewer `p` sees `s` through the
point `q` of the mouth (`q ∈ [s, p]`, `q ≠ s`), every line `A B` with the nook point weakly on
its right (`det A B s ≤ 0`) and the mouth point weakly on its left (`0 ≤ det A B q`) has `p`
weakly on its left. -/
theorem det_nonneg_of_beyond {A B s p q : Point} (hq : q ∈ segment s p) (hqs : q ≠ s)
    (hs : det A B s ≤ 0) (hqf : 0 ≤ det A B q) : 0 ≤ det A B p :=
  nonneg_of_mem_segment_beyond (det A B) (fun t => det_lerp A B s p t) hq hqs hs hqf

/-- **Partial visibility, coordinate form.**  Same for a linear functional
`α x + β y` (for instance a horizontal mouth line `y = Y`). -/
theorem lin_nonneg_of_beyond {s p q : Point} (α β γ : ℝ) (hq : q ∈ segment s p) (hqs : q ≠ s)
    (hs : α * s.1 + β * s.2 + γ ≤ 0) (hqf : 0 ≤ α * q.1 + β * q.2 + γ) :
    0 ≤ α * p.1 + β * p.2 + γ :=
  nonneg_of_mem_segment_beyond (fun x : Point => α * x.1 + β * x.2 + γ)
    (fun t => by simp only [lerp_fst, lerp_snd]; ring) hq hqs hs hqf

/-- A point on a segment lies on the line of the segment: affine functionals interpolate. -/
theorem affine_of_mem_segment {a b q : Point} (hq : q ∈ segment a b) (f : Point → ℝ)
    (hf : ∀ t : ℝ, f (lerp a b t) = (1 - t) * f a + t * f b) :
    min (f a) (f b) ≤ f q ∧ f q ≤ max (f a) (f b) := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  rw [hf]
  constructor
  · rcases le_total (f a) (f b) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total (f a) (f b) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

end Stade

end ArtGallery

end
