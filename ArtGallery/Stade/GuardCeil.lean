module

public import ArtGallery.Stade.GuardCopy

/-!
# The canonical guards see the ceiling features (proof plan §9)

Every ceiling feature `f ∈ ceilFeats n Φ` (wedges `W1, W3` of the inputs, wedges
`W1, W3, W4, W5` of the variables, copy nooks) is seen by the canonical guards of a solution `v`
(`ceil_cover`), provided the hall and the feature pieces lie in the region:
* the wedges of a segment region are seen by its guard (it lies in their cones, `GuardWedges`);
* a copy nook is seen by the variable guard and the input guard (equal values,
  `copy_pocket_cover`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

variable {n : ℕ} {Φ : List Constraint}

/-! ### Rational wedges as real triangles -/

/-- The wedge `W1` (mouth on the right) as a list of real points. -/
theorem wedgeW1_true_map (s H : ℚ) : (wedgeW1 s true H).map ratPoint =
    [((s : ℝ) + 1 / 4, 2 * (H : ℝ)), ((s : ℝ), 3 * (H : ℝ)), ((s : ℝ), 2 * (H : ℝ))] := by
  simp [wedgeW1, ratPoint]

/-- The wedge `W1` (mouth on the left) as a list of real points. -/
theorem wedgeW1_false_map (s H : ℚ) : (wedgeW1 s false H).map ratPoint =
    [((s : ℝ), 2 * (H : ℝ)), ((s : ℝ), 3 * (H : ℝ)), ((s : ℝ) - 1 / 4, 2 * (H : ℝ))] := by
  simp [wedgeW1, ratPoint]

/-- The wedge `W3` (tip on the left) as a list of real points. -/
theorem wedgeW3_true_map (s T H : ℚ) : (wedgeW3 s true T H).map ratPoint =
    [((s : ℝ) - ((H : ℝ) - 3) / (2 * (2 * (H : ℝ) - 3)), 2 * (H : ℝ)), ((s : ℝ) - 1 / 2, (T : ℝ)),
      ((s : ℝ) - 1 / 4, 2 * (H : ℝ))] := by
  simp [wedgeW3, ratPoint]

/-- The wedge `W3` (tip on the right) as a list of real points. -/
theorem wedgeW3_false_map (s T H : ℚ) : (wedgeW3 s false T H).map ratPoint =
    [((s : ℝ) + 1 / 4, 2 * (H : ℝ)), ((s : ℝ) + 1 / 2, (T : ℝ)),
      ((s : ℝ) + ((H : ℝ) - 3) / (2 * (2 * (H : ℝ) - 3)), 2 * (H : ℝ))] := by
  simp [wedgeW3, ratPoint]

/-- The wedge `W4` as a list of real points. -/
theorem wedgeW4_map (s H : ℚ) : (wedgeW4 s H).map ratPoint =
    [((s : ℝ) - 3 * ((H : ℝ) - 1) / (4 * (2 * (H : ℝ) - 1)), 2 * (H : ℝ)),
      ((s : ℝ) - 3 / 4, 3 * (H : ℝ)), ((s : ℝ) - 3 / 8, 2 * (H : ℝ))] := by
  simp [wedgeW4, ratPoint]

/-- The wedge `W5` as a list of real points. -/
theorem wedgeW5_map (s H : ℚ) : (wedgeW5 s H).map ratPoint =
    [((s : ℝ) - ((H : ℝ) - 3) / (2 * (H : ℝ) - 3), 2 * (H : ℝ)), ((s : ℝ) - 1, 3 * (H : ℝ)),
      ((s : ℝ) - ((H : ℝ) - 1) / (2 * (H : ℝ) - 1), 2 * (H : ℝ))] := by
  simp [wedgeW5, ratPoint]

/-! ### The ceiling segment of the hall -/

/-- A ceiling segment between abscissae in `[x_L, x_R]` lies in the hall. -/
theorem ceil_seg_hall {x₁ x₂ : ℝ} (h1 : (xL n Φ : ℝ) ≤ x₁) (h2 : x₁ ≤ (xR n Φ : ℝ))
    (h3 : (xL n Φ : ℝ) ≤ x₂) (h4 : x₂ ≤ (xR n Φ : ℝ)) :
    segment ((x₁, 2 * hH n Φ) : Point) (x₂, 2 * hH n Φ) ⊆ piece (hallPoly n Φ) := by
  have hH := hH_ge n Φ
  exact Geometry.segment_subset_of_convex (convex_piece _)
    (mem_hall.2 ⟨h1, h2, by linarith, le_rfl⟩) (mem_hall.2 ⟨h3, h4, by linarith, le_rfl⟩)

/-- **A ceiling wedge** `[a, b, c]` (mouth `c a` on the ceiling inside the hall) is seen by a
guard of the hall lying in its cone. -/
theorem ceil_wedge_cover {P : Polygon} (hHP : piece (hallPoly n Φ) ⊆ P.filled)
    {f : List (ℚ × ℚ)} {a b c g : Point} (hf : f.map ratPoint = [a, b, c])
    (hT : piece (Polygon.mk (f.map ratPoint)) ⊆ P.filled) (hD : 0 < det a b c)
    (hg1 : 0 ≤ det a b g) (hg2 : 0 ≤ det b c g) (hg3 : det c a g ≤ 0)
    (hgA : g ∈ piece (hallPoly n Φ)) (hmA : segment c a ⊆ piece (hallPoly n Φ)) :
    ∀ z ∈ piece (Polygon.mk (f.map ratPoint)), P.Sees g z := by
  rw [hf] at hT ⊢
  exact wedge_sees (convex_piece _) hHP hD hg1 hg2 hg3 hgA hmA hT

/-! ### Fractions -/

/-- Bounds on the mouth offset `(H − 3)/(2(2H − 3))` of `W3`. -/
theorem frac3_bounds_r {H : ℝ} (hH : 1000 ≤ H) :
    0 < (H - 3) / (2 * (2 * H - 3)) ∧ (H - 3) / (2 * (2 * H - 3)) < 1 / 4 := by
  have hd : 0 < 2 * (2 * H - 3) := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · rw [div_lt_iff₀ hd]; linarith

/-- Bounds on the mouth offset `3(H − 1)/(4(2H − 1))` of `W4`. -/
theorem frac4_bounds_r {H : ℝ} (hH : 1000 ≤ H) :
    0 < 3 * (H - 1) / (4 * (2 * H - 1)) ∧ 3 * (H - 1) / (4 * (2 * H - 1)) < 3 / 8 := by
  have hd : 0 < 4 * (2 * H - 1) := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · rw [div_lt_iff₀ hd]; linarith

/-- Bounds on the mouth offsets `(H − 3)/(2H − 3)`, `(H − 1)/(2H − 1)` of `W5`. -/
theorem frac5_bounds_r {H : ℝ} (hH : 1000 ≤ H) :
    0 < (H - 3) / (2 * H - 3) ∧ (H - 3) / (2 * H - 3) < 1 ∧ 0 < (H - 1) / (2 * H - 1) ∧
      (H - 1) / (2 * H - 1) < 1 := by
  have hd1 : 0 < 2 * H - 3 := by linarith
  have hd2 : 0 < 2 * H - 1 := by linarith
  refine ⟨div_pos (by linarith) hd1, ?_, div_pos (by linarith) hd2, ?_⟩
  · rw [div_lt_iff₀ hd1]; linarith
  · rw [div_lt_iff₀ hd2]; linarith

/-! ### Segment regions -/

/-- The ceiling wedges of a segment region at abscissa `s` (`x_L + 2 ≤ s ≤ x_R − 2`) are seen by
a guard `(s, y)` with `y` in the segment's range: `W1` (side `pos`) and `W3` with tip height `T`
(`[H, H+3]`, `T = 3H` for variables; `[0, 6]`, `T = 4H` for inputs). -/
theorem seg_wedge_cover {P : Polygon} (hHP : piece (hallPoly n Φ) ⊆ P.filled) {s : ℚ}
    (hs1 : (xL n Φ : ℝ) + 2 ≤ s) (hs2 : (s : ℝ) + 2 ≤ xR n Φ) {pos : Bool} {T : ℚ} {y : ℝ}
    (hT : 3 * (paramH n Φ : ℚ) ≤ T) (hy0 : -1 ≤ y) (hy : y ≤ 2 * hH n Φ)
    (hlo : 4 * hH n Φ - (T : ℝ) ≤ y)
    (hhi : (hH n Φ - 3) * ((T : ℝ) - 2 * hH n Φ) ≤ hH n Φ * (2 * hH n Φ - y))
    {f : List (ℚ × ℚ)} (hf : f = wedgeW1 s pos (paramH n Φ) ∨ f = wedgeW3 s pos T (paramH n Φ))
    (hTP : piece (Polygon.mk (f.map ratPoint)) ⊆ P.filled) :
    ∀ z ∈ piece (Polygon.mk (f.map ratPoint)), P.Sees ((s : ℝ), y) z := by
  have hH0 := hH_ge n Φ
  have hT' : 3 * hH n Φ ≤ (T : ℝ) := by
    have : ((3 * (paramH n Φ : ℚ) : ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    simpa using this
  have hgA : ((s : ℝ), y) ∈ piece (hallPoly n Φ) :=
    mem_hall.2 ⟨by linarith, by linarith, hy0, hy⟩
  obtain ⟨f3a, f3b⟩ := frac3_bounds_r hH0
  have hc : ((paramH n Φ : ℚ) : ℝ) = hH n Φ := by simp [hH]
  rcases hf with rfl | rfl <;> cases pos
  · have hm : (wedgeW1 s false (paramH n Φ)).map ratPoint =
        [((s : ℝ), 2 * hH n Φ), ((s : ℝ), 3 * hH n Φ), ((s : ℝ) - 1 / 4, 2 * hH n Φ)] := by
      rw [wedgeW1_false_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w1neg_det (s := (s : ℝ)) hH0 hy
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))
  · have hm : (wedgeW1 s true (paramH n Φ)).map ratPoint =
        [((s : ℝ) + 1 / 4, 2 * hH n Φ), ((s : ℝ), 3 * hH n Φ), ((s : ℝ), 2 * hH n Φ)] := by
      rw [wedgeW1_true_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w1pos_det (s := (s : ℝ)) hH0 hy
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))
  · have hm : (wedgeW3 s false T (paramH n Φ)).map ratPoint =
        [((s : ℝ) + 1 / 4, 2 * hH n Φ), ((s : ℝ) + 1 / 2, (T : ℝ)),
          ((s : ℝ) + (hH n Φ - 3) / (2 * (2 * hH n Φ - 3)), 2 * hH n Φ)] := by
      rw [wedgeW3_false_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w3neg_det (s := (s : ℝ)) hH0 hT' hy hlo hhi
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))
  · have hm : (wedgeW3 s true T (paramH n Φ)).map ratPoint =
        [((s : ℝ) - (hH n Φ - 3) / (2 * (2 * hH n Φ - 3)), 2 * hH n Φ),
          ((s : ℝ) - 1 / 2, (T : ℝ)), ((s : ℝ) - 1 / 4, 2 * hH n Φ)] := by
      rw [wedgeW3_true_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w3pos_det (s := (s : ℝ)) hH0 hT' hy hlo hhi
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))

/-- The wedges `W4, W5` of a variable with a constraint `x = 1` are seen by its guard
`(s, H + 1)` (value `1`). -/
theorem one_wedge_cover {P : Polygon} (hHP : piece (hallPoly n Φ) ⊆ P.filled) {s : ℚ}
    (hs1 : (xL n Φ : ℝ) + 2 ≤ s) (hs2 : (s : ℝ) + 2 ≤ xR n Φ) {f : List (ℚ × ℚ)}
    (hf : f = wedgeW4 s (paramH n Φ) ∨ f = wedgeW5 s (paramH n Φ))
    (hTP : piece (Polygon.mk (f.map ratPoint)) ⊆ P.filled) :
    ∀ z ∈ piece (Polygon.mk (f.map ratPoint)), P.Sees ((s : ℝ), hH n Φ + 1) z := by
  have hH0 := hH_ge n Φ
  have hgA : ((s : ℝ), hH n Φ + 1) ∈ piece (hallPoly n Φ) :=
    mem_hall.2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hc : ((paramH n Φ : ℚ) : ℝ) = hH n Φ := by simp [hH]
  obtain ⟨f4a, f4b⟩ := frac4_bounds_r hH0
  obtain ⟨f5a, f5b, f5c, f5d⟩ := frac5_bounds_r hH0
  rcases hf with rfl | rfl
  · have hm : (wedgeW4 s (paramH n Φ)).map ratPoint =
        [((s : ℝ) - 3 * (hH n Φ - 1) / (4 * (2 * hH n Φ - 1)), 2 * hH n Φ),
          ((s : ℝ) - 3 / 4, 3 * hH n Φ), ((s : ℝ) - 3 / 8, 2 * hH n Φ)] := by
      rw [wedgeW4_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w4_det (s := (s : ℝ)) hH0
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))
  · have hm : (wedgeW5 s (paramH n Φ)).map ratPoint =
        [((s : ℝ) - (hH n Φ - 3) / (2 * hH n Φ - 3), 2 * hH n Φ), ((s : ℝ) - 1, 3 * hH n Φ),
          ((s : ℝ) - (hH n Φ - 1) / (2 * hH n Φ - 1), 2 * hH n Φ)] := by
      rw [wedgeW5_map, hc]
    obtain ⟨h0, h1, h2, h3⟩ := w5_det (s := (s : ℝ)) hH0
    exact ceil_wedge_cover hHP hm hTP h0 h1 h2 h3 hgA
      (ceil_seg_hall (by linarith) (by linarith) (by linarith) (by linarith))

/-! ### Copy nooks -/

/-- **A copy nook** (of an input `i` copying the variable `k = i.var < n`) is seen by the guard
of `k` and the guard of `i`, at the same value `w`. -/
theorem copy_feat_cover {P : Polygon} (hHP : piece (hallPoly n Φ) ⊆ P.filled) {i : InputSeg}
    (hi : i ∈ inputs n Φ) (hk : i.var < n)
    (hTP : piece (Polygon.mk ((copyNook (varA Φ i.var) i.b i.ge (paramH n Φ)).map ratPoint)) ⊆
      P.filled) {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    ∀ z ∈ piece (Polygon.mk ((copyNook (varA Φ i.var) i.b i.ge (paramH n Φ)).map ratPoint)),
      P.Sees ((varA Φ i.var : ℝ), hH n Φ + 2 * w - 1) z ∨ P.Sees ((i.b : ℝ), 4 * w - 2) z := by
  have hH0 := hH_ge n Φ
  obtain ⟨d1, d2⟩ := input_delta hi hk
  have hp := CopyParams.of_rat (paramH_ge_q n Φ) (by linarith) (by linarith)
    (a := (varA Φ i.var : ℚ)) (b := i.b)
  have hc : ((paramH n Φ : ℚ) : ℝ) = hH n Φ := by simp [hH]
  have ha : (((varA Φ i.var : ℕ) : ℚ) : ℝ) = (varA Φ i.var : ℝ) := by simp
  rw [copyNook_map] at hTP ⊢
  rw [show ∀ a b c d : Point, (Polygon.mk [a, b, c, d]) = quad a b c d from fun _ _ _ _ => rfl,
    piece_copyNook] at hTP ⊢
  obtain ⟨x1, x2⟩ := input_nookX hi hk
  have hxL := s4_xL n Φ
  have hxN : (xL n Φ : ℝ) ≤ copyXN i.ge (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ) := by
    rw [← nookX_cast]
    have : xL n Φ ≤ nookX (varA Φ i.var) i.b i.ge := by linarith
    exact_mod_cast this
  have hva := var_lt_xR (Φ := Φ) hk
  have hvaR : (((varA Φ i.var : ℕ) : ℚ) : ℝ) ≤ (xR n Φ : ℝ) := by
    have : ((varA Φ i.var : ℕ) : ℚ) ≤ xR n Φ := by
      have := paramH_ge_q n Φ; linarith
    exact_mod_cast this
  obtain ⟨o1, o2, -, -⟩ := copy_mouth_order i.ge hp
  obtain ⟨m1, m2⟩ := copy_mouth_lt_a i.ge hp
  have hLx : copyXN i.ge (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ) <
      (copyLm i.ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ)).1 := by
    cases h : i.ge <;> simp only [copyLm_true, copyLm_false] <;> rw [h] at o1 o2 <;> assumption
  have hRx : copyXN i.ge (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ) <
      (copyRm i.ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ)).1 := by
    cases h : i.ge <;> simp only [copyRm_true, copyRm_false] <;> rw [h] at o1 o2 <;> assumption
  have hmA : segment (copyLm i.ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ))
      (copyRm i.ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ i.var : ℕ) : ℚ) : ℝ) (i.b : ℝ)) ⊆
      piece (hallPoly n Φ) := by
    refine Geometry.segment_subset_of_convex (convex_piece _) (mem_hall.2 ⟨?_, ?_, ?_, ?_⟩)
      (mem_hall.2 ⟨?_, ?_, ?_, ?_⟩) <;> (try simp only [copyLm_snd, copyRm_snd]) <;> linarith
  have hb := input_b_bounds hi
  have hX0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
  have hbR : (i.b : ℝ) + 700 ≤ (xR n Φ : ℝ) := by exact_mod_cast hb.2
  have hbL : (xL n Φ : ℝ) ≤ (i.b : ℝ) := by
    have : xL n Φ ≤ i.b := by have := xL_neg n Φ; linarith [hb.1]
    exact_mod_cast this
  have hσA : varPt (((paramH n Φ : ℚ)) : ℝ) (((varA Φ i.var : ℕ) : ℚ) : ℝ) w ∈
      piece (hallPoly n Φ) := by
    have h0 : (0 : ℝ) ≤ (((varA Φ i.var : ℕ) : ℚ) : ℝ) := by positivity
    have hxL' : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
    refine mem_hall.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [varPt, hc] <;> linarith
  have hτA : inPt (i.b : ℝ) w ∈ piece (hallPoly n Φ) := by
    refine mem_hall.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [inPt] <;> linarith
  intro z hz
  have := copy_pocket_cover i.ge hp (convex_piece _) hHP hmA hTP hw1 hw2 hσA hτA z hz
  simpa only [varPt, inPt, hc, ha] using this

/-! ### Variable floor needles -/

/-- The floor needle of variable `k` is seen by its guard. -/
theorem var_needle_cover {P : Polygon} (hHP : piece (hallPoly n Φ) ⊆ P.filled) {k : ℕ}
    (hk : k < n) {y : ℝ} (hy1 : -1 ≤ y) (hy2 : y ≤ 2 * hH n Φ)
    (hTP : piece (needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ⊆ P.filled) :
    ∀ z ∈ piece (needleL (varA Φ k : ℝ) (-1) (hH n Φ)), P.Sees ((varA Φ k : ℝ), y) z := by
  have hH0 := hH_ge n Φ
  have hva := var_lt_xR (Φ := Φ) hk
  have hvaR : (varA Φ k : ℝ) + hH n Φ + 100 ≤ (xR n Φ : ℝ) := by
    have : ((varA Φ k : ℕ) : ℝ) = (((varA Φ k : ℕ) : ℚ) : ℝ) := by simp
    rw [this]; unfold hH
    have h' : (((varA Φ k : ℚ) + (paramH n Φ : ℚ) + 100 : ℚ) : ℝ) ≤ (xR n Φ : ℝ) := by
      exact_mod_cast hva
    push_cast at h'; linarith
  have h0 : (0 : ℝ) ≤ (varA Φ k : ℝ) := by positivity
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  refine needleL_sees (convex_piece _) hHP (by linarith) hy1
    (mem_hall.2 ⟨by linarith, by linarith, hy1, hy2⟩) ?_ hTP
  exact Geometry.segment_subset_of_convex (convex_piece _)
    (mem_hall.2 ⟨by linarith, by linarith, le_rfl, by linarith⟩)
    (mem_hall.2 ⟨by linarith, by linarith, le_rfl, by linarith⟩)

end ArtGallery.Stade

end
