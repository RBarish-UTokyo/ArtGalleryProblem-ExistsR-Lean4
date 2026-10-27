module

public import ArtGallery.Stade.RobustCheck

/-!
# Tools for the simplicity proof: needles, quadrilateral nooks, separation

Generic lemmas (independent of the construction) about chains of rational points:

* `sep_floor`, `sep_ceil`: two chains separated by a vertical line are disjoint and correctly
  ordered (the pairwise hypothesis of `comb_floor` / `comb_ceiling`);
* `needle_ceil`: a three-vertex chain `(x_a, Y), (x_t, y_t), (x_b, Y)` with `x_b < x_a` and
  `y_t > Y` is a ceiling feature;
* `nook_ceil`: a four-vertex chain `(r, Y), (x₀, y_t), (x₀, y_b), (l, Y)` with `x₀ < l < r`
  and `Y < y_b < y_t` is a ceiling feature;
* `needles_strip`: two ceiling needles with tips at the same height, ordered at the line and at
  the tip height, are disjoint (the wedges `W3, W4, W5` of a variable).
-/

namespace ArtGallery.Stade.Chain

@[expose] public section

open ArtGallery.Geometry ArtGallery.Irrational Set

/-! ### Separation by a vertical line -/

theorem convex_fst_le (U : ℝ) : Convex ℝ {p : Point | p.1 ≤ U} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at ha hb ⊢
  have : s = 1 - t := by linarith
  subst this; nlinarith

theorem convex_fst_ge (L : ℝ) : Convex ℝ {p : Point | L ≤ p.1} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at ha hb ⊢
  have : s = 1 - t := by linarith
  subst this; nlinarith

theorem chainSet_fst_le {f : List (ℚ × ℚ)} {U : ℚ} (h : ∀ p ∈ f, p.1 ≤ U) :
    ∀ x ∈ chainSet (f.map ratPoint), x.1 ≤ (U : ℝ) := by
  intro x hx
  refine chainSet_subset_of_convex (convex_fst_le (U : ℝ)) (fun p hp => ?_) hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  show ((q.1 : ℚ) : ℝ) ≤ (U : ℝ)
  exact_mod_cast h q hq

theorem chainSet_fst_ge {f : List (ℚ × ℚ)} {L : ℚ} (h : ∀ p ∈ f, L ≤ p.1) :
    ∀ x ∈ chainSet (f.map ratPoint), (L : ℝ) ≤ x.1 := by
  intro x hx
  refine chainSet_subset_of_convex (convex_fst_ge (L : ℝ)) (fun p hp => ?_) hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  show (L : ℝ) ≤ ((q.1 : ℚ) : ℝ)
  exact_mod_cast h q hq

/-- Floor order: a chain entirely left of another one. -/
theorem sep_floor {f g : List (ℚ × ℚ)} {U L : ℚ} (hf : ∀ p ∈ f, p.1 ≤ U)
    (hg : ∀ q ∈ g, L ≤ q.1) (hUL : U < L) (hf2 : 2 ≤ f.length) (hg2 : 2 ≤ g.length) :
    Disjoint (chainSet (f.map ratPoint)) (chainSet (g.map ratPoint)) ∧
      (lstPt (f.map ratPoint)).1 < (fstPt (g.map ratPoint)).1 := by
  have hUL' : (U : ℝ) < (L : ℝ) := by exact_mod_cast hUL
  refine ⟨Set.disjoint_left.2 fun x h1 h2 => ?_, ?_⟩
  · linarith [chainSet_fst_le hf x h1, chainSet_fst_ge hg x h2]
  · have h1 := chainSet_fst_le hf _ (lstPt_mem (by simpa using hf2))
    have h2 := chainSet_fst_ge hg _ (fstPt_mem (by simpa using hg2))
    linarith

/-- Ceiling order: a chain entirely right of another one (the first one comes first). -/
theorem sep_ceil {f g : List (ℚ × ℚ)} {U L : ℚ} (hf : ∀ p ∈ f, L ≤ p.1)
    (hg : ∀ q ∈ g, q.1 ≤ U) (hUL : U < L) (hf2 : 2 ≤ f.length) (hg2 : 2 ≤ g.length) :
    Disjoint (chainSet (f.map ratPoint)) (chainSet (g.map ratPoint)) ∧
      (fstPt (g.map ratPoint)).1 < (lstPt (f.map ratPoint)).1 := by
  obtain ⟨h1, h2⟩ := sep_floor hg hf hUL hg2 hf2
  refine ⟨h1.symm, ?_⟩
  have h3 := chainSet_fst_le hg _ (fstPt_mem (by simpa using hg2))
  have h4 := chainSet_fst_ge hf _ (lstPt_mem (by simpa using hf2))
  have hUL' : (U : ℝ) < (L : ℝ) := by exact_mod_cast hUL
  linarith

/-! ### Needles and nooks on the ceiling -/

/-- A point of the segment from `(m, Y)` to `t` (with `t.2 > Y`) is the start point or lies
strictly above the line. -/
theorem seg_above {Y : ℝ} {u t x : Point} (hu : u.2 = Y) (ht : Y < t.2)
    (hx : x ∈ ArtGallery.segment u t) : Y < x.2 ∨ x = u := by
  obtain ⟨s, h0, h1, rfl⟩ := hx
  rcases eq_or_lt_of_le h0 with rfl | hs
  · right; ext <;> simp
  · left; simp only; rw [hu] at *; nlinarith

theorem ratPoint_mk (x y : ℚ) : ratPoint (x, y) = ((x : ℝ), (y : ℝ)) := rfl

/-- **Ceiling needle.**  `(x_a, Y), (x_t, y_t), (x_b, Y)` with `x_b < x_a`, `Y < y_t`, strictly
inside the strip, is a ceiling feature. -/
theorem needle_ceil {xa xt xb Y yt lo hi : ℚ} (hab : xb < xa) (hY : Y < yt)
    (hlo : lo < xb ∧ lo < xt) (hhi : xa < hi ∧ xt < hi) :
    CeilFeature (Y : ℝ) (lo : ℝ) (hi : ℝ) ([(xa, Y), (xt, yt), (xb, Y)].map ratPoint) := by
  have hab' : (xb : ℝ) < xa := by exact_mod_cast hab
  have hY' : (Y : ℝ) < yt := by exact_mod_cast hY
  simp only [List.map_cons, List.map_nil, ratPoint_mk]
  refine ⟨by simp, ?_, rfl, rfl, by
    simp only [fstPt, lstPt, List.headD_cons, List.getLastD_cons, List.getLastD_nil]; exact hab',
    ?_, ?_⟩
  · refine ⟨fun h => by simp at h; linarith, ?_, fun h => by simp at h; linarith, by simp, trivial⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty]
    rintro x ⟨h1, h2⟩
    refine eq_of_mem_segment_adjacent ?_ h1 h2
    rw [det_def]; simp only
    nlinarith
  · intro p hp
    simp only [chainSet_cons_cons, chainSet_single, union_empty, mem_union] at hp
    simp only [fstPt, lstPt, List.headD_cons, List.getLastD_cons, List.getLastD_nil]
    rcases hp with hp | hp
    · rcases seg_above rfl hY' hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [segment_comm] at hp
      rcases seg_above rfl hY' hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · apply chainSet_subset_of_convex (convex_open_strip _ _)
    have h1 : (lo : ℝ) < xb := by exact_mod_cast hlo.1
    have h2 : (lo : ℝ) < xt := by exact_mod_cast hlo.2
    have h3 : (xa : ℝ) < hi := by exact_mod_cast hhi.1
    have h4 : (xt : ℝ) < hi := by exact_mod_cast hhi.2
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Set.mem_ofPred_eq] <;>
      constructor <;> linarith

/-- **Ceiling nook.**  `(r, Y), (x₀, y_t), (x₀, y_b), (l, Y)` with `x₀ < l < r` and
`Y < y_b < y_t`, strictly inside the strip, is a ceiling feature. -/
theorem nook_ceil {r x0 l Y yt yb lo hi : ℚ} (h1 : x0 < l) (h2 : l < r) (h3 : Y < yb)
    (h4 : yb < yt) (hlo : lo < x0) (hhi : r < hi) :
    CeilFeature (Y : ℝ) (lo : ℝ) (hi : ℝ) ([(r, Y), (x0, yt), (x0, yb), (l, Y)].map ratPoint) := by
  have h1' : (x0 : ℝ) < l := by exact_mod_cast h1
  have h2' : (l : ℝ) < r := by exact_mod_cast h2
  have h3' : (Y : ℝ) < yb := by exact_mod_cast h3
  have h4' : (yb : ℝ) < yt := by exact_mod_cast h4
  simp only [List.map_cons, List.map_nil, ratPoint_mk]
  refine ⟨by simp, ?_, rfl, rfl, by simp [fstPt, lstPt]; linarith, ?_, ?_⟩
  · refine ⟨fun h => by simp at h; linarith, ?_, fun h => by simp at h; linarith, ?_,
      fun h => by simp at h; linarith, by simp, trivial⟩
    · simp only [chainSet_cons_cons, chainSet_single, union_empty]
      rintro x ⟨hx1, hx2 | hx2⟩
      · refine eq_of_mem_segment_adjacent ?_ hx1 hx2
        rw [det_def]; simp only; nlinarith
      · exfalso
        have hA : 0 < det ((x0 : ℝ), (yb : ℝ)) ((l : ℝ), (Y : ℝ)) ((r : ℝ), (Y : ℝ)) := by
          rw [det_def]; simp only; nlinarith
        have hB : 0 < det ((x0 : ℝ), (yb : ℝ)) ((l : ℝ), (Y : ℝ)) ((x0 : ℝ), (yt : ℝ)) := by
          rw [det_def]; simp only; nlinarith
        have := det_pos_of_mem_segment hA hB hx1
        rw [det_eq_zero_of_mem_segment hx2] at this
        exact lt_irrefl _ this
    · simp only [chainSet_cons_cons, chainSet_single, union_empty]
      rintro x ⟨hx1, hx2⟩
      refine eq_of_mem_segment_adjacent ?_ hx1 hx2
      rw [det_def]; simp only; nlinarith
  · intro p hp
    simp only [chainSet_cons_cons, chainSet_single, union_empty, mem_union] at hp
    simp only [fstPt, lstPt, List.headD_cons, List.getLastD_cons, List.getLastD_nil]
    rcases hp with hp | hp | hp
    · rcases seg_above rfl (by simp only; linarith) hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨s, hs0, hs1, rfl⟩ := hp
      left; simp only; nlinarith
    · rw [segment_comm] at hp
      rcases seg_above rfl (by simp only; linarith) hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · apply chainSet_subset_of_convex (convex_open_strip _ _)
    have h5 : (lo : ℝ) < x0 := by exact_mod_cast hlo
    have h6 : (r : ℝ) < hi := by exact_mod_cast hhi
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [Set.mem_ofPred_eq] <;>
      constructor <;> linarith

/-! ### Needles with tips at the same height -/

theorem mem_needle {xa xt xb Y T : ℝ} {p : Point}
    (hp : p ∈ chainSet [(xa, Y), (xt, T), (xb, Y)]) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (p.1 = (1 - u) * xa + u * xt ∨ p.1 = (1 - u) * xb + u * xt) ∧
      p.2 = Y + u * (T - Y) := by
  simp only [chainSet_cons_cons, chainSet_single, union_empty, mem_union] at hp
  rcases hp with ⟨s, h0, h1, rfl⟩ | ⟨s, h0, h1, rfl⟩
  · exact ⟨s, h0, h1, Or.inl (by simp only; ring), by simp only⟩
  · exact ⟨1 - s, by linarith, by linarith, Or.inr (by simp only; ring), by simp only; ring⟩

/-- **Strip lemma.**  Two ceiling needles `(a₁, Y), (t₁, T), (b₁, Y)` (with `b₁ < a₁`) and
`(a₂, Y), (t₂, T), (b₂, Y)` (with `b₂ < a₂`) with tips at the same height `T > Y`, the second
one left of the first one both on the line (`a₂ < b₁`) and at the tips (`t₂ < t₁`), are
disjoint. -/
theorem needles_strip {a₁ t₁ b₁ a₂ t₂ b₂ Y T : ℚ} (hY : Y < T) (h1 : b₁ < a₁) (h2 : b₂ < a₂)
    (h12 : a₂ < b₁) (ht : t₂ < t₁) :
    Disjoint (chainSet ([(a₁, Y), (t₁, T), (b₁, Y)].map ratPoint))
      (chainSet ([(a₂, Y), (t₂, T), (b₂, Y)].map ratPoint)) ∧
    (fstPt ([(a₂, Y), (t₂, T), (b₂, Y)].map ratPoint)).1 <
      (lstPt ([(a₁, Y), (t₁, T), (b₁, Y)].map ratPoint)).1 := by
  have hY' : (Y : ℝ) < T := by exact_mod_cast hY
  have h1' : (b₁ : ℝ) < a₁ := by exact_mod_cast h1
  have h2' : (b₂ : ℝ) < a₂ := by exact_mod_cast h2
  have h12' : (a₂ : ℝ) < b₁ := by exact_mod_cast h12
  have ht' : (t₂ : ℝ) < t₁ := by exact_mod_cast ht
  simp only [List.map_cons, List.map_nil, ratPoint_mk]
  refine ⟨Set.disjoint_left.2 fun p hp1 hp2 => ?_, by
    simp only [fstPt, lstPt, List.headD_cons, List.getLastD_cons, List.getLastD_nil]; exact h12'⟩
  obtain ⟨u, hu0, hu1, hx, hy⟩ := mem_needle hp1
  obtain ⟨w, hw0, hw1, hx', hy'⟩ := mem_needle hp2
  have huw : u = w := by
    have : (u - w) * ((T : ℝ) - Y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst huw
  have e1 := mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h1'.le)
  have e2 := mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h2'.le)
  have e3 := mul_nonneg hu0 (sub_nonneg.2 ht'.le)
  rcases eq_or_lt_of_le hu1 with rfl | hu1'
  · rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> linarith
  · have e4 := mul_pos (sub_pos.2 hu1') (sub_pos.2 h12')
    rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> nlinarith

end

end ArtGallery.Stade.Chain
