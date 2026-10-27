module

public import ArtGallery.Stade.SimpleCeil

/-!
# Simplicity of Stade's polygon (proof plan L2.2)

**Main result.** `simple n Φ : (Polygon.mk ((poly n Φ).map ratPoint)).Simple`, for every `n`
and every list `Φ` of ETR-INV-REV constraints (no hypothesis on the variables is needed: copy
nooks are only produced for variables `k < n`).

Proof: `poly n Φ` is the rectangle `[x_L, x_R] × [−1, 2H]` with the floor features hanging
below `y = −1` and the ceiling features standing above `y = 2H` (`Chain.simple_of_combs`).  The
floor features are robust template chains (`SimpleFloor.lean`), the ceiling features are needles
and quadrilateral nooks (`SimpleCeil.lean`); here we check that the ceiling features are
pairwise disjoint and ordered from right to left (`ceil_pw`).

Also: `poly_fst_ge` (every vertex has abscissa `≥ x_L`), `poly_length_ge`, and the description of
the first and last vertices, used for the orientation (`SimpleOrient.lean`).
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Ceiling features -/

theorem mem_ceilFeats {f : List (ℚ × ℚ)} (h : f ∈ ceilFeats n Φ) :
    (∃ i ∈ inputs n Φ, f ∈ inputCeil i.b i.pos (paramH n Φ)) ∨
    (∃ k < n, f ∈ varCeil (varA Φ k) (hasOne Φ k) (paramH n Φ)) ∨
    (∃ k < n, ∃ i ∈ inputs n Φ, i.var = k ∧ f = copyNook (varA Φ k) i.b i.ge (paramH n Φ)) := by
  simp only [ceilFeats, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq] at h
  rcases h with (⟨i, hi, hf⟩ | ⟨k, hk, hf⟩) | ⟨k, hk, i, ⟨hi, hik⟩, rfl⟩
  · exact Or.inl ⟨i, hi, hf⟩
  · exact Or.inr (Or.inl ⟨k, hk, hf⟩)
  · exact Or.inr (Or.inr ⟨k, hk, i, hi, hik, rfl⟩)

/-- The slope window of a copy nook: `H + 30 ≤ b − a_k ≤ 2H − 600`. -/
theorem input_delta {i : InputSeg} (hi : i ∈ inputs n Φ) {k : ℕ} (hk : k < n) :
    (paramH n Φ : ℚ) + 30 ≤ i.b - varA Φ k ∧ i.b - varA Φ k ≤ 2 * (paramH n Φ : ℚ) - 600 := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputs_b hi
  rw [hb]
  exact s1 hk hc hδ0 hδ1

/-- The range of the abscissa of a copy nook. -/
theorem input_nookX {i : InputSeg} (hi : i ∈ inputs n Φ) {k : ℕ} (hk : k < n) :
    -2 * (paramH n Φ : ℚ) - 16 ≤ nookX (varA Φ k) i.b i.ge ∧
      nookX (varA Φ k) i.b i.ge ≤ -1200 * (paramC Φ : ℚ) - 18 := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputs_b hi
  unfold nookX
  rw [hb]
  have he := copyE_bounds i.ge
  exact s3_range hk hc hδ0 hδ1 he.1 he.2

theorem input_b_bounds {i : InputSeg} (hi : i ∈ inputs n Φ) :
    (paramX0 n Φ : ℚ) + 30 ≤ i.b ∧ i.b + 700 ≤ xR n Φ := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputs_b hi
  have h1 := slot_lt_xR (n := n) hc
  have h2 : (paramX0 n Φ : ℚ) ≤ slotG n Φ c := by
    have : paramX0 n Φ ≤ slotG n Φ c := by unfold slotG; omega
    exact_mod_cast this
  rw [hb]; constructor <;> linarith

theorem xL_neg (n : ℕ) (Φ : List Constraint) : xL n Φ ≤ -3000 := by
  have := paramH_ge_q n Φ; unfold xL; linarith

theorem xR_pos (n : ℕ) (Φ : List Constraint) : 100 ≤ xR n Φ := by
  unfold xR
  have h1 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
  have h2 : (0 : ℚ) ≤ paramC Φ := by positivity
  linarith

/-- Every ceiling feature is a ceiling feature of the line `y = 2H` strictly between the
walls. -/
theorem ceil_feature : ∀ f ∈ ceilFeats n Φ,
    CeilFeature ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ) (xL n Φ : ℝ) (xR n Φ : ℝ) (f.map ratPoint) := by
  intro f hf
  have hH := paramH_ge_q n Φ
  have hxL := xL_neg n Φ
  have hxR := xR_pos n Φ
  rcases mem_ceilFeats hf with ⟨i, hi, hfi⟩ | ⟨k, hk, hfk⟩ | ⟨k, hk, i, hi, -, rfl⟩
  · have hb := input_b_bounds hi
    have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
    exact inputCeil_feature hH i.pos (by linarith) (by linarith) f hfi
  · have h1 := var_lt_xR (Φ := Φ) hk
    have h2 := varA_nonneg Φ k
    exact varCeil_feature hH _ (by linarith) (by linarith) f hfk
  · obtain ⟨h1, h2⟩ := input_delta hi hk
    obtain ⟨h3, h4⟩ := input_nookX hi hk
    have h5 := s4_xL n Φ
    have h6 : (0 : ℚ) ≤ paramC Φ := by positivity
    exact (copyNook_feature hH h1 h2 i.ge).2 _ _ (by linarith) (by linarith)

theorem ceil_len {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) : 2 ≤ f.length := by
  have := (ceil_feature f hf).1
  simpa using this

theorem ceilRel_of_bounds {f g : List (ℚ × ℚ)} (hf2 : f ∈ ceilFeats n Φ)
    (hg2 : g ∈ ceilFeats n Φ) {U L : ℚ} (hf : ∀ p ∈ f, L ≤ p.1) (hg : ∀ q ∈ g, q.1 ≤ U)
    (hUL : U < L) : CeilRel f g :=
  sep_ceil hf hg hUL (ceil_len hf2) (ceil_len hg2)

/-- The ceiling features are pairwise disjoint and ordered from right to left. -/
theorem ceil_pw : (ceilFeats n Φ).Pairwise CeilRel := by
  have hH := paramH_ge_q n Φ
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  refine List.Pairwise.imp_of_mem (R := fun f g => f ∈ ceilFeats n Φ → g ∈ ceilFeats n Φ →
    CeilRel f g) (fun ha hb h => h ha hb) ?_
  unfold ceilFeats
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- inputs
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => (inputCeil_pw hH i.pos).imp (fun h _ _ => h), ?_⟩
    rw [List.pairwise_reverse]
    refine inputs_pw.imp (fun {i j} hij => ?_)
    intro f hf g hg hf' hg'
    exact ceilRel_of_bounds hf' hg' (L := j.b - 1 / 2) (U := i.b + 1 / 2)
      (fun p hp => (inputCeil_x hH _ f hf p hp).1) (fun q hq => (inputCeil_x hH _ g hg q hq).2)
      (by linarith)
  · -- variables
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => (varCeil_pw hH _).imp (fun h _ _ => h), ?_⟩
    rw [List.pairwise_reverse]
    refine List.pairwise_lt_range.imp (fun {k k'} hkk => ?_)
    intro f hf g hg hf' hg'
    have := s2_var (Φ := Φ) hkk
    exact ceilRel_of_bounds hf' hg' (L := (varA Φ k' : ℚ) - 1) (U := (varA Φ k : ℚ) + 1 / 4)
      (fun p hp => (varCeil_x hH _ f hf p hp).1) (fun q hq => (varCeil_x hH _ g hg q hq).2)
      (by linarith)
  · -- inputs vs variables
    intro f hf g hg hf' hg'
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range] at hf hg
    obtain ⟨i, hi, hfi⟩ := hf
    obtain ⟨k, hk, hgk⟩ := hg
    have hb := input_b_bounds hi
    have hv := s2_var_slot (Φ := Φ) (c := 0) hk
    have : (slotG n Φ 0 : ℚ) = paramX0 n Φ := by simp [slotG]
    exact ceilRel_of_bounds hf' hg' (L := i.b - 1 / 2) (U := (varA Φ k : ℚ) + 1 / 4)
      (fun p hp => (inputCeil_x hH _ f hfi p hp).1) (fun q hq => (varCeil_x hH _ g hgk q hq).2)
      (by linarith)
  · -- copy nooks
    rw [List.pairwise_flatMap]
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [List.mem_reverse, List.mem_range] at hk
      rw [List.pairwise_map]
      refine (inputs_pw.filter _).imp_of_mem (fun {i j} hi hj hij hf' hg' => ?_)
      simp only [List.mem_filter, beq_iff_eq] at hi hj
      obtain ⟨d1, d2⟩ := input_delta hi.1 hk
      obtain ⟨d3, d4⟩ := input_delta hj.1 hk
      have hs := s3_same (a := (varA Φ k : ℚ)) hij (copyE_bounds i.ge) (copyE_bounds j.ge)
      exact ceilRel_of_bounds hf' hg' (L := nookX (varA Φ k) i.b i.ge)
        (U := nookX (varA Φ k) j.b j.ge + 3)
        (fun p hp => ((copyNook_feature hH d1 d2 i.ge).1 p hp).1)
        (fun q hq => ((copyNook_feature hH d3 d4 j.ge).1 q hq).2)
        (by unfold nookX; linarith)
    · rw [List.pairwise_reverse]
      refine List.pairwise_lt_range.imp_of_mem (fun {k k'} _ hk' hkk => ?_)
      rw [List.mem_range] at hk'
      intro f hf g hg hf' hg'
      simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hf hg
      obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hf
      obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hg
      obtain ⟨d1, d2⟩ := input_delta hj hk'
      obtain ⟨d3, d4⟩ := input_delta hi (hkk.trans hk')
      obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputs_b hi
      obtain ⟨c', hc', δ', hδ0', hδ1', hb'⟩ := inputs_b hj
      have hs := s3_diff (n := n) (Φ := Φ) (c := c) hkk hc' hδ0 hδ1' (copyE_bounds i.ge)
        (copyE_bounds j.ge)
      exact ceilRel_of_bounds hf' hg' (L := nookX (varA Φ k') j.b j.ge)
        (U := nookX (varA Φ k) i.b i.ge + 3)
        (fun p hp => ((copyNook_feature hH d1 d2 j.ge).1 p hp).1)
        (fun q hq => ((copyNook_feature hH d3 d4 i.ge).1 q hq).2)
        (by unfold nookX; rw [hb, hb']; linarith)
  · -- wedges vs copy nooks
    intro f hf g hg hf' hg'
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map,
      List.mem_filter, beq_iff_eq, List.mem_append] at hf hg
    obtain ⟨k, hk, i, ⟨hi, -⟩, rfl⟩ := hg
    obtain ⟨d1, d2⟩ := input_delta hi hk
    obtain ⟨h3, h4⟩ := input_nookX hi hk
    have hnook : ∀ q ∈ copyNook (varA Φ k) i.b i.ge (paramH n Φ), q.1 ≤ -15 := by
      intro q hq
      have := ((copyNook_feature hH d1 d2 i.ge).1 q hq).2
      linarith
    rcases hf with ⟨j, hj, hfj⟩ | ⟨k', hk', hfk⟩
    · have hb := input_b_bounds hj
      have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
      exact ceilRel_of_bounds hf' hg' (L := j.b - 1 / 2) (U := -15)
        (fun p hp => (inputCeil_x hH _ f hfj p hp).1) hnook (by linarith)
    · have h0 := varA_nonneg Φ k'
      exact ceilRel_of_bounds hf' hg' (L := (varA Φ k' : ℚ) - 1) (U := -15)
        (fun p hp => (varCeil_x hH _ f hfk p hp).1) hnook (by linarith)

/-! ### The polygon is simple -/

theorem poly_map (n : ℕ) (Φ : List Constraint) :
    (poly n Φ).map ratPoint =
      [((xL n Φ : ℝ), ((-1 : ℚ) : ℝ))] ++ ((floorFeats n Φ).map (List.map ratPoint)).flatten ++
        [((xR n Φ : ℝ), ((-1 : ℚ) : ℝ)),
          ((xR n Φ : ℝ), ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ))] ++
        ((ceilFeats n Φ).map (List.map ratPoint)).flatten ++
        [((xL n Φ : ℝ), ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ))] := by
  simp only [poly, List.map_append, List.map_cons, List.map_nil, List.map_flatten]
  rfl

theorem xL_lt_xR (n : ℕ) (Φ : List Constraint) : xL n Φ < xR n Φ := by
  linarith [xL_neg n Φ, xR_pos n Φ]

/-- **L2.2: the polygon of Stade's construction is simple.** -/
theorem simple (n : ℕ) (Φ : List Constraint) : (Polygon.mk ((poly n Φ).map ratPoint)).Simple := by
  rw [poly_map]
  have hx : (xL n Φ : ℝ) < xR n Φ := by exact_mod_cast xL_lt_xR n Φ
  have hy : ((-1 : ℚ) : ℝ) < ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ) := by
    have := paramH_ge_q n Φ
    exact_mod_cast (by linarith : (-1 : ℚ) < 2 * (paramH n Φ : ℚ))
  refine simple_of_combs hx hy _ _ ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact floor_feature g hg
  · rw [List.pairwise_map]; exact floor_pw
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact ceil_feature g hg
  · rw [List.pairwise_map]; exact ceil_pw

/-- The plan's form of L2.2 (the hypothesis on the variables is not needed). -/
theorem simple_of_varsLt (_hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    (Polygon.mk ((poly n Φ).map ratPoint)).Simple :=
  simple n Φ

/-! ### Vertex facts -/

/-- Every vertex of the polygon has abscissa `≥ x_L`. -/
theorem poly_fst_ge : ∀ p ∈ poly n Φ, xL n Φ ≤ p.1 := by
  intro p hp
  have hxLR := xL_lt_xR n Φ
  simp only [poly, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten] at hp
  rcases hp with (((rfl | ⟨f, hf, hpf⟩) | (rfl | rfl)) | ⟨f, hf, hpf⟩) | rfl
  · exact le_rfl
  · have hF := floor_feature f hf
    have hm : ratPoint p ∈ chainSet (f.map ratPoint) :=
      mem_chainSet_of_mem (List.mem_map.2 ⟨p, hpf, rfl⟩) hF.1
    have := (hF.2.2.2.2.2.2 _ hm).1
    rw [ratPoint_fst] at this
    exact_mod_cast this.le
  · exact hxLR.le
  · exact hxLR.le
  · have hF := ceil_feature f hf
    have hm : ratPoint p ∈ chainSet (f.map ratPoint) :=
      mem_chainSet_of_mem (List.mem_map.2 ⟨p, hpf, rfl⟩) hF.1
    have := (hF.2.2.2.2.2.2 _ hm).1
    rw [ratPoint_fst] at this
    exact_mod_cast this.le
  · exact le_rfl

theorem poly_head (n : ℕ) (Φ : List Constraint) : (poly n Φ).getD 0 (0, 0) = (xL n Φ, -1) := by
  simp [poly]

theorem poly_last (n : ℕ) (Φ : List Constraint) :
    (poly n Φ).getD ((poly n Φ).length - 1) (0, 0) = (xL n Φ, 2 * (paramH n Φ : ℚ)) := by
  have e : poly n Φ = ((xL n Φ, -1) :: ((floorFeats n Φ).flatten ++
      [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++ (ceilFeats n Φ).flatten)) ++
      [(xL n Φ, 2 * (paramH n Φ : ℚ))] := by
    simp [poly]
  rw [e]
  set pre := (xL n Φ, (-1 : ℚ)) :: ((floorFeats n Φ).flatten ++
      [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++ (ceilFeats n Φ).flatten)
  rw [show (pre ++ [(xL n Φ, 2 * (paramH n Φ : ℚ))]).length - 1 = pre.length by simp,
    List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

theorem poly_length_ge (n : ℕ) (Φ : List Constraint) : 4 ≤ (poly n Φ).length := by
  simp [poly]; omega

end

end ArtGallery.Stade
