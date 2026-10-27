module

public import ArtGallery.FewVars.Guards
public import ArtGallery.Membership.Witness.Visibility
public import ArtGallery.Vis.Local

/-!
# The boundary witness lemma

Let `γ` be a point of the region of a simple polygon and `y` a point of the open edge `e = [u, v]`
with `γ` off the line of `e`.

* `lerp_not_mem_boundary'`: if `γ` sees `y` and `y` is on no line through `γ` and a vertex other
  than `γ`, the open segment `(γ, y)` misses the boundary (blocking lemma);
* `sees_near_edge`: then `γ` also sees the points of the line of `e` near `y` that are on no edge
  line through `γ` (near `y` the region is a half-plane, `Vis.local_halfplane_sign`; in the
  middle the segment stays in the open interior; near `γ` it cannot leave the region);
* `sees_const_piece`: hence on an open piece of the edge free of such lines, `γ` sees all points
  or none (a clopen argument; the seen set is closed).

These are the ingredients of the boundary witness lemma `boundary_seen_of_witnesses`
(`ArtGallery/FewVars/Boundary/Cover.lean`).
-/

@[expose] public section

namespace ArtGallery.FewVars.Boundary

open Set Filter Topology Metric
open ArtGallery.Membership ArtGallery.FewVars
open ArtGallery.Geometry (lerp det_lerp continuous_lerp det_eq_zero_of_mem_segment det_lerp_self
  lerp_mem_segment lerp_eq_add_smul)
open ArtGallery.Membership.Witness (isClosed_sees mul_neg_of_combo_eq_zero
  exists_ball_boundary_near dist_lerp_left det_eq_zero_of_collinear)

variable {P : Polygon}

/-- **No boundary point on the open segment `(γ, y)`.** -/
theorem lerp_not_mem_boundary' (hP : P.Simple) {γ y : Point} (hs : P.Sees γ y)
    (hV : ∀ k < P.n, γ ≠ P.vtx k → det γ (P.vtx k) y ≠ 0) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    lerp γ y τ ∉ P.boundary := by
  rintro ⟨j, hj, hz⟩
  have hj' : (j + 1) % P.n < P.n := Jordan.succIdx_lt P hj
  set a := P.vtx j with ha
  set b := P.vtx ((j + 1) % P.n) with hb
  have hab : a ≠ b := Jordan.simple_vtx_succ_ne hP hj
  have hfz : det a b (lerp γ y τ) = 0 := det_eq_zero_of_mem_segment hz
  rw [det_lerp] at hfz
  by_cases hfγ : det a b γ = 0
  · have hfy : det a b y = 0 := by
      rw [hfγ, mul_zero, zero_add] at hfz
      exact (mul_eq_zero.1 hfz).resolve_left h0.ne'
    by_cases haγ : γ = a
    · have hbγ : γ ≠ b := fun h => hab (haγ.symm.trans h)
      exact hV _ hj' hbγ (det_eq_zero_of_collinear hab hfγ (Geometry.det_self_right a b) hfy)
    · exact hV _ hj haγ (det_eq_zero_of_collinear hab hfγ (Geometry.det_self_outer a b) hfy)
  · have hfy : det a b y ≠ 0 := by
      intro hfy
      rw [hfy, mul_zero, add_zero] at hfz
      rcases mul_eq_zero.1 hfz with h | h
      · linarith
      · exact hfγ h
    have h₁ : det a b γ * det a b y < 0 := mul_neg_of_combo_eq_zero hfγ hfy h0.le h1.le hfz
    obtain ⟨t, ht0, ht1, hzt⟩ := hz
    have hline : det γ y (lerp a b t) = 0 := by
      rw [show lerp a b t = lerp γ y τ from hzt.symm]
      exact det_lerp_self γ y τ
    rw [det_lerp] at hline
    have hnz : ∀ k < P.n, det a b (P.vtx k) = 0 → det γ y (P.vtx k) ≠ 0 := by
      intro k hk hk0 h0'
      by_cases hγk : γ = P.vtx k
      · rw [← hγk] at hk0
        exact hfγ hk0
      · apply hV k hk hγk
        rw [Geometry.det_swap23, h0', neg_zero]
    have hA : det γ y a ≠ 0 := hnz j hj (Geometry.det_self_outer _ _)
    have hB : det γ y b ≠ 0 := hnz _ hj' (Geometry.det_self_right _ _)
    have h₂ : det γ y a * det γ y b < 0 := mul_neg_of_combo_eq_zero hA hB ht0 ht1 hline
    exact Polygon.not_sees_of_proper_cross hP hj h₁ h₂ hs

/-- Distance from the end point of a point of the segment `γ y`. -/
theorem dist_lerp_right (γ y : Point) {τ : ℝ} (h1 : τ ≤ 1) :
    dist (lerp γ y τ) y = (1 - τ) * dist γ y := by
  rw [lerp_eq_add_smul, dist_eq_norm, dist_eq_norm,
    show γ + τ • (y - γ) - y = (1 - τ) • (γ - y) by module, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- Distance between two points of a parametrised line. -/
theorem dist_lerp_lerp (u v : Point) (t t' : ℝ) :
    dist (lerp u v t') (lerp u v t) = |t' - t| * dist v u := by
  rw [lerp_eq_add_smul, lerp_eq_add_smul, dist_eq_norm, dist_eq_norm,
    show u + t' • (v - u) - (u + t • (v - u)) = (t' - t) • (v - u) by module, norm_smul,
    Real.norm_eq_abs]

/-- **Visibility is relatively open along an edge.** -/
theorem sees_near_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {γ : Point} (hγ : γ ∈ P.filled)
    (hγe : det (P.vtx i) (P.vtx ((i + 1) % P.n)) γ ≠ 0)
    (hsee : P.Sees γ (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) s))
    (hV : ∀ k < P.n, γ ≠ P.vtx k →
      det γ (P.vtx k) (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) s) ≠ 0) :
    ∃ ε > 0, ∀ y' : Point, dist y' (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) s) < ε →
      det (P.vtx i) (P.vtx ((i + 1) % P.n)) y' = 0 →
      (∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 →
        det (P.vtx j) (P.vtx ((j + 1) % P.n)) y' ≠ 0) →
      P.Sees γ y' := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  set y := lerp u v s with hy
  have hI : IsOpen (P.filled \ P.boundary) := Jordan.isOpen_filled_sdiff_boundary hP
  obtain ⟨σ, hσ, r, hr, hloc⟩ := Vis.local_halfplane_sign hP hi hs0 hs1
  rw [← hu, ← hv, ← hy] at hloc
  set D := dist γ y with hD
  have hD0 : 0 ≤ D := dist_nonneg
  -- the sign of the guard
  have hσγ : 0 < σ * det u v γ := by
    set κ := min (1 / 2 : ℝ) (r / (2 * (D + 1))) with hκ
    have hκ0 : 0 < κ := lt_min (by norm_num) (div_pos hr (by positivity))
    have hκ1 : κ ≤ 1 / 2 := min_le_left _ _
    have hκr : κ * (D + 1) < r := by
      have h1 : κ ≤ r / (2 * (D + 1)) := min_le_right _ _
      have h2 := (le_div_iff₀ (by positivity)).1 h1
      nlinarith
    have hmem : lerp γ y (1 - κ) ∈ P.filled := hsee ⟨1 - κ, by linarith, by linarith, rfl⟩
    have hball : lerp γ y (1 - κ) ∈ ball y r := by
      rw [mem_ball, dist_lerp_right γ y (by linarith)]
      nlinarith
    have h := (hloc _ hball).1 hmem
    rw [det_lerp, show det u v y = 0 from det_lerp_self u v s, mul_zero, add_zero] at h
    have hne : σ * det u v γ ≠ 0 := mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hγe
    have h3 : 0 ≤ σ * det u v γ := by
      have e : σ * ((1 - (1 - κ)) * det u v γ) = κ * (σ * det u v γ) := by ring
      rw [e] at h
      by_contra hc
      push Not at hc
      nlinarith
    exact lt_of_le_of_ne h3 (Ne.symm hne)
  -- the parameter `s₁`: the end part of the segments stays in the ball
  set s₁ := min (1 / 2 : ℝ) (r / (4 * (D + 1))) with hs₁
  have hs₁0 : 0 < s₁ := lt_min (by norm_num) (div_pos hr (by positivity))
  have hs₁1 : s₁ ≤ 1 / 2 := min_le_left _ _
  have hs₁r : s₁ * (D + 1) ≤ r / 4 := by
    have h1 : s₁ ≤ r / (4 * (D + 1)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity)).1 h1
    nlinarith
  -- the boundary near `γ`
  obtain ⟨r₀, hr₀, hnear⟩ := exists_ball_boundary_near P γ
  set s₀ := min (1 / 4 : ℝ) (r₀ / (2 * (1 + D))) with hs₀
  have hs₀pos : 0 < s₀ := lt_min (by norm_num) (div_pos hr₀ (by positivity))
  have hs₀1 : s₀ ≤ 1 / 4 := min_le_left _ _
  have hs₀r : s₀ * (1 + D) < r₀ := by
    have h1 : s₀ ≤ r₀ / (2 * (1 + D)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity)).1 h1
    nlinarith
  -- the middle part
  have hKc : IsCompact ((lerp γ y) '' Icc s₀ (1 - s₁)) := isCompact_Icc.image (continuous_lerp γ y)
  have hKI : (lerp γ y) '' Icc s₀ (1 - s₁) ⊆ P.filled \ P.boundary := by
    rintro _ ⟨τ, ⟨h0, h1⟩, rfl⟩
    exact ⟨hsee ⟨τ, by linarith, by linarith, rfl⟩,
      lerp_not_mem_boundary' hP hsee hV (by linarith) (by linarith)⟩
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hI hKI
  refine ⟨min δ (min 1 (r / 4)), lt_min hδ (lt_min one_pos (by positivity)), ?_⟩
  intro y' hy' hy'l hoff
  rw [lt_min_iff, lt_min_iff] at hy'
  have hγy' : dist γ y' ≤ D + 1 := by
    have := dist_triangle γ y y'
    rw [dist_comm y y'] at this
    linarith [hy'.2.1]
  -- points at parameters in `[s₀, 1 - s₁]`
  have hfar : ∀ τ, s₀ ≤ τ → τ ≤ 1 - s₁ → lerp γ y' τ ∈ P.filled \ P.boundary := by
    intro τ h0 h1
    apply hthick
    rw [mem_thickening_iff]
    exact ⟨lerp γ y τ, ⟨τ, ⟨h0, h1⟩, rfl⟩,
      (Witness.dist_lerp_lerp_le γ y y' (by linarith) (by linarith)).trans_lt hy'.1⟩
  rintro _ ⟨τ, h0, h1, rfl⟩
  show lerp γ y' τ ∈ P.filled
  -- the end part
  by_cases hend : 1 - s₁ ≤ τ
  · have hball : lerp γ y' τ ∈ ball y r := by
      rw [mem_ball]
      have e1 := dist_triangle (lerp γ y' τ) y' y
      rw [dist_lerp_right γ y' h1] at e1
      have e2 : (1 - τ) * dist γ y' ≤ s₁ * (D + 1) :=
        mul_le_mul (by linarith) hγy' dist_nonneg hs₁0.le
      linarith [hy'.2.2]
    rw [hloc _ hball, det_lerp, hy'l, mul_zero, add_zero]
    have : 0 ≤ 1 - τ := by linarith
    nlinarith
  push Not at hend
  rcases le_or_gt s₀ τ with hss | hss
  · exact (hfar τ hss hend.le).1
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · subst h0'
    simpa using hγ
  -- the part near `γ`
  by_contra hout
  have hpc : IsPreconnected ((lerp γ y') '' Icc τ s₀) :=
    isPreconnected_Icc.image _ (continuous_lerp γ y').continuousOn
  have hcross : ∃ σ' ∈ Icc τ s₀, lerp γ y' σ' ∈ P.boundary := by
    by_contra hno
    push Not at hno
    obtain ⟨_, ⟨σ', hσ', rfl⟩, h1', h2'⟩ := hpc (P.filled)ᶜ (P.filled \ P.boundary)
      (Jordan.isClosed_filled P).isOpen_compl hI
      (by
        rintro _ ⟨σ', hσ', rfl⟩
        by_cases hm : lerp γ y' σ' ∈ P.filled
        · exact Or.inr ⟨hm, hno σ' hσ'⟩
        · exact Or.inl hm)
      ⟨lerp γ y' τ, ⟨τ, ⟨le_rfl, hss.le⟩, rfl⟩, hout⟩
      ⟨lerp γ y' s₀, ⟨s₀, ⟨hss.le, le_rfl⟩, rfl⟩, hfar s₀ le_rfl (by linarith)⟩
    exact h1' h2'.1
  obtain ⟨σ', ⟨hσ0, hσ1⟩, hσB⟩ := hcross
  have hσpos : 0 < σ' := h0'.trans_le hσ0
  have hdist : dist (lerp γ y' σ') γ < r₀ := by
    rw [dist_lerp_left γ y' hσpos.le, dist_comm]
    calc σ' * dist γ y' ≤ s₀ * (1 + D) := mul_le_mul hσ1 (by linarith) dist_nonneg hs₀pos.le
      _ < r₀ := hs₀r
  obtain ⟨j, hj, hwj, hjγ⟩ := hnear _ hσB hdist
  have h0j := det_eq_zero_of_mem_segment hwj
  rw [det_lerp, hjγ, mul_zero, zero_add] at h0j
  exact hoff j hj hjγ ((mul_eq_zero.1 h0j).resolve_left hσpos.ne')

/-- **Visibility is constant on an open piece of an edge** free of the lines through the guard
and a vertex and of the edge lines through the guard. -/
theorem sees_const_piece (hP : P.Simple) {i : ℕ} (hi : i < P.n) {lo hi' : ℝ} (hlo : 0 ≤ lo)
    (hhi : hi' ≤ 1) {γ : Point} (hγ : γ ∈ P.filled)
    (hγe : det (P.vtx i) (P.vtx ((i + 1) % P.n)) γ ≠ 0)
    (hV : ∀ t ∈ Ioo lo hi', ∀ k < P.n, γ ≠ P.vtx k →
      det γ (P.vtx k) (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t) ≠ 0)
    (hE : ∀ t ∈ Ioo lo hi', ∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 →
      det (P.vtx j) (P.vtx ((j + 1) % P.n)) (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t) ≠ 0)
    {t t' : ℝ} (ht : t ∈ Ioo lo hi') (ht' : t' ∈ Ioo lo hi')
    (hs : P.Sees γ (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t)) :
    P.Sees γ (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t') := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  by_contra hns
  let U : Set ℝ := {τ | ∃ ε > 0, ∀ τ', dist τ' τ < ε → τ' ∈ Ioo lo hi' → P.Sees γ (lerp u v τ')}
  let V : Set ℝ := {τ | ¬ P.Sees γ (lerp u v τ)}
  have hU : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro τ ⟨ε, hε, h⟩
    refine ⟨ε / 2, half_pos hε, fun τ'' hτ'' => ⟨ε / 2, half_pos hε, fun τ' h1 h2 => h τ' ?_ h2⟩⟩
    rw [mem_ball] at hτ''
    have := dist_triangle τ' τ'' τ
    linarith
  have hVo : IsOpen V :=
    (isClosed_sees P γ).isOpen_compl.preimage (continuous_lerp u v)
  have hcover : Ioo lo hi' ⊆ U ∪ V := by
    intro τ hτ
    by_cases hsτ : P.Sees γ (lerp u v τ)
    · left
      obtain ⟨ε, hε, hnear⟩ := sees_near_edge hP hi (by linarith [hτ.1]) (by linarith [hτ.2]) hγ
        hγe hsτ (hV τ hτ)
      refine ⟨ε / (dist v u + 1), div_pos hε (by positivity), fun τ' hd hτ' => ?_⟩
      refine hnear _ ?_ (det_lerp_self u v τ') (hE τ' hτ')
      rw [dist_lerp_lerp, ← Real.dist_eq]
      have h1 := (lt_div_iff₀ (by positivity : (0 : ℝ) < dist v u + 1)).1 hd
      nlinarith [dist_nonneg (x := τ') (y := τ), dist_nonneg (x := v) (y := u)]
    · exact Or.inr hsτ
  have hpc : IsPreconnected (Ioo lo hi') := isPreconnected_Ioo
  have htU : t ∈ U := by
    rcases hcover ht with h | h
    · exact h
    · exact absurd hs h
  obtain ⟨τ, hτI, ⟨ε, hε, hτU⟩, hτV⟩ := hpc U V hU hVo hcover ⟨t, ht, htU⟩ ⟨t', ht', hns⟩
  exact hτV (hτU τ (by rw [dist_self]; exact hε) hτI)

end ArtGallery.FewVars.Boundary

end
