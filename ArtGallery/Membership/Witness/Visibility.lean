module

public import ArtGallery.Membership.Witness.Basic
public import ArtGallery.Vis.API

/-!
# The witness lemma: visibility is locally constant off the arrangement

Let `γ` be a point of the region of a simple polygon `P`, and `y` a point lying on no edge line
and on no line through `γ` and a vertex different from `γ`.  If `γ` sees `y`, then `γ` sees every
point near `y` (`sees_eventually`).  Consequently visibility from `γ` is constant on every
preconnected set of such points (`sees_of_isPreconnected`).

The proof of `sees_eventually`:
* no point of the half-open segment `(γ, y]` is on the boundary (`lerp_not_mem_boundary`): it is
  not a vertex (else `y` is on a line through `γ` and a vertex), and it is not on an edge whose
  line misses `γ` (else the segment properly crosses that edge, contradicting the blocking lemma
  `Polygon.not_sees_of_proper_cross`), nor on an edge whose line contains `γ` (else `y` is on that
  edge line);
* near `γ` the boundary consists of edges whose lines pass through `γ`
  (`exists_ball_boundary_near`); a segment `γ y'` with `y'` off those lines meets them only at
  `γ`, so near `γ` it cannot leave the region;
* away from `γ` the segment `γ y` stays at positive distance from the boundary (compactness).
-/

namespace ArtGallery.Membership.Witness

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp continuous_lerp lerp_zero lerp_one
  continuous_det_right det_eq_zero_of_mem_segment det_lerp_self)

variable {P : Polygon}

/-- `q ↦ lerp γ q t` is continuous. -/
theorem continuous_lerp_right (γ : Point) (t : ℝ) : Continuous (fun q : Point => lerp γ q t) := by
  unfold lerp
  fun_prop

/-- The set of points seen from `γ` is closed. -/
theorem isClosed_sees (P : Polygon) (γ : Point) : IsClosed {q | P.Sees γ q} := by
  have e : {q | P.Sees γ q} = ⋂ t ∈ Icc (0 : ℝ) 1, (fun q => lerp γ q t) ⁻¹' P.filled := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, Polygon.Sees]
    constructor
    · intro h t ht
      exact h ⟨t, ht.1, ht.2, rfl⟩
    · rintro h p ⟨t, h0, h1, rfl⟩
      exact h t ⟨h0, h1⟩
  rw [e]
  exact isClosed_biInter fun t _ => (Jordan.isClosed_filled P).preimage (continuous_lerp_right γ t)

/-- Two nonzero reals `A`, `B` with `(1 - t) A + t B = 0` for some `t ∈ [0, 1]` have opposite
signs. -/
theorem mul_neg_of_combo_eq_zero {A B t : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (h : (1 - t) * A + t * B = 0) : A * B < 0 := by
  by_contra hneg
  push Not at hneg
  have e : (1 - t) * (A * B) = -(t * B ^ 2) := by linear_combination B * h
  have hB2 : 0 < B ^ 2 := by positivity
  have h1 : 0 ≤ (1 - t) * (A * B) := mul_nonneg (by linarith) hneg
  have h2 : 0 ≤ t * B ^ 2 := mul_nonneg ht0 hB2.le
  have h3 : t * B ^ 2 = 0 := by linarith
  have ht : t = 0 := (mul_eq_zero.1 h3).resolve_right hB2.ne'
  subst ht
  apply hA
  linarith

/-- **No boundary point on `(γ, y]`.**  If `γ` sees `y`, and `y` is on no edge line and on no
line through `γ` and a vertex other than `γ`, then the points `lerp γ y s`, `0 < s ≤ 1`, are off
the boundary. -/
theorem lerp_not_mem_boundary (hP : P.Simple) {γ y : Point} (hs : P.Sees γ y)
    (hE : ∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) y ≠ 0)
    (hV : ∀ k < P.n, γ ≠ P.vtx k → det γ (P.vtx k) y ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    lerp γ y s ∉ P.boundary := by
  rintro ⟨j, hj, hz⟩
  have hj' : (j + 1) % P.n < P.n := Jordan.succIdx_lt P hj
  set a := P.vtx j with ha
  set b := P.vtx ((j + 1) % P.n) with hb
  have hfz : det a b (lerp γ y s) = 0 := det_eq_zero_of_mem_segment hz
  rw [det_lerp] at hfz
  have hfy := hE j hj
  by_cases hfγ : det a b γ = 0
  · rw [hfγ, mul_zero, zero_add] at hfz
    exact hfy ((mul_eq_zero.1 hfz).resolve_left hs0.ne')
  · have h₁ : det a b γ * det a b y < 0 := by
      have e : (1 - s) * (det a b γ * det a b y) = -(s * det a b y ^ 2) := by
        linear_combination (det a b y) * hfz
      have hpos : 0 < det a b y ^ 2 := by positivity
      have : 0 < s * det a b y ^ 2 := mul_pos hs0 hpos
      by_contra hc
      push Not at hc
      have : 0 ≤ (1 - s) * (det a b γ * det a b y) := mul_nonneg (by linarith) hc
      linarith
    -- the edge endpoints are strictly on opposite sides of the line `γ y`
    obtain ⟨t, ht0, ht1, hzt⟩ := hz
    have hline : det γ y (lerp a b t) = 0 := by
      rw [show lerp a b t = lerp γ y s from hzt.symm]
      exact det_lerp_self γ y s
    rw [det_lerp] at hline
    have hnz : ∀ k < P.n, det a b (P.vtx k) = 0 → det γ y (P.vtx k) ≠ 0 := by
      intro k hk hk0 h0
      by_cases hγk : γ = P.vtx k
      · rw [← hγk] at hk0
        exact hfγ hk0
      · apply hV k hk hγk
        rw [Geometry.det_swap23, h0, neg_zero]
    have hA : det γ y a ≠ 0 := hnz j hj (Geometry.det_self_outer _ _)
    have hB : det γ y b ≠ 0 := hnz _ hj' (Geometry.det_self_right _ _)
    have h₂ : det γ y a * det γ y b < 0 := mul_neg_of_combo_eq_zero hA hB ht0 ht1 hline
    exact Polygon.not_sees_of_proper_cross hP hj h₁ h₂ hs

/-- Near `γ` the boundary lies on edges whose lines pass through `γ`. -/
theorem exists_ball_boundary_near (P : Polygon) (γ : Point) :
    ∃ r > 0, ∀ w ∈ P.boundary, dist w γ < r →
      ∃ j < P.n, w ∈ P.edge j ∧ det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 := by
  obtain ⟨r, hr, hball⟩ := Jordan.exists_ball_disjoint_edges P
    ((Finset.range P.n).filter (fun j => det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ ≠ 0))
    (q := γ) (by
      intro j hj hγ
      exact (Finset.mem_filter.1 hj).2 (det_eq_zero_of_mem_segment hγ))
  refine ⟨r, hr, fun w hw hwr => ?_⟩
  obtain ⟨j, hj, hwj⟩ := hw
  refine ⟨j, hj, hwj, ?_⟩
  by_contra hne
  exact hball w (mem_ball.2 hwr) j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hne⟩) hwj

/-- Distance between points at the same parameter on two segments from `γ`. -/
theorem dist_lerp_lerp_le (γ y y' : Point) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dist (lerp γ y' s) (lerp γ y s) ≤ dist y' y := by
  rw [Geometry.lerp_eq_add_smul, Geometry.lerp_eq_add_smul, dist_eq_norm, dist_eq_norm,
    show γ + s • (y' - γ) - (γ + s • (y - γ)) = s • (y' - y) by module, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs0]
  exact mul_le_of_le_one_left (norm_nonneg _) hs1

/-- Distance from `γ` of a point of the segment `γ y'`. -/
theorem dist_lerp_left (γ y' : Point) {s : ℝ} (hs0 : 0 ≤ s) :
    dist (lerp γ y' s) γ = s * dist y' γ := by
  rw [Geometry.lerp_eq_add_smul, dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs0]

/-- **Visibility is open at generic points.**  If `γ ∈ P.filled` sees `y`, and `y` lies on no
edge line and on no line through `γ` and a vertex other than `γ`, then `γ` sees every point near
`y`. -/
theorem sees_eventually (hP : P.Simple) {γ y : Point} (hγ : γ ∈ P.filled) (hs : P.Sees γ y)
    (hE : ∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) y ≠ 0)
    (hV : ∀ k < P.n, γ ≠ P.vtx k → det γ (P.vtx k) y ≠ 0) :
    ∀ᶠ y' in 𝓝 y, P.Sees γ y' := by
  have hI : IsOpen (P.filled \ P.boundary) := Jordan.isOpen_filled_sdiff_boundary hP
  -- the boundary near `γ`
  obtain ⟨r, hr, hnear⟩ := exists_ball_boundary_near P γ
  -- the parameter `s₀` below which the segments stay in the ball of radius `r` around `γ`
  obtain ⟨s₀, hs₀pos, hs₀1, hs₀r⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ s₀ * (1 + dist y γ) < r := by
    have hD0 : 0 ≤ dist y γ := dist_nonneg
    refine ⟨min 1 (r / (2 * (1 + dist y γ))), lt_min one_pos (div_pos hr (by positivity)),
      min_le_left _ _, ?_⟩
    have h1 : min 1 (r / (2 * (1 + dist y γ))) ≤ r / (2 * (1 + dist y γ)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity)).1 h1
    have e : min 1 (r / (2 * (1 + dist y γ))) * (2 * (1 + dist y γ)) =
        2 * (min 1 (r / (2 * (1 + dist y γ))) * (1 + dist y γ)) := by ring
    linarith
  -- the compact piece `lerp γ y '' [s₀, 1]` lies in the interior of the region
  have hKc : IsCompact ((lerp γ y) '' Icc s₀ 1) := isCompact_Icc.image (continuous_lerp γ y)
  have hKI : (lerp γ y) '' Icc s₀ 1 ⊆ P.filled \ P.boundary := by
    rintro _ ⟨s, ⟨h0, h1⟩, rfl⟩
    exact ⟨hs ⟨s, (hs₀pos.trans_le h0).le, h1, rfl⟩,
      lerp_not_mem_boundary hP hs hE hV (hs₀pos.trans_le h0) h1⟩
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hI hKI
  -- nearby points are still off the edge lines
  have hE' : ∀ᶠ y' in 𝓝 y, ∀ j ∈ Iio P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) y' ≠ 0 :=
    (eventually_all_finite (finite_Iio P.n)).2 fun j hj =>
      (continuous_det_right _ _).continuousAt.eventually_ne (hE j hj)
  filter_upwards [ball_mem_nhds y (lt_min hδ one_pos), hE'] with y' hy' hE'
  rw [mem_ball, lt_min_iff] at hy'
  -- points at parameters `≥ s₀`
  have hfar : ∀ s, s₀ ≤ s → s ≤ 1 → lerp γ y' s ∈ P.filled \ P.boundary := by
    intro s h0 h1
    apply hthick
    rw [mem_thickening_iff]
    exact ⟨lerp γ y s, ⟨s, ⟨h0, h1⟩, rfl⟩,
      (dist_lerp_lerp_le γ y y' (hs₀pos.trans_le h0).le h1).trans_lt hy'.1⟩
  rintro _ ⟨s, h0, h1, rfl⟩
  show lerp γ y' s ∈ P.filled
  rcases le_or_gt s₀ s with hss | hss
  · exact (hfar s hss h1).1
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · subst h0'
    simpa using hγ
  -- points at parameters in `(0, s₀)`: a boundary crossing would lie near `γ`
  by_contra hout
  have hpc : IsPreconnected ((lerp γ y') '' Icc s s₀) :=
    isPreconnected_Icc.image _ (continuous_lerp γ y').continuousOn
  have hcross : ∃ σ ∈ Icc s s₀, lerp γ y' σ ∈ P.boundary := by
    by_contra hno
    push Not at hno
    obtain ⟨_, ⟨σ, hσ, rfl⟩, h1', h2'⟩ := hpc (P.filled)ᶜ (P.filled \ P.boundary)
      (Jordan.isClosed_filled P).isOpen_compl hI
      (by
        rintro _ ⟨σ, hσ, rfl⟩
        by_cases hm : lerp γ y' σ ∈ P.filled
        · exact Or.inr ⟨hm, hno σ hσ⟩
        · exact Or.inl hm)
      ⟨lerp γ y' s, ⟨s, ⟨le_rfl, hss.le⟩, rfl⟩, hout⟩
      ⟨lerp γ y' s₀, ⟨s₀, ⟨hss.le, le_rfl⟩, rfl⟩, hfar s₀ le_rfl hs₀1⟩
    exact h1' h2'.1
  obtain ⟨σ, ⟨hσ0, hσ1⟩, hσB⟩ := hcross
  have hσpos : 0 < σ := h0'.trans_le hσ0
  have hdist : dist (lerp γ y' σ) γ < r := by
    rw [dist_lerp_left γ y' hσpos.le]
    have : dist y' γ ≤ 1 + dist y γ := by
      have := dist_triangle y' y γ
      linarith [hy'.2]
    calc σ * dist y' γ ≤ s₀ * (1 + dist y γ) :=
          mul_le_mul hσ1 this dist_nonneg hs₀pos.le
      _ < r := hs₀r
  obtain ⟨j, hj, hwj, hjγ⟩ := hnear _ hσB hdist
  have h0j := det_eq_zero_of_mem_segment hwj
  rw [det_lerp, hjγ, mul_zero, zero_add] at h0j
  exact hE' j hj ((mul_eq_zero.1 h0j).resolve_left hσpos.ne')

/-- **Visibility is constant on preconnected generic sets.**  On a preconnected set of points
lying on no edge line and on no line through `γ` and a vertex other than `γ`, the guard
`γ ∈ P.filled` sees either every point or none. -/
theorem sees_of_isPreconnected (hP : P.Simple) {γ : Point} (hγ : γ ∈ P.filled) {R : Set Point}
    (hR : IsPreconnected R)
    (hE : ∀ y ∈ R, ∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) y ≠ 0)
    (hV : ∀ y ∈ R, ∀ k < P.n, γ ≠ P.vtx k → det γ (P.vtx k) y ≠ 0)
    {x x' : Point} (hx : x ∈ R) (hx' : x' ∈ R) (hs : P.Sees γ x) : P.Sees γ x' := by
  by_contra hns
  have hint : ∀ y ∈ R, P.Sees γ y → y ∈ interior {q | P.Sees γ q} := fun y hy hsy =>
    mem_interior_iff_mem_nhds.2 (sees_eventually hP hγ hsy (hE y hy) (hV y hy))
  obtain ⟨z, -, hzU, hzV⟩ := hR (interior {q | P.Sees γ q}) {q | P.Sees γ q}ᶜ isOpen_interior
    (isClosed_sees P γ).isOpen_compl
    (by
      intro y hy
      by_cases h : P.Sees γ y
      · exact Or.inl (hint y hy h)
      · exact Or.inr h)
    ⟨x, hx, hint x hx hs⟩ ⟨x', hx', hns⟩
  exact hzV (interior_subset hzU)

end

end ArtGallery.Membership.Witness
