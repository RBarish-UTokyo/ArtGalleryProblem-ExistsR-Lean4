module

public import ArtGallery.Jordan.Local

/-!
# The polygonal Jordan curve theorem

For a simple polygon `P` the complement of the boundary has exactly two connected components:
the bounded one (the points of odd crossing parity) and the unbounded one (even parity).

Main statements (all for `hP : P.Simple`):

* `parity_true_iff_bounded`: off the boundary, `parity P z = true ↔` the component of `z` is
  bounded;
* `mem_filled_iff`: off the boundary, `z ∈ P.filled ↔ parity P z = true`;
* `filled_compl_connected`, `filled_compl_eq_component`: `P.filledᶜ` is the (preconnected)
  component of any of its points;
* `interior_filled`: `interior P.filled = P.filled \ P.boundary`, which is open, preconnected and
  nonempty;
* `edge_sides`: near every edge, exactly one of the two sides is filled;
* `boundary_subset_closure_interior`, `boundary_subset_closure_compl`.

The proof: the left sides of all edges lie in one component and the right sides in another
(`side_component_exists`, by the parallelogram argument along an edge and the sector lemma at
each vertex); every component of the complement reaches an edge (`component_touches_edge`, by a
frontier argument), so there are at most two components; the flip lemma shows the two sides of a
non-vertical edge have different parities, so there are exactly two.

Provenance: adapted from `Chazelle/Jordan/Jordan.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Jordan

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp continuous_lerp lerp_zero lerp_one
  lerp_mem_segment point_ext point_ext_iff det_lerp_self isBoundedSet_of_subset)

/-! ### Convexity helpers -/

theorem combo_lt {a b c s s' : ℝ} (ha : c < a) (hb : c < b) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : s + s' = 1) : c < s * a + s' * b := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · have : s' = 1 := by linarith
    subst this; simpa using hb
  · have e : c = s * c + s' * c := by rw [← add_mul, h, one_mul]
    nlinarith [mul_lt_mul_of_pos_left ha hs, mul_le_mul_of_nonneg_left hb.le hs']

theorem combo_gt {a b c s s' : ℝ} (ha : a < c) (hb : b < c) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : s + s' = 1) : s * a + s' * b < c := by
  have := combo_lt (neg_lt_neg ha) (neg_lt_neg hb) hs hs' h
  linarith

theorem convex_fst_gt (c : ℝ) : Convex ℝ {x : Point | c < x.1} := by
  intro x hx y hy s s' hs hs' h
  show c < (s • x + s' • y).1
  simp only [Geometry.add_fst, Geometry.smul_fst]
  exact combo_lt hx hy hs hs' h

theorem convex_fst_lt (c : ℝ) : Convex ℝ {x : Point | x.1 < c} := by
  intro x hx y hy s s' hs hs' h
  show (s • x + s' • y).1 < c
  simp only [Geometry.add_fst, Geometry.smul_fst]
  exact combo_gt hx hy hs hs' h

theorem convex_snd_gt (c : ℝ) : Convex ℝ {x : Point | c < x.2} := by
  intro x hx y hy s s' hs hs' h
  show c < (s • x + s' • y).2
  simp only [Geometry.add_snd, Geometry.smul_snd]
  exact combo_lt hx hy hs hs' h

theorem convex_snd_lt (c : ℝ) : Convex ℝ {x : Point | x.2 < c} := by
  intro x hx y hy s s' hs hs' h
  show (s • x + s' • y).2 < c
  simp only [Geometry.add_snd, Geometry.smul_snd]
  exact combo_gt hx hy hs hs' h

/-! ### The parallelogram along an edge -/

/-- The open parallelogram of `σ`-side offset points of the segment `u v`, with parameters in
`(t₁, t₂)` and offsets in `(0, δ₀)`. -/
def par (u v : Point) (σ t₁ t₂ δ₀ : ℝ) : Set Point :=
  {x | ∃ t δ : ℝ, t₁ < t ∧ t < t₂ ∧ 0 < δ ∧ δ < δ₀ ∧ x = offset u v t (σ * δ)}

theorem offset_mem_par {u v : Point} {σ t₁ t₂ δ₀ t δ : ℝ} (h1 : t₁ < t) (h2 : t < t₂)
    (h3 : 0 < δ) (h4 : δ < δ₀) : offset u v t (σ * δ) ∈ par u v σ t₁ t₂ δ₀ :=
  ⟨t, δ, h1, h2, h3, h4, rfl⟩

/-- Convex combinations of offset points. -/
theorem smul_offset_add_smul_offset (u v : Point) (t t' δ δ' s s' : ℝ) (h : s + s' = 1) :
    s • offset u v t δ + s' • offset u v t' δ' =
      offset u v (s * t + s' * t') (s * δ + s' * δ') := by
  have : s' = 1 - s := by linarith
  subst this
  apply point_ext <;> simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst,
    Geometry.smul_snd, offset_fst, offset_snd] <;> ring

/-- The parallelogram is convex. -/
theorem convex_par (u v : Point) (σ t₁ t₂ δ₀ : ℝ) : Convex ℝ (par u v σ t₁ t₂ δ₀) := by
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ y ⟨t', δ', ht1', ht2', hδ1', hδ2', rfl⟩ s s' hs hs' h
  refine ⟨s * t + s' * t', s * δ + s' * δ', combo_lt ht1 ht1' hs hs' h, combo_gt ht2 ht2' hs hs' h,
    combo_lt hδ1 hδ1' hs hs' h, combo_gt hδ2 hδ2' hs hs' h, ?_⟩
  rw [smul_offset_add_smul_offset u v _ _ _ _ s s' h]
  congr 1
  ring

/-- For a compact sub-segment of an open edge there is a thin parallelogram on either side
avoiding the boundary. -/
theorem exists_par_subset_compl {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ ≠ 0) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < 1) :
    ∃ δ₀ > 0, par (P.vtx i) (P.vtx ((i + 1) % P.n)) σ t₁ t₂ δ₀ ⊆ P.boundaryᶜ := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  have huv : u ≠ v := simple_vtx_succ_ne hP hi
  set K : Set Point := lerp u v '' Icc t₁ t₂ with hK
  have hKc : IsCompact K := isCompact_Icc.image (continuous_lerp u v)
  set O : Set Point := (⋃ j ∈ (Finset.range P.n).erase i, P.edge j)ᶜ with hO
  have hOo : IsOpen O := (isClosed_biUnion_finset fun j _ => isClosed_edge P j).isOpen_compl
  have hKO : K ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [hO, mem_compl_iff, mem_iUnion, Finset.mem_erase, Finset.mem_range, not_exists]
    rintro j ⟨hji, hj⟩ hmem
    exact simple_openEdge_not_mem_other hP hi ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩ hj hji hmem
  obtain ⟨δ', hδ', hthick⟩ := hKc.exists_thickening_subset_open hOo hKO
  have hden : 0 < |σ| * ‖nrm u v‖ + 1 := by positivity
  refine ⟨δ' / (|σ| * ‖nrm u v‖ + 1), by positivity, ?_⟩
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ hb
  obtain ⟨j, hj, hxj⟩ := hb
  by_cases hji : j = i
  · -- not on edge `i`: the determinant is nonzero
    subst hji
    have h0 := Geometry.det_eq_zero_of_mem_segment hxj
    rw [det_offset] at h0
    have : σ * δ ≠ 0 := mul_ne_zero hσ hδ1.ne'
    exact this (by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h (sqLen_pos huv).ne')
  · -- not on another edge: the point is in the thickening
    have hmem : offset u v t (σ * δ) ∈ thickening δ' K := by
      rw [mem_thickening_iff]
      refine ⟨lerp u v t, ⟨t, ⟨ht1.le, ht2.le⟩, rfl⟩, ?_⟩
      unfold offset
      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ1]
      calc |σ| * δ * ‖nrm u v‖ = δ * (|σ| * ‖nrm u v‖) := by ring
        _ ≤ δ * (|σ| * ‖nrm u v‖ + 1) := by nlinarith
        _ < δ' / (|σ| * ‖nrm u v‖ + 1) * (|σ| * ‖nrm u v‖ + 1) :=
          mul_lt_mul_of_pos_right hδ2 hden
        _ = δ' := div_mul_cancel₀ _ hden.ne'
    have := hthick hmem
    simp only [hO, mem_compl_iff, mem_iUnion, Finset.mem_erase, Finset.mem_range,
      not_exists] at this
    exact this j ⟨hji, hj⟩ hxj

/-- **All offset points on one side of an edge lie in one component.** -/
theorem edge_side_component {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ ≠ 0) :
    ∃ c ∈ P.boundaryᶜ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ c := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  obtain ⟨δs, hδs, hpar⟩ := exists_par_subset_compl hP hi hσ (t₁ := 1 / 4) (t₂ := 3 / 4)
    (by norm_num) (by norm_num)
  have hc : offset u v (1 / 2) (σ * (δs / 2)) ∈ par u v σ (1 / 4) (3 / 4) δs :=
    offset_mem_par (by norm_num) (by norm_num) (by positivity) (by linarith)
  refine ⟨offset u v (1 / 2) (σ * (δs / 2)), hpar hc, ?_⟩
  intro t ht
  set t₁ := min t (1 / 2) / 2 with ht₁
  set t₂ := (max t (1 / 2) + 1) / 2 with ht₂
  have h1 : 0 < t₁ := by
    rw [ht₁]; have := ht.1; have := lt_min this (by norm_num : (0 : ℝ) < 1 / 2); positivity
  have h2 : t₂ < 1 := by
    rw [ht₂]; have := ht.2; have := max_lt this (by norm_num : (1 / 2 : ℝ) < 1); linarith
  have h3 : t₁ < t := by
    rw [ht₁]; have := min_le_left t (1 / 2); have := ht.1; linarith
  have h4 : t < t₂ := by
    rw [ht₂]; have := le_max_left t (1 / 2); have := ht.2; linarith
  have h5 : t₁ < 1 / 2 := by
    rw [ht₁]; have := min_le_right t (1 / 2); linarith
  have h6 : 1 / 2 < t₂ := by
    rw [ht₂]; have := le_max_right t (1 / 2); linarith
  obtain ⟨δ₀, hδ₀, hpar'⟩ := exists_par_subset_compl hP hi hσ h1 h2
  set δ₁ := min δ₀ δs with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ hδs
  -- the point `m` lies in both parallelograms
  have hm1 : offset u v (1 / 2) (σ * (δ₁ / 2)) ∈ par u v σ t₁ t₂ δ₀ :=
    offset_mem_par h5 h6 (by positivity) (by linarith [min_le_left δ₀ δs])
  have hm2 : offset u v (1 / 2) (σ * (δ₁ / 2)) ∈ par u v σ (1 / 4) (3 / 4) δs :=
    offset_mem_par (by norm_num) (by norm_num) (by positivity) (by linarith [min_le_right δ₀ δs])
  have hmc : offset u v (1 / 2) (σ * (δ₁ / 2)) ∈
      connectedComponentIn P.boundaryᶜ (offset u v (1 / 2) (σ * (δs / 2))) :=
    (convex_par u v σ _ _ _).isPreconnected.subset_connectedComponentIn hc hpar hm2
  have hsub : par u v σ t₁ t₂ δ₀ ⊆
      connectedComponentIn P.boundaryᶜ (offset u v (1 / 2) (σ * (δs / 2))) := by
    rw [connectedComponentIn_eq hmc]
    exact (convex_par u v σ _ _ _).isPreconnected.subset_connectedComponentIn hm1 hpar'
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  exact hsub (offset_mem_par h3 h4 hδ.1 hδ.2)

/-! ### Chaining around the boundary -/

/-- **All left sides (resp. all right sides) of all edges lie in one component.** -/
theorem side_component_exists {P : Polygon} (hP : P.Simple) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c ∈ P.boundaryᶜ, ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ c := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hn := simple_three_le hP
  have hex : ∀ i, ∃ c : Point, i < P.n → c ∈ P.boundaryᶜ ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ c := by
    intro i
    by_cases hi : i < P.n
    · obtain ⟨c, hc, h⟩ := edge_side_component hP hi hσ0
      exact ⟨c, fun _ => ⟨hc, h⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hi⟩
  choose c hc using hex
  -- consecutive edges share the component
  have hstep : ∀ i, i + 1 < P.n →
      connectedComponentIn P.boundaryᶜ (c (i + 1)) = connectedComponentIn P.boundaryᶜ (c i) := by
    intro i hi1
    have hi : i < P.n := by omega
    have hmod : (i + 1) % P.n = i + 1 := Nat.mod_eq_of_lt hi1
    have hprev : prevIdx P (i + 1) = i := by
      rw [prevIdx_eq P hi1]; simp
    obtain ⟨U, hU1, hU2, hU3⟩ := vertex_sector hP hi1 hσ
    rw [hprev] at hU3
    have hci := (hc i hi).2
    have hci1 := (hc (i + 1) hi1).2
    rw [hmod] at hci
    obtain ⟨s, hs, hs01⟩ := (hU3.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have hs' : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs01.2], by linarith [hs01.1]⟩
    obtain ⟨δ, ⟨⟨hx, hy⟩, hxc⟩, hyc⟩ :=
      ((hs.and (hci (1 - s) hs')).and (hci1 s hs01)).exists
    have hUx : U ⊆ connectedComponentIn P.boundaryᶜ (c i) := by
      rw [connectedComponentIn_eq hxc]
      exact hU2.subset_connectedComponentIn hx hU1
    have hyci : offset (P.vtx (i + 1)) (P.vtx ((i + 1 + 1) % P.n)) s (σ * δ) ∈
        connectedComponentIn P.boundaryᶜ (c i) := hUx hy
    rw [connectedComponentIn_eq hyc, connectedComponentIn_eq hyci]
  have hall : ∀ i, i < P.n →
      connectedComponentIn P.boundaryᶜ (c i) = connectedComponentIn P.boundaryᶜ (c 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ k ih => intro hk; rw [hstep k hk, ih (by omega)]
  refine ⟨c 0, (hc 0 (by omega)).1, fun i hi t ht => ?_⟩
  filter_upwards [(hc i hi).2 t ht] with δ hδ
  rwa [hall i hi] at hδ

/-! ### Every component reaches an edge -/

/-- The punctured ball is preconnected. -/
theorem isPreconnected_punctured_ball (q : Point) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball q r \ {q}) := by
  have hA1 : IsPreconnected (ball q r ∩ {x : Point | q.2 < x.2}) :=
    ((convex_ball q r).inter (convex_snd_gt q.2)).isPreconnected
  have hA2 : IsPreconnected (ball q r ∩ {x : Point | q.1 < x.1}) :=
    ((convex_ball q r).inter (convex_fst_gt q.1)).isPreconnected
  have hA3 : IsPreconnected (ball q r ∩ {x : Point | x.2 < q.2}) :=
    ((convex_ball q r).inter (convex_snd_lt q.2)).isPreconnected
  have hA4 : IsPreconnected (ball q r ∩ {x : Point | x.1 < q.1}) :=
    ((convex_ball q r).inter (convex_fst_lt q.1)).isPreconnected
  have hr2 : |r / 2| < r := by rw [abs_of_pos (by positivity)]; linarith
  have hr2' : |-(r / 2)| < r := by rw [abs_neg]; exact hr2
  have hp12 : ((q.1 + r / 2, q.2 + r / 2) : Point) ∈ ball q r := by
    rw [mem_ball_iff_abs]; simp only [add_sub_cancel_left]; exact ⟨hr2, hr2⟩
  have hp23 : ((q.1 + r / 2, q.2 - r / 2) : Point) ∈ ball q r := by
    rw [mem_ball_iff_abs]; simp only [add_sub_cancel_left, sub_sub_cancel_left]; exact ⟨hr2, hr2'⟩
  have hp34 : ((q.1 - r / 2, q.2 - r / 2) : Point) ∈ ball q r := by
    rw [mem_ball_iff_abs]; simp only [sub_sub_cancel_left]; exact ⟨hr2', hr2'⟩
  have h12 : IsPreconnected ((ball q r ∩ {x : Point | q.2 < x.2}) ∪
      (ball q r ∩ {x : Point | q.1 < x.1})) :=
    IsPreconnected.union ((q.1 + r / 2, q.2 + r / 2) : Point)
      ⟨hp12, show q.2 < q.2 + r / 2 by linarith⟩ ⟨hp12, show q.1 < q.1 + r / 2 by linarith⟩ hA1 hA2
  have h123 : IsPreconnected (((ball q r ∩ {x : Point | q.2 < x.2}) ∪
      (ball q r ∩ {x : Point | q.1 < x.1})) ∪ (ball q r ∩ {x : Point | x.2 < q.2})) :=
    IsPreconnected.union ((q.1 + r / 2, q.2 - r / 2) : Point)
      (Or.inr ⟨hp23, show q.1 < q.1 + r / 2 by linarith⟩)
      ⟨hp23, show q.2 - r / 2 < q.2 by linarith⟩ h12 hA3
  have h1234 : IsPreconnected ((((ball q r ∩ {x : Point | q.2 < x.2}) ∪
      (ball q r ∩ {x : Point | q.1 < x.1})) ∪ (ball q r ∩ {x : Point | x.2 < q.2})) ∪
      (ball q r ∩ {x : Point | x.1 < q.1})) :=
    IsPreconnected.union ((q.1 - r / 2, q.2 - r / 2) : Point)
      (Or.inr ⟨hp34, show q.2 - r / 2 < q.2 by linarith⟩)
      ⟨hp34, show q.1 - r / 2 < q.1 by linarith⟩ h123 hA4
  convert h1234 using 1
  ext x
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
  constructor
  · rintro ⟨hx, hne⟩
    have : x.1 ≠ q.1 ∨ x.2 ≠ q.2 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hne (point_ext h.1 h.2)
    rcases this with h | h
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (Or.inl (Or.inr ⟨hx, h⟩))
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨hx, h⟩))
  · rintro (((⟨hx, h⟩ | ⟨hx, h⟩) | ⟨hx, h⟩) | ⟨hx, h⟩)
    · exact ⟨hx, fun hxq => by rw [hxq] at h; exact lt_irrefl _ (show q.2 < q.2 from h)⟩
    · exact ⟨hx, fun hxq => by rw [hxq] at h; exact lt_irrefl _ (show q.1 < q.1 from h)⟩
    · exact ⟨hx, fun hxq => by rw [hxq] at h; exact lt_irrefl _ (show q.2 < q.2 from h)⟩
    · exact ⟨hx, fun hxq => by rw [hxq] at h; exact lt_irrefl _ (show q.1 < q.1 from h)⟩

/-- The frontier of a component of the complement of the boundary lies in the boundary. -/
theorem frontier_component_subset_boundary (P : Polygon) (z : Point) :
    frontier (connectedComponentIn P.boundaryᶜ z) ⊆ P.boundary := by
  intro q hq
  by_contra hqb
  have hU : IsOpen (connectedComponentIn P.boundaryᶜ z) :=
    isOpen_connectedComponentIn_boundary_compl P z
  rw [hU.frontier_eq] at hq
  have hnhds : connectedComponentIn P.boundaryᶜ q ∈ 𝓝 q :=
    connectedComponentIn_mem_nhds ((isOpen_boundary_compl P).mem_nhds hqb)
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hq.1 _ hnhds
  have : connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ q := by
    rw [connectedComponentIn_eq hy2, connectedComponentIn_eq hy1]
  exact hq.2 (this ▸ mem_connectedComponentIn hqb)

/-- Every component of the complement of the boundary has a frontier point on an open edge. -/
theorem exists_frontier_point {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    ∃ q, q ∈ frontier (connectedComponentIn P.boundaryᶜ z) ∧ q ∈ P.boundary ∧
      ∀ j, j < P.n → q ≠ P.vtx j := by
  have hn := simple_three_le hP
  set U := connectedComponentIn P.boundaryᶜ z with hUdef
  have hU : IsOpen U := isOpen_connectedComponentIn_boundary_compl P z
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUb : U ⊆ P.boundaryᶜ := connectedComponentIn_subset _ _
  have hfr : frontier U ⊆ P.boundary := frontier_component_subset_boundary P z
  have hv0 : P.vtx 0 ∈ P.boundary := ⟨0, by omega, Geometry.left_mem_segment _ _⟩
  have hne : (frontier U).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at h
    rcases isClopen_iff.1 h with h | h
    · rw [h] at hzU; exact hzU
    · exact hUb (h ▸ mem_univ (P.vtx 0)) hv0
  by_contra hcon
  have hvert : ∀ q ∈ frontier U, ∃ j, j < P.n ∧ q = P.vtx j := by
    intro q hq
    by_contra h
    exact hcon ⟨q, hq, hfr hq, fun j hj hqj => h ⟨j, hj, hqj⟩⟩
  obtain ⟨q, hq⟩ := hne
  obtain ⟨j, hj, rfl⟩ := hvert q hq
  -- a ball around the vertex containing no other vertex
  set V : Set Point := ((((Finset.range P.n).image P.vtx).erase (P.vtx j) : Finset Point) : Set Point)
    with hV
  have hVc : IsClosed V := (Finset.finite_toSet _).isClosed
  have hqV : P.vtx j ∉ V := by simp [hV]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVc.isOpen_compl _ hqV
  set D := ball (P.vtx j) r \ {P.vtx j} with hD
  have hDfr : ∀ x ∈ D, x ∉ frontier U := by
    rintro x ⟨hxb, hxq⟩ hxf
    obtain ⟨k, hk, rfl⟩ := hvert x hxf
    apply hball hxb
    simp only [hV, Finset.coe_erase, Finset.coe_image, Finset.coe_range, Set.mem_sdiff, mem_image,
      mem_Iio, mem_singleton_iff]
    exact ⟨⟨k, hk, rfl⟩, hxq⟩
  have hDsub : D ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      intro hxc
      exact hDfr x hx (by rw [hU.frontier_eq]; exact ⟨hxc, hxU⟩)
  have hDU : (D ∩ U).Nonempty := by
    obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.1 (frontier_subset_closure hq) _ isOpen_ball
      (mem_ball_self hr)
    refine ⟨y, ⟨hyb, ?_⟩, hyU⟩
    rw [hU.frontier_eq] at hq
    rintro rfl
    exact hq.2 hyU
  have hDU' : D ⊆ U :=
    (isPreconnected_punctured_ball _ hr).subset_left_of_subset_union hU
      isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure) hDsub hDU
  -- but `D` contains points of edge `j`
  have hw : P.vtx j ≠ P.vtx ((j + 1) % P.n) := simple_vtx_succ_ne hP hj
  obtain ⟨ε, hεb, hε01⟩ := ((tendsto_lerp_zero (P.vtx j) (P.vtx ((j + 1) % P.n))).eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr))).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ)) |>.exists
  have hpD : lerp (P.vtx j) (P.vtx ((j + 1) % P.n)) ε ∈ D :=
    ⟨hεb, fun h => lerp_ne_left hw hε01.1 (mem_singleton_iff.1 h)⟩
  exact hUb (hDU' hpD) ⟨j, hj, lerp_mem_segment _ _ hε01.1.le hε01.2.le⟩

/-- A side of the strip around an open edge avoids the boundary. -/
theorem side_subset_compl (P : Polygon) {u v q : Point} {r : ℝ}
    (hstrip : ∀ x ∈ ball q r, (x ∈ P.boundary ↔ det u v x = 0)) (σ : ℝ) :
    ball q r ∩ {x | 0 < σ * det u v x} ⊆ P.boundaryᶜ := by
  rintro x ⟨hxb, hx⟩ hxB
  have hx' : 0 < σ * det u v x := hx
  rw [(hstrip x hxb).1 hxB, mul_zero] at hx'
  exact lt_irrefl _ hx'

/-- A side of the strip around an open edge lies in the component of any of its points. -/
theorem side_subset_component (P : Polygon) {u v q : Point} {r : ℝ}
    (hstrip : ∀ x ∈ ball q r, (x ∈ P.boundary ↔ det u v x = 0)) {σ : ℝ}
    {c x : Point} (hx : x ∈ ball q r ∩ {x | 0 < σ * det u v x})
    (hxc : x ∈ connectedComponentIn P.boundaryᶜ c) :
    ball q r ∩ {x | 0 < σ * det u v x} ⊆ connectedComponentIn P.boundaryᶜ c := by
  rw [connectedComponentIn_eq hxc]
  exact ((convex_ball q r).inter (convex_det_pos u v σ)).isPreconnected.subset_connectedComponentIn
    hx (side_subset_compl P hstrip σ)

/-- **Every component reaches an edge**: the component of any point off the boundary contains,
for some edge `i`, some parameter `t` and some side `σ`, all the offset points
`offset t (σ * δ)` for small `δ`. -/
theorem component_touches_edge {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    ∃ i, i < P.n ∧ ∃ t ∈ Ioo (0 : ℝ) 1, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ z := by
  obtain ⟨q, hqf, hqb, hqv⟩ := exists_frontier_point hP hz
  obtain ⟨i, hi, t₀, ht₀, rfl⟩ := exists_openEdge_of_mem_boundary P hqb hqv
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  obtain ⟨r, hr, hstrip⟩ := strip hP hi ht₀
  obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.1 (frontier_subset_closure hqf) _ isOpen_ball
    (mem_ball_self hr)
  have hyB : y ∉ P.boundary := connectedComponentIn_subset _ _ hyU
  have hdet : det u v y ≠ 0 := fun h => hyB ((hstrip y hyb).2 h)
  refine ⟨i, hi, t₀, ht₀, ?_⟩
  rcases lt_or_gt_of_ne hdet with h | h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hsub := side_subset_component P hstrip (σ := -1) (c := z) (x := y)
      ⟨hyb, by show 0 < (-1) * det u v y; linarith⟩ hyU
    filter_upwards [eventually_offset_mem (-1) isOpen_ball (mem_ball_self hr),
      self_mem_nhdsWithin] with δ hδ hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine hsub ⟨hδ, ?_⟩
    show 0 < (-1) * det u v (offset u v t₀ ((-1) * δ))
    rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos (simple_vtx_succ_ne hP hi))]
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hsub := side_subset_component P hstrip (σ := 1) (c := z) (x := y)
      ⟨hyb, by show 0 < 1 * det u v y; linarith⟩ hyU
    filter_upwards [eventually_offset_mem 1 isOpen_ball (mem_ball_self hr),
      self_mem_nhdsWithin] with δ hδ hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine hsub ⟨hδ, ?_⟩
    show 0 < 1 * det u v (offset u v t₀ (1 * δ))
    rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos (simple_vtx_succ_ne hP hi))]

/-! ### A non-vertical edge, and the two sides have different parities -/

/-- A simple polygon has a non-vertical edge. -/
theorem exists_nonvertical_edge {P : Polygon} (hP : P.Simple) :
    ∃ i, i < P.n ∧ (P.vtx i).1 ≠ (P.vtx ((i + 1) % P.n)).1 := by
  have hn := simple_three_le hP
  by_contra hcon
  have hvert : ∀ i, i < P.n → (P.vtx i).1 = (P.vtx ((i + 1) % P.n)).1 := by
    intro i hi
    by_contra h
    exact hcon ⟨i, hi, h⟩
  have hall : ∀ i, i < P.n → (P.vtx i).1 = (P.vtx 0).1 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have := hvert k (by omega)
      rw [Nat.mod_eq_of_lt hk] at this
      rw [← this, ih (by omega)]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range P.n) (fun i => (P.vtx i).2)
    ⟨0, Finset.mem_range.2 (by omega)⟩
  rw [Finset.mem_range] at hk
  set j := prevIdx P k with hj
  have hjn : j < P.n := prevIdx_lt P hk
  have hji : j ≠ k := prevIdx_ne P hn hk
  have hks : (k + 1) % P.n < P.n := succIdx_lt P hk
  set a := P.vtx j with ha
  set v := P.vtx k with hv
  set b := P.vtx ((k + 1) % P.n) with hb
  have hav : a ≠ v := simple_vtx_ne hP hjn hk hji
  have hvb : v ≠ b := simple_vtx_succ_ne hP hk
  have hab : a ≠ b := simple_vtx_ne hP hjn hks (prevIdx_ne_succIdx P hn hk)
  have ha1 : a.1 = v.1 := by rw [ha, hv, hall j hjn, hall k hk]
  have hb1 : b.1 = v.1 := by rw [hb, hv, hall _ hks, hall k hk]
  have ha2 : a.2 < v.2 := by
    rcases lt_or_eq_of_le (hmax j (Finset.mem_range.2 hjn)) with h | h
    · exact h
    · exact absurd (point_ext ha1 h) hav
  have hb2 : b.2 < v.2 := by
    rcases lt_or_eq_of_le (hmax _ (Finset.mem_range.2 hks)) with h | h
    · exact h
    · exact absurd (point_ext hb1 h) hvb.symm
  set ε := min (v.2 - a.2) (v.2 - b.2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min (sub_pos.2 ha2) (sub_pos.2 hb2); positivity
  have hεa : ε < v.2 - a.2 := by rw [hε]; have := min_le_left (v.2 - a.2) (v.2 - b.2); linarith
  have hεb : ε < v.2 - b.2 := by rw [hε]; have := min_le_right (v.2 - a.2) (v.2 - b.2); linarith
  set p : Point := (v.1, v.2 - ε) with hp
  have hp1 : p ∈ ArtGallery.segment a v :=
    mem_segment_of_vertical ha1 (by rw [hp, ha1]) (by rw [hp]; simp only; linarith)
      (by rw [hp]; simp only; linarith)
  have hp2 : p ∈ ArtGallery.segment v b := by
    rw [Geometry.segment_comm]
    exact mem_segment_of_vertical hb1 (by rw [hp, hb1]) (by rw [hp]; simp only; linarith)
      (by rw [hp]; simp only; linarith)
  have hmem : p ∈ P.edge j ∩ P.edge k := by
    rw [edge_prevIdx P hk]; exact ⟨hp1, hp2⟩
  rw [simple_edge_inter hP hjn hk hji] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [prevIdx_succ P hk] at h1
  have hpv : p ≠ v := fun h => by
    have := congrArg Prod.snd h; simp only [hp] at this; linarith
  have hpa : p ≠ a := fun h => by
    have := congrArg Prod.snd h; simp only [hp] at this; linarith
  have hpb : p ≠ b := fun h => by
    have := congrArg Prod.snd h; simp only [hp] at this; linarith
  rcases h1 with h1 | h1
  · exact hpa h1
  · exact hpv h1

/-- The vertical displacements of a point of the line through `u v`. -/
theorem det_vertical_shift (u v m : Point) (ε : ℝ) (hm : det u v m = 0) :
    det u v (m.1, m.2 + ε) = ε * (v.1 - u.1) ∧ det u v (m.1, m.2 - ε) = -(ε * (v.1 - u.1)) := by
  unfold det at *
  simp only at *
  constructor <;> linear_combination hm

/-- **The two components.**  For a simple polygon there are two points `cL`, `cR` off the
boundary with different parities such that every component of the complement of the boundary is
the component of `cL` or of `cR`, and for every edge the left offset points lie in the component
of `cL`, the right offset points in that of `cR`. -/
theorem two_components {P : Polygon} (hP : P.Simple) :
    ∃ cL cR : Point, cL ∉ P.boundary ∧ cR ∉ P.boundary ∧ parity P cL ≠ parity P cR ∧
      (∀ z, z ∉ P.boundary → connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ cL ∨
        connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ cR) ∧
      ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t δ ∈ connectedComponentIn P.boundaryᶜ cL ∧
        offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (-δ) ∈ connectedComponentIn P.boundaryᶜ cR := by
  obtain ⟨cL, hcL, hL⟩ := side_component_exists hP (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
  obtain ⟨cR, hcR, hR⟩ := side_component_exists hP (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
  simp only [one_mul] at hL
  simp only [neg_one_mul] at hR
  refine ⟨cL, cR, hcL, hcR, ?_, ?_, fun i hi t ht => (hL i hi t ht).and (hR i hi t ht)⟩
  · -- different parities, via the flip lemma at a non-vertical edge
    obtain ⟨i, hi, hne⟩ := exists_nonvertical_edge hP
    set u := P.vtx i with hu
    set v := P.vtx ((i + 1) % P.n) with hv
    have huv : u ≠ v := simple_vtx_succ_ne hP hi
    have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    set m := lerp u v (1 / 2) with hm
    obtain ⟨ε₀, hε₀, hflip⟩ := parity_flip P hi (lerp_mem_segment u v hmid.1.le hmid.2.le) hne
      (lerp_ne_left huv hmid.1) (lerp_ne_right huv hmid.2)
      (fun j hj hji => simple_openEdge_not_mem_other hP hi hmid hj hji)
    obtain ⟨r, hr, hstrip⟩ := strip hP hi hmid
    set ε := min ε₀ r / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; have := lt_min hε₀ hr; positivity
    have hεε₀ : ε < ε₀ := by rw [hε]; have := min_le_left ε₀ r; linarith
    have hεr : ε < r := by rw [hε]; have := min_le_right ε₀ r; linarith
    obtain ⟨hpB, hmB, hpar⟩ := hflip ε hε0 hεε₀
    have hpb : ((m.1, m.2 + ε) : Point) ∈ ball m r := by
      rw [mem_ball_iff_abs]; simp only [sub_self, abs_zero, add_sub_cancel_left]
      exact ⟨hr, by rw [abs_of_pos hε0]; exact hεr⟩
    have hmb : ((m.1, m.2 - ε) : Point) ∈ ball m r := by
      rw [mem_ball_iff_abs]; simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
      exact ⟨hr, by rw [abs_of_pos hε0]; exact hεr⟩
    obtain ⟨hd1, hd2⟩ := det_vertical_shift u v m ε (det_lerp_self u v _)
    -- the two sides lie in the two components
    have hLsub : ball m r ∩ {x | 0 < 1 * det u v x} ⊆ connectedComponentIn P.boundaryᶜ cL := by
      obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ0⟩ := ((eventually_offset_mem 1 isOpen_ball (mem_ball_self hr)).and
        (hL i hi _ hmid)).and self_mem_nhdsWithin |>.exists
      have hδ0' : (0 : ℝ) < δ := hδ0
      refine side_subset_component P hstrip (σ := 1) (x := offset u v (1 / 2) (1 * δ))
        ⟨hδ1, ?_⟩ (by rw [one_mul]; exact hδ2)
      show 0 < 1 * det u v (offset u v (1 / 2) (1 * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos huv)]
    have hRsub : ball m r ∩ {x | 0 < (-1) * det u v x} ⊆
        connectedComponentIn P.boundaryᶜ cR := by
      obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ0⟩ := ((eventually_offset_mem (-1) isOpen_ball (mem_ball_self hr)).and
        (hR i hi _ hmid)).and self_mem_nhdsWithin |>.exists
      have hδ0' : (0 : ℝ) < δ := hδ0
      refine side_subset_component P hstrip (σ := -1)
        (x := offset u v (1 / 2) ((-1) * δ)) ⟨hδ1, ?_⟩ (by rw [neg_one_mul]; exact hδ2)
      show 0 < (-1) * det u v (offset u v (1 / 2) ((-1) * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos huv)]
    intro hpar'
    apply hpar
    rcases lt_or_gt_of_ne hne with h | h
    · -- `u.1 < v.1`: the upper point is on the left
      have h1 : ((m.1, m.2 + ε) : Point) ∈ connectedComponentIn P.boundaryᶜ cL :=
        hLsub ⟨hpb, by show 0 < 1 * det u v (m.1, m.2 + ε); rw [hd1]; nlinarith⟩
      have h2 : ((m.1, m.2 - ε) : Point) ∈ connectedComponentIn P.boundaryᶜ cR :=
        hRsub ⟨hmb, by show 0 < (-1) * det u v (m.1, m.2 - ε); rw [hd2]; nlinarith⟩
      rw [parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2,
        hpar']
    · have h1 : ((m.1, m.2 + ε) : Point) ∈ connectedComponentIn P.boundaryᶜ cR :=
        hRsub ⟨hpb, by show 0 < (-1) * det u v (m.1, m.2 + ε); rw [hd1]; nlinarith⟩
      have h2 : ((m.1, m.2 - ε) : Point) ∈ connectedComponentIn P.boundaryᶜ cL :=
        hLsub ⟨hmb, by show 0 < 1 * det u v (m.1, m.2 - ε); rw [hd2]; nlinarith⟩
      rw [parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2,
        hpar']
  · -- every component is one of the two
    intro z hz
    obtain ⟨i, hi, t, ht, σ, hσ, hev⟩ := component_touches_edge hP hz
    rcases hσ with rfl | rfl
    · left
      obtain ⟨δ, h1, h2⟩ := (hev.and (hL i hi t ht)).exists
      rw [one_mul] at h1
      rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]
    · right
      obtain ⟨δ, h1, h2⟩ := (hev.and (hR i hi t ht)).exists
      rw [neg_one_mul] at h1
      rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]

/-! ### Consequences -/

/-- Points with the same component have the same parity. -/
theorem parity_eq_of_connectedComponentIn_eq (P : Polygon) {z w : Point} (hz : z ∉ P.boundary)
    (h : connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ w) :
    parity P z = parity P w := by
  have hzw : z ∈ connectedComponentIn P.boundaryᶜ w := h ▸ mem_connectedComponentIn hz
  exact parity_eq_of_mem_connectedComponentIn P hzw

/-- **Two points off the boundary with the same parity lie in the same component.** -/
theorem connectedComponentIn_eq_of_parity_eq {P : Polygon} (hP : P.Simple) {z w : Point}
    (hz : z ∉ P.boundary) (hw : w ∉ P.boundary) (h : parity P z = parity P w) :
    connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ w := by
  obtain ⟨cL, cR, hcL, hcR, hne, htwo, -⟩ := two_components hP
  rcases htwo z hz with hz' | hz' <;> rcases htwo w hw with hw' | hw'
  · rw [hz', hw']
  · exfalso
    apply hne
    rw [← parity_eq_of_connectedComponentIn_eq P hz hz', h,
      parity_eq_of_connectedComponentIn_eq P hw hw']
  · exfalso
    apply hne
    rw [← parity_eq_of_connectedComponentIn_eq P hw hw', ← h,
      parity_eq_of_connectedComponentIn_eq P hz hz']
  · rw [hz', hw']

/-- The far point `(0, -coordBound P - 1)`: off the boundary, even, unbounded component. -/
theorem far_point_spec (P : Polygon) :
    ((0, -coordBound P - 1) : Point) ∉ P.boundary ∧
      parity P (0, -coordBound P - 1) = false ∧
      ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ (0, -coordBound P - 1)) := by
  have hfar : coordBound P < ((0, -coordBound P - 1) : Point).1 ∨
      ((0, -coordBound P - 1) : Point).1 < -coordBound P ∨
      coordBound P < ((0, -coordBound P - 1) : Point).2 ∨
      ((0, -coordBound P - 1) : Point).2 < -coordBound P :=
    Or.inr (Or.inr (Or.inr (by simp only; linarith)))
  exact ⟨not_mem_boundary_of_far P hfar, parity_eq_false_of_far_any P hfar,
    not_isBoundedSet_connectedComponentIn_of_far P hfar⟩

/-- **Parity characterises boundedness**: off the boundary, the component of `z` is bounded iff
`z` has odd parity. -/
theorem parity_true_iff_bounded {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    parity P z = true ↔ IsBoundedSet (connectedComponentIn P.boundaryᶜ z) := by
  constructor
  · exact odd_component_bounded P
  · intro hb
    by_contra h
    rw [Bool.not_eq_true] at h
    obtain ⟨hw, hwp, hwu⟩ := far_point_spec P
    have := connectedComponentIn_eq_of_parity_eq hP hz hw (by rw [h, hwp])
    rw [this] at hb
    exact hwu hb

/-- **Membership in the filled region off the boundary is odd parity.** -/
theorem mem_filled_iff {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    z ∈ P.filled ↔ parity P z = true :=
  (mem_filled_iff_bounded P hz).trans (parity_true_iff_bounded hP hz).symm

/-- The complement of the filled region: the points off the boundary of even parity. -/
theorem filled_compl_eq {P : Polygon} (hP : P.Simple) :
    P.filledᶜ = {z | z ∉ P.boundary ∧ parity P z = false} := by
  ext z
  rw [mem_filled_compl_iff]
  constructor
  · rintro ⟨hz, hb⟩
    refine ⟨hz, ?_⟩
    rw [← Bool.not_eq_true, parity_true_iff_bounded hP hz]
    exact hb
  · rintro ⟨hz, hp⟩
    refine ⟨hz, ?_⟩
    rw [← parity_true_iff_bounded hP hz, hp]
    exact Bool.false_ne_true

/-- The filled region minus the boundary: the points off the boundary of odd parity. -/
theorem filled_sdiff_boundary_eq {P : Polygon} (hP : P.Simple) :
    P.filled \ P.boundary = {z | z ∉ P.boundary ∧ parity P z = true} := by
  ext z
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨hf, hz⟩
    exact ⟨hz, (mem_filled_iff hP hz).1 hf⟩
  · rintro ⟨hz, hp⟩
    exact ⟨(mem_filled_iff hP hz).2 hp, hz⟩

/-- The complement of the filled region is the component of any of its points. -/
theorem filled_compl_eq_component {P : Polygon} (hP : P.Simple) {w : Point} (hw : w ∈ P.filledᶜ) :
    P.filledᶜ = connectedComponentIn P.boundaryᶜ w := by
  rw [filled_compl_eq hP] at hw ⊢
  obtain ⟨hwb, hwp⟩ := hw
  ext z
  constructor
  · rintro ⟨hz, hp⟩
    rw [← connectedComponentIn_eq_of_parity_eq hP hz hwb (by rw [hp, hwp])]
    exact mem_connectedComponentIn hz
  · intro hz
    have hzb : z ∉ P.boundary := connectedComponentIn_subset _ _ hz
    exact ⟨hzb, by rw [parity_eq_of_mem_connectedComponentIn P hz, hwp]⟩

/-- The filled region minus the boundary is the component of any of its points. -/
theorem filled_sdiff_boundary_eq_component {P : Polygon} (hP : P.Simple) {w : Point}
    (hw : w ∈ P.filled \ P.boundary) :
    P.filled \ P.boundary = connectedComponentIn P.boundaryᶜ w := by
  rw [filled_sdiff_boundary_eq hP] at hw ⊢
  obtain ⟨hwb, hwp⟩ := hw
  ext z
  constructor
  · rintro ⟨hz, hp⟩
    rw [← connectedComponentIn_eq_of_parity_eq hP hz hwb (by rw [hp, hwp])]
    exact mem_connectedComponentIn hz
  · intro hz
    have hzb : z ∉ P.boundary := connectedComponentIn_subset _ _ hz
    exact ⟨hzb, by rw [parity_eq_of_mem_connectedComponentIn P hz, hwp]⟩

/-- The complement of the filled region is nonempty. -/
theorem filled_compl_nonempty (P : Polygon) : P.filledᶜ.Nonempty :=
  ⟨_, fun h => (far_point_spec P).2.2 ((mem_filled_iff_bounded P (far_point_spec P).1).1 h)⟩

/-- **The exterior is connected.** -/
theorem filled_compl_connected {P : Polygon} (hP : P.Simple) : IsPreconnected P.filledᶜ := by
  obtain ⟨w, hw⟩ := filled_compl_nonempty P
  rw [filled_compl_eq_component hP hw]
  exact isPreconnected_connectedComponentIn

/-- There is a point of odd parity off the boundary. -/
theorem exists_odd_point {P : Polygon} (hP : P.Simple) :
    ∃ z, z ∉ P.boundary ∧ parity P z = true := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, -⟩ := two_components hP
  cases hL : parity P cL
  · refine ⟨cR, hcR, ?_⟩
    cases hR : parity P cR
    · exact absurd (hL.trans hR.symm) hne
    · rfl
  · exact ⟨cL, hcL, hL⟩

/-- **The interior region is nonempty.** -/
theorem filled_sdiff_boundary_nonempty {P : Polygon} (hP : P.Simple) :
    (P.filled \ P.boundary).Nonempty := by
  obtain ⟨z, hz, hp⟩ := exists_odd_point hP
  exact ⟨z, odd_mem_filled P hp, hz⟩

/-- **The interior region is connected.** -/
theorem filled_sdiff_boundary_connected {P : Polygon} (hP : P.Simple) :
    IsPreconnected (P.filled \ P.boundary) := by
  obtain ⟨w, hw⟩ := filled_sdiff_boundary_nonempty hP
  rw [filled_sdiff_boundary_eq_component hP hw]
  exact isPreconnected_connectedComponentIn

/-- The filled region minus the boundary is open. -/
theorem isOpen_filled_sdiff_boundary {P : Polygon} (hP : P.Simple) :
    IsOpen (P.filled \ P.boundary) := by
  obtain ⟨w, hw⟩ := filled_sdiff_boundary_nonempty hP
  rw [filled_sdiff_boundary_eq_component hP hw]
  exact isOpen_connectedComponentIn_boundary_compl P w

/-- Points of an open edge are limits of `σ`-side offset points, hence in the closure of the
component containing those. -/
theorem openEdge_mem_closure_component (P : Polygon) {i : ℕ} {t : ℝ} {σ : ℝ} {c : Point}
    (hc : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ c) :
    lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t ∈ closure (connectedComponentIn P.boundaryᶜ c) := by
  have hcont : Continuous fun δ : ℝ => offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) :=
    (continuous_offset _ _ t).comp (continuous_const.mul continuous_id)
  have ht : Tendsto (fun δ : ℝ => offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ)) (𝓝[>] 0)
      (𝓝 (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t)) := by
    have := hcont.tendsto 0
    simp only [mul_zero, offset_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht hc

/-- Every boundary point is in the closure of the component containing the `σ`-sides of all
edges. -/
theorem boundary_subset_closure_component {P : Polygon} (hP : P.Simple) {σ : ℝ} {c : Point}
    (hc : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ connectedComponentIn P.boundaryᶜ c) :
    P.boundary ⊆ closure (connectedComponentIn P.boundaryᶜ c) := by
  intro q hq
  by_cases hv : ∃ j, j < P.n ∧ q = P.vtx j
  · obtain ⟨j, hj, rfl⟩ := hv
    have hw : P.vtx j ≠ P.vtx ((j + 1) % P.n) := simple_vtx_succ_ne hP hj
    rw [← closure_closure]
    refine mem_closure_of_tendsto (tendsto_lerp_zero (P.vtx j) (P.vtx ((j + 1) % P.n))) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    exact openEdge_mem_closure_component P (hc j hj s hs)
  · push Not at hv
    obtain ⟨i, hi, t, ht, rfl⟩ := exists_openEdge_of_mem_boundary P hq hv
    exact openEdge_mem_closure_component P (hc i hi t ht)

/-- **The boundary is in the closure of the exterior.** -/
theorem boundary_subset_closure_compl {P : Polygon} (hP : P.Simple) :
    P.boundary ⊆ closure P.filledᶜ := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  have hL : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (1 * δ) ∈ connectedComponentIn P.boundaryᶜ cL := by
    intro i hi t ht
    filter_upwards [hsides i hi t ht] with δ hδ
    rw [one_mul]; exact hδ.1
  have hR : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t ((-1) * δ) ∈
        connectedComponentIn P.boundaryᶜ cR := by
    intro i hi t ht
    filter_upwards [hsides i hi t ht] with δ hδ
    rw [neg_one_mul]; exact hδ.2
  cases hpL : parity P cL
  · have hcL' : cL ∈ P.filledᶜ := by rw [filled_compl_eq hP]; exact ⟨hcL, hpL⟩
    rw [filled_compl_eq_component hP hcL']
    exact boundary_subset_closure_component hP hL
  · have hpR : parity P cR = false := by
      cases h : parity P cR
      · rfl
      · exact absurd (hpL.trans h.symm) hne
    have hcR' : cR ∈ P.filledᶜ := by rw [filled_compl_eq hP]; exact ⟨hcR, hpR⟩
    rw [filled_compl_eq_component hP hcR']
    exact boundary_subset_closure_component hP hR

/-- **The boundary is in the closure of the interior region.** -/
theorem boundary_subset_closure_interior {P : Polygon} (hP : P.Simple) :
    P.boundary ⊆ closure (P.filled \ P.boundary) := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  have hL : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (1 * δ) ∈ connectedComponentIn P.boundaryᶜ cL := by
    intro i hi t ht
    filter_upwards [hsides i hi t ht] with δ hδ
    rw [one_mul]; exact hδ.1
  have hR : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t ((-1) * δ) ∈
        connectedComponentIn P.boundaryᶜ cR := by
    intro i hi t ht
    filter_upwards [hsides i hi t ht] with δ hδ
    rw [neg_one_mul]; exact hδ.2
  cases hpL : parity P cL
  · have hpR : parity P cR = true := by
      cases h : parity P cR
      · exact absurd (hpL.trans h.symm) hne
      · rfl
    have hcR' : cR ∈ P.filled \ P.boundary := by
      rw [filled_sdiff_boundary_eq hP]; exact ⟨hcR, hpR⟩
    rw [filled_sdiff_boundary_eq_component hP hcR']
    exact boundary_subset_closure_component hP hR
  · have hcL' : cL ∈ P.filled \ P.boundary := by
      rw [filled_sdiff_boundary_eq hP]; exact ⟨hcL, hpL⟩
    rw [filled_sdiff_boundary_eq_component hP hcL']
    exact boundary_subset_closure_component hP hL

/-- **The interior of the filled region is the filled region minus the boundary.** -/
theorem interior_filled {P : Polygon} (hP : P.Simple) :
    interior P.filled = P.filled \ P.boundary := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨interior_subset hx, fun hxb => ?_⟩
    have h1 : x ∈ closure P.filledᶜ := boundary_subset_closure_compl hP hxb
    rw [closure_compl] at h1
    exact h1 hx
  · exact interior_maximal sdiff_subset (isOpen_filled_sdiff_boundary hP)

/-! ### The two sides of an edge -/

/-- The point of edge `i` at parameter `t` pushed by `δ` to the left. -/
def leftPoint (P : Polygon) (i : ℕ) (t δ : ℝ) : Point :=
  offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t δ

/-- The point of edge `i` at parameter `t` pushed by `δ` to the right. -/
def rightPoint (P : Polygon) (i : ℕ) (t δ : ℝ) : Point :=
  offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (-δ)

/-- **Exactly one side of every edge is filled**: for `t ∈ (0,1)` and all small `δ > 0`, the
left point is in the filled region iff the right point is not. -/
theorem edge_sides {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (leftPoint P i t δ ∈ P.filled ↔ rightPoint P i t δ ∉ P.filled) := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  filter_upwards [hsides i hi t ht] with δ hδ
  obtain ⟨h1, h2⟩ := hδ
  unfold leftPoint rightPoint
  have h1b := connectedComponentIn_subset _ _ h1
  have h2b := connectedComponentIn_subset _ _ h2
  rw [mem_filled_iff hP h1b, mem_filled_iff hP h2b,
    parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2]
  revert hne
  generalize parity P cL = bL
  generalize parity P cR = bR
  cases bL <;> cases bR <;> simp

end

end ArtGallery.Jordan
