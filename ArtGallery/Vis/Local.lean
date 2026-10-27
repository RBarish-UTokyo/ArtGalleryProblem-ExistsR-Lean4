module

public import ArtGallery.Vis.Region

/-!
# Visibility library: the region near a boundary point

* `LeftInterior P`: the interior lies to the left of every edge (the hypothesis
  `Polygon.InteriorLeft` of the interface `ArtGallery.Vis.API`, stated with `Jordan.nrm`, which is
  definitionally the interface's `leftNormal`).
* `local_halfplane_sign`: near a point of an open edge of a simple polygon the region is one of the
  two closed half-planes of the edge (no orientation assumption); `local_halfplane`: under
  `LeftInterior` it is the left one.
* `local_wedge`: under `LeftInterior`, near a vertex the region is the closed wedge to the left of
  both incident edges at a convex corner, the closed union of the two left half-planes at a reflex
  corner, and the closed left half-plane at a straight corner.

The proofs only use that a preconnected set avoiding the boundary is entirely interior or entirely
exterior (`ArtGallery.Vis.subset_interior_of_preconnected`), the strip lemma `Jordan.strip`, the
side lemma `Jordan.edge_sides` and the description of the boundary near a vertex
`Existence.boundary_near_vtx`.
-/

namespace ArtGallery.Vis

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan
open ArtGallery.Geometry (lerp lerp_eq_add_smul det_lerp det_lerp_self lerp_mem_segment
  continuous_lerp)

/-! ### Offset points and the orientation hypothesis -/

/-- An offset point in vector form. -/
theorem offset_eq (u v : Point) (t δ : ℝ) : offset u v t δ = u + t • (v - u) + δ • nrm u v := by
  unfold offset
  rw [lerp_eq_add_smul]

/-- An offset point to the right, in vector form. -/
theorem offset_neg_eq (u v : Point) (t δ : ℝ) :
    offset u v t (-δ) = u + t • (v - u) - δ • nrm u v := by
  rw [offset_eq, neg_smul, ← sub_eq_add_neg]

/-- The interior lies to the left of every edge: for every point of an open edge, the points
pushed slightly along the left normal are interior points and those pushed slightly along the
right normal are outside the region.  (This is `Polygon.InteriorLeft` of the interface, with
`Jordan.nrm` in place of the definitionally equal `Polygon.leftNormal`.) -/
def LeftInterior (P : Polygon) : Prop :=
  ∀ i < P.n, ∀ t : ℝ, 0 < t → t < 1 → ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i) +
        δ • nrm (P.vtx i) (P.vtx ((i + 1) % P.n))) ∈ P.filled \ P.boundary ∧
    (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i) -
        δ • nrm (P.vtx i) (P.vtx ((i + 1) % P.n))) ∉ P.filled

/-- `LeftInterior` in terms of offset points and filters. -/
theorem LeftInterior.eventually {P : Polygon} (hL : LeftInterior P) {i : ℕ} (hi : i < P.n)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) s δ ∈ P.filled \ P.boundary ∧
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) s (-δ) ∉ P.filled := by
  obtain ⟨δ₀, hδ₀, h⟩ := hL i hi s hs0 hs1
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  rw [offset_neg_eq, offset_eq]
  exact h δ hδ.1 hδ.2

/-- Choosing a common small offset: if the base point lies in the open sets `W₁` and `W₂` and the
left offsets are eventually interior while the right ones are eventually exterior, some offset
`δ > 0` puts the left point in `W₁` and the region, and the right point in `W₂` outside it. -/
theorem exists_sides {P : Polygon} {v b : Point} {s : ℝ}
    (hside : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset v b s δ ∈ P.filled \ P.boundary ∧ offset v b s (-δ) ∉ P.filled)
    {W₁ W₂ : Set Point} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (h₁ : lerp v b s ∈ W₁)
    (h₂ : lerp v b s ∈ W₂) :
    ∃ δ > 0, (offset v b s δ ∈ W₁ ∧ offset v b s δ ∈ P.filled) ∧
      (offset v b s (-δ) ∈ W₂ ∧ offset v b s (-δ) ∉ P.filled) := by
  obtain ⟨δ, ⟨⟨hLR, hδ1⟩, hδ2⟩, hδ0⟩ := (((hside.and (eventually_offset_mem 1 hW₁ h₁)).and
    (eventually_offset_mem (-1) hW₂ h₂)).and self_mem_nhdsWithin).exists
  rw [one_mul] at hδ1
  rw [neg_one_mul] at hδ2
  exact ⟨δ, hδ0, ⟨hδ1, hLR.1.1⟩, ⟨hδ2, hLR.2⟩⟩

/-! ### Near a point of an open edge -/

/-- Near a point of a line, a set that is a closed half-plane up to the sign `σ`. -/
theorem halfplane_core {P : Polygon} {u v : Point} {t r : ℝ} (hr : 0 < r) (huv : u ≠ v)
    (hstrip : ∀ x ∈ ball (lerp u v t) r, (x ∈ P.boundary ↔ det u v x = 0))
    (hsides : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (offset u v t δ ∈ P.filled ↔ offset u v t (-δ) ∉ P.filled)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ z ∈ ball (lerp u v t) r, (z ∈ P.filled ↔ 0 ≤ σ * det u v z) := by
  have hsq := sqLen_pos huv
  have hconn : ∀ σ : ℝ, IsPreconnected (ball (lerp u v t) r ∩ {x | 0 < σ * det u v x}) :=
    fun σ => ((convex_ball _ r).inter (convex_det_pos u v σ)).isPreconnected
  have hoff : ∀ σ : ℝ, ball (lerp u v t) r ∩ {x | 0 < σ * det u v x} ⊆ P.boundaryᶜ :=
    fun σ => side_subset_compl P hstrip σ
  obtain ⟨δ, ⟨⟨hside, hL⟩, hR⟩, hδ0⟩ := (((hsides.and
    (eventually_offset_mem 1 isOpen_ball (mem_ball_self hr))).and
    (eventually_offset_mem (-1) isOpen_ball (mem_ball_self hr))).and self_mem_nhdsWithin).exists
  have hδ : (0 : ℝ) < δ := hδ0
  rw [one_mul] at hL
  rw [neg_one_mul] at hR
  have hLmem : offset u v t δ ∈ ball (lerp u v t) r ∩ {x | 0 < 1 * det u v x} := by
    refine ⟨hL, ?_⟩
    show 0 < 1 * det u v (offset u v t δ)
    rw [det_offset]
    nlinarith [mul_pos hδ hsq]
  have hRmem : offset u v t (-δ) ∈ ball (lerp u v t) r ∩ {x | 0 < (-1) * det u v x} := by
    refine ⟨hR, ?_⟩
    show 0 < (-1) * det u v (offset u v t (-δ))
    rw [det_offset]
    nlinarith [mul_pos hδ hsq]
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ball (lerp u v t) r ∩ {x | 0 < σ * det u v x} ⊆ P.filled →
      ball (lerp u v t) r ∩ {x | 0 < (-σ) * det u v x} ⊆ P.filledᶜ →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ z ∈ ball (lerp u v t) r, (z ∈ P.filled ↔ 0 ≤ σ * det u v z) := by
    intro σ hσ hin hout
    refine ⟨σ, hσ, fun z hz => ⟨fun hzf => ?_, fun hle => ?_⟩⟩
    · by_contra hlt
      have hlt' : σ * det u v z < 0 := not_le.1 hlt
      refine hout ⟨hz, ?_⟩ hzf
      show 0 < (-σ) * det u v z
      rw [neg_mul]
      linarith
    · rcases hle.lt_or_eq with hlt | heq
      · exact hin ⟨hz, hlt⟩
      · have hd : det u v z = 0 := by
          rcases hσ with rfl | rfl <;> linarith
        exact Or.inl ((hstrip z hz).2 hd)
  by_cases hLf : offset u v t δ ∈ P.filled
  · have hRf : offset u v t (-δ) ∉ P.filled := hside.1 hLf
    refine key 1 (Or.inl rfl) ?_ ?_
    · exact (subset_interior_of_preconnected P (hconn 1) (hoff 1) hLmem hLf).trans sdiff_subset
    · exact subset_compl_of_preconnected P (hconn (-1)) (hoff (-1)) hRmem hRf
  · have hRf : offset u v t (-δ) ∈ P.filled := by
      by_contra h
      exact hLf (hside.2 h)
    refine key (-1) (Or.inr rfl) ?_ ?_
    · exact (subset_interior_of_preconnected P (hconn (-1)) (hoff (-1)) hRmem hRf).trans
        sdiff_subset
    · rw [neg_neg]
      exact subset_compl_of_preconnected P (hconn 1) (hoff 1) hLmem hLf

/-- **Near a point of an open edge the region is a closed half-plane** (for some orientation
`σ = ±1` of the edge; no orientation assumption). -/
theorem local_halfplane_sign {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ r > 0,
      ∀ z ∈ ball (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t) r,
        (z ∈ P.filled ↔ 0 ≤ σ * det (P.vtx i) (P.vtx ((i + 1) % P.n)) z) := by
  obtain ⟨r, hr, hstrip⟩ := strip hP hi ⟨ht0, ht1⟩
  obtain ⟨σ, hσ, h⟩ := halfplane_core hr (simple_vtx_succ_ne hP hi) hstrip
    (edge_sides hP hi ⟨ht0, ht1⟩)
  exact ⟨σ, hσ, r, hr, h⟩

/-- **Local half-plane.** Under `LeftInterior`, near a point `y` of the open edge `i` the region
is the closed half-plane to the left of the edge. -/
theorem local_halfplane {P : Polygon} (hP : P.Simple) (hL : LeftInterior P) {i : ℕ}
    (hi : i < P.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r > 0, ∀ z : Point,
      dist z (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i)) < r →
        (z ∈ P.filled ↔ 0 ≤ det (P.vtx i) (P.vtx ((i + 1) % P.n)) z) := by
  obtain ⟨σ, hσ, r, hr, hloc⟩ := local_halfplane_sign hP hi ht0 ht1
  have hy : lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t =
      P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i) := lerp_eq_add_smul _ _ _
  rcases hσ with rfl | rfl
  · refine ⟨r, hr, fun z hz => ?_⟩
    have h := hloc z (by rw [mem_ball, hy]; exact hz)
    rwa [one_mul] at h
  · exfalso
    have hsq := sqLen_pos (simple_vtx_succ_ne hP hi)
    obtain ⟨δ, ⟨hin, hδb⟩, hδ0⟩ := (((hL.eventually hi ht0 ht1).and
      (eventually_offset_mem 1 isOpen_ball (mem_ball_self hr))).and self_mem_nhdsWithin).exists
    have hδ : (0 : ℝ) < δ := hδ0
    rw [one_mul] at hδb
    have h := (hloc _ hδb).1 hin.1.1
    rw [det_offset] at h
    nlinarith [mul_pos hδ hsq]

/-! ### Near a vertex -/

/-- The closed wedge condition at a corner with turn `D`, in terms of `A = det u v z` and
`B = det v w z`. -/
def condR (D A B : ℝ) : Prop :=
  if 0 < D then 0 ≤ A ∧ 0 ≤ B else if D < 0 then 0 ≤ A ∨ 0 ≤ B else 0 ≤ A

/-- The open wedge condition (strict version of `condR`). -/
def strictR (D A B : ℝ) : Prop :=
  if 0 < D then 0 < A ∧ 0 < B else if D < 0 then 0 < A ∨ 0 < B else 0 < A

/-- The negation of `condR`. -/
def outR (D A B : ℝ) : Prop :=
  if 0 < D then A < 0 ∨ B < 0 else if D < 0 then A < 0 ∧ B < 0 else A < 0

/-- The closed region near the corner `u v w`, as in the interface's `local_wedge`. -/
def wedgeCond (u v w z : Point) : Prop := condR (det u v w) (det u v z) (det v w z)

/-- The open region near the corner `u v w`. -/
def wedgeStrict (u v w z : Point) : Prop := strictR (det u v w) (det u v z) (det v w z)

/-- The open exterior near the corner `u v w`. -/
def wedgeOut (u v w z : Point) : Prop := outR (det u v w) (det u v z) (det v w z)

theorem not_condR_iff {D A B : ℝ} : ¬ condR D A B ↔ outR D A B := by
  unfold condR outR
  split_ifs <;> simp only [not_and_or, not_or, not_le]

theorem strictR_of_pos {D A B : ℝ} (h : 0 < D) : strictR D A B ↔ 0 < A ∧ 0 < B := by
  unfold strictR
  rw [ite_eq_left h]

theorem strictR_of_neg {D A B : ℝ} (h : D < 0) : strictR D A B ↔ 0 < A ∨ 0 < B := by
  unfold strictR
  rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]

theorem strictR_of_zero {D A B : ℝ} (h : D = 0) : strictR D A B ↔ 0 < A := by
  subst h
  unfold strictR
  rw [ite_eq_right (lt_irrefl (0 : ℝ)), ite_eq_right (lt_irrefl (0 : ℝ))]

theorem outR_of_pos {D A B : ℝ} (h : 0 < D) : outR D A B ↔ A < 0 ∨ B < 0 := by
  unfold outR
  rw [ite_eq_left h]

theorem outR_of_neg {D A B : ℝ} (h : D < 0) : outR D A B ↔ A < 0 ∧ B < 0 := by
  unfold outR
  rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]

theorem outR_of_zero {D A B : ℝ} (h : D = 0) : outR D A B ↔ A < 0 := by
  subst h
  unfold outR
  rw [ite_eq_right (lt_irrefl (0 : ℝ)), ite_eq_right (lt_irrefl (0 : ℝ))]

/-- Moving from a point of the closed wedge towards a point with both values positive enters the
open wedge. -/
theorem strictR_combo {D A B A' B' ε : ℝ} (h : condR D A B) (hA' : 0 < A') (hB' : 0 < B')
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    strictR D ((1 - ε) * A + ε * A') ((1 - ε) * B + ε * B') := by
  have h1 : 0 ≤ 1 - ε := by linarith
  unfold condR at h
  unfold strictR
  split_ifs at h ⊢ with hD hD'
  · exact ⟨by nlinarith [mul_nonneg h1 h.1, mul_pos hε0 hA'],
      by nlinarith [mul_nonneg h1 h.2, mul_pos hε0 hB']⟩
  · rcases h with h | h
    · exact Or.inl (by nlinarith [mul_nonneg h1 h, mul_pos hε0 hA'])
    · exact Or.inr (by nlinarith [mul_nonneg h1 h, mul_pos hε0 hB'])
  · nlinarith [mul_nonneg h1 h, mul_pos hε0 hA']

/-- Points of the incoming edge are neither in the open wedge nor in the open exterior. -/
theorem not_strictR_zero_left {D t : ℝ} (ht1 : t ≤ 1) :
    ¬ strictR D 0 ((1 - t) * D) ∧ ¬ outR D 0 ((1 - t) * D) := by
  have h1 : 0 ≤ 1 - t := by linarith
  unfold strictR outR
  split_ifs with hD hD'
  · exact ⟨fun h => lt_irrefl _ h.1,
      fun h => h.elim (lt_irrefl _) (fun h => by nlinarith [mul_nonneg h1 hD.le])⟩
  · exact ⟨fun h => h.elim (lt_irrefl _)
      (fun h => by nlinarith [mul_nonneg h1 (neg_nonneg.2 hD'.le)]), fun h => lt_irrefl _ h.1⟩
  · exact ⟨lt_irrefl _, lt_irrefl _⟩

/-- Points of the outgoing edge are neither in the open wedge nor in the open exterior. -/
theorem not_strictR_zero_right {D t : ℝ} (ht0 : 0 ≤ t) :
    ¬ strictR D (t * D) 0 ∧ ¬ outR D (t * D) 0 := by
  unfold strictR outR
  split_ifs with hD hD'
  · exact ⟨fun h => lt_irrefl _ h.2,
      fun h => h.elim (fun h => by nlinarith [mul_nonneg ht0 hD.le]) (lt_irrefl _)⟩
  · exact ⟨fun h => h.elim (fun h => by nlinarith [mul_nonneg ht0 (neg_nonneg.2 hD'.le)])
      (lt_irrefl _), fun h => lt_irrefl _ h.2⟩
  · have h0 : D = 0 := le_antisymm (not_lt.1 hD) (not_lt.1 hD')
    subst h0
    simp

/-- An open half-plane `{0 < det a b x}` is convex. -/
theorem convex_det_gt (a b : Point) : Convex ℝ {x : Point | 0 < det a b x} := by
  have h := convex_det_pos a b 1
  simp only [one_mul] at h
  exact h

/-- An open half-plane `{det a b x < 0}` is convex. -/
theorem convex_det_lt (a b : Point) : Convex ℝ {x : Point | det a b x < 0} := by
  have h := convex_det_pos a b (-1)
  simp only [neg_mul, one_mul, neg_pos] at h
  exact h

/-- Assembling the local description at a corner from its two sides. -/
theorem wedge_assemble {P : Polygon} {a v b : Point} {r : ℝ}
    (hLb : ball v r ∩ {x | wedgeStrict a v b x} ⊆ P.boundaryᶜ)
    (hRb : ball v r ∩ {x | wedgeOut a v b x} ⊆ P.boundaryᶜ)
    (hLc : IsPreconnected (ball v r ∩ {x | wedgeStrict a v b x}))
    (hRc : IsPreconnected (ball v r ∩ {x | wedgeOut a v b x}))
    {ℓ ρ c : Point} (hℓ : ℓ ∈ ball v r ∩ {x | wedgeStrict a v b x}) (hℓf : ℓ ∈ P.filled)
    (hρ : ρ ∈ ball v r ∩ {x | wedgeOut a v b x}) (hρf : ρ ∉ P.filled)
    (hca : 0 < det a v c) (hcb : 0 < det v b c) :
    ∀ z ∈ ball v r, (z ∈ P.filled ↔ wedgeCond a v b z) := by
  have hLf : ball v r ∩ {x | wedgeStrict a v b x} ⊆ P.filled :=
    (subset_interior_of_preconnected P hLc hLb hℓ hℓf).trans sdiff_subset
  have hRf := subset_compl_of_preconnected P hRc hRb hρ hρf
  intro z hz
  constructor
  · intro hzf
    by_contra hcon
    exact hRf ⟨hz, not_condR_iff.1 hcon⟩ hzf
  · intro hcond
    have hcl : z ∈ closure (ball v r ∩ {x | wedgeStrict a v b x}) := by
      refine mem_closure_of_tendsto (tendsto_lerp_zero z c) ?_
      filter_upwards [(tendsto_lerp_zero z c).eventually (isOpen_ball.mem_nhds hz),
        Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hεb hε
      refine ⟨hεb, ?_⟩
      show strictR (det a v b) (det a v (lerp z c ε)) (det v b (lerp z c ε))
      rw [det_lerp, det_lerp]
      exact strictR_combo hcond hca hcb hε.1 hε.2.le
    exact closure_minimal hLf (Jordan.isClosed_filled P) hcl

/-- The local description at a corner `a → v → b`, given a ball in which the boundary lies on the
two incident edges, the direction condition at a straight corner, and the side behaviour of the
outgoing edge near `v`. -/
theorem wedge_core {P : Polygon} {a v b : Point} {r : ℝ} (hr : 0 < r)
    (hball : ∀ x ∈ ball v r, x ∈ P.boundary →
      x ∈ ArtGallery.segment a v ∨ x ∈ ArtGallery.segment v b)
    (hvb : v ≠ b) (hK : det a v b = 0 → 0 < det a v (a + nrm v b))
    (hside : ∀ s : ℝ, 0 < s → s < 1 → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset v b s δ ∈ P.filled \ P.boundary ∧ offset v b s (-δ) ∉ P.filled) :
    ∀ z ∈ ball v r, (z ∈ P.filled ↔ wedgeCond a v b z) := by
  have hsq := sqLen_pos hvb
  -- boundary points are neither in the open wedge nor in the open exterior
  have hbd : ∀ x ∈ ball v r, x ∈ P.boundary → ¬ wedgeStrict a v b x ∧ ¬ wedgeOut a v b x := by
    intro x hx hxb
    rcases hball x hx hxb with h | h
    · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 h
      have e1 : det a v (lerp a v t) = 0 := det_lerp_self a v t
      have e2 : det v b (lerp a v t) = (1 - t) * det a v b := by
        rw [det_lerp, Geometry.det_self_outer, Geometry.det_cyclic a v b]
        ring
      unfold wedgeStrict wedgeOut
      rw [e1, e2]
      exact not_strictR_zero_left ht1
    · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 h
      have e1 : det v b (lerp v b t) = 0 := det_lerp_self v b t
      have e2 : det a v (lerp v b t) = t * det a v b := by
        rw [det_lerp, Geometry.det_self_right]
        ring
      unfold wedgeStrict wedgeOut
      rw [e1, e2]
      exact not_strictR_zero_right ht0
  have hLb : ball v r ∩ {x | wedgeStrict a v b x} ⊆ P.boundaryᶜ :=
    fun x hx hxb => (hbd x hx.1 hxb).1 hx.2
  have hRb : ball v r ∩ {x | wedgeOut a v b x} ⊆ P.boundaryᶜ :=
    fun x hx hxb => (hbd x hx.1 hxb).2 hx.2
  -- a point on the reflex side of the corner, close to `v`
  obtain ⟨ε, hεb, hε0⟩ : ∃ ε : ℝ, v + ε • ((v - a) - (b - v)) ∈ ball v r ∧ 0 < ε := by
    have ht : Tendsto (fun ε : ℝ => v + ε • ((v - a) - (b - v))) (𝓝[>] 0) (𝓝 v) := by
      have hc : Continuous fun ε : ℝ => v + ε • ((v - a) - (b - v)) := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ((ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).and
      self_mem_nhdsWithin).exists
  obtain ⟨hd1, hd2⟩ := det_reflex_point a v b ε
  -- a point of the outgoing edge close to `v`
  obtain ⟨s, hsB, hs⟩ := (((tendsto_lerp_zero v b).eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr))).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have es : det a v (lerp v b s) = s * det a v b := by
    rw [det_lerp, Geometry.det_self_right]
    ring
  have hside' := hside s hs.1 hs.2
  have hW : IsOpen (ball v r) := isOpen_ball
  rcases lt_trichotomy (det a v b) 0 with hneg | hzero | hpos
  · -- reflex corner
    have hLset : {x | wedgeStrict a v b x} = {x | 0 < det a v x} ∪ {x | 0 < det v b x} := by
      ext x
      exact strictR_of_neg (A := det a v x) (B := det v b x) hneg
    have hRset : {x | wedgeOut a v b x} = {x | det a v x < 0} ∩ {x | det v b x < 0} := by
      ext x
      exact outR_of_neg (A := det a v x) (B := det v b x) hneg
    have hW₂ : IsOpen (ball v r ∩ {x | 0 < (-1) * det a v x}) :=
      isOpen_ball.inter (isOpen_det_pos a v (-1))
    have h₂ : lerp v b s ∈ ball v r ∩ {x | 0 < (-1) * det a v x} := by
      refine ⟨hsB, ?_⟩
      show 0 < (-1) * det a v (lerp v b s)
      rw [es]
      nlinarith [mul_pos hs.1 (neg_pos.2 hneg)]
    obtain ⟨δ, hδ, ⟨hℓB, hℓf⟩, ⟨hρW, hρf⟩⟩ := exists_sides hside' hW hW₂ hsB h₂
    have hρa : 0 < (-1) * det a v (offset v b s (-δ)) := hρW.2
    refine wedge_assemble hLb hRb ?_ ?_ (ℓ := offset v b s δ) (ρ := offset v b s (-δ))
      (c := v + ε • ((v - a) - (b - v))) ?_ hℓf ?_ hρf ?_ ?_
    · rw [hLset, inter_union_distrib_left]
      refine IsPreconnected.union (v + ε • ((v - a) - (b - v))) ⟨hεb, ?_⟩ ⟨hεb, ?_⟩
        ((convex_ball v r).inter (convex_det_gt a v)).isPreconnected
        ((convex_ball v r).inter (convex_det_gt v b)).isPreconnected
      · show 0 < det a v (v + ε • ((v - a) - (b - v)))
        rw [hd1]
        nlinarith [mul_pos hε0 (neg_pos.2 hneg)]
      · show 0 < det v b (v + ε • ((v - a) - (b - v)))
        rw [hd2]
        nlinarith [mul_pos hε0 (neg_pos.2 hneg)]
    · rw [hRset]
      exact ((convex_ball v r).inter ((convex_det_lt a v).inter (convex_det_lt v b))).isPreconnected
    · refine ⟨hℓB, ?_⟩
      show strictR (det a v b) (det a v (offset v b s δ)) (det v b (offset v b s δ))
      rw [strictR_of_neg hneg, det_offset]
      exact Or.inr (mul_pos hδ hsq)
    · refine ⟨hρW.1, ?_⟩
      show outR (det a v b) (det a v (offset v b s (-δ))) (det v b (offset v b s (-δ)))
      rw [outR_of_neg hneg, det_offset]
      exact ⟨by linarith, by nlinarith [mul_pos hδ hsq]⟩
    · rw [hd1]
      nlinarith [mul_pos hε0 (neg_pos.2 hneg)]
    · rw [hd2]
      nlinarith [mul_pos hε0 (neg_pos.2 hneg)]
  · -- straight corner
    have hKpos := hK hzero
    have hLset : {x | wedgeStrict a v b x} = {x | 0 < det a v x} := by
      ext x
      exact strictR_of_zero (A := det a v x) (B := det v b x) hzero
    have hRset : {x | wedgeOut a v b x} = {x | det a v x < 0} := by
      ext x
      exact outR_of_zero (A := det a v x) (B := det v b x) hzero
    obtain ⟨δ, hδ, ⟨hℓB, hℓf⟩, ⟨hρB, hρf⟩⟩ := exists_sides hside' hW hW hsB hsB
    have hℓa : det a v (offset v b s δ) = δ * det a v (a + nrm v b) := by
      rw [det_offset_gen, es, hzero]
      ring
    have hρa : det a v (offset v b s (-δ)) = -δ * det a v (a + nrm v b) := by
      rw [det_offset_gen, es, hzero]
      ring
    refine wedge_assemble hLb hRb ?_ ?_ (ℓ := offset v b s δ) (ρ := offset v b s (-δ))
      (c := offset v b s δ) ?_ hℓf ?_ hρf ?_ ?_
    · rw [hLset]
      exact ((convex_ball v r).inter (convex_det_gt a v)).isPreconnected
    · rw [hRset]
      exact ((convex_ball v r).inter (convex_det_lt a v)).isPreconnected
    · refine ⟨hℓB, ?_⟩
      show strictR (det a v b) (det a v (offset v b s δ)) (det v b (offset v b s δ))
      rw [strictR_of_zero hzero, hℓa]
      exact mul_pos hδ hKpos
    · refine ⟨hρB, ?_⟩
      show outR (det a v b) (det a v (offset v b s (-δ))) (det v b (offset v b s (-δ)))
      rw [outR_of_zero hzero, hρa]
      nlinarith [mul_pos hδ hKpos]
    · rw [hℓa]
      exact mul_pos hδ hKpos
    · rw [det_offset]
      exact mul_pos hδ hsq
  · -- convex corner
    have hLset : {x | wedgeStrict a v b x} = {x | 0 < det a v x} ∩ {x | 0 < det v b x} := by
      ext x
      exact strictR_of_pos (A := det a v x) (B := det v b x) hpos
    have hRset : {x | wedgeOut a v b x} = {x | det a v x < 0} ∪ {x | det v b x < 0} := by
      ext x
      exact outR_of_pos (A := det a v x) (B := det v b x) hpos
    have hW₁ : IsOpen (ball v r ∩ {x | 0 < 1 * det a v x}) :=
      isOpen_ball.inter (isOpen_det_pos a v 1)
    have h₁ : lerp v b s ∈ ball v r ∩ {x | 0 < 1 * det a v x} := by
      refine ⟨hsB, ?_⟩
      show 0 < 1 * det a v (lerp v b s)
      rw [es]
      nlinarith [mul_pos hs.1 hpos]
    obtain ⟨δ, hδ, ⟨hℓW, hℓf⟩, ⟨hρB, hρf⟩⟩ := exists_sides hside' hW₁ hW h₁ hsB
    have hℓa : 0 < det a v (offset v b s δ) := by
      have h' : 0 < 1 * det a v (offset v b s δ) := hℓW.2
      rwa [one_mul] at h'
    refine wedge_assemble hLb hRb ?_ ?_ (ℓ := offset v b s δ) (ρ := offset v b s (-δ))
      (c := offset v b s δ) ?_ hℓf ?_ hρf hℓa ?_
    · rw [hLset]
      exact ((convex_ball v r).inter ((convex_det_gt a v).inter (convex_det_gt v b))).isPreconnected
    · rw [hRset, inter_union_distrib_left]
      refine IsPreconnected.union (v + ε • ((v - a) - (b - v))) ⟨hεb, ?_⟩ ⟨hεb, ?_⟩
        ((convex_ball v r).inter (convex_det_lt a v)).isPreconnected
        ((convex_ball v r).inter (convex_det_lt v b)).isPreconnected
      · show det a v (v + ε • ((v - a) - (b - v))) < 0
        rw [hd1]
        nlinarith [mul_pos hε0 hpos]
      · show det v b (v + ε • ((v - a) - (b - v))) < 0
        rw [hd2]
        nlinarith [mul_pos hε0 hpos]
    · refine ⟨hℓW.1, ?_⟩
      show strictR (det a v b) (det a v (offset v b s δ)) (det v b (offset v b s δ))
      rw [strictR_of_pos hpos, det_offset]
      exact ⟨hℓa, mul_pos hδ hsq⟩
    · refine ⟨hρB, ?_⟩
      show outR (det a v b) (det a v (offset v b s (-δ))) (det v b (offset v b s (-δ)))
      rw [outR_of_pos hpos, det_offset]
      exact Or.inr (by nlinarith [mul_pos hδ hsq])
    · rw [det_offset]
      exact mul_pos hδ hsq

/-- At a vertex of a simple polygon the two incident edges meet only in the vertex. -/
theorem corner_meet {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) :
    ArtGallery.segment (P.vtx (prevIdx P i)) (P.vtx i) ∩
      ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) ⊆ {P.vtx i} := by
  have hn := simple_three_le hP
  have hjn : prevIdx P i < P.n := prevIdx_lt P hi
  have hji : prevIdx P i ≠ i := prevIdx_ne P hn hi
  have hjs : prevIdx P i ≠ (i + 1) % P.n := prevIdx_ne_succIdx P hn hi
  have hsucc : (prevIdx P i + 1) % P.n = i := prevIdx_succ P hi
  have hab : P.vtx (prevIdx P i) ≠ P.vtx ((i + 1) % P.n) :=
    simple_vtx_ne hP hjn (succIdx_lt P hi) hjs
  intro p hp
  have hmem : p ∈ P.edge (prevIdx P i) ∩ P.edge i := by
    rw [edge_prevIdx P hi]
    exact hp
  rw [simple_edge_inter hP hjn hi hji] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [hsucc] at h1
  rcases h1 with rfl | rfl
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd h2 hab
  · exact Set.mem_singleton _

/-- The value of `det a v` at `a` plus the left normal of `v → b` is the scalar product of
`v - a` and `b - v`. -/
theorem det_add_nrm (a v b : Point) :
    det a v (a + nrm v b) = (v.1 - a.1) * (b.1 - v.1) + (v.2 - a.2) * (b.2 - v.2) := by
  unfold det nrm
  simp
  ring

/-- **Local wedge.** Under `LeftInterior`, near vertex `i` (with predecessor `u` and successor
`w`) the region is the closed wedge to the left of both edges at a convex corner
(`det u v w > 0`), the closed union of the two left half-planes at a reflex corner
(`det u v w < 0`), and the closed left half-plane at a straight corner. -/
theorem local_wedge {P : Polygon} (hP : P.Simple) (hL : LeftInterior P) {i : ℕ}
    (hi : i < P.n) :
    ∃ r > 0, ∀ z : Point, dist z (P.vtx i) < r →
      (z ∈ P.filled ↔ wedgeCond (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) z) := by
  have hn := simple_three_le hP
  obtain ⟨r, hr, hball⟩ := Existence.boundary_near_vtx hP hi
  have hvb : P.vtx i ≠ P.vtx ((i + 1) % P.n) := simple_vtx_succ_ne hP hi
  have hav : P.vtx (prevIdx P i) ≠ P.vtx i :=
    simple_vtx_ne hP (prevIdx_lt P hi) hi (prevIdx_ne P hn hi)
  have hK : det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) = 0 →
      0 < det (P.vtx (prevIdx P i)) (P.vtx i)
        (P.vtx (prevIdx P i) + nrm (P.vtx i) (P.vtx ((i + 1) % P.n))) := by
    intro h
    rw [det_add_nrm]
    exact dir_pos_of_collinear hav hvb (corner_meet hP hi) h
  exact ⟨r, hr, fun z hz =>
    wedge_core hr hball hvb hK (fun s hs0 hs1 => hL.eventually hi hs0 hs1) z hz⟩

end

end ArtGallery.Vis
