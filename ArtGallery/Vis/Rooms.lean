module

public import ArtGallery.Vis.Cones

/-!
# Visibility library: rooms and doors (tool T4)

A *room* of a polygon `P` is a closed set `R` with a *door* `D`: near every point of `R` that is
off the door, the region of `P` lies in `R` (`IsRoom`).  The definition is relative to the region:
for the rooms of the construction (`R = K.filled` for a sub-polygon `K`), the walls of the room are
walls of `P` and lie on the topological frontier of `R` although they are not doors.

* **Room lemma** (`sees_crosses_door`): a segment of the region from a point of the room to a
  point outside it meets the door.  The frontier form (`isRoom_of_frontier`) converts the
  hypothesis `∀ y ∈ frontier R, y ∈ P.filled → y ∈ D` into `IsRoom`.
* **Cone–door corollary** (`sees_mem_room`, `sees_mem_room_of_segment`): a point seen from a
  convex vertex of a room whose cone misses the door lies in the room.
* **Sub-polygon rooms** (`isRoom_of_chain`): the region of a simple, counter-clockwise polygon `K`
  whose vertices are a contiguous chain `P.vtx a, …, P.vtx (a + m)` of `P` (indices mod `P.n`),
  closed by the chord from `P.vtx (a + m)` back to `P.vtx a`, is a room with that chord as door.
  The proof is local: near a point of the chain the regions of `P` and `K` coincide
  (`local_halfplane` / `local_wedge` for both polygons, which share the incident edges).
* **Orientation of a sub-polygon** (`interiorLeft_of_supporting_edge`): a simple polygon with all
  vertices weakly to the left of the line of one of its edges is counter-clockwise (for the pocket
  rooms: the door on `y = 1` traversed from right to left, all vertices below).
-/

@[expose] public section

namespace ArtGallery

namespace Polygon

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)
open ArtGallery.Jordan

variable {P : Polygon}

/-! ### Rooms and the room lemma -/

/-- `R` is a room of `P` with door `D`: `R` is closed, and every point of `R ∩ P.filled` off the
door has a neighbourhood whose points of the region all lie in `R`. -/
def IsRoom (P : Polygon) (R D : Set Point) : Prop :=
  IsClosed R ∧ ∀ y ∈ R, y ∈ P.filled → y ∉ D → ∃ ε > 0, ∀ z ∈ P.filled, dist z y < ε → z ∈ R

/-- **Room lemma (T4).** If `t` is in the room `R`, `p` is not, and `t` sees `p`, then the
segment `t p` meets the door. -/
theorem sees_crosses_door {R D : Set Point} (hR : P.IsRoom R D) {t p : Point} (ht : t ∈ R)
    (hp : p ∉ R) (hs : P.Sees t p) : ∃ y ∈ D, y ∈ ArtGallery.segment t p := by
  by_contra hcon'
  have hcon : ∀ y ∈ D, y ∉ ArtGallery.segment t p := fun y hyD hy => hcon' ⟨y, hyD, hy⟩
  set S := ArtGallery.segment t p
  have hS : IsPreconnected S := by
    show IsPreconnected (ArtGallery.segment t p)
    rw [Geometry.segment_eq]
    exact (convex_segment t p).isPreconnected
  -- the points near which the region lies in `R`
  set U : Set Point := {x | ∃ ε > 0, ∀ z ∈ P.filled, dist z x < ε → z ∈ R}
  have hUo : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro x ⟨ε, hε, hx⟩
    refine ⟨ε / 2, half_pos hε, fun x' hx' => ⟨ε / 2, half_pos hε, fun z hz hzx => hx z hz ?_⟩⟩
    rw [mem_ball] at hx'
    calc dist z x ≤ dist z x' + dist x' x := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hzx hx'
      _ = ε := add_halves ε
  have hcover : S ⊆ U ∪ Rᶜ := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact Or.inl (hR.2 x hxR (hs hx) (fun hxD => hcon x hxD hx))
    · exact Or.inr hxR
  have htS : t ∈ S := Geometry.left_mem_segment t p
  have hpS : p ∈ S := by
    show p ∈ ArtGallery.segment t p
    rw [Geometry.segment_comm]
    exact Geometry.left_mem_segment p t
  obtain ⟨x, hxS, hxU, hxR⟩ := hS U Rᶜ hUo hR.1.isOpen_compl hcover
    ⟨t, htS, (hcover htS).resolve_right (not_not.2 ht)⟩ ⟨p, hpS, hp⟩
  obtain ⟨ε, hε, hx⟩ := hxU
  exact hxR (hx x (hs hxS) (by rw [dist_self]; exact hε))

/-- **Frontier form of the room hypothesis.** A closed set whose frontier points in the region
all lie on the door `D` is a room with door `D`. -/
theorem isRoom_of_frontier {R D : Set Point} (hRc : IsClosed R)
    (hfr : ∀ y ∈ frontier R, y ∈ P.filled → y ∈ D) : P.IsRoom R D := by
  refine ⟨hRc, fun y hy hyf hyD => ?_⟩
  have hint : y ∈ interior R := by
    by_contra h
    exact hyD (hfr y ⟨subset_closure hy, h⟩ hyf)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hint
  exact ⟨ε, hε, fun z _ hz => interior_subset (hball hz)⟩

/-- **Room lemma, frontier form** (as in `03_witness_tools.md`): for a closed set `R` with
`frontier R ∩ P.filled ⊆ D`, a segment of the region leaving `R` meets `D`. -/
theorem sees_crosses_door_of_frontier {R D : Set Point} (hRc : IsClosed R)
    (hfr : ∀ y ∈ frontier R, y ∈ P.filled → y ∈ D) {t p : Point} (ht : t ∈ R) (hp : p ∉ R)
    (hs : P.Sees t p) : ∃ y ∈ D, y ∈ ArtGallery.segment t p :=
  sees_crosses_door (isRoom_of_frontier hRc hfr) ht hp hs

/-! ### The cone–door corollary -/

/-- **Cone–door corollary.** If the convex vertex `v = P.vtx i` (predecessor `u`, successor `w`)
lies in the room `R` with door `D` and the cone at `v` misses the door, every point seen from `v`
lies in `R`. -/
theorem sees_mem_room (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {R D : Set Point}
    (hR : P.IsRoom R D) (hvR : v ∈ R) (hD : ∀ y ∈ D, y ∉ cornerCone u v w) {p : Point}
    (hs : P.Sees v p) : p ∈ R := by
  by_contra hp
  obtain ⟨y, hyD, hy⟩ := sees_crosses_door hR hvR hp hs
  exact hD y hyD (segment_subset_cone (sees_subset_cone hP hL hi hu hv hw hconv hs) hy)

/-- The cone–door corollary for the visibility set: `V(v) ⊆ R`. -/
theorem visSet_subset_room (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {R D : Set Point}
    (hR : P.IsRoom R D) (hvR : v ∈ R) (hD : ∀ y ∈ D, y ∉ cornerCone u v w) :
    P.visSet v ⊆ R :=
  fun _ hp => sees_mem_room hP hL hi hu hv hw hconv hR hvR hD hp.2

/-- The cone–door corollary for a segment door `a b`, with the door separated from the cone by
the line `c d` (`det c d` does not decrease from `v` along the cone generators and is strictly
smaller than at `v` at both door endpoints).  Taking `c d = v w` (resp. `u v`) the conditions
reduce to `det v w a < 0`, `det v w b < 0` (resp. with `u v`). -/
theorem sees_mem_room_of_segment (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {R : Set Point} {a b c d : Point}
    (hR : P.IsRoom R (ArtGallery.segment a b)) (hvR : v ∈ R)
    (hcu : det c d v ≤ det c d u) (hcw : det c d v ≤ det c d w) (hca : det c d a < det c d v)
    (hcb : det c d b < det c d v) {p : Point} (hs : P.Sees v p) : p ∈ R :=
  sees_mem_room hP hL hi hu hv hw hconv hR hvR (cone_disjoint_segment hconv hcu hcw hca hcb) hs

/-! ### Orientation from a supporting edge -/

/-- **Orientation from a supporting edge.** A simple polygon all of whose vertices lie weakly to
the left of the directed line of its edge `i` has its interior to the left of every edge. -/
theorem interiorLeft_of_supporting_edge {K : Polygon} (hK : K.Simple) {i : ℕ} (hi : i < K.n)
    (hsupp : ∀ j < K.n, 0 ≤ det (K.vtx i) (K.vtx ((i + 1) % K.n)) (K.vtx j)) :
    K.InteriorLeft := by
  set e₀ := K.vtx i
  set e₁ := K.vtx ((i + 1) % K.n)
  have hsq := sqLen_pos (simple_vtx_succ_ne hK hi)
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hK
  -- boundary points are weakly to the left of the line
  have hbd : ∀ x ∈ K.boundary, 0 ≤ det e₀ e₁ x := by
    rintro x ⟨j, hj, τ, hτ0, hτ1, rfl⟩
    have h1 := hsupp j hj
    have h2 := hsupp _ (succIdx_lt K hj)
    show 0 ≤ det e₀ e₁ (lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) τ)
    rw [det_lerp]
    nlinarith [mul_nonneg hτ0 h2, mul_nonneg (sub_nonneg.2 hτ1) h1]
  -- points strictly to the right are outside the region (a ray to the right avoids the boundary)
  have hright : ∀ x : Point, det e₀ e₁ x < 0 → x ∉ K.filled := by
    intro x hx
    have hxb : x ∉ K.boundary := fun h => by linarith [hbd x h]
    rw [mem_filled_iff_bounded K hxb]
    have hd : (-nrm e₀ e₁ : Point) ≠ 0 := by
      intro h0
      have : det e₀ e₁ (e₀ + -nrm e₀ e₁) = 0 := by rw [h0, add_zero, Geometry.det_self_outer]
      have e2 : det e₀ e₁ (e₀ + -nrm e₀ e₁) = -sqLen e₀ e₁ := by
        unfold det nrm sqLen; simp; ring
      linarith
    refine not_isBoundedSet_connectedComponentIn_of_ray K hd ?_
    rintro _ ⟨τ, hτ, rfl⟩ hp
    have h1 := hbd _ hp
    rw [Geometry.det_add_smul] at h1
    have e2 : det e₀ e₁ (e₀ + -nrm e₀ e₁) = -sqLen e₀ e₁ := by
      unfold det nrm sqLen; simp; ring
    rw [e2] at h1
    nlinarith [mul_nonneg (mem_Ici.1 hτ) hsq.le]
  -- the component of the right sides is exterior
  obtain ⟨δ, hδ, hδ0⟩ :=
    ((hsides i hi (1 / 2) ⟨by norm_num, by norm_num⟩).and self_mem_nhdsWithin).exists
  have hδ' : (0 : ℝ) < δ := hδ0
  have hRout : offset e₀ e₁ (1 / 2) (-δ) ∉ K.filled := by
    apply hright
    rw [det_offset]
    nlinarith [mul_pos hδ' hsq]
  have hcRout : cR ∉ K.filled := by
    have hsub := Vis.component_subset_compl K hRout
    rw [← connectedComponentIn_eq hδ.2] at hsub
    exact hsub (mem_connectedComponentIn hcR)
  -- the component of the left sides is interior
  have hcLin : cL ∈ K.filled \ K.boundary := by
    refine ⟨?_, hcL⟩
    rw [mem_filled_iff hK hcL]
    have hR : parity K cR = false := by
      rw [← Bool.not_eq_true, ← mem_filled_iff hK hcR]
      exact hcRout
    cases h : parity K cL
    · exact absurd (h.trans hR.symm) hne
    · rfl
  intro j hj t ht0 ht1
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hsides j hj t ⟨ht0, ht1⟩)
  refine ⟨δ₀, hδ₀, fun δ h0 h1 => ?_⟩
  obtain ⟨hl, hr⟩ := hsub ⟨h0, h1⟩
  have h1' := Vis.component_subset_interior K hcLin hl
  have h2' := Vis.component_subset_compl K hcRout hr
  rw [Vis.offset_eq] at h1'
  rw [Vis.offset_neg_eq] at h2'
  exact ⟨h1', h2'⟩

/-! ### Sub-polygon rooms -/

/-- Index bookkeeping for a chain: the successor of `(a + j) % n` is `(a + j + 1) % n`. -/
theorem chain_succ (n a j : ℕ) : ((a + j) % n + 1) % n = (a + (j + 1)) % n := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Index bookkeeping for a chain: the predecessor of `(a + j) % n` is `(a + (j - 1)) % n` for
`j ≥ 1`. -/
theorem chain_prev {Q : Polygon} (hn : 0 < Q.n) (a : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    prevIdx Q ((a + j) % Q.n) = (a + (j - 1)) % Q.n := by
  symm
  refine eq_prevIdx_of_succ Q (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_
  rw [chain_succ]
  congr 2
  omega

/-- Near an interior vertex of the chain the two regions coincide. -/
theorem chain_vertex_local {K : Polygon} (hP : P.Simple) (hL : P.InteriorLeft) (hK : K.Simple)
    (hKL : K.InteriorLeft) {a m : ℕ} (hKn : K.n = m + 1)
    (hchain : ∀ j ≤ m, K.vtx j = P.vtx ((a + j) % P.n)) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) :
    ∃ ε > 0, ∀ z : Point, dist z (K.vtx k) < ε → (z ∈ P.filled ↔ z ∈ K.filled) := by
  have hPn : 0 < P.n := by have := hP.1; omega
  have hkK : k < K.n := by omega
  obtain ⟨r₁, hr₁, h₁⟩ := Vis.local_wedge hK hKL hkK
  obtain ⟨r₂, hr₂, h₂⟩ := Vis.local_wedge hP hL (Nat.mod_lt (a + k) hPn)
  have eprevK : prevIdx K k = k - 1 := by
    rw [prevIdx_eq K hkK, ite_eq_right (by omega)]
  have esuccK : (k + 1) % K.n = k + 1 := Nat.mod_eq_of_lt (by omega)
  rw [eprevK, esuccK] at h₁
  rw [chain_prev hPn a hk1, chain_succ, ← hchain k hkm.le, ← hchain (k - 1) (by omega),
    ← hchain (k + 1) (by omega)] at h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [h₂ z (lt_of_lt_of_le hz (min_le_right _ _)), h₁ z (lt_of_lt_of_le hz (min_le_left _ _))]

/-- Near a point of an open edge of the chain the two regions coincide. -/
theorem chain_edge_local {K : Polygon} (hP : P.Simple) (hL : P.InteriorLeft) (hK : K.Simple)
    (hKL : K.InteriorLeft) {a m : ℕ} (hKn : K.n = m + 1)
    (hchain : ∀ j ≤ m, K.vtx j = P.vtx ((a + j) % P.n)) {j : ℕ} (hjm : j < m) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ε > 0, ∀ z : Point, dist z (lerp (K.vtx j) (K.vtx (j + 1)) t) < ε →
      (z ∈ P.filled ↔ z ∈ K.filled) := by
  have hPn : 0 < P.n := by have := hP.1; omega
  have hjK : j < K.n := by omega
  obtain ⟨r₁, hr₁, h₁⟩ := local_halfplane hK hKL hjK ht0 ht1
  obtain ⟨r₂, hr₂, h₂⟩ := local_halfplane hP hL (Nat.mod_lt (a + j) hPn) ht0 ht1
  have esuccK : (j + 1) % K.n = j + 1 := Nat.mod_eq_of_lt (by omega)
  rw [esuccK] at h₁
  rw [chain_succ, ← hchain j hjm.le, ← hchain (j + 1) (by omega)] at h₂
  rw [← Geometry.lerp_eq_add_smul] at h₁ h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [h₂ z (lt_of_lt_of_le hz (min_le_right _ _)), h₁ z (lt_of_lt_of_le hz (min_le_left _ _))]

/-- **Sub-polygon rooms.** Let `K` be a simple counter-clockwise polygon whose vertices are the
contiguous chain `P.vtx a, P.vtx (a+1), …, P.vtx (a+m)` of `P` (indices mod `P.n`), so that its
last edge is the chord from `K.vtx m = P.vtx (a+m)` back to `K.vtx 0 = P.vtx a`.  Then `K.filled`
is a room of `P` whose door is that chord.  More precisely, every point of `K.filled` off the
chord has a neighbourhood whose points of `P.filled` lie in `K.filled`. -/
theorem isRoom_of_chain {K : Polygon} (hP : P.Simple) (hL : P.InteriorLeft) (hK : K.Simple)
    (hKL : K.InteriorLeft) {a m : ℕ} (hKn : K.n = m + 1)
    (hchain : ∀ j ≤ m, K.vtx j = P.vtx ((a + j) % P.n)) :
    P.IsRoom K.filled (ArtGallery.segment (K.vtx m) (K.vtx 0)) := by
  refine ⟨isClosed_filled K, fun y hy _ hyD => ?_⟩
  have hK3 := hK.1
  -- local coincidence implies the room condition
  have fin : ∀ x : Point, (∃ ε > 0, ∀ z : Point, dist z x < ε → (z ∈ P.filled ↔ z ∈ K.filled)) →
      y = x → ∃ ε > 0, ∀ z ∈ P.filled, dist z y < ε → z ∈ K.filled := by
    rintro x ⟨ε, hε, h⟩ rfl
    exact ⟨ε, hε, fun z hz hzy => (h z hzy).1 hz⟩
  by_cases hyb : y ∈ K.boundary
  · obtain ⟨j, hjK, τ, hτ0, hτ1, hyj⟩ := hyb
    have hyl : y = lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) τ := hyj
    -- the door edge is excluded
    have hjm : j < m := by
      by_contra hjm
      have hj : j = m := by omega
      subst hj
      apply hyD
      rw [hKn, Nat.mod_self] at hyl
      rw [hyl]
      exact lerp_mem_segment _ _ hτ0 hτ1
    have esucc : (j + 1) % K.n = j + 1 := Nat.mod_eq_of_lt (by omega)
    rw [esucc] at hyl
    rcases hτ0.lt_or_eq with hτ0' | hτ0'
    · rcases hτ1.lt_or_eq with hτ1' | hτ1'
      · exact fin _ (chain_edge_local hP hL hK hKL hKn hchain hjm hτ0' hτ1') hyl
      · -- the end vertex of the edge
        rw [hτ1', Geometry.lerp_one] at hyl
        have hj1 : j + 1 ≠ m := by
          rintro h
          apply hyD
          rw [hyl, h]
          exact Geometry.left_mem_segment _ _
        exact fin _ (chain_vertex_local hP hL hK hKL hKn hchain (by omega) (by omega)) hyl
    · -- the start vertex of the edge
      rw [← hτ0', Geometry.lerp_zero] at hyl
      have hj0 : j ≠ 0 := by
        rintro rfl
        apply hyD
        rw [hyl, Geometry.segment_comm]
        exact Geometry.left_mem_segment _ _
      exact fin _ (chain_vertex_local hP hL hK hKL hKn hchain (by omega) hjm) hyl
  · -- an interior point of `K`
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_filled_sdiff_boundary hK) y ⟨hy, hyb⟩
    exact ⟨ε, hε, fun z _ hz => (hball hz).1⟩

/-- The vertices of the chain lie in the room `K.filled`. -/
theorem chain_vtx_mem_filled {K : Polygon} {a m : ℕ} (hKn : K.n = m + 1)
    (hchain : ∀ j ≤ m, K.vtx j = P.vtx ((a + j) % P.n)) {j : ℕ} (hj : j ≤ m) :
    P.vtx ((a + j) % P.n) ∈ K.filled := by
  rw [← hchain j hj]
  exact Or.inl ⟨j, by omega, Geometry.left_mem_segment _ _⟩

/-- **Sub-polygon rooms, local form.** Under the hypotheses of `isRoom_of_chain`, near every point
of `K.filled` off the chord the regions of `P` and `K` coincide. -/
theorem filled_iff_near_chain {K : Polygon} (hP : P.Simple) (hL : P.InteriorLeft)
    (hK : K.Simple) (hKL : K.InteriorLeft) {a m : ℕ} (hKn : K.n = m + 1)
    (hchain : ∀ j ≤ m, K.vtx j = P.vtx ((a + j) % P.n)) {y : Point} (hy : y ∈ K.boundary)
    (hyD : y ∉ ArtGallery.segment (K.vtx m) (K.vtx 0)) :
    ∃ ε > 0, ∀ z : Point, dist z y < ε → (z ∈ P.filled ↔ z ∈ K.filled) := by
  obtain ⟨j, hjK, τ, hτ0, hτ1, hyj⟩ := hy
  have hyl : y = lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) τ := hyj
  have hjm : j < m := by
    by_contra hjm
    have hj : j = m := by omega
    subst hj
    apply hyD
    rw [hKn, Nat.mod_self] at hyl
    rw [hyl]
    exact lerp_mem_segment _ _ hτ0 hτ1
  have esucc : (j + 1) % K.n = j + 1 := Nat.mod_eq_of_lt (by omega)
  rw [esucc] at hyl
  subst hyl
  rcases hτ0.lt_or_eq with hτ0' | hτ0'
  · rcases hτ1.lt_or_eq with hτ1' | hτ1'
    · exact chain_edge_local hP hL hK hKL hKn hchain hjm hτ0' hτ1'
    · rw [hτ1', Geometry.lerp_one] at hyD ⊢
      have hj1 : j + 1 ≠ m := by
        rintro h
        apply hyD
        rw [h]
        exact Geometry.left_mem_segment _ _
      exact chain_vertex_local hP hL hK hKL hKn hchain (by omega) (by omega)
  · rw [← hτ0', Geometry.lerp_zero] at hyD ⊢
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hyD
      rw [Geometry.segment_comm]
      exact Geometry.left_mem_segment _ _
    exact chain_vertex_local hP hL hK hKL hKn hchain (by omega) hjm

end Polygon

end ArtGallery

end
