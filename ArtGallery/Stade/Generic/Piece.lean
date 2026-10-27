module

public import ArtGallery.Vis.Rooms

/-!
# Convex pieces (proof plan L1.1)

A *piece* is a convex polygon `K` given by its vertex list in counter-clockwise order (collinear
consecutive vertices, i.e. subdivided sides, are allowed).  Its point set is
`piece K = {x | ∀ j < K.n, 0 ≤ det (K.vtx j) (K.vtx (j+1)) x}` (indices mod `K.n`), the points
weakly to the left of every directed side.  `IsPiece K` asks that every vertex lies in `piece K`
and that some point (`center`) is strictly to the left of every side.

Main facts:
* `piece K` is closed and convex, contains its vertices and sides (`edge_subset_piece`);
* **side location** (`mem_edge_of_det_eq_zero`): a point of `piece K` on the line of some side
  lies on some side `K.edge k` (this is where convex position and the center are used);
  consequently the frontier of `piece K` is covered by the sides (`mem_edge_of_mem_frontier`);
* **local structure**: near a point of an open side, `piece K` contains the half-plane of that
  side (`near_open_side`); near a vertex it contains the corner wedge (`near_vertex`); at a
  straight vertex the two side half-planes agree (`straight_side_nonneg`);
* interior points are strictly inside every side (`pos_of_mem_interior_piece`), and conversely
  (`mem_interior_piece_of_pos`);
* constructors for triangles and quadrilaterals (`isPiece_tri`, `isPiece_quad`).
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

/-! ### Definitions -/

/-- The closed convex set cut out by the side lines of `K`: the points weakly to the left of
every directed side `K.vtx j → K.vtx ((j+1) % K.n)`. -/
def piece (K : Polygon) : Set Point :=
  {x | ∀ j < K.n, 0 ≤ det (K.vtx j) (K.vtx ((j + 1) % K.n)) x}

/-- `K` is a convex piece: every vertex is weakly to the left of every side, and some point is
strictly to the left of every side. -/
structure IsPiece (K : Polygon) : Prop where
  /-- Convex position: every vertex lies weakly to the left of every side. -/
  vtx_mem : ∀ j < K.n, ∀ k < K.n, 0 ≤ det (K.vtx j) (K.vtx ((j + 1) % K.n)) (K.vtx k)
  /-- A point strictly to the left of every side. -/
  center : ∃ o : Point, ∀ j < K.n, 0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) o

variable {K : Polygon}

/-! ### Determinant identities -/

/-- `det` with two points on a line: `det a (lerp p q α) (lerp p q s) = (s − α) · det p q a`. -/
theorem det_lerp_lerp_right (a p q : Point) (α s : ℝ) :
    det a (lerp p q α) (lerp p q s) = (s - α) * det p q a := by
  unfold det lerp; simp only; ring

/-- `det (lerp p q α) (lerp p q β) z = (β − α) · det p q z`. -/
theorem det_lerp_lerp_left (p q z : Point) (α β : ℝ) :
    det (lerp p q α) (lerp p q β) z = (β - α) * det p q z := by
  unfold det lerp; simp only; ring

/-- The barycentric identity for the affine function `det a b ·` in the frame `p, q, o`. -/
theorem det_bary_affine (a b p q o z : Point) :
    det a b z * det p q o =
      det a b p * det z q o + det a b q * det p z o + det a b o * det p q z := by
  unfold det; ring

/-- `det q (lerp p q μ) z = (μ − 1) · det p q z`. -/
theorem det_right_lerp (p q z : Point) (μ : ℝ) :
    det q (lerp p q μ) z = (μ - 1) * det p q z := by
  unfold det lerp; simp only; ring

/-- `lerp` of two points of a line is a point of that line. -/
theorem lerp_lerp_lerp (p q : Point) (α β t : ℝ) :
    lerp (lerp p q α) (lerp p q β) t = lerp p q (α + t * (β - α)) := by
  ext <;> simp [lerp] <;> ring

/-- A point of a line between two other points of it lies on the segment joining them. -/
theorem lerp_mem_segment_of_between (p q : Point) {α β s : ℝ} (hαs : α ≤ s) (hsβ : s ≤ β)
    (hαβ : α < β) : lerp p q s ∈ ArtGallery.segment (lerp p q α) (lerp p q β) := by
  refine ⟨(s - α) / (β - α), div_nonneg (by linarith) (by linarith),
    (div_le_one (by linarith)).2 (by linarith), ?_⟩
  change lerp p q s = lerp (lerp p q α) (lerp p q β) ((s - α) / (β - α))
  rw [lerp_lerp_lerp]
  congr 1
  have : (s - α) / (β - α) * (β - α) = s - α := div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 hαβ))
  linarith

/-! ### Basic properties -/

/-- A piece is closed. -/
theorem isClosed_piece (K : Polygon) : IsClosed (piece K) := by
  have : piece K = ⋂ j ∈ Finset.range K.n,
      {x : Point | 0 ≤ det (K.vtx j) (K.vtx ((j + 1) % K.n)) x} := by
    ext x; simp [piece]
  rw [this]
  exact isClosed_biInter fun j _ =>
    isClosed_le continuous_const (Geometry.continuous_det_right _ _)

/-- A piece is convex. -/
theorem convex_piece (K : Polygon) : Convex ℝ (piece K) := by
  intro x hx y hy a b ha hb hab j hj
  have e : det (K.vtx j) (K.vtx ((j + 1) % K.n)) (a • x + b • y) =
      a * det (K.vtx j) (K.vtx ((j + 1) % K.n)) x +
        b * det (K.vtx j) (K.vtx ((j + 1) % K.n)) y := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    unfold det; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [e]
  exact add_nonneg (mul_nonneg ha (hx j hj)) (mul_nonneg hb (hy j hj))

/-- The vertices of a piece lie in the piece. -/
theorem vtx_mem_piece (hK : IsPiece K) {k : ℕ} (hk : k < K.n) : K.vtx k ∈ piece K :=
  fun j hj => hK.vtx_mem j hj k hk

/-- The successor index stays in range. -/
theorem succ_mod_lt {k : ℕ} (hk : k < K.n) : (k + 1) % K.n < K.n := Nat.mod_lt _ (by omega)

/-- The sides of a piece lie in the piece. -/
theorem edge_subset_piece (hK : IsPiece K) {j : ℕ} (hj : j < K.n) : K.edge j ⊆ piece K := by
  unfold Polygon.edge
  rw [Geometry.segment_eq]
  exact (convex_piece K).segment_subset (vtx_mem_piece hK hj) (vtx_mem_piece hK (succ_mod_lt hj))

/-- The two endpoints of a side are distinct. -/
theorem vtx_ne (hK : IsPiece K) {j : ℕ} (hj : j < K.n) : K.vtx j ≠ K.vtx ((j + 1) % K.n) := by
  obtain ⟨o, ho⟩ := hK.center
  intro h
  have := ho j hj
  rw [h, Geometry.det_self_left] at this
  exact lt_irrefl _ this

/-! ### Side location -/

/-- **Side location.** A point of a piece on the line of one of its sides lies on some side. -/
theorem mem_edge_of_det_eq_zero (hK : IsPiece K) {y : Point} (hy : y ∈ piece K) {j : ℕ}
    (hj : j < K.n) (hyj : det (K.vtx j) (K.vtx ((j + 1) % K.n)) y = 0) :
    ∃ k < K.n, y ∈ K.edge k := by
  classical
  set n := K.n with hn
  set p := K.vtx j with hp
  set q := K.vtx ((j + 1) % n) with hq
  have hpq : p ≠ q := vtx_ne hK hj
  obtain ⟨o, ho⟩ := hK.center
  have hpo : 0 < det p q o := ho j hj
  -- sides on the line `p q` point forward
  have fwd : ∀ k < n, ∀ α β : ℝ, K.vtx k = lerp p q α → K.vtx ((k + 1) % n) = lerp p q β →
      α < β := by
    intro k hk α β hα hβ
    have h1 := ho k hk
    rw [hα, hβ, det_lerp_lerp_left] at h1
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨s, rfl⟩ := Geometry.exists_lerp_of_det_eq_zero hpq hyj
  have hline : ∀ k, det p q (K.vtx k) = 0 → ∃ α, K.vtx k = lerp p q α :=
    fun k hk => Geometry.exists_lerp_of_det_eq_zero hpq hk
  choose! α hα using hline
  have hside : ∀ k < n, 0 ≤ det p q (K.vtx k) := fun k hk => hK.vtx_mem j hj k hk
  set W := (Finset.range n).filter (fun k => det p q (K.vtx k) = 0) with hW
  have hjW : j ∈ W := by
    rw [hW, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, Geometry.det_self_outer _ _⟩
  -- step 1: some vertex of the line is not beyond `y`
  set V := W.filter (fun k => α k ≤ s) with hV
  have hVne : V.Nonempty := by
    obtain ⟨k₀, hk₀W, hk₀min⟩ := W.exists_min_image α ⟨j, hjW⟩
    by_cases hk₀s : α k₀ ≤ s
    · exact ⟨k₀, Finset.mem_filter.2 ⟨hk₀W, hk₀s⟩⟩
    exfalso
    push Not at hk₀s
    rw [hW, Finset.mem_filter, Finset.mem_range] at hk₀W
    have hk₀n := hk₀W.1
    set k' := Jordan.prevIdx K k₀ with hk'
    have hk'n : k' < n := Jordan.prevIdx_lt K hk₀n
    have hk'succ : (k' + 1) % n = k₀ := Jordan.prevIdx_succ K hk₀n
    have h1 := hy k' hk'n
    rw [hk'succ, hα k₀ hk₀W.2, det_lerp_lerp_right] at h1
    have h2 := hside k' hk'n
    have h3 : det p q (K.vtx k') = 0 := by nlinarith
    have hk'W : k' ∈ W := by
      rw [hW, Finset.mem_filter, Finset.mem_range]; exact ⟨hk'n, h3⟩
    have h4 := hk₀min k' hk'W
    have h5 := fwd k' hk'n (α k') (α k₀) (hα k' h3) (by rw [hk'succ]; exact hα k₀ hk₀W.2)
    linarith
  -- step 2: the last such vertex starts the side containing `y`
  obtain ⟨k, hkV, hkmax⟩ := V.exists_max_image α hVne
  rw [hV, Finset.mem_filter, hW, Finset.mem_filter, Finset.mem_range] at hkV
  obtain ⟨⟨hkn, hkline⟩, hks⟩ := hkV
  have hk1n : (k + 1) % n < n := succ_mod_lt hkn
  have h1 := hy k hkn
  rw [hα k hkline, ← Geometry.det_cyclic, det_lerp_lerp_right] at h1
  -- h1 : 0 ≤ (α k - s) * det p q (K.vtx ((k+1) % n))
  rcases hks.lt_or_eq with hlt | heq
  · have h2 := hside _ hk1n
    have h3 : det p q (K.vtx ((k + 1) % n)) = 0 := by nlinarith
    have h4 := fwd k hkn (α k) (α ((k + 1) % n)) (hα k hkline) (hα _ h3)
    by_cases h5 : s ≤ α ((k + 1) % n)
    · refine ⟨k, hkn, ?_⟩
      unfold Polygon.edge
      rw [hα k hkline, hα _ h3]
      exact lerp_mem_segment_of_between p q hlt.le h5 h4
    · push Not at h5
      have hmem : (k + 1) % n ∈ V := by
        rw [hV, Finset.mem_filter, hW, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨hk1n, h3⟩, h5.le⟩
      have := hkmax _ hmem
      linarith
  · refine ⟨k, hkn, ?_⟩
    rw [← heq, ← hα k hkline]
    exact Geometry.left_mem_segment _ _

/-! ### Local structure -/

/-- Near a point of a piece, constraints that are strict at the point stay strict, so a point
satisfying the constraints active at `y` lies in the piece. -/
theorem near_mem_piece {y : Point} (hy : y ∈ piece K) :
    ∃ r > 0, ∀ z : Point, dist z y < r →
      (∀ k < K.n, det (K.vtx k) (K.vtx ((k + 1) % K.n)) y = 0 →
        0 ≤ det (K.vtx k) (K.vtx ((k + 1) % K.n)) z) → z ∈ piece K := by
  have hev : ∀ᶠ z in 𝓝 y, ∀ k ∈ Finset.range K.n,
      0 < det (K.vtx k) (K.vtx ((k + 1) % K.n)) y →
        0 < det (K.vtx k) (K.vtx ((k + 1) % K.n)) z := by
    rw [Finset.eventually_all]
    intro k _
    by_cases h : 0 < det (K.vtx k) (K.vtx ((k + 1) % K.n)) y
    · filter_upwards [(Geometry.continuous_det_right _ _).continuousAt.eventually
        (lt_mem_nhds h)] with z hz _ using hz
    · exact Eventually.of_forall fun z h' => absurd h' h
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r, hr, fun z hz hact k hk => ?_⟩
  rcases (hy k hk).lt_or_eq with h | h
  · exact (hball hz k (Finset.mem_range.2 hk) h).le
  · exact hact k hk h.symm

/-- **Open side.** Near a point of the open side `j`, the piece contains the half-plane of that
side. -/
theorem near_open_side (hK : IsPiece K) {j : ℕ} (hj : j < K.n) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    ∃ r > 0, ∀ z : Point, dist z (lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) t) < r →
      0 ≤ det (K.vtx j) (K.vtx ((j + 1) % K.n)) z → z ∈ piece K := by
  have hy : lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) t ∈ piece K :=
    edge_subset_piece hK hj (lerp_mem_segment _ _ ht0.le ht1.le)
  obtain ⟨r, hr, hnear⟩ := near_mem_piece hy
  obtain ⟨o, ho⟩ := hK.center
  refine ⟨r, hr, fun z hz hzj => hnear z hz fun k hk hact => ?_⟩
  rw [det_lerp] at hact
  have h1 := hK.vtx_mem k hk j hj
  have h2 := hK.vtx_mem k hk _ (succ_mod_lt hj)
  have e1 : det (K.vtx k) (K.vtx ((k + 1) % K.n)) (K.vtx j) = 0 := by nlinarith
  have e2 : det (K.vtx k) (K.vtx ((k + 1) % K.n)) (K.vtx ((j + 1) % K.n)) = 0 := by nlinarith
  have hb := det_bary_affine (K.vtx k) (K.vtx ((k + 1) % K.n)) (K.vtx j)
    (K.vtx ((j + 1) % K.n)) o z
  rw [e1, e2] at hb
  have hko := ho k hk
  have hjo := ho j hj
  have : 0 ≤ det (K.vtx k) (K.vtx ((k + 1) % K.n)) z * det (K.vtx j) (K.vtx ((j + 1) % K.n)) o := by
    rw [hb]; nlinarith
  exact (mul_nonneg_iff_of_pos_right hjo).1 this

/-- The predecessor side of vertex `a` ends at `a`. -/
theorem prev_succ {a : ℕ} (ha : a < K.n) : (Jordan.prevIdx K a + 1) % K.n = a :=
  Jordan.prevIdx_succ K ha

/-- **Straight vertex.** At a vertex where the two sides are collinear, the half-plane of the
outgoing side contains that of the incoming side. -/
theorem straight_side_nonneg (hK : IsPiece K) {a : ℕ} (ha : a < K.n)
    (hstr : det (K.vtx (Jordan.prevIdx K a)) (K.vtx a) (K.vtx ((a + 1) % K.n)) = 0) {z : Point}
    (hz : 0 ≤ det (K.vtx (Jordan.prevIdx K a)) (K.vtx a) z) :
    0 ≤ det (K.vtx a) (K.vtx ((a + 1) % K.n)) z := by
  have hpa := Jordan.prevIdx_lt K ha
  have hne : K.vtx (Jordan.prevIdx K a) ≠ K.vtx a := by
    have := vtx_ne hK hpa; rwa [prev_succ ha] at this
  obtain ⟨μ, hμ⟩ := Geometry.exists_lerp_of_det_eq_zero hne hstr
  obtain ⟨o, ho⟩ := hK.center
  have h1 := ho a ha
  have h2 := ho _ hpa
  rw [prev_succ ha] at h2
  rw [hμ, det_right_lerp] at h1 ⊢
  have hμ1 : 0 < μ - 1 := by
    by_contra h; push Not at h; nlinarith
  exact mul_nonneg hμ1.le hz

/-- **Vertex.** Near the vertex `a`, the piece contains the corner wedge (the points weakly left
of both sides at `a`). -/
theorem near_vertex (hK : IsPiece K) {a : ℕ} (ha : a < K.n) :
    ∃ r > 0, ∀ z : Point, dist z (K.vtx a) < r →
      0 ≤ det (K.vtx (Jordan.prevIdx K a)) (K.vtx a) z →
      0 ≤ det (K.vtx a) (K.vtx ((a + 1) % K.n)) z → z ∈ piece K := by
  obtain ⟨r, hr, hnear⟩ := near_mem_piece (vtx_mem_piece hK ha)
  obtain ⟨o, ho⟩ := hK.center
  set a' := Jordan.prevIdx K a with ha'
  have ha'n : a' < K.n := Jordan.prevIdx_lt K ha
  have ha's : (a' + 1) % K.n = a := prev_succ ha
  have ha1n := succ_mod_lt ha
  refine ⟨r, hr, fun z hz hz1 hz2 => hnear z hz fun k hk hact => ?_⟩
  have hD : 0 ≤ det (K.vtx a') (K.vtx a) (K.vtx ((a + 1) % K.n)) := by
    have := hK.vtx_mem a' ha'n _ ha1n; rwa [ha's] at this
  have hu := hK.vtx_mem k hk a' ha'n
  have hw := hK.vtx_mem k hk _ ha1n
  rcases hD.lt_or_eq with hD | hD
  · exact Polygon.det_nonneg_of_mem_cone hD ⟨hz1, hz2⟩ hact hu hw
  · -- straight vertex: the active constraint vanishes along the incoming side
    have hne : K.vtx a' ≠ K.vtx a := by
      have := vtx_ne hK ha'n; rwa [ha's] at this
    obtain ⟨μ, hμ⟩ := Geometry.exists_lerp_of_det_eq_zero hne hD.symm
    have h1 := ho a ha
    have h2 := ho a' ha'n
    rw [ha's] at h2
    rw [hμ, det_right_lerp] at h1
    have hμ1 : 0 < μ - 1 := by
      by_contra h; push Not at h; nlinarith
    rw [hμ, det_lerp] at hw
    rw [hact] at hw
    have e1 : det (K.vtx k) (K.vtx ((k + 1) % K.n)) (K.vtx a') = 0 := by nlinarith
    have hb := det_bary_affine (K.vtx k) (K.vtx ((k + 1) % K.n)) (K.vtx a') (K.vtx a) o z
    rw [e1, hact] at hb
    have hko := ho k hk
    have : 0 ≤ det (K.vtx k) (K.vtx ((k + 1) % K.n)) z * det (K.vtx a') (K.vtx a) o := by
      rw [hb]; nlinarith
    exact (mul_nonneg_iff_of_pos_right h2).1 this

/-! ### Interior -/

/-- An interior point of the closed half-plane `0 ≤ det c d ·` is strictly inside it. -/
theorem pos_of_mem_interior_halfplane {c d x : Point} (hcd : c ≠ d)
    (hx : x ∈ interior {z : Point | 0 ≤ det c d z}) : 0 < det c d x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set v : Point := (d.2 - c.2, -(d.1 - c.1)) with hv
  have hL : 0 < (d.1 - c.1) ^ 2 + (d.2 - c.2) ^ 2 := Jordan.sqLen_pos hcd
  set δ := ε / (2 * (‖v‖ + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  have hdist : dist (x + δ • v) x < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ0.le, hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hmem := interior_subset (hball (mem_ball.2 hdist))
  simp only [mem_ofPred_eq] at hmem
  rw [Geometry.det_add_smul] at hmem
  have e : det c d (c + v) = -((d.1 - c.1) ^ 2 + (d.2 - c.2) ^ 2) := by
    rw [hv]; unfold det; simp only [Prod.fst_add, Prod.snd_add]; ring
  rw [e] at hmem
  nlinarith

/-- Interior points of a piece are strictly to the left of every side. -/
theorem pos_of_mem_interior_piece (hK : IsPiece K) {x : Point} (hx : x ∈ interior (piece K))
    {j : ℕ} (hj : j < K.n) : 0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) x :=
  pos_of_mem_interior_halfplane (vtx_ne hK hj) (interior_mono
    (show piece K ⊆ {z : Point | 0 ≤ det (K.vtx j) (K.vtx ((j + 1) % K.n)) z} from
      fun _ hz => hz j hj) hx)

/-- Points strictly to the left of every side are interior points of the piece. -/
theorem mem_interior_piece_of_pos {x : Point}
    (hx : ∀ j < K.n, 0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) x) : x ∈ interior (piece K) := by
  rw [mem_interior_iff_mem_nhds]
  have hev : ∀ᶠ z in 𝓝 x, ∀ j ∈ Finset.range K.n,
      0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) z := by
    rw [Finset.eventually_all]
    intro j hj
    exact (Geometry.continuous_det_right _ _).continuousAt.eventually
      (lt_mem_nhds (hx j (Finset.mem_range.1 hj)))
  filter_upwards [hev] with z hz j hj using (hz j (Finset.mem_range.2 hj)).le

/-- The center of a piece is an interior point. -/
theorem center_mem_interior (hK : IsPiece K) : ∃ o, o ∈ interior (piece K) := by
  obtain ⟨o, ho⟩ := hK.center
  exact ⟨o, mem_interior_piece_of_pos ho⟩

/-- **Frontier.** Every frontier point of a piece lies on one of its sides. -/
theorem mem_edge_of_mem_frontier (hK : IsPiece K) {y : Point} (hy : y ∈ frontier (piece K)) :
    ∃ k < K.n, y ∈ K.edge k := by
  have hyK : y ∈ piece K := (isClosed_piece K).frontier_subset hy
  by_cases h : ∃ j < K.n, det (K.vtx j) (K.vtx ((j + 1) % K.n)) y = 0
  · obtain ⟨j, hj, hyj⟩ := h
    exact mem_edge_of_det_eq_zero hK hyK hj hyj
  · push Not at h
    exact absurd (mem_interior_piece_of_pos fun j hj => lt_of_le_of_ne (hyK j hj) (h j hj).symm)
      hy.2

/-- A segment whose endpoints are weakly to the right of a side line misses the interior of the
piece. -/
theorem disjoint_interior_of_side (hK : IsPiece K) {j : ℕ} (hj : j < K.n) {a b : Point}
    (ha : det (K.vtx j) (K.vtx ((j + 1) % K.n)) a ≤ 0)
    (hb : det (K.vtx j) (K.vtx ((j + 1) % K.n)) b ≤ 0) :
    Disjoint (interior (piece K)) (ArtGallery.segment a b) := by
  rw [Set.disjoint_left]
  intro x hx hxs
  have h1 := pos_of_mem_interior_piece hK hx hj
  obtain ⟨t, ht0, ht1, rfl⟩ := hxs
  change 0 < det _ _ (lerp a b t) at h1
  rw [det_lerp] at h1
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 hb), mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 ha)]

/-- A segment whose endpoints are weakly to the right of a line `c d` (with the piece weakly to
its left) misses the interior of the piece. -/
theorem disjoint_interior_of_halfplane {c d : Point} (hcd : c ≠ d)
    (hK : ∀ x ∈ piece K, 0 ≤ det c d x) {a b : Point} (ha : det c d a ≤ 0) (hb : det c d b ≤ 0) :
    Disjoint (interior (piece K)) (ArtGallery.segment a b) := by
  rw [Set.disjoint_left]
  intro x hx hxs
  have h1 := pos_of_mem_interior_halfplane hcd (interior_mono (fun z hz => hK z hz) hx)
  obtain ⟨t, ht0, ht1, rfl⟩ := hxs
  change 0 < det _ _ (lerp a b t) at h1
  rw [det_lerp] at h1
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 hb), mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 ha)]

/-! ### Triangles and quadrilaterals -/

/-- The triangle with vertices `a, b, c`. -/
def tri (a b c : Point) : Polygon := ⟨[a, b, c]⟩

/-- The quadrilateral with vertices `a, b, c, d`. -/
def quad (a b c d : Point) : Polygon := ⟨[a, b, c, d]⟩

/-- A triangle has three vertices. -/
theorem tri_n (a b c : Point) : (tri a b c).n = 3 := rfl
/-- A quadrilateral has four vertices. -/
theorem quad_n (a b c d : Point) : (quad a b c d).n = 4 := rfl
/-- Vertices of a triangle. -/
theorem tri_vtx_zero (a b c : Point) : (tri a b c).vtx 0 = a := rfl
/-- Vertices of a triangle. -/
theorem tri_vtx_one (a b c : Point) : (tri a b c).vtx 1 = b := rfl
/-- Vertices of a triangle. -/
theorem tri_vtx_two (a b c : Point) : (tri a b c).vtx 2 = c := rfl
/-- Vertices of a quadrilateral. -/
theorem quad_vtx_zero (a b c d : Point) : (quad a b c d).vtx 0 = a := rfl
/-- Vertices of a quadrilateral. -/
theorem quad_vtx_one (a b c d : Point) : (quad a b c d).vtx 1 = b := rfl
/-- Vertices of a quadrilateral. -/
theorem quad_vtx_two (a b c d : Point) : (quad a b c d).vtx 2 = c := rfl
/-- Vertices of a quadrilateral. -/
theorem quad_vtx_three (a b c d : Point) : (quad a b c d).vtx 3 = d := rfl

/-- The sides of a triangle. -/
theorem tri_edge (a b c : Point) :
    (tri a b c).edge 0 = ArtGallery.segment a b ∧ (tri a b c).edge 1 = ArtGallery.segment b c ∧
      (tri a b c).edge 2 = ArtGallery.segment c a :=
  ⟨rfl, rfl, by simp [Polygon.edge, tri, Polygon.vtx, Polygon.n]⟩

/-- The sides of a quadrilateral. -/
theorem quad_edge (a b c d : Point) :
    (quad a b c d).edge 0 = ArtGallery.segment a b ∧
      (quad a b c d).edge 1 = ArtGallery.segment b c ∧
      (quad a b c d).edge 2 = ArtGallery.segment c d ∧
      (quad a b c d).edge 3 = ArtGallery.segment d a :=
  ⟨rfl, rfl, rfl, by simp [Polygon.edge, quad, Polygon.vtx, Polygon.n]⟩

/-- Membership in a triangle piece. -/
theorem mem_piece_tri {a b c x : Point} :
    x ∈ piece (tri a b c) ↔ 0 ≤ det a b x ∧ 0 ≤ det b c x ∧ 0 ≤ det c a x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [tri, Polygon.vtx, Polygon.n] using h 0 (by simp [tri, Polygon.n])
    · simpa [tri, Polygon.vtx, Polygon.n] using h 1 (by simp [tri, Polygon.n])
    · simpa [tri, Polygon.vtx, Polygon.n] using h 2 (by simp [tri, Polygon.n])
  · rintro ⟨h0, h1, h2⟩ j hj
    simp only [tri, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simpa [tri, Polygon.vtx, Polygon.n]

/-- Membership in a quadrilateral piece. -/
theorem mem_piece_quad {a b c d x : Point} :
    x ∈ piece (quad a b c d) ↔
      0 ≤ det a b x ∧ 0 ≤ det b c x ∧ 0 ≤ det c d x ∧ 0 ≤ det d a x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [quad, Polygon.vtx, Polygon.n] using h 0 (by simp [quad, Polygon.n])
    · simpa [quad, Polygon.vtx, Polygon.n] using h 1 (by simp [quad, Polygon.n])
    · simpa [quad, Polygon.vtx, Polygon.n] using h 2 (by simp [quad, Polygon.n])
    · simpa [quad, Polygon.vtx, Polygon.n] using h 3 (by simp [quad, Polygon.n])
  · rintro ⟨h0, h1, h2, h3⟩ j hj
    simp only [quad, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simpa [quad, Polygon.vtx, Polygon.n]

/-- A counter-clockwise triangle is a piece. -/
theorem isPiece_tri {a b c : Point} (h : 0 < det a b c) : IsPiece (tri a b c) := by
  have h1 := Geometry.det_cyclic a b c
  have h2 := Geometry.det_cyclic_right a b c
  refine ⟨fun j hj k hk => ?_, ⟨((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3), fun j hj => ?_⟩⟩
  · simp only [tri, Polygon.n, List.length_cons, List.length_nil] at hj hk
    interval_cases j <;> interval_cases k <;>
      simp [tri, Polygon.vtx, Polygon.n] <;> linarith
  · simp only [tri, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [tri, Polygon.vtx, Polygon.n] <;> unfold det at h ⊢ <;>
      nlinarith

/-- A strictly convex counter-clockwise quadrilateral is a piece. -/
theorem isPiece_quad {a b c d : Point} (habc : 0 < det a b c) (hbcd : 0 < det b c d)
    (hcda : 0 < det c d a) (hdab : 0 < det d a b) : IsPiece (quad a b c d) := by
  have e1 := Geometry.det_cyclic a b c
  have e2 := Geometry.det_cyclic_right a b c
  have e3 := Geometry.det_cyclic b c d
  have e4 := Geometry.det_cyclic_right b c d
  have e5 := Geometry.det_cyclic c d a
  have e6 := Geometry.det_cyclic_right c d a
  have e7 := Geometry.det_cyclic d a b
  have e8 := Geometry.det_cyclic_right d a b
  refine ⟨fun j hj k hk => ?_, ⟨((a.1 + b.1 + c.1 + d.1) / 4, (a.2 + b.2 + c.2 + d.2) / 4),
    fun j hj => ?_⟩⟩
  · simp only [quad, Polygon.n, List.length_cons, List.length_nil] at hj hk
    interval_cases j <;> interval_cases k <;>
      simp [quad, Polygon.vtx, Polygon.n] <;> linarith
  · simp only [quad, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [quad, Polygon.vtx, Polygon.n] <;> unfold det at * <;>
      nlinarith

end ArtGallery.Stade

end
