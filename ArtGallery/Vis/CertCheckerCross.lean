module

public import ArtGallery.Vis.CertCheckerTransfer
public import ArtGallery.Vis.API

/-!
# Kernel-checkable certificates: crossings and cones

* **Sign of a determinant on a convex hull** (`det_pos_on_hull`, …): the determinant is affine
  in each argument, so a strict or weak sign condition on the vertices of a finite point set
  holds on its convex hull; for the bilinear dependence on two points the condition on all pairs
  of vertices propagates to all pairs of points of the two hulls (`forall_hull_hull`).
* **Crossing certificates** (`crossB`, `crossCheck`): every segment from a point of
  `conv P₁` to a point of `conv Q₁` properly crosses the segment `a b` (vertex sign tests on
  `P₁`, `Q₁` and all pairs).  With `a b` an edge of a simple polygon, no such segment is
  contained in the region (`not_sees_of_crossCheck`, via the blocking lemma
  `Polygon.not_sees_of_proper_cross`); rational form `not_sees_ratScale_of_crossCheck`.
* **Cone certificates** (`convexCornerCheck`, `inConeCheck`, `outConeCheck`): a vertex is a
  convex corner (`det u v w > 0`, as in `Polygon.local_wedge`), a convex hull lies in the closed
  cone of the corner, or strictly outside one of its two half-planes.
-/

@[expose] public section

namespace ArtGallery.Vis.Cert

open ArtGallery.Geometry ArtGallery.Hardening.Invariance Set

/-! ### Signs of determinants on convex hulls -/

/-- The determinant is affine in its last argument. -/
theorem det_combo (u v x y : Point) {s t : ℝ} (hst : s + t = 1) :
    det u v (s • x + t • y) = s * det u v x + t * det u v y := by
  have : s = 1 - t := by linarith
  subst this
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem convex_det_pos (u v : Point) : Convex ℝ {x | 0 < det u v x} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [det_combo u v x y hst]
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst; subst hst; simpa using hy
  · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]

theorem convex_det_neg (u v : Point) : Convex ℝ {x | det u v x < 0} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [det_combo u v x y hst]
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst; subst hst; simpa using hy
  · nlinarith [mul_pos hs' (neg_pos.2 hx), mul_nonneg ht (neg_nonneg.2 hy.le)]

theorem convex_det_nonneg (u v : Point) : Convex ℝ {x | 0 ≤ det u v x} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [det_combo u v x y hst]
  positivity

theorem convex_det_nonpos (u v : Point) : Convex ℝ {x | det u v x ≤ 0} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [det_combo u v x y hst]
  nlinarith [mul_nonneg hs (neg_nonneg.2 hx), mul_nonneg ht (neg_nonneg.2 hy)]

theorem det_pos_on_hull {u v : Point} {S : Set Point} (h : ∀ x ∈ S, 0 < det u v x) :
    ∀ x ∈ convexHull ℝ S, 0 < det u v x :=
  fun _ hx => convexHull_min h (convex_det_pos u v) hx

theorem det_neg_on_hull {u v : Point} {S : Set Point} (h : ∀ x ∈ S, det u v x < 0) :
    ∀ x ∈ convexHull ℝ S, det u v x < 0 :=
  fun _ hx => convexHull_min h (convex_det_neg u v) hx

theorem det_nonneg_on_hull {u v : Point} {S : Set Point} (h : ∀ x ∈ S, 0 ≤ det u v x) :
    ∀ x ∈ convexHull ℝ S, 0 ≤ det u v x :=
  fun _ hx => convexHull_min h (convex_det_nonneg u v) hx

theorem det_nonpos_on_hull {u v : Point} {S : Set Point} (h : ∀ x ∈ S, det u v x ≤ 0) :
    ∀ x ∈ convexHull ℝ S, det u v x ≤ 0 :=
  fun _ hx => convexHull_min h (convex_det_nonpos u v) hx

/-- A relation that is convex in each argument and holds on all pairs of points of `S × T`
holds on all pairs of points of `conv S × conv T`. -/
theorem forall_hull_hull {S T : Set Point} {R : Point → Point → Prop}
    (h₁ : ∀ q, Convex ℝ {p | R p q}) (h₂ : ∀ p, Convex ℝ {q | R p q})
    (h : ∀ p ∈ S, ∀ q ∈ T, R p q) : ∀ p ∈ convexHull ℝ S, ∀ q ∈ convexHull ℝ T, R p q := by
  have step : ∀ q ∈ T, ∀ p ∈ convexHull ℝ S, R p q :=
    fun q hq p hp => convexHull_min (fun p hp => h p hp q hq) (h₁ q) hp
  exact fun p hp q hq => convexHull_min (fun q hq => step q hq p hp) (h₂ p) hq

/-- The pair relation `det p q a < 0 < det p q b` is convex in `p` and in `q`. -/
theorem convex_pair_left (a b q : Point) :
    Convex ℝ {p | det p q a < 0 ∧ 0 < det p q b} := by
  have e : {p | det p q a < 0 ∧ 0 < det p q b} = {p | det q a p < 0} ∩ {p | 0 < det q b p} := by
    ext p; simp only [mem_ofPred_eq, mem_inter_iff, ← det_cyclic p q a, ← det_cyclic p q b]
  rw [e]; exact (convex_det_neg q a).inter (convex_det_pos q b)

theorem convex_pair_right (a b p : Point) :
    Convex ℝ {q | det p q a < 0 ∧ 0 < det p q b} := by
  have e : {q | det p q a < 0 ∧ 0 < det p q b} = {q | det a p q < 0} ∩ {q | 0 < det b p q} := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, ← det_cyclic_right p q a, ← det_cyclic_right p q b]
  rw [e]; exact (convex_det_neg a p).inter (convex_det_pos b p)

/-! ### Crossing certificates -/

/-- Every segment from `conv P₁` to `conv Q₁` properly crosses the segment `a b`: `P₁` and `Q₁`
lie strictly on opposite sides of the line `a b`, and for all vertex pairs `(p, q)` the points
`a`, `b` lie strictly on opposite sides of the line `p q`, with the same orientation for all
pairs. -/
def crossB (a b : IPt) (P₁ Q₁ : List IPt) : Bool :=
  ((P₁.all fun p => ipos (idet a b p)) && (Q₁.all fun q => ineg (idet a b q)) ||
    (P₁.all fun p => ineg (idet a b p)) && (Q₁.all fun q => ipos (idet a b q))) &&
  ((P₁.all fun p => Q₁.all fun q => ineg (idet p q a) && ipos (idet p q b)) ||
    (P₁.all fun p => Q₁.all fun q => ipos (idet p q a) && ineg (idet p q b)))

/-- **Soundness of `crossB`**: proper crossing for all segments between the two hulls. -/
theorem crossB_sound {a b : IPt} {P₁ Q₁ : List IPt} (h : crossB a b P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      det (intPoint a) (intPoint b) p * det (intPoint a) (intPoint b) q < 0 ∧
        det p q (intPoint a) * det p q (intPoint b) < 0 := by
  simp only [crossB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, ipos_iff,
    ineg_iff] at h
  obtain ⟨hside, hpair⟩ := h
  have vtx : ∀ {l : List IPt} {f : IPt → Prop} (_ : ∀ z ∈ l, f z), ∀ x ∈ intSet l,
      ∃ z, f z ∧ intPoint z = x := by
    rintro l f hf x ⟨z, hz, rfl⟩; exact ⟨z, hf z hz, rfl⟩
  intro p hp q hq
  constructor
  · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := det_pos_on_hull (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := vtx h1 x hx; rw [det_intPoint]; exact_mod_cast hz) p hp
      have e2 := det_neg_on_hull (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := vtx h2 x hx; rw [det_intPoint]; exact_mod_cast hz) q hq
      exact mul_neg_of_pos_of_neg e1 e2
    · have e1 := det_neg_on_hull (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := vtx h1 x hx; rw [det_intPoint]; exact_mod_cast hz) p hp
      have e2 := det_pos_on_hull (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := vtx h2 x hx; rw [det_intPoint]; exact_mod_cast hz) q hq
      exact mul_neg_of_neg_of_pos e1 e2
  · rcases hpair with h | h
    · have := forall_hull_hull (R := fun p q => det p q (intPoint a) < 0 ∧ 0 < det p q (intPoint b))
        (convex_pair_left _ _) (convex_pair_right _ _) (by
          rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
          obtain ⟨e1, e2⟩ := h z hz w hw
          rw [det_intPoint, det_intPoint]
          exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩) p hp q hq
      exact mul_neg_of_neg_of_pos this.1 this.2
    · have := forall_hull_hull (R := fun p q => det p q (intPoint b) < 0 ∧ 0 < det p q (intPoint a))
        (convex_pair_left _ _) (convex_pair_right _ _) (by
          rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
          obtain ⟨e1, e2⟩ := h z hz w hw
          rw [det_intPoint, det_intPoint]
          exact ⟨by exact_mod_cast e2, by exact_mod_cast e1⟩) p hp q hq
      exact mul_neg_of_pos_of_neg this.2 this.1

/-- **Crossing certificate** for edge `i` of the integer polygon `V`: every segment from
`conv P₁` to `conv Q₁` properly crosses edge `i`. -/
def crossCheck (V : List IPt) (i : ℕ) (P₁ Q₁ : List IPt) : Bool :=
  Nat.blt i V.length && crossB (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0)) P₁ Q₁

/-- **Soundness of the crossing certificate**: no point of `conv P₁` sees a point of `conv Q₁`
in the simple polygon `V`. -/
theorem not_sees_of_crossCheck {V : List IPt} (hP : (Polygon.mk (V.map intPoint)).Simple)
    {i : ℕ} {P₁ Q₁ : List IPt} (h : crossCheck V i P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      ¬ (Polygon.mk (V.map intPoint)).Sees p q := by
  simp only [crossCheck, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hi, h⟩ := h
  intro p hp q hq
  obtain ⟨h1, h2⟩ := crossB_sound h p hp q hq
  refine Polygon.not_sees_of_proper_cross hP (i := i) (by rw [n_map_intPoint]; exact hi) ?_ ?_
  · rw [vtx_map_intPoint, n_map_intPoint, vtx_map_intPoint]; exact h1
  · rw [vtx_map_intPoint, n_map_intPoint, vtx_map_intPoint]; exact h2

/-- Some edge of the polygon is a crossing certificate for `P₁`, `Q₁` (search over all
edges). -/
def crossCheckSome (V : List IPt) (P₁ Q₁ : List IPt) : Bool :=
  (List.range V.length).any fun i => crossCheck V i P₁ Q₁

theorem not_sees_of_crossCheckSome {V : List IPt} (hP : (Polygon.mk (V.map intPoint)).Simple)
    {P₁ Q₁ : List IPt} (h : crossCheckSome V P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      ¬ (Polygon.mk (V.map intPoint)).Sees p q := by
  simp only [crossCheckSome, List.any_eq_true] at h
  obtain ⟨i, -, hi⟩ := h
  exact not_sees_of_crossCheck hP hi

/-- **Crossing certificate, rational form**: the polygon and the point sets are the integer
data scaled by `1 / D`. -/
theorem not_sees_ratScale_of_crossCheck {D : ℕ} (hD : 0 < D) {V : List IPt}
    (hP : (Polygon.mk ((ratScale D V).map ratPoint)).Simple) {i : ℕ} {P₁ Q₁ : List IPt}
    (h : crossCheck V i P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (ratSet (ratScale D P₁)), ∀ q ∈ convexHull ℝ (ratSet (ratScale D Q₁)),
      ¬ (Polygon.mk ((ratScale D V).map ratPoint)).Sees p q := by
  rw [mk_ratScale_eq D hD, simple_mapPoly_iff] at hP
  rw [ratSet_ratScale D hD, ratSet_ratScale D hD, ← image_convexHull_affine,
    ← image_convexHull_affine, mk_ratScale_eq D hD]
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  rw [sees_mapPoly_iff]
  exact not_sees_of_crossCheck hP h p hp q hq

/-! ### Cone certificates -/

/-- The corner at vertex `i` (predecessor `u`, vertex `v`, successor `w`) as integer points. -/
def corner (V : List IPt) (i : ℕ) : IPt × IPt × IPt :=
  (V.getD ((i + V.length - 1) % V.length) (0, 0), V.getD i (0, 0),
    V.getD ((i + 1) % V.length) (0, 0))

theorem corner_intPoint (V : List IPt) (i : ℕ) :
    intPoint (corner V i).1 =
        (Polygon.mk (V.map intPoint)).vtx ((i + (Polygon.mk (V.map intPoint)).n - 1) %
          (Polygon.mk (V.map intPoint)).n) ∧
      intPoint (corner V i).2.1 = (Polygon.mk (V.map intPoint)).vtx i ∧
      intPoint (corner V i).2.2 = (Polygon.mk (V.map intPoint)).vtx
        ((i + 1) % (Polygon.mk (V.map intPoint)).n) := by
  simp only [corner, vtx_map_intPoint, n_map_intPoint, and_self]

/-- Vertex `i` is a convex corner: `det u v w > 0`. -/
def convexCornerCheck (V : List IPt) (i : ℕ) : Bool :=
  Nat.blt i V.length && ipos (idet (corner V i).1 (corner V i).2.1 (corner V i).2.2)

/-- **Soundness of the convex-corner certificate** (in the notation of
`Polygon.local_wedge`). -/
theorem convex_corner_of_check {V : List IPt} {i : ℕ} (h : convexCornerCheck V i = true) :
    i < (Polygon.mk (V.map intPoint)).n ∧
      0 < det ((Polygon.mk (V.map intPoint)).vtx ((i + (Polygon.mk (V.map intPoint)).n - 1) %
          (Polygon.mk (V.map intPoint)).n))
        ((Polygon.mk (V.map intPoint)).vtx i)
        ((Polygon.mk (V.map intPoint)).vtx ((i + 1) % (Polygon.mk (V.map intPoint)).n)) := by
  simp only [convexCornerCheck, Bool.and_eq_true, Nat.blt_eq, ipos_iff] at h
  obtain ⟨c1, c2, c3⟩ := corner_intPoint V i
  refine ⟨by rw [n_map_intPoint]; exact h.1, ?_⟩
  rw [← c1, ← c2, ← c3, det_intPoint]; exact_mod_cast h.2

/-- All points of `S` lie in the closed cone of the corner `i`: `0 ≤ det u v x` and
`0 ≤ det v w x`. -/
def inConeCheck (V : List IPt) (i : ℕ) (S : List IPt) : Bool :=
  S.all fun p => inonneg (idet (corner V i).1 (corner V i).2.1 p) &&
    inonneg (idet (corner V i).2.1 (corner V i).2.2 p)

theorem inCone_of_check {V : List IPt} {i : ℕ} {S : List IPt} (h : inConeCheck V i S = true) :
    ∀ x ∈ convexHull ℝ (intSet S),
      0 ≤ det ((Polygon.mk (V.map intPoint)).vtx ((i + (Polygon.mk (V.map intPoint)).n - 1) %
          (Polygon.mk (V.map intPoint)).n)) ((Polygon.mk (V.map intPoint)).vtx i) x ∧
      0 ≤ det ((Polygon.mk (V.map intPoint)).vtx i)
        ((Polygon.mk (V.map intPoint)).vtx ((i + 1) % (Polygon.mk (V.map intPoint)).n)) x := by
  obtain ⟨c1, c2, c3⟩ := corner_intPoint V i
  rw [← c1, ← c2, ← c3]
  simp only [inConeCheck, List.all_eq_true, Bool.and_eq_true, inonneg_iff] at h
  intro x hx
  refine ⟨det_nonneg_on_hull (fun y hy => ?_) x hx, det_nonneg_on_hull (fun y hy => ?_) x hx⟩
  · obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast (h z hz).1
  · obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast (h z hz).2

/-- All points of `S` lie strictly outside one of the two closed half-planes of the corner
`i`. -/
def outConeCheck (V : List IPt) (i : ℕ) (S : List IPt) : Bool :=
  (S.all fun p => ineg (idet (corner V i).1 (corner V i).2.1 p)) ||
    (S.all fun p => ineg (idet (corner V i).2.1 (corner V i).2.2 p))

theorem outCone_of_check {V : List IPt} {i : ℕ} {S : List IPt} (h : outConeCheck V i S = true) :
    (∀ x ∈ convexHull ℝ (intSet S),
      det ((Polygon.mk (V.map intPoint)).vtx ((i + (Polygon.mk (V.map intPoint)).n - 1) %
          (Polygon.mk (V.map intPoint)).n)) ((Polygon.mk (V.map intPoint)).vtx i) x < 0) ∨
    (∀ x ∈ convexHull ℝ (intSet S),
      det ((Polygon.mk (V.map intPoint)).vtx i)
        ((Polygon.mk (V.map intPoint)).vtx ((i + 1) % (Polygon.mk (V.map intPoint)).n)) x < 0) := by
  obtain ⟨c1, c2, c3⟩ := corner_intPoint V i
  rw [← c1, ← c2, ← c3]
  simp only [outConeCheck, Bool.or_eq_true, List.all_eq_true, ineg_iff] at h
  rcases h with h | h
  · refine Or.inl (det_neg_on_hull fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast h z hz
  · refine Or.inr (det_neg_on_hull fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast h z hz

end ArtGallery.Vis.Cert

end
