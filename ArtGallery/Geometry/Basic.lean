module

public import ArtGallery.Geometry.SpecExtra
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Planar geometry: points, segments, bounded sets

The plane is `ArtGallery.Point = ℝ × ℝ` with Mathlib's product structure
(`Module ℝ`, `NormedAddCommGroup` with the sup norm, product topology).

This file relates the specification's elementary notions to Mathlib:

* `ArtGallery.segment a b` is Mathlib's `segment ℝ a b` (`segment_eq`), hence the
  convex hull of the pair (`segment_eq_convexHull_pair`), convex, closed, compact;
* `lerp a b t = a + t • (b - a)` parametrises the segment (`mem_segment_iff_lerp`);
* `ArtGallery.IsBoundedSet` is `Bornology.IsBounded` (`isBoundedSet_iff`), with the
  usual closure properties (subsets, finite unions, compact sets).

Inside `namespace ArtGallery` the bare name `segment` is `ArtGallery.segment`;
Mathlib's segment is always written `_root_.segment ℝ a b` here.

Provenance: adapted from `Chazelle/Geometry/Basic.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`; it imports `ArtGallery.Geometry.SpecExtra` instead of the specification.
-/

namespace ArtGallery

namespace Geometry

@[expose] public section

/-! ### Coordinates of vector operations -/

@[simp] theorem add_fst (a b : Point) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem add_snd (a b : Point) : (a + b).2 = a.2 + b.2 := rfl
@[simp] theorem sub_fst (a b : Point) : (a - b).1 = a.1 - b.1 := rfl
@[simp] theorem sub_snd (a b : Point) : (a - b).2 = a.2 - b.2 := rfl
@[simp] theorem neg_fst (a : Point) : (-a).1 = -a.1 := rfl
@[simp] theorem neg_snd (a : Point) : (-a).2 = -a.2 := rfl
@[simp] theorem smul_fst (t : ℝ) (a : Point) : (t • a).1 = t * a.1 := rfl
@[simp] theorem smul_snd (t : ℝ) (a : Point) : (t • a).2 = t * a.2 := rfl
@[simp] theorem zero_fst : ((0 : Point)).1 = 0 := rfl
@[simp] theorem zero_snd : ((0 : Point)).2 = 0 := rfl

/-- Two points are equal iff both coordinates agree. -/
theorem point_ext_iff {a b : Point} : a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := Prod.ext_iff

/-- Two points are equal if both coordinates agree. -/
theorem point_ext {a b : Point} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := Prod.ext h1 h2

/-! ### The affine parametrisation `lerp` -/

/-- The point at parameter `t` on the line through `a` and `b`
(`t = 0` gives `a`, `t = 1` gives `b`). -/
def lerp (a b : Point) (t : ℝ) : Point := (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

@[simp] theorem lerp_fst (a b : Point) (t : ℝ) : (lerp a b t).1 = a.1 + t * (b.1 - a.1) := rfl
@[simp] theorem lerp_snd (a b : Point) (t : ℝ) : (lerp a b t).2 = a.2 + t * (b.2 - a.2) := rfl

/-- `lerp a b t = a + t • (b - a)` as vectors. -/
theorem lerp_eq_add_smul (a b : Point) (t : ℝ) : lerp a b t = a + t • (b - a) := by
  ext <;> simp [lerp]

/-- `lerp a b t = (1 - t) • a + t • b` as vectors. -/
theorem lerp_eq_smul_add_smul (a b : Point) (t : ℝ) : lerp a b t = (1 - t) • a + t • b := by
  ext <;> simp [lerp] <;> ring

@[simp] theorem lerp_zero (a b : Point) : lerp a b 0 = a := by ext <;> simp [lerp]

@[simp] theorem lerp_one (a b : Point) : lerp a b 1 = b := by ext <;> simp [lerp]

@[simp] theorem lerp_self (a : Point) (t : ℝ) : lerp a a t = a := by ext <;> simp [lerp]

/-- Reversing the segment: `lerp b a t = lerp a b (1 - t)`. -/
theorem lerp_symm (a b : Point) (t : ℝ) : lerp b a t = lerp a b (1 - t) := by
  ext <;> simp [lerp] <;> ring

/-- `lerp a b` is continuous in the parameter. -/
theorem continuous_lerp (a b : Point) : Continuous (lerp a b) := by
  unfold lerp; fun_prop

/-- `lerp a b t` is injective in `t` when `a ≠ b`. -/
theorem lerp_injective {a b : Point} (hab : a ≠ b) : Function.Injective (lerp a b) := by
  intro s t hst
  rw [point_ext_iff] at hst
  simp only [lerp_fst, lerp_snd] at hst
  by_contra hne
  apply hab
  apply point_ext
  · have : (s - t) * (b.1 - a.1) = 0 := by linear_combination hst.1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linarith
  · have : (s - t) * (b.2 - a.2) = 0 := by linear_combination hst.2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linarith

/-! ### The specification's segment is Mathlib's segment -/

/-- Membership in `ArtGallery.segment`, unfolded. -/
theorem mem_segment_iff {a b p : Point} :
    p ∈ ArtGallery.segment a b ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) :=
  Iff.rfl

/-- Membership in `ArtGallery.segment` via `lerp`. -/
theorem mem_segment_iff_lerp {a b p : Point} :
    p ∈ ArtGallery.segment a b ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = lerp a b t :=
  Iff.rfl

/-- `lerp a b t` lies on the segment for `0 ≤ t ≤ 1`. -/
theorem lerp_mem_segment (a b : Point) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp a b t ∈ ArtGallery.segment a b :=
  ⟨t, h0, h1, rfl⟩

/-- The specification's closed segment is Mathlib's `segment ℝ a b`. -/
theorem segment_eq (a b : Point) : ArtGallery.segment a b = _root_.segment ℝ a b := by
  ext p
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, (lerp_eq_add_smul a b t).symm⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, lerp_eq_add_smul a b t⟩

/-- Membership in the segment via Mathlib's two-weight description. -/
theorem mem_segment_iff_weights {a b p : Point} :
    p ∈ ArtGallery.segment a b ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ s • a + t • b = p := by
  rw [segment_eq]; rfl

/-- The segment is symmetric. -/
theorem segment_comm (a b : Point) : ArtGallery.segment a b = ArtGallery.segment b a := by
  rw [segment_eq, segment_eq, segment_symm]

/-- The left endpoint lies on the segment. -/
theorem left_mem_segment (a b : Point) : a ∈ ArtGallery.segment a b := by
  rw [segment_eq]; exact _root_.left_mem_segment ℝ a b

/-- The right endpoint lies on the segment. -/
theorem right_mem_segment (a b : Point) : b ∈ ArtGallery.segment a b := by
  rw [segment_eq]; exact _root_.right_mem_segment ℝ a b

/-- The degenerate segment is a point. -/
theorem segment_same (a : Point) : ArtGallery.segment a a = {a} := by
  rw [segment_eq]; exact _root_.segment_same ℝ a

/-- The segment is the convex hull of its endpoints. -/
theorem segment_eq_convexHull_pair (a b : Point) :
    ArtGallery.segment a b = convexHull ℝ {a, b} := by
  rw [segment_eq, convexHull_pair]

/-- A segment is convex. -/
theorem segment_convex (a b : Point) : Convex ℝ (ArtGallery.segment a b) := by
  rw [segment_eq]; exact convex_segment a b

/-- A segment with both endpoints in `s` lies in the convex hull of `s`. -/
theorem segment_subset_convexHull {s : Set Point} {a b : Point} (ha : a ∈ s) (hb : b ∈ s) :
    ArtGallery.segment a b ⊆ convexHull ℝ s := by
  rw [segment_eq]; exact _root_.segment_subset_convexHull ha hb

/-- A segment with both endpoints in a convex set lies in it. -/
theorem segment_subset_of_convex {s : Set Point} (hs : Convex ℝ s) {a b : Point}
    (ha : a ∈ s) (hb : b ∈ s) : ArtGallery.segment a b ⊆ s := by
  rw [segment_eq]; exact hs.segment_subset ha hb

/-- The convex hull of a finite set of points is compact. -/
theorem isCompact_convexHull_of_finite {s : Set Point} (hs : s.Finite) :
    IsCompact (convexHull ℝ s) :=
  hs.isCompact_convexHull ℝ

/-- A segment is compact. -/
theorem isCompact_segment (a b : Point) : IsCompact (ArtGallery.segment a b) := by
  rw [segment_eq_convexHull_pair]
  exact isCompact_convexHull_of_finite ((Set.finite_singleton b).insert a)

/-- A segment is closed. -/
theorem isClosed_segment (a b : Point) : IsClosed (ArtGallery.segment a b) :=
  (isCompact_segment a b).isClosed

/-- A segment is the continuous image of `[0,1]` under `lerp a b`. -/
theorem segment_eq_image_lerp (a b : Point) :
    ArtGallery.segment a b = lerp a b '' Set.Icc (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩

/-! ### Bounded sets -/

/-- The specification's boundedness is Mathlib's `Bornology.IsBounded` (sup norm). -/
theorem isBoundedSet_iff {S : Set Point} : IsBoundedSet S ↔ Bornology.IsBounded S := by
  constructor
  · rintro ⟨R, hR⟩
    refine isBounded_iff_forall_norm_le.2 ⟨R, fun p hp => ?_⟩
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact hR p hp
  · intro h
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h
    refine ⟨C, fun p hp => ?_⟩
    have h1 := (norm_fst_le p).trans (hC p hp)
    have h2 := (norm_snd_le p).trans (hC p hp)
    rw [Real.norm_eq_abs] at h1 h2
    exact ⟨h1, h2⟩

/-- A subset of a bounded set is bounded. -/
theorem isBoundedSet_of_subset {S T : Set Point} (hT : IsBoundedSet T) (h : S ⊆ T) :
    IsBoundedSet S := by
  rw [isBoundedSet_iff] at hT ⊢
  exact hT.subset h

/-- The union of two bounded sets is bounded. -/
theorem isBoundedSet_union {S T : Set Point} (hS : IsBoundedSet S) (hT : IsBoundedSet T) :
    IsBoundedSet (S ∪ T) := by
  rw [isBoundedSet_iff] at hS hT ⊢
  exact hS.union hT

/-- The empty set is bounded. -/
theorem isBoundedSet_empty : IsBoundedSet (∅ : Set Point) :=
  ⟨0, fun _ h => h.elim⟩

/-- A singleton is bounded. -/
theorem isBoundedSet_singleton (p : Point) : IsBoundedSet ({p} : Set Point) := by
  rw [isBoundedSet_iff]; exact Bornology.isBounded_singleton

/-- A finite set of points is bounded. -/
theorem isBoundedSet_of_finite {S : Set Point} (hS : S.Finite) : IsBoundedSet S := by
  rw [isBoundedSet_iff]; exact hS.isBounded

/-- A finite union of bounded sets is bounded. -/
theorem isBoundedSet_biUnion {ι : Type} {s : Set ι} (hs : s.Finite) {f : ι → Set Point}
    (h : ∀ i ∈ s, IsBoundedSet (f i)) : IsBoundedSet (⋃ i ∈ s, f i) := by
  rw [isBoundedSet_iff, Bornology.isBounded_biUnion hs]
  intro i hi
  rw [← isBoundedSet_iff]
  exact h i hi

/-- A union indexed by a finite type of bounded sets is bounded. -/
theorem isBoundedSet_iUnion {ι : Type} [Finite ι] {f : ι → Set Point}
    (h : ∀ i, IsBoundedSet (f i)) : IsBoundedSet (⋃ i, f i) := by
  rw [isBoundedSet_iff, Bornology.isBounded_iUnion]
  intro i
  rw [← isBoundedSet_iff]
  exact h i

/-- A union over a range of naturals of bounded sets is bounded. -/
theorem isBoundedSet_iUnion_lt {n : ℕ} {f : ℕ → Set Point}
    (h : ∀ i, i < n → IsBoundedSet (f i)) : IsBoundedSet (⋃ i, ⋃ (_ : i < n), f i) := by
  have : (⋃ i, ⋃ (_ : i < n), f i) = ⋃ i ∈ Set.Iio n, f i := by
    ext p; simp
  rw [this]
  exact isBoundedSet_biUnion (Set.finite_Iio n) (fun i hi => h i hi)

/-- A compact set is bounded. -/
theorem isBoundedSet_of_isCompact {S : Set Point} (hS : IsCompact S) : IsBoundedSet S := by
  rw [isBoundedSet_iff]; exact hS.isBounded

/-- A segment is bounded. -/
theorem segment_bounded (a b : Point) : IsBoundedSet (ArtGallery.segment a b) :=
  isBoundedSet_of_isCompact (isCompact_segment a b)

/-- The convex hull of a finite set of points is bounded. -/
theorem convexHull_bounded_of_finite {s : Set Point} (hs : s.Finite) :
    IsBoundedSet (convexHull ℝ s) :=
  isBoundedSet_of_isCompact (isCompact_convexHull_of_finite hs)

end

end Geometry

end ArtGallery
