module

public import ArtGallery.Invariance.Transport
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Invariance under invertible affine maps

For an invertible affine map `A : Point ≃ᵃ[ℝ] Point` of the plane and a polygon `P`, let
`mapPoly A P = ⟨P.vertices.map A⟩` be the image polygon (vertex `i` is `A (P.vtx i)`).  The
specification is invariant under `A` (no equivariance of any algorithm is claimed):

* `simple_mapPoly_iff : (mapPoly A P).Simple ↔ P.Simple`;
* `triangulates_mapPoly_iff : (mapPoly A P).Triangulates T ↔ P.Triangulates T` (same index
  triples: affine maps do not relabel vertices).

Ingredients: `A` maps segments to segments (`image_segment'`), edges and the boundary to edges
and the boundary, the complement of the boundary homeomorphically onto the complement of the
image boundary, hence connected components to connected components and bounded sets to bounded
sets (`filled_mapPoly : (mapPoly A P).filled = A '' P.filled`); closed triangles go to closed
triangles (`AffineMap.image_convexHull`); interiors to interiors (`A` is a homeomorphism); and
`det (A a) (A b) (A c) = κ · det a b c` for a constant `κ` depending only on `A` (`det_affine`),
so nondegeneracy is preserved (in both directions, using `A.symm`).

Provenance: adapted from `Chazelle/Hardening/Invariance/Affine.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery` and the directory is moved.
-/

@[expose] public section

namespace ArtGallery.Hardening.Invariance

open ArtGallery Set

/-- The image of a polygon under a map of the plane: the vertices are mapped one by one. -/
def mapPoly (f : Point → Point) (P : Polygon) : Polygon := ⟨P.vertices.map f⟩

section MapPoly

variable (f : Point → Point) (P : Polygon)

@[simp] theorem n_mapPoly : (mapPoly f P).n = P.n := by
  simp [mapPoly, Polygon.n]

/-- Vertex `i < n` of the image polygon is the image of vertex `i`. -/
theorem vtx_mapPoly {i : ℕ} (hi : i < P.n) : (mapPoly f P).vtx i = f (P.vtx i) := by
  unfold Polygon.vtx mapPoly
  have hi' : i < P.vertices.length := hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  rfl

/-- The successor vertex of the image polygon. -/
theorem vtx_succ_mapPoly {i : ℕ} (hi : i < P.n) :
    (mapPoly f P).vtx ((i + 1) % (mapPoly f P).n) = f (P.vtx ((i + 1) % P.n)) := by
  rw [n_mapPoly, vtx_mapPoly f P (Nat.mod_lt _ (by omega))]

theorem mapPoly_mapPoly (g : Point → Point) : mapPoly g (mapPoly f P) = mapPoly (g ∘ f) P := by
  simp [mapPoly, List.map_map]

theorem mapPoly_id_of (g : Point → Point) (h : ∀ x, g x = x) : mapPoly g P = P := by
  have : g = id := funext h
  subst this
  simp [mapPoly]

end MapPoly

/-! ### The affine map on segments and determinants -/

section Affine

variable (A : Point ≃ᵃ[ℝ] Point)

/-- An affine map sends the specification's segments to segments. -/
theorem image_segment' (a b : Point) : A '' segment a b = segment (A a) (A b) := by
  rw [Geometry.segment_eq, Geometry.segment_eq]
  exact image_segment ℝ A.toAffineMap a b

/-- **Determinants under an affine map**: `det (A a) (A b) (A c) = κ · det a b c`, where
`κ = det 0 (L (1,0)) (L (0,1))` only depends on the linear part `L` of `A`. -/
theorem det_affine (B : Point →ᵃ[ℝ] Point) (a b c : Point) :
    det (B a) (B b) (B c) =
      det 0 (B.linear (1, 0)) (B.linear (0, 1)) * det a b c := by
  have key : ∀ x y : Point,
      B y - B x = (y.1 - x.1) • B.linear (1, 0) + (y.2 - x.2) • B.linear (0, 1) := by
    intro x y
    rw [← vsub_eq_sub, ← AffineMap.linearMap_vsub, vsub_eq_sub, ← map_smul, ← map_smul,
      ← map_add]
    congr 1
    ext <;> simp
  have hb := key a b
  have hc := key a c
  have hb1 := congrArg Prod.fst hb
  have hb2 := congrArg Prod.snd hb
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hb1 hb2 hc1 hc2
  simp only [det, Prod.fst_zero, Prod.snd_zero, sub_zero]
  rw [hb1, hb2, hc1, hc2]
  ring

/-- Nondegeneracy is preserved by an invertible affine map. -/
theorem det_ne_zero_affine {a b c : Point} (h : det a b c ≠ 0) : det (A a) (A b) (A c) ≠ 0 := by
  intro h'
  apply h
  have := det_affine A.symm.toAffineMap (A a) (A b) (A c)
  simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.symm_apply_apply] at this
  rw [this, h', mul_zero]

/-- Bounded sets have bounded images under `A`. -/
theorem isBoundedSet_image {S : Set Point} (h : IsBoundedSet S) : IsBoundedSet (A '' S) := by
  rw [Geometry.isBoundedSet_iff] at h ⊢
  have hc : IsCompact (A '' closure S) :=
    h.isCompact_closure.image (AffineEquiv.continuous_of_finiteDimensional A)
  exact hc.isBounded.subset (image_mono subset_closure)

/-- Bounded sets are exactly the sets with bounded images. -/
theorem isBoundedSet_image_iff {S : Set Point} : IsBoundedSet (A '' S) ↔ IsBoundedSet S := by
  refine ⟨fun h => ?_, isBoundedSet_image A⟩
  have := isBoundedSet_image A.symm h
  rwa [← image_comp, show (A.symm ∘ A : Point → Point) = id from funext A.symm_apply_apply,
    image_id] at this

/-! ### The image polygon -/

variable (P : Polygon)

theorem edge_mapPoly {i : ℕ} (hi : i < P.n) : (mapPoly A P).edge i = A '' P.edge i := by
  unfold Polygon.edge
  rw [vtx_mapPoly A P hi, vtx_succ_mapPoly A P hi, image_segment']

theorem boundary_mapPoly : (mapPoly A P).boundary = A '' P.boundary := by
  ext p
  simp only [Polygon.boundary, mem_ofPred_eq, n_mapPoly, mem_image]
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [edge_mapPoly A P hi] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨x, ⟨i, hi, hx⟩, rfl⟩
  · rintro ⟨x, ⟨i, hi, hx⟩, rfl⟩
    exact ⟨i, hi, by rw [edge_mapPoly A P hi]; exact mem_image_of_mem _ hx⟩

theorem commonEndpoints_mapPoly {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    (mapPoly A P).commonEndpoints i j = A '' P.commonEndpoints i j := by
  unfold Polygon.commonEndpoints
  rw [vtx_mapPoly A P hi, vtx_mapPoly A P hj, vtx_succ_mapPoly A P hi, vtx_succ_mapPoly A P hj]
  ext p
  constructor
  · intro hp
    refine ⟨A.symm p, ?_, A.apply_symm_apply p⟩
    simp only [mem_ofPred_eq] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    constructor
    · rcases h1 with rfl | rfl <;> simp
    · rcases h2 with rfl | rfl <;> simp
  · rintro ⟨x, hx, rfl⟩
    simp only [mem_ofPred_eq] at hx ⊢
    simp only [A.apply_eq_iff_eq]
    exact hx

/-- **An invertible affine map preserves simplicity.** -/
theorem simple_mapPoly (hP : P.Simple) : (mapPoly A P).Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by rw [n_mapPoly]; exact h3, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · rw [n_mapPoly] at hi hj
    rw [vtx_mapPoly A P hi, vtx_mapPoly A P hj] at h
    exact hinj i j hi hj (A.injective h)
  · rw [n_mapPoly] at hi hj
    rw [edge_mapPoly A P hi, edge_mapPoly A P hj, commonEndpoints_mapPoly A P hi hj,
      ← image_inter A.injective, hedge i j hi hj hij]

/-- Mapping by `A` and then by `A.symm` gives back the polygon. -/
theorem mapPoly_symm_mapPoly : mapPoly A.symm (mapPoly A P) = P := by
  rw [mapPoly_mapPoly]
  exact mapPoly_id_of P _ (fun x => A.symm_apply_apply x)

/-- **Simplicity is invariant under invertible affine maps.** -/
theorem simple_mapPoly_iff : (mapPoly A P).Simple ↔ P.Simple := by
  refine ⟨fun h => ?_, simple_mapPoly A P⟩
  have := simple_mapPoly A.symm _ h
  rwa [mapPoly_symm_mapPoly] at this

/-- The homeomorphism underlying `A`. -/
noncomputable abbrev homeo : Point ≃ₜ Point := (AffineEquiv.toContinuousAffineEquiv A).toHomeomorph

theorem homeo_apply (x : Point) : homeo A x = A x := rfl

/-- `A` maps the filled region of `P` onto the filled region of the image polygon (pointwise
form). -/
theorem mem_filled_mapPoly_iff {x : Point} : A x ∈ (mapPoly A P).filled ↔ x ∈ P.filled := by
  unfold Polygon.filled
  rw [boundary_mapPoly]
  by_cases hx : x ∈ P.boundary
  · exact ⟨fun _ => Or.inl hx, fun _ => Or.inl (mem_image_of_mem _ hx)⟩
  · have hAx : A x ∉ A '' P.boundary := by
      rintro ⟨y, hy, hxy⟩; exact hx (A.injective hxy ▸ hy)
    have hcomp : connectedComponentIn (A '' P.boundary)ᶜ (A x) =
        A '' connectedComponentIn P.boundaryᶜ x := by
      rw [← image_compl_eq A.bijective]
      exact ((homeo A).image_connectedComponentIn (s := P.boundaryᶜ) hx).symm
    simp only [mem_union, mem_ofPred_eq, hx, hAx, false_or, hcomp, isBoundedSet_image_iff]

/-- **The filled region of the image polygon is the image of the filled region.** -/
theorem filled_mapPoly : (mapPoly A P).filled = A '' P.filled := by
  ext p
  constructor
  · intro hp
    refine ⟨A.symm p, ?_, A.apply_symm_apply p⟩
    rw [← mem_filled_mapPoly_iff A P, A.apply_symm_apply]; exact hp
  · rintro ⟨x, hx, rfl⟩
    exact (mem_filled_mapPoly_iff A P).2 hx

theorem triVertices_mapPoly {t : Polygon.Triangle} (ht : TriInRange P.n t) :
    (mapPoly A P).triVertices t = A '' P.triVertices t := by
  unfold Polygon.triVertices
  rw [vtx_mapPoly A P ht.1, vtx_mapPoly A P ht.2.1, vtx_mapPoly A P ht.2.2, image_insert_eq,
    image_insert_eq, image_singleton]

theorem triSet_mapPoly {t : Polygon.Triangle} (ht : TriInRange P.n t) :
    (mapPoly A P).triSet t = A '' P.triSet t := by
  unfold Polygon.triSet
  rw [triVertices_mapPoly A P ht]
  exact (AffineMap.image_convexHull A.toAffineMap _).symm

theorem validTriangle_mapPoly {t : Polygon.Triangle} (h : P.validTriangle t) :
    (mapPoly A P).validTriangle t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [n_mapPoly]; exact h1, by rw [n_mapPoly]; exact h2, by rw [n_mapPoly]; exact h3, ?_⟩
  rw [vtx_mapPoly A P h1, vtx_mapPoly A P h2, vtx_mapPoly A P h3]
  exact det_ne_zero_affine A h4

/-- **An invertible affine map carries triangulations along** (with the same index
triples). -/
theorem triangulates_mapPoly {T : List Polygon.Triangle} (hT : P.Triangulates T) :
    (mapPoly A P).Triangulates T := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hconf⟩ := hT
  have hidx : ∀ t ∈ T, TriInRange P.n t := fun t ht => triInRange_of_valid (hvalid t ht)
  refine ⟨fun t ht => validTriangle_mapPoly A P (hvalid t ht), by rw [n_mapPoly]; exact hcount,
    ?_, ?_, ?_⟩
  · rw [filled_mapPoly, ← hunion]
    ext p
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨t, ht, hp⟩
      rw [triSet_mapPoly A P (hidx t ht)] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact ⟨x, ⟨t, ht, hx⟩, rfl⟩
    · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
      exact ⟨t, ht, by rw [triSet_mapPoly A P (hidx t ht)]; exact mem_image_of_mem _ hx⟩
  · refine hdisj.imp_of_mem ?_
    intro a b ha hb h
    have e : ∀ S : Set Point, interior (A '' S) = A '' interior S := fun S => by
      exact ((homeo A).image_interior S).symm
    rw [triSet_mapPoly A P (hidx a ha), triSet_mapPoly A P (hidx b hb), e, e,
      disjoint_image_iff A.injective]
    exact h
  · refine hconf.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_mapPoly A P (hidx a ha), triSet_mapPoly A P (hidx b hb),
      triVertices_mapPoly A P (hidx a ha), triVertices_mapPoly A P (hidx b hb),
      ← image_inter A.injective, ← image_inter A.injective, h]
    exact AffineMap.image_convexHull A.toAffineMap _

/-- **Triangulating is invariant under invertible affine maps.** -/
theorem triangulates_mapPoly_iff {T : List Polygon.Triangle} :
    (mapPoly A P).Triangulates T ↔ P.Triangulates T := by
  refine ⟨fun h => ?_, triangulates_mapPoly A P⟩
  have := triangulates_mapPoly A.symm _ h
  rwa [mapPoly_symm_mapPoly] at this

end Affine

end ArtGallery.Hardening.Invariance
