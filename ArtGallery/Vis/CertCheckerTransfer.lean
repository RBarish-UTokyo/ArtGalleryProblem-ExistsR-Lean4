module

public import ArtGallery.Vis.CertCheckerSimple
public import ArtGallery.Invariance.Affine

/-!
# Kernel-checkable certificates: transfer lemmas

Invariance of the specification's notions under the maps used to place templates:

* for every invertible affine map `A` (`ArtGallery.Hardening.Invariance.mapPoly`):
  `Simple` (`simple_mapPoly_iff`, from `ArtGallery/Invariance/Affine.lean`), `filled`
  (`filled_mapPoly`), and here also `Sees` (`sees_mapPoly_iff`), convex hulls and interiors;
* the similarities `simil s hs t : p ↦ s • p + t` (`s ≠ 0`; translations and positive scalings
  in particular): `simple_map_simil_iff`, `filled_map_simil`, `sees_map_simil_iff`;
* the reversal of the vertex list (`revPoly`): `simple_revPoly_iff`, `boundary_revPoly`,
  `filled_revPoly`, `sees_revPoly_iff`, `edge_revPoly`;
* the mirror `x ↦ c − x` together with the reversal of the vertex list (`reflX`, `mirrorPoly`):
  `simple_mirrorPoly_iff`, `filled_mirrorPoly`, `sees_mirrorPoly_iff`, and the integer form
  `mirrorInt`.

It also provides the integer front end of the simplicity checker, `simpleCheck`
(`simple_of_simpleCheck`: the integer polygon is translated to natural coordinates), and the
bridge to rational data scaled by a common denominator (`ratScale`, `mk_ratScale_eq`,
`simple_ratScale_of_simpleCheck`).
-/

@[expose] public section

namespace ArtGallery.Vis.Cert

open ArtGallery.Geometry ArtGallery.Hardening.Invariance Set

/-! ### Affine maps: seeing, hulls, interiors -/

/-- **Seeing is invariant under invertible affine maps.** -/
theorem sees_mapPoly_iff (A : Point ≃ᵃ[ℝ] Point) (P : Polygon) (p q : Point) :
    (mapPoly A P).Sees (A p) (A q) ↔ P.Sees p q := by
  unfold Polygon.Sees
  rw [filled_mapPoly, ← image_segment', Set.image_subset_image_iff A.injective]

/-- An affine map sends convex hulls to convex hulls. -/
theorem image_convexHull_affine (A : Point ≃ᵃ[ℝ] Point) (S : Set Point) :
    A '' convexHull ℝ S = convexHull ℝ (A '' S) :=
  AffineMap.image_convexHull A.toAffineMap S

/-- An invertible affine map sends interiors to interiors. -/
theorem image_interior_affine (A : Point ≃ᵃ[ℝ] Point) (S : Set Point) :
    A '' interior S = interior (A '' S) :=
  (homeo A).image_interior S

/-! ### Similarities -/

/-- The similarity `p ↦ s • p + t` (`s ≠ 0`). -/
noncomputable def simil (s : ℝ) (hs : s ≠ 0) (t : Point) : Point ≃ᵃ[ℝ] Point :=
  (LinearEquiv.smulOfNeZero ℝ Point s hs).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Point t)

@[simp] theorem simil_apply (s : ℝ) (hs : s ≠ 0) (t p : Point) : simil s hs t p = s • p + t := by
  simp only [simil, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
    LinearEquiv.smulOfNeZero_apply, AffineEquiv.constVAdd_apply, vadd_eq_add]
  exact add_comm _ _

/-- **Simplicity is invariant under similarities** (translations, scalings). -/
theorem simple_map_simil_iff (s : ℝ) (hs : s ≠ 0) (t : Point) (V : List Point) :
    (Polygon.mk (V.map (simil s hs t))).Simple ↔ (Polygon.mk V).Simple :=
  simple_mapPoly_iff (simil s hs t) ⟨V⟩

/-- **The region of the image under a similarity is the image of the region.** -/
theorem filled_map_simil (s : ℝ) (hs : s ≠ 0) (t : Point) (V : List Point) :
    (Polygon.mk (V.map (simil s hs t))).filled = simil s hs t '' (Polygon.mk V).filled :=
  filled_mapPoly (simil s hs t) ⟨V⟩

/-- **Seeing is invariant under similarities.** -/
theorem sees_map_simil_iff (s : ℝ) (hs : s ≠ 0) (t : Point) (V : List Point) (p q : Point) :
    (Polygon.mk (V.map (simil s hs t))).Sees (s • p + t) (s • q + t) ↔ (Polygon.mk V).Sees p q := by
  have := sees_mapPoly_iff (simil s hs t) ⟨V⟩ p q
  rw [simil_apply, simil_apply] at this
  exact this

/-- The determinant under a similarity is multiplied by `s²` (orientation is preserved). -/
theorem det_simil (s : ℝ) (hs : s ≠ 0) (t a b c : Point) :
    det (simil s hs t a) (simil s hs t b) (simil s hs t c) = s ^ 2 * det a b c := by
  simp only [simil_apply, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-! ### Reversal of the vertex list -/

/-- The polygon with the vertex list reversed. -/
def revPoly (P : Polygon) : Polygon := ⟨P.vertices.reverse⟩

/-- The index map of the reversal on edges: edge `i` of the reversed polygon is edge
`revIdx n i` of the original (traversed backwards). -/
def revIdx (n i : ℕ) : ℕ := if i + 1 < n then n - 2 - i else n - 1

theorem revIdx_lt {n i : ℕ} (hi : i < n) : revIdx n i < n := by
  unfold revIdx; split_ifs <;> omega

theorem revIdx_revIdx {n i : ℕ} (hi : i < n) : revIdx n (revIdx n i) = i := by
  unfold revIdx; split_ifs <;> omega

theorem revIdx_injective {n i j : ℕ} (hi : i < n) (hj : j < n) (h : revIdx n i = revIdx n j) :
    i = j := by
  rw [← revIdx_revIdx hi, ← revIdx_revIdx hj, h]

section Reverse

variable (P : Polygon)

@[simp] theorem n_revPoly : (revPoly P).n = P.n := by simp [revPoly, Polygon.n]

theorem revPoly_revPoly : revPoly (revPoly P) = P := by simp [revPoly]

theorem vtx_revPoly {i : ℕ} (hi : i < P.n) : (revPoly P).vtx i = P.vtx (P.n - 1 - i) := by
  unfold Polygon.vtx revPoly
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse hi, List.getD_eq_getElem?_getD]
  rfl

/-- The endpoints of edge `i` of the reversed polygon are the endpoints of edge `revIdx n i`
of the original, swapped. -/
theorem endpoints_revPoly {i : ℕ} (hi : i < P.n) :
    (revPoly P).vtx i = P.vtx ((revIdx P.n i + 1) % P.n) ∧
      (revPoly P).vtx ((i + 1) % (revPoly P).n) = P.vtx (revIdx P.n i) := by
  rw [n_revPoly]
  unfold revIdx
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h, vtx_revPoly P hi, vtx_revPoly P h,
      Nat.mod_eq_of_lt (by omega : P.n - 2 - i + 1 < P.n)]
    exact ⟨congrArg P.vtx (by omega), congrArg P.vtx (by omega)⟩
  · have hi' : i = P.n - 1 := by omega
    subst hi'
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self, vtx_revPoly P hi,
      vtx_revPoly P (by omega)]
    exact ⟨congrArg P.vtx (by omega), congrArg P.vtx (by omega)⟩

theorem edge_revPoly {i : ℕ} (hi : i < P.n) : (revPoly P).edge i = P.edge (revIdx P.n i) := by
  unfold Polygon.edge
  obtain ⟨h1, h2⟩ := endpoints_revPoly P hi
  rw [h1, h2, segment_comm]

theorem commonEndpoints_revPoly {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    (revPoly P).commonEndpoints i j = P.commonEndpoints (revIdx P.n i) (revIdx P.n j) := by
  unfold Polygon.commonEndpoints
  obtain ⟨h1, h2⟩ := endpoints_revPoly P hi
  obtain ⟨h3, h4⟩ := endpoints_revPoly P hj
  rw [h1, h2, h3, h4]
  ext p
  simp only [mem_ofPred_eq]
  exact and_congr or_comm or_comm

/-- **Reversing the vertex list preserves simplicity.** -/
theorem simple_revPoly (hP : P.Simple) : (revPoly P).Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by rw [n_revPoly]; exact h3, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · rw [n_revPoly] at hi hj
    rw [vtx_revPoly P hi, vtx_revPoly P hj] at h
    have := hinj _ _ (by omega) (by omega) h
    omega
  · rw [n_revPoly] at hi hj
    rw [edge_revPoly P hi, edge_revPoly P hj, commonEndpoints_revPoly P hi hj]
    exact hedge _ _ (revIdx_lt hi) (revIdx_lt hj) fun h => hij (revIdx_injective hi hj h)

/-- **Simplicity is invariant under reversal of the vertex list.** -/
theorem simple_revPoly_iff : (revPoly P).Simple ↔ P.Simple := by
  refine ⟨fun h => ?_, simple_revPoly P⟩
  have := simple_revPoly _ h
  rwa [revPoly_revPoly] at this

/-- The reversed polygon has the same boundary. -/
theorem boundary_revPoly : (revPoly P).boundary = P.boundary := by
  ext p
  simp only [Polygon.boundary, mem_ofPred_eq, n_revPoly]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨revIdx P.n i, revIdx_lt hi, by rwa [edge_revPoly P hi] at hp⟩
  · rintro ⟨i, hi, hp⟩
    refine ⟨revIdx P.n i, revIdx_lt hi, ?_⟩
    rwa [edge_revPoly P (revIdx_lt hi), revIdx_revIdx hi]

/-- **The reversed polygon has the same region.** -/
theorem filled_revPoly : (revPoly P).filled = P.filled := by
  unfold Polygon.filled
  rw [boundary_revPoly]

/-- Seeing is invariant under reversal of the vertex list. -/
theorem sees_revPoly_iff (p q : Point) : (revPoly P).Sees p q ↔ P.Sees p q := by
  unfold Polygon.Sees
  rw [filled_revPoly]

end Reverse

/-! ### The mirror `x ↦ c − x` -/

/-- The linear map `(x, y) ↦ (−x, y)`. -/
noncomputable def flipX : Point ≃ₗ[ℝ] Point where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  map_add' p q := by ext <;> simp; ring
  map_smul' s p := by ext <;> simp
  left_inv p := by simp
  right_inv p := by simp

/-- The reflection `(x, y) ↦ (c − x, y)` in the vertical line `x = c/2`. -/
noncomputable def reflX (c : ℝ) : Point ≃ᵃ[ℝ] Point :=
  flipX.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Point (c, 0))

@[simp] theorem reflX_apply (c : ℝ) (p : Point) : reflX c p = (c - p.1, p.2) := by
  simp only [reflX, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
    AffineEquiv.constVAdd_apply, vadd_eq_add]
  ext <;> simp [flipX]; ring

/-- The mirror reverses orientation. -/
theorem det_reflX (c : ℝ) (a b d : Point) :
    det (reflX c a) (reflX c b) (reflX c d) = - det a b d := by
  simp only [reflX_apply, det]; ring

/-- The mirror image of a polygon, with the vertex list reversed (so that the orientation is
preserved). -/
noncomputable def mirrorPoly (c : ℝ) (P : Polygon) : Polygon := revPoly (mapPoly (reflX c) P)

theorem mirrorPoly_vertices (c : ℝ) (P : Polygon) :
    (mirrorPoly c P).vertices = (P.vertices.map (reflX c)).reverse := rfl

/-- **Simplicity is invariant under the mirror with reversal.** -/
theorem simple_mirrorPoly_iff (c : ℝ) (P : Polygon) : (mirrorPoly c P).Simple ↔ P.Simple :=
  (simple_revPoly_iff _).trans (simple_mapPoly_iff _ _)

/-- **The region of the mirrored polygon is the mirror image of the region.** -/
theorem filled_mirrorPoly (c : ℝ) (P : Polygon) :
    (mirrorPoly c P).filled = reflX c '' P.filled := by
  unfold mirrorPoly
  rw [filled_revPoly, filled_mapPoly]

/-- **Seeing is invariant under the mirror with reversal.** -/
theorem sees_mirrorPoly_iff (c : ℝ) (P : Polygon) (p q : Point) :
    (mirrorPoly c P).Sees (reflX c p) (reflX c q) ↔ P.Sees p q := by
  unfold mirrorPoly
  rw [sees_revPoly_iff, sees_mapPoly_iff]

/-- The mirror `x ↦ c − x` of an integer vertex list, reversed. -/
def mirrorInt (c : ℤ) (V : List IPt) : List IPt := (V.map fun z => (c - z.1, z.2)).reverse

theorem mk_mirrorInt (c : ℤ) (V : List IPt) :
    Polygon.mk ((mirrorInt c V).map intPoint) = mirrorPoly (c : ℝ) (Polygon.mk (V.map intPoint)) := by
  simp only [mirrorInt, mirrorPoly, revPoly, mapPoly, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun z _ => ?_
  simp [intPoint]

/-- **Integer mirror with reversal: simplicity.** -/
theorem simple_mirrorInt_iff (c : ℤ) (V : List IPt) :
    (Polygon.mk ((mirrorInt c V).map intPoint)).Simple ↔ (Polygon.mk (V.map intPoint)).Simple := by
  rw [mk_mirrorInt]; exact simple_mirrorPoly_iff _ _

/-- **Integer mirror with reversal: the region.** -/
theorem filled_mirrorInt (c : ℤ) (V : List IPt) :
    (Polygon.mk ((mirrorInt c V).map intPoint)).filled =
      reflX (c : ℝ) '' (Polygon.mk (V.map intPoint)).filled := by
  rw [mk_mirrorInt]; exact filled_mirrorPoly _ _

/-! ### Integer front end of the simplicity check -/

/-- Componentwise minimum of `m` and all points of a list. -/
def iminPt : List IPt → IPt → IPt
  | [], m => m
  | p :: l, m => iminPt l (cond (ile p.1 m.1) p.1 m.1, cond (ile p.2 m.2) p.2 m.2)

theorem iminPt_le : ∀ (l : List IPt) (m : IPt),
    ((iminPt l m).1 ≤ m.1 ∧ (iminPt l m).2 ≤ m.2) ∧
      ∀ q ∈ l, (iminPt l m).1 ≤ q.1 ∧ (iminPt l m).2 ≤ q.2
  | [], m => by simp [iminPt]
  | p :: l, m => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := iminPt_le l (cond (ile p.1 m.1) p.1 m.1, cond (ile p.2 m.2) p.2 m.2)
    have e1 : cond (ile p.1 m.1) p.1 m.1 = min p.1 m.1 := by
      by_cases h : p.1 ≤ m.1
      · rw [(ile_iff).2 h]; simp [h]
      · have : ile p.1 m.1 = false := by
          cases hh : ile p.1 m.1
          · rfl
          · exact absurd (ile_iff.1 hh) h
        rw [this]; simp; omega
    have e2 : cond (ile p.2 m.2) p.2 m.2 = min p.2 m.2 := by
      by_cases h : p.2 ≤ m.2
      · rw [(ile_iff).2 h]; simp [h]
      · have : ile p.2 m.2 = false := by
          cases hh : ile p.2 m.2
          · rfl
          · exact absurd (ile_iff.1 hh) h
        rw [this]; simp; omega
    simp only [iminPt, List.mem_cons, forall_eq_or_imp, e1, e2]
    rw [e1, e2] at h1 h2 h3
    refine ⟨⟨le_trans h1 (min_le_right _ _), le_trans h2 (min_le_right _ _)⟩,
      ⟨le_trans h1 (min_le_left _ _), le_trans h2 (min_le_left _ _)⟩, h3⟩

/-- Translate an integer point list to natural coordinates (subtracting the componentwise
minimum of the points and the origin). -/
def shiftN (V : List IPt) : List NPt :=
  let m := iminPt V (0, 0)
  V.map fun q => ((q.1 - m.1).toNat, (q.2 - m.2).toNat)

/-- The translated polygon is the translate of the integer polygon. -/
theorem mk_shiftN (V : List IPt) :
    Polygon.mk (V.map intPoint) =
      mapPoly (AffineEquiv.constVAdd ℝ Point (((iminPt V (0, 0)).1 : ℝ), ((iminPt V (0, 0)).2 : ℝ)))
        (Polygon.mk ((shiftN V).map natPoint)) := by
  simp only [mapPoly, shiftN, List.map_map]
  congr 1
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨-, h⟩ := iminPt_le V (0, 0)
  obtain ⟨h1, h2⟩ := h q hq
  simp only [Function.comp_apply, AffineEquiv.constVAdd_apply, vadd_eq_add, natPoint, intPoint]
  have e1 : (((q.1 - (iminPt V (0, 0)).1).toNat : ℕ) : ℝ) = (q.1 : ℝ) - (iminPt V (0, 0)).1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  have e2 : (((q.2 - (iminPt V (0, 0)).2).toNat : ℕ) : ℝ) = (q.2 : ℝ) - (iminPt V (0, 0)).2 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  ext <;> simp only [Prod.fst_add, Prod.snd_add, e1, e2] <;> ring

/-- **The simplicity check** for a polygon with integer vertex coordinates. -/
def simpleCheck (V : List IPt) : Bool := simpleCheckN (shiftN V)

/-- **Soundness of the simplicity check (integer coordinates).** -/
theorem simple_of_simpleCheck {V : List IPt} (h : simpleCheck V = true) :
    (Polygon.mk (V.map intPoint)).Simple := by
  rw [mk_shiftN]
  exact simple_mapPoly _ _ (simple_of_simpleCheckN h)

/-! ### Rational data scaled by a common denominator -/

/-- The rational point `z / D`. -/
def ratScalePt (D : ℕ) (z : IPt) : ℚ × ℚ := ((z.1 : ℚ) / D, (z.2 : ℚ) / D)

/-- The rational points `z / D` of an integer list. -/
def ratScale (D : ℕ) (V : List IPt) : List (ℚ × ℚ) := V.map (ratScalePt D)

/-- The scaling by `1 / D`. -/
noncomputable def scaleDown (D : ℕ) (hD : 0 < D) : Point ≃ᵃ[ℝ] Point :=
  simil ((D : ℝ)⁻¹) (inv_ne_zero (by exact_mod_cast hD.ne')) 0

theorem ratPoint_ratScalePt (D : ℕ) (hD : 0 < D) (z : IPt) :
    ratPoint (ratScalePt D z) = scaleDown D hD (intPoint z) := by
  simp only [ratPoint, ratScalePt, scaleDown, simil_apply, intPoint, add_zero]
  ext <;> simp [div_eq_inv_mul]

/-- The rational polygon is the image of the integer polygon under the scaling by `1 / D`. -/
theorem mk_ratScale_eq (D : ℕ) (hD : 0 < D) (V : List IPt) :
    Polygon.mk ((ratScale D V).map ratPoint) = mapPoly (scaleDown D hD) (Polygon.mk (V.map intPoint)) := by
  simp only [ratScale, mapPoly, List.map_map]
  congr 1
  exact List.map_congr_left fun z _ => ratPoint_ratScalePt D hD z

/-- The set of real points of a list of rational points. -/
def ratSet (l : List (ℚ × ℚ)) : Set Point := {x | ∃ z ∈ l, ratPoint z = x}

theorem finite_ratSet (l : List (ℚ × ℚ)) : (ratSet l).Finite := by
  have : ratSet l = ratPoint '' {z | z ∈ l} := by ext x; simp [ratSet]
  rw [this]; exact (List.finite_toSet l).image _

theorem ratSet_ratScale (D : ℕ) (hD : 0 < D) (l : List IPt) :
    ratSet (ratScale D l) = scaleDown D hD '' intSet l := by
  ext x
  simp only [ratSet, ratScale, List.mem_map, intSet, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨intPoint z, ⟨z, hz, rfl⟩, (ratPoint_ratScalePt D hD z).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨ratScalePt D z, ⟨z, hz, rfl⟩, ratPoint_ratScalePt D hD z⟩

/-- **Simplicity of a rational polygon** from the check on its integer multiple. -/
theorem simple_ratScale_of_simpleCheck {D : ℕ} (hD : 0 < D) {V : List IPt}
    (h : simpleCheck V = true) : (Polygon.mk ((ratScale D V).map ratPoint)).Simple := by
  rw [mk_ratScale_eq D hD]
  exact simple_mapPoly _ _ (simple_of_simpleCheck h)

/-- The region of the rational polygon is the scaled region of the integer polygon. -/
theorem filled_ratScale (D : ℕ) (hD : 0 < D) (V : List IPt) :
    (Polygon.mk ((ratScale D V).map ratPoint)).filled =
      scaleDown D hD '' (Polygon.mk (V.map intPoint)).filled := by
  rw [mk_ratScale_eq D hD]; exact filled_mapPoly _ _

end ArtGallery.Vis.Cert

end
