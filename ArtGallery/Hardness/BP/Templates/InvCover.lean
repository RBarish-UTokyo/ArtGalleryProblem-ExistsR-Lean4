module

public import ArtGallery.Hardness.BP.Templates.InvCoverData
public import ArtGallery.Hardness.BP.Templates.InvMech

/-!
# Boundary-point templates: the inversion template — coverage (T-cover)

As in Section 5 (`Sec5/Templates/InvCover.lean`), with the receivers in bays.
For an arbitrary simple counter-clockwise
polygon `P` containing the template chain (`ChainAt P bpInvV a`) whose other edges avoid `bpInvR`
(`SepAt P bpInvV a bpInvR`):

* **the template region** `bpInvTR` (`InvCoverData.lean`) is the union of `26` convex integer
  pieces; it contains the filled region of the *closed template chain*
  `bpInvK = Polygon.mk (bpInvV.map intPoint)` (the chain closed by the **mouth**
  `bpInvMouth = [V₃₇, V₀]`, from the last chain vertex back to the first) — `bpInvK_filled_subset`;
  `bpInvK.filled` is a room of `P` whose door is the mouth (`bpInv_room`), and `bpInvTR ⊆ P.filled`
  (`bpInvTR_subset`);
* **coverage** (`bpInv_cover`): for guard values `x, y ∈ [1/2, 2]` with `x y = 1`, every point of
  `bpInvTR` is seen by `bpInvGp x` (on `r_i`), `bpInvGq y` (on `r_j`) or the stationary guard
  `g = V₃₂`.  Pieces with a fixed guard are certified for the extreme guard positions (the hull of
  the piece and the guard segment lies in `P.filled`); the umbra zone `conv bpInvZu` is covered by
  `bpInv_umbra_cover` above the axis and by `g` below it; the nook is covered through the
  two-dimensional zone `conv bpInvCvZn2` (a triangle below the nook edge containing all critical
  crossings) by the nook identity (`bpInv_nook_identity`, sign argument as in `bpInv_nook_cover`);
* **the mouth** (`bpInv_mouth_sees`, `bpInv_sees_through_mouth`): every point of the mouth is seen by
  the guard `bpInvGp x`, and the hull of `r_i` and the mouth lies in `P.filled`, so a point beyond
  the mouth (in the channel) is seen by `bpInvGp x` as soon as the segment from the guard to it
  crosses the mouth at a point that sees it.  This is the interface to the channel / corridor
  coverage: what is left to the unit is the part of `P.filled` beyond the mouth.
-/

@[expose] public section

namespace ArtGallery.BP.Tmpl

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl
open ArtGallery.Irrational (HP)

/-! ### The closed template chain -/

/-- The stationary guard `g = V₃₂` is the point of `bpInvGs`. -/
theorem bpInv_g_mem : intPoint (cv bpInvV 32) ∈ convexHull ℝ (intSet bpInvGs) :=
  mem_intSet_hull (by decide +kernel)

/-- The closed template chain: the chain `bpInvV` closed by the mouth `V₃₇ → V₀`. -/
def bpInvK : Polygon := Polygon.mk (bpInvV.map intPoint)

/-- The mouth of the template: the segment from the last chain vertex back to the first. -/
def bpInvMouth : Set Point := ArtGallery.segment (intPoint (cv bpInvV 37)) (intPoint (cv bpInvV 0))

theorem bpInvK_simple : bpInvK.Simple := simple_of_simpleCheck (by decide +kernel)

theorem bpInvK_ccw : bpInvK.InteriorLeft :=
  interiorLeft_of_supportB bpInvK_simple (i := 5) (by decide +kernel)

theorem bpInvV_subList : subList bpInvV 0 37 = bpInvV := by decide +kernel

/-- **Completeness** (restated): the closed template chain lies in the template region. -/
theorem bpInvK_sub_TR : bpInvK.filled ⊆ bpInvTR := bpInvK_filled_subset

section Main

variable {P : Polygon} {a : ℕ}

/-- **The closed template chain is a room of `P` with the mouth as door.** -/
theorem bpInv_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a) :
    P.IsRoom bpInvK.filled bpInvMouth := by
  have h := subList_isRoom hP hL hC (k := 0) (m := 37) (by decide)
    (by rw [bpInvV_subList]; exact bpInvK_simple) (by rw [bpInvV_subList]; exact bpInvK_ccw)
  rw [bpInvV_subList] at h
  exact h

variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a) (hS : SepAt P bpInvV a bpInvR)
include hP hL hC hS

/-- The umbra zone lies in the region. -/
theorem bpInvZu_sub : convexHull ℝ (intSet bpInvZu) ⊆ P.filled :=
  (hull_subset_hull_of_all (by decide +kernel)).trans (bpInvBp_sub hP hL hC hS)

/-- The two-dimensional nook zone lies in the region. -/
theorem bpInvCvZn2_sub : convexHull ℝ (intSet bpInvCvZn2) ⊆ P.filled :=
  (hull_subset_hull_of_all (by decide +kernel)).trans (bpInvCvBn2_sub hP hL hC hS)

/-- **The template region lies in the region of `P`.** -/
theorem bpInvTR_subset : bpInvTR ⊆ P.filled := by
  rintro z ⟨Q, hQ, hz⟩
  rcases bpInvCv_dispatch hP hL hC hS Q hQ z hz with h | h | h | h | h
  · exact h _ (mem_intSet_hull (by decide : ((1504487371200 : ℤ), (0 : ℤ)) ∈ bpInvRi))
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact h _ (mem_intSet_hull (by decide : ((41824748919360 : ℤ), (300897474240 : ℤ)) ∈ bpInvRj))
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact h _ (bpInv_g_mem)
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact bpInvZu_sub hP hL hC hS h
  · exact bpInvCvZn2_sub hP hL hC hS h

/-! ### The zones -/

/-- **Umbra zone.**  For `x y ≤ 1`, every point of the umbra zone is seen by one of the guards
(above the axis: `bpInv_umbra_cover`; below the axis: the stationary guard). -/
theorem bpInv_cover_Zu {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y ≤ 1) {z : Point} (hz : z ∈ convexHull ℝ (intSet bpInvZu)) :
    P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z ∨ P.Sees (intPoint (cv bpInvV 32)) z := by
  by_cases hLu : 0 ≤ bpInvLu.val z
  · rcases bpInv_umbra_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z hz hLu with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hLu
    right; right
    have hedges := edges_nonneg_of_mem_hull (Q := bpInvZu) (by decide +kernel) hz
    by_cases hd : 0 ≤ Irrational.HP.val (11534172691200, (-27080772681600), (-3357564556576282272000000)) z
    · exact bpInvCvgF12_sees hP hL hC hS _ (bpInv_g_mem) z
        (bpInvCv_Zu_gF12 hedges hLu.le hd)
    · push Not at hd
      have hd' : 0 ≤ Irrational.HP.val ((-11534172691200), 27080772681600, 3357564556576282272000000) z := by
        simp only [Irrational.HP.val] at hd ⊢; push_cast at hd ⊢; linarith
      exact bpInvCvgW_sees hP hL hC hS _ (bpInv_g_mem) z (bpInvCv_Zu_gW hedges hLu.le hd')

/-- **Nook zone.**  For `x y ≥ 1`, every point of the two-dimensional nook zone is seen by one of
the two guards (the sign argument of `bpInv_nook_cover`, now off the nook edge: there
`Ln · det(ξ2, ξ3, ·) ≥ 0`). -/
theorem bpInv_cover_Zn2 {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 ≤ x * y) {z : Point} (hz : z ∈ convexHull ℝ (intSet bpInvCvZn2)) :
    P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hp : 0 < det (bpInvGp x) (intPoint bpInvXi2) z := by
    by_contra h; push Not at h
    exact h1 (bpInvCv_np hP hL hC hS _ (bpInvGp_mem hx0 hx1) z hz (by rw [bpInvXi2_eq]; exact h))
  have hq : det (bpInvGq y) (intPoint bpInvXi3) z < 0 := by
    by_contra h; push Not at h
    exact h2 (bpInvCv_nq hP hL hC hS _ (bpInvGq_mem hy0 hy1) z hz (by rw [bpInvXi3_eq]; exact h))
  rw [bpInvGp_det2] at hp
  rw [bpInvGq_det3] at hq
  have e2 : 0 ≤ bpInvE2.val z := nonneg_on_hull (by decide +kernel) z hz
  have e3 : 0 ≤ bpInvE3.val z := nonneg_on_hull (by decide +kernel) z hz
  have eL : 0 ≤ bpInvLn.val z := nonneg_on_hull (by decide +kernel) z hz
  have eF : 0 ≤ det (intPoint bpInvXi2) (intPoint bpInvXi3) z := by
    rw [← lineHP_val]; exact nonneg_on_hull (by decide +kernel) z hz
  have hid := bpInv_nook_identity z
  have hD : (0 : ℝ) < bpInvD := by rw [bpInvD_real]; norm_num
  set N2 := bpInvN2.val z
  set C3 := bpInvC3.val z
  set E2 := bpInvE2.val z
  set E3 := bpInvE3.val z
  set Dr := (bpInvD : ℝ)
  have hx : 0 ≤ Dr * x * E2 := by have : 0 ≤ x := by linarith
                                  positivity
  have hy : 0 ≤ Dr * y * E3 := by have : 0 ≤ y := by linarith
                                  positivity
  have s1 : (Dr * x * E2) * (Dr * y * E3) < N2 * C3 := mul_lt_mul'' (by linarith) (by linarith) hx hy
  have s3 : Dr ^ 2 * E2 * E3 ≤ (Dr * x * E2) * (Dr * y * E3) := by
    have : (Dr * x * E2) * (Dr * y * E3) = (x * y) * (Dr ^ 2 * E2 * E3) := by ring
    rw [this]
    have : 0 ≤ Dr ^ 2 * E2 * E3 := by positivity
    nlinarith
  have s4 : 0 ≤ bpInvLn.val z * det (intPoint bpInvXi2) (intPoint bpInvXi3) z := mul_nonneg eL eF
  nlinarith

/-! ### Coverage -/

/-- **T-cover for the inversion template.**  For guard values `x, y ∈ [1/2, 2]` with `x y = 1`
every point of the template region is seen by the guard `bpInvGp x` of `r_i`, the guard `bpInvGq y`
of `r_j` or the stationary guard `g = V₃₂`. -/
theorem bpInv_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y = 1) :
    ∀ z ∈ bpInvTR, P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z ∨ P.Sees (intPoint (cv bpInvV 32)) z := by
  rintro z ⟨Q, hQ, hz⟩
  rcases bpInvCv_dispatch hP hL hC hS Q hQ z hz with h | h | h | h | h
  · exact Or.inl (h _ (bpInvGp_mem hx0 hx1))
  · exact Or.inr (Or.inl (h _ (bpInvGq_mem hy0 hy1)))
  · exact Or.inr (Or.inr (h _ (bpInv_g_mem)))
  · exact bpInv_cover_Zu hP hL hC hS hx0 hx1 hy0 hy1 hxy.le h
  · rcases bpInv_cover_Zn2 hP hL hC hS hx0 hx1 hy0 hy1 hxy.ge h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

/-- **T-cover, region form**: every point of the closed template chain is seen. -/
theorem bpInv_cover_K {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y = 1) :
    ∀ z ∈ bpInvK.filled, P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z ∨ P.Sees (intPoint (cv bpInvV 32)) z :=
  fun z hz => bpInv_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z (bpInvK_filled_subset hz)

/-! ### The mouth -/

/-- **The mouth is seen by the guard of `r_i`** (any value), through the piece `pRoom`. -/
theorem bpInv_mouth_sees {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    ∀ m ∈ bpInvMouth, P.Sees (bpInvGp x) m := fun m hm =>
  bpInvCvpRoom_sees hP hL hC hS _ (bpInvGp_mem hx0 hx1) m
    (segment_subset_hull (by decide +kernel) (by decide +kernel) hm)

/-- **Seeing beyond the mouth**: if the segment from the guard of `r_i` to `z` crosses the mouth
at a point `m` that sees `z`, the guard sees `z` (used for the channel beyond the mouth). -/
theorem bpInv_sees_through_mouth {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) {z m : Point}
    (hm : m ∈ bpInvMouth) (hmz : m ∈ ArtGallery.segment (bpInvGp x) z) (hs : P.Sees m z) :
    P.Sees (bpInvGp x) z :=
  sees_of_mem_segment hmz (bpInv_mouth_sees hP hL hC hS hx0 hx1 m hm) hs

/-- **Seeing beyond the mouth, cone form**: a point `z` strictly beyond the mouth line, inside
the angle at the guard spanned by the two mouth ends, and seen from every point of the mouth, is
seen by the guard of `r_i`. -/
theorem bpInv_sees_beyond_mouth {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) {z : Point}
    (hz : det (intPoint (cv bpInvV 37)) (intPoint (cv bpInvV 0)) z < 0)
    (h0 : det (bpInvGp x) z (intPoint (cv bpInvV 37)) ≤ 0) (h1 : 0 ≤ det (bpInvGp x) z (intPoint (cv bpInvV 0)))
    (hm : ∀ m ∈ bpInvMouth, P.Sees m z) : P.Sees (bpInvGp x) z := by
  have hp : 0 < det (intPoint (cv bpInvV 37)) (intPoint (cv bpInvV 0)) (bpInvGp x) := by
    rw [← lineHP_val]; exact pos_on_hull (by decide +kernel) _ (bpInvGp_mem hx0 hx1)
  obtain ⟨m, hmM, hmz⟩ := exists_mem_segment_inter (mul_neg_of_pos_of_neg hp hz) h0 h1
  exact bpInv_sees_through_mouth hP hL hC hS hx0 hx1 hmM hmz (hm m hmM)

end Main

end ArtGallery.BP.Tmpl

end
