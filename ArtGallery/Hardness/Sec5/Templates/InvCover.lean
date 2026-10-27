module

public import ArtGallery.Hardness.Sec5.Templates.InvCoverData
public import ArtGallery.Hardness.Sec5.Templates.InvMech

/-!
# Section 5: the inversion template — coverage by the canonical guards (T-cover)

`docs/section5/08_proof_plan.md` §7 (T-cover), §9.  For an arbitrary simple counter-clockwise
polygon `P` containing the template chain (`ChainAt P invV a`) whose other edges avoid `invR`
(`SepAt P invV a invR`):

* **the template region** `invTR` (`InvCoverData.lean`) is the union of `29` convex integer
  pieces; it contains the filled region of the *closed template chain*
  `invK = Polygon.mk (invV.map intPoint)` (the chain closed by the **mouth**
  `invMouth = [V₄₁, V₀]`, from the last chain vertex back to the first) — `invK_filled_subset`;
  `invK.filled` is a room of `P` whose door is the mouth (`inv_room`), and `invTR ⊆ P.filled`
  (`invTR_subset`);
* **coverage** (`inv_cover`): for guard values `x, y ∈ [1/2, 2]` with `x y = 1`, every point of
  `invTR` is seen by `invGp x` (on `r_i`), `invGq y` (on `r_j`) or the stationary guard
  `g = V₃₆`.  Pieces with a fixed guard are certified for the extreme guard positions (the hull of
  the piece and the guard segment lies in `P.filled`); the umbra zone `conv invZu` is covered by
  `inv_umbra_cover` above the axis and by `g` below it; the nook is covered through the
  two-dimensional zone `conv invCvZn2` (a triangle below the nook edge containing all critical
  crossings) by the nook identity (`inv_nook_identity`, sign argument as in `inv_nook_cover`);
* **the mouth** (`inv_mouth_sees`, `inv_sees_through_mouth`): every point of the mouth is seen by
  the guard `invGp x`, and the hull of `r_i` and the mouth lies in `P.filled`, so a point beyond
  the mouth (in the channel) is seen by `invGp x` as soon as the segment from the guard to it
  crosses the mouth at a point that sees it.  This is the interface to the channel / corridor
  coverage: what is left to the unit is the part of `P.filled` beyond the mouth.
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)

/-! ### The closed template chain -/

/-- The stationary guard `g = V₃₆` is the point of `invGs`. -/
theorem inv_g_mem : intPoint (cv invV 36) ∈ convexHull ℝ (intSet invGs) :=
  mem_intSet_hull (by decide +kernel)

/-- The closed template chain: the chain `invV` closed by the mouth `V₄₁ → V₀`. -/
def invK : Polygon := Polygon.mk (invV.map intPoint)

/-- The mouth of the template: the segment from the last chain vertex back to the first. -/
def invMouth : Set Point := ArtGallery.segment (intPoint (cv invV 41)) (intPoint (cv invV 0))

theorem invK_simple : invK.Simple := simple_of_simpleCheck (by decide +kernel)

theorem invK_ccw : invK.InteriorLeft :=
  interiorLeft_of_supportB invK_simple (i := 28) (by decide +kernel)

theorem invV_subList : subList invV 0 41 = invV := by decide +kernel

/-- **Completeness** (restated): the closed template chain lies in the template region. -/
theorem invK_sub_TR : invK.filled ⊆ invTR := invK_filled_subset

section Main

variable {P : Polygon} {a : ℕ}

/-- **The closed template chain is a room of `P` with the mouth as door.** -/
theorem inv_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) :
    P.IsRoom invK.filled invMouth := by
  have h := subList_isRoom hP hL hC (k := 0) (m := 41) (by decide)
    (by rw [invV_subList]; exact invK_simple) (by rw [invV_subList]; exact invK_ccw)
  rw [invV_subList] at h
  exact h

variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) (hS : SepAt P invV a invR)
include hP hL hC hS

/-- The umbra zone lies in the region. -/
theorem invZu_sub : convexHull ℝ (intSet invZu) ⊆ P.filled :=
  (hull_subset_hull_of_all (by decide +kernel)).trans (invBp_sub hP hL hC hS)

/-- The two-dimensional nook zone lies in the region. -/
theorem invCvZn2_sub : convexHull ℝ (intSet invCvZn2) ⊆ P.filled :=
  (hull_subset_hull_of_all (by decide +kernel)).trans (invCvBn2_sub hP hL hC hS)

/-- **The template region lies in the region of `P`.** -/
theorem invTR_subset : invTR ⊆ P.filled := by
  rintro z ⟨Q, hQ, hz⟩
  rcases invCv_dispatch hP hL hC hS Q hQ z hz with h | h | h | h | h
  · exact h _ (mem_intSet_hull (by decide : ((250747895200 : ℤ), (0 : ℤ)) ∈ invRi))
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact h _ (mem_intSet_hull (by decide : ((6970791486560 : ℤ), (50149579040 : ℤ)) ∈ invRj))
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact h _ (inv_g_mem)
      (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  · exact invZu_sub hP hL hC hS h
  · exact invCvZn2_sub hP hL hC hS h

/-! ### The zones -/

/-- **Umbra zone.**  For `x y ≤ 1`, every point of the umbra zone is seen by one of the guards
(above the axis: `inv_umbra_cover`; below the axis: the stationary guard). -/
theorem inv_cover_Zu {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y ≤ 1) {z : Point} (hz : z ∈ convexHull ℝ (intSet invZu)) :
    P.Sees (invGp x) z ∨ P.Sees (invGq y) z ∨ P.Sees (intPoint (cv invV 36)) z := by
  by_cases hLu : 0 ≤ invLu.val z
  · rcases inv_umbra_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z hz hLu with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hLu
    right; right
    have hedges := edges_nonneg_of_mem_hull (Q := invZu) (by decide +kernel) hz
    by_cases hd : 0 ≤ Irrational.HP.val (1922362115200, (-4513462113600), (-93265682127118952000000)) z
    · exact invCvgF14_sees hP hL hC hS _ (inv_g_mem) z
        (invCv_Zu_gF14 hedges hLu.le hd)
    · push Not at hd
      have hd' : 0 ≤ Irrational.HP.val ((-1922362115200), 4513462113600, 93265682127118952000000) z := by
        simp only [Irrational.HP.val] at hd ⊢; push_cast at hd ⊢; linarith
      exact invCvgW_sees hP hL hC hS _ (inv_g_mem) z (invCv_Zu_gW hedges hLu.le hd')

/-- **Nook zone.**  For `x y ≥ 1`, every point of the two-dimensional nook zone is seen by one of
the two guards (the sign argument of `inv_nook_cover`, now off the nook edge: there
`Ln · det(ξ2, ξ3, ·) ≥ 0`). -/
theorem inv_cover_Zn2 {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 ≤ x * y) {z : Point} (hz : z ∈ convexHull ℝ (intSet invCvZn2)) :
    P.Sees (invGp x) z ∨ P.Sees (invGq y) z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hp : 0 < det (invGp x) (intPoint invXi2) z := by
    by_contra h; push Not at h
    exact h1 (invCv_np hP hL hC hS _ (invGp_mem hx0 hx1) z hz (by rw [invXi2_eq]; exact h))
  have hq : det (invGq y) (intPoint invXi3) z < 0 := by
    by_contra h; push Not at h
    exact h2 (invCv_nq hP hL hC hS _ (invGq_mem hy0 hy1) z hz (by rw [invXi3_eq]; exact h))
  rw [invGp_det2] at hp
  rw [invGq_det3] at hq
  have e2 : 0 ≤ invE2.val z := nonneg_on_hull (by decide +kernel) z hz
  have e3 : 0 ≤ invE3.val z := nonneg_on_hull (by decide +kernel) z hz
  have eL : 0 ≤ invLn.val z := nonneg_on_hull (by decide +kernel) z hz
  have eF : 0 ≤ det (intPoint invXi2) (intPoint invXi3) z := by
    rw [← lineHP_val]; exact nonneg_on_hull (by decide +kernel) z hz
  have hid := inv_nook_identity z
  have hD : (0 : ℝ) < invD := by rw [invD_real]; norm_num
  set N2 := invN2.val z
  set C3 := invC3.val z
  set E2 := invE2.val z
  set E3 := invE3.val z
  set Dr := (invD : ℝ)
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
  have s4 : 0 ≤ invLn.val z * det (intPoint invXi2) (intPoint invXi3) z := mul_nonneg eL eF
  nlinarith

/-! ### Coverage -/

/-- **T-cover for the inversion template.**  For guard values `x, y ∈ [1/2, 2]` with `x y = 1`
every point of the template region is seen by the guard `invGp x` of `r_i`, the guard `invGq y`
of `r_j` or the stationary guard `g = V₃₆`. -/
theorem inv_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y = 1) :
    ∀ z ∈ invTR, P.Sees (invGp x) z ∨ P.Sees (invGq y) z ∨ P.Sees (intPoint (cv invV 36)) z := by
  rintro z ⟨Q, hQ, hz⟩
  rcases invCv_dispatch hP hL hC hS Q hQ z hz with h | h | h | h | h
  · exact Or.inl (h _ (invGp_mem hx0 hx1))
  · exact Or.inr (Or.inl (h _ (invGq_mem hy0 hy1)))
  · exact Or.inr (Or.inr (h _ (inv_g_mem)))
  · exact inv_cover_Zu hP hL hC hS hx0 hx1 hy0 hy1 hxy.le h
  · rcases inv_cover_Zn2 hP hL hC hS hx0 hx1 hy0 hy1 hxy.ge h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

/-- **T-cover, region form**: every point of the closed template chain is seen. -/
theorem inv_cover_K {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y = 1) :
    ∀ z ∈ invK.filled, P.Sees (invGp x) z ∨ P.Sees (invGq y) z ∨ P.Sees (intPoint (cv invV 36)) z :=
  fun z hz => inv_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z (invK_filled_subset hz)

/-! ### The mouth -/

/-- **The mouth is seen by the guard of `r_i`** (any value), through the piece `pRoom`. -/
theorem inv_mouth_sees {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    ∀ m ∈ invMouth, P.Sees (invGp x) m := fun m hm =>
  invCvpRoom_sees hP hL hC hS _ (invGp_mem hx0 hx1) m
    (segment_subset_hull (by decide +kernel) (by decide +kernel) hm)

/-- **Seeing beyond the mouth**: if the segment from the guard of `r_i` to `z` crosses the mouth
at a point `m` that sees `z`, the guard sees `z` (used for the channel beyond the mouth). -/
theorem inv_sees_through_mouth {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) {z m : Point}
    (hm : m ∈ invMouth) (hmz : m ∈ ArtGallery.segment (invGp x) z) (hs : P.Sees m z) :
    P.Sees (invGp x) z :=
  sees_of_mem_segment hmz (inv_mouth_sees hP hL hC hS hx0 hx1 m hm) hs

/-- **Seeing beyond the mouth, cone form**: a point `z` strictly beyond the mouth line, inside
the angle at the guard spanned by the two mouth ends, and seen from every point of the mouth, is
seen by the guard of `r_i`. -/
theorem inv_sees_beyond_mouth {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) {z : Point}
    (hz : det (intPoint (cv invV 41)) (intPoint (cv invV 0)) z < 0)
    (h0 : det (invGp x) z (intPoint (cv invV 41)) ≤ 0) (h1 : 0 ≤ det (invGp x) z (intPoint (cv invV 0)))
    (hm : ∀ m ∈ invMouth, P.Sees m z) : P.Sees (invGp x) z := by
  have hp : 0 < det (intPoint (cv invV 41)) (intPoint (cv invV 0)) (invGp x) := by
    rw [← lineHP_val]; exact pos_on_hull (by decide +kernel) _ (invGp_mem hx0 hx1)
  obtain ⟨m, hmM, hmz⟩ := exists_mem_segment_inter (mul_neg_of_pos_of_neg hp hz) h0 h1
  exact inv_sees_through_mouth hP hL hC hS hx0 hx1 hmM hmz (hm m hmM)

end Main

end ArtGallery.Sec5.Tmpl

end
