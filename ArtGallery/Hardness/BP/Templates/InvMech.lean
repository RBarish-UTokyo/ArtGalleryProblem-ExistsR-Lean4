module

public import ArtGallery.Hardness.BP.Templates.InvData

/-!
# Boundary-point templates: the inversion template — the mechanism (paper Lemmas 49/50)

Integer template coordinates (`InvData.lean`, `T = Z / bpInvD`).  The mechanism is the one of
Section 5 (`Sec5/Templates/InvMech.lean`); only the receivers lie in bays.
For values `x, y ∈ [1/2, 2]` the guard of `r_i` is `bpInvGp x = (D x, 0)` and the guard of `r_j` is
`bpInvGq y = (D (159/10 − y), D/10)`.  For an arbitrary simple counter-clockwise polygon `P`
containing the template chain (`ChainAt P bpInvV a`) whose other edges avoid `bpInvR`
(`SepAt P bpInvV a bpInvR`):

* **umbra** (`bpInv_umbra_iff`): the points of the umbra zone `conv bpInvZu` strictly above the axis
  `f0 f1` (`bpInvLu > 0`) are all seen by the two guards iff `x y ≤ 1`; for `x y ≤ 1` even the
  points on the axis are covered (`bpInv_umbra_cover`), for `x y > 1` an explicit crossing point
  `bpInvX x' y'` is seen by neither (`bpInv_umbra_gap`);
* **nook** (`bpInv_nook_iff`): the nook zone `conv bpInvZn` (a sub-segment of the nook top edge
  containing the critical segment `[f2, f3]`, with the corrected `f2` of Section 5) is covered iff `x y ≥ 1`.

Proof: the visibility characterisations of `InvData.lean` (`bpInv_vis_up`, …) reduce coverage to
sign conditions; with `det(p, ξ0, z) = N0 − D x E0` and `det(q, ξ1, z) = −C1 + D y E1` the
*inversion identity* `N0 C1 − D² E0 E1 = K · Lu · det(ξ0, ξ1, z)` (`bpInv_umbra_identity`,
the conic through `ξ0`, `ξ1` of the crossings for `x y = 1` splits into the axis and the floor
line) gives the umbra; the nook identity (`bpInv_nook_identity`) vanishes on the nook axis.  The
gap points are explicit crossing points; their membership in the zones is reduced to the four
corners of the value square by bilinear interpolation (`bilin_nonneg`).
-/

@[expose] public section

namespace ArtGallery.BP.Tmpl

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl
open ArtGallery.Irrational (HP)

/-! ### Guards and algebra -/

/-- The guard on `r_i` with value `x`. -/
noncomputable def bpInvGp (x : ℝ) : Point := ((bpInvD : ℝ) * x, 0)

/-- The guard on `r_j` with value `y` (left-oriented: abscissa `159/10 − y`). -/
noncomputable def bpInvGq (y : ℝ) : Point := ((bpInvD : ℝ) * (159 / 10 - y), (bpInvD : ℝ) / 10)

theorem bpInvD_real : (bpInvD : ℝ) = 3008974742400 := by norm_num [bpInvD]

theorem bpInvGp_mem {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) : bpInvGp x ∈ convexHull ℝ (intSet bpInvRi) := by
  have e : bpInvGp x = Geometry.lerp (intPoint (1504487371200, 0)) (intPoint (6017949484800, 0))
      ((x - 1 / 2) * (2 / 3)) := by
    simp only [bpInvGp, Geometry.lerp, intPoint, bpInvD_real]; push_cast
    ext <;> simp only <;> ring
  rw [e]; exact mem_hull_pair (by nlinarith) (by nlinarith)

theorem bpInvGq_mem {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) : bpInvGq y ∈ convexHull ℝ (intSet bpInvRj) := by
  have e : bpInvGq y = Geometry.lerp (intPoint (41824748919360, 300897474240))
      (intPoint (46338211032960, 300897474240)) ((2 - y) * (2 / 3)) := by
    simp only [bpInvGq, Geometry.lerp, intPoint, bpInvD_real]; push_cast
    ext <;> simp only <;> ring
  rw [e]; exact mem_hull_pair (by nlinarith) (by nlinarith)

theorem bpInvGp_det (x : ℝ) (z : Point) :
    det (bpInvGp x) (intPoint bpInvXi0) z = bpInvN0.val z - (bpInvD : ℝ) * x * bpInvE0.val z := by
  simp only [det, bpInvGp, intPoint, bpInvXi0, bpInvN0, bpInvE0, Irrational.HP.val]; push_cast; ring

theorem bpInvGq_det (y : ℝ) (z : Point) :
    det (bpInvGq y) (intPoint bpInvXi1) z = -bpInvC1.val z + (bpInvD : ℝ) * y * bpInvE1.val z := by
  simp only [det, bpInvGq, intPoint, bpInvXi1, bpInvC1, bpInvE1, Irrational.HP.val, bpInvD_real]
  push_cast; ring

theorem bpInvGp_det2 (x : ℝ) (z : Point) :
    det (bpInvGp x) (intPoint bpInvXi2) z = bpInvN2.val z - (bpInvD : ℝ) * x * bpInvE2.val z := by
  simp only [det, bpInvGp, intPoint, bpInvXi2, bpInvN2, bpInvE2, Irrational.HP.val]; push_cast; ring

theorem bpInvGq_det3 (y : ℝ) (z : Point) :
    det (bpInvGq y) (intPoint bpInvXi3) z = -bpInvC3.val z + (bpInvD : ℝ) * y * bpInvE3.val z := by
  simp only [det, bpInvGq, intPoint, bpInvXi3, bpInvC3, bpInvE3, Irrational.HP.val, bpInvD_real]
  push_cast; ring

/-- **The inversion identity of the umbra.** -/
theorem bpInv_umbra_identity (z : Point) :
    bpInvN0.val z * bpInvC1.val z - (bpInvD : ℝ) ^ 2 * bpInvE0.val z * bpInvE1.val z =
      1635312360 * bpInvLu.val z * det (intPoint bpInvXi0) (intPoint bpInvXi1) z := by
  simp only [det, intPoint, bpInvXi0, bpInvXi1, bpInvN0, bpInvC1, bpInvE0, bpInvE1, bpInvLu,
    Irrational.HP.val, bpInvD_real]
  push_cast; ring

/-- **The inversion identity of the nook.** -/
theorem bpInv_nook_identity (z : Point) :
    bpInvN2.val z * bpInvC3.val z - (bpInvD : ℝ) ^ 2 * bpInvE2.val z * bpInvE3.val z =
      -400129620 * bpInvLn.val z * det (intPoint bpInvXi2) (intPoint bpInvXi3) z := by
  simp only [det, intPoint, bpInvXi2, bpInvXi3, bpInvN2, bpInvC3, bpInvE2, bpInvE3, bpInvLn,
    Irrational.HP.val, bpInvD_real]
  push_cast; ring

/-! ### Signs on the zones -/

theorem bpInvZu_E0 : ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvE0.val z :=
  pos_on_hull (by decide +kernel)

theorem bpInvZu_E1 : ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvE1.val z :=
  pos_on_hull (by decide +kernel)

theorem bpInvZu_C1 : ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvC1.val z :=
  pos_on_hull (by decide +kernel)

theorem bpInvZu_F : ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < det (intPoint bpInvXi0) (intPoint bpInvXi1) z :=
  det_pos_on_hull (fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    rw [det_intPoint]
    have : ∀ z ∈ bpInvZu, 0 < idet bpInvXi0 bpInvXi1 z := by decide +kernel
    exact_mod_cast this z hz)

theorem bpInvZn_E2 : ∀ z ∈ convexHull ℝ (intSet bpInvZn), 0 < bpInvE2.val z :=
  pos_on_hull (by decide +kernel)

theorem bpInvZn_E3 : ∀ z ∈ convexHull ℝ (intSet bpInvZn), 0 < bpInvE3.val z :=
  pos_on_hull (by decide +kernel)

theorem bpInvZn_Ln : ∀ z ∈ convexHull ℝ (intSet bpInvZn), bpInvLn.val z = 0 :=
  zero_on_hull (by decide +kernel)

/-- On the nook zone, the projections of the two guards' lines are related by `x° y° = 1`. -/
theorem bpInvZn_rel {w : Point} (hw : w ∈ convexHull ℝ (intSet bpInvZn)) :
    bpInvN2.val w * bpInvC3.val w = (bpInvD : ℝ) ^ 2 * bpInvE2.val w * bpInvE3.val w := by
  have := bpInv_nook_identity w
  rw [bpInvZn_Ln w hw] at this
  linarith

/-! ### Visibility in the zones -/

section Vis

variable {P : Polygon} {a : ℕ}
variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a) (hS : SepAt P bpInvV a bpInvR)
include hP hL hC hS

theorem bpInv_sees_p_umbra {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) {z : Point}
    (hz : z ∈ convexHull ℝ (intSet bpInvZu)) :
    P.Sees (bpInvGp x) z ↔ (bpInvD : ℝ) * x * bpInvE0.val z ≤ bpInvN0.val z := by
  rw [bpInv_vis_up hP hL hC hS _ (bpInvGp_mem h0 h1) z hz, bpInvXi0_eq, bpInvGp_det]
  constructor <;> intro h <;> linarith

theorem bpInv_sees_q_umbra {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) {z : Point}
    (hz : z ∈ convexHull ℝ (intSet bpInvZu)) :
    P.Sees (bpInvGq y) z ↔ (bpInvD : ℝ) * y * bpInvE1.val z ≤ bpInvC1.val z := by
  rw [bpInv_vis_uq hP hL hC hS _ (bpInvGq_mem h0 h1) z hz, bpInvXi1_eq, bpInvGq_det]
  constructor <;> intro h <;> linarith

theorem bpInv_sees_p_nook {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) {w : Point}
    (hw : w ∈ convexHull ℝ (intSet bpInvZn)) :
    P.Sees (bpInvGp x) w ↔ bpInvN2.val w ≤ (bpInvD : ℝ) * x * bpInvE2.val w := by
  rw [bpInv_vis_np hP hL hC hS _ (bpInvGp_mem h0 h1) w hw, bpInvXi2_eq, bpInvGp_det2]
  constructor <;> intro h <;> linarith

theorem bpInv_sees_q_nook {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) {w : Point}
    (hw : w ∈ convexHull ℝ (intSet bpInvZn)) :
    P.Sees (bpInvGq y) w ↔ bpInvC3.val w ≤ (bpInvD : ℝ) * y * bpInvE3.val w := by
  rw [bpInv_vis_nq hP hL hC hS _ (bpInvGq_mem h0 h1) w hw, bpInvXi3_eq, bpInvGq_det3]
  constructor <;> intro h <;> linarith

/-- **Umbra, sufficiency.**  If `x y ≤ 1`, every point of the umbra zone on or above the axis
is seen by one of the two guards. -/
theorem bpInv_umbra_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y ≤ 1) :
    ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 ≤ bpInvLu.val z →
      P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z := by
  intro z hz hLz
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [bpInv_sees_p_umbra hP hL hC hS hx0 hx1 hz, not_le] at h1
  rw [bpInv_sees_q_umbra hP hL hC hS hy0 hy1 hz, not_le] at h2
  have e0 := bpInvZu_E0 z hz
  have e1 := bpInvZu_E1 z hz
  have c1 := bpInvZu_C1 z hz
  have f := bpInvZu_F z hz
  have hid := bpInv_umbra_identity z
  have hD : (0 : ℝ) < bpInvD := by rw [bpInvD_real]; norm_num
  set N0 := bpInvN0.val z
  set C1 := bpInvC1.val z
  set E0 := bpInvE0.val z
  set E1 := bpInvE1.val z
  set Dr := (bpInvD : ℝ)
  have hx : 0 < Dr * x * E0 := by positivity
  have hy : 0 < Dr * y * E1 := by positivity
  have s1 : N0 * C1 < (Dr * x * E0) * C1 := mul_lt_mul_of_pos_right h1 c1
  have s2 : (Dr * x * E0) * C1 < (Dr * x * E0) * (Dr * y * E1) := mul_lt_mul_of_pos_left h2 hx
  have s3 : (Dr * x * E0) * (Dr * y * E1) ≤ Dr ^ 2 * E0 * E1 := by
    have : (Dr * x * E0) * (Dr * y * E1) = (x * y) * (Dr ^ 2 * E0 * E1) := by ring
    rw [this]
    have : 0 < Dr ^ 2 * E0 * E1 := by positivity
    nlinarith
  have s4 : 0 ≤ 1635312360 * bpInvLu.val z * det (intPoint bpInvXi0) (intPoint bpInvXi1) z := by
    positivity
  nlinarith

/-- **Nook, sufficiency.**  If `x y ≥ 1`, the nook zone is seen by the two guards. -/
theorem bpInv_nook_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 ≤ x * y) :
    ∀ w ∈ convexHull ℝ (intSet bpInvZn), P.Sees (bpInvGp x) w ∨ P.Sees (bpInvGq y) w := by
  intro w hw
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [bpInv_sees_p_nook hP hL hC hS hx0 hx1 hw, not_le] at h1
  rw [bpInv_sees_q_nook hP hL hC hS hy0 hy1 hw, not_le] at h2
  have e2 := bpInvZn_E2 w hw
  have e3 := bpInvZn_E3 w hw
  have hrel := bpInvZn_rel hw
  have hD : (0 : ℝ) < bpInvD := by rw [bpInvD_real]; norm_num
  set N2 := bpInvN2.val w
  set C3 := bpInvC3.val w
  set E2 := bpInvE2.val w
  set E3 := bpInvE3.val w
  set Dr := (bpInvD : ℝ)
  have hx : 0 < Dr * x * E2 := by positivity
  have hy : 0 < Dr * y * E3 := by positivity
  have s1 : (Dr * x * E2) * (Dr * y * E3) < N2 * C3 := mul_lt_mul'' h1 h2 hx.le hy.le
  have s3 : Dr ^ 2 * E2 * E3 ≤ (Dr * x * E2) * (Dr * y * E3) := by
    have : (Dr * x * E2) * (Dr * y * E3) = (x * y) * (Dr ^ 2 * E2 * E3) := by ring
    rw [this]
    have : 0 < Dr ^ 2 * E2 * E3 := by positivity
    nlinarith
  linarith

end Vis

/-! ### The gap points -/

/-- Numerator of the crossing parameter. -/
noncomputable def bpInvNum (x y : ℝ) : ℝ := det (bpInvGq y) (intPoint bpInvXi1) (bpInvGp x)

/-- Denominator of the crossing parameter. -/
noncomputable def bpInvDen (x y : ℝ) : ℝ :=
  bpInvNum x y - det (bpInvGq y) (intPoint bpInvXi1) (intPoint bpInvXi0)

/-- The crossing point `X(x, y)` of the lines `(bpInvGp x) ξ0` and `(bpInvGq y) ξ1`. -/
noncomputable def bpInvX (x y : ℝ) : Point :=
  Geometry.lerp (bpInvGp x) (intPoint bpInvXi0) (bpInvNum x y / bpInvDen x y)

/-- The edge function of the zone edge `A B` at `X(x, y)`, times the denominator. -/
noncomputable def bpInvBil (A B : IPt) (x y : ℝ) : ℝ :=
  -det (bpInvGq y) (intPoint bpInvXi1) (intPoint bpInvXi0) * det (intPoint A) (intPoint B) (bpInvGp x) +
    bpInvNum x y * det (intPoint A) (intPoint B) (intPoint bpInvXi0)

theorem bpInvBil_hf (A B : IPt) : ∀ x y : ℝ, 9 / 4 * bpInvBil A B x y =
    (2 - x) * (2 - y) * bpInvBil A B (1 / 2) (1 / 2) + (x - 1 / 2) * (2 - y) * bpInvBil A B 2 (1 / 2) +
      (2 - x) * (y - 1 / 2) * bpInvBil A B (1 / 2) 2 + (x - 1 / 2) * (y - 1 / 2) * bpInvBil A B 2 2 := by
  intro x y
  simp only [bpInvBil, bpInvNum, det, bpInvGq, bpInvGp, intPoint]
  ring

theorem bpInvDen_hf : ∀ x y : ℝ, 9 / 4 * bpInvDen x y =
    (2 - x) * (2 - y) * bpInvDen (1 / 2) (1 / 2) + (x - 1 / 2) * (2 - y) * bpInvDen 2 (1 / 2) +
      (2 - x) * (y - 1 / 2) * bpInvDen (1 / 2) 2 + (x - 1 / 2) * (y - 1 / 2) * bpInvDen 2 2 := by
  intro x y
  simp only [bpInvDen, bpInvNum, det, bpInvGq, bpInvGp, intPoint]
  ring

/-- Unfold a corner value. -/
macro "bpInv_corner" : tactic =>
  `(tactic| (simp only [bpInvBil, bpInvDen, bpInvNum, det, bpInvGq, bpInvGp, intPoint, bpInvXi0, bpInvXi1,
    bpInvZu0, bpInvZu1, bpInvZu2, bpInvZu3, bpInvD_real]; norm_num))

theorem bpInvDen_pos {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    0 < bpInvDen x y :=
  bilin_pos bpInvDen bpInvDen_hf (by bpInv_corner) (by bpInv_corner) (by bpInv_corner) (by bpInv_corner)
    hx0 hx1 hy0 hy1

theorem bpInvBil_eq {A B : IPt} {x y : ℝ} (hd : bpInvDen x y ≠ 0) :
    bpInvDen x y * det (intPoint A) (intPoint B) (bpInvX x y) = bpInvBil A B x y := by
  rw [bpInvX, Geometry.det_lerp, bpInvBil]
  have e : bpInvDen x y - bpInvNum x y = -det (bpInvGq y) (intPoint bpInvXi1) (intPoint bpInvXi0) := by
    rw [bpInvDen]; ring
  field_simp
  rw [e]; ring

theorem bpInvX_mem {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    bpInvX x y ∈ convexHull ℝ (intSet bpInvZu) := by
  have hd := bpInvDen_pos hx0 hx1 hy0 hy1
  have edge : ∀ A B : IPt, 0 ≤ bpInvBil A B (1 / 2) (1 / 2) → 0 ≤ bpInvBil A B 2 (1 / 2) →
      0 ≤ bpInvBil A B (1 / 2) 2 → 0 ≤ bpInvBil A B 2 2 →
      0 ≤ det (intPoint A) (intPoint B) (bpInvX x y) := by
    intro A B h1 h2 h3 h4
    have := bilin_nonneg (bpInvBil A B) (bpInvBil_hf A B) h1 h2 h3 h4 hx0 hx1 hy0 hy1
    rw [← bpInvBil_eq hd.ne'] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hd
  rw [bpInvZu_eq]
  refine mem_hull_quad (A := bpInvZu0) (B := bpInvZu1) (C := bpInvZu2) (D := bpInvZu3)
    (by simp) (by simp) (by simp) (by simp) (by decide +kernel) (by decide +kernel)
    (edge _ _ (by bpInv_corner) (by bpInv_corner) (by bpInv_corner) (by bpInv_corner))
    (edge _ _ (by bpInv_corner) (by bpInv_corner) (by bpInv_corner) (by bpInv_corner))
    (edge _ _ (by bpInv_corner) (by bpInv_corner) (by bpInv_corner) (by bpInv_corner))
    (edge _ _ (by bpInv_corner) (by bpInv_corner) (by bpInv_corner) (by bpInv_corner))

theorem bpInvX_on_p (x y : ℝ) : det (bpInvGp x) (intPoint bpInvXi0) (bpInvX x y) = 0 :=
  Geometry.det_lerp_self _ _ _

theorem bpInvX_on_q {x y : ℝ} (hd : bpInvDen x y ≠ 0) :
    det (bpInvGq y) (intPoint bpInvXi1) (bpInvX x y) = 0 := by
  rw [bpInvX, Geometry.det_lerp]
  have e : det (bpInvGq y) (intPoint bpInvXi1) (bpInvGp x) = bpInvNum x y := rfl
  rw [e]
  have e2 : det (bpInvGq y) (intPoint bpInvXi1) (intPoint bpInvXi0) = bpInvNum x y - bpInvDen x y := by
    rw [bpInvDen]; ring
  rw [e2]
  field_simp
  ring

/-- Numerator of the nook projection parameter. -/
noncomputable def bpInvNumN (x : ℝ) : ℝ := det (bpInvGp x) (intPoint bpInvXi2) (intPoint bpInvZna)

/-- The value at the right end of the nook zone. -/
noncomputable def bpInvNumN' (x : ℝ) : ℝ := -det (bpInvGp x) (intPoint bpInvXi2) (intPoint bpInvZnb)

/-- The projection `π(x)` of the guard `bpInvGp x` through `ξ2` onto the nook zone. -/
noncomputable def bpInvW (x : ℝ) : Point :=
  Geometry.lerp (intPoint bpInvZna) (intPoint bpInvZnb) (bpInvNumN x / (bpInvNumN x + bpInvNumN' x))

theorem bpInvNumN_hf : ∀ x y : ℝ, 9 / 4 * (fun x (_ : ℝ) => bpInvNumN x) x y =
    (2 - x) * (2 - y) * bpInvNumN (1 / 2) + (x - 1 / 2) * (2 - y) * bpInvNumN 2 +
      (2 - x) * (y - 1 / 2) * bpInvNumN (1 / 2) + (x - 1 / 2) * (y - 1 / 2) * bpInvNumN 2 := by
  intro x y; simp only [bpInvNumN, det, bpInvGp, intPoint]; ring

theorem bpInvNumN'_hf : ∀ x y : ℝ, 9 / 4 * (fun x (_ : ℝ) => bpInvNumN' x) x y =
    (2 - x) * (2 - y) * bpInvNumN' (1 / 2) + (x - 1 / 2) * (2 - y) * bpInvNumN' 2 +
      (2 - x) * (y - 1 / 2) * bpInvNumN' (1 / 2) + (x - 1 / 2) * (y - 1 / 2) * bpInvNumN' 2 := by
  intro x y; simp only [bpInvNumN', det, bpInvGp, intPoint]; ring

/-- Unfold a nook corner value. -/
macro "bpInv_ncorner" : tactic =>
  `(tactic| (simp only [bpInvNumN, bpInvNumN', det, bpInvGp, intPoint, bpInvXi2, bpInvZna, bpInvZnb,
    bpInvD_real]; norm_num))

theorem bpInvNumN_pos {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) : 0 < bpInvNumN x :=
  bilin_pos (fun x (_ : ℝ) => bpInvNumN x) bpInvNumN_hf (by bpInv_ncorner) (by bpInv_ncorner)
    (by bpInv_ncorner) (by bpInv_ncorner) hx0 hx1 (y := 1) (by norm_num) (by norm_num)

theorem bpInvNumN'_pos {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) : 0 < bpInvNumN' x :=
  bilin_pos (fun x (_ : ℝ) => bpInvNumN' x) bpInvNumN'_hf (by bpInv_ncorner) (by bpInv_ncorner)
    (by bpInv_ncorner) (by bpInv_ncorner) hx0 hx1 (y := 1) (by norm_num) (by norm_num)

theorem bpInvW_mem {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    bpInvW x ∈ convexHull ℝ (intSet bpInvZn) := by
  have h1 := bpInvNumN_pos hx0 hx1
  have h2 := bpInvNumN'_pos hx0 hx1
  rw [bpInvZn_eq, bpInvW]
  exact mem_hull_pair (div_nonneg h1.le (by linarith))
    ((div_le_one (by linarith)).2 (by linarith))

theorem bpInvW_on_p {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    det (bpInvGp x) (intPoint bpInvXi2) (bpInvW x) = 0 := by
  have h1 := bpInvNumN_pos hx0 hx1
  have h2 := bpInvNumN'_pos hx0 hx1
  rw [bpInvW, Geometry.det_lerp]
  have e1 : det (bpInvGp x) (intPoint bpInvXi2) (intPoint bpInvZna) = bpInvNumN x := rfl
  have e2 : det (bpInvGp x) (intPoint bpInvXi2) (intPoint bpInvZnb) = -bpInvNumN' x := by
    rw [bpInvNumN']; ring
  rw [e1, e2]
  have : bpInvNumN x + bpInvNumN' x ≠ 0 := by linarith
  field_simp
  ring

/-! ### The mechanism -/

section Mech

variable {P : Polygon} {a : ℕ}
variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a) (hS : SepAt P bpInvV a bpInvR)
include hP hL hC hS

/-- **Umbra, gap.**  If `x y > 1`, a crossing point strictly above the axis is seen by neither
guard. -/
theorem bpInv_umbra_gap {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 < x * y) :
    ∃ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvLu.val z ∧ ¬ P.Sees (bpInvGp x) z ∧
      ¬ P.Sees (bpInvGq y) z := by
  have hy : 0 < y := by linarith
  set x' := (x + 1 / y) / 2 with hx'
  have hyi : 1 / y < x := by rw [div_lt_iff₀ hy]; linarith
  have hyi0 : 1 / 2 ≤ 1 / y := by rw [div_le_div_iff₀ (by norm_num) hy]; linarith
  have hyi1 : 1 / y ≤ 2 := by rw [div_le_iff₀ hy]; linarith
  have hx'0 : 1 / 2 ≤ x' := by rw [hx']; linarith
  have hx'1 : x' ≤ 2 := by rw [hx']; linarith
  have hx'x : x' < x := by rw [hx']; linarith
  have hx'pos : 0 < x' := by linarith
  have hx'y : 1 < x' * y := by
    have : 1 / y < x' := by rw [hx']; linarith
    rw [div_lt_iff₀ hy] at this; linarith
  set y' := (y + 1 / x') / 2 with hy'
  have hxi : 1 / x' < y := by rw [div_lt_iff₀ hx'pos]; linarith
  have hxi0 : 1 / 2 ≤ 1 / x' := by rw [div_le_div_iff₀ (by norm_num) hx'pos]; linarith
  have hy'0 : 1 / 2 ≤ y' := by rw [hy']; linarith
  have hy'1 : y' ≤ 2 := by rw [hy']; linarith
  have hy'y : y' < y := by rw [hy']; linarith
  have hx'y' : 1 < x' * y' := by
    have : 1 / x' < y' := by rw [hy']; linarith
    rw [div_lt_iff₀ hx'pos] at this; linarith
  have hd := bpInvDen_pos hx'0 hx'1 hy'0 hy'1
  set z := bpInvX x' y'
  have hz := bpInvX_mem hx'0 hx'1 hy'0 hy'1
  have hp0 := bpInvX_on_p x' y'
  have hq0 := bpInvX_on_q hd.ne'
  rw [bpInvGp_det] at hp0
  rw [bpInvGq_det] at hq0
  have e0 := bpInvZu_E0 z hz
  have e1 := bpInvZu_E1 z hz
  have f := bpInvZu_F z hz
  have hD : (0 : ℝ) < bpInvD := by rw [bpInvD_real]; norm_num
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · have hid := bpInv_umbra_identity z
    have hN : bpInvN0.val z = (bpInvD : ℝ) * x' * bpInvE0.val z := by linarith
    have hC1 : bpInvC1.val z = (bpInvD : ℝ) * y' * bpInvE1.val z := by linarith
    rw [hN, hC1] at hid
    have : 0 < 1635312360 * bpInvLu.val z * det (intPoint bpInvXi0) (intPoint bpInvXi1) z := by
      rw [← hid]
      have : (bpInvD : ℝ) * x' * bpInvE0.val z * ((bpInvD : ℝ) * y' * bpInvE1.val z) -
          (bpInvD : ℝ) ^ 2 * bpInvE0.val z * bpInvE1.val z =
          (x' * y' - 1) * ((bpInvD : ℝ) ^ 2 * bpInvE0.val z * bpInvE1.val z) := by ring
      rw [this]
      have : 0 < (bpInvD : ℝ) ^ 2 * bpInvE0.val z * bpInvE1.val z := by positivity
      have : 0 < x' * y' - 1 := by linarith
      positivity
    by_contra hneg
    push Not at hneg
    have : 1635312360 * bpInvLu.val z * det (intPoint bpInvXi0) (intPoint bpInvXi1) z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) f.le
    linarith
  · rw [bpInv_sees_p_umbra hP hL hC hS hx0 hx1 hz]
    have : (bpInvD : ℝ) * x' * bpInvE0.val z < (bpInvD : ℝ) * x * bpInvE0.val z := by
      have := mul_pos hD e0
      nlinarith
    linarith
  · rw [bpInv_sees_q_umbra hP hL hC hS hy0 hy1 hz]
    have : (bpInvD : ℝ) * y' * bpInvE1.val z < (bpInvD : ℝ) * y * bpInvE1.val z := by
      have := mul_pos hD e1
      nlinarith
    linarith

/-- **The umbra of the inversion gadget (Lemma 49).**  For `x, y ∈ [1/2, 2]` the points of the
umbra zone strictly above the axis are all seen by the guards `bpInvGp x`, `bpInvGq y` iff
`x y ≤ 1`. -/
theorem bpInv_umbra_iff {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    (∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvLu.val z →
      P.Sees (bpInvGp x) z ∨ P.Sees (bpInvGq y) z) ↔ x * y ≤ 1 := by
  constructor
  · intro h
    by_contra hxy
    push Not at hxy
    obtain ⟨z, hz, hLz, h1, h2⟩ := bpInv_umbra_gap hP hL hC hS hx0 hx1 hy0 hy1 hxy
    rcases h z hz hLz with h' | h'
    exacts [h1 h', h2 h']
  · intro hxy z hz hLz
    exact bpInv_umbra_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z hz hLz.le

/-- **Nook, gap.**  If `x y < 1`, the projection of a guard position between the two values is
seen by neither guard. -/
theorem bpInv_nook_gap {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y < 1) :
    ∃ w ∈ convexHull ℝ (intSet bpInvZn), ¬ P.Sees (bpInvGp x) w ∧ ¬ P.Sees (bpInvGq y) w := by
  have hy : 0 < y := by linarith
  set x' := (x + 1 / y) / 2 with hx'
  have hyi : x < 1 / y := by rw [lt_div_iff₀ hy]; linarith
  have hyi1 : 1 / y ≤ 2 := by rw [div_le_iff₀ hy]; linarith
  have hx'0 : 1 / 2 ≤ x' := by rw [hx']; linarith
  have hx'1 : x' ≤ 2 := by rw [hx']; linarith
  have hx'x : x < x' := by rw [hx']; linarith
  have hx'pos : 0 < x' := by linarith
  have hx'y : x' * y < 1 := by
    have : x' < 1 / y := by rw [hx']; linarith
    rw [lt_div_iff₀ hy] at this; linarith
  set w := bpInvW x'
  have hw := bpInvW_mem hx'0 hx'1
  have hp0 := bpInvW_on_p hx'0 hx'1
  rw [bpInvGp_det2] at hp0
  have e2 := bpInvZn_E2 w hw
  have e3 := bpInvZn_E3 w hw
  have hrel := bpInvZn_rel hw
  have hD : (0 : ℝ) < bpInvD := by rw [bpInvD_real]; norm_num
  have hN : bpInvN2.val w = (bpInvD : ℝ) * x' * bpInvE2.val w := by linarith
  refine ⟨w, hw, ?_, ?_⟩
  · rw [bpInv_sees_p_nook hP hL hC hS hx0 hx1 hw, hN]
    have := mul_pos hD e2
    nlinarith
  · rw [bpInv_sees_q_nook hP hL hC hS hy0 hy1 hw]
    rw [hN] at hrel
    -- `C3 = D E3 / x'`
    have hC3 : x' * bpInvC3.val w = (bpInvD : ℝ) * bpInvE3.val w := by
      have h2 : 0 < (bpInvD : ℝ) * bpInvE2.val w := mul_pos hD e2
      have : ((bpInvD : ℝ) * bpInvE2.val w) * (x' * bpInvC3.val w) =
          ((bpInvD : ℝ) * bpInvE2.val w) * ((bpInvD : ℝ) * bpInvE3.val w) := by
        linear_combination hrel
      exact mul_left_cancel₀ h2.ne' this
    intro hle
    have h3 : 0 < (bpInvD : ℝ) * bpInvE3.val w := mul_pos hD e3
    have : x' * bpInvC3.val w ≤ x' * ((bpInvD : ℝ) * y * bpInvE3.val w) :=
      mul_le_mul_of_nonneg_left hle hx'pos.le
    rw [hC3] at this
    nlinarith

/-- **The nook of the inversion gadget (Lemma 50).**  For `x, y ∈ [1/2, 2]` the nook zone is
seen by the guards `bpInvGp x`, `bpInvGq y` iff `x y ≥ 1`. -/
theorem bpInv_nook_iff {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    (∀ w ∈ convexHull ℝ (intSet bpInvZn), P.Sees (bpInvGp x) w ∨ P.Sees (bpInvGq y) w) ↔
      1 ≤ x * y := by
  constructor
  · intro h
    by_contra hxy
    push Not at hxy
    obtain ⟨w, hw, h1, h2⟩ := bpInv_nook_gap hP hL hC hS hx0 hx1 hy0 hy1 hxy
    rcases h w hw with h' | h'
    exacts [h1 h', h2 h']
  · exact bpInv_nook_cover hP hL hC hS hx0 hx1 hy0 hy1

end Mech

end ArtGallery.BP.Tmpl

end
