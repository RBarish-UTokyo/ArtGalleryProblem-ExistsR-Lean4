module

public import ArtGallery.Hardness.Sec5.Templates.InvData

/-!
# Section 5: the inversion template — the mechanism (paper Lemmas 49/50)

Integer template coordinates (`InvData.lean`, `T = Z / invD`).  For values `x, y ∈ [1/2, 2]` the
guard of `r_i` is `invGp x = (D x, 0)` and the guard of `r_j` is
`invGq y = (D (159/10 − y), D/10)`.  For an arbitrary simple counter-clockwise polygon `P`
containing the template chain (`ChainAt P invV a`) whose other edges avoid `invR`
(`SepAt P invV a invR`):

* **umbra** (`inv_umbra_iff`): the points of the umbra zone `conv invZu` strictly above the axis
  `f0 f1` (`invLu > 0`) are all seen by the two guards iff `x y ≤ 1`; for `x y ≤ 1` even the
  points on the axis are covered (`inv_umbra_cover`), for `x y > 1` an explicit crossing point
  `invX x' y'` is seen by neither (`inv_umbra_gap`);
* **nook** (`inv_nook_iff`): the nook zone `conv invZn` (a sub-segment of the nook top edge
  containing the critical segment `[f2, f3]`, with the corrected `f2`, see
  `docs/section5/05_gadgets.md`) is covered iff `x y ≥ 1`.

Proof: the visibility characterisations of `InvData.lean` (`inv_vis_up`, …) reduce coverage to
sign conditions; with `det(p, ξ0, z) = N0 − D x E0` and `det(q, ξ1, z) = −C1 + D y E1` the
*inversion identity* `8892400 (N0 C1 − D² E0 E1) = K · Lu · det(ξ0, ξ1, z)` (`inv_umbra_identity`,
the conic through `ξ0`, `ξ1` of the crossings for `x y = 1` splits into the axis and the floor
line) gives the umbra; the nook identity (`inv_nook_identity`) vanishes on the nook axis.  The
gap points are explicit crossing points; their membership in the zones is reduced to the four
corners of the value square by bilinear interpolation (`bilin_nonneg`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)

/-! ### Guards and algebra -/

/-- The guard on `r_i` with value `x`. -/
noncomputable def invGp (x : ℝ) : Point := ((invD : ℝ) * x, 0)

/-- The guard on `r_j` with value `y` (left-oriented: abscissa `159/10 − y`). -/
noncomputable def invGq (y : ℝ) : Point := ((invD : ℝ) * (159 / 10 - y), (invD : ℝ) / 10)

theorem invD_real : (invD : ℝ) = 501495790400 := by norm_num [invD]

theorem invGp_mem {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) : invGp x ∈ convexHull ℝ (intSet invRi) := by
  have e : invGp x = Geometry.lerp (intPoint (250747895200, 0)) (intPoint (1002991580800, 0))
      ((x - 1 / 2) * (2 / 3)) := by
    simp only [invGp, Geometry.lerp, intPoint, invD_real]; push_cast
    ext <;> simp only <;> ring
  rw [e]; exact mem_hull_pair (by nlinarith) (by nlinarith)

theorem invGq_mem {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) : invGq y ∈ convexHull ℝ (intSet invRj) := by
  have e : invGq y = Geometry.lerp (intPoint (6970791486560, 50149579040))
      (intPoint (7723035172160, 50149579040)) ((2 - y) * (2 / 3)) := by
    simp only [invGq, Geometry.lerp, intPoint, invD_real]; push_cast
    ext <;> simp only <;> ring
  rw [e]; exact mem_hull_pair (by nlinarith) (by nlinarith)

theorem invGp_det (x : ℝ) (z : Point) :
    det (invGp x) (intPoint invXi0) z = invN0.val z - (invD : ℝ) * x * invE0.val z := by
  simp only [det, invGp, intPoint, invXi0, invN0, invE0, Irrational.HP.val]; push_cast; ring

theorem invGq_det (y : ℝ) (z : Point) :
    det (invGq y) (intPoint invXi1) z = -invC1.val z + (invD : ℝ) * y * invE1.val z := by
  simp only [det, invGq, intPoint, invXi1, invC1, invE1, Irrational.HP.val, invD_real]
  push_cast; ring

theorem invGp_det2 (x : ℝ) (z : Point) :
    det (invGp x) (intPoint invXi2) z = invN2.val z - (invD : ℝ) * x * invE2.val z := by
  simp only [det, invGp, intPoint, invXi2, invN2, invE2, Irrational.HP.val]; push_cast; ring

theorem invGq_det3 (y : ℝ) (z : Point) :
    det (invGq y) (intPoint invXi3) z = -invC3.val z + (invD : ℝ) * y * invE3.val z := by
  simp only [det, invGq, intPoint, invXi3, invC3, invE3, Irrational.HP.val, invD_real]
  push_cast; ring

/-- **The inversion identity of the umbra.** -/
theorem inv_umbra_identity (z : Point) :
    8892400 * (invN0.val z * invC1.val z - (invD : ℝ) ^ 2 * invE0.val z * invE1.val z) =
      2423641938344000 * invLu.val z * det (intPoint invXi0) (intPoint invXi1) z := by
  simp only [det, intPoint, invXi0, invXi1, invN0, invC1, invE0, invE1, invLu,
    Irrational.HP.val, invD_real]
  push_cast; ring

/-- **The inversion identity of the nook.** -/
theorem inv_nook_identity (z : Point) :
    2175800 * (invN2.val z * invC3.val z - (invD : ℝ) ^ 2 * invE2.val z * invE3.val z) =
      -145100337866000 * invLn.val z * det (intPoint invXi2) (intPoint invXi3) z := by
  simp only [det, intPoint, invXi2, invXi3, invN2, invC3, invE2, invE3, invLn,
    Irrational.HP.val, invD_real]
  push_cast; ring

/-! ### Signs on the zones -/

theorem invZu_E0 : ∀ z ∈ convexHull ℝ (intSet invZu), 0 < invE0.val z :=
  pos_on_hull (by decide +kernel)

theorem invZu_E1 : ∀ z ∈ convexHull ℝ (intSet invZu), 0 < invE1.val z :=
  pos_on_hull (by decide +kernel)

theorem invZu_C1 : ∀ z ∈ convexHull ℝ (intSet invZu), 0 < invC1.val z :=
  pos_on_hull (by decide +kernel)

theorem invZu_F : ∀ z ∈ convexHull ℝ (intSet invZu), 0 < det (intPoint invXi0) (intPoint invXi1) z :=
  det_pos_on_hull (fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    rw [det_intPoint]
    have : ∀ z ∈ invZu, 0 < idet invXi0 invXi1 z := by decide +kernel
    exact_mod_cast this z hz)

theorem invZn_E2 : ∀ z ∈ convexHull ℝ (intSet invZn), 0 < invE2.val z :=
  pos_on_hull (by decide +kernel)

theorem invZn_E3 : ∀ z ∈ convexHull ℝ (intSet invZn), 0 < invE3.val z :=
  pos_on_hull (by decide +kernel)

theorem invZn_Ln : ∀ z ∈ convexHull ℝ (intSet invZn), invLn.val z = 0 :=
  zero_on_hull (by decide +kernel)

/-- On the nook zone, the projections of the two guards' lines are related by `x° y° = 1`. -/
theorem invZn_rel {w : Point} (hw : w ∈ convexHull ℝ (intSet invZn)) :
    invN2.val w * invC3.val w = (invD : ℝ) ^ 2 * invE2.val w * invE3.val w := by
  have := inv_nook_identity w
  rw [invZn_Ln w hw] at this
  linarith

/-! ### Visibility in the zones -/

section Vis

variable {P : Polygon} {a : ℕ}
variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) (hS : SepAt P invV a invR)
include hP hL hC hS

theorem inv_sees_p_umbra {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) {z : Point}
    (hz : z ∈ convexHull ℝ (intSet invZu)) :
    P.Sees (invGp x) z ↔ (invD : ℝ) * x * invE0.val z ≤ invN0.val z := by
  rw [inv_vis_up hP hL hC hS _ (invGp_mem h0 h1) z hz, invXi0_eq, invGp_det]
  constructor <;> intro h <;> linarith

theorem inv_sees_q_umbra {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) {z : Point}
    (hz : z ∈ convexHull ℝ (intSet invZu)) :
    P.Sees (invGq y) z ↔ (invD : ℝ) * y * invE1.val z ≤ invC1.val z := by
  rw [inv_vis_uq hP hL hC hS _ (invGq_mem h0 h1) z hz, invXi1_eq, invGq_det]
  constructor <;> intro h <;> linarith

theorem inv_sees_p_nook {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 2) {w : Point}
    (hw : w ∈ convexHull ℝ (intSet invZn)) :
    P.Sees (invGp x) w ↔ invN2.val w ≤ (invD : ℝ) * x * invE2.val w := by
  rw [inv_vis_np hP hL hC hS _ (invGp_mem h0 h1) w hw, invXi2_eq, invGp_det2]
  constructor <;> intro h <;> linarith

theorem inv_sees_q_nook {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y ≤ 2) {w : Point}
    (hw : w ∈ convexHull ℝ (intSet invZn)) :
    P.Sees (invGq y) w ↔ invC3.val w ≤ (invD : ℝ) * y * invE3.val w := by
  rw [inv_vis_nq hP hL hC hS _ (invGq_mem h0 h1) w hw, invXi3_eq, invGq_det3]
  constructor <;> intro h <;> linarith

/-- **Umbra, sufficiency.**  If `x y ≤ 1`, every point of the umbra zone on or above the axis
is seen by one of the two guards. -/
theorem inv_umbra_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y ≤ 1) :
    ∀ z ∈ convexHull ℝ (intSet invZu), 0 ≤ invLu.val z →
      P.Sees (invGp x) z ∨ P.Sees (invGq y) z := by
  intro z hz hLz
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [inv_sees_p_umbra hP hL hC hS hx0 hx1 hz, not_le] at h1
  rw [inv_sees_q_umbra hP hL hC hS hy0 hy1 hz, not_le] at h2
  have e0 := invZu_E0 z hz
  have e1 := invZu_E1 z hz
  have c1 := invZu_C1 z hz
  have f := invZu_F z hz
  have hid := inv_umbra_identity z
  have hD : (0 : ℝ) < invD := by rw [invD_real]; norm_num
  set N0 := invN0.val z
  set C1 := invC1.val z
  set E0 := invE0.val z
  set E1 := invE1.val z
  set Dr := (invD : ℝ)
  have hx : 0 < Dr * x * E0 := by positivity
  have hy : 0 < Dr * y * E1 := by positivity
  have s1 : N0 * C1 < (Dr * x * E0) * C1 := mul_lt_mul_of_pos_right h1 c1
  have s2 : (Dr * x * E0) * C1 < (Dr * x * E0) * (Dr * y * E1) := mul_lt_mul_of_pos_left h2 hx
  have s3 : (Dr * x * E0) * (Dr * y * E1) ≤ Dr ^ 2 * E0 * E1 := by
    have : (Dr * x * E0) * (Dr * y * E1) = (x * y) * (Dr ^ 2 * E0 * E1) := by ring
    rw [this]
    have : 0 < Dr ^ 2 * E0 * E1 := by positivity
    nlinarith
  have s4 : 0 ≤ 2423641938344000 * invLu.val z * det (intPoint invXi0) (intPoint invXi1) z := by
    positivity
  nlinarith

/-- **Nook, sufficiency.**  If `x y ≥ 1`, the nook zone is seen by the two guards. -/
theorem inv_nook_cover {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 ≤ x * y) :
    ∀ w ∈ convexHull ℝ (intSet invZn), P.Sees (invGp x) w ∨ P.Sees (invGq y) w := by
  intro w hw
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [inv_sees_p_nook hP hL hC hS hx0 hx1 hw, not_le] at h1
  rw [inv_sees_q_nook hP hL hC hS hy0 hy1 hw, not_le] at h2
  have e2 := invZn_E2 w hw
  have e3 := invZn_E3 w hw
  have hrel := invZn_rel hw
  have hD : (0 : ℝ) < invD := by rw [invD_real]; norm_num
  set N2 := invN2.val w
  set C3 := invC3.val w
  set E2 := invE2.val w
  set E3 := invE3.val w
  set Dr := (invD : ℝ)
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
noncomputable def invNum (x y : ℝ) : ℝ := det (invGq y) (intPoint invXi1) (invGp x)

/-- Denominator of the crossing parameter. -/
noncomputable def invDen (x y : ℝ) : ℝ :=
  invNum x y - det (invGq y) (intPoint invXi1) (intPoint invXi0)

/-- The crossing point `X(x, y)` of the lines `(invGp x) ξ0` and `(invGq y) ξ1`. -/
noncomputable def invX (x y : ℝ) : Point :=
  Geometry.lerp (invGp x) (intPoint invXi0) (invNum x y / invDen x y)

/-- The edge function of the zone edge `A B` at `X(x, y)`, times the denominator. -/
noncomputable def invBil (A B : IPt) (x y : ℝ) : ℝ :=
  -det (invGq y) (intPoint invXi1) (intPoint invXi0) * det (intPoint A) (intPoint B) (invGp x) +
    invNum x y * det (intPoint A) (intPoint B) (intPoint invXi0)

theorem invBil_hf (A B : IPt) : ∀ x y : ℝ, 9 / 4 * invBil A B x y =
    (2 - x) * (2 - y) * invBil A B (1 / 2) (1 / 2) + (x - 1 / 2) * (2 - y) * invBil A B 2 (1 / 2) +
      (2 - x) * (y - 1 / 2) * invBil A B (1 / 2) 2 + (x - 1 / 2) * (y - 1 / 2) * invBil A B 2 2 := by
  intro x y
  simp only [invBil, invNum, det, invGq, invGp, intPoint]
  ring

theorem invDen_hf : ∀ x y : ℝ, 9 / 4 * invDen x y =
    (2 - x) * (2 - y) * invDen (1 / 2) (1 / 2) + (x - 1 / 2) * (2 - y) * invDen 2 (1 / 2) +
      (2 - x) * (y - 1 / 2) * invDen (1 / 2) 2 + (x - 1 / 2) * (y - 1 / 2) * invDen 2 2 := by
  intro x y
  simp only [invDen, invNum, det, invGq, invGp, intPoint]
  ring

/-- Unfold a corner value. -/
macro "inv_corner" : tactic =>
  `(tactic| (simp only [invBil, invDen, invNum, det, invGq, invGp, intPoint, invXi0, invXi1,
    invZu0, invZu1, invZu2, invZu3, invD_real]; norm_num))

theorem invDen_pos {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    0 < invDen x y :=
  bilin_pos invDen invDen_hf (by inv_corner) (by inv_corner) (by inv_corner) (by inv_corner)
    hx0 hx1 hy0 hy1

theorem invBil_eq {A B : IPt} {x y : ℝ} (hd : invDen x y ≠ 0) :
    invDen x y * det (intPoint A) (intPoint B) (invX x y) = invBil A B x y := by
  rw [invX, Geometry.det_lerp, invBil]
  have e : invDen x y - invNum x y = -det (invGq y) (intPoint invXi1) (intPoint invXi0) := by
    rw [invDen]; ring
  field_simp
  rw [e]; ring

theorem invX_mem {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    invX x y ∈ convexHull ℝ (intSet invZu) := by
  have hd := invDen_pos hx0 hx1 hy0 hy1
  have edge : ∀ A B : IPt, 0 ≤ invBil A B (1 / 2) (1 / 2) → 0 ≤ invBil A B 2 (1 / 2) →
      0 ≤ invBil A B (1 / 2) 2 → 0 ≤ invBil A B 2 2 →
      0 ≤ det (intPoint A) (intPoint B) (invX x y) := by
    intro A B h1 h2 h3 h4
    have := bilin_nonneg (invBil A B) (invBil_hf A B) h1 h2 h3 h4 hx0 hx1 hy0 hy1
    rw [← invBil_eq hd.ne'] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hd
  rw [invZu_eq]
  refine mem_hull_quad (A := invZu0) (B := invZu1) (C := invZu2) (D := invZu3)
    (by simp) (by simp) (by simp) (by simp) (by decide +kernel) (by decide +kernel)
    (edge _ _ (by inv_corner) (by inv_corner) (by inv_corner) (by inv_corner))
    (edge _ _ (by inv_corner) (by inv_corner) (by inv_corner) (by inv_corner))
    (edge _ _ (by inv_corner) (by inv_corner) (by inv_corner) (by inv_corner))
    (edge _ _ (by inv_corner) (by inv_corner) (by inv_corner) (by inv_corner))

theorem invX_on_p (x y : ℝ) : det (invGp x) (intPoint invXi0) (invX x y) = 0 :=
  Geometry.det_lerp_self _ _ _

theorem invX_on_q {x y : ℝ} (hd : invDen x y ≠ 0) :
    det (invGq y) (intPoint invXi1) (invX x y) = 0 := by
  rw [invX, Geometry.det_lerp]
  have e : det (invGq y) (intPoint invXi1) (invGp x) = invNum x y := rfl
  rw [e]
  have e2 : det (invGq y) (intPoint invXi1) (intPoint invXi0) = invNum x y - invDen x y := by
    rw [invDen]; ring
  rw [e2]
  field_simp
  ring

/-- Numerator of the nook projection parameter. -/
noncomputable def invNumN (x : ℝ) : ℝ := det (invGp x) (intPoint invXi2) (intPoint invZna)

/-- The value at the right end of the nook zone. -/
noncomputable def invNumN' (x : ℝ) : ℝ := -det (invGp x) (intPoint invXi2) (intPoint invZnb)

/-- The projection `π(x)` of the guard `invGp x` through `ξ2` onto the nook zone. -/
noncomputable def invW (x : ℝ) : Point :=
  Geometry.lerp (intPoint invZna) (intPoint invZnb) (invNumN x / (invNumN x + invNumN' x))

theorem invNumN_hf : ∀ x y : ℝ, 9 / 4 * (fun x (_ : ℝ) => invNumN x) x y =
    (2 - x) * (2 - y) * invNumN (1 / 2) + (x - 1 / 2) * (2 - y) * invNumN 2 +
      (2 - x) * (y - 1 / 2) * invNumN (1 / 2) + (x - 1 / 2) * (y - 1 / 2) * invNumN 2 := by
  intro x y; simp only [invNumN, det, invGp, intPoint]; ring

theorem invNumN'_hf : ∀ x y : ℝ, 9 / 4 * (fun x (_ : ℝ) => invNumN' x) x y =
    (2 - x) * (2 - y) * invNumN' (1 / 2) + (x - 1 / 2) * (2 - y) * invNumN' 2 +
      (2 - x) * (y - 1 / 2) * invNumN' (1 / 2) + (x - 1 / 2) * (y - 1 / 2) * invNumN' 2 := by
  intro x y; simp only [invNumN', det, invGp, intPoint]; ring

/-- Unfold a nook corner value. -/
macro "inv_ncorner" : tactic =>
  `(tactic| (simp only [invNumN, invNumN', det, invGp, intPoint, invXi2, invZna, invZnb,
    invD_real]; norm_num))

theorem invNumN_pos {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) : 0 < invNumN x :=
  bilin_pos (fun x (_ : ℝ) => invNumN x) invNumN_hf (by inv_ncorner) (by inv_ncorner)
    (by inv_ncorner) (by inv_ncorner) hx0 hx1 (y := 1) (by norm_num) (by norm_num)

theorem invNumN'_pos {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) : 0 < invNumN' x :=
  bilin_pos (fun x (_ : ℝ) => invNumN' x) invNumN'_hf (by inv_ncorner) (by inv_ncorner)
    (by inv_ncorner) (by inv_ncorner) hx0 hx1 (y := 1) (by norm_num) (by norm_num)

theorem invW_mem {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    invW x ∈ convexHull ℝ (intSet invZn) := by
  have h1 := invNumN_pos hx0 hx1
  have h2 := invNumN'_pos hx0 hx1
  rw [invZn_eq, invW]
  exact mem_hull_pair (div_nonneg h1.le (by linarith))
    ((div_le_one (by linarith)).2 (by linarith))

theorem invW_on_p {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) :
    det (invGp x) (intPoint invXi2) (invW x) = 0 := by
  have h1 := invNumN_pos hx0 hx1
  have h2 := invNumN'_pos hx0 hx1
  rw [invW, Geometry.det_lerp]
  have e1 : det (invGp x) (intPoint invXi2) (intPoint invZna) = invNumN x := rfl
  have e2 : det (invGp x) (intPoint invXi2) (intPoint invZnb) = -invNumN' x := by
    rw [invNumN']; ring
  rw [e1, e2]
  have : invNumN x + invNumN' x ≠ 0 := by linarith
  field_simp
  ring

/-! ### The mechanism -/

section Mech

variable {P : Polygon} {a : ℕ}
variable (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) (hS : SepAt P invV a invR)
include hP hL hC hS

/-- **Umbra, gap.**  If `x y > 1`, a crossing point strictly above the axis is seen by neither
guard. -/
theorem inv_umbra_gap {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : 1 < x * y) :
    ∃ z ∈ convexHull ℝ (intSet invZu), 0 < invLu.val z ∧ ¬ P.Sees (invGp x) z ∧
      ¬ P.Sees (invGq y) z := by
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
  have hd := invDen_pos hx'0 hx'1 hy'0 hy'1
  set z := invX x' y'
  have hz := invX_mem hx'0 hx'1 hy'0 hy'1
  have hp0 := invX_on_p x' y'
  have hq0 := invX_on_q hd.ne'
  rw [invGp_det] at hp0
  rw [invGq_det] at hq0
  have e0 := invZu_E0 z hz
  have e1 := invZu_E1 z hz
  have f := invZu_F z hz
  have hD : (0 : ℝ) < invD := by rw [invD_real]; norm_num
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · have hid := inv_umbra_identity z
    have hN : invN0.val z = (invD : ℝ) * x' * invE0.val z := by linarith
    have hC1 : invC1.val z = (invD : ℝ) * y' * invE1.val z := by linarith
    rw [hN, hC1] at hid
    have : 0 < 2423641938344000 * invLu.val z * det (intPoint invXi0) (intPoint invXi1) z := by
      rw [← hid]
      have : (invD : ℝ) * x' * invE0.val z * ((invD : ℝ) * y' * invE1.val z) -
          (invD : ℝ) ^ 2 * invE0.val z * invE1.val z =
          (x' * y' - 1) * ((invD : ℝ) ^ 2 * invE0.val z * invE1.val z) := by ring
      rw [this]
      have : 0 < (invD : ℝ) ^ 2 * invE0.val z * invE1.val z := by positivity
      have : 0 < x' * y' - 1 := by linarith
      positivity
    by_contra hneg
    push Not at hneg
    have : 2423641938344000 * invLu.val z * det (intPoint invXi0) (intPoint invXi1) z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) f.le
    linarith
  · rw [inv_sees_p_umbra hP hL hC hS hx0 hx1 hz]
    have : (invD : ℝ) * x' * invE0.val z < (invD : ℝ) * x * invE0.val z := by
      have := mul_pos hD e0
      nlinarith
    linarith
  · rw [inv_sees_q_umbra hP hL hC hS hy0 hy1 hz]
    have : (invD : ℝ) * y' * invE1.val z < (invD : ℝ) * y * invE1.val z := by
      have := mul_pos hD e1
      nlinarith
    linarith

/-- **The umbra of the inversion gadget (Lemma 49).**  For `x, y ∈ [1/2, 2]` the points of the
umbra zone strictly above the axis are all seen by the guards `invGp x`, `invGq y` iff
`x y ≤ 1`. -/
theorem inv_umbra_iff {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    (∀ z ∈ convexHull ℝ (intSet invZu), 0 < invLu.val z →
      P.Sees (invGp x) z ∨ P.Sees (invGq y) z) ↔ x * y ≤ 1 := by
  constructor
  · intro h
    by_contra hxy
    push Not at hxy
    obtain ⟨z, hz, hLz, h1, h2⟩ := inv_umbra_gap hP hL hC hS hx0 hx1 hy0 hy1 hxy
    rcases h z hz hLz with h' | h'
    exacts [h1 h', h2 h']
  · intro hxy z hz hLz
    exact inv_umbra_cover hP hL hC hS hx0 hx1 hy0 hy1 hxy z hz hLz.le

/-- **Nook, gap.**  If `x y < 1`, the projection of a guard position between the two values is
seen by neither guard. -/
theorem inv_nook_gap {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (hxy : x * y < 1) :
    ∃ w ∈ convexHull ℝ (intSet invZn), ¬ P.Sees (invGp x) w ∧ ¬ P.Sees (invGq y) w := by
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
  set w := invW x'
  have hw := invW_mem hx'0 hx'1
  have hp0 := invW_on_p hx'0 hx'1
  rw [invGp_det2] at hp0
  have e2 := invZn_E2 w hw
  have e3 := invZn_E3 w hw
  have hrel := invZn_rel hw
  have hD : (0 : ℝ) < invD := by rw [invD_real]; norm_num
  have hN : invN2.val w = (invD : ℝ) * x' * invE2.val w := by linarith
  refine ⟨w, hw, ?_, ?_⟩
  · rw [inv_sees_p_nook hP hL hC hS hx0 hx1 hw, hN]
    have := mul_pos hD e2
    nlinarith
  · rw [inv_sees_q_nook hP hL hC hS hy0 hy1 hw]
    rw [hN] at hrel
    -- `C3 = D E3 / x'`
    have hC3 : x' * invC3.val w = (invD : ℝ) * invE3.val w := by
      have h2 : 0 < (invD : ℝ) * invE2.val w := mul_pos hD e2
      have : ((invD : ℝ) * invE2.val w) * (x' * invC3.val w) =
          ((invD : ℝ) * invE2.val w) * ((invD : ℝ) * invE3.val w) := by
        linear_combination hrel
      exact mul_left_cancel₀ h2.ne' this
    intro hle
    have h3 : 0 < (invD : ℝ) * invE3.val w := mul_pos hD e3
    have : x' * invC3.val w ≤ x' * ((invD : ℝ) * y * invE3.val w) :=
      mul_le_mul_of_nonneg_left hle hx'pos.le
    rw [hC3] at this
    nlinarith

/-- **The nook of the inversion gadget (Lemma 50).**  For `x, y ∈ [1/2, 2]` the nook zone is
seen by the guards `invGp x`, `invGq y` iff `x y ≥ 1`. -/
theorem inv_nook_iff {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    (∀ w ∈ convexHull ℝ (intSet invZn), P.Sees (invGp x) w ∨ P.Sees (invGq y) w) ↔
      1 ≤ x * y := by
  constructor
  · intro h
    by_contra hxy
    push Not at hxy
    obtain ⟨w, hw, h1, h2⟩ := inv_nook_gap hP hL hC hS hx0 hx1 hy0 hy1 hxy
    rcases h w hw with h' | h'
    exacts [h1 h', h2 h']
  · exact inv_nook_cover hP hL hC hS hx0 hx1 hy0 hy1

end Mech

end ArtGallery.Sec5.Tmpl

end
