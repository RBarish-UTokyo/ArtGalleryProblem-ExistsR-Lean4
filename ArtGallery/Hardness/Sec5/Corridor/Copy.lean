module

public import ArtGallery.Hardness.Sec5.Corridor.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Section 5: corridors — the exact copy algebra (Lemmas 27/28 generalised)

A *copy pair* consists of two shadow corners `k0` (base side) and `k1` (gadget side) and two
horizontal guard segments, parametrised by the offset `t`:
`p t = a0 + (s0·t, 0)` (base) and `q t = a1 + (s1·t, 0)` (gadget); equal offsets mean equal
values (in the corridor `s0 = 1`, `s1 = 1/S`, `t ∈ [0, 3/2]`).

**Perspective-axis identity** (`axis_identity`).  If `k0, k1` have the same height, then for
all `z`, `t`, `t'`
`s1·det(p t, k0, z) − s0·det(q t', k1, z) = L(z) + s0 s1 (z.y − k0.y)(t' − t)`,
where `L(z) = s1·det(a0, k0, z) − s0·det(a1, k1, z)` is affine.  Hence the crossing point
`X t t'` of the lines `(p t) k0` and `(q t') k1` lies on the line `L = 0` (the *axis*) iff
`t = t'`, strictly above it (`L > 0`) iff `t > t'`, and the axis is the line through
`f0 = X ℓ ℓ` and `f1 = X 0 0` (`L_eq_zero_of_det2`, `L_mul_eq_det2`): the composite projection
`s_σ → axis → r_τ` preserves the offset (paper Lemma 27, `lemma27`).

**Sides.**  A base guard `p t` sees (through `k0`) the points with `det(p t, k0, z) ≥ 0` above
the floor, a gadget guard `q t'` (through `k1`) those with `det(q t', k1, z) ≤ 0` (umbra
situation, `UmbraCovered`); for a nook (shadow corners at the nook mouth) the sides are reversed
(`NookCovered`).  With `v₀(z), v₁(z)` the offsets of the projections of `z` through `k0`, `k1`
(`det(p t, k0, z) = s0 (z.y − k0.y)(v₀ − t)`):
* `umbra_covered`: `t ≤ t'` ⇒ every point on or above the axis (above the floor) is covered;
* `umbra_gap`: the crossing point `X v₀ v₁` with `t' < v₁ ≤ v₀ < t` is covered by neither guard
  and lies on or above the axis (`L = s0 s1 w (v₀ − v₁)`);
* `umbra_iff`: covering the region `{X v₀ v₁ | 0 ≤ v₁ ≤ v₀ ≤ ℓ}` above the critical segment
  `⟺ t ≤ t'`  ("umbra covered iff value(q) ≥ value(p)");
* `nook_covered`, `nook_gap`, `nook_iff`: covering the axis points `X v v`, `v ∈ [0, ℓ]`,
  `⟺ t' ≤ t` ("nook covered iff value(q) ≤ value(p)");
* `X_diag_mem`: `X v v` lies on the critical segment `[f1, f0]` for `v ∈ [0, ℓ]`.

Everything is stated over an arbitrary ordered field.  The corridor instances (shadow corners
`c0, c1` for the umbra and `z0, z1` for the nook) are in `Corridor/CopyCorridor.lean`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

/-- A copy pair: shadow corners `k0` (base side), `k1` (gadget side), left endpoints `a0`, `a1`
and scales `s0`, `s1` of the two horizontal guard segments (`p t = a0 + (s0 t, 0)`,
`q t = a1 + (s1 t, 0)`). -/
structure CopyPair (K : Type*) where
  /-- Shadow corner on the base side. -/
  k0 : K × K
  /-- Shadow corner on the gadget side. -/
  k1 : K × K
  /-- Left endpoint of the base segment. -/
  a0 : K × K
  /-- Left endpoint of the gadget (receiver) segment. -/
  a1 : K × K
  /-- Scale of the base segment. -/
  s0 : K
  /-- Scale of the gadget segment. -/
  s1 : K

namespace CopyPair

section Field

variable {K : Type*} [Field K] (C : CopyPair K)

/-- The base guard at offset `t`. -/
def p (t : K) : K × K := (C.a0.1 + C.s0 * t, C.a0.2)

/-- The gadget guard at offset `t`. -/
def q (t : K) : K × K := (C.a1.1 + C.s1 * t, C.a1.2)

/-- The axis function `L(z) = s1·det(a0, k0, z) − s0·det(a1, k1, z)` (affine in `z`). -/
def L (z : K × K) : K := C.s1 * det2 C.a0 C.k0 z - C.s0 * det2 C.a1 C.k1 z

/-- The height of `z` above the shadow corners. -/
def w (z : K × K) : K := z.2 - C.k0.2

/-- The crossing point of the lines `(p t₀) k0` and `(q t₁) k1`. -/
def X (t₀ t₁ : K) : K × K := lineInter (C.p t₀) C.k0 (C.q t₁) C.k1

/-- The denominator of the crossing point. -/
def G (t₀ t₁ : K) : K :=
  (C.k0.1 - (C.p t₀).1) * (C.k1.2 - C.a1.2) + ((C.q t₁).1 - C.k1.1) * (C.k0.2 - C.a0.2)

/-- `z` is covered in the umbra situation: the base guard `p t` sees past `k0`
(`det(p t, k0, z) ≥ 0`) or the gadget guard `q t'` sees past `k1` (`det(q t', k1, z) ≤ 0`). -/
def UmbraCovered (t t' : K) [LE K] (z : K × K) : Prop :=
  0 ≤ det2 (C.p t) C.k0 z ∨ det2 (C.q t') C.k1 z ≤ 0

/-- `z` is covered in the nook situation (sides reversed: the guards look into the nook through
the mouth corners `k0`, `k1`). -/
def NookCovered (t t' : K) [LE K] (z : K × K) : Prop :=
  det2 (C.p t) C.k0 z ≤ 0 ∨ 0 ≤ det2 (C.q t') C.k1 z

/-- Moving the base guard changes the side by a multiple of the height. -/
theorem det2_p (t : K) (z : K × K) :
    det2 (C.p t) C.k0 z = det2 C.a0 C.k0 z - C.s0 * t * C.w z := by
  simp only [det2, p, w]; ring

/-- Moving the gadget guard changes the side by a multiple of the height. -/
theorem det2_q (t : K) (z : K × K) :
    det2 (C.q t) C.k1 z = det2 C.a1 C.k1 z - C.s1 * t * (z.2 - C.k1.2) := by
  simp only [det2, q]; ring

/-- Comparing two base guards. -/
theorem det2_p_sub (t v : K) (z : K × K) :
    det2 (C.p t) C.k0 z = det2 (C.p v) C.k0 z + C.s0 * (v - t) * C.w z := by
  rw [det2_p, det2_p]; ring

/-- Comparing two gadget guards. -/
theorem det2_q_sub (hk : C.k0.2 = C.k1.2) (t v : K) (z : K × K) :
    det2 (C.q t) C.k1 z = det2 (C.q v) C.k1 z + C.s1 * (v - t) * C.w z := by
  rw [det2_q, det2_q, w, hk]; ring

/-- **Perspective-axis identity.** -/
theorem axis_identity (hk : C.k0.2 = C.k1.2) (t t' : K) (z : K × K) :
    C.s1 * det2 (C.p t) C.k0 z - C.s0 * det2 (C.q t') C.k1 z =
      C.L z + C.s0 * C.s1 * C.w z * (t' - t) := by
  rw [det2_p, det2_q, L, w, hk]; ring

/-- A point on the lines `(p t) k0` and `(q t') k1` has `L = s0 s1 w (t − t')`. -/
theorem L_of_on_lines (hk : C.k0.2 = C.k1.2) {t t' : K} {z : K × K}
    (h₀ : det2 (C.p t) C.k0 z = 0) (h₁ : det2 (C.q t') C.k1 z = 0) :
    C.L z = C.s0 * C.s1 * C.w z * (t - t') := by
  have := C.axis_identity hk t t' z
  rw [h₀, h₁] at this
  linear_combination -this

/-- The denominator of `lineInter` for the crossing point is `G`. -/
theorem lineDen_eq (t₀ t₁ : K) : lineDen (C.p t₀) C.k0 (C.q t₁) C.k1 = C.G t₀ t₁ := by
  simp only [lineDen, G, p, q]; ring

/-- The crossing point lies on `(p t₀) k0`. -/
theorem det2_X_left (t₀ t₁ : K) : det2 (C.p t₀) C.k0 (C.X t₀ t₁) = 0 :=
  det2_lineInter_left _ _ _ _

/-- The crossing point lies on `(q t₁) k1`. -/
theorem det2_X_right {t₀ t₁ : K} (hG : C.G t₀ t₁ ≠ 0) : det2 (C.q t₁) C.k1 (C.X t₀ t₁) = 0 :=
  det2_lineInter_right _ _ _ _ (by rwa [lineDen_eq])

/-- The axis function at a crossing point. -/
theorem L_X (hk : C.k0.2 = C.k1.2) {t₀ t₁ : K} (hG : C.G t₀ t₁ ≠ 0) :
    C.L (C.X t₀ t₁) = C.s0 * C.s1 * C.w (C.X t₀ t₁) * (t₀ - t₁) :=
  C.L_of_on_lines hk (C.det2_X_left t₀ t₁) (C.det2_X_right hG)

/-- **Lemma 27 (generalised).** Crossing points of equal offsets lie on the axis. -/
theorem L_X_diag (hk : C.k0.2 = C.k1.2) {t : K} (hG : C.G t t ≠ 0) : C.L (C.X t t) = 0 := by
  rw [C.L_X hk hG, sub_self, mul_zero]

/-- **Lemma 27 (value transfer).** If a point `e` of the axis (off the floor line) is the
projection of `p v` through `k0`, then it is the projection of `q v` through `k1`: the
composite projection `s_σ → axis → r_τ` preserves offsets. -/
theorem lemma27 (hk : C.k0.2 = C.k1.2) (hs0 : C.s0 ≠ 0) {v : K} {e : K × K}
    (he : C.L e = 0) (h₀ : det2 (C.p v) C.k0 e = 0) : det2 (C.q v) C.k1 e = 0 := by
  have h := C.axis_identity hk v v e
  rw [h₀, he] at h
  have : C.s0 * det2 (C.q v) C.k1 e = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left hs0

/-- The factor `λ` of the crossing point `X t₀ t₁ = k0 + λ (k0 − p t₀)`. -/
def lam (t₀ t₁ : K) : K := (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) / C.G t₀ t₁

/-- The crossing point in closed form: `X t₀ t₁ = k0 + λ (k0 − p t₀)`,
`λ = (k1.y − a1.y)(k1.x − k0.x)/G`. -/
theorem X_eq (hk : C.k0.2 = C.k1.2) {t₀ t₁ : K} (hG : C.G t₀ t₁ ≠ 0) :
    C.X t₀ t₁ = (C.k0.1 + C.lam t₀ t₁ * (C.k0.1 - (C.p t₀).1),
      C.k0.2 + C.lam t₀ t₁ * (C.k0.2 - C.a0.2)) := by
  symm
  apply eq_lineInter (by rwa [lineDen_eq])
  · generalize C.lam t₀ t₁ = μ
    simp only [det2, p]
    ring
  · have key : ∀ μ : K, det2 (C.q t₁) C.k1
        (C.k0.1 + μ * (C.k0.1 - (C.p t₀).1), C.k0.2 + μ * (C.k0.2 - C.a0.2)) =
        det2 (C.q t₁) C.k1 C.k0 + μ * ((C.k1.1 - (C.q t₁).1) * (C.k0.2 - C.a0.2) -
          (C.k0.1 - (C.p t₀).1) * (C.k1.2 - (C.q t₁).2)) := by
      intro μ; simp only [det2]; ring
    have hpoly : det2 (C.q t₁) C.k1 C.k0 * C.G t₀ t₁ + (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) *
        ((C.k1.1 - (C.q t₁).1) * (C.k0.2 - C.a0.2) -
          (C.k0.1 - (C.p t₀).1) * (C.k1.2 - (C.q t₁).2)) = 0 := by
      simp only [det2, G, p, q]
      rw [hk]
      ring
    rw [key, lam]
    generalize C.G t₀ t₁ = g at hG hpoly
    field_simp
    linear_combination hpoly

/-- The height of a crossing point above the shadow corners: `w = λ (k0.y − a0.y)`. -/
theorem w_X (hk : C.k0.2 = C.k1.2) {t₀ t₁ : K} (hG : C.G t₀ t₁ ≠ 0) :
    C.w (C.X t₀ t₁) = C.lam t₀ t₁ * (C.k0.2 - C.a0.2) := by
  rw [w, C.X_eq hk hG]; ring

/-- Side of `z` with respect to `(p t) k0` in terms of a reference line `(p v) k0` through
`z`: `det(p t, k0, z) = s0 w (v − t)`. -/
theorem det2_p_of_on (v t : K) {z : K × K} (hz : det2 (C.p v) C.k0 z = 0) :
    det2 (C.p t) C.k0 z = C.s0 * (v - t) * C.w z := by
  rw [C.det2_p_sub t v, hz, zero_add]

/-- Side of `z` with respect to `(q t') k1` in terms of a reference line `(q v) k1` through
`z`. -/
theorem det2_q_of_on (hk : C.k0.2 = C.k1.2) (v t : K) {z : K × K}
    (hz : det2 (C.q v) C.k1 z = 0) : det2 (C.q t) C.k1 z = C.s1 * (v - t) * C.w z := by
  rw [C.det2_q_sub hk t v, hz, zero_add]

/-- **The axis is a line**: an affine function of the form `L` vanishing at two distinct
points `f₀, f₁` vanishes on the whole line `f₀ f₁`. -/
theorem L_eq_zero_of_det2 {f₀ f₁ z : K × K} (h₀ : C.L f₀ = 0) (h₁ : C.L f₁ = 0) (hne : f₀ ≠ f₁)
    (hz : det2 f₀ f₁ z = 0) : C.L z = 0 := by
  set α := -C.s1 * (C.k0.2 - C.a0.2) + C.s0 * (C.k1.2 - C.a1.2)
  set β := C.s1 * (C.k0.1 - C.a0.1) - C.s0 * (C.k1.1 - C.a1.1)
  have e1 : (f₁.1 - f₀.1) * C.L z = 0 := by
    simp only [L, det2] at h₀ h₁ hz ⊢
    linear_combination (f₁.1 - f₀.1) * h₀ + (z.1 - f₀.1) * (h₁ - h₀) + β * hz
  have e2 : (f₁.2 - f₀.2) * C.L z = 0 := by
    simp only [L, det2] at h₀ h₁ hz ⊢
    linear_combination (f₁.2 - f₀.2) * h₀ + (z.2 - f₀.2) * (h₁ - h₀) - α * hz
  by_cases hx : f₁.1 - f₀.1 = 0
  · have hy : f₁.2 - f₀.2 ≠ 0 := by
      intro hy
      apply hne
      ext
      · linear_combination -hx
      · linear_combination -hy
    exact (mul_eq_zero.mp e2).resolve_left hy
  · exact (mul_eq_zero.mp e1).resolve_left hx

end Field

/-! ### Ordered fields: sides and coverage -/

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (C : CopyPair K)

/-- The standing hypotheses of a copy pair: shadow corners at equal height, positive scales. -/
structure Hyp : Prop where
  /-- The shadow corners have the same height. -/
  hk : C.k0.2 = C.k1.2
  /-- Positive base scale. -/
  hs0 : 0 < C.s0
  /-- Positive gadget scale. -/
  hs1 : 0 < C.s1

/-- Admissible configuration for offsets in `[0, ℓ]`: the base segment lies left of `k0` and
below it, the gadget segment right of `k1` and below it, and `k0` is left of `k1`. -/
structure Adm (ℓ : K) : Prop where
  /-- The offset range is nonempty. -/
  hℓ : 0 ≤ ℓ
  /-- The base segment ends left of `k0`. -/
  hp : (C.p ℓ).1 < C.k0.1
  /-- `k0` is left of `k1`. -/
  hk01 : C.k0.1 < C.k1.1
  /-- The gadget segment starts right of `k1`. -/
  hq : C.k1.1 < (C.q 0).1
  /-- The base segment is below `k0`. -/
  hy0 : C.a0.2 < C.k0.2
  /-- The gadget segment is below `k1`. -/
  hy1 : C.a1.2 < C.k1.2

variable {C}

/-- In an admissible configuration the crossing denominator is positive. -/
theorem G_pos (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) {t₀ t₁ : K} (h₀ : t₀ ≤ ℓ) (h₁ : 0 ≤ t₁) :
    0 < C.G t₀ t₁ := by
  obtain ⟨_, hp, hk01, hq, hy0, hy1⟩ := hA
  have hp' : (C.p t₀).1 < C.k0.1 := by
    simp only [p] at hp ⊢; nlinarith [hC.hs0]
  have hq' : C.k1.1 < (C.q t₁).1 := by
    simp only [q] at hq ⊢; nlinarith [hC.hs1]
  simp only [G]
  have := mul_pos (sub_pos.mpr hp') (sub_pos.mpr hy1)
  have := mul_pos (sub_pos.mpr hq') (sub_pos.mpr hy0)
  linarith

/-- In an admissible configuration crossing points lie strictly above the shadow corners. -/
theorem w_X_pos (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) {t₀ t₁ : K} (h₀ : t₀ ≤ ℓ) (h₁ : 0 ≤ t₁) :
    0 < C.w (C.X t₀ t₁) := by
  have hG := G_pos hC hA h₀ h₁
  rw [C.w_X hC.hk hG.ne', lam]
  have := sub_pos.mpr hA.hy0
  have := sub_pos.mpr hA.hy1
  have := sub_pos.mpr hA.hk01
  positivity

/-- **Umbra, sufficiency.** If `t ≤ t'` (value of the gadget guard at least the value of the
base guard), every point on or above the axis and above the floor is covered. -/
theorem umbra_covered (hC : C.Hyp) {t t' : K} (htt : t ≤ t') {z : K × K} (hw : 0 < C.w z)
    (hL : 0 ≤ C.L z) : C.UmbraCovered t t' z := by
  by_contra hcon
  simp only [UmbraCovered, not_or, not_le] at hcon
  obtain ⟨h₀, h₁⟩ := hcon
  have hid := C.axis_identity hC.hk t t' z
  have hs := mul_pos hC.hs0 hC.hs1
  have : 0 ≤ C.s0 * C.s1 * C.w z * (t' - t) := by
    have := mul_pos hs hw
    exact mul_nonneg this.le (sub_nonneg.mpr htt)
  nlinarith [mul_pos hC.hs1 (neg_pos.mpr h₀), mul_pos hC.hs0 h₁]

/-- **Umbra, gap.** A point on the lines `(p v₀) k0` and `(q v₁) k1` above the floor with
`t' < v₁ ≤ v₀ < t` is covered by neither guard, and lies on or above the axis. -/
theorem umbra_gap (hC : C.Hyp) {t t' v₀ v₁ : K} {z : K × K} (hw : 0 < C.w z)
    (h₀ : det2 (C.p v₀) C.k0 z = 0) (h₁ : det2 (C.q v₁) C.k1 z = 0) (hv₀ : v₀ < t)
    (hv₁ : t' < v₁) (hv : v₁ ≤ v₀) :
    ¬ C.UmbraCovered t t' z ∧ 0 ≤ C.L z ∧ C.L z = C.s0 * C.s1 * C.w z * (v₀ - v₁) := by
  have hL := C.L_of_on_lines hC.hk h₀ h₁
  refine ⟨?_, ?_, hL⟩
  · simp only [UmbraCovered, not_or, not_le]
    rw [C.det2_p_of_on v₀ t h₀, C.det2_q_of_on hC.hk v₁ t' h₁]
    constructor
    · have := mul_pos hC.hs0 hw
      nlinarith
    · have := mul_pos hC.hs1 hw
      nlinarith
  · rw [hL]
    have := mul_pos (mul_pos hC.hs0 hC.hs1) hw
    nlinarith

/-- **Umbra (Lemma 28, umbra half).** For offsets `t, t' ∈ [0, ℓ]` in an admissible
configuration: all points `X v₀ v₁` (`0 ≤ v₁ ≤ v₀ ≤ ℓ`; the region on and just above the
critical segment `[f1, f0]`) are covered iff `t ≤ t'`. -/
theorem umbra_iff (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) {t t' : K} (ht : t ≤ ℓ) (ht' : 0 ≤ t') :
    (∀ v₀ v₁, 0 ≤ v₁ → v₁ ≤ v₀ → v₀ ≤ ℓ → C.UmbraCovered t t' (C.X v₀ v₁)) ↔ t ≤ t' := by
  constructor
  · intro hall
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    set v := (t + t') / 2
    have hv1 : t' < v := by simp only [v]; linarith
    have hv2 : v < t := by simp only [v]; linarith
    have hG := G_pos hC hA (t₀ := v) (t₁ := v) (by linarith) (by linarith)
    have := umbra_gap hC (w_X_pos hC hA (by linarith) (by linarith)) (C.det2_X_left v v)
      (C.det2_X_right hG.ne') hv2 hv1 le_rfl
    exact this.1 (hall v v (by linarith) le_rfl (by linarith))
  · intro htt v₀ v₁ h₁ hv h₀
    have hG := G_pos hC hA h₀ h₁
    have hw := w_X_pos hC hA h₀ h₁
    apply umbra_covered hC htt hw
    rw [C.L_X hC.hk hG.ne']
    have := mul_pos (mul_pos hC.hs0 hC.hs1) hw
    nlinarith

/-- **Nook, sufficiency.** If `t' ≤ t` (value of the gadget guard at most the value of the
base guard), every point on or below the axis and above the mouth line is covered. -/
theorem nook_covered (hC : C.Hyp) {t t' : K} (htt : t' ≤ t) {z : K × K} (hw : 0 < C.w z)
    (hL : C.L z ≤ 0) : C.NookCovered t t' z := by
  by_contra hcon
  simp only [NookCovered, not_or, not_le] at hcon
  obtain ⟨h₀, h₁⟩ := hcon
  have hid := C.axis_identity hC.hk t t' z
  have hs := mul_pos hC.hs0 hC.hs1
  have : C.s0 * C.s1 * C.w z * (t' - t) ≤ 0 := by
    have := mul_pos hs hw
    exact mul_nonpos_of_nonneg_of_nonpos this.le (sub_nonpos.mpr htt)
  nlinarith [mul_pos hC.hs1 h₀, mul_pos hC.hs0 (neg_pos.mpr h₁)]

/-- **Nook, gap.** The axis point `X v v` (`t < v < t'`) is covered by neither guard. -/
theorem nook_gap (hC : C.Hyp) {t t' v : K} {z : K × K} (hw : 0 < C.w z)
    (h₀ : det2 (C.p v) C.k0 z = 0) (h₁ : det2 (C.q v) C.k1 z = 0) (hv₀ : t < v)
    (hv₁ : v < t') : ¬ C.NookCovered t t' z ∧ C.L z = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [NookCovered, not_or, not_le]
    rw [C.det2_p_of_on v t h₀, C.det2_q_of_on hC.hk v t' h₁]
    constructor
    · have := mul_pos hC.hs0 hw
      nlinarith
    · have := mul_pos hC.hs1 hw
      nlinarith
  · rw [C.L_of_on_lines hC.hk h₀ h₁, sub_self, mul_zero]

/-- **Nook (Lemma 28, nook half).** For offsets `t, t' ∈ [0, ℓ]` in an admissible
configuration: all axis points `X v v` (`v ∈ [0, ℓ]`, the critical segment) are covered iff
`t' ≤ t`. -/
theorem nook_iff (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) {t t' : K} (ht : 0 ≤ t) (ht' : t' ≤ ℓ) :
    (∀ v, 0 ≤ v → v ≤ ℓ → C.NookCovered t t' (C.X v v)) ↔ t' ≤ t := by
  constructor
  · intro hall
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    set v := (t + t') / 2
    have hv1 : t < v := by simp only [v]; linarith
    have hv2 : v < t' := by simp only [v]; linarith
    have hG := G_pos hC hA (t₀ := v) (t₁ := v) (by linarith) (by linarith)
    have := nook_gap hC (w_X_pos hC hA (by linarith) (by linarith)) (C.det2_X_left v v)
      (C.det2_X_right hG.ne') hv1 hv2
    exact this.1 (hall v (by linarith) (by linarith))
  · intro htt v h₀ h₁
    have hG := G_pos hC hA h₁ h₀
    exact nook_covered hC htt (w_X_pos hC hA h₁ h₀) (C.L_X_diag hC.hk hG.ne').le

/-- **The critical segment.** For `v ∈ [0, ℓ]` the axis point `X v v` lies on the segment from
`f1 = X 0 0` to `f0 = X ℓ ℓ` (in the parametrisation of `ArtGallery.segment`). -/
theorem X_diag_mem (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) (hℓ : 0 < ℓ) {v : K} (h₀ : 0 ≤ v)
    (h₁ : v ≤ ℓ) :
    ∃ α : K, 0 ≤ α ∧ α ≤ 1 ∧
      C.X v v = ((C.X 0 0).1 + α * ((C.X ℓ ℓ).1 - (C.X 0 0).1),
        (C.X 0 0).2 + α * ((C.X ℓ ℓ).2 - (C.X 0 0).2)) := by
  have hG0 := G_pos hC hA hA.hℓ le_rfl (t₀ := 0)
  have hGl := G_pos hC hA le_rfl hA.hℓ
  have hGv := G_pos hC hA h₁ h₀
  have hGlin : C.G v v * ℓ = (ℓ - v) * C.G 0 0 + v * C.G ℓ ℓ := by
    simp only [G, p, q]; ring
  have hD : 0 < (ℓ - v) * C.G 0 0 + v * C.G ℓ ℓ := by rw [← hGlin]; positivity
  have hGv' : C.G v v = ((ℓ - v) * C.G 0 0 + v * C.G ℓ ℓ) / ℓ := by
    rw [← hGlin]; field_simp
  refine ⟨v * C.G ℓ ℓ / ((ℓ - v) * C.G 0 0 + v * C.G ℓ ℓ), by positivity, ?_, ?_⟩
  · rw [div_le_one hD]
    have : 0 ≤ (ℓ - v) * C.G 0 0 := mul_nonneg (by linarith) hG0.le
    linarith
  · rw [C.X_eq hC.hk hGv.ne', C.X_eq hC.hk hG0.ne', C.X_eq hC.hk hGl.ne']
    simp only [lam]
    rw [hGv']
    simp only [p]
    have hD' := hD.ne'
    have hG0' := hG0.ne'
    have hGl' := hGl.ne'
    generalize C.G 0 0 = g0 at hD' hG0' hGl' ⊢
    generalize C.G ℓ ℓ = g1 at hD' hG0' hGl' ⊢
    simp only [Prod.mk.injEq]
    constructor
    · field_simp
      ring
    · field_simp
      ring

/-- The critical segment runs from west to east: `f0.x < f1.x`. -/
theorem X_fst_lt (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) (hℓ : 0 < ℓ) :
    (C.X ℓ ℓ).1 < (C.X 0 0).1 := by
  have hG0 := G_pos hC hA hA.hℓ le_rfl (t₀ := 0)
  have hGl := G_pos hC hA le_rfl hA.hℓ
  rw [C.X_eq hC.hk hGl.ne', C.X_eq hC.hk hG0.ne']
  simp only [lam, div_mul_eq_mul_div]
  have hn0 : 0 < C.k0.1 - (C.p 0).1 := by
    have := hA.hp; simp only [p] at this ⊢; nlinarith [hC.hs0]
  have hm0 : 0 < (C.q 0).1 - C.k1.1 := sub_pos.mpr hA.hq
  have hc : 0 < (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) :=
    mul_pos (sub_pos.mpr hA.hy1) (sub_pos.mpr hA.hk01)
  rw [add_lt_add_iff_left, div_lt_div_iff₀ hGl hG0]
  have key : (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) * (C.k0.1 - (C.p 0).1) * C.G ℓ ℓ -
      (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) * (C.k0.1 - (C.p ℓ).1) * C.G 0 0 =
      (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * ℓ *
        ((C.k0.1 - (C.p 0).1) * C.s1 + C.s0 * ((C.q 0).1 - C.k1.1)) := by
    simp only [G, p, q]; ring
  have : 0 < (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * ℓ *
      ((C.k0.1 - (C.p 0).1) * C.s1 + C.s0 * ((C.q 0).1 - C.k1.1)) := by
    have := sub_pos.mpr hA.hy0
    have := mul_pos hn0 hC.hs1
    have := mul_pos hC.hs0 hm0
    have := hC.hs0
    positivity
  linarith

/-- **Sign of the axis function.** `L` is a positive multiple of `det(f0, f1, ·)` where
`f0 = X ℓ ℓ`, `f1 = X 0 0`:
`L(z)·ℓ (k1.x − k0.x)(k0.y − a0.y)(k1.y − a1.y) = G(0,0) G(ℓ,ℓ) det(f0, f1, z)`.
So "above the axis" (`L > 0`) is "left of the eastward critical segment `f0 → f1`". -/
theorem L_mul_eq_det2 (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) (z : K × K) :
    C.L z * (ℓ * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * (C.k1.2 - C.a1.2)) =
      C.G 0 0 * C.G ℓ ℓ * det2 (C.X ℓ ℓ) (C.X 0 0) z := by
  have hG0 := (G_pos hC hA hA.hℓ le_rfl (t₀ := 0)).ne'
  have hGl := (G_pos hC hA le_rfl hA.hℓ).ne'
  rw [C.X_eq hC.hk hGl, C.X_eq hC.hk hG0]
  simp only [lam]
  set c := (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1)
  set n0 := C.k0.1 - (C.p 0).1
  set nl := C.k0.1 - (C.p ℓ).1
  set m := C.k0.2 - C.a0.2
  have key : ∀ g0 g1 : K, g0 ≠ 0 → g1 ≠ 0 →
      g0 * g1 * det2 (C.k0.1 + c / g1 * nl, C.k0.2 + c / g1 * m)
        (C.k0.1 + c / g0 * n0, C.k0.2 + c / g0 * m) z =
      c * ((g1 * n0 - g0 * nl) * (z.2 - C.k0.2) - (z.1 - C.k0.1) * (g1 * m - g0 * m) -
        c * (n0 * m - m * nl)) := by
    intro g0 g1 h0 h1
    simp only [det2]
    field_simp
    ring
  rw [key _ _ hG0 hGl]
  obtain ⟨⟨K0, h0⟩, ⟨K1, h1⟩, ⟨A0, y0⟩, ⟨A1, y1⟩, s0, s1⟩ := C
  have hk := hC.hk
  simp only at hk
  subst hk
  simp only [c, n0, nl, m, G, p, q, L, det2]
  ring

/-- Above the axis iff left of `f0 → f1`. -/
theorem L_pos_iff (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) (hℓ : 0 < ℓ) (z : K × K) :
    0 < C.L z ↔ 0 < det2 (C.X ℓ ℓ) (C.X 0 0) z := by
  have h := C.L_mul_eq_det2 hC hA z
  have hc : 0 < ℓ * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * (C.k1.2 - C.a1.2) := by
    have := sub_pos.mpr hA.hk01
    have := sub_pos.mpr hA.hy0
    have := sub_pos.mpr hA.hy1
    positivity
  have hg : 0 < C.G 0 0 * C.G ℓ ℓ :=
    mul_pos (G_pos hC hA hA.hℓ le_rfl) (G_pos hC hA le_rfl hA.hℓ)
  constructor
  · intro hL
    have : 0 < C.G 0 0 * C.G ℓ ℓ * det2 (C.X ℓ ℓ) (C.X 0 0) z := by rw [← h]; positivity
    exact pos_of_mul_pos_right this hg.le
  · intro hd
    have : 0 < C.L z * (ℓ * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * (C.k1.2 - C.a1.2)) := by
      rw [h]; positivity
    exact pos_of_mul_pos_left this hc.le

/-- On or above the axis iff on or left of `f0 → f1`. -/
theorem L_nonneg_iff (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) (hℓ : 0 < ℓ) (z : K × K) :
    0 ≤ C.L z ↔ 0 ≤ det2 (C.X ℓ ℓ) (C.X 0 0) z := by
  have h := C.L_mul_eq_det2 hC hA z
  have hc : 0 < ℓ * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * (C.k1.2 - C.a1.2) := by
    have := sub_pos.mpr hA.hk01
    have := sub_pos.mpr hA.hy0
    have := sub_pos.mpr hA.hy1
    positivity
  have hg : 0 < C.G 0 0 * C.G ℓ ℓ :=
    mul_pos (G_pos hC hA hA.hℓ le_rfl) (G_pos hC hA le_rfl hA.hℓ)
  constructor
  · intro hL
    have : 0 ≤ C.G 0 0 * C.G ℓ ℓ * det2 (C.X ℓ ℓ) (C.X 0 0) z := by rw [← h]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hg
  · intro hd
    have : 0 ≤ C.L z * (ℓ * (C.k1.1 - C.k0.1) * (C.k0.2 - C.a0.2) * (C.k1.2 - C.a1.2)) := by
      rw [h]; positivity
    exact nonneg_of_mul_nonneg_left this hc

end Ordered

end CopyPair

end ArtGallery.Sec5.Corridor

end
