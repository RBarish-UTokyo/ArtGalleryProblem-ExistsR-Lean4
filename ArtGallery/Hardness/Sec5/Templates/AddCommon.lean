module

public import ArtGallery.Hardness.Sec5.Templates.Tools
public import ArtGallery.Hardness.Sec5.Corridor.Copy
public import ArtGallery.Vis.StationaryGuard

/-!
# Section 5: addition-type templates — common mechanism lemmas

Abstract forms of the two mechanisms of the addition-type templates (`Add ge`, `Add le`,
`Add orient`, `docs/section5/05_gadgets.md`), stated for an arbitrary polygon `P` and a zone `Z`
on which the visibility of the three guards is characterised by the side of a line through a
shadow corner (the certificates of `Add*Cert.lean`):

* **`Γ` (paper Lemma 41).**  The guards `A` (on `r'_i`, corner `e_i`), `B` (on `r_j`, corner
  `e_j`) and `C` (on `r_l` or the stationary guard `p`, corner `e_l`) satisfy the *projection
  identity* `det(A, e_i, z) + det(B, e_j, z) − det(C, e_l, z) = (z.y − h)(C.x − A.x − B.x)`
  (the corners at height `h`, `A`, `B` at height `0`, `C` at `−h`, `e_l` the midpoint of
  `e_j e_i`).  Hence above height `h` every point is seen when `C.x ≤ A.x + B.x`
  (`gamma_cover`), and the crossing point of the lines through the shifted guards
  `A + (δ, 0)`, `B + (δ, 0)` is seen by none of them when `2δ < C.x − A.x − B.x`
  (`gamma_gap`).
* **Weak-copy nook.**  The nook of the pair `(r_i, r'_i)` is a copy pair
  (`Corridor.CopyPair`, `Corridor/Copy.lean`): with the visibility characterisations, the nook
  zone is covered iff the value on `r'_i` is at most the value on `r_i` (`copyNook_iff`).

Also: guards on segments (`segGuard`), bilinear interpolation on an arbitrary square
(`bilin_nonneg_box`, `bilin_pos_box`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert

/-! ### Guards on segments -/

/-- The guard with value `u ∈ [1/2, 2]` on the right-oriented guard segment `[A, B]`
(`A` the left end, value `1/2`; `B` the right end, value `2`). -/
noncomputable def segGuard (A B : IPt) (u : ℝ) : Point :=
  Geometry.lerp (intPoint A) (intPoint B) ((u - 1 / 2) * (2 / 3))

theorem segGuard_mem {A B : IPt} {u : ℝ} (h0 : 1 / 2 ≤ u) (h1 : u ≤ 2) :
    segGuard A B u ∈ convexHull ℝ (intSet [A, B]) :=
  mem_hull_pair (by nlinarith) (by nlinarith)

/-! ### Bilinear interpolation on a square -/

theorem bilin_nonneg_box {lo hi : ℝ} (hlh : lo < hi) (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, (hi - lo) ^ 2 * f x y = (hi - x) * (hi - y) * f lo lo +
      (x - lo) * (hi - y) * f hi lo + (hi - x) * (y - lo) * f lo hi + (x - lo) * (y - lo) * f hi hi)
    (h00 : 0 ≤ f lo lo) (h10 : 0 ≤ f hi lo) (h01 : 0 ≤ f lo hi) (h11 : 0 ≤ f hi hi) {x y : ℝ}
    (hx0 : lo ≤ x) (hx1 : x ≤ hi) (hy0 : lo ≤ y) (hy1 : y ≤ hi) : 0 ≤ f x y := by
  have := hf x y
  have a1 : 0 ≤ (hi - x) * (hi - y) := mul_nonneg (by linarith) (by linarith)
  have a2 : 0 ≤ (x - lo) * (hi - y) := mul_nonneg (by linarith) (by linarith)
  have a3 : 0 ≤ (hi - x) * (y - lo) := mul_nonneg (by linarith) (by linarith)
  have a4 : 0 ≤ (x - lo) * (y - lo) := mul_nonneg (by linarith) (by linarith)
  have hpos : 0 < (hi - lo) ^ 2 := by have : 0 < hi - lo := by linarith
                                      positivity
  have : 0 ≤ (hi - lo) ^ 2 * f x y := by
    rw [this]
    have := mul_nonneg a1 h00; have := mul_nonneg a2 h10; have := mul_nonneg a3 h01
    have := mul_nonneg a4 h11; linarith
  exact nonneg_of_mul_nonneg_right (by linarith) hpos

theorem bilin_pos_box {lo hi : ℝ} (hlh : lo < hi) (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, (hi - lo) ^ 2 * f x y = (hi - x) * (hi - y) * f lo lo +
      (x - lo) * (hi - y) * f hi lo + (hi - x) * (y - lo) * f lo hi + (x - lo) * (y - lo) * f hi hi)
    (h00 : 0 < f lo lo) (h10 : 0 < f hi lo) (h01 : 0 < f lo hi) (h11 : 0 < f hi hi) {x y : ℝ}
    (hx0 : lo ≤ x) (hx1 : x ≤ hi) (hy0 : lo ≤ y) (hy1 : y ≤ hi) : 0 < f x y := by
  set m := min (min (f lo lo) (f hi lo)) (min (f lo hi) (f hi hi))
  have hm : 0 < m := lt_min (lt_min h00 h10) (lt_min h01 h11)
  have g : ∀ x y, (hi - lo) ^ 2 * (f x y - m) = (hi - x) * (hi - y) * (f lo lo - m) +
      (x - lo) * (hi - y) * (f hi lo - m) + (hi - x) * (y - lo) * (f lo hi - m) +
      (x - lo) * (y - lo) * (f hi hi - m) := by
    intro x y; have := hf x y; linear_combination this
  have m1 := min_le_left (min (f lo lo) (f hi lo)) (min (f lo hi) (f hi hi))
  have m2 := min_le_right (min (f lo lo) (f hi lo)) (min (f lo hi) (f hi hi))
  have m3 := min_le_left (f lo lo) (f hi lo)
  have m4 := min_le_right (f lo lo) (f hi lo)
  have m5 := min_le_left (f lo hi) (f hi hi)
  have m6 := min_le_right (f lo hi) (f hi hi)
  have := bilin_nonneg_box hlh (fun x y => f x y - m) g (by linarith)
    (by linarith) (by linarith) (by linarith) hx0 hx1 hy0 hy1
  linarith

/-! ### `Γ`: the projection identity -/

section Gamma

variable {P : Polygon} {A B C ei ej el : Point} {h : ℝ} {Z : Set Point}

/-- **`Γ`, sufficiency (Lemma 41, abstract).** -/
theorem gamma_cover (hA : ∀ z ∈ Z, P.Sees A z ↔ det A ei z ≤ 0)
    (hB : ∀ z ∈ Z, P.Sees B z ↔ det B ej z ≤ 0) (hC : ∀ z ∈ Z, P.Sees C z ↔ 0 ≤ det C el z)
    (hid : ∀ z : Point, det A ei z + det B ej z - det C el z = (z.2 - h) * (C.1 - A.1 - B.1))
    (hZ : ∀ z ∈ Z, h < z.2) (hle : C.1 ≤ A.1 + B.1) :
    ∀ z ∈ Z, P.Sees A z ∨ P.Sees B z ∨ P.Sees C z := by
  intro z hz
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  rw [hA z hz, not_le] at h1
  rw [hB z hz, not_le] at h2
  rw [hC z hz, not_le] at h3
  have e := hid z
  have hz' := hZ z hz
  have : (z.2 - h) * (C.1 - A.1 - B.1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith

/-- Shifting the guard along its horizontal segment changes the side by a multiple of the
height above the corner. -/
theorem det_shift (A e z : Point) (δ : ℝ) :
    det A e z = det (A.1 + δ, A.2) e z + δ * (z.2 - e.2) := by
  unfold det; ring

/-- **`Γ`, gap (Lemma 41, abstract).**  The crossing point `z` of the lines through `e_i` and
`e_j` and the shifted guards `A + (δ, 0)`, `B + (δ, 0)` is seen by none of the three guards when
`0 < 2δ < C.x − A.x − B.x`. -/
theorem gamma_gap (hA : ∀ z ∈ Z, P.Sees A z ↔ det A ei z ≤ 0)
    (hB : ∀ z ∈ Z, P.Sees B z ↔ det B ej z ≤ 0) (hC : ∀ z ∈ Z, P.Sees C z ↔ 0 ≤ det C el z)
    (hid : ∀ z : Point, det A ei z + det B ej z - det C el z = (z.2 - h) * (C.1 - A.1 - B.1))
    {z : Point} (hz : z ∈ Z) (hzh : h < z.2) (hei : ei.2 = h) (hej : ej.2 = h) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : 2 * δ < C.1 - A.1 - B.1)
    (hzA : det (A.1 + δ, A.2) ei z = 0) (hzB : det (B.1 + δ, B.2) ej z = 0) :
    ¬ P.Sees A z ∧ ¬ P.Sees B z ∧ ¬ P.Sees C z := by
  have eA := det_shift A ei z δ
  have eB := det_shift B ej z δ
  rw [hzA, hei] at eA
  rw [hzB, hej] at eB
  have hpos : 0 < δ * (z.2 - h) := mul_pos hδ (by linarith)
  have e := hid z
  refine ⟨?_, ?_, ?_⟩
  · rw [hA z hz]; linarith
  · rw [hB z hz]; linarith
  · rw [hC z hz, not_le]
    have : det C el z = (z.2 - h) * (2 * δ - (C.1 - A.1 - B.1)) := by
      linear_combination -e + eA + eB
    rw [this]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

end Gamma

/-! ### The weak-copy nook -/

open Corridor in
/-- **The weak-copy nook (abstract).**  For a copy pair in an admissible configuration and a
zone `Z` on the axis (`L = 0`) above the shadow corners, containing the critical points `X v v`,
on which the visibility of the two guards is characterised by the sides of the lines through
the shadow corners: the zone is covered iff `t' ≤ t`. -/
theorem copyNook_iff {P : Polygon} (C : CopyPair ℝ) (hC : C.Hyp) (hA : C.Adm (3 / 2))
    {Z : Set Point} {t t' : ℝ} (ht0 : 0 ≤ t) (ht1' : t' ≤ 3 / 2)
    (hp : ∀ z ∈ Z, P.Sees (C.p t) z ↔ det (C.p t) C.k0 z ≤ 0)
    (hq : ∀ z ∈ Z, P.Sees (C.q t') z ↔ 0 ≤ det (C.q t') C.k1 z)
    (hw : ∀ z ∈ Z, 0 < C.w z) (hL : ∀ z ∈ Z, C.L z = 0)
    (hX : ∀ v, 0 ≤ v → v ≤ 3 / 2 → C.X v v ∈ Z) :
    (∀ z ∈ Z, P.Sees (C.p t) z ∨ P.Sees (C.q t') z) ↔ t' ≤ t := by
  constructor
  · intro hall
    refine (CopyPair.nook_iff hC hA ht0 ht1').1 fun v hv0 hv1 => ?_
    have hz := hX v hv0 hv1
    rcases hall _ hz with h | h
    · exact Or.inl ((hp _ hz).1 h)
    · exact Or.inr ((hq _ hz).1 h)
  · intro htt z hz
    rcases CopyPair.nook_covered hC htt (hw z hz) (hL z hz).le with h | h
    · exact Or.inl ((hp z hz).2 h)
    · exact Or.inr ((hq z hz).2 h)

end ArtGallery.Sec5.Tmpl

end
