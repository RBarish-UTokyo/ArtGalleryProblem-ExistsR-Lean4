module

public import ArtGallery.Hardness.Sec5.Corridor.Member

/-!
# Section 5: corridors — what the stationary guards do not see

* `Good.sg_cone`: a point seen by the stationary guard `p_j` is weakly west of `p_j` and on or
  below the umbra axis `A_j` (`L_j ≤ 0`): the vertex cone of the convex corner
  `base_j → p_j → z'_j`.
* `Good.sg_not_sees_nook`: no stationary guard sees a point of a nook top edge `[n0_k, n1_k]`.
* `Good.sg_not_sees_umbra`: no stationary guard sees an umbra critical point `X_k(v₀, v₁)` strictly
  above the axis (`v₁ < v₀`).  For a guard `p_j` of a pair to the east (`j < k`) whose axis
  passes above the point, the view is blocked by the upper-wall edge `z0_j → valley_{j+1}`.

All three are statements about an arbitrary simple counter-clockwise polygon `P` containing the
corridor chains as contiguous vertex chains (`CorridorAt`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-! ## Elementary identities -/

/-- **Shear identity.** For an affine `L` with `y`-coefficient `B` vanishing at `p`:
`B · det(p, z, c) = (z.x − p.x) L(c) − (c.x − p.x) L(z)`. -/
theorem shear_identity {L : Point → ℝ} {A B C : ℝ} (hL : ∀ x, L x = A * x.1 + B * x.2 + C)
    {p z c : Point} (hp : L p = 0) :
    B * det p z c = (z.1 - p.1) * L c - (c.1 - p.1) * L z := by
  rw [hL] at hp
  rw [hL, hL]
  simp only [det]
  linear_combination (c.1 - z.1) * hp

/-- Lower bounds on an affine function from its values at the ends of an interval. -/
theorem affine_ge_of_ends {c1 c0 M X e : ℝ} (hM : 0 < M) (hX : |X| ≤ M)
    (h1 : e ≤ c1 * M + c0) (h2 : e ≤ c1 * -M + c0) : e ≤ c1 * X + c0 := by
  rw [abs_le] at hX
  have key : 2 * M * (c1 * X + c0) = (M + X) * (c1 * M + c0) + (M - X) * (c1 * -M + c0) := by
    ring
  have a1 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ M + X)
  have a2 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ M - X)
  have : 2 * M * e ≤ 2 * M * (c1 * X + c0) := by rw [key]; linarith
  exact le_of_mul_le_mul_left this (by linarith)

/-- Bounds on an affine function from its values at the ends of an interval. -/
theorem abs_affine_le_of_ends {c1 c0 M X e : ℝ} (hM : 0 < M) (hX : |X| ≤ M)
    (h1 : |c1 * M + c0| ≤ e) (h2 : |c1 * -M + c0| ≤ e) : |c1 * X + c0| ≤ e := by
  rw [abs_le] at h1 h2 ⊢
  refine ⟨affine_ge_of_ends hM hX h1.1 h2.1, ?_⟩
  have := affine_ge_of_ends (c1 := -c1) (c0 := -c0) (e := -e) hM hX (by linarith) (by linarith)
  linarith

/-- Sign of `det(p, z, c)` for a point `c` strictly above the line, `z` on or below it. -/
theorem shear_sign_neg {B d zp cp Lc Lz : ℝ} (hB : 0 < B) (h : B * d = zp * Lc - cp * Lz)
    (hzp : zp < 0) (hcp : cp < 0) (hLc : 0 < Lc) (hLz : Lz ≤ 0) : d < 0 := by
  have h1 := mul_neg_of_neg_of_pos hzp hLc
  have h2 := mul_nonneg_of_nonpos_of_nonpos hcp.le hLz
  have : B * d < 0 := by linarith
  exact neg_of_mul_neg_right this hB.le

/-- Sign of `det(p, z, c)` for a point `c` far below the line, `z` at most slightly below it. -/
theorem shear_sign_pos {B d zp cp Lc Lz K : ℝ} (hB : 0 < B) (h : B * d = zp * Lc - cp * Lz)
    (hK : 0 < K) (hzc : zp < cp) (hcp : cp < 0) (hLc : Lc ≤ -37 * K) (hLz : -K / 4 < Lz) :
    0 < d := by
  have h1 : zp * (-37 * K) ≤ zp * Lc := mul_le_mul_of_nonpos_left hLc (by linarith)
  have h2 : -cp * (-K / 4) < -cp * Lz := mul_lt_mul_of_pos_left hLz (by linarith)
  have h3 : 0 < K * (-37 * zp + cp / 4) := mul_pos hK (by linarith)
  have : 0 < B * d := by nlinarith
  exact pos_of_mul_pos_right this hB.le

namespace CopyPair

/-- The axis function of a rational copy pair is affine over `ℝ`. -/
theorem castR_L_eq (C : CopyPair ℚ) (z : Point) :
    C.castR.L z = ((C.L (0, 0) : ℚ) : ℝ) + ((C.L (1, 0) - C.L (0, 0) : ℚ) : ℝ) * z.1 +
      ((C.L (0, 1) - C.L (0, 0) : ℚ) : ℝ) * z.2 := by
  simp only [L, castR, det2, ratPoint]
  push_cast
  ring

end CopyPair

namespace Input

variable {I : Input} {N : ℚ}

/-- Determinants in local `ε`-units. -/
theorem det_local (a b c : Point) :
    (8 * (I.S : ℝ)) ^ 2 * det a b c = (I.lXR b - I.lXR a) * (I.lYR c - I.lYR a) -
      (I.lXR c - I.lXR a) * (I.lYR b - I.lYR a) := by
  simp only [det, lXR, lYR]; ring

/-- The umbra axis function of pair `k` over `ℝ`. -/
theorem umbraR_L_affine (hg : I.Good N) (k : ℕ) (x : Point) :
    (I.umbraR k).L x = ((-I.hh k / I.S : ℚ) : ℝ) * x.1 + ((I.DD k / I.S : ℚ) : ℝ) * x.2 +
      (((I.hh k * (I.S + 1) - I.DD k * (I.H + 1) - I.gg k) / I.S : ℚ) : ℝ) := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  rw [umbraR, CopyPair.castR_L_eq]
  simp only [umbraQ_L_eq hg]
  push_cast
  field_simp
  ring

/-- The umbra axis function in local units: `8S² L = D·Y − h·X − 8S·g`. -/
theorem umbraR_L_local (hg : I.Good N) (k : ℕ) (x : Point) :
    8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L x =
      (I.DD k : ℝ) * I.lYR x - (I.hh k : ℝ) * I.lXR x - 8 * (I.S : ℝ) * (I.gg k : ℝ) := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  rw [umbraR_L_affine hg]
  push_cast
  simp only [lXR, lYR]
  field_simp
  ring

/-- `lX` is strictly monotone in the abscissa (real version). -/
theorem lXR_lt_iff (hg : I.Good N) {x y : Point} : x.1 < y.1 ↔ I.lXR x < I.lXR y := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lXR]
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith

/-- The slots move west: `ℓ` grows and `r` drops by at least `108` per pair. -/
theorem Good.steps (hg : I.Good N) (j : ℕ) : ∀ d : ℕ, j + d < I.np →
    I.lwE j + 108 * d ≤ I.lwE (j + d) ∧ I.rwE (j + d) = I.rwE j - 108 * d
  | 0 => fun _ => by simp
  | d + 1 => fun h => by
    obtain ⟨h1, h2⟩ := Good.steps hg j d (by omega)
    have h3 := hg.lwE_succ (k := j + d) (by omega)
    have h4 := hg.rwE_succ (k := j + d) (by omega)
    rw [← Nat.add_assoc]
    push_cast
    constructor <;> linarith

theorem Good.steps_le (hg : I.Good N) {j k : ℕ} (hjk : j < k) (hk : k < I.np) :
    I.lwE j + 108 ≤ I.lwE k ∧ I.rwE k ≤ I.rwE j - 108 ∧
      I.lwE j + I.rwE j ≤ I.lwE k + I.rwE k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + (d + 1) := ⟨k - j - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hg.steps j (d + 1) hk
  have : (0 : ℚ) ≤ d := by positivity
  push_cast at h1 h2
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

section Pair

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The umbra axis in local units, for real abscissae in the window. -/
theorem Good.axis_approxR {X : ℝ} (hX : |X| ≤ 456 * (N : ℝ)) :
    |((I.hh k : ℝ) * X + 8 * (I.S : ℝ) * (I.gg k : ℝ)) / (I.DD k : ℝ) - 4 * (I.gg k : ℝ)| ≤
      1 / 8 := by
  have hD : (0 : ℝ) < (I.DD k : ℝ) := by
    have := hg.DD_pos hk; have := hg.S_pos
    exact_mod_cast (by linarith : (0 : ℚ) < I.DD k)
  have hN : (0 : ℚ) < N := by have := hg.N_ge; linarith
  have hM : (0 : ℝ) < 456 * (N : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) < 456 * N)
  have q1 := hg.axis_approx hk (X := 456 * N) (by rw [abs_of_pos (by linarith)])
  have q2 := hg.axis_approx hk (X := -(456 * N)) (by rw [abs_neg, abs_of_pos (by linarith)])
  have r1 := rat_cast_le_of q1
  have r2 := rat_cast_le_of q2
  push_cast at r1 r2
  have key := abs_affine_le_of_ends (c1 := (I.hh k : ℝ) / (I.DD k : ℝ))
    (c0 := 8 * (I.S : ℝ) * (I.gg k : ℝ) / (I.DD k : ℝ) - 4 * (I.gg k : ℝ)) (e := 1 / 8) hM hX
    (by convert r1 using 2; field_simp; ring) (by convert r2 using 2; field_simp; ring)
  convert key using 2
  field_simp
  ring

/-- **Height above the axis.** In the window, `8S² L_k(z)` is `D_k` times the height of `z`
above `4 g_k` up to `±1/8`. -/
theorem Good.L_bounds {z : Point} (hX : |I.lXR z| ≤ 456 * (N : ℝ)) :
    (I.DD k : ℝ) * (I.lYR z - 4 * (I.gg k : ℝ) - 1 / 8) ≤ 8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L z ∧
      8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L z ≤
        (I.DD k : ℝ) * (I.lYR z - 4 * (I.gg k : ℝ) + 1 / 8) := by
  have hD : (0 : ℝ) < (I.DD k : ℝ) := by
    have := hg.DD_pos hk; have := hg.S_pos
    exact_mod_cast (by linarith : (0 : ℚ) < I.DD k)
  have ax := hg.axis_approxR hk hX
  rw [abs_le] at ax
  set Q := ((I.hh k : ℝ) * I.lXR z + 8 * (I.S : ℝ) * (I.gg k : ℝ)) / (I.DD k : ℝ) with hQ
  have eQ : (I.DD k : ℝ) * Q = (I.hh k : ℝ) * I.lXR z + 8 * (I.S : ℝ) * (I.gg k : ℝ) := by
    rw [hQ]; field_simp
  rw [umbraR_L_local hg]
  have a1 := mul_le_mul_of_nonneg_left ax.1 hD.le
  have a2 := mul_le_mul_of_nonneg_left ax.2 hD.le
  constructor <;> nlinarith

/-- Rational version of the height bounds. -/
theorem Good.L_boundsQ {c : ℚ × ℚ} (hX : |I.lX c| ≤ 456 * N) :
    (I.DD k : ℝ) * ((I.lY c : ℝ) - 4 * (I.gg k : ℝ) - 1 / 8) ≤
        8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L (ratPoint c) ∧
      8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L (ratPoint c) ≤
        (I.DD k : ℝ) * ((I.lY c : ℝ) - 4 * (I.gg k : ℝ) + 1 / 8) := by
  have h := hg.L_bounds hk (z := ratPoint c) (by
    rw [lXR_ratPoint, ← Rat.cast_abs]; exact_mod_cast hX)
  rwa [lYR_ratPoint] at h

/-- The stationary guard `p_k` is east of the mouth: `lX(p_k) > X_a + 15`. -/
theorem Good.lX_sgPt_gt : (I.rwE k - I.lwE k) / 2 + 15 < I.lX (I.sgPt k) := by
  have h1 := hg.lX_zp hk
  have h2 := (fst_lt_iff hg).1 (hg.zp_lt_sgPt hk)
  rw [abs_le] at h1
  linarith

/-- `ζ(p_k) < ℓ_k`: the stationary guard is right of the line `ζ = Lw_k`. -/
theorem Good.sg_zeta_lt : I.lY (I.sgPt k) - I.lX (I.sgPt k) < I.lwE k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [lX_sgPt_zero]
    have h1 := hg.lY_sgPt_zero_abs hk
    have h2 := (hg.lwE_bound hk).1
    have hN := hg.N_ge; have hS := hg.S_eq
    rw [abs_le] at h1
    nlinarith
  · rw [lX_sgPt hg hk hk1]
    have h1 := hg.lY_sgPt hk hk1
    have h2 := hg.lwE_succ (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h2
    rw [abs_le] at h1
    linarith

/-- Umbra critical points `X(v₀, v₁)` with `v₁ < v₀` are strictly above the axis. -/
theorem Good.umbra_L_pos {v₀ v₁ : ℝ} (h₁ : 0 ≤ v₁) (hv : v₁ < v₀) (h₀' : v₀ ≤ 3 / 2) :
    0 < (I.umbraR k).L ((I.umbraR k).X v₀ v₁) := by
  have hC := umbraR_hyp hg.toValid k
  have hA := umbraR_adm hg.toValid hk
  have hG := CopyPair.G_pos hC hA (t₀ := v₀) (t₁ := v₁) h₀' h₁
  have hw := CopyPair.w_X_pos hC hA h₀' h₁
  rw [(I.umbraR k).L_X hC.hk hG.ne']
  exact mul_pos (mul_pos (mul_pos hC.hs0 hC.hs1) hw) (by linarith)

end Pair

/-! ## The vertex cone of a stationary guard -/

section SGCone

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b) {j : ℕ} (hj : j < I.np)
include hg hP hL hC hj

/-- **The cone of a stationary guard.** A point seen by `p_j` is weakly west of `p_j` and on
or below the umbra axis of pair `j`. -/
theorem Good.sg_cone {z : Point} (h : P.Sees (ratPoint (I.sgPt j)) z) :
    z.1 ≤ (ratPoint (I.sgPt j)).1 ∧ (I.umbraR j).L z ≤ 0 := by
  have hn : 0 < P.n := by have := hP.1; omega
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_infix_sg hj
  obtain ⟨hp₁, hu, hw, -, -⟩ := vtx_triple hn hC.after hA
  have cfg := hg.sgConfig hj
  have hpu := cfg.hpu
  have hpw := cfg.hpw
  have he := cfg.he
  have hbx : (I.base j).1 = (I.sgPt j).1 := rfl
  have hpu' : ((I.base j).2 : ℝ) < (I.sgPt j).2 := by
    exact_mod_cast (by linarith : (I.base j).2 < (I.sgPt j).2)
  have hpw' : ((I.zp j).1 : ℝ) < (I.sgPt j).1 := by
    exact_mod_cast (by linarith : (I.zp j).1 < (I.sgPt j).1)
  have e1 : ((I.base j).1 : ℝ) = ((I.sgPt j).1 : ℝ) := by rw [hbx]
  have hconv : 0 < det (ratPoint (I.base j)) (ratPoint (I.sgPt j)) (ratPoint (I.zp j)) := by
    simp only [det, ratPoint]
    rw [e1]
    have := mul_pos (sub_pos.2 hpw') (sub_pos.2 hpu')
    nlinarith
  obtain ⟨c1, c2⟩ := Polygon.sees_subset_cone hP hL (Nat.mod_lt _ hn) hu hp₁ hw hconv h
  -- the axis function vanishes at `p_j` and `z'_j`
  have Lp : (I.umbraR j).L (ratPoint (I.sgPt j)) = 0 := by
    rw [umbraR_L, umbra_L_sgPt hg.toValid hj, Rat.cast_zero]
  have Lw : (I.umbraR j).L (ratPoint (I.zp j)) = 0 := by
    rw [umbraR_L, umbra_L_zp hg.toValid hj, Rat.cast_zero]
  have hsh := shear_identity (umbraR_L_affine hg j) (z := ratPoint (I.zp j)) (c := z) Lp
  rw [Lw, mul_zero, sub_zero] at hsh
  have hB : (0 : ℝ) < ((I.DD j / I.S : ℚ) : ℝ) := by
    have := hg.DD_pos hj; have := hg.S_pos
    exact_mod_cast div_pos (by linarith) this
  have hm : 0 ≤ ((ratPoint (I.zp j)).1 - (ratPoint (I.sgPt j)).1) * (I.umbraR j).L z := by
    rw [← hsh]; exact mul_nonneg hB.le c2
  have hneg : (ratPoint (I.zp j)).1 - (ratPoint (I.sgPt j)).1 < 0 := by
    simp only [ratPoint_fst]; linarith
  refine ⟨?_, ?_⟩
  · simp only [det, ratPoint] at c1 ⊢
    rw [e1] at c1
    by_contra hc
    push Not at hc
    have := mul_pos (sub_pos.2 hc) (sub_pos.2 hpu')
    linarith
  · by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hneg hc
    linarith

/-- A point seen by `p_j` has local abscissa at most that of `p_j`. -/
theorem Good.sg_sees_lX {z : Point} (h : P.Sees (ratPoint (I.sgPt j)) z) :
    I.lXR z ≤ (I.lX (I.sgPt j) : ℝ) := by
  have h1 := (hg.sg_cone hP hL hC hj h).1
  rw [← lXR_ratPoint]
  by_contra hc
  push Not at hc
  exact absurd ((lXR_lt_iff hg).2 hc) (not_lt.2 h1)

end SGCone

/-! ## Stationary guards and the critical sets -/

section Crit

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b) {j k : ℕ} (hj : j < I.np) (hk : k < I.np)
include hg hP hL hC hj hk

/-- A stationary guard of a pair to the west sees nothing east of `X_a(k) − 53`. -/
theorem Good.sg_west {z : Point} (hjk : k < j) (hz : (((I.rwE k - I.lwE k) / 2 - 53 : ℚ) : ℝ) <
    I.lXR z) : ¬ P.Sees (ratPoint (I.sgPt j)) z := by
  intro hs
  have h1 := hg.sg_sees_lX hP hL hC hj hs
  have hj1 : 0 < j := by omega
  have e := lX_sgPt hg hj hj1
  obtain ⟨s1, s2, -⟩ := hg.steps_le (j := k) (k := j) hjk hj
  rcases (by omega : k = j - 1 ∨ k < j - 1) with h | h
  · subst h
    have : I.lX (I.sgPt j) ≤ (I.rwE (j - 1) - I.lwE (j - 1)) / 2 - 53 := by rw [e]; linarith
    have := rat_cast_le_of this
    linarith
  · have s3 := (hg.steps_le (j := k) (k := j - 1) h (by omega)).1
    have : I.lX (I.sgPt j) ≤ (I.rwE k - I.lwE k) / 2 - 53 := by rw [e]; linarith
    have := rat_cast_le_of this
    linarith

/-- **No stationary guard sees a nook top edge.** -/
theorem Good.sg_not_sees_nook {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    ¬ P.Sees (ratPoint (I.sgPt j)) z := by
  obtain ⟨-, -, -, -, hx1, hx2, hy1, -⟩ := hg.nook_edge_loc hk hz
  rcases lt_or_ge k j with hkj | hjk
  · exact hg.sg_west hP hL hC hj hk hkj (by push_cast; linarith)
  intro hs
  have hLz := (hg.sg_cone hP hL hC hj hs).2
  -- `z` is well above the axis of pair `j`
  have hw := rat_cast_le_of (hg.window_apex hk)
  push_cast at hw
  have hX : |I.lXR z| ≤ 456 * (N : ℝ) := by
    rw [abs_le]
    rcases abs_cases ((((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      constructor <;> linarith
  have hb := hg.L_bounds hj hX
  have hD : (0 : ℝ) < (I.DD j : ℝ) := by
    have := hg.DD_pos hj; have := hg.S_pos
    exact_mod_cast (by linarith : (0 : ℚ) < I.DD j)
  have hgg : 4 * I.gg j ≤ (I.lwE k + I.rwE k) / 2 - 16 := by
    have e := lw_add_rw (I := I) j
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · linarith
    · obtain ⟨s1, s2, s3⟩ := hg.steps_le hlt hk; linarith
  have hgg' := rat_cast_le_of hgg
  push_cast at hgg'
  have : 0 < (I.DD j : ℝ) * (I.lYR z - 4 * (I.gg j : ℝ) - 1 / 8) :=
    mul_pos hD (by linarith)
  have hS : (0 : ℝ) < 8 * (I.S : ℝ) ^ 2 := by
    have : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
    positivity
  have := mul_nonpos_of_nonneg_of_nonpos hS.le hLz
  linarith

/-- **No stationary guard sees an umbra critical point strictly above the axis** (`v₁ < v₀`).
The guard of the pair itself and those of pairs to the east whose axis passes below the point
are excluded by their vertex cone; guards of pairs to the west by abscissa; a guard `p_j` of a
pair to the east whose axis passes above the point is blocked by the edge `z0_j → valley_{j+1}`
(the critical point is within `ε/4` of `A_j` and the valley more than `37ε` below it). -/
theorem Good.sg_not_sees_umbra {v₀ v₁ : ℝ} (h₁ : 0 ≤ v₁) (hv : v₁ < v₀) (h₀' : v₀ ≤ 3 / 2) :
    ¬ P.Sees (ratPoint (I.sgPt j)) ((I.umbraR k).X v₀ v₁) := by
  have hLk := hg.umbra_L_pos hk h₁ hv h₀'
  obtain ⟨hzζ, -, -, -, hzX, -, -⟩ :=
    hg.umbra_crit_eps hk (by linarith) h₀' h₁ (by linarith)
  set z := (I.umbraR k).X v₀ v₁ with hz
  rw [abs_le] at hzX
  rcases lt_trichotomy j k with hjk | rfl | hkj
  rotate_left
  · intro hs
    have := (hg.sg_cone hP hL hC hj hs).2
    linarith
  · exact hg.sg_west hP hL hC hj hk hkj (by push_cast; linarith)
  intro hs
  have hLj := (hg.sg_cone hP hL hC hj hs).2
  have hn : 0 < P.n := by have := hP.1; omega
  have hj1 : j + 1 < I.np := by omega
  -- the blocking edge `z0_j → valley_{j+1}`
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hj
  have hA' : I.chainAfter = (A₁ ++ [I.sgPt j, I.zp j, I.z1 j, I.n1 j]) ++
      [I.n0 j, I.z0 j, I.nxt j] ++ A₂ := by rw [hA]; simp
  obtain ⟨hy, -, hz', -, -⟩ := vtx_triple hn hC.after hA'
  rw [nxt, ite_eq_left hj1] at hz'
  -- local data of pair `j`, of `p_j` and of the critical point
  have hS0 : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have hS : (0 : ℝ) < (8 * (I.S : ℝ)) ^ 2 := by positivity
  have hS2 : (0 : ℝ) < 8 * (I.S : ℝ) ^ 2 := by positivity
  have xz0 : I.lXR (ratPoint (I.z0 j)) = ((I.rwE j : ℝ) - (I.lwE j : ℝ)) / 2 - 3 := by
    rw [lXR_ratPoint, lX_z0 hg hj]; push_cast; ring
  have yz0 : I.lYR (ratPoint (I.z0 j)) = ((I.lwE j : ℝ) + (I.rwE j : ℝ)) / 2 - 3 := by
    rw [lYR_ratPoint, lY_z0 hg hj]; push_cast; ring
  have xv : I.lXR (ratPoint (I.valley (j + 1))) = ((I.rwE j : ℝ) - (I.lwE j : ℝ)) / 2 - 215 / 4 := by
    rw [lXR_ratPoint, lX_valley hg hj1, hg.rwE_succ hj1, show j + 1 - 1 = j by omega]
    push_cast; ring
  have yv : I.lYR (ratPoint (I.valley (j + 1))) = ((I.lwE j : ℝ) + (I.rwE j : ℝ)) / 2 - 215 / 4 := by
    rw [lYR_ratPoint, lY_valley hg hj1, hg.rwE_succ hj1, show j + 1 - 1 = j by omega]
    push_cast; ring
  obtain ⟨s1, s2, s3⟩ := hg.steps_le hjk hk
  have s1' := rat_cast_le_of s1
  have s2' := rat_cast_le_of s2
  have s3' := rat_cast_le_of s3
  push_cast at s1' s2' s3'
  have gj : ((I.lwE j : ℝ) + (I.rwE j : ℝ)) / 2 = 4 * (I.gg j : ℝ) + 16 := by
    have e := congrArg (fun q : ℚ => (q : ℝ)) (lw_add_rw (I := I) j)
    push_cast at e; exact e
  have gk : ((I.lwE k : ℝ) + (I.rwE k : ℝ)) / 2 = 4 * (I.gg k : ℝ) + 16 := by
    have e := congrArg (fun q : ℚ => (q : ℝ)) (lw_add_rw (I := I) k)
    push_cast at e; exact e
  have hw := rat_cast_le_of (hg.window_apex hk)
  push_cast at hw
  have hXz : |I.lXR z| ≤ 456 * (N : ℝ) := by
    rw [abs_le]
    rcases abs_cases ((((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      constructor <;> linarith
  have hDj : (0 : ℝ) < (I.DD j : ℝ) := by
    have := hg.DD_pos hj; have := hg.S_pos
    exact_mod_cast (by linarith : (0 : ℚ) < I.DD j)
  have hDk : (0 : ℝ) < (I.DD k : ℝ) := by
    have := hg.DD_pos hk; have := hg.S_pos
    exact_mod_cast (by linarith : (0 : ℚ) < I.DD k)
  refine Polygon.not_sees_of_proper_cross hP
    (i := (b + (A₁ ++ [I.sgPt j, I.zp j, I.z1 j, I.n1 j]).length + 1) % P.n) (Nat.mod_lt _ hn)
    ?_ ?_ hs <;> rw [hy, hz']
  · -- `p_j` and the critical point are on opposite sides of the line `ζ = Lw_j`
    have edet : ∀ x : Point, (8 * (I.S : ℝ)) ^ 2 * det (ratPoint (I.z0 j))
        (ratPoint (I.valley (j + 1))) x = -203 / 4 * ((I.lYR x - I.lXR x) - (I.lwE j : ℝ)) := by
      intro x
      rw [det_local, xz0, yz0, xv, yv]
      ring
    have hp := hg.sg_zeta_lt hj
    have hp' := rat_cast_le_of hp.le
    have hpne : ((I.lY (I.sgPt j) - I.lX (I.sgPt j) : ℚ) : ℝ) ≠ ((I.lwE j : ℚ) : ℝ) := by
      rw [Ne, Rat.cast_inj]; exact hp.ne
    push_cast at hp' hpne
    have hpl : I.lYR (ratPoint (I.sgPt j)) - I.lXR (ratPoint (I.sgPt j)) < (I.lwE j : ℝ) := by
      rw [lXR_ratPoint, lYR_ratPoint]; exact lt_of_le_of_ne hp' hpne
    have d1 : 0 < det (ratPoint (I.z0 j)) (ratPoint (I.valley (j + 1))) (ratPoint (I.sgPt j)) := by
      have e := edet (ratPoint (I.sgPt j))
      have : 0 < (8 * (I.S : ℝ)) ^ 2 * det (ratPoint (I.z0 j)) (ratPoint (I.valley (j + 1)))
          (ratPoint (I.sgPt j)) := by rw [e]; linarith
      exact pos_of_mul_pos_right this hS.le
    have d2 : det (ratPoint (I.z0 j)) (ratPoint (I.valley (j + 1))) z < 0 := by
      have e := edet z
      have : (8 * (I.S : ℝ)) ^ 2 * det (ratPoint (I.z0 j)) (ratPoint (I.valley (j + 1))) z < 0 := by
        rw [e]; linarith
      exact neg_of_mul_neg_right this hS.le
    exact mul_neg_of_pos_of_neg d1 d2
  · -- `z0_j` is above and `valley_{j+1}` far below the line `p_j z`
    have Lp : (I.umbraR j).L (ratPoint (I.sgPt j)) = 0 := by
      rw [umbraR_L, umbra_L_sgPt hg.toValid hj, Rat.cast_zero]
    have hB : (0 : ℝ) < 8 * (I.S : ℝ) ^ 2 * ((I.DD j / I.S : ℚ) : ℝ) := by
      have := hg.DD_pos hj; have := hg.S_pos
      have : (0 : ℝ) < ((I.DD j / I.S : ℚ) : ℝ) := by
        exact_mod_cast div_pos (by linarith) this
      positivity
    have sh : ∀ c : Point, 8 * (I.S : ℝ) ^ 2 * ((I.DD j / I.S : ℚ) : ℝ) *
        det (ratPoint (I.sgPt j)) z c = (z.1 - (ratPoint (I.sgPt j)).1) *
          (8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L c) -
        (c.1 - (ratPoint (I.sgPt j)).1) * (8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L z) := by
      intro c
      have := shear_identity (umbraR_L_affine hg j) (z := z) (c := c) Lp
      linear_combination (8 * (I.S : ℝ) ^ 2) * this
    -- abscissae: `z < valley_{j+1} < z0_j < p_j`
    have hpx := rat_cast_le_of (hg.lX_sgPt_gt hj).le
    push_cast at hpx
    rw [← lXR_ratPoint] at hpx
    have o1 : z.1 < (ratPoint (I.valley (j + 1))).1 := by rw [lXR_lt_iff hg, xv]; linarith
    have o2 : (ratPoint (I.z0 j)).1 < (ratPoint (I.sgPt j)).1 := by
      rw [lXR_lt_iff hg, xz0]; linarith
    have o3 : (ratPoint (I.valley (j + 1))).1 < (ratPoint (I.sgPt j)).1 := by
      rw [lXR_lt_iff hg, xv]; linarith
    -- heights relative to the axis of pair `j`
    have Lz0 : 0 < 8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L (ratPoint (I.z0 j)) := by
      have h := (hg.L_boundsQ hj (c := I.z0 j) (hg.feature_z0 hj).1).1
      rw [← lYR_ratPoint, yz0, gj] at h
      have : 0 < (I.DD j : ℝ) * (4 * (I.gg j : ℝ) + 16 - 3 - 4 * (I.gg j : ℝ) - 1 / 8) :=
        mul_pos hDj (by linarith)
      linarith
    have Lv : 8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L (ratPoint (I.valley (j + 1))) ≤
        -37 * (I.DD j : ℝ) := by
      have h := (hg.L_boundsQ hj (c := I.valley (j + 1)) (hg.feature_valley hj1 (by omega)).1).2
      rw [← lYR_ratPoint, yv, gj] at h
      linarith
    have Lzu : 8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hS2.le hLj
    have Lzl : -(I.DD j : ℝ) / 4 < 8 * (I.S : ℝ) ^ 2 * (I.umbraR j).L z := by
      have hb := (hg.L_bounds hj hXz).1
      have hk' := (hg.L_bounds hk hXz).2
      have hpos : 0 < 8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L z := mul_pos hS2 hLk
      have hy : 0 < I.lYR z - 4 * (I.gg k : ℝ) + 1 / 8 := by
        by_contra hc
        push Not at hc
        have := mul_nonpos_of_nonneg_of_nonpos hDk.le hc
        linarith
      have : (I.DD j : ℝ) * (-1 / 4) < (I.DD j : ℝ) * (I.lYR z - 4 * (I.gg j : ℝ) - 1 / 8) :=
        mul_lt_mul_of_pos_left (by linarith) hDj
      linarith
    have d1 := shear_sign_neg hB (sh _) (by linarith) (by linarith) Lz0 Lzu
    have d2 := shear_sign_pos hB (sh _) hDj (by linarith) (by linarith) Lv Lzl
    exact mul_neg_of_neg_of_pos d1 d2

end Crit

/-! ## Base guards and receivers of other pairs -/

section Bands

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b) {k : ℕ} (hk : k < I.np)
include hg hP hL hC hk

/-- **Umbra critical points are seen by no base guard of another slot** (V1 with band
separation). -/
theorem Good.base_not_sees_umbra {σ' : ℕ} (hne : I.sigma k ≠ σ') {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 3 / 2) (hx : 27 * (σ' : ℝ) / 2 + t ≤ 14 * N) {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀)
    (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁) (h₁' : v₁ ≤ 3 / 2) :
    ¬ P.Sees (27 * (σ' : ℝ) / 2 + t, 0) ((I.umbraR k).X v₀ v₁) :=
  hg.not_sees_base_of_zeta hP hL hC hne ht0 ht1 hx (hg.umbra_crit_mem hk h₀ h₀' h₁ h₁').1
    (hg.umbra_crit_loc hk h₀ h₀' h₁ h₁').1 (hg.umbra_crit_band hk h₀ h₀' h₁ h₁').1

/-- **Umbra critical points are seen by no receiver of another pair.** -/
theorem Good.recv_not_sees_umbra {τ' : ℕ} (hne : I.tau k ≠ τ') {T : Point} {t : ℝ}
    (hr : RecvHyp T (ratPoint I.T0) τ' t) {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2)
    (h₁ : 0 ≤ v₁) (h₁' : v₁ ≤ 3 / 2) :
    ¬ P.Sees (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) ((I.umbraR k).X v₀ v₁) :=
  hg.not_sees_recv_of_xi hP hL hC hne hr (hg.umbra_crit_mem hk h₀ h₀' h₁ h₁').1
    (hg.umbra_crit_loc hk h₀ h₀' h₁ h₁').1 (hg.umbra_crit_band hk h₀ h₀' h₁ h₁').2

/-- **The nook top edge is seen by no base guard of another slot.** -/
theorem Good.base_not_sees_nook {σ' : ℕ} (hne : I.sigma k ≠ σ') {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 3 / 2) (hx : 27 * (σ' : ℝ) / 2 + t ≤ 14 * N) {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    ¬ P.Sees (27 * (σ' : ℝ) / 2 + t, 0) z :=
  hg.not_sees_base_of_zeta hP hL hC hne ht0 ht1 hx
    (Polygon.boundary_subset_filled _ (hg.nook_edge_boundary hk hz))
    (hg.nook_edge_band hk hz).1 (hg.nook_edge_band hk hz).2.1

/-- **The nook top edge is seen by no receiver of another pair.** -/
theorem Good.recv_not_sees_nook {τ' : ℕ} (hne : I.tau k ≠ τ') {T : Point} {t : ℝ}
    (hr : RecvHyp T (ratPoint I.T0) τ' t) {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    ¬ P.Sees (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) z :=
  hg.not_sees_recv_of_xi hP hL hC hne hr
    (Polygon.boundary_subset_filled _ (hg.nook_edge_boundary hk hz))
    (hg.nook_edge_band hk hz).1 (hg.nook_edge_band hk hz).2.2

end Bands

end Input

end ArtGallery.Sec5.Corridor

end
