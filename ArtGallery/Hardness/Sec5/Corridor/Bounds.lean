module

public import ArtGallery.Hardness.Sec5.Corridor.Coords

/-!
# Section 5: corridors — bounds on the corridor vertices

Quantitative positions (in units of `ε`, local frame at `O`) of the vertices that lie on the axes:
with `ℓ = lwE k`, `r = rwE k`, `X_a = (r − ℓ)/2` (abscissa of the apex):

| vertex | `lX` | `lY` |
|---|---|---|
| `p_0` (`sgPt 0`) | `8S` | `|·| ≤ 8(20N + 150)` |
| `p_k`, `k ≥ 1` | `(r_k − ℓ_{k−1})/2 + 1/4` (exact) | `(ℓ + r)/2 − 16 ± 1/8` |
| `z'_k` (`zp`) | `X_a + 16 + 3/16 ± 3/16` | `(ℓ + r)/2 − 16 ± 1/8` |
| `n1` | `X_a + 3` (exact) | `(ℓ + r)/2 − 1 ± 1/8` |
| `n0` | `X_a − 3` (exact) | `(ℓ + r)/2 + 1 ± 1/8` |

and the umbra axis is within `1/8` of `lY = (ℓ + r)/2 − 16` inside the window `|lX| ≤ 456N`
(`Good.axis_approx`).  Everything follows from `S = 200000 N²`, `N ≥ 2`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

/-- Product of bounded quantities. -/
theorem abs_mul_le_of {a b A B : ℚ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- A quotient by a large positive denominator. -/
theorem abs_div_le_of {a D c : ℚ} (hD : 0 < D) (h : |a| ≤ c * D) : |a / D| ≤ c := by
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]; exact h

/-! ## Generic estimates in the atoms -/

section Atoms

variable {N S η b u w : ℚ}

/-- **Axis error.** -/
theorem axis_err (hN : 2 ≤ N) (hS : S = 200000 * N ^ 2) (hη1 : 1 ≤ η) (hη2 : η ≤ 3 * N)
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 14 * N) (hu1 : -50 ≤ u) (hu2 : u ≤ 50) (hw1 : -50 ≤ w)
    (hw2 : w ≤ 50) {X : ℚ} (hX : |X| ≤ 456 * N) :
    |((η + w) * X + 8 * S * (η + b - (u + w))) / (2 * S + u - b) - 4 * (η + b - (u + w))| ≤
      1 / 8 := by
  have hD : S ≤ 2 * S + u - b := by nlinarith
  have hSpos : 0 < S := by rw [hS]; positivity
  have hDpos : 0 < 2 * S + u - b := by linarith
  have hDne : 2 * S + u - b ≠ 0 := hDpos.ne'
  have e : ((η + w) * X + 8 * S * (η + b - (u + w))) / (2 * S + u - b) - 4 * (η + b - (u + w)) =
      ((η + w) * X + 4 * (η + b - (u + w)) * (b - u)) / (2 * S + u - b) := by
    rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]; ring
  rw [e]
  apply abs_div_le_of hDpos
  have h1 : |(η + w) * X| ≤ (3 * N + 50) * (456 * N) :=
    abs_mul_le_of (by rw [abs_le]; constructor <;> linarith) hX
  have h2 : |4 * (η + b - (u + w)) * (b - u)| ≤ (4 * (17 * N + 100)) * (14 * N + 50) := by
    rw [mul_assoc]
    rw [show 4 * (17 * N + 100) * (14 * N + 50) = 4 * ((17 * N + 100) * (14 * N + 50)) by ring]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 4)]
    have := abs_mul_le_of (a := η + b - (u + w)) (b := b - u) (A := 17 * N + 100)
      (B := 14 * N + 50) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)
    linarith
  calc |(η + w) * X + 4 * (η + b - (u + w)) * (b - u)|
      ≤ |(η + w) * X| + |4 * (η + b - (u + w)) * (b - u)| := abs_add_le _ _
    _ ≤ (3 * N + 50) * (456 * N) + (4 * (17 * N + 100)) * (14 * N + 50) := add_le_add h1 h2
    _ ≤ 1 / 8 * S := by rw [hS]; nlinarith
    _ ≤ 1 / 8 * (2 * S + u - b) := by linarith

/-- The nook axis coefficient `β` (in the atoms). -/
def nkBeta (S η b u w : ℚ) : ℚ :=
  3 * S - b / 2 + η / 2 + 3 * u / 2 + w / 2 + 11 / 8 - (b + η + u + w + 9 / 4) / (2 * S)

/-- The error term of `n1`. -/
def nkE1 (S η b u w : ℚ) : ℚ :=
  b + 5 * η - 3 * u - w + 13 / 4 + (4 * b + 4 * η - 2 * u - 2 * w + 12) / S

/-- The error term of `n0`. -/
def nkE0 (S η b u w : ℚ) : ℚ :=
  5 * b + η - 9 * u - 11 * w + 17 / 4 + (2 * b + 2 * η + 2 * u + 2 * w + 9 / 2) / S

theorem nkBeta_ge (hN : 2 ≤ N) (hS : S = 200000 * N ^ 2) (hη1 : 1 ≤ η) (hη2 : η ≤ 3 * N)
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 14 * N) (hu1 : -50 ≤ u) (hu2 : u ≤ 50) (hw1 : -50 ≤ w)
    (hw2 : w ≤ 50) : 2 * S ≤ nkBeta S η b u w := by
  have hSpos : 0 < S := by rw [hS]; positivity
  have hS8 : 800000 ≤ S := by rw [hS]; nlinarith
  have h1 : (b + η + u + w + 9 / 4) / (2 * S) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  simp only [nkBeta]
  nlinarith

theorem nkE1_abs (hN : 2 ≤ N) (hS : S = 200000 * N ^ 2) (hη1 : 1 ≤ η) (hη2 : η ≤ 3 * N)
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 14 * N) (hu1 : -50 ≤ u) (hu2 : u ≤ 50) (hw1 : -50 ≤ w)
    (hw2 : w ≤ 50) : |nkE1 S η b u w| ≤ 1 / 8 * (2 * S) := by
  have hSpos : 0 < S := by rw [hS]; positivity
  have hS8 : 800000 ≤ S := by rw [hS]; nlinarith
  have h1 : |(4 * b + 4 * η - 2 * u - 2 * w + 12) / S| ≤ 1 := by
    rw [abs_div, abs_of_pos hSpos, div_le_one hSpos, abs_le]; constructor <;> nlinarith
  simp only [nkE1]
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

theorem nkE0_abs (hN : 2 ≤ N) (hS : S = 200000 * N ^ 2) (hη1 : 1 ≤ η) (hη2 : η ≤ 3 * N)
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 14 * N) (hu1 : -50 ≤ u) (hu2 : u ≤ 50) (hw1 : -50 ≤ w)
    (hw2 : w ≤ 50) : |nkE0 S η b u w| ≤ 1 / 8 * (2 * S) := by
  have hSpos : 0 < S := by rw [hS]; positivity
  have hS8 : 800000 ≤ S := by rw [hS]; nlinarith
  have h1 : |(2 * b + 2 * η + 2 * u + 2 * w + 9 / 2) / S| ≤ 1 := by
    rw [abs_div, abs_of_pos hSpos, div_le_one hSpos, abs_le]; constructor <;> nlinarith
  simp only [nkE0]
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

end Atoms

namespace Input

variable {I : Input} {N : ℚ}

/-! ## Atom bounds -/

section AtomBounds

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

theorem Good.lwE_bound : 30 ≤ I.lwE k ∧ I.lwE k ≤ 136 * N + 10 := by
  have := hg.eta_ge; have := hg.eta_le; have := hg.bx_nonneg k; have := hg.bx_le hk
  simp only [lwE]; constructor <;> linarith

theorem Good.rwE_bound : -790 ≤ I.rwE k ∧ I.rwE k ≤ 810 := by
  have := hg.tu_bound hk; have := hg.tw_bound hk
  simp only [rwE]; constructor <;> linarith

theorem Good.window_apex : |(I.rwE k - I.lwE k) / 2| + 20 ≤ 456 * N := by
  have := hg.lwE_bound hk; have := hg.rwE_bound hk; have := hg.N_ge
  rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

/-- The umbra axis is nearly horizontal inside the window. -/
theorem Good.axis_approx {X : ℚ} (hX : |X| ≤ 456 * N) :
    |(I.hh k * X + 8 * I.S * I.gg k) / I.DD k - 4 * I.gg k| ≤ 1 / 8 := by
  have hu := hg.tu_bound hk; have hw := hg.tw_bound hk
  have h := axis_err hg.N_ge hg.S_eq hg.eta_ge hg.eta_le (hg.bx_nonneg k)
    (by linarith [hg.bx_le hk]) hu.1 hu.2 hw.1 hw.2 hX
  simpa [hh, gg, DD] using h

theorem Good.hh_abs : |I.hh k| ≤ 3 * N + 50 := by
  have := hg.tw_bound hk; have := hg.eta_ge; have := hg.eta_le
  simp only [hh]; rw [abs_le]; constructor <;> linarith

theorem Good.gg_abs : |I.gg k| ≤ 17 * N + 100 := by
  have := hg.tw_bound hk; have := hg.tu_bound hk; have := hg.eta_ge; have := hg.eta_le
  have := hg.bx_nonneg k; have := hg.bx_le hk
  simp only [gg]; rw [abs_le]; constructor <;> linarith

end AtomBounds

/-! ## The umbra-axis vertices -/

/-- The stationary guard of the first pair is on the window line `x = S + 2`. -/
theorem lX_sgPt_zero : I.lX (I.sgPt 0) = 8 * I.S := by
  simp only [sgPt, base_zero, onUmbra, onLine_fst, lX_def, d1]; ring

theorem Good.lY_sgPt_zero_abs (hg : I.Good N) (h0 : 0 < I.np) :
    |I.lY (I.sgPt 0)| ≤ 8 * (20 * N + 150) := by
  have hS := hg.S_pos
  have hD := hg.DD_pos h0
  rw [show I.sgPt 0 = I.onUmbra 0 (I.sgPt 0).1 from rfl, lY_onUmbra hg h0,
    show I.lX (I.onUmbra 0 (I.sgPt 0).1) = I.lX (I.sgPt 0) from rfl, lX_sgPt_zero]
  rw [show (I.hh 0 * (8 * I.S) + 8 * I.S * I.gg 0) = (8 * (I.hh 0 + I.gg 0)) * I.S by ring]
  apply abs_div_le_of (by linarith)
  have h1 := hg.hh_abs h0
  have h2 := hg.gg_abs h0
  rw [abs_mul, abs_of_pos hS]
  have : |8 * (I.hh 0 + I.gg 0)| ≤ 8 * (20 * N + 150) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 8)]
    have := abs_add_le (I.hh 0) (I.gg 0)
    linarith
  have hN := hg.N_ge
  calc |8 * (I.hh 0 + I.gg 0)| * I.S ≤ 8 * (20 * N + 150) * I.S :=
        mul_le_mul_of_nonneg_right this hS.le
    _ ≤ 8 * (20 * N + 150) * I.DD 0 := mul_le_mul_of_nonneg_left hD (by positivity)

section Umbra

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- Points of the umbra axis inside the window are within `1/8` of `lY = (ℓ + r)/2 − 16`. -/
theorem Good.lY_onUmbra_approx (x : ℚ) (hx : |I.lX (I.onUmbra k x)| ≤ 456 * N) :
    |I.lY (I.onUmbra k x) - ((I.lwE k + I.rwE k) / 2 - 16)| ≤ 1 / 8 := by
  rw [lY_onUmbra hg hk, lw_add_rw]
  have := hg.axis_approx hk hx
  rwa [show 4 * I.gg k + 16 - 16 = 4 * I.gg k by ring]

/-- The abscissa of `z'_k` in `ε`-units: `(⌈8(r − Y_a)⌉ + 1)/8`, `Y_a` the axis height at the
apex abscissa. -/
theorem lX_zp_eq : I.lX (I.zp k) = (((⌈8 * (I.rwE k -
    I.lY (I.onUmbra k (I.apex k).1))⌉ : ℤ) : ℚ) + 1) / 8 := by
  have hS := hg.S_pos
  have hS' : I.S ≠ 0 := hS.ne'
  have harg : (I.O.1 + (I.Rw k - I.ya k) - I.O.1) / (I.ε / 8) =
      8 * (I.rwE k - I.lY (I.onUmbra k (I.apex k).1)) := by
    rw [Rw_eq hg hk]; simp only [ya, lY_def, Input.O, Oc, Input.ε, eps]; field_simp; ring
  have h1 : I.lX (I.zp k) = 8 * I.S * (I.ε / 8) *
      (((⌈(I.O.1 + (I.Rw k - I.ya k) - I.O.1) / (I.ε / 8)⌉ : ℤ) : ℚ) + 1) := by
    simp only [lX_def, zp, onUmbra_fst', gridXUp, Input.O, Oc]; ring
  rw [h1, harg, Input.ε, eps]
  field_simp

theorem lX_onUmbra_apex : I.lX (I.onUmbra k (I.apex k).1) = (I.rwE k - I.lwE k) / 2 := by
  rw [show I.lX (I.onUmbra k (I.apex k).1) = I.lX (I.apex k) from rfl, lX_apex hg hk]

/-- **Rounding of `z'_k`**: one to two grid units `1/8` east of `X = r − Y_a`. -/
theorem lX_zp_ceil : I.rwE k - I.lY (I.onUmbra k (I.apex k).1) + 1 / 8 ≤ I.lX (I.zp k) ∧
    I.lX (I.zp k) < I.rwE k - I.lY (I.onUmbra k (I.apex k).1) + 1 / 4 := by
  rw [lX_zp_eq hg hk]
  set q := 8 * (I.rwE k - I.lY (I.onUmbra k (I.apex k).1)) with hq
  have h1 := Int.le_ceil q
  have h2 := Int.ceil_lt_add_one q
  constructor <;> linarith

/-- **Position of `z'_k`**: `X_a + 16 ≤ lX z'_k ≤ X_a + 16 + 3/8`. -/
theorem Good.lX_zp : |I.lX (I.zp k) - ((I.rwE k - I.lwE k) / 2 + 16 + 3 / 16)| ≤ 3 / 16 := by
  have h1 := hg.lY_onUmbra_approx hk (I.apex k).1 (by
    rw [lX_onUmbra_apex hg hk]; linarith [hg.window_apex hk, abs_nonneg ((I.rwE k - I.lwE k) / 2)])
  have h2 := lX_zp_ceil hg hk
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem Good.lX_zp_window : |I.lX (I.zp k)| ≤ 456 * N := by
  have h1 := hg.lX_zp hk
  have h2 := hg.window_apex hk
  rw [abs_le] at h1 ⊢
  rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [h] at h2 <;>
    constructor <;> linarith

/-- **Height of `z'_k`.** -/
theorem Good.lY_zp : |I.lY (I.zp k) - ((I.lwE k + I.rwE k) / 2 - 16)| ≤ 1 / 8 :=
  hg.lY_onUmbra_approx hk _ (hg.lX_zp_window hk)

/-- **`z'_k` lies strictly beyond the wall line `ξ = Rw`**: `r + 1/16 ≤ ξ(z'_k) ≤ r + 5/16`
(in `ε`-units, `ξ = lX + lY`). -/
theorem Good.xi_zp : I.rwE k + 1 / 16 ≤ I.lX (I.zp k) + I.lY (I.zp k) ∧
    I.lX (I.zp k) + I.lY (I.zp k) ≤ I.rwE k + 5 / 16 := by
  have hS := hg.S_pos
  have hD := hg.DD_pos hk
  have hN := hg.N_ge
  have hSe := hg.S_eq
  have hc := lX_zp_ceil hg hk
  have hz := hg.lX_zp hk
  have ha := lX_onUmbra_apex hg hk
  have e1 := lY_onUmbra hg hk (I.zp k).1
  have e2 := lY_onUmbra hg hk (I.apex k).1
  rw [show I.onUmbra k (I.zp k).1 = I.zp k from rfl] at e1
  -- the axis rises by `h (lX z' − X_a)/D` between the apex abscissa and `z'_k`
  have ediff : I.lY (I.zp k) - I.lY (I.onUmbra k (I.apex k).1) =
      I.hh k * (I.lX (I.zp k) - I.lX (I.onUmbra k (I.apex k).1)) / I.DD k := by
    rw [e1, e2]; field_simp; ring
  have hb : |I.hh k * (I.lX (I.zp k) - I.lX (I.onUmbra k (I.apex k).1)) / I.DD k| ≤ 1 / 100 := by
    apply abs_div_le_of (by linarith)
    have h1 := hg.hh_abs hk
    have h2 : |I.lX (I.zp k) - I.lX (I.onUmbra k (I.apex k).1)| ≤ 17 := by
      rw [ha]; rw [abs_le] at hz ⊢; constructor <;> linarith
    have := abs_mul_le_of h1 h2
    have : (3 * N + 50) * 17 ≤ 1 / 100 * I.S := by rw [hSe]; nlinarith
    linarith
  rw [← ediff, abs_le] at hb
  constructor <;> linarith [hc.1, hc.2]

end Umbra

section Later

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k)
include hg hk hk1

theorem Good.window_valley : |(I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4| + 20 ≤ 456 * N := by
  have := hg.lwE_bound (k := k - 1) (by omega); have := hg.rwE_bound hk; have := hg.N_ge
  rcases abs_cases ((I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    linarith

theorem lX_sgPt : I.lX (I.sgPt k) = (I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4 := by
  rw [show I.lX (I.sgPt k) = I.lX (I.base k) from rfl,
    show I.base k = I.valley k by simp [base, show k ≠ 0 by omega], lX_valley hg hk]

/-- **Height of the stationary guard `p_k`, `k ≥ 1`.** -/
theorem Good.lY_sgPt : |I.lY (I.sgPt k) - ((I.lwE k + I.rwE k) / 2 - 16)| ≤ 1 / 8 :=
  hg.lY_onUmbra_approx hk _ (by
    rw [show I.lX (I.onUmbra k (I.base k).1) = I.lX (I.sgPt k) from rfl, lX_sgPt hg hk hk1]
    linarith [hg.window_valley hk hk1])

end Later

/-! ## The nook top edge -/

theorem z0_eq_local (k : ℕ) : I.z0 k = (I.S + 1 + (I.yN k - I.Lw k), I.H + 1 + I.yN k) := rfl

theorem z1_eq_local (k : ℕ) : I.z1 k = (I.S + 1 + (I.Rw k - I.yN k), I.H + 1 + I.yN k) := rfl

theorem lX_n1 (k : ℕ) : I.lX (I.n1 k) = I.lX (I.z1 k) := rfl

theorem lX_n0 (k : ℕ) : I.lX (I.n0 k) = I.lX (I.z0 k) := rfl

section Nook

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

omit hk in
/-- The nook axis relation for the points `n0`, `n1` in the atoms. -/
theorem nook_relation (z : ℚ × ℚ) (hz : (I.nookQ k).L z = 0) :
    let S := I.S
    let H := I.H
    let yN := I.yN k
    let X0 := I.yN k - I.Lw k
    let X1 := I.Rw k - I.yN k
    let u := I.tu k
    let w := I.tw k
    let b := I.bx k
    (S * (2 + yN) - H - w - yN - 1) * (z.1 - (S + 1)) +
      (S * (3 - X1) + X0 + u - b + 1) * (z.2 - (H + 1)) +
      (H * X0 - 2 * S * X1 - 3 * S * yN + X0 + X1 * w - u * yN + b * yN - yN) = 0 := by
  have hS := hg.S_pos
  rw [nookQ, z0_eq_local, z1_eq_local, copyPair_L_local hS.ne', div_eq_zero_iff] at hz
  rcases hz with hz | hz
  · simp only [tu, tw, bx]; exact hz
  · exact absurd hz hS.ne'

/-- **Height of `n1`**: two units above the mouth corner `z1`. -/
theorem Good.lY_n1 : |I.lY (I.n1 k) - ((I.lwE k + I.rwE k) / 2 - 1)| ≤ 1 / 8 := by
  have hS := hg.S_pos
  have hrel := nook_relation hg (I.n1 k) (nook_L_n1 hg.toValid hk)
  simp only at hrel
  rw [show (I.n1 k).1 = (I.z1 k).1 from rfl, z1_eq_local] at hrel
  simp only at hrel
  rw [yN_eq' hg hk, Lw_eq hg, Rw_eq hg hk] at hrel
  have hu := hg.tu_bound hk; have hw := hg.tw_bound hk
  have hβ := nkBeta_ge hg.N_ge hg.S_eq hg.eta_ge hg.eta_le (hg.bx_nonneg k)
    (by linarith [hg.bx_le hk]) hu.1 hu.2 hw.1 hw.2
  have hE := nkE1_abs hg.N_ge hg.S_eq hg.eta_ge hg.eta_le (hg.bx_nonneg k)
    (by linarith [hg.bx_le hk]) hu.1 hu.2 hw.1 hw.2
  set β := nkBeta I.S I.eta (I.bx k) (I.tu k) (I.tw k) with hβdef
  set E := nkE1 I.S I.eta (I.bx k) (I.tu k) (I.tw k) with hEdef
  have hβpos : 0 < β := by linarith
  -- solve the axis relation
  have hS' : I.S ≠ 0 := hS.ne'
  have key : β * I.lY (I.n1 k) = β * ((I.lwE k + I.rwE k) / 2 - 1) + E := by
    rw [lY_def, hβdef, hEdef]
    simp only [nkBeta, nkE1, lwE, rwE, eta] at hrel ⊢
    linear_combination (norm := (field_simp; ring)) (8 * I.S) * hrel
  have : I.lY (I.n1 k) - ((I.lwE k + I.rwE k) / 2 - 1) = E / β := by
    field_simp; linarith
  rw [this]
  apply abs_div_le_of hβpos
  linarith

/-- **Height of `n0`**: four units above the mouth corner `z0`. -/
theorem Good.lY_n0 : |I.lY (I.n0 k) - ((I.lwE k + I.rwE k) / 2 + 1)| ≤ 1 / 8 := by
  have hS := hg.S_pos
  have hrel := nook_relation hg (I.n0 k) (nook_L_n0 hg.toValid hk)
  simp only at hrel
  rw [show (I.n0 k).1 = (I.z0 k).1 from rfl, z0_eq_local] at hrel
  simp only at hrel
  rw [yN_eq' hg hk, Lw_eq hg, Rw_eq hg hk] at hrel
  have hu := hg.tu_bound hk; have hw := hg.tw_bound hk
  have hβ := nkBeta_ge hg.N_ge hg.S_eq hg.eta_ge hg.eta_le (hg.bx_nonneg k)
    (by linarith [hg.bx_le hk]) hu.1 hu.2 hw.1 hw.2
  have hE := nkE0_abs hg.N_ge hg.S_eq hg.eta_ge hg.eta_le (hg.bx_nonneg k)
    (by linarith [hg.bx_le hk]) hu.1 hu.2 hw.1 hw.2
  set β := nkBeta I.S I.eta (I.bx k) (I.tu k) (I.tw k) with hβdef
  set E := nkE0 I.S I.eta (I.bx k) (I.tu k) (I.tw k) with hEdef
  have hβpos : 0 < β := by linarith
  have hS' : I.S ≠ 0 := hS.ne'
  have key : β * I.lY (I.n0 k) = β * ((I.lwE k + I.rwE k) / 2 + 1) + E := by
    rw [lY_def, hβdef, hEdef]
    simp only [nkBeta, nkE0, lwE, rwE, eta] at hrel ⊢
    linear_combination (norm := (field_simp; ring)) (8 * I.S) * hrel
  have : I.lY (I.n0 k) - ((I.lwE k + I.rwE k) / 2 + 1) = E / β := by
    field_simp; linarith
  rw [this]
  apply abs_div_le_of hβpos
  linarith

end Nook

end Input

end ArtGallery.Sec5.Corridor

end
