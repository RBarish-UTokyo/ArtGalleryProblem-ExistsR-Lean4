module

public import ArtGallery.Hardness.Sec5.Corridor.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Section 5: corridors — the slab inequalities

These replace the paper's Lemmas 32/33/39/40 (docs/section5/08_proof_plan.md §6, SL1–SL4).
Everything is stated over an arbitrary ordered field `K` (so it applies to rational corridor
data and to real guard positions alike).

**Line forms.** In the local frame at `O`, the line through `p` and `k` (not vertical) consists
of the points whose `ζ`-coordinate is `lineZeta O p k X` (resp. whose `ξ`-coordinate is
`lineXi O p k X`) at local abscissa `X`, and the side of a point `z` is read off from
`det2 p k z = (k.x − p.x)·(ζ(z) − lineZeta O p k X(z))` (`det2_eq_lineZeta`, `det2_eq_lineXi`).

**Explicit lines** (`O = Oc = (S+1, H+1)`): for a base point `p = (x, 0)` and a receiver point
`q = m + (T + (t, 0))/S` (`u = T.x + t`, `v = u + T.y`):
* `p c0`: `ζ = (H/(S−x) − 1)(X + 1)`;  `p d0`: `ζ = 2ρ + ((H+2ρ)/(S−x) − 1)(X + 1)`;
* `q c1`: `ξ = v (X − 1)/(S + u)`;    `q d1`: `ξ = ρ + (v − 3/2)(X − 1)/(S + u)`.

**Slab inequalities** (`2 ≤ N`, `S = 200000 N²`, `S + 1 ≤ H ≤ S + 3N`, base point
`x = 27σ/2 + t ≤ 14N`, `t ∈ [0, 3/2]`; receivers `|T.x|, |T.y| ≤ 50` with
`T.x + T.y = T₀.x + T₀.y − 27τ/2`; window `|X| ≤ 57N/S = 38Nρ`):
* (SL1) `0 ≤ ζ_{pc0}(0) − Z(σ, 2t/3) < ε/40`, `0 ≤ ζ_{pd0}(0) − Z(σ, 2 + 2t/3) < ε/20`;
* (SL2) `|ζ_{pc0}(X) − ζ_{pc0}(0)| < ε/20`, same for `p d0`;
  combined: `|ζ_{pc0}(X) − Z(σ, 2t/3)| < ε/10`, `|ζ_{pd0}(X) − Z(σ, 2 + 2t/3)| < ε/10`;
* (SL3) receivers: `|ξ_{qc1}(0) − Ξ(τ, 1 − 2t/3)| < ε/16`, `|ξ_{qd1}(0) − Ξ(τ, 3 − 2t/3)| < ε/16`,
  slope parts `< ε/8`; combined `< ε/4`;
* (SL4) band separation `Z(σ,3) + ε < Z(σ+1,0) − ε`, `Ξ(τ,3) + ε < Ξ(τ+1,0) − ε`.

(The budgets differ from the ones printed in 08 §6, which are not all correct: the slope bound
`(17N/S)(57N/S) < ε/40` of SL2 fails — the true value is `≈ 1.55·ε/40` — and the receiver
offset bound `100²/S² < ε/40` fails for `N ≤ 3`.  The bounds above are proved; all combined
errors stay below `ε`, which is what the band lemma needs.)
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

section LineForms

variable {K : Type*} [Field K]

/-- The `ζ`-coordinate (relative to `O`) of the point of the line `p k` with local abscissa `X`. -/
def lineZeta (O p k : K × K) (X : K) : K :=
  zetaOf O k + ((k.2 - p.2) / (k.1 - p.1) - 1) * (X - (k.1 - O.1))

/-- The `ξ`-coordinate (relative to `O`) of the point of the line `p k` with local abscissa `X`. -/
def lineXi (O p k : K × K) (X : K) : K :=
  xiOf O k + ((k.2 - p.2) / (k.1 - p.1) + 1) * (X - (k.1 - O.1))

/-- The side of `z` with respect to the line `p → k`, in `ζ`-form. -/
theorem det2_eq_lineZeta (O p k z : K × K) (h : k.1 - p.1 ≠ 0) :
    det2 p k z = (k.1 - p.1) * (zetaOf O z - lineZeta O p k (z.1 - O.1)) := by
  simp only [det2, lineZeta, zetaOf]
  field_simp
  ring

/-- The side of `z` with respect to the line `p → k`, in `ξ`-form. -/
theorem det2_eq_lineXi (O p k z : K × K) (h : k.1 - p.1 ≠ 0) :
    det2 p k z = (k.1 - p.1) * (xiOf O z - lineXi O p k (z.1 - O.1)) := by
  simp only [det2, lineXi, xiOf]
  field_simp
  ring

/-- The line `p c0` for a base point `p = (x, 0)`. -/
theorem lineZeta_c0 (S H x X : K) :
    lineZeta (Oc S H) (x, 0) (c0 S H) X = (H / (S - x) - 1) * (X + 1) := by
  simp only [lineZeta, zetaOf, Oc, c0]
  ring

/-- The line `p d0` for a base point `p = (x, 0)`. -/
theorem lineZeta_d0 (S H x X : K) :
    lineZeta (Oc S H) (x, 0) (d0 S H) X =
      2 * rho S + ((H + 2 * rho S) / (S - x) - 1) * (X + 1) := by
  simp only [lineZeta, zetaOf, Oc, d0]
  ring

/-- The line `q c1` for a receiver point `q = m + (T + (t, 0))/S`. -/
theorem lineXi_c1 (S H X t : K) (T : K × K) (hS : S ≠ 0) (hu : S + (T.1 + t) ≠ 0) :
    lineXi (Oc S H) (place S H (T.1 + t, T.2)) (c1 S H) X =
      (T.1 + t + T.2) * (X - 1) / (S + (T.1 + t)) := by
  simp only [lineXi, xiOf, Oc, c1, place]
  have h1 : S + 2 - (S + 3 + (T.1 + t) / S) = -((S + (T.1 + t)) / S) := by
    field_simp; ring
  rw [h1]
  field_simp
  ring

/-- The line `q d1` for a receiver point `q = m + (T + (t, 0))/S`. -/
theorem lineXi_d1 (S H X t : K) (T : K × K) (hS : S ≠ 0) (hu : S + (T.1 + t) ≠ 0) :
    lineXi (Oc S H) (place S H (T.1 + t, T.2)) (d1 S H) X =
      rho S + (T.1 + t + T.2 - 3 / 2) * (X - 1) / (S + (T.1 + t)) := by
  simp only [lineXi, xiOf, Oc, d1, place, rho]
  have h1 : S + 2 - (S + 3 + (T.1 + t) / S) = -((S + (T.1 + t)) / S) := by
    field_simp; ring
  rw [h1]
  field_simp
  ring

end LineForms

section Inequalities

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The standing hypotheses on the scale: `2 ≤ N`, `S = 200000 N²`, `S + 1 ≤ H ≤ S + 3N`. -/
structure ScaleHyp (N S H : K) : Prop where
  /-- `N = max(4n + k, 2) ≥ 2`. -/
  two_le : 2 ≤ N
  /-- The scale `S = C N²`, `C = 200000`. -/
  hS : S = 200000 * N ^ 2
  /-- The unit height is at least `S + 1`. -/
  hH1 : S + 1 ≤ H
  /-- The unit height is at most `S + 3N`. -/
  hH2 : H ≤ S + 3 * N

namespace ScaleHyp

variable {N S H : K} (h : ScaleHyp N S H)
include h

theorem S_pos : 0 < S := by have := h.two_le; rw [h.hS]; positivity

theorem S_ge : 800000 ≤ S := by
  have := h.two_le; rw [h.hS]; nlinarith

theorem N_pos : 0 < N := by have := h.two_le; linarith

end ScaleHyp

/-- The bookkeeping step of all slab bounds: `a / (S b) < ε/k` follows from `8 k a < b`. -/
theorem div_lt_eps_div {a b S k : K} (hS : 0 < S) (hb : 0 < b) (hk : 0 < k) (h : 8 * k * a < b) :
    a / (S * b) < eps S / k := by
  rw [eps, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left h hS]

/-! ### Base lines (`p c0`, `p d0`) -/

section Base

variable {N S H t : K} {σ : ℕ}

/-- The exact offset of `p c0` at `X = 0` from the slab centre:
`ζ_p − Z(σ, 2t/3) = x (H − S + x) / (S (S − x))`, `x = 27σ/2 + t`. -/
theorem zetaC0_sub_Zs (hS : S ≠ 0) (hx : S - (27 * σ / 2 + t) ≠ 0) :
    (H / (S - (27 * σ / 2 + t)) - 1) - Zs S H σ (2 * t / 3) =
      (27 * σ / 2 + t) * (H - S + (27 * σ / 2 + t)) / (S * (S - (27 * σ / 2 + t))) := by
  have hZ : Zs S H σ (2 * t / 3) = (H - S) / S + (27 * σ / 2 + t) / S := by
    simp only [Zs, zetaO, delta, rho]; field_simp; ring
  rw [hZ]
  generalize 27 * (σ : K) / 2 + t = x at hx ⊢
  field_simp
  ring

/-- **(SL1)** The line `p c0` crosses `X = 0` within `ε/40` above the slab centre
`Z(σ, 2t/3)`. -/
theorem sl1_c0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N) :
    0 ≤ lineZeta (Oc S H) (27 * σ / 2 + t, 0) (c0 S H) 0 - Zs S H σ (2 * t / 3) ∧
      lineZeta (Oc S H) (27 * σ / 2 + t, 0) (c0 S H) 0 - Zs S H σ (2 * t / 3) < eps S / 40 := by
  have hSp := h.S_pos
  have hN := h.two_le
  have hσ : (0 : K) ≤ σ := Nat.cast_nonneg σ
  set x : K := 27 * σ / 2 + t with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hSx : 0 < S - x := by have := h.hS; nlinarith
  rw [lineZeta_c0 S H x 0, zero_add, mul_one, zetaC0_sub_Zs hSp.ne' hSx.ne']
  have hHS : 0 ≤ H - S + x := by have := h.hH1; linarith
  constructor
  · positivity
  · apply div_lt_eps_div hSp hSx (by norm_num)
    have h1 : x * (H - S + x) ≤ 14 * N * (17 * N) :=
      mul_le_mul hx (by have := h.hH2; linarith) hHS (by linarith)
    have := h.hS
    nlinarith

/-- The exact offset of `p d0` at `X = 0` from the slab centre `Z(σ, 2 + 2t/3)`. -/
theorem zetaD0_sub_Zs (hS : S ≠ 0) (hx : S - (27 * σ / 2 + t) ≠ 0) :
    (2 * rho S + ((H + 2 * rho S) / (S - (27 * σ / 2 + t)) - 1)) - Zs S H σ (2 + 2 * t / 3) =
      ((27 * σ / 2 + t) * (H - S + (27 * σ / 2 + t)) + 3) / (S * (S - (27 * σ / 2 + t))) := by
  have hZ : Zs S H σ (2 + 2 * t / 3) = (H - S) / S + (27 * σ / 2 + t) / S + 3 / S := by
    simp only [Zs, zetaO, delta, rho]; field_simp; ring
  rw [hZ]
  simp only [rho]
  generalize 27 * (σ : K) / 2 + t = x at hx ⊢
  field_simp
  ring

/-- **(SL1')** The line `p d0` crosses `X = 0` within `ε/20` above the slab centre
`Z(σ, 2 + 2t/3)`. -/
theorem sl1_d0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N) :
    0 ≤ lineZeta (Oc S H) (27 * σ / 2 + t, 0) (d0 S H) 0 - Zs S H σ (2 + 2 * t / 3) ∧
      lineZeta (Oc S H) (27 * σ / 2 + t, 0) (d0 S H) 0 - Zs S H σ (2 + 2 * t / 3) <
        eps S / 20 := by
  have hSp := h.S_pos
  have hN := h.two_le
  have hσ : (0 : K) ≤ σ := Nat.cast_nonneg σ
  set x : K := 27 * σ / 2 + t with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hSx : 0 < S - x := by have := h.hS; nlinarith
  rw [lineZeta_d0 S H x 0, zero_add, mul_one, zetaD0_sub_Zs hSp.ne' hSx.ne']
  have hHS : 0 ≤ H - S + x := by have := h.hH1; linarith
  constructor
  · positivity
  · apply div_lt_eps_div hSp hSx (by norm_num)
    have h1 : x * (H - S + x) ≤ 14 * N * (17 * N) :=
      mul_le_mul hx (by have := h.hH2; linarith) hHS (by linarith)
    have := h.hS
    nlinarith

/-- A product bound used for the slope parts: if `0 ≤ a`, `a·B < c` and `|X| ≤ B` then
`|a X| < c`. -/
theorem abs_mul_lt_of_le {a X B c : K} (ha : 0 ≤ a) (hX : |X| ≤ B) (hc : a * B < c) :
    |a * X| < c := by
  rw [abs_mul, abs_of_nonneg ha]
  calc a * |X| ≤ a * B := mul_le_mul_of_nonneg_left hX ha
    _ < c := hc

/-- **(SL2)** Inside the window `|X| ≤ 57N/S`, the line `p c0` deviates from its value at
`X = 0` by less than `ε/20`. -/
theorem sl2_c0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N)
    {X : K} (hX : |X| ≤ 57 * N / S) :
    |lineZeta (Oc S H) (27 * σ / 2 + t, 0) (c0 S H) X -
        lineZeta (Oc S H) (27 * σ / 2 + t, 0) (c0 S H) 0| < eps S / 20 := by
  have hSp := h.S_pos
  have hN := h.two_le
  have hσ : (0 : K) ≤ σ := Nat.cast_nonneg σ
  set x : K := 27 * σ / 2 + t with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hSx : 0 < S - x := by have := h.hS; nlinarith
  rw [lineZeta_c0 S H x X, lineZeta_c0 S H x 0]
  have hHS : 0 ≤ H - S + x := by have := h.hH1; linarith
  have ha : H / (S - x) - 1 = (H - S + x) / (S - x) := by field_simp; ring
  have e : (H / (S - x) - 1) * (X + 1) - (H / (S - x) - 1) * (0 + 1) =
      (H - S + x) / (S - x) * X := by rw [ha]; ring
  rw [e]
  apply abs_mul_lt_of_le (by positivity) hX
  rw [div_mul_div_comm, mul_comm (S - x) S]
  apply div_lt_eps_div hSp hSx (by norm_num)
  have h1 : H - S + x ≤ 17 * N := by have := h.hH2; linarith
  have h2 : (H - S + x) * N ≤ 17 * N * N := mul_le_mul_of_nonneg_right h1 (by linarith)
  have := h.hS
  nlinarith

/-- **(SL2')** Inside the window `|X| ≤ 57N/S`, the line `p d0` deviates from its value at
`X = 0` by less than `ε/20`. -/
theorem sl2_d0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N)
    {X : K} (hX : |X| ≤ 57 * N / S) :
    |lineZeta (Oc S H) (27 * σ / 2 + t, 0) (d0 S H) X -
        lineZeta (Oc S H) (27 * σ / 2 + t, 0) (d0 S H) 0| < eps S / 20 := by
  have hSp := h.S_pos
  have hN := h.two_le
  have hS8 := h.S_ge
  have hσ : (0 : K) ≤ σ := Nat.cast_nonneg σ
  set x : K := 27 * σ / 2 + t with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hSx : 0 < S - x := by have := h.hS; nlinarith
  rw [lineZeta_d0 S H x X, lineZeta_d0 S H x 0]
  have hHS : 0 ≤ H - S + x := by have := h.hH1; linarith
  have ha : (H + 2 * rho S) / (S - x) - 1 = (H - S + x + 3 / S) / (S - x) := by
    simp only [rho]; field_simp; ring
  have e : 2 * rho S + ((H + 2 * rho S) / (S - x) - 1) * (X + 1) -
      (2 * rho S + ((H + 2 * rho S) / (S - x) - 1) * (0 + 1)) =
      (H - S + x + 3 / S) / (S - x) * X := by rw [ha]; ring
  rw [e]
  apply abs_mul_lt_of_le (by positivity) hX
  rw [div_mul_div_comm, mul_comm (S - x) S]
  apply div_lt_eps_div hSp hSx (by norm_num)
  have h3S : 3 / S ≤ 1 := by rw [div_le_one hSp]; linarith
  have h1 : H - S + x + 3 / S ≤ 17 * N + 1 := by have := h.hH2; linarith
  have h2 : (H - S + x + 3 / S) * N ≤ (17 * N + 1) * N :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have := h.hS
  nlinarith

/-- **Band of `p c0`.** Inside the window, the line `p c0` is within `ε/10` of `Z(σ, 2t/3)`. -/
theorem band_c0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N)
    {X : K} (hX : |X| ≤ 57 * N / S) :
    |lineZeta (Oc S H) (27 * σ / 2 + t, 0) (c0 S H) X - Zs S H σ (2 * t / 3)| < eps S / 10 := by
  have h1 := sl1_c0 h ht0 hx
  have h2 := sl2_c0 h ht0 hx hX
  have he : 0 < eps S := by have := h.S_pos; simp only [eps]; positivity
  rw [abs_lt] at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Band of `p d0`.** Inside the window, the line `p d0` is within `ε/10` of
`Z(σ, 2 + 2t/3)`. -/
theorem band_d0 (h : ScaleHyp N S H) (ht0 : 0 ≤ t) (hx : 27 * (σ : K) / 2 + t ≤ 14 * N)
    {X : K} (hX : |X| ≤ 57 * N / S) :
    |lineZeta (Oc S H) (27 * σ / 2 + t, 0) (d0 S H) X - Zs S H σ (2 + 2 * t / 3)| <
      eps S / 10 := by
  have h1 := sl1_d0 h ht0 hx
  have h2 := sl2_d0 h ht0 hx hX
  have he : 0 < eps S := by have := h.S_pos; simp only [eps]; positivity
  rw [abs_lt] at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Base

/-! ### Receiver lines (`q c1`, `q d1`) -/

section Receiver

variable {N S H t : K} {T T₀ : K × K} {τ : ℕ}

/-- The standing hypotheses on a receiver: `|T.x|, |T.y| ≤ 50`, offset `t ∈ [0, 3/2]`, and the
coordinate sum `T.x + T.y = T₀.x + T₀.y − 27τ/2` (generalised Lemma 39). -/
structure RecvHyp (T T₀ : K × K) (τ : ℕ) (t : K) : Prop where
  /-- Lower bound on `T.x`. -/
  hx1 : -50 ≤ T.1
  /-- Upper bound on `T.x`. -/
  hx2 : T.1 ≤ 50
  /-- Lower bound on `T.y`. -/
  hy1 : -50 ≤ T.2
  /-- Upper bound on `T.y`. -/
  hy2 : T.2 ≤ 50
  /-- The offset is nonnegative. -/
  ht0 : 0 ≤ t
  /-- The offset is at most the segment length `3/2`. -/
  ht1 : t ≤ 3 / 2
  /-- Coordinate sums spaced by `27/2` (generalised Lemma 39). -/
  hsum : T.1 + T.2 = T₀.1 + T₀.2 - 27 * τ / 2

/-- The receiver slab centre in closed form: `Ξ(τ, 1 − 2t/3) = −(T.x + t + T.y)/S`. -/
theorem Xis_recv (hS : S ≠ 0) (hT : T.1 + T.2 = T₀.1 + T₀.2 - 27 * τ / 2) :
    Xis S T₀ τ (1 - 2 * t / 3) = -(T.1 + t + T.2) / S := by
  simp only [Xis, xiRef, delta, rho]
  field_simp
  linear_combination 2 * hT

/-- **(SL3)** The line `q c1` crosses `X = 0` within `ε/16` of the slab centre
`Ξ(τ, 1 − 2t/3)`. -/
theorem sl3_c1 (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (c1 S H) 0 - Xis S T₀ τ (1 - 2 * t / 3)| <
      eps S / 16 := by
  have hSp := h.S_pos
  have hS8 := h.S_ge
  obtain ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩ := hr
  have hu : 0 < S + (T.1 + t) := by linarith
  rw [lineXi_c1 S H 0 t T hSp.ne' hu.ne', Xis_recv hSp.ne' hsum]
  have e : (T.1 + t + T.2) * (0 - 1) / (S + (T.1 + t)) - -(T.1 + t + T.2) / S =
      ((T.1 + t + T.2) * (T.1 + t)) / (S * (S + (T.1 + t))) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < S * (S + (T.1 + t)))]
  apply div_lt_eps_div hSp hu (by norm_num)
  have hv : |T.1 + t + T.2| ≤ 102 := by rw [abs_le]; constructor <;> linarith
  have hu' : |T.1 + t| ≤ 52 := by rw [abs_le]; constructor <;> linarith
  have hm : |(T.1 + t + T.2) * (T.1 + t)| ≤ 102 * 52 := by
    rw [abs_mul]; exact mul_le_mul hv hu' (abs_nonneg _) (by norm_num)
  nlinarith

/-- **(SL3')** The line `q d1` crosses `X = 0` within `ε/16` of the slab centre
`Ξ(τ, 3 − 2t/3)`. -/
theorem sl3_d1 (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (d1 S H) 0 - Xis S T₀ τ (3 - 2 * t / 3)| <
      eps S / 16 := by
  have hSp := h.S_pos
  have hS8 := h.S_ge
  have hX3 : Xis S T₀ τ (3 - 2 * t / 3) = Xis S T₀ τ (1 - 2 * t / 3) + 2 * rho S := by
    simp only [Xis]; ring
  obtain ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩ := hr
  have hu : 0 < S + (T.1 + t) := by linarith
  rw [lineXi_d1 S H 0 t T hSp.ne' hu.ne', hX3, Xis_recv hSp.ne' hsum]
  have e : rho S + (T.1 + t + T.2 - 3 / 2) * (0 - 1) / (S + (T.1 + t)) -
      (-(T.1 + t + T.2) / S + 2 * rho S) =
      ((T.1 + t + T.2 - 3 / 2) * (T.1 + t)) / (S * (S + (T.1 + t))) := by
    simp only [rho]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < S * (S + (T.1 + t)))]
  apply div_lt_eps_div hSp hu (by norm_num)
  have hv : |T.1 + t + T.2 - 3 / 2| ≤ 102 := by rw [abs_le]; constructor <;> linarith
  have hu' : |T.1 + t| ≤ 52 := by rw [abs_le]; constructor <;> linarith
  have hm : |(T.1 + t + T.2 - 3 / 2) * (T.1 + t)| ≤ 102 * 52 := by
    rw [abs_mul]; exact mul_le_mul hv hu' (abs_nonneg _) (by norm_num)
  nlinarith

/-- A slope-part bound for the receiver lines: `|A X/(S + u)| < ε/8` when `|A| ≤ 102`,
`|X| ≤ 57N/S`, `−52 ≤ u`. -/
theorem recv_slope_bound (h : ScaleHyp N S H) {A u X : K} (hA : |A| ≤ 102) (hu : -52 ≤ u)
    (hX : |X| ≤ 57 * N / S) : |A * X / (S + u)| < eps S / 8 := by
  have hSp := h.S_pos
  have hS8 := h.S_ge
  have hN := h.two_le
  have hSu : 0 < S + u := by linarith
  rw [abs_div, abs_mul, abs_of_pos hSu]
  have h1 : |A| * |X| ≤ 102 * (57 * N / S) :=
    mul_le_mul hA hX (abs_nonneg _) (by norm_num)
  calc |A| * |X| / (S + u) ≤ 102 * (57 * N / S) / (S + u) :=
        div_le_div_of_nonneg_right h1 hSu.le
    _ = (102 * 57 * N) / (S * (S + u)) := by field_simp
    _ < eps S / 8 := by
        apply div_lt_eps_div hSp hSu (by norm_num)
        have := h.hS
        nlinarith

/-- **(SL3'')** Inside the window, the line `q c1` deviates from its value at `X = 0` by less
than `ε/8`. -/
theorem sl3_c1_slope (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) {X : K}
    (hX : |X| ≤ 57 * N / S) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (c1 S H) X -
        lineXi (Oc S H) (place S H (T.1 + t, T.2)) (c1 S H) 0| < eps S / 8 := by
  have hSp := h.S_pos
  have hS8 := h.S_ge
  obtain ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩ := hr
  have hu : 0 < S + (T.1 + t) := by linarith
  rw [lineXi_c1 S H X t T hSp.ne' hu.ne', lineXi_c1 S H 0 t T hSp.ne' hu.ne']
  have e : (T.1 + t + T.2) * (X - 1) / (S + (T.1 + t)) -
      (T.1 + t + T.2) * (0 - 1) / (S + (T.1 + t)) = (T.1 + t + T.2) * X / (S + (T.1 + t)) := by
    field_simp; ring
  rw [e]
  exact recv_slope_bound h (by rw [abs_le]; constructor <;> linarith) (by linarith) hX

/-- **(SL3''')** Inside the window, the line `q d1` deviates from its value at `X = 0` by less
than `ε/8`. -/
theorem sl3_d1_slope (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) {X : K}
    (hX : |X| ≤ 57 * N / S) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (d1 S H) X -
        lineXi (Oc S H) (place S H (T.1 + t, T.2)) (d1 S H) 0| < eps S / 8 := by
  have hSp := h.S_pos
  have hS8 := h.S_ge
  obtain ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩ := hr
  have hu : 0 < S + (T.1 + t) := by linarith
  rw [lineXi_d1 S H X t T hSp.ne' hu.ne', lineXi_d1 S H 0 t T hSp.ne' hu.ne']
  have e : rho S + (T.1 + t + T.2 - 3 / 2) * (X - 1) / (S + (T.1 + t)) -
      (rho S + (T.1 + t + T.2 - 3 / 2) * (0 - 1) / (S + (T.1 + t))) =
      (T.1 + t + T.2 - 3 / 2) * X / (S + (T.1 + t)) := by
    field_simp; ring
  rw [e]
  exact recv_slope_bound h (by rw [abs_le]; constructor <;> linarith) (by linarith) hX

/-- **Band of `q c1`.** Inside the window, the line `q c1` is within `ε/4` of
`Ξ(τ, 1 − 2t/3)`. -/
theorem band_c1 (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) {X : K}
    (hX : |X| ≤ 57 * N / S) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (c1 S H) X - Xis S T₀ τ (1 - 2 * t / 3)| <
      eps S / 4 := by
  have h1 := sl3_c1 h hr
  have h2 := sl3_c1_slope h hr hX
  have he : 0 < eps S := by have := h.S_pos; simp only [eps]; positivity
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Band of `q d1`.** Inside the window, the line `q d1` is within `ε/4` of
`Ξ(τ, 3 − 2t/3)`. -/
theorem band_d1 (h : ScaleHyp N S H) (hr : RecvHyp T T₀ τ t) {X : K}
    (hX : |X| ≤ 57 * N / S) :
    |lineXi (Oc S H) (place S H (T.1 + t, T.2)) (d1 S H) X - Xis S T₀ τ (3 - 2 * t / 3)| <
      eps S / 4 := by
  have h1 := sl3_d1 h hr
  have h2 := sl3_d1_slope h hr hX
  have he : 0 < eps S := by have := h.S_pos; simp only [eps]; positivity
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Receiver

/-! ### Band separation (SL4) -/

section Separation

variable {S H : K}

/-- **(SL4)** Consecutive L-bands are separated: `Z(σ, 3) + ε < Z(σ + 1, 0) − ε` (gap
`6ρ − 2ε`). -/
theorem sl4_L (hS : 0 < S) (σ : ℕ) : Zs S H σ 3 + eps S < Zs S H (σ + 1) 0 - eps S := by
  simp only [Zs, zetaO, delta, rho, eps]
  push_cast
  rw [← sub_pos]
  have e : (H - S) / S + ((σ : K) + 1) * (27 / (2 * S)) + 0 * (3 / (2 * S)) - 1 / (8 * S) -
      ((H - S) / S + (σ : K) * (27 / (2 * S)) + 3 * (3 / (2 * S)) + 1 / (8 * S)) =
      35 / (4 * S) := by field_simp; ring
  rw [e]; positivity

/-- **(SL4)** Consecutive R-bands are separated: `Ξ(τ, 3) + ε < Ξ(τ + 1, 0) − ε`. -/
theorem sl4_R (hS : 0 < S) (T₀ : K × K) (τ : ℕ) :
    Xis S T₀ τ 3 + eps S < Xis S T₀ (τ + 1) 0 - eps S := by
  simp only [Xis, delta, rho, eps]
  push_cast
  rw [← sub_pos]
  have e : xiRef S T₀ + ((τ : K) + 1) * (27 / (2 * S)) + 0 * (3 / (2 * S)) - 1 / (8 * S) -
      (xiRef S T₀ + (τ : K) * (27 / (2 * S)) + 3 * (3 / (2 * S)) + 1 / (8 * S)) =
      35 / (4 * S) := by field_simp; ring
  rw [e]; positivity

/-- Slab centres are increasing in `γ`. -/
theorem Zs_mono (hS : 0 < S) (σ : ℕ) {γ γ' : K} (h : γ ≤ γ') : Zs S H σ γ ≤ Zs S H σ γ' := by
  simp only [Zs, rho]
  have : 0 < 3 / (2 * S) := by positivity
  nlinarith

/-- Slab centres are increasing in `γ`. -/
theorem Xis_mono (hS : 0 < S) (T₀ : K × K) (τ : ℕ) {γ γ' : K} (h : γ ≤ γ') :
    Xis S T₀ τ γ ≤ Xis S T₀ τ γ' := by
  simp only [Xis, rho]
  have : 0 < 3 / (2 * S) := by positivity
  nlinarith

/-- L-bands of different slots are ordered: `Z(σ, 3) + ε < Z(σ', 0) − ε` for `σ < σ'`. -/
theorem Zs_band_lt (hS : 0 < S) {σ σ' : ℕ} (h : σ < σ') :
    Zs S H σ 3 + eps S < Zs S H σ' 0 - eps S := by
  have h1 := sl4_L (H := H) hS σ
  have h2 : Zs S H (σ + 1) 0 ≤ Zs S H σ' 0 := by
    simp only [Zs, delta]
    push_cast
    have : ((σ + 1 : ℕ) : K) ≤ σ' := by exact_mod_cast h
    have hd : 0 < 27 / (2 * S) := by positivity
    push_cast at this
    nlinarith
  linarith

/-- R-bands of different receivers are ordered: `Ξ(τ, 3) + ε < Ξ(τ', 0) − ε` for `τ < τ'`. -/
theorem Xis_band_lt (hS : 0 < S) (T₀ : K × K) {τ τ' : ℕ} (h : τ < τ') :
    Xis S T₀ τ 3 + eps S < Xis S T₀ τ' 0 - eps S := by
  have h1 := sl4_R hS T₀ τ
  have h2 : Xis S T₀ (τ + 1) 0 ≤ Xis S T₀ τ' 0 := by
    simp only [Xis, delta]
    push_cast
    have : ((τ + 1 : ℕ) : K) ≤ τ' := by exact_mod_cast h
    have hd : 0 < 27 / (2 * S) := by positivity
    push_cast at this
    nlinarith
  linarith

end Separation

end Inequalities

end ArtGallery.Sec5.Corridor

end
