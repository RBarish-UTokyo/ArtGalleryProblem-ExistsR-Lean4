module

public import ArtGallery.Hardness.Sec5.Corridor.SGView

/-!
# Section 5: corridors — the receiver conditions

The receiver `q_k(t)` (`(I.umbraQ k).q t`, `t ∈ [0, 3/2]`) of pair `k` looks into the corridor
along lines that are almost parallel to the wall `ξ = Rw_k` (slope `−1`): along a line of `q_k`
the coordinate `ξ` drifts by only `O(1/S)` per unit of `ζ`.  Its lines through the nook mouth
corner `z1_k` (on `ξ = Rw_k`) must pass west of the reflex corner `z'_k` and below the valley
`v_k`, and its line through `z'_k` must pass below `v_k`
(docs/section5/04_corridor.md, §Receiver conditions):

* `Good.recv_zp`: `det(q_k(t), z'_k, z1_k) ≥ 0`;
* `Good.recv_valley_z1`: `det(q_k(t), v_k, z1_k) ≥ 0` (`k ≥ 1`);
* `Good.recv_valley_zp`: `det(q_k(t), v_k, z'_k) ≥ 0` (`k ≥ 1`).

They hold because `z'_k` lies at `ξ ∈ [r + 1/16, r + 5/16]` (`Good.xi_zp`, `z'_k` rounded up plus
one grid unit) and `v_k` at `ξ = r + 1/2` (in `ε`-units), against a drift of less than `ε/100`.

Method: in the local `ε`-coordinates `ζ = lY − lX`, `ξ = lY + lX`,
`2 (8S)² det(q, a, b) = (ζ_b − ζ_q)(ξ_a − ξ_b) − (ζ_a − ζ_b)(ξ_b − ξ_q)` (`det2_zx`), with
`ζ_b − ζ_q ≈ 32S` huge and the other three factors bounded (`det2_nonneg_of_zx`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

namespace Input

variable {I : Input} {N : ℚ}

/-- The determinant in local `ζξ`-coordinates (`ε`-units). -/
theorem det2_zx (hg : I.Good N) (q a b : ℚ × ℚ) :
    2 * (8 * I.S) ^ 2 * det2 q a b =
      ((I.lY b - I.lX b) - (I.lY q - I.lX q)) * ((I.lY a + I.lX a) - (I.lY b + I.lX b)) -
        ((I.lY a - I.lX a) - (I.lY b - I.lX b)) * ((I.lY b + I.lX b) - (I.lY q + I.lX q)) := by
  have := hg.S_pos
  simp only [lX_def, lY_def, det2]
  ring

/-- **Sign of a determinant from local bounds.**  If `ζ_b − ζ_q ≥ P ≥ 0`, `ξ_a − ξ_b ≥ m ≥ 0`,
`|ζ_a − ζ_b| ≤ A`, `|ξ_b − ξ_q| ≤ B` and `A B ≤ P m`, then `det(q, a, b) ≥ 0`. -/
theorem det2_nonneg_of_zx (hg : I.Good N) {q a b : ℚ × ℚ} {P m A B : ℚ} (hP0 : 0 ≤ P)
    (hP : P ≤ (I.lY b - I.lX b) - (I.lY q - I.lX q))
    (hm : m ≤ (I.lY a + I.lX a) - (I.lY b + I.lX b)) (hm0 : 0 ≤ m)
    (hA : |(I.lY a - I.lX a) - (I.lY b - I.lX b)| ≤ A)
    (hB : |(I.lY b + I.lX b) - (I.lY q + I.lX q)| ≤ B) (hAB : A * B ≤ P * m) :
    0 ≤ det2 q a b := by
  have hS := hg.S_pos
  have e := det2_zx hg q a b
  set ζ := (I.lY b - I.lX b) - (I.lY q - I.lX q)
  set ξ := (I.lY a + I.lX a) - (I.lY b + I.lX b)
  set α := (I.lY a - I.lX a) - (I.lY b - I.lX b)
  set β := (I.lY b + I.lX b) - (I.lY q + I.lX q)
  have h1 : P * m ≤ ζ * ξ := by
    have : ζ * ξ - P * m = (ζ - P) * ξ + P * (ξ - m) := by ring
    have := mul_nonneg (sub_nonneg.2 hP) (hm0.trans hm)
    have := mul_nonneg hP0 (sub_nonneg.2 hm)
    linarith
  have h2 : α * β ≤ A * B := by
    have := abs_mul_le_of hA hB
    exact (le_abs_self _).trans this
  have h3 : 0 ≤ 2 * (8 * I.S) ^ 2 * det2 q a b := by rw [e]; linarith
  have h4 : (0 : ℚ) < 2 * (8 * I.S) ^ 2 := by positivity
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg h4 hc
  linarith

/-! ## Local coordinates of the receiver -/

section Recv

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np) {t : ℚ}
include hg

omit hg in
/-- The receiver position in coordinates. -/
theorem umbraQ_q (t : ℚ) :
    (I.umbraQ k).q t = place I.S I.H (I.tu k + t, I.tw k) := by
  rw [umbraQ, copyPair_q]; rfl

theorem lX_recv : I.lX ((I.umbraQ k).q t) = 16 * I.S + 8 * (I.tu k + t) := by
  have := hg.S_pos
  rw [umbraQ_q, lX_def]; simp only [place]; field_simp; ring

theorem lY_recv : I.lY ((I.umbraQ k).q t) = -(16 * I.S) + 8 * I.tw k := by
  have := hg.S_pos
  rw [umbraQ_q, lY_def]; simp only [place]; field_simp; ring

include hk

/-- `ζ` of the receiver: about `−32S`. -/
theorem zeta_recv (ht0 : 0 ≤ t) :
    I.lY ((I.umbraQ k).q t) - I.lX ((I.umbraQ k).q t) ≤ -(32 * I.S) + 800 := by
  rw [lX_recv hg, lY_recv hg]
  have := hg.tu_bound hk; have := hg.tw_bound hk
  linarith

/-- `ξ` of the receiver: `8(u + w + t) ∈ [−800, 812]`. -/
theorem xi_recv (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) :
    -800 ≤ I.lY ((I.umbraQ k).q t) + I.lX ((I.umbraQ k).q t) ∧
      I.lY ((I.umbraQ k).q t) + I.lX ((I.umbraQ k).q t) ≤ 812 := by
  rw [lX_recv hg, lY_recv hg]
  have := hg.tu_bound hk; have := hg.tw_bound hk
  constructor <;> linarith

/-- `ζ` of `z'_k`: `ℓ − 32 ± 1/2`. -/
theorem zeta_zp : |(I.lY (I.zp k) - I.lX (I.zp k)) - (I.lwE k - 32)| ≤ 1 / 2 := by
  have h1 := hg.lX_zp hk; have h2 := hg.lY_zp hk
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

end Recv

/-! ## The receiver conditions -/

/-- **The receiver's lines through `z1_k` pass west of the reflex corner `z'_k`.** -/
theorem Good.recv_zp (hg : I.Good N) {k : ℕ} (hk : k < I.np) {t : ℚ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 3 / 2) : 0 ≤ det2 ((I.umbraQ k).q t) (I.zp k) (I.z1 k) := by
  have hS := hg.scale.S_ge
  have hq := zeta_recv hg hk ht0
  have hqx := xi_recv hg hk ht0 ht1
  have hz := zeta_zp hg hk
  have hxz := hg.xi_zp hk
  have hl := hg.lwE_bound hk
  have hr := hg.rwE_bound hk
  have x1 := lX_z1 hg hk
  have y1 := lY_z1 hg hk
  refine det2_nonneg_of_zx hg (P := 32 * I.S - 806) (m := 1 / 16) (A := 27) (B := 1622)
    (by linarith) ?_ ?_ (by norm_num) ?_ ?_ (by nlinarith)
  · rw [x1, y1]; linarith
  · rw [x1, y1]; linarith
  · rw [x1, y1]; rw [abs_le] at hz ⊢; constructor <;> linarith
  · rw [x1, y1]; rw [abs_le]; constructor <;> linarith

/-- **The receiver's lines through `z1_k` pass below the valley `v_k`** (`k ≥ 1`). -/
theorem Good.recv_valley_z1 (hg : I.Good N) {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k) {t : ℚ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) : 0 ≤ det2 ((I.umbraQ k).q t) (I.valley k) (I.z1 k) := by
  have hS := hg.scale.S_ge
  have hSe := hg.S_eq
  have hN := hg.N_ge
  have hq := zeta_recv hg hk ht0
  have hqx := xi_recv hg hk ht0 ht1
  have hl := hg.lwE_bound hk
  have hl' := hg.lwE_bound (k := k - 1) (by omega)
  have hr := hg.rwE_bound hk
  have x1 := lX_z1 hg hk
  have y1 := lY_z1 hg hk
  have xv := lX_valley hg hk
  have yv := lY_valley hg hk
  refine det2_nonneg_of_zx hg (P := 32 * I.S - 806) (m := 1 / 2) (A := 136 * N + 10)
    (B := 1622) (by linarith) ?_ ?_ (by norm_num) ?_ ?_ (by nlinarith)
  · rw [x1, y1]; linarith
  · rw [x1, y1, xv, yv]; linarith
  · rw [x1, y1, xv, yv]; rw [abs_le]; constructor <;> linarith
  · rw [x1, y1]; rw [abs_le]; constructor <;> linarith

/-- **The receiver's line through `z'_k` passes below the valley `v_k`** (`k ≥ 1`). -/
theorem Good.recv_valley_zp (hg : I.Good N) {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k) {t : ℚ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) : 0 ≤ det2 ((I.umbraQ k).q t) (I.valley k) (I.zp k) := by
  have hS := hg.scale.S_ge
  have hSe := hg.S_eq
  have hN := hg.N_ge
  have hq := zeta_recv hg hk ht0
  have hqx := xi_recv hg hk ht0 ht1
  have hz := zeta_zp hg hk
  have hxz := hg.xi_zp hk
  have hl := hg.lwE_bound hk
  have hl' := hg.lwE_bound (k := k - 1) (by omega)
  have hr := hg.rwE_bound hk
  have xv := lX_valley hg hk
  have yv := lY_valley hg hk
  rw [abs_le] at hz
  refine det2_nonneg_of_zx hg (P := 32 * I.S - 806) (m := 3 / 16) (A := 136 * N + 43)
    (B := 1623) (by linarith) ?_ ?_ (by norm_num) ?_ ?_ (by nlinarith)
  · linarith
  · rw [xv, yv]; linarith
  · rw [xv, yv]; rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

end Input

end ArtGallery.Sec5.Corridor

end
