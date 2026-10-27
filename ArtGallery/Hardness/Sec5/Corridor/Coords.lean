module

public import ArtGallery.Hardness.Sec5.Corridor.CopyCorridor

/-!
# Section 5: corridors — local coordinates of the corridor vertices

All corridor vertices in the local frame at `O = Oc = (S + 1, H + 1)`, in units of
`ε = 1/(8S)`: `lX z = 8S (z.x − O.x)`, `lY z = 8S (z.y − O.y)` (docs/section5/04_corridor.md,
08_proof_plan.md §6 "corridor shape facts").

**Atoms of pair `k`.**  `η = H − S ∈ [1, 3N]`, `b = 27σ_k/2 ∈ [0, 14N]`, the receiver template
endpoint `T_τ = (u, w)` with `|u|, |w| ≤ 50` (`τ = τ_k`).  In `ε`-units the walls of pair `k` are
`ℓ = Lw/ε = 8(η + b) + 22` (`lwE`) and `r = Rw/ε = 10 − 8(u + w)` (`rwE`); consecutive pairs
satisfy `r_{k+1} = r_k − 108` and `ℓ_{k+1} ≥ ℓ_k + 108`.

**Exact positions** (`lX_*`, `lY_*`): apex `((r−ℓ)/2, (r+ℓ)/2)`, mouth corners
`z1 = ((r−ℓ)/2 + 3, (r+ℓ)/2 − 3)`, `z0 = ((r−ℓ)/2 − 3, (r+ℓ)/2 − 3)`, valley
`((r_k − ℓ_{k−1})/2 + 1/4, (r_k + ℓ_{k−1})/2 + 1/4)` (i.e. `(ζ, ξ) = (ℓ_{k−1}, r_k + 1/2)`), the corners `c0, c1, d0, d1`.

**Axes.**  For shadow corners `O + (X₀, Y₀)`, `O + (X₁, Y₀)` the axis function of the copy pair is
`L(z) = (α X + β Y + γ)/S` in local coordinates (`copyPair_L_local`).  The umbra axis is
`Y = (hX + g)/D` with `h = η + w`, `g = η + b − u − w`, `D = 2S + u − b` (`lY_onUmbra`), within
`1/8` (in `ε`-units, inside the window `|lX| ≤ 456N`) of the horizontal line `lY = 4g = (ℓ+r)/2 − 16`
(`axis_approx`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

/-! ## Rounding -/

/-- Rounding half to even is within `1/2` of its argument. -/
theorem abs_roundHalfEven_sub (q : ℚ) : |(roundHalfEven q : ℚ) - q| ≤ 1 / 2 := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q.num : ℚ) / ((q.den : ℤ) : ℚ) = q := by
    rw [show ((q.den : ℤ) : ℚ) = (q.den : ℚ) by push_cast; rfl]; exact Rat.num_div_den q
  unfold roundHalfEven
  simp only
  generalize q.num = n at hq ⊢
  generalize (q.den : ℤ) = d at hd hq ⊢
  have hdiv := Int.mul_ediv_add_emod n d
  have hr0 := Int.emod_nonneg n (ne_of_gt hd)
  have hr1 := Int.emod_lt_of_pos n hd
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hq' : q = ((n / d : ℤ) : ℚ) + ((n % d : ℤ) : ℚ) / (d : ℚ) := by
    rw [← hq]
    have : (n : ℚ) = (d : ℚ) * ((n / d : ℤ) : ℚ) + ((n % d : ℤ) : ℚ) := by
      exact_mod_cast hdiv.symm
    rw [this]
    field_simp
  subst hq'
  generalize n / d = a at hdiv ⊢
  generalize n % d = r at hdiv hr0 hr1 ⊢
  have hr0' : (0 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr0
  have hr1' : (r : ℚ) < (d : ℚ) := by exact_mod_cast hr1
  have hrd : (r : ℚ) / (d : ℚ) < 1 := by rw [div_lt_one hdq]; exact hr1'
  have hrd0 : 0 ≤ (r : ℚ) / (d : ℚ) := div_nonneg hr0' hdq.le
  rw [abs_le]
  split_ifs with h1 h2 h3
  · have h1' : 2 * (r : ℚ) < (d : ℚ) := by exact_mod_cast h1
    have : (r : ℚ) / (d : ℚ) < 1 / 2 := by rw [div_lt_iff₀ hdq]; linarith
    constructor <;> linarith
  · have h2' : (d : ℚ) < 2 * (r : ℚ) := by exact_mod_cast h2
    have : 1 / 2 < (r : ℚ) / (d : ℚ) := by rw [lt_div_iff₀ hdq]; linarith
    push_cast
    constructor <;> linarith
  · have h3' : 2 * (r : ℚ) = (d : ℚ) := by
      have : 2 * r = d := by omega
      exact_mod_cast this
    have : (r : ℚ) / (d : ℚ) = 1 / 2 := by rw [div_eq_iff hdq.ne']; linarith
    rw [this]
    constructor <;> linarith
  · have h3' : 2 * (r : ℚ) = (d : ℚ) := by
      have : 2 * r = d := by omega
      exact_mod_cast this
    have : (r : ℚ) / (d : ℚ) = 1 / 2 := by rw [div_eq_iff hdq.ne']; linarith
    rw [this]
    push_cast
    constructor <;> linarith

/-! ## The axis function in local coordinates -/

/-- **The axis function of a copy pair in local coordinates.**  For shadow corners
`k0 = O + (X₀, Y₀)`, `k1 = O + (X₁, Y₀)` (`O = (S + 1, H + 1)`), base slot `σ` and receiver template
endpoint `T = (u, w)`: `S · L(z) = α X + β Y + γ` with `X = z.x − O.x`, `Y = z.y − O.y`,
`α = S(2 + Y₀) − H − w − Y₀ − 1`, `β = S(3 − X₁) + X₀ + u − 27σ/2 + 1`,
`γ = H X₀ − 2S X₁ − 3S Y₀ + X₀ + X₁ w − u Y₀ + (27σ/2) Y₀ − Y₀`. -/
theorem copyPair_L_local {S H : ℚ} (hS : S ≠ 0) (σ : ℕ) (T : ℚ × ℚ) (X₀ X₁ Y₀ : ℚ)
    (z : ℚ × ℚ) :
    (copyPair S H σ T (S + 1 + X₀, H + 1 + Y₀) (S + 1 + X₁, H + 1 + Y₀)).L z =
      ((S * (2 + Y₀) - H - T.2 - Y₀ - 1) * (z.1 - (S + 1)) +
        (S * (3 - X₁) + X₀ + T.1 - 27 * σ / 2 + 1) * (z.2 - (H + 1)) +
        (H * X₀ - 2 * S * X₁ - 3 * S * Y₀ + X₀ + X₁ * T.2 - T.1 * Y₀ + 27 * σ / 2 * Y₀ - Y₀)) /
        S := by
  simp only [copyPair, CopyPair.L, det2, baseA, recvA, place]
  field_simp
  ring

namespace Input

variable (I : Input)

/-! ## Good inputs and atoms -/

/-- The inputs treated here: valid, at least one pair, strictly increasing slots. -/
structure Good (N : ℚ) : Prop extends I.Valid N where
  /-- At least one copied pair. -/
  np_pos : 1 ≤ I.np
  /-- The working slots are strictly increasing. -/
  mono : ∀ k, k + 1 < I.np → I.sigma k < I.sigma (k + 1)

/-- Local abscissa in units of `ε`: `8S (z.x − O.x)`. -/
def lX (z : ℚ × ℚ) : ℚ := 8 * I.S * (z.1 - I.O.1)

/-- Local ordinate in units of `ε`: `8S (z.y − O.y)`. -/
def lY (z : ℚ × ℚ) : ℚ := 8 * I.S * (z.2 - I.O.2)

/-- `η = H − S`. -/
def eta : ℚ := I.H - I.S

/-- `b = 27σ_k/2`: the left end of the base slot of pair `k`. -/
def bx (k : ℕ) : ℚ := 27 * (I.sigma k : ℚ) / 2

/-- `u = T_τ.x` for `τ = τ_k`. -/
def tu (k : ℕ) : ℚ := (I.Tt (I.tau k)).1

/-- `w = T_τ.y` for `τ = τ_k`. -/
def tw (k : ℕ) : ℚ := (I.Tt (I.tau k)).2

/-- `ℓ = Lw/ε = 8(η + b) + 22`. -/
def lwE (k : ℕ) : ℚ := 8 * (I.eta + I.bx k) + 22

/-- `r = Rw/ε = 10 − 8(u + w)`. -/
def rwE (k : ℕ) : ℚ := 10 - 8 * (I.tu k + I.tw k)

/-- Umbra axis slope numerator `h = η + w`. -/
def hh (k : ℕ) : ℚ := I.eta + I.tw k

/-- Umbra axis offset numerator `g = η + b − u − w`. -/
def gg (k : ℕ) : ℚ := I.eta + I.bx k - (I.tu k + I.tw k)

/-- Umbra axis denominator `D = 2S + u − b`. -/
def DD (k : ℕ) : ℚ := 2 * I.S + I.tu k - I.bx k

variable {I} {N : ℚ}

theorem Good.S_pos (hg : I.Good N) : 0 < I.S := hg.scale.S_pos

theorem Good.S_eq (hg : I.Good N) : I.S = 200000 * N ^ 2 := hg.scale.hS

theorem Good.N_ge (hg : I.Good N) : 2 ≤ N := hg.scale.two_le

theorem Good.eta_ge (hg : I.Good N) : 1 ≤ I.eta := by
  have := hg.scale.hH1; simp only [eta]; linarith

theorem Good.eta_le (hg : I.Good N) : I.eta ≤ 3 * N := by
  have := hg.scale.hH2; simp only [eta]; linarith

theorem Good.bx_nonneg (_hg : I.Good N) (k : ℕ) : 0 ≤ I.bx k := by
  simp only [bx]; positivity

theorem Good.bx_le (hg : I.Good N) {k : ℕ} (hk : k < I.np) : I.bx k ≤ 14 * N - 3 / 2 := by
  have := hg.slot_le k hk; simp only [bx]; linarith

theorem Good.tau_lt (_hg : I.Good N) {k : ℕ} (hk : k < I.np) : I.tau k < I.np := by
  simp only [tau]; omega

theorem Good.tu_bound (hg : I.Good N) {k : ℕ} (hk : k < I.np) :
    -50 ≤ I.tu k ∧ I.tu k ≤ 50 := by
  obtain ⟨h1, h2, -, -⟩ := hg.T_bound _ (hg.tau_lt hk); exact ⟨h1, h2⟩

theorem Good.tw_bound (hg : I.Good N) {k : ℕ} (hk : k < I.np) :
    -50 ≤ I.tw k ∧ I.tw k ≤ 50 := by
  obtain ⟨-, -, h1, h2⟩ := hg.T_bound _ (hg.tau_lt hk); exact ⟨h1, h2⟩

/-- The slots of different pairs are ordered. -/
theorem Good.sigma_lt (hg : I.Good N) {j k : ℕ} (hjk : j < k) (hk : k < I.np) :
    I.sigma j < I.sigma k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
    · exact (ih h (by omega)).trans (hg.mono k hk)
    · subst h; exact hg.mono j hk

/-! ## Exact identities -/

theorem eps_eq : I.ε = 1 / (8 * I.S) := rfl

theorem O_eq : I.O = (I.S + 1, I.H + 1) := rfl

/-- `Lw = ℓ ε`. -/
theorem Lw_eq (hg : I.Good N) (k : ℕ) : I.Lw k = I.lwE k / (8 * I.S) := by
  have hS := hg.S_pos
  simp only [Lw, Zs, zetaO, delta, rho, Input.ε, eps, lwE, eta, bx]
  field_simp
  ring

/-- `Rw = r ε` (uses the spacing of the receiver coordinate sums). -/
theorem Rw_eq (hg : I.Good N) {k : ℕ} (hk : k < I.np) : I.Rw k = I.rwE k / (8 * I.S) := by
  have hS := hg.S_pos
  have hsum := hg.T_sum _ (hg.tau_lt hk)
  simp only [Rw, Xis, xiRef, delta, rho, Input.ε, eps, rwE, tu, tw]
  rw [show I.T0 = I.Tt 0 from rfl] at hsum ⊢
  field_simp
  linear_combination 16 * hsum

/-- The receiver walls step down by `108` from pair to pair. -/
theorem Good.rwE_succ (hg : I.Good N) {k : ℕ} (hk : k + 1 < I.np) :
    I.rwE (k + 1) = I.rwE k - 108 := by
  have h1 := hg.T_sum _ (hg.tau_lt hk)
  have h2 := hg.T_sum _ (hg.tau_lt (show k < I.np by omega))
  have ht : (I.tau k : ℚ) = (I.tau (k + 1) : ℚ) + 1 := by
    simp only [tau]; push_cast [show I.np - 1 - k = I.np - 1 - (k + 1) + 1 by omega]; ring
  simp only [rwE, tu, tw]
  rw [ht] at h2
  linear_combination 8 * h2 - 8 * h1

/-- The base walls step up by at least `108` from pair to pair. -/
theorem Good.lwE_succ (hg : I.Good N) {k : ℕ} (hk : k + 1 < I.np) :
    I.lwE k + 108 ≤ I.lwE (k + 1) := by
  have h := hg.mono k hk
  have h' : ((I.sigma k : ℕ) : ℚ) + 1 ≤ (I.sigma (k + 1) : ℚ) := by exact_mod_cast h
  simp only [lwE, bx]
  linarith

/-- `(ℓ + r)/2 = 4g + 16`. -/
theorem lw_add_rw (k : ℕ) : (I.lwE k + I.rwE k) / 2 = 4 * I.gg k + 16 := by
  simp only [lwE, rwE, gg]; ring

theorem lX_def (z : ℚ × ℚ) : I.lX z = 8 * I.S * (z.1 - (I.S + 1)) := rfl

theorem lY_def (z : ℚ × ℚ) : I.lY z = 8 * I.S * (z.2 - (I.H + 1)) := rfl

/-- Recovering a point from its local coordinates. -/
theorem fst_eq_of_lX (hg : I.Good N) (z : ℚ × ℚ) : z.1 = I.S + 1 + I.lX z / (8 * I.S) := by
  have := hg.S_pos; simp only [lX_def]; field_simp; ring

theorem snd_eq_of_lY (hg : I.Good N) (z : ℚ × ℚ) : z.2 = I.H + 1 + I.lY z / (8 * I.S) := by
  have := hg.S_pos; simp only [lY_def]; field_simp; ring

theorem lX_c0 : I.lX (c0 I.S I.H) = -(8 * I.S) := by simp only [lX_def, c0]; ring

theorem lY_c0 : I.lY (c0 I.S I.H) = -(8 * I.S) := by simp only [lY_def, c0]; ring

theorem lX_c1 : I.lX (c1 I.S I.H) = 8 * I.S := by simp only [lX_def, c1]; ring

theorem lY_c1 : I.lY (c1 I.S I.H) = -(8 * I.S) := by simp only [lY_def, c1]; ring

theorem lX_d0 : I.lX (d0 I.S I.H) = -(8 * I.S) := by simp only [lX_def, d0]; ring

theorem lX_d1 : I.lX (d1 I.S I.H) = 8 * I.S := by simp only [lX_def, d1]; ring

section Positions

variable (hg : I.Good N)
include hg

theorem lX_apex {k : ℕ} (hk : k < I.np) : I.lX (I.apex k) = (I.rwE k - I.lwE k) / 2 := by
  have := hg.S_pos
  simp only [lX_def, apex, ofZetaXi, Input.O, Oc, Lw_eq hg, Rw_eq hg hk]
  field_simp; ring

theorem lY_apex {k : ℕ} (hk : k < I.np) : I.lY (I.apex k) = (I.rwE k + I.lwE k) / 2 := by
  have := hg.S_pos
  simp only [lY_def, apex, ofZetaXi, Input.O, Oc, Lw_eq hg, Rw_eq hg hk]
  field_simp; ring

theorem yN_eq' {k : ℕ} (hk : k < I.np) :
    I.yN k = ((I.lwE k + I.rwE k) / 2 - 3) / (8 * I.S) := by
  have := hg.S_pos
  rw [yN_eq, Lw_eq hg, Rw_eq hg hk, Input.ε, eps]
  field_simp

theorem lX_z1 {k : ℕ} (hk : k < I.np) : I.lX (I.z1 k) = (I.rwE k - I.lwE k) / 2 + 3 := by
  have := hg.S_pos
  simp only [lX_def, z1, ofLocal, Input.O, Oc, yN_eq' hg hk, Rw_eq hg hk]
  field_simp; ring

theorem lY_z1 {k : ℕ} (hk : k < I.np) : I.lY (I.z1 k) = (I.lwE k + I.rwE k) / 2 - 3 := by
  have := hg.S_pos
  simp only [lY_def, z1, ofLocal, Input.O, Oc, yN_eq' hg hk]
  field_simp; ring

theorem lX_z0 {k : ℕ} (hk : k < I.np) : I.lX (I.z0 k) = (I.rwE k - I.lwE k) / 2 - 3 := by
  have := hg.S_pos
  simp only [lX_def, z0, ofLocal, Input.O, Oc, yN_eq' hg hk, Lw_eq hg]
  field_simp; ring

theorem lY_z0 {k : ℕ} (hk : k < I.np) : I.lY (I.z0 k) = (I.lwE k + I.rwE k) / 2 - 3 := by
  have := hg.S_pos
  simp only [lY_def, z0, ofLocal, Input.O, Oc, yN_eq' hg hk]
  field_simp; ring

theorem lX_valley {k : ℕ} (hk : k < I.np) :
    I.lX (I.valley k) = (I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4 := by
  have := hg.S_pos
  simp only [lX_def, valley, ofZetaXi, Input.O, Oc, Lw_eq hg, Rw_eq hg hk, Input.ε, eps]
  field_simp; ring

theorem lY_valley {k : ℕ} (hk : k < I.np) :
    I.lY (I.valley k) = (I.rwE k + I.lwE (k - 1)) / 2 + 1 / 4 := by
  have := hg.S_pos
  simp only [lY_def, valley, ofZetaXi, Input.O, Oc, Lw_eq hg, Rw_eq hg hk, Input.ε, eps]
  field_simp; ring

theorem lY_d0 : I.lY (d0 I.S I.H) = -(8 * I.S) + 24 := by
  have := hg.S_pos
  simp only [lY_def, d0, rho]; field_simp; ring

theorem lY_d1 : I.lY (d1 I.S I.H) = -(8 * I.S) + 12 := by
  have := hg.S_pos
  simp only [lY_def, d1, rho]; field_simp; ring

end Positions

/-! ## The umbra axis -/

theorem c0_eq_local : c0 I.S I.H = (I.S + 1 + -1, I.H + 1 + -1) := by
  simp only [c0, Prod.mk.injEq]; constructor <;> ring

theorem c1_eq_local : c1 I.S I.H = (I.S + 1 + 1, I.H + 1 + -1) := by
  simp only [c1, Prod.mk.injEq]; constructor <;> ring

theorem onUmbra_fst' (k : ℕ) (x : ℚ) : (I.onUmbra k x).1 = x := rfl

/-- **The umbra axis function**: `S · L(z) = D Y − h X − g` in local coordinates. -/
theorem umbraQ_L_eq (hg : I.Good N) (k : ℕ) (z : ℚ × ℚ) :
    (I.umbraQ k).L z = (I.DD k * (z.2 - (I.H + 1)) - I.hh k * (z.1 - (I.S + 1)) - I.gg k) /
      I.S := by
  have hS := hg.S_pos
  rw [umbraQ, c0_eq_local, c1_eq_local, copyPair_L_local hS.ne']
  simp only [DD, hh, gg, eta, tu, tw, bx]
  congr 1
  ring

theorem Good.DD_pos (hg : I.Good N) {k : ℕ} (hk : k < I.np) : I.S ≤ I.DD k := by
  have h1 := hg.bx_le hk
  have h2 := (hg.tu_bound hk).1
  have h3 := hg.scale.S_ge
  have hN := hg.N_ge
  have hS := hg.S_eq
  simp only [DD]
  nlinarith

/-- Points of the umbra axis: `Y = (h X + g)/D`. -/
theorem onUmbra_snd (hg : I.Good N) {k : ℕ} (hk : k < I.np) (x : ℚ) :
    (I.onUmbra k x).2 = I.H + 1 + (I.hh k * (x - (I.S + 1)) + I.gg k) / I.DD k := by
  have hL := L_onLine_zero (umbraQ_hyp hg.toValid k) (umbraQ_adm hg.toValid hk) x
  rw [← f0_eq, ← f1_eq] at hL
  have hS := hg.S_pos
  have hD := (hg.DD_pos hk)
  change (I.umbraQ k).L (I.onUmbra k x) = 0 at hL
  rw [umbraQ_L_eq hg, onUmbra_fst', div_eq_zero_iff] at hL
  rcases hL with hL | hL
  · have hY : (I.onUmbra k x).2 - (I.H + 1) =
        (I.hh k * (x - (I.S + 1)) + I.gg k) / I.DD k := by
      rw [eq_div_iff (by linarith)]; linarith
    linarith
  · exact absurd hL hS.ne'

theorem onUmbra_fst (k : ℕ) (x : ℚ) : (I.onUmbra k x).1 = x := rfl

/-- The umbra axis in `ε`-units: `lY = (h lX + 8S g)/D`. -/
theorem lY_onUmbra (hg : I.Good N) {k : ℕ} (hk : k < I.np) (x : ℚ) :
    I.lY (I.onUmbra k x) =
      (I.hh k * I.lX (I.onUmbra k x) + 8 * I.S * I.gg k) / I.DD k := by
  have hS := hg.S_pos
  have hD := (hg.DD_pos hk)
  rw [lY_def, onUmbra_snd hg hk, lX_def, onUmbra_fst]
  field_simp
  ring

/-- Above the umbra axis in `ε`-units: `8 S² L(z) = D lY − h lX − 8S g`. -/
theorem umbraQ_L_lY (hg : I.Good N) (k : ℕ) (z : ℚ × ℚ) :
    8 * I.S ^ 2 * (I.umbraQ k).L z = I.DD k * I.lY z - I.hh k * I.lX z - 8 * I.S * I.gg k := by
  have hS := hg.S_pos
  rw [umbraQ_L_eq hg, lY_def, lX_def]
  field_simp

end Input

end ArtGallery.Sec5.Corridor

end
