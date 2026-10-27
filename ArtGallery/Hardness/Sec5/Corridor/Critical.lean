module

public import ArtGallery.Hardness.Sec5.Corridor.Slots

/-!
# Section 5: corridors — location of the critical sets

The critical sets of pair `k` (docs/section5/08_proof_plan.md §6, Lemma V2):

* the **umbra critical points** `X v₀ v₁ = (p(v₀) c0) ∩ (q(v₁) c1)` (`0 ≤ v₁ ≤ v₀ ≤ 3/2`) of the
  umbra copy pair `umbraR k`: they lie inside the window, with `ζ ∈ [Z(σ,0) − ε/10, Z(σ,1) + ε/10]`
  and `ξ ∈ [Ξ(τ,0) − ε/4, Ξ(τ,1) + ε/4]` (`Good.umbra_crit_loc`); in `ε`-units around the apex
  `(X_a, Y_a)`: `|lX − X_a| ≤ 31/5`, `lY ∈ [Y_a − 111/5, Y_a − 49/5]`;
* the **nook top edge** `[n0, n1]` (which contains the nook critical points `X v v`): inside the
  window with `ζ ∈ [ℓ − 33/8, ℓ + 33/8]`, `ξ ∈ [r − 17/8, r + 17/8]` (`ε`-units,
  `Good.nook_edge_loc`).

In particular both critical sets lie in the bands of `σ_k` and `τ_k` only
(`Good.umbra_crit_band`, `Good.nook_edge_band`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- Real local abscissa in `ε`-units. -/
noncomputable def lXR (I : Input) (z : Point) : ℝ := 8 * (I.S : ℝ) * (z.1 - ((I.S : ℝ) + 1))

/-- Real local ordinate in `ε`-units. -/
noncomputable def lYR (I : Input) (z : Point) : ℝ := 8 * (I.S : ℝ) * (z.2 - ((I.H : ℝ) + 1))

theorem lXR_ratPoint (z : ℚ × ℚ) : I.lXR (ratPoint z) = ((I.lX z : ℚ) : ℝ) := by
  simp [lXR, lX_def, ratPoint]

theorem lYR_ratPoint (z : ℚ × ℚ) : I.lYR (ratPoint z) = ((I.lY z : ℚ) : ℝ) := by
  simp [lYR, lY_def, ratPoint]

/-- `8S·ζ = lY − lX`. -/
theorem zeta_lXR (z : Point) :
    8 * (I.S : ℝ) * zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z = I.lYR z - I.lXR z := by
  simp only [zetaOf, Oc, lXR, lYR]; ring

/-- `8S·ξ = lY + lX`. -/
theorem xi_lXR (z : Point) :
    8 * (I.S : ℝ) * xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z = I.lYR z + I.lXR z := by
  simp only [xiOf, Oc, lXR, lYR]; ring

section Bands

variable (hg : I.Good N)
include hg

/-- The L-slab centres in `ε`-units: `8S·Z(σ_k, γ) = ℓ − 22 + 12γ`. -/
theorem Good.Zs_eps (k : ℕ) (γ : ℝ) :
    8 * (I.S : ℝ) * Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) γ = ((I.lwE k : ℚ) : ℝ) - 22 + 12 * γ := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  simp only [Zs, zetaO, delta, rho, lwE, eta, bx]
  push_cast
  field_simp
  ring

/-- The R-slab centres in `ε`-units: `8S·Ξ(τ_k, γ) = r − 22 + 12γ`. -/
theorem Good.Xis_eps {k : ℕ} (hk : k < I.np) (γ : ℝ) :
    8 * (I.S : ℝ) * Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) γ =
      ((I.rwE k : ℚ) : ℝ) - 22 + 12 * γ := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  have hsum := hg.T_sum _ (hg.tau_lt hk)
  have hsum' := congrArg (fun q : ℚ => (q : ℝ)) hsum
  push_cast at hsum'
  have e1 : 8 * (I.S : ℝ) * Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) γ =
      -8 * ((I.T0.1 : ℝ) + 3 / 2 + I.T0.2) + 108 * (I.tau k : ℝ) + 12 * γ := by
    simp only [Xis, xiRef, delta, rho, ratPoint]; field_simp; ring
  rw [e1]
  simp only [rwE, tu, tw]
  push_cast
  linarith

/-- `8S·ε = 1`. -/
theorem Good.eps_eps : 8 * (I.S : ℝ) * eps (I.S : ℝ) = 1 := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  simp only [eps]; field_simp

end Bands

/-! ## The umbra critical points -/

section Umbra

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The receiver hypotheses of pair `k` at offset `t`. -/
theorem Good.recvHyp {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) :
    RecvHyp (ratPoint (I.Tt (I.tau k))) (ratPoint I.T0) (I.tau k) t := by
  obtain ⟨h1, h2, h3, h4⟩ := hg.T_bound _ (hg.tau_lt hk)
  have hs := hg.T_sum _ (hg.tau_lt hk)
  refine ⟨?_, ?_, ?_, ?_, ht0, ht1, ?_⟩ <;> simp only [ratPoint_fst, ratPoint_snd]
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · have : (((I.Tt (I.tau k)).1 + (I.Tt (I.tau k)).2 : ℚ) : ℝ) =
        ((I.T0.1 + I.T0.2 - 27 * (I.tau k) / 2 : ℚ) : ℝ) := by rw [hs]
    push_cast at this; exact this

/-- **Location of the umbra critical points.** -/
theorem Good.umbra_crit_loc {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁)
    (h₁' : v₁ ≤ 3 / 2) :
    let z := (I.umbraR k).X v₀ v₁
    |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S ∧
      Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) (2 * v₀ / 3) - eps (I.S : ℝ) / 10 <
        zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z <
        Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) (2 * v₀ / 3) + eps (I.S : ℝ) / 10 ∧
      Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) (1 - 2 * v₁ / 3) - eps (I.S : ℝ) / 4 <
        xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z <
        Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) (1 - 2 * v₁ / 3) + eps (I.S : ℝ) / 4 := by
  intro z
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hS8 := hsc.S_ge
  have hN := hsc.two_le
  have hNS := hsc.hS
  set C := I.umbraR k
  have hC := umbraR_hyp hg.toValid k
  have hA := umbraR_adm hg.toValid hk
  have hG := CopyPair.G_pos hC hA (t₀ := v₀) (t₁ := v₁) h₀' h₁
  have e0 := C.det2_X_left v₀ v₁
  have e1 := C.det2_X_right hG.ne'
  rw [umbraR_p, umbraR_k0, ratPoint_c0] at e0
  rw [umbraR_q, umbraR_k1, ratPoint_c1] at e1
  -- the slot and the receiver
  have hσ : 27 * ((I.sigma k : ℕ) : ℝ) / 2 + v₀ ≤ 14 * N := by
    have := hg.slot_le k hk
    have : (27 * (I.sigma k : ℚ) / 2 + 3 / 2 : ℚ) ≤ 14 * N := this
    have h' : ((27 * (I.sigma k : ℚ) / 2 + 3 / 2 : ℚ) : ℝ) ≤ ((14 * N : ℚ) : ℝ) :=
      rat_cast_le_of this
    push_cast at h'; linarith
  have hσ0 : (0 : ℝ) ≤ (I.sigma k : ℝ) := Nat.cast_nonneg _
  have hr := hg.recvHyp hk h₁ h₁'
  obtain ⟨hx1, hx2, hy1, hy2, -, -, hsum⟩ := hr
  simp only [ratPoint_fst, ratPoint_snd] at hx1 hx2 hy1 hy2 hsum
  set u : ℝ := ((I.Tt (I.tau k)).1 : ℝ)
  set w : ℝ := ((I.Tt (I.tau k)).2 : ℝ)
  have hu : 0 < (I.S : ℝ) + (u + v₁) := by linarith
  have hx : (I.S : ℝ) - (27 * (I.sigma k : ℝ) / 2 + v₀) > 0 := by nlinarith
  -- `z` lies on both lines
  rw [det2_eq_lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _ (by simp [c0]; linarith)] at e0
  have hcq : (c1 (I.S : ℝ) (I.H : ℝ)).1 - (place (I.S : ℝ) (I.H : ℝ) (u + v₁, w)).1 ≠ 0 := by
    simp only [c1, place]
    have : -1 < (u + v₁) / (I.S : ℝ) := by rw [lt_div_iff₀ hS]; linarith
    linarith
  rw [det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _ hcq] at e1
  have hz0 : zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z = lineZeta (Oc (I.S : ℝ) (I.H : ℝ))
      (27 * (I.sigma k : ℝ) / 2 + v₀, 0) (c0 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) := by
    rcases mul_eq_zero.1 e0 with h | h
    · simp [c0] at h; linarith
    · linarith
  have hz1 : xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z = lineXi (Oc (I.S : ℝ) (I.H : ℝ))
      (place (I.S : ℝ) (I.H : ℝ) (u + v₁, w)) (c1 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) := by
    rcases mul_eq_zero.1 e1 with h | h
    · exact absurd h hcq
    · linarith
  -- the window bound
  set X := z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1 with hXdef
  have hX : |X| ≤ 57 * N / I.S := by
    rw [lineZeta_c0] at hz0
    rw [show (place (I.S : ℝ) (I.H : ℝ) (u + v₁, w)) = place (I.S : ℝ) (I.H : ℝ)
      ((u, w).1 + v₁, (u, w).2) from rfl, lineXi_c1 _ _ _ _ _ hS.ne' hu.ne'] at hz1
    simp only at hz1
    set lam := (I.H : ℝ) / ((I.S : ℝ) - (27 * (I.sigma k : ℝ) / 2 + v₀)) - 1
    set μ := (u + v₁ + w) / ((I.S : ℝ) + (u + v₁))
    have hdiff : xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z - zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z = 2 * X := by
      simp only [xiOf, zetaOf, hXdef]; ring
    have hμ' : (u + v₁ + w) * (X - 1) / ((I.S : ℝ) + (u + v₁)) = μ * (X - 1) := by
      simp only [μ]; ring
    rw [hz0, hz1, hμ'] at hdiff
    have key : X * (2 - μ + lam) = -(μ + lam) := by linarith
    -- bounds on `lam` and `μ`
    have hN2 : 2 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hSN' : 400000 * (N : ℝ) ≤ I.S := by rw [hNS]; linarith
    have hxN : 27 * (I.sigma k : ℝ) / 2 + v₀ ≤ 14 * N := hσ
    have hl0 : 0 ≤ lam := by
      simp only [lam]
      rw [sub_nonneg, le_div_iff₀ hx]; linarith [hsc.hH1]
    have hl1 : lam ≤ 18 * N / I.S := by
      simp only [lam]
      rw [sub_le_iff_le_add, div_le_iff₀ hx]
      have : (18 * N / I.S + 1) * ((I.S : ℝ) - (27 * (I.sigma k : ℝ) / 2 + v₀)) =
          18 * N + I.S - (27 * (I.sigma k : ℝ) / 2 + v₀) -
            18 * N * (27 * (I.sigma k : ℝ) / 2 + v₀) / I.S := by field_simp; ring
      rw [this]
      have h3 : 18 * N * (27 * (I.sigma k : ℝ) / 2 + v₀) / I.S ≤ 1 := by
        rw [div_le_one hS]
        have := mul_le_mul_of_nonneg_left hxN (by linarith : (0 : ℝ) ≤ 18 * N)
        nlinarith
      linarith [hsc.hH2]
    have hμ : |μ| ≤ 103 / I.S := by
      simp only [μ]
      rw [abs_div, abs_of_pos hu, div_le_div_iff₀ hu hS]
      have h102 : |u + v₁ + w| ≤ 102 := by rw [abs_le]; constructor <;> linarith
      calc |u + v₁ + w| * I.S ≤ 102 * I.S := mul_le_mul_of_nonneg_right h102 hS.le
        _ ≤ 103 * ((I.S : ℝ) + (u + v₁)) := by linarith
    have hSN : 18 * (N : ℝ) / I.S ≤ 1 / 1000 := by
      rw [div_le_iff₀ hS]; linarith
    have h103 : 103 / (I.S : ℝ) ≤ 1 / 1000 := by rw [div_le_iff₀ hS]; linarith
    rw [abs_le] at hμ
    have hden : 19 / 10 ≤ 2 - μ + lam := by linarith
    have hnum : |μ + lam| ≤ (103 + 18 * N) / I.S := by
      rw [abs_le, add_div]; constructor <;> linarith
    have : |X| * (2 - μ + lam) = |μ + lam| := by
      rw [← abs_of_pos (show (0 : ℝ) < 2 - μ + lam by linarith), ← abs_mul, key, abs_neg]
    have h1 : |X| * (19 / 10) ≤ (103 + 18 * N) / I.S := by
      have := mul_le_mul_of_nonneg_left hden (abs_nonneg X); linarith
    have h2 : (103 + 18 * (N : ℝ)) / I.S ≤ 57 * N / I.S * (19 / 10) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hS]; linarith
    linarith
  have hX' : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S := by simpa [hXdef, Oc] using hX
  refine ⟨hX', ?_, ?_, ?_, ?_⟩
  · have := band_c0 hsc h₀ hσ hX
    rw [abs_lt] at this; rw [hz0]; linarith [this.1]
  · have := band_c0 hsc h₀ hσ hX
    rw [abs_lt] at this; rw [hz0]; linarith [this.2]
  · have hr' : RecvHyp (u, w) (ratPoint I.T0) (I.tau k) v₁ := ⟨hx1, hx2, hy1, hy2, h₁, h₁', hsum⟩
    have := band_c1 hsc hr' hX
    rw [abs_lt] at this; rw [hz1]; simp only at this ⊢; linarith [this.1]
  · have hr' : RecvHyp (u, w) (ratPoint I.T0) (I.tau k) v₁ := ⟨hx1, hx2, hy1, hy2, h₁, h₁', hsum⟩
    have := band_c1 hsc hr' hX
    rw [abs_lt] at this; rw [hz1]; simp only at this ⊢; linarith [this.2]

/-- **Umbra critical points in `ε`-units**: around the apex `(X_a, Y_a)`,
`|lX − X_a| ≤ 31/5` and `Y_a − 111/5 ≤ lY ≤ Y_a − 49/5`; and `ζ`, `ξ` (in `ε`-units) lie in
`[ℓ − 221/10, ℓ − 99/10]`, `[r − 89/4, r − 39/4]`. -/
theorem Good.umbra_crit_eps {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁)
    (h₁' : v₁ ≤ 3 / 2) :
    let z := (I.umbraR k).X v₀ v₁
    let ℓ : ℝ := ((I.lwE k : ℚ) : ℝ)
    let r : ℝ := ((I.rwE k : ℚ) : ℝ)
    ℓ - 221 / 10 ≤ I.lYR z - I.lXR z ∧ I.lYR z - I.lXR z ≤ ℓ - 99 / 10 ∧
      r - 89 / 4 ≤ I.lYR z + I.lXR z ∧ I.lYR z + I.lXR z ≤ r - 39 / 4 ∧
      |I.lXR z - (r - ℓ) / 2| ≤ 31 / 5 ∧
      (ℓ + r) / 2 - 111 / 5 ≤ I.lYR z ∧ I.lYR z ≤ (ℓ + r) / 2 - 49 / 5 := by
  intro z ℓ r
  obtain ⟨-, a1, a2, a3, a4⟩ := hg.umbra_crit_loc hk h₀ h₀' h₁ h₁'
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have z1 := hg.Zs_eps k (2 * v₀ / 3)
  have x1 := hg.Xis_eps hk (1 - 2 * v₁ / 3)
  have ee := hg.eps_eps
  have q1 := mul_lt_mul_of_pos_left a1 h8
  have q2 := mul_lt_mul_of_pos_left a2 h8
  have q3 := mul_lt_mul_of_pos_left a3 h8
  have q4 := mul_lt_mul_of_pos_left a4 h8
  rw [zeta_lXR] at q1 q2
  rw [xi_lXR] at q3 q4
  rw [mul_sub, z1, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 10) = 1 / 10 by rw [← ee]; ring] at q1
  rw [mul_add, z1, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 10) = 1 / 10 by rw [← ee]; ring] at q2
  rw [mul_sub, x1, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 4) = 1 / 4 by rw [← ee]; ring] at q3
  rw [mul_add, x1, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 4) = 1 / 4 by rw [← ee]; ring] at q4
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, by linarith, by linarith⟩
  rw [abs_le]; constructor <;> linarith

/-- **The umbra critical points lie in the bands of the pair.** -/
theorem Good.umbra_crit_band {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁)
    (h₁' : v₁ ≤ 3 / 2) :
    let z := (I.umbraR k).X v₀ v₁
    (Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) 0 - eps (I.S : ℝ) ≤ zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤ Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) 3 + eps (I.S : ℝ)) ∧
    (Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) 0 - eps (I.S : ℝ) ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤
        Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) 3 + eps (I.S : ℝ)) := by
  intro z
  obtain ⟨-, a1, a2, a3, a4⟩ := hg.umbra_crit_loc hk h₀ h₀' h₁ h₁'
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have he : 0 < eps (I.S : ℝ) := by simp only [eps]; positivity
  have m1 := Zs_mono (H := (I.H : ℝ)) hS (I.sigma k) (γ := 0) (γ' := 2 * v₀ / 3) (by linarith)
  have m2 := Zs_mono (H := (I.H : ℝ)) hS (I.sigma k) (γ := 2 * v₀ / 3) (γ' := 3) (by linarith)
  have m3 := Xis_mono hS (ratPoint I.T0) (I.tau k) (γ := 0) (γ' := 1 - 2 * v₁ / 3) (by linarith)
  have m4 := Xis_mono hS (ratPoint I.T0) (I.tau k) (γ := 1 - 2 * v₁ / 3) (γ' := 3) (by linarith)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Umbra

/-! ## The nook top edge -/

section Nook

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- **Location of the nook top edge** (in `ε`-units). -/
theorem Good.nook_edge_loc {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    let ℓ : ℝ := ((I.lwE k : ℚ) : ℝ)
    let r : ℝ := ((I.rwE k : ℚ) : ℝ)
    ℓ - 33 / 8 ≤ I.lYR z - I.lXR z ∧ I.lYR z - I.lXR z ≤ ℓ + 33 / 8 ∧
      r - 17 / 8 ≤ I.lYR z + I.lXR z ∧ I.lYR z + I.lXR z ≤ r + 17 / 8 ∧
      (r - ℓ) / 2 - 3 ≤ I.lXR z ∧ I.lXR z ≤ (r - ℓ) / 2 + 3 ∧
      (ℓ + r) / 2 - 9 / 8 ≤ I.lYR z ∧ I.lYR z ≤ (ℓ + r) / 2 + 9 / 8 := by
  intro ℓ r
  have hn0 := hg.lY_n0 hk
  have hn1 := hg.lY_n1 hk
  rw [abs_le] at hn0 hn1
  have hx0 : I.lX (I.n0 k) = (I.rwE k - I.lwE k) / 2 - 3 := by rw [lX_n0, lX_z0 hg hk]
  have hx1 : I.lX (I.n1 k) = (I.rwE k - I.lwE k) / 2 + 3 := by rw [lX_n1, lX_z1 hg hk]
  -- the endpoints in real `ε`-units
  have a0 := lXR_ratPoint (I := I) (I.n0 k)
  have a1 := lXR_ratPoint (I := I) (I.n1 k)
  have b0 := lYR_ratPoint (I := I) (I.n0 k)
  have b1 := lYR_ratPoint (I := I) (I.n1 k)
  rw [hx0] at a0; rw [hx1] at a1
  have c0l : ((I.lwE k + I.rwE k) / 2 + 1 - 1 / 8 : ℚ) ≤ I.lY (I.n0 k) := by linarith
  have c0u : I.lY (I.n0 k) ≤ (I.lwE k + I.rwE k) / 2 + 1 + 1 / 8 := by linarith
  have c1l : ((I.lwE k + I.rwE k) / 2 - 1 - 1 / 8 : ℚ) ≤ I.lY (I.n1 k) := by linarith
  have c1u : I.lY (I.n1 k) ≤ (I.lwE k + I.rwE k) / 2 - 1 + 1 / 8 := by linarith
  have d0l := rat_cast_le_of c0l; have d0u := rat_cast_le_of c0u
  have d1l := rat_cast_le_of c1l; have d1u := rat_cast_le_of c1u
  push_cast at a0 a1 d0l d0u d1l d1u
  rw [← b0] at d0l d0u
  rw [← b1] at d1l d1u
  -- `lX`, `lY` are affine along the segment
  obtain ⟨t, ht0, ht1, hzt⟩ := Irrational.mem_segment_coords hz
  have hX : I.lXR z = (1 - t) * I.lXR (ratPoint (I.n0 k)) + t * I.lXR (ratPoint (I.n1 k)) := by
    simp only [lXR, hzt]; ring
  have hY : I.lYR z = (1 - t) * I.lYR (ratPoint (I.n0 k)) + t * I.lYR (ratPoint (I.n1 k)) := by
    simp only [lYR, hzt]; ring
  rw [a0, a1] at hX
  have ht' : 0 ≤ 1 - t := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hX, hY, ℓ, r] <;>
    nlinarith [mul_nonneg ht' (sub_nonneg.2 d0l), mul_nonneg ht' (sub_nonneg.2 d0u),
      mul_nonneg ht0 (sub_nonneg.2 d1l), mul_nonneg ht0 (sub_nonneg.2 d1u)]

/-- **The nook top edge lies in the bands of the pair, inside the window.** -/
theorem Good.nook_edge_band {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S ∧
    (Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) 0 - eps (I.S : ℝ) ≤ zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤ Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) 3 + eps (I.S : ℝ)) ∧
    (Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) 0 - eps (I.S : ℝ) ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤
        Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) 3 + eps (I.S : ℝ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hg.nook_edge_loc hk hz
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have z0 := hg.Zs_eps k 0
  have z3 := hg.Zs_eps k 3
  have x0 := hg.Xis_eps hk 0
  have x3 := hg.Xis_eps hk 3
  have ee := hg.eps_eps
  have zl := zeta_lXR (I := I) z
  have xl := xi_lXR (I := I) z
  have hw := hg.window_apex hk
  have hw' : |((I.rwE k : ℚ) : ℝ) / 2 - ((I.lwE k : ℚ) : ℝ) / 2| + 20 ≤ 456 * (N : ℝ) := by
    have : |((I.rwE k - I.lwE k) / 2 : ℚ)| + 20 ≤ 456 * N := hw
    have h' := rat_cast_le_of this
    push_cast at h'
    rwa [sub_div] at h'
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hw'' : |((I.rwE k : ℚ) : ℝ) / 2 - ((I.lwE k : ℚ) : ℝ) / 2| ≤ 456 * (N : ℝ) - 20 := by
      linarith
    rw [abs_le] at hw''
    have hl : |I.lXR z| ≤ 456 * (N : ℝ) := by
      rw [abs_le]; constructor <;> linarith [hw''.1, hw''.2]
    have e : z.1 - ((I.S : ℝ) + 1) = I.lXR z / (8 * I.S) := by simp only [lXR]; field_simp
    rw [e, abs_div, abs_of_pos h8, div_le_div_iff₀ h8 hS]
    nlinarith
  all_goals
    first
    | (apply le_of_mul_le_mul_left _ h8; rw [mul_sub, z0, show 8 * (I.S : ℝ) * eps (I.S : ℝ) = 1
        from ee, zl]; linarith)
    | (apply le_of_mul_le_mul_left _ h8; rw [mul_add, z3, show 8 * (I.S : ℝ) * eps (I.S : ℝ) = 1
        from ee, zl]; linarith)
    | (apply le_of_mul_le_mul_left _ h8; rw [mul_sub, x0, show 8 * (I.S : ℝ) * eps (I.S : ℝ) = 1
        from ee, xl]; linarith)
    | (apply le_of_mul_le_mul_left _ h8; rw [mul_add, x3, show 8 * (I.S : ℝ) * eps (I.S : ℝ) = 1
        from ee, xl]; linarith)

end Nook

end Input

end ArtGallery.Sec5.Corridor

end
