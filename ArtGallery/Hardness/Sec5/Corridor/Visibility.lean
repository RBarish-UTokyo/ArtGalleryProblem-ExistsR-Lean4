module

public import ArtGallery.Hardness.Sec5.Corridor.Room

/-!
# Section 5: corridors — the band lemma (Lemma V1)

Let `P` be a simple counter-clockwise polygon with `CorridorAt P I a b`.

* **Through the doors** (exact form).  A point `g` left of the corridor (`g.x < S`) sees a point
  `z` of the corridor (`z.x < S + 2`) only through the entrance: `z` lies in the closed wedge
  `det(g, c0, z) ≥ 0 ≥ det(g, d0, z)` (`Good.sees_through_entrance`).  A point right of the
  corridor (`g.x > S + 2`) sees `z` (`z.x > S`) only through the window:
  `det(g, c1, z) ≤ 0 ≤ det(g, d1, z)` (`Good.sees_through_window`).
* **Bands** (Lemma V1, with the budgets of `Slabs.lean`).  Inside the window `|X| ≤ 57N/S` around
  `O`, a point seen by the base guard `(27σ/2 + t, 0)` has `ζ ∈ (Z(σ, 2t/3) − ε/10,
  Z(σ, 2 + 2t/3) + ε/10)` (`Good.base_band`), a point seen by the receiver guard
  `m + (T + (t, 0))/S` has `ξ ∈ (Ξ(τ, 1 − 2t/3) − ε/4, Ξ(τ, 3 − 2t/3) + ε/4)`
  (`Good.recv_band`); in particular `ζ ∈ (Z(σ,0) − ε, Z(σ,3) + ε)`, resp.
  `ξ ∈ (Ξ(τ,0) − ε, Ξ(τ,3) + ε)` (`Good.base_band_wide`, `Good.recv_band_wide`).
* **Separation** (`Good.not_sees_base_of_zeta`, `Good.not_sees_recv_of_xi`): a corridor point of
  the window whose `ζ` lies in the band of slot `σ` is not seen by any base guard of another slot;
  likewise for receivers and `ξ`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- The real scale hypotheses. -/
theorem Good.scaleR (hg : I.Good N) : ScaleHyp (N : ℝ) (I.S : ℝ) (I.H : ℝ) :=
  ⟨by exact_mod_cast hg.scale.two_le, by exact_mod_cast hg.scale.hS,
    by exact_mod_cast hg.scale.hH1, by exact_mod_cast hg.scale.hH2⟩

/-- The real local origin. -/
theorem ratPoint_O : ratPoint I.O = Oc (I.S : ℝ) (I.H : ℝ) := ratPoint_Oc I.S I.H

section Doors

variable (hg : I.Good N)
include hg

/-- Points strictly left of `x = S` are outside the corridor. -/
theorem Good.not_mem_poly_of_lt {g : Point} (hgx : g.1 < (I.S : ℝ)) : g ∉ I.poly.filled :=
  fun h => by have := (hg.poly_filled_box h).1; linarith

/-- Points strictly right of `x = S + 2` are outside the corridor. -/
theorem Good.not_mem_poly_of_gt {g : Point} (hgx : (I.S : ℝ) + 2 < g.1) : g ∉ I.poly.filled :=
  fun h => by have := (hg.poly_filled_box h).2.1; linarith

variable {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : CorridorAt P I a b)
include hP hL hC

/-- **Through the entrance.** -/
theorem Good.sees_through_entrance {g z : Point} (hgx : g.1 < (I.S : ℝ))
    (hz : z ∈ I.poly.filled) (hzx : z.1 < (I.S : ℝ) + 2) (hs : P.Sees g z) :
    0 ≤ det g (ratPoint (c0 I.S I.H)) z ∧ det g (ratPoint (d0 I.S I.H)) z ≤ 0 := by
  have hρ := hg.rhoR_pos
  obtain ⟨y, hyD, hyg⟩ := hg.sees_crosses_door hP hL hC (hg.not_mem_poly_of_lt hgx) hz hs
  have hymax : y.1 ≤ max g.1 z.1 := Irrational.seg_fst_le hyg
  rcases hyD with hyw | hye
  · exfalso
    rw [window, ratPoint_c1', ratPoint_d1'] at hyw
    have := seg_fst_of_vertical hyw rfl
    simp only at this
    rcases le_total g.1 z.1 with h | h
    · rw [max_eq_right h] at hymax; linarith
    · rw [max_eq_left h] at hymax; linarith
  · rw [entrance, ratPoint_d0', ratPoint_c0'] at hye
    have hy1 : y.1 = (I.S : ℝ) := by rw [seg_fst_of_vertical hye rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hye (by simp; linarith) (by simp)
    have hy3 : y.2 ≤ (I.H : ℝ) + 2 * I.rhoR := Vis.Cert.seg_snd_ub hye (by simp) (by simp; linarith)
    obtain ⟨s, hs0, hs1, hy⟩ := hyg
    have hsp : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hy; have := congrArg Prod.fst hy; simp at this; linarith
    rw [ratPoint_c0', ratPoint_d0']
    have e1 : det g ((I.S : ℝ), (I.H : ℝ)) y = s * det g ((I.S : ℝ), (I.H : ℝ)) z := by
      rw [hy]; simp only [det]; ring
    have e2 : det g ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR) y =
        s * det g ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR) z := by
      rw [hy]; simp only [det]; ring
    have f1 : det g ((I.S : ℝ), (I.H : ℝ)) y = ((I.S : ℝ) - g.1) * (y.2 - I.H) := by
      simp only [det, hy1]; ring
    have f2 : det g ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR) y =
        ((I.S : ℝ) - g.1) * (y.2 - (I.H + 2 * I.rhoR)) := by
      simp only [det, hy1]; ring
    have g1 : 0 ≤ s * det g ((I.S : ℝ), (I.H : ℝ)) z := by
      rw [← e1, f1]; exact mul_nonneg (by linarith) (by linarith)
    have g2 : s * det g ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR) z ≤ 0 := by
      rw [← e2, f2]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    refine ⟨(mul_nonneg_iff_of_pos_left hsp).1 g1, ?_⟩
    by_contra hcon
    push Not at hcon
    have := mul_pos hsp hcon
    linarith

/-- **Through the window.** -/
theorem Good.sees_through_window {g z : Point} (hgx : (I.S : ℝ) + 2 < g.1)
    (hz : z ∈ I.poly.filled) (hzx : (I.S : ℝ) < z.1) (hs : P.Sees g z) :
    det g (ratPoint (c1 I.S I.H)) z ≤ 0 ∧ 0 ≤ det g (ratPoint (d1 I.S I.H)) z := by
  have hρ := hg.rhoR_pos
  obtain ⟨y, hyD, hyg⟩ := hg.sees_crosses_door hP hL hC (hg.not_mem_poly_of_gt hgx) hz hs
  have hymin : min g.1 z.1 ≤ y.1 := Irrational.seg_fst_ge hyg
  rcases hyD with hyw | hye
  · rw [window, ratPoint_c1', ratPoint_d1'] at hyw
    have hy1 : y.1 = (I.S : ℝ) + 2 := by rw [seg_fst_of_vertical hyw rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hyw (by simp) (by simp; linarith)
    have hy3 : y.2 ≤ (I.H : ℝ) + I.rhoR := Vis.Cert.seg_snd_ub hyw (by simp; linarith) (by simp)
    obtain ⟨s, hs0, hs1, hy⟩ := hyg
    have hsp : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hy; have := congrArg Prod.fst hy; simp at this; linarith
    rw [ratPoint_c1', ratPoint_d1']
    have e1 : det g ((I.S : ℝ) + 2, (I.H : ℝ)) y = s * det g ((I.S : ℝ) + 2, (I.H : ℝ)) z := by
      rw [hy]; simp only [det]; ring
    have e2 : det g ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) y =
        s * det g ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) z := by
      rw [hy]; simp only [det]; ring
    have f1 : det g ((I.S : ℝ) + 2, (I.H : ℝ)) y = ((I.S : ℝ) + 2 - g.1) * (y.2 - I.H) := by
      simp only [det, hy1]; ring
    have f2 : det g ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) y =
        ((I.S : ℝ) + 2 - g.1) * (y.2 - (I.H + I.rhoR)) := by
      simp only [det, hy1]; ring
    have g1 : s * det g ((I.S : ℝ) + 2, (I.H : ℝ)) z ≤ 0 := by
      rw [← e1, f1]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have g2 : 0 ≤ s * det g ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) z := by
      rw [← e2, f2]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    constructor <;> nlinarith
  · exfalso
    rw [entrance, ratPoint_d0', ratPoint_c0'] at hye
    have := seg_fst_of_vertical hye rfl
    simp only at this
    rcases le_total g.1 z.1 with h | h
    · rw [min_eq_left h] at hymin; linarith
    · rw [min_eq_right h] at hymin; linarith

/-! ### Bands -/

/-- **Band lemma for base guards.** -/
theorem Good.base_band {σ : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (_ht1 : t ≤ 3 / 2)
    (hx : 27 * (σ : ℝ) / 2 + t ≤ 14 * N) {z : Point} (hz : z ∈ I.poly.filled)
    (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hs : P.Sees (27 * (σ : ℝ) / 2 + t, 0) z) :
    Zs (I.S : ℝ) (I.H : ℝ) σ (2 * t / 3) - eps (I.S : ℝ) / 10 <
        zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z <
        Zs (I.S : ℝ) (I.H : ℝ) σ (2 + 2 * t / 3) + eps (I.S : ℝ) / 10 := by
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hN := hsc.two_le
  have hσ : (0 : ℝ) ≤ σ := Nat.cast_nonneg σ
  have hxS : 27 * (σ : ℝ) / 2 + t < I.S := by have := hsc.hS; nlinarith
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by simpa [Oc] using hX
  have hzx : z.1 < (I.S : ℝ) + 2 := by
    have h57 : 57 * (N : ℝ) / I.S < 1 := by
      rw [div_lt_one hS]; have := hsc.hS; nlinarith
    rw [abs_le] at hX; linarith
  obtain ⟨h1, h2⟩ := hg.sees_through_entrance hP hL hC (by simpa using hxS) hz hzx hs
  rw [ratPoint_c0, det_eq_det2, det2_eq_lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    (by simp [c0]; linarith)] at h1
  rw [ratPoint_d0, det_eq_det2, det2_eq_lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    (by simp [d0]; linarith)] at h2
  have hc : (0 : ℝ) < (c0 (I.S : ℝ) (I.H : ℝ)).1 - (27 * σ / 2 + t, (0 : ℝ)).1 := by
    simp [c0]; linarith
  have hd : (0 : ℝ) < (d0 (I.S : ℝ) (I.H : ℝ)).1 - (27 * σ / 2 + t, (0 : ℝ)).1 := by
    simp [d0]; linarith
  have b1 := band_c0 hsc ht0 hx hX'
  have b2 := band_d0 hsc ht0 hx hX'
  rw [abs_lt] at b1 b2
  have k1 := nonneg_of_mul_nonneg_right h1 hc |> fun h => by
    have := (mul_nonneg_iff_of_pos_left hc).1 h1; exact this
  have k2 : zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z - lineZeta (Oc (I.S : ℝ) (I.H : ℝ))
      (27 * σ / 2 + t, 0) (d0 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) ≤ 0 := by
    by_contra hc'
    push Not at hc'
    have := mul_pos hd hc'
    linarith
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- **Band lemma for base guards (wide form).** -/
theorem Good.base_band_wide {σ : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    (hx : 27 * (σ : ℝ) / 2 + t ≤ 14 * N) {z : Point} (hz : z ∈ I.poly.filled)
    (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hs : P.Sees (27 * (σ : ℝ) / 2 + t, 0) z) :
    Zs (I.S : ℝ) (I.H : ℝ) σ 0 - eps (I.S : ℝ) < zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z < Zs (I.S : ℝ) (I.H : ℝ) σ 3 + eps (I.S : ℝ) := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have he : 0 < eps (I.S : ℝ) := by simp only [eps]; positivity
  obtain ⟨h1, h2⟩ := hg.base_band hP hL hC ht0 ht1 hx hz hX hs
  have m1 := Zs_mono (H := (I.H : ℝ)) hS σ (γ := 0) (γ' := 2 * t / 3) (by linarith)
  have m2 := Zs_mono (H := (I.H : ℝ)) hS σ (γ := 2 + 2 * t / 3) (γ' := 3) (by linarith)
  constructor <;> linarith

/-- **Band lemma for receivers.** -/
theorem Good.recv_band {T : Point} {τ : ℕ} {t : ℝ} (hr : RecvHyp T (ratPoint I.T0) τ t)
    {z : Point} (hz : z ∈ I.poly.filled) (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hs : P.Sees (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) z) :
    Xis (I.S : ℝ) (ratPoint I.T0) τ (1 - 2 * t / 3) - eps (I.S : ℝ) / 4 <
        xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z <
        Xis (I.S : ℝ) (ratPoint I.T0) τ (3 - 2 * t / 3) + eps (I.S : ℝ) / 4 := by
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hS8 := hsc.S_ge
  have hN := hsc.two_le
  obtain ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩ := hr
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by simpa [Oc] using hX
  have hzx : (I.S : ℝ) < z.1 := by
    have h57 : 57 * (N : ℝ) / I.S < 1 := by
      rw [div_lt_one hS]; have := hsc.hS; nlinarith
    rw [abs_le] at hX; linarith
  have hu : -1 < (T.1 + t) / (I.S : ℝ) := by
    rw [lt_div_iff₀ hS]; linarith
  have hqx : (I.S : ℝ) + 2 < (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)).1 := by
    simp only [place]; linarith
  obtain ⟨h1, h2⟩ := hg.sees_through_window hP hL hC hqx hz hzx hs
  have hc : (c1 (I.S : ℝ) (I.H : ℝ)).1 - (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)).1 < 0 := by
    simp only [c1, place]; linarith
  have hd : (d1 (I.S : ℝ) (I.H : ℝ)).1 - (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)).1 < 0 := by
    simp only [d1, place]; linarith
  rw [ratPoint_c1, det_eq_det2, det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _ hc.ne] at h1
  rw [ratPoint_d1, det_eq_det2, det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _ hd.ne] at h2
  have hr' : RecvHyp T (ratPoint I.T0) τ t := ⟨hx1, hx2, hy1, hy2, ht0, ht1, hsum⟩
  have b1 := band_c1 hsc hr' hX'
  have b2 := band_d1 hsc hr' hX'
  rw [abs_lt] at b1 b2
  have k1 : 0 ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z - lineXi (Oc (I.S : ℝ) (I.H : ℝ))
      (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) (c1 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) := by
    by_contra hc'
    push Not at hc'
    have := mul_pos_of_neg_of_neg hc hc'
    linarith
  have k2 : xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z - lineXi (Oc (I.S : ℝ) (I.H : ℝ))
      (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) (d1 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) ≤ 0 := by
    by_contra hc'
    push Not at hc'
    have := mul_neg_of_neg_of_pos hd hc'
    linarith
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- **Band lemma for receivers (wide form).** -/
theorem Good.recv_band_wide {T : Point} {τ : ℕ} {t : ℝ} (hr : RecvHyp T (ratPoint I.T0) τ t)
    {z : Point} (hz : z ∈ I.poly.filled) (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hs : P.Sees (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) z) :
    Xis (I.S : ℝ) (ratPoint I.T0) τ 0 - eps (I.S : ℝ) < xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z < Xis (I.S : ℝ) (ratPoint I.T0) τ 3 + eps (I.S : ℝ) := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  have he : 0 < eps (I.S : ℝ) := by simp only [eps]; positivity
  have ht0 := hr.ht0
  have ht1 := hr.ht1
  obtain ⟨h1, h2⟩ := hg.recv_band hP hL hC hr hz hX hs
  have m1 := Xis_mono hS (ratPoint I.T0) τ (γ := 0) (γ' := 1 - 2 * t / 3) (by linarith)
  have m2 := Xis_mono hS (ratPoint I.T0) τ (γ := 3 - 2 * t / 3) (γ' := 3) (by linarith)
  constructor <;> linarith

/-! ### Separation of the bands -/

/-- **Other base slots do not see the band of slot `σ`.** -/
theorem Good.not_sees_base_of_zeta {σ σ' : ℕ} (hne : σ ≠ σ') {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 3 / 2) (hx : 27 * (σ' : ℝ) / 2 + t ≤ 14 * N) {z : Point}
    (hz : z ∈ I.poly.filled) (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hzeta : Zs (I.S : ℝ) (I.H : ℝ) σ 0 - eps (I.S : ℝ) ≤ zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤ Zs (I.S : ℝ) (I.H : ℝ) σ 3 + eps (I.S : ℝ)) :
    ¬ P.Sees (27 * (σ' : ℝ) / 2 + t, 0) z := by
  intro hs
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  obtain ⟨h1, h2⟩ := hg.base_band_wide hP hL hC ht0 ht1 hx hz hX hs
  rcases lt_or_gt_of_ne hne with h | h
  · have := Zs_band_lt (H := (I.H : ℝ)) hS h; linarith [hzeta.2]
  · have := Zs_band_lt (H := (I.H : ℝ)) hS h; linarith [hzeta.1]

/-- **Other receivers do not see the band of receiver `τ`.** -/
theorem Good.not_sees_recv_of_xi {τ τ' : ℕ} (hne : τ ≠ τ') {T : Point} {t : ℝ}
    (hr : RecvHyp T (ratPoint I.T0) τ' t) {z : Point} (hz : z ∈ I.poly.filled)
    (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hxi : Xis (I.S : ℝ) (ratPoint I.T0) τ 0 - eps (I.S : ℝ) ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤ Xis (I.S : ℝ) (ratPoint I.T0) τ 3 + eps (I.S : ℝ)) :
    ¬ P.Sees (place (I.S : ℝ) (I.H : ℝ) (T.1 + t, T.2)) z := by
  intro hs
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  obtain ⟨h1, h2⟩ := hg.recv_band_wide hP hL hC hr hz hX hs
  rcases lt_or_gt_of_ne hne with h | h
  · have := Xis_band_lt hS (ratPoint I.T0) h; linarith [hxi.2]
  · have := Xis_band_lt hS (ratPoint I.T0) h; linarith [hxi.1]

end Doors

end Input

end ArtGallery.Sec5.Corridor

end
