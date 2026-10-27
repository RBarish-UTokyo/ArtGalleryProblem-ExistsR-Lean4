module

public import ArtGallery.Stade.NookAlg

/-!
# Stade construction, §5: algebra of the copy nooks

Notation of `docs/stade/construction.md` §5, for real parameters `H, a, b` (variable abscissa
`a`, input abscissa `b`, `Δ = b − a ∈ [H, 2H]`, `H ≥ 1000`) and the copy type `ge : Bool`
(`true` = GE: enforce `v_var ≥ v_in`, offset `e = 12`; `false` = LE: `v_var ≤ v_in`, `e = −16`):

```
x_N   = 2a − b + e,          N_top = (x_N, 2H + 1 + 3/(2H−3)),  N_bot = (x_N, 2H + 1 − 3/(2H−3))
P_σ   = ((x_N(2H−3) + 2a)/(2H−1), 2H),      P_τ = ((x_N(2H−3) + b)/(2H−2), 2H)
L_m, R_m = P_σ, P_τ (GE)  resp.  P_τ, P_σ (LE)        (mouth [L_m, R_m] on the ceiling y = 2H)
σ(v)  = (a, H + 2v − 1),   τ(w) = (b, 4w − 2)          (guards of value v, w ∈ [1/2, 2])
```

Main facts (the perspectivity identities of [Stade, Lemmas 4.1/4.2] in these coordinates):

* **homothety** (L5.1, `copy_vproj_sig`, `copy_vproj_tau`): the shadow of `σ(v)` through `P_σ`
  and the shadow of `τ(v)` through `P_τ` on the nook line `x = x_N` are both
  `copyShadow H v = N_top − 4(v − 1/2)/(2H−3)`;
* **non-restriction** (L5.3, `copyGE_sig_Pt`, `copyGE_tau_Ps`, `copyLE_sig_Pt`,
  `copyLE_tau_Ps`): the shadows through the other mouth end lie beyond the nook;
* **what each guard sees** (L5.4, `copy_sig_seen`, `copy_tau_seen`): a nook point seen from
  `σ(v)` through the mouth lies above (GE) / below (LE) `copyShadow H v`, and the opposite
  for `τ(w)`; **coverage ⇒ copy inequality** (`copy_rel_of_cover`);
* **positive visibility** (L5.6, `copy_sig_cross`, `copy_tau_cross`): conversely every nook
  point on the correct side of the shadow is reached through the mouth;
* **partial visibility region** (L5.5, `copyPV`, `mem_copyPV_of_cross`, band lemmas
  `copyPV_var_band`, `copyPV_in_band`, `copyPV_low`, `copyPV_low_le`).
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

/-! ### Definitions -/

/-- Standing hypotheses on the parameters of a copy nook: `H ≥ 1000`, `H ≤ b − a ≤ 2H`. -/
structure CopyParams (H a b : ℝ) : Prop where
  hH : 1000 ≤ H
  hlo : H ≤ b - a
  hhi : b - a ≤ 2 * H

/-- The offset `e` of a copy nook: `12` for type GE, `−16` for type LE. -/
def copyOff : Bool → ℝ
  | true => 12
  | false => -16

/-- The abscissa `x_N = 2a − b + e` of the nook segment. -/
def copyXN (ge : Bool) (a b : ℝ) : ℝ := 2 * a - b + copyOff ge

/-- The upper end `N_top` of the nook segment. -/
noncomputable def copyNtop (ge : Bool) (H a b : ℝ) : Point :=
  (copyXN ge a b, 2 * H + 1 + 3 / (2 * H - 3))

/-- The lower end `N_bot` of the nook segment. -/
noncomputable def copyNbot (ge : Bool) (H a b : ℝ) : Point :=
  (copyXN ge a b, 2 * H + 1 - 3 / (2 * H - 3))

/-- The homothety centre `P_σ` (variable segment → nook segment), on the ceiling. -/
noncomputable def copyPs (ge : Bool) (H a b : ℝ) : Point :=
  ((copyXN ge a b * (2 * H - 3) + 2 * a) / (2 * H - 1), 2 * H)

/-- The homothety centre `P_τ` (input segment → nook segment), on the ceiling. -/
noncomputable def copyPt (ge : Bool) (H a b : ℝ) : Point :=
  ((copyXN ge a b * (2 * H - 3) + b) / (2 * H - 2), 2 * H)

/-- The left mouth end `L_m` (`P_σ` for GE, `P_τ` for LE). -/
noncomputable def copyLm : Bool → ℝ → ℝ → ℝ → Point
  | true, H, a, b => copyPs true H a b
  | false, H, a, b => copyPt false H a b

/-- The right mouth end `R_m` (`P_τ` for GE, `P_σ` for LE). -/
noncomputable def copyRm : Bool → ℝ → ℝ → ℝ → Point
  | true, H, a, b => copyPt true H a b
  | false, H, a, b => copyPs false H a b

/-- The common shadow height `N_top − 4(v − 1/2)/(2H − 3)` of a guard of value `v`. -/
noncomputable def copyShadow (H v : ℝ) : ℝ :=
  2 * H + 1 + 3 / (2 * H - 3) - 4 * (v - 1 / 2) / (2 * H - 3)

/-! ### Elementary facts -/

section

variable {H a b : ℝ}

/-- `2H − 3 > 0`. -/
theorem CopyParams.pos3 (hp : CopyParams H a b) : 0 < 2 * H - 3 := by linarith [hp.hH]
/-- `2H − 1 > 0`. -/
theorem CopyParams.pos1 (hp : CopyParams H a b) : 0 < 2 * H - 1 := by linarith [hp.hH]
/-- `2H − 2 > 0`. -/
theorem CopyParams.pos2 (hp : CopyParams H a b) : 0 < 2 * H - 2 := by linarith [hp.hH]

@[simp] theorem copyNtop_fst (ge : Bool) : (copyNtop ge H a b).1 = copyXN ge a b := rfl
@[simp] theorem copyNtop_snd (ge : Bool) :
    (copyNtop ge H a b).2 = 2 * H + 1 + 3 / (2 * H - 3) := rfl
@[simp] theorem copyNbot_fst (ge : Bool) : (copyNbot ge H a b).1 = copyXN ge a b := rfl
@[simp] theorem copyNbot_snd (ge : Bool) :
    (copyNbot ge H a b).2 = 2 * H + 1 - 3 / (2 * H - 3) := rfl
@[simp] theorem copyPs_snd (ge : Bool) : (copyPs ge H a b).2 = 2 * H := rfl
@[simp] theorem copyPt_snd (ge : Bool) : (copyPt ge H a b).2 = 2 * H := rfl
@[simp] theorem copyLm_true : copyLm true H a b = copyPs true H a b := rfl
@[simp] theorem copyLm_false : copyLm false H a b = copyPt false H a b := rfl
@[simp] theorem copyRm_true : copyRm true H a b = copyPt true H a b := rfl
@[simp] theorem copyRm_false : copyRm false H a b = copyPs false H a b := rfl
@[simp] theorem copyLm_snd (ge : Bool) : (copyLm ge H a b).2 = 2 * H := by cases ge <;> rfl
@[simp] theorem copyRm_snd (ge : Bool) : (copyRm ge H a b).2 = 2 * H := by cases ge <;> rfl

/-- `|e| ≤ 16`, `e ≠ 0`: the two offsets. -/
theorem copyOff_cases (ge : Bool) : copyOff ge = 12 ∨ copyOff ge = -16 := by
  cases ge
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `P_σ − x_N = 2(Δ − e)/(2H − 1)`. -/
theorem copyPs_fst_sub_xN (ge : Bool) (hp : CopyParams H a b) :
    (copyPs ge H a b).1 - copyXN ge a b = 2 * (b - a - copyOff ge) / (2 * H - 1) := by
  have := hp.pos1.ne'
  unfold copyPs copyXN
  field_simp
  ring

/-- `P_τ − x_N = (2Δ − e)/(2H − 2)`. -/
theorem copyPt_fst_sub_xN (ge : Bool) (hp : CopyParams H a b) :
    (copyPt ge H a b).1 - copyXN ge a b = (2 * (b - a) - copyOff ge) / (2 * H - 2) := by
  have := hp.pos2.ne'
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  unfold copyPt copyXN
  field_simp
  ring

/-- `P_σ − a = −(Δ − e)(2H − 3)/(2H − 1)`. -/
theorem copyPs_fst_sub_a (ge : Bool) (hp : CopyParams H a b) :
    (copyPs ge H a b).1 - a = -((b - a - copyOff ge) * (2 * H - 3)) / (2 * H - 1) := by
  have := hp.pos1.ne'
  unfold copyPs copyXN
  field_simp
  ring

/-- `P_τ − b = −(2Δ − e)(2H − 3)/(2H − 2)`. -/
theorem copyPt_fst_sub_b (ge : Bool) (hp : CopyParams H a b) :
    (copyPt ge H a b).1 - b = -((2 * (b - a) - copyOff ge) * (2 * H - 3)) / (2 * H - 2) := by
  have := hp.pos2.ne'
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  unfold copyPt copyXN
  field_simp
  ring

/-- `P_τ − a = ((x_N − a)(2H − 3) + Δ)/(2H − 2)`. -/
theorem copyPt_fst_sub_a (ge : Bool) (hp : CopyParams H a b) :
    (copyPt ge H a b).1 - a = ((a - b + copyOff ge) * (2 * H - 3) + (b - a)) / (2 * H - 2) := by
  have := hp.pos2.ne'
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  unfold copyPt copyXN
  field_simp
  ring

/-- `P_σ − b = (2(a − b)(2H − 2) + e(2H − 3))/(2H − 1)`. -/
theorem copyPs_fst_sub_b (ge : Bool) (hp : CopyParams H a b) :
    (copyPs ge H a b).1 - b =
      (2 * (a - b) * (2 * H - 2) + copyOff ge * (2 * H - 3)) / (2 * H - 1) := by
  have := hp.pos1.ne'
  unfold copyPs copyXN
  field_simp
  ring

/-- `−16 ≤ e ≤ 12`. -/
theorem copyOff_bounds (ge : Bool) : -16 ≤ copyOff ge ∧ copyOff ge ≤ 12 := by
  cases ge <;> simp [copyOff] <;> norm_num

/-- The mouth ends lie strictly between the nook line and the variable segment:
`x_N < P_σ, P_τ < a`. -/
theorem copy_mouth_order (ge : Bool) (hp : CopyParams H a b) :
    copyXN ge a b < (copyPs ge H a b).1 ∧ copyXN ge a b < (copyPt ge H a b).1 ∧
      (copyPs ge H a b).1 < a ∧ (copyPt ge H a b).1 < a := by
  obtain ⟨he1, he2⟩ := copyOff_bounds ge
  have h1 := hp.pos1; have h2 := hp.pos2; have h3 := hp.pos3
  have hH := hp.hH; have hlo := hp.hlo
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := copyPs_fst_sub_xN ge hp
    have : 0 < 2 * (b - a - copyOff ge) / (2 * H - 1) := div_pos (by linarith) h1
    linarith
  · have := copyPt_fst_sub_xN ge hp
    have : 0 < (2 * (b - a) - copyOff ge) / (2 * H - 2) := div_pos (by linarith) h2
    linarith
  · have := copyPs_fst_sub_a ge hp
    have : -((b - a - copyOff ge) * (2 * H - 3)) / (2 * H - 1) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) h1
    linarith
  · have := copyPt_fst_sub_a ge hp
    have : ((a - b + copyOff ge) * (2 * H - 3) + (b - a)) / (2 * H - 2) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) h2
    linarith

/-- The left mouth end is left of the right one: `L_m < R_m`. -/
theorem copyLm_lt_Rm (ge : Bool) (hp : CopyParams H a b) :
    (copyLm ge H a b).1 < (copyRm ge H a b).1 := by
  have h1 := hp.pos1; have h2 := hp.pos2
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have e1 := copyPs_fst_sub_xN ge hp
  have e2 := copyPt_fst_sub_xN ge hp
  cases ge
  · simp only [copyLm_false, copyRm_false]
    simp only [copyOff] at e1 e2
    have : (2 * (b - a) - -16) / (2 * H - 2) < 2 * (b - a - -16) / (2 * H - 1) := by
      rw [div_lt_div_iff₀ h2 h1]; nlinarith
    linarith
  · simp only [copyLm_true, copyRm_true]
    simp only [copyOff] at e1 e2
    have : 2 * (b - a - 12) / (2 * H - 1) < (2 * (b - a) - 12) / (2 * H - 2) := by
      rw [div_lt_div_iff₀ h1 h2]; nlinarith
    linarith

/-- The shadow of a guard value in `[1/2, 2]` lies on the nook segment. -/
theorem copyShadow_mem (hp : CopyParams H a b) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    2 * H + 1 - 3 / (2 * H - 3) ≤ copyShadow H v ∧
      copyShadow H v ≤ 2 * H + 1 + 3 / (2 * H - 3) := by
  have h3 := hp.pos3
  unfold copyShadow
  constructor
  · have : 4 * (v - 1 / 2) / (2 * H - 3) ≤ 6 / (2 * H - 3) :=
      div_le_div_of_nonneg_right (by linarith) h3.le
    have e : (6 : ℝ) / (2 * H - 3) = 3 / (2 * H - 3) + 3 / (2 * H - 3) := by ring
    linarith
  · have : 0 ≤ 4 * (v - 1 / 2) / (2 * H - 3) := div_nonneg (by linarith) h3.le
    linarith

/-- The shadow is strictly decreasing in the value. -/
theorem copyShadow_lt_iff (hp : CopyParams H a b) {v w : ℝ} :
    copyShadow H v < copyShadow H w ↔ w < v := by
  have h3 := hp.pos3
  unfold copyShadow
  constructor
  · intro h
    by_contra hc; push Not at hc
    have : 4 * (v - 1 / 2) / (2 * H - 3) ≤ 4 * (w - 1 / 2) / (2 * H - 3) :=
      div_le_div_of_nonneg_right (by linarith) h3.le
    linarith
  · intro h
    have : 4 * (w - 1 / 2) / (2 * H - 3) < 4 * (v - 1 / 2) / (2 * H - 3) :=
      div_lt_div_of_pos_right (by linarith) h3
    linarith

/-- The shadow is decreasing in the value (non-strict form). -/
theorem copyShadow_le_iff (hp : CopyParams H a b) {v w : ℝ} :
    copyShadow H v ≤ copyShadow H w ↔ w ≤ v := by
  rw [← not_lt, copyShadow_lt_iff hp, not_lt]


/-! ### Homothety (L5.1) -/
/-- **Homothety, variable side.** The line through `σ(v)` and `P_σ` meets the nook line at
height `copyShadow H v`. -/
theorem copy_vproj_sig (ge : Bool) (hp : CopyParams H a b) (v : ℝ) :
    vproj (varPt H a v) (copyPs ge H a b) (copyXN ge a b) = copyShadow H v := by
  have hX : (copyPs ge H a b).1 - (varPt H a v).1 = _ := copyPs_fst_sub_a ge hp
  obtain ⟨he1, he2⟩ := copyOff_bounds ge
  have hd : b - a - copyOff ge ≠ 0 := by linarith [hp.hlo, hp.hH]
  rw [vproj_eq_of hX]
  simp only [varPt, copyPs_snd, copyShadow, copyXN]
  generalize copyOff ge = e at hd ⊢
  have := hp.pos1.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 1 ≠ 0 := by linarith [hp.hH]
  field_simp
  ring

/-- **Homothety, input side.** The line through `τ(w)` and `P_τ` meets the nook line at
height `copyShadow H w`. -/
theorem copy_vproj_tau (ge : Bool) (hp : CopyParams H a b) (w : ℝ) :
    vproj (inPt b w) (copyPt ge H a b) (copyXN ge a b) = copyShadow H w := by
  have hX : (copyPt ge H a b).1 - (inPt b w).1 = _ := copyPt_fst_sub_b ge hp
  obtain ⟨he1, he2⟩ := copyOff_bounds ge
  have hd : 2 * (b - a) - copyOff ge ≠ 0 := by linarith [hp.hlo, hp.hH]
  rw [vproj_eq_of hX]
  simp only [inPt, copyPt_snd, copyShadow, copyXN]
  generalize copyOff ge = e at hd ⊢
  have := hp.pos2.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 2 ≠ 0 := by linarith [hp.hH]
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  field_simp
  ring

/-! ### Non-restriction (L5.3) -/

/-- GE: the shadow of `σ(v)` through `R_m = P_τ` is at or above `N_top`. -/
theorem copyGE_sig_Pt (hp : CopyParams H a b) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    (copyNtop true H a b).2 ≤ vproj (varPt H a v) (copyPt true H a b) (copyXN true a b) := by
  have hX := copyPt_fst_sub_a true hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - 2 * Δ - 12 * H + 18 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - 2 * Δ - 12 * H + 18 = K at hK
  have hX' : (copyPt true H a (a + Δ)).1 - (varPt H a v).1 = -K / (H - 1) := by
    rw [varPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  have key : vproj (varPt H a v) (copyPt true H a (a + Δ)) (copyXN true a (a + Δ)) -
      (copyNtop true H a (a + Δ)).2 =
      -(4 * Δ * H * v - 3 * Δ * H - 6 * Δ * v + 3 * Δ - 12 * H ^ 2 - 24 * H * v + 30 * H
        + 36 * v - 18) / ((2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [varPt, copyPt_snd, copyNtop_snd, copyXN, copyOff]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ -(4 * Δ * H * v - 3 * Δ * H - 6 * Δ * v + 3 * Δ - 12 * H ^ 2 - 24 * H * v
      + 30 * H + 36 * v - 18) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := div_nonneg hnum (mul_pos h3 hK).le
  rw [← key] at hfin
  linarith

/-- GE: the shadow of `τ(w)` through `L_m = P_σ` is at or below `N_bot`. -/
theorem copyGE_tau_Ps (hp : CopyParams H a b) {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    vproj (inPt b w) (copyPs true H a b) (copyXN true a b) ≤ (copyNbot true H a b).2 := by
  have hX := copyPs_fst_sub_b true hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - Δ - 6 * H + 9 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - Δ - 6 * H + 9 = K at hK
  have hX' : (copyPs true H a (a + Δ)).1 - (inPt (a + Δ) w).1 = -(4 * K) / (2 * H - 1) := by
    rw [inPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  have key : vproj (inPt (a + Δ) w) (copyPs true H a (a + Δ)) (copyXN true a (a + Δ)) -
      (copyNbot true H a (a + Δ)).2 =
      -(4 * Δ * H * w - 7 * Δ * H - 6 * Δ * w + 9 * Δ + 12 * H ^ 2 - 48 * H * w + 42 * H
        + 72 * w - 90) / ((2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [inPt, copyPs_snd, copyNbot_snd, copyXN, copyOff]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ 4 * Δ * H * w - 7 * Δ * H - 6 * Δ * w + 9 * Δ + 12 * H ^ 2 - 48 * H * w
      + 42 * H + 72 * w - 90 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := neg_nonpos.2 (div_nonneg hnum (mul_pos h3 hK).le)
  rw [← neg_div, ← key] at hfin
  linarith

/-- LE: the shadow of `σ(v)` through `L_m = P_τ` is at or below `N_bot`. -/
theorem copyLE_sig_Pt (hp : CopyParams H a b) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    vproj (varPt H a v) (copyPt false H a b) (copyXN false a b) ≤ (copyNbot false H a b).2 := by
  have hX := copyPt_fst_sub_a false hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - 2 * Δ + 16 * H - 24 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - 2 * Δ + 16 * H - 24 = K at hK
  have hX' : (copyPt false H a (a + Δ)).1 - (varPt H a v).1 = -K / (H - 1) := by
    rw [varPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  have key : vproj (varPt H a v) (copyPt false H a (a + Δ)) (copyXN false a (a + Δ)) -
      (copyNbot false H a (a + Δ)).2 =
      -(4 * Δ * H * v - 9 * Δ * H - 6 * Δ * v + 15 * Δ + 16 * H ^ 2 + 32 * H * v - 136 * H
        - 48 * v + 168) / ((2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [varPt, copyPt_snd, copyNbot_snd, copyXN, copyOff]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ 4 * Δ * H * v - 9 * Δ * H - 6 * Δ * v + 15 * Δ + 16 * H ^ 2 + 32 * H * v
      - 136 * H - 48 * v + 168 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := neg_nonpos.2 (div_nonneg hnum (mul_pos h3 hK).le)
  rw [← neg_div, ← key] at hfin
  linarith

/-- LE: the shadow of `τ(w)` through `R_m = P_σ` is at or above `N_top`. -/
theorem copyLE_tau_Ps (hp : CopyParams H a b) {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    (copyNtop false H a b).2 ≤ vproj (inPt b w) (copyPs false H a b) (copyXN false a b) := by
  have hX := copyPs_fst_sub_b false hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - Δ + 8 * H - 12 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - Δ + 8 * H - 12 = K at hK
  have hX' : (copyPs false H a (a + Δ)).1 - (inPt (a + Δ) w).1 = -(4 * K) / (2 * H - 1) := by
    rw [inPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  have key : vproj (inPt (a + Δ) w) (copyPs false H a (a + Δ)) (copyXN false a (a + Δ)) -
      (copyNtop false H a (a + Δ)).2 =
      -(4 * Δ * H * w - Δ * H - 6 * Δ * w + 3 * Δ - 16 * H ^ 2 + 64 * H * w - 8 * H - 96 * w
        + 48) / ((2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [inPt, copyPs_snd, copyNtop_snd, copyXN, copyOff]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ -(4 * Δ * H * w - Δ * H - 6 * Δ * w + 3 * Δ - 16 * H ^ 2 + 64 * H * w - 8 * H
      - 96 * w + 48) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := div_nonneg hnum (mul_pos h3 hK).le
  rw [← key] at hfin
  linarith

/-! ### What each guard sees (L5.4) -/

/-- Both mouth ends lie strictly left of the variable segment. -/
theorem copy_mouth_lt_a (ge : Bool) (hp : CopyParams H a b) :
    (copyLm ge H a b).1 < a ∧ (copyRm ge H a b).1 < a := by
  obtain ⟨-, -, h1, h2⟩ := copy_mouth_order ge hp
  cases ge
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

/-- Both mouth ends lie strictly left of the input segment. -/
theorem copy_mouth_lt_b (ge : Bool) (hp : CopyParams H a b) :
    (copyLm ge H a b).1 < b ∧ (copyRm ge H a b).1 < b := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a ge hp
  have := hp.hlo; have := hp.hH
  exact ⟨by linarith, by linarith⟩

/-- The nook segment lies strictly above the ceiling. -/
theorem copyNbot_snd_gt (ge : Bool) (hp : CopyParams H a b) : 2 * H < (copyNbot ge H a b).2 := by
  have h3 := hp.pos3
  have : 3 / (2 * H - 3) < 1 := by rw [div_lt_one h3]; linarith [hp.hH]
  simp only [copyNbot_snd]; linarith

/-- `N_bot` is below `N_top`. -/
theorem copyNbot_lt_Ntop (ge : Bool) (hp : CopyParams H a b) :
    (copyNbot ge H a b).2 < (copyNtop ge H a b).2 := by
  have : 0 < 3 / (2 * H - 3) := div_pos (by norm_num) hp.pos3
  simp only [copyNbot_snd, copyNtop_snd]; linarith

/-- **Variable guard, GE.** A nook point `(x_N, h)` seen from `σ(v)` through the mouth lies at or
above the shadow `copyShadow H v`. -/
theorem copyGE_sig_seen (hp : CopyParams H a b) {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hh : h ≤ (copyNtop true H a b).2) {q : Point}
    (hq : q ∈ segment (copyLm true H a b) (copyRm true H a b))
    (hqs : q ∈ segment (varPt H a v) (copyXN true a b, h)) : copyShadow H v ≤ h := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a true hp
  have hc := between_of_cross_vert hq hqs h1 h2
  simp only [copyLm_true, copyRm_true] at hc
  rw [copy_vproj_sig true hp] at hc
  have hu := copyGE_sig_Pt hp hv1 hv2
  have hs := (copyShadow_mem hp hv1 hv2).2
  simp only [copyNtop_snd] at hh hu
  set u := vproj (varPt H a v) (copyPt true H a b) (copyXN true a b)
  rcases lt_or_eq_of_le (hh.trans hu) with hlt | heq
  · by_contra hcon; push Not at hcon; nlinarith
  · linarith

/-- **Variable guard, LE.** A nook point seen from `σ(v)` through the mouth lies at or below
`copyShadow H v`. -/
theorem copyLE_sig_seen (hp : CopyParams H a b) {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hh : (copyNbot false H a b).2 ≤ h) {q : Point}
    (hq : q ∈ segment (copyLm false H a b) (copyRm false H a b))
    (hqs : q ∈ segment (varPt H a v) (copyXN false a b, h)) : h ≤ copyShadow H v := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a false hp
  have hc := between_of_cross_vert hq hqs h1 h2
  simp only [copyLm_false, copyRm_false] at hc
  rw [copy_vproj_sig false hp] at hc
  have hu := copyLE_sig_Pt hp hv1 hv2
  have hs := (copyShadow_mem hp hv1 hv2).1
  simp only [copyNbot_snd] at hh hu
  set u := vproj (varPt H a v) (copyPt false H a b) (copyXN false a b)
  rcases lt_or_eq_of_le (hu.trans hh) with hlt | heq
  · by_contra hcon; push Not at hcon; nlinarith
  · linarith

/-- **Input guard, GE.** A nook point seen from `τ(w)` through the mouth lies at or below
`copyShadow H w`. -/
theorem copyGE_tau_seen (hp : CopyParams H a b) {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hh : (copyNbot true H a b).2 ≤ h) {q : Point}
    (hq : q ∈ segment (copyLm true H a b) (copyRm true H a b))
    (hqs : q ∈ segment (inPt b w) (copyXN true a b, h)) : h ≤ copyShadow H w := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_b true hp
  have hc := between_of_cross_vert hq hqs h1 h2
  simp only [copyLm_true, copyRm_true] at hc
  rw [copy_vproj_tau true hp] at hc
  have hu := copyGE_tau_Ps hp hw1 hw2
  have hs := (copyShadow_mem hp hw1 hw2).1
  simp only [copyNbot_snd] at hh hu
  set u := vproj (inPt b w) (copyPs true H a b) (copyXN true a b)
  rcases lt_or_eq_of_le (hu.trans hh) with hlt | heq
  · by_contra hcon; push Not at hcon; nlinarith
  · linarith

/-- **Input guard, LE.** A nook point seen from `τ(w)` through the mouth lies at or above
`copyShadow H w`. -/
theorem copyLE_tau_seen (hp : CopyParams H a b) {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hh : h ≤ (copyNtop false H a b).2) {q : Point}
    (hq : q ∈ segment (copyLm false H a b) (copyRm false H a b))
    (hqs : q ∈ segment (inPt b w) (copyXN false a b, h)) : copyShadow H w ≤ h := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_b false hp
  have hc := between_of_cross_vert hq hqs h1 h2
  simp only [copyLm_false, copyRm_false] at hc
  rw [copy_vproj_tau false hp] at hc
  have hu := copyLE_tau_Ps hp hw1 hw2
  have hs := (copyShadow_mem hp hw1 hw2).2
  simp only [copyNtop_snd] at hh hu
  set u := vproj (inPt b w) (copyPs false H a b) (copyXN false a b)
  rcases lt_or_eq_of_le (hh.trans hu) with hlt | heq
  · by_contra hcon; push Not at hcon; nlinarith
  · linarith

/-- **Coverage ⇒ copy inequality, GE.** If every height of the nook segment is at or above the
shadow of `v` or at or below the shadow of `w`, then `w ≤ v`. -/
theorem copyGE_rel_of_shadows (hp : CopyParams H a b) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hcov : ∀ h, 2 * H + 1 - 3 / (2 * H - 3) ≤ h → h ≤ 2 * H + 1 + 3 / (2 * H - 3) →
      copyShadow H v ≤ h ∨ h ≤ copyShadow H w) : w ≤ v := by
  by_contra hlt
  push Not at hlt
  have hs := (copyShadow_lt_iff hp).2 hlt
  have hv := copyShadow_mem hp hv1 hv2
  have hw := copyShadow_mem hp hw1 hw2
  rcases hcov ((copyShadow H v + copyShadow H w) / 2) (by linarith) (by linarith) with h | h
  · linarith
  · linarith

/-- **Coverage ⇒ copy inequality, LE.** If every height of the nook segment is at or below the
shadow of `v` or at or above the shadow of `w`, then `v ≤ w`. -/
theorem copyLE_rel_of_shadows (hp : CopyParams H a b) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hcov : ∀ h, 2 * H + 1 - 3 / (2 * H - 3) ≤ h → h ≤ 2 * H + 1 + 3 / (2 * H - 3) →
      h ≤ copyShadow H v ∨ copyShadow H w ≤ h) : v ≤ w := by
  by_contra hlt
  push Not at hlt
  have hs := (copyShadow_lt_iff hp).2 hlt
  have hv := copyShadow_mem hp hv1 hv2
  have hw := copyShadow_mem hp hw1 hw2
  rcases hcov ((copyShadow H v + copyShadow H w) / 2) (by linarith) (by linarith) with h | h
  · linarith
  · linarith

/-! ### Positive visibility (L5.6): crossing the mouth -/

/-- The mouth line: `det L_m R_m p = (R_m − L_m)(p.2 − 2H)`. -/
theorem copy_det_mouth (ge : Bool) (p : Point) :
    det (copyLm ge H a b) (copyRm ge H a b) p =
      ((copyRm ge H a b).1 - (copyLm ge H a b).1) * (p.2 - 2 * H) := by
  unfold det; rw [copyLm_snd, copyRm_snd]; ring

/-- A guard strictly below the ceiling and a nook point are on opposite sides of the mouth. -/
theorem copy_side (ge : Bool) (hp : CopyParams H a b) {g : Point} (hg : g.2 < 2 * H) {h : ℝ}
    (hh : (copyNbot ge H a b).2 ≤ h) :
    det (copyLm ge H a b) (copyRm ge H a b) g *
      det (copyLm ge H a b) (copyRm ge H a b) (copyXN ge a b, h) < 0 := by
  rw [copy_det_mouth, copy_det_mouth]
  have h1 := copyLm_lt_Rm ge hp
  have h2 := copyNbot_snd_gt ge hp
  have hpos : 0 < (copyRm ge H a b).1 - (copyLm ge H a b).1 := by linarith
  have hA : 0 < h - 2 * H := by linarith
  have hB : 0 < 2 * H - g.2 := by linarith
  nlinarith [mul_pos (mul_pos hpos hpos) (mul_pos hA hB)]

/-- The variable segment lies below the ceiling. -/
theorem varPt_snd_lt (hp : CopyParams H a b) {v : ℝ} (hv2 : v ≤ 2) : (varPt H a v).2 < 2 * H := by
  simp only [varPt_snd]; linarith [hp.hH]

/-- The input segment lies below the ceiling. -/
theorem inPt_snd_lt (hp : CopyParams H a b) {w : ℝ} (hw2 : w ≤ 2) : (inPt b w).2 < 2 * H := by
  simp only [inPt_snd]; linarith [hp.hH]

/-- **Positive visibility, variable guard, GE**: every nook point at or above the shadow of `v` is
reached from `σ(v)` through the mouth. -/
theorem copyGE_sig_cross (hp : CopyParams H a b) {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hh1 : copyShadow H v ≤ h) (hh2 : h ≤ (copyNtop true H a b).2) :
    ∃ q ∈ segment (copyLm true H a b) (copyRm true H a b),
      q ∈ segment (varPt H a v) (copyXN true a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a true hp
  refine exists_cross_vert (copy_side true hp (varPt_snd_lt hp hv2) ?_) h1 h2 ?_
  · linarith [(copyShadow_mem hp hv1 hv2).1, copyNbot_snd (H := H) (a := a) (b := b) true]
  · simp only [copyLm_true, copyRm_true]
    rw [copy_vproj_sig true hp]
    have hu := copyGE_sig_Pt hp hv1 hv2
    nlinarith

/-- **Positive visibility, variable guard, LE**: every nook point at or below the shadow of `v` is
reached from `σ(v)` through the mouth. -/
theorem copyLE_sig_cross (hp : CopyParams H a b) {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hh1 : (copyNbot false H a b).2 ≤ h) (hh2 : h ≤ copyShadow H v) :
    ∃ q ∈ segment (copyLm false H a b) (copyRm false H a b),
      q ∈ segment (varPt H a v) (copyXN false a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a false hp
  refine exists_cross_vert (copy_side false hp (varPt_snd_lt hp hv2) hh1) h1 h2 ?_
  simp only [copyLm_false, copyRm_false]
  rw [copy_vproj_sig false hp]
  have hu := copyLE_sig_Pt hp hv1 hv2
  nlinarith

/-- **Positive visibility, input guard, GE**: every nook point at or below the shadow of `w` is
reached from `τ(w)` through the mouth. -/
theorem copyGE_tau_cross (hp : CopyParams H a b) {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hh1 : (copyNbot true H a b).2 ≤ h) (hh2 : h ≤ copyShadow H w) :
    ∃ q ∈ segment (copyLm true H a b) (copyRm true H a b),
      q ∈ segment (inPt b w) (copyXN true a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_b true hp
  refine exists_cross_vert (copy_side true hp (inPt_snd_lt hp hw2) hh1) h1 h2 ?_
  simp only [copyLm_true, copyRm_true]
  rw [copy_vproj_tau true hp]
  have hu := copyGE_tau_Ps hp hw1 hw2
  nlinarith

/-- **Positive visibility, input guard, LE**: every nook point at or above the shadow of `w` is
reached from `τ(w)` through the mouth. -/
theorem copyLE_tau_cross (hp : CopyParams H a b) {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hh1 : copyShadow H w ≤ h) (hh2 : h ≤ (copyNtop false H a b).2) :
    ∃ q ∈ segment (copyLm false H a b) (copyRm false H a b),
      q ∈ segment (inPt b w) (copyXN false a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_b false hp
  refine exists_cross_vert (copy_side false hp (inPt_snd_lt hp hw2) ?_) h1 h2 ?_
  · linarith [(copyShadow_mem hp hw1 hw2).1, copyNbot_snd (H := H) (a := a) (b := b) false]
  · simp only [copyLm_false, copyRm_false]
    rw [copy_vproj_tau false hp]
    have hu := copyLE_tau_Ps hp hw1 hw2
    nlinarith

/-! ### The partial-visibility region (L5.5) -/

/-- The partial-visibility region of a copy nook: beyond the mouth (`y ≤ 2H`) and between the
two diagonals `N_top L_m` and `N_bot R_m` of the pocket. -/
def copyPV (ge : Bool) (H a b : ℝ) : Set Point :=
  {p | p.2 ≤ 2 * H ∧ 0 ≤ det (copyNtop ge H a b) (copyLm ge H a b) p ∧
    det (copyNbot ge H a b) (copyRm ge H a b) p ≤ 0}

/-- **Viewers of the nook lie in `copyPV` (L1.4).** If `q` is a mouth point on the segment from
a nook point `s` to `p`, then `p ∈ copyPV`. -/
theorem mem_copyPV_of_cross (ge : Bool) (hp : CopyParams H a b) {s q p : Point}
    (hs : s ∈ segment (copyNbot ge H a b) (copyNtop ge H a b))
    (hq : q ∈ segment (copyLm ge H a b) (copyRm ge H a b)) (hqp : q ∈ segment s p) :
    p ∈ copyPV ge H a b := by
  have hLR := copyLm_lt_Rm ge hp
  have hNB := copyNbot_snd_gt ge hp
  have hNN := copyNbot_lt_Ntop ge hp
  obtain ⟨hxL, hxR⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧
      copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  -- heights: `s` above the ceiling, `q` on it
  have hs2 := (affine_of_mem_segment hs Prod.snd (fun t => by simp only [lerp_snd]; ring)).1
  have hq2 : q.2 = 2 * H := by
    have := affine_of_mem_segment hq Prod.snd (fun t => by simp only [lerp_snd]; ring)
    simp only [copyLm_snd, copyRm_snd, min_self, max_self] at this
    linarith [this.1, this.2]
  have hqs : q ≠ s := by
    intro h; rw [h] at hq2
    have : min (copyNbot ge H a b).2 (copyNtop ge H a b).2 = (copyNbot ge H a b).2 :=
      min_eq_left hNN.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- beyond the mouth line
    have := lin_nonneg_of_beyond 0 (-1) (2 * H) hqp hqs (by
      have : min (copyNbot ge H a b).2 (copyNtop ge H a b).2 = (copyNbot ge H a b).2 :=
        min_eq_left hNN.le
      linarith) (by rw [hq2]; ring_nf; rfl)
    linarith
  · -- left diagonal
    refine det_nonneg_of_beyond hqp hqs ?_ ?_
    · have := (affine_of_mem_segment hs (det (copyNtop ge H a b) (copyLm ge H a b))
        (fun t => det_lerp _ _ _ _ t)).2
      have e1 : det (copyNtop ge H a b) (copyLm ge H a b) (copyNbot ge H a b) ≤ 0 := by
        unfold det; simp only [copyNtop_fst, copyNbot_fst, sub_self, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have e2 : det (copyNtop ge H a b) (copyLm ge H a b) (copyNtop ge H a b) = 0 := by simp
      rw [e2, max_eq_right e1] at this
      exact this
    · have := (affine_of_mem_segment hq (det (copyNtop ge H a b) (copyLm ge H a b))
        (fun t => det_lerp _ _ _ _ t)).1
      have e1 : 0 ≤ det (copyNtop ge H a b) (copyLm ge H a b) (copyRm ge H a b) := by
        unfold det; rw [copyLm_snd, copyRm_snd]; simp only [copyNtop_fst]
        have : 2 * H - (copyNtop ge H a b).2 < 0 := by linarith
        nlinarith
      have e2 : det (copyNtop ge H a b) (copyLm ge H a b) (copyLm ge H a b) = 0 := by simp
      rw [e2, min_eq_left e1] at this
      exact this
  · -- right diagonal
    have := nonneg_of_mem_segment_beyond (fun x => -det (copyNbot ge H a b) (copyRm ge H a b) x)
      (fun t => by simp only [det_lerp]; ring) hqp hqs ?_ ?_
    · linarith
    · have := (affine_of_mem_segment hs (det (copyNbot ge H a b) (copyRm ge H a b))
        (fun t => det_lerp _ _ _ _ t)).1
      have e1 : 0 ≤ det (copyNbot ge H a b) (copyRm ge H a b) (copyNtop ge H a b) := by
        unfold det; simp only [copyNtop_fst, copyNbot_fst, sub_self, zero_mul, sub_zero]
        exact mul_nonneg (by linarith) (by linarith)
      have e2 : det (copyNbot ge H a b) (copyRm ge H a b) (copyNbot ge H a b) = 0 := by simp
      rw [e2, min_eq_left e1] at this
      linarith
    · have := (affine_of_mem_segment hq (det (copyNbot ge H a b) (copyRm ge H a b))
        (fun t => det_lerp _ _ _ _ t)).2
      have e1 : det (copyNbot ge H a b) (copyRm ge H a b) (copyLm ge H a b) ≤ 0 := by
        unfold det; rw [copyLm_snd, copyRm_snd]; simp only [copyNbot_fst]
        have : 2 * H - (copyNbot ge H a b).2 < 0 := by linarith
        nlinarith
      have e2 : det (copyNbot ge H a b) (copyRm ge H a b) (copyRm ge H a b) = 0 := by simp
      rw [e2, max_eq_right e1] at this
      linarith

/-! ### Polynomial form of the diagonals -/


/-- GE: the left diagonal `N_top L_m` (through `σ_bot = (a, H)`), polynomial form. -/
theorem copyGE_detL (hp : CopyParams H a b) (p : Point) :
    det (copyNtop true H a b) (copyLm true H a b) p =
      2 * (H * (2 * H - 1) * (p.1 - b) + 2 * H * (12 * H + (b - a) - 18)
        + p.2 * (2 * H - 3) * (b - a - 12)) / ((2 * H - 3) * (2 * H - 1)) := by
  have := hp.pos1.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 1 ≠ 0 := by linarith [hp.hH]
  simp only [copyLm_true, copyNtop, copyPs, copyXN, copyOff, det]
  field_simp
  ring

/-- GE: the right diagonal `N_bot R_m` (through `τ_top = (b, 6)`), polynomial form. -/
theorem copyGE_detR (hp : CopyParams H a b) (p : Point) :
    det (copyNbot true H a b) (copyRm true H a b) p =
      (2 * (H - 1) * (H - 3) * (p.1 - b) + (2 * H - 3) * (b - a - 6) * (p.2 - 6))
        / ((H - 1) * (2 * H - 3)) := by
  have := hp.pos2.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 2 ≠ 0 := by linarith [hp.hH]
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  simp only [copyRm_true, copyNbot, copyPt, copyXN, copyOff, det]
  field_simp
  ring

/-- LE: the left diagonal `N_top L_m` (through `τ_bot = (b, 0)`), polynomial form. -/
theorem copyLE_detL (hp : CopyParams H a b) (p : Point) :
    det (copyNtop false H a b) (copyLm false H a b) p =
      (2 * H * (H - 1) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 8))
        / ((H - 1) * (2 * H - 3)) := by
  have := hp.pos2.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 2 ≠ 0 := by linarith [hp.hH]
  have : H - 1 ≠ 0 := by linarith [hp.hH]
  simp only [copyLm_false, copyNtop, copyPt, copyXN, copyOff, det]
  field_simp
  ring

/-- LE: the right diagonal `N_bot R_m` (through `σ_top = (a, H + 3)`), polynomial form. -/
theorem copyLE_detR (hp : CopyParams H a b) (p : Point) :
    det (copyNbot false H a b) (copyRm false H a b) p =
      2 * ((2 * H - 1) * (H - 3) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 16)
        - 2 * (5 * H - 6) * (b - a) - 16 * (2 * H - 3) * (H + 3)) /
        ((2 * H - 3) * (2 * H - 1)) := by
  have := hp.pos1.ne'; have := hp.pos3.ne'
  have : H * 2 - 3 ≠ 0 := by linarith [hp.hH]
  have : H * 2 - 1 ≠ 0 := by linarith [hp.hH]
  simp only [copyRm_false, copyNbot, copyPs, copyXN, copyOff, det]
  field_simp
  ring

/-! ### Band lemmas -/

/-- Core inequality of the band lemmas: GE, variable band, left diagonal. -/
theorem coreGE_var_lo {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ H * (2 * H - 1) * x + 2 * H * (12 * H + Δ - 18) + y * (2 * H - 3) * (Δ - 12))
    (_hy1 : H ≤ y) (hy2 : y ≤ H + 3) : -15 - Δ ≤ x := by
  have hc : 0 < H * (2 * H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ - 12) ≤ (H + 3) * (2 * H - 3) * (Δ - 12) := by
    have : 0 ≤ (2 * H - 3) * (Δ - 12) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: GE, variable band, right diagonal. -/
theorem coreGE_var_hi {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hR : 2 * (H - 1) * (H - 3) * x + (2 * H - 3) * (Δ - 6) * (y - 6) ≤ 0)
    (hy1 : H ≤ y) (_hy2 : y ≤ H + 3) : x ≤ 15 - Δ := by
  have hc : 0 < 2 * (H - 1) * (H - 3) := by nlinarith
  have h1 : (2 * H - 3) * (Δ - 6) * (H - 6) ≤ (2 * H - 3) * (Δ - 6) * (y - 6) := by
    have : 0 ≤ (2 * H - 3) * (Δ - 6) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: LE, variable band, left diagonal. -/
theorem coreLE_var_lo {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ 2 * H * (H - 1) * x + y * (2 * H - 3) * (Δ + 8))
    (_hy1 : H ≤ y) (hy2 : y ≤ H + 3) : -15 - Δ ≤ x := by
  have hc : 0 < 2 * H * (H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ + 8) ≤ (H + 3) * (2 * H - 3) * (Δ + 8) := by
    have : 0 ≤ (2 * H - 3) * (Δ + 8) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: LE, variable band, right diagonal. -/
theorem coreLE_var_hi {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hR : (2 * H - 1) * (H - 3) * x + y * (2 * H - 3) * (Δ + 16)
        - 2 * (5 * H - 6) * Δ - 16 * (2 * H - 3) * (H + 3) ≤ 0)
    (hy1 : H ≤ y) (_hy2 : y ≤ H + 3) : x ≤ 15 - Δ := by
  have hc : 0 < (2 * H - 1) * (H - 3) := by nlinarith
  have h1 : H * (2 * H - 3) * (Δ + 16) ≤ y * (2 * H - 3) * (Δ + 16) := by
    have : 0 ≤ (2 * H - 3) * (Δ + 16) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: GE, input band, left diagonal. -/
theorem coreGE_in_lo {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ H * (2 * H - 1) * x + 2 * H * (12 * H + Δ - 18) + y * (2 * H - 3) * (Δ - 12))
    (_hy1 : 0 ≤ y) (hy2 : y ≤ 6) : -27 ≤ x := by
  have hc : 0 < H * (2 * H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ - 12) ≤ 6 * (2 * H - 3) * (Δ - 12) := by
    have : 0 ≤ (2 * H - 3) * (Δ - 12) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]

/-- Core inequality of the band lemmas: GE, input band, right diagonal. -/
theorem coreGE_in_hi {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hR : 2 * (H - 1) * (H - 3) * x + (2 * H - 3) * (Δ - 6) * (y - 6) ≤ 0)
    (hy1 : 0 ≤ y) (_hy2 : y ≤ 6) : x ≤ 27 := by
  have hc : 0 < 2 * (H - 1) * (H - 3) := by nlinarith
  have h1 : (2 * H - 3) * (Δ - 6) * (0 - 6) ≤ (2 * H - 3) * (Δ - 6) * (y - 6) := by
    have : 0 ≤ (2 * H - 3) * (Δ - 6) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]

/-- Core inequality of the band lemmas: LE, input band, left diagonal. -/
theorem coreLE_in_lo {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ 2 * H * (H - 1) * x + y * (2 * H - 3) * (Δ + 8))
    (_hy1 : 0 ≤ y) (hy2 : y ≤ 6) : -27 ≤ x := by
  have hc : 0 < 2 * H * (H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ + 8) ≤ 6 * (2 * H - 3) * (Δ + 8) := by
    have : 0 ≤ (2 * H - 3) * (Δ + 8) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]

/-- Core inequality of the band lemmas: LE, input band, right diagonal. -/
theorem coreLE_in_hi {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hR : (2 * H - 1) * (H - 3) * x + y * (2 * H - 3) * (Δ + 16)
        - 2 * (5 * H - 6) * Δ - 16 * (2 * H - 3) * (H + 3) ≤ 0)
    (hy1 : 0 ≤ y) (_hy2 : y ≤ 6) : x ≤ 27 := by
  have hc : 0 < (2 * H - 1) * (H - 3) := by nlinarith
  have h1 : 0 ≤ y * (2 * H - 3) * (Δ + 16) := by
    have : 0 ≤ (2 * H - 3) * (Δ + 16) := by nlinarith
    nlinarith
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: GE, below the input band, left diagonal. -/
theorem coreGE_low {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ H * (2 * H - 1) * x + 2 * H * (12 * H + Δ - 18) + y * (2 * H - 3) * (Δ - 12))
    (hy : y ≤ 0) : -14 - 9 / 10 * y ≤ x := by
  have hc : 0 < H * (2 * H - 1) := by nlinarith
  have hq : 0 ≤ (2 * H - 3) * (H - 12) - 9 / 10 * H * (2 * H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ - 12) ≤ y * (9 / 10 * H * (2 * H - 1)) := by
    nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hy) (by linarith : (0:ℝ) ≤ 2 * H - 3))
      (sub_nonneg.2 hlo), mul_nonneg (neg_nonneg.2 hy) hq]
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0:ℝ) ≤ H)]


/-- Core inequality of the band lemmas: LE, below the input band, left diagonal. -/
theorem coreLE_low {H Δ x y : ℝ} (hH : 1000 ≤ H) (hlo : H ≤ Δ) (_hhi : Δ ≤ 2 * H)
    (hL : 0 ≤ 2 * H * (H - 1) * x + y * (2 * H - 3) * (Δ + 8))
    (hy : y ≤ 0) : -y ≤ x := by
  have hc : 0 < 2 * H * (H - 1) := by nlinarith
  have h1 : y * (2 * H - 3) * (Δ + 8) ≤ y * (2 * H * (H - 1)) := by
    nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hy) (by linarith : (0:ℝ) ≤ 2 * H - 3))
      (sub_nonneg.2 hlo)]
  by_contra hx; push Not at hx
  nlinarith

/-- Polynomial form of `0 ≤ det N_top L_m p` and `det N_bot R_m p ≤ 0` (type GE). -/
theorem copyGE_PV_poly (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV true H a b) :
    0 ≤ H * (2 * H - 1) * (p.1 - b) + 2 * H * (12 * H + (b - a) - 18)
        + p.2 * (2 * H - 3) * (b - a - 12) ∧
      2 * (H - 1) * (H - 3) * (p.1 - b) + (2 * H - 3) * (b - a - 6) * (p.2 - 6) ≤ 0 := by
  obtain ⟨-, hL, hR⟩ := hpv
  rw [copyGE_detL hp] at hL
  rw [copyGE_detR hp] at hR
  have h1 := hp.pos1; have h3 := hp.pos3
  have hH1 : 0 < H - 1 := by linarith [hp.hH]
  constructor
  · by_contra hc; push Not at hc
    have : 2 * (H * (2 * H - 1) * (p.1 - b) + 2 * H * (12 * H + (b - a) - 18)
        + p.2 * (2 * H - 3) * (b - a - 12)) / ((2 * H - 3) * (2 * H - 1)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (mul_pos h3 h1)
    linarith
  · by_contra hc; push Not at hc
    have : 0 < (2 * (H - 1) * (H - 3) * (p.1 - b) + (2 * H - 3) * (b - a - 6) * (p.2 - 6))
        / ((H - 1) * (2 * H - 3)) := div_pos hc (mul_pos hH1 h3)
    linarith

/-- Polynomial form of `0 ≤ det N_top L_m p` and `det N_bot R_m p ≤ 0` (type LE). -/
theorem copyLE_PV_poly (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV false H a b) :
    0 ≤ 2 * H * (H - 1) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 8) ∧
      (2 * H - 1) * (H - 3) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 16)
        - 2 * (5 * H - 6) * (b - a) - 16 * (2 * H - 3) * (H + 3) ≤ 0 := by
  obtain ⟨-, hL, hR⟩ := hpv
  rw [copyLE_detL hp] at hL
  rw [copyLE_detR hp] at hR
  have h1 := hp.pos1; have h3 := hp.pos3
  have hH1 : 0 < H - 1 := by linarith [hp.hH]
  constructor
  · by_contra hc; push Not at hc
    have : (2 * H * (H - 1) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 8))
        / ((H - 1) * (2 * H - 3)) < 0 := div_neg_of_neg_of_pos hc (mul_pos hH1 h3)
    linarith
  · by_contra hc; push Not at hc
    have : 0 < 2 * ((2 * H - 1) * (H - 3) * (p.1 - b) + p.2 * (2 * H - 3) * (b - a + 16)
        - 2 * (5 * H - 6) * (b - a) - 16 * (2 * H - 3) * (H + 3)) / ((2 * H - 3) * (2 * H - 1)) :=
      div_pos (by linarith) (mul_pos h3 h1)
    linarith

/-- **Exclusion at the variable band.** A point of the partial-visibility region at height
`y ∈ [H, H + 3]` is within `15` of the variable abscissa `a`. -/
theorem copyPV_var_band (ge : Bool) (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV ge H a b)
    (hy1 : H ≤ p.2) (hy2 : p.2 ≤ H + 3) : a - 15 ≤ p.1 ∧ p.1 ≤ a + 15 := by
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  cases ge
  · obtain ⟨hL, hR⟩ := copyLE_PV_poly hp hpv
    have h1 := coreLE_var_lo hH hlo hhi hL hy1 hy2
    have h2 := coreLE_var_hi hH hlo hhi hR hy1 hy2
    constructor <;> linarith
  · obtain ⟨hL, hR⟩ := copyGE_PV_poly hp hpv
    have h1 := coreGE_var_lo hH hlo hhi hL hy1 hy2
    have h2 := coreGE_var_hi hH hlo hhi hR hy1 hy2
    constructor <;> linarith

/-- **Exclusion at the input band.** A point of the partial-visibility region at height
`y ∈ [0, 6]` is within `27` of the input abscissa `b`. -/
theorem copyPV_in_band (ge : Bool) (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV ge H a b)
    (hy1 : 0 ≤ p.2) (hy2 : p.2 ≤ 6) : b - 27 ≤ p.1 ∧ p.1 ≤ b + 27 := by
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  cases ge
  · obtain ⟨hL, hR⟩ := copyLE_PV_poly hp hpv
    have h1 := coreLE_in_lo hH hlo hhi hL hy1 hy2
    have h2 := coreLE_in_hi hH hlo hhi hR hy1 hy2
    constructor <;> linarith
  · obtain ⟨hL, hR⟩ := copyGE_PV_poly hp hpv
    have h1 := coreGE_in_lo hH hlo hhi hL hy1 hy2
    have h2 := coreGE_in_hi hH hlo hhi hR hy1 hy2
    constructor <;> linarith

/-- **Exclusion below the input band.** A point of the partial-visibility region at height
`y ≤ 0` satisfies `x ≥ b − 14 − (9/10) y` (the region moves right as it goes down). -/
theorem copyPV_low (ge : Bool) (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV ge H a b)
    (hy : p.2 ≤ 0) : b - 14 - 9 / 10 * p.2 ≤ p.1 := by
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  cases ge
  · have h1 := coreLE_low hH hlo hhi (copyLE_PV_poly hp hpv).1 hy
    linarith
  · have h1 := coreGE_low hH hlo hhi (copyGE_PV_poly hp hpv).1 hy
    linarith

/-- **Exclusion below the input band, type LE** (sharper): `x ≥ b − y` for `y ≤ 0`. -/
theorem copyPV_low_LE (hp : CopyParams H a b) {p : Point} (hpv : p ∈ copyPV false H a b)
    (hy : p.2 ≤ 0) : b - p.2 ≤ p.1 := by
  have h1 := coreLE_low hp.hH hp.hlo hp.hhi (copyLE_PV_poly hp hpv).1 hy
  linarith

end

end Stade

end ArtGallery

end
