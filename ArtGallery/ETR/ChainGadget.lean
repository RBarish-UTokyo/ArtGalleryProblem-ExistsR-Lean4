module

public import ArtGallery.ETR.Chain
public import Mathlib.Tactic.LinearCombination

/-!
# The gadgets of the reduction to ETR-INV (paper §4, pp. 17–19)

All gadgets use only the ETR-INV equations `x = 1`, `x + y = z`, `x · y = 1`.  They refer to a
block of seven constants at indices `M, …, M + 6` with the values

  `1, 2, 1/2, 3/2, 3/4, 7/4, 7/8`   (`constHeader`, `ConstsOK`),

and to fresh variables at a base index `b`.

The constants are built from `1` by additions only (`1/2 + 1/2 = 1`), so the only inversions are
those of the squaring gadget; their second arguments `σ + 3/4`, `1/(σ − 1/4)`,
`(σ − 1/4)(σ + 3/4)` lie in `[1, 2]` (`sqGadget_invArg`), as needed for ETR-INV-REV.

* `sqGadget M s b` (12 fresh variables): for `σ = Y s ∈ [7/8, 9/8]`,
  `b ↦ σ + 3/4`, `b+1 ↦ 1/(σ + 3/4)`, `b+2 ↦ σ − 1/4`, `b+3 ↦ 1/(σ − 1/4)`,
  `b+4 ↦ 1/(σ − 1/4) − 1/(σ + 3/4) = 1/((σ − 1/4)(σ + 3/4))`, `b+5 ↦ σ² + σ/2 − 3/16`,
  `b+6 ↦ σ + 7/8`, `b+7 ↦ σ + 1/8`, `b+8 ↦ σ/2 + 1/16`, `b+9 ↦ σ² − 1/4`,
  `b+10 ↦ σ² + 1/2`, `b+11 ↦ σ²/2 + 1/4`.
  This is the paper's `V_{x²}` gadget (p. 18), whose interval claims we verified; we stop at
  `σ²/2 + 1/4` (the paper continues to `σ²`, which lies outside `[1/2, 2]` only if `σ` does).
* `prodGadget M X Y Z b` (35 fresh variables) expresses `(X − 7/8)(Y − 7/8) = Z − 7/8`, i.e.
  the product `a · a' = c` of the ETR^{1/8,+,·} variables `a = X − 7/8`, `a' = Y − 7/8`,
  `c = Z − 7/8`, for `a, a' ∈ [−1/8, 1/8]`.  This replaces the combination of the paper's
  product gadget of p. 17 with the product gadget of pp. 18–19 by a shorter chain with two
  squarings instead of three: with `σ = 1 + (a + a')/2`, `δ = 1 + (a − a')/2 ∈ [7/8, 9/8]` we have
  `σ² − δ² = 2a' + a a'`, and
  `b ↦ X + Y`, `b+1 ↦ (X + Y)/2`, `b+2 ↦ (X + Y)/2 + 1`, `b+3 ↦ σ`, `b+4 ↦ X + 1`, `b+5 ↦ δ`,
  `b+6 … b+17`: `sqGadget` of `σ`, `b+18 … b+29`: `sqGadget` of `δ`,
  `b+30 ↦ 5/4 − δ²/2`, `b+31 ↦ 3/2 + a' + a a'/2`, `b+32 ↦ a a'/2 + 5/8`,
  `b+33 ↦ a a' + 5/4`, `b+34 ↦ a a' + 7/4`, and finally `Z + 7/8 = V_{b+34}`.
  All values lie in `[1/2, 2]` (`prodFirst_range`, `sqList_range`, `prodLast_range`).

Soundness of the gadgets (`sqGadget_sound`, `prodGadget_sound`) is pure algebra and needs no
range assumption.
-/

@[expose] public section

namespace ArtGallery.Chain

open ArtGallery.ETRINV

/-- Universal quantification over the empty list. -/
theorem forall_mem_nil_iff {α : Type} (P : α → Prop) : (∀ x ∈ ([] : List α), P x) ↔ True := by
  simp

/-! ## Constants -/

/-- The constants `1, 2, 1/2, 3/2, 3/4, 7/4, 7/8` at the indices `M, …, M + 6`. -/
def constHeader (M : ℕ) : List Constraint :=
  [.one M, .add M M (M + 1), .add (M + 2) (M + 2) M, .add M (M + 2) (M + 3),
    .add (M + 4) (M + 4) (M + 3), .add M (M + 4) (M + 5), .add (M + 6) (M + 6) (M + 5)]

/-- The constants at `M, …, M + 6` have the values `1, 2, 1/2, 3/2, 3/4, 7/4, 7/8`. -/
def ConstsOK (Y : ℕ → ℝ) (M : ℕ) : Prop :=
  Y M = 1 ∧ Y (M + 1) = 2 ∧ Y (M + 2) = 1 / 2 ∧ Y (M + 3) = 3 / 2 ∧ Y (M + 4) = 3 / 4 ∧
    Y (M + 5) = 7 / 4 ∧ Y (M + 6) = 7 / 8

theorem constHeader_sound {Y : ℕ → ℝ} {M : ℕ} (h : ∀ c ∈ constHeader M, c.Holds Y) :
    ConstsOK Y M := by
  simp only [constHeader, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Constraint.Holds] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  have e1 : Y (M + 1) = 2 := by linarith
  have e2 : Y (M + 2) = 1 / 2 := by linarith
  have e3 : Y (M + 3) = 3 / 2 := by linarith
  have e4 : Y (M + 4) = 3 / 4 := by linarith
  have e5 : Y (M + 5) = 7 / 4 := by linarith
  have e6 : Y (M + 6) = 7 / 8 := by linarith
  exact ⟨h0, e1, e2, e3, e4, e5, e6⟩

theorem constHeader_complete {Y : ℕ → ℝ} {M : ℕ} (h : ConstsOK Y M) :
    ∀ c ∈ constHeader M, c.Holds Y := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [constHeader, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Constraint.Holds, h0, h1, h2, h3, h4, h5, h6]
  norm_num

/-! ## Squaring -/

/-- The squaring gadget: `Y (b + 11) = (Y s)²/2 + 1/4`, using inversions only. -/
def sqGadget (M s b : ℕ) : List Constraint :=
  [.add s (M + 4) b, .inv (b + 1) b, .add (b + 2) M b, .inv (b + 2) (b + 3),
    .add (b + 4) (b + 1) (b + 3), .inv (b + 4) (b + 5), .add s (M + 6) (b + 6),
    .add (b + 7) (M + 4) (b + 6), .add (b + 8) (b + 8) (b + 7), .add (b + 9) (b + 8) (b + 5),
    .add (b + 9) (M + 4) (b + 10), .add (b + 11) (b + 11) (b + 10)]

/-- The values of the fresh variables of the squaring gadget. -/
noncomputable def sqList (σ : ℝ) : List ℝ :=
  [σ + 3 / 4, (σ + 3 / 4)⁻¹, σ - 1 / 4, (σ - 1 / 4)⁻¹, (σ - 1 / 4)⁻¹ - (σ + 3 / 4)⁻¹,
    (σ - 1 / 4) * (σ + 3 / 4), σ + 7 / 8, σ + 1 / 8, σ / 2 + 1 / 16, σ ^ 2 - 1 / 4, σ ^ 2 + 1 / 2,
    σ ^ 2 / 2 + 1 / 4]

theorem sqGadget_sound {Y : ℕ → ℝ} {M s b : ℕ} (hc : ConstsOK Y M)
    (h : ∀ c ∈ sqGadget M s b, c.Holds Y) : Y (b + 11) = Y s ^ 2 / 2 + 1 / 4 := by
  obtain ⟨c1, -, -, -, c34, -, c78⟩ := hc
  simp only [sqGadget, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Constraint.Holds] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  rw [c34] at h0 h7 h10
  rw [c1] at h2
  rw [c78] at h6
  have hAC : Y b - Y (b + 2) = 1 := by linarith
  have hE : Y (b + 4) = Y (b + 3) - Y (b + 1) := by linarith
  have key : Y (b + 4) * (Y b * Y (b + 2)) = 1 := by
    rw [hE]
    linear_combination (Y b) * h3 - (Y (b + 2)) * h1 + hAC
  have hF : Y (b + 5) = Y b * Y (b + 2) := by
    linear_combination (-Y (b + 5)) * key + (Y b * Y (b + 2)) * h5
  have hA : Y b = Y s + 3 / 4 := by linarith
  have hC : Y (b + 2) = Y s - 1 / 4 := by linarith
  have e : Y (b + 11) = (Y (b + 5) - (Y s + 1 / 8) / 2 + 3 / 4) / 2 := by linarith
  rw [e, hF, hA, hC]
  ring

theorem sqGadget_complete {Y : ℕ → ℝ} {M s b : ℕ} (hc : ConstsOK Y M) {σ : ℝ}
    (hσ : 7 / 8 ≤ σ) (hs : Y s = σ) (hb : ∀ i < 12, Y (b + i) = (sqList σ).getD i 1) :
    ∀ c ∈ sqGadget M s b, c.Holds Y := by
  obtain ⟨c1, -, -, -, c34, -, c78⟩ := hc
  have y0 : Y b = σ + 3 / 4 := hb 0 (by norm_num)
  have y1 : Y (b + 1) = (σ + 3 / 4)⁻¹ := hb 1 (by norm_num)
  have y2 : Y (b + 2) = σ - 1 / 4 := hb 2 (by norm_num)
  have y3 : Y (b + 3) = (σ - 1 / 4)⁻¹ := hb 3 (by norm_num)
  have y4 : Y (b + 4) = (σ - 1 / 4)⁻¹ - (σ + 3 / 4)⁻¹ := hb 4 (by norm_num)
  have y5 : Y (b + 5) = (σ - 1 / 4) * (σ + 3 / 4) := hb 5 (by norm_num)
  have y6 : Y (b + 6) = σ + 7 / 8 := hb 6 (by norm_num)
  have y7 : Y (b + 7) = σ + 1 / 8 := hb 7 (by norm_num)
  have y8 : Y (b + 8) = σ / 2 + 1 / 16 := hb 8 (by norm_num)
  have y9 : Y (b + 9) = σ ^ 2 - 1 / 4 := hb 9 (by norm_num)
  have y10 : Y (b + 10) = σ ^ 2 + 1 / 2 := hb 10 (by norm_num)
  have y11 : Y (b + 11) = σ ^ 2 / 2 + 1 / 4 := hb 11 (by norm_num)
  have hA : σ + 3 / 4 ≠ 0 := by intro h; linarith
  have hC : σ - 1 / 4 ≠ 0 := by intro h; linarith
  intro c hc
  simp only [sqGadget, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Constraint.Holds, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, hs, c1, c34,
      c78] <;>
    first
    | ring1
    | exact inv_mul_cancel₀ hA
    | exact mul_inv_cancel₀ hC
    | (rw [inv_sub_inv hC hA, div_mul_cancel₀ _ (mul_ne_zero hC hA)]; ring1)

/-! ## Ranges -/

theorem inv_mem_half_two {t : ℝ} (h₁ : 1 / 2 ≤ t) (h₂ : t ≤ 2) : 1 / 2 ≤ t⁻¹ ∧ t⁻¹ ≤ 2 := by
  have ht : 0 < t := by linarith
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hp : 0 < t⁻¹ := inv_pos.mpr ht
  constructor <;> nlinarith

theorem sqList_range {σ : ℝ} (hσ₁ : 7 / 8 ≤ σ) (hσ₂ : σ ≤ 9 / 8) :
    ∀ w ∈ sqList σ, 1 / 2 ≤ w ∧ w ≤ 2 := by
  have hA := inv_mem_half_two (t := σ + 3 / 4) (by linarith) (by linarith)
  have hC := inv_mem_half_two (t := σ - 1 / 4) (by linarith) (by linarith)
  have hP : 1 / 2 ≤ (σ - 1 / 4) * (σ + 3 / 4) ∧ (σ - 1 / 4) * (σ + 3 / 4) ≤ 2 := by
    constructor <;> nlinarith
  have hE : (σ - 1 / 4)⁻¹ - (σ + 3 / 4)⁻¹ = ((σ - 1 / 4) * (σ + 3 / 4))⁻¹ := by
    have : σ + 3 / 4 ≠ 0 := by intro h; linarith
    have : σ - 1 / 4 ≠ 0 := by intro h; linarith
    rw [inv_sub_inv this ‹σ + 3 / 4 ≠ 0›]
    ring
  have hEr := inv_mem_half_two hP.1 hP.2
  simp only [sqList, List.forall_mem_cons, forall_mem_nil_iff, and_true]
  refine ⟨⟨by linarith, by linarith⟩, hA, ⟨by linarith, by linarith⟩, hC, hE ▸ hEr, hP,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem getD_range {l : List ℝ} (h : ∀ w ∈ l, 1 / 2 ≤ w ∧ w ≤ 2) (i : ℕ) :
    1 / 2 ≤ l.getD i 1 ∧ l.getD i 1 ≤ 2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => norm_num
  | some w => exact h w (List.mem_of_getElem? hi)

/-! ## Products -/

/-- The product gadget: `(Y X − 7/8)(Y Yv − 7/8) = Y Z − 7/8`. -/
def prodGadget (M X Yv Z b : ℕ) : List Constraint :=
  [.add X Yv b, .add (b + 1) (b + 1) b, .add (b + 1) M (b + 2), .add (b + 3) (M + 6) (b + 2),
    .add X M (b + 4), .add (b + 5) (b + 1) (b + 4)] ++
  sqGadget M (b + 3) (b + 6) ++ sqGadget M (b + 5) (b + 18) ++
  [.add (b + 30) (b + 18 + 11) (M + 3), .add (b + 30) (b + 6 + 11) (b + 30 + 1),
    .add (b + 30 + 2) Yv (b + 30 + 1), .add (b + 30 + 2) (b + 30 + 2) (b + 30 + 3),
    .add (b + 30 + 3) (M + 2) (b + 30 + 4), .add Z (M + 6) (b + 30 + 4)]

/-- The values of the first six fresh variables of the product gadget. -/
noncomputable def prodFirst (a a' : ℝ) : List ℝ :=
  [a + a' + 7 / 4, (a + a') / 2 + 7 / 8, (a + a') / 2 + 15 / 8, 1 + (a + a') / 2, a + 15 / 8,
    1 + (a - a') / 2]

/-- The values of the last five fresh variables of the product gadget. -/
noncomputable def prodLast (a a' : ℝ) : List ℝ :=
  [5 / 4 - (1 + (a - a') / 2) ^ 2 / 2, 3 / 2 + a' + a * a' / 2, a * a' / 2 + 5 / 8,
    a * a' + 5 / 4, a * a' + 7 / 4]

theorem prodGadget_sound {Y : ℕ → ℝ} {M X Yv Z b : ℕ} (hc : ConstsOK Y M)
    (h : ∀ c ∈ prodGadget M X Yv Z b, c.Holds Y) :
    (Y X - 7 / 8) * (Y Yv - 7 / 8) = Y Z - 7 / 8 := by
  simp only [prodGadget, List.forall_mem_append] at h
  obtain ⟨⟨⟨hf, hs⟩, hd⟩, hl⟩ := h
  have eS := sqGadget_sound hc hs
  have eD := sqGadget_sound hc hd
  obtain ⟨c1, -, c12, c32, -, -, c78⟩ := hc
  simp only [List.forall_mem_cons, forall_mem_nil_iff, and_true, Constraint.Holds] at hf hl
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hf
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hl
  rw [c1] at p2 p4
  rw [c78] at p3 q5
  rw [c32] at q0
  rw [c12] at q4
  have hZ : Y Z = 21 / 8 + Y (b + 3) ^ 2 - Y (b + 5) ^ 2 - 2 * Y Yv := by linarith
  have hσ : Y (b + 3) = (Y X + Y Yv) / 2 + 1 / 8 := by linarith
  have hδ : Y (b + 5) = (Y X - Y Yv) / 2 + 1 := by linarith
  rw [hZ, hσ, hδ]
  ring

theorem prodGadget_complete {Y : ℕ → ℝ} {M X Yv Z b : ℕ} (hc : ConstsOK Y M) {a a' : ℝ}
    (ha₁ : -1 / 8 ≤ a) (ha'₁ : -1 / 8 ≤ a') (ha'₂ : a' ≤ 1 / 8)
    (hX : Y X = a + 7 / 8) (hY : Y Yv = a' + 7 / 8) (hZ : Y Z = a * a' + 7 / 8)
    (hf : ∀ i < 6, Y (b + i) = (prodFirst a a').getD i 1)
    (hs : ∀ i < 12, Y (b + 6 + i) = (sqList (1 + (a + a') / 2)).getD i 1)
    (hd : ∀ i < 12, Y (b + 18 + i) = (sqList (1 + (a - a') / 2)).getD i 1)
    (hl : ∀ i < 5, Y (b + 30 + i) = (prodLast a a').getD i 1) :
    ∀ c ∈ prodGadget M X Yv Z b, c.Holds Y := by
  have f0 : Y b = a + a' + 7 / 4 := hf 0 (by norm_num)
  have f1 : Y (b + 1) = (a + a') / 2 + 7 / 8 := hf 1 (by norm_num)
  have f2 : Y (b + 2) = (a + a') / 2 + 15 / 8 := hf 2 (by norm_num)
  have f3 : Y (b + 3) = 1 + (a + a') / 2 := hf 3 (by norm_num)
  have f4 : Y (b + 4) = a + 15 / 8 := hf 4 (by norm_num)
  have f5 : Y (b + 5) = 1 + (a - a') / 2 := hf 5 (by norm_num)
  have S := sqGadget_complete hc (by linarith) f3 hs
  have D := sqGadget_complete hc (by linarith) f5 hd
  have s11 : Y (b + 6 + 11) = (1 + (a + a') / 2) ^ 2 / 2 + 1 / 4 := hs 11 (by norm_num)
  have d11 : Y (b + 18 + 11) = (1 + (a - a') / 2) ^ 2 / 2 + 1 / 4 := hd 11 (by norm_num)
  have l0 : Y (b + 30) = 5 / 4 - (1 + (a - a') / 2) ^ 2 / 2 := hl 0 (by norm_num)
  have l1 : Y (b + 30 + 1) = 3 / 2 + a' + a * a' / 2 := hl 1 (by norm_num)
  have l2 : Y (b + 30 + 2) = a * a' / 2 + 5 / 8 := hl 2 (by norm_num)
  have l3 : Y (b + 30 + 3) = a * a' + 5 / 4 := hl 3 (by norm_num)
  have l4 : Y (b + 30 + 4) = a * a' + 7 / 4 := hl 4 (by norm_num)
  obtain ⟨c1, -, c12, c32, -, -, c78⟩ := hc
  simp only [prodGadget, List.forall_mem_append]
  refine ⟨⟨⟨?_, S⟩, D⟩, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Constraint.Holds, hX, hY, f0, f1, f2, f3, f4, f5, c1, c78] <;> ring1
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Constraint.Holds, hY, hZ, s11, d11, l0, l1, l2, l3, l4, c12, c32, c78] <;> ring1

theorem prodFirst_range {a a' : ℝ} (ha₁ : -1 / 8 ≤ a) (ha₂ : a ≤ 1 / 8) (ha'₁ : -1 / 8 ≤ a')
    (ha'₂ : a' ≤ 1 / 8) : ∀ w ∈ prodFirst a a', 1 / 2 ≤ w ∧ w ≤ 2 := by
  simp only [prodFirst, List.forall_mem_cons, forall_mem_nil_iff, and_true]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem prodLast_range {a a' : ℝ} (ha₁ : -1 / 8 ≤ a) (ha₂ : a ≤ 1 / 8) (ha'₁ : -1 / 8 ≤ a')
    (ha'₂ : a' ≤ 1 / 8) : ∀ w ∈ prodLast a a', 1 / 2 ≤ w ∧ w ≤ 2 := by
  have p₁ : a * a' ≤ 1 / 64 := by nlinarith
  have p₂ : -1 / 64 ≤ a * a' := by nlinarith
  have d₁ : 49 / 64 ≤ (1 + (a - a') / 2) ^ 2 := by nlinarith
  have d₂ : (1 + (a - a') / 2) ^ 2 ≤ 81 / 64 := by nlinarith
  simp only [prodLast, List.forall_mem_cons, forall_mem_nil_iff, and_true]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ## Arguments of the inversions

For the reduction to ETR-INV-REV (`ArtGallery.ETR.REV`) we record that, in the solutions built
by the completeness lemmas, the second argument of every inversion lies in `[1, 2]`. -/

theorem sqGadget_invArg {Y : ℕ → ℝ} {M s b : ℕ} {σ : ℝ} (hσ₁ : 7 / 8 ≤ σ) (hσ₂ : σ ≤ 9 / 8)
    (hb : ∀ i < 12, Y (b + i) = (sqList σ).getD i 1) :
    ∀ x y, Constraint.inv x y ∈ sqGadget M s b → 1 ≤ Y y ∧ Y y ≤ 2 := by
  have y0 : Y b = σ + 3 / 4 := hb 0 (by norm_num)
  have y3 : Y (b + 3) = (σ - 1 / 4)⁻¹ := hb 3 (by norm_num)
  have y5 : Y (b + 5) = (σ - 1 / 4) * (σ + 3 / 4) := hb 5 (by norm_num)
  intro x y h
  simp [sqGadget] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [y0]
    constructor <;> linarith
  · rw [y3]
    have ht : 0 < σ - 1 / 4 := by linarith
    have hi : (σ - 1 / 4) * (σ - 1 / 4)⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have hp : 0 < (σ - 1 / 4)⁻¹ := inv_pos.mpr ht
    constructor <;> nlinarith
  · rw [y5]
    constructor <;> nlinarith

theorem prodGadget_invArg {Y : ℕ → ℝ} {M X Yv Z b : ℕ} {a a' : ℝ}
    (ha₁ : -1 / 8 ≤ a) (ha₂ : a ≤ 1 / 8) (ha'₁ : -1 / 8 ≤ a') (ha'₂ : a' ≤ 1 / 8)
    (hs : ∀ i < 12, Y (b + 6 + i) = (sqList (1 + (a + a') / 2)).getD i 1)
    (hd : ∀ i < 12, Y (b + 18 + i) = (sqList (1 + (a - a') / 2)).getD i 1) :
    ∀ x y, Constraint.inv x y ∈ prodGadget M X Yv Z b → 1 ≤ Y y ∧ Y y ≤ 2 := by
  intro x y h
  simp only [prodGadget, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · simp at h
  · exact sqGadget_invArg (by linarith) (by linarith) hs x y h
  · exact sqGadget_invArg (by linarith) (by linarith) hd x y h
  · simp at h

/-! ## Variable bounds -/

theorem sqGadget_vars {M s b B : ℕ} (hs : s < B) (hb : b + 12 ≤ B) (hM : M + 7 ≤ B) :
    ∀ c ∈ sqGadget M s b, c.VarsLt B := by
  simp only [sqGadget, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Constraint.VarsLt]
  omega

theorem prodGadget_vars {M X Yv Z b B : ℕ} (hX : X < B) (hY : Yv < B) (hZ : Z < B)
    (hb : b + 35 ≤ B) (hM : M + 7 ≤ B) : ∀ c ∈ prodGadget M X Yv Z b, c.VarsLt B := by
  simp only [prodGadget, List.forall_mem_append]
  refine ⟨⟨⟨?_, sqGadget_vars (by omega) (by omega) hM⟩, sqGadget_vars (by omega) (by omega) hM⟩,
    ?_⟩ <;>
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, and_true, Constraint.VarsLt]
    omega

end ArtGallery.Chain

end
