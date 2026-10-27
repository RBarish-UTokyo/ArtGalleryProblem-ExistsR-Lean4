module

public import ArtGallery.ETR.REVDefs
public import ArtGallery.ETR.Reduction

/-!
# ETR-INV-REV is ∃ℝ-hard: the reduction (Stade, Theorem 2.4)

Starting from the ETR-INV instance `etrToINV φ`, every equation is replaced as follows
(`revConstraint`, Stade's proof of Theorem 2.4 with the interval `I = [1, 2]`):

* `x = 1` is kept;
* `x + y = z` becomes `x + y ≤ z`, `x + y ≥ z`;
* `a · b = 1` becomes `a · b ≥ 1` and `a · (5/2 − V) ≤ 1`, where four fresh variables
  `V₁, V₂, V₃, V` satisfy (each equation as a pair of inequalities)
  `V₁ + V₁ = b`, `V₁ + V₂ = 3/2`, `V₂ + V₂ = V₃`, `V + 1/2 = V₃`,
  so that `V = 5/2 − b` in every solution.  For `b ∈ [1, 2]` the values `V₁ = b/2 ∈ [1/2, 1]`,
  `V₂ = 3/2 − b/2 ∈ [1/2, 1]`, `V₃ = 3 − b ∈ [1, 2]`, `V = 5/2 − b ∈ [1/2, 3/2]` lie in
  `[1/2, 2]`.

The constants `1/2` and `3/2` are those of the ETR-INV instance (built from `1` by additions
only), and in the solutions produced by `Chain.invSystem_complete` the second argument `b` of
every inversion lies in `[1, 2]`.  Since `V = 5/2 − b` is forced by linear equations, soundness
needs no range assumption.

The `j`-th equation gets the fresh variables `F + 4j, …, F + 4j + 3` with `F = etrToINVVars φ`;
original variable `i` keeps index `i`.
-/

@[expose] public section

namespace ArtGallery

open ArtGallery.Gate ArtGallery.Chain

namespace REV

/-- The ETR-INV-REV translation of one ETR-INV equation, with the constants `1/2` at `K` and
`3/2` at `K + 1`, and the fresh variables `V₁, V₂, V₃, V` at `F, F + 1, F + 2, F + 3`. -/
def revConstraint (K F : ℕ) : ETRINV.Constraint → List ETRINVREV.Constraint
  | .one x => [.one x]
  | .add x y z => [.addLe x y z, .addGe x y z]
  | .inv a b => [.invGe a b, .invRevLe a (F + 3),
      .addLe F F b, .addGe F F b, .addLe F (F + 1) (K + 1), .addGe F (F + 1) (K + 1),
      .addLe (F + 1) (F + 1) (F + 2), .addGe (F + 1) (F + 1) (F + 2),
      .addLe (F + 3) K (F + 2), .addGe (F + 3) K (F + 2)]

/-- The ETR-INV-REV translation of an ETR-INV instance; equation number `j` uses the fresh
variables `F + 4j, …, F + 4j + 3`. -/
def toREV (K F : ℕ) (Φ : List ETRINV.Constraint) : List ETRINVREV.Constraint :=
  blocks (fun j c => revConstraint K (F + 4 * j) c) 0 Φ

theorem revConstraint_sound_basic {K F : ℕ} {Y : ℕ → ℝ} {c : ETRINV.Constraint}
    (h : ∀ d ∈ revConstraint K F c, d.Holds Y) (hc : ∀ a b, c ≠ .inv a b) : c.Holds Y := by
  cases c with
  | one x => exact h (.one x) (by simp [revConstraint])
  | add x y z =>
    have h₁ : Y x + Y y ≤ Y z := h (.addLe x y z) (by simp [revConstraint])
    have h₂ : Y z ≤ Y x + Y y := h (.addGe x y z) (by simp [revConstraint])
    exact le_antisymm h₁ h₂
  | inv a b => exact absurd rfl (hc a b)

theorem revConstraint_sound {K F : ℕ} {Y : ℕ → ℝ} {c : ETRINV.Constraint}
    (h : ∀ d ∈ revConstraint K F c, d.Holds Y) (hK : Y K = 1 / 2) (hK' : Y (K + 1) = 3 / 2) :
    c.Holds Y := by
  cases c with
  | inv a b =>
    simp only [revConstraint, List.forall_mem_cons, forall_mem_nil_iff, and_true,
      ETRINVREV.Constraint.Holds] at h
    obtain ⟨h₀, h₁, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := h
    rw [hK'] at e₃ e₄
    rw [hK] at e₇ e₈
    have hV : Y (F + 3) = 5 / 2 - Y b := by linarith
    rw [hV, show (5 / 2 : ℝ) - (5 / 2 - Y b) = Y b by ring] at h₁
    exact le_antisymm h₁ h₀
  | one x => exact revConstraint_sound_basic h (by simp)
  | add x y z => exact revConstraint_sound_basic h (by simp)

/-- A solution of `toREV K F Φ` satisfies the equations `x = 1` and `x + y = z` of `Φ`. -/
theorem toREV_sound_basic {K F : ℕ} {Φ : List ETRINV.Constraint} {Y : ℕ → ℝ}
    (h : ∀ d ∈ toREV K F Φ, d.Holds Y) :
    ∀ c ∈ Φ, (∀ a b, c ≠ .inv a b) → c.Holds Y := by
  intro c hc hinv
  obtain ⟨i, hi⟩ := subset_blocks (f := fun j c => revConstraint K (F + 4 * j) c) (j := 0) hc
  exact revConstraint_sound_basic (fun d hd => h d (hi d hd)) hinv

/-- A solution of `toREV K F Φ` in which `K` and `K + 1` carry `1/2` and `3/2` solves `Φ`. -/
theorem toREV_sound {K F : ℕ} {Φ : List ETRINV.Constraint} {Y : ℕ → ℝ}
    (h : ∀ d ∈ toREV K F Φ, d.Holds Y) (hK : Y K = 1 / 2) (hK' : Y (K + 1) = 3 / 2) :
    ∀ c ∈ Φ, c.Holds Y := by
  intro c hc
  obtain ⟨i, hi⟩ := subset_blocks (f := fun j c => revConstraint K (F + 4 * j) c) (j := 0) hc
  exact revConstraint_sound (fun d hd => h d (hi d hd)) hK hK'

/-- The values of the fresh variables `V₁, V₂, V₃, V` of an inversion `a · b = 1`. -/
noncomputable def revVal (Y : ℕ → ℝ) : Option ETRINV.Constraint → ℕ → ℝ
  | some (.inv _ b), s => [Y b / 2, 3 / 2 - Y b / 2, 3 - Y b, 5 / 2 - Y b].getD s 1
  | _, _ => 1

/-- **Completeness of the reversal**: a solution of `Φ` in `[1/2, 2]` in which the second
argument of every inversion lies in `[1, 2]` extends to a solution of `toREV K F Φ` in
`[1/2, 2]`. -/
theorem toREV_complete {K F : ℕ} {Φ : List ETRINV.Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt F)
    (hKF : K + 1 < F) {Y : ℕ → ℝ} (hY : ∀ c ∈ Φ, c.Holds Y) (hr : ∀ i, 1 / 2 ≤ Y i ∧ Y i ≤ 2)
    (hinv : ∀ a b, ETRINV.Constraint.inv a b ∈ Φ → 1 ≤ Y b ∧ Y b ≤ 2)
    (hK : Y K = 1 / 2) (hK' : Y (K + 1) = 3 / 2) :
    ∃ Y' : ℕ → ℝ, (∀ i, 1 / 2 ≤ Y' i ∧ Y' i ≤ 2) ∧ (∀ d ∈ toREV K F Φ, d.Holds Y') ∧
      ∀ i < F, Y' i = Y i := by
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → ℝ, Y' = fun i => if i < F then Y i
      else revVal Y Φ[(i - F) / 4]? ((i - F) % 4) := ⟨_, rfl⟩
  have Ylt : ∀ i < F, Y' i = Y i := fun i hi => by simp only [hY', ite_eq_left hi]
  have Yb : ∀ j s, s < 4 → Y' (F + 4 * j + s) = revVal Y Φ[j]? s := by
    intro j s hs
    have h₁ : (F + 4 * j + s - F) / 4 = j := by omega
    have h₂ : (F + 4 * j + s - F) % 4 = s := by omega
    simp only [hY']
    rw [ite_eq_right (by omega), h₁, h₂]
  refine ⟨Y', ?_, ?_, Ylt⟩
  · intro i
    simp only [hY']
    split_ifs
    · exact hr i
    · cases hc : Φ[(i - F) / 4]? with
      | none => norm_num [revVal]
      | some c =>
        cases c with
        | one x => norm_num [revVal]
        | add x y z => norm_num [revVal]
        | inv a b =>
          have hb := hinv a b (List.mem_of_getElem? hc)
          apply getD_range
          simp only [List.forall_mem_cons, forall_mem_nil_iff, and_true]
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hb.1, hb.2]
  · intro d hd
    obtain ⟨j, c, hj, hdc⟩ := mem_blocks hd
    simp only [zero_add] at hdc
    have hmem : c ∈ Φ := List.mem_of_getElem? hj
    have hc := hY c hmem
    have hv := hΦ c hmem
    cases c with
    | one x =>
      simp only [revConstraint, List.mem_singleton] at hdc
      subst hdc
      have hx : x < F := hv
      show Y' x = 1
      rw [Ylt x hx]
      exact hc
    | add x y z =>
      obtain ⟨hx, hy, hz⟩ := hv
      have e : Y x + Y y = Y z := hc
      simp only [revConstraint, List.mem_cons, List.mem_nil_iff, or_false] at hdc
      rcases hdc with rfl | rfl
      · show Y' x + Y' y ≤ Y' z
        rw [Ylt x hx, Ylt y hy, Ylt z hz, e]
      · show Y' z ≤ Y' x + Y' y
        rw [Ylt x hx, Ylt y hy, Ylt z hz, e]
    | inv a b =>
      obtain ⟨ha, hb⟩ := hv
      have e : Y a * Y b = 1 := hc
      have v0 : Y' (F + 4 * j) = Y b / 2 := by
        have := Yb j 0 (by norm_num); rw [Nat.add_zero, hj] at this; rw [this]; rfl
      have v1 : Y' (F + 4 * j + 1) = 3 / 2 - Y b / 2 := by rw [Yb j 1 (by norm_num), hj]; rfl
      have v2 : Y' (F + 4 * j + 2) = 3 - Y b := by rw [Yb j 2 (by norm_num), hj]; rfl
      have v3 : Y' (F + 4 * j + 3) = 5 / 2 - Y b := by rw [Yb j 3 (by norm_num), hj]; rfl
      have k0 : Y' K = 1 / 2 := by rw [Ylt K (by omega), hK]
      have k1 : Y' (K + 1) = 3 / 2 := by rw [Ylt (K + 1) hKF, hK']
      have ya := Ylt a ha
      have yb := Ylt b hb
      simp only [revConstraint, List.mem_cons, List.mem_nil_iff, or_false] at hdc
      rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [ETRINVREV.Constraint.Holds, v0, v1, v2, v3, k0, k1, ya, yb] <;>
        first
        | (rw [e])
        | (rw [show (5 / 2 : ℝ) - (5 / 2 - Y b) = Y b by ring, e])
        | (apply le_of_eq; ring)

/-- Variable bound of `toREV K F Φ`. -/
theorem toREV_vars {K F : ℕ} {Φ : List ETRINV.Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt F)
    (hKF : K + 1 < F) : ∀ d ∈ toREV K F Φ, d.VarsLt (F + 4 * Φ.length) := by
  intro d hd
  obtain ⟨j, c, hj, hdc⟩ := mem_blocks hd
  simp only [zero_add] at hdc
  have hjl : j < Φ.length := (List.getElem?_eq_some_iff.mp hj).1
  have hv := hΦ c (List.mem_of_getElem? hj)
  have hb : F + 4 * j + 4 ≤ F + 4 * Φ.length := by omega
  cases c with
  | one x =>
    simp only [revConstraint, List.mem_singleton] at hdc
    subst hdc
    have hx : x < F := hv
    show x < _
    omega
  | add x y z =>
    obtain ⟨hx, hy, hz⟩ := hv
    simp only [revConstraint, List.mem_cons, List.mem_nil_iff, or_false] at hdc
    rcases hdc with rfl | rfl <;> simp only [ETRINVREV.Constraint.VarsLt] <;> omega
  | inv a b =>
    obtain ⟨ha, hb'⟩ := hv
    simp only [revConstraint, List.mem_cons, List.mem_nil_iff, or_false] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [ETRINVREV.Constraint.VarsLt] <;> omega

end REV

open REV

/-- The index of the constant `1/2` in `etrToINV φ` (the constant `3/2` follows it). -/
def etrHalfIndex (φ : ETR.Formula) : ℕ := etrScaledVars φ + 2

/-- **The ETR-INV-REV instance of a formula.** -/
def etrToREV (φ : ETR.Formula) : List ETRINVREV.Constraint :=
  toREV (etrHalfIndex φ) (etrToINVVars φ) (etrToINV φ)

/-- An exclusive bound on the variable indices of `etrToREV φ`. -/
def etrToREVVars (φ : ETR.Formula) : ℕ := etrToINVVars φ + 4 * (etrToINV φ).length

theorem etrHalfIndex_lt (φ : ETR.Formula) : etrHalfIndex φ + 1 < etrToINVVars φ := by
  simp only [etrHalfIndex, etrToINVVars]
  omega

/-- All variable indices of `etrToREV φ` are below `etrToREVVars φ`. -/
theorem etrToREV_vars (φ : ETR.Formula) : ∀ c ∈ etrToREV φ, c.VarsLt (etrToREVVars φ) :=
  toREV_vars (etrToINV_vars φ) (etrHalfIndex_lt φ)

/-- The constant equations of `etrToINV φ` are not inversions. -/
theorem constHeader_not_inv (M : ℕ) : ∀ c ∈ constHeader M, ∀ a b, c ≠ .inv a b := by
  intro c hc a b
  simp only [constHeader, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **Completeness**: if `φ` is satisfiable, then `etrToREV φ` has a solution in `[1/2, 2]`. -/
theorem etrToREV_complete (φ : ETR.Formula) (h : φ.Satisfiable) :
    ETRINVREV.Satisfiable (etrToREV φ) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨v, hv, -⟩ := φ.toCircuit_complete x hx
  obtain ⟨w, hw, hwR⟩ := ball_bound φ.toCircuit φ.circuitVars φ.toCircuit_vars ⟨v, hv⟩
  obtain ⟨y, hy, hyr⟩ := scaleSystem_complete (etrK_two_le φ) φ.toCircuit_vars hw hwR
    (eps_mul_ball_le _)
  obtain ⟨Y, hYr, hY, hinv, -⟩ := invSystem_complete (etrScaled_vars φ) hy hyr
  have hc : ConstsOK Y (etrScaledVars φ) :=
    constHeader_sound (fun c hc => hY c (List.mem_append_left _ hc))
  obtain ⟨Y', hY'r, hY', -⟩ := toREV_complete (etrToINV_vars φ) (etrHalfIndex_lt φ) hY hYr hinv
    hc.2.2.1 hc.2.2.2.1
  exact ⟨Y', hY'r, hY'⟩

/-- **Soundness**: every solution `y` of `etrToREV φ` (with no range restriction) comes from a
satisfying assignment `x` of `φ` via `y i = ε x i + 7/8` on the variables of `φ`. -/
theorem etrToREV_sound (φ : ETR.Formula) (y : ℕ → ℝ)
    (hy : ∀ c ∈ etrToREV φ, c.Holds y) :
    ∃ x : ℕ → ℝ, φ.Holds x ∧ ∀ i < φ.varBound, y i = (etrScale φ : ℝ) * x i + 7 / 8 := by
  have hbasic := toREV_sound_basic hy
  have hc : ConstsOK y (etrScaledVars φ) := constHeader_sound fun c hc =>
    hbasic c (List.mem_append_left _ hc) (constHeader_not_inv _ c hc)
  exact etrToINV_sound φ y (toREV_sound hy hc.2.2.1 hc.2.2.2.1)

/-- `φ` is satisfiable iff its ETR-INV-REV instance is. -/
theorem etrToREV_iff (φ : ETR.Formula) :
    φ.Satisfiable ↔ ETRINVREV.Satisfiable (etrToREV φ) := by
  refine ⟨etrToREV_complete φ, fun ⟨y, _, hy⟩ => ?_⟩
  obtain ⟨x, hx, -⟩ := etrToREV_sound φ y hy
  exact ⟨x, hx⟩

end ArtGallery

end
