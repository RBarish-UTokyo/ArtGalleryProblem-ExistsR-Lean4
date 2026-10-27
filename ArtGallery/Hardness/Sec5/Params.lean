module

public import ArtGallery.Spec
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Rat.Cast.Order

/-!
# Section 5: parameters of the construction

The global parameters of the reduction ETR-INV → AGP (`docs/section5/01_overview.md`,
`02_main_area.md`, `06_assembly.md`).

* `bigN n k = max (4n + k) 2` (`k` the number of constraints), `S = 200000 · N²`,
  `ρ = 3/(2S)`, `δ = 9ρ`, `ε = ρ/12 = 1/(8S)`;
* slots: `a_σ = (27σ/2, 0)`, guard segment `s_σ = [a_σ, a_σ + (3/2, 0)]`; the shift of
  Theorem 54 `d_i = 27i/2 − 1/2`; the mirror `x ↦ 54n − 12 − x`; `X_L = 54n − 12 − S`;
* the `one` slots (`σ < n` with `one σ ∈ Φ`), the unit list `unitSpecs` and the guard count
  `guardCount n Φ = 46n + 16 k_add + 5 k_inv`;
* basic inequalities between them.

All definitions are computable (lists, natural numbers, rationals).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery

/-- Rational points of the plane (the data of the construction). -/
abbrev Q2 : Type := ℚ × ℚ

/-! ### Global parameters -/

/-- `N = max (4n + k) 2`, where `n` is the number of variables and `k` the number of
constraints. -/
def bigN (n k : ℕ) : ℕ := max (4 * n + k) 2

/-- The scale `S = 200000 · N²`. -/
def S (n k : ℕ) : ℕ := 200000 * bigN n k ^ 2

/-- `ρ = 3/(2S)`. -/
def rho (n k : ℕ) : ℚ := 3 / (2 * (S n k : ℚ))

/-- `δ = 9ρ`. -/
def delta (n k : ℕ) : ℚ := 9 * rho n k

/-- `ε = ρ/12`. -/
def eps (n k : ℕ) : ℚ := rho n k / 12

/-! ### Slots, shifts, mirror -/

/-- The abscissa `27σ/2` of the left endpoint of the guard segment of slot `σ`. -/
def slotX (σ : ℕ) : ℚ := 27 * (σ : ℚ) / 2

/-- The left endpoint `a_σ = (27σ/2, 0)` of the guard segment of slot `σ`. -/
def slotA (σ : ℕ) : Q2 := (slotX σ, 0)

/-- The right endpoint `a_σ + (3/2, 0)` of the guard segment of slot `σ`. -/
def slotB (σ : ℕ) : Q2 := (slotX σ + 3 / 2, 0)

/-- The shift `d_i = 27i/2 − 1/2` of Theorem 54: the guard `(x_i + d_i, 0)` lies on `s_i`. -/
def shift (i : ℕ) : ℚ := 27 * (i : ℚ) / 2 - 1 / 2

/-- The mirror axis constant: the mirror is `x ↦ 54n − 12 − x`. -/
def xMirror (n : ℕ) : ℚ := 54 * (n : ℚ) - 12

/-- The mirror `x ↦ 54n − 12 − x` (maps slot `σ` onto slot `4n − 1 − σ`). -/
def mirror (n : ℕ) (p : Q2) : Q2 := (xMirror n - p.1, p.2)

/-- The abscissa `X_L = 54n − 12 − S` of the left unit line `ℓ_l`. -/
def XL (n k : ℕ) : ℚ := xMirror n - (S n k : ℚ)

/-! ### Constraints -/

/-- The constraint is an addition `x + y = z`. -/
def isAdd : ETRINV.Constraint → Bool
  | .add _ _ _ => true
  | _ => false

/-- The constraint is an inversion `x · y = 1`. -/
def isInv : ETRINV.Constraint → Bool
  | .inv _ _ => true
  | _ => false

/-- The constraint is `x_σ = 1`. -/
def isOneOf (σ : ℕ) : ETRINV.Constraint → Bool
  | .one x => x == σ
  | _ => false

/-- The number of addition constraints. -/
def kAdd (Φ : List ETRINV.Constraint) : ℕ := Φ.countP isAdd

/-- The number of inversion constraints. -/
def kInv (Φ : List ETRINV.Constraint) : ℕ := Φ.countP isInv

/-- Slot `σ` carries the two `one` spikes: `σ < n` and `one σ ∈ Φ` (`mainarea.bottom_wall`). -/
def slotOne (n : ℕ) (Φ : List ETRINV.Constraint) (σ : ℕ) : Bool :=
  decide (σ < n) && Φ.any (isOneOf σ)

/-- **The number of guards** `g = 46n + 16 k_add + 5 k_inv` (`06_assembly.md`). -/
def guardCount (n : ℕ) (Φ : List ETRINV.Constraint) : ℕ := 46 * n + 16 * kAdd Φ + 5 * kInv Φ

/-! ### Units -/

/-- The kind of a unit (the gadget template it carries). -/
inductive Kind where
  | orient
  | ge
  | le
  | inv
  deriving DecidableEq, Repr

/-- A unit: its kind, its real slots and its working slots (`construct.unit_specs`). -/
structure UnitSpec where
  /-- The gadget template. -/
  kind : Kind
  /-- The real slots (base segments) the unit reads. -/
  real : List ℕ
  /-- The working slots (equal to the real slots for right units, `4n − 1 − σ` for left units). -/
  work : List ℕ
  deriving DecidableEq, Repr

/-- The working slot `4n − 1 − σ` of a left unit. -/
def workSlot (n σ : ℕ) : ℕ := 4 * n - 1 - σ

/-- The right orientation units: for `i < n`, `g < 3`, slots `(gn + i, 3n + i)`. -/
def orientR (n : ℕ) : List UnitSpec :=
  (List.range n).flatMap fun i => (List.range 3).map fun g =>
    ⟨.orient, [g * n + i, 3 * n + i], [g * n + i, 3 * n + i]⟩

/-- The left orientation units: real slots `(3n + i, gn + i)`, working slots mirrored. -/
def orientL (n : ℕ) : List UnitSpec :=
  (List.range n).flatMap fun i => (List.range 3).map fun g =>
    ⟨.orient, [3 * n + i, g * n + i], [workSlot n (3 * n + i), workSlot n (g * n + i)]⟩

/-- The right unit of a constraint: `≥`-add on `(a, n+b, 2n+c)` for `add a b c`. -/
def addR (n : ℕ) : ETRINV.Constraint → List UnitSpec
  | .add a b c => [⟨.ge, [a, n + b, 2 * n + c], [a, n + b, 2 * n + c]⟩]
  | _ => []

/-- The left unit of a constraint: `≤`-add on real slots `(2n+b, n+a, c)` for `add a b c`. -/
def addL (n : ℕ) : ETRINV.Constraint → List UnitSpec
  | .add a b c => [⟨.le, [2 * n + b, n + a, c],
      [workSlot n (2 * n + b), workSlot n (n + a), workSlot n c]⟩]
  | _ => []

/-- The inversion unit of a constraint: slots `(a, 3n+b)` for `inv a b`. -/
def invR (n : ℕ) : ETRINV.Constraint → List UnitSpec
  | .inv a b => [⟨.inv, [a, 3 * n + b], [a, 3 * n + b]⟩]
  | _ => []

/-- **The units** `(right, left)` in their deterministic order (`01_overview.md`): right =
orientation units, `≥`-add units, inversion units; left = orientation units, `≤`-add units. -/
def unitSpecs (n : ℕ) (Φ : List ETRINV.Constraint) : List UnitSpec × List UnitSpec :=
  (orientR n ++ Φ.flatMap (addR n) ++ Φ.flatMap (invR n), orientL n ++ Φ.flatMap (addL n))

/-- The number of guards inside a unit (`06_assembly.md`, table). -/
def Kind.nguards : Kind → ℕ
  | .orient => 7
  | .ge => 8
  | .le => 8
  | .inv => 5

/-! ### Basic facts -/

section Basic

variable {n k : ℕ}

theorem two_le_bigN : 2 ≤ bigN n k := le_max_right _ _

theorem four_n_add_k_le_bigN : 4 * n + k ≤ bigN n k := le_max_left _ _

theorem four_n_le_bigN : 4 * n ≤ bigN n k := le_trans (Nat.le_add_right _ _) four_n_add_k_le_bigN

theorem k_le_bigN : k ≤ bigN n k := le_trans (Nat.le_add_left _ _) four_n_add_k_le_bigN

theorem bigN_pos : 0 < bigN n k := lt_of_lt_of_le (by norm_num) two_le_bigN

/-- `S = 200000 N²` as a rational number. -/
theorem S_cast : ((S n k : ℕ) : ℚ) = 200000 * (bigN n k : ℚ) ^ 2 := by
  simp [S]

theorem S_ge : 800000 ≤ S n k := by
  have h := two_le_bigN (n := n) (k := k)
  unfold S
  nlinarith

theorem S_pos : 0 < S n k := lt_of_lt_of_le (by norm_num) S_ge

theorem S_pos_q : (0 : ℚ) < S n k := by exact_mod_cast S_pos

/-- `S ≥ 100000 N`: in particular `S` dominates every slot abscissa `≤ 14N`. -/
theorem S_ge_mul_bigN : 100000 * bigN n k ≤ S n k := by
  have h := two_le_bigN (n := n) (k := k)
  unfold S
  nlinarith

/-- The slot abscissae are small: `54n ≤ 14N` and `14N · 10⁴ ≤ S`. -/
theorem fiftyfour_n_le : 54 * n ≤ 14 * bigN n k := by
  have := four_n_le_bigN (n := n) (k := k); omega

theorem bigN_mul_le_S : 140000 * bigN n k ≤ S n k := by
  have h := two_le_bigN (n := n) (k := k)
  unfold S
  nlinarith

theorem rho_eq : rho n k = 3 / (2 * (S n k : ℚ)) := rfl

theorem delta_eq : delta n k = 27 / (2 * (S n k : ℚ)) := by
  unfold delta rho; ring

theorem eps_eq : eps n k = 1 / (8 * (S n k : ℚ)) := by
  have := S_pos_q (n := n) (k := k)
  unfold eps rho; field_simp; ring

theorem rho_pos : 0 < rho n k := by
  have := S_pos_q (n := n) (k := k); unfold rho; positivity

theorem delta_pos : 0 < delta n k := by
  have := rho_pos (n := n) (k := k); unfold delta; positivity

theorem eps_pos : 0 < eps n k := by
  have := rho_pos (n := n) (k := k); unfold eps; positivity

/-- `δ − 3ρ = 6ρ > 2ε` (band separation, 08 §6 SL4). -/
theorem two_eps_lt_delta_sub : 2 * eps n k < delta n k - 3 * rho n k := by
  have := rho_pos (n := n) (k := k); unfold eps delta; linarith

/-- The width `S − 54n + 6` of the gap between the base line and `ℓ_r` is positive and large. -/
theorem slots_lt_S : 54 * (n : ℚ) + 100000 ≤ S n k := by
  have h1 : ((54 * n : ℕ) : ℚ) ≤ ((14 * bigN n k : ℕ) : ℚ) := by exact_mod_cast fiftyfour_n_le
  have h2 : ((140000 * bigN n k : ℕ) : ℚ) ≤ ((S n k : ℕ) : ℚ) := by exact_mod_cast bigN_mul_le_S
  have h3 : (2 : ℚ) ≤ bigN n k := by exact_mod_cast two_le_bigN
  push_cast at h1 h2
  nlinarith

/-- `X_L ≤ −6 − 100000`: the left unit line is far to the left of the first pocket. -/
theorem XL_le : XL n k ≤ -6 - 99994 := by
  have := slots_lt_S (n := n) (k := k)
  unfold XL xMirror; linarith

/-- The slot abscissae are nonnegative. -/
theorem slotX_nonneg (σ : ℕ) : 0 ≤ slotX σ := by unfold slotX; positivity

/-- Consecutive slots have pitch `27/2`. -/
theorem slotX_succ (σ : ℕ) : slotX (σ + 1) = slotX σ + 27 / 2 := by
  unfold slotX; push_cast; ring

/-- The slots are increasing. -/
theorem slotX_lt {σ σ' : ℕ} (h : σ < σ') : slotX σ + 27 / 2 ≤ slotX σ' := by
  have : ((σ + 1 : ℕ) : ℚ) ≤ σ' := by exact_mod_cast h
  push_cast at this
  unfold slotX; linarith

/-- The last pocket ends at `w_r`: `27σ/2 + 15/2 ≤ 54n − 6` for `σ < 4n`. -/
theorem slotX_add_le {σ : ℕ} (h : σ < 4 * n) : slotX σ + 15 / 2 ≤ 54 * (n : ℚ) - 6 := by
  have : ((σ + 1 : ℕ) : ℚ) ≤ ((4 * n : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at this
  unfold slotX; linarith

/-- The slot `i < n` contains the guard `(x + d_i, 0)` iff `x ∈ [1/2, 2]`. -/
theorem shift_add_mem (i : ℕ) (x : ℚ) :
    (slotX i ≤ x + shift i ∧ x + shift i ≤ slotX i + 3 / 2) ↔ (1 / 2 ≤ x ∧ x ≤ 2) := by
  unfold slotX shift
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The mirror maps the guard segment of slot `σ < 4n` onto that of slot `4n − 1 − σ`
(reversing it). -/
theorem mirror_slotA {σ : ℕ} (h : σ < 4 * n) :
    mirror n (slotX σ + 3 / 2, 0) = slotA (4 * n - 1 - σ) := by
  have e : ((4 * n - 1 - σ : ℕ) : ℚ) = 4 * (n : ℚ) - 1 - σ := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  simp only [mirror, slotA, slotX, xMirror, e, Prod.mk.injEq, and_true]
  ring

/-- The mirror is an involution. -/
theorem mirror_mirror (p : Q2) : mirror n (mirror n p) = p := by
  simp [mirror]

end Basic

end ArtGallery.Sec5

end
