module

public import ArtGallery.ETR.REVDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Stade's construction: global parameters

The global parameters of the construction of `docs/stade/construction.md` §2, for an instance `Φ` of
ETR-INV-REV on the variables `x 0, …, x (n-1)`:

```
gad = [c ∈ Φ | c is not `one`]          C = |gad|
D_V = 600·C + 50                         (spacing of the variable segments)
H   = max(1000, (n−1)·D_V + 1200·C)      (`n − 1` truncated at `0`)
X_0 = H + (n−1)·D_V                      (left end of the gadget row)
a_k = k·D_V                              (abscissa of variable `k`)
g_c = X_0 + 1200·c                       (origin of slot `c`)
x_L = −3H,  x_R = X_0 + 1200·C + 100
```

All parameters are natural numbers (`paramH`, …); the walls `x_L`, `x_R` are rationals.
The *separation inequalities* S1–S4 of proof plan §3 are proved for a generic input abscissa
`b = g_c + δ` with a template offset `δ ∈ [30, 600]` (the template offsets are
`40, 100, 60, 104, 92.5, 210, 370, 530`, see `ArtGallery/Stade/Templates.lean`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

/-! ### Gadget constraints -/

/-- A constraint gets a gadget (a slot of the gadget row) unless it is `x = 1`. -/
def isGad : Constraint → Bool
  | .one _ => false
  | _ => true

/-- The constraint is `x = k` … `= 1`, i.e. `one k`. -/
def isOneOf (k : ℕ) : Constraint → Bool
  | .one x => x == k
  | _ => false

/-- The gadget constraints of `Φ`, in the order of `Φ`. -/
def gad (Φ : List Constraint) : List Constraint := Φ.filter isGad

/-- The `c`-th gadget constraint (`one 0` if `c` is out of range; never used then). -/
def gadAt (Φ : List Constraint) (c : ℕ) : Constraint := (gad Φ).getD c (.one 0)

/-- Variable `k` carries a constraint `x k = 1`. -/
def hasOne (Φ : List Constraint) (k : ℕ) : Bool := Φ.any (isOneOf k)

/-! ### Parameters -/

/-- The number `C` of slots (gadget constraints). -/
def paramC (Φ : List Constraint) : ℕ := (gad Φ).length

/-- The spacing `D_V = 600 C + 50` of the variable segments. -/
def paramDV (Φ : List Constraint) : ℕ := 600 * paramC Φ + 50

/-- The height parameter `H = max(1000, (n−1) D_V + 1200 C)`. -/
def paramH (n : ℕ) (Φ : List Constraint) : ℕ := max 1000 ((n - 1) * paramDV Φ + 1200 * paramC Φ)

/-- The left end `X_0 = H + (n−1) D_V` of the gadget row. -/
def paramX0 (n : ℕ) (Φ : List Constraint) : ℕ := paramH n Φ + (n - 1) * paramDV Φ

/-- The abscissa `a_k = k D_V` of variable `k`. -/
def varA (Φ : List Constraint) (k : ℕ) : ℕ := k * paramDV Φ

/-- The origin `g_c = X_0 + 1200 c` of slot `c`. -/
def slotG (n : ℕ) (Φ : List Constraint) (c : ℕ) : ℕ := paramX0 n Φ + 1200 * c

/-- The left wall `x_L = −3H`. -/
def xL (n : ℕ) (Φ : List Constraint) : ℚ := -3 * (paramH n Φ : ℚ)

/-- The right wall `x_R = X_0 + 1200 C + 100`. -/
def xR (n : ℕ) (Φ : List Constraint) : ℚ := (paramX0 n Φ : ℚ) + 1200 * (paramC Φ : ℚ) + 100

/-! ### Basic facts -/

theorem paramH_ge (n : ℕ) (Φ : List Constraint) : 1000 ≤ paramH n Φ := le_max_left _ _

theorem paramH_ge' (n : ℕ) (Φ : List Constraint) :
    (n - 1) * paramDV Φ + 1200 * paramC Φ ≤ paramH n Φ := le_max_right _ _

theorem paramDV_ge (Φ : List Constraint) : 600 * paramC Φ + 50 = paramDV Φ := rfl

theorem paramH_pos (n : ℕ) (Φ : List Constraint) : 0 < paramH n Φ := by
  have := paramH_ge n Φ; omega

/-- `H ≥ 1000` over `ℚ`. -/
theorem paramH_ge_q (n : ℕ) (Φ : List Constraint) : (1000 : ℚ) ≤ (paramH n Φ : ℚ) := by
  exact_mod_cast paramH_ge n Φ

/-! ### S1: slope window -/

/-- **S1** (lower half, over `ℕ`).  Every slot origin lies at least `H` to the right of every
variable `k < n`. -/
theorem s1_lower {n : ℕ} {Φ : List Constraint} {k c : ℕ} (hk : k < n) :
    varA Φ k + paramH n Φ ≤ slotG n Φ c := by
  unfold slotG paramX0 varA
  have : k * paramDV Φ ≤ (n - 1) * paramDV Φ := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **S1** over `ℚ`: for `b = g_c + δ` with `c < C`, `30 ≤ δ ≤ 600`, and `k < n`:
`H ≤ b − a_k ≤ 2H − 600`. -/
theorem s1 {n : ℕ} {Φ : List Constraint} {k c : ℕ} (hk : k < n) (hc : c < paramC Φ) {δ : ℚ}
    (hδ0 : 30 ≤ δ) (hδ1 : δ ≤ 600) :
    (paramH n Φ : ℚ) + 30 ≤ (slotG n Φ c : ℚ) + δ - (varA Φ k : ℚ) ∧
      (slotG n Φ c : ℚ) + δ - (varA Φ k : ℚ) ≤ 2 * (paramH n Φ : ℚ) - 600 := by
  have h1 : k * paramDV Φ ≤ (n - 1) * paramDV Φ := Nat.mul_le_mul_right _ (by omega)
  have h2 := paramH_ge' n Φ
  have e1 : varA Φ k + paramH n Φ ≤ slotG n Φ c := by unfold slotG paramX0 varA; omega
  have e2 : slotG n Φ c + 1200 ≤ varA Φ k + 2 * paramH n Φ := by
    unfold slotG paramX0 varA
    have : 1200 * c + 1200 ≤ 1200 * paramC Φ := by omega
    omega
  have e1' : ((varA Φ k : ℕ) : ℚ) + (paramH n Φ : ℚ) ≤ (slotG n Φ c : ℚ) := by exact_mod_cast e1
  have e2' : (slotG n Φ c : ℚ) + 1200 ≤ (varA Φ k : ℚ) + 2 * (paramH n Φ : ℚ) := by
    exact_mod_cast e2
  constructor <;> linarith

/-! ### S2: separation of the segment abscissae -/

/-- **S2** (variables).  Distinct variables are `D_V ≥ 650` apart. -/
theorem s2_var {Φ : List Constraint} {k k' : ℕ} (h : k < k') :
    (varA Φ k : ℚ) + 50 + 600 * (paramC Φ : ℚ) ≤ (varA Φ k' : ℚ) := by
  have : varA Φ k + paramDV Φ ≤ varA Φ k' := by
    unfold varA
    have := Nat.mul_le_mul_right (paramDV Φ) (show k + 1 ≤ k' by omega)
    rw [Nat.add_mul, one_mul] at this
    exact this
  have h' : ((varA Φ k + paramDV Φ : ℕ) : ℚ) ≤ (varA Φ k' : ℚ) := by exact_mod_cast this
  push_cast [paramDV] at h'
  linarith

/-- **S2** (slots).  Slot `c` lies `1200` to the left of slot `c' > c`. -/
theorem s2_slot {n : ℕ} {Φ : List Constraint} {c c' : ℕ} (h : c < c') :
    (slotG n Φ c : ℚ) + 1200 ≤ (slotG n Φ c' : ℚ) := by
  have : slotG n Φ c + 1200 ≤ slotG n Φ c' := by unfold slotG; omega
  exact_mod_cast this

/-- **S2** (variables vs inputs).  Every input lies at least `H` to the right of every
variable (`k < n`). -/
theorem s2_var_slot {n : ℕ} {Φ : List Constraint} {k c : ℕ} (hk : k < n) :
    (varA Φ k : ℚ) + (paramH n Φ : ℚ) ≤ (slotG n Φ c : ℚ) := by
  have := s1_lower (Φ := Φ) (c := c) hk
  exact_mod_cast this

/-- The slots lie strictly between the walls: `g_c + 600 + 100 ≤ x_R` for `c < C`. -/
theorem slot_lt_xR {n : ℕ} {Φ : List Constraint} {c : ℕ} (hc : c < paramC Φ) :
    (slotG n Φ c : ℚ) + 1300 ≤ xR n Φ := by
  have : slotG n Φ c + 1200 ≤ paramX0 n Φ + 1200 * paramC Φ := by unfold slotG; omega
  have h' : ((slotG n Φ c + 1200 : ℕ) : ℚ) ≤ ((paramX0 n Φ + 1200 * paramC Φ : ℕ) : ℚ) := by
    exact_mod_cast this
  push_cast at h'
  unfold xR; linarith

/-- The variables lie strictly between the walls. -/
theorem var_lt_xR {n : ℕ} {Φ : List Constraint} {k : ℕ} (hk : k < n) :
    (varA Φ k : ℚ) + (paramH n Φ : ℚ) + 100 ≤ xR n Φ := by
  have h := s2_var_slot (Φ := Φ) (c := 0) hk
  have : (slotG n Φ 0 : ℚ) = (paramX0 n Φ : ℚ) := by simp [slotG]
  unfold xR
  have : (0 : ℚ) ≤ paramC Φ := by positivity
  linarith

/-! ### S3: copy nooks -/

/-- **S3** (range of a copy nook).  For a variable `k < n` and an input `b = g_c + δ`
(`c < C`, `30 ≤ δ ≤ 600`) and an offset `e ∈ [−16, 12]`, the nook abscissa
`x_N = 2 a_k − b + e` satisfies `−2H − 16 ≤ x_N ≤ −1200 C − 18`, hence `x_N + 3 < −1` and
`x_L < x_N`. -/
theorem s3_range {n : ℕ} {Φ : List Constraint} {k c : ℕ} (hk : k < n) (hc : c < paramC Φ)
    {δ e : ℚ} (hδ0 : 30 ≤ δ) (hδ1 : δ ≤ 600) (he0 : -16 ≤ e) (he1 : e ≤ 12) :
    -2 * (paramH n Φ : ℚ) - 16 ≤ 2 * (varA Φ k : ℚ) - ((slotG n Φ c : ℚ) + δ) + e ∧
      2 * (varA Φ k : ℚ) - ((slotG n Φ c : ℚ) + δ) + e ≤ -1200 * (paramC Φ : ℚ) - 18 := by
  obtain ⟨h1, h2⟩ := s1 (Φ := Φ) hk hc hδ0 hδ1
  have h3 : k * paramDV Φ ≤ (n - 1) * paramDV Φ := Nat.mul_le_mul_right _ (by omega)
  have h4 := paramH_ge' n Φ
  have e3 : varA Φ k + 1200 * paramC Φ ≤ paramH n Φ := by unfold varA; omega
  have e3' : (varA Φ k : ℚ) + 1200 * (paramC Φ : ℚ) ≤ (paramH n Φ : ℚ) := by exact_mod_cast e3
  have : (0 : ℚ) ≤ varA Φ k := by positivity
  constructor <;> linarith

/-- **S3** (separation of copy nooks).  Two copy nooks of the same variable whose inputs are at
least `44` apart (`b + 44 ≤ b'`) have abscissae at least `16` apart (in reverse order). -/
theorem s3_same {a b b' e e' : ℚ} (hb : b + 44 ≤ b') (he : -16 ≤ e ∧ e ≤ 12)
    (he' : -16 ≤ e' ∧ e' ≤ 12) : (2 * a - b' + e') + 16 ≤ 2 * a - b + e := by
  linarith [he.1, he'.2]

/-- **S3** (separation of copy nooks of different variables).  If `k < k'` then every copy
nook of `k'` lies more than `600` to the right of every copy nook of `k`. -/
theorem s3_diff {n : ℕ} {Φ : List Constraint} {k k' c c' : ℕ} (hkk : k < k')
    (hc' : c' < paramC Φ) {δ δ' e e' : ℚ} (hδ0 : 30 ≤ δ) (hδ1' : δ' ≤ 600)
    (he : -16 ≤ e ∧ e ≤ 12) (he' : -16 ≤ e' ∧ e' ≤ 12) :
    2 * (varA Φ k : ℚ) - ((slotG n Φ c : ℚ) + δ) + e + 600 ≤
      2 * (varA Φ k' : ℚ) - ((slotG n Φ c' : ℚ) + δ') + e' := by
  have h1 := s2_var (Φ := Φ) hkk
  have hc1 : (slotG n Φ c : ℚ) + 0 ≥ (paramX0 n Φ : ℚ) := by
    have : paramX0 n Φ ≤ slotG n Φ c := by unfold slotG; omega
    simp only [add_zero, ge_iff_le]; exact_mod_cast this
  have hc2 : (slotG n Φ c' : ℚ) + 1200 ≤ (paramX0 n Φ : ℚ) + 1200 * (paramC Φ : ℚ) := by
    have : slotG n Φ c' + 1200 ≤ paramX0 n Φ + 1200 * paramC Φ := by unfold slotG; omega
    exact_mod_cast this
  linarith [he.1, he.2, he'.1, he'.2]

/-! ### S4: walls -/

/-- **S4** (walls).  `x_L + 900 ≤ −2H − 16`: the walls are far to the left of all copy nooks. -/
theorem s4_xL (n : ℕ) (Φ : List Constraint) : xL n Φ + 900 ≤ -2 * (paramH n Φ : ℚ) - 16 := by
  have := paramH_ge_q n Φ
  unfold xL; linarith

end ArtGallery.Stade

end
