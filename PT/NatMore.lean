module

public import PT.Nat

/-!
# More polynomial-time arithmetic

* `PT.log2` — the binary logarithm `Nat.log2`;
* `PT.pow_of_le` — a power `b a ^ e a` whose *value* is polynomially bounded (numbers are
  coded in unary, so without such a bound exponentiation is not polynomial-time);
* `PT.two_pow_log2`, `PT.two_pow_mul_log2`, `PT.two_pow_log2_mul` — the powers
  `2 ^ (B * Nat.log2 (m a))`, which need no side condition
  (`two_pow_mul_log2_le : 2 ^ (B * Nat.log2 m) ≤ (m + 1) ^ B`);
* `PT.boolToNat`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.boolToNat {b : α → Bool} (hb : PT b) :
    PT (fun a => (b a).toNat) :=
  (PT.ite hb (PT.const 1) (PT.const 0)).of_eq fun a => by cases b a <;> rfl

/-! ### The binary logarithm -/

/-- One step of the computation of `Nat.log2` on the state `(counter, number)`. -/
def log2Step (s : Nat × Nat) : Nat × Nat := (s.1 + (if 2 ≤ s.2 then 1 else 0), s.2 / 2)

theorem log2Step_iterate (fuel n k : Nat) (h : n ≤ fuel) :
    (log2Step^[fuel] (k, n)).1 = k + Nat.log2 n := by
  induction fuel generalizing n k with
  | zero =>
    obtain rfl : n = 0 := by omega
    simp
  | succ fuel ih =>
    have hs : log2Step (k, n) = (k + (if 2 ≤ n then 1 else 0), n / 2) := rfl
    rw [Function.iterate_succ_apply, hs, ih _ _ (by omega : n / 2 ≤ fuel), Nat.log2_def n]
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      omega
    · have h0 : n / 2 = 0 := by omega
      simp [h2, h0]

theorem log2Step_iterate_le (i n k : Nat) :
    (log2Step^[i] (k, n)).1 ≤ k + i ∧ (log2Step^[i] (k, n)).2 ≤ n := by
  induction i generalizing n k with
  | zero => simp
  | succ i ih =>
    have hs : log2Step (k, n) = (k + (if 2 ≤ n then 1 else 0), n / 2) := rfl
    rw [Function.iterate_succ_apply, hs]
    have h1 := ih (n / 2) (k + (if 2 ≤ n then 1 else 0))
    have h2 : n / 2 ≤ n := Nat.div_le_self _ _
    have h3 : (if 2 ≤ n then 1 else 0) ≤ 1 := by split <;> omega
    omega

@[fun_prop] protected theorem PT.log2 {n : α → Nat} (hn : PT n) :
    PT (fun a => Nat.log2 (n a)) := by
  obtain ⟨c, k, hk⟩ := hn.nat_le
  have hstep : PT log2Step := by
    unfold log2Step
    fun_prop
  have h := PT.iterate_const (step := log2Step) (init := fun a => (0, n a)) (n := n) hstep
    (PT.pair (PT.const 0) hn) hn (fun N => 2 * powerBound c k N + 2)
    (((PolynomialBound.constant 2).mul (PolynomialBound.power c k)).add
      (PolynomialBound.constant 2)) ?_
  · exact (PT.fst h).of_eq fun a => by
      rw [log2Step_iterate _ _ _ (Nat.le_refl _), Nat.zero_add]
  · intro a i hi
    have h1 := hk a
    have h2 := log2Step_iterate_le i (n a) 0
    simp only [size_prod, size_nat]
    omega

/-- `2 ^ Nat.log2 m ≤ m + 1` (with equality only for `m = 0`). -/
theorem two_pow_log2_le (m : Nat) : 2 ^ Nat.log2 m ≤ m + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · exact Nat.le_succ_of_le (Nat.log2_self_le (by omega))

/-- `2 ^ (B * Nat.log2 m) ≤ m ^ B` for `m ≠ 0`. -/
theorem two_pow_mul_log2_le_of_ne_zero {m : Nat} (hm : m ≠ 0) (B : Nat) :
    2 ^ (B * Nat.log2 m) ≤ m ^ B := by
  rw [Nat.mul_comm, Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.log2_self_le hm) B

/-- `2 ^ (B * Nat.log2 m) ≤ (m + 1) ^ B`. -/
theorem two_pow_mul_log2_le (m B : Nat) : 2 ^ (B * Nat.log2 m) ≤ (m + 1) ^ B := by
  rw [Nat.mul_comm, Nat.pow_mul]
  exact Nat.pow_le_pow_left (two_pow_log2_le m) B

/-! ### Bounded powers -/

/-- **Bounded exponentiation**: `b a ^ e a` is polynomial-time when its value is polynomially
bounded. -/
protected theorem PT.pow_of_le {b e : α → Nat} (hb : PT b) (he : PT e)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, b a ^ e a ≤ bound (size a)) : PT (fun a => b a ^ e a) := by
  refine PT.of_natRec (g := fun a i => b a ^ i) (base := fun _ => 1)
    (step := fun a _ s => s * b a) (PT.const 1) (PT.mul (PT.snd PT.snd') (hb.comp PT.fst')) he
    (fun _ => rfl) (fun _ _ => rfl) (fun N => bound N + 2)
    (hbound.add (PolynomialBound.constant 2)) ?_
  intro a i hi
  rw [size_nat]
  rcases Nat.eq_zero_or_pos (b a) with h0 | hpos
  · rw [h0]
    cases i <;> simp
  · have h1 := Nat.pow_le_pow_right hpos hi
    have h2 := h a
    omega

/-- Powers of two with a polynomially bounded value. -/
protected theorem PT.two_pow_of_le {e : α → Nat} (he : PT e)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, 2 ^ e a ≤ bound (size a)) : PT (fun a => 2 ^ e a) :=
  PT.pow_of_le (PT.const 2) he bound hbound h

/-- `2 ^ (B * Nat.log2 (m a))` for a constant `B` (no side condition). -/
@[fun_prop] protected theorem PT.two_pow_mul_log2 (B : Nat) {m : α → Nat} (hm : PT m) :
    PT (fun a => 2 ^ (B * Nat.log2 (m a))) := by
  obtain ⟨c, k, hk⟩ := hm.nat_le
  refine PT.two_pow_of_le (PT.mul (PT.const B) (PT.log2 hm)) (fun N => powerBound c k N ^ B)
    ((PolynomialBound.power c k).pow B) fun a => ?_
  exact Nat.le_trans (two_pow_mul_log2_le (m a) B) (Nat.pow_le_pow_left (hk a) B)

@[fun_prop] protected theorem PT.two_pow_log2_mul (B : Nat) {m : α → Nat} (hm : PT m) :
    PT (fun a => 2 ^ (Nat.log2 (m a) * B)) :=
  (PT.two_pow_mul_log2 B hm).of_eq fun a => by rw [Nat.mul_comm]

@[fun_prop] protected theorem PT.two_pow_log2 {m : α → Nat} (hm : PT m) :
    PT (fun a => 2 ^ Nat.log2 (m a)) :=
  (PT.two_pow_mul_log2 1 hm).of_eq fun a => by rw [Nat.one_mul]

/-- The function `n ↦ 2 ^ (B * Nat.log2 (n + 2))` (the number of random strings of a
logarithmic-randomness verifier) is polynomial-time. -/
theorem PT.two_pow_mul_log2_add_two (B : Nat) : PT (fun n : Nat => 2 ^ (B * Nat.log2 (n + 2))) :=
  PT.two_pow_mul_log2 B (PT.add PT.id (PT.const 2))

end Complexity.PT
