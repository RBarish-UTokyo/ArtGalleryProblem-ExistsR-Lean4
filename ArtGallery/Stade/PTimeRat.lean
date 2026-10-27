module

public import ArtGallery.PTime.Binary

/-!
# Polynomial-time arithmetic on integers and rationals (unary codes)

The `PT` framework codes integers by their sign and their absolute value in unary
(`ArtGallery.instCodeInt`).  Here:

* `PT.gcd`: Euclid's algorithm (`gcdStep`) on unary natural numbers;
* integer arithmetic: `PT.intSubNat`, `PT.intAdd`, `PT.intSub`, `PT.intNeg'`, `PT.intMul`,
  `PT.intDivNat` (exact division by a natural number);
* a code for `ℚ` (`instCodeRat`: numerator and denominator of the normal form, both in unary)
  and the field operations `PT.mkRat`, `PT.ratAdd`, `PT.ratSub`, `PT.ratNeg`, `PT.ratMul`,
  `PT.ratInv`, `PT.ratDiv`, the casts `PT.ratOfNat`, `PT.ratOfInt` and the projections
  `PT.ratNum`, `PT.ratDen`.

All values stay polynomially bounded in unary, so `fun_prop` proves polynomial time of
rational-valued constructions whose numbers have polynomially bounded numerators and
denominators.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Stade

open Complexity Complexity.PT Complexity.PT.Code

variable {α : Type} [Code α]

/-! ### The greatest common divisor -/

/-- One step of Euclid's algorithm. -/
def gcdStep (s : ℕ × ℕ) : ℕ × ℕ := if s.2 = 0 then s else (s.2, s.1 % s.2)

theorem gcdStep_iterate_zero (k a : ℕ) : gcdStep^[k] (a, 0) = (a, 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; simpa [gcdStep] using ih

theorem gcdStep_iterate (k : ℕ) : ∀ a b, b ≤ k → (gcdStep^[k] (a, b)).1 = Nat.gcd a b := by
  induction k with
  | zero =>
    intro a b hb
    obtain rfl : b = 0 := by omega
    simp
  | succ k ih =>
    intro a b hb
    rw [Function.iterate_succ_apply]
    by_cases hb0 : b = 0
    · subst hb0
      simp [gcdStep, gcdStep_iterate_zero]
    · have hlt := Nat.mod_lt a (Nat.pos_of_ne_zero hb0)
      simp only [gcdStep, hb0, ite_false]
      rw [ih b (a % b) (by omega), Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcdStep_iterate_le (k : ℕ) : ∀ a b, (gcdStep^[k] (a, b)).1 ≤ max a b ∧
    (gcdStep^[k] (a, b)).2 ≤ max a b := by
  induction k with
  | zero => intro a b; simp
  | succ k ih =>
    intro a b
    rw [Function.iterate_succ_apply]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [gcdStep, ite_true]
      exact ih a 0
    · have hlt := Nat.mod_lt a (Nat.pos_of_ne_zero hb0)
      simp only [gcdStep, hb0, ite_false]
      have := ih b (a % b)
      constructor <;> omega

/-- **The greatest common divisor** (Euclid's algorithm, `b + 1` steps). -/
@[fun_prop] protected theorem PT.gcd {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT (fun a => Nat.gcd (f a) (g a)) := by
  obtain ⟨cf, kf, hsf⟩ := hf.nat_le
  obtain ⟨cg, kg, hsg⟩ := hg.nat_le
  have h := PT.iterate (step := fun _ => gcdStep) (init := fun a => (f a, g a)) (n := g)
    (by unfold gcdStep; fun_prop) (PT.pair hf hg) hg
    (fun N => 2 * (powerBound cf kf N + powerBound cg kg N) + 2)
    (((PolynomialBound.constant 2).mul ((PolynomialBound.power cf kf).add
      (PolynomialBound.power cg kg))).add (PolynomialBound.constant 2)) ?_
  · exact (PT.fst h).of_eq fun a => gcdStep_iterate (g a) (f a) (g a) le_rfl
  · intro a i _
    have h1 := hsf a
    have h2 := hsg a
    have h3 := gcdStep_iterate_le i (f a) (g a)
    simp only [size_prod, size_nat]
    omega

/-! ### Integers -/

theorem int_sub_natAbs (m n : ℕ) :
    ((m : ℤ) - n).natAbs = if m < n then n - m else m - n := by
  split_ifs with h
  · rw [show ((m : ℤ) - n) = -((n - m : ℕ) : ℤ) by push_cast [h.le]; ring]
    simp
  · have h := not_lt.mp h
    rw [show ((m : ℤ) - n) = ((m - n : ℕ) : ℤ) by push_cast [h]; ring]
    simp

/-- The difference of two natural numbers, as an integer. -/
@[fun_prop] protected theorem PT.intSubNat {m n : α → ℕ} (hm : PT m) (hn : PT n) :
    PT (fun a => ((m a : ℤ) - (n a : ℤ))) := by
  apply PT.int_of_signAbs
  have h : PT (fun a => (decide (m a < n a), if m a < n a then n a - m a else m a - n a)) := by
    fun_prop
  refine h.of_eq fun a => ?_
  rw [int_sub_natAbs]
  congr 1
  simp only [decide_eq_decide]
  omega

/-- The positive part of an integer. -/
def intPos (z : ℤ) : ℕ := if z < 0 then 0 else z.natAbs

/-- The negative part of an integer. -/
def intNegPart (z : ℤ) : ℕ := if z < 0 then z.natAbs else 0

theorem int_eq_pos_sub_neg (z : ℤ) : z = (intPos z : ℤ) - (intNegPart z : ℤ) := by
  unfold intPos intNegPart
  split_ifs with h <;> omega

@[fun_prop] protected theorem PT.intPos {z : α → ℤ} (hz : PT z) : PT (fun a => intPos (z a)) := by
  unfold intPos
  fun_prop

@[fun_prop] protected theorem PT.intNegPart {z : α → ℤ} (hz : PT z) :
    PT (fun a => intNegPart (z a)) := by
  unfold intNegPart
  fun_prop

@[fun_prop] protected theorem PT.intAdd {z w : α → ℤ} (hz : PT z) (hw : PT w) :
    PT (fun a => z a + w a) := by
  have h := PT.intSubNat (m := fun a => intPos (z a) + intPos (w a))
    (n := fun a => intNegPart (z a) + intNegPart (w a)) (by fun_prop) (by fun_prop)
  refine h.of_eq fun a => ?_
  conv_rhs => rw [int_eq_pos_sub_neg (z a), int_eq_pos_sub_neg (w a)]
  push_cast; ring

@[fun_prop] protected theorem PT.intSub {z w : α → ℤ} (hz : PT z) (hw : PT w) :
    PT (fun a => z a - w a) := by
  have h := PT.intSubNat (m := fun a => intPos (z a) + intNegPart (w a))
    (n := fun a => intNegPart (z a) + intPos (w a)) (by fun_prop) (by fun_prop)
  refine h.of_eq fun a => ?_
  conv_rhs => rw [int_eq_pos_sub_neg (z a), int_eq_pos_sub_neg (w a)]
  push_cast; ring

@[fun_prop] protected theorem PT.intNeg' {z : α → ℤ} (hz : PT z) : PT (fun a => -z a) := by
  have h := PT.intSubNat (m := fun a => intNegPart (z a)) (n := fun a => intPos (z a))
    (by fun_prop) (by fun_prop)
  refine h.of_eq fun a => ?_
  conv_rhs => rw [int_eq_pos_sub_neg (z a)]
  ring

@[fun_prop] protected theorem PT.intMul {z w : α → ℤ} (hz : PT z) (hw : PT w) :
    PT (fun a => z a * w a) := by
  have h := PT.intSubNat
    (m := fun a => intPos (z a) * intPos (w a) + intNegPart (z a) * intNegPart (w a))
    (n := fun a => intPos (z a) * intNegPart (w a) + intNegPart (z a) * intPos (w a))
    (by fun_prop) (by fun_prop)
  refine h.of_eq fun a => ?_
  conv_rhs => rw [int_eq_pos_sub_neg (z a), int_eq_pos_sub_neg (w a)]
  push_cast; ring

theorem int_ediv_of_dvd (z : ℤ) (g : ℕ) (h : g ∣ z.natAbs) :
    z / (g : ℤ) = ((intPos z / g : ℕ) : ℤ) - ((intNegPart z / g : ℕ) : ℤ) := by
  unfold intPos intNegPart
  by_cases hz : z < 0
  · simp only [hz, ite_true, Nat.zero_div, Nat.cast_zero, zero_sub]
    have e : z = -((z.natAbs : ℕ) : ℤ) := by omega
    conv_lhs => rw [e]
    rw [Int.neg_ediv_of_dvd (Int.natCast_dvd_natCast.2 h), Int.natCast_ediv]
  · simp only [hz, ite_false, Nat.zero_div, Nat.cast_zero, sub_zero]
    have e : z = ((z.natAbs : ℕ) : ℤ) := by omega
    conv_lhs => rw [e]
    rw [Int.natCast_ediv]

/-- Exact division of an integer by a natural number dividing it. -/
protected theorem PT.intDivNat {z : α → ℤ} {g : α → ℕ} (hz : PT z) (hg : PT g)
    (h : ∀ a, g a ∣ (z a).natAbs) : PT (fun a => z a / (g a : ℤ)) := by
  have h' := PT.intSubNat (m := fun a => intPos (z a) / g a) (n := fun a => intNegPart (z a) / g a)
    (by fun_prop) (by fun_prop)
  exact h'.of_eq fun a => (int_ediv_of_dvd (z a) (g a) (h a)).symm

/-! ### Rationals -/

theorem ratCode_left_inv (q : ℚ) :
    (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)) (q.num, q.den) = q := Rat.num_div_den q

/-- Rationals are coded by the numerator and the denominator of their normal form. -/
instance instCodeRat : Code ℚ :=
  Code.ofInj (fun q : ℚ => (q.num, q.den)) (fun p => (p.1 : ℚ) / (p.2 : ℚ)) ratCode_left_inv

/-- Numerator and denominator. -/
@[fun_prop] protected theorem PT.ratNumDen {q : α → ℚ} (hq : PT q) :
    PT (fun a => ((q a).num, (q a).den)) :=
  (PT.ofInj_to (fun q : ℚ => (q.num, q.den)) (fun p => (p.1 : ℚ) / (p.2 : ℚ))
    ratCode_left_inv).comp hq

@[fun_prop] protected theorem PT.ratNum {q : α → ℚ} (hq : PT q) : PT (fun a => (q a).num) :=
  PT.fst (PT.ratNumDen hq)

@[fun_prop] protected theorem PT.ratDen {q : α → ℚ} (hq : PT q) : PT (fun a => (q a).den) :=
  PT.snd (PT.ratNumDen hq)

/-- Into `ℚ`: it suffices to compute the numerator and the denominator. -/
theorem PT.rat_of_numDen {q : α → ℚ} (h : PT (fun a => ((q a).num, (q a).den))) : PT q :=
  PT.ofInj_mk (fun q : ℚ => (q.num, q.den)) (fun p => (p.1 : ℚ) / (p.2 : ℚ)) ratCode_left_inv h

/-- `mkRat`: the normal form of a fraction. -/
@[fun_prop] protected theorem PT.mkRat {n : α → ℤ} {d : α → ℕ} (hn : PT n) (hd : PT d) :
    PT (fun a => mkRat (n a) (d a)) := by
  apply PT.rat_of_numDen
  simp only [Rat.num_mkRat, Rat.den_mkRat]
  refine PT.pair (PT.ite_prop (by fun_prop) (PT.const 0) ?_) (by fun_prop)
  exact PT.intDivNat hn (by fun_prop) fun a => Nat.gcd_dvd_right _ _

@[fun_prop] protected theorem PT.ratAdd {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => q a + r a) := by
  simp only [Rat.add_def']
  fun_prop

@[fun_prop] protected theorem PT.ratSub {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => q a - r a) := by
  simp only [Rat.sub_def']
  fun_prop

@[fun_prop] protected theorem PT.ratMul {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => q a * r a) := by
  simp only [Rat.mul_def']
  fun_prop

theorem rat_neg_eq (q : ℚ) : -q = mkRat (-q.num) q.den := by
  rw [Rat.mkRat_eq_div]
  conv_lhs => rw [← Rat.num_div_den q]
  push_cast; ring

@[fun_prop] protected theorem PT.ratNeg {q : α → ℚ} (hq : PT q) : PT (fun a => -q a) := by
  simp only [rat_neg_eq]
  fun_prop

theorem rat_inv_eq (q : ℚ) :
    q⁻¹ = mkRat (if q.num < 0 then -(q.den : ℤ) else (q.den : ℤ)) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rcases lt_trichotomy q.num 0 with h | h | h
  · have hc : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]
    rw [ite_eq_left h, hc]
    conv_lhs => rw [hq]
    push_cast
    rw [inv_div, neg_div_neg_eq]
  · have h0 : q = 0 := by rw [hq, h]; simp
    simp [h0]
  · have hc : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h)]
    rw [ite_eq_right (by omega), hc]
    conv_lhs => rw [hq]
    rw [inv_div]
    push_cast; rfl

@[fun_prop] protected theorem PT.ratInv {q : α → ℚ} (hq : PT q) : PT (fun a => (q a)⁻¹) := by
  simp only [rat_inv_eq]
  fun_prop

@[fun_prop] protected theorem PT.ratDiv {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => q a / r a) := by
  simp only [div_eq_mul_inv]
  fun_prop

@[fun_prop] protected theorem PT.ratOfInt {z : α → ℤ} (hz : PT z) : PT (fun a => ((z a : ℤ) : ℚ)) := by
  apply PT.rat_of_numDen
  simp only [Rat.num_intCast, Rat.den_intCast]
  fun_prop

@[fun_prop] protected theorem PT.ratOfNat {n : α → ℕ} (hn : PT n) : PT (fun a => ((n a : ℕ) : ℚ)) := by
  apply PT.rat_of_numDen
  simp only [Rat.num_natCast, Rat.den_natCast]
  fun_prop

end ArtGallery.Stade

end
