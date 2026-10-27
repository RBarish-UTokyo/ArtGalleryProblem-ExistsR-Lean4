module

public import PT.ListMore
public import PT.NatMore
public import Complexity.Approx.Defs
public import Complexity.SATVariants

/-!
# Binary numerals and enumerations of words

Numbers are coded in unary, words in binary; the conversions are:

* `PT.natBits` — the binary digits `natBits (n a)` of a number, least significant first
  (no side condition);
* `PT.binaryValue` — the value `SAT.binaryValue (w a)` of a least-significant-first word, and
  `PT.binValue_foldl` — the value of a most-significant-first word, written as the fold
  `w.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0`; both under the hypothesis that
  `2 ^ (w a).length` is polynomially bounded (the value is exponential in the length);
* `PT.allWords` — all words of length `n a`, when `2 ^ n a` is polynomially bounded, and
  `PT.allWords_mul_log2` — all words of length `c * Nat.log2 (m a)` (no side condition);
* `PT.unary`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α : Type} [Code α]

/-! ### Unary numerals -/

@[fun_prop] protected theorem PT.unary {n : α → Nat} (hn : PT n) : PT (fun a => unary (n a)) :=
  PT.replicate hn (PT.const true)

@[simp] theorem length_unary (k : Nat) : (unary k).length = k := by simp [unary]

/-! ### Binary numerals, most significant digit first -/

theorem binFold_lt (w : Word) (acc : Nat) :
    w.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) acc < (acc + 1) * 2 ^ w.length := by
  induction w generalizing acc with
  | nil => simp
  | cons b w ih =>
    have h1 := ih (2 * acc + (if b then 1 else 0))
    have h2 : (2 * acc + (if b then 1 else 0) + 1) * 2 ^ w.length ≤
        (2 * acc + 2) * 2 ^ w.length :=
      Nat.mul_le_mul_right _ (by split <;> omega)
    have h3 : (acc + 1) * 2 ^ (w.length + 1) = (2 * acc + 2) * 2 ^ w.length := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w.length) 2, ← Nat.mul_assoc]
      congr 1
      omega
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The value of a word read as a binary numeral, most significant digit first (this fold is
`Complexity.binValue`), when `2 ^ (w a).length` is polynomially bounded. -/
protected theorem PT.binValue_foldl {w : α → Word} (hw : PT w)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, 2 ^ (w a).length ≤ bound (size a)) :
    PT (fun a => (w a).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0) := by
  refine PT.foldl (f := fun _ acc b => 2 * acc + (if b then 1 else 0)) (init := fun _ => 0)
    (by fun_prop) (PT.const 0) hw bound hbound ?_
  intro a pre hpre
  have h1 := binFold_lt pre 0
  have h2 : 2 ^ pre.length ≤ 2 ^ (w a).length :=
    Nat.pow_le_pow_right (by omega) hpre.length_le
  have h3 := h a
  rw [size_nat]
  omega

/-! ### Binary numerals, least significant digit first -/

theorem binaryValue_lt (w : Word) : SAT.binaryValue w < 2 ^ w.length := by
  induction w with
  | nil => simp [SAT.binaryValue]
  | cons b w ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [SAT.binaryValue, List.length_cons, Nat.pow_succ]
    omega

/-- The value of a word read as a binary numeral, least significant digit first, when
`2 ^ (w a).length` is polynomially bounded. -/
protected theorem PT.binaryValue {w : α → Word} (hw : PT w)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, 2 ^ (w a).length ≤ bound (size a)) :
    PT (fun a => SAT.binaryValue (w a)) := by
  refine PT.of_listRec (g := fun _ t => SAT.binaryValue t) (base := fun _ => 0)
    (step := fun _ b _ r => b.toNat + 2 * r) (PT.const 0) (by fun_prop) hw (fun _ => rfl)
    (fun _ _ _ => rfl) bound hbound ?_
  intro a suf hsuf
  have h1 := binaryValue_lt suf
  have h2 : 2 ^ suf.length ≤ 2 ^ (w a).length :=
    Nat.pow_le_pow_right (by omega) hsuf.length_le
  have h3 := h a
  rw [size_nat]
  omega

theorem binaryValue_eq_foldr (w : Word) :
    SAT.binaryValue w = w.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [SAT.binaryValue, ih]

/-- The least-significant-first value, written as a right fold. -/
protected theorem PT.binaryValue_foldr {w : α → Word} (hw : PT w)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, 2 ^ (w a).length ≤ bound (size a)) :
    PT (fun a => (w a).foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0) :=
  (PT.binaryValue hw bound hbound h).of_eq fun a => binaryValue_eq_foldr (w a)

theorem natBitsFuel_zero (fuel : Nat) : natBitsFuel fuel 0 = [] := by
  cases fuel <;> simp [natBitsFuel]

theorem length_natBitsFuel_le (fuel n : Nat) : (natBitsFuel fuel n).length ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [natBitsFuel]
  | succ fuel ih =>
    have := ih (n / 2)
    simp only [natBitsFuel]
    split
    · simp
    · simp only [List.length_cons]
      omega

theorem length_natBits_le (n : Nat) : (natBits n).length ≤ n := length_natBitsFuel_le n n

theorem binaryValue_natBitsFuel (fuel n : Nat) (h : n ≤ fuel) :
    SAT.binaryValue (natBitsFuel fuel n) = n := by
  induction fuel generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega
    rfl
  | succ fuel ih =>
    simp only [natBitsFuel]
    split
    · next h0 => rw [h0]; rfl
    · have h1 := ih (n / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;>
        simp only [SAT.binaryValue, h1, h2] <;> simp <;> omega

/-- `natBits` is a right inverse of `SAT.binaryValue`. -/
@[simp] theorem binaryValue_natBits (n : Nat) : SAT.binaryValue (natBits n) = n :=
  binaryValue_natBitsFuel n n (Nat.le_refl n)

/-- One step of the computation of `natBits` on the state `(number, reversed digits)`. -/
def natBitsStep (s : Nat × Word) : Nat × Word :=
  if s.1 = 0 then s else (s.1 / 2, decide (s.1 % 2 = 1) :: s.2)

theorem natBitsStep_iterate (i m : Nat) (acc : Word) :
    natBitsStep^[i] (m, acc) = (m / 2 ^ i, (natBitsFuel i m).reverse ++ acc) := by
  induction i generalizing m acc with
  | zero => simp [natBitsFuel]
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    by_cases h : m = 0
    · subst h
      simp [natBitsStep, ih, natBitsFuel_zero]
    · simp [natBitsStep, h, ih, natBitsFuel, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The binary digits of a number (least significant first). -/
@[fun_prop] protected theorem PT.natBits {n : α → Nat} (hn : PT n) :
    PT (fun a => natBits (n a)) := by
  obtain ⟨c, k, hk⟩ := hn.nat_le
  have hstep : PT natBitsStep := by
    unfold natBitsStep
    fun_prop
  have h := PT.iterate_const (step := natBitsStep) (init := fun a => (n a, ([] : Word))) (n := n)
    hstep (PT.pair hn (PT.const [])) hn (fun N => 3 * powerBound c k N + 2)
    (((PolynomialBound.constant 3).mul (PolynomialBound.power c k)).add
      (PolynomialBound.constant 2)) ?_
  · exact (PT.reverse (PT.snd h)).of_eq fun a => by simp [natBitsStep_iterate, natBits]
  · intro a i hi
    have h1 := hk a
    have h2 := length_natBitsFuel_le i (n a)
    have h3 : n a / 2 ^ i ≤ n a := Nat.div_le_self _ _
    simp only [natBitsStep_iterate, size_prod, size_nat, size_word, List.append_nil,
      List.length_reverse]
    omega

/-! ### All words of a given length -/

theorem length_allWords (n : Nat) : (allWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ l : List Word,
        (l.flatMap fun w => [false :: w, true :: w]).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons w l ihl => simp only [List.flatMap_cons, List.length_append, ihl, List.length_cons,
          List.length_nil]; omega
    rw [allWords_succ, h, ih, Nat.pow_succ, Nat.mul_comm]

theorem length_of_mem_allWords {n : Nat} {w : Word} (h : w ∈ allWords n) : w.length = n := by
  induction n generalizing w with
  | zero => simpa [allWords_zero, allWords_succ] using h
  | succ n ih =>
    simp only [allWords_succ, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨v, hv, rfl | rfl⟩ := h <;> simp [ih hv]

theorem size_allWords_le (n : Nat) : size (allWords n) ≤ 2 ^ n * (2 * n + 2) + 1 := by
  have h := size_map_le (l := allWords n) (g := fun w : Word => w) (K := 2 * n + 1) fun w hw => by
    rw [size_word, length_of_mem_allWords hw]
    exact Nat.le_refl _
  rwa [List.map_id', length_allWords] at h

/-- All words of length `n a`, when their number `2 ^ n a` is polynomially bounded. -/
protected theorem PT.allWords {n : α → Nat} (hn : PT n)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (h : ∀ a, 2 ^ n a ≤ bound (size a)) : PT (fun a => allWords (n a)) := by
  obtain ⟨c, k, hk⟩ := hn.nat_le
  refine PT.of_natRec (g := fun _ i => allWords i) (base := fun _ => [[]])
    (step := fun _ _ s => s.flatMap fun w => [false :: w, true :: w]) (PT.const [[]])
    (by fun_prop) hn (fun _ => rfl) (fun _ _ => rfl)
    (fun N => bound N * (2 * powerBound c k N + 2) + 1)
    ((hbound.mul (((PolynomialBound.constant 2).mul (PolynomialBound.power c k)).add
      (PolynomialBound.constant 2))).add (PolynomialBound.constant 1)) ?_
  intro a i hi
  have h1 := hk a
  have h2 : 2 ^ i ≤ bound (size a) :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hi) (h a)
  exact Nat.le_trans (size_allWords_le i)
    (Nat.add_le_add_right (Nat.mul_le_mul h2 (by omega)) _)

/-- All words of logarithmic length `c * Nat.log2 (m a)` (no side condition). -/
@[fun_prop] protected theorem PT.allWords_mul_log2 (c : Nat) {m : α → Nat} (hm : PT m) :
    PT (fun a => allWords (c * Nat.log2 (m a))) := by
  obtain ⟨d, k, hk⟩ := hm.nat_le
  refine PT.allWords (PT.mul (PT.const c) (PT.log2 hm)) (fun N => powerBound d k N ^ c)
    ((PolynomialBound.power d k).pow c) fun a => ?_
  exact Nat.le_trans (two_pow_mul_log2_le (m a) c) (Nat.pow_le_pow_left (hk a) c)

@[fun_prop] protected theorem PT.allWords_log2_mul (c : Nat) {m : α → Nat} (hm : PT m) :
    PT (fun a => allWords (Nat.log2 (m a) * c)) :=
  (PT.allWords_mul_log2 c hm).of_eq fun a => by rw [Nat.mul_comm]

@[fun_prop] protected theorem PT.allWords_log2 {m : α → Nat} (hm : PT m) :
    PT (fun a => allWords (Nat.log2 (m a))) :=
  (PT.allWords_mul_log2 1 hm).of_eq fun a => by rw [Nat.one_mul]

/-- The random strings of a logarithmic-randomness verifier, as in `InPCP`. -/
theorem PT.allWords_mul_log2_add_two (c : Nat) {m : α → Nat} (hm : PT m) :
    PT (fun a => allWords (c * Nat.log2 (m a + 2))) :=
  PT.allWords_mul_log2 c (PT.add hm (PT.const 2))

end Complexity.PT
