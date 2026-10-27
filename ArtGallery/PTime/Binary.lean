module

public import ArtGallery.PTime.Scan

/-!
# Binary numbers

Digit lists are least significant digit first, as `Nat.bits` (the binary codes of
`ArtGallery.Spec`); the value of a digit list is `SAT.binaryValue`.

* `natBits_eq_bits : Complexity.natBits n = n.bits`; `binWord d` (the binary code with digits
  `d`), `binaryNat_eq_binWord`, `PT.binWord`, `PT.binaryNat`;
* a `Code ℤ` instance (sign bit and absolute value in unary, `instCodeInt`), `intDigits`,
  `binIntWord`, `binaryInt_eq_binIntWord`, `PT.intDigits`, `PT.binaryInt`;
* readers of binary numbers at the start of a word, returning the digits and the rest:
  `readBin`, `readBinInt` (`readBin_binWord`, `readBinInt_binIntWord`, `PT.readBin`,
  `PT.readBinInt`), and the decoders `decodeBinaryNat`, `decodeBinaryInt` (round trip and
  soundness);
* digit lists of numbers: `natDigitsOk d` (no leading zero) ↔ `d = n.bits` for some `n`
  (`bits_binaryValue`, `natDigitsOk_bits`), and `intDigitsOk`, `intOfDigits`;
* **`PT.binaryValue_min`**: the value of a binary numeral clamped by a unary bound,
  `min (SAT.binaryValue d) B`, is polynomial-time;
* a generic scanner `scanList` for `encodeList`-codes (`scanList_encodeList`, `PT.scanList`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

/-! ### Digits of natural numbers -/

theorem natBitsFuel_eq_bits (fuel n : ℕ) (h : n ≤ fuel) : natBitsFuel fuel n = n.bits := by
  induction fuel generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega
    simp [natBitsFuel]
  | succ fuel ih =>
    simp only [natBitsFuel]
    split_ifs with h0
    · subst h0; simp
    · rw [ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · have e : n = 2 * (n / 2) := by omega
        conv_rhs => rw [e]
        rw [Nat.bit0_bits _ (by omega)]
        simp [h2]
      · have e : n = 2 * (n / 2) + 1 := by omega
        conv_rhs => rw [e]
        rw [Nat.bit1_bits]
        simp [h2]

/-- The library's `natBits` is Mathlib's `Nat.bits`. -/
theorem natBits_eq_bits (n : ℕ) : natBits n = n.bits := natBitsFuel_eq_bits n n le_rfl

theorem binaryValue_bits (n : ℕ) : SAT.binaryValue n.bits = n := by
  rw [← natBits_eq_bits]
  exact binaryValue_natBits n

/-- A digit list without leading zero (its most significant digit, the last one, is `1`). -/
def natDigitsOk (d : Word) : Bool := d.getLast? != some false

theorem bits_binaryValue {d : Word} (h : natDigitsOk d = true) : (SAT.binaryValue d).bits = d := by
  induction d with
  | nil => simp [SAT.binaryValue]
  | cons b d ih =>
    rcases d with _ | ⟨c, d⟩
    · have hb : b = true := by simpa [natDigitsOk] using h
      subst hb
      simp [SAT.binaryValue]
    · have h' : natDigitsOk (c :: d) = true := by simpa [natDigitsOk] using h
      have ih' := ih h'
      have hne : SAT.binaryValue (c :: d) ≠ 0 := by
        intro h0
        rw [h0] at ih'
        simp at ih'
      simp only [SAT.binaryValue] at ih' hne ⊢
      generalize SAT.binaryValue d = m at ih' hne ⊢
      cases b
      · simp only [Bool.toNat_false, Nat.zero_add]
        rw [Nat.bit0_bits _ hne, ih']
      · simp only [Bool.toNat_true]
        rw [Nat.add_comm, Nat.bit1_bits, ih']

theorem natDigitsOk_bits (n : ℕ) : natDigitsOk n.bits = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [natDigitsOk]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · have e : n = 2 * (n / 2) := by omega
      have hm : n / 2 ≠ 0 := by omega
      rw [e, Nat.bit0_bits _ hm]
      have := ih (n / 2) (by omega)
      obtain ⟨c, l, hcl⟩ : ∃ c l, (n / 2).bits = c :: l := by
        rcases h : (n / 2).bits with _ | ⟨c, l⟩
        · have := binaryValue_bits (n / 2); rw [h] at this; simp [SAT.binaryValue] at this
          omega
        · exact ⟨c, l, rfl⟩
      rw [hcl] at this ⊢
      simpa [natDigitsOk] using this
    · have e : n = 2 * (n / 2) + 1 := by omega
      rw [e, Nat.bit1_bits]
      rcases Nat.eq_zero_or_pos (n / 2) with h0 | h0
      · rw [h0]; simp [natDigitsOk]
      · have := ih (n / 2) (by omega)
        obtain ⟨c, l, hcl⟩ : ∃ c l, (n / 2).bits = c :: l := by
          rcases h : (n / 2).bits with _ | ⟨c, l⟩
          · have := binaryValue_bits (n / 2); rw [h] at this; simp [SAT.binaryValue] at this
            omega
          · exact ⟨c, l, rfl⟩
        rw [hcl] at this ⊢
        simpa [natDigitsOk] using this

/-- The binary code with digit list `d`: the number of digits in unary, then the digits. -/
def binWord (d : Word) : Word := ArtGallery.unary d.length ++ d

theorem binaryNat_eq_binWord (n : ℕ) : binaryNat n = binWord n.bits := rfl

/-! ### Integers -/

theorem intCode_left_inv (z : ℤ) :
    (fun p : Bool × ℕ => if p.1 then -(p.2 : ℤ) else (p.2 : ℤ)) (decide (z < 0), z.natAbs) = z := by
  by_cases h : z < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

/-- Integers are coded by their sign and their absolute value (in unary). -/
instance instCodeInt : Code ℤ :=
  Code.ofInj (fun z : ℤ => (decide (z < 0), z.natAbs))
    (fun p => if p.1 then -(p.2 : ℤ) else (p.2 : ℤ)) intCode_left_inv

/-- The digits of an integer: its sign and the digits of its absolute value. -/
def intDigits (z : ℤ) : Bool × Word := (decide (z < 0), z.natAbs.bits)

/-- The binary code of an integer with sign `p.1` and digits `p.2`. -/
def binIntWord (p : Bool × Word) : Word := p.1 :: binWord p.2

theorem binaryInt_eq_binIntWord (z : ℤ) : binaryInt z = binIntWord (intDigits z) := rfl

/-- The integer with sign `p.1` and digits `p.2`. -/
def intOfDigits (p : Bool × Word) : ℤ :=
  if p.1 then -(SAT.binaryValue p.2 : ℤ) else (SAT.binaryValue p.2 : ℤ)

/-- Valid digits of an integer: no leading zero, and no negative zero. -/
def intDigitsOk (p : Bool × Word) : Bool := natDigitsOk p.2 && (!p.1 || !p.2.isEmpty)

theorem intOfDigits_intDigits (z : ℤ) : intOfDigits (intDigits z) = z := by
  unfold intOfDigits intDigits
  by_cases h : z < 0
  · simp [h, binaryValue_bits, abs_of_neg h]
  · simp [h, binaryValue_bits, abs_of_nonneg (not_lt.mp h)]

theorem intDigitsOk_intDigits (z : ℤ) : intDigitsOk (intDigits z) = true := by
  unfold intDigitsOk intDigits
  by_cases h : z < 0
  · have hz : z.natAbs ≠ 0 := by omega
    have hb : z.natAbs.bits ≠ [] := by
      intro hb
      have := binaryValue_bits z.natAbs
      rw [hb] at this
      simp [SAT.binaryValue] at this
      omega
    simp [h, natDigitsOk_bits, hb]
  · simp [h, natDigitsOk_bits]

theorem intDigits_intOfDigits {p : Bool × Word} (h : intDigitsOk p = true) :
    intDigits (intOfDigits p) = p := by
  obtain ⟨s, d⟩ := p
  simp only [intDigitsOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  obtain ⟨hd, hs⟩ := h
  have hb := bits_binaryValue hd
  unfold intDigits intOfDigits
  cases s
  · simp [hb]
  · have hne : d ≠ [] := by simpa using hs
    have hv : SAT.binaryValue d ≠ 0 := by
      intro h0
      rw [h0] at hb
      exact hne (by simpa using hb.symm)
    have hv' : 0 < SAT.binaryValue d := Nat.pos_of_ne_zero hv
    simp [hb, hv']

/-! ### Readers -/

/-- Read a binary natural number at the start of a word: its digits and the rest. -/
def readBin (w : Word) : Word × Word :=
  ((w.drop (leadOnes w + 1)).take (leadOnes w), w.drop (leadOnes w + 1 + leadOnes w))

/-- Read a binary integer at the start of a word: its sign and digits, and the rest. -/
def readBinInt (w : Word) : (Bool × Word) × Word :=
  ((w.headD false, (readBin w.tail).1), (readBin w.tail).2)

@[simp] theorem readBin_binWord (d r : Word) : readBin (binWord d ++ r) = (d, r) := by
  have h1 : leadOnes (binWord d ++ r) = d.length := by simp [binWord, List.append_assoc]
  have h2 : (binWord d ++ r).drop (d.length + 1) = d ++ r := by simp [binWord, List.append_assoc]
  have h3 : (binWord d ++ r).drop (d.length + 1 + d.length) = r :=
    List.drop_left' (by simp [binWord, length_unary])
  simp only [readBin, h1, h2, h3, List.take_left' (l₂ := r) (rfl : d.length = d.length)]

@[simp] theorem readBin_binWord' (d : Word) : readBin (binWord d) = (d, []) := by
  simpa using readBin_binWord d []

@[simp] theorem readBinInt_binIntWord (p : Bool × Word) (r : Word) :
    readBinInt (binIntWord p ++ r) = (p, r) := by
  simp [readBinInt, binIntWord]

@[simp] theorem readBinInt_binIntWord' (p : Bool × Word) : readBinInt (binIntWord p) = (p, []) := by
  simpa using readBinInt_binIntWord p []

theorem readBin_binaryNat (n : ℕ) (r : Word) : readBin (binaryNat n ++ r) = (n.bits, r) :=
  readBin_binWord _ r

theorem readBinInt_binaryInt (z : ℤ) (r : Word) :
    readBinInt (binaryInt z ++ r) = (intDigits z, r) := by
  rw [binaryInt_eq_binIntWord]
  exact readBinInt_binIntWord _ r

theorem length_readBin_fst (w : Word) : (readBin w).1.length ≤ w.length := by
  simp only [readBin, List.length_take, List.length_drop]
  omega

theorem length_readBin_snd (w : Word) : (readBin w).2.length ≤ w.length := by
  simp [readBin]

theorem length_readBinInt_snd (w : Word) : (readBinInt w).2.length ≤ w.length := by
  have := length_readBin_snd w.tail
  simp only [readBinInt, List.length_tail] at this ⊢
  omega

theorem size_readBinInt_fst (w : Word) : size (readBinInt w).1 ≤ 2 * w.length + 2 := by
  have := length_readBin_fst w.tail
  simp only [readBinInt, size_prod, size_bool, size_word, List.length_tail] at this ⊢
  omega

/-- Decode a raw word as a binary natural number, returning its digits. -/
def decodeBinaryNat (w : Word) : Option Word :=
  if natDigitsOk (readBin w).1 = true ∧ binWord (readBin w).1 = w then some (readBin w).1 else none

/-- Decode a raw word as a binary integer, returning its sign and digits. -/
def decodeBinaryInt (w : Word) : Option (Bool × Word) :=
  if intDigitsOk (readBinInt w).1 = true ∧ binIntWord (readBinInt w).1 = w then
    some (readBinInt w).1 else none

theorem decodeBinaryNat_binaryNat (n : ℕ) : decodeBinaryNat (binaryNat n) = some n.bits := by
  simp [decodeBinaryNat, natDigitsOk_bits, binaryNat_eq_binWord]

theorem decodeBinaryNat_sound {w d : Word} (h : decodeBinaryNat w = some d) :
    ∃ n : ℕ, n.bits = d ∧ binaryNat n = w := by
  unfold decodeBinaryNat at h
  split_ifs at h with h'
  cases h
  exact ⟨SAT.binaryValue (readBin w).1, bits_binaryValue h'.1, by
    rw [binaryNat_eq_binWord, bits_binaryValue h'.1, h'.2]⟩

theorem decodeBinaryInt_binaryInt (z : ℤ) : decodeBinaryInt (binaryInt z) = some (intDigits z) := by
  simp [decodeBinaryInt, intDigitsOk_intDigits, binaryInt_eq_binIntWord]

theorem decodeBinaryInt_sound {w : Word} {p : Bool × Word} (h : decodeBinaryInt w = some p) :
    ∃ z : ℤ, intDigits z = p ∧ binaryInt z = w := by
  unfold decodeBinaryInt at h
  split_ifs at h with h'
  cases h
  exact ⟨intOfDigits (readBinInt w).1, intDigits_intOfDigits h'.1, by
    rw [binaryInt_eq_binIntWord, intDigits_intOfDigits h'.1, h'.2]⟩

/-! ### Polynomial time -/

section PTLemmas

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.binWord {d : α → Word} (hd : PT d) :
    PT (fun a => binWord (d a)) := by
  unfold binWord
  fun_prop

@[fun_prop] protected theorem PT.natDigitsOk {d : α → Word} (hd : PT d) :
    PT (fun a => natDigitsOk (d a)) := by
  unfold natDigitsOk
  fun_prop

/-- `Nat.bits` (on unary inputs). -/
@[fun_prop] protected theorem PT.bits {n : α → ℕ} (hn : PT n) : PT (fun a => (n a).bits) :=
  (PT.natBits hn).of_eq fun a => natBits_eq_bits (n a)

/-- `binaryNat` (on unary inputs). -/
@[fun_prop] protected theorem PT.binaryNat {n : α → ℕ} (hn : PT n) :
    PT (fun a => binaryNat (n a)) := by
  simp only [binaryNat_eq_binWord]
  fun_prop

/-- The sign and absolute value of an integer. -/
@[fun_prop] protected theorem PT.intSignAbs {z : α → ℤ} (hz : PT z) :
    PT (fun a => (decide (z a < 0), (z a).natAbs)) :=
  (PT.ofInj_to (fun z : ℤ => (decide (z < 0), z.natAbs))
    (fun p => if p.1 then -(p.2 : ℤ) else (p.2 : ℤ)) intCode_left_inv).comp hz

@[fun_prop] protected theorem PT.intNeg {z : α → ℤ} (hz : PT z) : PT (fun a => decide (z a < 0)) :=
  PT.fst (PT.intSignAbs hz)

@[fun_prop] protected theorem PT.natAbs {z : α → ℤ} (hz : PT z) : PT (fun a => (z a).natAbs) :=
  PT.snd (PT.intSignAbs hz)

/-- Into `ℤ`: it suffices to compute the sign and the absolute value. -/
theorem PT.int_of_signAbs {z : α → ℤ} (h : PT (fun a => (decide (z a < 0), (z a).natAbs))) :
    PT z :=
  PT.ofInj_mk (fun z : ℤ => (decide (z < 0), z.natAbs))
    (fun p => if p.1 then -(p.2 : ℤ) else (p.2 : ℤ)) intCode_left_inv h

/-- The cast `ℕ → ℤ`. -/
@[fun_prop] protected theorem PT.intOfNat {n : α → ℕ} (hn : PT n) : PT (fun a => ((n a : ℕ) : ℤ)) :=
  PT.int_of_signAbs ((PT.pair (PT.const false) hn).of_eq fun a => by simp)

@[fun_prop] protected theorem PT.intDigits {z : α → ℤ} (hz : PT z) :
    PT (fun a => intDigits (z a)) := by
  unfold intDigits
  fun_prop

@[fun_prop] protected theorem PT.binIntWord {p : α → Bool × Word} (hp : PT p) :
    PT (fun a => binIntWord (p a)) := by
  unfold binIntWord
  fun_prop

/-- `binaryInt` (on unary inputs). -/
@[fun_prop] protected theorem PT.binaryInt {z : α → ℤ} (hz : PT z) :
    PT (fun a => binaryInt (z a)) := by
  simp only [binaryInt_eq_binIntWord]
  fun_prop

@[fun_prop] protected theorem PT.intDigitsOk {p : α → Bool × Word} (hp : PT p) :
    PT (fun a => intDigitsOk (p a)) := by
  unfold intDigitsOk
  fun_prop

@[fun_prop] protected theorem PT.readBin {w : α → Word} (hw : PT w) :
    PT (fun a => readBin (w a)) := by
  unfold readBin
  fun_prop

@[fun_prop] protected theorem PT.readBinInt {w : α → Word} (hw : PT w) :
    PT (fun a => readBinInt (w a)) := by
  unfold readBinInt
  fun_prop

@[fun_prop] protected theorem PT.decodeBinaryNat {w : α → Word} (hw : PT w) :
    PT (fun a => decodeBinaryNat (w a)) := by
  unfold decodeBinaryNat
  fun_prop

@[fun_prop] protected theorem PT.decodeBinaryInt {w : α → Word} (hw : PT w) :
    PT (fun a => decodeBinaryInt (w a)) := by
  unfold decodeBinaryInt
  fun_prop

end PTLemmas

/-! ### Clamped values -/

/-- One step of the clamped evaluation (most significant digit first). -/
def clampStep (B acc : ℕ) (b : Bool) : ℕ := min (2 * acc + b.toNat) (B + 1)

theorem foldr_clampStep (B : ℕ) (d : Word) :
    d.foldr (fun b acc => clampStep B acc b) 0 = min (SAT.binaryValue d) (B + 1) := by
  induction d with
  | nil => simp [SAT.binaryValue]
  | cons b d ih =>
    rw [List.foldr_cons, ih]
    simp only [clampStep, SAT.binaryValue]
    have := Bool.toNat_le b
    generalize SAT.binaryValue d = v
    generalize b.toNat = t at this ⊢
    simp only [Nat.min_def]
    split_ifs <;> omega

theorem foldl_reverse_clampStep (B : ℕ) (d : Word) :
    d.reverse.foldl (clampStep B) 0 = min (SAT.binaryValue d) (B + 1) := by
  rw [List.foldl_reverse]
  exact foldr_clampStep B d

/-- **The value of a binary numeral, clamped by a unary bound, is polynomial-time.** -/
@[fun_prop] protected theorem PT.binaryValue_min {α : Type} [Code α] {d : α → Word} {B : α → ℕ}
    (hd : PT d) (hB : PT B) : PT (fun a => min (SAT.binaryValue (d a)) (B a)) := by
  obtain ⟨c, k, hk⟩ := hB.nat_le
  have h := PT.foldl_of_size_le (f := fun a acc b => clampStep (B a) acc b) (init := fun _ => 0)
    (l := fun a => (d a).reverse) (by unfold clampStep; fun_prop) (PT.const 0) (by fun_prop)
    (fun N => powerBound c k N + 2) ((PolynomialBound.power c k).add (PolynomialBound.constant 2))
    (fun a s b _ => by
      have := hk a
      have : clampStep (B a) s b ≤ B a + 1 := Nat.min_le_right _ _
      rw [size_nat]
      omega)
  refine (PT.min h hB).of_eq fun a => ?_
  show min ((d a).reverse.foldl (clampStep (B a)) 0) (B a) = _
  rw [foldl_reverse_clampStep]
  omega

/-! ### Scanning `encodeList` codes -/

section ScanList

variable {β : Type}

/-- One step of the scan of an `encodeList` code, with an element reader `rd`. -/
def listStep (rd : Word → β × Word) (s : Word × List β) : Word × List β :=
  if s.1.head? = some true then ((rd s.1.tail).2, (rd s.1.tail).1 :: s.2) else s

/-- Read an `encodeList` code with the element reader `rd`: the elements and the rest after the
terminating `0` (correct on codes, `scanList_encodeList`). -/
def scanList (rd : Word → β × Word) (w : Word) : List β × Word :=
  (((listStep rd)^[w.length] (w, [])).2.reverse, ((listStep rd)^[w.length] (w, [])).1.tail)

theorem encodeList_eq_flatMap (e : β → Word) (l : List β) :
    encodeList e l = l.flatMap (fun b => true :: e b) ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [encodeList, ih]

theorem scanList_encodeList {rd : Word → β × Word} {e : β → Word}
    (hrd : ∀ b r, rd (e b ++ r) = (b, r)) (l : List β) (r : Word) :
    scanList rd (encodeList e l ++ r) = (l, r) := by
  have key : ∀ (l : List β) (acc : List β), (listStep rd)^[l.length]
      (l.flatMap (fun b => true :: e b) ++ false :: r, acc) = (false :: r, l.reverse ++ acc) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b l ih =>
      intro acc
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.flatMap_cons, List.cons_append, List.append_assoc]
      have h1 : listStep rd (true :: (e b ++ (l.flatMap (fun b => true :: e b) ++ false :: r)),
          acc) = (l.flatMap (fun b => true :: e b) ++ false :: r, b :: acc) := by
        simp [listStep, hrd]
      rw [h1, ih]
      simp
  have hlen : l.length ≤ (l.flatMap (fun b => true :: e b)).length :=
    length_le_length_flatMap _ _ fun b _ => by simp
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hlen
  have hw : encodeList e l ++ r = l.flatMap (fun b => true :: e b) ++ false :: r := by
    simp [encodeList_eq_flatMap]
  have hfix : listStep rd (false :: r, l.reverse) = (false :: r, l.reverse) := by
    simp [listStep]
  have hit : (listStep rd)^[(encodeList e l ++ r).length] (encodeList e l ++ r, []) =
      (false :: r, l.reverse) := by
    rw [hw, List.length_append, List.length_cons, hn,
      show l.length + n + (r.length + 1) = (n + r.length + 1) + l.length by omega,
      Function.iterate_add_apply, key l [], List.append_nil, iterate_fixed _ _ hfix]
  unfold scanList
  rw [hit]
  simp

/-- The size invariant of the scan. -/
theorem listStep_inv {rd : Word → β × Word} [Code β] {C : ℕ}
    (hrd : ∀ x, (rd x).2.length ≤ x.length ∧ size (rd x).1 ≤ C * (x.length + 1))
    (n i : ℕ) (s : Word × List β) (h : s.1.length ≤ n ∧ size s.2 ≤ i * (C * (n + 1) + 1) + 1) :
    (listStep rd s).1.length ≤ n ∧
      size (listStep rd s).2 ≤ (i + 1) * (C * (n + 1) + 1) + 1 := by
  obtain ⟨r, acc⟩ := s
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  obtain ⟨h3, h4⟩ := hrd r.tail
  have h5 : C * (r.tail.length + 1) ≤ C * (n + 1) :=
    Nat.mul_le_mul_left _ (by simp only [List.length_tail]; omega)
  have h6 : r.tail.length ≤ r.length := by simp
  rw [Nat.succ_mul]
  generalize i * (C * (n + 1) + 1) = M at h2 ⊢
  generalize C * (n + 1) = K at h5 ⊢
  unfold listStep
  split_ifs
  · simp only [size_cons]
    constructor <;> omega
  · simp only
    constructor <;> omega

/-- **Scanning an `encodeList` code is polynomial-time** for a polynomial-time element reader that
does not lengthen the word and returns elements of linear size. -/
protected theorem PT.scanList [Code β] {rd : Word → β × Word} (hpt : PT rd) (C : ℕ)
    (hrd : ∀ x, (rd x).2.length ≤ x.length ∧ size (rd x).1 ≤ C * (x.length + 1)) :
    PT (scanList rd) := by
  have hstep : PT (listStep rd) := by
    unfold listStep
    fun_prop
  have h := PT.iterate_const (step := listStep rd) (init := fun w : Word => (w, ([] : List β)))
    (n := fun w : Word => w.length) hstep (by fun_prop) (by fun_prop)
    (fun N => 2 * N + 2 + N * (C * (N + 1) + 1))
    ((((PolynomialBound.constant 2).mul PolynomialBound.identity).add
      (PolynomialBound.constant 2)).add (PolynomialBound.identity.mul
        (((PolynomialBound.constant C).mul (PolynomialBound.identity.add
          (PolynomialBound.constant 1))).add (PolynomialBound.constant 1)))) ?_
  · exact (PT.pair (PT.reverse (PT.snd h)) (PT.tail (PT.fst h))).of_eq fun _ => rfl
  · intro w i hi
    have key := iterate_invariant (listStep rd) (fun i s => s.1.length ≤ w.length ∧
      size s.2 ≤ i * (C * (w.length + 1) + 1) + 1) (w, []) (by simp)
      (fun i s h => listStep_inv hrd w.length i s h) i
    obtain ⟨h1, h2⟩ := key
    generalize (listStep rd)^[i] (w, []) = s at h1 h2
    obtain ⟨r, acc⟩ := s
    simp only at h1 h2
    have hw := size_word w
    have hc : C * (w.length + 1) ≤ C * (2 * w.length + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    have hm : i * (C * (w.length + 1) + 1) ≤ (2 * w.length + 1) * (C * (2 * w.length + 1 + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [size_prod, size_word]
    omega

end ScanList

end ArtGallery

end
