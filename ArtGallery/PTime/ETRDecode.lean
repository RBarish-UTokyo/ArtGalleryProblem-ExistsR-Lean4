module

public import ArtGallery.PTime.TreeRec

/-!
# Decoding raw ETR formulas

`ETR.decodeFormula : Word → Option ETR.Formula` inverts `ETR.Formula.encode`:

* `ETR.decodeFormula_encode`: `decodeFormula φ.encode = some φ` (round trip);
* `ETR.encode_of_decodeFormula`: `decodeFormula w = some φ → φ.encode = w` (soundness);
* `ETR.Formula.encode_injective`;
* `PT.decodeFormula`: the decoder is polynomial-time (on raw words).

The decoder splits the word into tokens (`ETR.tokenize`, a left-to-right scan that keeps the
numbers `a`, `b` of pending term and formula arguments: the pending arguments are always `a`
terms followed by `b` formulas), parses the tokens (`ETR.Formula.ofToks`), and accepts iff the
result re-encodes to the input.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETR

/-- The value of the first three bits of a word (missing bits read as `0`). -/
def tag3 (r : Word) : ℕ :=
  4 * (r.getD 0 false).toNat + 2 * (r.getD 1 false).toNat + (r.getD 2 false).toNat

theorem tag3_le (r : Word) : tag3 r ≤ 7 := by
  have h0 := Bool.toNat_le (r.getD 0 false)
  have h1 := Bool.toNat_le (r.getD 1 false)
  have h2 := Bool.toNat_le (r.getD 2 false)
  unfold tag3
  omega

/-- One step of the tokenizer on the state `(rest, a, b, reversed tokens)`, where `a` and `b`
are the numbers of pending term and formula arguments. -/
def lexStep (s : Word × ℕ × ℕ × List ℕ) : Word × ℕ × ℕ × List ℕ :=
  if 0 < s.2.1 then
    if tag3 s.1 = 0 then
      ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1), s.2.1 - 1, s.2.2.1,
        (leadOnes (s.1.drop 3) + 11) :: s.2.2.2)
    else if tag3 s.1 ≤ 2 then (s.1.drop 3, s.2.1 - 1, s.2.2.1, (tag3 s.1 + 5) :: s.2.2.2)
    else if tag3 s.1 ≤ 5 then (s.1.drop 3, s.2.1 + 1, s.2.2.1, (tag3 s.1 + 5) :: s.2.2.2)
    else ([], 0, 0, s.2.2.2)
  else if 0 < s.2.2.1 then
    if tag3 s.1 ≤ 2 then (s.1.drop 3, 2, s.2.2.1 - 1, tag3 s.1 :: s.2.2.2)
    else if tag3 s.1 = 3 then (s.1.drop 3, 0, s.2.2.1, 3 :: s.2.2.2)
    else if tag3 s.1 ≤ 5 then (s.1.drop 3, 0, s.2.2.1 + 1, tag3 s.1 :: s.2.2.2)
    else ([], 0, 0, s.2.2.2)
  else s

/-- The tokens of a word (correct on codes of formulas). -/
def tokenize (w : Word) : List ℕ := (lexStep^[w.length] (w, 0, 1, [])).2.2.2.reverse

/-- Decode a raw word as a formula: tokenize, parse, and check by re-encoding. -/
def decodeFormula (w : Word) : Option Formula :=
  if (Formula.ofToks (tokenize w)).encode = w then some (Formula.ofToks (tokenize w)) else none

/-! ### Correctness on codes -/

theorem lexStep_fixed (r : Word) (acc : List ℕ) : lexStep (r, 0, 0, acc) = (r, 0, 0, acc) := by
  simp [lexStep]

theorem Term.lex (t : Term) (r : Word) (a b : ℕ) (acc : List ℕ) :
    lexStep^[t.toks.length] (t.encode ++ r, a + 1, b, acc) = (r, a, b, t.toks.reverse ++ acc) := by
  induction t generalizing r a acc with
  | var i => simp [Term.toks, Term.encode, lexStep, tag3]
  | zero => simp [Term.toks, Term.encode, lexStep, tag3]
  | one => simp [Term.toks, Term.encode, lexStep, tag3]
  | add s t ihs iht =>
    have h1 : lexStep (false :: true :: true :: (s.encode ++ (t.encode ++ r)), a + 1, b, acc) =
        (s.encode ++ (t.encode ++ r), (a + 1) + 1, b, 8 :: acc) := by simp [lexStep, tag3]
    simp only [Term.toks, Term.encode, List.length_cons, List.length_append, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, ihs, iht]
    simp
  | sub s t ihs iht =>
    have h1 : lexStep (true :: false :: false :: (s.encode ++ (t.encode ++ r)), a + 1, b, acc) =
        (s.encode ++ (t.encode ++ r), (a + 1) + 1, b, 9 :: acc) := by simp [lexStep, tag3]
    simp only [Term.toks, Term.encode, List.length_cons, List.length_append, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, ihs, iht]
    simp
  | mul s t ihs iht =>
    have h1 : lexStep (true :: false :: true :: (s.encode ++ (t.encode ++ r)), a + 1, b, acc) =
        (s.encode ++ (t.encode ++ r), (a + 1) + 1, b, 10 :: acc) := by simp [lexStep, tag3]
    simp only [Term.toks, Term.encode, List.length_cons, List.length_append, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, ihs, iht]
    simp

theorem Formula.lex (φ : Formula) (r : Word) (b : ℕ) (acc : List ℕ) :
    lexStep^[φ.toks.length] (φ.encode ++ r, 0, b + 1, acc) = (r, 0, b, φ.toks.reverse ++ acc) := by
  induction φ generalizing r b acc with
  | eq s t =>
    have h1 : lexStep (false :: false :: false :: (s.encode ++ (t.encode ++ r)), 0, b + 1, acc) =
        (s.encode ++ (t.encode ++ r), 0 + 1 + 1, b, 0 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.length_append,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, Term.lex s _ (0 + 1), Term.lex t _ 0]
    simp
  | lt s t =>
    have h1 : lexStep (false :: false :: true :: (s.encode ++ (t.encode ++ r)), 0, b + 1, acc) =
        (s.encode ++ (t.encode ++ r), 0 + 1 + 1, b, 1 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.length_append,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, Term.lex s _ (0 + 1), Term.lex t _ 0]
    simp
  | le s t =>
    have h1 : lexStep (false :: true :: false :: (s.encode ++ (t.encode ++ r)), 0, b + 1, acc) =
        (s.encode ++ (t.encode ++ r), 0 + 1 + 1, b, 2 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.length_append,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [Nat.add_comm s.toks.length t.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, Term.lex s _ (0 + 1), Term.lex t _ 0]
    simp
  | not φ ih =>
    have h1 : lexStep (false :: true :: true :: (φ.encode ++ r), 0, b + 1, acc) =
        (φ.encode ++ r, 0, b + 1, 3 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.cons_append, List.nil_append]
    rw [Function.iterate_succ_apply, h1, ih]
    simp
  | and φ ψ ihφ ihψ =>
    have h1 : lexStep (true :: false :: false :: (φ.encode ++ (ψ.encode ++ r)), 0, b + 1, acc) =
        (φ.encode ++ (ψ.encode ++ r), 0, b + 1 + 1, 4 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.length_append,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [Nat.add_comm φ.toks.length ψ.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, ihφ, ihψ]
    simp
  | or φ ψ ihφ ihψ =>
    have h1 : lexStep (true :: false :: true :: (φ.encode ++ (ψ.encode ++ r)), 0, b + 1, acc) =
        (φ.encode ++ (ψ.encode ++ r), 0, b + 1 + 1, 5 :: acc) := by simp [lexStep, tag3]
    simp only [Formula.toks, Formula.encode, List.length_cons, List.length_append,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [Nat.add_comm φ.toks.length ψ.toks.length, Function.iterate_succ_apply,
      Function.iterate_add_apply, h1, ihφ, ihψ]
    simp

theorem tokenize_encode (φ : Formula) : tokenize φ.encode = φ.toks := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Formula.length_toks_le φ)
  have h : lexStep^[φ.toks.length] (φ.encode, 0, 1, []) = ([], 0, 0, φ.toks.reverse) := by
    simpa using Formula.lex φ [] 0 []
  unfold tokenize
  rw [he, Nat.add_comm φ.toks.length e, Function.iterate_add_apply, h,
    iterate_fixed _ _ (lexStep_fixed _ _)]
  simp

/-- **Round trip.** -/
theorem decodeFormula_encode (φ : Formula) : decodeFormula φ.encode = some φ := by
  unfold decodeFormula
  rw [tokenize_encode, Formula.ofToks_toks]
  simp

/-- **Soundness.** -/
theorem encode_of_decodeFormula {w : Word} {φ : Formula} (h : decodeFormula w = some φ) :
    φ.encode = w := by
  unfold decodeFormula at h
  split_ifs at h with h'
  cases h
  exact h'

theorem Formula.encode_injective : Function.Injective Formula.encode := fun φ ψ h => by
  have h1 := decodeFormula_encode φ
  rw [h, decodeFormula_encode ψ] at h1
  exact (Option.some.inj h1).symm

/-! ### Polynomial time -/

/-- The tokenizer preserves the size invariant. -/
theorem lexStep_inv (n i : ℕ) (s : Word × ℕ × ℕ × List ℕ)
    (h : s.1.length ≤ n ∧ s.2.1 ≤ i + 2 ∧ s.2.2.1 ≤ i + 1 ∧ size s.2.2.2 ≤ i * (n + 20) + 1) :
    (lexStep s).1.length ≤ n ∧ (lexStep s).2.1 ≤ (i + 1) + 2 ∧ (lexStep s).2.2.1 ≤ (i + 1) + 1 ∧
      size (lexStep s).2.2.2 ≤ (i + 1) * (n + 20) + 1 := by
  obtain ⟨r, a, b, acc⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  have ht := tag3_le r
  have hl : leadOnes (r.drop 3) ≤ r.length - 3 := by simpa using leadOnes_le (r.drop 3)
  have hm : (i + 1) * (n + 20) = i * (n + 20) + (n + 20) := Nat.succ_mul _ _
  rw [hm]
  generalize i * (n + 20) = M at h4 ⊢
  unfold lexStep
  split_ifs <;> simp only [size_cons, size_nat, List.length_drop, List.length_nil] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end ETR

open ETR

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.lexStep : PT lexStep := by
  unfold lexStep tag3
  fun_prop

/-- The tokenizer is polynomial-time. -/
@[fun_prop] protected theorem PT.tokenize : PT tokenize := by
  have h := PT.iterate_const (step := lexStep) (init := fun w : Word => (w, 0, 1, ([] : List ℕ)))
    (n := fun w : Word => w.length) PT.lexStep (by fun_prop) (by fun_prop)
    (fun N => 4 * N + 7 + N * (N + 20))
    (((PolynomialBound.constant 4).mul PolynomialBound.identity).add
      (PolynomialBound.constant 7) |>.add (PolynomialBound.identity.mul
        (PolynomialBound.identity.add (PolynomialBound.constant 20)))) ?_
  · exact (PT.reverse (PT.snd (PT.snd (PT.snd h)))).of_eq fun _ => rfl
  · intro w i hi
    have key := iterate_invariant lexStep (fun i s => s.1.length ≤ w.length ∧ s.2.1 ≤ i + 2 ∧
      s.2.2.1 ≤ i + 1 ∧ size s.2.2.2 ≤ i * (w.length + 20) + 1) (w, 0, 1, [])
      (by simp) (fun i s h => lexStep_inv w.length i s h) i
    obtain ⟨h1, h2, h3, h4⟩ := key
    generalize lexStep^[i] (w, 0, 1, []) = s at h1 h2 h3 h4
    obtain ⟨r, a, b, acc⟩ := s
    simp only at h1 h2 h3 h4
    have hw := size_word w
    have hm : i * (w.length + 20) ≤ (2 * w.length + 1) * (2 * w.length + 1 + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [size_prod, size_nat, size_word]
    omega

/-- **The formula decoder is polynomial-time.** -/
@[fun_prop] protected theorem PT.decodeFormula {w : α → Word} (hw : PT w) :
    PT (fun a => decodeFormula (w a)) := by
  unfold decodeFormula
  fun_prop

end ArtGallery

end
