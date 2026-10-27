module

public import PT.Word
public import Complexity.SAT
public import Mathlib.Logic.Equiv.Defs

/-!
# Prefix-free binary codes

`Code α` equips `α` with a prefix-free binary code whose leading item can be measured (and
hence split off) in polynomial time.  Instances: `Unit`, `Bool`, `Nat` (unary), products,
`Option`, sums, lists, and `SAT.Literal`; the codes of clauses and CNF formulas coincide with
`SAT.encodeClause` and `SAT.encode`.
-/

@[expose] public section

namespace Complexity.PT

open Complexity.Reg

/-- A prefix-free binary code for `α` whose leading item can be split off in polynomial
time. -/
class Code (α : Type) where
  /-- The code of a value. -/
  enc : α → Word
  /-- The code is prefix-free (in particular injective). -/
  enc_inj : ∀ {a b : α} {r s : Word}, enc a ++ r = enc b ++ s → a = b ∧ r = s
  /-- The length of the leading code of a word can be computed (in unary) in polynomial
  time. -/
  len_polyTime : ∃ F : Word → Word, PolyTime F ∧
    ∀ (a : α) (r : Word), F (enc a ++ r) = List.replicate (enc a).length true

/-- The size of a value: the length of its code. -/
def size {α : Type} [Code α] (a : α) : Nat := (Code.enc a).length

namespace Code

variable {α β : Type}

theorem enc_injective [Code α] : Function.Injective (enc : α → Word) := by
  intro a b h
  exact (enc_inj (r := []) (s := []) (by rw [h])).1

@[simp] theorem enc_eq_iff [Code α] {a b : α} : enc a = enc b ↔ a = b :=
  enc_injective.eq_iff

/-- The leading code of a word can be extracted in polynomial time. -/
theorem exists_take (α : Type) [Code α] :
    ∃ T : Word → Word, PolyTime T ∧ ∀ (a : α) (r : Word), T (enc a ++ r) = enc a := by
  obtain ⟨F, hF, hF'⟩ := len_polyTime (α := α)
  refine ⟨_, polyTime_take hF polyTime_id, fun a r => ?_⟩
  simp only [hF', List.length_replicate, List.take_left']

/-- The leading code of a word can be removed in polynomial time. -/
theorem exists_drop (α : Type) [Code α] :
    ∃ T : Word → Word, PolyTime T ∧ ∀ (a : α) (r : Word), T (enc a ++ r) = r := by
  obtain ⟨F, hF, hF'⟩ := len_polyTime (α := α)
  refine ⟨_, polyTime_drop hF polyTime_id, fun a r => ?_⟩
  simp only [hF', List.length_replicate, List.drop_left']

/-- Transport a code along an injection with an explicit left inverse. -/
@[reducible] def ofInj [Code β] (f : α → β) (g : β → α) (h : ∀ a, g (f a) = a) : Code α where
  enc a := enc (f a)
  enc_inj {a b r s} e := by
    obtain ⟨h1, h2⟩ := enc_inj e
    exact ⟨by rw [← h a, ← h b, h1], h2⟩
  len_polyTime := by
    obtain ⟨F, hF, hF'⟩ := len_polyTime (α := β)
    exact ⟨F, hF, fun a r => hF' (f a) r⟩

/-- Transport a code along an equivalence. -/
@[reducible] def ofEquiv [Code β] (e : α ≃ β) : Code α :=
  ofInj e e.symm e.symm_apply_apply

end Code

open Code

/-! ### `Unit`, `Bool`, `Nat` -/

instance instCodeUnit : Code Unit where
  enc _ := []
  enc_inj h := ⟨rfl, by simpa using h⟩
  len_polyTime := ⟨fun _ => [], polyTime_const [], fun _ _ => rfl⟩

instance instCodeBool : Code Bool where
  enc b := [b]
  enc_inj h := by simpa using h
  len_polyTime := ⟨fun _ => [true], polyTime_const [true], fun _ _ => rfl⟩

theorem writeNat_eq (n : Nat) : SAT.writeNat n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [SAT.writeNat, ih, List.replicate_succ]

@[simp] theorem length_writeNat (n : Nat) : (SAT.writeNat n).length = n + 1 := by
  simp [writeNat_eq]

theorem writeNat_append (n : Nat) (r : Word) :
    SAT.writeNat n ++ r = List.replicate n true ++ false :: r := by
  simp [writeNat_eq]

theorem writeNat_inj {m n : Nat} {r s : Word} (h : SAT.writeNat m ++ r = SAT.writeNat n ++ s) :
    m = n ∧ r = s := by
  have h' := congrArg SAT.readNat h
  simpa using h'

/-- Natural numbers are coded in unary: `n` ones followed by a zero. -/
instance instCodeNat : Code Nat where
  enc := SAT.writeNat
  enc_inj := writeNat_inj
  len_polyTime := ⟨fun x => true :: leadingOnes x, polyTime_cons true polyTime_leadingOnes,
    fun n r => by simp [writeNat_append, List.replicate_succ]⟩

@[simp] theorem enc_unit (u : Unit) : enc u = [] := rfl
@[simp] theorem enc_bool (b : Bool) : enc b = [b] := rfl
theorem enc_nat (n : Nat) : enc n = SAT.writeNat n := rfl
@[simp] theorem enc_zero : enc (0 : Nat) = [false] := rfl
@[simp] theorem enc_succ (n : Nat) : enc (n + 1) = true :: enc n := rfl
theorem enc_nat_eq (n : Nat) : enc n = List.replicate n true ++ [false] := writeNat_eq n

@[simp] theorem size_unit (u : Unit) : size u = 0 := rfl
@[simp] theorem size_bool (b : Bool) : size b = 1 := rfl
@[simp] theorem size_nat (n : Nat) : size n = n + 1 := length_writeNat n

/-! ### Products, options, sums -/

section Composite

variable {α β : Type} [Code α] [Code β]

instance instCodeProd : Code (α × β) where
  enc p := enc p.1 ++ enc p.2
  enc_inj {p q r s} h := by
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨h1, h'⟩ := enc_inj h
    obtain ⟨h2, h3⟩ := enc_inj h'
    exact ⟨Prod.ext h1 h2, h3⟩
  len_polyTime := by
    obtain ⟨F, hF, hF'⟩ := len_polyTime (α := α)
    obtain ⟨G, hG, hG'⟩ := len_polyTime (α := β)
    refine ⟨fun x => F x ++ G (x.drop (F x).length),
      polyTime_append hF (polyTime_comp hG (polyTime_drop hF polyTime_id)), ?_⟩
    rintro ⟨a, b⟩ r
    simp only [List.append_assoc, hF', List.length_replicate, List.drop_left', hG',
      List.replicate_append_replicate, List.length_append]

theorem enc_prod (p : α × β) : enc p = enc p.1 ++ enc p.2 := rfl
@[simp] theorem enc_pair (a : α) (b : β) : enc (a, b) = enc a ++ enc b := rfl

@[simp] theorem size_prod (p : α × β) : size p = size p.1 + size p.2 := by
  simp [size, enc_prod]

theorem size_pair (a : α) (b : β) : size (a, b) = size a + size b := size_prod (a, b)

instance instCodeOption : Code (Option α) where
  enc
    | none => [false]
    | some a => true :: enc a
  enc_inj {a b r s} h := by
    cases a <;> cases b <;> simp at h
    · exact ⟨rfl, h⟩
    · obtain ⟨h1, h2⟩ := enc_inj h
      exact ⟨by rw [h1], h2⟩
  len_polyTime := by
    obtain ⟨F, hF, hF'⟩ := len_polyTime (α := α)
    refine ⟨fun x => if x.take 1 = [true] then true :: F x.tail else [true],
      polyTime_ite (polyTime_take_one polyTime_id)
        (polyTime_cons true (polyTime_comp hF (polyTime_tail polyTime_id)))
        (polyTime_const [true]), ?_⟩
    rintro (_ | a) r <;> simp [hF', List.replicate_succ]

@[simp] theorem enc_none : enc (none : Option α) = [false] := rfl
@[simp] theorem enc_some (a : α) : enc (some a) = true :: enc a := rfl
@[simp] theorem size_none : size (none : Option α) = 1 := rfl
@[simp] theorem size_some (a : α) : size (some a) = size a + 1 := by simp [size]

instance instCodeSum : Code (α ⊕ β) where
  enc
    | .inl a => false :: enc a
    | .inr b => true :: enc b
  enc_inj {a b r s} h := by
    cases a <;> cases b <;> simp at h
    · obtain ⟨h1, h2⟩ := enc_inj h
      exact ⟨by rw [h1], h2⟩
    · obtain ⟨h1, h2⟩ := enc_inj h
      exact ⟨by rw [h1], h2⟩
  len_polyTime := by
    obtain ⟨F, hF, hF'⟩ := len_polyTime (α := α)
    obtain ⟨G, hG, hG'⟩ := len_polyTime (α := β)
    refine ⟨fun x => if x.take 1 = [true] then true :: G x.tail else true :: F x.tail,
      polyTime_ite (polyTime_take_one polyTime_id)
        (polyTime_cons true (polyTime_comp hG (polyTime_tail polyTime_id)))
        (polyTime_cons true (polyTime_comp hF (polyTime_tail polyTime_id))), ?_⟩
    rintro (a | b) r <;> simp [hF', hG', List.replicate_succ]

@[simp] theorem enc_inl (a : α) : enc (Sum.inl a : α ⊕ β) = false :: enc a := rfl
@[simp] theorem enc_inr (b : β) : enc (Sum.inr b : α ⊕ β) = true :: enc b := rfl
@[simp] theorem size_inl (a : α) : size (Sum.inl a : α ⊕ β) = size a + 1 := by simp [size]
@[simp] theorem size_inr (b : β) : size (Sum.inr b : α ⊕ β) = size b + 1 := by simp [size]

end Composite

/-! ### Lists -/

section ListCode

variable {α : Type}

theorem writeValues_append (e : α → Word) (l₁ l₂ : List α) :
    SAT.writeValues e (l₁ ++ l₂) = SAT.writeValues e l₁ ++ SAT.writeValues e l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp [SAT.writeValues, ih]

@[simp] theorem writeValues_nil (e : α → Word) : SAT.writeValues e [] = [] := rfl

@[simp] theorem writeValues_cons (e : α → Word) (a : α) (l : List α) :
    SAT.writeValues e (a :: l) = e a ++ SAT.writeValues e l := rfl

theorem length_writeValues (e : α → Word) (l : List α) :
    (SAT.writeValues e l).length = (l.map fun a => (e a).length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem length_writeValues_take_add_drop (e : α → Word) (l : List α) (i : Nat) :
    (SAT.writeValues e (l.take i)).length + (SAT.writeValues e (l.drop i)).length =
      (SAT.writeValues e l).length := by
  rw [← List.length_append, ← writeValues_append, List.take_append_drop]

theorem writeValues_bits (w : Word) : SAT.writeValues (fun b : Bool => [b]) w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem writeList_append (e : α → Word) (l : List α) (r : Word) :
    SAT.writeList e l ++ r =
      List.replicate l.length true ++ false :: (SAT.writeValues e l ++ r) := by
  simp [SAT.writeList, writeNat_eq]

variable [Code α]

theorem writeValues_inj : ∀ {l l' : List α} {r s : Word}, l.length = l'.length →
    SAT.writeValues enc l ++ r = SAT.writeValues enc l' ++ s → l = l' ∧ r = s
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | a :: l, b :: l', r, s, hl, h => by
    simp only [writeValues_cons, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := enc_inj h
    obtain ⟨h3, h4⟩ := writeValues_inj (by simpa using hl) h2
    exact ⟨by rw [h1, h3], h4⟩

/-- One step of the scan measuring a list code: the state `(acc, w)` becomes
`(acc ++ 1^|c|, w')` where `w = c ++ w'` and `c` is the leading element code of `w`. -/
def listLenStep (L : Word → Word) (w : Word) : Word :=
  pairWords ((unpair w).1 ++ L (unpair w).2) ((unpair w).2.drop (L (unpair w).2).length)

theorem polyTime_listLenStep {L : Word → Word} (hL : PolyTime L) : PolyTime (listLenStep L) :=
  polyTime_pair (polyTime_append polyTime_pair_fst (polyTime_comp hL polyTime_pair_snd))
    (polyTime_drop (polyTime_comp hL polyTime_pair_snd) polyTime_pair_snd)

theorem listLenStep_iterate {L : Word → Word}
    (hL : ∀ (a : α) (r : Word), L (enc a ++ r) = List.replicate (enc a).length true)
    (i : Nat) (l : List α) (acc r : Word) (hi : i ≤ l.length) :
    (listLenStep L)^[i] (pairWords acc (SAT.writeValues enc l ++ r)) =
      pairWords (acc ++ List.replicate (SAT.writeValues enc (l.take i)).length true)
        (SAT.writeValues enc (l.drop i) ++ r) := by
  induction i generalizing l acc with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp at hi
    | cons a l =>
      have hstep : listLenStep L (pairWords acc (SAT.writeValues enc (a :: l) ++ r)) =
          pairWords (acc ++ List.replicate (enc a).length true) (SAT.writeValues enc l ++ r) := by
        simp only [listLenStep, unpair_pairWords, writeValues_cons, List.append_assoc, hL,
          List.length_replicate, List.drop_left']
      rw [Function.iterate_succ_apply, hstep, ih l _ (by simpa using hi)]
      simp only [List.take_succ_cons, List.drop_succ_cons, writeValues_cons, List.append_assoc,
        List.replicate_append_replicate, List.length_append]

/-- Lists are coded as `SAT.writeList`: the length in unary, then the element codes. -/
instance instCodeList : Code (List α) where
  enc l := SAT.writeList enc l
  enc_inj {l l' r s} h := by
    simp only [SAT.writeList, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := writeNat_inj h
    exact writeValues_inj h1 h2
  len_polyTime := by
    obtain ⟨L, hL, hL'⟩ := len_polyTime (α := α)
    obtain ⟨G, hG, hG'⟩ := polyTime_iterate_on
      (fun x => ∃ (l : List α) (r : Word), x = SAT.writeList enc l ++ r)
      (polyTime_listLenStep hL)
      (polyTime_pair (polyTime_cons true polyTime_leadingOnes) polyTime_afterOnes)
      polyTime_leadingOnes (fun n => 2 * n + 1)
      (((PolynomialBound.constant 2).mul PolynomialBound.identity).add
        (PolynomialBound.constant 1)) (by
        rintro x ⟨l, r, rfl⟩ i hi
        simp only [writeList_append, leadingOnes_ones, List.length_replicate,
          afterOnes_ones] at hi ⊢
        rw [listLenStep_iterate hL' i l _ r hi]
        have h := length_writeValues_take_add_drop enc l i
        simp only [pairWords_length, List.length_append, List.length_cons, List.length_replicate]
        omega)
    refine ⟨fun x => (unpair (G x)).1, polyTime_comp polyTime_pair_fst hG, fun l r => ?_⟩
    show (unpair (G (SAT.writeList enc l ++ r))).1 = _
    rw [hG' _ ⟨l, r, rfl⟩]
    simp only [writeList_append, leadingOnes_ones, List.length_replicate, afterOnes_ones]
    rw [listLenStep_iterate hL' l.length l _ r (Nat.le_refl _)]
    simp only [unpair_pairWords, List.take_length,
      List.replicate_append_replicate, ← List.replicate_succ, List.length_append,
      SAT.writeList, length_writeNat]

theorem enc_list (l : List α) : enc l = SAT.writeList enc l := rfl

theorem enc_list_eq (l : List α) :
    enc l = List.replicate l.length true ++ false :: SAT.writeValues enc l := by
  rw [enc_list, SAT.writeList, writeNat_append]

@[simp] theorem enc_nil : enc ([] : List α) = [false] := rfl

@[simp] theorem enc_cons (a : α) (l : List α) :
    enc (a :: l) = true :: (List.replicate l.length true ++ false ::
      (enc a ++ SAT.writeValues enc l)) := by
  simp [enc_list_eq, List.replicate_succ]

/-- The code of a word as a list of bits: its length in unary, then the word. -/
theorem enc_word (w : Word) : enc w = SAT.writeNat w.length ++ w := by
  rw [enc_list, SAT.writeList]
  exact congrArg _ (writeValues_bits w)

theorem size_list (l : List α) : size l = l.length + 1 + (l.map size).sum := by
  simp [size, enc_list, SAT.writeList, length_writeValues]
  rfl

@[simp] theorem size_nil : size ([] : List α) = 1 := rfl

@[simp] theorem size_cons (a : α) (l : List α) : size (a :: l) = size a + size l + 1 := by
  simp [size_list]
  omega

theorem size_append (l₁ l₂ : List α) : size (l₁ ++ l₂) + 1 = size l₁ + size l₂ := by
  simp [size_list]
  omega

@[simp] theorem size_reverse (l : List α) : size l.reverse = size l := by
  simp [size_list]

theorem size_word (w : Word) : size w = 2 * w.length + 1 := by
  simp [size, enc_word]
  omega

theorem length_lt_size (l : List α) : l.length < size l := by
  rw [size_list]
  omega

theorem size_pos_list (l : List α) : 0 < size l := Nat.lt_of_le_of_lt (Nat.zero_le _) (length_lt_size l)

theorem size_le_of_sublist {l₁ l₂ : List α} (h : l₁.Sublist l₂) : size l₁ ≤ size l₂ := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => rw [size_cons]; omega
  | cons_cons a _ ih => rw [size_cons, size_cons]; omega

theorem size_le_of_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) : size l₁ ≤ size l₂ :=
  size_le_of_sublist h.sublist

theorem size_take_le (l : List α) (i : Nat) : size (l.take i) ≤ size l :=
  size_le_of_sublist (List.take_sublist i l)

theorem size_drop_le (l : List α) (i : Nat) : size (l.drop i) ≤ size l :=
  size_le_of_sublist (List.drop_sublist i l)

theorem size_tail_le (l : List α) : size l.tail ≤ size l :=
  size_le_of_sublist (List.tail_sublist l)

theorem size_lt_of_mem {a : α} {l : List α} (h : a ∈ l) : size a < size l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [size_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem size_le_of_mem {a : α} {l : List α} (h : a ∈ l) : size a ≤ size l :=
  Nat.le_of_lt (size_lt_of_mem h)

end ListCode

/-! ### SAT literals, clauses, formulas -/

/-- A literal is coded as the pair `(positive, var)`; this is `SAT.encodeLiteral`. -/
instance instCodeLiteral : Code SAT.Literal :=
  Code.ofInj (fun l => (l.positive, l.var)) (fun p => ⟨p.2, p.1⟩) (fun _ => rfl)

@[simp] theorem enc_literal (l : SAT.Literal) : enc l = SAT.encodeLiteral l := rfl

theorem enc_literal_fun : (enc : SAT.Literal → Word) = SAT.encodeLiteral := rfl

@[simp] theorem enc_clause (c : SAT.Clause) : enc c = SAT.encodeClause c := rfl

theorem enc_clause_fun : (enc : SAT.Clause → Word) = SAT.encodeClause := rfl

/-- The code of a CNF formula is its `SAT.encode`. -/
@[simp] theorem enc_cnf (f : SAT.CNF) : enc f = SAT.encode f := rfl

@[simp] theorem size_literal (l : SAT.Literal) : size l = l.var + 2 := by
  simp [size, SAT.encodeLiteral]

end Complexity.PT
