module

public import ArtGallery.Spec
public import PT.All
public import ArtGallery.PTime.Scan

/-!
# Codes for the syntax of the existential theory of the reals

Terms and formulas are coded (for the `PT` framework) through their **Polish token lists**:
one natural number per node, in prefix order,

* formula tokens: `0` `=`, `1` `<`, `2` `≤`, `3` `¬`, `4` `∧`, `5` `∨`;
* term tokens: `6` `0`, `7` `1`, `8` `+`, `9` `−`, `10` `·`, `i + 11` the variable `x i`.

`ETR.Term.toks`, `ETR.Formula.toks` compute the token lists, and the tokens are evaluated from
right to left with a pair of stacks (terms, formulas) by `ETR.tokStep`.  With the constructors as
operations this evaluation inverts `toks` (`ETR.Term.ofToks_toks`, `ETR.Formula.ofToks_toks`);
with arbitrary operations it computes the catamorphisms `ETR.Term.cata`, `ETR.Formula.cata`
(`ETR.Term.foldr_toks`, `ETR.Formula.foldr_toks`).

The codes are `Code.ofInj toks ofToks _`.  Main facts:

* `PT` of the constructors (`PT.termVar`, …, `PT.formulaOr`) and of `toks`
  (`PT.termToks`, `PT.formulaToks`), all `@[fun_prop]`;
* `PT.termEncode`, `PT.formulaEncode`: the raw binary codes `Term.encode`, `Formula.encode`
  of `ArtGallery.Spec` are polynomial-time (they are `flatMap tokBits` of the token lists).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETR

/-! ### Stack operations -/

section Stack

variable {τ σ : Type}

/-- Replace the two top entries `x, y` of a stack by `f x y` (unchanged if too short). -/
def ap2 (f : τ → τ → τ) (l : List τ) : List τ :=
  match l with
  | x :: y :: r => f x y :: r
  | _ => l

/-- Replace the top entry `x` of a stack by `f x` (unchanged if empty). -/
def ap1 (f : σ → σ) (l : List σ) : List σ :=
  match l with
  | x :: r => f x :: r
  | [] => []

/-- Pop the two top entries `x, y` of the term stack and push `f x y` on the formula stack
(unchanged if the term stack is too short). -/
def atom2 (f : τ → τ → σ) (st : List τ × List σ) : List τ × List σ :=
  match st.1 with
  | x :: y :: r => (r, f x y :: st.2)
  | _ => st

@[simp] theorem ap2_cons_cons (f : τ → τ → τ) (x y : τ) (r : List τ) :
    ap2 f (x :: y :: r) = f x y :: r := rfl

@[simp] theorem ap1_cons (f : σ → σ) (x : σ) (r : List σ) : ap1 f (x :: r) = f x :: r := rfl

@[simp] theorem atom2_cons_cons (f : τ → τ → σ) (x y : τ) (r : List τ) (s : List σ) :
    atom2 f (x :: y :: r, s) = (r, f x y :: s) := rfl

/-- One step of the right-to-left evaluation of a Polish token list, on the pair of stacks
(term values, formula values). -/
def tokStep (fv : ℕ → τ) (fz fo : τ) (fadd fsub fmul : τ → τ → τ) (feq flt fle : τ → τ → σ)
    (fnot : σ → σ) (fAnd fOr : σ → σ → σ) (k : ℕ) (st : List τ × List σ) :
    List τ × List σ :=
  if k = 0 then atom2 feq st
  else if k = 1 then atom2 flt st
  else if k = 2 then atom2 fle st
  else if k = 3 then (st.1, ap1 fnot st.2)
  else if k = 4 then (st.1, ap2 fAnd st.2)
  else if k = 5 then (st.1, ap2 fOr st.2)
  else if k = 6 then (fz :: st.1, st.2)
  else if k = 7 then (fo :: st.1, st.2)
  else if k = 8 then (ap2 fadd st.1, st.2)
  else if k = 9 then (ap2 fsub st.1, st.2)
  else if k = 10 then (ap2 fmul st.1, st.2)
  else (fv (k - 11) :: st.1, st.2)

variable {fv : ℕ → τ} {fz fo : τ} {fadd fsub fmul : τ → τ → τ} {feq flt fle : τ → τ → σ}
  {fnot : σ → σ} {fAnd fOr : σ → σ → σ} (st : List τ × List σ)

@[simp] theorem tokStep_0 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 0 st =
    atom2 feq st := rfl
@[simp] theorem tokStep_1 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 1 st =
    atom2 flt st := rfl
@[simp] theorem tokStep_2 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 2 st =
    atom2 fle st := rfl
@[simp] theorem tokStep_3 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 3 st =
    (st.1, ap1 fnot st.2) := rfl
@[simp] theorem tokStep_4 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 4 st =
    (st.1, ap2 fAnd st.2) := rfl
@[simp] theorem tokStep_5 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 5 st =
    (st.1, ap2 fOr st.2) := rfl
@[simp] theorem tokStep_6 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 6 st =
    (fz :: st.1, st.2) := rfl
@[simp] theorem tokStep_7 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 7 st =
    (fo :: st.1, st.2) := rfl
@[simp] theorem tokStep_8 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 8 st =
    (ap2 fadd st.1, st.2) := rfl
@[simp] theorem tokStep_9 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 9 st =
    (ap2 fsub st.1, st.2) := rfl
@[simp] theorem tokStep_10 : tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr 10 st =
    (ap2 fmul st.1, st.2) := rfl

@[simp] theorem tokStep_var (i : ℕ) :
    tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr (i + 11) st =
      (fv i :: st.1, st.2) := by
  unfold tokStep
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]

end Stack

/-! ### Token lists and catamorphisms -/

/-- The Polish token list of a term. -/
def Term.toks : Term → List ℕ
  | .var i => [i + 11]
  | .zero => [6]
  | .one => [7]
  | .add s t => 8 :: (s.toks ++ t.toks)
  | .sub s t => 9 :: (s.toks ++ t.toks)
  | .mul s t => 10 :: (s.toks ++ t.toks)

/-- The Polish token list of a formula (the atoms are followed by the tokens of their terms). -/
def Formula.toks : Formula → List ℕ
  | .eq s t => 0 :: (s.toks ++ t.toks)
  | .lt s t => 1 :: (s.toks ++ t.toks)
  | .le s t => 2 :: (s.toks ++ t.toks)
  | .not φ => 3 :: φ.toks
  | .and φ ψ => 4 :: (φ.toks ++ ψ.toks)
  | .or φ ψ => 5 :: (φ.toks ++ ψ.toks)

section Cata

variable {τ σ : Type}

/-- Bottom-up structural recursion (catamorphism) on terms: the value of a node is computed
from its label and the values of its children. -/
def Term.cata (fv : ℕ → τ) (fz fo : τ) (fadd fsub fmul : τ → τ → τ) : Term → τ
  | .var i => fv i
  | .zero => fz
  | .one => fo
  | .add s t => fadd (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)
  | .sub s t => fsub (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)
  | .mul s t => fmul (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)

/-- Bottom-up structural recursion (catamorphism) on formulas; an atom is evaluated from the
values of its two terms (computed by `Term.cata`). -/
def Formula.cata (fv : ℕ → τ) (fz fo : τ) (fadd fsub fmul : τ → τ → τ)
    (feq flt fle : τ → τ → σ) (fnot : σ → σ) (fAnd fOr : σ → σ → σ) : Formula → σ
  | .eq s t => feq (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)
  | .lt s t => flt (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)
  | .le s t => fle (s.cata fv fz fo fadd fsub fmul) (t.cata fv fz fo fadd fsub fmul)
  | .not φ => fnot (φ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr)
  | .and φ ψ => fAnd (φ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr)
      (ψ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr)
  | .or φ ψ => fOr (φ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr)
      (ψ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr)

variable {fv : ℕ → τ} {fz fo : τ} {fadd fsub fmul : τ → τ → τ} {feq flt fle : τ → τ → σ}
  {fnot : σ → σ} {fAnd fOr : σ → σ → σ}

/-- Evaluating the tokens of a term pushes its catamorphism value on the term stack. -/
theorem Term.foldr_toks (t : Term) (st : List τ × List σ) :
    t.toks.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
      (t.cata fv fz fo fadd fsub fmul :: st.1, st.2) := by
  induction t generalizing st with
  | var i => simp [Term.toks, Term.cata]
  | zero => simp [Term.toks, Term.cata]
  | one => simp [Term.toks, Term.cata]
  | add s t ihs iht => simp [Term.toks, Term.cata, List.foldr_append, iht, ihs]
  | sub s t ihs iht => simp [Term.toks, Term.cata, List.foldr_append, iht, ihs]
  | mul s t ihs iht => simp [Term.toks, Term.cata, List.foldr_append, iht, ihs]

/-- Evaluating the tokens of a formula pushes its catamorphism value on the formula stack. -/
theorem Formula.foldr_toks (φ : Formula) (st : List τ × List σ) :
    φ.toks.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
      (st.1, φ.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr :: st.2) := by
  induction φ generalizing st with
  | eq s t => simp [Formula.toks, Formula.cata, List.foldr_append, Term.foldr_toks]
  | lt s t => simp [Formula.toks, Formula.cata, List.foldr_append, Term.foldr_toks]
  | le s t => simp [Formula.toks, Formula.cata, List.foldr_append, Term.foldr_toks]
  | not φ ih => simp [Formula.toks, Formula.cata, ih]
  | and φ ψ ihφ ihψ => simp [Formula.toks, Formula.cata, List.foldr_append, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [Formula.toks, Formula.cata, List.foldr_append, ihφ, ihψ]

end Cata

/-- The catamorphism with the constructors as operations is the identity. -/
theorem Term.cata_self (t : Term) :
    t.cata Term.var Term.zero Term.one Term.add Term.sub Term.mul = t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp only [Term.cata, ihs, iht]
  | sub s t ihs iht => simp only [Term.cata, ihs, iht]
  | mul s t ihs iht => simp only [Term.cata, ihs, iht]

/-- The catamorphism with the constructors as operations is the identity. -/
theorem Formula.cata_self (φ : Formula) :
    φ.cata Term.var Term.zero Term.one Term.add Term.sub Term.mul Formula.eq Formula.lt
      Formula.le Formula.not Formula.and Formula.or = φ := by
  induction φ with
  | eq s t => simp only [Formula.cata, Term.cata_self]
  | lt s t => simp only [Formula.cata, Term.cata_self]
  | le s t => simp only [Formula.cata, Term.cata_self]
  | not φ ih => simp only [Formula.cata, ih]
  | and φ ψ ihφ ihψ => simp only [Formula.cata, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [Formula.cata, ihφ, ihψ]

/-- The always false formula `1 < 0`. -/
def falseFormula : Formula := .lt .one .zero

/-- The always true formula `0 ≤ 0`. -/
def trueFormula : Formula := .le .zero .zero

/-- The parsing step: `tokStep` with the constructors as operations. -/
def parseStep : ℕ → List Term × List Formula → List Term × List Formula :=
  tokStep Term.var Term.zero Term.one Term.add Term.sub Term.mul Formula.eq Formula.lt
    Formula.le Formula.not Formula.and Formula.or

/-- Parse a token list as a term (total: the top of the term stack, or `0`). -/
def Term.ofToks (l : List ℕ) : Term := (l.foldr parseStep ([], [])).1.headD .zero

/-- Parse a token list as a formula (total: the top of the formula stack, or `falseFormula`). -/
def Formula.ofToks (l : List ℕ) : Formula := (l.foldr parseStep ([], [])).2.headD falseFormula

theorem Term.ofToks_toks (t : Term) : Term.ofToks t.toks = t := by
  simp only [Term.ofToks, parseStep, Term.foldr_toks, List.headD_cons, Term.cata_self]

theorem Formula.ofToks_toks (φ : Formula) : Formula.ofToks φ.toks = φ := by
  simp only [Formula.ofToks, parseStep, Formula.foldr_toks, List.headD_cons, Formula.cata_self]

theorem Term.toks_injective : Function.Injective Term.toks := fun s t h => by
  rw [← Term.ofToks_toks s, h, Term.ofToks_toks]

theorem Formula.toks_injective : Function.Injective Formula.toks := fun φ ψ h => by
  rw [← Formula.ofToks_toks φ, h, Formula.ofToks_toks]

/-! ### Codes -/

/-- Terms are coded by their token lists. -/
instance instCodeTerm : Code Term := Code.ofInj Term.toks Term.ofToks Term.ofToks_toks

/-- Formulas are coded by their token lists. -/
instance instCodeFormula : Code Formula :=
  Code.ofInj Formula.toks Formula.ofToks Formula.ofToks_toks

theorem enc_term (t : Term) : (Code.enc t : Word) = Code.enc t.toks := rfl

theorem enc_formula (φ : Formula) : (Code.enc φ : Word) = Code.enc φ.toks := rfl

theorem size_term (t : Term) : size t = size t.toks := rfl

theorem size_formula (φ : Formula) : size φ = size φ.toks := rfl

end ETR

/-! ### Polynomial-time constructors and token lists -/

open ETR

variable {α : Type} [Code α]

/-- The token list of a term. -/
@[fun_prop] protected theorem PT.termToks {t : α → Term} (ht : PT t) :
    PT (fun a => (t a).toks) :=
  (PT.ofInj_to Term.toks Term.ofToks Term.ofToks_toks).comp ht

/-- The token list of a formula. -/
@[fun_prop] protected theorem PT.formulaToks {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => (φ a).toks) :=
  (PT.ofInj_to Formula.toks Formula.ofToks Formula.ofToks_toks).comp hφ

/-- Into terms: it suffices to compute the token list. -/
theorem PT.term_of_toks {t : α → Term} (h : PT (fun a => (t a).toks)) : PT t :=
  PT.ofInj_mk Term.toks Term.ofToks Term.ofToks_toks h

/-- Into formulas: it suffices to compute the token list. -/
theorem PT.formula_of_toks {φ : α → Formula} (h : PT (fun a => (φ a).toks)) : PT φ :=
  PT.ofInj_mk Formula.toks Formula.ofToks Formula.ofToks_toks h

@[fun_prop] protected theorem PT.termVar {i : α → ℕ} (hi : PT i) : PT (fun a => Term.var (i a)) :=
  PT.term_of_toks (by simp only [Term.toks]; fun_prop)

@[fun_prop] protected theorem PT.termZero : PT (fun _ : α => Term.zero) := PT.const _

@[fun_prop] protected theorem PT.termOne : PT (fun _ : α => Term.one) := PT.const _

@[fun_prop] protected theorem PT.termAdd {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Term.add (s a) (t a)) :=
  PT.term_of_toks (by simp only [Term.toks]; fun_prop)

@[fun_prop] protected theorem PT.termSub {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Term.sub (s a) (t a)) :=
  PT.term_of_toks (by simp only [Term.toks]; fun_prop)

@[fun_prop] protected theorem PT.termMul {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Term.mul (s a) (t a)) :=
  PT.term_of_toks (by simp only [Term.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaEq {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Formula.eq (s a) (t a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaLt {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Formula.lt (s a) (t a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaLe {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => Formula.le (s a) (t a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaNot {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => Formula.not (φ a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaAnd {φ ψ : α → Formula} (hφ : PT φ) (hψ : PT ψ) :
    PT (fun a => Formula.and (φ a) (ψ a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

@[fun_prop] protected theorem PT.formulaOr {φ ψ : α → Formula} (hφ : PT φ) (hψ : PT ψ) :
    PT (fun a => Formula.or (φ a) (ψ a)) :=
  PT.formula_of_toks (by simp only [Formula.toks]; fun_prop)

/-! ### The raw binary codes -/

namespace ETR

/-- The bits written for one token by `Term.encode` / `Formula.encode`. -/
def tokBits (k : ℕ) : Word :=
  if k = 0 then [false, false, false]
  else if k = 1 then [false, false, true]
  else if k = 2 then [false, true, false]
  else if k = 3 then [false, true, true]
  else if k = 4 then [true, false, false]
  else if k = 5 then [true, false, true]
  else if k = 6 then [false, false, true]
  else if k = 7 then [false, true, false]
  else if k = 8 then [false, true, true]
  else if k = 9 then [true, false, false]
  else if k = 10 then [true, false, true]
  else [false, false, false] ++ (List.replicate (k - 11) true ++ [false])

theorem tokBits_var (i : ℕ) : tokBits (i + 11) = [false, false, false] ++ ArtGallery.unary i := by
  unfold tokBits
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
  rfl

@[simp] theorem tokBits_0 : tokBits 0 = [false, false, false] := rfl
@[simp] theorem tokBits_1 : tokBits 1 = [false, false, true] := rfl
@[simp] theorem tokBits_2 : tokBits 2 = [false, true, false] := rfl
@[simp] theorem tokBits_3 : tokBits 3 = [false, true, true] := rfl
@[simp] theorem tokBits_4 : tokBits 4 = [true, false, false] := rfl
@[simp] theorem tokBits_5 : tokBits 5 = [true, false, true] := rfl
@[simp] theorem tokBits_6 : tokBits 6 = [false, false, true] := rfl
@[simp] theorem tokBits_7 : tokBits 7 = [false, true, false] := rfl
@[simp] theorem tokBits_8 : tokBits 8 = [false, true, true] := rfl
@[simp] theorem tokBits_9 : tokBits 9 = [true, false, false] := rfl
@[simp] theorem tokBits_10 : tokBits 10 = [true, false, true] := rfl

theorem three_le_length_tokBits (k : ℕ) : 3 ≤ (tokBits k).length := by
  unfold tokBits
  repeat' split
  all_goals (simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]; try omega)

/-- The raw code of a term is the concatenation of the bits of its tokens. -/
theorem Term.encode_eq_flatMap (t : Term) : t.encode = t.toks.flatMap tokBits := by
  induction t with
  | var i => simp [Term.encode, Term.toks, tokBits_var]
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp [Term.encode, Term.toks, ihs, iht]
  | sub s t ihs iht => simp [Term.encode, Term.toks, ihs, iht]
  | mul s t ihs iht => simp [Term.encode, Term.toks, ihs, iht]

/-- The raw code of a formula is the concatenation of the bits of its tokens. -/
theorem Formula.encode_eq_flatMap (φ : Formula) : φ.encode = φ.toks.flatMap tokBits := by
  induction φ with
  | eq s t => simp [Formula.encode, Formula.toks, Term.encode_eq_flatMap]
  | lt s t => simp [Formula.encode, Formula.toks, Term.encode_eq_flatMap]
  | le s t => simp [Formula.encode, Formula.toks, Term.encode_eq_flatMap]
  | not φ ih => simp [Formula.encode, Formula.toks, ih]
  | and φ ψ ihφ ihψ => simp [Formula.encode, Formula.toks, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [Formula.encode, Formula.toks, ihφ, ihψ]

/-- A formula has at most as many tokens as its raw code has bits. -/
theorem Formula.length_toks_le (φ : Formula) : φ.toks.length ≤ φ.encode.length := by
  rw [Formula.encode_eq_flatMap]
  exact length_le_length_flatMap _ _ fun k _ => Nat.le_trans (by omega) (three_le_length_tokBits k)

end ETR

@[fun_prop] protected theorem PT.tokBits {k : α → ℕ} (hk : PT k) : PT (fun a => tokBits (k a)) := by
  unfold tokBits
  fun_prop

/-- The raw code of a term (`ArtGallery.ETR.Term.encode`), as a word. -/
@[fun_prop] protected theorem PT.termEncode {t : α → Term} (ht : PT t) :
    PT (fun a => (t a).encode) := by
  have h : PT (fun a => (t a).toks.flatMap tokBits) :=
    PT.flatMap (f := fun _ k => tokBits k) (PT.tokBits PT.snd') (PT.termToks ht)
  exact h.of_eq fun a => (Term.encode_eq_flatMap (t a)).symm

/-- The raw code of a formula (`ArtGallery.ETR.Formula.encode`), as a word. -/
@[fun_prop] protected theorem PT.formulaEncode {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => (φ a).encode) := by
  have h : PT (fun a => (φ a).toks.flatMap tokBits) :=
    PT.flatMap (f := fun _ k => tokBits k) (PT.tokBits PT.snd') (PT.formulaToks hφ)
  exact h.of_eq fun a => (Formula.encode_eq_flatMap (φ a)).symm

end ArtGallery

end
