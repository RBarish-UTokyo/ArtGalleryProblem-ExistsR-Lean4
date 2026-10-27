module

public import ArtGallery.PTime.ETRCode
public import ArtGallery.PTime.Scan

/-!
# Polynomial-time bottom-up recursion on ETR terms and formulas

* `PT.tokStep`: one step of the stack evaluation of Polish token lists is polynomial-time
  (when the node operations are);
* **`PT.termCata`**, **`PT.formulaCata`**: a catamorphism (`ETR.Term.cata`,
  `ETR.Formula.cata`) whose node operations are polynomial-time is polynomial-time, provided its
  values on all subterms / subformulas of the input (`ETR.Term.subterms`,
  `ETR.Formula.subterms`, `ETR.Formula.subformulas`) are polynomially bounded in size
  (`size_le_of_mem_subterms` etc. bound the size of a subterm by the size of the input);
* `PT.termOfToks`, `PT.formulaOfToks`: parsing an arbitrary token list is polynomial-time.

The evaluation runs on the Polish token list from right to left (`List.foldr`) with a stack of
term values and a stack of formula values; every stack entry is the value of a subterm or
subformula (`Term.suffix_foldr`, `Formula.suffix_foldr`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETR

/-! ### Subterms and subformulas -/

/-- All subterms of a term (with repetitions), the term itself first. -/
def Term.subterms : Term → List Term
  | .var i => [.var i]
  | .zero => [.zero]
  | .one => [.one]
  | .add s t => .add s t :: (s.subterms ++ t.subterms)
  | .sub s t => .sub s t :: (s.subterms ++ t.subterms)
  | .mul s t => .mul s t :: (s.subterms ++ t.subterms)

/-- All subterms of the atoms of a formula. -/
def Formula.subterms : Formula → List Term
  | .eq s t => s.subterms ++ t.subterms
  | .lt s t => s.subterms ++ t.subterms
  | .le s t => s.subterms ++ t.subterms
  | .not φ => φ.subterms
  | .and φ ψ => φ.subterms ++ ψ.subterms
  | .or φ ψ => φ.subterms ++ ψ.subterms

/-- All subformulas of a formula (with repetitions), the formula itself first. -/
def Formula.subformulas : Formula → List Formula
  | .eq s t => [.eq s t]
  | .lt s t => [.lt s t]
  | .le s t => [.le s t]
  | .not φ => .not φ :: φ.subformulas
  | .and φ ψ => .and φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | .or φ ψ => .or φ ψ :: (φ.subformulas ++ ψ.subformulas)

theorem Term.mem_subterms_self (t : Term) : t ∈ t.subterms := by
  cases t <;> simp [Term.subterms]

theorem Formula.mem_subformulas_self (φ : Formula) : φ ∈ φ.subformulas := by
  cases φ <;> simp [Formula.subformulas]

theorem Term.toks_ne_nil (t : Term) : t.toks ≠ [] := by
  cases t <;> simp [Term.toks]

theorem Term.one_le_length_toks (t : Term) : 1 ≤ t.toks.length :=
  List.length_pos_iff.mpr t.toks_ne_nil

theorem Formula.one_le_length_toks (φ : Formula) : 1 ≤ φ.toks.length := by
  cases φ <;> simp [Formula.toks]

/-- The tokens of a subterm form a contiguous piece of the tokens of the term. -/
theorem Term.toks_infix_of_mem {u t : Term} (h : u ∈ t.subterms) : u.toks <:+: t.toks := by
  induction t with
  | var i => simp only [Term.subterms, List.mem_singleton] at h; subst h; exact List.infix_rfl
  | zero => simp only [Term.subterms, List.mem_singleton] at h; subst h; exact List.infix_rfl
  | one => simp only [Term.subterms, List.mem_singleton] at h; subst h; exact List.infix_rfl
  | add s t ihs iht | sub s t ihs iht | mul s t ihs iht =>
    simp only [Term.subterms, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact List.infix_rfl
    · exact (ihs h).trans ((List.prefix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))
    · exact (iht h).trans ((List.suffix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))

/-- The tokens of a subterm of a formula form a contiguous piece of its tokens. -/
theorem Formula.toks_infix_of_mem_subterms {u : Term} {φ : Formula} (h : u ∈ φ.subterms) :
    u.toks <:+: φ.toks := by
  induction φ with
  | eq s t | lt s t | le s t =>
    simp only [Formula.subterms, List.mem_append] at h
    rcases h with h | h
    · exact (Term.toks_infix_of_mem h).trans
        ((List.prefix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))
    · exact (Term.toks_infix_of_mem h).trans
        ((List.suffix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))
  | not φ ih =>
    exact (ih h).trans (List.infix_cons List.infix_rfl)
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [Formula.subterms, List.mem_append] at h
    rcases h with h | h
    · exact (ihφ h).trans ((List.prefix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))
    · exact (ihψ h).trans ((List.suffix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))

/-- The tokens of a subformula form a contiguous piece of the tokens of the formula. -/
theorem Formula.toks_infix_of_mem_subformulas {ψ φ : Formula} (h : ψ ∈ φ.subformulas) :
    ψ.toks <:+: φ.toks := by
  induction φ with
  | eq s t | lt s t | le s t =>
    simp only [Formula.subformulas, List.mem_singleton] at h; subst h; exact List.infix_rfl
  | not φ ih =>
    simp only [Formula.subformulas, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.infix_rfl
    · exact (ih h).trans (List.infix_cons List.infix_rfl)
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact List.infix_rfl
    · exact (ih₁ h).trans ((List.prefix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))
    · exact (ih₂ h).trans ((List.suffix_append _ _).isInfix.trans (List.infix_cons List.infix_rfl))

theorem size_le_of_mem_subterms {u t : Term} (h : u ∈ t.subterms) : size u ≤ size t :=
  size_le_of_sublist (Term.toks_infix_of_mem h).sublist

theorem size_le_of_mem_formula_subterms {u : Term} {φ : Formula} (h : u ∈ φ.subterms) :
    size u ≤ size φ :=
  size_le_of_sublist (Formula.toks_infix_of_mem_subterms h).sublist

theorem size_le_of_mem_subformulas {ψ φ : Formula} (h : ψ ∈ φ.subformulas) :
    size ψ ≤ size φ :=
  size_le_of_sublist (Formula.toks_infix_of_mem_subformulas h).sublist

/-! ### The stacks along the evaluation -/

section Suffix

variable {τ σ : Type} {fv : ℕ → τ} {fz fo : τ} {fadd fsub fmul : τ → τ → τ}
  {feq flt fle : τ → τ → σ} {fnot : σ → σ} {fAnd fOr : σ → σ → σ}

/-- Evaluating all tokens of a term pushes its value. -/
theorem Term.whole_foldr (t : Term) :
    ∃ L : List Term, (∀ u ∈ L, u ∈ t.subterms) ∧ L.length ≤ t.toks.length ∧
      ∀ st : List τ × List σ,
        t.toks.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
          (L.map (Term.cata fv fz fo fadd fsub fmul) ++ st.1, st.2) :=
  ⟨[t], by simp [Term.mem_subterms_self], by simpa using t.one_le_length_toks,
    fun st => by simp [Term.foldr_toks]⟩

/-- Evaluating a suffix of the tokens of a term pushes the values of some subterms. -/
theorem Term.suffix_foldr (t : Term) {suf : List ℕ} (h : suf <:+ t.toks) :
    ∃ L : List Term, (∀ u ∈ L, u ∈ t.subterms) ∧ L.length ≤ suf.length ∧
      ∀ st : List τ × List σ,
        suf.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
          (L.map (Term.cata fv fz fo fadd fsub fmul) ++ st.1, st.2) := by
  induction t generalizing suf with
  | var i | zero | one =>
    simp only [Term.toks, List.suffix_cons_iff, List.suffix_nil] at h
    rcases h with rfl | rfl
    · exact Term.whole_foldr _
    · exact ⟨[], by simp, by simp, fun st => by simp⟩
  | add s t ihs iht | sub s t ihs iht | mul s t ihs iht =>
    simp only [Term.toks, List.suffix_cons_iff] at h
    rcases h with rfl | h
    · exact Term.whole_foldr _
    rcases suffix_append_cases h with h | ⟨l', hl', rfl⟩
    · obtain ⟨L, hL, hlen, hst⟩ := iht h
      exact ⟨L, fun u hu => by simp [Term.subterms, hL u hu], hlen, hst⟩
    · obtain ⟨L, hL, hlen, hst⟩ := ihs hl'
      refine ⟨L ++ [t], fun u hu => ?_, ?_, fun st => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · simp [Term.subterms, hL u hu]
        · simp [Term.subterms, Term.mem_subterms_self]
      · have := t.one_le_length_toks
        simp only [List.length_append, List.length_singleton]
        omega
      · simp [List.foldr_append, Term.foldr_toks, hst]

/-- Evaluating all tokens of a formula pushes its value. -/
theorem Formula.whole_foldr (φ : Formula) :
    ∃ (LT : List Term) (LF : List Formula), (∀ u ∈ LT, u ∈ φ.subterms) ∧
      (∀ ψ ∈ LF, ψ ∈ φ.subformulas) ∧ LT.length + LF.length ≤ φ.toks.length ∧
      ∀ st : List τ × List σ,
        φ.toks.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
          (LT.map (Term.cata fv fz fo fadd fsub fmul) ++ st.1,
            LF.map (Formula.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) ++ st.2) :=
  ⟨[], [φ], by simp, by simp [Formula.mem_subformulas_self],
    by simpa using φ.one_le_length_toks, fun st => by simp [Formula.foldr_toks]⟩

/-- Evaluating a suffix of the tokens of a formula pushes the values of some subterms and
subformulas. -/
theorem Formula.suffix_foldr (φ : Formula) {suf : List ℕ} (h : suf <:+ φ.toks) :
    ∃ (LT : List Term) (LF : List Formula), (∀ u ∈ LT, u ∈ φ.subterms) ∧
      (∀ ψ ∈ LF, ψ ∈ φ.subformulas) ∧ LT.length + LF.length ≤ suf.length ∧
      ∀ st : List τ × List σ,
        suf.foldr (tokStep fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) st =
          (LT.map (Term.cata fv fz fo fadd fsub fmul) ++ st.1,
            LF.map (Formula.cata fv fz fo fadd fsub fmul feq flt fle fnot fAnd fOr) ++ st.2) := by
  induction φ generalizing suf with
  | eq s t | lt s t | le s t =>
    simp only [Formula.toks, List.suffix_cons_iff] at h
    rcases h with rfl | h
    · exact Formula.whole_foldr _
    rcases suffix_append_cases h with h | ⟨l', hl', rfl⟩
    · obtain ⟨L, hL, hlen, hst⟩ := Term.suffix_foldr (τ := τ) (σ := σ) (fv := fv) (fz := fz)
        (fo := fo) (fadd := fadd) (fsub := fsub) (fmul := fmul) (feq := feq) (flt := flt)
        (fle := fle) (fnot := fnot) (fAnd := fAnd) (fOr := fOr) t h
      exact ⟨L, [], fun u hu => by simp [Formula.subterms, hL u hu], by simp,
        by simpa using hlen, fun st => by simp [hst]⟩
    · obtain ⟨L, hL, hlen, hst⟩ := Term.suffix_foldr (τ := τ) (σ := σ) (fv := fv) (fz := fz)
        (fo := fo) (fadd := fadd) (fsub := fsub) (fmul := fmul) (feq := feq) (flt := flt)
        (fle := fle) (fnot := fnot) (fAnd := fAnd) (fOr := fOr) s hl'
      refine ⟨L ++ [t], [], fun u hu => ?_, by simp, ?_, fun st => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · simp [Formula.subterms, hL u hu]
        · simp [Formula.subterms, Term.mem_subterms_self]
      · have := t.one_le_length_toks
        simp only [List.length_append, List.length_singleton, List.length_nil]
        omega
      · simp [List.foldr_append, Term.foldr_toks, hst]
  | not φ ih =>
    simp only [Formula.toks, List.suffix_cons_iff] at h
    rcases h with rfl | h
    · exact Formula.whole_foldr _
    obtain ⟨LT, LF, hT, hF, hlen, hst⟩ := ih h
    exact ⟨LT, LF, fun u hu => by simpa [Formula.subterms] using hT u hu,
      fun ψ hψ => by simp [Formula.subformulas, hF ψ hψ], hlen, hst⟩
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.toks, List.suffix_cons_iff] at h
    rcases h with rfl | h
    · exact Formula.whole_foldr _
    rcases suffix_append_cases h with h | ⟨l', hl', rfl⟩
    · obtain ⟨LT, LF, hT, hF, hlen, hst⟩ := ih₂ h
      exact ⟨LT, LF, fun u hu => by simp [Formula.subterms, hT u hu],
        fun ψ hψ => by simp [Formula.subformulas, hF ψ hψ], hlen, hst⟩
    · obtain ⟨LT, LF, hT, hF, hlen, hst⟩ := ih₁ hl'
      refine ⟨LT, LF ++ [φ₂], fun u hu => by simp [Formula.subterms, hT u hu], fun ψ hψ => ?_,
        ?_, fun st => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hψ
        rcases hψ with hψ | rfl
        · simp [Formula.subformulas, hF ψ hψ]
        · simp [Formula.subformulas, Formula.mem_subformulas_self]
      · have := φ₂.one_le_length_toks
        simp only [List.length_append, List.length_singleton]
        omega
      · simp [List.foldr_append, Formula.foldr_toks, hst]

end Suffix

end ETR

/-! ### Polynomial time -/

open ETR

section PTLemmas

variable {α τ σ : Type} [Code α] [Code τ] [Code σ]

@[fun_prop] protected theorem PT.ap2 {f : α → τ → τ → τ} {l : α → List τ}
    (hf : PT (fun p : α × τ × τ => f p.1 p.2.1 p.2.2)) (hl : PT l) :
    PT (fun a => ap2 (f a) (l a)) := by
  have h : PT (fun a => (l a).head?.elim (l a) (fun x => (l a).tail.head?.elim (l a)
      (fun y => f a x y :: (l a).tail.tail))) := by
    refine PT.optionElim (PT.head? hl) hl ?_
    refine PT.optionElim (PT.head? (PT.tail (hl.comp (PT.fst PT.id)))) (hl.comp (PT.fst PT.id)) ?_
    exact PT.cons (hf.comp (PT.pair (PT.fst (PT.fst PT.id))
      (PT.pair (PT.snd (PT.fst PT.id)) (PT.snd PT.id))))
      (PT.tail (PT.tail (hl.comp (PT.fst (PT.fst PT.id)))))
  refine h.of_eq fun a => ?_
  generalize l a = m
  rcases m with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> rfl

@[fun_prop] protected theorem PT.ap1 {f : α → σ → σ} {l : α → List σ}
    (hf : PT (fun p : α × σ => f p.1 p.2)) (hl : PT l) :
    PT (fun a => ap1 (f a) (l a)) := by
  have h : PT (fun a => (l a).head?.elim [] (fun x => f a x :: (l a).tail)) := by
    refine PT.optionElim (PT.head? hl) (PT.const []) ?_
    exact PT.cons hf (PT.tail (hl.comp (PT.fst PT.id)))
  refine h.of_eq fun a => ?_
  generalize l a = m
  rcases m with _ | ⟨x, r⟩ <;> rfl

@[fun_prop] protected theorem PT.atom2 {f : α → τ → τ → σ} {st : α → List τ × List σ}
    (hf : PT (fun p : α × τ × τ => f p.1 p.2.1 p.2.2)) (hst : PT st) :
    PT (fun a => atom2 (f a) (st a)) := by
  have h : PT (fun a => (st a).1.head?.elim (st a) (fun x => (st a).1.tail.head?.elim (st a)
      (fun y => ((st a).1.tail.tail, f a x y :: (st a).2)))) := by
    refine PT.optionElim (PT.head? (PT.fst hst)) hst ?_
    refine PT.optionElim (PT.head? (PT.tail (PT.fst (hst.comp (PT.fst PT.id)))))
      (hst.comp (PT.fst PT.id)) ?_
    exact PT.pair (PT.tail (PT.tail (PT.fst (hst.comp (PT.fst (PT.fst PT.id))))))
      (PT.cons (hf.comp (PT.pair (PT.fst (PT.fst PT.id))
        (PT.pair (PT.snd (PT.fst PT.id)) (PT.snd PT.id))))
        (PT.snd (hst.comp (PT.fst (PT.fst PT.id)))))
  refine h.of_eq fun a => ?_
  generalize st a = m
  rcases m with ⟨_ | ⟨x, _ | ⟨y, r⟩⟩, s⟩ <;> rfl

variable {fv : α → ℕ → τ} {fz fo : α → τ} {fadd fsub fmul : α → τ → τ → τ}
  {feq flt fle : α → τ → τ → σ} {fnot : α → σ → σ} {fAnd fOr : α → σ → σ → σ}

/-- **One evaluation step is polynomial-time** (compositional form). -/
protected theorem PT.tokStep
    (hv : PT (fun p : α × ℕ => fv p.1 p.2)) (hz : PT fz) (ho : PT fo)
    (hadd : PT (fun p : α × τ × τ => fadd p.1 p.2.1 p.2.2))
    (hsub : PT (fun p : α × τ × τ => fsub p.1 p.2.1 p.2.2))
    (hmul : PT (fun p : α × τ × τ => fmul p.1 p.2.1 p.2.2))
    (heq : PT (fun p : α × τ × τ => feq p.1 p.2.1 p.2.2))
    (hlt : PT (fun p : α × τ × τ => flt p.1 p.2.1 p.2.2))
    (hle : PT (fun p : α × τ × τ => fle p.1 p.2.1 p.2.2))
    (hnot : PT (fun p : α × σ => fnot p.1 p.2))
    (hand : PT (fun p : α × σ × σ => fAnd p.1 p.2.1 p.2.2))
    (hor : PT (fun p : α × σ × σ => fOr p.1 p.2.1 p.2.2))
    {k : α → ℕ} {st : α → List τ × List σ} (hk : PT k) (hst : PT st) :
    PT (fun a => tokStep (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a) (feq a) (flt a) (fle a)
      (fnot a) (fAnd a) (fOr a) (k a) (st a)) := by
  have hvar : PT (fun a => fv a (k a - 11)) := hv.comp (PT.pair PT.id (PT.sub hk (PT.const 11)))
  unfold tokStep
  refine PT.ite_prop (PT.natEq hk (PT.const 0)) (PT.atom2 heq hst) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 1)) (PT.atom2 hlt hst) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 2)) (PT.atom2 hle hst) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 3)) (PT.pair (PT.fst hst) (PT.ap1 hnot (PT.snd hst))) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 4)) (PT.pair (PT.fst hst) (PT.ap2 hand (PT.snd hst))) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 5)) (PT.pair (PT.fst hst) (PT.ap2 hor (PT.snd hst))) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 6)) (PT.pair (PT.cons hz (PT.fst hst)) (PT.snd hst)) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 7)) (PT.pair (PT.cons ho (PT.fst hst)) (PT.snd hst)) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 8)) (PT.pair (PT.ap2 hadd (PT.fst hst)) (PT.snd hst)) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 9)) (PT.pair (PT.ap2 hsub (PT.fst hst)) (PT.snd hst)) ?_
  refine PT.ite_prop (PT.natEq hk (PT.const 10)) (PT.pair (PT.ap2 hmul (PT.fst hst)) (PT.snd hst)) ?_
  exact PT.pair (PT.cons hvar (PT.fst hst)) (PT.snd hst)

/-- One evaluation step is polynomial-time (uncurried form, as needed by `PT.foldr`). -/
protected theorem PT.tokStep'
    (hv : PT (fun p : α × ℕ => fv p.1 p.2)) (hz : PT fz) (ho : PT fo)
    (hadd : PT (fun p : α × τ × τ => fadd p.1 p.2.1 p.2.2))
    (hsub : PT (fun p : α × τ × τ => fsub p.1 p.2.1 p.2.2))
    (hmul : PT (fun p : α × τ × τ => fmul p.1 p.2.1 p.2.2))
    (heq : PT (fun p : α × τ × τ => feq p.1 p.2.1 p.2.2))
    (hlt : PT (fun p : α × τ × τ => flt p.1 p.2.1 p.2.2))
    (hle : PT (fun p : α × τ × τ => fle p.1 p.2.1 p.2.2))
    (hnot : PT (fun p : α × σ => fnot p.1 p.2))
    (hand : PT (fun p : α × σ × σ => fAnd p.1 p.2.1 p.2.2))
    (hor : PT (fun p : α × σ × σ => fOr p.1 p.2.1 p.2.2)) :
    PT (fun p : α × ℕ × (List τ × List σ) => tokStep (fv p.1) (fz p.1) (fo p.1) (fadd p.1)
      (fsub p.1) (fmul p.1) (feq p.1) (flt p.1) (fle p.1) (fnot p.1) (fAnd p.1) (fOr p.1)
      p.2.1 p.2.2) := by
  have e2 : PT (fun q : (α × ℕ × (List τ × List σ)) × τ × τ => (q.1.1, q.2)) := by fun_prop
  have e3 : PT (fun q : (α × ℕ × (List τ × List σ)) × σ × σ => (q.1.1, q.2)) := by fun_prop
  exact PT.tokStep (fv := fun p => fv p.1) (fz := fun p => fz p.1) (fo := fun p => fo p.1)
    (fadd := fun p => fadd p.1) (fsub := fun p => fsub p.1) (fmul := fun p => fmul p.1)
    (feq := fun p => feq p.1) (flt := fun p => flt p.1) (fle := fun p => fle p.1)
    (fnot := fun p => fnot p.1) (fAnd := fun p => fAnd p.1) (fOr := fun p => fOr p.1)
    (hv.comp (g := fun q : (α × ℕ × (List τ × List σ)) × ℕ => (q.1.1, q.2)) (by fun_prop))
    (hz.comp (g := fun p : α × ℕ × (List τ × List σ) => p.1) (by fun_prop))
    (ho.comp (g := fun p : α × ℕ × (List τ × List σ) => p.1) (by fun_prop))
    (hadd.comp e2) (hsub.comp e2) (hmul.comp e2) (heq.comp e2) (hlt.comp e2) (hle.comp e2)
    (hnot.comp (g := fun q : (α × ℕ × (List τ × List σ)) × σ => (q.1.1, q.2)) (by fun_prop))
    (hand.comp e3) (hor.comp e3)
    (PT.fst (PT.snd PT.id)) (PT.snd (PT.snd PT.id))

/-- **Bottom-up recursion on formulas is polynomial-time.**  The node operations are
polynomial-time (in uncurried form, with the environment `a` as first component), and the values
of the recursion on all subterms and subformulas of `φ a` are polynomially bounded in size. -/
theorem PT.formulaCata {φ : α → Formula}
    (hv : PT (fun p : α × ℕ => fv p.1 p.2)) (hz : PT fz) (ho : PT fo)
    (hadd : PT (fun p : α × τ × τ => fadd p.1 p.2.1 p.2.2))
    (hsub : PT (fun p : α × τ × τ => fsub p.1 p.2.1 p.2.2))
    (hmul : PT (fun p : α × τ × τ => fmul p.1 p.2.1 p.2.2))
    (heq : PT (fun p : α × τ × τ => feq p.1 p.2.1 p.2.2))
    (hlt : PT (fun p : α × τ × τ => flt p.1 p.2.1 p.2.2))
    (hle : PT (fun p : α × τ × τ => fle p.1 p.2.1 p.2.2))
    (hnot : PT (fun p : α × σ => fnot p.1 p.2))
    (hand : PT (fun p : α × σ × σ => fAnd p.1 p.2.1 p.2.2))
    (hor : PT (fun p : α × σ × σ => fOr p.1 p.2.1 p.2.2))
    (hφ : PT φ) (bound : ℕ → ℕ) (hbound : PolynomialBound bound)
    (hsizeT : ∀ a, ∀ u ∈ (φ a).subterms,
      size (u.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)) ≤ bound (size a))
    (hsizeF : ∀ a, ∀ ψ ∈ (φ a).subformulas,
      size (ψ.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a) (feq a) (flt a) (fle a)
        (fnot a) (fAnd a) (fOr a)) ≤ bound (size a)) :
    PT (fun a => (φ a).cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a) (feq a) (flt a)
      (fle a) (fnot a) (fAnd a) (fOr a)) := by
  obtain ⟨c, k, hk⟩ := hφ.size_le
  have hfold := PT.foldr (f := fun a => tokStep (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)
      (feq a) (flt a) (fle a) (fnot a) (fAnd a) (fOr a)) (init := fun _ => ([], []))
    (l := fun a => (φ a).toks)
    (PT.tokStep' hv hz ho hadd hsub hmul heq hlt hle hnot hand hor) (PT.const _)
    (PT.formulaToks hφ) (fun N => 2 * (powerBound c k N * (bound N + 1) + 1))
    (((PolynomialBound.constant 2).mul (((PolynomialBound.power c k).mul
      (hbound.add (PolynomialBound.constant 1))).add (PolynomialBound.constant 1)))) ?_
  · refine PT.of_some ((PT.head? (PT.snd hfold)).of_eq fun a => ?_)
    simp [Formula.foldr_toks]
  · intro a suf hsuf
    try dsimp only
    obtain ⟨LT, LF, hT, hF, hlen, hst⟩ := (φ a).suffix_foldr (fv := fv a) (fz := fz a)
      (fo := fo a) (fadd := fadd a) (fsub := fsub a) (fmul := fmul a) (feq := feq a)
      (flt := flt a) (fle := fle a) (fnot := fnot a) (fAnd := fAnd a) (fOr := fOr a) hsuf
    rw [hst]
    simp only [List.append_nil, size_prod]
    have hsl : suf.length ≤ powerBound c k (size a) := by
      have h1 := hsuf.length_le
      have h2 := length_lt_size (φ a).toks
      have h3 := hk a
      rw [size_formula] at h3
      omega
    have h1 := size_map_le (g := (Term.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)))
      (K := bound (size a)) (l := LT) fun u hu => hsizeT a u (hT u hu)
    have h2 := size_map_le (g := (Formula.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)
      (feq a) (flt a) (fle a) (fnot a) (fAnd a) (fOr a))) (K := bound (size a)) (l := LF)
      fun ψ hψ => hsizeF a ψ (hF ψ hψ)
    have h3 : LT.length * (bound (size a) + 1) ≤ powerBound c k (size a) * (bound (size a) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : LF.length * (bound (size a) + 1) ≤ powerBound c k (size a) * (bound (size a) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- **Bottom-up recursion on terms is polynomial-time.**  The node operations are
polynomial-time (in uncurried form, with the environment `a` as first component), and the values
of the recursion on all subterms of `t a` are polynomially bounded in size. -/
theorem PT.termCata {t : α → Term}
    (hv : PT (fun p : α × ℕ => fv p.1 p.2)) (hz : PT fz) (ho : PT fo)
    (hadd : PT (fun p : α × τ × τ => fadd p.1 p.2.1 p.2.2))
    (hsub : PT (fun p : α × τ × τ => fsub p.1 p.2.1 p.2.2))
    (hmul : PT (fun p : α × τ × τ => fmul p.1 p.2.1 p.2.2))
    (ht : PT t) (bound : ℕ → ℕ) (hbound : PolynomialBound bound)
    (hsize : ∀ a, ∀ u ∈ (t a).subterms,
      size (u.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)) ≤ bound (size a)) :
    PT (fun a => (t a).cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)) := by
  obtain ⟨c, k, hk⟩ := ht.size_le
  have hfold := PT.foldr (f := fun a => tokStep (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)
      (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => ()) (fun _ => ()) (fun _ _ => ())
      (fun _ _ => ())) (init := fun _ => (([] : List τ), ([] : List Unit)))
    (l := fun a => (t a).toks)
    (PT.tokStep' (σ := Unit) (fv := fv) (fz := fz) (fo := fo) (fadd := fadd) (fsub := fsub)
      (fmul := fmul) (feq := fun _ _ _ => ()) (flt := fun _ _ _ => ()) (fle := fun _ _ _ => ())
      (fnot := fun _ _ => ()) (fAnd := fun _ _ _ => ()) (fOr := fun _ _ _ => ())
      hv hz ho hadd hsub hmul (PT.const ()) (PT.const ()) (PT.const ())
      (PT.const ()) (PT.const ()) (PT.const ())) (PT.const _)
    (PT.termToks ht) (fun N => powerBound c k N * (bound N + 1) + 2)
    (((PolynomialBound.power c k).mul (hbound.add (PolynomialBound.constant 1))).add
      (PolynomialBound.constant 2)) ?_
  · refine (PT.headD (PT.fst hfold) hz).of_eq fun a => ?_
    simp [Term.foldr_toks]
  · intro a suf hsuf
    try dsimp only
    obtain ⟨L, hL, hlen, hst⟩ := (t a).suffix_foldr (σ := Unit) (fv := fv a) (fz := fz a)
      (fo := fo a) (fadd := fadd a) (fsub := fsub a) (fmul := fmul a) (feq := fun _ _ => ())
      (flt := fun _ _ => ()) (fle := fun _ _ => ()) (fnot := fun _ => ()) (fAnd := fun _ _ => ())
      (fOr := fun _ _ => ()) hsuf
    rw [hst]
    simp only [List.append_nil, size_prod, size_nil]
    have hsl : suf.length ≤ powerBound c k (size a) := by
      have h1 := hsuf.length_le
      have h2 := length_lt_size (t a).toks
      have h3 := hk a
      rw [size_term] at h3
      omega
    have h1 := size_map_le (g := (Term.cata (fv a) (fz a) (fo a) (fadd a) (fsub a) (fmul a)))
      (K := bound (size a)) (l := L) fun u hu => hsize a u (hL u hu)
    have h3 : L.length * (bound (size a) + 1) ≤ powerBound c k (size a) * (bound (size a) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end PTLemmas

/-! ### Parsing arbitrary token lists -/

namespace ETR

theorem size_node_term {k : ℕ} (hk : k ≤ 10) (f : Term → Term → Term)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (x y : Term) :
    size (f x y) ≤ size x + size y + 11 := by
  have := size_append x.toks y.toks
  rw [size_term, hf, size_term x, size_term y, size_cons, size_nat]
  omega

theorem size_node_atom {k : ℕ} (hk : k ≤ 10) (f : Term → Term → Formula)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (x y : Term) :
    size (f x y) ≤ size x + size y + 11 := by
  have := size_append x.toks y.toks
  rw [size_formula, hf, size_term x, size_term y, size_cons, size_nat]
  omega

theorem size_node_formula {k : ℕ} (hk : k ≤ 10) (f : Formula → Formula → Formula)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (x y : Formula) :
    size (f x y) ≤ size x + size y + 11 := by
  have := size_append x.toks y.toks
  rw [size_formula, hf, size_formula x, size_formula y, size_cons, size_nat]
  omega

theorem size_ap2_le {τ : Type} [Code τ] (f : τ → τ → τ) (C : ℕ)
    (hf : ∀ x y, size (f x y) ≤ size x + size y + C) (l : List τ) :
    size (ap2 f l) ≤ size l + C := by
  rcases l with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp [ap2]
  · simp [ap2]
  · have := hf x y
    simp only [ap2_cons_cons, size_cons]
    omega

theorem size_ap1_le {σ : Type} [Code σ] (f : σ → σ) (C : ℕ) (hf : ∀ x, size (f x) ≤ size x + C)
    (l : List σ) : size (ap1 f l) ≤ size l + C := by
  rcases l with _ | ⟨x, r⟩
  · simp [ap1]
  · have := hf x
    simp only [ap1_cons, size_cons]
    omega

theorem size_atom2_le {τ σ : Type} [Code τ] [Code σ] (f : τ → τ → σ) (C : ℕ)
    (hf : ∀ x y, size (f x y) ≤ size x + size y + C) (st : List τ × List σ) :
    size (atom2 f st) ≤ size st + C := by
  rcases st with ⟨_ | ⟨x, _ | ⟨y, r⟩⟩, s⟩
  · simp [atom2]
  · simp [atom2]
  · have := hf x y
    simp only [atom2_cons_cons, size_prod, size_cons]
    omega

/-- One parsing step increases the size of the stacks by at most the size of the token plus a
constant. -/
theorem size_parseStep (k : ℕ) (st : List Term × List Formula) :
    size (parseStep k st) ≤ size st + k + 16 := by
  have hadd := size_ap2_le Term.add 11 (size_node_term (k := 8) (by omega) _ fun _ _ => rfl) st.1
  have hsub := size_ap2_le Term.sub 11 (size_node_term (k := 9) (by omega) _ fun _ _ => rfl) st.1
  have hmul := size_ap2_le Term.mul 11 (size_node_term (k := 10) (by omega) _ fun _ _ => rfl) st.1
  have hand := size_ap2_le Formula.and 11
    (size_node_formula (k := 4) (by omega) _ fun _ _ => rfl) st.2
  have hor := size_ap2_le Formula.or 11
    (size_node_formula (k := 5) (by omega) _ fun _ _ => rfl) st.2
  have hnot := size_ap1_le Formula.not 5 (fun x => by
    rw [size_formula, size_formula x]
    simp only [Formula.toks, size_cons, size_nat]
    omega) st.2
  have heq := size_atom2_le Formula.eq 11 (size_node_atom (k := 0) (by omega) _ fun _ _ => rfl) st
  have hlt := size_atom2_le Formula.lt 11 (size_node_atom (k := 1) (by omega) _ fun _ _ => rfl) st
  have hle := size_atom2_le Formula.le 11 (size_node_atom (k := 2) (by omega) _ fun _ _ => rfl) st
  have hz : size Term.zero = 9 := by rw [size_term]; simp [Term.toks]
  have ho : size Term.one = 10 := by rw [size_term]; simp [Term.toks]
  match k with
  | 0 => simp only [parseStep, tokStep_0]; omega
  | 1 => simp only [parseStep, tokStep_1]; omega
  | 2 => simp only [parseStep, tokStep_2]; omega
  | 3 => simp only [parseStep, tokStep_3, size_prod]; omega
  | 4 => simp only [parseStep, tokStep_4, size_prod]; omega
  | 5 => simp only [parseStep, tokStep_5, size_prod]; omega
  | 6 => simp only [parseStep, tokStep_6, size_prod, size_cons]; omega
  | 7 => simp only [parseStep, tokStep_7, size_prod, size_cons]; omega
  | 8 => simp only [parseStep, tokStep_8, size_prod]; omega
  | 9 => simp only [parseStep, tokStep_9, size_prod]; omega
  | 10 => simp only [parseStep, tokStep_10, size_prod]; omega
  | j + 11 =>
    have hv : size (Term.var j) = j + 14 := by
      rw [size_term]
      simp only [Term.toks, size_cons, size_nil, size_nat]
    simp only [parseStep, tokStep_var, size_prod, size_cons]
    omega

end ETR

section Parse

variable {α : Type} [Code α]

/-- The parsing evaluation is polynomial-time on arbitrary token lists. -/
theorem PT.parseFoldr {l : α → List ℕ} (hl : PT l) :
    PT (fun a => (l a).foldr parseStep ([], [])) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  refine PT.foldr_of_add_le (f := fun _ => parseStep) (by
      have := PT.tokStep' (α := α) (fv := fun _ i => Term.var i) (fz := fun _ => Term.zero)
        (fo := fun _ => Term.one) (fadd := fun _ => Term.add) (fsub := fun _ => Term.sub)
        (fmul := fun _ => Term.mul) (feq := fun _ => Formula.eq) (flt := fun _ => Formula.lt)
        (fle := fun _ => Formula.le) (fnot := fun _ => Formula.not) (fAnd := fun _ => Formula.and)
        (fOr := fun _ => Formula.or) (PT.termVar PT.snd') (PT.const _) (PT.const _)
        (PT.termAdd (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.termSub (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.termMul (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.formulaEq (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.formulaLt (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.formulaLe (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.formulaNot PT.snd')
        (PT.formulaAnd (PT.fst PT.snd') (PT.snd PT.snd'))
        (PT.formulaOr (PT.fst PT.snd') (PT.snd PT.snd'))
      exact this) (PT.const _) hl (fun N => powerBound c k N + 16)
    ((PolynomialBound.power c k).add (PolynomialBound.constant 16)) ?_
  intro a b s hb
  try dsimp only
  have h1 := size_parseStep b s
  have h2 := size_le_of_mem hb
  have h3 := hk a
  rw [size_nat] at h2
  omega

/-- Parsing an arbitrary token list as a term is polynomial-time. -/
@[fun_prop] protected theorem PT.termOfToks {l : α → List ℕ} (hl : PT l) :
    PT (fun a => Term.ofToks (l a)) :=
  PT.headD (PT.fst (PT.parseFoldr hl)) (PT.const _)

/-- Parsing an arbitrary token list as a formula is polynomial-time. -/
@[fun_prop] protected theorem PT.formulaOfToks {l : α → List ℕ} (hl : PT l) :
    PT (fun a => Formula.ofToks (l a)) :=
  PT.headD (PT.snd (PT.parseFoldr hl)) (PT.const _)

end Parse

end ArtGallery

end
