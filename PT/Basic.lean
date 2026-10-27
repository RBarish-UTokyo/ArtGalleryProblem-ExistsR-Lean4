module

public import PT.Code
public import Mathlib.Tactic.FunProp

/-!
# Polynomial-time functions on coded data

`PT f` says that `f : α → β` is computed, on codes, by a polynomial-time word function.
This file contains the structural lemmas (identity, constants, composition, pairing,
projections, branching), the Boolean connectives and the size bound `PT.size_le`.

All lemmas are stated in the form expected by Mathlib's `fun_prop` tactic and tagged
`@[fun_prop]`, so goals such as `PT (fun p : Nat × Bool => if p.2 then (p.1, p.1) else (0, p.1))`
are proved by `fun_prop`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ δ ε : Type} [Code α] [Code β] [Code γ] [Code δ] [Code ε]

/-- `f` is polynomial-time computable on codes. -/
@[fun_prop] def PT {α β : Type} [Code α] [Code β] (f : α → β) : Prop :=
  ∃ F : Word → Word, PolyTime F ∧ ∀ a, F (Code.enc a) = Code.enc (f a)

/-- Congruence under pointwise equality. -/
protected theorem PT.of_eq {f g : α → β} (hf : PT f) (h : ∀ a, f a = g a) : PT g := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨F, hF, fun a => by simp only [hF', h]⟩

protected theorem PT.congr {f g : α → β} (h : ∀ a, f a = g a) : PT f ↔ PT g :=
  ⟨fun hf => hf.of_eq h, fun hg => hg.of_eq fun a => (h a).symm⟩

/-! ### Structural lemmas -/

@[fun_prop] protected theorem PT.id : PT (fun a : α => a) := ⟨fun x => x, polyTime_id, fun _ => rfl⟩

protected theorem PT.id' : PT (id : α → α) := PT.id

@[fun_prop] protected theorem PT.const (b : β) : PT (fun _ : α => b) :=
  ⟨fun _ => enc b, polyTime_const _, fun _ => rfl⟩

@[fun_prop] protected theorem PT.comp {f : β → γ} {g : α → β} (hf : PT f) (hg : PT g) :
    PT (fun a => f (g a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  exact ⟨fun x => F (G x), polyTime_comp hF hG, fun a => by simp only [hG', hF']⟩

protected theorem PT.comp' {f : β → γ} {g : α → β} (hf : PT f) (hg : PT g) : PT (f ∘ g) := hf.comp hg

@[fun_prop] protected theorem PT.pair {f : α → β} {g : α → γ} (hf : PT f) (hg : PT g) :
    PT (fun a => (f a, g a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  exact ⟨fun x => F x ++ G x, polyTime_append hF hG, fun a => by simp only [hF', hG', enc_pair]⟩

@[fun_prop] protected theorem PT.fst {f : α → β × γ} (hf : PT f) : PT (fun a => (f a).1) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨T, hT, hT'⟩ := exists_take β
  exact ⟨fun x => T (F x), polyTime_comp hT hF, fun a => by simp only [hF', enc_prod, hT']⟩

@[fun_prop] protected theorem PT.snd {f : α → β × γ} (hf : PT f) : PT (fun a => (f a).2) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨T, hT, hT'⟩ := exists_drop β
  exact ⟨fun x => T (F x), polyTime_comp hT hF, fun a => by simp only [hF', enc_prod, hT']⟩

protected theorem PT.fst' : PT (Prod.fst : α × β → α) := PT.fst PT.id

protected theorem PT.snd' : PT (Prod.snd : α × β → β) := PT.snd PT.id

@[fun_prop] protected theorem PT.swap {f : α → β × γ} (hf : PT f) : PT (fun a => (f a).swap) :=
  PT.pair (PT.snd hf) (PT.fst hf)

/-- Binary functions: from the uncurried form to the compositional form. -/
protected theorem PT.comp₂ {h : β → γ → δ} (hh : PT (fun p : β × γ => h p.1 p.2))
    {f : α → β} {g : α → γ} (hf : PT f) (hg : PT g) : PT (fun a => h (f a) (g a)) :=
  hh.comp (hf.pair hg)

/-- Ternary functions: from the uncurried form to the compositional form. -/
protected theorem PT.comp₃ {h : β → γ → δ → ε} (hh : PT (fun p : β × γ × δ => h p.1 p.2.1 p.2.2))
    {f : α → β} {g : α → γ} {k : α → δ} (hf : PT f) (hg : PT g) (hk : PT k) :
    PT (fun a => h (f a) (g a) (k a)) :=
  hh.comp (hf.pair (hg.pair hk))

/-- A binary function in compositional form is polynomial-time in uncurried form. -/
protected theorem PT.uncurry {h : β → γ → δ}
    (hh : ∀ {f : β × γ → β} {g : β × γ → γ}, PT f → PT g → PT (fun a => h (f a) (g a))) :
    PT (fun p : β × γ => h p.1 p.2) :=
  hh PT.fst' PT.snd'

/-! ### Branching -/

/-- Branching on a polynomial-time Boolean test. -/
protected theorem PT.ite {c : α → Bool} {f g : α → β} (hc : PT c) (hf : PT f) (hg : PT g) :
    PT (fun a => if c a then f a else g a) := by
  obtain ⟨C, hC, hC'⟩ := hc
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  refine ⟨fun x => if C x = [true] then F x else G x, polyTime_ite hC hF hG, fun a => ?_⟩
  simp only [hC', hF', hG', enc_bool]
  cases c a <;> simp

@[fun_prop] protected theorem PT.cond {c : α → Bool} {f g : α → β} (hc : PT c) (hf : PT f) (hg : PT g) :
    PT (fun a => bif c a then f a else g a) :=
  (PT.ite hc hf hg).of_eq fun a => by cases c a <;> rfl

/-- Branching on a decidable proposition whose truth value is polynomial-time. -/
@[fun_prop] protected theorem PT.ite_prop {P : α → Prop} [inst : ∀ a, Decidable (P a)] {f g : α → β}
    (hP : PT (fun a => decide (P a))) (hf : PT f) (hg : PT g) :
    PT (fun a => if P a then f a else g a) :=
  (PT.ite hP hf hg).of_eq fun a => by by_cases h : P a <;> simp [h]

/-- Dependent branching, with both branches polynomial-time as total functions. -/
protected theorem PT.dite_of_eq {P : α → Prop} [inst : ∀ a, Decidable (P a)] {f g : α → β}
    {t : ∀ a, P a → β} {e : ∀ a, ¬ P a → β}
    (hP : PT (fun a => decide (P a))) (hf : PT f) (hg : PT g)
    (ht : ∀ a h, t a h = f a) (he : ∀ a h, e a h = g a) :
    PT (fun a => if h : P a then t a h else e a h) :=
  (PT.ite_prop hP hf hg).of_eq fun a => by by_cases h : P a <;> simp [h, ht, he]

/-! ### Booleans -/

@[fun_prop] protected theorem PT.not {f : α → Bool} (hf : PT f) : PT (fun a => !f a) :=
  (PT.ite hf (PT.const false) (PT.const true)).of_eq fun a => by cases f a <;> rfl

@[fun_prop] protected theorem PT.and {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT (fun a => f a && g a) :=
  (PT.ite hf hg (PT.const false)).of_eq fun a => by cases f a <;> simp

@[fun_prop] protected theorem PT.or {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT (fun a => f a || g a) :=
  (PT.ite hf (PT.const true) hg).of_eq fun a => by cases f a <;> simp

@[fun_prop] protected theorem PT.xor {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT (fun a => Bool.xor (f a) (g a)) :=
  (PT.ite hf (PT.not hg) hg).of_eq fun a => by cases f a <;> simp

/-- Equality test on Booleans. -/
@[fun_prop] protected theorem PT.boolBeq {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT (fun a => f a == g a) :=
  (PT.ite hf hg (PT.not hg)).of_eq fun a => by cases f a <;> cases g a <;> rfl

@[fun_prop] protected theorem PT.boolBne {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT (fun a => f a != g a) :=
  (PT.xor hf hg).of_eq fun a => by cases f a <;> cases g a <;> rfl

/-! ### `decide` -/

/-- `decide` of a Boolean coerced to a proposition.

Not tagged `@[fun_prop]`: since Lean v4.35 (where `decide (b = true)` unfolds to `b`) the pattern
`decide (?c a = true)` unifies with every `decide P`, which derails `fun_prop`.  `fun_prop` handles
these goals with `PT.decide_boolEq`. -/
protected theorem PT.decide_eq_true {c : α → Bool} [inst : ∀ a, Decidable (c a = true)]
    (hc : PT c) : PT (fun a => decide (c a = true)) :=
  hc.of_eq fun a => by simp

@[fun_prop] protected theorem PT.decide_eq_false {c : α → Bool} [inst : ∀ a, Decidable (c a = false)]
    (hc : PT c) : PT (fun a => decide (c a = false)) :=
  (PT.not hc).of_eq fun a => by by_cases h : c a = false <;> simp_all

@[fun_prop] protected theorem PT.decide_and {P Q : α → Prop} [∀ a, Decidable (P a)] [∀ a, Decidable (Q a)]
    [inst : ∀ a, Decidable (P a ∧ Q a)]
    (hP : PT (fun a => decide (P a))) (hQ : PT (fun a => decide (Q a))) :
    PT (fun a => decide (P a ∧ Q a)) :=
  (PT.and hP hQ).of_eq fun a => by simp

@[fun_prop] protected theorem PT.decide_or {P Q : α → Prop} [∀ a, Decidable (P a)] [∀ a, Decidable (Q a)]
    [inst : ∀ a, Decidable (P a ∨ Q a)]
    (hP : PT (fun a => decide (P a))) (hQ : PT (fun a => decide (Q a))) :
    PT (fun a => decide (P a ∨ Q a)) :=
  (PT.or hP hQ).of_eq fun a => by simp

@[fun_prop] protected theorem PT.decide_not {P : α → Prop} [∀ a, Decidable (P a)]
    [inst : ∀ a, Decidable (¬ P a)]
    (hP : PT (fun a => decide (P a))) : PT (fun a => decide (¬ P a)) :=
  (PT.not hP).of_eq fun a => by simp

/-- Equality of Booleans as a decidable proposition. -/
@[fun_prop] protected theorem PT.decide_boolEq {f g : α → Bool} [inst : ∀ a, Decidable (f a = g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a = g a)) :=
  (PT.boolBeq hf hg).of_eq fun a => by by_cases h : f a = g a <;> simp [h]

/-- Change the decidability instance, or the proposition up to equivalence. -/
protected theorem PT.decide_congr {P Q : α → Prop} [∀ a, Decidable (P a)] [∀ a, Decidable (Q a)]
    (hP : PT (fun a => decide (P a))) (h : ∀ a, P a ↔ Q a) : PT (fun a => decide (Q a)) :=
  hP.of_eq fun a => by simp [h a]

/-! ### Size bounds -/

/-- The size of the value of a polynomial-time function is polynomially bounded
(`powerBound c k` is monotone: `powerBound_mono`). -/
protected theorem PT.size_le {f : α → β} (hf : PT f) :
    ∃ c k, ∀ a, size (f a) ≤ powerBound c k (size a) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨c, k, h⟩ := polyTime_length_le hF
  refine ⟨c, k, fun a => ?_⟩
  have := h (enc a)
  rwa [hF'] at this

/-- The size of the value of a polynomial-time function is polynomially bounded. -/
theorem size_le_of_PT {f : α → β} (hf : PT f) :
    ∃ p : Nat → Nat, PolynomialBound p ∧ ∀ a, size (f a) ≤ p (size a) := by
  obtain ⟨c, k, h⟩ := hf.size_le
  exact ⟨powerBound c k, PolynomialBound.power c k, h⟩

/-- A monotone polynomial bound on the size of the value of a polynomial-time function. -/
protected theorem PT.size_le_mono {f : α → β} (hf : PT f) :
    ∃ p : Nat → Nat, PolynomialBound p ∧ (∀ m n, m ≤ n → p m ≤ p n) ∧
      ∀ a, size (f a) ≤ p (size a) := by
  obtain ⟨c, k, h⟩ := hf.size_le
  exact ⟨powerBound c k, PolynomialBound.power c k, fun _ _ hmn => powerBound_mono c k hmn, h⟩

/-! ### Transported codes -/

section Transport

variable {σ : Type}

/-- Into a type coded through `Code.ofInj i j h`: it suffices to compute the image under
`i`. -/
protected theorem PT.ofInj_mk (i : σ → β) (j : β → σ) (h : ∀ s, j (i s) = s) {f : α → σ}
    (hf : PT (fun a => i (f a))) : @PT α σ _ (Code.ofInj i j h) f := hf

/-- Out of a type coded through `Code.ofInj i j h`: it suffices to compute `f ∘ j`. -/
protected theorem PT.ofInj_elim (i : σ → β) (j : β → σ) (h : ∀ s, j (i s) = s) {f : σ → γ}
    (hf : PT (fun b => f (j b))) : @PT σ γ (Code.ofInj i j h) _ f := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨F, hF, fun s => by
    have := hF' (i s)
    simp only [h] at this
    exact this⟩

/-- The coding map of a transported code is polynomial-time. -/
protected theorem PT.ofInj_to (i : σ → β) (j : β → σ) (h : ∀ s, j (i s) = s) :
    @PT σ β (Code.ofInj i j h) _ i :=
  ⟨fun x => x, polyTime_id, fun _ => rfl⟩

end Transport

/-! ### SAT literals -/

@[fun_prop] protected theorem PT.literalVar {f : α → SAT.Literal} (hf : PT f) : PT (fun a => (f a).var) := by
  have h : PT (fun l : SAT.Literal => l.var) :=
    PT.ofInj_elim (fun l : SAT.Literal => (l.positive, l.var)) (fun p => ⟨p.2, p.1⟩)
      (fun _ => rfl) (PT.snd PT.id)
  exact h.comp hf

@[fun_prop] protected theorem PT.literalPositive {f : α → SAT.Literal} (hf : PT f) :
    PT (fun a => (f a).positive) := by
  have h : PT (fun l : SAT.Literal => l.positive) :=
    PT.ofInj_elim (fun l : SAT.Literal => (l.positive, l.var)) (fun p => ⟨p.2, p.1⟩)
      (fun _ => rfl) (PT.fst PT.id)
  exact h.comp hf

@[fun_prop] protected theorem PT.literalMk {v : α → Nat} {p : α → Bool} (hv : PT v) (hp : PT p) :
    PT (fun a => (⟨v a, p a⟩ : SAT.Literal)) :=
  PT.ofInj_mk (fun l : SAT.Literal => (l.positive, l.var)) (fun p => ⟨p.2, p.1⟩)
    (fun _ => rfl) (PT.pair hp hv)

end Complexity.PT
