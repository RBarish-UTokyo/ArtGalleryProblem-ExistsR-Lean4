module

public import PT.Basic

/-!
# Polynomial-time functions on options and sums

The case-analysis combinators `PT.optionElim` and `PT.sumElim` take the branch functions in
uncurried form (`PT (fun p : α × β => f p.1 p.2)`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ δ : Type} [Code α] [Code β] [Code γ] [Code δ]

/-! ### Options -/

@[fun_prop] protected theorem PT.some {f : α → β} (hf : PT f) : PT (fun a => some (f a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => true :: F x, polyTime_cons true hF, fun a => by simp only [hF', enc_some]⟩

protected theorem PT.none : PT (fun _ : α => (none : Option β)) := PT.const none

/-- Case analysis on an option. -/
@[fun_prop] protected theorem PT.optionElim {o : α → Option β} {d : α → γ} {f : α → β → γ}
    (ho : PT o) (hd : PT d) (hf : PT (fun p : α × β => f p.1 p.2)) :
    PT (fun a => (o a).elim (d a) (f a)) := by
  obtain ⟨O, hO, hO'⟩ := ho
  obtain ⟨D, hD, hD'⟩ := hd
  obtain ⟨F, hF, hF'⟩ := hf
  refine ⟨fun x => if (O x).take 1 = [true] then F (x ++ (O x).tail) else D x,
    polyTime_ite (polyTime_take_one hO)
      (polyTime_comp hF (polyTime_append polyTime_id (polyTime_tail hO))) hD, fun a => ?_⟩
  simp only [hO', hD']
  cases h : o a with
  | none => simp
  | some b =>
    have := hF' (a, b)
    simp only [enc_pair] at this
    simp [this]

/-- Case analysis on an option, in equational form: `g` is given by `d` where `o` is `none`
and by `f` where it is `some`.  This is the robust way to treat a function defined by a
`match` (prove the two equations with `intro a h; simp [h]`). -/
protected theorem PT.of_optionCases {o : α → Option β} {d : α → γ} {f : α → β → γ} {g : α → γ}
    (ho : PT o) (hd : PT d) (hf : PT (fun p : α × β => f p.1 p.2))
    (hnone : ∀ a, o a = none → g a = d a) (hsome : ∀ a b, o a = some b → g a = f a b) :
    PT g :=
  (PT.optionElim ho hd hf).of_eq fun a => by
    cases h : o a with
    | none => exact (hnone a h).symm
    | some b => exact (hsome a b h).symm

/-- Case analysis on an option, in `match` form.  (`apply` only unifies this with a goal whose
`match` was compiled to the same matcher, i.e. with a generic element type; otherwise use
`PT.of_optionCases` or `PT.optionElim`.) -/
protected theorem PT.optionCases {o : α → Option β} {d : α → γ} {f : α → β → γ}
    (ho : PT o) (hd : PT d) (hf : PT (fun p : α × β => f p.1 p.2)) :
    PT (fun a => match o a with
      | none => d a
      | some b => f a b) :=
  PT.of_optionCases ho hd hf (fun a h => by simp only [h]) (fun a b h => by simp only [h])

@[fun_prop] protected theorem PT.isSome {o : α → Option β} (ho : PT o) :
    PT (fun a => (o a).isSome) :=
  (PT.optionElim ho (PT.const false) (PT.const true)).of_eq fun a => by cases o a <;> rfl

@[fun_prop] protected theorem PT.isNone {o : α → Option β} (ho : PT o) :
    PT (fun a => (o a).isNone) :=
  (PT.optionElim ho (PT.const true) (PT.const false)).of_eq fun a => by cases o a <;> rfl

@[fun_prop] protected theorem PT.getD {o : α → Option β} {d : α → β} (ho : PT o) (hd : PT d) :
    PT (fun a => (o a).getD (d a)) :=
  (PT.optionElim ho hd PT.snd').of_eq fun a => by cases o a <;> rfl

@[fun_prop] protected theorem PT.optionMap {o : α → Option β} {f : α → β → γ}
    (ho : PT o) (hf : PT (fun p : α × β => f p.1 p.2)) :
    PT (fun a => (o a).map (f a)) :=
  (PT.optionElim ho (PT.const none) (PT.some hf)).of_eq fun a => by cases o a <;> rfl

@[fun_prop] protected theorem PT.optionBind {o : α → Option β} {f : α → β → Option γ}
    (ho : PT o) (hf : PT (fun p : α × β => f p.1 p.2)) :
    PT (fun a => (o a).bind (f a)) :=
  (PT.optionElim ho (PT.const none) hf).of_eq fun a => by cases o a <;> rfl

@[fun_prop] protected theorem PT.optionOr {o o' : α → Option β} (ho : PT o) (ho' : PT o') :
    PT (fun a => (o a).or (o' a)) :=
  (PT.optionElim ho ho' (PT.some PT.snd')).of_eq fun a => by cases o a <;> rfl

/-! ### Sums -/

@[fun_prop] protected theorem PT.inl {f : α → β} (hf : PT f) :
    PT (fun a => (Sum.inl (f a) : β ⊕ γ)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => false :: F x, polyTime_cons false hF, fun a => by simp only [hF', enc_inl]⟩

@[fun_prop] protected theorem PT.inr {f : α → γ} (hf : PT f) :
    PT (fun a => (Sum.inr (f a) : β ⊕ γ)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => true :: F x, polyTime_cons true hF, fun a => by simp only [hF', enc_inr]⟩

/-- Case analysis on a sum. -/
@[fun_prop] protected theorem PT.sumElim {s : α → β ⊕ γ} {f : α → β → δ} {g : α → γ → δ}
    (hf : PT (fun p : α × β => f p.1 p.2)) (hg : PT (fun p : α × γ => g p.1 p.2)) (hs : PT s) :
    PT (fun a => Sum.elim (f a) (g a) (s a)) := by
  obtain ⟨S, hS, hS'⟩ := hs
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  refine ⟨fun x => if (S x).take 1 = [true] then G (x ++ (S x).tail) else F (x ++ (S x).tail),
    polyTime_ite (polyTime_take_one hS)
      (polyTime_comp hG (polyTime_append polyTime_id (polyTime_tail hS)))
      (polyTime_comp hF (polyTime_append polyTime_id (polyTime_tail hS))), fun a => ?_⟩
  simp only [hS']
  cases h : s a with
  | inl b =>
    have := hF' (a, b)
    simp only [enc_pair] at this
    simp [this]
  | inr c =>
    have := hG' (a, c)
    simp only [enc_pair] at this
    simp [this]

/-- Case analysis on a sum, in equational form. -/
protected theorem PT.of_sumCases {s : α → β ⊕ γ} {f : α → β → δ} {g : α → γ → δ} {k : α → δ}
    (hs : PT s) (hf : PT (fun p : α × β => f p.1 p.2)) (hg : PT (fun p : α × γ => g p.1 p.2))
    (hinl : ∀ a b, s a = .inl b → k a = f a b) (hinr : ∀ a c, s a = .inr c → k a = g a c) :
    PT k :=
  (PT.sumElim hf hg hs).of_eq fun a => by
    cases h : s a with
    | inl b => exact (hinl a b h).symm
    | inr c => exact (hinr a c h).symm

/-- Case analysis on a sum, in `match` form (see the remark at `PT.optionCases`). -/
protected theorem PT.sumCases {s : α → β ⊕ γ} {f : α → β → δ} {g : α → γ → δ}
    (hs : PT s) (hf : PT (fun p : α × β => f p.1 p.2)) (hg : PT (fun p : α × γ => g p.1 p.2)) :
    PT (fun a => match s a with
      | .inl b => f a b
      | .inr c => g a c) :=
  PT.of_sumCases hs hf hg (fun a b h => by simp only [h]) (fun a c h => by simp only [h])

@[fun_prop] protected theorem PT.isLeft {s : α → β ⊕ γ} (hs : PT s) :
    PT (fun a => (s a).isLeft) :=
  (PT.sumElim (PT.const true) (PT.const false) hs).of_eq fun a => by cases s a <;> rfl

@[fun_prop] protected theorem PT.isRight {s : α → β ⊕ γ} (hs : PT s) :
    PT (fun a => (s a).isRight) :=
  (PT.sumElim (PT.const false) (PT.const true) hs).of_eq fun a => by cases s a <;> rfl

end Complexity.PT
