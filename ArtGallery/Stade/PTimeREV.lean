module

public import ArtGallery.PTime.ETRtoINV
public import ArtGallery.ETR.REV

/-!
# The reduction ETR → ETR-INV-REV is polynomial-time

* `Code ETRINVREV.Constraint` through `ETRINVREV.Constraint.toSum`;
* case analysis `ETRINVREV.Constraint.elim` with `PT.revElim`, and the constructors
  `PT.revOne`, `PT.revInvGe`, `PT.revInvRevLe`, `PT.revAddLe`, `PT.revAddGe`;
* `PT.toREV` (the translation `REV.toREV` is a `blocks` map) and **`PT.etrToREV`**,
  `PT.etrToREVVars`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETRINVREV

/-- A constraint as a sum: `one`, `invGe`, `invRevLe`, `addLe`, `addGe`. -/
def Constraint.toSum : Constraint → ℕ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ)
  | .one x => .inl x
  | .invGe x y => .inr (.inl (x, y))
  | .invRevLe x y => .inr (.inr (.inl (x, y)))
  | .addLe x y z => .inr (.inr (.inr (.inl (x, y, z))))
  | .addGe x y z => .inr (.inr (.inr (.inr (x, y, z))))

/-- The inverse of `Constraint.toSum`. -/
def Constraint.ofSum : ℕ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) → Constraint
  | .inl x => .one x
  | .inr (.inl (x, y)) => .invGe x y
  | .inr (.inr (.inl (x, y))) => .invRevLe x y
  | .inr (.inr (.inr (.inl (x, y, z)))) => .addLe x y z
  | .inr (.inr (.inr (.inr (x, y, z)))) => .addGe x y z

theorem Constraint.ofSum_toSum (c : Constraint) : Constraint.ofSum c.toSum = c := by
  cases c <;> rfl

/-- Constraints are coded as sums. -/
instance instCodeConstraint : Code Constraint :=
  Code.ofInj Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum

/-- Case analysis on a constraint. -/
def Constraint.elim {β : Type} (f₁ : ℕ → β) (f₂ f₃ : ℕ → ℕ → β) (f₄ f₅ : ℕ → ℕ → ℕ → β) :
    Constraint → β
  | .one x => f₁ x
  | .invGe x y => f₂ x y
  | .invRevLe x y => f₃ x y
  | .addLe x y z => f₄ x y z
  | .addGe x y z => f₅ x y z

theorem Constraint.elim_eq {β : Type} (f₁ : ℕ → β) (f₂ f₃ : ℕ → ℕ → β) (f₄ f₅ : ℕ → ℕ → ℕ → β)
    (c : Constraint) : c.elim f₁ f₂ f₃ f₄ f₅ =
      Sum.elim f₁ (Sum.elim (fun q => f₂ q.1 q.2) (Sum.elim (fun q => f₃ q.1 q.2)
        (Sum.elim (fun q => f₄ q.1 q.2.1 q.2.2) (fun q => f₅ q.1 q.2.1 q.2.2)))) c.toSum := by
  cases c <;> rfl

/-- Every function on constraints is a case analysis. -/
theorem Constraint.eq_elim {β : Type} (f : Constraint → β) (c : Constraint) :
    f c = c.elim (fun x => f (.one x)) (fun x y => f (.invGe x y)) (fun x y => f (.invRevLe x y))
      (fun x y z => f (.addLe x y z)) (fun x y z => f (.addGe x y z)) := by
  cases c <;> rfl

end ETRINVREV

open ETRINVREV

section PTLemmas

variable {α β : Type} [Code α] [Code β]

@[fun_prop] protected theorem PT.revToSum {c : α → Constraint} (hc : PT c) :
    PT (fun a => (c a).toSum) :=
  (PT.ofInj_to Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum).comp hc

theorem PT.rev_of_toSum {c : α → Constraint} (h : PT (fun a => (c a).toSum)) : PT c :=
  PT.ofInj_mk Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum h

@[fun_prop] protected theorem PT.revOne {x : α → ℕ} (hx : PT x) :
    PT (fun a => Constraint.one (x a)) :=
  PT.rev_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.revInvGe {x y : α → ℕ} (hx : PT x) (hy : PT y) :
    PT (fun a => Constraint.invGe (x a) (y a)) :=
  PT.rev_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.revInvRevLe {x y : α → ℕ} (hx : PT x) (hy : PT y) :
    PT (fun a => Constraint.invRevLe (x a) (y a)) :=
  PT.rev_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.revAddLe {x y z : α → ℕ} (hx : PT x) (hy : PT y) (hz : PT z) :
    PT (fun a => Constraint.addLe (x a) (y a) (z a)) :=
  PT.rev_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.revAddGe {x y z : α → ℕ} (hx : PT x) (hy : PT y) (hz : PT z) :
    PT (fun a => Constraint.addGe (x a) (y a) (z a)) :=
  PT.rev_of_toSum (by simp only [Constraint.toSum]; fun_prop)

/-- Case analysis on a constraint (the branches in uncurried form). -/
@[fun_prop] protected theorem PT.revElim {c : α → Constraint} {f₁ : α → ℕ → β}
    {f₂ f₃ : α → ℕ → ℕ → β} {f₄ f₅ : α → ℕ → ℕ → ℕ → β}
    (h₁ : PT (fun p : α × ℕ => f₁ p.1 p.2))
    (h₂ : PT (fun p : α × ℕ × ℕ => f₂ p.1 p.2.1 p.2.2))
    (h₃ : PT (fun p : α × ℕ × ℕ => f₃ p.1 p.2.1 p.2.2))
    (h₄ : PT (fun p : α × ℕ × ℕ × ℕ => f₄ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h₅ : PT (fun p : α × ℕ × ℕ × ℕ => f₅ p.1 p.2.1 p.2.2.1 p.2.2.2)) (hc : PT c) :
    PT (fun a => (c a).elim (f₁ a) (f₂ a) (f₃ a) (f₄ a) (f₅ a)) := by
  have e : ∀ {γ : Type} [Code γ], PT (fun p : (α × γ) => p.1) := fun {_ _} => PT.fst PT.id
  have h : PT (fun a => Sum.elim (f₁ a) (Sum.elim (fun q => f₂ a q.1 q.2) (Sum.elim
      (fun q => f₃ a q.1 q.2) (Sum.elim (fun q => f₄ a q.1 q.2.1 q.2.2)
        (fun q => f₅ a q.1 q.2.1 q.2.2)))) (c a).toSum) := by
    refine PT.sumElim h₁ (PT.sumElim (h₂.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
      (PT.sumElim (h₃.comp (PT.pair (PT.fst (PT.fst (PT.fst PT.id))) (PT.snd PT.id)))
        (PT.sumElim (h₄.comp (PT.pair (PT.fst (PT.fst (PT.fst (PT.fst PT.id)))) (PT.snd PT.id)))
          (h₅.comp (PT.pair (PT.fst (PT.fst (PT.fst (PT.fst PT.id)))) (PT.snd PT.id))) PT.snd')
        PT.snd') PT.snd') (PT.revToSum hc)
  exact h.of_eq fun a => (Constraint.elim_eq _ _ _ _ _ (c a)).symm

/-- A function on constraints given by its values on the constructors. -/
theorem PT.revFun {f : Constraint → β}
    (h₁ : PT (fun x : ℕ => f (.one x)))
    (h₂ : PT (fun p : ℕ × ℕ => f (.invGe p.1 p.2)))
    (h₃ : PT (fun p : ℕ × ℕ => f (.invRevLe p.1 p.2)))
    (h₄ : PT (fun p : ℕ × ℕ × ℕ => f (.addLe p.1 p.2.1 p.2.2)))
    (h₅ : PT (fun p : ℕ × ℕ × ℕ => f (.addGe p.1 p.2.1 p.2.2))) : PT f := by
  have h := PT.revElim (c := fun c : Constraint => c) (f₁ := fun _ x => f (.one x))
    (f₂ := fun _ x y => f (.invGe x y)) (f₃ := fun _ x y => f (.invRevLe x y))
    (f₄ := fun _ x y z => f (.addLe x y z)) (f₅ := fun _ x y z => f (.addGe x y z))
    (h₁.comp PT.snd') (h₂.comp PT.snd') (h₃.comp PT.snd') (h₄.comp PT.snd') (h₅.comp PT.snd')
    PT.id
  exact h.of_eq fun c => (Constraint.eq_elim f c).symm

theorem revConstraint_eq (K F : ℕ) (c : ETRINV.Constraint) : REV.revConstraint K F c = c.elim
    (fun x => [.one x]) (fun x y z => [.addLe x y z, .addGe x y z])
    (fun a b => [.invGe a b, .invRevLe a (F + 3),
      .addLe F F b, .addGe F F b, .addLe F (F + 1) (K + 1), .addGe F (F + 1) (K + 1),
      .addLe (F + 1) (F + 1) (F + 2), .addGe (F + 1) (F + 1) (F + 2),
      .addLe (F + 3) K (F + 2), .addGe (F + 3) K (F + 2)]) := by
  cases c <;> rfl

/-- The translation `REV.toREV` is polynomial-time. -/
@[fun_prop] protected theorem PT.toREV {K F : α → ℕ} {Φ : α → List ETRINV.Constraint}
    (hK : PT K) (hF : PT F) (hΦ : PT Φ) : PT (fun a => REV.toREV (K a) (F a) (Φ a)) := by
  unfold REV.toREV
  refine PT.blocks ?_ (PT.const 0) hΦ
  simp only [revConstraint_eq]
  fun_prop

/-- The variable bound `etrToINVVars` is polynomial-time. -/
@[fun_prop] protected theorem PT.etrToINVVars {φ : α → ETR.Formula} (hφ : PT φ) :
    PT (fun a => etrToINVVars (φ a)) := by
  unfold etrToINVVars etrScaledVars etrScaled etrK Gate.ballExp
  fun_prop

/-- **The reduction from ETR to ETR-INV-REV is polynomial-time** (on formulas). -/
@[fun_prop] protected theorem PT.etrToREV {φ : α → ETR.Formula} (hφ : PT φ) :
    PT (fun a => etrToREV (φ a)) := by
  unfold etrToREV etrHalfIndex etrScaledVars etrK Gate.ballExp
  fun_prop

/-- The variable bound `etrToREVVars` is polynomial-time. -/
@[fun_prop] protected theorem PT.etrToREVVars {φ : α → ETR.Formula} (hφ : PT φ) :
    PT (fun a => etrToREVVars (φ a)) := by
  unfold etrToREVVars
  fun_prop

end PTLemmas

end ArtGallery

end
