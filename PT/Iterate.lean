module

public import PT.Basic

/-!
# Bounded iteration

`PT.iterate`: iterating a polynomial-time step function (with access to an environment
`a : α`) a polynomial-time computable number of times is polynomial-time, provided all
intermediate states have polynomially bounded size.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β σ : Type} [Code α] [Code β] [Code σ]

/-- **Bounded iteration with an environment.** -/
protected theorem PT.iterate {step : α → σ → σ} {init : α → σ} {n : α → Nat}
    (hstep : PT (fun p : α × σ => step p.1 p.2)) (hinit : PT init) (hn : PT n)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a i, i ≤ n a → size ((step a)^[i] (init a)) ≤ bound (size a)) :
    PT (fun a => (step a)^[n a] (init a)) := by
  obtain ⟨S, hS, hS'⟩ := hstep
  obtain ⟨I, hI, hI'⟩ := hinit
  obtain ⟨N, hN, hN'⟩ := hn
  obtain ⟨T, hT, hT'⟩ := exists_take α
  obtain ⟨Dr, hDr, hDr'⟩ := exists_drop α
  have key : ∀ (a : α) (i : Nat) (s : σ),
      (fun w => T w ++ S w)^[i] (enc a ++ enc s) = enc a ++ enc ((step a)^[i] s) := by
    intro a i
    induction i with
    | zero => intro s; rfl
    | succ i ih =>
      intro s
      have h1 : T (enc a ++ enc s) ++ S (enc a ++ enc s) = enc a ++ enc (step a s) := by
        rw [hT']
        exact congrArg _ (hS' (a, s))
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [h1]
      exact ih (step a s)
  have hcount : ∀ a : α, (N (enc a)).tail.length = n a := fun a => by
    rw [hN', enc_nat, List.length_tail, length_writeNat]
    rfl
  obtain ⟨G, hG, hG'⟩ := polyTime_iterate_on (fun x => ∃ a : α, x = enc a)
    (step := fun w => T w ++ S w) (init := fun x => x ++ I x) (count := fun x => (N x).tail)
    (polyTime_append hT hS) (polyTime_append polyTime_id hI) (polyTime_tail hN)
    (fun m => m + bound m) (PolynomialBound.identity.add hbound) (by
      rintro x ⟨a, rfl⟩ i hi
      rw [hcount] at hi
      have := hsize a i hi
      simp only [hI', key, List.length_append]
      exact Nat.add_le_add_left this _)
  refine ⟨fun x => Dr (G x), polyTime_comp hDr hG, fun a => ?_⟩
  simp only [hG' _ ⟨a, rfl⟩, hcount, hI', key, hDr']

/-- Bounded iteration of a fixed polynomial-time function. -/
protected theorem PT.iterate_const {step : σ → σ} {init : α → σ} {n : α → Nat}
    (hstep : PT step) (hinit : PT init) (hn : PT n)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a i, i ≤ n a → size (step^[i] (init a)) ≤ bound (size a)) :
    PT (fun a => step^[n a] (init a)) :=
  PT.iterate (step := fun _ => step) (hstep.comp PT.snd') hinit hn bound hbound hsize

end Complexity.PT
