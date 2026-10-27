module

public import ArtGallery.Spec
public import PT.All

/-!
# Helpers for scanning binary words

* `ArtGallery.leadOnes r`: the number of leading `true`s of `r` (a unary numeral is read as
  `leadOnes r`, and the rest after it is `r.drop (leadOnes r + 1)`), with `PT.leadOnes`;
* `ArtGallery.iterate_invariant`: an invariant of the iterates of a function, used to bound the
  sizes of the states of the scans (for `PT.iterate`);
* small facts on `ArtGallery.unary`, `List.drop`, suffixes.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

/-- The number of leading `true`s of a word. -/
def leadOnes (r : Word) : ℕ := (r.takeWhile (fun b => b)).length

theorem leadOnes_le (r : Word) : leadOnes r ≤ r.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix _)

@[simp] theorem leadOnes_replicate_false (n : ℕ) (r : Word) :
    leadOnes (List.replicate n true ++ false :: r) = n := by
  induction n with
  | zero => simp [leadOnes]
  | succ n ih =>
    unfold leadOnes at ih ⊢
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos (by rfl),
      List.length_cons, ih]

@[simp] theorem leadOnes_unary_append (n : ℕ) (r : Word) :
    leadOnes (ArtGallery.unary n ++ r) = n := by
  simp [ArtGallery.unary]

theorem drop_replicate_false (n : ℕ) (r : Word) :
    (List.replicate n true ++ false :: r).drop (n + 1) = r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.drop_succ_cons, ih]

@[simp] theorem drop_unary_append (n : ℕ) (r : Word) :
    (ArtGallery.unary n ++ r).drop (n + 1) = r := by
  simp only [ArtGallery.unary, List.append_assoc, List.singleton_append]
  exact drop_replicate_false n r

theorem length_unary (n : ℕ) : (ArtGallery.unary n).length = n + 1 := by
  simp [ArtGallery.unary]

/-- `ArtGallery.unary` is the unary `Code` of a natural number. -/
theorem unary_eq_enc (n : ℕ) : ArtGallery.unary n = (Code.enc n : Word) := by
  rw [enc_nat_eq]
  rfl

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.leadOnes {r : α → Word} (hr : PT r) :
    PT (fun a => leadOnes (r a)) := by
  unfold leadOnes
  fun_prop

@[fun_prop] protected theorem PT.artUnary {n : α → ℕ} (hn : PT n) :
    PT (fun a => ArtGallery.unary (n a)) := by
  unfold ArtGallery.unary
  fun_prop

/-- An invariant of the iterates of `f`, indexed by the number of steps. -/
theorem iterate_invariant {σ : Type} (f : σ → σ) (P : ℕ → σ → Prop) (x : σ) (h0 : P 0 x)
    (hs : ∀ i s, P i s → P (i + 1) (f s)) : ∀ i, P i (f^[i] x) := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih => rw [Function.iterate_succ_apply']; exact hs i _ ih

/-- Iterating from a fixed point. -/
theorem iterate_fixed {σ : Type} (f : σ → σ) (x : σ) (h : f x = x) (n : ℕ) : f^[n] x = x :=
  Function.iterate_fixed h n

/-- A suffix of an append. -/
theorem suffix_append_cases {β : Type} {l l₁ l₂ : List β} (h : l <:+ l₁ ++ l₂) :
    l <:+ l₂ ∨ ∃ l', l' <:+ l₁ ∧ l = l' ++ l₂ := by
  obtain ⟨p, hp⟩ := h
  rcases List.append_eq_append_iff.mp hp with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · exact Or.inr ⟨as, ⟨p, h1.symm⟩, h2⟩
  · exact Or.inl ⟨bs, h2.symm⟩

theorem length_le_length_flatMap {β : Type} (l : List β) (f : β → Word)
    (h : ∀ b ∈ l, 1 ≤ (f b).length) : l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have h1 := h b (List.mem_cons_self ..)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem length_drop_le' (n : ℕ) (r : Word) : (r.drop n).length ≤ r.length := by
  simp

end ArtGallery

end
