module

public import ArtGallery.Stade.PTimeRat
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Rat.Floor

/-!
# Polynomial-time tools for the Section 5 construction

Generic `PT` lemmas used by the polynomial-time proof of the Section 5 polygon, on top of the
unary rational arithmetic of `ArtGallery/Stade/PTimeRat.lean`:

* integer division by a natural number (rounding down, `PT.intEDivNat`), `⌊q⌋` and `⌈q⌉` of a
  rational (`PT.ratFloor`, `PT.ratCeil`);
* comparisons of integers and rationals (`PT.intLe`, `PT.ratLe`, `PT.ratLt`);
* addition and subtraction of rational points (`PT.q2Add`, `PT.q2Sub`; not `fun_prop` lemmas);
* sorting: `PT.orderedInsert`, `PT.insertionSort` for a polynomial-time Boolean comparator, and
  `PT.mergeSort` for a total and transitive one, through
  `mergeSort_eq_insertionSort_bool` (both sorts are stable, so they agree also when the
  comparator is only a preorder).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Sec5.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

variable {α β : Type} [Code α] [Code β]

/-! ### Integer division, floor and ceiling -/

/-- Integer division by a natural number (rounding down), through the positive and the negative
part of the dividend. -/
theorem int_ediv_nat_eq (z : ℤ) (g : ℕ) :
    z / (g : ℤ) = ((intPos z / g : ℕ) : ℤ) - (((intNegPart z + g - 1) / g : ℕ) : ℤ) := by
  cases z with
  | ofNat m =>
    have h1 : intPos (Int.ofNat m) = m := by simp [intPos]
    have h2 : intNegPart (Int.ofNat m) = 0 := by simp [intNegPart]
    rw [h1, h2]
    have h3 : (0 + g - 1) / g = 0 := by
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · rfl
      · exact Nat.div_eq_of_lt (by omega)
    rw [h3]
    simp only [Int.ofNat_eq_natCast, Nat.cast_zero, sub_zero]
    exact (Int.natCast_ediv m g).symm
  | negSucc m =>
    have h1 : intPos (Int.negSucc m) = 0 := by simp [intPos, Int.negSucc_lt_zero]
    have h2 : intNegPart (Int.negSucc m) = m + 1 := by
      simp [intNegPart, Int.negSucc_lt_zero]
    rw [h1, h2]
    cases g with
    | zero => simp
    | succ g =>
      have h3 : (m + 1 + (g + 1) - 1) / (g + 1) = m / (g + 1) + 1 := by
        rw [show m + 1 + (g + 1) - 1 = m + (g + 1) by omega, Nat.add_div_right _ (by omega)]
      rw [h3]
      show Int.negSucc (m / (g + 1)) = _
      simp only [Nat.zero_div, Nat.cast_zero, zero_sub, Int.negSucc_eq]
      push_cast
      ring

/-- Integer division by a natural number (rounding down; `z / 0 = 0`). -/
@[fun_prop] protected theorem PT.intEDivNat {z : α → ℤ} {g : α → ℕ} (hz : PT z) (hg : PT g) :
    PT (fun a => z a / (g a : ℤ)) := by
  simp only [int_ediv_nat_eq]
  fun_prop

/-- The floor of a rational. -/
@[fun_prop] protected theorem PT.ratFloor {q : α → ℚ} (hq : PT q) : PT (fun a => ⌊q a⌋) := by
  simp only [Rat.floor_def']
  fun_prop

/-- The ceiling of a rational. -/
@[fun_prop] protected theorem PT.ratCeil {q : α → ℚ} (hq : PT q) : PT (fun a => ⌈q a⌉) := by
  simp only [Rat.ceil_def']
  fun_prop

/-! ### Comparisons -/

@[fun_prop] protected theorem PT.intLe {z w : α → ℤ} (hz : PT z) (hw : PT w) :
    PT (fun a => decide (z a ≤ w a)) :=
  (PT.not (PT.intNeg (PT.intSub hw hz))).of_eq fun a => by
    by_cases h : z a ≤ w a
    · have : ¬ (w a - z a < 0) := by omega
      simp [h, this]
    · have : w a - z a < 0 := by omega
      simp [h, this]

@[fun_prop] protected theorem PT.intLt {z w : α → ℤ} (hz : PT z) (hw : PT w) :
    PT (fun a => decide (z a < w a)) :=
  (PT.not (PT.intLe hw hz)).of_eq fun a => by
    by_cases h : z a < w a
    · have : ¬ (w a ≤ z a) := by omega
      simp [h, this]
    · have : w a ≤ z a := by omega
      simp [h, this]

@[fun_prop] protected theorem PT.ratLe {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => decide (q a ≤ r a)) := by
  refine PT.decide_congr (P := fun a => (q a).num * (r a).den ≤ (r a).num * (q a).den)
    (by fun_prop) fun a => ?_
  exact (Rat.le_iff _ _).symm

@[fun_prop] protected theorem PT.ratLt {q r : α → ℚ} (hq : PT q) (hr : PT r) :
    PT (fun a => decide (q a < r a)) := by
  refine PT.decide_congr (P := fun a => ¬ (r a ≤ q a)) (by fun_prop) fun a => ?_
  exact not_le

/-! ### Rational points

Not tagged `@[fun_prop]`: trying these lemmas on sums of rationals makes `fun_prop` unfold the
rational addition, which is very slow.  Apply them by hand. -/

protected theorem PT.q2Add {p q : α → ℚ × ℚ} (hp : PT p) (hq : PT q) :
    PT (fun a => p a + q a) :=
  (show PT (fun a => ((p a).1 + (q a).1, (p a).2 + (q a).2)) by fun_prop).of_eq fun _ => rfl

protected theorem PT.q2Sub {p q : α → ℚ × ℚ} (hp : PT p) (hq : PT q) :
    PT (fun a => p a - q a) :=
  (show PT (fun a => ((p a).1 - (q a).1, (p a).2 - (q a).2)) by fun_prop).of_eq fun _ => rfl

/-! ### Sorting -/

section Sorting

omit [Code β] in
/-- Inserting `a` between a prefix of elements it does not precede and a suffix of elements it
precedes. -/
theorem orderedInsert_append_eq {r : β → β → Prop} [DecidableRel r] (a : β) :
    ∀ (l₁ l₂ : List β), (∀ b ∈ l₁, ¬ r a b) → (∀ b ∈ l₂, r a b) →
      (l₁ ++ l₂).orderedInsert r a = l₁ ++ a :: l₂
  | [], [], _, _ => by simp
  | [], b :: l₂, _, h₂ => by
    simp [List.orderedInsert_cons, h₂ b (by simp)]
  | c :: l₁, l₂, h₁, h₂ => by
    have hc : ¬ r a c := h₁ c (by simp)
    simp only [List.cons_append, List.orderedInsert_cons, hc, ite_false]
    rw [orderedInsert_append_eq a l₁ l₂ (fun b hb => h₁ b (by simp [hb])) h₂]

omit [Code β] in
/-- **Merge sort is insertion sort** for a total and transitive Boolean comparator (both are
stable). -/
theorem mergeSort_eq_insertionSort_bool {le : β → β → Bool}
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a) :
    ∀ l : List β, l.mergeSort le = l.insertionSort (fun a b => le a b = true)
  | [] => by simp
  | a :: l => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons trans total a l
    have hs := List.pairwise_mergeSort trans total (a :: l)
    rw [h1] at hs
    have ha : ∀ b ∈ l₂, le a b = true := by
      intro b hb
      have := (List.pairwise_append.1 hs).2.1
      exact (List.pairwise_cons.1 this).1 b hb
    rw [h1, List.insertionSort_cons, ← mergeSort_eq_insertionSort_bool trans total l, h2]
    refine (orderedInsert_append_eq a l₁ l₂ (fun b hb => ?_) ha).symm
    have := h3 b hb
    simpa using this

omit [Code β] in
theorem size_eq_of_perm {l l' : List β} [Code β] (h : l.Perm l') : size l = size l' := by
  rw [size_list, size_list, h.length_eq, (h.map size).sum_eq]

/-- Insertion into a list, for a polynomial-time Boolean comparator. -/
@[fun_prop] protected theorem PT.orderedInsert {le : α → β → β → Bool}
    (hle : PT (fun p : α × β × β => le p.1 p.2.1 p.2.2)) {x : α → β} {l : α → List β}
    (hx : PT x) (hl : PT l) :
    PT (fun a => (l a).orderedInsert (fun b c => le a b c = true) (x a)) := by
  obtain ⟨cx, kx, hkx⟩ := hx.size_le
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  have hc : PT (fun p : α × β × List β × List β => le p.1 (x p.1) p.2.1) :=
    hle.comp (PT.pair PT.fst' (PT.pair (hx.comp PT.fst') (PT.fst PT.snd')))
  refine PT.of_listRec (g := fun a t => t.orderedInsert (fun b c => le a b c = true) (x a))
    (base := fun a => [x a])
    (step := fun a b t s => if le a (x a) b then x a :: b :: t else b :: s) (l := l)
    (by fun_prop) ?_ hl (fun _ => by simp) ?_
    (fun N => powerBound cx kx N + powerBound cl kl N + 1)
    (((PolynomialBound.power cx kx).add (PolynomialBound.power cl kl)).add
      (PolynomialBound.constant 1)) ?_
  · exact PT.ite hc (PT.cons (hx.comp PT.fst') (PT.cons (PT.fst PT.snd')
      (PT.fst (PT.snd PT.snd')))) (PT.cons (PT.fst PT.snd') (PT.snd (PT.snd PT.snd')))
  · intro a b t
    simp only [List.orderedInsert_cons]
  · intro a suf hsuf
    rw [size_eq_of_perm (List.perm_orderedInsert _ _ _), size_cons]
    have h1 := hkx a
    have h2 := Nat.le_trans (size_le_of_sublist hsuf.sublist) (hkl a)
    omega

/-- Insertion sort, for a polynomial-time Boolean comparator. -/
@[fun_prop] protected theorem PT.insertionSort {le : α → β → β → Bool}
    (hle : PT (fun p : α × β × β => le p.1 p.2.1 p.2.2)) {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).insertionSort (fun b c => le a b c = true)) := by
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  have hf : PT (fun p : α × β × List β =>
      p.2.2.orderedInsert (fun b c => le p.1 b c = true) p.2.1) :=
    PT.orderedInsert (le := fun p => le p.1)
      (hle.comp (PT.pair (PT.fst PT.fst') PT.snd')) (PT.fst PT.snd') (PT.snd PT.snd')
  refine (PT.foldr_of_add_le (f := fun a b s => s.orderedInsert (fun b c => le a b c = true) b)
    (init := fun _ => []) (l := l) hf (PT.const _) hl (fun N => powerBound cl kl N + 1)
    ((PolynomialBound.power cl kl).add (PolynomialBound.constant 1)) ?_).of_eq fun a => ?_
  swap
  · induction l a with
    | nil => simp
    | cons b t ih => simp [ih]
  intro a b s hb
  rw [size_eq_of_perm (List.perm_orderedInsert _ _ _), size_cons]
  have := Nat.le_trans (size_le_of_mem hb) (hkl a)
  omega

/-- Merge sort, for a polynomial-time, total and transitive Boolean comparator. -/
protected theorem PT.mergeSort {le : α → β → β → Bool}
    (hle : PT (fun p : α × β × β => le p.1 p.2.1 p.2.2))
    (trans : ∀ a x y z, le a x y → le a y z → le a x z) (total : ∀ a x y, le a x y || le a y x)
    {l : α → List β} (hl : PT l) : PT (fun a => (l a).mergeSort (le a)) :=
  (PT.insertionSort hle hl).of_eq fun a =>
    (mergeSort_eq_insertionSort_bool (trans a) (total a) (l a)).symm

/-- Merge sort by a rational key (stable). -/
protected theorem PT.mergeSortKey {key : β → ℚ} (hkey : PT key) {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).mergeSort (fun x y => decide (key x ≤ key y))) :=
  PT.mergeSort (le := fun _ x y => decide (key x ≤ key y))
    (PT.ratLe (hkey.comp (PT.fst PT.snd')) (hkey.comp (PT.snd PT.snd')))
    (fun _ x y z h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; exact h1.trans h2)
    (fun _ x y => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) hl

end Sorting

end ArtGallery.Sec5.PTime

end
