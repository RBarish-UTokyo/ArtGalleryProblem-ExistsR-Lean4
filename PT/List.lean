module

public import PT.ListBasic

/-!
# Polynomial-time list operations

None of the `@[fun_prop]` lemmas of this file has a size side condition.

* `PT.flatMap`, `PT.flatten`, `PT.filter`, `PT.filterMap`, `PT.partition`;
* `PT.any`, `PT.all`, `PT.countP`, `PT.find?`, `PT.findSome?`, `PT.findIdx`;
* `PT.drop`, `PT.take`, `PT.getElem?`, `PT.listGetD`, `PT.getElem!`, `PT.head!`,
  `PT.getLast?`, `PT.getLastD`, `PT.dropLast`, `PT.splitAt`, `PT.set`, `PT.eraseIdx`
  (and `PT.getElem`, `PT.of_some`, which are not `fun_prop` lemmas);
* `PT.takeWhile`, `PT.dropWhile`;
* `PT.zip`, `PT.zipWith`, `PT.unzip`, `PT.range`, `PT.range'`, `PT.replicate`, `PT.zipIdx`;
* `PT.sum`, `PT.foldl_max`, `PT.foldl_min`, `PT.max?`, `PT.min?` (lists of numbers).

Recursion schemes (these do have a size hypothesis):

* `PT.of_listRec` / `PT.listRec` — bounded structural recursion on a list;
* `PT.foldl_of_add_le`, `PT.foldr_of_add_le` — folds whose accumulator grows additively;
* `PT.foldl_of_size_le` — folds whose accumulator has bounded size after every step.

Function arguments take an environment and are given in uncurried form, e.g.
`PT (fun q : α × β => p q.1 q.2)` for the predicate of `(l a).filter (p a)`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ δ σ : Type} [Code α] [Code β] [Code γ] [Code δ] [Code σ]

/-! ### `flatMap` and its consequences -/

omit [Code β] in
/-- The size of a `flatMap`, when the images have size at most `K`. -/
theorem size_flatMap_le {l : List β} {g : β → List γ} {K : Nat} (h : ∀ b ∈ l, size (g b) ≤ K) :
    size (l.flatMap g) ≤ l.length * K + 1 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have h1 := h b (List.mem_cons_self ..)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h3 := size_append (g b) (t.flatMap g)
    simp only [List.flatMap_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **`flatMap`** (no side condition; the function is given in uncurried form). -/
@[fun_prop] protected theorem PT.flatMap {f : α → β → List γ} {l : α → List β}
    (hf : PT (fun p : α × β => f p.1 p.2)) (hl : PT l) :
    PT (fun a => (l a).flatMap (f a)) := by
  obtain ⟨c, k, hk⟩ := hf.size_le
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  have h := PT.foldl (f := fun a (acc : List γ) b => acc ++ f a b) (init := fun _ => [])
    (PT.append (PT.fst PT.snd') (hf.comp (PT.pair PT.fst' (PT.snd PT.snd')))) (PT.const []) hl
    (fun N => powerBound cl kl N * powerBound c k (N + powerBound cl kl N) + 1)
    (((PolynomialBound.power cl kl).mul ((PolynomialBound.power c k).comp
      (PolynomialBound.identity.add (PolynomialBound.power cl kl)))).add
        (PolynomialBound.constant 1)) ?_
  · exact h.of_eq fun _ => List.flatMap_eq_foldl.symm
  · intro a pre hpre
    have hlen : pre.length ≤ powerBound cl kl (size a) :=
      Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hpre.length_le (length_lt_size _))) (hkl a)
    have hK : ∀ b ∈ pre, size (f a b) ≤ powerBound c k (size a + powerBound cl kl (size a)) := by
      intro b hb
      have hb' : size b ≤ powerBound cl kl (size a) :=
        Nat.le_trans (size_le_of_mem (hpre.subset hb)) (hkl a)
      have := hk (a, b)
      rw [size_prod] at this
      exact Nat.le_trans this (powerBound_mono c k (Nat.add_le_add_left hb' _))
    rw [← List.flatMap_eq_foldl]
    exact Nat.le_trans (size_flatMap_le hK)
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _)

@[fun_prop] protected theorem PT.flatten {l : α → List (List β)} (hl : PT l) :
    PT (fun a => (l a).flatten) :=
  (PT.flatMap (f := fun _ b => b) PT.snd' hl).of_eq fun _ => by simp

omit [Code β] in
theorem filter_eq_flatMap (p : β → Bool) (l : List β) :
    l.filter p = l.flatMap (fun b => if p b then [b] else []) := by
  induction l with
  | nil => rfl
  | cons b t ih => by_cases h : p b <;> simp [h, ih]

/-- **`filter`** (the predicate is given in uncurried form). -/
@[fun_prop] protected theorem PT.filter {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).filter (p a)) :=
  (PT.flatMap (f := fun a b => if p a b then [b] else [])
    (PT.ite hp (PT.cons PT.snd' (PT.const [])) (PT.const [])) hl).of_eq fun _ =>
      (filter_eq_flatMap _ _).symm

omit [Code β] [Code γ] in
theorem filterMap_eq_flatMap (f : β → Option γ) (l : List β) :
    l.filterMap f = l.flatMap (fun b => (f b).elim [] (fun c => [c])) := by
  induction l with
  | nil => rfl
  | cons b t ih => cases h : f b <;> simp [h, ih]

@[fun_prop] protected theorem PT.filterMap {f : α → β → Option γ} {l : α → List β}
    (hf : PT (fun q : α × β => f q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).filterMap (f a)) :=
  (PT.flatMap (f := fun a b => (f a b).elim [] (fun c => [c]))
    (PT.optionElim hf (PT.const []) (PT.cons PT.snd' (PT.const []))) hl).of_eq fun _ =>
      (filterMap_eq_flatMap _ _).symm

omit [Code β] in
theorem any_eq_filter (p : β → Bool) (l : List β) : l.any p = !(l.filter p).isEmpty := by
  induction l with
  | nil => rfl
  | cons b t ih => by_cases h : p b <;> simp [h, ih]

omit [Code β] in
theorem all_eq_filter (p : β → Bool) (l : List β) :
    l.all p = (l.filter fun b => !p b).isEmpty := by
  induction l with
  | nil => rfl
  | cons b t ih => by_cases h : p b <;> simp [h, ih]

@[fun_prop] protected theorem PT.any {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).any (p a)) :=
  (PT.not (PT.isEmpty (PT.filter hp hl))).of_eq fun _ => (any_eq_filter _ _).symm

@[fun_prop] protected theorem PT.all {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).all (p a)) :=
  (PT.isEmpty (PT.filter (p := fun a b => !p a b) (PT.not hp) hl)).of_eq fun _ =>
    (all_eq_filter _ _).symm

@[fun_prop] protected theorem PT.countP {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).countP (p a)) :=
  (PT.length (PT.filter hp hl)).of_eq fun _ => List.countP_eq_length_filter.symm

@[fun_prop] protected theorem PT.find? {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).find? (p a)) :=
  (PT.head? (PT.filter hp hl)).of_eq fun _ => List.head?_filter

@[fun_prop] protected theorem PT.findSome? {f : α → β → Option γ} {l : α → List β}
    (hf : PT (fun q : α × β => f q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).findSome? (f a)) :=
  (PT.head? (PT.filterMap hf hl)).of_eq fun _ => List.head?_filterMap

@[fun_prop] protected theorem PT.partition {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).partition (p a)) :=
  (PT.pair (PT.filter hp hl) (PT.filter (p := fun a b => !p a b) (PT.not hp) hl)).of_eq fun _ => by
    simp [List.partition_eq_filter_filter, Function.comp_def]

/-- Conjunction of a list of Booleans. -/
@[fun_prop] protected theorem PT.listAnd {l : α → List Bool} (hl : PT l) :
    PT (fun a => (l a).and) :=
  (PT.all (p := fun _ b => b) PT.snd' hl).of_eq fun _ => rfl

/-- Disjunction of a list of Booleans. -/
@[fun_prop] protected theorem PT.listOr {l : α → List Bool} (hl : PT l) :
    PT (fun a => (l a).or) :=
  (PT.any (p := fun _ b => b) PT.snd' hl).of_eq fun _ => rfl

/-! ### Bounded structural recursion on a list -/

/-- **Bounded structural recursion on a list.**  If `g a [] = base a` and
`g a (x :: xs) = step a x xs (g a xs)` with `base`, `step` polynomial-time and the values
`g a suf`, for the suffixes `suf` of `l a`, polynomially bounded in size, then
`fun a => g a (l a)` is polynomial-time. -/
protected theorem PT.of_listRec {g : α → List β → σ} {base : α → σ}
    {step : α → β → List β → σ → σ} {l : α → List β} (hbase : PT base)
    (hstep : PT (fun p : α × β × List β × σ => step p.1 p.2.1 p.2.2.1 p.2.2.2)) (hl : PT l)
    (h0 : ∀ a, g a [] = base a) (hs : ∀ a x xs, g a (x :: xs) = step a x xs (g a xs))
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a (suf : List β), suf <:+ l a → size (g a suf) ≤ bound (size a)) :
    PT (fun a => g a (l a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have key : ∀ a (pre xs : List β),
      pre.foldl (fun (s : List β × σ) x => (x :: s.1, step a x s.1 s.2)) (xs, g a xs) =
        (pre.reverse ++ xs, g a (pre.reverse ++ xs)) := by
    intro a pre
    induction pre with
    | nil => intro xs; rfl
    | cons x pre ih =>
      intro xs
      rw [List.foldl_cons, ← hs, ih]
      simp
  have h := PT.foldl (f := fun a (s : List β × σ) x => (x :: s.1, step a x s.1 s.2))
    (init := fun a => ([], base a)) (l := fun a => (l a).reverse)
    (PT.pair (PT.cons (PT.snd PT.snd') (PT.fst (PT.fst PT.snd')))
      (hstep.comp (PT.pair PT.fst' (PT.pair (PT.snd PT.snd')
        (PT.pair (PT.fst (PT.fst PT.snd')) (PT.snd (PT.fst PT.snd')))))))
    (PT.pair (PT.const []) hbase) (PT.reverse hl)
    (fun N => powerBound c k N + bound N) ((PolynomialBound.power c k).add hbound) ?_
  · exact (PT.snd h).of_eq fun a => by
      show ((l a).reverse.foldl _ ([], base a)).2 = _
      rw [← h0 a, key]
      simp
  · intro a pre hpre
    have h1 : pre.reverse <:+ l a := by
      rw [← List.reverse_prefix, List.reverse_reverse]
      exact hpre
    show size (pre.foldl _ ([], base a)) ≤ _
    rw [← h0 a, key, List.append_nil, size_prod]
    exact Nat.add_le_add (Nat.le_trans (size_le_of_sublist h1.sublist) (hk a)) (hsize a _ h1)

/-- Bounded structural recursion on a list, stated with `List.rec`. -/
protected theorem PT.listRec {base : α → σ} {step : α → β → List β → σ → σ} {l : α → List β}
    (hbase : PT base)
    (hstep : PT (fun p : α × β × List β × σ => step p.1 p.2.1 p.2.2.1 p.2.2.2)) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a (suf : List β), suf <:+ l a →
      size (List.rec (motive := fun _ => σ) (base a) (step a) suf) ≤ bound (size a)) :
    PT (fun a => List.rec (motive := fun _ => σ) (base a) (step a) (l a)) :=
  PT.of_listRec (g := fun a t => List.rec (motive := fun _ => σ) (base a) (step a) t)
    hbase hstep hl (fun _ => rfl) (fun _ _ _ => rfl) bound hbound hsize

/-! ### Folds with a simple growth condition -/

omit [Code β] in
theorem size_foldl_le_add {f : σ → β → σ} {K : Nat} (pre : List β) (s : σ)
    (h : ∀ b ∈ pre, ∀ s, size (f s b) ≤ size s + K) :
    size (pre.foldl f s) ≤ size s + pre.length * K := by
  induction pre generalizing s with
  | nil => simp
  | cons b t ih =>
    have h1 := h b (List.mem_cons_self ..) s
    have h2 := ih (f s b) fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.foldl_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **Left fold with additive growth.**  If each step increases the size of the accumulator by
at most a polynomial in the size of the input, the fold is polynomial-time. -/
protected theorem PT.foldl_of_add_le {f : α → σ → β → σ} {init : α → σ} {l : α → List β}
    (hf : PT (fun p : α × σ × β => f p.1 p.2.1 p.2.2)) (hinit : PT init) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a s b, b ∈ l a → size (f a s b) ≤ size s + bound (size a)) :
    PT (fun a => (l a).foldl (f a) (init a)) := by
  obtain ⟨ci, ki, hki⟩ := hinit.size_le
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  refine PT.foldl hf hinit hl (fun N => powerBound ci ki N + powerBound cl kl N * bound N)
    ((PolynomialBound.power ci ki).add ((PolynomialBound.power cl kl).mul hbound)) ?_
  intro a pre hpre
  have hlen : pre.length ≤ powerBound cl kl (size a) :=
    Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hpre.length_le (length_lt_size _))) (hkl a)
  exact Nat.le_trans (size_foldl_le_add pre (init a) fun b hb s => hsize a s b (hpre.subset hb))
    (Nat.add_le_add (hki a) (Nat.mul_le_mul_right _ hlen))

/-- **Right fold with additive growth.** -/
protected theorem PT.foldr_of_add_le {f : α → β → σ → σ} {init : α → σ} {l : α → List β}
    (hf : PT (fun p : α × β × σ => f p.1 p.2.1 p.2.2)) (hinit : PT init) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a b s, b ∈ l a → size (f a b s) ≤ size s + bound (size a)) :
    PT (fun a => (l a).foldr (f a) (init a)) := by
  have h := PT.foldl_of_add_le (f := fun a s b => f a b s) (init := init)
    (l := fun a => (l a).reverse)
    (hf.comp (PT.pair PT.fst' (PT.pair (PT.snd PT.snd') (PT.fst PT.snd')))) hinit
    (PT.reverse hl) bound hbound (fun a s b hb => hsize a b s (List.mem_reverse.mp hb))
  exact h.of_eq fun a => by simp [List.foldl_reverse]

/-- **Left fold with a bounded accumulator.**  If the result of every step has polynomially
bounded size (whatever the accumulator was), the fold is polynomial-time. -/
protected theorem PT.foldl_of_size_le {f : α → σ → β → σ} {init : α → σ} {l : α → List β}
    (hf : PT (fun p : α × σ × β => f p.1 p.2.1 p.2.2)) (hinit : PT init) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a s b, b ∈ l a → size (f a s b) ≤ bound (size a)) :
    PT (fun a => (l a).foldl (f a) (init a)) := by
  obtain ⟨ci, ki, hki⟩ := hinit.size_le
  refine PT.foldl hf hinit hl (fun N => powerBound ci ki N + bound N)
    ((PolynomialBound.power ci ki).add hbound) ?_
  intro a pre hpre
  rcases List.eq_nil_or_concat pre with rfl | ⟨t, b, rfl⟩
  · exact Nat.le_trans (hki a) (Nat.le_add_right _ _)
  · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.le_trans (hsize a _ b (hpre.subset (by simp))) (Nat.le_add_left _ _)

/-! ### `drop`, `take`, indexing -/

omit [Code β] in
theorem iterate_tail (n : Nat) (l : List β) : List.tail^[n] l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp

@[fun_prop] protected theorem PT.drop {n : α → Nat} {l : α → List β} (hn : PT n) (hl : PT l) :
    PT (fun a => (l a).drop (n a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have h := PT.iterate_const (step := (List.tail : List β → List β)) (init := l) (n := n)
    (PT.tail PT.id) hl hn (powerBound c k) (PolynomialBound.power c k) ?_
  · exact h.of_eq fun a => iterate_tail _ _
  · intro a i _
    rw [iterate_tail]
    exact Nat.le_trans (size_drop_le _ _) (hk a)

@[fun_prop] protected theorem PT.take {n : α → Nat} {l : α → List β} (hn : PT n) (hl : PT l) :
    PT (fun a => (l a).take (n a)) :=
  (PT.reverse (PT.drop (PT.sub (PT.length hl) hn) (PT.reverse hl))).of_eq fun _ => by
    rw [← List.reverse_take, List.reverse_reverse]

/-- `l[i]?`. -/
@[fun_prop] protected theorem PT.getElem? {l : α → List β} {n : α → Nat} (hl : PT l) (hn : PT n) :
    PT (fun a => (l a)[n a]?) :=
  (PT.head? (PT.drop hn hl)).of_eq fun _ => List.head?_drop

/-- `List.getD`. -/
@[fun_prop] protected theorem PT.listGetD {l : α → List β} {n : α → Nat} {d : α → β}
    (hl : PT l) (hn : PT n) (hd : PT d) : PT (fun a => (l a).getD (n a) (d a)) :=
  (PT.getD (PT.getElem? hl hn) hd).of_eq fun _ => List.getD_eq_getElem?_getD.symm

/-- `l[i]!`. -/
@[fun_prop] protected theorem PT.getElem! [Inhabited β] {l : α → List β} {n : α → Nat}
    (hl : PT l) (hn : PT n) : PT (fun a => (l a)[n a]!) :=
  (PT.listGetD hl hn (PT.const default)).of_eq fun _ => by simp

/-- A function is polynomial-time if its composition with `some` is. -/
protected theorem PT.of_some {f : α → β} (hf : PT (fun a => some (f a))) : PT f := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => (F x).tail, polyTime_tail hF, fun a => by simp [hF']⟩

/-- `l[i]` with a proof that the index is in range. -/
protected theorem PT.getElem {l : α → List β} {n : α → Nat} (hl : PT l) (hn : PT n)
    (h : ∀ a, n a < (l a).length) : PT (fun a => (l a)[n a]'(h a)) :=
  PT.of_some ((PT.getElem? hl hn).of_eq fun a => List.getElem?_eq_getElem (h a))

/-- `l.head!`. -/
@[fun_prop] protected theorem PT.head! [Inhabited β] {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).head!) :=
  (PT.headD hl (PT.const default)).of_eq fun a => by cases l a <;> rfl

@[fun_prop] protected theorem PT.getLast? {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).getLast?) :=
  (PT.head? (PT.reverse hl)).of_eq fun _ => List.getLast?_eq_head?_reverse.symm

@[fun_prop] protected theorem PT.getLastD {l : α → List β} {d : α → β} (hl : PT l) (hd : PT d) :
    PT (fun a => (l a).getLastD (d a)) :=
  (PT.getD (PT.getLast? hl) hd).of_eq fun _ => by simp

@[fun_prop] protected theorem PT.dropLast {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).dropLast) :=
  (PT.take (PT.sub (PT.length hl) (PT.const 1)) hl).of_eq fun _ => List.dropLast_eq_take.symm

@[fun_prop] protected theorem PT.splitAt {n : α → Nat} {l : α → List β} (hn : PT n) (hl : PT l) :
    PT (fun a => (l a).splitAt (n a)) :=
  (PT.pair (PT.take hn hl) (PT.drop hn hl)).of_eq fun _ => List.splitAt_eq.symm

@[fun_prop] protected theorem PT.set {l : α → List β} {n : α → Nat} {x : α → β}
    (hl : PT l) (hn : PT n) (hx : PT x) : PT (fun a => (l a).set (n a) (x a)) :=
  (PT.ite_prop (PT.natLt hn (PT.length hl))
    (PT.append (PT.take hn hl) (PT.cons hx (PT.drop (PT.succ hn) hl))) hl).of_eq fun a => by
      by_cases h : n a < (l a).length
      · simp [h, List.set_eq_take_append_cons_drop]
      · simp [h, List.set_eq_of_length_le (Nat.le_of_not_lt h)]

@[fun_prop] protected theorem PT.eraseIdx {l : α → List β} {n : α → Nat} (hl : PT l) (hn : PT n) :
    PT (fun a => (l a).eraseIdx (n a)) :=
  (PT.append (PT.take hn hl) (PT.drop (PT.succ hn) hl)).of_eq fun _ =>
    (List.eraseIdx_eq_take_drop_succ ..).symm

/-! ### `takeWhile`, `dropWhile`, `findIdx` -/

@[fun_prop] protected theorem PT.takeWhile {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).takeWhile (p a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  refine PT.of_listRec (g := fun a t => t.takeWhile (p a)) (base := fun _ => [])
    (step := fun a x _ r => if p a x then x :: r else []) (PT.const [])
    (PT.ite (hp.comp (PT.pair PT.fst' (PT.fst PT.snd')))
      (PT.cons (PT.fst PT.snd') (PT.snd (PT.snd PT.snd'))) (PT.const [])) hl (fun _ => rfl)
    (fun a x xs => List.takeWhile_cons) (powerBound c k) (PolynomialBound.power c k) ?_
  intro a suf hsuf
  exact Nat.le_trans
    (size_le_of_sublist ((List.takeWhile_sublist _).trans hsuf.sublist)) (hk a)

@[fun_prop] protected theorem PT.dropWhile {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).dropWhile (p a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  refine PT.of_listRec (g := fun a t => t.dropWhile (p a)) (base := fun _ => [])
    (step := fun a x xs r => if p a x then r else x :: xs) (PT.const [])
    (PT.ite (hp.comp (PT.pair PT.fst' (PT.fst PT.snd')))
      (PT.snd (PT.snd PT.snd')) (PT.cons (PT.fst PT.snd') (PT.fst (PT.snd PT.snd')))) hl
    (fun _ => rfl) (fun a x xs => List.dropWhile_cons) (powerBound c k)
    (PolynomialBound.power c k) ?_
  intro a suf hsuf
  exact Nat.le_trans
    (size_le_of_sublist ((List.dropWhile_sublist _).trans hsuf.sublist)) (hk a)

@[fun_prop] protected theorem PT.findIdx {p : α → β → Bool} {l : α → List β}
    (hp : PT (fun q : α × β => p q.1 q.2)) (hl : PT l) :
    PT (fun a => (l a).findIdx (p a)) :=
  (PT.length (PT.takeWhile (p := fun a b => !p a b) (PT.not hp) hl)).of_eq fun a => by
    induction l a with
    | nil => rfl
    | cons b t ih => by_cases h : p a b <;> simp [h, List.findIdx_cons, ih]

/-! ### `zip`, `range`, `replicate`, `zipIdx` -/

omit [Code α] in
theorem size_zip_le (l : List β) (m : List γ) : size (l.zip m) ≤ size l + size m := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    cases m with
    | nil => simp
    | cons c m =>
      have := ih m
      simp only [List.zip_cons_cons, size_cons, size_prod]
      omega

/-- One step of `zip` as a left fold on the state `(reversed result, rest of second list)`. -/
def zipStep (s : List (β × γ) × List γ) (b : β) : List (β × γ) × List γ :=
  s.2.head?.elim (s.1, []) (fun c => ((b, c) :: s.1, s.2.tail))

omit [Code β] [Code γ] in
theorem zipStep_foldl (pre : List β) (acc : List (β × γ)) (m : List γ) :
    pre.foldl zipStep (acc, m) = ((pre.zip m).reverse ++ acc, m.drop pre.length) := by
  induction pre generalizing acc m with
  | nil => simp
  | cons b pre ih =>
    cases m with
    | nil => simpa [zipStep] using ih acc []
    | cons c m => simpa [zipStep] using ih ((b, c) :: acc) m

@[fun_prop] protected theorem PT.zip {l : α → List β} {m : α → List γ} (hl : PT l) (hm : PT m) :
    PT (fun a => (l a).zip (m a)) := by
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  obtain ⟨cm, km, hkm⟩ := hm.size_le
  have hstep : PT (fun p : α × (List (β × γ) × List γ) × β => zipStep p.2.1 p.2.2) := by
    unfold zipStep
    fun_prop
  have h := PT.foldl (f := fun _ s b => zipStep s b) (init := fun a => ([], m a)) hstep
    (PT.pair (PT.const []) hm) hl
    (fun N => powerBound cl kl N + powerBound cm km N + powerBound cm km N)
    (((PolynomialBound.power cl kl).add (PolynomialBound.power cm km)).add
      (PolynomialBound.power cm km)) ?_
  · exact (PT.reverse (PT.fst h)).of_eq fun a => by simp [zipStep_foldl]
  · intro a pre hpre
    simp only [zipStep_foldl, List.append_nil, size_prod, size_reverse]
    have h1 := size_zip_le pre (m a)
    have h2 := size_le_of_prefix hpre
    have h3 := size_drop_le (m a) pre.length
    have h4 := hkl a
    have h5 := hkm a
    omega

@[fun_prop] protected theorem PT.zipWith {f : α → β → γ → δ} {l : α → List β} {m : α → List γ}
    (hf : PT (fun p : α × β × γ => f p.1 p.2.1 p.2.2)) (hl : PT l) (hm : PT m) :
    PT (fun a => List.zipWith (f a) (l a) (m a)) :=
  (PT.map (f := fun a (q : β × γ) => f a q.1 q.2)
    (hf.comp (PT.pair PT.fst' PT.snd')) (PT.zip hl hm)).of_eq fun a => by
      simp [List.zip_eq_zipWith, List.map_zipWith]

@[fun_prop] protected theorem PT.unzip {l : α → List (β × γ)} (hl : PT l) :
    PT (fun a => (l a).unzip) :=
  (PT.pair (PT.map (f := fun _ q => q.1) (PT.fst PT.snd') hl)
    (PT.map (f := fun _ q => q.2) (PT.snd PT.snd') hl)).of_eq fun a => by
      simp [List.unzip_eq_map]

theorem size_range_le (n : Nat) : size (List.range n) ≤ (n + 1) * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := size_append (List.range n) [n]
    simp only [List.range_succ, size_cons, size_nil, size_nat, Nat.succ_mul, Nat.mul_succ] at *
    omega

@[fun_prop] protected theorem PT.range {n : α → Nat} (hn : PT n) :
    PT (fun a => List.range (n a)) := by
  obtain ⟨c, k, hk⟩ := hn.nat_le
  refine PT.of_natRec (g := fun _ i => List.range i) (base := fun _ => [])
    (step := fun _ i s => s ++ [i]) (PT.const [])
    (PT.append (PT.snd PT.snd') (PT.cons (PT.fst PT.snd') (PT.const []))) hn (fun _ => rfl)
    (fun _ i => List.range_succ) (fun N => (powerBound c k N + 1) * (powerBound c k N + 1))
    (((PolynomialBound.power c k).add (PolynomialBound.constant 1)).mul
      ((PolynomialBound.power c k).add (PolynomialBound.constant 1))) ?_
  intro a i hi
  have := hk a
  exact Nat.le_trans (size_range_le i) (Nat.mul_le_mul (by omega) (by omega))

theorem range'_eq_map (s n step : Nat) :
    List.range' s n step = (List.range n).map (fun i => s + step * i) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def, Nat.mul_zero, Nat.add_zero, List.cons.injEq, true_and]
    exact List.map_congr_left fun i _ => by rw [Nat.mul_succ]; omega

/-- `List.range' s n step`. -/
@[fun_prop] protected theorem PT.range' {s n : α → Nat} (hs : PT s) (hn : PT n) (step : Nat) :
    PT (fun a => List.range' (s a) (n a) step) :=
  (PT.map (f := fun a i => s a + step * i)
    (PT.add (hs.comp PT.fst') (PT.mul (PT.const step) PT.snd')) (PT.range hn)).of_eq fun _ =>
      (range'_eq_map _ _ _).symm

@[fun_prop] protected theorem PT.replicate {n : α → Nat} {x : α → β} (hn : PT n) (hx : PT x) :
    PT (fun a => List.replicate (n a) (x a)) :=
  (PT.map (f := fun a _ => x a) (hx.comp PT.fst') (PT.range hn)).of_eq fun _ => by
    rw [List.map_const', List.length_range]

/-- `l.zipIdx k`: the list of pairs `(x, i)` of an element and its index, counted from `k`. -/
@[fun_prop] protected theorem PT.zipIdx {l : α → List β} {k : α → Nat} (hl : PT l) (hk : PT k) :
    PT (fun a => (l a).zipIdx (k a)) :=
  (PT.zip hl (PT.range' hk (PT.length hl) 1)).of_eq fun _ => List.zipIdx_eq_zip_range'.symm

/-! ### Sums and maxima of lists of numbers -/

@[fun_prop] protected theorem PT.sum {l : α → List Nat} (hl : PT l) : PT (fun a => (l a).sum) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have h := PT.foldl_of_add_le (f := fun _ s b => s + b) (init := fun _ => 0) (l := l)
    (PT.add (PT.fst PT.snd') (PT.snd PT.snd')) (PT.const 0) hl (powerBound c k)
    (PolynomialBound.power c k) ?_
  · exact h.of_eq fun a => by simp [List.sum_eq_foldl]
  · intro a s b hb
    have h1 := size_le_of_mem hb
    have h2 := hk a
    simp only [size_nat] at *
    omega

/-- The maximum of a list of numbers (and of a starting value). -/
@[fun_prop] protected theorem PT.foldl_max {l : α → List Nat} {s : α → Nat} (hl : PT l)
    (hs : PT s) : PT (fun a => (l a).foldl max (s a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  refine PT.foldl_of_add_le (f := fun _ s b => max s b) (PT.max (PT.fst PT.snd') (PT.snd PT.snd'))
    hs hl (powerBound c k) (PolynomialBound.power c k) ?_
  intro a s b hb
  have h1 := size_le_of_mem hb
  have h2 := hk a
  simp only [size_nat] at *
  omega

/-- The minimum of a list of numbers and of a starting value. -/
@[fun_prop] protected theorem PT.foldl_min {l : α → List Nat} {s : α → Nat} (hl : PT l)
    (hs : PT s) : PT (fun a => (l a).foldl min (s a)) := by
  refine PT.foldl_of_add_le (f := fun _ s b => min s b) (PT.min (PT.fst PT.snd') (PT.snd PT.snd'))
    hs hl (fun _ => 0) (PolynomialBound.constant 0) ?_
  intro a s b _
  simp only [size_nat]
  omega

/-- `List.max?` on numbers. -/
@[fun_prop] protected theorem PT.max? {l : α → List Nat} (hl : PT l) :
    PT (fun a => (l a).max?) :=
  (PT.listElim (f := fun _ b t => some (t.foldl max b)) hl (PT.const none)
    (PT.some (PT.foldl_max (PT.snd PT.snd') (PT.fst PT.snd')))).of_eq fun a => by
      cases l a <;> rfl

/-- `List.min?` on numbers. -/
@[fun_prop] protected theorem PT.min? {l : α → List Nat} (hl : PT l) :
    PT (fun a => (l a).min?) :=
  (PT.listElim (f := fun _ b t => some (t.foldl min b)) hl (PT.const none)
    (PT.some (PT.foldl_min (PT.snd PT.snd') (PT.fst PT.snd')))).of_eq fun a => by
      cases l a <;> rfl

end Complexity.PT
