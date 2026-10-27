module

public import PT.List
public import PT.Raw

/-!
# Equality tests, membership and association lists

* **Equality is polynomial-time on every coded type** (`PT.decEq`): codes are injective, and
  two codes are compared bit by bit.  The compositional forms are `PT.decide_eq`
  (`decide (f a = g a)`), `PT.decide_ne`, `PT.beq` (`f a == g a` for a lawful `BEq`) and
  `PT.bne`; they apply to `Nat`, `Bool`, products, options, sums, lists, `SAT.Literal`,
  clauses, formulas, ….
* Membership: `PT.contains`, `PT.elem`, `PT.decide_mem` (`decide (b a ∈ l a)`),
  `PT.decide_forall_mem`, `PT.decide_exists_mem`, `PT.decide_subset`; for a `BEq` that is not
  lawful, `PT.contains_of_beq` takes a polynomial-time test as a hypothesis.
* `PT.count`, `PT.idxOf`, `PT.lookup`, `PT.erase`, `PT.insert`, `PT.removeAll`,
  `PT.eraseDups`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ δ : Type} [Code α] [Code β] [Code γ] [Code δ]

/-! ### Equality -/

omit [Code β] in
theorem list_eq_iff_zip [DecidableEq β] (u v : List β) :
    u = v ↔ u.length = v.length ∧ (u.zip v).all (fun p => decide (p.1 = p.2)) = true := by
  induction u generalizing v with
  | nil => cases v <;> simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v => simp [ih v, and_left_comm]

/-- Equality of words is polynomial-time. -/
protected theorem PT.wordEq : PT (fun p : Word × Word => decide (p.1 = p.2)) := by
  have h : PT (fun p : Word × Word =>
      decide (p.1.length = p.2.length) && (p.1.zip p.2).all (fun q => q.1 == q.2)) := by
    fun_prop
  exact h.of_eq fun p => by
    rw [Bool.eq_iff_iff]
    simp [list_eq_iff_zip p.1 p.2]

/-- **Equality is polynomial-time on every coded type.** -/
protected theorem PT.decEq [DecidableEq β] : PT (fun p : β × β => decide (p.1 = p.2)) :=
  (PT.wordEq.comp (PT.pair (PT.enc PT.fst') (PT.enc PT.snd'))).of_eq fun p => by simp

/-- Equality test, compositional form (any decidability instance). -/
@[fun_prop] protected theorem PT.decide_eq {f g : α → β} [inst : ∀ a, Decidable (f a = g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a = g a)) := by
  classical
  exact ((PT.decEq (β := β)).comp (hf.pair hg)).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

@[fun_prop] protected theorem PT.decide_ne {f g : α → β} [inst : ∀ a, Decidable (f a ≠ g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a ≠ g a)) := by
  classical
  exact (PT.decide_not (PT.decide_eq hf hg)).decide_congr fun _ => Iff.rfl

/-- Boolean equality for a lawful `BEq` instance. -/
@[fun_prop] protected theorem PT.beq [BEq β] [LawfulBEq β] {f g : α → β} (hf : PT f) (hg : PT g) :
    PT (fun a => f a == g a) := by
  classical
  exact (PT.decide_eq hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

@[fun_prop] protected theorem PT.bne [BEq β] [LawfulBEq β] {f g : α → β} (hf : PT f) (hg : PT g) :
    PT (fun a => f a != g a) :=
  (PT.not (PT.beq hf hg)).of_eq fun _ => rfl

/-! ### Membership -/

/-- `List.contains` for an arbitrary `BEq` instance with a polynomial-time test. -/
protected theorem PT.contains_of_beq [BEq β] (hbeq : PT (fun p : β × β => p.1 == p.2))
    {l : α → List β} {b : α → β} (hl : PT l) (hb : PT b) :
    PT (fun a => (l a).contains (b a)) :=
  (PT.any (p := fun a x => b a == x) (hbeq.comp (PT.pair (hb.comp PT.fst') PT.snd')) hl).of_eq
    fun _ => List.contains_eq_any_beq.symm

@[fun_prop] protected theorem PT.contains [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β}
    (hl : PT l) (hb : PT b) : PT (fun a => (l a).contains (b a)) :=
  PT.contains_of_beq (PT.beq PT.fst' PT.snd') hl hb

@[fun_prop] protected theorem PT.elem [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β}
    (hb : PT b) (hl : PT l) : PT (fun a => List.elem (b a) (l a)) :=
  (PT.contains hl hb).of_eq fun _ => List.elem_eq_contains.symm

/-- Membership test (any decidability instance). -/
@[fun_prop] protected theorem PT.decide_mem {b : α → β} {l : α → List β}
    [inst : ∀ a, Decidable (b a ∈ l a)] (hb : PT b) (hl : PT l) :
    PT (fun a => decide (b a ∈ l a)) := by
  classical
  exact (PT.any (p := fun a x => decide (b a = x))
    (PT.decide_eq (hb.comp PT.fst') PT.snd') hl).of_eq fun a => by
      rw [Bool.eq_iff_iff]
      simp

/-- Bounded universal quantification over a list. -/
@[fun_prop] protected theorem PT.decide_forall_mem {l : α → List β} {P : α → β → Prop}
    [∀ a b, Decidable (P a b)] [inst : ∀ a, Decidable (∀ x ∈ l a, P a x)] (hl : PT l)
    (hP : PT (fun q : α × β => decide (P q.1 q.2))) : PT (fun a => decide (∀ x ∈ l a, P a x)) :=
  (PT.all (p := fun a x => decide (P a x)) hP hl).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

/-- Bounded existential quantification over a list. -/
@[fun_prop] protected theorem PT.decide_exists_mem {l : α → List β} {P : α → β → Prop}
    [∀ a b, Decidable (P a b)] [inst : ∀ a, Decidable (∃ x ∈ l a, P a x)] (hl : PT l)
    (hP : PT (fun q : α × β => decide (P q.1 q.2))) : PT (fun a => decide (∃ x ∈ l a, P a x)) :=
  (PT.any (p := fun a x => decide (P a x)) hP hl).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

/-- Inclusion of lists. -/
@[fun_prop] protected theorem PT.decide_subset {l m : α → List β}
    [inst : ∀ a, Decidable (l a ⊆ m a)] (hl : PT l) (hm : PT m) :
    PT (fun a => decide (l a ⊆ m a)) := by
  classical
  exact (PT.decide_forall_mem (P := fun a x => x ∈ m a) hl
    (PT.decide_mem PT.snd' (hm.comp PT.fst'))).decide_congr fun _ => Iff.rfl

@[fun_prop] protected theorem PT.count [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β}
    (hl : PT l) (hb : PT b) : PT (fun a => (l a).count (b a)) :=
  (PT.countP (p := fun a x => x == b a) (PT.beq PT.snd' (hb.comp PT.fst')) hl).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.idxOf [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β}
    (hl : PT l) (hb : PT b) : PT (fun a => (l a).idxOf (b a)) :=
  (PT.findIdx (p := fun a x => x == b a) (PT.beq PT.snd' (hb.comp PT.fst')) hl).of_eq fun _ => rfl

/-! ### Association lists, erasing and inserting -/

omit [Code β] [Code γ] in
theorem lookup_eq_find? [BEq β] (k : β) (l : List (β × γ)) :
    l.lookup k = (l.find? (fun q => k == q.1)).map (·.2) := by
  induction l with
  | nil => rfl
  | cons q t ih =>
    obtain ⟨x, y⟩ := q
    rw [List.lookup_cons, List.find?_cons]
    cases h : k == x <;> simp [ih]

/-- Lookup in an association list. -/
@[fun_prop] protected theorem PT.lookup [BEq β] [LawfulBEq β] {k : α → β}
    {l : α → List (β × γ)} (hk : PT k) (hl : PT l) : PT (fun a => (l a).lookup (k a)) :=
  (PT.optionMap (f := fun _ q => q.2)
    (PT.find? (p := fun a q => k a == q.1) (PT.beq (hk.comp PT.fst') (PT.fst PT.snd')) hl)
    (PT.snd PT.snd')).of_eq fun _ => (lookup_eq_find? _ _).symm

@[fun_prop] protected theorem PT.erase [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β}
    (hl : PT l) (hb : PT b) : PT (fun a => (l a).erase (b a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  refine PT.of_listRec (g := fun a t => t.erase (b a)) (base := fun _ => [])
    (step := fun a x xs r => if x == b a then xs else x :: r) (PT.const [])
    (PT.ite (PT.beq (PT.fst PT.snd') (hb.comp PT.fst')) (PT.fst (PT.snd PT.snd'))
      (PT.cons (PT.fst PT.snd') (PT.snd (PT.snd PT.snd')))) hl (fun _ => rfl)
    (fun a x xs => List.erase_cons) (powerBound c k) (PolynomialBound.power c k) ?_
  intro a suf hsuf
  exact Nat.le_trans
    (size_le_of_sublist ((List.erase_sublist ..).trans hsuf.sublist)) (hk a)

@[fun_prop] protected theorem PT.insert [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β}
    (hb : PT b) (hl : PT l) : PT (fun a => (l a).insert (b a)) :=
  (PT.ite (PT.contains hl hb) hl (PT.cons hb hl)).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.removeAll [BEq β] [LawfulBEq β] {l m : α → List β}
    (hl : PT l) (hm : PT m) : PT (fun a => (l a).removeAll (m a)) :=
  (PT.filter (p := fun a x => !List.elem x (m a))
    (PT.not (PT.elem PT.snd' (hm.comp PT.fst'))) hl).of_eq fun _ => rfl

omit [Code β] in
theorem eraseDupsBy_loop_eq (r : β → β → Bool) (as bs : List β) :
    List.eraseDupsBy.loop r as bs =
      (as.foldl (fun bs a => if bs.any (r a) then bs else a :: bs) bs).reverse := by
  induction as generalizing bs with
  | nil => simp [List.eraseDupsBy.loop]
  | cons a as ih =>
    rw [List.eraseDupsBy.loop, List.foldl_cons]
    cases h : bs.any (r a) <;> simp [ih]

/-- Removing duplicates (keeping first occurrences), for a polynomial-time relation. -/
protected theorem PT.eraseDupsBy {r : β → β → Bool} (hr : PT (fun p : β × β => r p.1 p.2))
    {l : α → List β} (hl : PT l) : PT (fun a => (l a).eraseDupsBy r) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have h := PT.foldl_of_add_le
    (f := fun (_ : α) (bs : List β) b => if bs.any (r b) then bs else b :: bs)
    (init := fun _ => []) (l := l)
    (PT.ite (PT.any (p := fun (q : α × List β × β) x => r q.2.2 x)
        (hr.comp (PT.pair (PT.snd (PT.snd PT.fst')) PT.snd')) (PT.fst PT.snd'))
      (PT.fst PT.snd') (PT.cons (PT.snd PT.snd') (PT.fst PT.snd'))) (PT.const []) hl
    (fun N => powerBound c k N + 1) ((PolynomialBound.power c k).add (PolynomialBound.constant 1))
    ?_
  · exact (PT.reverse h).of_eq fun a => (eraseDupsBy_loop_eq r (l a) []).symm
  · intro a s b hb
    have h1 := size_le_of_mem hb
    have h2 := hk a
    by_cases h : s.any (r b) = true
    · simp only [h, ite_true]
      omega
    · simp only [h, Bool.false_eq_true, ite_false, size_cons]
      omega

@[fun_prop] protected theorem PT.eraseDups [BEq β] [LawfulBEq β] {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).eraseDups) :=
  PT.eraseDupsBy (r := fun x y => x == y) (PT.beq PT.fst' PT.snd') hl

end Complexity.PT
