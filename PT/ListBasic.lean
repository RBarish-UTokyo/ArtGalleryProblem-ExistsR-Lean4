module

public import PT.Nat
public import PT.Option

/-!
# Basic polynomial-time list primitives

`PT.nil`, `PT.cons`, `PT.head?`, `PT.headD`, `PT.tail`, `PT.isEmpty`, `PT.length`,
`PT.append`, the case-analysis combinator `PT.listCases`, the bounded folds `PT.foldl` and
`PT.foldr`, and from them `PT.reverse` and `PT.map`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ σ : Type} [Code α] [Code β] [Code γ] [Code σ]

theorem leadingOnes_enc_list (l : List β) :
    leadingOnes (enc l) = List.replicate l.length true := by
  rw [enc_list_eq, leadingOnes_ones]

theorem afterOnes_enc_list (l : List β) : afterOnes (enc l) = SAT.writeValues enc l := by
  rw [enc_list_eq, afterOnes_ones]

/-! ### Constructors and destructors -/

protected theorem PT.nil : PT (fun _ : α => ([] : List β)) := PT.const []

@[fun_prop] protected theorem PT.cons {f : α → β} {l : α → List β} (hf : PT f) (hl : PT l) :
    PT (fun a => f a :: l a) := by
  obtain ⟨B, hB, hB'⟩ := hf
  obtain ⟨L, hL, hL'⟩ := hl
  refine ⟨fun x => true :: (leadingOnes (L x) ++ false :: (B x ++ afterOnes (L x))),
    polyTime_cons true (polyTime_append (polyTime_comp polyTime_leadingOnes hL)
      (polyTime_cons false (polyTime_append hB (polyTime_comp polyTime_afterOnes hL)))),
    fun a => ?_⟩
  simp only [hB', hL', leadingOnes_enc_list, afterOnes_enc_list, enc_cons]

@[fun_prop] protected theorem PT.length {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).length) := by
  obtain ⟨L, hL, hL'⟩ := hl
  refine ⟨fun x => leadingOnes (L x) ++ [false],
    polyTime_append (polyTime_comp polyTime_leadingOnes hL) (polyTime_const _), fun a => ?_⟩
  simp only [hL', leadingOnes_enc_list, enc_nat_eq]

@[fun_prop] protected theorem PT.head? {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).head?) := by
  obtain ⟨L, hL, hL'⟩ := hl
  obtain ⟨T, hT, hT'⟩ := exists_take β
  refine ⟨fun x => if (L x).take 1 = [true] then true :: T (afterOnes (L x)) else [false],
    polyTime_ite (polyTime_take_one hL)
      (polyTime_cons true (polyTime_comp hT (polyTime_comp polyTime_afterOnes hL)))
      (polyTime_const _), fun a => ?_⟩
  simp only [hL']
  cases l a with
  | nil => simp
  | cons b t =>
    simp only [afterOnes_enc_list, writeValues_cons, hT']
    simp

@[fun_prop] protected theorem PT.tail {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).tail) := by
  obtain ⟨L, hL, hL'⟩ := hl
  obtain ⟨D, hD, hD'⟩ := exists_drop β
  refine ⟨fun x => if (L x).take 1 = [true]
      then (leadingOnes (L x)).tail ++ false :: D (afterOnes (L x)) else [false],
    polyTime_ite (polyTime_take_one hL)
      (polyTime_append (polyTime_tail (polyTime_comp polyTime_leadingOnes hL))
        (polyTime_cons false (polyTime_comp hD (polyTime_comp polyTime_afterOnes hL))))
      (polyTime_const _), fun a => ?_⟩
  simp only [hL']
  cases l a with
  | nil => simp
  | cons b t =>
    simp only [leadingOnes_enc_list, afterOnes_enc_list, writeValues_cons, hD', List.tail_cons,
      enc_list_eq t]
    simp [List.replicate_succ]

@[fun_prop] protected theorem PT.isEmpty {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).isEmpty) :=
  (PT.isNone (PT.head? hl)).of_eq fun a => by cases l a <;> rfl

@[fun_prop] protected theorem PT.headD {l : α → List β} {d : α → β} (hl : PT l) (hd : PT d) :
    PT (fun a => (l a).headD (d a)) :=
  (PT.getD (PT.head? hl) hd).of_eq fun a => by cases l a <;> rfl

@[fun_prop] protected theorem PT.append {l₁ l₂ : α → List β} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => l₁ a ++ l₂ a) := by
  obtain ⟨L₁, hL₁, hL₁'⟩ := h₁
  obtain ⟨L₂, hL₂, hL₂'⟩ := h₂
  refine ⟨fun x => leadingOnes (L₁ x) ++ (leadingOnes (L₂ x) ++
      false :: (afterOnes (L₁ x) ++ afterOnes (L₂ x))),
    polyTime_append (polyTime_comp polyTime_leadingOnes hL₁)
      (polyTime_append (polyTime_comp polyTime_leadingOnes hL₂)
        (polyTime_cons false (polyTime_append (polyTime_comp polyTime_afterOnes hL₁)
          (polyTime_comp polyTime_afterOnes hL₂)))), fun a => ?_⟩
  simp only [hL₁', hL₂', leadingOnes_enc_list, afterOnes_enc_list]
  rw [enc_list_eq, List.length_append, writeValues_append, ← List.replicate_append_replicate,
    List.append_assoc]

/-- Case analysis on a list (the cons branch in uncurried form). -/
@[fun_prop] protected theorem PT.listElim {l : α → List β} {d : α → γ} {f : α → β → List β → γ}
    (hl : PT l) (hd : PT d) (hf : PT (fun p : α × β × List β => f p.1 p.2.1 p.2.2)) :
    PT (fun a => (l a).head?.elim (d a) (fun b => f a b (l a).tail)) :=
  PT.optionElim (PT.head? hl) hd
    (hf.comp (PT.pair PT.fst' (PT.pair PT.snd' (PT.tail (hl.comp PT.fst')))))

/-- Case analysis on a list, in equational form: `g` is given by `d` where `l` is empty and
by `f` where it is a cons.  This is the robust way to treat a function defined by a `match`
(prove the two equations with `intro a h; simp [h]`). -/
protected theorem PT.of_listCases {l : α → List β} {d : α → γ} {f : α → β → List β → γ}
    {g : α → γ} (hl : PT l) (hd : PT d)
    (hf : PT (fun p : α × β × List β => f p.1 p.2.1 p.2.2))
    (hnil : ∀ a, l a = [] → g a = d a) (hcons : ∀ a b t, l a = b :: t → g a = f a b t) :
    PT g :=
  (PT.listElim hl hd hf).of_eq fun a => by
    cases h : l a with
    | nil => exact (hnil a h).symm
    | cons b t => exact (hcons a b t h).symm

/-- Case analysis on a list, in `match` form.  (`apply` only unifies this with a goal whose
`match` was compiled to the same matcher, i.e. with a generic element type; otherwise use
`PT.of_listCases` or `PT.listElim`.) -/
protected theorem PT.listCases {l : α → List β} {d : α → γ} {f : α → β → List β → γ}
    (hl : PT l) (hd : PT d) (hf : PT (fun p : α × β × List β => f p.1 p.2.1 p.2.2)) :
    PT (fun a => match l a with
      | [] => d a
      | b :: t => f a b t) :=
  PT.of_listCases hl hd hf (fun a h => by simp only [h]) (fun a b t h => by simp only [h])

/-! ### Bounded folds -/

/-- One step of a left fold on the state `(accumulator, remaining list)`. -/
def foldStep (g : σ → β → σ) (p : σ × List β) : σ × List β :=
  (p.2.head?.elim p.1 (fun b => g p.1 b), p.2.tail)

omit [Code β] [Code σ] in
theorem foldStep_iterate (g : σ → β → σ) (i : Nat) (s : σ) (t : List β) :
    (foldStep g)^[i] (s, t) = ((t.take i).foldl g s, t.drop i) := by
  induction i generalizing s t with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => simpa [foldStep] using ih s []
    | cons b t => simpa [foldStep] using ih (g s b) t

/-- **Bounded left fold.**  The step function is given in uncurried form; the accumulator must
stay polynomially bounded in size along all prefixes of the list. -/
protected theorem PT.foldl {f : α → σ → β → σ} {init : α → σ} {l : α → List β}
    (hf : PT (fun p : α × σ × β => f p.1 p.2.1 p.2.2)) (hinit : PT init) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a (pre : List β), pre <+: l a →
      size (pre.foldl (f a) (init a)) ≤ bound (size a)) :
    PT (fun a => (l a).foldl (f a) (init a)) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have hstep : PT (fun p : α × (σ × List β) => foldStep (f p.1) p.2) :=
    PT.pair (PT.optionElim (PT.head? (PT.snd PT.snd')) (PT.fst PT.snd')
      (hf.comp (PT.pair (PT.fst PT.fst') (PT.pair (PT.fst (PT.snd PT.fst')) PT.snd'))))
      (PT.tail (PT.snd PT.snd'))
  have h := PT.iterate (step := fun a => foldStep (f a)) (init := fun a => (init a, l a))
    (n := fun a => (l a).length) hstep (hinit.pair hl) (PT.length hl)
    (fun N => bound N + powerBound c k N) (hbound.add (PolynomialBound.power c k)) ?_
  · exact (PT.fst h).of_eq fun a => by simp [foldStep_iterate]
  · intro a i _
    simp only [foldStep_iterate, size_prod]
    exact Nat.add_le_add (hsize a _ (List.take_prefix i (l a)))
      (Nat.le_trans (size_drop_le _ _) (hk a))

@[fun_prop] protected theorem PT.reverse {l : α → List β} (hl : PT l) :
    PT (fun a => (l a).reverse) := by
  obtain ⟨c, k, hk⟩ := hl.size_le
  have h := PT.foldl (f := fun _ (acc : List β) b => b :: acc) (init := fun _ => [])
    (PT.cons (PT.snd PT.snd') (PT.fst PT.snd')) (PT.const []) hl
    (powerBound c k) (PolynomialBound.power c k) ?_
  · exact h.of_eq fun a => by simp
  · intro a pre hpre
    have h1 : pre.foldl (fun acc b => b :: acc) [] = pre.reverse := by simp
    rw [h1, size_reverse]
    exact Nat.le_trans (size_le_of_prefix hpre) (hk a)

omit [Code β] in
theorem sum_map_le_mul {l : List β} {g : β → Nat} {K : Nat} (h : ∀ b ∈ l, g b ≤ K) :
    (l.map g).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have h1 := h b (List.mem_cons_self ..)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

omit [Code β] in
/-- The size of a mapped list, when the images have size at most `K`. -/
theorem size_map_le {l : List β} {g : β → γ} {K : Nat} (h : ∀ b ∈ l, size (g b) ≤ K) :
    size (l.map g) ≤ l.length * (K + 1) + 1 := by
  have := sum_map_le_mul (g := fun b => size (g b)) h
  rw [size_list, List.length_map, List.map_map, Nat.mul_succ]
  exact Nat.le_trans (Nat.add_le_add_left this _) (by omega)

/-- **Map** (no side condition; the function is given in uncurried form). -/
@[fun_prop] protected theorem PT.map {f : α → β → γ} {l : α → List β}
    (hf : PT (fun p : α × β => f p.1 p.2)) (hl : PT l) :
    PT (fun a => (l a).map (f a)) := by
  obtain ⟨c, k, hk⟩ := hf.size_le
  obtain ⟨cl, kl, hkl⟩ := hl.size_le
  have h := PT.foldl (f := fun a (acc : List γ) b => f a b :: acc) (init := fun _ => [])
    (PT.cons (hf.comp (PT.pair PT.fst' (PT.snd PT.snd'))) (PT.fst PT.snd')) (PT.const []) hl
    (fun N => powerBound cl kl N * (powerBound c k (N + powerBound cl kl N) + 1) + 1)
    ((((PolynomialBound.power cl kl).mul (((PolynomialBound.power c k).comp
      (PolynomialBound.identity.add (PolynomialBound.power cl kl))).add
        (PolynomialBound.constant 1)))).add (PolynomialBound.constant 1)) ?_
  · exact (PT.reverse h).of_eq fun a => by simp
  · intro a pre hpre
    have h1 : pre.foldl (fun acc b => f a b :: acc) [] = (pre.map (f a)).reverse := by simp
    have hlen : pre.length ≤ powerBound cl kl (size a) :=
      Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hpre.length_le (length_lt_size _))) (hkl a)
    have hK : ∀ b ∈ pre, size (f a b) ≤ powerBound c k (size a + powerBound cl kl (size a)) := by
      intro b hb
      have hb' : size b ≤ powerBound cl kl (size a) :=
        Nat.le_trans (size_le_of_mem (hpre.subset hb)) (hkl a)
      have := hk (a, b)
      rw [size_prod] at this
      exact Nat.le_trans this (powerBound_mono c k (Nat.add_le_add_left hb' _))
    rw [h1, size_reverse]
    exact Nat.le_trans (size_map_le hK)
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _)

/-- **Bounded right fold.**  The accumulator must stay polynomially bounded in size along all
suffixes of the list. -/
protected theorem PT.foldr {f : α → β → σ → σ} {init : α → σ} {l : α → List β}
    (hf : PT (fun p : α × β × σ => f p.1 p.2.1 p.2.2)) (hinit : PT init) (hl : PT l)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a (suf : List β), suf <:+ l a →
      size (suf.foldr (f a) (init a)) ≤ bound (size a)) :
    PT (fun a => (l a).foldr (f a) (init a)) := by
  have h := PT.foldl (f := fun a s b => f a b s) (init := init) (l := fun a => (l a).reverse)
    (hf.comp (PT.pair PT.fst' (PT.pair (PT.snd PT.snd') (PT.fst PT.snd')))) hinit
    (PT.reverse hl) bound hbound ?_
  · exact h.of_eq fun a => by simp [List.foldl_reverse]
  · intro a pre hpre
    have h1 : pre.reverse <:+ l a := by
      rw [← List.reverse_prefix, List.reverse_reverse]
      exact hpre
    have h2 := hsize a _ h1
    rwa [List.foldr_reverse] at h2

end Complexity.PT
