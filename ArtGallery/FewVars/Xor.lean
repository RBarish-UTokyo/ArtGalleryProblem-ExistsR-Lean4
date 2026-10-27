module

public import ArtGallery.PTime.AGPFormulaPT
public import Mathlib.Data.ZMod.Defs

/-!
# Exclusive or of a list of formulas

`xorList l` holds iff an odd number of the formulas of `l` hold.  It is built as a balanced
binary tree: `xorRound` combines neighbouring formulas with the exclusive or
`fXor φ ψ := (φ ∧ ¬ψ) ∨ (¬φ ∧ ψ)`, halving the length of the list, and `xorList` applies
`log₂ n + 1` rounds.  Each round at most doubles the total size, so the result has size
`O(n · size l)` (the balanced tree avoids the exponential blow-up of a linear chain).

Main results: `holds_xorList` (semantics, through the `ZMod 2` sum `parityOf`) and
`PT.xorList` (polynomial time, via bounded iteration `PT.iterate`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Complexity Complexity.PT Complexity.PT.Code

/-- Exclusive or. -/
def fXor (φ ψ : Formula) : Formula := .or (.and φ (.not ψ)) (.and (.not φ) ψ)

/-- One round: neighbouring formulas are combined by `fXor`. -/
def xorRound (l : List Formula) : List Formula :=
  (List.range ((l.length + 1) / 2)).map fun i =>
    if 2 * i + 1 < l.length then fXor (l.getD (2 * i) fFalse) (l.getD (2 * i + 1) fFalse)
    else l.getD (2 * i) fFalse

/-- **Exclusive or of a list of formulas** (balanced tree). -/
def xorList (l : List Formula) : Formula :=
  (xorRound^[Nat.log2 l.length + 1] l).headD fFalse

theorem xorRound_nil : xorRound [] = [] := rfl

theorem xorRound_single (a : Formula) : xorRound [a] = [a] := by simp [xorRound]

theorem xorRound_cons_cons (a b : Formula) (l : List Formula) :
    xorRound (a :: b :: l) = fXor a b :: xorRound l := by
  unfold xorRound
  rw [show ((a :: b :: l).length + 1) / 2 = (l.length + 1) / 2 + 1 by simp; omega,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ List.cons (by simp) ?_
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.length_cons]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ]
    split_ifs <;> first | rfl | omega

theorem length_xorRound (l : List Formula) : (xorRound l).length = (l.length + 1) / 2 := by
  simp [xorRound]

/-! ## Semantics -/

section Sem

open Classical

/-- The number (mod 2) of formulas of the list that hold. -/
noncomputable def parityOf (x : ℕ → ℝ) (l : List Formula) : ZMod 2 :=
  (l.map fun φ => if φ.Holds x then 1 else 0).sum

theorem parityOf_nil (x : ℕ → ℝ) : parityOf x [] = 0 := rfl

theorem parityOf_cons (x : ℕ → ℝ) (a : Formula) (l : List Formula) :
    parityOf x (a :: l) = (if a.Holds x then 1 else 0) + parityOf x l := by
  simp [parityOf]

theorem holds_fXor_ind (x : ℕ → ℝ) (a b : Formula) :
    (if (fXor a b).Holds x then (1 : ZMod 2) else 0) =
      (if a.Holds x then 1 else 0) + (if b.Holds x then 1 else 0) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases ha : a.Holds x <;> by_cases hb : b.Holds x <;> simp [fXor, ha, hb, h11]

theorem parityOf_xorRound (x : ℕ → ℝ) : ∀ l : List Formula,
    parityOf x (xorRound l) = parityOf x l
  | [] => rfl
  | [_] => by rw [xorRound_single]
  | a :: b :: l => by
    rw [xorRound_cons_cons, parityOf_cons, holds_fXor_ind, parityOf_xorRound x l,
      parityOf_cons, parityOf_cons, add_assoc]

theorem parityOf_iterate (x : ℕ → ℝ) (l : List Formula) (k : ℕ) :
    parityOf x (xorRound^[k] l) = parityOf x l := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, parityOf_xorRound]

theorem length_iterate_le (l : List Formula) (k : ℕ) (h : l.length ≤ 2 ^ k) :
    (xorRound^[k] l).length ≤ 1 := by
  induction k generalizing l with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    rw [length_xorRound]
    rw [pow_succ] at h
    omega

theorem zmod2_cases' (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

/-- **Semantics of `xorList`**: it holds iff an odd number of the formulas hold. -/
theorem holds_xorList (x : ℕ → ℝ) (l : List Formula) :
    (xorList l).Holds x ↔ parityOf x l = 1 := by
  rw [xorList, ← parityOf_iterate x l (Nat.log2 l.length + 1)]
  have hlen := length_iterate_le l (Nat.log2 l.length + 1) (Nat.lt_log2_self).le
  generalize xorRound^[Nat.log2 l.length + 1] l = L at hlen ⊢
  match L, hlen with
  | [], _ => simp [parityOf_nil]
  | [a], _ =>
    rw [List.headD_cons, parityOf_cons, parityOf_nil, add_zero]
    by_cases ha : a.Holds x <;> simp [ha]

end Sem

/-! ## Variables -/

theorem FVars_fXor {S : ℕ → Prop} {a b : Formula} (ha : FVars S a) (hb : FVars S b) :
    FVars S (fXor a b) := ⟨⟨ha, hb⟩, ⟨ha, hb⟩⟩

theorem FVars_xorRound {S : ℕ → Prop} {l : List Formula} (hl : ∀ φ ∈ l, FVars S φ) :
    ∀ φ ∈ xorRound l, FVars S φ := by
  have hget : ∀ i, FVars S (l.getD i fFalse) := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact FVars_fFalse S
    | some φ => exact hl φ (List.mem_of_getElem? h)
  intro φ hφ
  simp only [xorRound, List.mem_map, List.mem_range] at hφ
  obtain ⟨i, _, rfl⟩ := hφ
  split_ifs
  · exact FVars_fXor (hget _) (hget _)
  · exact hget _

theorem FVars_xorList {S : ℕ → Prop} {l : List Formula} (hl : ∀ φ ∈ l, FVars S φ) :
    FVars S (xorList l) := by
  have : ∀ k, ∀ φ ∈ xorRound^[k] l, FVars S φ := by
    intro k
    induction k with
    | zero => exact hl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact FVars_xorRound ih
  unfold xorList
  generalize hL : xorRound^[Nat.log2 l.length + 1] l = L
  have hL' := hL ▸ this (Nat.log2 l.length + 1)
  cases L with
  | nil => exact FVars_fFalse S
  | cons a L => exact hL' a (by simp)

/-! ## Polynomial time -/

theorem size_formula_or (φ ψ : Formula) : size (Formula.or φ ψ) = size φ + size ψ + 6 := by
  simp only [size_formula, Formula.toks, size_cons, size_nat]
  have := size_append φ.toks ψ.toks
  omega

theorem size_formula_and (φ ψ : Formula) : size (Formula.and φ ψ) = size φ + size ψ + 5 := by
  simp only [size_formula, Formula.toks, size_cons, size_nat]
  have := size_append φ.toks ψ.toks
  omega

theorem size_formula_not (φ : Formula) : size (Formula.not φ) = size φ + 5 := by
  simp only [size_formula, Formula.toks, size_cons, size_nat]
  omega

theorem size_fXor (φ ψ : Formula) : size (fXor φ ψ) = 2 * size φ + 2 * size ψ + 26 := by
  simp only [fXor, size_formula_or, size_formula_and, size_formula_not]
  ring

/-- The weight of a list of formulas: the sum of `size φ + 30`. -/
def xorWeight (l : List Formula) : ℕ := (l.map fun φ => size φ + 30).sum

theorem xorWeight_cons (a : Formula) (l : List Formula) :
    xorWeight (a :: l) = size a + 30 + xorWeight l := by
  simp [xorWeight]

theorem xorWeight_xorRound : ∀ l : List Formula, xorWeight (xorRound l) ≤ 2 * xorWeight l
  | [] => by simp [xorRound_nil, xorWeight]
  | [a] => by rw [xorRound_single]; omega
  | a :: b :: l => by
    rw [xorRound_cons_cons, xorWeight_cons, xorWeight_cons, xorWeight_cons, size_fXor]
    have := xorWeight_xorRound l
    omega

theorem xorWeight_iterate (l : List Formula) (k : ℕ) :
    xorWeight (xorRound^[k] l) ≤ 2 ^ k * xorWeight l := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine (xorWeight_xorRound _).trans ?_
    rw [pow_succ]
    have := ih l
    nlinarith

theorem size_le_xorWeight (l : List Formula) : size l ≤ xorWeight l + 1 := by
  rw [size_list]
  induction l with
  | nil => simp [xorWeight]
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons, xorWeight_cons] at ih ⊢; omega

theorem xorWeight_le_size (l : List Formula) : xorWeight l ≤ 30 * size l := by
  rw [size_list]
  induction l with
  | nil => simp [xorWeight]
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons, xorWeight_cons] at ih ⊢; omega

theorem two_pow_log2_succ_le (n : ℕ) : 2 ^ (Nat.log2 n + 1) ≤ 2 * n + 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hn)
    rw [pow_succ]; omega

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.fXor {φ ψ : α → Formula} (hφ : PT φ) (hψ : PT ψ) :
    PT (fun a => fXor (φ a) (ψ a)) := by
  unfold fXor; fun_prop

protected theorem PT.xorRound : PT xorRound := by
  unfold xorRound; fun_prop

/-- **`xorList` is polynomial-time.** -/
@[fun_prop] protected theorem PT.xorList {l : α → List Formula} (hl : PT l) :
    PT (fun a => xorList (l a)) := by
  obtain ⟨p, hp, hmono, hpl⟩ := hl.size_le_mono
  have hit := PT.iterate (step := fun (_ : α) => xorRound) (init := l)
    (n := fun a => Nat.log2 (l a).length + 1) (PT.xorRound.comp PT.snd') hl (by fun_prop)
    (fun N => (2 * p N + 2) * (30 * p N) + 1)
    (((((PolynomialBound.constant 2).mul hp).add (PolynomialBound.constant 2)).mul
      ((PolynomialBound.constant 30).mul hp)).add (PolynomialBound.constant 1)) ?_
  · unfold xorList
    exact PT.headD hit (PT.const _)
  · intro a i hi
    refine (size_le_xorWeight _).trans ?_
    have h1 := xorWeight_iterate (l a) i
    have h2 : 2 ^ i ≤ 2 ^ (Nat.log2 (l a).length + 1) := Nat.pow_le_pow_right (by omega) hi
    have h3 := two_pow_log2_succ_le (l a).length
    have h4 : (l a).length ≤ size (l a) := Nat.le_of_lt (length_lt_size (l a))
    have h5 := xorWeight_le_size (l a)
    have h6 := hpl a
    have h7 : 2 ^ i ≤ 2 * p (size a) + 2 := by omega
    have h8 : xorWeight (l a) ≤ 30 * p (size a) := by omega
    have := Nat.mul_le_mul h7 h8
    omega

end ArtGallery.FewVars

end
