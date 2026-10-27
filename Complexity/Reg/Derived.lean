module

public import Complexity.Reg.Compile
import Lean.Elab.Tactic.Omega

/-!
# Derived register commands and tools for writing `Exec` proofs

* `ofList l` is a canonical way to write down register contents; `regs_simp`
  normalises `set (ofList l) j w` and `ofList l j` for numeral registers `j`.
* `clear`, `move`, `scatter`, `copy`, `pushWord`, `ifTrue` are derived commands
  with proved specifications and costs.
* `exec_loop_inv` is a counted loop-invariant rule.
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set)
open Complexity.StackWords (mapBit)

/-! ### Register contents as lists -/

/-- The `n`-th word of a list, empty beyond its end. -/
def getAt : List Word → Nat → Word
  | [], _ => []
  | a :: _, 0 => a
  | _ :: l, n + 1 => getAt l n

/-- Overwrite the `n`-th word of a list, padding with empty words if necessary. -/
def setAt : List Word → Nat → Word → List Word
  | [], 0, w => [w]
  | [], n + 1, w => [] :: setAt [] n w
  | _ :: l, 0, w => w :: l
  | a :: l, n + 1, w => a :: setAt l n w

@[simp] theorem getAt_nil (n : Nat) : getAt [] n = [] := by cases n <;> rfl
@[simp] theorem getAt_cons_zero (a : Word) (l : List Word) : getAt (a :: l) 0 = a := rfl
@[simp] theorem getAt_cons_succ (a : Word) (l : List Word) (n : Nat) :
    getAt (a :: l) (n + 1) = getAt l n := rfl
@[simp] theorem setAt_nil_zero (w : Word) : setAt [] 0 w = [w] := rfl
@[simp] theorem setAt_nil_succ (n : Nat) (w : Word) :
    setAt [] (n + 1) w = [] :: setAt [] n w := rfl
@[simp] theorem setAt_cons_zero (a : Word) (l : List Word) (w : Word) :
    setAt (a :: l) 0 w = w :: l := rfl
@[simp] theorem setAt_cons_succ (a : Word) (l : List Word) (n : Nat) (w : Word) :
    setAt (a :: l) (n + 1) w = a :: setAt l n w := rfl

theorem getAt_setAt (l : List Word) (n : Nat) (w : Word) (m : Nat) :
    getAt (setAt l n w) m = if m = n then w else getAt l m := by
  induction l generalizing n m with
  | nil =>
    induction n generalizing m with
    | zero => cases m <;> simp
    | succ n ih => cases m <;> simp [ih]
  | cons a l ih =>
    cases n with
    | zero => cases m <;> simp
    | succ n => cases m <;> simp [ih]

/-- Register contents given by a list of words: register `j` holds the `j`-th word, and
registers beyond the end of the list are empty. -/
def ofList {k : Nat} (l : List Word) : Regs k := fun j => getAt l j.val

theorem set_ofList {k : Nat} (l : List Word) (j : Fin (k + 1)) (w : Word) :
    set (ofList l) j w = ofList (setAt l j.val w) := by
  funext i
  simp only [StackMachine.set, ofList, getAt_setAt, Fin.ext_iff]

theorem ofList_apply {k : Nat} (l : List Word) (j : Fin (k + 1)) :
    ofList l j = getAt l j.val := rfl

/-- The initial register contents in list form. -/
theorem init_eq_ofList {k : Nat} (x : Word) : (init x : Regs k) = ofList [x] := by
  funext j
  by_cases h : j = 0
  · subst h
    simp [init, ofList]
  · have hv : j.val ≠ 0 := fun e => h (Fin.ext e)
    obtain ⟨n, hn⟩ : ∃ n, j.val = n + 1 := ⟨j.val - 1, by omega⟩
    simp [init, ofList, h, hn]

theorem fun_eq_ofList {k : Nat} (x : Word) :
    (fun j => if j = 0 then x else [] : Regs k) = ofList [x] := init_eq_ofList x

/-- `polyTime_of_cmd` with the initial registers written as `ofList [x]`. -/
theorem polyTime_of_cmd_ofList {k : Nat} (c : Cmd k) (hc : c.Sound) (f : Word → Word)
    (bound : Nat → Nat) (hb : PolynomialBound bound)
    (h : ∀ x, ∃ n regs', Exec c (ofList [x]) n regs' ∧ n ≤ bound x.length ∧ regs' 0 = f x) :
    PolyTime f := by
  apply polyTime_of_cmd c hc f bound hb
  intro x
  rw [fun_eq_ofList]
  exact h x

theorem val_three {n : Nat} : ((3 : Fin (n + 4)) : Nat) = 3 := rfl
theorem val_four {n : Nat} : ((4 : Fin (n + 5)) : Nat) = 4 := rfl
theorem val_five {n : Nat} : ((5 : Fin (n + 6)) : Nat) = 5 := rfl
theorem val_six {n : Nat} : ((6 : Fin (n + 7)) : Nat) = 6 := rfl
theorem val_seven {n : Nat} : ((7 : Fin (n + 8)) : Nat) = 7 := rfl
theorem val_eight {n : Nat} : ((8 : Fin (n + 9)) : Nat) = 8 := rfl
theorem val_nine {n : Nat} : ((9 : Fin (n + 10)) : Nat) = 9 := rfl
theorem val_ten {n : Nat} : ((10 : Fin (n + 11)) : Nat) = 10 := rfl
theorem val_eleven {n : Nat} : ((11 : Fin (n + 12)) : Nat) = 11 := rfl

/-- Normalise register contents written with `ofList`: evaluates `set (ofList l) j w` and
`ofList l j` for numeral registers `j` (up to register `11`). -/
macro "regs_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [set_ofList, ofList_apply, fun_eq_ofList, init_eq_ofList,
      Fin.val_zero, Fin.val_one, Fin.val_two,
      val_three, val_four, val_five, val_six, val_seven, val_eight, val_nine, val_ten,
      val_eleven, getAt_nil, getAt_cons_zero, getAt_cons_succ, setAt_nil_zero, setAt_nil_succ,
      setAt_cons_zero, setAt_cons_succ] $[$loc]?)

/-- All words of the list are empty. -/
def AllNil : List Word → Prop
  | [] => True
  | a :: l => a = [] ∧ AllNil l

/-- Two lists describe the same register contents: equal entrywise, up to trailing empty
words. -/
def ListEqv : List Word → List Word → Prop
  | [], l' => AllNil l'
  | a :: l, [] => a = [] ∧ AllNil l
  | a :: l, b :: l' => a = b ∧ ListEqv l l'

@[simp] theorem allNil_nil : AllNil [] = True := rfl
@[simp] theorem allNil_cons (a : Word) (l : List Word) :
    AllNil (a :: l) = (a = [] ∧ AllNil l) := rfl
@[simp] theorem listEqv_nil (l' : List Word) : ListEqv [] l' = AllNil l' := rfl
@[simp] theorem listEqv_cons_nil (a : Word) (l : List Word) :
    ListEqv (a :: l) [] = (a = [] ∧ AllNil l) := rfl
@[simp] theorem listEqv_cons_cons (a b : Word) (l l' : List Word) :
    ListEqv (a :: l) (b :: l') = (a = b ∧ ListEqv l l') := rfl

theorem getAt_of_allNil {l : List Word} (h : AllNil l) (n : Nat) : getAt l n = [] := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => exact h.1
    | succ n => exact ih h.2 n

theorem getAt_eq_of_listEqv {l l' : List Word} (h : ListEqv l l') (n : Nat) :
    getAt l n = getAt l' n := by
  induction l generalizing l' n with
  | nil => rw [getAt_nil, getAt_of_allNil h]
  | cons a l ih =>
    cases l' with
    | nil => rw [getAt_nil, getAt_of_allNil (l := a :: l) h]
    | cons b l' =>
      cases n with
      | zero => exact h.1
      | succ n => exact ih h.2 n

/-- `ofList` ignores trailing empty words. -/
theorem ofList_eq_of_eqv {k : Nat} {l l' : List Word} (h : ListEqv l l') :
    (ofList l : Regs k) = ofList l' := by
  funext j
  exact getAt_eq_of_listEqv h j.val

/-- Closing tactic for side goals about `ofList` register contents: normalise with
`regs_simp`, then try `rfl`, `simp`, `omega`, and equality of `ofList`s up to trailing
empty registers. -/
macro "regs" : tactic =>
  `(tactic| ((try regs_simp); first
    | done
    | rfl
    | (simp; done)
    | omega
    | (simp; omega)
    | (apply ofList_eq_of_eqv; simp; done)))

/-! ### Small facts about `set` -/

theorem set_eq_self {k : Nat} (r : Regs k) (j : Fin (k + 1)) (w : Word) (h : r j = w) :
    set r j w = r := by
  subst h
  exact StackWords.set_unchanged r j

/-! ### `clear` -/

section Derived

variable {k : Nat}

/-- Empty a register. -/
def clear (j : Fin (k + 1)) : Cmd k := .loop j (.pop j)

@[simp] theorem sound_clear (j : Fin (k + 1)) : (clear j).Sound := trivial

theorem exec_clear_aux (j : Fin (k + 1)) (xs : Word) (r : Regs k) (hr : r j = xs) :
    Exec (clear j) r (2 * xs.length + 1) (set r j []) := by
  induction xs generalizing r with
  | nil => exact (Exec.loop_nil hr).cast (set_eq_self r j [] hr).symm (by simp)
  | cons b xs ih =>
    have h1 : Exec (.pop j) r 1 (set r j xs) := Exec.pop' (by rw [hr]; rfl) (Nat.le_refl 1)
    have h2 := ih (set r j xs) (StackMachine.set_same r j xs)
    refine (Exec.loop_cons hr h1 h2).cast (StackWords.set_overwrite r j xs []) ?_
    simp only [List.length_cons]
    omega

/-- `clear j` empties register `j` at cost `2 |r j| + 1`. -/
theorem exec_clear (j : Fin (k + 1)) (r : Regs k) :
    Exec (clear j) r (2 * (r j).length + 1) (set r j []) :=
  exec_clear_aux j (r j) r rfl

/-! ### `move` -/

/-- Pop all of `src`, pushing each bit onto `dst`. -/
def move (src dst : Fin (k + 1)) : Cmd k :=
  .loop src (.cases src .skip
    (.seq (.pop src) (.push dst false))
    (.seq (.pop src) (.push dst true)))

@[simp] theorem sound_move (src dst : Fin (k + 1)) : (move src dst).Sound :=
  ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

theorem exec_move_aux (src dst : Fin (k + 1)) (hne : src ≠ dst) (xs : Word) (r : Regs k)
    (hr : r src = xs) :
    Exec (move src dst) r (4 * xs.length + 1)
      (set (set r src []) dst (xs.reverse ++ r dst)) := by
  induction xs generalizing r with
  | nil =>
    refine (Exec.loop_nil hr).cast ?_ (by simp)
    funext a
    by_cases hd : a = dst
    · subst hd
      simp
    · by_cases hs : a = src
      · subst hs
        simp [hd, hr]
      · simp [hd, hs]
  | cons b xs ih =>
    have hbody : Exec (.cases src .skip (.seq (.pop src) (.push dst false))
        (.seq (.pop src) (.push dst true))) r 3 (set (set r src xs) dst (b :: r dst)) := by
      have hpop : Exec (.pop src) r 1 (set r src xs) :=
        Exec.pop' (by rw [hr]; rfl) (Nat.le_refl 1)
      have hpush : Exec (.push dst b) (set r src xs) 1 (set (set r src xs) dst (b :: r dst)) :=
        Exec.push' (by rw [StackMachine.set_other r (Ne.symm hne)]) (Nat.le_refl 1)
      cases b with
      | false => exact .casesFalse hr (.seq hpop hpush)
      | true => exact .casesTrue hr (.seq hpop hpush)
    have h2 := ih (set (set r src xs) dst (b :: r dst)) (by simp [hne])
    refine (Exec.loop_cons hr hbody h2).cast
      (StackWords.transfer_registers src dst hne r b xs) ?_
    simp only [List.length_cons]
    omega

/-- `move src dst`: `dst := src.reverse ++ dst`, `src := []`, at cost `4 |src| + 1`. -/
theorem exec_move (src dst : Fin (k + 1)) (hne : src ≠ dst) (r : Regs k) :
    Exec (move src dst) r (4 * (r src).length + 1)
      (set (set r src []) dst ((r src).reverse ++ r dst)) :=
  exec_move_aux src dst hne (r src) r rfl

/-! ### `scatter` -/

/-- Pop all of `src`; push each bit `b` onto `d1` and the bit `mapBit zero one b`
(that is, `zero` for `false` and `one` for `true`) onto `d2`. -/
def scatter (src d1 d2 : Fin (k + 1)) (zero one : Bool) : Cmd k :=
  .loop src (.cases src .skip
    (.seq (.pop src) (.seq (.push d1 false) (.push d2 zero)))
    (.seq (.pop src) (.seq (.push d1 true) (.push d2 one))))

@[simp] theorem sound_scatter (src d1 d2 : Fin (k + 1)) (zero one : Bool) :
    (scatter src d1 d2 zero one).Sound :=
  ⟨trivial, ⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩

theorem exec_scatter_aux (src d1 d2 : Fin (k + 1))
    (hsf : src ≠ d1) (hss : src ≠ d2) (hfs : d1 ≠ d2) (zero one : Bool)
    (xs : Word) (r : Regs k) (hr : r src = xs) :
    Exec (scatter src d1 d2 zero one) r (5 * xs.length + 1)
      (set (set (set r src []) d1 (xs.reverse ++ r d1)) d2
        (xs.reverse.map (mapBit zero one) ++ r d2)) := by
  induction xs generalizing r with
  | nil =>
    refine (Exec.loop_nil hr).cast ?_ (by simp)
    funext a
    by_cases h2 : a = d2
    · subst h2
      simp
    · by_cases h1 : a = d1
      · subst h1
        simp [h2]
      · by_cases hs : a = src
        · subst hs
          simp [h2, h1, hr]
        · simp [h2, h1, hs]
  | cons b xs ih =>
    have hbody : Exec (.cases src .skip
        (.seq (.pop src) (.seq (.push d1 false) (.push d2 zero)))
        (.seq (.pop src) (.seq (.push d1 true) (.push d2 one)))) r 4
        (set (set (set r src xs) d1 (b :: r d1)) d2 (mapBit zero one b :: r d2)) := by
      have hpop : Exec (.pop src) r 1 (set r src xs) :=
        Exec.pop' (by rw [hr]; rfl) (Nat.le_refl 1)
      have hpush1 : Exec (.push d1 b) (set r src xs) 1 (set (set r src xs) d1 (b :: r d1)) :=
        Exec.push' (by rw [StackMachine.set_other r (Ne.symm hsf)]) (Nat.le_refl 1)
      have hpush2 : Exec (.push d2 (mapBit zero one b)) (set (set r src xs) d1 (b :: r d1)) 1
          (set (set (set r src xs) d1 (b :: r d1)) d2 (mapBit zero one b :: r d2)) :=
        Exec.push' (by
          rw [StackMachine.set_other (set r src xs) (Ne.symm hfs),
            StackMachine.set_other r (Ne.symm hss)]) (Nat.le_refl 1)
      cases b with
      | false => exact .casesFalse hr (.seq hpop (.seq hpush1 hpush2))
      | true => exact .casesTrue hr (.seq hpop (.seq hpush1 hpush2))
    have h2 := ih (set (set (set r src xs) d1 (b :: r d1)) d2 (mapBit zero one b :: r d2))
      (by simp [hsf, hss])
    refine (Exec.loop_cons hr hbody h2).cast
      (StackWords.scatter_registers src d1 d2 hsf hss hfs zero one r b xs) ?_
    simp only [List.length_cons]
    omega

/-- `scatter src d1 d2 zero one`: `d1 := src.reverse ++ d1`,
`d2 := src.reverse.map (mapBit zero one) ++ d2`, `src := []`, at cost `5 |src| + 1`. -/
theorem exec_scatter (src d1 d2 : Fin (k + 1))
    (hsf : src ≠ d1) (hss : src ≠ d2) (hfs : d1 ≠ d2) (zero one : Bool) (r : Regs k) :
    Exec (scatter src d1 d2 zero one) r (5 * (r src).length + 1)
      (set (set (set r src []) d1 ((r src).reverse ++ r d1)) d2
        ((r src).reverse.map (mapBit zero one) ++ r d2)) :=
  exec_scatter_aux src d1 d2 hsf hss hfs zero one (r src) r rfl

/-! ### `copy` -/

/-- Copy `src` onto `dst` using the (empty) scratch register `tmp`. -/
def copy (src dst tmp : Fin (k + 1)) : Cmd k :=
  .seq (move src tmp) (scatter tmp src dst false true)

@[simp] theorem sound_copy (src dst tmp : Fin (k + 1)) : (copy src dst tmp).Sound :=
  ⟨sound_move src tmp, sound_scatter tmp src dst false true⟩

/-- `copy src dst tmp`: `dst := src ++ dst`; `src` is unchanged and `tmp`, which must be
empty initially, is empty again at the end.  Cost `9 |src| + 2`. -/
theorem exec_copy (src dst tmp : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (r : Regs k) (ht : r tmp = []) :
    Exec (copy src dst tmp) r (9 * (r src).length + 2) (set r dst (r src ++ r dst)) := by
  have h1 := exec_move src tmp hst r
  have h2 := exec_scatter tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd false true
    (set (set r src []) tmp ((r src).reverse ++ r tmp))
  refine (Exec.seq h1 h2).cast ?_ ?_
  · funext a
    by_cases hd : a = dst
    · subst hd
      simp [hst, hdt, Ne.symm hsd, ht, StackWords.map_identity]
    · by_cases hs : a = src
      · subst hs
        simp [hd, hst, hdt, ht]
      · by_cases htm : a = tmp
        · subst htm
          simp [hd, hs, ht]
        · simp [hd, hs, htm]
  · simp [ht]
    omega

/-! ### `pushWord` -/

/-- Push a constant word: `j := w ++ j`. -/
def pushWord (j : Fin (k + 1)) : Word → Cmd k
  | [] => .skip
  | b :: w => .seq (pushWord j w) (.push j b)

@[simp] theorem sound_pushWord (j : Fin (k + 1)) (w : Word) : (pushWord j w).Sound := by
  induction w with
  | nil => trivial
  | cons b w ih => exact ⟨ih, trivial⟩

/-- `pushWord j w`: `j := w ++ j` at cost `|w| + 1`. -/
theorem exec_pushWord (j : Fin (k + 1)) (w : Word) (r : Regs k) :
    Exec (pushWord j w) r (w.length + 1) (set r j (w ++ r j)) := by
  induction w with
  | nil => exact (Exec.skip r).cast (set_eq_self r j _ rfl).symm (by simp)
  | cons b w ih =>
    refine (Exec.seq ih (Exec.push _ j b)).cast ?_ (by simp)
    simp

/-! ### `callOn` -/

/-- `callOn f t j` is `Cmd.call f t j`: `j := f j`, with declared time bound `t`. -/
abbrev callOn (f : Word → Word) (t : Nat → Nat) (j : Fin (k + 1)) : Cmd k := .call f t j

/-- `callOn f t j`: `j := f j` at cost `t |r j| + |r j| + 1`. -/
theorem exec_callOn (f : Word → Word) (t : Nat → Nat) (j : Fin (k + 1)) (r : Regs k) :
    Exec (callOn f t j) r (t (r j).length + (r j).length + 1) (set r j (f (r j))) :=
  Exec.call f t r j

/-- A call of a polynomial-time function with a monotone declared bound, on a register
whose length is at most `B`, costs at most `t B + B + 1`. -/
theorem exec_call_le {f : Word → Word} {t : Nat → Nat} {j : Fin (k + 1)} {r r' : Regs k}
    {B n : Nat} (hmono : ∀ a b, a ≤ b → t a ≤ t b) (hB : (r j).length ≤ B)
    (hr : r' = set r j (f (r j))) (hn : t B + B + 1 ≤ n) : Exec (.call f t j) r n r' := by
  have := hmono _ _ hB
  exact Exec.call' hr (by omega)

/-! ### `ifTrue` -/

/-- Run `thenC` if register `j` holds exactly `[true]`, and `elseC` otherwise.
Register `j` is unchanged by the test. -/
def ifTrue (j : Fin (k + 1)) (thenC elseC : Cmd k) : Cmd k :=
  .cases j elseC elseC
    (.seq (.pop j) (.cases j
      (.seq (.push j true) thenC)
      (.seq (.push j true) elseC)
      (.seq (.push j true) elseC)))

@[simp] theorem sound_ifTrue (j : Fin (k + 1)) (thenC elseC : Cmd k) :
    (ifTrue j thenC elseC).Sound ↔ thenC.Sound ∧ elseC.Sound := by
  constructor
  · intro h
    exact ⟨h.2.2.2.1.2, h.1⟩
  · intro h
    exact ⟨h.2, h.2, trivial, ⟨trivial, h.1⟩, ⟨trivial, h.2⟩, ⟨trivial, h.2⟩⟩

theorem exec_ifTrue_pos {j : Fin (k + 1)} {thenC elseC : Cmd k} {r r' : Regs k} {n : Nat}
    (h : r j = [true]) (ht : Exec thenC r n r') :
    Exec (ifTrue j thenC elseC) r (n + 4) r' := by
  have hpop : Exec (.pop j) r 1 (set r j []) := Exec.pop' (by rw [h]; rfl) (Nat.le_refl 1)
  have hpush : Exec (.push j true) (set r j []) 1 r :=
    Exec.push' (by simp [set_eq_self r j [true] h]) (Nat.le_refl 1)
  have hinner : Exec (.cases j (.seq (.push j true) thenC) (.seq (.push j true) elseC)
      (.seq (.push j true) elseC)) (set r j []) (1 + n + 1) r' :=
    .casesEmpty (StackMachine.set_same r j []) (.seq hpush ht)
  exact (Exec.casesTrue h (.seq hpop hinner)).mono (by omega)

theorem exec_ifTrue_neg {j : Fin (k + 1)} {thenC elseC : Cmd k} {r r' : Regs k} {n : Nat}
    (h : r j ≠ [true]) (he : Exec elseC r n r') :
    Exec (ifTrue j thenC elseC) r (n + 4) r' := by
  cases hr : r j with
  | nil => exact (Exec.casesEmpty hr he).mono (by omega)
  | cons b tl =>
    cases b with
    | false => exact (Exec.casesFalse hr he).mono (by omega)
    | true =>
      cases tl with
      | nil => exact absurd hr h
      | cons c tl =>
        have hpop : Exec (.pop j) r 1 (set r j (c :: tl)) :=
          Exec.pop' (by rw [hr]; rfl) (Nat.le_refl 1)
        have hpush : Exec (.push j true) (set r j (c :: tl)) 1 r :=
          Exec.push' (by simp [set_eq_self r j (true :: c :: tl) hr]) (Nat.le_refl 1)
        have hinner : Exec (.cases j (.seq (.push j true) thenC) (.seq (.push j true) elseC)
            (.seq (.push j true) elseC)) (set r j (c :: tl)) (1 + n + 1) r' := by
          cases c with
          | false => exact .casesFalse (StackMachine.set_same r j _) (.seq hpush he)
          | true => exact .casesTrue (StackMachine.set_same r j _) (.seq hpush he)
        exact (Exec.casesTrue hr (.seq hpop hinner)).mono (by omega)

/-! ### A counted loop-invariant rule -/

/-- If `P (n + 1)` guarantees that the loop register is nonempty and that the body, at
cost at most `cost`, re-establishes `P n`, and `P 0` forces the loop register to be empty,
then from `P n` the loop terminates at cost `n * (cost + 1) + 1` in a state satisfying
`P 0`. -/
theorem exec_loop_inv {j : Fin (k + 1)} {body : Cmd k} (P : Nat → Regs k → Prop) (cost : Nat)
    (hstep : ∀ n r, P (n + 1) r → r j ≠ [] ∧ ∃ r', Exec body r cost r' ∧ P n r')
    (hdone : ∀ r, P 0 r → r j = []) :
    ∀ n r, P n r → ∃ r', Exec (.loop j body) r (n * (cost + 1) + 1) r' ∧ P 0 r' := by
  intro n
  induction n with
  | zero =>
    intro r h
    exact ⟨r, (Exec.loop_nil (hdone r h)).mono (by omega), h⟩
  | succ n ih =>
    intro r h
    obtain ⟨hne, r1, hb, hP⟩ := hstep n r h
    obtain ⟨r', hl, hP'⟩ := ih r1 hP
    refine ⟨r', (Exec.loopStep hne hb hl).mono ?_, hP'⟩
    rw [Nat.succ_mul]
    omega

end Derived

end Complexity.Reg
