module

public import Complexity.Reg.Derived
public import Complexity.Planarity
import Lean.Elab.Tactic.Omega

/-!
# Closure of `PolyTime` under pairing, projections, branching and bounded iteration

Every theorem here is obtained from `polyTime_of_cmd`: a small register program is written
down, its execution is established with the derived-command specifications, and its cost
is bounded by a polynomial.

Iteration uses the library's `Complexity.iterate` (`iterate f (n + 1) x = iterate f n (f x)`),
which has the same recursion as Mathlib's `Nat.iterate`.
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set)
open Complexity.StackWords (mapBit)

/-! ### Constants -/

/-- `x ↦ w`: clear the input and push the constant. -/
def constCmd (w : Word) : Cmd 0 := .seq (clear 0) (pushWord 0 w)

theorem polyTime_const (w : Word) : PolyTime (fun _ => w) := by
  refine polyTime_of_cmd_ofList (constCmd w) ⟨sound_clear 0, sound_pushWord 0 w⟩ _
    (fun n => 2 * n + 1 + (w.length + 1))
    ((((PolynomialBound.constant 2).mul PolynomialBound.identity).add
      (PolynomialBound.constant 1)).add (PolynomialBound.constant (w.length + 1))) ?_
  intro x
  have h1 : Exec (clear 0) (ofList [x] : Regs 0) (2 * x.length + 1) (ofList [[]]) :=
    (exec_clear 0 _).cast (by regs) (by regs)
  have h2 : Exec (pushWord 0 w) (ofList [[]] : Regs 0) (w.length + 1) (ofList [w]) :=
    (exec_pushWord 0 w _).cast (by regs) (by regs)
  exact ⟨_, _, .seq h1 h2, Nat.le_refl _, rfl⟩

/-! ### Pairing -/

/-- Registers: `0` input/output, `1` second copy of the input, `2`, `3` scratch. -/
def pairCmd (f g : Word → Word) (tf tg : Nat → Nat) : Cmd 3 :=
  .seq (copy 0 1 2) (.seq (.call f tf 0) (.seq (.call g tg 1)
    (.seq (move 0 2) (.seq (move 1 3) (.seq (move 3 0)
      (.seq (scatter 2 0 1 true true) (.seq (.push 0 false) (move 1 0))))))))

theorem exec_pairCmd (f g : Word → Word) (tf tg : Nat → Nat) (x : Word) :
    Exec (pairCmd f g tf tg) (ofList [x])
      ((9 * x.length + 2) + ((tf x.length + x.length + 1) + ((tg x.length + x.length + 1) +
        ((4 * (f x).length + 1) + ((4 * (g x).length + 1) + ((4 * (g x).length + 1) +
          ((5 * (f x).length + 1) + (1 + (4 * (f x).length + 1)))))))))
      (ofList [pairWords (f x) (g x), [], [], []]) := by
  have h1 : Exec (copy 0 1 2) (ofList [x] : Regs 3) (9 * x.length + 2) (ofList [x, x]) :=
    (exec_copy 0 1 2 (by decide) (by decide) (by decide) _ (by regs)).cast (by regs) (by regs)
  have h2 : Exec (.call f tf 0) (ofList [x, x] : Regs 3) (tf x.length + x.length + 1)
      (ofList [f x, x]) := Exec.call' (by regs) (by regs)
  have h3 : Exec (.call g tg 1) (ofList [f x, x] : Regs 3) (tg x.length + x.length + 1)
      (ofList [f x, g x]) := Exec.call' (by regs) (by regs)
  have h4 : Exec (move 0 2) (ofList [f x, g x] : Regs 3) (4 * (f x).length + 1)
      (ofList [[], g x, (f x).reverse]) :=
    (exec_move 0 2 (by decide) _).cast (by regs) (by regs)
  have h5 : Exec (move 1 3) (ofList [[], g x, (f x).reverse] : Regs 3) (4 * (g x).length + 1)
      (ofList [[], [], (f x).reverse, (g x).reverse]) :=
    (exec_move 1 3 (by decide) _).cast (by regs) (by regs)
  have h6 : Exec (move 3 0) (ofList [[], [], (f x).reverse, (g x).reverse] : Regs 3)
      (4 * (g x).length + 1) (ofList [g x, [], (f x).reverse, []]) :=
    (exec_move 3 0 (by decide) _).cast (by regs) (by regs)
  have h7 : Exec (scatter 2 0 1 true true) (ofList [g x, [], (f x).reverse, []] : Regs 3)
      (5 * (f x).length + 1)
      (ofList [f x ++ g x, List.replicate (f x).length true, [], []]) :=
    (exec_scatter 2 0 1 (by decide) (by decide) (by decide) true true _).cast
      (by regs_simp; simp [StackWords.map_ones]) (by regs)
  have h8 : Exec (.push 0 false)
      (ofList [f x ++ g x, List.replicate (f x).length true, [], []] : Regs 3) 1
      (ofList [false :: (f x ++ g x), List.replicate (f x).length true, [], []]) :=
    Exec.push' (by regs) (Nat.le_refl 1)
  have h9 : Exec (move 1 0)
      (ofList [false :: (f x ++ g x), List.replicate (f x).length true, [], []] : Regs 3)
      (4 * (f x).length + 1) (ofList [pairWords (f x) (g x), [], [], []]) :=
    (exec_move 1 0 (by decide) _).cast (by regs_simp; simp [pairWords]) (by regs)
  exact .seq h1 (.seq h2 (.seq h3 (.seq h4 (.seq h5 (.seq h6 (.seq h7 (.seq h8 h9)))))))

/-- Polynomial-time functions are closed under pairing. -/
theorem polyTime_pair {f g : Word → Word} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun x => pairWords (f x) (g x)) := by
  obtain ⟨cf, ef, hf'⟩ := TimeBounded.of_polyTime hf
  obtain ⟨cg, eg, hg'⟩ := TimeBounded.of_polyTime hg
  refine polyTime_of_cmd_ofList (pairCmd f g (powerBound cf ef) (powerBound cg eg))
    ⟨sound_copy 0 1 2, hf', hg', sound_move 0 2, sound_move 1 3, sound_move 3 0,
      sound_scatter 2 0 1 true true, trivial, sound_move 1 0⟩ _
    (fun n => 40 * (n + powerBound cf ef n + powerBound cg eg n + 1))
    ((PolynomialBound.constant 40).mul (((PolynomialBound.identity.add
      (PolynomialBound.power cf ef)).add (PolynomialBound.power cg eg)).add
        (PolynomialBound.constant 1))) ?_
  intro x
  have he := exec_pairCmd f g (powerBound cf ef) (powerBound cg eg) x
  have hlf := hf'.length_le x
  have hlg := hg'.length_le x
  exact ⟨_, _, he, by omega, rfl⟩

/-! ### Concatenation -/

/-- Registers: `0` input/output, `1` second copy of the input, `2`, `3` scratch. -/
def appendCmd (f g : Word → Word) (tf tg : Nat → Nat) : Cmd 3 :=
  .seq (copy 0 1 2) (.seq (.call f tf 0) (.seq (.call g tg 1)
    (.seq (move 0 2) (.seq (move 1 3) (.seq (move 3 0) (move 2 0))))))

theorem exec_appendCmd (f g : Word → Word) (tf tg : Nat → Nat) (x : Word) :
    Exec (appendCmd f g tf tg) (ofList [x])
      ((9 * x.length + 2) + ((tf x.length + x.length + 1) + ((tg x.length + x.length + 1) +
        ((4 * (f x).length + 1) + ((4 * (g x).length + 1) + ((4 * (g x).length + 1) +
          (4 * (f x).length + 1)))))))
      (ofList [f x ++ g x, [], [], []]) := by
  have h1 : Exec (copy 0 1 2) (ofList [x] : Regs 3) (9 * x.length + 2) (ofList [x, x]) :=
    (exec_copy 0 1 2 (by decide) (by decide) (by decide) _ (by regs)).cast (by regs) (by regs)
  have h2 : Exec (.call f tf 0) (ofList [x, x] : Regs 3) (tf x.length + x.length + 1)
      (ofList [f x, x]) := Exec.call' (by regs) (by regs)
  have h3 : Exec (.call g tg 1) (ofList [f x, x] : Regs 3) (tg x.length + x.length + 1)
      (ofList [f x, g x]) := Exec.call' (by regs) (by regs)
  have h4 : Exec (move 0 2) (ofList [f x, g x] : Regs 3) (4 * (f x).length + 1)
      (ofList [[], g x, (f x).reverse]) :=
    (exec_move 0 2 (by decide) _).cast (by regs) (by regs)
  have h5 : Exec (move 1 3) (ofList [[], g x, (f x).reverse] : Regs 3) (4 * (g x).length + 1)
      (ofList [[], [], (f x).reverse, (g x).reverse]) :=
    (exec_move 1 3 (by decide) _).cast (by regs) (by regs)
  have h6 : Exec (move 3 0) (ofList [[], [], (f x).reverse, (g x).reverse] : Regs 3)
      (4 * (g x).length + 1) (ofList [g x, [], (f x).reverse, []]) :=
    (exec_move 3 0 (by decide) _).cast (by regs) (by regs)
  have h7 : Exec (move 2 0) (ofList [g x, [], (f x).reverse, []] : Regs 3)
      (4 * (f x).length + 1) (ofList [f x ++ g x, [], [], []]) :=
    (exec_move 2 0 (by decide) _).cast (by regs) (by regs)
  exact .seq h1 (.seq h2 (.seq h3 (.seq h4 (.seq h5 (.seq h6 h7)))))

/-- Polynomial-time functions are closed under concatenation of their outputs. -/
theorem polyTime_append {f g : Word → Word} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun x => f x ++ g x) := by
  obtain ⟨cf, ef, hf'⟩ := TimeBounded.of_polyTime hf
  obtain ⟨cg, eg, hg'⟩ := TimeBounded.of_polyTime hg
  refine polyTime_of_cmd_ofList (appendCmd f g (powerBound cf ef) (powerBound cg eg))
    ⟨sound_copy 0 1 2, hf', hg', sound_move 0 2, sound_move 1 3, sound_move 3 0,
      sound_move 2 0⟩ _
    (fun n => 40 * (n + powerBound cf ef n + powerBound cg eg n + 1))
    ((PolynomialBound.constant 40).mul (((PolynomialBound.identity.add
      (PolynomialBound.power cf ef)).add (PolynomialBound.power cg eg)).add
        (PolynomialBound.constant 1))) ?_
  intro x
  have he := exec_appendCmd f g (powerBound cf ef) (powerBound cg eg) x
  have hlf := hf'.length_le x
  have hlg := hg'.length_le x
  exact ⟨_, _, he, by omega, rfl⟩

/-! ### Unpairing -/

/-- Strip the leading `true`s of a word, counting them, and drop the following `false`. -/
def stripOnes : Word → Nat → Word × Nat
  | true :: w, n => stripOnes w (n + 1)
  | false :: w, n => (w, n)
  | [], n => ([], n)

/-- A total inverse of `pairWords`: read the unary length prefix, drop the separator, and
split the remainder at that length. -/
def unpair (w : Word) : Word × Word :=
  ((stripOnes w 0).1.take (stripOnes w 0).2, (stripOnes w 0).1.drop (stripOnes w 0).2)

theorem stripOnes_replicate (m n : Nat) (z : Word) :
    stripOnes (List.replicate m true ++ false :: z) n = (z, n + m) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    have h := ih (n + 1)
    rw [show n + 1 + m = n + (m + 1) by omega] at h
    simpa [List.replicate_succ, stripOnes] using h

@[simp] theorem unpair_pairWords (x y : Word) : unpair (pairWords x y) = (x, y) := by
  simp [unpair, pairWords, stripOnes_replicate]

theorem stripOnes_length_le (w : Word) (n : Nat) :
    (stripOnes w n).1.length ≤ w.length ∧ (stripOnes w n).2 ≤ n + w.length := by
  induction w generalizing n with
  | nil => simp [stripOnes]
  | cons b w ih =>
    cases b with
    | false => simp [stripOnes]
    | true =>
      have h := ih (n + 1)
      simp only [stripOnes, List.length_cons]
      omega

/-- Phase 1: move the unary prefix of register `0` to the counter register `1` and drop
the separator.  Register `3` is a flag that is nonempty while the scan continues. -/
def stripCmd : Cmd 3 :=
  .seq (.push 3 true)
    (.loop 3 (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0)) (.seq (.pop 0) (.push 1 true))))

theorem exec_stripLoop (w : Word) (n : Nat) :
    Exec (.loop 3 (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0)) (.seq (.pop 0) (.push 1 true))))
      (ofList [w, List.replicate n true, [], [true]] : Regs 3) (4 * w.length + 4)
      (ofList [(stripOnes w n).1, List.replicate (stripOnes w n).2 true, [], []]) := by
  induction w generalizing n with
  | nil =>
    have hbody : Exec (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0)) (.seq (.pop 0) (.push 1 true)))
        (ofList [[], List.replicate n true, [], [true]] : Regs 3) 2
        (ofList [[], List.replicate n true, [], []]) :=
      .casesEmpty (by regs) (Exec.pop' (by regs) (Nat.le_refl 1))
    have hdone : Exec (.loop 3 (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0))
        (.seq (.pop 0) (.push 1 true))))
        (ofList [[], List.replicate n true, [], []] : Regs 3) 1
        (ofList [[], List.replicate n true, [], []]) := Exec.loop_nil (by regs)
    exact (Exec.loop_cons (b := true) (tl := []) (by regs) hbody hdone).cast (by rfl) (by simp)
  | cons b w ih =>
    cases b with
    | false =>
      have hbody : Exec (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0))
          (.seq (.pop 0) (.push 1 true)))
          (ofList [false :: w, List.replicate n true, [], [true]] : Regs 3) 3
          (ofList [w, List.replicate n true, [], []]) :=
        .casesFalse (tl := w) (by regs)
          (.seq (r' := ofList [false :: w, List.replicate n true, [], []])
            (Exec.pop' (by regs) (Nat.le_refl 1)) (Exec.pop' (by regs) (Nat.le_refl 1)))
      have hdone : Exec (.loop 3 (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0))
          (.seq (.pop 0) (.push 1 true))))
          (ofList [w, List.replicate n true, [], []] : Regs 3) 1
          (ofList [w, List.replicate n true, [], []]) := Exec.loop_nil (by regs)
      refine (Exec.loop_cons (b := true) (tl := []) (by regs) hbody hdone).cast (by rfl) ?_
      simp only [List.length_cons]
      omega
    | true =>
      have hbody : Exec (.cases 0 (.pop 3) (.seq (.pop 3) (.pop 0))
          (.seq (.pop 0) (.push 1 true)))
          (ofList [true :: w, List.replicate n true, [], [true]] : Regs 3) 3
          (ofList [w, List.replicate (n + 1) true, [], [true]]) :=
        .casesTrue (tl := w) (by regs)
          (.seq (r' := ofList [w, List.replicate n true, [], [true]])
            (Exec.pop' (by regs) (Nat.le_refl 1))
            (Exec.push' (by regs_simp; simp [List.replicate_succ]) (Nat.le_refl 1)))
      refine (Exec.loop_cons (b := true) (tl := []) (by regs) hbody (ih (n + 1))).cast
        (by rfl) ?_
      simp only [List.length_cons]
      omega

theorem exec_stripCmd (w : Word) :
    Exec stripCmd (ofList [w] : Regs 3) (4 * w.length + 5)
      (ofList [(stripOnes w 0).1, List.replicate (stripOnes w 0).2 true, [], []]) := by
  have h1 : Exec (.push 3 true) (ofList [w] : Regs 3) 1 (ofList [w, [], [], [true]]) :=
    Exec.push' (by regs) (Nat.le_refl 1)
  exact (Exec.seq h1 (exec_stripLoop w 0)).mono (by omega)

/-- Phase 2: move as many bits as the counter register `1` holds from register `0` to
register `2` (reversing them). -/
def takeCmd : Cmd 3 :=
  .loop 1 (.seq (.pop 1)
    (.cases 0 .skip (.seq (.pop 0) (.push 2 false)) (.seq (.pop 0) (.push 2 true))))

theorem exec_takeCmd (n : Nat) (w acc : Word) :
    Exec takeCmd (ofList [w, List.replicate n true, acc, []] : Regs 3) (5 * n + 1)
      (ofList [w.drop n, [], (w.take n).reverse ++ acc, []]) := by
  induction n generalizing w acc with
  | zero => exact (Exec.loop_nil (by regs)).cast (by simp) (by simp)
  | succ n ih =>
    have hpop : Exec (.pop 1) (ofList [w, List.replicate (n + 1) true, acc, []] : Regs 3) 1
        (ofList [w, List.replicate n true, acc, []]) :=
      Exec.pop' (by regs_simp; simp [List.replicate_succ]) (Nat.le_refl 1)
    cases w with
    | nil =>
      have hbody : Exec (.seq (.pop 1) (.cases 0 .skip (.seq (.pop 0) (.push 2 false))
          (.seq (.pop 0) (.push 2 true))))
          (ofList [[], List.replicate (n + 1) true, acc, []] : Regs 3) 3
          (ofList [[], List.replicate n true, acc, []]) :=
        .seq hpop (.casesEmpty (by regs) (.skip _))
      refine (Exec.loop_cons (b := true) (tl := List.replicate n true)
        (by regs_simp; simp [List.replicate_succ]) hbody (ih [] acc)).cast (by simp) (by omega)
    | cons b w =>
      have hinner : Exec (.seq (.pop 0) (.push 2 b))
          (ofList [b :: w, List.replicate n true, acc, []] : Regs 3) 2
          (ofList [w, List.replicate n true, b :: acc, []]) :=
        .seq (r' := ofList [w, List.replicate n true, acc, []])
          (Exec.pop' (by regs) (Nat.le_refl 1)) (Exec.push' (by regs) (Nat.le_refl 1))
      have hbody : Exec (.seq (.pop 1) (.cases 0 .skip (.seq (.pop 0) (.push 2 false))
          (.seq (.pop 0) (.push 2 true))))
          (ofList [b :: w, List.replicate (n + 1) true, acc, []] : Regs 3) 4
          (ofList [w, List.replicate n true, b :: acc, []]) := by
        cases b with
        | false => exact .seq hpop (.casesFalse (tl := w) (by regs) hinner)
        | true => exact .seq hpop (.casesTrue (tl := w) (by regs) hinner)
      refine (Exec.loop_cons (b := true) (tl := List.replicate n true)
        (by regs_simp; simp [List.replicate_succ]) hbody (ih w (b :: acc))).cast (by simp)
        (by omega)

/-- First projection: registers `0` input/output, `1` counter, `2` accumulator, `3` flag. -/
def fstCmd : Cmd 3 := .seq stripCmd (.seq takeCmd (.seq (clear 0) (move 2 0)))

/-- Second projection. -/
def sndCmd : Cmd 3 := .seq stripCmd takeCmd

theorem sound_stripCmd : stripCmd.Sound := ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial⟩

theorem sound_takeCmd : takeCmd.Sound :=
  ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial⟩

theorem exec_sndCmd (w : Word) :
    Exec sndCmd (ofList [w] : Regs 3) (9 * w.length + 6)
      (ofList [(unpair w).2, [], ((stripOnes w 0).1.take (stripOnes w 0).2).reverse, []]) := by
  have h1 := exec_stripCmd w
  have h2 := exec_takeCmd (stripOnes w 0).2 (stripOnes w 0).1 []
  have hl := stripOnes_length_le w 0
  exact (Exec.seq h1 h2).cast (by simp [unpair]) (by omega)

theorem exec_fstCmd (w : Word) :
    Exec fstCmd (ofList [w] : Regs 3) (15 * w.length + 8)
      (ofList [(unpair w).1, [], [], []]) := by
  have hl := stripOnes_length_le w 0
  have hd : ((stripOnes w 0).1.drop (stripOnes w 0).2).length ≤ w.length := by
    rw [List.length_drop]
    omega
  have ht : ((stripOnes w 0).1.take (stripOnes w 0).2).length ≤ w.length := by
    rw [List.length_take]
    omega
  have h3 : Exec (clear 0)
      (ofList [(unpair w).2, [], ((stripOnes w 0).1.take (stripOnes w 0).2).reverse, []] : Regs 3)
      (2 * w.length + 1)
      (ofList [[], [], ((stripOnes w 0).1.take (stripOnes w 0).2).reverse, []]) :=
    (exec_clear 0 _).cast (by regs) (by regs_simp; simp only [unpair]; omega)
  have h4 : Exec (move 2 0)
      (ofList [[], [], ((stripOnes w 0).1.take (stripOnes w 0).2).reverse, []] : Regs 3)
      (4 * w.length + 1) (ofList [(unpair w).1, [], [], []]) :=
    (exec_move 2 0 (by decide) _).cast (by regs_simp; simp [unpair])
      (by regs_simp; simp only [List.length_reverse]; omega)
  have h2 : Exec takeCmd
      (ofList [(stripOnes w 0).1, List.replicate (stripOnes w 0).2 true, [], []] : Regs 3)
      (5 * (stripOnes w 0).2 + 1)
      (ofList [(unpair w).2, [], ((stripOnes w 0).1.take (stripOnes w 0).2).reverse, []]) :=
    (exec_takeCmd (stripOnes w 0).2 (stripOnes w 0).1 []).cast (by simp [unpair])
      (Nat.le_refl _)
  exact (Exec.seq (exec_stripCmd w) (.seq h2 (.seq h3 h4))).mono (by omega)

/-- The first projection of the pairing function is polynomial-time computable. -/
theorem polyTime_pair_fst : PolyTime (fun w => (unpair w).1) := by
  refine polyTime_of_cmd_ofList fstCmd
    ⟨sound_stripCmd, sound_takeCmd, sound_clear 0, sound_move 2 0⟩ _
    (fun n => 15 * n + 8)
    (((PolynomialBound.constant 15).mul PolynomialBound.identity).add
      (PolynomialBound.constant 8)) ?_
  intro w
  exact ⟨_, _, exec_fstCmd w, Nat.le_refl _, rfl⟩

/-- The second projection of the pairing function is polynomial-time computable. -/
theorem polyTime_pair_snd : PolyTime (fun w => (unpair w).2) := by
  refine polyTime_of_cmd_ofList sndCmd ⟨sound_stripCmd, sound_takeCmd⟩ _
    (fun n => 9 * n + 6)
    (((PolynomialBound.constant 9).mul PolynomialBound.identity).add
      (PolynomialBound.constant 6)) ?_
  intro w
  exact ⟨_, _, exec_sndCmd w, Nat.le_refl _, rfl⟩

/-! ### Branching -/

/-- Registers: `0` input/output, `1` the condition, `2` scratch. -/
def iteCmd (c f g : Word → Word) (tc tf tg : Nat → Nat) : Cmd 2 :=
  .seq (copy 0 1 2) (.seq (.call c tc 1) (ifTrue 1 (.call f tf 0) (.call g tg 0)))

theorem exec_iteCmd (c f g : Word → Word) (tc tf tg : Nat → Nat) (x : Word) :
    Exec (iteCmd c f g tc tf tg) (ofList [x])
      ((9 * x.length + 2) + ((tc x.length + x.length + 1) +
        (tf x.length + tg x.length + x.length + 1 + 4)))
      (ofList [if c x = [true] then f x else g x, c x]) := by
  have h1 : Exec (copy 0 1 2) (ofList [x] : Regs 2) (9 * x.length + 2) (ofList [x, x]) :=
    (exec_copy 0 1 2 (by decide) (by decide) (by decide) _ (by regs)).cast (by regs) (by regs)
  have h2 : Exec (.call c tc 1) (ofList [x, x] : Regs 2) (tc x.length + x.length + 1)
      (ofList [x, c x]) := Exec.call' (by regs) (by regs)
  have h3 : Exec (ifTrue 1 (.call f tf 0) (.call g tg 0)) (ofList [x, c x] : Regs 2)
      (tf x.length + tg x.length + x.length + 1 + 4)
      (ofList [if c x = [true] then f x else g x, c x]) := by
    by_cases hc : c x = [true]
    · have hite : (if c x = [true] then f x else g x) = f x := by simp [hc]
      rw [hite]
      exact exec_ifTrue_pos (by regs_simp; exact hc)
        (Exec.call' (by regs) (by regs_simp; omega))
    · have hite : (if c x = [true] then f x else g x) = g x := by simp [hc]
      rw [hite]
      exact exec_ifTrue_neg (by regs_simp; exact hc)
        (Exec.call' (by regs) (by regs_simp; omega))
  exact .seq h1 (.seq h2 h3)

/-- Polynomial-time functions are closed under branching on a polynomial-time test. -/
theorem polyTime_ite {c f g : Word → Word} (hc : PolyTime c) (hf : PolyTime f)
    (hg : PolyTime g) : PolyTime (fun x => if c x = [true] then f x else g x) := by
  obtain ⟨cc, ec, hc'⟩ := TimeBounded.of_polyTime hc
  obtain ⟨cf, ef, hf'⟩ := TimeBounded.of_polyTime hf
  obtain ⟨cg, eg, hg'⟩ := TimeBounded.of_polyTime hg
  refine polyTime_of_cmd_ofList
    (iteCmd c f g (powerBound cc ec) (powerBound cf ef) (powerBound cg eg))
    ⟨sound_copy 0 1 2, hc', (sound_ifTrue 1 _ _).mpr ⟨hf', hg'⟩⟩ _
    (fun n => (9 * n + 2) + ((powerBound cc ec n + n + 1) +
      (powerBound cf ef n + powerBound cg eg n + n + 1 + 4)))
    ((((PolynomialBound.constant 9).mul PolynomialBound.identity).add
      (PolynomialBound.constant 2)).add
      ((((PolynomialBound.power cc ec).add PolynomialBound.identity).add
        (PolynomialBound.constant 1)).add
        ((((((PolynomialBound.power cf ef).add (PolynomialBound.power cg eg)).add
          PolynomialBound.identity).add (PolynomialBound.constant 1)).add
            (PolynomialBound.constant 4))))) ?_
  intro x
  exact ⟨_, _, exec_iteCmd c f g _ _ _ x, Nat.le_refl _, rfl⟩

/-- Selection: on `pairWords c (pairWords x y)` return `x` if `c = [true]`, else `y`. -/
def select (w : Word) : Word :=
  if (unpair w).1 = [true] then (unpair (unpair w).2).1 else (unpair (unpair w).2).2

@[simp] theorem select_pairWords (c x y : Word) :
    select (pairWords c (pairWords x y)) = if c = [true] then x else y := by
  simp [select]

/-- Selection is polynomial-time computable. -/
theorem polyTime_select : PolyTime select :=
  polyTime_ite polyTime_pair_fst
    (polyTime_comp polyTime_pair_fst polyTime_pair_snd)
    (polyTime_comp polyTime_pair_snd polyTime_pair_snd)

/-! ### Bounded iteration -/

/-- Registers: `0` the iterated value, `1` the counter, `2` scratch. -/
def iterateCmd (step init count : Word → Word) (ts ti tc : Nat → Nat) : Cmd 2 :=
  .seq (copy 0 1 2) (.seq (.call count tc 1) (.seq (.call init ti 0)
    (.loop 1 (.seq (.pop 1) (.call step ts 0)))))

theorem exec_iterateLoop (step : Word → Word) (c e B : Nat) (cnt s : Word)
    (hB : ∀ i, i ≤ cnt.length → (iterate step i s).length ≤ B) :
    Exec (.loop 1 (.seq (.pop 1) (.call step (powerBound c e) 0))) (ofList [s, cnt] : Regs 2)
      (cnt.length * (powerBound c e B + B + 3) + 1)
      (ofList [iterate step cnt.length s, []]) := by
  induction cnt generalizing s with
  | nil => exact (Exec.loop_nil (by regs)).cast (by rfl) (by simp)
  | cons b cnt ih =>
    have hpop : Exec (.pop 1) (ofList [s, b :: cnt] : Regs 2) 1 (ofList [s, cnt]) :=
      Exec.pop' (by regs) (Nat.le_refl 1)
    have hs0 : s.length ≤ B := hB 0 (Nat.zero_le _)
    have hmono := powerBound_mono c e hs0
    have hcall : Exec (.call step (powerBound c e) 0) (ofList [s, cnt] : Regs 2)
        (powerBound c e B + B + 1) (ofList [step s, cnt]) :=
      Exec.call' (by regs) (by regs_simp; omega)
    have hrest := ih (step s) (fun i hi => hB (i + 1) (by simp only [List.length_cons]; omega))
    refine (Exec.loop_cons (b := b) (tl := cnt) (by regs) (.seq hpop hcall) hrest).cast
      (by rfl) ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem exec_iterateCmd (step init count : Word → Word) (cs es : Nat) (ti tc : Nat → Nat)
    (B : Nat) (x : Word)
    (hB : ∀ i, i ≤ (count x).length → (iterate step i (init x)).length ≤ B) :
    Exec (iterateCmd step init count (powerBound cs es) ti tc) (ofList [x])
      ((9 * x.length + 2) + ((tc x.length + x.length + 1) + ((ti x.length + x.length + 1) +
        ((count x).length * (powerBound cs es B + B + 3) + 1))))
      (ofList [iterate step (count x).length (init x), []]) := by
  have h1 : Exec (copy 0 1 2) (ofList [x] : Regs 2) (9 * x.length + 2) (ofList [x, x]) :=
    (exec_copy 0 1 2 (by decide) (by decide) (by decide) _ (by regs)).cast (by regs) (by regs)
  have h2 : Exec (.call count tc 1) (ofList [x, x] : Regs 2) (tc x.length + x.length + 1)
      (ofList [x, count x]) := Exec.call' (by regs) (by regs)
  have h3 : Exec (.call init ti 0) (ofList [x, count x] : Regs 2) (ti x.length + x.length + 1)
      (ofList [init x, count x]) := Exec.call' (by regs) (by regs)
  exact .seq h1 (.seq h2 (.seq h3 (exec_iterateLoop step cs es B (count x) (init x) hB)))

/-- **Bounded iteration.** If `step`, `init` and `count` are polynomial-time computable and
all intermediate values stay polynomially bounded in size, then iterating `step` as many
times as the *length* of `count x`, starting from `init x`, is polynomial-time computable. -/
theorem polyTime_iterate {step init count : Word → Word}
    (hstep : PolyTime step) (hinit : PolyTime init) (hcount : PolyTime count)
    (size : Nat → Nat) (hsize : PolynomialBound size)
    (hbound : ∀ x i, i ≤ (count x).length → (iterate step i (init x)).length ≤ size x.length) :
    PolyTime (fun x => iterate step (count x).length (init x)) := by
  obtain ⟨cs, es, hs⟩ := TimeBounded.of_polyTime hstep
  obtain ⟨ci, ei, hi⟩ := TimeBounded.of_polyTime hinit
  obtain ⟨cc, ec, hc⟩ := TimeBounded.of_polyTime hcount
  have hK : PolynomialBound (fun n => powerBound cs es (size n) + size n + 3) :=
    (((PolynomialBound.power cs es).comp hsize).add hsize).add (PolynomialBound.constant 3)
  have hN : PolynomialBound (fun n => n + 2 * powerBound cc ec n) :=
    PolynomialBound.identity.add
      ((PolynomialBound.constant 2).mul (PolynomialBound.power cc ec))
  refine polyTime_of_cmd_ofList
    (iterateCmd step init count (powerBound cs es) (powerBound ci ei) (powerBound cc ec))
    ⟨sound_copy 0 1 2, hc, hi, trivial, hs⟩ _
    (fun n => (9 * n + 2) + ((powerBound cc ec n + n + 1) + ((powerBound ci ei n + n + 1) +
      ((n + 2 * powerBound cc ec n) * (powerBound cs es (size n) + size n + 3) + 1))))
    ((((PolynomialBound.constant 9).mul PolynomialBound.identity).add
      (PolynomialBound.constant 2)).add
      ((((PolynomialBound.power cc ec).add PolynomialBound.identity).add
        (PolynomialBound.constant 1)).add
        ((((PolynomialBound.power ci ei).add PolynomialBound.identity).add
          (PolynomialBound.constant 1)).add
          ((hN.mul hK).add (PolynomialBound.constant 1))))) ?_
  intro x
  have he := exec_iterateCmd step init count cs es (powerBound ci ei) (powerBound cc ec)
    (size x.length) x (hbound x)
  have hlen := hc.length_le x
  have hmul := Nat.mul_le_mul_right
    (powerBound cs es (size x.length) + size x.length + 3) hlen
  exact ⟨_, _, he, by omega, rfl⟩

end Complexity.Reg
