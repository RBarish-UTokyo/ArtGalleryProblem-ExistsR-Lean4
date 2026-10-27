module

public import Complexity.Composition
import Lean.Elab.Tactic.Omega

/-!
# A structured register language with subroutine calls

`Cmd k` is a small structured language over `k + 1` Boolean stacks (registers).
Besides single-bit pushes and pops, sequencing, a three-way branch on the top
bit, and a `while r ≠ []` loop, it has a `call f t r` instruction replacing the
contents of register `r` by `f` of it, where `t` is a *declared* time bound.
A command is `Sound` when every declared bound is witnessed by a genuine
single-tape machine (`TimeBounded`).

`Exec c r n r'` is a big-step relation with an explicit cost `n`.  It is closed
under weakening of the cost, so `n` should be read as an upper bound.
`Complexity.Reg.polyTime_of_cmd` (in `Complexity/Reg/Compile.lean`) turns a
polynomial cost bound into `PolyTime`.
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set)

/-- Register contents: `k + 1` Boolean stacks; the head of each list is the top. -/
abbrev Regs (k : Nat) := StackMachine.Registers k

/-- `f` is computed by some tape machine within `t |x|` steps on every input. -/
def TimeBounded (f : Word → Word) (t : Nat → Nat) : Prop :=
  ∃ M : Machine, ∀ x : Word, ∃ time tape, time ≤ t x.length ∧
    runInput M time x = some (true, tape) ∧ tape.output = f x

/-- A polynomial-time function is time bounded by some `powerBound`. -/
theorem TimeBounded.of_polyTime {f : Word → Word} (hf : PolyTime f) :
    ∃ c e, TimeBounded f (powerBound c e) := by
  obtain ⟨M, c, e, hM⟩ := hf
  exact ⟨c, e, M, hM⟩

/-- The output of a time-bounded function is linearly bounded by input length plus time. -/
theorem TimeBounded.length_le {f : Word → Word} {t : Nat → Nat} (hf : TimeBounded f t)
    (x : Word) : (f x).length ≤ x.length + 2 * t x.length := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨time, tape, ht, hrun, hout⟩ := hM x
  have h := runInput_output_length_le M time x (true, tape) hrun
  simp only at h
  rw [hout] at h
  omega

/-- A declared time bound may be enlarged. -/
theorem TimeBounded.mono {f : Word → Word} {t t' : Nat → Nat} (hf : TimeBounded f t)
    (h : ∀ n, t n ≤ t' n) : TimeBounded f t' := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, fun x => ?_⟩
  obtain ⟨time, tape, ht, hrun, hout⟩ := hM x
  exact ⟨time, tape, Nat.le_trans ht (h x.length), hrun, hout⟩

/-- A function with a polynomially bounded time bound is polynomial-time computable. -/
theorem TimeBounded.polyTime {f : Word → Word} {t : Nat → Nat} (hf : TimeBounded f t)
    (ht : PolynomialBound t) : PolyTime f := by
  obtain ⟨c, e, hce⟩ := ht
  obtain ⟨M, hM⟩ := hf.mono hce
  exact ⟨M, c, e, hM⟩

/-- Structured register commands over `k + 1` registers. -/
inductive Cmd (k : Nat) where
  /-- Do nothing. -/
  | skip
  /-- `r := b :: r`. -/
  | push (r : Fin (k + 1)) (b : Bool)
  /-- `r := r.tail`. -/
  | pop (r : Fin (k + 1))
  /-- Run `c`, then `d`. -/
  | seq (c d : Cmd k)
  /-- Branch on the top bit of `r` (which is left unchanged). -/
  | cases (r : Fin (k + 1)) (onEmpty onFalse onTrue : Cmd k)
  /-- `while r ≠ [] do body`. -/
  | loop (r : Fin (k + 1)) (body : Cmd k)
  /-- `r := f r`, where `t` is the declared time bound of `f`. -/
  | call (f : Word → Word) (t : Nat → Nat) (r : Fin (k + 1))

/-- Every declared time bound of a `call` in the command is realised by a tape machine. -/
def Cmd.Sound {k : Nat} : Cmd k → Prop
  | .skip => True
  | .push _ _ => True
  | .pop _ => True
  | .seq c d => c.Sound ∧ d.Sound
  | .cases _ e z o => e.Sound ∧ z.Sound ∧ o.Sound
  | .loop _ body => body.Sound
  | .call f t _ => TimeBounded f t

@[simp] theorem Cmd.sound_skip {k : Nat} : (Cmd.skip : Cmd k).Sound := trivial
@[simp] theorem Cmd.sound_push {k : Nat} (j : Fin (k + 1)) (b : Bool) :
    (Cmd.push j b).Sound := trivial
@[simp] theorem Cmd.sound_pop {k : Nat} (j : Fin (k + 1)) : (Cmd.pop j).Sound := trivial
@[simp] theorem Cmd.sound_seq {k : Nat} (c d : Cmd k) :
    (Cmd.seq c d).Sound ↔ c.Sound ∧ d.Sound := Iff.rfl
@[simp] theorem Cmd.sound_cases {k : Nat} (j : Fin (k + 1)) (e z o : Cmd k) :
    (Cmd.cases j e z o).Sound ↔ e.Sound ∧ z.Sound ∧ o.Sound := Iff.rfl
@[simp] theorem Cmd.sound_loop {k : Nat} (j : Fin (k + 1)) (body : Cmd k) :
    (Cmd.loop j body).Sound ↔ body.Sound := Iff.rfl
@[simp] theorem Cmd.sound_call {k : Nat} (f : Word → Word) (t : Nat → Nat) (j : Fin (k + 1)) :
    (Cmd.call f t j : Cmd k).Sound ↔ TimeBounded f t := Iff.rfl

/-- Big-step execution with an explicit cost.  Every primitive costs `1`, sequencing adds
costs, a branch costs one more than the branch taken, a loop costs one per test, and
`call f t r` costs `t |r| + |r| + 1`.  The cost may always be weakened. -/
inductive Exec {k : Nat} : Cmd k → Regs k → Nat → Regs k → Prop where
  | skip (r : Regs k) : Exec .skip r 1 r
  | push (r : Regs k) (j : Fin (k + 1)) (b : Bool) :
      Exec (.push j b) r 1 (set r j (b :: r j))
  | pop (r : Regs k) (j : Fin (k + 1)) :
      Exec (.pop j) r 1 (set r j (r j).tail)
  | seq {c d : Cmd k} {r r' r'' : Regs k} {n m : Nat}
      (hc : Exec c r n r') (hd : Exec d r' m r'') : Exec (.seq c d) r (n + m) r''
  | casesEmpty {j : Fin (k + 1)} {e z o : Cmd k} {r r' : Regs k} {n : Nat}
      (h : r j = []) (he : Exec e r n r') : Exec (.cases j e z o) r (n + 1) r'
  | casesFalse {j : Fin (k + 1)} {e z o : Cmd k} {r r' : Regs k} {n : Nat} {tl : Word}
      (h : r j = false :: tl) (hz : Exec z r n r') : Exec (.cases j e z o) r (n + 1) r'
  | casesTrue {j : Fin (k + 1)} {e z o : Cmd k} {r r' : Regs k} {n : Nat} {tl : Word}
      (h : r j = true :: tl) (ho : Exec o r n r') : Exec (.cases j e z o) r (n + 1) r'
  | loopDone {j : Fin (k + 1)} {body : Cmd k} {r : Regs k}
      (h : r j = []) : Exec (.loop j body) r 1 r
  | loopStep {j : Fin (k + 1)} {body : Cmd k} {r r' r'' : Regs k} {n m : Nat}
      (h : r j ≠ []) (hb : Exec body r n r') (hl : Exec (.loop j body) r' m r'') :
      Exec (.loop j body) r (n + m + 1) r''
  | call (f : Word → Word) (t : Nat → Nat) (r : Regs k) (j : Fin (k + 1)) :
      Exec (.call f t j) r (t (r j).length + (r j).length + 1) (set r j (f (r j)))
  | weaken {c : Cmd k} {r r' : Regs k} {n m : Nat}
      (h : Exec c r n r') (hle : n ≤ m) : Exec c r m r'

/-- The initial register contents: the input in register `0`, all others empty. -/
def init {k : Nat} (x : Word) : Regs k := fun j => if j = 0 then x else []

@[simp] theorem init_zero {k : Nat} (x : Word) : (init x : Regs k) 0 = x := by
  simp [init]

namespace Exec

variable {k : Nat}

/-- Change the result state and weaken the cost. -/
theorem cast {c : Cmd k} {r r' r'' : Regs k} {n m : Nat} (h : Exec c r n r')
    (hr : r' = r'') (hle : n ≤ m) : Exec c r m r'' := by
  subst hr
  exact h.weaken hle

theorem mono {c : Cmd k} {r r' : Regs k} {n m : Nat} (h : Exec c r n r') (hle : n ≤ m) :
    Exec c r m r' := h.weaken hle

theorem skip' {r r' : Regs k} {n : Nat} (hr : r' = r) (hn : 1 ≤ n) : Exec .skip r n r' :=
  (Exec.skip r).cast hr.symm hn

theorem push' {r r' : Regs k} {j : Fin (k + 1)} {b : Bool} {n : Nat}
    (hr : r' = set r j (b :: r j)) (hn : 1 ≤ n) : Exec (.push j b) r n r' :=
  (Exec.push r j b).cast hr.symm hn

theorem pop' {r r' : Regs k} {j : Fin (k + 1)} {n : Nat}
    (hr : r' = set r j (r j).tail) (hn : 1 ≤ n) : Exec (.pop j) r n r' :=
  (Exec.pop r j).cast hr.symm hn

theorem seq' {c d : Cmd k} {r r' r'' : Regs k} {n m N : Nat}
    (hc : Exec c r n r') (hd : Exec d r' m r'') (hN : n + m ≤ N) :
    Exec (.seq c d) r N r'' :=
  (Exec.seq hc hd).weaken hN

theorem call' {f : Word → Word} {t : Nat → Nat} {r r' : Regs k} {j : Fin (k + 1)} {n : Nat}
    (hr : r' = set r j (f (r j))) (hn : t (r j).length + (r j).length + 1 ≤ n) :
    Exec (.call f t j) r n r' :=
  (Exec.call f t r j).cast hr.symm hn

/-- Branch on an explicitly known register content. -/
theorem cases_of {j : Fin (k + 1)} {e z o : Cmd k} {r r' : Regs k} {n : Nat}
    (h : match r j with
      | [] => Exec e r n r'
      | false :: _ => Exec z r n r'
      | true :: _ => Exec o r n r') :
    Exec (.cases j e z o) r (n + 1) r' := by
  cases hr : r j with
  | nil => rw [hr] at h; exact .casesEmpty hr h
  | cons b tl =>
    cases b with
    | false => rw [hr] at h; exact .casesFalse hr h
    | true => rw [hr] at h; exact .casesTrue hr h

/-- A loop on an empty register stops after one test. -/
theorem loop_nil {j : Fin (k + 1)} {body : Cmd k} {r : Regs k} (h : r j = []) :
    Exec (.loop j body) r 1 r := .loopDone h

/-- A loop on a nonempty register runs the body once, then the loop again. -/
theorem loop_cons {j : Fin (k + 1)} {body : Cmd k} {r r' r'' : Regs k} {n m : Nat}
    {b : Bool} {tl : Word} (h : r j = b :: tl) (hb : Exec body r n r')
    (hl : Exec (.loop j body) r' m r'') : Exec (.loop j body) r (n + m + 1) r'' :=
  .loopStep (by rw [h]; exact List.cons_ne_nil b tl) hb hl

end Exec

end Complexity.Reg
