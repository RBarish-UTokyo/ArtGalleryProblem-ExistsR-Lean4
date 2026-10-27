module

public import Complexity.Reg.Derived
import Lean.Elab.Tactic.Omega

/-!
# Decision procedures and characteristic functions

* A polynomial-time function `χ` yields a polynomial-time *decider* accepting exactly the
  inputs with `χ x = [true]`; hence `inP_of_polyTime` and `inNP_of_polyTime`.
* Conversely a total polynomial-time decider yields a polynomial-time characteristic
  function with values `[true]` / `[false]`.  This direction simulates the decider, with
  either halting decision, on three stacks (`TapeToStacks.simulate_core`), erases all work
  data and writes the decision bit.
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set)
open Complexity.StackProgram (Program Op Encoding mapOp)
open Complexity.TapeToStacks (regs)

set_option backward.isDefEq.respectTransparency false

/-! ### From characteristic functions to deciders -/

/-- A polynomial-time function `χ` yields a polynomial-time machine accepting exactly the
inputs `x` with `χ x = [true]`. -/
theorem decider_of_polyTime {χ : Word → Word} (hχ : PolyTime χ) :
    ∃ M : Machine, PolynomialTimeMachine M ∧ ∀ x, Accepts M x ↔ χ x = [true] := by
  obtain ⟨c, e, hc⟩ := TimeBounded.of_polyTime hχ
  refine decider_of_cmd (k := 0) (.call χ (powerBound c e) 0) hc χ
    (fun n => powerBound c e n + n + 1)
    (((PolynomialBound.power c e).add PolynomialBound.identity).add
      (PolynomialBound.constant 1)) ?_
  intro x
  exact ⟨_, _, Exec.call χ (powerBound c e) _ 0, Nat.le_refl _, by simp⟩

/-- A polynomial-time 0/1-valued function decides a language in P. -/
theorem inP_of_polyTime {L : Language} {χ : Word → Word} (hχ : PolyTime χ)
    (h : ∀ x, L x ↔ χ x = [true]) : InP L := by
  obtain ⟨M, hM, hacc⟩ := decider_of_polyTime hχ
  exact ⟨M, hM, fun x => (h x).trans (hacc x).symm⟩

/-- NP from a polynomial-time checking function. -/
theorem inNP_of_polyTime {L : Language} {χ : Word → Word} (hχ : PolyTime χ) (c e : Nat)
    (h : ∀ x, L x ↔ ∃ w : Word, w.length ≤ powerBound c e x.length ∧
      χ (pairWords x w) = [true]) :
    InNP L := by
  obtain ⟨M, hM, hacc⟩ := decider_of_polyTime hχ
  refine ⟨M, c, e, hM, fun x => (h x).trans ⟨?_, ?_⟩⟩
  · intro ⟨w, hw, hx⟩
    exact ⟨w, hw, (hacc _).mpr hx⟩
  · intro ⟨w, hw, hx⟩
    exact ⟨w, hw, (hacc _).mp hx⟩

/-! ### From deciders to characteristic functions -/

/-- Run `p`; when it halts with decision `b`, continue with `q b`. -/
def bind {k : Nat} {A B : Type} (p : Program k A) (q : Bool → Program k B) :
    Program k (Sum A (Bool × B)) where
  start := .inl p.start
  code := fun label => match label with
    | .inl a => mapOp Sum.inl (fun b => .goto (.inr (b, (q b).start))) (p.code a)
    | .inr (b, x) => mapOp (fun y => .inr (b, y)) Op.halt ((q b).code x)

theorem step_bind_left {k : Nat} {A B : Type} (p : Program k A) (q : Bool → Program k B)
    (a : A) (r : Regs k) :
    StackProgram.step (bind p q) (.inl a) r = match StackProgram.step p a r with
      | .inl (b, out) => .inr (.inr (b, (q b).start), out)
      | .inr (a', out) => .inr (.inl a', out) := by
  cases hc : p.code a with
  | halt b => simp [StackProgram.step, bind, hc, mapOp]
  | goto a' => simp [StackProgram.step, bind, hc, mapOp]
  | push j b a' => simp [StackProgram.step, bind, hc, mapOp]
  | pop j e z o => simp [StackProgram.step, bind, hc, mapOp, StackProgram.branch_map]
  | peek j e z o => simp [StackProgram.step, bind, hc, mapOp, StackProgram.branch_map]

/-- `bind` adds the exact instruction counts (the halt of `p` becomes the connecting jump). -/
theorem exec_bind {k : Nat} {A B : Type} (p : Program k A) (q : Bool → Program k B)
    {a : A} {r : Regs k} {t : Nat} {b : Bool} {middle : Regs k} {s : Nat}
    {result : Bool × Regs k}
    (hp : StackProgram.Exec p a r t (b, middle))
    (hq : StackProgram.Exec (q b) (q b).start middle s result) :
    StackProgram.Exec (bind p q) (.inl a) r (t + s) result := by
  apply StackProgram.exec_link p (bind p q) Sum.inl hp
  · intro a r a' r' hs
    rw [step_bind_left, hs]
  · intro a r hs
    exact .next (by rw [step_bind_left, hs])
      (StackProgram.exec_embed (q b) (bind p q) (fun y => .inr (b, y)) (by intro x; rfl) hq)

/-- Erase the two tape registers and the io register, then write the single bit `b`. -/
def writeBit (b : Bool) : Program 2 (Sum Bool (Sum Bool (Sum Bool Bool))) :=
  StackProgram.seq (StackWords.clear 1) (StackProgram.seq (StackWords.clear 2)
    (StackProgram.seq (StackWords.clear 0) (StackProgram.push 0 b)))

theorem exec_writeBit (b : Bool) (io left right : List Bool) :
    StackProgram.Exec (writeBit b) (writeBit b).start (regs io left right)
      (left.length + 2 + (right.length + 2 + (io.length + 2 + 2)))
      (true, regs [b] [] []) := by
  have h1 := StackWords.exec_clear (k := 2) 1 (regs io left right)
  simp only [TapeToStacks.regs_one, TapeToStacks.set_regs_one] at h1
  have h2 := StackWords.exec_clear (k := 2) 2 (regs io [] right)
  simp only [TapeToStacks.regs_two, TapeToStacks.set_regs_two] at h2
  have h3 := StackWords.exec_clear (k := 2) 0 (regs io [] [])
  simp only [TapeToStacks.regs_zero, TapeToStacks.set_regs_zero] at h3
  have h4 := StackProgram.exec_push (k := 2) 0 b (regs [] [] [])
  simp only [TapeToStacks.regs_zero, TapeToStacks.set_regs_zero] at h4
  exact StackProgram.exec_seq _ _ h1 (StackProgram.exec_seq _ _ h2
    (StackProgram.exec_seq _ _ h3 h4))

abbrev DecideLabel (M : Machine) :=
  Sum (Sum (Fin 4) (Fin 6))
    (Sum (TapeToStacks.Label M) (Bool × Sum Bool (Sum Bool (Sum Bool Bool))))

/-- Simulate the decider `M` and leave its decision bit as the only content of register 0. -/
def decideProgram (M : Machine) : Program 2 (DecideLabel M) :=
  StackProgram.seq TapeToStacks.initializer (bind (TapeToStacks.core M) writeBit)

def decideEncoding (M : Machine) : Encoding (DecideLabel M) :=
  Encoding.sum (Encoding.sum (Encoding.fin 3) (Encoding.fin 5))
    (Encoding.sum (TapeToStacks.labelEncoding M)
      (Encoding.bool.prod (Encoding.bool.sum (Encoding.bool.sum
        (Encoding.bool.sum Encoding.bool)))))

theorem exec_decideProgram (M : Machine) (fuel : Nat) (input : List Bool) (b : Bool)
    (out : Tape) (h : runInput M fuel input = some (b, out)) :
    ∃ time, time ≤ 7 * input.length + 8 * fuel + 16 ∧
      StackProgram.Exec (decideProgram M) (decideProgram M).start (regs input [] []) time
        (true, regs [b] [] []) := by
  obtain ⟨time, ht, he⟩ := TapeToStacks.simulate_core M fuel input b out h []
  have hw := exec_writeBit b [] (TapeToStacks.symbols out.left)
    (TapeToStacks.symbols (out.read :: out.right.drop 1))
  have hfull := StackProgram.exec_seq TapeToStacks.initializer
    (bind (TapeToStacks.core M) writeBit) (TapeToStacks.exec_initializer input)
    (exec_bind (TapeToStacks.core M) writeBit he hw)
  have hlen := TapeToStacks.restore_head_length_le out
  have hsize := run_size_le M fuel (initial M input) (b, out) h
  simp only [initial, Tape.size_ofInput] at hsize
  simp only [Tape.size] at hsize
  simp only [TapeToStacks.symbols_length, List.length_nil] at hfull
  exact ⟨_, by omega, hfull⟩

/-- The stack machine computing the characteristic function of the decider `M`. -/
def decideMachine (M : Machine) : StackMachine.Machine :=
  StackProgram.compile (decideProgram M) (decideEncoding M)

theorem run_decideMachine (M : Machine) (fuel : Nat) (input : List Bool) (b : Bool)
    (out : Tape) (h : runInput M fuel input = some (b, out)) :
    ∃ time, time ≤ 7 * input.length + 8 * fuel + 16 ∧
      StackMachine.runInput (decideMachine M) time input = some (true, regs [b] [] []) := by
  obtain ⟨time, ht, he⟩ := exec_decideProgram M fuel input b out h
  exact ⟨time, ht, by
    simpa only [StackMachine.runInput, StackMachine.initial, decideMachine,
      StackProgram.compile, TapeToStacks.registers_initial]
      using StackProgram.compile_exec (decideEncoding M) he⟩

/-- Conversely a total polynomial-time decider yields a polynomial-time characteristic
function: `χ x = [true]` exactly on the accepted inputs, and `χ x = [false]` otherwise. -/
theorem polyTime_of_polynomialTimeMachine {M : Machine} (hM : PolynomialTimeMachine M) :
    ∃ χ : Word → Word, PolyTime χ ∧
      ∀ x, (χ x = [true] ↔ Accepts M x) ∧ (χ x = [true] ∨ χ x = [false]) := by
  obtain ⟨c, e, hM⟩ := hM
  have hdec : ∀ x : Word, ∃ b : Bool, ∃ time tape,
      time ≤ powerBound c e x.length ∧ runInput M time x = some (b, tape) := by
    intro x
    obtain ⟨time, b, tape, ht, hr⟩ := hM x
    exact ⟨b, time, tape, ht, hr⟩
  refine ⟨fun x => [Classical.choose (hdec x)], ?_, ?_⟩
  · apply StackCompile.polyTime_of_stack (decideMachine M)
      (fun n => 7 * n + 8 * powerBound c e n + 16)
      ((((PolynomialBound.constant 7).mul PolynomialBound.identity).add
        ((PolynomialBound.constant 8).mul (PolynomialBound.power c e))).add
          (PolynomialBound.constant 16))
    intro x
    obtain ⟨time, tape, ht, hr⟩ := Classical.choose_spec (hdec x)
    obtain ⟨T, hT, hrun⟩ := run_decideMachine M time x _ tape hr
    exact ⟨T, _, by omega, hrun, rfl⟩
  · intro x
    obtain ⟨time, tape, ht, hr⟩ := Classical.choose_spec (hdec x)
    constructor
    · constructor
      · intro hx
        have hb : Classical.choose (hdec x) = true := by simpa using hx
        rw [hb] at hr
        exact ⟨time, tape, hr⟩
      · intro ⟨time', tape', hr'⟩
        have heq := run_deterministic M (initial M x) hr hr'
        have hb : Classical.choose (hdec x) = true := congrArg Prod.fst heq
        exact congrArg (fun b : Bool => [b]) hb
    · cases Classical.choose (hdec x) <;> simp

end Complexity.Reg
