module

public import Complexity.Reg.Cmd
import Lean.Elab.Tactic.Omega

/-!
# Compiling register commands to finite-control stack programs

A sound command over `k + 1` registers is realised by a `StackProgram.Program`
over `k + 3` registers: the two extra registers hold the two tape halves while a
`call` simulates the tape machine of the called function, and are empty between
source instructions.  The number of executed stack instructions is at most a
constant (depending on the command only) times the cost of the source execution.
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set branch)
open Complexity.StackProgram (Program Op Encoding mapOp)

set_option backward.isDefEq.respectTransparency false

/-! ### Renaming the registers of a stack program along an injection -/

section Rename

variable {a b : Nat} {L : Type}

/-- Rename the register of a single instruction. -/
def renameOp (ρ : Fin (a + 1) → Fin (b + 1)) : Op a L → Op b L
  | .halt d => .halt d
  | .goto q => .goto q
  | .push j v q => .push (ρ j) v q
  | .pop j e z o => .pop (ρ j) e z o
  | .peek j e z o => .peek (ρ j) e z o

/-- Run a program over registers `Fin (a + 1)` on the registers `ρ i` of a larger family. -/
def rename (ρ : Fin (a + 1) → Fin (b + 1)) (p : Program a L) : Program b L where
  start := p.start
  code := fun q => renameOp ρ (p.code q)

/-- The source registers seen through the renaming. -/
def pull (ρ : Fin (a + 1) → Fin (b + 1)) (R : Regs b) : Regs a := fun i => R (ρ i)

theorem pull_set (ρ : Fin (a + 1) → Fin (b + 1)) (hρ : ∀ i j, ρ i = ρ j → i = j)
    (R : Regs b) (j : Fin (a + 1)) (w : Word) :
    pull ρ (set R (ρ j) w) = set (pull ρ R) j w := by
  funext i
  by_cases h : i = j
  · subst h
    simp [pull]
  · have h' : ρ i ≠ ρ j := fun e => h (hρ i j e)
    simp [pull, StackMachine.set, h, h']

theorem step_rename_halt (ρ : Fin (a + 1) → Fin (b + 1)) (p : Program a L) (q : L)
    (R : Regs b) (result : Bool × Regs a)
    (hs : StackProgram.step p q (pull ρ R) = .inl result) :
    StackProgram.step (rename ρ p) q R = .inl (result.1, R) ∧ result.2 = pull ρ R := by
  cases hc : p.code q with
  | halt d =>
    simp only [StackProgram.step, hc, Sum.inl.injEq] at hs
    subst hs
    simp [StackProgram.step, rename, renameOp, hc]
  | goto q1 => simp [StackProgram.step, hc] at hs
  | push j v q1 => simp [StackProgram.step, hc] at hs
  | pop j e z o => simp [StackProgram.step, hc] at hs
  | peek j e z o => simp [StackProgram.step, hc] at hs

theorem step_rename_next (ρ : Fin (a + 1) → Fin (b + 1)) (hρ : ∀ i j, ρ i = ρ j → i = j)
    (p : Program a L) (q : L) (R : Regs b) (q' : L) (r' : Regs a)
    (hs : StackProgram.step p q (pull ρ R) = .inr (q', r')) :
    ∃ R', StackProgram.step (rename ρ p) q R = .inr (q', R') ∧ pull ρ R' = r' ∧
      ∀ j, (∀ i, ρ i ≠ j) → R' j = R j := by
  cases hc : p.code q with
  | halt d => simp [StackProgram.step, hc] at hs
  | goto q1 =>
    simp only [StackProgram.step, hc, Sum.inr.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨R, by simp [StackProgram.step, rename, renameOp, hc], rfl, fun _ _ => rfl⟩
  | push j v q1 =>
    simp only [StackProgram.step, hc, Sum.inr.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨set R (ρ j) (v :: R (ρ j)),
      by simp [StackProgram.step, rename, renameOp, hc], ?_, ?_⟩
    · rw [pull_set ρ hρ]
      rfl
    · intro j' hj'
      exact StackMachine.set_other R (Ne.symm (hj' j)) _
  | pop j e z o =>
    simp only [StackProgram.step, hc, Sum.inr.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨set R (ρ j) (R (ρ j)).tail,
      by simp [StackProgram.step, rename, renameOp, hc, pull], ?_, ?_⟩
    · rw [pull_set ρ hρ]
      rfl
    · intro j' hj'
      exact StackMachine.set_other R (Ne.symm (hj' j)) _
  | peek j e z o =>
    simp only [StackProgram.step, hc, Sum.inr.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨R, by simp [StackProgram.step, rename, renameOp, hc, pull], rfl, fun _ _ => rfl⟩

/-- A renamed program performs the same computation on the renamed registers, in exactly
the same number of instructions, and leaves every register outside the range untouched. -/
theorem exec_rename (ρ : Fin (a + 1) → Fin (b + 1)) (hρ : ∀ i j, ρ i = ρ j → i = j)
    {p : Program a L} {q : L} {r : Regs a} {t : Nat} {result : Bool × Regs a}
    (h : StackProgram.Exec p q r t result) :
    ∀ R : Regs b, pull ρ R = r →
      ∃ R', StackProgram.Exec (rename ρ p) q R t (result.1, R') ∧ pull ρ R' = result.2 ∧
        ∀ j, (∀ i, ρ i ≠ j) → R' j = R j := by
  induction h with
  | halt hs =>
    intro R hR
    subst hR
    obtain ⟨h1, h2⟩ := step_rename_halt ρ p _ R _ hs
    exact ⟨R, .halt h1, h2.symm, fun _ _ => rfl⟩
  | next hs _ ih =>
    intro R hR
    subst hR
    obtain ⟨R1, h1, h2, h3⟩ := step_rename_next ρ hρ p _ R _ _ hs
    obtain ⟨R', e, h4, h5⟩ := ih R1 h2
    exact ⟨R', .next h1 e, h4, fun j hj => (h5 j hj).trans (h3 j hj)⟩

end Rename

/-! ### Two extra work registers -/

section Lift

variable {k : Nat}

/-- Source register `j` as a register of the compiled program. -/
def emb (j : Fin (k + 1)) : Fin (k + 2 + 1) := ⟨j.val, by omega⟩

/-- Source registers extended by two empty work registers. -/
def lift (r : Regs k) : Regs (k + 2) := fun i => if h : i.val < k + 1 then r ⟨i.val, h⟩ else []

@[simp] theorem lift_emb (r : Regs k) (j : Fin (k + 1)) : lift r (emb j) = r j := by
  simp [lift, emb]

theorem lift_zero (r : Regs k) : lift r 0 = r 0 := lift_emb r 0

theorem set_lift (r : Regs k) (j : Fin (k + 1)) (w : Word) :
    set (lift r) (emb j) w = lift (set r j w) := by
  funext i
  by_cases h : i.val < k + 1
  · by_cases hij : i.val = j.val
    · obtain rfl : i = emb j := Fin.ext hij
      simp [StackMachine.set, lift, emb]
    · have h1 : i ≠ emb j := fun e => hij (congrArg Fin.val e)
      have h2 : (⟨i.val, h⟩ : Fin (k + 1)) ≠ j := fun e => hij (congrArg Fin.val e)
      simp [StackMachine.set, lift, h, h1, h2]
  · have h1 : i ≠ emb j := by
      intro e
      apply h
      rw [e]
      exact j.isLt
    simp [StackMachine.set, lift, h, h1]

theorem lift_init (x : Word) :
    lift (init x : Regs k) = fun j => if j = 0 then x else [] := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [lift, init]
  · have hv : i.val ≠ 0 := fun e => hi (Fin.ext e)
    by_cases h : i.val < k + 1
    · have h2 : (⟨i.val, h⟩ : Fin (k + 1)) ≠ 0 := fun e => hv (congrArg Fin.val e)
      simp [lift, init, h, hi, h2]
    · simp [lift, h, hi]

/-- The register renaming used by a call on register `j`: the simulated machine's
input/output register is `j`, its two tape halves are the two work registers. -/
def callMap (j : Fin (k + 1)) (i : Fin 3) : Fin (k + 2 + 1) :=
  ⟨if i.val = 0 then j.val else k + i.val, by
    have := i.isLt
    have := j.isLt
    split <;> omega⟩

theorem callMap_injective (j : Fin (k + 1)) :
    ∀ i i', callMap j i = callMap j i' → i = i' := by
  intro i i' h
  have h' := congrArg Fin.val h
  simp only [callMap] at h'
  have := j.isLt
  apply Fin.ext
  split at h' <;> split at h' <;> omega

theorem callMap_zero (j : Fin (k + 1)) : callMap j 0 = emb j :=
  Fin.ext (by simp [callMap, emb])

theorem pull_callMap_lift (r : Regs k) (j : Fin (k + 1)) :
    pull (callMap j) (lift r) = TapeToStacks.regs (r j) [] [] := by
  funext i
  rcases TapeToStacks.fin_three_cases i with rfl | rfl | rfl
  · simp [pull, callMap_zero]
  · simp [pull, callMap, lift]
  · simp [pull, callMap, lift]

theorem call_result (r : Regs k) (j : Fin (k + 1)) (out : Word) (R' : Regs (k + 2))
    (h1 : pull (callMap j) R' = TapeToStacks.regs out [] [])
    (h2 : ∀ i, (∀ a, callMap j a ≠ i) → R' i = lift r i) :
    R' = lift (set r j out) := by
  funext i
  by_cases hi : i.val < k + 1
  · by_cases hij : i.val = j.val
    · obtain rfl : i = emb j := Fin.ext hij
      rw [lift_emb, StackMachine.set_same]
      have h := congrFun h1 0
      simpa [pull, callMap_zero] using h
    · have hne : ∀ a, callMap j a ≠ i := by
        intro a e
        have e' := congrArg Fin.val e
        simp only [callMap] at e'
        split at e' <;> omega
      rw [h2 i hne]
      have h3 : (⟨i.val, hi⟩ : Fin (k + 1)) ≠ j := fun e => hij (congrArg Fin.val e)
      simp [lift, hi, StackMachine.set, h3]
  · have hlt := i.isLt
    have hR : R' i = [] := by
      rcases (by omega : i.val = k + 1 ∨ i.val = k + 2) with h | h
      · have e : i = callMap j 1 := Fin.ext (by simp [callMap, h])
        have h := congrFun h1 1
        rw [e]
        simpa [pull] using h
      · have e : i = callMap j 2 := Fin.ext (by simp [callMap, h])
        have h := congrFun h1 2
        rw [e]
        simpa [pull] using h
    rw [hR]
    simp [lift, hi]

end Lift

/-! ### A `while r ≠ []` combinator for stack programs -/

/-- Peek at `j`; when nonempty run the body and test again. Body failure propagates. -/
def whileNonempty {k : Nat} {L : Type} (j : Fin (k + 1)) (body : Program k L) :
    Program k (Sum Bool L) where
  start := .inl false
  code := fun q => match q with
    | .inl false => .peek j (.inl true) (.inr body.start) (.inr body.start)
    | .inl true => .halt true
    | .inr a => mapOp Sum.inr
        (fun b => if b then .goto (.inl false) else .halt false) (body.code a)

theorem step_whileNonempty_body {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) (a : L) (r : Regs k) :
    StackProgram.step (whileNonempty j body) (.inr a) r = match StackProgram.step body a r with
      | .inl (true, out) => .inr (.inl false, out)
      | .inl (false, out) => .inl (false, out)
      | .inr (a', out) => .inr (.inr a', out) := by
  cases hc : body.code a with
  | halt b => cases b <;> simp [StackProgram.step, whileNonempty, hc, mapOp]
  | goto a' => simp [StackProgram.step, whileNonempty, hc, mapOp]
  | push j b a' => simp [StackProgram.step, whileNonempty, hc, mapOp]
  | pop j e z o =>
    simp [StackProgram.step, whileNonempty, hc, mapOp, StackProgram.branch_map]
  | peek j e z o =>
    simp [StackProgram.step, whileNonempty, hc, mapOp, StackProgram.branch_map]

theorem exec_whileNonempty_done {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) (r : Regs k) (hr : r j = []) :
    StackProgram.Exec (whileNonempty j body) (.inl false) r 2 (true, r) := by
  apply StackProgram.Exec.next (q' := .inl true) (r' := r)
  · simp [StackProgram.step, whileNonempty, hr, branch]
  · exact .halt rfl

theorem exec_whileNonempty_next {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) {r : Regs k} {t : Nat} {middle : Regs k} {s : Nat}
    {result : Bool × Regs k} (hr : r j ≠ [])
    (hb : StackProgram.Exec body body.start r t (true, middle))
    (hrest : StackProgram.Exec (whileNonempty j body) (.inl false) middle s result) :
    StackProgram.Exec (whileNonempty j body) (.inl false) r (t + s + 1) result := by
  apply StackProgram.Exec.next (q' := .inr body.start) (r' := r)
  · cases hrj : r j with
    | nil => exact absurd hrj hr
    | cons b tl => cases b <;> simp [StackProgram.step, whileNonempty, hrj, branch]
  · apply StackProgram.exec_link body (whileNonempty j body) Sum.inr hb
    · intro a r a' r' hs
      rw [step_whileNonempty_body, hs]
    · intro a r hs
      exact .next (by rw [step_whileNonempty_body, hs]) hrest

/-! ### Realising each construct -/

/-- `p` realises `c` with slowdown `C`: every source execution of cost `n` is matched by at
most `C * n` stack instructions of `p` on the lifted registers. -/
def Realizes {k : Nat} {L : Type} (c : Cmd k) (p : Program (k + 2) L) (C : Nat) : Prop :=
  ∀ (r : Regs k) (n : Nat) (r' : Regs k), Exec c r n r' →
    ∃ time, time ≤ C * n ∧ StackProgram.Exec p p.start (lift r) time (true, lift r')

theorem realizes_skip {k : Nat} :
    Realizes (Cmd.skip : Cmd k) (StackProgram.stop (k + 2) true) 1 := by
  intro r n r' h
  generalize hcd : (Cmd.skip : Cmd k) = cd at h
  induction h with
  | skip r => exact ⟨1, by omega, StackProgram.exec_stop _ true _⟩
  | weaken h hle ih =>
    obtain ⟨time, ht, he⟩ := ih hcd
    exact ⟨time, by omega, he⟩
  | _ => cases hcd

theorem realizes_push {k : Nat} (j : Fin (k + 1)) (b : Bool) :
    Realizes (Cmd.push j b) (StackProgram.push (emb j) b) 2 := by
  intro r n r' h
  generalize hcd : Cmd.push j b = cd at h
  induction h with
  | push r j' b' =>
    injection hcd with hj hb
    subst hj hb
    have he := StackProgram.exec_push (emb j) b (lift r)
    rw [lift_emb, set_lift] at he
    exact ⟨2, by omega, he⟩
  | weaken h hle ih =>
    obtain ⟨time, ht, he⟩ := ih hcd
    exact ⟨time, by omega, he⟩
  | _ => cases hcd

theorem realizes_pop {k : Nat} (j : Fin (k + 1)) :
    Realizes (Cmd.pop j) (StackProgram.pop (emb j)) 2 := by
  intro r n r' h
  generalize hcd : Cmd.pop j = cd at h
  induction h with
  | pop r j' =>
    injection hcd with hj
    subst hj
    have he := StackProgram.exec_pop (emb j) (lift r)
    rw [lift_emb, set_lift] at he
    exact ⟨2, by omega, he⟩
  | weaken h hle ih =>
    obtain ⟨time, ht, he⟩ := ih hcd
    exact ⟨time, by omega, he⟩
  | _ => cases hcd

theorem realizes_seq {k : Nat} {A B : Type} {c d : Cmd k} {p : Program (k + 2) A}
    {q : Program (k + 2) B} {C D : Nat} (hp : Realizes c p C) (hq : Realizes d q D) :
    Realizes (Cmd.seq c d) (StackProgram.seq p q) (C + D) := by
  intro r n r' h
  generalize hcd : Cmd.seq c d = cd at h
  induction h with
  | @seq c' d' r r1 r2 n m h1 h2 _ _ =>
    injection hcd with hc hd
    subst hc hd
    obtain ⟨t1, ht1, he1⟩ := hp _ _ _ h1
    obtain ⟨t2, ht2, he2⟩ := hq _ _ _ h2
    refine ⟨t1 + t2, ?_, StackProgram.exec_seq p q he1 he2⟩
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  | weaken h hle ih =>
    obtain ⟨time, ht, he⟩ := ih hcd
    exact ⟨time, Nat.le_trans ht (Nat.mul_le_mul_left _ hle), he⟩
  | _ => cases hcd

theorem realizes_cases {k : Nat} {A B G : Type} (j : Fin (k + 1)) {e z o : Cmd k}
    {pe : Program (k + 2) A} {pz : Program (k + 2) B} {po : Program (k + 2) G}
    {Ce Cz Co : Nat} (he : Realizes e pe Ce) (hz : Realizes z pz Cz) (ho : Realizes o po Co) :
    Realizes (Cmd.cases j e z o) (StackProgram.peekCase (emb j) pe pz po) (Ce + Cz + Co + 1) := by
  intro r n r' h
  generalize hcd : Cmd.cases j e z o = cd at h
  induction h with
  | @casesEmpty j' e' z' o' r r' n hr h1 _ =>
    injection hcd with hj h_e h_z h_o
    subst hj h_e h_z h_o
    obtain ⟨t, ht, hx⟩ := he _ _ _ h1
    refine ⟨t + 1, ?_, StackProgram.exec_peekCase_empty (emb j) pe pz po
      (by rw [lift_emb]; exact hr) hx⟩
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  | @casesFalse j' e' z' o' r r' n tl hr h1 _ =>
    injection hcd with hj h_e h_z h_o
    subst hj h_e h_z h_o
    obtain ⟨t, ht, hx⟩ := hz _ _ _ h1
    refine ⟨t + 1, ?_, StackProgram.exec_peekCase_zero (emb j) pe pz po
      (by rw [lift_emb]; exact hr) hx⟩
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  | @casesTrue j' e' z' o' r r' n tl hr h1 _ =>
    injection hcd with hj h_e h_z h_o
    subst hj h_e h_z h_o
    obtain ⟨t, ht, hx⟩ := ho _ _ _ h1
    refine ⟨t + 1, ?_, StackProgram.exec_peekCase_one (emb j) pe pz po
      (by rw [lift_emb]; exact hr) hx⟩
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  | weaken h hle ih =>
    obtain ⟨time, ht, hx⟩ := ih hcd
    exact ⟨time, Nat.le_trans ht (Nat.mul_le_mul_left _ hle), hx⟩
  | _ => cases hcd

theorem realizes_loop {k : Nat} {A : Type} (j : Fin (k + 1)) {body : Cmd k}
    {pb : Program (k + 2) A} {Cb : Nat} (hb : Realizes body pb Cb) :
    Realizes (Cmd.loop j body) (whileNonempty (emb j) pb) (Cb + 2) := by
  intro r n r' h
  generalize hcd : Cmd.loop j body = cd at h
  induction h with
  | @loopDone j' body' r hr =>
    injection hcd with hj hbody
    subst hj hbody
    exact ⟨2, by omega, exec_whileNonempty_done (emb j) pb (lift r) (by rw [lift_emb]; exact hr)⟩
  | @loopStep j' body' r r1 r2 n m hr h1 h2 _ ih2 =>
    injection hcd with hj hbody
    subst hj hbody
    obtain ⟨t, ht, hx⟩ := hb _ _ _ h1
    obtain ⟨s, hs, hy⟩ := ih2 rfl
    refine ⟨t + s + 1, ?_, exec_whileNonempty_next (emb j) pb
      (by rw [lift_emb]; exact hr) hx hy⟩
    simp only [Nat.add_mul, Nat.mul_add] at hs ⊢
    omega
  | weaken h hle ih =>
    obtain ⟨time, ht, hx⟩ := ih hcd
    exact ⟨time, Nat.le_trans ht (Nat.mul_le_mul_left _ hle), hx⟩
  | _ => cases hcd

theorem realizes_call {k : Nat} (f : Word → Word) (t : Nat → Nat) (j : Fin (k + 1))
    (M : Machine)
    (hM : ∀ x : Word, ∃ time tape, time ≤ t x.length ∧
      runInput M time x = some (true, tape) ∧ tape.output = f x) :
    Realizes (Cmd.call f t j) (rename (callMap j) (TapeToStacks.normalized M)) 36 := by
  intro r n r' h
  generalize hcd : Cmd.call f t j = cd at h
  induction h with
  | call f' t' r j' =>
    injection hcd with hf ht hj
    subst hf ht hj
    obtain ⟨time, tape, htime, hrun, hout⟩ := hM (r j)
    obtain ⟨T, hT, he⟩ := TapeToStacks.exec_normalized M time (r j) tape hrun
    obtain ⟨R', hR, hpull, hframe⟩ :=
      exec_rename (callMap j) (callMap_injective j) he (lift r) (pull_callMap_lift r j)
    have hres : R' = lift (set r j (f (r j))) := by
      apply call_result r j (f (r j)) R'
      · rw [hpull, hout]
      · exact hframe
    rw [hres] at hR
    exact ⟨T, by omega, hR⟩
  | weaken h hle ih =>
    obtain ⟨time, ht, hx⟩ := ih hcd
    exact ⟨time, by omega, hx⟩
  | _ => cases hcd

/-- Every sound command is realised by a finite-control stack program with an explicit
finite label encoding and a constant slowdown. -/
theorem exists_program {k : Nat} (c : Cmd k) (hc : c.Sound) :
    ∃ (L : Type) (p : Program (k + 2) L) (_ : Encoding L) (C : Nat), Realizes c p C := by
  induction c with
  | skip => exact ⟨Unit, _, Encoding.unit, 1, realizes_skip⟩
  | push j b => exact ⟨Bool, _, Encoding.bool, 2, realizes_push j b⟩
  | pop j => exact ⟨Bool, _, Encoding.bool, 2, realizes_pop j⟩
  | seq c d ihc ihd =>
    obtain ⟨A, p, ea, C, hp⟩ := ihc hc.1
    obtain ⟨B, q, eb, D, hq⟩ := ihd hc.2
    exact ⟨Sum A B, StackProgram.seq p q, ea.sum eb, C + D, realizes_seq hp hq⟩
  | cases j e z o ihe ihz iho =>
    obtain ⟨A, pe, ea, Ce, he⟩ := ihe hc.1
    obtain ⟨B, pz, eb, Cz, hz⟩ := ihz hc.2.1
    obtain ⟨G, po, eg, Co, ho⟩ := iho hc.2.2
    exact ⟨_, StackProgram.peekCase (emb j) pe pz po,
      Encoding.unit.sum (ea.sum (eb.sum eg)), _, realizes_cases j he hz ho⟩
  | loop j body ih =>
    obtain ⟨A, pb, ea, Cb, hb⟩ := ih hc
    exact ⟨_, whileNonempty (emb j) pb, Encoding.bool.sum ea, _, realizes_loop j hb⟩
  | call f t j =>
    obtain ⟨M, hM⟩ := hc
    exact ⟨_, rename (callMap j) (TapeToStacks.normalized M), TapeToStacks.normalEncoding M, 36,
      realizes_call f t j M hM⟩

/-! ### From commands to stack machines and tape machines -/

/-- A sound command is implemented by a Boolean-stack machine with constant slowdown. -/
theorem exists_stackMachine {k : Nat} (c : Cmd k) (hc : c.Sound) :
    ∃ (S : StackMachine.Machine) (C : Nat), ∀ (x : Word) (n : Nat) (r' : Regs k),
      Exec c (init x) n r' →
      ∃ time registers, time ≤ C * n ∧
        StackMachine.runInput S time x = some (true, registers) ∧ registers 0 = r' 0 := by
  obtain ⟨L, p, e, C, hp⟩ := exists_program c hc
  refine ⟨StackProgram.compile p e, C, ?_⟩
  intro x n r' h
  obtain ⟨time, ht, he⟩ := hp _ _ _ h
  have hrun := StackProgram.compile_exec e he
  rw [lift_init] at hrun
  exact ⟨time, lift r', ht, hrun, lift_zero r'⟩

/-- Test whether register `0` holds exactly the word `[true]` (destroying it). -/
def testTrue (k : Nat) : Program k (Fin 4) where
  start := 0
  code := fun q => if q = 0 then .pop 0 2 2 1
    else if q = 1 then .peek 0 3 2 2
    else if q = 2 then .halt false
    else .halt true

theorem exec_testTrue (k : Nat) (r : Regs k) :
    ∃ time r', time ≤ 3 ∧
      StackProgram.Exec (testTrue k) 0 r time (decide (r 0 = [true]), r') := by
  cases h : r 0 with
  | nil =>
    exact ⟨2, set r 0 [], by omega,
      .next (q' := 2) (r' := set r 0 [])
        (by simp [StackProgram.step, testTrue, h, branch])
        (.halt (by simp [StackProgram.step, testTrue]))⟩
  | cons b tl =>
    cases b with
    | false =>
      exact ⟨2, set r 0 tl, by omega,
        .next (q' := 2) (r' := set r 0 tl)
          (by simp [StackProgram.step, testTrue, h, branch])
          (.halt (by simp [StackProgram.step, testTrue]))⟩
    | true =>
      cases tl with
      | nil =>
        exact ⟨3, set r 0 [], by omega,
          .next (q' := 1) (r' := set r 0 [])
            (by simp [StackProgram.step, testTrue, h, branch])
            (.next (q' := 3) (r' := set r 0 [])
              (by simp [StackProgram.step, testTrue, branch])
              (.halt (by simp [StackProgram.step, testTrue])))⟩
      | cons c tl =>
        exact ⟨3, set r 0 (c :: tl), by omega,
          .next (q' := 1) (r' := set r 0 (c :: tl))
            (by simp [StackProgram.step, testTrue, h, branch])
            (.next (q' := 2) (r' := set r 0 (c :: tl))
              (by cases c <;> simp [StackProgram.step, testTrue, branch])
              (.halt (by simp [StackProgram.step, testTrue])))⟩

/-- A sound command followed by the test "register `0` is `[true]`", as a stack machine. -/
theorem exists_stackDecider {k : Nat} (c : Cmd k) (hc : c.Sound) :
    ∃ (S : StackMachine.Machine) (C : Nat), ∀ (x : Word) (n : Nat) (r' : Regs k),
      Exec c (init x) n r' →
      ∃ time registers, time ≤ C * n + 3 ∧
        StackMachine.runInput S time x = some (decide (r' 0 = [true]), registers) := by
  obtain ⟨L, p, e, C, hp⟩ := exists_program c hc
  refine ⟨StackProgram.compile (StackProgram.seq p (testTrue (k + 2)))
    (e.sum (Encoding.fin 3)), C, ?_⟩
  intro x n r' h
  obtain ⟨time, ht, he⟩ := hp _ _ _ h
  obtain ⟨s, R, hs, hq⟩ := exec_testTrue (k + 2) (lift r')
  rw [lift_zero] at hq
  have hrun := StackProgram.compile_exec (e.sum (Encoding.fin 3))
    (StackProgram.exec_seq p (testTrue (k + 2)) he hq)
  rw [lift_init] at hrun
  exact ⟨time + s, R, by omega, hrun⟩

/-- **Main theorem.** If a sound command, started with the input in register `0` and all
other registers empty, always terminates within polynomially bounded cost and leaves `f x`
in register `0`, then `f` is polynomial-time computable on the single-tape model. -/
theorem polyTime_of_cmd {k : Nat} (c : Cmd k) (hc : c.Sound) (f : Word → Word)
    (bound : Nat → Nat) (hb : PolynomialBound bound)
    (h : ∀ x, ∃ n regs', Exec c (fun j => if j = 0 then x else []) n regs' ∧
        n ≤ bound x.length ∧ regs' 0 = f x) :
    PolyTime f := by
  obtain ⟨S, C, hS⟩ := exists_stackMachine c hc
  apply StackCompile.polyTime_of_stack S (fun n => C * bound n)
    ((PolynomialBound.constant C).mul hb)
  intro x
  obtain ⟨n, regs', he, hn, hout⟩ := h x
  obtain ⟨time, registers, ht, hrun, hreg⟩ := hS x n regs' he
  exact ⟨time, registers, Nat.le_trans ht (Nat.mul_le_mul_left C hn), hrun, hreg.trans hout⟩

/-- **Decision variant.** Under the same hypotheses, the language of all inputs on which the
command leaves exactly `[true]` in register `0` is decided by a polynomial-time machine. -/
theorem decider_of_cmd {k : Nat} (c : Cmd k) (hc : c.Sound) (χ : Word → Word)
    (bound : Nat → Nat) (hb : PolynomialBound bound)
    (h : ∀ x, ∃ n regs', Exec c (fun j => if j = 0 then x else []) n regs' ∧
        n ≤ bound x.length ∧ regs' 0 = χ x) :
    ∃ M : Machine, PolynomialTimeMachine M ∧ ∀ x, Accepts M x ↔ χ x = [true] := by
  obtain ⟨S, C, hS⟩ := exists_stackDecider c hc
  have hrun : ∀ x : Word, ∃ time registers, time ≤ C * bound x.length + 3 ∧
      StackMachine.runInput S time x = some (decide (χ x = [true]), registers) := by
    intro x
    obtain ⟨n, regs', he, hn, hout⟩ := h x
    obtain ⟨time, registers, ht, hr⟩ := hS x n regs' he
    rw [hout] at hr
    have hmul := Nat.mul_le_mul_left C hn
    exact ⟨time, registers, by omega, hr⟩
  refine ⟨StackCompile.compile S, ?_, ?_⟩
  · apply StackCompile.polynomialTimeMachine_of_stack S (fun n => C * bound n + 3)
      (((PolynomialBound.constant C).mul hb).add (PolynomialBound.constant 3))
    intro x
    obtain ⟨time, registers, ht, hr⟩ := hrun x
    exact ⟨time, _, registers, ht, hr⟩
  · intro x
    obtain ⟨time, registers, ht, hr⟩ := hrun x
    rw [StackCompile.accepts_iff S x ⟨time, _, registers, hr⟩]
    constructor
    · intro ⟨time', registers', hr'⟩
      have heq := StackMachine.run_deterministic S (StackMachine.initial S x) hr hr'
      have hd : decide (χ x = [true]) = true := congrArg Prod.fst heq
      exact of_decide_eq_true hd
    · intro hx
      refine ⟨time, registers, ?_⟩
      rw [hr, decide_eq_true hx]

/-- The same decision statement packaged as membership in `P`. -/
theorem inP_of_cmd {k : Nat} (c : Cmd k) (hc : c.Sound) (L : Language)
    (bound : Nat → Nat) (hb : PolynomialBound bound)
    (h : ∀ x, ∃ n regs', Exec c (fun j => if j = 0 then x else []) n regs' ∧
        n ≤ bound x.length ∧ (L x ↔ regs' 0 = [true])) :
    InP L := by
  have h' : ∀ x, ∃ w : Word,
      (∃ n regs', Exec c (fun j => if j = 0 then x else []) n regs' ∧
        n ≤ bound x.length ∧ regs' 0 = w) ∧ (L x ↔ w = [true]) := by
    intro x
    obtain ⟨n, regs', he, hn, hL⟩ := h x
    exact ⟨regs' 0, ⟨n, regs', he, hn, rfl⟩, hL⟩
  obtain ⟨M, hM, hacc⟩ := decider_of_cmd c hc (fun x => Classical.choose (h' x)) bound hb
    (fun x => (Classical.choose_spec (h' x)).1)
  exact ⟨M, hM, fun x => ((Classical.choose_spec (h' x)).2).trans (hacc x).symm⟩

end Complexity.Reg
