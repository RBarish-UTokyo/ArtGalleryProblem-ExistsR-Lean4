module

public import Complexity.Reg.Cmd
public import Complexity.Reg.Compile
public import Complexity.Reg.Derived
public import Complexity.Reg.Closure
public import Complexity.Reg.Decide

/-!
# Register programs with subroutine calls: a toolkit for `PolyTime` proofs

* `Complexity.Reg.Cmd` — the language `Cmd k`, soundness of declared time bounds
  (`Cmd.Sound`, `TimeBounded`) and the cost-counting big-step semantics `Exec`.
* `Complexity.Reg.Compile` — compilation to finite-control stack programs
  (register renaming, `Realizes`), and the main theorems `polyTime_of_cmd`,
  `decider_of_cmd`, `inP_of_cmd`.
* `Complexity.Reg.Derived` — register contents as lists (`ofList`, tactics `regs_simp` and
  `regs`), derived commands `clear`, `move`, `scatter`, `copy`, `pushWord`, `callOn`,
  `ifTrue` with specifications, and the loop rule `exec_loop_inv`.
* `Complexity.Reg.Closure` — `polyTime_const`, `polyTime_pair`, `polyTime_append`,
  `unpair`, `polyTime_pair_fst`, `polyTime_pair_snd`, `polyTime_ite`, `polyTime_select`,
  `polyTime_iterate`.
* `Complexity.Reg.Decide` — `decider_of_polyTime`, `inP_of_polyTime`, `inNP_of_polyTime`,
  `polyTime_of_polynomialTimeMachine`.
-/
