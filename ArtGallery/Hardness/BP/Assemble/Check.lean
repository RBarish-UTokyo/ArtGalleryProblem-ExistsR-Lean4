module

public import ArtGallery.Hardness.BP.Assemble.Construct
public import ArtGallery.Hardness.BP.Assemble.RefDataA
public import ArtGallery.Hardness.BP.Assemble.RefDataB
public import ArtGallery.Hardness.BP.Assemble.RefDataC
public import ArtGallery.Hardness.Sec5.Assemble.Check

/-!
# Boundary-point variant: `constructBP` agrees with the reference vertex lists

`constructBP Φ n` reproduces the vertex lists `refBPA`, `refBPB`, `refBPC` computed by
an independent exact-arithmetic implementation of the construction (not included in this repository) — a kernel-checked equality
(`constructBP_refA`, `constructBP_refB`, `constructBP_refC`), and `numGuardsBP` the guard numbers
computed there.

As in `Sec5/Assemble/Check.lean`, the corridor floors are sorted by the structurally recursive
insertion sort for the check (`constructIBP`), which agrees with `constructBP` whenever all floor
keys are distinct (`floorsOKBP`, itself checked by the kernel).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery
open ArtGallery.Sec5 (Q2 UnitSpec ratCode floorSortI floorOK floor_eq_of_floorOK numC unitSpecs
  leftChain wR vR tR tL vL)
open ArtGallery.Sec5.Corridor

/-- `unitChainBP` with the floor sorted by insertion sort. -/
def unitChainIBP (n k m : ℕ) (u : UnitSpec) : List Q2 :=
  ([c0 (unitInputBP n k m u).S (unitInputBP n k m u).H] ++
      (floorSortI (unitInputBP n k m u)).flatMap (·.2) ++
      [c1 (unitInputBP n k m u).S (unitInputBP n k m u).H]) ++
    placedTmplBP (unitInputBP n k m u) u.kind ++ (unitInputBP n k m u).chainAfter

/-- `unitChainsBP` with insertion sort. -/
def unitChainsIBP (n k : ℕ) : ℕ → List UnitSpec → List (List Q2)
  | _, [] => []
  | m, u :: us => unitChainIBP n k m u :: unitChainsIBP n k (m + 1) us

/-- All floors of the units `m₀, m₀ + 1, …` have distinct keys. -/
def unitsOKBP (n k : ℕ) : ℕ → List UnitSpec → Bool
  | _, [] => true
  | m, u :: us => floorOK (unitInputBP n k m u) && unitsOKBP n k (m + 1) us

theorem unitChainsBP_eq_I {n k : ℕ} : ∀ {m : ℕ} {us : List UnitSpec},
    unitsOKBP n k m us = true → unitChainsBP n k m us = unitChainsIBP n k m us
  | _, [], _ => rfl
  | m, u :: us, h => by
    simp only [unitsOKBP, Bool.and_eq_true] at h
    simp only [unitChainsBP, unitChainsIBP, unitChainsBP_eq_I h.2, List.cons.injEq, and_true]
    simp only [unitChainBP, unitChainIBP, Input.chainBefore, floor_eq_of_floorOK h.1]

/-- `constructPosBP` with insertion sort. -/
def constructIBP (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++
    (unitChainsIBP n (numC Φ) 0 (unitSpecs n Φ).1).flatten ++
    [tR n (numC Φ), tL n (numC Φ)] ++
    ((unitChainsIBP n (numC Φ) 0 (unitSpecs n Φ).2).map (leftChain n)).reverse.flatten ++
    [vL n (numC Φ)]

/-- All corridor floors of the instance have distinct keys. -/
def floorsOKBP (Φ : List ETRINV.Constraint) (n : ℕ) : Bool :=
  unitsOKBP n (numC Φ) 0 (unitSpecs n Φ).1 && unitsOKBP n (numC Φ) 0 (unitSpecs n Φ).2

theorem constructBP_eq_I {Φ : List ETRINV.Constraint} {n : ℕ} (hn : n ≠ 0)
    (h : floorsOKBP Φ n = true) : constructBP Φ n = constructIBP Φ n := by
  simp only [floorsOKBP, Bool.and_eq_true] at h
  rw [constructBP_pos hn]
  simp only [constructPosBP, constructIBP, rightPartBP, leftPartBP, unitChainsBP_eq_I h.1,
    unitChainsBP_eq_I h.2]

/-! ### The three reference instances -/

theorem floorsOKBP_A : floorsOKBP [] 1 = true := by decide +kernel

/-- **Agreement** for `n = 1`, `Φ = []`. -/
theorem constructBP_refA : (constructBP [] 1).map ratCode = refBPA := by
  rw [constructBP_eq_I (by norm_num) floorsOKBP_A]
  decide +kernel

theorem floorsOKBP_B : floorsOKBP [.one 0, .add 0 0 0, .inv 0 0] 1 = true := by decide +kernel

/-- **Agreement** for `n = 1`, `Φ = [one 0, add 0 0 0, inv 0 0]` (all four unit kinds). -/
theorem constructBP_refB : (constructBP [.one 0, .add 0 0 0, .inv 0 0] 1).map ratCode = refBPB := by
  rw [constructBP_eq_I (by norm_num) floorsOKBP_B]
  decide +kernel

theorem floorsOKBP_C : floorsOKBP [.inv 1 0, .add 1 0 1, .one 1] 2 = true := by decide +kernel

/-- **Agreement** for `n = 2`, `Φ = [inv 1 0, add 1 0 1, one 1]`. -/
theorem constructBP_refC : (constructBP [.inv 1 0, .add 1 0 1, .one 1] 2).map ratCode = refBPC := by
  rw [constructBP_eq_I (by norm_num) floorsOKBP_C]
  decide +kernel

/-! ### The guard numbers -/

theorem numGuardsBP_refA : numGuardsBP [] 1 = 46 := by decide
theorem numGuardsBP_refB : numGuardsBP [.one 0, .add 0 0 0, .inv 0 0] 1 = 67 := by decide
theorem numGuardsBP_refC : numGuardsBP [.inv 1 0, .add 1 0 1, .one 1] 2 = 113 := by decide

end ArtGallery.BP

end
