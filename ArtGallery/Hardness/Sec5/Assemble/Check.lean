module

public import ArtGallery.Hardness.Sec5.Assemble.Construct
public import ArtGallery.Hardness.Sec5.Assemble.RefData
public import ArtGallery.Hardness.Sec5.Assemble.RefDataC
public import ArtGallery.Hardness.Sec5.Corridor.Floor

/-!
# Section 5: `construct` agrees with the reference vertex lists

`construct Φ n` reproduces the vertex lists `refA`, `refB`, `refC` (`RefData.lean`) computed by
an independent exact-arithmetic implementation of the construction (not included in this repository) — a kernel-checked equality
(`construct_refA`, `construct_refB`, `construct_refC`).

The corridor floor is sorted with `List.mergeSort` (well-founded recursion, which the kernel does
not evaluate).  For the check we use the structurally recursive `constructI`, in which the floor
is sorted by insertion sort, and prove `construct = constructI` whenever all floor keys are
distinct (`floorsOK`, itself checked by the kernel): both sorts then give the unique strictly
sorted permutation (`Corridor.mergeSort_eq_of_perm`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Corridor

/-- The code `(num x, den x, num y, den y)` of a rational point. -/
def ratCode (p : Q2) : ℤ × ℕ × ℤ × ℕ := (p.1.num, p.1.den, p.2.num, p.2.den)

/-- Insertion of a floor entry into a list sorted by key (structural). -/
def floorIns (a : ℚ × List Q2) : List (ℚ × List Q2) → List (ℚ × List Q2)
  | [] => [a]
  | b :: l => if a.1 ≤ b.1 then a :: b :: l else b :: floorIns a l

/-- Insertion sort of floor entries by key (structural). -/
def floorSort : List (ℚ × List Q2) → List (ℚ × List Q2)
  | [] => []
  | a :: l => floorIns a (floorSort l)

/-- The keys of a list of floor entries are strictly increasing. -/
def keysStrict : List (ℚ × List Q2) → Bool
  | a :: b :: l => decide (a.1 < b.1) && keysStrict (b :: l)
  | _ => true

theorem floorIns_perm (a : ℚ × List Q2) (l : List (ℚ × List Q2)) : (floorIns a l).Perm (a :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons b l ih =>
    simp only [floorIns]
    split_ifs
    · exact List.Perm.refl _
    · exact (ih.cons b).trans (List.Perm.swap a b l)

theorem floorSort_perm (l : List (ℚ × List Q2)) : (floorSort l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih => exact (floorIns_perm a _).trans (ih.cons a)

theorem pairwise_of_keysStrict : ∀ {l : List (ℚ × List Q2)}, keysStrict l = true →
    l.Pairwise fun a b => a.1 < b.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [keysStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_keysStrict h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 ih).1 c hc)

/-- The floor entries of a corridor, sorted by insertion sort. -/
def floorSortI (I : Input) : List (ℚ × List Q2) := floorSort I.floorEntries

/-- The floor keys of the corridor are strictly increasing after sorting. -/
def floorOK (I : Input) : Bool := keysStrict (floorSortI I)

theorem floor_eq_of_floorOK {I : Input} (h : floorOK I = true) :
    I.floor = (floorSortI I).flatMap (·.2) := by
  unfold Input.floor
  rw [mergeSort_eq_of_perm (fun a : ℚ × List Q2 => a.1) (floorSort_perm _)
    (pairwise_of_keysStrict h)]
  rfl

/-- `unitChain` with the floor sorted by insertion sort. -/
def unitChainI (n k m : ℕ) (u : UnitSpec) : List Q2 :=
  ([c0 (unitInput n k m u).S (unitInput n k m u).H] ++
      (floorSortI (unitInput n k m u)).flatMap (·.2) ++
      [c1 (unitInput n k m u).S (unitInput n k m u).H]) ++
    placedTmpl (unitInput n k m u) u.kind ++ (unitInput n k m u).chainAfter

/-- `unitChains` with insertion sort. -/
def unitChainsI (n k : ℕ) : ℕ → List UnitSpec → List (List Q2)
  | _, [] => []
  | m, u :: us => unitChainI n k m u :: unitChainsI n k (m + 1) us

/-- All floors of the units `m₀, m₀ + 1, …` have distinct keys. -/
def unitsOK (n k : ℕ) : ℕ → List UnitSpec → Bool
  | _, [] => true
  | m, u :: us => floorOK (unitInput n k m u) && unitsOK n k (m + 1) us

theorem unitChains_eq_I {n k : ℕ} : ∀ {m : ℕ} {us : List UnitSpec}, unitsOK n k m us = true →
    unitChains n k m us = unitChainsI n k m us
  | _, [], _ => rfl
  | m, u :: us, h => by
    simp only [unitsOK, Bool.and_eq_true] at h
    simp only [unitChains, unitChainsI, unitChains_eq_I h.2, List.cons.injEq, and_true]
    simp only [unitChain, unitChainI, Input.chainBefore, floor_eq_of_floorOK h.1]

/-- `constructPos` with insertion sort. -/
def constructI (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ (unitChainsI n (numC Φ) 0 (unitSpecs n Φ).1).flatten ++
    [tR n (numC Φ), tL n (numC Φ)] ++
    ((unitChainsI n (numC Φ) 0 (unitSpecs n Φ).2).map (leftChain n)).reverse.flatten ++
    [vL n (numC Φ)]

/-- All corridor floors of the instance have distinct keys. -/
def floorsOK (Φ : List ETRINV.Constraint) (n : ℕ) : Bool :=
  unitsOK n (numC Φ) 0 (unitSpecs n Φ).1 && unitsOK n (numC Φ) 0 (unitSpecs n Φ).2

theorem construct_eq_I {Φ : List ETRINV.Constraint} {n : ℕ} (hn : n ≠ 0)
    (h : floorsOK Φ n = true) : construct Φ n = constructI Φ n := by
  simp only [floorsOK, Bool.and_eq_true] at h
  rw [construct_pos hn]
  simp only [constructPos, constructI, rightPart, leftPart, unitChains_eq_I h.1,
    unitChains_eq_I h.2]

/-! ### The three reference instances -/

theorem floorsOK_A : floorsOK [] 1 = true := by decide +kernel

/-- **Agreement** for `n = 1`, `Φ = []`. -/
theorem construct_refA : (construct [] 1).map ratCode = refA := by
  rw [construct_eq_I (by norm_num) floorsOK_A]
  decide +kernel

theorem floorsOK_B : floorsOK [.one 0, .add 0 0 0, .inv 0 0] 1 = true := by decide +kernel

/-- **Agreement** for `n = 1`, `Φ = [one 0, add 0 0 0, inv 0 0]` (all four unit kinds). -/
theorem construct_refB : (construct [.one 0, .add 0 0 0, .inv 0 0] 1).map ratCode = refB := by
  rw [construct_eq_I (by norm_num) floorsOK_B]
  decide +kernel

theorem floorsOK_C : floorsOK [.inv 1 0, .add 1 0 1, .one 1] 2 = true := by decide +kernel

/-- **Agreement** for `n = 2`, `Φ = [inv 1 0, add 1 0 1, one 1]`. -/
theorem construct_refC : (construct [.inv 1 0, .add 1 0 1, .one 1] 2).map ratCode = refC := by
  rw [construct_eq_I (by norm_num) floorsOK_C]
  decide +kernel

/-! ### The guard numbers -/

theorem numGuards_refA : numGuards [] 1 = 46 := by decide
theorem numGuards_refB : numGuards [.one 0, .add 0 0 0, .inv 0 0] 1 = 67 := by decide
theorem numGuards_refC : numGuards [.inv 1 0, .add 1 0 1, .one 1] 2 = 113 := by decide

end ArtGallery.Sec5

end
