module

public import ArtGallery.Hardness.BP.Assemble.TmplData
public import ArtGallery.Hardness.BP.MainArea
public import ArtGallery.Hardness.Sec5.Assemble.Construct

/-!
# Boundary-point variant: the global polygon `constructBP Φ n`

The polygon of the reduction ETR-INV → AGP with guards on the boundary
(`docs/boundary_point/design.md` §3).  It is the Section 5 polygon
(`Sec5/Assemble/Construct.lean`) with two changes:

* the bottom wall carries bays instead of pockets (`bottomWallBP`, `BP/MainArea.lean`);
* the units carry the boundary-point templates `tmplVBP` with the receivers `tmplTBP`
  (`BP/Assemble/TmplData.lean`).

Unit order, heights `H_m = S + 3m + 1`, corridors (`Corridor.Input` with the new receivers),
placement `φ(T) = m + T/S`, the mirror `x ↦ 54n − 12 − x` of the left units and the hexagon
corners are those of Section 5:
```
bottom wall with bays (slots 0 … 4n−1), w_r, v_r, right units 0 … R−1, t_r, t_l,
left units L−1 … 0 (mirrored, reversed), v_l
```
For `n = 0` it is the triangle `(0,0), (1,0), (0,1)`.  The number of guards is the Section 5
number (`numGuardsBP = numGuards`: the weak copy `A` replaces `r'_i`, and the guard counts of the
four kinds are unchanged).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery
open ArtGallery.Sec5 (Q2 UnitSpec Kind S unitH numC unitSpecs mirror leftChain wR vR tR tL vL
  triangle0 numGuards)

/-! ### One unit -/

/-- The corridor input of unit `m` with spec `u` (right working frame). -/
def unitInputBP (n k m : ℕ) (u : UnitSpec) : Sec5.Corridor.Input :=
  ⟨(S n k : ℚ), unitH n k m, u.work, tmplTBP u.kind⟩

/-- The placed template chain of a unit: `φ(T) = m + T/S` for the template points `T`. -/
def placedTmplBP (I : Sec5.Corridor.Input) (kd : Kind) : List Q2 :=
  (tmplVBP kd).map fun V => Sec5.Corridor.place I.S I.H (tmplPtBP kd V)

/-- **The chain of a unit** in the right working frame:
`c0, floor…, c1, φ(template)…, d1, upper…, d0`. -/
def unitChainBP (n k m : ℕ) (u : UnitSpec) : List Q2 :=
  (unitInputBP n k m u).chainBefore ++ placedTmplBP (unitInputBP n k m u) u.kind ++
    (unitInputBP n k m u).chainAfter

/-- The chains of the units of one side, unit `m₀, m₀ + 1, …` (working frame). -/
def unitChainsBP (n k : ℕ) : ℕ → List UnitSpec → List (List Q2)
  | _, [] => []
  | m, u :: us => unitChainBP n k m u :: unitChainsBP n k (m + 1) us

/-- The right side: the right unit chains `0, …, R − 1`. -/
def rightPartBP (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).1).flatten

/-- The left side: the left unit chains `L − 1, …, 0`, mirrored and reversed. -/
def leftPartBP (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  ((unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).2).map (leftChain n)).reverse.flatten

/-- The polygon for `n ≥ 1`. -/
def constructPosBP (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ ++
    [tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++ [vL n (numC Φ)]

/-- **The polygon of the boundary-point reduction** (rational vertices, counter-clockwise). -/
def constructBP (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  if n = 0 then triangle0 else constructPosBP Φ n

/-- **The number of guards**: the Section 5 number `46n + 16 k_add + 5 k_inv` (`n ≥ 1`), `1` for
`n = 0`. -/
def numGuardsBP (Φ : List ETRINV.Constraint) (n : ℕ) : ℕ := numGuards Φ n

theorem numGuardsBP_eq (Φ : List ETRINV.Constraint) (n : ℕ) :
    numGuardsBP Φ n = if n = 0 then 1 else Sec5.guardCount n Φ := rfl

theorem constructBP_pos {Φ : List ETRINV.Constraint} {n : ℕ} (hn : n ≠ 0) :
    constructBP Φ n = constructPosBP Φ n := by
  simp [constructBP, hn]

theorem constructBP_zero (Φ : List ETRINV.Constraint) : constructBP Φ 0 = triangle0 := by
  simp [constructBP]

theorem length_unitChainsBP (n k m : ℕ) (us : List UnitSpec) :
    (unitChainsBP n k m us).length = us.length := by
  induction us generalizing m with
  | nil => rfl
  | cons u us ih => simp [unitChainsBP, ih]

/-- The `j`-th chain of `unitChainsBP n k m us` is the chain of unit `m + j`. -/
theorem getElem_unitChainsBP (n k m : ℕ) (us : List UnitSpec) (j : ℕ)
    (hj : j < (unitChainsBP n k m us).length) :
    (unitChainsBP n k m us)[j] =
      unitChainBP n k (m + j) (us[j]'(by rw [length_unitChainsBP] at hj; exact hj)) := by
  induction us generalizing m j with
  | nil => simp [unitChainsBP] at hj
  | cons u us ih =>
    cases j with
    | zero => simp [unitChainsBP]
    | succ j =>
      simp only [unitChainsBP, List.getElem_cons_succ]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm 1 j]

end ArtGallery.BP

end
