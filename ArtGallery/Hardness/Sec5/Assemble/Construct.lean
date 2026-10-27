module

public import ArtGallery.Hardness.Sec5.Assemble.TmplData
public import ArtGallery.Hardness.Sec5.MainArea
public import ArtGallery.Hardness.Sec5.Corridor.Defs

/-!
# Section 5: the global polygon `construct Φ n`

The polygon of the reduction ETR-INV → AGP (`docs/section5/06_assembly.md`).

* **Units** (`unitSpecs`, `Params.lean`): unit `m` of a side has height `H_m = S + 3m + 1`
  (`unitH`) and the corridor input `unitInput` (scale `S`, height `H_m`, the working slots, the
  template's receivers `tmplT`).  Its chain in the right working frame is
  `unitChain = c0, floor…, c1, φ(template chain)…, d1, upper wall…, d0` with the placement
  `φ(T) = m + T/S`, `m = c1 + (1, −1)` (`Corridor.place`) of the template points
  `T = tmplV / tmplD` (`tmplPt`).  A left unit is the mirror image `x ↦ 54n − 12 − x` of its
  working-frame chain, traversed backwards (`leftChain`).
* **The polygon** (`n ≥ 1`, counter-clockwise):
  ```
  bottom wall (pockets 0 … 4n−1), w_r, v_r, right units 0 … R−1, t_r, t_l,
  left units L−1 … 0 (mirrored, reversed), v_l
  ```
  For `n = 0` it is the triangle `(0,0), (1,0), (0,1)` (06 §n = 0).
* `numGuards Φ n`: `guardCount n Φ = 46n + 16 k_add + 5 k_inv` for `n ≥ 1`, and `1` for `n = 0`;
  the shift of Theorem 54 is `shift i = 27i/2 − 1/2` (`Params.lean`).

All definitions are computable, by `List.range`/`map`/`flatMap` and structural recursion.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery

/-! ### One unit -/

/-- The number of constraints, the parameter `k` of `bigN`, `S`. -/
abbrev numC (Φ : List ETRINV.Constraint) : ℕ := Φ.length

/-- The height `H_m = S + 3m + 1` of unit `m` (both sides). -/
def unitH (n k m : ℕ) : ℚ := (S n k : ℚ) + 3 * (m : ℚ) + 1

/-- The corridor input of unit `m` with spec `u` (right working frame). -/
def unitInput (n k m : ℕ) (u : UnitSpec) : Corridor.Input :=
  ⟨(S n k : ℚ), unitH n k m, u.work, tmplT u.kind⟩

/-- The placed template chain of a unit: `φ(T) = m + T/S` for the template points `T`. -/
def placedTmpl (I : Corridor.Input) (kd : Kind) : List Q2 :=
  (tmplV kd).map fun V => Corridor.place I.S I.H (tmplPt kd V)

/-- **The chain of a unit** in the right working frame:
`c0, floor…, c1, φ(template)…, d1, upper…, d0` (`construct.Unit.chain_work`). -/
def unitChain (n k m : ℕ) (u : UnitSpec) : List Q2 :=
  (unitInput n k m u).chainBefore ++ placedTmpl (unitInput n k m u) u.kind ++
    (unitInput n k m u).chainAfter

/-- The chains of the units of one side, unit `m₀, m₀ + 1, …` (working frame). -/
def unitChains (n k : ℕ) : ℕ → List UnitSpec → List (List Q2)
  | _, [] => []
  | m, u :: us => unitChain n k m u :: unitChains n k (m + 1) us

/-- A left unit chain: the mirror image of the working-frame chain, traversed backwards. -/
def leftChain (n : ℕ) (c : List Q2) : List Q2 := c.reverse.map (mirror n)

/-- The right side: the right unit chains `0, …, R − 1`. -/
def rightPart (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  (unitChains n (numC Φ) 0 (unitSpecs n Φ).1).flatten

/-- The left side: the left unit chains `L − 1, …, 0`, mirrored and reversed. -/
def leftPart (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  ((unitChains n (numC Φ) 0 (unitSpecs n Φ).2).map (leftChain n)).reverse.flatten

/-- The polygon for `n ≥ 1` (`construct.Instance.V`). -/
def constructPos (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ ++
    [tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++ [vL n (numC Φ)]

/-- The degenerate polygon for `n = 0`: the triangle `(0,0), (1,0), (0,1)`. -/
def triangle0 : List Q2 := [(0, 0), (1, 0), (0, 1)]

/-- **The polygon of the reduction** (rational vertices, counter-clockwise). -/
def construct (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  if n = 0 then triangle0 else constructPos Φ n

/-- **The number of guards**: `46n + 16 k_add + 5 k_inv` (`n ≥ 1`), `1` for `n = 0`. -/
def numGuards (Φ : List ETRINV.Constraint) (n : ℕ) : ℕ :=
  if n = 0 then 1 else guardCount n Φ

/-- The guards of the units of a list (`Kind.nguards`). -/
def unitGuards (us : List UnitSpec) : ℕ := (us.map fun u => u.kind.nguards).sum

theorem construct_pos {Φ : List ETRINV.Constraint} {n : ℕ} (hn : n ≠ 0) :
    construct Φ n = constructPos Φ n := by
  simp [construct, hn]

theorem construct_zero (Φ : List ETRINV.Constraint) : construct Φ 0 = triangle0 := by
  simp [construct]

theorem length_unitChains (n k m : ℕ) (us : List UnitSpec) :
    (unitChains n k m us).length = us.length := by
  induction us generalizing m with
  | nil => rfl
  | cons u us ih => simp [unitChains, ih]

/-- The `j`-th chain of `unitChains n k m us` is the chain of unit `m + j`. -/
theorem getElem_unitChains (n k m : ℕ) (us : List UnitSpec) (j : ℕ)
    (hj : j < (unitChains n k m us).length) :
    (unitChains n k m us)[j] =
      unitChain n k (m + j) (us[j]'(by rw [length_unitChains] at hj; exact hj)) := by
  induction us generalizing m j with
  | nil => simp [unitChains] at hj
  | cons u us ih =>
    cases j with
    | zero => simp [unitChains]
    | succ j =>
      simp only [unitChains, List.getElem_cons_succ]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm 1 j]

end ArtGallery.Sec5

end
