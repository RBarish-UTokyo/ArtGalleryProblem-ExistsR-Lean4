module

public import ArtGallery.Hardness.BP.Assemble.Construct
public import ArtGallery.Hardness.BP.PTime.Construct

/-!
# Boundary-point variant: the construction is polynomial-time

`fun_prop` lemmas for `BP/Assemble/Construct.lean`, on top of the lemmas for the Section 5
construction (`BP/PTime/*`, see the note at the top of `BP/PTime/Construct.lean`): the bays
(`PT.bayRel`), the pockets with bays and the bottom wall (`PT.pocketBP`, `PT.bottomWallBP`), the
template data of the boundary-point templates (`PT.tmplVBP`, …, functions of the kind by
`PT.kindFun`), the units (`PT.unitInputBP`, `PT.placedTmplBP`, `PT.unitChainBP`,
`PT.unitChainsBP`), and

* **`PT.constructBP`**: `fun a => constructBP (Φ a) (n a)` is polynomial-time (`PT.constructBP'`:
  the uncurried form on `List ETRINV.Constraint × ℕ`);
* **`PT.numGuardsBP`** (and `PT.numGuardsBP'`);
* **`PT.constructInstanceBP`**: the code
  `encodeAGP ((constructBP Φ n).map FracPoint.ofRat) (numGuardsBP Φ n)` of the art-gallery
  instance.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.BP.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade ArtGallery.ETRINV
open ArtGallery.Sec5 (Q2 Kind UnitSpec numC unitSpecs leftChain unitH slotA)
open ArtGallery.Sec5.PTime

variable {α : Type} [Code α]

/-! ### The main area with bays -/

@[fun_prop] protected theorem PT.bayRel {one : α → Bool} (hone : PT one) :
    PT (fun a => bayRel (one a)) := by
  unfold bayRel
  fun_prop

@[fun_prop] protected theorem PT.pocketBPRel {one : α → Bool} (hone : PT one) :
    PT (fun a => pocketBPRel (one a)) := by
  unfold pocketBPRel
  fun_prop

@[fun_prop] protected theorem PT.pocketBP {one : α → Bool} {σ : α → ℕ} (hone : PT one)
    (hσ : PT σ) : PT (fun a => pocketBP (one a) (σ a)) := by
  unfold pocketBP
  exact PT.map (PT.q2Add PT.snd' (PT.slotA (hσ.comp PT.fst'))) (PT.pocketBPRel hone)

/-- **The bottom wall with bays.** -/
@[fun_prop] protected theorem PT.bottomWallBP {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => bottomWallBP (n a) (Φ a)) := by
  unfold bottomWallBP
  fun_prop

/-! ### Template data -/

@[fun_prop] protected theorem PT.tmplDBP {k : α → Kind} (hk : PT k) :
    PT (fun a => tmplDBP (k a)) :=
  PT.kindFun tmplDBP hk

@[fun_prop] protected theorem PT.tmplVBP {k : α → Kind} (hk : PT k) :
    PT (fun a => tmplVBP (k a)) :=
  PT.kindFun tmplVBP hk

@[fun_prop] protected theorem PT.tmplTBP {k : α → Kind} (hk : PT k) :
    PT (fun a => tmplTBP (k a)) :=
  PT.kindFun tmplTBP hk

@[fun_prop] protected theorem PT.tmplPtBP {k : α → Kind} {V : α → ℤ × ℤ} (hk : PT k)
    (hV : PT V) : PT (fun a => tmplPtBP (k a) (V a)) := by
  unfold tmplPtBP
  fun_prop

/-! ### One unit -/

@[fun_prop] protected theorem PT.unitInputBP {n k m : α → ℕ} {u : α → UnitSpec} (hn : PT n)
    (hk : PT k) (hm : PT m) (hu : PT u) : PT (fun a => unitInputBP (n a) (k a) (m a) (u a)) := by
  unfold unitInputBP
  fun_prop

@[fun_prop] protected theorem PT.placedTmplBP {I : α → Sec5.Corridor.Input} {kd : α → Kind}
    (hI : PT I) (hkd : PT kd) : PT (fun a => placedTmplBP (I a) (kd a)) := by
  unfold placedTmplBP
  fun_prop

/-- **The chain of a unit.** -/
@[fun_prop] protected theorem PT.unitChainBP {n k m : α → ℕ} {u : α → UnitSpec} (hn : PT n)
    (hk : PT k) (hm : PT m) (hu : PT u) : PT (fun a => unitChainBP (n a) (k a) (m a) (u a)) := by
  unfold unitChainBP
  fun_prop

/-- The recursion `unitChainsBP` as a `map` over the indexed unit list. -/
theorem unitChainsBP_eq_map (n k : ℕ) : ∀ (m : ℕ) (us : List UnitSpec),
    unitChainsBP n k m us = (us.zipIdx m).map (fun p => unitChainBP n k p.2 p.1)
  | _, [] => rfl
  | m, u :: us => by
    rw [unitChainsBP, unitChainsBP_eq_map n k (m + 1) us, List.zipIdx_cons, List.map_cons]

@[fun_prop] protected theorem PT.unitChainsBP {n k m : α → ℕ} {us : α → List UnitSpec}
    (hn : PT n) (hk : PT k) (hm : PT m) (hus : PT us) :
    PT (fun a => unitChainsBP (n a) (k a) (m a) (us a)) := by
  simp only [unitChainsBP_eq_map]
  fun_prop

/-! ### The polygon -/

@[fun_prop] protected theorem PT.rightPartBP {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => rightPartBP (n a) (Φ a)) := by
  unfold rightPartBP
  fun_prop

@[fun_prop] protected theorem PT.leftPartBP {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => leftPartBP (n a) (Φ a)) := by
  unfold leftPartBP
  fun_prop

@[fun_prop] protected theorem PT.constructPosBP {Φ : α → List Constraint} {n : α → ℕ}
    (hΦ : PT Φ) (hn : PT n) : PT (fun a => constructPosBP (Φ a) (n a)) := by
  unfold constructPosBP
  fun_prop

/-- **The polygon of the boundary-point construction is polynomial-time.** -/
@[fun_prop] protected theorem PT.constructBP {Φ : α → List Constraint} {n : α → ℕ} (hΦ : PT Φ)
    (hn : PT n) : PT (fun a => constructBP (Φ a) (n a)) := by
  unfold constructBP
  fun_prop

/-- **The polygon of the boundary-point construction is polynomial-time** (uncurried form). -/
theorem PT.constructBP' : PT (fun p : List Constraint × ℕ => constructBP p.1 p.2) := by
  fun_prop

/-- **The number of guards is polynomial-time.** -/
@[fun_prop] protected theorem PT.numGuardsBP {Φ : α → List Constraint} {n : α → ℕ} (hΦ : PT Φ)
    (hn : PT n) : PT (fun a => numGuardsBP (Φ a) (n a)) := by
  unfold numGuardsBP
  fun_prop

/-- The number of guards (uncurried form). -/
theorem PT.numGuardsBP' : PT (fun p : List Constraint × ℕ => numGuardsBP p.1 p.2) := by
  fun_prop

/-- **The code of the art-gallery instance** (the polygon with the fraction vertices of the
normal forms, and the number of guards) is polynomial-time. -/
theorem PT.constructInstanceBP : PT (fun p : List Constraint × ℕ =>
    encodeAGP ((constructBP p.1 p.2).map FracPoint.ofRat) (numGuardsBP p.1 p.2)) := by
  fun_prop

end ArtGallery.BP.PTime

end
