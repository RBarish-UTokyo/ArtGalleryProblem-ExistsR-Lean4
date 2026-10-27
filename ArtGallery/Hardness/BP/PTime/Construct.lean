module

public import ArtGallery.Hardness.BP.PTime.Params
public import ArtGallery.Hardness.BP.PTime.Corridor
public import ArtGallery.Hardness.BP.PTime.Encode
public import ArtGallery.Hardness.Sec5.Assemble.Construct

/-!
# The Section 5 construction is polynomial-time

`fun_prop` lemmas for the assembly of `ArtGallery/Hardness/Sec5/Assemble/Construct.lean`:
unit heights and corridor inputs (`PT.unitH`, `PT.unitInput`), the placed template chain
(`PT.placedTmpl`), the chain of a unit (`PT.unitChain`), the chains of a side (`PT.unitChains`,
through `unitChains_eq_map`), the mirror image of a left chain (`PT.leftChain`), the two sides,
and

* **`PT.construct`**: `fun a => construct (Φ a) (n a)` is polynomial-time (`PT.construct'`: the
  uncurried form on `List ETRINV.Constraint × ℕ`);
* **`PT.numGuards`** (and `PT.numGuards'`);
* `PT.constructInstance`: the code `encodeAGP ((construct Φ n).map FracPoint.ofRat) (numGuards Φ n)`
  of the art-gallery instance.

All numbers occurring are rationals with polynomially bounded numerators and denominators (in
unary); the field operations of `ArtGallery/Stade/PTimeRat.lean` are polynomial-time without side
conditions, so only the recursive parts need care: the corridor floor is sorted by
`List.mergeSort`, which is insertion sort (`mergeSort_eq_insertionSort_bool`, `PT.mergeSortKey`),
and the recursion `unitChains` is a `map` over `zipIdx`.

## Reusing the proof for a modified construction

The lemmas are stated compositionally (`PT (fun a => f (x a) (y a))`) and tagged `@[fun_prop]`,
so the polynomial time of a modified polygon (bays instead of pockets, new template data) is
again `unfold …; fun_prop` once the new pieces have their own lemmas.  Unchanged pieces need no
work.  A modified construction must re-supply:

* **New data types**: a `Code` instance for each (as a tuple through `Code.ofInj`, as
  `instCodeUnitSpec`, `instCodeInput`) with projection and constructor lemmas.  If the unit kinds
  change, a new `instCodeKind` and `PT.kindFun` (copy the four-line proof).
* **Template data** (`tmplV`, `tmplD`, `tmplT` or their replacements): each function of the unit
  kind is polynomial-time by `PT.kindFun f`; tag one lemma per function.
* **Main area** (bays in place of `pocketRel`, `pocket`, `bottomWall`): one lemma per definition,
  by `unfold …; fun_prop`.  Translations of rational points by `+` are not handled by `fun_prop`
  (see `PT.q2Add`): apply `PT.q2Add` by hand (as in `PT.pocket`).
* **Any `match`** on constraints or kinds: `PT.constraintFun`, `PT.constraintFun₂`,
  `PT.kindFun₂`; **recursion**: rewrite as `map`/`flatMap`/`zipIdx` (as `unitChains_eq_map`)
  or use `PT.of_listRec`; sorting by a rational key: `PT.mergeSortKey`.
* **The assembly** (`unitChain`, `constructPos`, `construct`, `numGuards` or their
  replacements): restate the lemmas of this file for the new definitions, each by
  `unfold …; fun_prop`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Sec5.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade ArtGallery.ETRINV

variable {α : Type} [Code α]

/-! ### One unit -/

@[fun_prop] protected theorem PT.unitH {n k m : α → ℕ} (hn : PT n) (hk : PT k) (hm : PT m) :
    PT (fun a => unitH (n a) (k a) (m a)) := by
  unfold unitH
  fun_prop

@[fun_prop] protected theorem PT.unitInput {n k m : α → ℕ} {u : α → UnitSpec} (hn : PT n)
    (hk : PT k) (hm : PT m) (hu : PT u) : PT (fun a => unitInput (n a) (k a) (m a) (u a)) := by
  unfold unitInput
  fun_prop

@[fun_prop] protected theorem PT.placedTmpl {I : α → Corridor.Input} {kd : α → Kind} (hI : PT I)
    (hkd : PT kd) : PT (fun a => placedTmpl (I a) (kd a)) := by
  unfold placedTmpl
  fun_prop

/-- **The chain of a unit.** -/
@[fun_prop] protected theorem PT.unitChain {n k m : α → ℕ} {u : α → UnitSpec} (hn : PT n)
    (hk : PT k) (hm : PT m) (hu : PT u) : PT (fun a => unitChain (n a) (k a) (m a) (u a)) := by
  unfold unitChain
  fun_prop

/-- The recursion `unitChains` as a `map` over the indexed unit list. -/
theorem unitChains_eq_map (n k : ℕ) : ∀ (m : ℕ) (us : List UnitSpec),
    unitChains n k m us = (us.zipIdx m).map (fun p => unitChain n k p.2 p.1)
  | _, [] => rfl
  | m, u :: us => by
    rw [unitChains, unitChains_eq_map n k (m + 1) us, List.zipIdx_cons, List.map_cons]

@[fun_prop] protected theorem PT.unitChains {n k m : α → ℕ} {us : α → List UnitSpec} (hn : PT n)
    (hk : PT k) (hm : PT m) (hus : PT us) :
    PT (fun a => unitChains (n a) (k a) (m a) (us a)) := by
  simp only [unitChains_eq_map]
  fun_prop

@[fun_prop] protected theorem PT.leftChain {n : α → ℕ} {c : α → List Q2} (hn : PT n) (hc : PT c) :
    PT (fun a => leftChain (n a) (c a)) := by
  unfold leftChain
  fun_prop

/-! ### The polygon -/

@[fun_prop] protected theorem PT.numC {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => numC (Φ a)) := by
  unfold numC
  fun_prop

@[fun_prop] protected theorem PT.rightPart {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => rightPart (n a) (Φ a)) := by
  unfold rightPart
  fun_prop

@[fun_prop] protected theorem PT.leftPart {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => leftPart (n a) (Φ a)) := by
  unfold leftPart
  fun_prop

@[fun_prop] protected theorem PT.constructPos {Φ : α → List Constraint} {n : α → ℕ} (hΦ : PT Φ)
    (hn : PT n) : PT (fun a => constructPos (Φ a) (n a)) := by
  unfold constructPos
  fun_prop

/-- **The polygon of the Section 5 construction is polynomial-time.** -/
@[fun_prop] protected theorem PT.construct {Φ : α → List Constraint} {n : α → ℕ} (hΦ : PT Φ)
    (hn : PT n) : PT (fun a => construct (Φ a) (n a)) := by
  unfold construct
  fun_prop

/-- **The polygon of the Section 5 construction is polynomial-time** (uncurried form). -/
theorem PT.construct' : PT (fun p : List Constraint × ℕ => construct p.1 p.2) := by
  fun_prop

/-- **The number of guards is polynomial-time.** -/
@[fun_prop] protected theorem PT.numGuards {Φ : α → List Constraint} {n : α → ℕ} (hΦ : PT Φ)
    (hn : PT n) : PT (fun a => numGuards (Φ a) (n a)) := by
  unfold numGuards
  fun_prop

/-- The number of guards (uncurried form). -/
theorem PT.numGuards' : PT (fun p : List Constraint × ℕ => numGuards p.1 p.2) := by
  fun_prop

@[fun_prop] protected theorem PT.unitGuards {us : α → List UnitSpec} (hus : PT us) :
    PT (fun a => unitGuards (us a)) := by
  unfold unitGuards
  fun_prop

/-- **The code of the art-gallery instance** (the polygon with the fraction vertices of the
normal forms, and the number of guards) is polynomial-time. -/
theorem PT.constructInstance : PT (fun p : List Constraint × ℕ =>
    encodeAGP ((construct p.1 p.2).map FracPoint.ofRat) (numGuards p.1 p.2)) := by
  fun_prop

end ArtGallery.Sec5.PTime

end
