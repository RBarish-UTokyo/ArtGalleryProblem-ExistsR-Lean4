module

public import ArtGallery.Hardness.BP.PTime.Tools
public import ArtGallery.Hardness.Sec5.Corridor.Defs

/-!
# Polynomial time of the Section 5 construction: corridors

A code for corridor inputs (`instCodeInput`, as tuples `(S, H, slots, T)`) and `fun_prop`
lemmas for all functions of `ArtGallery/Hardness/Sec5/Corridor/Defs.lean` used by the
construction, over `ℚ`, bottom-up:

* planar primitives: `PT.lineDen`, `PT.lineInter`, `PT.onLine`, `PT.ofZetaXi`, `PT.ofLocal`, …;
* corridor parameters: `PT.corrRho`, `PT.c0`, …, `PT.place`, `PT.pairAxis`;
* the corridor of an input: pairs (`PT.inputApex`, `PT.inputUmbra`, `PT.inputZp` with the
  ceiling of `gridXUp`, the nook, the floor witness slots), the floor (`PT.inputFloor`: merge sort
  by the abscissa, `PT.mergeSortKey`), the upper wall and the two chains
  (`PT.inputChainBefore`, `PT.inputChainAfter`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Sec5.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

variable {α : Type} [Code α]

/-! ### Planar primitives over `ℚ` -/

@[fun_prop] protected theorem PT.lineDen {p q r s : α → ℚ × ℚ} (hp : PT p) (hq : PT q)
    (hr : PT r) (hs : PT s) : PT (fun a => Corridor.lineDen (p a) (q a) (r a) (s a)) := by
  unfold Corridor.lineDen
  fun_prop

@[fun_prop] protected theorem PT.lineInter {p q r s : α → ℚ × ℚ} (hp : PT p) (hq : PT q)
    (hr : PT r) (hs : PT s) : PT (fun a => Corridor.lineInter (p a) (q a) (r a) (s a)) := by
  unfold Corridor.lineInter
  dsimp only
  fun_prop

@[fun_prop] protected theorem PT.onLine {p q : α → ℚ × ℚ} {x : α → ℚ} (hp : PT p) (hq : PT q)
    (hx : PT x) : PT (fun a => Corridor.onLine (p a) (q a) (x a)) := by
  unfold Corridor.onLine
  fun_prop

@[fun_prop] protected theorem PT.zetaOf {O z : α → ℚ × ℚ} (hO : PT O) (hz : PT z) :
    PT (fun a => Corridor.zetaOf (O a) (z a)) := by
  unfold Corridor.zetaOf
  fun_prop

@[fun_prop] protected theorem PT.xiOf {O z : α → ℚ × ℚ} (hO : PT O) (hz : PT z) :
    PT (fun a => Corridor.xiOf (O a) (z a)) := by
  unfold Corridor.xiOf
  fun_prop

@[fun_prop] protected theorem PT.ofZetaXi {O : α → ℚ × ℚ} {ζ ξ : α → ℚ} (hO : PT O) (hζ : PT ζ)
    (hξ : PT ξ) : PT (fun a => Corridor.ofZetaXi (O a) (ζ a) (ξ a)) := by
  unfold Corridor.ofZetaXi
  fun_prop

@[fun_prop] protected theorem PT.ofLocal {O : α → ℚ × ℚ} {X Y : α → ℚ} (hO : PT O) (hX : PT X)
    (hY : PT Y) : PT (fun a => Corridor.ofLocal (O a) (X a) (Y a)) := by
  unfold Corridor.ofLocal
  fun_prop

/-! ### Corridor parameters -/

section Params

variable {S H : α → ℚ}

@[fun_prop] protected theorem PT.corrRho (hS : PT S) : PT (fun a => Corridor.rho (S a)) := by
  unfold Corridor.rho
  fun_prop

@[fun_prop] protected theorem PT.corrDelta (hS : PT S) : PT (fun a => Corridor.delta (S a)) := by
  unfold Corridor.delta
  fun_prop

@[fun_prop] protected theorem PT.corrEps (hS : PT S) : PT (fun a => Corridor.eps (S a)) := by
  unfold Corridor.eps
  fun_prop

@[fun_prop] protected theorem PT.c0 (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.c0 (S a) (H a)) := by
  unfold Corridor.c0
  fun_prop

@[fun_prop] protected theorem PT.c1 (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.c1 (S a) (H a)) := by
  unfold Corridor.c1
  fun_prop

@[fun_prop] protected theorem PT.d0 (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.d0 (S a) (H a)) := by
  unfold Corridor.d0
  fun_prop

@[fun_prop] protected theorem PT.d1 (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.d1 (S a) (H a)) := by
  unfold Corridor.d1
  fun_prop

@[fun_prop] protected theorem PT.Oc (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.Oc (S a) (H a)) := by
  unfold Corridor.Oc
  fun_prop

@[fun_prop] protected theorem PT.mPt (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.mPt (S a) (H a)) := by
  unfold Corridor.mPt
  fun_prop

@[fun_prop] protected theorem PT.place {T : α → ℚ × ℚ} (hS : PT S) (hH : PT H) (hT : PT T) :
    PT (fun a => Corridor.place (S a) (H a) (T a)) := by
  unfold Corridor.place
  fun_prop

@[fun_prop] protected theorem PT.baseA {σ : α → ℕ} (hσ : PT σ) :
    PT (fun a => (Corridor.baseA (σ a) : ℚ × ℚ)) := by
  unfold Corridor.baseA
  fun_prop

@[fun_prop] protected theorem PT.baseB {σ : α → ℕ} (hσ : PT σ) :
    PT (fun a => (Corridor.baseB (σ a) : ℚ × ℚ)) := by
  unfold Corridor.baseB
  fun_prop

@[fun_prop] protected theorem PT.recvA {T : α → ℚ × ℚ} (hS : PT S) (hH : PT H) (hT : PT T) :
    PT (fun a => Corridor.recvA (S a) (H a) (T a)) := by
  unfold Corridor.recvA
  fun_prop

@[fun_prop] protected theorem PT.recvB {T : α → ℚ × ℚ} (hS : PT S) (hH : PT H) (hT : PT T) :
    PT (fun a => Corridor.recvB (S a) (H a) (T a)) := by
  unfold Corridor.recvB
  fun_prop

@[fun_prop] protected theorem PT.zetaO (hS : PT S) (hH : PT H) :
    PT (fun a => Corridor.zetaO (S a) (H a)) := by
  unfold Corridor.zetaO
  fun_prop

@[fun_prop] protected theorem PT.Zs {σ : α → ℕ} {γ : α → ℚ} (hS : PT S) (hH : PT H) (hσ : PT σ)
    (hγ : PT γ) : PT (fun a => Corridor.Zs (S a) (H a) (σ a) (γ a)) := by
  unfold Corridor.Zs
  fun_prop

@[fun_prop] protected theorem PT.xiRef {T : α → ℚ × ℚ} (hS : PT S) (hT : PT T) :
    PT (fun a => Corridor.xiRef (S a) (T a)) := by
  unfold Corridor.xiRef
  fun_prop

@[fun_prop] protected theorem PT.Xis {T : α → ℚ × ℚ} {τ : α → ℕ} {γ : α → ℚ} (hS : PT S)
    (hT : PT T) (hτ : PT τ) (hγ : PT γ) : PT (fun a => Corridor.Xis (S a) (T a) (τ a) (γ a)) := by
  unfold Corridor.Xis
  fun_prop

@[fun_prop] protected theorem PT.pairAxis {σ : α → ℕ} {T k0 k1 : α → ℚ × ℚ} (hS : PT S)
    (hH : PT H) (hσ : PT σ) (hT : PT T) (hk0 : PT k0) (hk1 : PT k1) :
    PT (fun a => Corridor.pairAxis (S a) (H a) (σ a) (T a) (k0 a) (k1 a)) := by
  unfold Corridor.pairAxis
  fun_prop

end Params

/-! ### Corridor inputs -/

/-- A corridor input as a tuple. -/
def inputTuple (I : Corridor.Input) : ℚ × ℚ × List ℕ × List (ℚ × ℚ) := (I.S, I.H, I.slots, I.T)

/-- The corridor input of a tuple. -/
def inputOfTuple (p : ℚ × ℚ × List ℕ × List (ℚ × ℚ)) : Corridor.Input :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

/-- Corridor inputs are coded as tuples. -/
instance instCodeInput : Code Corridor.Input :=
  Code.ofInj inputTuple inputOfTuple (fun _ => rfl)

section Input

variable {I : α → Corridor.Input} {k : α → ℕ}

@[fun_prop] protected theorem PT.inputTuple (hI : PT I) : PT (fun a => inputTuple (I a)) :=
  (PT.ofInj_to inputTuple inputOfTuple (fun _ => rfl)).comp hI

@[fun_prop] protected theorem PT.inputS (hI : PT I) : PT (fun a => (I a).S) :=
  PT.fst (PT.inputTuple hI)

@[fun_prop] protected theorem PT.inputH (hI : PT I) : PT (fun a => (I a).H) :=
  PT.fst (PT.snd (PT.inputTuple hI))

@[fun_prop] protected theorem PT.inputSlots (hI : PT I) : PT (fun a => (I a).slots) :=
  PT.fst (PT.snd (PT.snd (PT.inputTuple hI)))

@[fun_prop] protected theorem PT.inputT (hI : PT I) : PT (fun a => (I a).T) :=
  PT.snd (PT.snd (PT.snd (PT.inputTuple hI)))

@[fun_prop] protected theorem PT.inputMk {S H : α → ℚ} {sl : α → List ℕ} {T : α → List (ℚ × ℚ)}
    (hS : PT S) (hH : PT H) (hsl : PT sl) (hT : PT T) :
    PT (fun a => (⟨S a, H a, sl a, T a⟩ : Corridor.Input)) :=
  PT.ofInj_mk inputTuple inputOfTuple (fun _ => rfl)
    (show PT (fun a => (S a, H a, sl a, T a)) by fun_prop)

@[fun_prop] protected theorem PT.inputNp (hI : PT I) : PT (fun a => (I a).np) := by
  unfold Corridor.Input.np
  fun_prop

@[fun_prop] protected theorem PT.inputSigma (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).sigma (k a)) := by
  unfold Corridor.Input.sigma
  fun_prop

@[fun_prop] protected theorem PT.inputTau (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).tau (k a)) := by
  unfold Corridor.Input.tau
  fun_prop

@[fun_prop] protected theorem PT.inputTt (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).Tt (k a)) := by
  unfold Corridor.Input.Tt
  fun_prop

@[fun_prop] protected theorem PT.inputT0 (hI : PT I) : PT (fun a => (I a).T0) := by
  unfold Corridor.Input.T0
  fun_prop

@[fun_prop] protected theorem PT.inputO (hI : PT I) : PT (fun a => (I a).O) := by
  unfold Corridor.Input.O
  fun_prop

@[fun_prop] protected theorem PT.inputEps (hI : PT I) : PT (fun a => (I a).ε) := by
  unfold Corridor.Input.ε
  fun_prop

@[fun_prop] protected theorem PT.inputLw (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).Lw (k a)) := by
  unfold Corridor.Input.Lw
  fun_prop

@[fun_prop] protected theorem PT.inputRw (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).Rw (k a)) := by
  unfold Corridor.Input.Rw
  fun_prop

@[fun_prop] protected theorem PT.inputApex (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).apex (k a)) := by
  unfold Corridor.Input.apex
  fun_prop

@[fun_prop] protected theorem PT.inputUmbra (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).umbra (k a)) := by
  unfold Corridor.Input.umbra
  fun_prop

@[fun_prop] protected theorem PT.inputF0 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).f0 (k a)) := by
  unfold Corridor.Input.f0
  fun_prop

@[fun_prop] protected theorem PT.inputF1 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).f1 (k a)) := by
  unfold Corridor.Input.f1
  fun_prop

@[fun_prop] protected theorem PT.inputOnUmbra {x : α → ℚ} (hI : PT I) (hk : PT k) (hx : PT x) :
    PT (fun a => (I a).onUmbra (k a) (x a)) := by
  unfold Corridor.Input.onUmbra
  fun_prop

@[fun_prop] protected theorem PT.inputYa (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).ya (k a)) := by
  unfold Corridor.Input.ya
  fun_prop

/-- The grid abscissa rounded up (a ceiling). -/
@[fun_prop] protected theorem PT.inputGridXUp {x u : α → ℚ} (hI : PT I) (hx : PT x) (hu : PT u) :
    PT (fun a => (I a).gridXUp (x a) (u a)) := by
  unfold Corridor.Input.gridXUp
  fun_prop

@[fun_prop] protected theorem PT.inputZp (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).zp (k a)) := by
  unfold Corridor.Input.zp
  fun_prop

@[fun_prop] protected theorem PT.inputValley (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).valley (k a)) := by
  unfold Corridor.Input.valley
  fun_prop

@[fun_prop] protected theorem PT.inputBase (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).base (k a)) := by
  unfold Corridor.Input.base
  fun_prop

@[fun_prop] protected theorem PT.inputSgPt (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).sgPt (k a)) := by
  unfold Corridor.Input.sgPt
  fun_prop

@[fun_prop] protected theorem PT.inputYN (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).yN (k a)) := by
  unfold Corridor.Input.yN
  fun_prop

@[fun_prop] protected theorem PT.inputZ1 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).z1 (k a)) := by
  unfold Corridor.Input.z1
  fun_prop

@[fun_prop] protected theorem PT.inputZ0 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).z0 (k a)) := by
  unfold Corridor.Input.z0
  fun_prop

@[fun_prop] protected theorem PT.inputNook (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).nook (k a)) := by
  unfold Corridor.Input.nook
  fun_prop

@[fun_prop] protected theorem PT.inputBigF0 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).F0 (k a)) := by
  unfold Corridor.Input.F0
  fun_prop

@[fun_prop] protected theorem PT.inputBigF1 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).F1 (k a)) := by
  unfold Corridor.Input.F1
  fun_prop

@[fun_prop] protected theorem PT.inputN1 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).n1 (k a)) := by
  unfold Corridor.Input.n1
  fun_prop

@[fun_prop] protected theorem PT.inputN0 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).n0 (k a)) := by
  unfold Corridor.Input.n0
  fun_prop

@[fun_prop] protected theorem PT.inputKx {s : α → ℚ} (hI : PT I) (hk : PT k) (hs : PT s) :
    PT (fun a => (I a).kx (k a) (s a)) := by
  unfold Corridor.Input.kx
  fun_prop

@[fun_prop] protected theorem PT.inputSlotTip {s : α → ℚ} (hI : PT I) (hk : PT k) (hs : PT s) :
    PT (fun a => (I a).slotTip (k a) (s a)) := by
  unfold Corridor.Input.slotTip
  fun_prop

@[fun_prop] protected theorem PT.inputSlot2 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).slot2 (k a)) := by
  unfold Corridor.Input.slot2
  fun_prop

@[fun_prop] protected theorem PT.inputSlot4 (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).slot4 (k a)) := by
  unfold Corridor.Input.slot4
  fun_prop

@[fun_prop] protected theorem PT.inputFloorEntries (hI : PT I) :
    PT (fun a => (I a).floorEntries) := by
  unfold Corridor.Input.floorEntries
  fun_prop

/-- **The corridor floor** (merge sort by the abscissa). -/
@[fun_prop] protected theorem PT.inputFloor (hI : PT I) : PT (fun a => (I a).floor) := by
  unfold Corridor.Input.floor
  have h : PT (fun a => (I a).floorEntries.mergeSort fun x y => decide (x.1 ≤ y.1)) :=
    PT.mergeSortKey (key := fun e : ℚ × List (ℚ × ℚ) => e.1) PT.fst' (PT.inputFloorEntries hI)
  fun_prop

@[fun_prop] protected theorem PT.inputUpperPair (hI : PT I) (hk : PT k) :
    PT (fun a => (I a).upperPair (k a)) := by
  unfold Corridor.Input.upperPair
  fun_prop

@[fun_prop] protected theorem PT.inputUpper (hI : PT I) : PT (fun a => (I a).upper) := by
  unfold Corridor.Input.upper
  fun_prop

/-- The corridor chain before the gadget: `c0`, the floor, `c1`. -/
@[fun_prop] protected theorem PT.inputChainBefore (hI : PT I) :
    PT (fun a => (I a).chainBefore) := by
  unfold Corridor.Input.chainBefore
  fun_prop

/-- The corridor chain after the gadget: `d1`, the upper wall, `d0`. -/
@[fun_prop] protected theorem PT.inputChainAfter (hI : PT I) :
    PT (fun a => (I a).chainAfter) := by
  unfold Corridor.Input.chainAfter
  fun_prop

@[fun_prop] protected theorem PT.inputSgPts (hI : PT I) : PT (fun a => (I a).sgPts) := by
  unfold Corridor.Input.sgPts
  fun_prop

end Input

end ArtGallery.Sec5.PTime

end
