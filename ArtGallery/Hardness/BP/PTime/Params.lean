module

public import ArtGallery.Hardness.BP.PTime.Tools
public import ArtGallery.PTime.INVCode
public import ArtGallery.Hardness.Sec5.MainArea
public import ArtGallery.Hardness.Sec5.Assemble.TmplData

/-!
# Polynomial time of the Section 5 construction: parameters, main area, template data

Codes for the data of the construction and `fun_prop` lemmas, bottom-up:

* case analysis on ETR-INV constraints (`PT.constraintFun`, `PT.constraintFun₂`);
* codes for unit kinds (`instCodeKind`, by index; **every function of the kind is
  polynomial-time**, `PT.kindFun`) and unit specifications (`instCodeUnitSpec`, as tuples);
* the global parameters (`PT.bigN`, `PT.S`, …), slots, shifts and the mirror (`PT.mirror`),
  the constraint counts and the guard count (`PT.guardCount`), the units (`PT.unitSpecs`);
* the main area: pockets (`PT.pocket`), the bottom wall (`PT.bottomWall`), the hexagon corners;
* the template data `tmplV`, `tmplD`, `tmplT`, `tmplPt` (functions of the kind).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Sec5.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade ArtGallery.ETRINV

variable {α β : Type} [Code α] [Code β]

/-! ### Case analysis on constraints -/

omit [Code β] in
/-- Every function on constraints is a case analysis. -/
theorem constraint_eq_elim (f : Constraint → β) (c : Constraint) :
    f c = c.elim (fun x => f (.one x)) (fun x y z => f (.add x y z)) (fun x y => f (.inv x y)) := by
  cases c <;> rfl

/-- A function of a parameter and a constraint, given by its values on the constructors. -/
theorem PT.constraintFun₂ {f : α → Constraint → β}
    (h₁ : PT (fun p : α × ℕ => f p.1 (.one p.2)))
    (h₂ : PT (fun p : α × ℕ × ℕ × ℕ => f p.1 (.add p.2.1 p.2.2.1 p.2.2.2)))
    (h₃ : PT (fun p : α × ℕ × ℕ => f p.1 (.inv p.2.1 p.2.2))) :
    PT (fun p : α × Constraint => f p.1 p.2) := by
  have h := PT.constraintElim (c := fun p : α × Constraint => p.2)
    (f₁ := fun p x => f p.1 (.one x)) (f₂ := fun p x y z => f p.1 (.add x y z))
    (f₃ := fun p x y => f p.1 (.inv x y))
    (h₁.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
    (h₂.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
    (h₃.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id))) PT.snd'
  exact h.of_eq fun p => (constraint_eq_elim (f p.1) p.2).symm

/-- A function on constraints given by its values on the constructors. -/
theorem PT.constraintFun {f : Constraint → β}
    (h₁ : PT (fun x : ℕ => f (.one x)))
    (h₂ : PT (fun p : ℕ × ℕ × ℕ => f (.add p.1 p.2.1 p.2.2)))
    (h₃ : PT (fun p : ℕ × ℕ => f (.inv p.1 p.2))) : PT f := by
  have h := PT.constraintFun₂ (α := Unit) (f := fun _ c => f c) (h₁.comp PT.snd')
    (h₂.comp PT.snd') (h₃.comp PT.snd')
  exact (h.comp (PT.pair (PT.const ()) PT.id)).of_eq fun _ => rfl

/-! ### Unit kinds and unit specifications -/

/-- The index of a unit kind. -/
def Kind.idx : Kind → ℕ
  | .orient => 0
  | .ge => 1
  | .le => 2
  | .inv => 3

/-- The unit kind of an index. -/
def Kind.ofIdx : ℕ → Kind
  | 0 => .orient
  | 1 => .ge
  | 2 => .le
  | _ => .inv

theorem Kind.ofIdx_idx (k : Kind) : Kind.ofIdx (Kind.idx k) = k := by cases k <;> rfl

/-- Unit kinds are coded by their index. -/
instance instCodeKind : Code Kind := Code.ofInj Kind.idx Kind.ofIdx Kind.ofIdx_idx

omit [Code β] in
theorem kind_ofIdx_eq (f : Kind → β) (n : ℕ) : f (Kind.ofIdx n) =
    if n = 0 then f .orient else if n = 1 then f .ge else if n = 2 then f .le else f .inv := by
  rcases n with _ | _ | _ | n <;> simp [Kind.ofIdx]

/-- **Every function of the unit kind is polynomial-time.** -/
theorem PT.kindFun (f : Kind → β) {k : α → Kind} (hk : PT k) : PT (fun a => f (k a)) := by
  have h : PT (fun n : ℕ => if n = 0 then f .orient else if n = 1 then f .ge
      else if n = 2 then f .le else f .inv) := by fun_prop
  have h' : PT f := PT.ofInj_elim Kind.idx Kind.ofIdx Kind.ofIdx_idx
    (h.of_eq fun n => (kind_ofIdx_eq f n).symm)
  exact h'.comp hk

/-- Functions of a parameter and a unit kind. -/
theorem PT.kindFun₂ {f : α → Kind → β} (hf : ∀ k : Kind, PT (fun a => f a k)) :
    PT (fun p : α × Kind => f p.1 p.2) := by
  have h : PT (fun p : α × Kind => if Kind.idx p.2 = 0 then f p.1 .orient else if Kind.idx p.2 = 1 then
      f p.1 .ge else if Kind.idx p.2 = 2 then f p.1 .le else f p.1 .inv) := by
    have hi : PT (fun p : α × Kind => Kind.idx p.2) :=
      (PT.ofInj_to Kind.idx Kind.ofIdx Kind.ofIdx_idx).comp PT.snd'
    have h0 := (hf .orient).comp (PT.fst' (α := α) (β := Kind))
    have h1 := (hf .ge).comp (PT.fst' (α := α) (β := Kind))
    have h2 := (hf .le).comp (PT.fst' (α := α) (β := Kind))
    have h3 := (hf .inv).comp (PT.fst' (α := α) (β := Kind))
    fun_prop
  refine h.of_eq fun p => ?_
  rcases p with ⟨a, k⟩
  cases k <;> rfl

/-- A unit specification as a tuple. -/
def UnitSpec.toTuple (u : UnitSpec) : Kind × List ℕ × List ℕ := (u.kind, u.real, u.work)

/-- The unit specification of a tuple. -/
def UnitSpec.ofTuple (p : Kind × List ℕ × List ℕ) : UnitSpec := ⟨p.1, p.2.1, p.2.2⟩

/-- Unit specifications are coded as tuples. -/
instance instCodeUnitSpec : Code UnitSpec :=
  Code.ofInj UnitSpec.toTuple UnitSpec.ofTuple (fun _ => rfl)

@[fun_prop] protected theorem PT.unitSpecTuple {u : α → UnitSpec} (hu : PT u) :
    PT (fun a => UnitSpec.toTuple (u a)) :=
  (PT.ofInj_to UnitSpec.toTuple UnitSpec.ofTuple (fun _ => rfl)).comp hu

@[fun_prop] protected theorem PT.unitSpecKind {u : α → UnitSpec} (hu : PT u) :
    PT (fun a => (u a).kind) :=
  PT.fst (PT.unitSpecTuple hu)

@[fun_prop] protected theorem PT.unitSpecReal {u : α → UnitSpec} (hu : PT u) :
    PT (fun a => (u a).real) :=
  PT.fst (PT.snd (PT.unitSpecTuple hu))

@[fun_prop] protected theorem PT.unitSpecWork {u : α → UnitSpec} (hu : PT u) :
    PT (fun a => (u a).work) :=
  PT.snd (PT.snd (PT.unitSpecTuple hu))

@[fun_prop] protected theorem PT.unitSpecMk {k : α → Kind} {r w : α → List ℕ} (hk : PT k)
    (hr : PT r) (hw : PT w) : PT (fun a => (⟨k a, r a, w a⟩ : UnitSpec)) :=
  PT.ofInj_mk UnitSpec.toTuple UnitSpec.ofTuple (fun _ => rfl)
    (show PT (fun a => (k a, r a, w a)) by fun_prop)

/-! ### Global parameters -/

@[fun_prop] protected theorem PT.bigN {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => bigN (n a) (k a)) := by
  unfold bigN
  fun_prop

@[fun_prop] protected theorem PT.S {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => S (n a) (k a)) := by
  unfold S
  fun_prop

@[fun_prop] protected theorem PT.rho {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => rho (n a) (k a)) := by
  unfold rho
  fun_prop

@[fun_prop] protected theorem PT.delta {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => delta (n a) (k a)) := by
  unfold delta
  fun_prop

@[fun_prop] protected theorem PT.eps {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => eps (n a) (k a)) := by
  unfold eps
  fun_prop

/-! ### Slots, shifts, mirror -/

@[fun_prop] protected theorem PT.slotX {σ : α → ℕ} (hσ : PT σ) : PT (fun a => slotX (σ a)) := by
  unfold slotX
  fun_prop

@[fun_prop] protected theorem PT.slotA {σ : α → ℕ} (hσ : PT σ) : PT (fun a => slotA (σ a)) := by
  unfold slotA
  fun_prop

@[fun_prop] protected theorem PT.slotB {σ : α → ℕ} (hσ : PT σ) : PT (fun a => slotB (σ a)) := by
  unfold slotB
  fun_prop

@[fun_prop] protected theorem PT.shift {i : α → ℕ} (hi : PT i) : PT (fun a => shift (i a)) := by
  unfold shift
  fun_prop

@[fun_prop] protected theorem PT.xMirror {n : α → ℕ} (hn : PT n) :
    PT (fun a => xMirror (n a)) := by
  unfold xMirror
  fun_prop

@[fun_prop] protected theorem PT.mirror {n : α → ℕ} {p : α → Q2} (hn : PT n) (hp : PT p) :
    PT (fun a => mirror (n a) (p a)) := by
  unfold mirror
  fun_prop

@[fun_prop] protected theorem PT.XL {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => XL (n a) (k a)) := by
  unfold XL
  fun_prop

/-! ### Constraints and the guard count -/

@[fun_prop] protected theorem PT.isAdd {c : α → Constraint} (hc : PT c) :
    PT (fun a => isAdd (c a)) := by
  have h : PT isAdd := by
    refine PT.constraintFun ?_ ?_ ?_ <;> simp only [isAdd] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.isInv {c : α → Constraint} (hc : PT c) :
    PT (fun a => isInv (c a)) := by
  have h : PT isInv := by
    refine PT.constraintFun ?_ ?_ ?_ <;> simp only [isInv] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.isOneOf {σ : α → ℕ} {c : α → Constraint} (hσ : PT σ)
    (hc : PT c) : PT (fun a => isOneOf (σ a) (c a)) := by
  have h : PT (fun p : ℕ × Constraint => isOneOf p.1 p.2) := by
    refine PT.constraintFun₂ ?_ ?_ ?_ <;> simp only [isOneOf] <;> fun_prop
  exact h.comp (PT.pair hσ hc)

@[fun_prop] protected theorem PT.kAdd {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => kAdd (Φ a)) := by
  unfold kAdd
  fun_prop

@[fun_prop] protected theorem PT.kInv {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => kInv (Φ a)) := by
  unfold kInv
  fun_prop

@[fun_prop] protected theorem PT.slotOne {n : α → ℕ} {Φ : α → List Constraint} {σ : α → ℕ}
    (hn : PT n) (hΦ : PT Φ) (hσ : PT σ) : PT (fun a => slotOne (n a) (Φ a) (σ a)) := by
  unfold slotOne
  fun_prop

@[fun_prop] protected theorem PT.guardCount {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => guardCount (n a) (Φ a)) := by
  unfold guardCount
  fun_prop

/-! ### Units -/

@[fun_prop] protected theorem PT.workSlot {n σ : α → ℕ} (hn : PT n) (hσ : PT σ) :
    PT (fun a => workSlot (n a) (σ a)) := by
  unfold workSlot
  fun_prop

@[fun_prop] protected theorem PT.orientR {n : α → ℕ} (hn : PT n) : PT (fun a => orientR (n a)) := by
  unfold orientR
  fun_prop

@[fun_prop] protected theorem PT.orientL {n : α → ℕ} (hn : PT n) : PT (fun a => orientL (n a)) := by
  unfold orientL
  fun_prop

@[fun_prop] protected theorem PT.addR {n : α → ℕ} {c : α → Constraint} (hn : PT n) (hc : PT c) :
    PT (fun a => addR (n a) (c a)) := by
  have h : PT (fun p : ℕ × Constraint => addR p.1 p.2) := by
    refine PT.constraintFun₂ ?_ ?_ ?_ <;> simp only [addR] <;> fun_prop
  exact h.comp (PT.pair hn hc)

@[fun_prop] protected theorem PT.addL {n : α → ℕ} {c : α → Constraint} (hn : PT n) (hc : PT c) :
    PT (fun a => addL (n a) (c a)) := by
  have h : PT (fun p : ℕ × Constraint => addL p.1 p.2) := by
    refine PT.constraintFun₂ ?_ ?_ ?_ <;> simp only [addL] <;> fun_prop
  exact h.comp (PT.pair hn hc)

@[fun_prop] protected theorem PT.invR {n : α → ℕ} {c : α → Constraint} (hn : PT n) (hc : PT c) :
    PT (fun a => invR (n a) (c a)) := by
  have h : PT (fun p : ℕ × Constraint => invR p.1 p.2) := by
    refine PT.constraintFun₂ ?_ ?_ ?_ <;> simp only [invR] <;> fun_prop
  exact h.comp (PT.pair hn hc)

/-- **The units of the construction.** -/
@[fun_prop] protected theorem PT.unitSpecs {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => unitSpecs (n a) (Φ a)) := by
  unfold unitSpecs
  fun_prop

@[fun_prop] protected theorem PT.nguards {k : α → Kind} (hk : PT k) :
    PT (fun a => (k a).nguards) := PT.kindFun Kind.nguards hk

/-! ### The main area -/

@[fun_prop] protected theorem PT.pocketRel {one : α → Bool} (hone : PT one) :
    PT (fun a => pocketRel (one a)) := by
  unfold pocketRel
  fun_prop

@[fun_prop] protected theorem PT.pocket {one : α → Bool} {σ : α → ℕ} (hone : PT one) (hσ : PT σ) :
    PT (fun a => pocket (one a) (σ a)) := by
  unfold pocket
  exact PT.map (PT.q2Add PT.snd' (PT.slotA (hσ.comp PT.fst'))) (PT.pocketRel hone)

@[fun_prop] protected theorem PT.pocketClosedRel {one : α → Bool} (hone : PT one) :
    PT (fun a => pocketClosedRel (one a)) := by
  unfold pocketClosedRel
  fun_prop

@[fun_prop] protected theorem PT.pocketClosed {one : α → Bool} {σ : α → ℕ} (hone : PT one)
    (hσ : PT σ) : PT (fun a => pocketClosed (one a) (σ a)) := by
  unfold pocketClosed
  exact PT.map (PT.q2Add PT.snd' (PT.slotA (hσ.comp PT.fst'))) (PT.pocketClosedRel hone)

@[fun_prop] protected theorem PT.mL {σ : α → ℕ} (hσ : PT σ) : PT (fun a => mL (σ a)) := by
  unfold mL
  exact PT.q2Add (PT.const _) (PT.slotA hσ)

@[fun_prop] protected theorem PT.mR {σ : α → ℕ} (hσ : PT σ) : PT (fun a => mR (σ a)) := by
  unfold mR
  exact PT.q2Add (PT.const _) (PT.slotA hσ)

/-- **The bottom wall.** -/
@[fun_prop] protected theorem PT.bottomWall {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => bottomWall (n a) (Φ a)) := by
  unfold bottomWall
  fun_prop

@[fun_prop] protected theorem PT.pocketStart {n : α → ℕ} {Φ : α → List Constraint} {σ : α → ℕ}
    (hn : PT n) (hΦ : PT Φ) (hσ : PT σ) : PT (fun a => pocketStart (n a) (Φ a) (σ a)) := by
  unfold pocketStart
  fun_prop

@[fun_prop] protected theorem PT.wR {n : α → ℕ} (hn : PT n) : PT (fun a => wR (n a)) := by
  unfold wR
  fun_prop

@[fun_prop] protected theorem PT.vR {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => vR (n a) (k a)) := by
  unfold vR
  fun_prop

@[fun_prop] protected theorem PT.tR {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => tR (n a) (k a)) := by
  unfold tR
  fun_prop

@[fun_prop] protected theorem PT.tL {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => tL (n a) (k a)) := by
  unfold tL
  fun_prop

@[fun_prop] protected theorem PT.vL {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => vL (n a) (k a)) := by
  unfold vL
  fun_prop

@[fun_prop] protected theorem PT.hexTop {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => hexTop (n a) (k a)) := by
  unfold hexTop
  fun_prop

@[fun_prop] protected theorem PT.hexagon {n k : α → ℕ} (hn : PT n) (hk : PT k) :
    PT (fun a => hexagon (n a) (k a)) := by
  unfold hexagon
  fun_prop

/-! ### Template data -/

@[fun_prop] protected theorem PT.tmplD {k : α → Kind} (hk : PT k) : PT (fun a => tmplD (k a)) :=
  PT.kindFun tmplD hk

@[fun_prop] protected theorem PT.tmplV {k : α → Kind} (hk : PT k) : PT (fun a => tmplV (k a)) :=
  PT.kindFun tmplV hk

@[fun_prop] protected theorem PT.tmplT {k : α → Kind} (hk : PT k) : PT (fun a => tmplT (k a)) :=
  PT.kindFun tmplT hk

@[fun_prop] protected theorem PT.tmplPt {k : α → Kind} {V : α → ℤ × ℤ} (hk : PT k) (hV : PT V) :
    PT (fun a => tmplPt (k a) (V a)) := by
  unfold tmplPt
  fun_prop

end ArtGallery.Sec5.PTime

end
