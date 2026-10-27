module

public import ArtGallery.Stade.Polygon
public import ArtGallery.Stade.PTimeRat
public import ArtGallery.Stade.PTimeREV

/-!
# Stade's construction is polynomial-time

Codes for the data of the construction (`TKind`, `TInput`, `InputSeg`; rationals are coded by
`ArtGallery.Stade.instCodeRat`) and `fun_prop` lemmas for all its functions, bottom-up:
parameters (`PT.paramH`, …), constraint data (`PT.cKind`, `PT.cVars`, …), templates
(`PT.tkindFun`: every function of the template kind), input segments, wedges, copy nooks, and

* **`PT.poly`**: `fun a => poly (n a) (Φ a)` is polynomial-time;
* `PT.guards`.

All numbers occurring are polynomially bounded in unary (their numerators and denominators are
polynomials in `H`), which is what the unary rational arithmetic of `PTimeRat` requires.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Stade

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV ArtGallery.Stade.Chain

/-! ### Codes -/

/-- The index of a template kind. -/
def TKind.idx : TKind → ℕ
  | .invGe => 0
  | .invRevLe => 1
  | .addLe => 2
  | .addGe => 3

/-- The template kind of an index. -/
def TKind.ofIdx : ℕ → TKind
  | 0 => .invGe
  | 1 => .invRevLe
  | 2 => .addLe
  | _ => .addGe

theorem TKind.ofIdx_idx (k : TKind) : TKind.ofIdx k.idx = k := by cases k <;> rfl

/-- Template kinds are coded by their index. -/
instance instCodeTKind : Code TKind := Code.ofInj TKind.idx TKind.ofIdx TKind.ofIdx_idx

/-- A template input as a tuple. -/
def TInput.toTuple (i : TInput) : ℚ × Bool × ℕ × Bool := (i.lx, i.pos, i.role, i.ge)

/-- The template input of a tuple. -/
def TInput.ofTuple (p : ℚ × Bool × ℕ × Bool) : TInput := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

/-- Template inputs are coded as tuples. -/
instance instCodeTInput : Code TInput := Code.ofInj TInput.toTuple TInput.ofTuple (fun _ => rfl)

/-- An input segment as a tuple. -/
def InputSeg.toTuple (i : InputSeg) : ℚ × Bool × ℕ × Bool × ℕ × ℕ :=
  (i.b, i.pos, i.var, i.ge, i.slot, i.role)

/-- The input segment of a tuple. -/
def InputSeg.ofTuple (p : ℚ × Bool × ℕ × Bool × ℕ × ℕ) : InputSeg :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩

/-- Input segments are coded as tuples. -/
instance instCodeInputSeg : Code InputSeg :=
  Code.ofInj InputSeg.toTuple InputSeg.ofTuple (fun _ => rfl)

variable {α β : Type} [Code α] [Code β]

/-! ### Template kinds -/

omit [Code β] in
theorem tkind_ofIdx_eq (f : TKind → β) (n : ℕ) : f (TKind.ofIdx n) =
    if n = 0 then f .invGe else if n = 1 then f .invRevLe else if n = 2 then f .addLe
      else f .addGe := by
  rcases n with _ | _ | _ | n <;> simp [TKind.ofIdx]

/-- **Every function of the template kind is polynomial-time.** -/
theorem PT.tkindFun (f : TKind → β) {k : α → TKind} (hk : PT k) : PT (fun a => f (k a)) := by
  have h : PT (fun n : ℕ => if n = 0 then f .invGe else if n = 1 then f .invRevLe
      else if n = 2 then f .addLe else f .addGe) := by fun_prop
  have h' : PT f := PT.ofInj_elim TKind.idx TKind.ofIdx TKind.ofIdx_idx
    (h.of_eq fun n => (tkind_ofIdx_eq f n).symm)
  exact h'.comp hk

@[fun_prop] protected theorem PT.tmplInputs {k : α → TKind} (hk : PT k) :
    PT (fun a => tmplInputs (k a)) := PT.tkindFun tmplInputs hk

@[fun_prop] protected theorem PT.tmplFloor {k : α → TKind} (hk : PT k) :
    PT (fun a => tmplFloor (k a)) := PT.tkindFun tmplFloor hk

/-! ### Template inputs and input segments -/

@[fun_prop] protected theorem PT.tinputTuple {i : α → TInput} (hi : PT i) :
    PT (fun a => (i a).toTuple) :=
  (PT.ofInj_to TInput.toTuple TInput.ofTuple (fun _ => rfl)).comp hi

@[fun_prop] protected theorem PT.tinputLx {i : α → TInput} (hi : PT i) : PT (fun a => (i a).lx) :=
  PT.fst (PT.tinputTuple hi)

@[fun_prop] protected theorem PT.tinputPos {i : α → TInput} (hi : PT i) :
    PT (fun a => (i a).pos) :=
  PT.fst (PT.snd (PT.tinputTuple hi))

@[fun_prop] protected theorem PT.tinputRole {i : α → TInput} (hi : PT i) :
    PT (fun a => (i a).role) :=
  PT.fst (PT.snd (PT.snd (PT.tinputTuple hi)))

@[fun_prop] protected theorem PT.tinputGe {i : α → TInput} (hi : PT i) : PT (fun a => (i a).ge) :=
  PT.snd (PT.snd (PT.snd (PT.tinputTuple hi)))

@[fun_prop] protected theorem PT.inputSegTuple {i : α → InputSeg} (hi : PT i) :
    PT (fun a => (i a).toTuple) :=
  (PT.ofInj_to InputSeg.toTuple InputSeg.ofTuple (fun _ => rfl)).comp hi

@[fun_prop] protected theorem PT.inputSegB {i : α → InputSeg} (hi : PT i) :
    PT (fun a => (i a).b) :=
  PT.fst (PT.inputSegTuple hi)

@[fun_prop] protected theorem PT.inputSegPos {i : α → InputSeg} (hi : PT i) :
    PT (fun a => (i a).pos) :=
  PT.fst (PT.snd (PT.inputSegTuple hi))

@[fun_prop] protected theorem PT.inputSegVar {i : α → InputSeg} (hi : PT i) :
    PT (fun a => (i a).var) :=
  PT.fst (PT.snd (PT.snd (PT.inputSegTuple hi)))

@[fun_prop] protected theorem PT.inputSegGe {i : α → InputSeg} (hi : PT i) :
    PT (fun a => (i a).ge) :=
  PT.fst (PT.snd (PT.snd (PT.snd (PT.inputSegTuple hi))))

@[fun_prop] protected theorem PT.inputSegMk {b : α → ℚ} {pos : α → Bool} {var : α → ℕ}
    {ge : α → Bool} {slot role : α → ℕ} (hb : PT b) (hpos : PT pos) (hvar : PT var) (hge : PT ge)
    (hslot : PT slot) (hrole : PT role) :
    PT (fun a => (⟨b a, pos a, var a, ge a, slot a, role a⟩ : InputSeg)) :=
  PT.ofInj_mk InputSeg.toTuple InputSeg.ofTuple (fun _ => rfl)
    (show PT (fun a => (b a, pos a, var a, ge a, slot a, role a)) by fun_prop)

/-! ### Constraints -/

@[fun_prop] protected theorem PT.isGad {c : α → Constraint} (hc : PT c) :
    PT (fun a => isGad (c a)) := by
  have h : PT isGad := by
    refine PT.revFun ?_ ?_ ?_ ?_ ?_ <;> simp only [isGad] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.isAdd {c : α → Constraint} (hc : PT c) :
    PT (fun a => isAdd (c a)) := by
  have h : PT isAdd := by
    refine PT.revFun ?_ ?_ ?_ ?_ ?_ <;> simp only [isAdd] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.cKind {c : α → Constraint} (hc : PT c) :
    PT (fun a => cKind (c a)) := by
  have h : PT cKind := by
    refine PT.revFun ?_ ?_ ?_ ?_ ?_ <;> simp only [cKind] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.cVars {c : α → Constraint} (hc : PT c) :
    PT (fun a => cVars (c a)) := by
  have h : PT cVars := by
    refine PT.revFun ?_ ?_ ?_ ?_ ?_ <;> simp only [cVars] <;> fun_prop
  exact h.comp hc

@[fun_prop] protected theorem PT.isOneOf {k : α → ℕ} {c : α → Constraint} (hk : PT k)
    (hc : PT c) : PT (fun a => isOneOf (k a) (c a)) := by
  have h : PT (fun p : ℕ × Constraint => isOneOf p.1 p.2) := by
    have e : ∀ p : ℕ × Constraint, isOneOf p.1 p.2 = p.2.elim (fun x => x == p.1)
        (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false) (fun _ _ _ => false) := by
      intro p; cases p.2 <;> rfl
    simp only [e]
    fun_prop
  exact h.comp (PT.pair hk hc)

/-! ### Parameters -/

@[fun_prop] protected theorem PT.gad {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => gad (Φ a)) := by
  unfold gad
  fun_prop

@[fun_prop] protected theorem PT.gadAt {Φ : α → List Constraint} {c : α → ℕ} (hΦ : PT Φ)
    (hc : PT c) : PT (fun a => gadAt (Φ a) (c a)) := by
  unfold gadAt
  fun_prop

@[fun_prop] protected theorem PT.hasOne {Φ : α → List Constraint} {k : α → ℕ} (hΦ : PT Φ)
    (hk : PT k) : PT (fun a => hasOne (Φ a) (k a)) := by
  unfold hasOne
  fun_prop

@[fun_prop] protected theorem PT.paramC {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => paramC (Φ a)) := by
  unfold paramC
  fun_prop

@[fun_prop] protected theorem PT.paramDV {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => paramDV (Φ a)) := by
  unfold paramDV
  fun_prop

@[fun_prop] protected theorem PT.paramH {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => paramH (n a) (Φ a)) := by
  unfold paramH
  fun_prop

@[fun_prop] protected theorem PT.paramX0 {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => paramX0 (n a) (Φ a)) := by
  unfold paramX0
  fun_prop

@[fun_prop] protected theorem PT.varA {Φ : α → List Constraint} {k : α → ℕ} (hΦ : PT Φ)
    (hk : PT k) : PT (fun a => varA (Φ a) (k a)) := by
  unfold varA
  fun_prop

@[fun_prop] protected theorem PT.slotG {n : α → ℕ} {Φ : α → List Constraint} {c : α → ℕ}
    (hn : PT n) (hΦ : PT Φ) (hc : PT c) : PT (fun a => slotG (n a) (Φ a) (c a)) := by
  unfold slotG
  fun_prop

@[fun_prop] protected theorem PT.xL {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => xL (n a) (Φ a)) := by
  unfold xL
  fun_prop

@[fun_prop] protected theorem PT.xR {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => xR (n a) (Φ a)) := by
  unfold xR
  fun_prop

/-! ### Inputs and floor -/

@[fun_prop] protected theorem PT.rptInst {H ox : α → ℚ} {p : α → RPt} (hH : PT H) (hox : PT ox)
    (hp : PT p) : PT (fun a => RPt.inst (H a) (ox a) (p a)) := by
  unfold RPt.inst
  fun_prop

@[fun_prop] protected theorem PT.slotInputs {n : α → ℕ} {Φ : α → List Constraint} {c : α → ℕ}
    (hn : PT n) (hΦ : PT Φ) (hc : PT c) : PT (fun a => slotInputs (n a) (Φ a) (c a)) := by
  unfold slotInputs
  fun_prop

@[fun_prop] protected theorem PT.inputs {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => inputs (n a) (Φ a)) := by
  unfold inputs
  fun_prop

@[fun_prop] protected theorem PT.floorFeats {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => floorFeats (n a) (Φ a)) := by
  unfold floorFeats
  fun_prop

/-! ### Ceiling -/

@[fun_prop] protected theorem PT.wedgeW1 {s : α → ℚ} {pos : α → Bool} {H : α → ℚ} (hs : PT s)
    (hpos : PT pos) (hH : PT H) : PT (fun a => wedgeW1 (s a) (pos a) (H a)) := by
  unfold wedgeW1
  fun_prop

@[fun_prop] protected theorem PT.wedgeW3 {s : α → ℚ} {pos : α → Bool} {T H : α → ℚ} (hs : PT s)
    (hpos : PT pos) (hT : PT T) (hH : PT H) : PT (fun a => wedgeW3 (s a) (pos a) (T a) (H a)) := by
  unfold wedgeW3
  fun_prop

@[fun_prop] protected theorem PT.wedgeW4 {s H : α → ℚ} (hs : PT s) (hH : PT H) :
    PT (fun a => wedgeW4 (s a) (H a)) := by
  unfold wedgeW4
  fun_prop

@[fun_prop] protected theorem PT.wedgeW5 {s H : α → ℚ} (hs : PT s) (hH : PT H) :
    PT (fun a => wedgeW5 (s a) (H a)) := by
  unfold wedgeW5
  fun_prop

@[fun_prop] protected theorem PT.varCeil {s : α → ℚ} {one : α → Bool} {H : α → ℚ} (hs : PT s)
    (hone : PT one) (hH : PT H) : PT (fun a => varCeil (s a) (one a) (H a)) := by
  unfold varCeil
  fun_prop

@[fun_prop] protected theorem PT.inputCeil {b : α → ℚ} {pos : α → Bool} {H : α → ℚ} (hb : PT b)
    (hpos : PT pos) (hH : PT H) : PT (fun a => inputCeil (b a) (pos a) (H a)) := by
  unfold inputCeil
  fun_prop

@[fun_prop] protected theorem PT.copyNook {a b : α → ℚ} {ge : α → Bool} {H : α → ℚ} (ha : PT a)
    (hb : PT b) (hge : PT ge) (hH : PT H) : PT (fun x => copyNook (a x) (b x) (ge x) (H x)) := by
  unfold copyNook nookPs nookPt nookTop nookBot nookX copyE
  fun_prop

@[fun_prop] protected theorem PT.ceilFeats {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => ceilFeats (n a) (Φ a)) := by
  unfold ceilFeats
  fun_prop

/-! ### The polygon -/

/-- **The polygon of Stade's construction is polynomial-time.** -/
@[fun_prop] protected theorem PT.poly {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => poly (n a) (Φ a)) := by
  unfold poly
  fun_prop

/-- The guard number is polynomial-time. -/
@[fun_prop] protected theorem PT.guards {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => guards (n a) (Φ a)) := by
  unfold guards
  fun_prop

end ArtGallery.Stade

end
