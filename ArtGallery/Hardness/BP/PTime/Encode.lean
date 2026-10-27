module

public import ArtGallery.Stade.Main

/-!
# Polynomial time of the instance code of a rational polygon

A code for fraction vertices (`instCodeFracPoint`, as tuples) and

* `PT.fracOfRat`: the fraction vertex `FracPoint.ofRat` of a rational point (normal forms of the
  coordinates); hence `fun_prop` proves `PT (fun a => (L a).map FracPoint.ofRat)`;
* `PT.fracEncode`, **`PT.encodeAGP`**: the instance code `encodeAGP V g` (vertex list and number
  of guards in binary) is polynomial-time.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Sec5.PTime

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

variable {α : Type} [Code α]

/-- A fraction vertex as a tuple. -/
def fracTuple (p : FracPoint) : ℤ × ℕ × ℤ × ℕ := (p.xNum, p.xDen, p.yNum, p.yDen)

/-- The fraction vertex of a tuple. -/
def fracOfTuple (t : ℤ × ℕ × ℤ × ℕ) : FracPoint := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

/-- Fraction vertices are coded as tuples. -/
instance instCodeFracPoint : Code FracPoint := Code.ofInj fracTuple fracOfTuple (fun _ => rfl)

@[fun_prop] protected theorem PT.fracTuple {p : α → FracPoint} (hp : PT p) :
    PT (fun a => fracTuple (p a)) :=
  (PT.ofInj_to fracTuple fracOfTuple (fun _ => rfl)).comp hp

@[fun_prop] protected theorem PT.fracXNum {p : α → FracPoint} (hp : PT p) :
    PT (fun a => (p a).xNum) := PT.fst (PT.fracTuple hp)

@[fun_prop] protected theorem PT.fracXDen {p : α → FracPoint} (hp : PT p) :
    PT (fun a => (p a).xDen) := PT.fst (PT.snd (PT.fracTuple hp))

@[fun_prop] protected theorem PT.fracYNum {p : α → FracPoint} (hp : PT p) :
    PT (fun a => (p a).yNum) := PT.fst (PT.snd (PT.snd (PT.fracTuple hp)))

@[fun_prop] protected theorem PT.fracYDen {p : α → FracPoint} (hp : PT p) :
    PT (fun a => (p a).yDen) := PT.snd (PT.snd (PT.snd (PT.fracTuple hp)))

@[fun_prop] protected theorem PT.fracMk {xn yn : α → ℤ} {xd yd : α → ℕ} (hxn : PT xn) (hxd : PT xd)
    (hyn : PT yn) (hyd : PT yd) : PT (fun a => (⟨xn a, xd a, yn a, yd a⟩ : FracPoint)) :=
  PT.ofInj_mk fracTuple fracOfTuple (fun _ => rfl)
    (show PT (fun a => (xn a, xd a, yn a, yd a)) by fun_prop)

/-- The fraction vertex of a rational point. -/
@[fun_prop] protected theorem PT.fracOfRat {p : α → ℚ × ℚ} (hp : PT p) :
    PT (fun a => FracPoint.ofRat (p a)) := by
  unfold FracPoint.ofRat
  fun_prop

/-- The code of a fraction vertex. -/
@[fun_prop] protected theorem PT.fracEncode {p : α → FracPoint} (hp : PT p) :
    PT (fun a => (p a).encode) := by
  unfold FracPoint.encode
  fun_prop

/-- **The code of an art-gallery instance is polynomial-time.** -/
@[fun_prop] protected theorem PT.encodeAGP {V : α → List FracPoint} {g : α → ℕ} (hV : PT V)
    (hg : PT g) : PT (fun a => encodeAGP (V a) (g a)) := by
  unfold encodeAGP
  have he : PT FracPoint.encode := PT.fracEncode PT.id
  fun_prop

/-- The instance code of a rational polygon with `g` guards. -/
theorem PT.encodeAGP_ofRat : PT (fun p : List (ℚ × ℚ) × ℕ =>
    encodeAGP (p.1.map FracPoint.ofRat) p.2) := by
  fun_prop

end ArtGallery.Sec5.PTime

end
