module

public import ArtGallery.Stade.Params
public import ArtGallery.Stade.Templates

/-!
# Stade's construction: the polygon

The polygon `poly n Φ` of `docs/stade/construction.md` §3–§7, its guard number `guards n Φ`, and the value
maps `varX`, `varY0` (proof plan §0).  The vertex list is (counterclockwise)

```
(x_L, −1),  floor features (left to right),  (x_R, −1), (x_R, 2H),
            ceiling features (right to left), (x_L, 2H)
```

* **Floor features** (`floorFeats`): the floor needle `W2` of every variable `k`
  (`k = 0, …, n−1`), then for every slot `c = 0, …, C−1` the floor features of the template of
  the `c`-th gadget constraint translated by `g_c` (`tmplFloor`).
* **Ceiling features** (`ceilFeats`): the wedges `W3`/`W1` of every input segment (by decreasing
  abscissa: inputs in reverse order of `inputs n Φ`), the wedges `W1, W3` (and `W4, W5` for a
  variable with a constraint `x = 1`) of every variable (`k = n−1, …, 0`), and the copy nooks:
  for `k = n−1, …, 0` the copy nooks of the inputs copying variable `k`, in the order of the
  inputs.  This is the order of decreasing abscissa of the script (all copy nooks of a larger
  variable lie to the right, and among the copy nooks of one variable the one of the leftmost
  input lies rightmost); no sorting is needed.

All functions are computable and defined by `List.range`, `map`, `flatMap`, `filter` and
structural recursion.
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain

/-! ### Constraints and their inputs -/

/-- The gadget kind of a constraint (`one` is never a gadget; mapped to `invGe` arbitrarily). -/
def cKind : Constraint → TKind
  | .one _ => .invGe
  | .invGe .. => .invGe
  | .invRevLe .. => .invRevLe
  | .addLe .. => .addLe
  | .addGe .. => .addGe

/-- The variables of a constraint, by role (`x, y, z`). -/
def cVars : Constraint → List ℕ
  | .one x => [x]
  | .invGe x y => [x, y]
  | .invRevLe x y => [x, y]
  | .addLe x y z => [x, y, z]
  | .addGe x y z => [x, y, z]

/-- The constraint is an addition constraint (it has an aux guard). -/
def isAdd : Constraint → Bool
  | .addLe .. => true
  | .addGe .. => true
  | _ => false

/-- An input segment `{b} × [0, 6]` of the construction. -/
structure InputSeg where
  /-- The abscissa `b`. -/
  b : ℚ
  /-- The top wedge `W1` lies on the right (side `σ = +1`). -/
  pos : Bool
  /-- The variable copied by the input. -/
  var : ℕ
  /-- Copy type GE (`v_var ≥ v_in`); otherwise LE. -/
  ge : Bool
  /-- The slot of the input. -/
  slot : ℕ
  /-- The role (`0, 1, 2` for `x, y, z`). -/
  role : ℕ

/-- The input segments of slot `c`, by increasing abscissa. -/
def slotInputs (n : ℕ) (Φ : List Constraint) (c : ℕ) : List InputSeg :=
  (tmplInputs (cKind (gadAt Φ c))).map fun i =>
    ⟨(slotG n Φ c : ℚ) + i.lx, i.pos, (cVars (gadAt Φ c)).getD i.role 0, i.ge, c, i.role⟩

/-- All input segments, by increasing abscissa (slots from left to right). -/
def inputs (n : ℕ) (Φ : List Constraint) : List InputSeg :=
  (List.range (paramC Φ)).flatMap (slotInputs n Φ)

/-! ### Floor -/

/-- The floor features: the needles `W2` of the variables, then the slots. -/
def floorFeats (n : ℕ) (Φ : List Constraint) : List (List (ℚ × ℚ)) :=
  (List.range n).map (fun k => needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k))) ++
  (List.range (paramC Φ)).flatMap (fun c =>
    (tmplFloor (cKind (gadAt Φ c))).map (fun ch => ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))))

/-! ### Ceiling wedges -/

/-- The top wedge `W1` of a segment region at abscissa `s` (tip `(s, 3H)`, mouth `[s, s + 1/4]`
if `pos`, `[s − 1/4, s]` otherwise), in ceiling order (right to left). -/
def wedgeW1 (s : ℚ) (pos : Bool) (H : ℚ) : List (ℚ × ℚ) :=
  if pos then [(s + 1 / 4, 2 * H), (s, 3 * H), (s, 2 * H)]
  else [(s, 2 * H), (s, 3 * H), (s - 1 / 4, 2 * H)]

/-- The cutter `W3` of a segment region at abscissa `s` with tip height `T` (`3H` for variables,
`4H` for inputs): tip `(s ∓ 1/2, T)`, mouth through the ends of the segment. -/
def wedgeW3 (s : ℚ) (pos : Bool) (T H : ℚ) : List (ℚ × ℚ) :=
  if pos then [(s - (H - 3) / (2 * (2 * H - 3)), 2 * H), (s - 1 / 2, T), (s - 1 / 4, 2 * H)]
  else [(s + 1 / 4, 2 * H), (s + 1 / 2, T), (s + (H - 3) / (2 * (2 * H - 3)), 2 * H)]

/-- The wedge `W4` of a variable with `x = 1` (cone ∩ segment `= [H, H+1]`). -/
def wedgeW4 (s H : ℚ) : List (ℚ × ℚ) :=
  [(s - 3 * (H - 1) / (4 * (2 * H - 1)), 2 * H), (s - 3 / 4, 3 * H), (s - 3 / 8, 2 * H)]

/-- The wedge `W5` of a variable with `x = 1` (cone ∩ segment `= [H+1, H+3]`). -/
def wedgeW5 (s H : ℚ) : List (ℚ × ℚ) :=
  [(s - (H - 3) / (2 * H - 3), 2 * H), (s - 1, 3 * H), (s - (H - 1) / (2 * H - 1), 2 * H)]

/-- The ceiling wedges of variable segment at abscissa `s`, right to left. -/
def varCeil (s : ℚ) (one : Bool) (H : ℚ) : List (List (ℚ × ℚ)) :=
  [wedgeW1 s true H, wedgeW3 s true (3 * H) H] ++ (if one then [wedgeW4 s H, wedgeW5 s H] else [])

/-- The ceiling wedges of an input segment at abscissa `b`, right to left. -/
def inputCeil (b : ℚ) (pos : Bool) (H : ℚ) : List (List (ℚ × ℚ)) :=
  if pos then [wedgeW1 b true H, wedgeW3 b true (4 * H) H]
  else [wedgeW3 b false (4 * H) H, wedgeW1 b false H]

/-! ### Copy nooks -/

/-- The copy offset `e`: `+12` for type GE, `−16` for type LE. -/
def copyE (ge : Bool) : ℚ := if ge then 12 else -16

/-- The abscissa `x_N = 2a − b + e` of the copy nook of an input at `b` copying a variable at
`a`. -/
def nookX (a b : ℚ) (ge : Bool) : ℚ := 2 * a - b + copyE ge

/-- The opening `P_σ` (homothety centre of the variable segment and the nook), on the ceiling. -/
def nookPs (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ :=
  ((nookX a b ge * (2 * H - 3) + 2 * a) / (2 * H - 1), 2 * H)

/-- The opening `P_τ` (homothety centre of the input segment and the nook), on the ceiling. -/
def nookPt (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ :=
  ((nookX a b ge * (2 * H - 3) + b) / (2 * H - 2), 2 * H)

/-- The upper end `N_top` of the nook segment. -/
def nookTop (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ := (nookX a b ge, 2 * H + 1 + 3 / (2 * H - 3))

/-- The lower end `N_bot` of the nook segment. -/
def nookBot (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ := (nookX a b ge, 2 * H + 1 - 3 / (2 * H - 3))

/-- The copy nook of an input at `b` copying a variable at `a`, in ceiling order
`R_m, N_top, N_bot, L_m` (`R_m = P_τ` for type GE, `P_σ` for type LE). -/
def copyNook (a b : ℚ) (ge : Bool) (H : ℚ) : List (ℚ × ℚ) :=
  if ge then [nookPt a b ge H, nookTop a b ge H, nookBot a b ge H, nookPs a b ge H]
  else [nookPs a b ge H, nookTop a b ge H, nookBot a b ge H, nookPt a b ge H]

/-! ### Ceiling -/

/-- The ceiling features, right to left: input wedges, variable wedges, copy nooks. -/
def ceilFeats (n : ℕ) (Φ : List Constraint) : List (List (ℚ × ℚ)) :=
  (inputs n Φ).reverse.flatMap (fun i => inputCeil i.b i.pos (paramH n Φ)) ++
  (List.range n).reverse.flatMap (fun k => varCeil (varA Φ k) (hasOne Φ k) (paramH n Φ)) ++
  (List.range n).reverse.flatMap (fun k => ((inputs n Φ).filter (fun i => i.var == k)).map
    (fun i => copyNook (varA Φ k) i.b i.ge (paramH n Φ)))

/-! ### The polygon -/

/-- **The polygon** of Stade's construction (rational vertices, counterclockwise). -/
def poly (n : ℕ) (Φ : List Constraint) : List (ℚ × ℚ) :=
  [(xL n Φ, -1)] ++ (floorFeats n Φ).flatten ++
    [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++ (ceilFeats n Φ).flatten ++
    [(xL n Φ, 2 * (paramH n Φ : ℚ))]

/-- **The guard number** `g(Φ) = n + m + A`: one guard per variable, per input segment and per
addition constraint. -/
def guards (n : ℕ) (Φ : List Constraint) : ℕ :=
  n + (inputs n Φ).length + ((gad Φ).filter isAdd).length

/-- The abscissa `a_i = i·D_V` of the segment of variable `i`. -/
def varX (_n : ℕ) (Φ : List Constraint) (i : ℕ) : ℚ := (varA Φ i : ℚ)

/-- The base ordinate `H − 1`: the guard of variable `i` with value `v` sits at
`(varX i, varY0 + 2v)`. -/
def varY0 (n : ℕ) (Φ : List Constraint) : ℚ := (paramH n Φ : ℚ) - 1

end

end ArtGallery.Stade
