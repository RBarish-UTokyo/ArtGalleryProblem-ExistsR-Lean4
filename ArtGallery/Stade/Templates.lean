module

public import ArtGallery.Stade.RobustCheck

/-!
# Stade's construction: the gadget templates

The fixed data of the four constraint gadgets of `docs/stade/construction.md` §6–§7, in
**local coordinates** of a slot: the slot origin `g_c` is at `x = 0`, the floor is `y = −1`, the
input segments are `{δ} × [0, 6]`.

A template vertex is a triple `(x, y₀, d) : RPt` standing for `(x, y₀ − d·H)`: the only
`H`-dependent vertices are the tips of the needles (`d = 1`).

* `tmplInputs k`: the input segments, sorted by their local abscissa `δ` (`lx`), with the side
  of their top wedge `W1` (`pos`: on the right), the role (`0, 1, 2` for `x, y, z`) and the copy
  type (`ge`: the copy nook enforces `v_var ≥ v_in`);
* `tmplFloor k`: the floor features of the slot, from left to right: the gadget chain (with the
  needles hanging from the gadget walls) and the floor needles `W2` of the inputs not standing
  above the gadget;
* `tmplNooks k`, `tmplWedges k`, `tmplRoom k`, `addParams k`: further data of the gadgets
  (pockets, wedges inside the chain, the room of an addition gadget, the parameters of the
  addition algebra).

Local facts checked by `decide +kernel` with the verified checkers of
`ArtGallery/Stade/RobustCheck.lean` (valid for every `H ≥ 1000`):
`tmplFloor_ok` (every floor feature is a robust floor feature of `y = −1`), `tmplFloor_sep`
(the features are ordered and separated by vertical lines), `tmplFloor_range` (all abscissae in
`[30, 600]`), `tmplInputs_ok` (input abscissae in `[30, 600]`, increasing with gaps `≥ 44`),
`tmplPocket_convex` (every pocket is a strictly convex quadrilateral),
`tmplNook_edges` (the nook segment and a pocket wall are consecutive edges of the chain) and
`tmplWedge_edges` (the wedges are consecutive vertices of the chain).
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.Stade.Chain ArtGallery.Irrational

/-- The four kinds of gadgets. -/
inductive TKind where
  | invGe
  | invRevLe
  | addLe
  | addGe
  deriving DecidableEq

/-- An input segment of a template. -/
structure TInput where
  /-- Local abscissa `δ` of the input segment `{δ} × [0, 6]`. -/
  lx : ℚ
  /-- The top wedge `W1` lies on the right of the segment (side `σ = +1`). -/
  pos : Bool
  /-- The role: `0`, `1`, `2` for the variables `x`, `y`, `z` of the constraint. -/
  role : ℕ
  /-- The copy nook enforces `v_var ≥ v_in` (type GE); otherwise `v_var ≤ v_in` (type LE). -/
  ge : Bool
  deriving DecidableEq

/-- The input segments of a template, sorted by local abscissa. -/
def tmplInputs : TKind → List TInput
  | .invGe => [⟨40, true, 0, true⟩, ⟨100, false, 1, true⟩]
  | .invRevLe => [⟨60, false, 0, false⟩, ⟨104, false, 1, true⟩]
  | .addLe => [⟨210, false, 1, false⟩, ⟨370, false, 0, false⟩, ⟨530, false, 2, true⟩]
  | .addGe => [⟨185 / 2, false, 2, false⟩, ⟨210, false, 1, true⟩, ⟨370, false, 0, true⟩]

/-- The floor needle `W2` hanging from `y = −1` at local abscissa `0` (mouth `[−1/4, 0]`). -/
def needleDownL : List RPt := [(-1 / 4, -1, 0), (0, -1, 1), (0, -1, 0)]

/-- The floor needle `W2` hanging from `y = −1` at local abscissa `0` (mouth `[0, 1/4]`). -/
def needleDownR : List RPt := [(0, -1, 0), (0, -1, 1), (1 / 4, -1, 0)]

/-- The gadget chain of `invGe` (§6.1). -/
def chainInvGe : List RPt :=
  [(81 / 2, -1, 0), (43, -6, 0), (61, -78, 0), (79, -78, 0), (97, -6, 0), (199 / 2, -1, 0)]

/-- The gadget chain of `invRevLe` (§6.2), with the needle of the x-input hanging from the
pocket wall `I Q`. -/
def chainInvRevLe : List RPt :=
  [(59, -1, 0), (38, -22, 0), (56, -22, 0), (60, -59 / 3, 0), (60, -59 / 3, 1),
    (241 / 4, -937 / 48, 0), (80, -8, 0), (101, -1, 0)]

/-- The gadget chain of `addLe` (§7): window, three pockets on the left wall `x = 50`, aux wedge
and two needles hanging from the bottom `y = −128`, right wall `x = 527`. -/
def chainAddLe : List RPt :=
  [(200, -1, 0), (50, -445 / 4, 0), (30, -7561 / 64, 0), (30, -7589 / 64, 0), (50, -113, 0),
    (50, -118, 0), (30, -499 / 4, 0), (30, -2001 / 16, 0), (50, -2994 / 25, 0),
    (50, -491 / 4, 0), (30, -4417 / 32, 0), (30, -4443 / 32, 0), (50, -128, 0),
    (439 / 4, -128, 0), (110, -519 / 4, 0), (441 / 4, -128, 0), (210, -128, 0), (210, -128, 1),
    (841 / 4, -128, 0), (370, -128, 0), (370, -128, 1), (1481 / 4, -128, 0), (527, -128, 0),
    (527, -1, 0)]

/-- The gadget chain of `addGe` (§7): as `addLe`, with the bay `N1 N2 Q` of the z-pocket. -/
def chainAddGe : List RPt :=
  [(85, -1, 0), (50, -37, 0), (30, -2601 / 64, 0), (30, -2649 / 64, 0), (50, -153 / 4, 0),
    (65 / 2, -5977 / 100, 0), (30, -5941 / 96, 0), (30, -6001 / 96, 0), (50, -151 / 3, 0),
    (50, -77, 0), (30, -423 / 4, 0), (30, -855 / 8, 0), (50, -94, 0), (327 / 4, -94, 0),
    (82, -113, 0), (329 / 4, -94, 0), (185 / 2, -94, 0), (185 / 2, -94, 1), (371 / 4, -94, 0),
    (210, -94, 0), (210, -94, 1), (841 / 4, -94, 0), (363, -94, 0), (363, -1, 0)]

/-- Translate a template chain horizontally (local abscissa `dx`). -/
def shiftR (dx : ℚ) (ch : List RPt) : List RPt := ch.map fun p => (dx + p.1, p.2)

/-- The floor features of a slot, from left to right (gadget chain and floor needles). -/
def tmplFloor : TKind → List (List RPt)
  | .invGe => [shiftR 40 needleDownL, chainInvGe, shiftR 100 needleDownR]
  | .invRevLe => [chainInvRevLe, shiftR 104 needleDownR]
  | .addLe => [chainAddLe, shiftR 530 needleDownR]
  | .addGe => [chainAddGe, shiftR 370 needleDownR]

/-- The gadget chain of a template. -/
def tmplChain : TKind → List RPt
  | .invGe => chainInvGe
  | .invRevLe => chainInvRevLe
  | .addLe => chainAddLe
  | .addGe => chainAddGe

/-! ### Nooks, wedges, rooms -/

/-- A nook of a gadget: the pocket `[lo, dn, up, hi]` (counterclockwise) with nook segment
`[lo, hi]` and mouth `[dn, up]`; `roles` are the roles of the two designated guards (`3` is the
aux guard of an addition gadget). -/
structure TNook where
  /-- Lower end of the nook segment. -/
  lo : ℚ × ℚ
  /-- Mouth end adjacent to `lo`. -/
  dn : ℚ × ℚ
  /-- Mouth end adjacent to `hi`. -/
  up : ℚ × ℚ
  /-- Upper end of the nook segment. -/
  hi : ℚ × ℚ
  /-- Roles of the designated guards. -/
  roles : List ℕ

/-- The nooks of a template. -/
def tmplNooks : TKind → List TNook
  | .invGe => [⟨(61, -78), (43, -6), (97, -6), (79, -78), [0, 1]⟩]
  | .invRevLe => [⟨(38, -22), (59, -1), (80, -8), (56, -22), [0, 1]⟩]
  | .addLe =>
    [⟨(30, -7589 / 64), (50, -113), (50, -445 / 4), (30, -7561 / 64), [0, 3]⟩,
     ⟨(30, -4443 / 32), (50, -128), (50, -491 / 4), (30, -4417 / 32), [1, 3]⟩,
     ⟨(30, -2001 / 16), (50, -2994 / 25), (50, -118), (30, -499 / 4), [2, 3]⟩]
  | .addGe =>
    [⟨(30, -2649 / 64), (50, -153 / 4), (50, -37), (30, -2601 / 64), [0, 3]⟩,
     ⟨(30, -855 / 8), (50, -94), (50, -77), (30, -423 / 4), [1, 3]⟩,
     ⟨(30, -6001 / 96), (50, -151 / 3), (65 / 2, -5977 / 100), (30, -5941 / 96), [2, 3]⟩]

/-- A wedge contained in a gadget chain: role of its region (`3` = aux), tip and mouth. -/
structure TWedge where
  /-- Role of the guard region (`0, 1, 2` inputs, `3` aux). -/
  role : ℕ
  /-- Tip (a template vertex, possibly at depth `H`). -/
  tip : RPt
  /-- First mouth end (in chain order). -/
  m₁ : RPt
  /-- Second mouth end (in chain order). -/
  m₂ : RPt

/-- The wedges contained in the gadget chain of a template. -/
def tmplWedges : TKind → List TWedge
  | .invGe => []
  | .invRevLe => [⟨0, (60, -59 / 3, 1), (60, -59 / 3, 0), (241 / 4, -937 / 48, 0)⟩]
  | .addLe =>
    [⟨3, (110, -519 / 4, 0), (439 / 4, -128, 0), (441 / 4, -128, 0)⟩,
     ⟨1, (210, -128, 1), (210, -128, 0), (841 / 4, -128, 0)⟩,
     ⟨0, (370, -128, 1), (370, -128, 0), (1481 / 4, -128, 0)⟩]
  | .addGe =>
    [⟨3, (82, -113, 0), (327 / 4, -94, 0), (329 / 4, -94, 0)⟩,
     ⟨2, (185 / 2, -94, 1), (185 / 2, -94, 0), (371 / 4, -94, 0)⟩,
     ⟨1, (210, -94, 1), (210, -94, 0), (841 / 4, -94, 0)⟩]

/-- The convex part of the room of an addition gadget (window `WL`, `T0`, `B0`, bottom right
corner, `WR`); empty for the inversion gadgets. -/
def tmplRoom : TKind → List (ℚ × ℚ)
  | .addLe => [(200, -1), (50, -445 / 4), (50, -128), (527, -128), (527, -1)]
  | .addGe => [(85, -1), (50, -37), (50, -94), (363, -94), (363, -1)]
  | _ => []

/-- The parameters of the algebraic core of an addition gadget (§7.1), in local coordinates
(nook line `x = 30`, aux openings on `x = 50`): `μ`, the scales `k_x, k_y, k_z`, the shadow
constants `c_x, c_y, c_z`, the aux openings `P, Q, R` and the input openings `N1, N2, N3`, the
margin `marg`. -/
structure AddParams where
  /-- `μ = k_y / (k_x + k_y)`. -/
  mu : ℚ
  /-- Scales `k_x, k_y, k_z`. -/
  k : ℚ × ℚ × ℚ
  /-- Shadow constants `c_x, c_y, c_z` (`s_i(v) = c_i − 4 k_i v`). -/
  c : ℚ × ℚ × ℚ
  /-- Aux opening of the x-nook. -/
  P : ℚ × ℚ
  /-- Aux opening of the z-nook. -/
  Q : ℚ × ℚ
  /-- Aux opening of the y-nook. -/
  R : ℚ × ℚ
  /-- Input opening of the x-nook. -/
  N1 : ℚ × ℚ
  /-- Input opening of the z-nook. -/
  N2 : ℚ × ℚ
  /-- Input opening of the y-nook. -/
  N3 : ℚ × ℚ
  /-- Margin of the nook segments. -/
  marg : ℚ

/-- The addition parameters of `addLe` and `addGe` (local coordinates). -/
def addParams : TKind → AddParams
  | .addGe => ⟨2 / 3, (1 / 16, 1 / 8, 1 / 24), (-2593 / 64, -211 / 2, -5969 / 96), (50, -37),
      (50, -151 / 3), (50, -77), (50, -153 / 4), (65 / 2, -5977 / 100), (50, -94), 3 / 8⟩
  | _ => ⟨2 / 3, (1 / 16, 1 / 8, 1 / 24), (-7557 / 64, -4411 / 32, -374 / 3), (50, -113),
      (50, -118), (50, -128), (50, -445 / 4), (50, -2994 / 25), (50, -491 / 4), 1 / 16⟩

/-! ### Checks -/

/-- All template kinds. -/
def allKinds : List TKind := [.invGe, .invRevLe, .addLe, .addGe]

theorem mem_allKinds (k : TKind) : k ∈ allKinds := by cases k <;> simp [allKinds]

/-- Every floor feature of every template is a robust floor feature of `y = −1` for
`H ≥ 1000`. -/
theorem tmplFloor_ok : allKinds.all (fun k => (tmplFloor k).all (rFloorFeatB 1000 (-1))) = true := by
  decide +kernel

/-- The floor features of every template are separated by vertical lines, in order. -/
theorem tmplFloor_sep :
    allKinds.all (fun k => pairwiseB (fun f g => decide (xmaxR f < xminR g)) (tmplFloor k)) = true := by
  decide +kernel

/-- All abscissae of the floor features lie in `[30, 600]`. -/
theorem tmplFloor_range :
    allKinds.all (fun k => (tmplFloor k).all (fun f => f.all (fun p => decide (30 ≤ p.1 ∧ p.1 ≤ 600)))) = true := by
  decide +kernel

/-- The input abscissae lie in `[30, 600]` and increase with gaps `≥ 44`. -/
theorem tmplInputs_ok :
    allKinds.all (fun k => (tmplInputs k).all (fun i => decide (30 ≤ i.lx ∧ i.lx ≤ 600)) &&
      pairwiseB (fun i j => decide (i.lx + 44 ≤ j.lx)) (tmplInputs k)) = true := by
  decide +kernel

/-- Every pocket `[lo, dn, up, hi]` is a strictly convex quadrilateral (clockwise for the
inversion gadgets, counterclockwise for the addition gadgets). -/
theorem tmplPocket_convex :
    allKinds.all (fun k => (tmplNooks k).all (fun nk =>
      decide ((0 < qdet nk.lo nk.dn nk.up ∧ 0 < qdet nk.dn nk.up nk.hi ∧
          0 < qdet nk.up nk.hi nk.lo ∧ 0 < qdet nk.hi nk.lo nk.dn) ∨
        (qdet nk.lo nk.dn nk.up < 0 ∧ qdet nk.dn nk.up nk.hi < 0 ∧
          qdet nk.up nk.hi nk.lo < 0 ∧ qdet nk.hi nk.lo nk.dn < 0)))) = true := by
  decide +kernel

/-- The fixed point `(x, y)` as a template vertex. -/
def fixR (p : ℚ × ℚ) : RPt := (p.1, p.2, 0)

/-- The pocket wall `dn lo` and the nook segment `lo hi` are consecutive edges of the gadget
chain (traversed as `dn, lo, hi` or as `hi, lo, dn`). -/
theorem tmplNook_edges :
    allKinds.all (fun k => (tmplNooks k).all (fun nk =>
      decide ([fixR nk.dn, fixR nk.lo, fixR nk.hi] <:+: tmplChain k) ||
      decide ([fixR nk.hi, fixR nk.lo, fixR nk.dn] <:+: tmplChain k))) = true := by
  decide +kernel

/-- The wedges `m₁, tip, m₂` are consecutive vertices of the gadget chain. -/
theorem tmplWedge_edges :
    allKinds.all (fun k => (tmplWedges k).all (fun w =>
      decide ([w.m₁, w.tip, w.m₂] <:+: tmplChain k))) = true := by
  decide +kernel

end

end ArtGallery.Stade
