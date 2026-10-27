module

public import ArtGallery.Irrational.Checker

/-!
# The polygon of Section 2.1

The polygon `𝒫` of Abrahamsen–Adamaszek–Miltzow, §2.1 and Fig. 2 (p. 6–8), with its 50 corners
in counterclockwise boundary order, starting at the origin.  It is the basic rectangle
`[0,20] × [0,4]` with

* six triangular pockets `T_b^ℓ, T_b^m, T_b^r` (below) and `T_t^r, T_t^m, T_t^ℓ` (above),
* three rectangular pockets `R_r = [20,30] × [0.5,0.6]`, `R_m = [10.5,10.6] × [4,8]`,
  `R_ℓ = [-10,0] × [1.7,1.8]`,
* four quadrilateral pockets `P_b^ℓ, P_b^r, P_t^r, P_t^ℓ`.

The region is described as the union `U` of 14 closed convex pieces (`pieces`), each given by
half-plane constraints `a x + b y + c ≥ 0` with integer coefficients.  This file checks, by
kernel computation:

* `simple_P : P.Simple`;
* `boundary_subset_U : P.boundary ⊆ U`;
* the open pieces and the 13 *bridges* (an open convex set straddling the opening of a pocket)
  meet no edge.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set

/-- The 50 corners of the polygon, counterclockwise (coordinates of §2.1 and Fig. 2). -/
def paperVerts : List QPt :=
  [(0, 0), (19/10, 0), (2, -1/2), (2, 0), (3, 0), (3, -3/20), (7/2, 0), (4, 0), (4, -12/19),
   (8, -18/19), (8, 0), (12, 0), (12, -34/21), (16, -36/21), (16, 0), (189/10, 0), (19, -1/2),
   (19, 0), (20, 0), (20, 1/2), (30, 1/2), (30, 3/5), (20, 3/5), (20, 4), (191/10, 4),
   (19, 9/2), (19, 4), (52/3, 4), (52/3, 83/20), (101/6, 4), (16, 4), (16, 1776/375),
   (12, 2486/375), (12, 4), (53/5, 4), (53/5, 8), (21/2, 8), (21/2, 4), (8, 4), (8, 294/47),
   (4, 280/47), (4, 4), (21/10, 4), (2, 9/2), (2, 4), (0, 4), (0, 9/5), (-10, 9/5),
   (-10, 17/10), (0, 17/10)]

/-- The polygon `𝒫` of §2.1. -/
def P : Polygon := ⟨paperVerts.map ratPoint⟩

theorem P_n : P.n = 50 := rfl

/-! ### The pieces (constraints `a x + b y + c ≥ 0`) -/

/-- The basic rectangle `[0,20] × [0,4]`. -/
def cB : List HP := [(1, 0, 0), (-1, 0, 20), (0, 1, 0), (0, -1, 4)]
/-- `T_b^ℓ`: triangle `(1.9,0), (2,-0.5), (2,0)`. -/
def cTbl : List HP := [(0, -1, 0), (-1, 0, 2), (10, 2, -19)]
/-- `T_b^m`: triangle `(3,0), (3,-0.15), (3.5,0)`. -/
def cTbm : List HP := [(0, -1, 0), (1, 0, -3), (-6, 20, 21)]
/-- `P_b^ℓ`: quadrilateral `(4,0), (4,-12/19), (8,-18/19), (8,0)`. -/
def cPbl : List HP := [(0, -1, 0), (1, 0, -4), (-1, 0, 8), (3, 38, 12)]
/-- `P_b^r`: quadrilateral `(12,0), (12,-34/21), (16,-36/21), (16,0)`. -/
def cPbr : List HP := [(0, -1, 0), (1, 0, -12), (-1, 0, 16), (1, 42, 56)]
/-- `T_b^r`: triangle `(18.9,0), (19,-0.5), (19,0)`. -/
def cTbr : List HP := [(0, -1, 0), (-1, 0, 19), (10, 2, -189)]
/-- `T_t^ℓ`: triangle `(2,4), (2.1,4), (2,4.5)`. -/
def cTtl : List HP := [(0, 1, -4), (1, 0, -2), (-10, -2, 29)]
/-- `T_t^m`: triangle `(16 5/6,4), (17 1/3,4.15), (17 1/3,4)`. -/
def cTtm : List HP := [(0, 1, -4), (-3, 0, 52), (6, -20, -21)]
/-- `T_t^r`: triangle `(19,4), (19.1,4), (19,4.5)`. -/
def cTtr : List HP := [(0, 1, -4), (1, 0, -19), (-10, -2, 199)]
/-- `P_t^ℓ`: quadrilateral `(4,4), (8,4), (8,294/47), (4,280/47)`. -/
def cPtl : List HP := [(0, 1, -4), (1, 0, -4), (-1, 0, 8), (7, -94, 532)]
/-- `P_t^r`: quadrilateral `(12,4), (16,4), (16,1776/375), (12,2486/375)`. -/
def cPtr : List HP := [(0, 1, -4), (1, 0, -12), (-1, 0, 16), (-355, -750, 9232)]
/-- `R_m = [10.5,10.6] × [4,8]`. -/
def cRm : List HP := [(0, 1, -4), (2, 0, -21), (-5, 0, 53), (0, -1, 8)]
/-- `R_ℓ = [-10,0] × [1.7,1.8]`. -/
def cRl : List HP := [(-1, 0, 0), (1, 0, 10), (0, 10, -17), (0, -5, 9)]
/-- `R_r = [20,30] × [0.5,0.6]`. -/
def cRr : List HP := [(1, 0, -20), (-1, 0, 30), (0, 2, -1), (0, -5, 3)]

/-- The 14 pieces. -/
def pieces : List (List HP) :=
  [cB, cTbl, cTbm, cPbl, cPbr, cTbr, cTtl, cTtm, cTtr, cPtl, cPtr, cRm, cRl, cRr]

/-- The region, as a union of closed convex pieces. -/
def U : Set Point := unionHP pieces

/-! ### Bridges: open convex sets across the openings of the pockets -/

/-- Bridge across the opening of `T_b^ℓ`. -/
def wTbl : List HP := [(-1, 0, 2), (10, 2, -19), (1, 0, 0), (-1, 0, 20), (0, -1, 4)]
/-- Bridge across the opening of `T_b^m`. -/
def wTbm : List HP := [(1, 0, -3), (-6, 20, 21), (1, 0, 0), (-1, 0, 20), (0, -1, 4)]
/-- Bridge across the opening of `P_b^ℓ`. -/
def wPbl : List HP := [(1, 0, -4), (-1, 0, 8), (3, 38, 12), (1, 0, 0), (-1, 0, 20), (0, -1, 4)]
/-- Bridge across the opening of `P_b^r`. -/
def wPbr : List HP := [(1, 0, -12), (-1, 0, 16), (1, 42, 56), (1, 0, 0), (-1, 0, 20), (0, -1, 4)]
/-- Bridge across the opening of `T_b^r`. -/
def wTbr : List HP := [(-1, 0, 19), (10, 2, -189), (1, 0, 0), (-1, 0, 20), (0, -1, 4)]
/-- Bridge across the opening of `T_t^ℓ`. -/
def wTtl : List HP := [(1, 0, -2), (-10, -2, 29), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `T_t^m`. -/
def wTtm : List HP := [(-3, 0, 52), (6, -20, -21), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `T_t^r`. -/
def wTtr : List HP := [(1, 0, -19), (-10, -2, 199), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `P_t^ℓ`. -/
def wPtl : List HP := [(1, 0, -4), (-1, 0, 8), (7, -94, 532), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `P_t^r`. -/
def wPtr : List HP :=
  [(1, 0, -12), (-1, 0, 16), (-355, -750, 9232), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `R_m`. -/
def wRm : List HP := [(2, 0, -21), (-5, 0, 53), (0, -1, 8), (1, 0, 0), (-1, 0, 20), (0, 1, 0)]
/-- Bridge across the opening of `R_ℓ`. -/
def wRl : List HP := [(1, 0, 10), (0, 10, -17), (0, -5, 9), (-1, 0, 20), (0, 1, 0), (0, -1, 4)]
/-- Bridge across the opening of `R_r`. -/
def wRr : List HP := [(-1, 0, 30), (0, 2, -1), (0, -5, 3), (1, 0, 0), (0, 1, 0), (0, -1, 4)]

/-- All open sets that must avoid the boundary: the open pieces and the bridges. -/
def openSets : List (List HP) :=
  pieces ++ [wTbl, wTbm, wPbl, wPbr, wTbr, wTtl, wTtm, wTtr, wPtl, wPtr, wRm, wRl, wRr]

/-! ### Kernel-checked facts -/

theorem simpleCheck_P : simpleCheck paperVerts = true := by decide +kernel

/-- **The polygon is simple.** -/
theorem simple_P : P.Simple := simple_of_simpleCheck simpleCheck_P

theorem edgesInPieces_P : edgesInPieces paperVerts pieces = true := by decide +kernel

/-- **The boundary lies in `U`.** -/
theorem boundary_subset_U : P.boundary ⊆ U := boundary_subset_of_edgesInPieces edgesInPieces_P

theorem openAvoids_P : openSets.all (openAvoids paperVerts) = true := by decide +kernel

/-- **The open pieces and the bridges meet no edge.** -/
theorem not_mem_boundary_of_mem_open {l : List HP} (hl : l ∈ openSets) {p : Point}
    (hp : p ∈ hpo l) : p ∉ P.boundary :=
  not_mem_boundary_of_openAvoids (List.all_eq_true.1 openAvoids_P l hl) hp

end

end ArtGallery.Irrational
