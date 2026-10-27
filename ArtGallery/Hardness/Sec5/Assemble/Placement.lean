module

public import ArtGallery.Hardness.Sec5.Assemble.Simple
public import ArtGallery.Hardness.Sec5.Assemble.Entrance
public import ArtGallery.Hardness.Sec5.Templates.Tools

/-!
# Section 5: where the units sit in a polygon (generic)

`SideAt Q n k us st`: the working-frame chains of the units `us` occupy consecutive vertices of
the simple counter-clockwise polygon `Q` (unit `m` from index `unitStart … m`), and right of the
line `x = S` the boundary of `Q` consists of these chains.  The right side of `construct Φ n` is
such a side of the global polygon, the left side of its mirror image (`Assemble/Sides.lean`).

For unit `m` of such a side (corridor input `I = unitInput n k m u`, template kind `u.kind`):

* `SideAt.corridorAt`: `CorridorAt Q I a b` with `a = unitStart m`,
  `b = a + |chainBefore| + |template|` (what `Corridor/Room.lean` needs);
* `SideAt.corridorClear`: `CorridorClear Q I` (what `Good.poly_subset` needs);
* `SideAt.chainAt`: the template chain `tmplV u.kind` is the chain of the polygon
  `φ⁻¹(Q)` (template coordinates, `φ = tmplMap`) from index `a + |chainBefore|`
  (`Tmpl.ChainAt`, what the template lemmas need);
* `SideAt.sep_walls`: inside the box `|x|, |y| < 60 D` the only points of non-chain edges of
  `φ⁻¹(Q)` lie on the two channel walls `[V₀, φ⁻¹(c1)]`, `[V_l, φ⁻¹(d1)]` — the geometric content
  of `Tmpl.SepAt` (`sepAt_of_walls` turns it into `SepAt` for a region whose zones contain the
  walls).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input CorridorAt)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### Chains of a concatenation -/

/-- The chain of `A ++ B` (both nonempty): `A`, the joining edge, `B`. -/
theorem chainSet_append_two {A B : List Point} (hA : A ≠ []) (hB : B ≠ []) :
    chainSet (A ++ B) = chainSet A ∪ ArtGallery.segment (lstPt A) (fstPt B) ∪ chainSet B := by
  obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  obtain ⟨A', a, rfl⟩ : ∃ A' a, A = A' ++ [a] :=
    ⟨A.dropLast, A.getLast hA, (List.dropLast_append_getLast hA).symm⟩
  rw [chainSet_append_cons, List.append_assoc, List.singleton_append, chainSet_append_cons,
    lstPt_append_single, fstPt_cons]
  simp

/-! ### Sides -/

/-- The index of the first vertex of unit `m` of a side starting at index `st`. -/
def unitStart (n k : ℕ) (us : List UnitSpec) (st m : ℕ) : ℕ :=
  st + (((unitChains n k 0 us).take m).map List.length).sum

theorem unitStart_succ {n k : ℕ} {us : List UnitSpec} {st m : ℕ} (hm : m < us.length) :
    unitStart n k us st (m + 1) =
      unitStart n k us st m + (unitChain n k m (us[m]'hm)).length := by
  have hm' : m < (unitChains n k 0 us).length := by rw [length_unitChains]; exact hm
  simp only [unitStart, List.take_add_one, List.getElem?_eq_getElem hm', Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, getElem_unitChains, Nat.zero_add]
  omega

theorem unitStart_mono {n k : ℕ} {us : List UnitSpec} {st m m' : ℕ} (h : m ≤ m') :
    unitStart n k us st m ≤ unitStart n k us st m' := by
  simp only [unitStart, Nat.add_le_add_iff_left]
  generalize unitChains n k 0 us = l
  have e : (l.take m').take m = l.take m := by rw [List.take_take, Nat.min_eq_left h]
  have := List.sum_take_add_sum_drop ((l.take m').map List.length) m
  rw [← List.map_take, e] at this
  omega

/-- The units `us` of a side are placed in `Q`. -/
structure SideAt (Q : Polygon) (n k : ℕ) (us : List UnitSpec) (st : ℕ) : Prop where
  /-- `Q` is simple. -/
  simple : Q.Simple
  /-- `Q` is counter-clockwise. -/
  ccw : Q.InteriorLeft
  /-- The units are admissible. -/
  ok : ∀ u ∈ us, UnitOK n u
  /-- At most `N` units. -/
  len : us.length ≤ bigN n k
  /-- `4n ≤ N`. -/
  four : 4 * n ≤ bigN n k
  /-- The unit chains fit into the vertex list. -/
  fit : unitStart n k us st us.length ≤ Q.n
  /-- The vertices of unit `m`. -/
  vtx : ∀ m (hm : m < us.length), ∀ i < (unitChain n k m (us[m]'hm)).length,
    Q.vtx (unitStart n k us st m + i) = ratPoint ((unitChain n k m (us[m]'hm)).getD i 0)
  /-- Right of `x = S` the boundary consists of the unit chains. -/
  bdry : ∀ p ∈ Q.boundary, p.1 ≤ (S n k : ℝ) ∨ ∃ f ∈ sideChainsR n k us, p ∈ chainSet f

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

theorem SideAt.end_le : unitStart n k us st m + (unitChain n k m (us[m]'hm)).length ≤ Q.n := by
  rw [← unitStart_succ hm]
  exact (unitStart_mono (by omega)).trans hQ.fit

theorem SideAt.good : (unitInput n k m (us[m]'hm)).Good (bigN n k : ℚ) :=
  unitInput_good (hQ.ok _ (List.getElem_mem _)) (by have := hQ.len; omega) hQ.four

/-- **The corridor of unit `m` sits in `Q`.** -/
theorem SideAt.corridorAt :
    CorridorAt Q (unitInput n k m (us[m]'hm)) (unitStart n k us st m)
      (unitStart n k us st m + (unitInput n k m (us[m]'hm)).chainBefore.length +
        (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length) := by
  have hend := hQ.end_le hm
  have hlen : (unitChain n k m (us[m]'hm)).length =
      (unitInput n k m (us[m]'hm)).chainBefore.length +
        (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length +
        (unitInput n k m (us[m]'hm)).chainAfter.length := by
    simp [unitChain, Nat.add_assoc]
  constructor
  · intro j hj
    rw [Nat.mod_eq_of_lt (by omega), hQ.vtx m hm j (by omega)]
    congr 1
    simp only [unitChain, List.append_assoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · intro j hj
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_assoc, Nat.add_assoc, hQ.vtx m hm _ (by omega)]
    congr 1
    simp only [unitChain]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]; omega

omit hQ in
/-- The real working-frame chain of unit `m`. -/
theorem SideAt.mem_side : (unitChain n k m (us[m]'hm)).map ratPoint ∈ sideChainsR n k us := by
  simp only [sideChainsR]
  have h1 := List.getElem_mem (l := unitChains n k 0 us) (n := m) (by rw [length_unitChains]; exact hm)
  rw [getElem_unitChains] at h1
  simp only [Nat.zero_add] at h1
  exact List.mem_map_of_mem h1

end Side

end ArtGallery.Sec5

end
