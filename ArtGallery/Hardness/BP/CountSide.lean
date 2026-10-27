module

public import ArtGallery.Hardness.BP.Assemble
public import ArtGallery.Hardness.BP.CountUnit
public import ArtGallery.Hardness.BP.Templates.CountAddGE
public import ArtGallery.Hardness.BP.Templates.CountAddLE
public import ArtGallery.Hardness.BP.Templates.CountOrient
public import ArtGallery.Hardness.BP.Templates.CountInv
public import ArtGallery.Hardness.Sec5.CountSide

/-!
# Boundary-point variant, counting: the units of a side

As `Sec5/CountSide.lean`:

* `tsysOfBP k`: the template positions of a unit kind (`BP/Templates/Count*.lean`; all ranks
  `0`), with the boundary counting facts `tsysOfBP_facts` (separation region `tmplRBP k`).  The
  order of the positions: `ge`, `le`: `g, B, W, C, A`; `orient`: `g, p, B, W, A`;
  `inv`: `g, r_i, r_j`.
* `side_unitRoomBP`: the chain of a unit closed by its entrance is a room of the polygon inside
  the unit box (Section 5 `Count.unitRoom`).
* `side_unitHypBP`: every unit of a side satisfies `UnitHypBP`, hence (`UnitHypBP.okOn`) its
  positions satisfy the counting conditions for guards on the boundary.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.Count

open ArtGallery Set Polygon Sec5.Tmpl
open ArtGallery.Sec5
open ArtGallery.Sec5.Count (unitBox getD_map_ratPoint)
open ArtGallery.Sec5.Corridor (Input CorridorAt)
open ArtGallery.Sec5.Corridor.Input
open Vis.Cert
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### The template positions of a kind -/

/-- The template positions of a unit kind (boundary-point templates). -/
def tsysOfBP : Kind → TSys
  | .orient => BP.Tmpl.bpORTS
  | .ge => BP.Tmpl.bpGETS
  | .le => BP.Tmpl.bpLETS
  | .inv => BP.Tmpl.bpInvTS

/-- **The boundary counting facts of the templates.** -/
theorem tsysOfBP_facts (k : Kind) :
    BP.Tmpl.TFactsBd (tmplVBP k) (tmplDBP k) (tmplRBP k) (tsysOfBP k) := by
  cases k
  · rw [tmplVBP_orient, tmplDBP_orient]; exact BP.Tmpl.bpORTS_factsBd
  · rw [tmplVBP_ge, tmplDBP_ge]; exact BP.Tmpl.bpGETS_factsBd
  · rw [tmplVBP_le, tmplDBP_le]; exact BP.Tmpl.bpLETS_factsBd
  · rw [tmplVBP_inv, tmplDBP_inv]; exact BP.Tmpl.bpInvTS_factsBd

/-- All template positions have rank `0`. -/
theorem tsysOfBP_rank (k : Kind) (X : Fin (tsysOfBP k).r) : (tsysOfBP k).rank X = 0 := by
  cases k <;> fin_cases X <;> rfl

/-- The number of template positions of a kind. -/
theorem tsysOfBP_r (k : Kind) : (tsysOfBP k).r = k.nguards - (tmplTBP k).length := by
  cases k <;> rfl

/-! ### The units of a side -/

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- The unit polygon (unit chain closed by the entrance). -/
noncomputable def unitPolyBP (n k m : ℕ) (u : UnitSpec) : Polygon :=
  Polygon.mk ((unitChainBP n k m u).map ratPoint)

theorem side_unitRoomBP :
    Q.IsRoom (unitPolyBP n k m (us[m]'hm)).filled (unitInputBP n k m (us[m]'hm)).entrance ∧
      (unitPolyBP n k m (us[m]'hm)).filled ⊆
        unitBox (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H ∧
      ∀ j < (unitChainBP n k m (us[m]'hm)).length,
        ratPoint ((unitChainBP n k m (us[m]'hm)).getD j 0) ∈
          (unitPolyBP n k m (us[m]'hm)).filled := by
  have hf := unitChainBP_feature (m := m) (u := us[m]'hm) (hQ.ok _ (List.getElem_mem hm))
    (by have := hQ.len; omega) hQ.four
  have hρ : (0 : ℝ) < (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ) := by
    have := S_pos_q (n := n) (k := k)
    have : (0 : ℚ) < Corridor.rho ((S n k : ℕ) : ℚ) := by simp only [Corridor.rho]; positivity
    exact_mod_cast this
  have hlen : 3 ≤ ((unitChainBP n k m (us[m]'hm)).map ratPoint).length := by
    have := tmplBP_length (us[m]'hm).kind
    simp [unitChainBP, placedTmplBP]; omega
  have hend := hQ.end_le hm
  obtain ⟨hR, hB, hV⟩ := Count.unitRoom hQ.simple hQ.ccw hρ hf hlen
    (st := unitStartBP n k us st m) (by simpa using hend) (fun j hj => by
      rw [hQ.vtx m hm j (by simpa using hj), getD_map_ratPoint])
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  have hent : (unitInputBP n k m (us[m]'hm)).entrance = ArtGallery.segment
      ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1 + 2 * (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ))
      ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1) := by
    rw [Corridor.Input.entrance, Corridor.Input.ratPoint_d0', Corridor.Input.ratPoint_c0', eS, eH]
    rfl
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [hent]; exact hR
  · rw [eS, eH]; exact hB
  · have := hV j (by simpa using hj)
    rwa [getD_map_ratPoint] at this

/-- **Every unit of a side satisfies the unit hypotheses** (boundary-point variant). -/
theorem side_unitHypBP :
    UnitHypBP Q (unitInputBP n k m (us[m]'hm)) (bigN n k : ℚ) (unitStartBP n k us st m)
      (unitStartBP n k us st m + (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length)
      (tmplVBP (us[m]'hm).kind) (tmplDBP (us[m]'hm).kind) (tmplRBP (us[m]'hm).kind)
      (tsysOfBP (us[m]'hm).kind)
      (tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
        (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)) (hQ.tStart hm)
      (unitPolyBP n k m (us[m]'hm)).filled := by
  have hg := hQ.good hm
  obtain ⟨hR, hB, hV⟩ := side_unitRoomBP hQ hm
  refine ⟨hQ.simple, hQ.ccw, hg, hQ.corridorAt hm, tsysOfBP_facts _, tsysOfBP_rank _,
    hQ.tmpl_simple hm, hQ.tmpl_ccw hm, hQ.chainAt hm, hQ.sepAt hm, tmplDBP_pos _, hg.S_ge_real,
    fun p => tmplMapBP_apply _ _ p, ?_, hR, hB, ?_⟩
  · intro j hj
    exact boxOK_mem (tmplBP_boxOK (us[m]'hm).kind) _ (getD_mem' hj)
  · intro j hj
    have hlen : (unitChainBP n k m (us[m]'hm)).length =
        (unitInputBP n k m (us[m]'hm)).chainBefore.length +
          (tmplVBP (us[m]'hm).kind).length + (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
      simp [unitChainBP, placedTmplBP, Nat.add_assoc]
    have e1 := hQ.tmpl_vtx hm j hj
    have e2 := hQ.vtx m hm ((unitInputBP n k m (us[m]'hm)).chainBefore.length + j) (by omega)
    rw [SideAtBP.tStart, Nat.add_assoc] at e1
    rw [e1] at e2
    rw [show tpt (tmplVBP (us[m]'hm).kind) j =
      intPoint ((tmplVBP (us[m]'hm).kind).getD j (0, 0)) from rfl, e2]
    exact hV _ (by omega)

end Side

end ArtGallery.BP.Count

end
