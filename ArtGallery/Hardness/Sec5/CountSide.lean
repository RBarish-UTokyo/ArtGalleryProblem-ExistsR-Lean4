module

public import ArtGallery.Hardness.Sec5.Assemble
public import ArtGallery.Hardness.Sec5.CountUnit
public import ArtGallery.Hardness.Sec5.CountTmplGE
public import ArtGallery.Hardness.Sec5.CountTmplLE
public import ArtGallery.Hardness.Sec5.CountTmplOrient
public import ArtGallery.Hardness.Sec5.CountTmplInv
public import ArtGallery.Stade.Counting

/-!
# Section 5, counting: the units of a side

* `tsysOf k`: the template positions of a unit kind, `tsysOf_facts`.
* `unitRoom`: the chain of a unit (`UnitFeature`) closed by the entrance `d0 c0` is a simple
  counter-clockwise polygon whose region is a room of the global polygon with door the entrance,
  inside the unit box.
* `SideAt.unitHyp`: every unit of a side satisfies `UnitHyp`, hence (`UnitHyp.ok`) its positions
  satisfy the counting conditions with region `unitBox S H_m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Count

open ArtGallery Set Polygon Tmpl
open Corridor (Input CorridorAt)
open Corridor.Input
open Vis.Cert
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### The template positions of a kind -/

/-- The template positions of a unit kind. -/
def tsysOf : Kind → TSys
  | .orient => addORTS
  | .ge => addGETS
  | .le => addLETS
  | .inv => invTS

theorem tsysOf_facts (k : Kind) : (tsysOf k).Facts (tmplV k) (tmplD k) := by
  cases k
  · rw [tmplV_orient, tmplD_orient]; exact addORTS_facts
  · rw [tmplV_ge, tmplD_ge]; exact addGETS_facts
  · rw [tmplV_le, tmplD_le]; exact addLETS_facts
  · rw [tmplV_inv, tmplD_inv]; exact invTS_facts

/-- The number of template positions of a kind. -/
theorem tsysOf_r (k : Kind) : (tsysOf k).r = k.nguards - (tmplT k).length := by
  cases k <;> rfl

/-! ### The unit room -/

/-- **The unit room.** A chain `f` of the polygon `Q` (no wrap-around) with the unit features is,
closed by its entrance, a simple counter-clockwise polygon whose region is a room of `Q` with door
the entrance, and which lies in the unit box. -/
theorem unitRoom {Q : Polygon} (hQ : Q.Simple) (hQL : Q.InteriorLeft) {S H ρ : ℝ} (hρ : 0 < ρ)
    {f : List Point} (hf : UnitFeature S H ρ f) (hlen : 3 ≤ f.length) {st : ℕ}
    (hfit : st + f.length ≤ Q.n) (hvtx : ∀ j < f.length, Q.vtx (st + j) = f.getD j (0, 0)) :
    Q.IsRoom (Polygon.mk f).filled (ArtGallery.segment (S, H + 2 * ρ) (S, H)) ∧
      (Polygon.mk f).filled ⊆ unitBox S H ∧
      ∀ j < f.length, f.getD j (0, 0) ∈ (Polygon.mk f).filled := by
  -- decomposition `f = a :: m ++ [z]`
  obtain ⟨a, f', rfl⟩ := List.exists_cons_of_ne_nil (show f ≠ [] by rintro rfl; simp at hlen)
  have hf'ne : f' ≠ [] := by rintro rfl; simp at hlen
  obtain ⟨m, z, hmz⟩ : ∃ m z, f' = m ++ [z] :=
    ⟨f'.dropLast, f'.getLast hf'ne, (List.dropLast_append_getLast hf'ne).symm⟩
  subst hmz
  have hm : m ≠ [] := by rintro rfl; simp at hlen
  have hfst : fstPt (a :: (m ++ [z])) = a := rfl
  have hlst : lstPt (a :: (m ++ [z])) = z := by
    rw [show a :: (m ++ [z]) = (a :: m) ++ [z] by simp, lstPt_append_single]
  have ha : a = (S, H) := by rw [← hfst]; exact hf.fst
  have hz : z = (S, H + 2 * ρ) := by rw [← hlst]; exact hf.lst
  have hc : ChainSimple (a :: m ++ [z]) := by simpa using hf.simple
  -- vertices are in the box
  have hvb : ∀ v ∈ a :: (m ++ [z]), S ≤ v.1 ∧ v.1 ≤ S + 4 ∧ H - 1 - 1 / 100 ≤ v.2 ∧
      v.2 ≤ H + 3 / 2 := fun v hv => hf.box v (mem_chainSet_of_mem' hv hf.len)
  have hK : (Polygon.mk (a :: (m ++ [z]))).Simple := by
    have := simple_of_chain hm hc ?_
    · simpa using this
    rintro p ⟨hp1, hp2⟩
    have hpx : p.1 = S := by
      rw [ha, hz] at hp1
      obtain ⟨t, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp1
      simp [Geometry.lerp]
    rcases hf.right p (by simpa using hp2) with h | h | h
    · linarith
    · rw [hfst] at h; exact Or.inl h
    · rw [hlst] at h; exact Or.inr h
  have hKn : (Polygon.mk (a :: (m ++ [z]))).n = m.length + 2 := by simp [Polygon.n]
  have hvtxK : ∀ j < (Polygon.mk (a :: (m ++ [z]))).n,
      (Polygon.mk (a :: (m ++ [z]))).vtx j ∈ a :: (m ++ [z]) := by
    intro j hj
    simp only [Polygon.vtx]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Polygon.n] using hj)]
    exact List.getElem_mem _
  have hlast : (Polygon.mk (a :: (m ++ [z]))).vtx (m.length + 1) = z := by
    simp only [Polygon.vtx]
    rw [show a :: (m ++ [z]) = (a :: m) ++ [z] by simp]
    exact getD_append_singleton_last (a :: m) z
  have hfirst : (Polygon.mk (a :: (m ++ [z]))).vtx 0 = a := rfl
  have hKL : (Polygon.mk (a :: (m ++ [z]))).InteriorLeft := by
    refine Polygon.interiorLeft_of_supporting_edge hK (i := m.length + 1) (by omega) ?_
    intro j hj
    have b1 := (hvb _ (hvtxK j hj)).1
    rw [show (m.length + 1 + 1) % (Polygon.mk (a :: (m ++ [z]))).n = 0 by
      rw [hKn]; simp, hlast, hfirst]
    generalize (Polygon.mk (a :: (m ++ [z]))).vtx j = v at b1 ⊢
    rw [ha, hz]
    simp only [det]
    nlinarith
  have hn : (a :: (m ++ [z])).length = m.length + 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · have hR := Polygon.isRoom_of_chain hQ hQL hK hKL (a := st) (m := m.length + 1) hKn
      (fun j hj => by
        rw [Nat.mod_eq_of_lt (by rw [hn] at hfit; omega), hvtx j (by rw [hn]; omega)]
        rfl)
    rw [hlast, hfirst] at hR
    rwa [← ha, ← hz]
  · intro p hp
    have f1 := Stade.filled_fst_ge _ (fun j hj => (hvb _ (hvtxK j hj)).1) p hp
    have f2 := Stade.filled_fst_le _ (fun j hj => (hvb _ (hvtxK j hj)).2.1) p hp
    have f3 := Stade.filled_snd_ge _ (fun j hj => (hvb _ (hvtxK j hj)).2.2.1) p hp
    have f4 := Stade.filled_snd_le _ (fun j hj => (hvb _ (hvtxK j hj)).2.2.2) p hp
    exact ⟨f1, f2, f3, f4⟩
  · intro j hj
    have : (Polygon.mk (a :: (m ++ [z]))).vtx j = (a :: (m ++ [z])).getD j (0, 0) := rfl
    rw [← this]
    exact Or.inl ⟨j, by simpa [Polygon.n] using hj, Geometry.left_mem_segment _ _⟩

/-! ### The units of a side -/

theorem getD_map_ratPoint (l : List Q2) (j : ℕ) :
    (l.map ratPoint).getD j (0, 0) = ratPoint (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [ratPoint]

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- The unit polygon (unit chain closed by the entrance). -/
noncomputable def unitPoly (n k m : ℕ) (u : UnitSpec) : Polygon :=
  Polygon.mk ((unitChain n k m u).map ratPoint)

theorem side_unitRoom :
    Q.IsRoom (unitPoly n k m (us[m]'hm)).filled (unitInput n k m (us[m]'hm)).entrance ∧
      (unitPoly n k m (us[m]'hm)).filled ⊆
        unitBox (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H ∧
      ∀ j < (unitChain n k m (us[m]'hm)).length,
        ratPoint ((unitChain n k m (us[m]'hm)).getD j 0) ∈ (unitPoly n k m (us[m]'hm)).filled := by
  have hf := unitChain_feature (m := m) (u := us[m]'hm) (hQ.ok _ (List.getElem_mem hm))
    (by have := hQ.len; omega) hQ.four
  have hg := hQ.good hm
  have hρ : (0 : ℝ) < (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ) := by
    have := S_pos_q (n := n) (k := k)
    have : (0 : ℚ) < Corridor.rho ((S n k : ℕ) : ℚ) := by simp only [Corridor.rho]; positivity
    exact_mod_cast this
  have hlen : 3 ≤ ((unitChain n k m (us[m]'hm)).map ratPoint).length := by
    have := tmpl_length (us[m]'hm).kind
    simp [unitChain, placedTmpl]; omega
  have hend := hQ.end_le hm
  obtain ⟨hR, hB, hV⟩ := Count.unitRoom hQ.simple hQ.ccw hρ hf hlen (st := unitStart n k us st m)
    (by simpa using hend) (fun j hj => by
      rw [hQ.vtx m hm j (by simpa using hj), getD_map_ratPoint])
  have eS := hQ.cast_S hm
  have eH := hQ.cast_H hm
  have hent : (unitInput n k m (us[m]'hm)).entrance = ArtGallery.segment
      ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1 + 2 * (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ))
      ((S n k : ℝ), (S n k : ℝ) + 3 * m + 1) := by
    rw [Corridor.Input.entrance, Corridor.Input.ratPoint_d0', Corridor.Input.ratPoint_c0', eS, eH]
    rfl
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [hent]; exact hR
  · rw [eS, eH]; exact hB
  · have := hV j (by simpa using hj)
    rwa [getD_map_ratPoint] at this

/-- **Every unit of a side satisfies the unit hypotheses.** -/
theorem side_unitHyp :
    UnitHyp Q (unitInput n k m (us[m]'hm)) (bigN n k : ℚ) (unitStart n k us st m)
      (unitStart n k us st m + (unitInput n k m (us[m]'hm)).chainBefore.length +
        (placedTmpl (unitInput n k m (us[m]'hm)) (us[m]'hm).kind).length)
      (tmplV (us[m]'hm).kind) (tmplD (us[m]'hm).kind) (tsysOf (us[m]'hm).kind)
      (tmplMap (us[m]'hm).kind (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
        (S_ne_of (hQ.good hm).S_ge_k)) (hQ.tStart hm) (unitPoly n k m (us[m]'hm)).filled := by
  have hg := hQ.good hm
  obtain ⟨hR, hB, hV⟩ := side_unitRoom hQ hm
  refine ⟨hQ.simple, hQ.ccw, hg, hQ.corridorAt hm, tsysOf_facts _, hQ.tmpl_simple hm,
    hQ.tmpl_ccw hm, hQ.chainAt hm, tmplD_pos _, hg.S_ge_real, fun p => tmplMap_apply _ _ p,
    ?_, hR, hB, ?_⟩
  · intro j hj
    have := boxOK_mem (tmpl_boxOK (us[m]'hm).kind) _ (getD_mem' hj)
    exact this
  · intro j hj
    have hlen : (unitChain n k m (us[m]'hm)).length =
        (unitInput n k m (us[m]'hm)).chainBefore.length +
          (tmplV (us[m]'hm).kind).length + (unitInput n k m (us[m]'hm)).chainAfter.length := by
      simp [unitChain, placedTmpl, Nat.add_assoc]
    have e1 := hQ.tmpl_vtx hm j hj
    have e2 := hQ.vtx m hm ((unitInput n k m (us[m]'hm)).chainBefore.length + j) (by omega)
    rw [SideAt.tStart, Nat.add_assoc] at e1
    rw [e1] at e2
    rw [show tpt (tmplV (us[m]'hm).kind) j = intPoint ((tmplV (us[m]'hm).kind).getD j (0, 0))
      from rfl, e2]
    exact hV _ (by omega)

end Side

end ArtGallery.Sec5.Count

end
