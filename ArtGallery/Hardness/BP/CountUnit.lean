module

public import ArtGallery.Hardness.Sec5.CountUnit
public import ArtGallery.Hardness.BP.Templates.BdTools

/-!
# Boundary-point variant, counting: the positions of one unit

As `Sec5/CountUnit.lean`, for guards restricted to the boundary (allowed set `Ω = ∂Q`).  A unit
(corridor + placed template) in a simple counter-clockwise polygon `Q` is given by the hypotheses
`UnitHypBP`: the corridor of the input `I` sits in `Q` (`CorridorAt`), the template chain `V` sits
in `φ⁻¹(Q)` (`ChainAt`) and is separated from the rest of the boundary there (`SepAt` with the
region `R`), the template position system `T` (all ranks `0`) satisfies the boundary counting
facts `TFactsBd`, and the unit room `K` is a room of `Q` inside the unit box.

The positions of the unit are those of Section 5 (`Count.unitSys`): the corridor stationary guards
`p_k` (rank `np − 1 − k`) and the template positions (rank `np`).  `UnitHypBP.okOn`: they satisfy
`PosSys.OKOn Q Q.boundary` with the region `unitBox S H`.  The corridor conditions hold for all
points of the plane (Section 5); only the template conditions (W1), (W3) use that the guards lie
on the boundary.  `UnitHypBP.spot_bd`: every position lies on `∂Q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.Count

open ArtGallery Set Polygon Sec5.Tmpl
open ArtGallery.Sec5.Count (PosSys unitSys unitBox sees_sub)
open ArtGallery.Sec5.Corridor (Input CorridorAt corridorBox)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.BP.Tmpl (TFactsBd)
open Vis.Cert

/-- The hypotheses on a unit (boundary-point variant). -/
structure UnitHypBP (Q : Polygon) (I : Input) (N : ℚ) (a b : ℕ) (V : List IPt) (D : ℕ)
    (R : Region) (T : TSys) (φ : Point ≃ᵃ[ℝ] Point) (t0 : ℕ) (K : Set Point) : Prop where
  simple : Q.Simple
  ccw : Q.InteriorLeft
  good : I.Good N
  cor : CorridorAt Q I a b
  facts : TFactsBd V D R T
  rank0 : ∀ X, T.rank X = 0
  tsimple : (Hardening.Invariance.mapPoly φ.symm Q).Simple
  tccw : (Hardening.Invariance.mapPoly φ.symm Q).InteriorLeft
  chain : ChainAt (Hardening.Invariance.mapPoly φ.symm Q) V t0
  sep : SepAt (Hardening.Invariance.mapPoly φ.symm Q) V t0 R
  D_pos : 0 < D
  S_ge : 800000 ≤ (I.S : ℝ)
  φ_apply : ∀ p : Point, φ p =
    ((I.S : ℝ) + 3 + p.1 / ((D : ℝ) * I.S), (I.H : ℝ) - 1 + p.2 / ((D : ℝ) * I.S))
  vbox : ∀ j < V.length, -(50 * (D : ℤ)) ≤ (cv V j).1 ∧ (cv V j).1 ≤ 50 * D ∧
    -(50 * (D : ℤ)) ≤ (cv V j).2 ∧ (cv V j).2 ≤ 50 * D
  room : Q.IsRoom K I.entrance
  room_box : K ⊆ unitBox I.S I.H
  room_mem : ∀ j < V.length, φ (tpt V j) ∈ K

namespace UnitHypBP

variable {Q : Polygon} {I : Input} {N : ℚ} {a b : ℕ} {V : List IPt} {D : ℕ} {R : Region}
  {T : TSys} {φ : Point ≃ᵃ[ℝ] Point} {t0 : ℕ} {K : Set Point}
  (h : UnitHypBP Q I N a b V D R T φ t0 K)
include h

/-- Visibility of a placed template point, in template coordinates. -/
theorem sees_iff {x t : Point} :
    Q.Sees x (φ t) ↔ (Hardening.Invariance.mapPoly φ.symm Q).Sees (φ.symm x) t := by
  have := Vis.Cert.sees_mapPoly_iff φ.symm Q x (φ t)
  rw [AffineEquiv.symm_apply_apply] at this
  exact this.symm

theorem DS_pos : (0 : ℝ) < (D : ℝ) * I.S := by
  have := h.S_ge
  have : (0 : ℝ) < D := by exact_mod_cast h.D_pos
  positivity

/-- A placed point of the template box lies in the unit box, strictly east of the window. -/
theorem phi_box {t : Point} (h1 : -(50 * (D : ℝ)) ≤ t.1) (h2 : t.1 ≤ 50 * D)
    (h3 : -(50 * (D : ℝ)) ≤ t.2) (h4 : t.2 ≤ 50 * D) :
    (I.S : ℝ) + 2 < (φ t).1 ∧ φ t ∈ unitBox I.S I.H := by
  have hDS := h.DS_pos
  have hS := h.S_ge
  have hD : (0 : ℝ) < D := by exact_mod_cast h.D_pos
  have b1 : -(1 / 100 : ℝ) ≤ t.1 / ((D : ℝ) * I.S) ∧ t.1 / ((D : ℝ) * I.S) ≤ 1 / 100 := by
    constructor
    · rw [le_div_iff₀ hDS]; nlinarith
    · rw [div_le_iff₀ hDS]; nlinarith
  have b2 : -(1 / 100 : ℝ) ≤ t.2 / ((D : ℝ) * I.S) ∧ t.2 / ((D : ℝ) * I.S) ≤ 1 / 100 := by
    constructor
    · rw [le_div_iff₀ hDS]; nlinarith
    · rw [div_le_iff₀ hDS]; nlinarith
  rw [h.φ_apply]
  refine ⟨by simp only; linarith, ?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith

theorem phi_vtx_box {j : ℕ} (hj : j < V.length) :
    (I.S : ℝ) + 2 < (φ (tpt V j)).1 ∧ φ (tpt V j) ∈ unitBox I.S I.H := by
  obtain ⟨b1, b2, b3, b4⟩ := h.vbox j hj
  refine h.phi_box ?_ ?_ ?_ ?_ <;> simp only [tpt, intPoint]
  · exact_mod_cast b1
  · exact_mod_cast b2
  · exact_mod_cast b3
  · exact_mod_cast b4

theorem phi_spot_box {X : Fin T.r} {x : Point} (hx : x ∈ convexHull ℝ (intSet (T.spot X))) :
    (I.S : ℝ) + 2 < (φ x).1 ∧ φ x ∈ unitBox I.S I.H := by
  obtain ⟨b1, b2, b3, b4⟩ := Sec5.Count.hull_box (h.facts.box X) x hx
  push_cast at b1 b2 b3 b4
  exact h.phi_box b1 b2 b3 b4

theorem corridorBox_sub {z : Point} (hz : z ∈ corridorBox (I.S : ℝ) (I.H : ℝ)) :
    z ∈ unitBox I.S I.H := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  exact ⟨z1, by linarith, by linarith, z4⟩

theorem tmpl_mem_filled {j : ℕ} (hj : j < V.length) : φ (tpt V j) ∈ Q.filled := by
  have := h.chain.vtx_mem_filled h.tsimple hj
  rw [Hardening.Invariance.filled_mapPoly] at this
  obtain ⟨q, hq, e⟩ := this
  rw [show tpt V j = intPoint (cv V j) from rfl, ← e, AffineEquiv.apply_symm_apply]; exact hq

theorem symm_mem_bd {p : Point} (hp : p ∈ Q.boundary) :
    φ.symm p ∈ (Hardening.Invariance.mapPoly φ.symm Q).boundary := by
  rw [Hardening.Invariance.boundary_mapPoly]; exact ⟨p, hp, rfl⟩

/-! ### The doors in template coordinates -/

theorem phi_winT0 : φ (winT0 D I.S) = ratPoint (Sec5.Corridor.c1 I.S I.H) := by
  have hDS := h.DS_pos.ne'
  have hD : (D : ℝ) ≠ 0 := by have : (0 : ℝ) < D := by exact_mod_cast h.D_pos
                              exact this.ne'
  have hS0 : (I.S : ℝ) ≠ 0 := by have := h.S_ge; positivity
  rw [h.φ_apply, Sec5.Corridor.Input.ratPoint_c1']
  simp only [winT0]
  ext <;> simp only <;> field_simp <;> ring

theorem phi_winT1 : φ (winT1 D I.S) = ratPoint (Sec5.Corridor.d1 I.S I.H) := by
  have hDS := h.DS_pos.ne'
  have hD : (D : ℝ) ≠ 0 := by have : (0 : ℝ) < D := by exact_mod_cast h.D_pos
                              exact this.ne'
  have hS : (I.S : ℝ) ≠ 0 := by have := h.S_ge; positivity
  rw [h.φ_apply, Sec5.Corridor.Input.ratPoint_d1', Sec5.Corridor.Input.rhoR_eq]
  simp only [winT1]
  ext <;> simp only <;> field_simp <;> ring

theorem phi_entT0 : φ (entT0 D I.S) = ratPoint (Sec5.Corridor.c0 I.S I.H) := by
  have hDS := h.DS_pos.ne'
  have hD : (D : ℝ) ≠ 0 := by have : (0 : ℝ) < D := by exact_mod_cast h.D_pos
                              exact this.ne'
  have hS0 : (I.S : ℝ) ≠ 0 := by have := h.S_ge; positivity
  rw [h.φ_apply, Sec5.Corridor.Input.ratPoint_c0']
  simp only [entT0]
  ext <;> simp only <;> field_simp <;> ring

theorem phi_entT1 : φ (entT1 D I.S) = ratPoint (Sec5.Corridor.d0 I.S I.H) := by
  have hDS := h.DS_pos.ne'
  have hD : (D : ℝ) ≠ 0 := by have : (0 : ℝ) < D := by exact_mod_cast h.D_pos
                              exact this.ne'
  have hS : (I.S : ℝ) ≠ 0 := by have := h.S_ge; positivity
  rw [h.φ_apply, Sec5.Corridor.Input.ratPoint_d0', Sec5.Corridor.Input.rhoR_eq]
  simp only [entT1]
  ext <;> simp only <;> field_simp <;> ring

theorem symm_mem_win {y : Point} (hy : y ∈ I.window) :
    φ.symm y ∈ ArtGallery.segment (winT0 D I.S) (winT1 D I.S) := by
  rw [Sec5.Corridor.Input.window, ← h.phi_winT0, ← h.phi_winT1,
    ← Hardening.Invariance.image_segment'] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rwa [AffineEquiv.symm_apply_apply]

theorem symm_mem_ent {y : Point} (hy : y ∈ I.entrance) :
    φ.symm y ∈ ArtGallery.segment (entT0 D I.S) (entT1 D I.S) := by
  rw [Sec5.Corridor.Input.entrance, ← h.phi_entT0, ← h.phi_entT1, Geometry.segment_comm,
    ← Hardening.Invariance.image_segment'] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rwa [AffineEquiv.symm_apply_apply]

/-! ### Template witnesses and the corridor -/

/-- **The visibility set of a template witness lies in the unit room**, hence in the unit box. -/
theorem reg_tmpl {X : Fin T.r} {j : ℕ} (hj : j ∈ T.W X) {p : Point}
    (hs : Q.Sees p (φ (tpt V j))) : p ∈ unitBox I.S I.H := by
  have hjl := h.facts.idx X j hj
  by_cases hp : p ∈ K
  · exact h.room_box hp
  exfalso
  obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door h.room (h.room_mem j hjl) hp
    (Polygon.sees_comm.1 hs)
  have h1 : Q.Sees y (φ (tpt V j)) := Polygon.sees_comm.1 (sees_sub (Polygon.sees_comm.1 hs) hy)
  rw [h.sees_iff] at h1
  exact h.facts.entrance h.tsimple h.tccw h.chain X j hj I.S h.S_ge _ (h.symm_mem_ent hyD) h1

/-- **No point of the corridor sees a main template witness.** -/
theorem corridor_not_sees {X : Fin T.r} {p : Point} (hp : p ∈ I.poly.filled) :
    ¬ Q.Sees p (φ (tpt V (T.m X))) := by
  intro hs
  have hjl := h.facts.idx X _ (h.facts.m_W X)
  have hout : φ (tpt V (T.m X)) ∉ I.poly.filled := by
    intro hin
    have := (h.good.poly_filled_box hin).2.1
    have := (h.phi_vtx_box hjl).1
    linarith
  obtain ⟨y, hyD, hy⟩ := h.good.sees_crosses_door h.simple h.ccw h.cor hout hp
    (Polygon.sees_comm.1 hs)
  have h1 : Q.Sees y (φ (tpt V (T.m X))) :=
    Polygon.sees_comm.1 (sees_sub (Polygon.sees_comm.1 hs) hy)
  rw [h.sees_iff] at h1
  rcases hyD with hw | he
  · exact h.facts.window h.tsimple h.tccw h.chain X I.S h.S_ge _ (h.symm_mem_win hw) h1
  · exact h.facts.entrance h.tsimple h.tccw h.chain X _ (h.facts.m_W X) I.S h.S_ge _
      (h.symm_mem_ent he) h1

theorem tip2_mem_filled {k : ℕ} (hk : k < I.np) : ratPoint (I.slotTip k 2) ∈ Q.filled := by
  obtain ⟨i, hi, e, -, -⟩ := h.good.tip2_vtx h.simple h.ccw h.cor hk
  rw [← e]; exact Or.inl ⟨i, hi, Geometry.left_mem_segment _ _⟩

theorem tip4_mem_filled {k : ℕ} (hk : k < I.np) : ratPoint (I.slotTip k 4) ∈ Q.filled := by
  obtain ⟨i, hi, e, -, -⟩ := h.good.tip4_vtx h.simple h.ccw h.cor hk
  rw [← e]; exact Or.inl ⟨i, hi, Geometry.left_mem_segment _ _⟩

theorem sg_corridor {k : ℕ} (hk : k < I.np) :
    ratPoint (I.sgPt k) ∈ corridorBox (I.S : ℝ) (I.H : ℝ) := by
  apply h.good.poly_filled_box
  apply Sec5.Corridor.Input.mem_poly_of_mem
  obtain ⟨A₁, A₂, hA⟩ := Sec5.Corridor.Input.chainAfter_infix_sg (I := I) hk
  rw [hA]; simp

/-- A corridor stationary guard lies on the boundary (it is a vertex of `Q`). -/
theorem sg_mem_boundary {k : ℕ} (hk : k < I.np) : ratPoint (I.sgPt k) ∈ Q.boundary := by
  have hn : 0 < Q.n := by have := h.simple.1; omega
  obtain ⟨A₁, A₂, hA⟩ := Sec5.Corridor.Input.chainAfter_infix_sg (I := I) hk
  obtain ⟨hp₁, -⟩ := Sec5.Corridor.vtx_triple hn h.cor.after hA
  refine ⟨(b + A₁.length + 1) % Q.n, Nat.mod_lt _ hn, ?_⟩
  rw [Polygon.edge, hp₁]
  exact Geometry.left_mem_segment _ _

theorem sgPt_ne {j k : ℕ} (hjk : j < k) (hk : k < I.np) :
    ratPoint (I.sgPt j) ≠ ratPoint (I.sgPt k) := by
  intro e
  have hsep := h.good.kx_sep (Or.inr rfl) hjk hk
  have hsep' : (I.kx k 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 4 : ℝ) := by exact_mod_cast hsep
  have e1 := Sec5.Corridor.Input.sgPt_on_slot4 (I := I) j
  have e2 := Sec5.Corridor.Input.sgPt_on_slot4 (I := I) k
  have f1 : ((I.sgPt j).1 : ℝ) = (I.sgPt k).1 := congrArg Prod.fst e
  have f2 : ((I.sgPt j).2 : ℝ) = (I.sgPt k).2 := congrArg Prod.snd e
  have he := h.good.eps_real
  rw [f1, f2] at e1
  linarith

/-! ### The position system of the unit -/

/-- **The positions of a unit satisfy the counting conditions for guards on the boundary.** -/
theorem okOn : (unitSys I V T φ).OKOn Q Q.boundary (unitBox I.S I.H) := by
  have hP := h.simple
  have hL := h.ccw
  have hg := h.good
  have hC := h.cor
  have F := h.facts
  have hT := h.tsimple
  have hTL := h.tccw
  have hCT := h.chain
  have hST := h.sep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_W
    rintro (k | X)
    · exact Or.inr rfl
    · exact ⟨_, F.m_W X, rfl⟩
  · -- W_filled
    rintro (k | X) w hw
    · rcases hw with rfl | rfl
      · exact h.tip2_mem_filled k.2
      · exact h.tip4_mem_filled k.2
    · obtain ⟨j, hj, rfl⟩ := hw
      exact h.tmpl_mem_filled (F.idx X j hj)
  · -- reg
    rintro (k | X) w hw p _ hs
    · rcases hw with rfl | rfl
      · exact h.corridorBox_sub (hg.poly_filled_box (hg.sees_tip2_mem hP hL hC k.2 hs))
      · exact h.corridorBox_sub (hg.poly_filled_box (hg.sees_tip4_mem hP hL hC k.2 hs))
    · obtain ⟨j, hj, rfl⟩ := hw
      exact h.reg_tmpl hj hs
  · -- spot
    rintro (k | X) p hp hall
    · exact hg.sg_unique hP hL hC k.2 (hall _ (Or.inl rfl)) (hall _ (Or.inr rfl))
    · refine ⟨φ.symm p, F.spot hT hTL hCT hST X _ (h.symm_mem_bd hp) fun j hj => ?_, by simp⟩
      have := hall _ ⟨j, hj, rfl⟩
      rwa [h.sees_iff] at this
  · -- spot_reg
    rintro (k | X) p hp
    · rcases hp with rfl
      exact h.corridorBox_sub (h.sg_corridor k.2)
    · obtain ⟨x, hx, rfl⟩ := hp
      exact (h.phi_spot_box hx).2
  · -- spot_disj
    rintro (k | X) (k' | Y) hne
    · have hkk : (k : ℕ) ≠ k' := fun e => hne (by rw [Fin.ext e])
      simp only [unitSys, Sum.elim_inl, Set.disjoint_singleton]
      rcases lt_or_gt_of_ne hkk with hlt | hlt
      · exact h.sgPt_ne hlt k'.2
      · exact (h.sgPt_ne hlt k.2).symm
    · simp only [unitSys, Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_left]
      rintro ⟨x, hx, e⟩
      have := (h.phi_spot_box hx).1
      have := (h.sg_corridor k.2).2.1
      rw [e] at *
      linarith
    · simp only [unitSys, Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_right]
      rintro ⟨x, hx, e⟩
      have := (h.phi_spot_box hx).1
      have := (h.sg_corridor k'.2).2.1
      rw [e] at *
      linarith
    · have hXY : X ≠ Y := fun e => hne (by rw [e])
      exact Set.disjoint_image_of_injective φ.injective (F.spot_disj X Y hXY)
  · -- disj
    rintro (k | X) (k' | Y) hne p hp h1 h2
    · have hkk : (k : ℕ) ≠ k' := fun e => hne (by rw [Fin.ext e])
      exact hg.not_sees_tip4_tip4 hP hL hC (Ne.symm hkk) k'.2 k.2 h1 h2
    · exact h.corridor_not_sees (X := Y) (hg.sees_tip4_mem hP hL hC k.2 h1) h2
    · exact h.corridor_not_sees (X := X) (hg.sees_tip4_mem hP hL hC k'.2 h2) h1
    · have hXY : X ≠ Y := fun e => hne (by rw [e])
      change Q.Sees p (φ _) at h1
      change Q.Sees p (φ _) at h2
      rw [h.sees_iff] at h1 h2
      exact F.disj hT hTL hCT hST hXY (h.symm_mem_bd hp) h1 h2
  · -- early
    rintro (k | X) (k' | Y) hne hr w hw p _ hp h1 h2
    · -- corridor guard `k'` (west of `k`) does not see the tips of `k`
      simp only [unitSys, Sum.elim_inl] at hr hw hp
      rcases hp with rfl
      have hkk : (k' : ℕ) ≠ k := by omega
      rcases hw with rfl | rfl
      · exact hg.not_sees_tip2_sg hP hL hC hkk k'.2 k.2 h2
      · exact hg.not_sees_tip4_sg hP hL hC hkk k'.2 k.2 h2
    · simp only [unitSys, Sum.elim_inl, Sum.elim_inr] at hr
      omega
    · -- a stationary guard sees only points west of `x = S + 2`
      simp only [unitSys, Sum.elim_inl, Sum.elim_inr] at hw hp
      rcases hp with rfl
      obtain ⟨j, hj, rfl⟩ := hw
      have c := (hg.sg_cone hP hL hC k'.2 h2).1
      have := (h.phi_vtx_box (F.idx X j hj)).1
      have := (h.sg_corridor k'.2).2.1
      linarith
    · simp only [unitSys, Sum.elim_inr, h.rank0] at hr
      omega
  · -- late
    rintro (k | X) (k' | Y) hne hr w hw p hp h1 h2
    · simp only [unitSys, Sum.elim_inl] at hr hw h1
      have hkk : (k' : ℕ) < k := by
        have : (k' : ℕ) ≠ k := fun e => hne (by rw [Fin.ext e])
        omega
      rcases hw with rfl | rfl
      · exact hg.not_sees_tip4_tip2 hP hL hC hkk k.2 h1 h2
      · exact hg.not_sees_tip4_tip4 hP hL hC (Nat.ne_of_gt hkk) k.2 k'.2 h1 h2
    · simp only [unitSys, Sum.elim_inl, Sum.elim_inr] at hw h1
      have hp : p ∈ I.poly.filled := by
        rcases hw with rfl | rfl
        · exact hg.sees_tip2_mem hP hL hC k.2 h2
        · exact hg.sees_tip4_mem hP hL hC k.2 h2
      exact h.corridor_not_sees (X := Y) hp h1
    · simp only [unitSys, Sum.elim_inl, Sum.elim_inr] at hr
      omega
    · have hXY : Y ≠ X := fun e => hne (by rw [e])
      simp only [unitSys, Sum.elim_inr] at hw h1
      obtain ⟨j, hj, rfl⟩ := hw
      rw [h.sees_iff] at h1 h2
      exact F.late hT hTL hCT hST X Y hXY j hj _ (h.symm_mem_bd hp) h1 h2

/-- **The positions of a unit lie on the boundary.** -/
theorem spot_bd : ∀ X, (unitSys I V T φ).Spot X ⊆ Q.boundary := by
  rintro (k | X) p hp
  · rcases hp with rfl
    exact h.sg_mem_boundary k.2
  · obtain ⟨x, hx, rfl⟩ := hp
    have := h.facts.spot_bd h.tsimple h.chain X hx
    rw [Hardening.Invariance.boundary_mapPoly] at this
    obtain ⟨q, hq, e⟩ := this
    rw [← e, AffineEquiv.apply_symm_apply]; exact hq

end UnitHypBP

end ArtGallery.BP.Count

end
