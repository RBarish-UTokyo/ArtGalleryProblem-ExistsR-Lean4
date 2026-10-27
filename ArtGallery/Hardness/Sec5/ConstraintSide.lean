module

public import ArtGallery.Hardness.Sec5.ConstraintKinds

/-!
# Section 5, constraints: the guards of a side

`SideG`: a guard set `G` of a polygon `Q` with the units `us` of one side (`SideAt`), in the
working frame of the side, whose points are base guards `(27σ/2 + off σ, 0)`, the corridor
stationary guards or template guards `tgs j X` of the units `j` of the side, or points of the far
region `x ≤ −S/2`, `S − 1 ≤ y ≤ S + 3N + 3` (the units of the other side).

`SideG.unitG`: such a guard set satisfies `UnitG` for every unit of the side (the guards of the
other units of the side lie in their unit boxes, at least `3` higher or lower: `Foreign`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon Tmpl Vis.Cert
open Corridor (Input place)
open Corridor.Input
open ArtGallery.Sec5.Count (tsysOf uφ unitBox)

/-- The far region (the units of the other side, in the working frame). -/
def FarG (S N : ℝ) (g : Point) : Prop := g.1 ≤ -(S / 2) ∧ S - 1 ≤ g.2 ∧ g.2 ≤ S + 3 * N + 3

/-- **The guards of a side** (working frame). -/
structure SideG (Q : Polygon) (n k : ℕ) (us : List UnitSpec) (G : Set Point) (off : ℕ → ℝ)
    (tgs : (j : Fin us.length) → Fin (tsysOf (us[j]).kind).r → Point) : Prop where
  cov : ∀ z ∈ Q.filled, ∃ g ∈ G, Q.Sees g z
  off_mem : ∀ σ < 4 * n, 0 ≤ off σ ∧ off σ ≤ 3 / 2
  tg_mem : ∀ (j : Fin us.length) X, tgs j X ∈ uφ n k j (us[j]) '' convexHull ℝ (intSet ((tsysOf (us[j]).kind).spot X))
  cls : ∀ g ∈ G, (∃ σ < 4 * n, g = (27 * (σ : ℝ) / 2 + off σ, 0)) ∨
    (∃ j : Fin us.length, (∃ kk < (unitInput n k j (us[j])).np,
        g = ratPoint ((unitInput n k j (us[j])).sgPt kk)) ∨ ∃ X, g = tgs j X) ∨
    FarG (S n k : ℝ) ((bigN n k : ℚ) : ℝ) g

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {G : Set Point} {off : ℕ → ℝ}
  {tgs : (j : Fin us.length) → Fin (tsysOf (us[j]).kind).r → Point}
include hQ

omit hQ in
/-- The scale of a unit as a real number. -/
theorem unitInput_SR (j : ℕ) (u : UnitSpec) : ((unitInput n k j u).S : ℝ) = (S n k : ℝ) := by
  simp [unitInput]

omit hQ in
/-- The height of a unit as a real number. -/
theorem unitInput_HR (j : ℕ) (u : UnitSpec) :
    ((unitInput n k j u).H : ℝ) = (S n k : ℝ) + 3 * j + 1 := by
  simp [unitInput, unitH]

/-- The positions of unit `j` lie in its unit box. -/
theorem unit_pos_box (j : Fin us.length) {g : Point}
    (hg : (∃ kk < (unitInput n k j (us[j])).np, g = ratPoint ((unitInput n k j (us[j])).sgPt kk)) ∨
      ∃ X : Fin (tsysOf (us[j]).kind).r, g ∈ uφ n k j (us[j]) '' convexHull ℝ (intSet ((tsysOf (us[j]).kind).spot X))) :
    g ∈ unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) := by
  have hH := Count.side_unitHyp hQ j.2
  have e : unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) =
      unitBox ((unitInput n k j (us[j])).S : ℝ) ((unitInput n k j (us[j])).H : ℝ) := by
    rw [unitInput_SR, unitInput_HR]
  rw [e]
  rcases hg with ⟨kk, hkk, rfl⟩ | ⟨X, x, hx, rfl⟩
  · exact corridorBox_sub_unitBox (hH.sg_corridor hkk)
  · exact (hH.phi_spot_box hx).2

/-- The positions of unit `j` lie in its unit box. -/
theorem SideG.pos_box (hS : SideG Q n k us G off tgs) (j : Fin us.length) {g : Point}
    (hg : (∃ kk < (unitInput n k j (us[j])).np, g = ratPoint ((unitInput n k j (us[j])).sgPt kk)) ∨
      ∃ X, g = tgs j X) :
    g ∈ unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) := by
  rcases hg with h | ⟨X, rfl⟩
  · exact unit_pos_box hQ j (Or.inl h)
  · exact unit_pos_box hQ j (Or.inr ⟨X, hS.tg_mem j X⟩)

/-- **Every unit of the side sees `UnitG` guards.** -/
theorem SideG.unitG (hS : SideG Q n k us G off tgs) {m : ℕ} (hm : m < us.length) :
    UnitG Q n k us m hm (us[m]'hm).kind G off (tgs ⟨m, hm⟩) := by
  refine ⟨rfl, hS.cov, hS.off_mem, hS.tg_mem ⟨m, hm⟩, fun g hg => ?_⟩
  have hSR := unitInput_SR (n := n) (k := k) m (us[m]'hm)
  have hHR := unitInput_HR (n := n) (k := k) m (us[m]'hm)
  rcases hS.cls g hg with hb | ⟨j, hj⟩ | hf
  · exact Or.inl hb
  · by_cases hjm : (j : ℕ) = m
    · have hj' : j = ⟨m, hm⟩ := Fin.ext hjm
      subst hj'
      rcases hj with hsg | hX
      · exact Or.inr (Or.inr (Or.inl hsg))
      · exact Or.inr (Or.inr (Or.inr hX))
    · refine Or.inr (Or.inl (Or.inl ⟨(S n k : ℝ) + 3 * (j : ℕ) + 1, ?_, ?_⟩))
      · rw [hHR]
        rcases lt_or_gt_of_ne hjm with h | h
        · left
          have : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h
          linarith
        · right
          have : (m : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
          linarith
      · rw [hSR]; exact hS.pos_box hQ j hj
  · refine Or.inr (Or.inl (Or.inr ?_))
    rw [hSR]
    exact hf

end Side

end ArtGallery.Sec5.Constraint

end
