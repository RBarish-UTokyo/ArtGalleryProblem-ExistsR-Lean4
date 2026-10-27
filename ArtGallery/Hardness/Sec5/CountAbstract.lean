module

public import ArtGallery.Vis.Pinning

/-!
# Section 5, counting (ii)/(iii): positions grouped in zones

The guard positions of the global polygon (base segments, corridor stationary guards, template
segments and stationary guards) are grouped in **zones** (the main area, and one zone per unit).
Each zone `z` carries a *position system* `PosSys P (κ z)`: for every position `X` a main witness
`m X ∈ W X`, a finite witness set `W X`, the position itself `Spot X` and a rank (the pinning
order inside the zone), together with a region `Reg z` containing every point that sees a witness
of the zone.  The regions of different zones are disjoint, so all cross-zone conditions (W2, W3)
are automatic; inside a zone the conditions of `Polygon.guards_pinned` are required
(`PosSys.OK`).

* `card_le_of_zones`: every guard set has at least `∑ |κ z|` guards (W2).
* `pinned_of_zones`: a guard set with exactly `∑ |κ z|` guards is in bijection with the positions,
  the guard of `X` lies in `Spot X`, and it is the only guard in `Spot X`.

Both statements also come in a form with an **allowed set** `Ω` of guard positions
(`PosSys.OKOn`, `card_le_of_zones_on`, `pinned_of_zones_on`): the conditions on points are only
required for points of `Ω`, and the conclusions are for sets of guards in `Ω` seeing the region.
`PosSys.OK` is the case `Ω = P.filled` with the conditions required for all points
(`PosSys.OK.toOKOn`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Count

open ArtGallery Polygon Set

/-- The data of the guard positions of one zone: main witness, witness set, position, rank. -/
structure PosSys (κ : Type*) where
  /-- The main witness of a position. -/
  m : κ → Point
  /-- The witnesses of a position. -/
  W : κ → Set Point
  /-- The position (a guard segment or a stationary point). -/
  Spot : κ → Set Point
  /-- The pinning order inside the zone (smaller ranks are pinned first). -/
  rank : κ → ℕ

/-- The conditions on the positions of one zone, with region `Reg` (the points seeing a witness
of the zone). -/
structure PosSys.OK {κ : Type*} (P : Polygon) (Z : PosSys κ) (Reg : Set Point) : Prop where
  /-- The main witness is a witness. -/
  m_W : ∀ X, Z.m X ∈ Z.W X
  /-- The witnesses are in the region. -/
  W_filled : ∀ X, Z.W X ⊆ P.filled
  /-- Points seeing a witness lie in `Reg`. -/
  reg : ∀ X, ∀ w ∈ Z.W X, ∀ p, P.Sees p w → p ∈ Reg
  /-- (W1) A point seeing all witnesses of `X` lies on `X`. -/
  spot : ∀ X, ∀ p ∈ P.filled, (∀ w ∈ Z.W X, P.Sees p w) → p ∈ Z.Spot X
  /-- The positions lie in the region of the zone. -/
  spot_reg : ∀ X, Z.Spot X ⊆ Reg
  /-- Distinct positions are disjoint. -/
  spot_disj : ∀ X Y, X ≠ Y → Disjoint (Z.Spot X) (Z.Spot Y)
  /-- (W2) No point sees two main witnesses. -/
  disj : ∀ X Y, X ≠ Y → ∀ p, P.Sees p (Z.m X) → ¬ P.Sees p (Z.m Y)
  /-- (W3, earlier positions) Points of an earlier position seeing its main witness see no
  witness of a later position. -/
  early : ∀ X Y, Y ≠ X → Z.rank Y < Z.rank X → ∀ w ∈ Z.W X, ∀ p ∈ Z.Spot Y,
    P.Sees p (Z.m Y) → ¬ P.Sees p w
  /-- (W3, other positions) No point sees the main witness of a position that is not earlier
  together with a witness of `X`. -/
  late : ∀ X Y, Y ≠ X → ¬ Z.rank Y < Z.rank X → ∀ w ∈ Z.W X, ∀ p,
    P.Sees p (Z.m Y) → ¬ P.Sees p w

/-- The conditions on the positions of one zone for guards in the allowed set `Ω`, with region
`Reg` (the points of `Ω` seeing a witness of the zone). -/
structure PosSys.OKOn {κ : Type*} (P : Polygon) (Ω : Set Point) (Z : PosSys κ) (Reg : Set Point) :
    Prop where
  /-- The main witness is a witness. -/
  m_W : ∀ X, Z.m X ∈ Z.W X
  /-- The witnesses are in the region. -/
  W_filled : ∀ X, Z.W X ⊆ P.filled
  /-- Points of `Ω` seeing a witness lie in `Reg`. -/
  reg : ∀ X, ∀ w ∈ Z.W X, ∀ p ∈ Ω, P.Sees p w → p ∈ Reg
  /-- (W1) A point of `Ω` seeing all witnesses of `X` lies on `X`. -/
  spot : ∀ X, ∀ p ∈ Ω, (∀ w ∈ Z.W X, P.Sees p w) → p ∈ Z.Spot X
  /-- The positions lie in the region of the zone. -/
  spot_reg : ∀ X, Z.Spot X ⊆ Reg
  /-- Distinct positions are disjoint. -/
  spot_disj : ∀ X Y, X ≠ Y → Disjoint (Z.Spot X) (Z.Spot Y)
  /-- (W2) No point of `Ω` sees two main witnesses. -/
  disj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (Z.m X) → ¬ P.Sees p (Z.m Y)
  /-- (W3, earlier positions) Points of `Ω` on an earlier position seeing its main witness see no
  witness of a later position. -/
  early : ∀ X Y, Y ≠ X → Z.rank Y < Z.rank X → ∀ w ∈ Z.W X, ∀ p ∈ Ω, p ∈ Z.Spot Y →
    P.Sees p (Z.m Y) → ¬ P.Sees p w
  /-- (W3, other positions) No point of `Ω` sees the main witness of a position that is not
  earlier together with a witness of `X`. -/
  late : ∀ X Y, Y ≠ X → ¬ Z.rank Y < Z.rank X → ∀ w ∈ Z.W X, ∀ p ∈ Ω,
    P.Sees p (Z.m Y) → ¬ P.Sees p w

/-- `PosSys.OK` gives the conditions for the allowed set `Ω = P.filled`. -/
theorem PosSys.OK.toOKOn {κ : Type*} {P : Polygon} {Z : PosSys κ} {Reg : Set Point}
    (h : Z.OK P Reg) : Z.OKOn P P.filled Reg :=
  ⟨h.m_W, h.W_filled, fun X w hw p _ => h.reg X w hw p, h.spot, h.spot_reg, h.spot_disj,
    fun X Y hne p _ => h.disj X Y hne p, fun X Y hne hr w hw p _ => h.early X Y hne hr w hw p,
    fun X Y hne hr w hw p _ => h.late X Y hne hr w hw p⟩

section Zones

variable {P : Polygon} {ζ : Type*} [Fintype ζ] {κ : ζ → Type*} [∀ z, Fintype (κ z)]
  (Z : ∀ z, PosSys (κ z)) (Reg : ζ → Set Point)

/-- All positions. -/
abbrev Pos (κ : ζ → Type*) : Type _ := Σ z, κ z

/-- The global main witness. -/
def gm (X : Pos κ) : Point := (Z X.1).m X.2

/-- The global witness set. -/
def gW (X : Pos κ) : Set Point := (Z X.1).W X.2

/-- The global position. -/
def gSpot (X : Pos κ) : Set Point := (Z X.1).Spot X.2

/-- The global order: same zone, smaller rank. -/
def gr (Y X : Pos κ) : Prop := Y.1 = X.1 ∧ (Z Y.1).rank Y.2 < (Z X.1).rank X.2

theorem gr_wf : WellFounded (gr Z) :=
  Subrelation.wf (fun {_ _} h => h.2) (InvImage.wf (fun X : Pos κ => (Z X.1).rank X.2) wellFounded_lt)

variable {Z Reg} {Ω : Set Point}

section On

variable (hOK : ∀ z, (Z z).OKOn P Ω (Reg z))
  (hReg : ∀ z z', z ≠ z' → Disjoint (Reg z) (Reg z'))
include hOK hReg

theorem g_m_mem (X : Pos κ) : gm Z X ∈ P.filled := (hOK X.1).W_filled X.2 ((hOK X.1).m_W X.2)

theorem g_reg {X : Pos κ} {w p : Point} (hw : w ∈ gW Z X) (hp : p ∈ Ω) (hs : P.Sees p w) :
    p ∈ Reg X.1 :=
  (hOK X.1).reg X.2 w hw p hp hs

theorem g_cross {X Y : Pos κ} (h : X.1 ≠ Y.1) {w w' p : Point} (hw : w ∈ gW Z X)
    (hw' : w' ∈ gW Z Y) (hp : p ∈ Ω) (hs : P.Sees p w) : ¬ P.Sees p w' := fun hs' =>
  Set.disjoint_left.1 (hReg _ _ h) (g_reg hOK hReg hw hp hs) (g_reg hOK hReg hw' hp hs')

theorem g_disj : ∀ X Y : Pos κ, X ≠ Y → ∀ p ∈ Ω, P.Sees p (gm Z X) → ¬ P.Sees p (gm Z Y) := by
  rintro ⟨z, X⟩ ⟨z', Y⟩ hne p hp hs
  by_cases hz : z = z'
  · subst hz
    have : X ≠ Y := fun h => hne (by rw [h])
    exact (hOK z).disj X Y this p hp hs
  · exact g_cross hOK hReg (X := ⟨z, X⟩) (Y := ⟨z', Y⟩) hz ((hOK z).m_W X) ((hOK z').m_W Y) hp hs

theorem g_early : ∀ X Y : Pos κ, Y ≠ X → gr Z Y X → ∀ w ∈ gW Z X, ∀ p ∈ Ω,
    p ∈ gSpot Z Y → P.Sees p (gm Z Y) → ¬ P.Sees p w := by
  rintro ⟨z, X⟩ ⟨z', Y⟩ hne ⟨hz, hr⟩ w hw p hpΩ hp hs
  simp only at hz
  subst hz
  have : Y ≠ X := fun h => hne (by rw [h])
  exact (hOK z').early X Y this hr w hw p hpΩ hp hs

theorem g_late : ∀ X Y : Pos κ, Y ≠ X → ¬ gr Z Y X → ∀ w ∈ gW Z X, ∀ p ∈ Ω,
    P.Sees p (gm Z Y) → ¬ P.Sees p w := by
  rintro ⟨z, X⟩ ⟨z', Y⟩ hne hr w hw p hp hs
  by_cases hz : z' = z
  · subst hz
    have : Y ≠ X := fun h => hne (by rw [h])
    exact (hOK z').late X Y this (fun h => hr ⟨rfl, h⟩) w hw p hp hs
  · exact g_cross hOK hReg (X := ⟨z', Y⟩) (Y := ⟨z, X⟩) hz ((hOK z').m_W Y) hw hp hs

/-- **Lower bound (ii), allowed set `Ω`.** Every set of guards in `Ω` seeing the region has at
least as many guards as there are positions. -/
theorem card_le_of_zones_on (G : Finset Point) (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q) :
    Fintype.card (Pos κ) ≤ G.card :=
  card_le_of_witnesses_on hGΩ hcov (gm Z) (g_m_mem hOK hReg) (g_disj hOK hReg)

/-- **Pinning (iii), allowed set `Ω`.** A set of guards in `Ω` seeing the region, with exactly as
many guards as positions, is in bijection with the positions; the guard of `X` lies on `X` and is
the only guard on `X`. -/
theorem pinned_of_zones_on (G : Finset Point) (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (hcard : G.card = Fintype.card (Pos κ)) :
    ∃ e : Pos κ ≃ G, ∀ X, ((e X : Point) ∈ gSpot Z X ∧ ∀ q ∈ G, q ∈ gSpot Z X → q = e X) := by
  classical
  obtain ⟨h1, -⟩ := guards_pinned_on hGΩ hcov (gm Z) (g_m_mem hOK hReg) (g_disj hOK hReg) hcard
    (gW Z) (fun X => (hOK X.1).W_filled X.2) (gSpot Z) (fun X => (hOK X.1).spot X.2) (gr Z)
    (gr_wf Z) (g_early hOK hReg) (g_late hOK hReg)
  choose f hfG hfs hfS hfu using h1
  let f' : Pos κ → G := fun X => ⟨f X, hfG X⟩
  have hinj : Function.Injective f' := by
    intro X Y hXY
    by_contra hne
    have e : f X = f Y := congrArg Subtype.val hXY
    exact g_disj hOK hReg X Y hne (f X) (hGΩ (hfG X)) (hfs X) (e ▸ hfs Y)
  have hbij : Function.Bijective f' := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_coe, hcard]
  refine ⟨Equiv.ofBijective f' hbij, fun X => ⟨hfS X, fun q hq hqS => ?_⟩⟩
  obtain ⟨Y, hY⟩ := (Equiv.ofBijective f' hbij).surjective ⟨q, hq⟩
  have hqY : q = f Y := (congrArg Subtype.val hY).symm
  have hYS : q ∈ gSpot Z Y := hqY ▸ hfS Y
  by_cases hXY : X = Y
  · rw [hXY]; exact hqY
  obtain ⟨z, X⟩ := X
  obtain ⟨z', Y⟩ := Y
  by_cases hz : z = z'
  · subst hz
    have hne : X ≠ Y := fun h => hXY (by rw [h])
    exact absurd hYS (Set.disjoint_left.1 ((hOK z).spot_disj X Y hne) hqS)
  · exact absurd ((hOK z').spot_reg Y hYS)
      (Set.disjoint_left.1 (hReg z z' hz) ((hOK z).spot_reg X hqS))

end On

/-- **Lower bound (ii).** Every guard set has at least as many guards as there are positions. -/
theorem card_le_of_zones (hOK : ∀ z, (Z z).OK P (Reg z))
    (hReg : ∀ z z', z ≠ z' → Disjoint (Reg z) (Reg z')) (G : Finset Point)
    (hG : P.IsGuardSet (G : Set Point)) :
    Fintype.card (Pos κ) ≤ G.card :=
  card_le_of_zones_on (fun z => (hOK z).toOKOn) hReg G hG.1 hG.2

/-- **Pinning (iii).** A guard set with exactly as many guards as positions is in bijection with
the positions; the guard of `X` lies on `X` and is the only guard on `X`. -/
theorem pinned_of_zones (hOK : ∀ z, (Z z).OK P (Reg z))
    (hReg : ∀ z z', z ≠ z' → Disjoint (Reg z) (Reg z')) (G : Finset Point)
    (hG : P.IsGuardSet (G : Set Point)) (hcard : G.card = Fintype.card (Pos κ)) :
    ∃ e : Pos κ ≃ G, ∀ X, ((e X : Point) ∈ gSpot Z X ∧ ∀ q ∈ G, q ∈ gSpot Z X → q = e X) :=
  pinned_of_zones_on (fun z => (hOK z).toOKOn) hReg G hG.1 hG.2 hcard

end Zones

/-! ### Transport of a position system along a bijection preserving visibility -/

section Transport

variable {P P' : Polygon} {κ : Type*}

/-- The image of a position system under a map `f` (positions and witnesses are mapped). -/
def PosSys.map (f : Point → Point) (Z : PosSys κ) : PosSys κ :=
  ⟨fun X => f (Z.m X), fun X => f '' Z.W X, fun X => f '' Z.Spot X, Z.rank⟩

/-- **Transport.** If `f` is a bijection with `P'.Sees (f p) (f q) ↔ P.Sees p q` and
`P'.filled = f '' P.filled`, a position system of `P` with region `Reg` gives one of `P'` with
region `f '' Reg`. -/
theorem PosSys.OK.map {Z : PosSys κ} {Reg : Set Point} (h : Z.OK P Reg) (f : Point ≃ Point)
    (hs : ∀ p q, P'.Sees (f p) (f q) ↔ P.Sees p q) (hf : P'.filled = f '' P.filled) :
    (Z.map f).OK P' (f '' Reg) := by
  have hs' : ∀ p q, P'.Sees p q ↔ P.Sees (f.symm p) (f.symm q) := by
    intro p q
    rw [← hs, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨fun X => ⟨_, h.m_W X, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro X _ ⟨w, hw, rfl⟩
    rw [hf]; exact ⟨w, h.W_filled X hw, rfl⟩
  · rintro X _ ⟨w, hw, rfl⟩ p hp
    rw [hs', Equiv.symm_apply_apply] at hp
    exact ⟨f.symm p, h.reg X w hw _ hp, by simp⟩
  · intro X p hp hall
    have hp' : f.symm p ∈ P.filled := by
      rw [hf] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simpa using hq
    refine ⟨f.symm p, h.spot X _ hp' fun w hw => ?_, by simp⟩
    have := hall (f w) ⟨w, hw, rfl⟩
    rwa [hs', Equiv.symm_apply_apply] at this
  · rintro X _ ⟨p, hp, rfl⟩
    exact ⟨p, h.spot_reg X hp, rfl⟩
  · intro X Y hne
    exact Set.disjoint_image_of_injective f.injective (h.spot_disj X Y hne)
  · intro X Y hne p h1 h2
    rw [PosSys.map, hs', Equiv.symm_apply_apply] at h1 h2
    exact h.disj X Y hne _ h1 h2
  · rintro X Y hne hr _ ⟨w, hw, rfl⟩ _ ⟨p, hp, rfl⟩ h1 h2
    rw [PosSys.map, hs] at h1
    rw [hs] at h2
    exact h.early X Y hne hr w hw p hp h1 h2
  · rintro X Y hne hr _ ⟨w, hw, rfl⟩ p h1 h2
    rw [PosSys.map, hs', Equiv.symm_apply_apply] at h1
    rw [hs', Equiv.symm_apply_apply] at h2
    exact h.late X Y hne hr w hw _ h1 h2

/-- **Transport, allowed set `Ω`.** If `f` is a bijection with
`P'.Sees (f p) (f q) ↔ P.Sees p q` and `P'.filled = f '' P.filled`, a position system of `P` for
the allowed set `Ω` with region `Reg` gives one of `P'` for the allowed set `f '' Ω` with region
`f '' Reg`. -/
theorem PosSys.OKOn.map {Ω Reg : Set Point} {Z : PosSys κ} (h : Z.OKOn P Ω Reg) (f : Point ≃ Point)
    (hs : ∀ p q, P'.Sees (f p) (f q) ↔ P.Sees p q) (hf : P'.filled = f '' P.filled) :
    (Z.map f).OKOn P' (f '' Ω) (f '' Reg) := by
  refine ⟨fun X => ⟨_, h.m_W X, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro X _ ⟨w, hw, rfl⟩
    rw [hf]; exact ⟨w, h.W_filled X hw, rfl⟩
  · rintro X _ ⟨w, hw, rfl⟩ _ ⟨p, hp, rfl⟩ h1
    rw [hs] at h1
    exact ⟨p, h.reg X w hw p hp h1, rfl⟩
  · rintro X _ ⟨p, hp, rfl⟩ hall
    refine ⟨p, h.spot X p hp fun w hw => ?_, rfl⟩
    exact (hs p w).1 (hall (f w) ⟨w, hw, rfl⟩)
  · rintro X _ ⟨p, hp, rfl⟩
    exact ⟨p, h.spot_reg X hp, rfl⟩
  · intro X Y hne
    exact Set.disjoint_image_of_injective f.injective (h.spot_disj X Y hne)
  · rintro X Y hne _ ⟨p, hp, rfl⟩ h1 h2
    rw [PosSys.map, hs] at h1 h2
    exact h.disj X Y hne p hp h1 h2
  · rintro X Y hne hr _ ⟨w, hw, rfl⟩ _ ⟨p, hpΩ, rfl⟩ ⟨p', hp', e⟩ h1 h2
    rw [f.injective e] at hp'
    rw [PosSys.map, hs] at h1
    rw [hs] at h2
    exact h.early X Y hne hr w hw p hpΩ hp' h1 h2
  · rintro X Y hne hr _ ⟨w, hw, rfl⟩ _ ⟨p, hp, rfl⟩ h1 h2
    rw [PosSys.map, hs] at h1
    rw [hs] at h2
    exact h.late X Y hne hr w hw p hp h1 h2

end Transport

end ArtGallery.Sec5.Count

end
