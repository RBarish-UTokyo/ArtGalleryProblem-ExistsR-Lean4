module

public import ArtGallery.Hardness.BP.CountSide
public import ArtGallery.Hardness.BP.MainAreaCount
public import ArtGallery.Hardness.Sec5.CountGlobal

/-!
# Boundary-point variant, counting: facts (ii) and (iii) for the global polygon

The positions of the global polygon `polyCBP Φ n` (`n ≥ 1`) for guards restricted to the
boundary, grouped in the zones of Section 5 (`Sec5.Count.Zone Φ n`: the main area, the right
and the left units).  Positions of a zone (`ZPosBP`):

* main area: `Fin (4n)`, position `σ` = the floor segment of the bay of slot `σ` (`baySpot`;
  `gPosSpotBP_main_eq`: the base segment `s_σ`, or the point of value `1` if slot `σ` carries
  `one` spikes);
* a right unit `i`: `Fin np ⊕ Fin r` — the corridor stationary guards `p_k` and the template
  positions of the boundary-point template (`tsysOfBP`), placed by `φ = tmplMapBP`;
* a left unit `i`: the same in the working frame, mirrored by `x ↦ 54n − 12 − x`.

`card_posBP`: there are `numGuardsBP Φ n` positions.  `gPosSpotBP_disjoint`: distinct positions
are disjoint; `gPosSpotBP_subset_boundary`: every position lies on `∂P`.

* **(ii)** `count_lowerBP`: every set of guards on the boundary seeing the polygon has at least
  `numGuardsBP Φ n` guards (also for `n = 0`).
* **(iii)** `count_pinnedBP`: such a set with exactly `numGuardsBP Φ n` guards is in bijection
  with the positions, the guard of a position lies on it and is the only guard on it.

The proof is the two-stage counting argument of `Sec5/CountAbstract.lean` with the allowed set
`Ω = ∂P`: within a zone the conditions are `MainHypBP.okOn`, `UnitHypBP.okOn`; the zones are
separated by their regions (`gRegBP_disjoint`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.Count

open ArtGallery Set Polygon Sec5.Tmpl
open ArtGallery.Sec5
open ArtGallery.Sec5.Count (Zone Pos gSpot PosSys unitSys unitBox mainReg baseSeg mirrorEquiv
  mirrorEquiv_apply mirrorEquiv_mirrorEquiv mirrorEquiv_eq card_le_of_zones_on pinned_of_zones_on
  guardCount_eq)
open ArtGallery.Sec5.Corridor (Input CorridorAt)

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-! ### Zones and positions -/

/-- The positions of unit `i` of the list `us`: corridor stationary guards and template
positions. -/
abbrev UPosBP (n k : ℕ) (us : List UnitSpec) (i : Fin us.length) : Type :=
  Fin (unitInputBP n k i us[i]).np ⊕ Fin (tsysOfBP us[i].kind).r

/-- The positions of a zone. -/
def ZPosBP (Φ : List ETRINV.Constraint) (n : ℕ) : Zone Φ n → Type
  | .inl _ => Fin (4 * n)
  | .inr (.inl i) => UPosBP n (numC Φ) (unitSpecs n Φ).1 i
  | .inr (.inr i) => UPosBP n (numC Φ) (unitSpecs n Φ).2 i

instance instFintypeZPosBP (z : Zone Φ n) : Fintype (ZPosBP Φ n z) := by
  rcases z with _ | i | i <;> unfold ZPosBP <;> infer_instance

/-- **All positions of the global polygon** (boundary-point variant). -/
abbrev GPosBP (Φ : List ETRINV.Constraint) (n : ℕ) : Type := Pos (ZPosBP Φ n)

theorem unitS_geBP (n k m : ℕ) (u : UnitSpec) : (1000 : ℝ) ≤ ((unitInputBP n k m u).S : ℝ) := by
  have := S_ge (n := n) (k := k)
  have : (800000 : ℝ) ≤ (S n k : ℝ) := by exact_mod_cast this
  simp only [unitInputBP]; push_cast; linarith

/-- The placement of the template of a unit. -/
noncomputable def uφBP (n k m : ℕ) (u : UnitSpec) : Point ≃ᵃ[ℝ] Point :=
  tmplMapBP u.kind (unitInputBP n k m u).S (unitInputBP n k m u).H (S_ne_of (unitS_geBP n k m u))

/-- The positions of a unit (working frame). -/
noncomputable def uSysBP (n k m : ℕ) (u : UnitSpec) :
    PosSys (Fin (unitInputBP n k m u).np ⊕ Fin (tsysOfBP u.kind).r) :=
  unitSys (unitInputBP n k m u) (tmplVBP u.kind) (tsysOfBP u.kind) (uφBP n k m u)

/-- The position systems of the zones (left units mirrored into the global frame). -/
noncomputable def gZBP (Φ : List ETRINV.Constraint) (n : ℕ) :
    (z : Zone Φ n) → PosSys (ZPosBP Φ n z)
  | .inl _ => mainSysBP n (slotOne n Φ)
  | .inr (.inl i) => uSysBP n (numC Φ) i (unitSpecs n Φ).1[i]
  | .inr (.inr i) => (uSysBP n (numC Φ) i (unitSpecs n Φ).2[i]).map (mirrorEquiv n)

/-- The regions of the zones. -/
def gRegBP (Φ : List ETRINV.Constraint) (n : ℕ) : Zone Φ n → Set Point
  | .inl _ => mainReg n (numC Φ)
  | .inr (.inl i) => unitBox ((unitInputBP n (numC Φ) i (unitSpecs n Φ).1[i]).S : ℝ)
      ((unitInputBP n (numC Φ) i (unitSpecs n Φ).1[i]).H : ℝ)
  | .inr (.inr i) => mirrorEquiv n '' unitBox
      ((unitInputBP n (numC Φ) i (unitSpecs n Φ).2[i]).S : ℝ)
      ((unitInputBP n (numC Φ) i (unitSpecs n Φ).2[i]).H : ℝ)

theorem unitInputBP_S (n k m : ℕ) (u : UnitSpec) :
    ((unitInputBP n k m u).S : ℝ) = (S n k : ℝ) := by
  simp [unitInputBP]

theorem unitInputBP_H (n k m : ℕ) (u : UnitSpec) :
    ((unitInputBP n k m u).H : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
  simp [unitInputBP, unitH]

/-- **The position of `X`** (a bay floor segment or value-`1` point, a corridor stationary guard,
a template position, or the mirror image of one). -/
noncomputable def gPosSpotBP (X : GPosBP Φ n) : Set Point := gSpot (gZBP Φ n) X

/-! ### The number of positions -/

theorem tmplTBP_length (k : Kind) : (tmplTBP k).length = (tmplT k).length := by
  cases k <;> rfl

theorem card_UPosBP {k : ℕ} {us : List UnitSpec} (hok : ∀ u ∈ us, UnitOK n u)
    (i : Fin us.length) : Fintype.card (UPosBP n k us i) = us[i].kind.nguards := by
  have h : us[i].work.length = (tmplT us[i].kind).length := (hok _ (List.getElem_mem i.2)).len
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have e : (unitInputBP n k i us[i]).np = us[i].work.length := rfl
  rw [e, h, tsysOfBP_r, tmplTBP_length]
  generalize us[i].kind = kd
  cases kd <;> decide

theorem sum_card_UPosBP {k : ℕ} {us : List UnitSpec} (hok : ∀ u ∈ us, UnitOK n u) :
    ∑ i : Fin us.length, Fintype.card (UPosBP n k us i) = unitGuards us := by
  simp only [card_UPosBP hok, unitGuards]
  exact Fin.sum_univ_fun_getElem us (fun u => u.kind.nguards)

/-- **There are `numGuardsBP Φ n` positions.** -/
theorem card_posBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    Fintype.card (GPosBP Φ n) = numGuardsBP Φ n := by
  have hok := unitSpecs_ok hΦ
  simp only [numGuardsBP, numGuards, Nat.pos_iff_ne_zero.1 hn, ite_false]
  rw [guardCount_eq, Fintype.card_sigma]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have e1 : Fintype.card (ZPosBP Φ n (.inl default)) = 4 * n := by
    simp [ZPosBP]
  have e2 := sum_card_UPosBP (k := numC Φ) (fun u hu => hok u (List.mem_append_left _ hu))
  have e3 := sum_card_UPosBP (k := numC Φ) (fun u hu => hok u (List.mem_append_right _ hu))
  rw [e1]
  simp only [ZPosBP]
  rw [e2, e3]
  ring

/-! ### The mirror -/

theorem sees_polyCBP_mirror (p q : Point) :
    (polyCBP Φ n).Sees (mirrorEquiv n p) (mirrorEquiv n q) ↔ (polyMBP Φ n).Sees p q := by
  have := Vis.Cert.sees_mirrorPoly_iff (54 * (n : ℝ) - 12) (polyCBP Φ n) (mirrorEquiv n p)
    (mirrorEquiv n q)
  rw [← mirrorEquiv_eq, ← mirrorEquiv_eq, mirrorEquiv_mirrorEquiv, mirrorEquiv_mirrorEquiv] at this
  exact this.symm

theorem mirror_comp_reflX :
    (fun x => mirrorEquiv n (Vis.Cert.reflX (54 * (n : ℝ) - 12) x)) = id := by
  funext x; rw [← mirrorEquiv_eq, mirrorEquiv_mirrorEquiv]; rfl

theorem filled_polyCBP_mirror : (polyCBP Φ n).filled = mirrorEquiv n '' (polyMBP Φ n).filled := by
  rw [polyMBP, Vis.Cert.filled_mirrorPoly, Set.image_image, mirror_comp_reflX, Set.image_id]

theorem boundary_polyCBP_mirror :
    (polyCBP Φ n).boundary = mirrorEquiv n '' (polyMBP Φ n).boundary := by
  rw [polyMBP, Vis.Cert.mirrorPoly, Vis.Cert.boundary_revPoly,
    Hardening.Invariance.boundary_mapPoly, Set.image_image]
  rw [show (fun x => mirrorEquiv n ((Vis.Cert.reflX (54 * (n : ℝ) - 12)) x)) = id from
    mirror_comp_reflX, Set.image_id]

/-! ### The zones satisfy the counting conditions -/

/-- **Every zone satisfies the counting conditions for guards on the boundary.** -/
theorem gZBP_okOn (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    ∀ z, (gZBP Φ n z).OKOn (polyCBP Φ n) (polyCBP Φ n).boundary (gRegBP Φ n z) := by
  rintro (_ | i | i)
  · exact (mainHypBP hΦ hn).okOn
  · exact (side_unitHypBP (rightSideBP hΦ hn) i.2).okOn
  · have h := (side_unitHypBP (leftSideBP hΦ hn) i.2).okOn
    have h' := h.map (mirrorEquiv n) (fun p q => sees_polyCBP_mirror p q) filled_polyCBP_mirror
    rw [← boundary_polyCBP_mirror] at h'
    exact h'

/-! ### The regions of the zones are disjoint -/

theorem S_bigBP : 54 * (n : ℝ) + 100000 ≤ (S n (numC Φ) : ℝ) := by
  have := slots_lt_S (n := n) (k := numC Φ)
  have : ((54 * (n : ℚ) + 100000 : ℚ) : ℝ) ≤ ((S n (numC Φ) : ℚ) : ℝ) := by exact_mod_cast this
  push_cast at this; exact this

theorem gRegBP_disjoint : ∀ z z' : Zone Φ n, z ≠ z' → Disjoint (gRegBP Φ n z) (gRegBP Φ n z') := by
  have hS := S_bigBP (n := n) (Φ := Φ)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rintro (_ | i | i) (_ | j | j) hne <;> rw [Set.disjoint_left] <;>
    simp only [gRegBP, unitInputBP_S, unitInputBP_H]
  · exact absurd rfl hne
  · rintro p ⟨-, h1⟩ ⟨h2, -⟩; linarith
  · rintro p ⟨h1, -⟩ ⟨q, ⟨h2, -⟩, rfl⟩
    rw [mirrorEquiv_apply] at h1; simp only at h1; linarith
  · rintro p ⟨h2, -⟩ ⟨-, h1⟩; linarith
  · rintro p ⟨-, -, a3, a4⟩ ⟨-, -, b3, b4⟩
    have hij : (i : ℕ) ≠ j := fun e => hne (by rw [Fin.ext e])
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      linarith
  · rintro p ⟨h1, -⟩ ⟨q, ⟨h2, -⟩, rfl⟩
    rw [mirrorEquiv_apply] at h1; simp only at h1; linarith
  · rintro p ⟨q, ⟨h2, -⟩, rfl⟩ ⟨h1, -⟩
    rw [mirrorEquiv_apply] at h1; simp only at h1; linarith
  · rintro p ⟨q, ⟨h2, -⟩, rfl⟩ ⟨h1, -⟩
    rw [mirrorEquiv_apply] at h1; simp only at h1; linarith
  · rintro p ⟨q, ⟨-, -, a3, a4⟩, rfl⟩ ⟨q', ⟨-, -, b3, b4⟩, e⟩
    have e2 : q'.2 = q.2 := by
      have := congrArg Prod.snd e
      rwa [mirrorEquiv_apply, mirrorEquiv_apply] at this
    have hij : (i : ℕ) ≠ j := fun e => hne (by rw [Fin.ext e])
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      linarith

/-! ### The positions explicitly -/

/-- A base position: the floor segment of the bay of slot `σ` (or its value-`1` point). -/
theorem gPosSpotBP_main (σ : Fin (4 * n)) :
    gPosSpotBP (⟨.inl (), σ⟩ : GPosBP Φ n) = baySpot (slotOne n Φ σ) (slotFrame σ) := rfl

/-- A base position explicitly: the base segment `s_σ = [a_σ, a_σ + (3/2, 0)]`, or the point
`a_σ + (1/2, 0)` of value `1` if slot `σ` carries `one` spikes. -/
theorem gPosSpotBP_main_eq (σ : Fin (4 * n)) :
    gPosSpotBP (⟨.inl (), σ⟩ : GPosBP Φ n) =
      if slotOne n Φ σ = true then {((slotX σ : ℝ) + 1 / 2, 0)} else baseSeg σ := by
  rw [gPosSpotBP_main]
  by_cases h : slotOne n Φ σ = true
  · simp only [h, baySpot, ↓reduceIte, Frame.pt, Frame.abs, slotFrame, g1Rel, ratPoint]
    norm_num
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    ext p
    simp only [baySpot, Bool.false_eq_true, ↓reduceIte, Frame.rel, slotFrame, div_one, sub_zero,
      mem_ofPred_eq, baseSeg]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩

/-- A corridor stationary guard of a right unit. -/
theorem gPosSpotBP_right_sg (i : Fin (unitSpecs n Φ).1.length)
    (k : Fin (unitInputBP n (numC Φ) i (unitSpecs n Φ).1[i]).np) :
    gPosSpotBP (⟨.inr (.inl i), (.inl k : UPosBP n (numC Φ) (unitSpecs n Φ).1 i)⟩ : GPosBP Φ n) =
      {ratPoint ((unitInputBP n (numC Φ) i (unitSpecs n Φ).1[i]).sgPt k)} := rfl

/-- A template position of a right unit (a placed guard segment or stationary point). -/
theorem gPosSpotBP_right_tmpl (i : Fin (unitSpecs n Φ).1.length)
    (X : Fin (tsysOfBP (unitSpecs n Φ).1[i].kind).r) :
    gPosSpotBP (⟨.inr (.inl i), (.inr X : UPosBP n (numC Φ) (unitSpecs n Φ).1 i)⟩ : GPosBP Φ n) =
      uφBP n (numC Φ) i (unitSpecs n Φ).1[i] ''
        convexHull ℝ (Vis.Cert.intSet ((tsysOfBP (unitSpecs n Φ).1[i].kind).spot X)) := rfl

/-- A corridor stationary guard of a left unit (mirror image of the working frame). -/
theorem gPosSpotBP_left_sg (i : Fin (unitSpecs n Φ).2.length)
    (k : Fin (unitInputBP n (numC Φ) i (unitSpecs n Φ).2[i]).np) :
    gPosSpotBP (⟨.inr (.inr i), (.inl k : UPosBP n (numC Φ) (unitSpecs n Φ).2 i)⟩ : GPosBP Φ n) =
      mirrorEquiv n '' {ratPoint ((unitInputBP n (numC Φ) i (unitSpecs n Φ).2[i]).sgPt k)} := rfl

/-- A template position of a left unit (mirror image of the working frame). -/
theorem gPosSpotBP_left_tmpl (i : Fin (unitSpecs n Φ).2.length)
    (X : Fin (tsysOfBP (unitSpecs n Φ).2[i].kind).r) :
    gPosSpotBP (⟨.inr (.inr i), (.inr X : UPosBP n (numC Φ) (unitSpecs n Φ).2 i)⟩ : GPosBP Φ n) =
      mirrorEquiv n '' (uφBP n (numC Φ) i (unitSpecs n Φ).2[i] ''
        convexHull ℝ (Vis.Cert.intSet ((tsysOfBP (unitSpecs n Φ).2[i].kind).spot X))) := rfl

/-! ### Disjointness and boundary -/

/-- **Distinct positions are disjoint.** -/
theorem gPosSpotBP_disjoint (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {X Y : GPosBP Φ n}
    (h : X ≠ Y) : Disjoint (gPosSpotBP X) (gPosSpotBP Y) := by
  have hOK := gZBP_okOn hΦ hn
  obtain ⟨z, X⟩ := X
  obtain ⟨z', Y⟩ := Y
  by_cases hz : z = z'
  · subst hz
    have hne : X ≠ Y := fun e => h (by rw [e])
    exact (hOK z).spot_disj X Y hne
  · exact Set.disjoint_of_subset ((hOK z).spot_reg X) ((hOK z').spot_reg Y)
      (gRegBP_disjoint z z' hz)

/-- **Every position lies on the boundary.** -/
theorem gPosSpotBP_subset_boundary (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (X : GPosBP Φ n) :
    gPosSpotBP X ⊆ (polyCBP Φ n).boundary := by
  obtain ⟨z, X⟩ := X
  rcases z with _ | i | i
  · intro p hp
    exact baySpot_mem_boundary ((mainHypBP hΦ hn).bayAt X.2) (mainHypBP hΦ hn).simple hp
  · exact (side_unitHypBP (rightSideBP hΦ hn) i.2).spot_bd X
  · rintro _ ⟨p, hp, rfl⟩
    rw [boundary_polyCBP_mirror]
    exact ⟨p, (side_unitHypBP (leftSideBP hΦ hn) i.2).spot_bd X hp, rfl⟩

/-! ### Facts (ii) and (iii) -/

/-- **(ii) Lower bound, guards on the boundary.** Every set of guards on the boundary of the
polygon of the boundary-point reduction that sees the whole polygon has at least
`numGuardsBP Φ n` guards. -/
theorem count_lowerBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (G : Finset Point)
    (hGΩ : (G : Set Point) ⊆ (polyCBP Φ n).boundary)
    (hcov : ∀ q ∈ (polyCBP Φ n).filled, ∃ g ∈ (G : Set Point), (polyCBP Φ n).Sees g q) :
    numGuardsBP Φ n ≤ G.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the triangle: a guard set is nonempty
    simp only [numGuardsBP, numGuards, ↓reduceIte]
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    rintro rfl
    have hv : (polyCBP Φ 0).vtx 0 ∈ (polyCBP Φ 0).filled := by
      refine Or.inl ⟨0, ?_, Geometry.left_mem_segment _ _⟩
      simp [polyCBP, constructBP_zero, triangle0, Polygon.n]
    obtain ⟨g, hg, -⟩ := hcov _ hv
    simp at hg
  · rw [← card_posBP hΦ hn]
    exact card_le_of_zones_on (gZBP_okOn hΦ hn) gRegBP_disjoint G hGΩ hcov

/-- **(iii) Pinning, guards on the boundary.** A set of guards on the boundary seeing the polygon
with exactly `numGuardsBP Φ n` guards is in bijection with the positions: the guard `e X` of the
position `X` lies on `X` (`gPosSpotBP X`) and it is the only guard on `X`. -/
theorem count_pinnedBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (G : Finset Point)
    (hGΩ : (G : Set Point) ⊆ (polyCBP Φ n).boundary)
    (hcov : ∀ q ∈ (polyCBP Φ n).filled, ∃ g ∈ (G : Set Point), (polyCBP Φ n).Sees g q)
    (hcard : G.card = numGuardsBP Φ n) :
    ∃ e : GPosBP Φ n ≃ G, ∀ X, (e X : Point) ∈ gPosSpotBP X ∧
      ∀ q ∈ G, q ∈ gPosSpotBP X → q = e X := by
  rw [← card_posBP hΦ hn] at hcard
  exact pinned_of_zones_on (gZBP_okOn hΦ hn) gRegBP_disjoint G hGΩ hcov hcard

end ArtGallery.BP.Count

end
