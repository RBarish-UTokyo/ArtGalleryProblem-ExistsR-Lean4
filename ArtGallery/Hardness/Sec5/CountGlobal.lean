module

public import ArtGallery.Hardness.Sec5.CountSide
public import ArtGallery.Hardness.Sec5.CountMain

/-!
# Section 5, counting: facts (ii) and (iii) for the global polygon

The positions of the global polygon `polyC Φ n = Polygon.mk ((construct Φ n).map ratPoint)`
(`n ≥ 1`) are grouped in zones (`Zone Φ n`): the main area (the `4n` base segments) and the
right and left units.  Positions of a zone (`ZPos`):

* main area: `Fin (4n)`, position `σ` = the base segment `s_σ` (`baseSeg σ`), or the point
  `g1Pt σ` if slot `σ` carries `one` spikes;
* a right unit `i`: `Fin np ⊕ Fin r` — the corridor stationary guards `p_k` (the points
  `ratPoint (sgPt k)`) and the template positions (receivers / guard segments and gadget
  stationary guards, the images `φ '' conv(spot)` under the placement `φ = tmplMap`);
* a left unit `i`: the same in the working frame, mirrored by `x ↦ 54n − 12 − x`.

`card_pos`: there are `numGuards Φ n` positions.

* **(ii)** `count_lower`: every guard set has at least `numGuards Φ n` guards (also for `n = 0`).
* **(iii)** `count_pinned`: a guard set with exactly `numGuards Φ n` guards is in bijection with
  the positions, the guard of a position lies on it and is the only guard on it.

The proof is the two-stage counting argument (`CountAbstract`): within a zone the conditions are
`MainHyp.ok`, `UnitHyp.ok`; the zones are separated by their regions (`gReg_disjoint`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Count

open ArtGallery Set Polygon Tmpl
open Corridor (Input CorridorAt)

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-! ### Zones and positions -/

/-- The zones: the main area, the right units, the left units. -/
abbrev Zone (Φ : List ETRINV.Constraint) (n : ℕ) : Type :=
  Unit ⊕ (Fin (unitSpecs n Φ).1.length ⊕ Fin (unitSpecs n Φ).2.length)

/-- The positions of unit `i` of the list `us`: corridor stationary guards and template
positions. -/
abbrev UPos (n k : ℕ) (us : List UnitSpec) (i : Fin us.length) : Type :=
  Fin (unitInput n k i us[i]).np ⊕ Fin (tsysOf us[i].kind).r

/-- The positions of a zone. -/
def ZPos (Φ : List ETRINV.Constraint) (n : ℕ) : Zone Φ n → Type
  | .inl _ => Fin (4 * n)
  | .inr (.inl i) => UPos n (numC Φ) (unitSpecs n Φ).1 i
  | .inr (.inr i) => UPos n (numC Φ) (unitSpecs n Φ).2 i

instance instFintypeZPos (z : Zone Φ n) : Fintype (ZPos Φ n z) := by
  rcases z with _ | i | i <;> unfold ZPos <;> infer_instance

/-- All positions of the global polygon. -/
abbrev GPos (Φ : List ETRINV.Constraint) (n : ℕ) : Type := Pos (ZPos Φ n)

theorem unitS_ge (n k m : ℕ) (u : UnitSpec) : (1000 : ℝ) ≤ ((unitInput n k m u).S : ℝ) := by
  have := S_ge (n := n) (k := k)
  have : (800000 : ℝ) ≤ (S n k : ℝ) := by exact_mod_cast this
  simp only [unitInput]; push_cast; linarith

/-- The placement of the template of a unit. -/
noncomputable def uφ (n k m : ℕ) (u : UnitSpec) : Point ≃ᵃ[ℝ] Point :=
  tmplMap u.kind (unitInput n k m u).S (unitInput n k m u).H (S_ne_of (unitS_ge n k m u))

/-- The positions of a unit (working frame). -/
noncomputable def uSys (n k m : ℕ) (u : UnitSpec) :
    PosSys (Fin (unitInput n k m u).np ⊕ Fin (tsysOf u.kind).r) :=
  unitSys (unitInput n k m u) (tmplV u.kind) (tsysOf u.kind) (uφ n k m u)

/-- The mirror `x ↦ 54n − 12 − x` as a bijection. -/
noncomputable def mirrorEquiv (n : ℕ) : Point ≃ Point := (mirrorR n).toEquiv

theorem mirrorEquiv_apply (p : Point) : mirrorEquiv n p = (54 * (n : ℝ) - 12 - p.1, p.2) := by
  simp [mirrorEquiv, mirrorR]

/-- The position systems of the zones (left units mirrored into the global frame). -/
noncomputable def gZ (Φ : List ETRINV.Constraint) (n : ℕ) : (z : Zone Φ n) → PosSys (ZPos Φ n z)
  | .inl _ => mainSys n (slotOne n Φ)
  | .inr (.inl i) => uSys n (numC Φ) i (unitSpecs n Φ).1[i]
  | .inr (.inr i) => (uSys n (numC Φ) i (unitSpecs n Φ).2[i]).map (mirrorEquiv n)

/-- The regions of the zones. -/
def gReg (Φ : List ETRINV.Constraint) (n : ℕ) : Zone Φ n → Set Point
  | .inl _ => mainReg n (numC Φ)
  | .inr (.inl i) => unitBox ((unitInput n (numC Φ) i (unitSpecs n Φ).1[i]).S : ℝ)
      ((unitInput n (numC Φ) i (unitSpecs n Φ).1[i]).H : ℝ)
  | .inr (.inr i) => mirrorEquiv n '' unitBox ((unitInput n (numC Φ) i (unitSpecs n Φ).2[i]).S : ℝ)
      ((unitInput n (numC Φ) i (unitSpecs n Φ).2[i]).H : ℝ)

theorem unitInput_S (n k m : ℕ) (u : UnitSpec) : ((unitInput n k m u).S : ℝ) = (S n k : ℝ) := by
  simp [unitInput]

theorem unitInput_H (n k m : ℕ) (u : UnitSpec) :
    ((unitInput n k m u).H : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
  simp [unitInput, unitH]

/-- **The position of `X`** (a base segment, a corridor stationary guard, a template position, or
the mirror image of one). -/
noncomputable def gPosSpot (X : GPos Φ n) : Set Point := gSpot (gZ Φ n) X

/-! ### The number of positions -/

theorem unitGuards_append (a b : List UnitSpec) :
    unitGuards (a ++ b) = unitGuards a + unitGuards b := by
  simp [unitGuards]

theorem sum_flatMap_const (L : List ℕ) (l : List ℕ) :
    (L.flatMap fun _ => l).sum = L.length * l.sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]; ring

theorem unitGuards_orientR : unitGuards (orientR n) = 21 * n := by
  simp only [unitGuards, orientR, List.map_flatMap, List.map_map]
  simp [Function.comp_def, Kind.nguards, sum_flatMap_const]
  ring

theorem unitGuards_orientL : unitGuards (orientL n) = 21 * n := by
  simp only [unitGuards, orientL, List.map_flatMap, List.map_map]
  simp [Function.comp_def, Kind.nguards, sum_flatMap_const]
  ring

theorem unitGuards_addR : ∀ Φ : List ETRINV.Constraint,
    unitGuards (Φ.flatMap (addR n)) = 8 * kAdd Φ
  | [] => rfl
  | c :: Φ => by
    have ih := unitGuards_addR Φ
    simp only [List.flatMap_cons, unitGuards_append, ih, kAdd, List.countP_cons]
    cases c <;> simp [addR, unitGuards, Kind.nguards, isAdd] <;> ring

theorem unitGuards_addL : ∀ Φ : List ETRINV.Constraint,
    unitGuards (Φ.flatMap (addL n)) = 8 * kAdd Φ
  | [] => rfl
  | c :: Φ => by
    have ih := unitGuards_addL Φ
    simp only [List.flatMap_cons, unitGuards_append, ih, kAdd, List.countP_cons]
    cases c <;> simp [addL, unitGuards, Kind.nguards, isAdd] <;> ring

theorem unitGuards_invR : ∀ Φ : List ETRINV.Constraint,
    unitGuards (Φ.flatMap (invR n)) = 5 * kInv Φ
  | [] => rfl
  | c :: Φ => by
    have ih := unitGuards_invR Φ
    simp only [List.flatMap_cons, unitGuards_append, ih, kInv, List.countP_cons]
    cases c <;> simp [invR, unitGuards, Kind.nguards, isInv] <;> ring

theorem guardCount_eq :
    guardCount n Φ = 4 * n + unitGuards (unitSpecs n Φ).1 + unitGuards (unitSpecs n Φ).2 := by
  simp only [unitSpecs, unitGuards_append, unitGuards_orientR, unitGuards_orientL,
    unitGuards_addR, unitGuards_addL, unitGuards_invR, guardCount]
  ring

theorem card_UPos {k : ℕ} {us : List UnitSpec} (hok : ∀ u ∈ us, UnitOK n u) (i : Fin us.length) :
    Fintype.card (UPos n k us i) = us[i].kind.nguards := by
  have h : us[i].work.length = (tmplT us[i].kind).length := (hok _ (List.getElem_mem i.2)).len
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have e : (unitInput n k i us[i]).np = us[i].work.length := rfl
  rw [e, h, tsysOf_r]
  generalize us[i].kind = kd
  cases kd <;> decide

theorem sum_card_UPos {k : ℕ} {us : List UnitSpec} (hok : ∀ u ∈ us, UnitOK n u) :
    ∑ i : Fin us.length, Fintype.card (UPos n k us i) = unitGuards us := by
  simp only [card_UPos hok, unitGuards]
  exact Fin.sum_univ_fun_getElem us (fun u => u.kind.nguards)

/-- **There are `numGuards Φ n` positions.** -/
theorem card_pos (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    Fintype.card (GPos Φ n) = numGuards Φ n := by
  have hok := unitSpecs_ok hΦ
  simp only [numGuards, Nat.pos_iff_ne_zero.1 hn, ite_false]
  rw [guardCount_eq, Fintype.card_sigma]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have e1 : Fintype.card (ZPos Φ n (.inl default)) = 4 * n := by
    simp [ZPos]
  have e2 := sum_card_UPos (k := numC Φ) (fun u hu => hok u (List.mem_append_left _ hu))
  have e3 := sum_card_UPos (k := numC Φ) (fun u hu => hok u (List.mem_append_right _ hu))
  rw [e1]
  simp only [ZPos]
  rw [e2, e3]
  ring

/-! ### The zones satisfy the counting conditions -/

theorem polyC_bottom (hn : 0 < n) : polyC Φ n = Polygon.mk ((bottomWall n Φ ++
    ([wR n, vR n (numC Φ)] ++ rightPart n Φ ++ [tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++
      [vL n (numC Φ)])).map ratPoint) := by
  rw [polyC, construct_pos (by omega)]
  simp [constructPos, List.append_assoc]

/-- The main-area hypotheses for the global polygon. -/
theorem mainHyp (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    MainHyp (polyC Φ n) n (numC Φ) (slotOne n Φ) (pocketStart n Φ) := by
  obtain ⟨h1, h2, -, -, h5⟩ := construct_global hΦ hn
  refine ⟨h1, h2, fun σ hσ => ?_, fun p hp => ?_, fun σ hσ => ?_⟩
  · rw [polyC_bottom hn]
    exact pocketAt_of_bottomWall (by simp) hσ
  · refine Stade.filled_snd_le (polyC Φ n) (fun j hj => h5 _ ?_) p hp
    exact ⟨j, hj, Geometry.left_mem_segment _ _⟩
  · simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq] at hσ
    exact hσ.1

theorem mirrorEquiv_mirrorEquiv (p : Point) : mirrorEquiv n (mirrorEquiv n p) = p := by
  rw [mirrorEquiv_apply, mirrorEquiv_apply]; ext <;> simp

theorem mirrorEquiv_eq (p : Point) : mirrorEquiv n p = Vis.Cert.reflX (54 * (n : ℝ) - 12) p := rfl

theorem sees_polyC_mirror (p q : Point) :
    (polyC Φ n).Sees (mirrorEquiv n p) (mirrorEquiv n q) ↔ (polyM Φ n).Sees p q := by
  have := Vis.Cert.sees_mirrorPoly_iff (54 * (n : ℝ) - 12) (polyC Φ n) (mirrorEquiv n p)
    (mirrorEquiv n q)
  rw [← mirrorEquiv_eq, ← mirrorEquiv_eq, mirrorEquiv_mirrorEquiv, mirrorEquiv_mirrorEquiv] at this
  exact this.symm

theorem filled_polyC_mirror : (polyC Φ n).filled = mirrorEquiv n '' (polyM Φ n).filled := by
  rw [polyM, Vis.Cert.filled_mirrorPoly, Set.image_image]
  have : (fun x => mirrorEquiv n (Vis.Cert.reflX (54 * (n : ℝ) - 12) x)) = id := by
    funext x; rw [← mirrorEquiv_eq, mirrorEquiv_mirrorEquiv]; rfl
  rw [this, Set.image_id]

/-- **Every zone satisfies the counting conditions.** -/
theorem gZ_ok (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    ∀ z, (gZ Φ n z).OK (polyC Φ n) (gReg Φ n z) := by
  rintro (_ | i | i)
  · exact (mainHyp hΦ hn).ok
  · have hQ := rightSide hΦ hn
    exact (side_unitHyp hQ i.2).ok
  · have hQ := leftSide hΦ hn
    have h := (side_unitHyp hQ i.2).ok
    exact h.map (mirrorEquiv n) (fun p q => sees_polyC_mirror p q) filled_polyC_mirror

/-! ### The regions of the zones are disjoint -/

theorem S_big : 54 * (n : ℝ) + 100000 ≤ (S n (numC Φ) : ℝ) := by
  have := slots_lt_S (n := n) (k := numC Φ)
  have : ((54 * (n : ℚ) + 100000 : ℚ) : ℝ) ≤ ((S n (numC Φ) : ℚ) : ℝ) := by exact_mod_cast this
  push_cast at this; exact this

theorem gReg_disjoint : ∀ z z' : Zone Φ n, z ≠ z' → Disjoint (gReg Φ n z) (gReg Φ n z') := by
  have hS := S_big (n := n) (Φ := Φ)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rintro (_ | i | i) (_ | j | j) hne <;> rw [Set.disjoint_left] <;>
    simp only [gReg, unitInput_S, unitInput_H]
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

/-- A base position: the base segment `s_σ`, or the value-`1` point with `one` spikes. -/
theorem gPosSpot_main (σ : Fin (4 * n)) :
    gPosSpot (⟨.inl (), σ⟩ : GPos Φ n) =
      if slotOne n Φ σ = true then {g1Pt σ} else baseSeg σ := rfl

/-- A corridor stationary guard of a right unit. -/
theorem gPosSpot_right_sg (i : Fin (unitSpecs n Φ).1.length)
    (k : Fin (unitInput n (numC Φ) i (unitSpecs n Φ).1[i]).np) :
    gPosSpot (⟨.inr (.inl i), (.inl k : UPos n (numC Φ) (unitSpecs n Φ).1 i)⟩ : GPos Φ n) =
      {ratPoint ((unitInput n (numC Φ) i (unitSpecs n Φ).1[i]).sgPt k)} := rfl

/-- A template position of a right unit (a placed guard segment or stationary point). -/
theorem gPosSpot_right_tmpl (i : Fin (unitSpecs n Φ).1.length)
    (X : Fin (tsysOf (unitSpecs n Φ).1[i].kind).r) :
    gPosSpot (⟨.inr (.inl i), (.inr X : UPos n (numC Φ) (unitSpecs n Φ).1 i)⟩ : GPos Φ n) =
      uφ n (numC Φ) i (unitSpecs n Φ).1[i] ''
        convexHull ℝ (Vis.Cert.intSet ((tsysOf (unitSpecs n Φ).1[i].kind).spot X)) := rfl

/-- A corridor stationary guard of a left unit (mirror image of the working frame). -/
theorem gPosSpot_left_sg (i : Fin (unitSpecs n Φ).2.length)
    (k : Fin (unitInput n (numC Φ) i (unitSpecs n Φ).2[i]).np) :
    gPosSpot (⟨.inr (.inr i), (.inl k : UPos n (numC Φ) (unitSpecs n Φ).2 i)⟩ : GPos Φ n) =
      mirrorEquiv n '' {ratPoint ((unitInput n (numC Φ) i (unitSpecs n Φ).2[i]).sgPt k)} := rfl

/-- A template position of a left unit (mirror image of the working frame). -/
theorem gPosSpot_left_tmpl (i : Fin (unitSpecs n Φ).2.length)
    (X : Fin (tsysOf (unitSpecs n Φ).2[i].kind).r) :
    gPosSpot (⟨.inr (.inr i), (.inr X : UPos n (numC Φ) (unitSpecs n Φ).2 i)⟩ : GPos Φ n) =
      mirrorEquiv n '' (uφ n (numC Φ) i (unitSpecs n Φ).2[i] ''
        convexHull ℝ (Vis.Cert.intSet ((tsysOf (unitSpecs n Φ).2[i].kind).spot X))) := rfl

/-! ### Facts (ii) and (iii) -/

/-- **(ii) Lower bound.** Every guard set of the polygon of the reduction has at least
`numGuards Φ n` guards. -/
theorem count_lower (hΦ : ∀ c ∈ Φ, c.VarsLt n) (G : Finset Point)
    (hG : (polyC Φ n).IsGuardSet (G : Set Point)) : numGuards Φ n ≤ G.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the triangle: a guard set is nonempty
    simp only [numGuards, ↓reduceIte]
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    rintro rfl
    have hv : (polyC Φ 0).vtx 0 ∈ (polyC Φ 0).filled := by
      refine Or.inl ⟨0, ?_, Geometry.left_mem_segment _ _⟩
      simp [polyC, construct_zero, triangle0, Polygon.n]
    obtain ⟨g, hg, -⟩ := hG.2 _ hv
    simp at hg
  · rw [← card_pos hΦ hn]
    exact card_le_of_zones (gZ_ok hΦ hn) gReg_disjoint G hG

/-- **(iii) Pinning.** A guard set with exactly `numGuards Φ n` guards is in bijection with the
positions: the guard `e X` of the position `X` lies on `X` (`gPosSpot X`: the base segment,
the stationary point, or the template guard segment / stationary point), and it is the only
guard on `X`. -/
theorem count_pinned (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (G : Finset Point)
    (hG : (polyC Φ n).IsGuardSet (G : Set Point)) (hcard : G.card = numGuards Φ n) :
    ∃ e : GPos Φ n ≃ G, ∀ X, (e X : Point) ∈ gPosSpot X ∧
      ∀ q ∈ G, q ∈ gPosSpot X → q = e X := by
  rw [← card_pos hΦ hn] at hcard
  exact pinned_of_zones (gZ_ok hΦ hn) gReg_disjoint G hG hcard

end ArtGallery.Sec5.Count

end
