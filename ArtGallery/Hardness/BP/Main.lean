module

public import ArtGallery.Hardness.BP.Assemble
public import ArtGallery.Hardness.BP.CountGlobal
public import ArtGallery.Hardness.BP.ConstraintGlobal
public import ArtGallery.Hardness.BP.CoverMain
public import ArtGallery.Hardness.Sec5.Main
public import ArtGallery.Stade.Main
public import ArtGallery.Stade.PTimeREV

/-!
# ETR reduces in polynomial time to `AGPBoundaryPoint`

Assembly of the boundary-point construction.  For an ETR-INV instance `Φ` on the variables `< n`
we use the polygon `polyCBP Φ N` with `N = max n 1`, so that the global construction (`N ≥ 1`)
is available (for `n = 0` the instance `Φ` is empty, and the polygon is the one of the empty
instance on one variable):

* `polyCBP Φ N` is simple (`constructBP_simple`);
* a solution gives a guard set on the boundary with `numGuardsBP Φ N` guards (`canonGuardsBP`);
* a guard set on the boundary with `numGuardsBP Φ N` guards encodes a solution
  (`guardSet_solutionBP`).

Hence `Φ` is solvable iff `polyCBP Φ N` has a guard set on the boundary of cardinality
`numGuardsBP Φ N` (`sat_iff_hasGuardSetOnBoundaryOfCard`).  A formula `φ` goes to the ETR-INV
instance `etrToINV φ` on the variables `< etrToINVVars φ` (a positive number), then to the code
of this polygon (each coordinate as the fraction of its normal form, `FracPoint.ofRat`) and
number of guards; a word that is not the code of a formula goes to the code of the empty polygon
(not simple).

Main results: **`etr_polyRed_agpBoundaryPoint'`** and, in namespace `ArtGallery`,
**`etr_polyRed_agpBoundaryPoint`** and **`agpBoundaryPoint_erComplete`**.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.BP

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

/-! ### Correctness of the polygon -/

/-- A solution of the instance restricted to the variables `< n` (all others set to `1`). -/
theorem sat_of_restrictedBP {n : ℕ} {Φ : List ETRINV.Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    {v : ℕ → ℝ} (hv : ∀ i < n, 1 / 2 ≤ v i ∧ v i ≤ 2) (hs : ∀ c ∈ Φ, c.Holds v) :
    ETRINV.Satisfiable Φ := by
  refine ⟨fun i => if i < n then v i else 1, fun i => ?_, fun c hc => ?_⟩
  · by_cases hi : i < n
    · simp only [hi, ↓reduceIte]; exact hv i hi
    · simp only [hi]; norm_num
  · exact Sec5.holds_congr (hΦ c hc) (fun i hi => by simp [hi]) (hs c hc)

/-- **Solvable iff guardable from the boundary** (for `n ≥ 1` variables). -/
theorem sat_iff_hasGuardSetOnBoundaryOfCard_of_pos (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    ETRINV.Satisfiable Φ ↔ (polyCBP Φ n).HasGuardSetOnBoundaryOfCard (numGuardsBP Φ n) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    exact ⟨canonGuardsBP Φ n v, canonGuardsBP_card hΦ (fun i _ => hv i) hs,
      canonGuardsBP_guard hΦ hn (fun i _ => hv i) hs⟩
  · rintro ⟨G, hG, hGΩ, hcov⟩
    obtain ⟨x, hx, hs, -⟩ := Constraint.guardSet_solutionBP hΦ hn G hGΩ hcov hG
    exact sat_of_restrictedBP hΦ hx hs

/-- **Solvable iff guardable from the boundary**: an ETR-INV instance `Φ` on the variables `< n`
is solvable iff the polygon `polyCBP Φ (max n 1)` has a guard set on the boundary of cardinality
`numGuardsBP Φ (max n 1)`. -/
theorem sat_iff_hasGuardSetOnBoundaryOfCard (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ETRINV.Satisfiable Φ ↔
      (polyCBP Φ (max n 1)).HasGuardSetOnBoundaryOfCard (numGuardsBP Φ (max n 1)) :=
  sat_iff_hasGuardSetOnBoundaryOfCard_of_pos Φ (max n 1)
    (fun c hc => Sec5.varsLt_mono (le_max_left _ _) (hΦ c hc))
    (lt_of_lt_of_le one_pos (le_max_right _ _))

/-- The polygon `polyCBP Φ (max n 1)` is simple. -/
theorem polyCBP_simple (Φ : List ETRINV.Constraint) (n : ℕ) (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    (polyCBP Φ (max n 1)).Simple :=
  (constructBP_simple fun c hc => Sec5.varsLt_mono (le_max_left _ _) (hΦ c hc)).1

/-! ### Codes -/

theorem AGPBoundaryPoint_encode_iff (L : List (ℚ × ℚ)) (g : ℕ) :
    AGPBoundaryPoint (encodeAGP (L.map FracPoint.ofRat) g) ↔ (Polygon.mk (L.map ratPoint)).Simple ∧
      (Polygon.mk (L.map ratPoint)).HasGuardSetOnBoundaryOfCard g := by
  constructor
  · rintro ⟨V', g', h, -, hS, hG⟩
    obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
    rw [map_toPoint_ofRat] at hS hG
    exact ⟨hS, hG⟩
  · rintro ⟨hS, hG⟩
    refine ⟨L.map FracPoint.ofRat, g, rfl, fun p hp => ?_, ?_, ?_⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨q.1.den_pos, q.2.den_pos⟩
    · rw [map_toPoint_ofRat]; exact hS
    · rw [map_toPoint_ofRat]; exact hG

theorem not_AGPBoundaryPoint_empty : ¬ AGPBoundaryPoint (encodeAGP [] 0) := by
  rintro ⟨V, g, h, -, hS, -⟩
  obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
  have := hS.1
  simp [Polygon.n] at this

/-! ### The reduction -/

/-- The boundary-point instance of a formula. -/
def agpBoundaryPointOfFormula (φ : ETR.Formula) : Word :=
  encodeAGP ((constructBP (etrToINV φ) (etrToINVVars φ)).map FracPoint.ofRat)
    (numGuardsBP (etrToINV φ) (etrToINVVars φ))

/-- **The reduction from ETR to AGPBoundaryPoint** on raw words. -/
def etrToAGPBoundaryPoint (w : Word) : Word :=
  match ETR.decodeFormula w with
  | some φ => agpBoundaryPointOfFormula φ
  | none => encodeAGP [] 0

/-- The ETR-INV instance of a formula has at least one variable. -/
theorem etrToINVVars_pos (φ : ETR.Formula) : 0 < etrToINVVars φ := by
  unfold etrToINVVars; omega

theorem agpBoundaryPointOfFormula_correct (φ : ETR.Formula) :
    φ.Satisfiable ↔ AGPBoundaryPoint (agpBoundaryPointOfFormula φ) := by
  rw [agpBoundaryPointOfFormula, AGPBoundaryPoint_encode_iff, etrToINV_iff,
    sat_iff_hasGuardSetOnBoundaryOfCard_of_pos _ _ (etrToINV_vars φ) (etrToINVVars_pos φ)]
  exact ⟨fun h => ⟨(constructBP_simple (etrToINV_vars φ)).1, h⟩, fun h => h.2⟩

theorem etrToAGPBoundaryPoint_correct (w : Word) :
    ArtGallery.ETR w ↔ AGPBoundaryPoint (etrToAGPBoundaryPoint w) := by
  unfold etrToAGPBoundaryPoint
  cases h : ETR.decodeFormula w with
  | none =>
    exact ⟨fun h' => absurd h' (not_ETR_of_decode_none h),
      fun h' => absurd h' not_AGPBoundaryPoint_empty⟩
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, agpBoundaryPointOfFormula_correct]

/-! ### Polynomial time -/

protected theorem PT.agpBoundaryPointOfFormula : PT agpBoundaryPointOfFormula :=
  PT.comp₂ (h := fun Φ n => encodeAGP ((constructBP Φ n).map FracPoint.ofRat) (numGuardsBP Φ n))
    PTime.PT.constructInstanceBP (PT.etrToINV PT.id) (PT.etrToINVVars PT.id)

protected theorem PT.etrToAGPBoundaryPoint : PT etrToAGPBoundaryPoint := by
  refine PT.of_optionCases (o := ETR.decodeFormula) (d := fun _ => encodeAGP [] 0)
    (f := fun _ φ => agpBoundaryPointOfFormula φ) (PT.decodeFormula PT.id) (PT.const _)
    (PT.agpBoundaryPointOfFormula.comp PT.snd') ?_ ?_
  · intro w h; simp [etrToAGPBoundaryPoint, h]
  · intro w φ h; simp [etrToAGPBoundaryPoint, h]

/-! ### Main theorem -/

/-- **ETR reduces in polynomial time to the boundary-point art gallery problem.** -/
theorem etr_polyRed_agpBoundaryPoint' : PolyRed ETR AGPBoundaryPoint :=
  PT.polyRed PT.etrToAGPBoundaryPoint etrToAGPBoundaryPoint_correct

end ArtGallery.BP

end
