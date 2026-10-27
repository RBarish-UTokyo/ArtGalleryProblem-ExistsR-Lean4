module

public import ArtGallery.Stade.PTimeScale
public import ArtGallery.Stade.API
public import ArtGallery.PTime.AGPinER

/-!
# ETR reduces in polynomial time to `AGPInt` and to `AGPPointBoundary` (Stade's construction)

A formula `φ` goes to the ETR-INV-REV instance `Φ = etrToREV φ` on the variables
`< n = etrToREVVars φ` (`etrToREV_iff`, `etrToREV_vars`), then to Stade's polygon `poly n Φ` with
`guards n Φ` guards.  By the three facts of `ArtGallery/Stade/API.lean` (and
`IsGuardSet → IsBoundaryGuardSet`), `Φ` is solvable iff the polygon has a guard set of
cardinality `guards n Φ`, iff it has a boundary guard set of that cardinality
(`sat_iff_hasGuardSetOfCard`, `sat_iff_hasBoundaryGuardSetOfCard`).

* `etrToAGPInt`: the integer polygon `polyInt n Φ` (scaled by the common denominator,
  `ArtGallery/Stade/PTimeScale.lean`), written with `encodeAGPInt`;
* `etrToAGPPointBoundary`: the rational polygon, each coordinate as the fraction of its normal form
  (`FracPoint.ofRat`), written with `encodeAGP`;
* a word that is not the code of a formula goes to the code of the empty polygon (not simple).

Main results: **`etr_polyRed_agpInt'`** and **`etr_polyRed_agpPointBoundary'`**.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Stade

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV

/-! ### Correctness of the polygon -/

theorem holds_congr {n : ℕ} {c : Constraint} (hc : c.VarsLt n) {v w : ℕ → ℝ}
    (h : ∀ i < n, v i = w i) : c.Holds v ↔ c.Holds w := by
  cases c with
  | one x => simp only [Constraint.Holds, h x hc]
  | invGe x y => simp only [Constraint.Holds, h x hc.1, h y hc.2]
  | invRevLe x y => simp only [Constraint.Holds, h x hc.1, h y hc.2]
  | addLe x y z => simp only [Constraint.Holds, h x hc.1, h y hc.2.1, h z hc.2.2]
  | addGe x y z => simp only [Constraint.Holds, h x hc.1, h y hc.2.1, h z hc.2.2]

/-- A solution of the instance restricted to the variables `< n` (all others set to `1`). -/
theorem sat_of_restricted {n : ℕ} {Φ : List Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt n) {v : ℕ → ℝ}
    (hv : ∀ i < n, 1 / 2 ≤ v i ∧ v i ≤ 2) (hs : ∀ c ∈ Φ, c.Holds v) : Satisfiable Φ := by
  refine ⟨fun i => if i < n then v i else 1, fun i => ?_, fun c hc => ?_⟩
  · by_cases hi : i < n
    · simp only [hi, ↓reduceIte]; exact hv i hi
    · simp only [hi]; norm_num
  · exact (holds_congr (hΦ c hc) (fun i hi => by simp [hi])).1 (hs c hc)

/-- **Solvable iff guardable** (point-point). -/
theorem sat_iff_hasGuardSetOfCard (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) :
    Satisfiable Φ ↔ (Polygon.mk ((poly n Φ).map ratPoint)).HasGuardSetOfCard (guards n Φ) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    obtain ⟨G, hG, hGS, -⟩ := guardSet_of_sat n Φ hΦ hn hv hs
    exact ⟨G, hG, hGS⟩
  · rintro ⟨G, hG, hGS⟩
    obtain ⟨v, hv, hs, -⟩ := sat_of_boundaryGuard n Φ hΦ G (isBoundaryGuardSet_of_isGuardSet hGS) hG
    exact sat_of_restricted hΦ hv hs

/-- **Solvable iff the boundary is guardable** (point-boundary). -/
theorem sat_iff_hasBoundaryGuardSetOfCard (n : ℕ) (Φ : List Constraint)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    Satisfiable Φ ↔
      (Polygon.mk ((poly n Φ).map ratPoint)).HasBoundaryGuardSetOfCard (guards n Φ) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    obtain ⟨G, hG, hGS, -⟩ := guardSet_of_sat n Φ hΦ hn hv hs
    exact ⟨G, hG, isBoundaryGuardSet_of_isGuardSet hGS⟩
  · rintro ⟨G, hG, hGS⟩
    obtain ⟨v, hv, hs, -⟩ := sat_of_boundaryGuard n Φ hΦ G hGS hG
    exact sat_of_restricted hΦ hv hs

/-! ### Codes -/

theorem intPointDigits_injective : Function.Injective intPointDigits := by
  intro p q h
  have h1 := congrArg (fun D => intOfDigits D.1) h
  have h2 := congrArg (fun D => intOfDigits D.2) h
  simp only [intPointDigits, intOfDigits_intDigits] at h1 h2
  exact Prod.ext h1 h2

theorem encodeAGPInt_inj {V V' : List (ℤ × ℤ)} {g g' : ℕ}
    (h : encodeAGPInt V g = encodeAGPInt V' g') : V = V' ∧ g = g' := by
  have h1 := decodeAGPInt_encodeAGPInt V g
  rw [h, decodeAGPInt_encodeAGPInt] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨h1, h2⟩ := h1
  refine ⟨(List.map_injective_iff.2 intPointDigits_injective h1).symm, ?_⟩
  have := congrArg SAT.binaryValue h2
  simpa [binaryValue_bits] using this.symm

theorem AGPInt_encode_iff (V : List (ℤ × ℤ)) (g : ℕ) :
    AGPInt (encodeAGPInt V g) ↔ (Polygon.mk (V.map intPoint)).Simple ∧
      (Polygon.mk (V.map intPoint)).HasGuardSetOfCard g := by
  constructor
  · rintro ⟨V', g', h, hS, hG⟩
    obtain ⟨rfl, rfl⟩ := encodeAGPInt_inj h
    exact ⟨hS, hG⟩
  · rintro ⟨hS, hG⟩
    exact ⟨V, g, rfl, hS, hG⟩

/-- The fraction vertex with the normal forms of the coordinates. -/
def FracPoint.ofRat (p : ℚ × ℚ) : FracPoint := ⟨p.1.num, p.1.den, p.2.num, p.2.den⟩

theorem FracPoint.toPoint_ofRat (p : ℚ × ℚ) : (FracPoint.ofRat p).toPoint = ratPoint p := by
  simp only [FracPoint.toPoint, FracPoint.ofRat, ratPoint, Rat.cast_def]

theorem map_toPoint_ofRat (L : List (ℚ × ℚ)) :
    (L.map FracPoint.ofRat).map FracPoint.toPoint = L.map ratPoint := by
  rw [List.map_map]
  exact List.map_congr_left fun p _ => FracPoint.toPoint_ofRat p

theorem AGPPointBoundary_encode_iff (L : List (ℚ × ℚ)) (g : ℕ) :
    AGPPointBoundary (encodeAGP (L.map FracPoint.ofRat) g) ↔ (Polygon.mk (L.map ratPoint)).Simple ∧
      (Polygon.mk (L.map ratPoint)).HasBoundaryGuardSetOfCard g := by
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

theorem not_AGPInt_empty : ¬ AGPInt (encodeAGPInt [] 0) := by
  rw [AGPInt_encode_iff]
  rintro ⟨hS, -⟩
  have := hS.1
  simp [Polygon.n] at this

theorem not_AGPPointBoundary_empty : ¬ AGPPointBoundary (encodeAGP [] 0) := by
  rintro ⟨V, g, h, -, hS, -⟩
  obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
  have := hS.1
  simp [Polygon.n] at this

/-! ### The reductions -/

/-- The integer instance of a formula. -/
def agpIntOfFormula (φ : ETR.Formula) : Word :=
  encodeAGPInt (polyInt (etrToREVVars φ) (etrToREV φ)) (guards (etrToREVVars φ) (etrToREV φ))

/-- The point-boundary instance of a formula. -/
def agpPointBoundaryOfFormula (φ : ETR.Formula) : Word :=
  encodeAGP ((poly (etrToREVVars φ) (etrToREV φ)).map FracPoint.ofRat)
    (guards (etrToREVVars φ) (etrToREV φ))

/-- **The reduction from ETR to AGPInt** on raw words. -/
def etrToAGPInt (w : Word) : Word :=
  match ETR.decodeFormula w with
  | some φ => agpIntOfFormula φ
  | none => encodeAGPInt [] 0

/-- **The reduction from ETR to AGPPointBoundary** on raw words. -/
def etrToAGPPointBoundary (w : Word) : Word :=
  match ETR.decodeFormula w with
  | some φ => agpPointBoundaryOfFormula φ
  | none => encodeAGP [] 0

/-- The reduction produces at least one variable. -/
theorem etrToREVVars_pos (φ : ETR.Formula) : 0 < etrToREVVars φ := by
  have := etrHalfIndex_lt φ
  unfold etrToREVVars; omega

theorem agpIntOfFormula_correct (φ : ETR.Formula) :
    φ.Satisfiable ↔ AGPInt (agpIntOfFormula φ) := by
  rw [agpIntOfFormula, AGPInt_encode_iff, etrToREV_iff,
    sat_iff_hasGuardSetOfCard _ _ (etrToREV_vars φ) (etrToREVVars_pos φ), hasGuardSetOfCard_polyInt_iff]
  exact ⟨fun h => ⟨simple_polyInt _ _, h⟩, fun h => h.2⟩

theorem agpPointBoundaryOfFormula_correct (φ : ETR.Formula) :
    φ.Satisfiable ↔ AGPPointBoundary (agpPointBoundaryOfFormula φ) := by
  rw [agpPointBoundaryOfFormula, AGPPointBoundary_encode_iff, etrToREV_iff,
    sat_iff_hasBoundaryGuardSetOfCard _ _ (etrToREV_vars φ) (etrToREVVars_pos φ)]
  exact ⟨fun h => ⟨simple _ _, h⟩, fun h => h.2⟩

theorem not_ETR_of_decode_none {w : Word} (h : ETR.decodeFormula w = none) : ¬ ArtGallery.ETR w := by
  rintro ⟨φ, rfl, -⟩
  rw [ETR.decodeFormula_encode] at h
  exact absurd h (by simp)

theorem etrToAGPInt_correct (w : Word) : ArtGallery.ETR w ↔ AGPInt (etrToAGPInt w) := by
  unfold etrToAGPInt
  cases h : ETR.decodeFormula w with
  | none => exact ⟨fun h' => absurd h' (not_ETR_of_decode_none h), fun h' => absurd h' not_AGPInt_empty⟩
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, agpIntOfFormula_correct]

theorem etrToAGPPointBoundary_correct (w : Word) :
    ArtGallery.ETR w ↔ AGPPointBoundary (etrToAGPPointBoundary w) := by
  unfold etrToAGPPointBoundary
  cases h : ETR.decodeFormula w with
  | none =>
    exact ⟨fun h' => absurd h' (not_ETR_of_decode_none h), fun h' => absurd h' not_AGPPointBoundary_empty⟩
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, agpPointBoundaryOfFormula_correct]

/-! ### Polynomial time -/

protected theorem PT.agpIntOfFormula : PT agpIntOfFormula := by
  unfold agpIntOfFormula encodeAGPInt
  fun_prop

theorem agpPointBoundaryOfFormula_eq (φ : ETR.Formula) : agpPointBoundaryOfFormula φ =
    encodeList (fun p : ℚ × ℚ => binaryInt p.1.num ++ binaryNat p.1.den ++ binaryInt p.2.num ++
      binaryNat p.2.den) (poly (etrToREVVars φ) (etrToREV φ)) ++
      binaryNat (guards (etrToREVVars φ) (etrToREV φ)) := by
  unfold agpPointBoundaryOfFormula encodeAGP
  rw [encodeList_map]
  rfl

protected theorem PT.agpPointBoundaryOfFormula : PT agpPointBoundaryOfFormula := by
  refine PT.of_eq ?_ fun φ => (agpPointBoundaryOfFormula_eq φ).symm
  fun_prop

protected theorem PT.etrToAGPInt : PT etrToAGPInt := by
  refine PT.of_optionCases (o := ETR.decodeFormula) (d := fun _ => encodeAGPInt [] 0)
    (f := fun _ φ => agpIntOfFormula φ) (PT.decodeFormula PT.id) (PT.const _)
    (PT.agpIntOfFormula.comp PT.snd') ?_ ?_
  · intro w h; simp [etrToAGPInt, h]
  · intro w φ h; simp [etrToAGPInt, h]

protected theorem PT.etrToAGPPointBoundary : PT etrToAGPPointBoundary := by
  refine PT.of_optionCases (o := ETR.decodeFormula) (d := fun _ => encodeAGP [] 0)
    (f := fun _ φ => agpPointBoundaryOfFormula φ) (PT.decodeFormula PT.id) (PT.const _)
    (PT.agpPointBoundaryOfFormula.comp PT.snd') ?_ ?_
  · intro w h; simp [etrToAGPPointBoundary, h]
  · intro w φ h; simp [etrToAGPPointBoundary, h]

/-! ### Main theorems -/

/-- **ETR reduces in polynomial time to the art gallery problem with integer coordinates.** -/
theorem etr_polyRed_agpInt' : PolyRed ETR AGPInt :=
  PT.polyRed PT.etrToAGPInt etrToAGPInt_correct

/-- **ETR reduces in polynomial time to the point-boundary art gallery problem.** -/
theorem etr_polyRed_agpPointBoundary' : PolyRed ETR AGPPointBoundary :=
  PT.polyRed PT.etrToAGPPointBoundary etrToAGPPointBoundary_correct

end ArtGallery.Stade

end
