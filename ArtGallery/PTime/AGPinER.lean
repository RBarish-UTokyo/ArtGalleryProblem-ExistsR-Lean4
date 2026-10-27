module

public import ArtGallery.PTime.AGPFormulaPT
public import ArtGallery.PTime.AGPDecode

/-!
# The art gallery problem is in `∃ℝ` (paper, Theorem 13)

The mathematical reduction `Membership.agpToETR` (with `Membership.agpToETR_correct`) decodes the
number of guards `g` as a natural number, i.e. (for the `PT` framework) in unary, which is
exponential in its binary length.  Here we compute the same formula from the *digits* of the
instance (`ArtGallery.decodeAGP`):

* the vertex data enters only through the Horner terms of the digit lists (`coordFD`), and
  the validity test through the non-emptiness of the denominators' digit lists (`validBD`);
* the formula depends on `g` only through the test `n ≤ g + 2` and, when `g + 2 < n`, through `g`
  itself; hence `g` may be replaced by the clamped value `min g (n + 3)` (`agpFormula_eq`), which
  is computed from the binary digits in polynomial time (`PT.binaryValue_min`).

Main results:

* `agpToETRD_eq : agpToETRD w = Membership.agpToETR w`, `PT.agpReduction`;
* **`ArtGallery.agp_inER : InER AGP`**;
* the reduction `agpIntReduction : AGPInt ≤ AGP` (integer vertices become fractions with
  denominators `1`; a non-code goes to the code of the empty polygon), `PT.agpIntReduction`,
  `agpIntReduction_correct`;
* **`ArtGallery.agpInt_inER : InER AGPInt`**.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETR ArtGallery.Membership

/-! ### The formula, computed from the digits of the instance -/

/-- The term of the integer with sign `p.1` and absolute-value digits `p.2`. -/
def intTermD (p : Bool × Word) : Term := if p.1 then .sub .zero (bitsTerm p.2) else bitsTerm p.2

theorem intTerm_eq_intTermD (z : ℤ) : intTerm z = intTermD (intDigits z) := by
  unfold intTerm intTermD intDigits natTerm
  by_cases h : z < 0 <;> simp [h]

/-- The coordinate equations of the vertex with digits `D`, number `k`. -/
def coordAtD (D : FracDigits) (k : ℕ) : Formula :=
  .and (.eq (.mul (bitsTerm D.2.1) (.var (2 * k))) (intTermD D.1))
    (.eq (.mul (bitsTerm D.2.2.2) (.var (2 * k + 1))) (intTermD D.2.2.1))

/-- The coordinate equations of the vertices with digits `D`, starting with number `k`. -/
def coordFD (D : List FracDigits) (k : ℕ) : Formula :=
  bigAnd ((D.zipIdx k).map fun q => coordAtD q.1 q.2)

theorem coordF_eq_coordFD (V : List FracPoint) (k : ℕ) :
    coordF V k = coordFD (V.map FracPoint.digits) k := by
  induction V generalizing k with
  | nil => rfl
  | cons p V ih =>
    rw [coordF, ih (k + 1)]
    simp only [coordFD, List.map_cons, List.zipIdx_cons, bigAnd, List.foldr_cons, coordAtD,
      FracPoint.digits, natTerm, intTerm_eq_intTermD]

/-- All denominators are positive, tested on their digit lists. -/
def validBD (D : List FracDigits) : Bool := D.all fun d => !d.2.1.isEmpty && !d.2.2.2.isEmpty

theorem bits_isEmpty_iff (n : ℕ) : n.bits.isEmpty = true ↔ n = 0 := by
  constructor
  · intro h
    rw [← binaryValue_bits n, List.isEmpty_iff.1 h]
    rfl
  · rintro rfl
    simp [Nat.zero_bits]

theorem validB_eq_validBD (V : List FracPoint) : validB V = validBD (V.map FracPoint.digits) := by
  simp only [validB, validBD, List.all_map]
  congr 1
  funext p
  simp only [Function.comp_apply, FracPoint.digits]
  have h1 := bits_isEmpty_iff p.xDen
  have h2 := bits_isEmpty_iff p.yDen
  cases hx : p.xDen.bits.isEmpty <;> cases hy : p.yDen.bits.isEmpty <;>
    simp_all [Nat.pos_iff_ne_zero]

/-- The formula of an instance given by the digits `D` of its vertices and a number of guards
`g` (in unary). -/
def agpFormulaD (D : List FracDigits) (g : ℕ) : Formula :=
  if validBD D then
    if D.length ≤ g + 2 then .and (coordFD D 0) (simpleF D.length (2 * D.length))
    else .and (coordFD D 0) (.and (simpleF D.length (2 * D.length))
      (guardsF D.length g (2 * D.length + simpleSize D.length)))
  else fFalse

/-- The formula of an instance only depends on the clamped number of guards `min g (n + 3)`. -/
theorem agpFormula_eq (V : List FracPoint) (g : ℕ) :
    agpFormula V g = agpFormulaD (V.map FracPoint.digits) (min g (V.length + 3)) := by
  unfold agpFormula agpFormulaD
  rw [← validB_eq_validBD, List.length_map, ← coordF_eq_coordFD]
  split_ifs <;> first | rfl | omega | rw [show min g (V.length + 3) = g by omega]

/-- **The reduction from AGP to ETR, computed from the digits of the instance.** -/
def agpToETRD (w : Word) : Formula :=
  match ArtGallery.decodeAGP w with
  | none => fFalse
  | some (D, gd) => agpFormulaD D (min (SAT.binaryValue gd) (D.length + 3))

/-- The digit version computes the formula of the mathematical reduction. -/
theorem agpToETRD_eq (w : Word) : agpToETRD w = Membership.agpToETR w := by
  unfold agpToETRD Membership.agpToETR
  cases h : ArtGallery.decodeAGP w with
  | none =>
    cases h' : Membership.decodeAGP w with
    | none => rfl
    | some r =>
      obtain ⟨V, g⟩ := r
      have hw := Membership.encodeAGP_of_decodeAGP h'
      rw [← hw, ArtGallery.decodeAGP_encodeAGP] at h
      exact absurd h (by simp)
  | some r =>
    obtain ⟨D, gd⟩ := r
    obtain ⟨V, g, rfl, rfl, rfl⟩ := ArtGallery.decodeAGP_sound h
    rw [Membership.decodeAGP_encodeAGP]
    simp only [agpFormula_eq, binaryValue_bits, List.length_map]

/-- **The reduction from AGP to ETR** on raw words. -/
def agpReduction (w : Word) : Word := (agpToETRD w).encode

theorem agpReduction_correct (w : Word) : AGP w ↔ ArtGallery.ETR (agpReduction w) := by
  rw [agpReduction, ETR_encode_iff, agpToETRD_eq, agpToETR_correct]

/-! ### Polynomial time -/

section PTLemmas

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.intTermD {p : α → Bool × Word} (hp : PT p) :
    PT (fun a => intTermD (p a)) := by
  unfold intTermD; fun_prop

@[fun_prop] protected theorem PT.coordAtD {D : α → FracDigits} {k : α → ℕ} (hD : PT D)
    (hk : PT k) : PT (fun a => coordAtD (D a) (k a)) := by
  unfold coordAtD; fun_prop

@[fun_prop] protected theorem PT.coordFD {D : α → List FracDigits} {k : α → ℕ} (hD : PT D)
    (hk : PT k) : PT (fun a => coordFD (D a) (k a)) := by
  unfold coordFD; fun_prop

@[fun_prop] protected theorem PT.validBD {D : α → List FracDigits} (hD : PT D) :
    PT (fun a => validBD (D a)) := by
  unfold validBD; fun_prop

@[fun_prop] protected theorem PT.agpFormulaD {D : α → List FracDigits} {g : α → ℕ} (hD : PT D)
    (hg : PT g) : PT (fun a => agpFormulaD (D a) (g a)) := by
  unfold agpFormulaD; fun_prop

end PTLemmas

/-- The digit version of the reduction is polynomial-time. -/
protected theorem PT.agpToETRD : PT agpToETRD := by
  refine PT.of_optionCases (o := ArtGallery.decodeAGP) (d := fun _ => fFalse)
    (f := fun _ r => agpFormulaD r.1 (min (SAT.binaryValue r.2) (r.1.length + 3)))
    (PT.decodeAGP PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [agpToETRD, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [agpToETRD, h]

/-- **The reduction from AGP to ETR is polynomial-time.** -/
protected theorem PT.agpReduction : PT agpReduction := by
  unfold agpReduction
  exact PT.formulaEncode PT.agpToETRD

/-- **The art gallery problem is in `∃ℝ`** (paper, Theorem 13). -/
theorem agp_inER : InER AGP :=
  PT.polyRed PT.agpReduction agpReduction_correct

/-! ### Integer coordinates -/

/-- The digits of the fraction vertex `x/1, y/1` from the digits of the integer vertex `(x, y)`. -/
def intToFracDigits (D : (Bool × Word) × (Bool × Word)) : FracDigits := (D.1, [true], D.2, [true])

/-- **The reduction from AGP with integer coordinates to AGP** on raw words: integer vertices
become fractions with denominators `1`; a non-code goes to the code of the empty polygon. -/
def agpIntReduction (w : Word) : Word :=
  match decodeAGPInt w with
  | none => encodeAGP [] 0
  | some (D, gd) => agpWord (D.map intToFracDigits) gd

/-- The fraction vertex `x/1, y/1`. -/
def FracPoint.ofInt (p : ℤ × ℤ) : FracPoint := ⟨p.1, 1, p.2, 1⟩

theorem bits_one : (1 : ℕ).bits = [true] := by
  simp

theorem FracPoint.digits_ofInt (p : ℤ × ℤ) :
    (FracPoint.ofInt p).digits = intToFracDigits (intPointDigits p) := by
  simp [FracPoint.digits, FracPoint.ofInt, intToFracDigits, intPointDigits]

theorem FracPoint.toPoint_ofInt (p : ℤ × ℤ) : (FracPoint.ofInt p).toPoint = intPoint p := by
  simp [FracPoint.toPoint, FracPoint.ofInt, intPoint]

theorem agpIntReduction_encode (V : List (ℤ × ℤ)) (g : ℕ) :
    agpIntReduction (encodeAGPInt V g) = encodeAGP (V.map FracPoint.ofInt) g := by
  unfold agpIntReduction
  rw [decodeAGPInt_encodeAGPInt, encodeAGP_eq_agpWord (V.map FracPoint.ofInt) g]
  simp only [List.map_map]
  congr 2
  funext p
  exact (FracPoint.digits_ofInt p).symm

theorem encodeAGP_inj {V V' : List FracPoint} {g g' : ℕ} (h : encodeAGP V g = encodeAGP V' g') :
    V = V' ∧ g = g' := by
  have h1 := Membership.decodeAGP_encodeAGP V g
  rw [h, Membership.decodeAGP_encodeAGP] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

theorem not_AGP_empty : ¬ AGP (encodeAGP [] 0) := by
  rintro ⟨V, g, h, _, hS, _⟩
  obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
  have := hS.1
  simp [Polygon.n] at this

/-- Correctness of the reduction `AGPInt ≤ AGP`. -/
theorem agpIntReduction_correct (w : Word) : AGPInt w ↔ AGP (agpIntReduction w) := by
  constructor
  · rintro ⟨V, g, rfl, hS, hG⟩
    rw [agpIntReduction_encode]
    have hP : (V.map FracPoint.ofInt).map FracPoint.toPoint = V.map intPoint := by
      simp only [List.map_map]
      congr 1
      funext p
      exact FracPoint.toPoint_ofInt p
    refine ⟨V.map FracPoint.ofInt, g, rfl, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, _, rfl⟩ := List.mem_map.1 hp
      exact ⟨Nat.one_pos, Nat.one_pos⟩
    · rw [hP]; exact hS
    · rw [hP]; exact hG
  · intro h
    cases hd : decodeAGPInt w with
    | none =>
      unfold agpIntReduction at h
      rw [hd] at h
      exact absurd h not_AGP_empty
    | some r =>
      obtain ⟨D, gd⟩ := r
      obtain ⟨V, g, rfl, rfl, rfl⟩ := decodeAGPInt_sound hd
      rw [agpIntReduction_encode] at h
      obtain ⟨V', g', he, _, hS, hG⟩ := h
      obtain ⟨hV, hg⟩ := encodeAGP_inj he
      subst hV
      rw [hg] at hG
      have hP : (V.map FracPoint.ofInt).map FracPoint.toPoint = V.map intPoint := by
        simp only [List.map_map]
        congr 1
        funext p
        exact FracPoint.toPoint_ofInt p
      rw [hP] at hS hG
      exact ⟨V, g, rfl, hS, hG⟩

/-- The reduction `AGPInt ≤ AGP` is polynomial-time. -/
protected theorem PT.agpIntReduction : PT agpIntReduction := by
  refine PT.of_optionCases (o := decodeAGPInt) (d := fun _ => encodeAGP [] 0)
    (f := fun _ r => agpWord (r.1.map intToFracDigits) r.2)
    (PT.decodeAGPInt PT.id) (PT.const _) (by unfold agpWord intToFracDigits; fun_prop) ?_ ?_
  · intro w h; simp [agpIntReduction, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [agpIntReduction, h]

/-- `AGPInt` reduces to `AGP` in polynomial time. -/
theorem agpInt_polyRed_agp : PolyRed AGPInt AGP :=
  PT.polyRed PT.agpIntReduction agpIntReduction_correct

/-- **The art gallery problem with integer coordinates is in `∃ℝ`.** -/
theorem agpInt_inER : InER AGPInt :=
  InER.of_polyRed agpInt_polyRed_agp agp_inER

end ArtGallery

end
