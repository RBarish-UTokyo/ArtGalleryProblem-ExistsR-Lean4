module

public import ArtGallery.Hardness.BP.Assemble.Construct
public import ArtGallery.Hardness.Sec5.Assemble.TmplFacts

/-!
# Boundary-point variant: the placed template chains (simplicity and position)

Kernel-checked facts about the template chains `tmplVBP k` (integer template coordinates,
`BP/Assemble/TmplData.lean`) and their consequences for the placed chain `φ(tmplVBP k)`, where
`φ(V) = (S + 3, H − 1) + V/(D S)` (`tmplMapBP`, a similarity), as in `Sec5/Assemble/TmplFacts.lean`:

* (T-simple) the template chain closed by the stub `tmplStubBP` (the stub of
  `BP/Templates/*Data.lean`) passes the integer simplicity checker (`tmplPlacedBP_simple`);
* (box) all template coordinates are at most `50` in absolute value (`tmplPlacedBP_box`);
* (walls) every template edge lies right of the first vertex `V₀` or below it, and right of the
  last vertex `V_l` or below it (`tmplPlacedBP_quad`);
* (window) `(V_l.x + V_l.y) − (V₀.x + V₀.y) ≥ 1` (template units, `tmplBP_window`).  Unlike
  Section 5, the line `x + y = 0` does not separate `V₀` from `V_l` (for the addition kinds
  `V_l = e_j = (−15, 21/2)`); the two channel walls are separated by the line through the lower
  wall instead (`BP/Assemble/UnitChain.lean`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue
open ArtGallery.Sec5 (Kind boxOK quadOK boxOK_mem pairsIn_of_quadOK S_ne_of)

/-! ### Integer checks -/

/-- The stub closing the template chain to a polygon (as in `BP/Templates/*Data.lean`). -/
def tmplStubBP : Kind → List (ℤ × ℤ)
  | .ge => [((-27840000), 26587200), ((-27840000), 16599600)]
  | .le => [((-35520000), 33921600), ((-35520000), 22066800)]
  | .orient => [((-27840000), 26587200), ((-27840000), 16599600)]
  | .inv => [((-300897474240000), 357431788249800), ((-300897474240000), 299769108711600)]

/-- The template polygon: the chain closed by the stub. -/
def tmplVTBP (k : Kind) : List (ℤ × ℤ) := tmplVBP k ++ tmplStubBP k

/-- The first template vertex `V₀`. -/
def tmplFstBP (k : Kind) : ℤ × ℤ := (tmplVBP k).headD (0, 0)

/-- The last template vertex `V_l`. -/
def tmplLstBP (k : Kind) : ℤ × ℤ := (tmplVBP k).getLastD (0, 0)

/-- (T-simple) The template polygon passes the integer simplicity checker. -/
theorem tmplBP_simpleCheck (k : Kind) : Vis.Cert.simpleCheck (tmplVTBP k) = true := by
  cases k <;> decide +kernel

/-- (box) All template coordinates are at most `50 D` in absolute value. -/
theorem tmplBP_boxOK (k : Kind) : boxOK (50 * (tmplDBP k : ℤ)) (tmplVBP k) = true := by
  cases k <;> decide +kernel

/-- (walls) Every template edge is right of or below the first vertex. -/
theorem tmplBP_quadFst (k : Kind) : quadOK (tmplFstBP k) (tmplVBP k) = true := by
  cases k <;> decide +kernel

/-- (walls) Every template edge is right of or below the last vertex. -/
theorem tmplBP_quadLst (k : Kind) : quadOK (tmplLstBP k) (tmplVBP k) = true := by
  cases k <;> decide +kernel

/-- (window) `(V_l.x + V_l.y) − (V₀.x + V₀.y) ≥ D`. -/
theorem tmplBP_window (k : Kind) :
    (tmplDBP k : ℤ) ≤ (tmplLstBP k).1 + (tmplLstBP k).2 - ((tmplFstBP k).1 + (tmplFstBP k).2) := by
  cases k <;> decide +kernel

theorem tmplBP_length (k : Kind) : 3 ≤ (tmplVBP k).length := by
  cases k <;> decide +kernel

theorem tmplDBP_pos (k : Kind) : 0 < tmplDBP k := by cases k <;> decide

/-! ### From the checks to real statements -/

/-- The scale factor `1/(D S)` of the placement is nonzero. -/
theorem tmplScaleBP_ne {k : Kind} {S : ℝ} (hS : S ≠ 0) : 1 / ((tmplDBP k : ℝ) * S) ≠ 0 := by
  have : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  exact one_div_ne_zero (mul_ne_zero this.ne' hS)

/-- The placement `V ↦ (S + 3, H − 1) + V/(D S)` of integer template points. -/
noncomputable def tmplMapBP (k : Kind) (S H : ℝ) (hS : S ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  Vis.Cert.simil (1 / ((tmplDBP k : ℝ) * S)) (tmplScaleBP_ne hS) (S + 3, H - 1)

theorem tmplMapBP_apply (k : Kind) {S H : ℝ} (hS : S ≠ 0) (p : Point) :
    tmplMapBP k S H hS p = (S + 3 + p.1 / ((tmplDBP k : ℝ) * S), H - 1 + p.2 / ((tmplDBP k : ℝ) * S)) := by
  simp only [tmplMapBP, Vis.Cert.simil_apply]
  ext <;> simp <;> ring

/-- The placed template chain (real points). -/
noncomputable def tmplPlacedBP (k : Kind) (S H : ℝ) (hS : S ≠ 0) : List Point :=
  (tmplVBP k).map fun V => tmplMapBP k S H hS (intPoint V)

section Placed

variable (k : Kind) {S H : ℝ} (hS : 1000 ≤ S)


include hS

theorem tmplPlacedBP_eq : tmplPlacedBP k S H (S_ne_of hS) =
    ((tmplVBP k).map intPoint).map (tmplMapBP k S H (S_ne_of hS)) := by
  simp [tmplPlacedBP, List.map_map, Function.comp_def]

theorem tmplPlacedBP_length : 3 ≤ (tmplPlacedBP k S H (S_ne_of hS)).length := by
  simpa [tmplPlacedBP] using tmplBP_length k

/-- **The placed template chain is simple.** -/
theorem tmplPlacedBP_simple : ChainSimple (tmplPlacedBP k S H (S_ne_of hS)) := by
  have hP := Vis.Cert.simple_of_simpleCheck (tmplBP_simpleCheck k)
  have hP' := Hardening.Invariance.simple_mapPoly (tmplMapBP k S H (S_ne_of hS)) _ hP
  simp only [Hardening.Invariance.mapPoly, tmplVTBP, List.map_append] at hP'
  rw [tmplPlacedBP_eq k hS]
  exact chainSimple_of_simple hP'

theorem tmplPlacedBP_mem {p : Point} (hp : p ∈ chainSet (tmplPlacedBP k S H (S_ne_of hS))) :
    ∃ q ∈ chainSet ((tmplVBP k).map intPoint), p = tmplMapBP k S H (S_ne_of hS) q := by
  rw [tmplPlacedBP_eq k hS, chainSet_map] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  exact ⟨q, hq, hqp.symm⟩

omit hS in
theorem tmplBP_box_int {q : Point} (hq : q ∈ chainSet ((tmplVBP k).map intPoint)) :
    -(50 * (tmplDBP k : ℝ)) ≤ q.1 ∧ q.1 ≤ 50 * (tmplDBP k : ℝ) ∧
      -(50 * (tmplDBP k : ℝ)) ≤ q.2 ∧ q.2 ≤ 50 * (tmplDBP k : ℝ) := by
  have hb := boxOK_mem (tmplBP_boxOK k)
  have hv : ∀ p ∈ (tmplVBP k).map intPoint, -(50 * (tmplDBP k : ℝ)) ≤ p.1 ∧ p.1 ≤ 50 * (tmplDBP k : ℝ) ∧
      -(50 * (tmplDBP k : ℝ)) ≤ p.2 ∧ p.2 ≤ 50 * (tmplDBP k : ℝ) := by
    intro p hp
    obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hp
    obtain ⟨a1, a2, a3, a4⟩ := hb V hV
    simp only [intPoint]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : ((-(50 * (tmplDBP k : ℤ)) : ℤ) : ℝ) ≤ (V.1 : ℝ) := by exact_mod_cast a1
      push_cast at this; linarith
    · have : ((V.1 : ℤ) : ℝ) ≤ ((50 * (tmplDBP k : ℤ) : ℤ) : ℝ) := by exact_mod_cast a2
      push_cast at this; linarith
    · have : ((-(50 * (tmplDBP k : ℤ)) : ℤ) : ℝ) ≤ (V.2 : ℝ) := by exact_mod_cast a3
      push_cast at this; linarith
    · have : ((V.2 : ℤ) : ℝ) ≤ ((50 * (tmplDBP k : ℤ) : ℤ) : ℝ) := by exact_mod_cast a4
      push_cast at this; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := 50 * (tmplDBP k : ℝ))
      (fun p hp => by have := (hv p hp).1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := 50 * (tmplDBP k : ℝ))
      (fun p hp => by have := (hv p hp).2.1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 0) (β := -1) (c := 50 * (tmplDBP k : ℝ))
      (fun p hp => by have := (hv p hp).2.2.1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := 50 * (tmplDBP k : ℝ))
      (fun p hp => by have := (hv p hp).2.2.2; linarith) q hq
    linarith

/-- **Position of the placed template.** -/
theorem tmplPlacedBP_box {p : Point} (hp : p ∈ chainSet (tmplPlacedBP k S H (S_ne_of hS))) :
    S + 3 - 50 / S ≤ p.1 ∧ p.1 ≤ S + 3 + 50 / S ∧ H - 1 - 50 / S ≤ p.2 ∧ p.2 ≤ H - 1 + 50 / S := by
  obtain ⟨q, hq, rfl⟩ := tmplPlacedBP_mem k hS hp
  obtain ⟨b1, b2, b3, b4⟩ := tmplBP_box_int k hq
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  rw [tmplMapBP_apply]
  have e : ∀ x : ℝ, x / ((tmplDBP k : ℝ) * S) = (x / (tmplDBP k : ℝ)) / S := fun x => by
    field_simp
  have hb : ∀ x : ℝ, -(50 * (tmplDBP k : ℝ)) ≤ x → x ≤ 50 * (tmplDBP k : ℝ) →
      -(50 / S) ≤ x / ((tmplDBP k : ℝ) * S) ∧ x / ((tmplDBP k : ℝ) * S) ≤ 50 / S := by
    intro x h1 h2
    rw [e]
    have h1' : -50 ≤ x / (tmplDBP k : ℝ) := by rw [le_div_iff₀ hD]; linarith
    have h2' : x / (tmplDBP k : ℝ) ≤ 50 := by rw [div_le_iff₀ hD]; linarith
    constructor
    · rw [neg_div', div_le_div_iff_of_pos_right hS0]; linarith
    · exact div_le_div_of_nonneg_right h2' hS0.le
  obtain ⟨c1, c2⟩ := hb _ b1 b2
  obtain ⟨c3, c4⟩ := hb _ b3 b4
  simp only
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem tmplPlacedBP_fst : fstPt (tmplPlacedBP k S H (S_ne_of hS)) =
    tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k)) := by
  have hne : tmplVBP k ≠ [] := by cases k <;> simp [tmplVBP, tmplVGEBP, tmplVLEBP, tmplVORBP, tmplVInvBP]
  obtain ⟨a, l, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [tmplPlacedBP, tmplFstBP, he]
  rfl

theorem tmplPlacedBP_lst : lstPt (tmplPlacedBP k S H (S_ne_of hS)) =
    tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k)) := by
  have hne : tmplVBP k ≠ [] := by cases k <;> simp [tmplVBP, tmplVGEBP, tmplVLEBP, tmplVORBP, tmplVInvBP]
  unfold tmplPlacedBP tmplLstBP lstPt
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map,
    List.getLast?_eq_some_getLast hne]
  rfl

/-- The coordinate-wise monotone placement. -/
theorem tmplMapBP_le_iff {a b : ℝ} : a / ((tmplDBP k : ℝ) * S) ≤ b / ((tmplDBP k : ℝ) * S) ↔ a ≤ b := by
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  exact div_le_div_iff_of_pos_right (by positivity)

theorem tmplPlacedBP_quad {P : ℤ × ℤ} (hq : quadOK P (tmplVBP k) = true) {p : Point}
    (hp : p ∈ chainSet (tmplPlacedBP k S H (S_ne_of hS))) :
    (tmplMapBP k S H (S_ne_of hS) (intPoint P)).1 ≤ p.1 ∨
      p.2 ≤ (tmplMapBP k S H (S_ne_of hS) (intPoint P)).2 := by
  obtain ⟨q, hq', rfl⟩ := tmplPlacedBP_mem k hS hp
  have := chainSet_subset_union (convex_halfplane _ _ _) (convex_halfplane _ _ _)
    (pairsIn_of_quadOK hq) hq'
  rw [tmplMapBP_apply, tmplMapBP_apply]
  simp only [intPoint, mem_union, mem_ofPred_eq] at this ⊢
  rcases this with h | h
  · left
    have : (P.1 : ℝ) ≤ q.1 := by linarith
    have := (tmplMapBP_le_iff k hS).2 this
    linarith
  · right
    have : q.2 ≤ (P.2 : ℝ) := by linarith
    have := (tmplMapBP_le_iff k hS).2 this
    linarith

theorem tmplPlacedBP_fst_mem : tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k)) ∈
    chainSet (tmplPlacedBP k S H (S_ne_of hS)) := by
  rw [← tmplPlacedBP_fst k hS]
  exact fstPt_mem (by have := tmplPlacedBP_length k hS (H := H); omega)

theorem tmplPlacedBP_lst_mem : tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k)) ∈
    chainSet (tmplPlacedBP k S H (S_ne_of hS)) := by
  rw [← tmplPlacedBP_lst k hS]
  exact lstPt_mem (by have := tmplPlacedBP_length k hS (H := H); omega)

end Placed

end ArtGallery.BP

end