module

public import ArtGallery.FewVars.PT

/-!
# AGP reduces to ETR with only the guard coordinates as variables

Improvement on the open problem of the paper's §7.2 (its formula uses `(n + g)^6` variables,
`n` the number of corners): the polynomial-time reduction `FewVars.fvReduction` maps an instance
`(V, g)` to a formula whose only variables are `x₀, …, x_{2g-1}`, the coordinates of the `g`
guards.  All auxiliary quantities of the §3 formula (corner coordinates, separating lines,
crossing parities, breakpoints, arrangement vertices, centroids) are written as explicit
rational expressions in the guard coordinates (`ArtGallery/FewVars`).
-/

@[expose] public section

namespace ArtGallery

open Complexity Complexity.PT ArtGallery.FewVars

/-- **The reduction from AGP to ETR with only guard variables**, on raw words. -/
def FewVars.fvReduction (w : Word) : Word := (fvToETR w).encode

/-- **Improvement on the open problem of §7.2.** The art gallery problem reduces in polynomial
time to ETR by formulas whose only variables are the `2g` coordinates of the `g` guards (the
paper's formula uses `(n + g)^6` variables, `n` the number of corners). -/
theorem agp_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGP w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  refine ⟨FewVars.fvReduction, (PT.formulaEncode PT.fvToETR).polyTime_word, fun w => ?_,
    fun V g => ⟨fvToETR (encodeAGP V g), rfl, fvToETR_encodeAGP_varsLt V g⟩⟩
  rw [FewVars.fvReduction, ETR.ETR_encode_iff, fvToETR_correct]

end ArtGallery

end
