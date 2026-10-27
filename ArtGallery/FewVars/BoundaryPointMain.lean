module

public import ArtGallery.FewVars.BoundaryPoint.Formula

/-!
# The boundary-point art gallery problem is in `∃ℝ`, with only guard variables

The polynomial-time reduction `FewVars.BoundaryPoint.fvbpReduction` maps an instance `(V, g)` of
the boundary-point art gallery problem (guards on the boundary, the whole region must be seen)
to a formula whose only variables are the `2g` guard coordinates.  It is the point-point
formula of `ArtGallery/FewVars/Formula.lean` (guards see every witness point of the
arrangement, hence the whole region) together with the condition that every guard lies on an
edge.
-/

@[expose] public section

namespace ArtGallery

open Complexity Complexity.PT ArtGallery.FewVars ArtGallery.FewVars.BoundaryPoint

/-- **The reduction from the boundary-point AGP to ETR with only guard variables**, on raw
words. -/
def FewVars.BoundaryPoint.fvbpReduction (w : Word) : Word := (fvbpToETR w).encode

/-- The boundary-point art gallery problem reduces in polynomial time to ETR by formulas whose
only variables are the `2g` coordinates of the `g` guards. -/
theorem agpBoundaryPoint_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPBoundaryPoint w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  refine ⟨fvbpReduction, (PT.formulaEncode BoundaryPoint.PT.fvbpToETR).polyTime_word,
    fun w => ?_, fun V g => ⟨fvbpToETR (encodeAGP V g), rfl, fvbpToETR_encodeAGP_varsLt V g⟩⟩
  rw [fvbpReduction, ETR.ETR_encode_iff, fvbpToETR_correct]

/-- **The boundary-point art gallery problem is in `∃ℝ`.** -/
theorem agpBoundaryPoint_inER : InER AGPBoundaryPoint := by
  obtain ⟨f, hf, hc, -⟩ := agpBoundaryPoint_inER_guard_variables
  exact ⟨f, hf, hc⟩

end ArtGallery

end
