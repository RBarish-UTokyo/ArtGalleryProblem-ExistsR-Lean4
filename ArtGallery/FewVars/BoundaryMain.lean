module

public import ArtGallery.FewVars.Boundary.Formula

/-!
# The point-boundary art gallery problem is in `∃ℝ`, with only guard variables

The polynomial-time reduction `FewVars.Boundary.fvbReduction` maps an instance `(V, g)` of the
point-boundary art gallery problem (Stade, SoCG 2025: guards anywhere in the region, only the
boundary must be seen) to a formula whose only variables are the `2g` guard coordinates.  The
key ingredient is the boundary witness lemma `Boundary.boundary_seen_of_witnesses`: guards see
the whole boundary iff they see finitely many explicit points of the edges (breakpoints of the
edges with the arrangement lines, and midpoints of pairs of breakpoints).
-/

@[expose] public section

namespace ArtGallery

open Complexity Complexity.PT ArtGallery.FewVars ArtGallery.FewVars.Boundary

/-- **The reduction from the point-boundary AGP to ETR with only guard variables**, on raw
words. -/
def FewVars.Boundary.fvbReduction (w : Word) : Word := (fvbToETR w).encode

/-- The point-boundary art gallery problem reduces in polynomial time to ETR by formulas whose
only variables are the `2g` coordinates of the `g` guards. -/
theorem agpPointBoundary_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPPointBoundary w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  refine ⟨fvbReduction, (PT.formulaEncode Boundary.PT.fvbToETR).polyTime_word, fun w => ?_,
    fun V g => ⟨fvbToETR (encodeAGP V g), rfl, fvbToETR_encodeAGP_varsLt V g⟩⟩
  rw [fvbReduction, ETR.ETR_encode_iff, fvbToETR_correct]

/-- **The point-boundary art gallery problem is in `∃ℝ`.** -/
theorem agpPointBoundary_inER : InER AGPPointBoundary := by
  obtain ⟨f, hf, hc, -⟩ := agpPointBoundary_inER_guard_variables
  exact ⟨f, hf, hc⟩

end ArtGallery

end
