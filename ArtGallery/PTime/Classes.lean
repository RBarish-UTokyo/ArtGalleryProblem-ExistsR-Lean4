module

public import ArtGallery.Spec
public import Complexity.Composition

/-!
# Closure properties of `PolyRed`, `InER`, `ERHard`, `ERComplete`

* `PolyRed` is reflexive (`ArtGallery.polyRed_refl'`) and transitive (`ArtGallery.polyRed_trans`);
* `InER` is closed under reductions to the left (`ArtGallery.InER.of_polyRed`);
* `ArtGallery.ERHard.of_polyRed`: hardness transfers along reductions;
* `ArtGallery.ETR_inER`, `ArtGallery.ETR_erHard`, `ArtGallery.ETR_erComplete`;
* packaging: `ArtGallery.ERComplete.of_polyRed` (membership plus a reduction from an
  `∃ℝ`-hard language) and `ArtGallery.ERComplete.of_polyRed_ETR`.
-/

@[expose] public section

namespace ArtGallery

open Complexity

/-- `PolyRed` is reflexive. -/
theorem polyRed_refl' (A : Language) : PolyRed A A := Complexity.polyRed_refl A

/-- `PolyRed` is transitive. -/
theorem polyRed_trans {A B C : Language} (hAB : PolyRed A B) (hBC : PolyRed B C) :
    PolyRed A C := by
  obtain ⟨f, hf, hf'⟩ := hAB
  obtain ⟨g, hg, hg'⟩ := hBC
  exact ⟨fun x => g (f x), polyTime_comp hg hf, fun x => (hf' x).trans (hg' (f x))⟩

/-- `InER` is closed under reductions to the left. -/
theorem InER.of_polyRed {A B : Language} (hAB : PolyRed A B) (hB : InER B) : InER A :=
  polyRed_trans hAB hB

/-- `∃ℝ`-hardness transfers along reductions. -/
theorem ERHard.of_polyRed {A B : Language} (hA : ERHard A) (hAB : PolyRed A B) : ERHard B :=
  fun L hL => polyRed_trans (hA L hL) hAB

/-- `ETR` is in `∃ℝ`. -/
theorem ETR_inER : InER ETR := polyRed_refl' ETR

/-- `ETR` is `∃ℝ`-hard (by definition of `∃ℝ`). -/
theorem ETR_erHard : ERHard ETR := fun _ hL => hL

/-- `ETR` is `∃ℝ`-complete. -/
theorem ETR_erComplete : ERComplete ETR := ⟨ETR_inER, ETR_erHard⟩

/-- A language in `∃ℝ` to which an `∃ℝ`-hard language reduces is `∃ℝ`-complete. -/
theorem ERComplete.of_polyRed {A B : Language} (hB : InER B) (hA : ERHard A)
    (hAB : PolyRed A B) : ERComplete B :=
  ⟨hB, hA.of_polyRed hAB⟩

/-- A language in `∃ℝ` to which `ETR` reduces is `∃ℝ`-complete. -/
theorem ERComplete.of_polyRed_ETR {B : Language} (hB : InER B) (hAB : PolyRed ETR B) :
    ERComplete B :=
  ERComplete.of_polyRed hB ETR_erHard hAB

/-- `∃ℝ`-completeness transfers along reductions in both directions. -/
theorem ERComplete.of_polyRed_both {A B : Language} (hA : ERComplete A) (hAB : PolyRed A B)
    (hBA : PolyRed B A) : ERComplete B :=
  ⟨InER.of_polyRed hBA hA.1, hA.2.of_polyRed hAB⟩

/-- `InER` is invariant under pointwise equivalence of languages. -/
theorem InER.congr {A B : Language} (h : ∀ w, A w ↔ B w) (hA : InER A) : InER B :=
  polyRed_congr h (fun _ => Iff.rfl) hA

end ArtGallery

end
