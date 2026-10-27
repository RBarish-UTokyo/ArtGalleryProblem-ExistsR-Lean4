module

public import ArtGallery.Geometry.SpecExtra

/-!
# The lexicographic order on points

Adapted from `Chazelle/Programs/MinVertex.lean` of the Palomar entry
PALOMAR-2026-10-05-000003, `LinearTimeTriangulation-ChazelleAlgorithm-Lean4` (only the order and
its lemmas).
-/

@[expose] public section

namespace ArtGallery

namespace Programs

/-! ### The lexicographic order on points -/

/-- Lexicographic `≤` on points: smaller abscissa, or equal abscissa and `≤` ordinate. -/
def lexLE (p q : Point) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- Lexicographic `<` on points. -/
def lexLT (p q : Point) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem lexLE_refl (p : Point) : lexLE p p := Or.inr ⟨rfl, le_rfl⟩

theorem lexLE_trans {p q r : Point} (h₁ : lexLE p q) (h₂ : lexLE q r) : lexLE p r := by
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₂ ▸ h₁)
  · exact Or.inl (h₁ ▸ h₂)
  · exact Or.inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩

theorem lexLE_of_lexLT {p q : Point} (h : lexLT p q) : lexLE p q := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, h'.le⟩

/-- Totality: if `p` is not lexicographically smaller than `q` then `q ≤ p`. -/
theorem lexLE_of_not_lexLT {p q : Point} (h : ¬ lexLT p q) : lexLE q p := by
  rcases lt_trichotomy p.1 q.1 with h₁ | h₁ | h₁
  · exact absurd (Or.inl h₁) h
  · rcases lt_or_ge p.2 q.2 with h₂ | h₂
    · exact absurd (Or.inr ⟨h₁, h₂⟩) h
    · exact Or.inr ⟨h₁.symm, h₂⟩
  · exact Or.inl h₁

/-- Two points that are lexicographically `≤` each other are equal. -/
theorem lexLE_antisymm {p q : Point} (h₁ : lexLE p q) (h₂ : lexLE q p) : p = q := by
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact absurd (h₁.trans h₂) (lt_irrefl _)
  · exact absurd (h₂ ▸ h₁) (lt_irrefl _)
  · exact absurd (h₁ ▸ h₂) (lt_irrefl _)
  · exact Prod.ext h₁ (le_antisymm h₁' h₂')

end Programs

end ArtGallery

end
