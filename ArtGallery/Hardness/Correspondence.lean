module

public import ArtGallery.Spec
public import ArtGallery.Hardness.Sec5.Main

/-!
# Theorem 54 (interface)

The reduction from ETR-INV to the art gallery problem (paper §5): the polygon `P(Φ)`, the
number `g(Φ)`, and the correspondence between solutions and guard sets.  The proof is
assembled in `ArtGallery/Hardness/Sec5/Main.lean` (`Sec5.etrinv_guard_correspondence'`).
-/

@[expose] public section

namespace ArtGallery

/-- **Theorem 54.** For every ETR-INV instance `Φ` on the variables `x 0, …, x (n-1)` there is
a simple polygon with rational vertices, a number `g` and rational shifts `d i` such that every
guard set has at least `g` guards, and an assignment `x` solves `Φ` (with every variable in
`[1/2, 2]`) iff every `x i` is in `[1/2, 2]` and some guard set of cardinality `g` contains the
guards `(x i + d i, 0)`; moreover
every guard set of cardinality `g` contains these guards for some solution `x`. -/
theorem etrinv_guard_correspondence (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∃ (V : List (ℚ × ℚ)) (g : ℕ) (d : ℕ → ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        g ≤ G.card) ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        G.card = g → ∃ x : ℕ → ℝ, ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ∧
          ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G) ∧
      ∀ x : ℕ → ℝ,
        ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ↔
          (∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∃ G : Finset Point, G.card = g ∧
            (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) ∧
            ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G :=
  Sec5.etrinv_guard_correspondence' Φ n hΦ

end ArtGallery

end
