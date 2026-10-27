module

public import ArtGallery.Existence.SplitDiagonal
public import ArtGallery.Existence.Base
public import ArtGallery.Existence.Diagonal

/-!
# Existence of a triangulation

Every simple polygon has a triangulation (`exists_triangulation`).

The proof is a strong induction on the number of vertices `n`:

* `n = 3`: the polygon is weakly triangulated by its single triangle
  (`weakTriangulates_triangle`);
* `n ≥ 4`: there is an interior diagonal `(s, L)` (`exists_diagonal`); the two arcs it cuts
  off are simple (`simple_arc`, `simple_arc_compl`) with `L + 1 < n` and `n - L + 1 < n`
  vertices, so the induction hypothesis weakly triangulates both, and the two weak
  triangulations combine (`weakTriangulates_of_diagonal`).

A weak triangulation is a triangulation (`triangulates_of_weak`).

The file ends with two elementary facts about `Triangulates` that the machine side uses:
the length of a triangulation is `n - 2`, and triangulating is invariant under permutation of
the list of triangles.

Provenance: adapted from `Chazelle/Existence/Main.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open ArtGallery

/-- **Every simple polygon has a weak triangulation.**  Strong induction on the number of
vertices, cutting along an interior diagonal. -/
theorem exists_weakTriangulation {P : Polygon} (hP : P.Simple) :
    ∃ T : List Polygon.Triangle, WeakTriangulates P T := by
  suffices h : ∀ m : ℕ, ∀ Q : Polygon, Q.n = m → Q.Simple →
      ∃ T : List Polygon.Triangle, WeakTriangulates Q T from h P.n P rfl hP
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Q hQm hQ
  have h3 : 3 ≤ Q.n := hQ.1
  by_cases h3' : Q.n = 3
  · exact ⟨[(0, 1, 2)], weakTriangulates_triangle Q hQ h3'⟩
  have h4 : 4 ≤ Q.n := by omega
  obtain ⟨s, L, hd, hin⟩ := exists_diagonal hQ h4
  have hL2 : 2 ≤ L := hd.1
  have hLn : L + 2 ≤ Q.n := hd.2.1
  have hA₁ : (Q.arc s L).Simple := simple_arc Q s L hQ hd
  have hA₂ : (Q.arc ((s + L) % Q.n) (Q.n - L)).Simple := simple_arc_compl Q s L hQ hd
  obtain ⟨T₁, hT₁⟩ := ih (Q.arc s L).n (by rw [n_arc]; omega) (Q.arc s L) rfl hA₁
  obtain ⟨T₂, hT₂⟩ := ih (Q.arc ((s + L) % Q.n) (Q.n - L)).n (by rw [n_arc]; omega)
    (Q.arc ((s + L) % Q.n) (Q.n - L)) rfl hA₂
  exact ⟨_, weakTriangulates_of_diagonal hQ hd hin hT₁ hT₂⟩

/-- **Every simple polygon has a triangulation.** -/
theorem exists_triangulation {P : Polygon} (hP : P.Simple) :
    ∃ T : List Polygon.Triangle, P.Triangulates T := by
  obtain ⟨T, hT⟩ := exists_weakTriangulation hP
  exact ⟨T, triangulates_of_weak hT⟩

/-! ### Elementary consequences of `Triangulates` -/

/-- A triangulation of `P` has exactly `n - 2` triangles. -/
theorem triangulates_length {P : Polygon} {T : List Polygon.Triangle} (h : P.Triangulates T) :
    T.length = P.n - 2 := by
  have := h.2.1
  omega

/-- The interior-disjointness relation on triangles is symmetric. -/
theorem disjoint_interior_symm (P : Polygon) {s t : Polygon.Triangle}
    (h : Disjoint (interior (P.triSet s)) (interior (P.triSet t))) :
    Disjoint (interior (P.triSet t)) (interior (P.triSet s)) :=
  h.symm

/-- The conformity relation on triangles is symmetric. -/
theorem conforming_symm (P : Polygon) {s t : Polygon.Triangle}
    (h : P.triSet s ∩ P.triSet t = convexHull ℝ (P.triVertices s ∩ P.triVertices t)) :
    P.triSet t ∩ P.triSet s = convexHull ℝ (P.triVertices t ∩ P.triVertices s) := by
  rw [Set.inter_comm, h, Set.inter_comm]

/-- **Triangulating is invariant under permutation of the list of triangles.** -/
theorem triangulates_of_perm {P : Polygon} {T T' : List Polygon.Triangle}
    (h : P.Triangulates T) (hp : T.Perm T') : P.Triangulates T' := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hconf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hvalid t (hp.mem_iff.mpr ht)
  · rw [← hp.length_eq]
    exact hcount
  · rw [← hunion]
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, hpt⟩
      exact ⟨t, hp.mem_iff.mpr ht, hpt⟩
    · rintro ⟨t, ht, hpt⟩
      exact ⟨t, hp.mem_iff.mp ht, hpt⟩
  · exact (hp.pairwise_iff (fun {_ _} h => disjoint_interior_symm P h)).mp hdisj
  · exact (hp.pairwise_iff (fun {_ _} h => conforming_symm P h)).mp hconf

end

end ArtGallery.Existence
