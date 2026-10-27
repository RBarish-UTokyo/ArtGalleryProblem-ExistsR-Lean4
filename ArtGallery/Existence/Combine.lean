module

public import ArtGallery.Existence.Arc
public import ArtGallery.Geometry.Conformity

/-!
# Combining triangulations of the two arcs of a diagonal

The induction invariant for the existence of triangulations is `WeakTriangulates P T`: the
first four clauses of `Polygon.Triangulates` (valid triangles, count `n - 2`, union equal to
the filled region, pairwise disjoint interiors), with the conformity clause replaced by the
*vertex condition*: every vertex of `P` lying in a triangle of `T` is a corner of that
triangle.  The conformity criterion `ArtGallery.Geometry.triSet_inter_triSet_of_disjoint_interiors`
turns a weak triangulation into a triangulation (`triangulates_of_weak`).

`weakTriangulates_combine` assembles weak triangulations `T₁` of the arc `P.arc s L` and
`T₂` of the complementary arc `P.arc ((s + L) % n) (n - L)` into a weak triangulation of `P`,
by relabelling the triangle indices through `relabel`.  The geometric input, taken here as
hypotheses (they follow from the Jordan curve theorem for the arcs), is:

* `hcover`: the filled region of `P` is the union of the filled regions of the two arcs;
* `hmeet`: the filled regions of the two arcs meet only on the chord;
* `hdisj`: the interiors of the filled regions of the two arcs are disjoint.

(`hdisj` follows from `hmeet` and the fact that the chord lies on the boundary of each arc,
which is disjoint from the interior of its filled region; that last fact is topological and is
not available at this level, so it is taken as a hypothesis.)

Provenance: adapted from `Chazelle/Existence/Combine.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open ArtGallery.Jordan

/-! ### Weak triangulations -/

/-- `T` weakly triangulates `P`: valid triangles, exactly `n - 2` of them, covering exactly
the filled region, with pairwise disjoint interiors, and such that every vertex of `P` lying in
a triangle of `T` is a corner of that triangle. -/
def WeakTriangulates (P : Polygon) (T : List Polygon.Triangle) : Prop :=
  (∀ t ∈ T, P.validTriangle t) ∧
  T.length + 2 = P.n ∧
  {p | ∃ t ∈ T, p ∈ P.triSet t} = P.filled ∧
  T.Pairwise (fun s t => Disjoint (interior (P.triSet s)) (interior (P.triSet t))) ∧
  (∀ t ∈ T, ∀ i, i < P.n → P.vtx i ∈ P.triSet t → P.vtx i ∈ P.triVertices t)

/-- Every triangle of a weak triangulation lies in the filled region. -/
theorem triSet_subset_filled_of_weak {P : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates P T) {t : Polygon.Triangle} (ht : t ∈ T) : P.triSet t ⊆ P.filled :=
  fun _ hp => h.2.2.1 ▸ ⟨t, ht, hp⟩

/-- **A weak triangulation is a triangulation**: conformity follows from the disjointness of
the interiors and the vertex condition, by the conformity criterion. -/
theorem triangulates_of_weak {P : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates P T) : P.Triangulates T := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hvert⟩ := h
  refine ⟨hvalid, hcount, hunion, hdisj, ?_⟩
  refine hdisj.imp_of_mem ?_
  intro a b ha hb hab
  apply Geometry.triSet_inter_triSet_of_disjoint_interiors (hvalid a ha) (hvalid b hb) hab
  · intro v hv hva
    simp only [Polygon.triVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hvert a ha _ (hvalid b hb).1 hva
    · exact hvert a ha _ (hvalid b hb).2.1 hva
    · exact hvert a ha _ (hvalid b hb).2.2.1 hva
  · intro v hv hvb
    simp only [Polygon.triVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hvert b hb _ (hvalid a ha).1 hvb
    · exact hvert b hb _ (hvalid a ha).2.1 hvb
    · exact hvert b hb _ (hvalid a ha).2.2.1 hvb

/-! ### Vertices of `P` in the filled region of an arc -/

variable (P : Polygon) (s L : ℕ)

/-- The first vertex of the arc is vertex `s % n` of `P`. -/
theorem vtx_arc_zero : (P.arc s L).vtx 0 = P.vtx (s % P.n) := by
  rw [vtx_arc P s L (Nat.zero_le L), Nat.add_zero s]

/-- The last vertex of the arc is vertex `(s + L) % n` of `P`. -/
theorem vtx_arc_last : (P.arc s L).vtx L = P.vtx ((s + L) % P.n) :=
  vtx_arc P s L le_rfl

/-- The first vertex of the complementary arc is vertex `(s + L) % n` of `P`. -/
theorem vtx_arc_compl_zero :
    (P.arc ((s + L) % P.n) (P.n - L)).vtx 0 = P.vtx ((s + L) % P.n) := by
  rw [vtx_arc_zero, Nat.mod_mod]

/-- The last vertex of the complementary arc is vertex `s % n` of `P`. -/
theorem vtx_arc_compl_last (hL : L ≤ P.n) :
    (P.arc ((s + L) % P.n) (P.n - L)).vtx (P.n - L) = P.vtx (s % P.n) := by
  rw [vtx_arc_last, compl_arc_last_index P s L hL]

/-- A vertex of `P` on the chord of a diagonal is one of its two endpoints. -/
theorem vtx_eq_chord_endpoint (hd : IsDiagonal P s L) {i : ℕ} (hi : i < P.n)
    (h : P.vtx i ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n))) :
    P.vtx i = P.vtx (s % P.n) ∨ P.vtx i = P.vtx ((s + L) % P.n) := by
  by_contra hcon
  rw [not_or] at hcon
  exact hd.2.2 _ h hcon.1 hcon.2 (vtx_mem_boundary P hi)

/-- A vertex of `P` lying in the filled region of the arc is a vertex of the arc, provided the
filled regions of the two arcs meet only on the chord. -/
theorem exists_arc_vertex_of_mem_filled (hd : IsDiagonal P s L)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled →
      p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)))
    {i : ℕ} (hi : i < P.n) (h : P.vtx i ∈ (P.arc s L).filled) :
    ∃ k, k ≤ L ∧ (P.arc s L).vtx k = P.vtx i := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hL : L ≤ P.n := by have := hd.2.1; omega
  rcases vertex_index_cases P s L hL hn hi with ⟨k, hk, hki⟩ | ⟨k, hk, hki⟩
  · exact ⟨k, hk, by rw [vtx_arc P s L hk, hki]⟩
  · have h2 : P.vtx i ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled := by
      rw [← hki, ← vtx_arc P _ _ hk]
      exact boundary_subset_filled _ (vtx_mem_boundary _ (by rw [n_arc]; omega))
    rcases vtx_eq_chord_endpoint P s L hd hi (hmeet _ h h2) with h3 | h3
    · exact ⟨0, Nat.zero_le L, by rw [vtx_arc_zero, h3]⟩
    · exact ⟨L, le_rfl, by rw [vtx_arc_last, h3]⟩

/-- A vertex of `P` lying in the filled region of the complementary arc is a vertex of the
complementary arc, provided the filled regions of the two arcs meet only on the chord. -/
theorem exists_arc_compl_vertex_of_mem_filled (hd : IsDiagonal P s L)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled →
      p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)))
    {i : ℕ} (hi : i < P.n) (h : P.vtx i ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled) :
    ∃ k, k ≤ P.n - L ∧ (P.arc ((s + L) % P.n) (P.n - L)).vtx k = P.vtx i := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hL : L ≤ P.n := by have := hd.2.1; omega
  rcases vertex_index_cases P s L hL hn hi with ⟨k, hk, hki⟩ | ⟨k, hk, hki⟩
  · have h1 : P.vtx i ∈ (P.arc s L).filled := by
      rw [← hki, ← vtx_arc P s L hk]
      exact boundary_subset_filled _ (vtx_mem_boundary _ (by rw [n_arc]; omega))
    rcases vtx_eq_chord_endpoint P s L hd hi (hmeet _ h1 h) with h3 | h3
    · exact ⟨P.n - L, le_rfl, by rw [vtx_arc_compl_last P s L hL, h3]⟩
    · exact ⟨0, Nat.zero_le _, by rw [vtx_arc_compl_zero, h3]⟩
  · exact ⟨k, hk, by rw [vtx_arc P _ _ hk, hki]⟩

/-! ### Combining -/

/-- **Combining weak triangulations along a diagonal.**  Let `(s, L)` be a diagonal of `P`,
`T₁` a weak triangulation of the arc `P.arc s L` and `T₂` one of the complementary arc
`P.arc ((s + L) % n) (n - L)`.  Assume the filled region of `P` is the union of those of the
arcs (`hcover`), that the filled regions of the arcs meet only on the chord (`hmeet`), and that
their interiors are disjoint (`hdisj`).  Then the relabelled triangles of `T₁` and `T₂`
together weakly triangulate `P`. -/
theorem weakTriangulates_combine {P : Polygon} {s L : ℕ} (hd : IsDiagonal P s L)
    {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates (P.arc s L) T₁)
    (h₂ : WeakTriangulates (P.arc ((s + L) % P.n) (P.n - L)) T₂)
    (hcover : P.filled = (P.arc s L).filled ∪ (P.arc ((s + L) % P.n) (P.n - L)).filled)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled →
      p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)))
    (hdisj : Disjoint (interior (P.arc s L).filled)
      (interior (P.arc ((s + L) % P.n) (P.n - L)).filled)) :
    WeakTriangulates P (T₁.map (relabel s P.n) ++ T₂.map (relabel ((s + L) % P.n) P.n)) := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hsub₁ := fun t ht => triSet_subset_filled_of_weak h₁ (t := t) ht
  have hsub₂ := fun t ht => triSet_subset_filled_of_weak h₂ (t := t) ht
  obtain ⟨hv₁, hc₁, hu₁, hp₁, hx₁⟩ := h₁
  obtain ⟨hv₂, hc₂, hu₂, hp₂, hx₂⟩ := h₂
  have hle₁ : ∀ t ∈ T₁, t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L :=
    fun t ht => index_le_of_validTriangle_arc P s L (hv₁ t ht)
  have hle₂ : ∀ t ∈ T₂, t.1 ≤ P.n - L ∧ t.2.1 ≤ P.n - L ∧ t.2.2 ≤ P.n - L :=
    fun t ht => index_le_of_validTriangle_arc P _ _ (hv₂ t ht)
  have hts₁ : ∀ t ∈ T₁, P.triSet (relabel s P.n t) = (P.arc s L).triSet t :=
    fun t ht => (triSet_arc P s L (hle₁ t ht)).symm
  have hts₂ : ∀ t ∈ T₂, P.triSet (relabel ((s + L) % P.n) P.n t) =
      (P.arc ((s + L) % P.n) (P.n - L)).triSet t :=
    fun t ht => (triSet_arc P _ _ (hle₂ t ht)).symm
  have htv₁ : ∀ t ∈ T₁, P.triVertices (relabel s P.n t) = (P.arc s L).triVertices t :=
    fun t ht => (triVertices_arc P s L (hle₁ t ht)).symm
  have htv₂ : ∀ t ∈ T₂, P.triVertices (relabel ((s + L) % P.n) P.n t) =
      (P.arc ((s + L) % P.n) (P.n - L)).triVertices t :=
    fun t ht => (triVertices_arc P _ _ (hle₂ t ht)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- validity
    intro t ht
    rw [List.mem_append, List.mem_map, List.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
    · exact validTriangle_arc P s L hn (hv₁ t' ht')
    · exact validTriangle_arc P _ _ hn (hv₂ t' ht')
  · -- count
    rw [List.length_append, List.length_map, List.length_map]
    rw [n_arc] at hc₁ hc₂
    have := hd.1
    have := hd.2.1
    omega
  · -- union
    rw [hcover, ← hu₁, ← hu₂]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨t, (⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩), hp⟩
      · exact Or.inl ⟨t', ht', by rw [← hts₁ t' ht']; exact hp⟩
      · exact Or.inr ⟨t', ht', by rw [← hts₂ t' ht']; exact hp⟩
    · rintro (⟨t', ht', hp⟩ | ⟨t', ht', hp⟩)
      · exact ⟨_, Or.inl ⟨t', ht', rfl⟩, by rw [hts₁ t' ht']; exact hp⟩
      · exact ⟨_, Or.inr ⟨t', ht', rfl⟩, by rw [hts₂ t' ht']; exact hp⟩
  · -- disjoint interiors
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine hp₁.imp_of_mem ?_
      intro a b ha hb h
      rw [hts₁ a ha, hts₁ b hb]
      exact h
    · rw [List.pairwise_map]
      refine hp₂.imp_of_mem ?_
      intro a b ha hb h
      rw [hts₂ a ha, hts₂ b hb]
      exact h
    · intro a ha b hb
      rw [List.mem_map] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [hts₁ a' ha', hts₂ b' hb']
      exact hdisj.mono (interior_mono (hsub₁ a' ha')) (interior_mono (hsub₂ b' hb'))
  · -- vertex condition
    intro t ht i hi hpi
    rw [List.mem_append, List.mem_map, List.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
    · rw [hts₁ t' ht'] at hpi
      rw [htv₁ t' ht']
      obtain ⟨k, hk, hki⟩ :=
        exists_arc_vertex_of_mem_filled P s L hd hmeet hi (hsub₁ t' ht' hpi)
      rw [← hki] at hpi ⊢
      exact hx₁ t' ht' k (by rw [n_arc]; omega) hpi
    · rw [hts₂ t' ht'] at hpi
      rw [htv₂ t' ht']
      obtain ⟨k, hk, hki⟩ :=
        exists_arc_compl_vertex_of_mem_filled P s L hd hmeet hi (hsub₂ t' ht' hpi)
      rw [← hki] at hpi ⊢
      exact hx₂ t' ht' k (by rw [n_arc]; omega) hpi

end

end ArtGallery.Existence
