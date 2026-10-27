module

public import ArtGallery.Existence.Rotate

/-!
# Arcs of a polygon cut along a diagonal

`P.arc s L` is the polygon with the `L + 1` vertices `P.vtx ((s + i) % n)`, `i = 0, …, L`.
Its edges `0, …, L - 1` are the edges `(s + i) % n` of `P` (`edge_arc`) and its last edge is
the chord from vertex `(s + L) % n` back to vertex `s % n` (`edge_arc_last`).

The *complementary* arc `P.arc ((s + L) % n) (n - L)` has vertices `s + L, …, s + n ≡ s`
and closes with the same chord, reversed (`edge_arc_compl_last`).

* `crossSum_split` / `parity_split`: the crossing sum of `P` at `z` is the sum of the crossing
  sums of the two arcs (the two indicators of the chord cancel in `ZMod 2`, the remaining
  edges are the edges of `P` rotated to start at `s`).
* `IsDiagonal P s L`: `2 ≤ L`, `L + 2 ≤ n`, and the open chord avoids the boundary of `P`.
* `simple_arc`, `simple_arc_compl`: for a simple `P` and a diagonal, both arcs are simple.
* `boundary_arc_subset`, `boundary_subset_arcs`: the boundaries of the arcs are the boundary
  of `P` together with the chord.
* `triSet_arc`, `triVertices_arc`, `validTriangle_arc`: triangles of an arc relabel
  (`relabel s n`) to triangles of `P` with the same point sets.

Provenance: adapted from `Chazelle/Existence/Arc.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open ArtGallery.Jordan

/-! ### Elementary facts about vertices and edges -/

/-- Vertex `i` lies on edge `i`. -/
theorem vtx_mem_edge (P : Polygon) (i : ℕ) : P.vtx i ∈ P.edge i :=
  left_mem_segment _ _

/-- Vertex `(i + 1) % n` lies on edge `i`. -/
theorem vtx_succ_mem_edge (P : Polygon) (i : ℕ) : P.vtx ((i + 1) % P.n) ∈ P.edge i :=
  right_mem_segment _ _

/-- Every vertex with index in range lies on the boundary. -/
theorem vtx_mem_boundary (P : Polygon) {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.boundary :=
  ⟨i, hi, vtx_mem_edge P i⟩

/-- The boundary is contained in the filled region. -/
theorem boundary_subset_filled (P : Polygon) : P.boundary ⊆ P.filled :=
  Set.subset_union_left

/-- Every edge with index in range is contained in the boundary. -/
theorem edge_subset_boundary (P : Polygon) {i : ℕ} (hi : i < P.n) : P.edge i ⊆ P.boundary :=
  fun _ hp => ⟨i, hi, hp⟩

/-- `commonEndpoints` is symmetric. -/
theorem commonEndpoints_comm (P : Polygon) (i j : ℕ) :
    P.commonEndpoints i j = P.commonEndpoints j i := by
  ext p
  simp only [Polygon.commonEndpoints, Set.mem_ofPred_eq]
  exact and_comm

/-- In a simple polygon, a vertex lying on an edge is one of its endpoints. -/
theorem eq_endpoint_of_vtx_mem_edge {P : Polygon} (hP : P.Simple) {k i : ℕ} (hk : k < P.n)
    (hi : i < P.n) (h : P.vtx k ∈ P.edge i) :
    P.vtx k = P.vtx i ∨ P.vtx k = P.vtx ((i + 1) % P.n) := by
  by_cases hki : k = i
  · exact Or.inl (by rw [hki])
  · have hmem : P.vtx k ∈ P.edge i ∩ P.edge k := ⟨h, vtx_mem_edge P k⟩
    rw [hP.2.2 i k hi hk (Ne.symm hki)] at hmem
    exact hmem.1

/-! ### The arc -/

/-- The arc of `P` from vertex `s` through the next `L` vertices, closed by the chord back
to vertex `s`: its vertices are `P.vtx ((s + i) % n)` for `i = 0, …, L`. -/
def _root_.ArtGallery.Polygon.arc (P : ArtGallery.Polygon) (s L : ℕ) : ArtGallery.Polygon :=
  ⟨(List.range (L + 1)).map fun i => P.vtx ((s + i) % P.n)⟩

variable (P : Polygon) (s L : ℕ)

/-- The arc has `L + 1` vertices. -/
@[simp] theorem n_arc : (P.arc s L).n = L + 1 := by
  simp [Polygon.arc, Polygon.n]

/-- Vertex `i ≤ L` of the arc is vertex `(s + i) % n` of `P`. -/
theorem vtx_arc {i : ℕ} (hi : i ≤ L) : (P.arc s L).vtx i = P.vtx ((s + i) % P.n) := by
  simp [Polygon.arc, Polygon.vtx, List.getD_eq_getElem?_getD,
    List.getElem?_range (Nat.lt_succ_of_le hi)]

/-- The successor vertex of the arc, for `i < L`. -/
theorem vtx_arc_succ {i : ℕ} (hi : i < L) :
    (P.arc s L).vtx ((i + 1) % (P.arc s L).n) = P.vtx (((s + i) % P.n + 1) % P.n) := by
  rw [n_arc, Nat.mod_eq_of_lt (by omega : i + 1 < L + 1), vtx_arc P s L (by omega),
    mod_add_one_mod]

/-- Edge `i < L` of the arc is edge `(s + i) % n` of `P`. -/
theorem edge_arc {i : ℕ} (hi : i < L) : (P.arc s L).edge i = P.edge ((s + i) % P.n) := by
  unfold Polygon.edge
  rw [vtx_arc P s L hi.le, vtx_arc_succ P s L hi]

/-- The last edge of the arc is the chord from vertex `(s + L) % n` to vertex `s % n`. -/
theorem edge_arc_last :
    (P.arc s L).edge L = segment (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) := by
  unfold Polygon.edge
  rw [n_arc, Nat.mod_self, vtx_arc P s L le_rfl, vtx_arc P s L (Nat.zero_le L), Nat.add_zero s]

/-- The common endpoints of two non-chord edges of the arc. -/
theorem commonEndpoints_arc {i j : ℕ} (hi : i < L) (hj : j < L) :
    (P.arc s L).commonEndpoints i j =
      P.commonEndpoints ((s + i) % P.n) ((s + j) % P.n) := by
  unfold Polygon.commonEndpoints
  rw [vtx_arc P s L hi.le, vtx_arc P s L hj.le, vtx_arc_succ P s L hi, vtx_arc_succ P s L hj]

/-- The common endpoints of a non-chord edge of the arc and the chord. -/
theorem commonEndpoints_arc_last {i : ℕ} (hi : i < L) :
    (P.arc s L).commonEndpoints i L =
      {p | (p = P.vtx ((s + i) % P.n) ∨ p = P.vtx (((s + i) % P.n + 1) % P.n)) ∧
        (p = P.vtx ((s + L) % P.n) ∨ p = P.vtx (s % P.n))} := by
  unfold Polygon.commonEndpoints
  rw [vtx_arc_succ P s L hi, n_arc, Nat.mod_self, vtx_arc P s L hi.le, vtx_arc P s L le_rfl,
    vtx_arc P s L (Nat.zero_le L), Nat.add_zero s]

/-- Membership in the boundary of the arc: on an edge `(s + i) % n` of `P` with `i < L`, or
on the chord. -/
theorem mem_boundary_arc_iff {p : Point} :
    p ∈ (P.arc s L).boundary ↔
      (∃ i, i < L ∧ p ∈ P.edge ((s + i) % P.n)) ∨
        p ∈ segment (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) := by
  simp only [Polygon.boundary, Set.mem_ofPred_eq, n_arc]
  constructor
  · rintro ⟨i, hi, hp⟩
    rcases Nat.lt_or_ge i L with h | h
    · exact Or.inl ⟨i, h, by rw [← edge_arc P s L h]; exact hp⟩
    · have : i = L := by omega
      rw [this] at hp
      exact Or.inr (by rw [← edge_arc_last P s L]; exact hp)
  · rintro (⟨i, hi, hp⟩ | hp)
    · exact ⟨i, by omega, by rw [edge_arc P s L hi]; exact hp⟩
    · exact ⟨L, by omega, by rw [edge_arc_last]; exact hp⟩

/-- The boundary of the arc: the edges `(s + i) % n` of `P` for `i < L`, and the chord. -/
theorem boundary_arc :
    (P.arc s L).boundary =
      {p | ∃ i, i < L ∧ p ∈ P.edge ((s + i) % P.n)} ∪
        segment (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) := by
  ext p
  exact mem_boundary_arc_iff P s L

/-! ### The complementary arc -/

/-- Index arithmetic for the complementary arc: its vertex `i` is vertex `s + L + i` of `P`. -/
theorem compl_arc_index (i : ℕ) : ((s + L) % P.n + i) % P.n = (s + L + i) % P.n :=
  Nat.mod_add_mod _ _ _

/-- Index arithmetic for the complementary arc: its last vertex is vertex `s % n` of `P`. -/
theorem compl_arc_last_index (hL : L ≤ P.n) :
    ((s + L) % P.n + (P.n - L)) % P.n = s % P.n := by
  rw [Nat.mod_add_mod, show s + L + (P.n - L) = s + P.n by omega, Nat.add_mod_right]

/-- The last edge of the complementary arc is the chord, reversed. -/
theorem edge_arc_compl_last (hL : L ≤ P.n) :
    (P.arc ((s + L) % P.n) (P.n - L)).edge (P.n - L) =
      segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) := by
  rw [edge_arc_last, compl_arc_last_index P s L hL, Nat.mod_mod]

/-- Every vertex index of `P` is a vertex index of the arc or of the complementary arc. -/
theorem vertex_index_cases (hL : L ≤ P.n) (hn : 0 < P.n) {i : ℕ} (hi : i < P.n) :
    (∃ k, k ≤ L ∧ (s + k) % P.n = i) ∨
      (∃ k, k ≤ P.n - L ∧ ((s + L) % P.n + k) % P.n = i) := by
  obtain ⟨k, hk, hki⟩ := exists_rot_index hn s i hi
  rcases Nat.lt_or_ge k (L + 1) with h | h
  · exact Or.inl ⟨k, by omega, hki⟩
  · refine Or.inr ⟨k - L, by omega, ?_⟩
    rw [compl_arc_index, show s + L + (k - L) = s + k by omega, hki]

/-! ### Splitting the crossing sum along the chord -/

/-- The crossing sum of the arc: the sum over its non-chord edges plus the chord indicator. -/
theorem crossSum_arc (z : Point) :
    crossSum (P.arc s L) z =
      (∑ i ∈ Finset.range L,
        crossInd z (P.vtx ((s + i) % P.n)) (P.vtx (((s + i) % P.n + 1) % P.n))) +
        crossInd z (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) := by
  unfold crossSum
  rw [n_arc, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [vtx_arc P s L hi.le, Nat.mod_eq_of_lt (by omega : i + 1 < L + 1),
      vtx_arc P s L (by omega), mod_add_one_mod]
  · rw [Nat.mod_self, vtx_arc P s L le_rfl, vtx_arc P s L (Nat.zero_le L), Nat.add_zero s]

/-- The crossing sum of `P` splits over the edges `s, …, s + L - 1` and `s + L, …, s + n - 1`. -/
theorem crossSum_eq_sum_split (hL : L ≤ P.n) (z : Point) :
    crossSum P z =
      (∑ i ∈ Finset.range L,
        crossInd z (P.vtx ((s + i) % P.n)) (P.vtx (((s + i) % P.n + 1) % P.n))) +
      ∑ i ∈ Finset.range (P.n - L),
        crossInd z (P.vtx ((s + L + i) % P.n)) (P.vtx (((s + L + i) % P.n + 1) % P.n)) := by
  set g : ℕ → ZMod 2 := fun k => crossInd z (P.vtx k) (P.vtx ((k + 1) % P.n)) with hg
  have h1 : crossSum P z = ∑ i ∈ Finset.range P.n, g ((s + i) % P.n) := by
    unfold crossSum
    rw [sum_range_rot g s P.n]
  have h2 := Finset.sum_range_add (fun i => g ((s + i) % P.n)) L (P.n - L)
  rw [show L + (P.n - L) = P.n by omega] at h2
  rw [h1, h2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  show g ((s + (L + i)) % P.n) = _
  rw [← Nat.add_assoc]

/-- **Splitting along a chord.**  The crossing sum of `P` at `z` is the sum of the crossing
sums of the arc `P.arc s L` and of the complementary arc `P.arc ((s + L) % n) (n - L)`: the
two chord indicators cancel in `ZMod 2`. -/
theorem crossSum_split (hL : L ≤ P.n) (z : Point) :
    crossSum P z =
      crossSum (P.arc s L) z + crossSum (P.arc ((s + L) % P.n) (P.n - L)) z := by
  rw [crossSum_arc, crossSum_arc, compl_arc_last_index P s L hL, Nat.mod_mod,
    crossInd_comm (u := P.vtx (s % P.n)), add_add_add_comm, zmod_two_add_self, add_zero,
    crossSum_eq_sum_split P s L hL z]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [compl_arc_index P s L i]

/-- **Parity splits along a chord**: the parity with respect to `P` is the exclusive or of
the parities with respect to the two arcs. -/
theorem parity_split (hL : L ≤ P.n) (z : Point) :
    parity P z =
      Bool.xor (parity (P.arc s L) z) (parity (P.arc ((s + L) % P.n) (P.n - L)) z) := by
  unfold parity
  rw [crossSum_split P s L hL z]
  generalize crossSum (P.arc s L) z = a
  generalize crossSum (P.arc ((s + L) % P.n) (P.n - L)) z = b
  revert a b
  decide

/-! ### Diagonals and simplicity of the arcs -/

/-- `(s, L)` names a diagonal of `P`: the chord from vertex `s % n` to vertex `(s + L) % n`
with `2 ≤ L ≤ n - 2`, whose open part avoids the boundary of `P`.  (Whether the chord lies
inside or outside the polygon is a separate matter.) -/
def IsDiagonal (P : Polygon) (s L : ℕ) : Prop :=
  2 ≤ L ∧ L + 2 ≤ P.n ∧
    ∀ p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)),
      p ≠ P.vtx (s % P.n) → p ≠ P.vtx ((s + L) % P.n) → p ∉ P.boundary

/-- The complementary arc of a diagonal is again cut along a diagonal. -/
theorem isDiagonal_compl (hd : IsDiagonal P s L) : IsDiagonal P ((s + L) % P.n) (P.n - L) := by
  obtain ⟨h2, hn, hch⟩ := hd
  refine ⟨by omega, by omega, ?_⟩
  rw [compl_arc_last_index P s L (by omega), Nat.mod_mod, segment_comm]
  intro p hp h1 h2
  exact hch p hp h2 h1

/-- Simplicity of an arc, from the chord condition alone (with `2 ≤ L` and `L + 1 ≤ n`). -/
theorem simple_arc_of_chord (hP : P.Simple) (h2 : 2 ≤ L) (hLn : L + 1 ≤ P.n)
    (hch : ∀ p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)),
      p ≠ P.vtx (s % P.n) → p ≠ P.vtx ((s + L) % P.n) → p ∉ P.boundary) :
    (P.arc s L).Simple := by
  have hn : 0 < P.n := by omega
  refine ⟨by rw [n_arc]; omega, ?_, ?_⟩
  · intro i j hi hj hij
    rw [n_arc] at hi hj
    rw [vtx_arc P s L (by omega), vtx_arc P s L (by omega)] at hij
    exact rot_index_inj (by omega) (by omega)
      (hP.2.1 _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hij)
  · have key : ∀ i, i < L →
        (P.arc s L).edge i ∩ (P.arc s L).edge L = (P.arc s L).commonEndpoints i L := by
      intro i hi
      rw [edge_arc P s L hi, edge_arc_last, commonEndpoints_arc_last P s L hi]
      ext p
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp1, hp2⟩
        have hab : p = P.vtx (s % P.n) ∨ p = P.vtx ((s + L) % P.n) := by
          by_contra hcon
          rw [not_or] at hcon
          exact hch p (by rw [segment_comm]; exact hp2) hcon.1 hcon.2
            ⟨_, Nat.mod_lt _ hn, hp1⟩
        refine ⟨?_, hab.symm⟩
        rcases hab with rfl | rfl
        · exact eq_endpoint_of_vtx_mem_edge hP (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hp1
        · exact eq_endpoint_of_vtx_mem_edge hP (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hp1
      · rintro ⟨h1, h2⟩
        constructor
        · rcases h1 with rfl | rfl
          · exact left_mem_segment _ _
          · exact right_mem_segment _ _
        · rcases h2 with rfl | rfl
          · exact left_mem_segment _ _
          · exact right_mem_segment _ _
    intro i j hi hj hij
    rw [n_arc] at hi hj
    rcases Nat.lt_or_ge i L with hiL | hiL <;> rcases Nat.lt_or_ge j L with hjL | hjL
    · rw [edge_arc P s L hiL, edge_arc P s L hjL, commonEndpoints_arc P s L hiL hjL]
      exact hP.2.2 _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
        (fun h => hij (rot_index_inj (by omega) (by omega) h))
    · have : j = L := by omega
      subst this
      exact key i hiL
    · have : i = L := by omega
      subst this
      rw [Set.inter_comm, commonEndpoints_comm, key j hjL]
    · omega

/-- **The arc of a diagonal is simple.** -/
theorem simple_arc (hP : P.Simple) (hd : IsDiagonal P s L) : (P.arc s L).Simple :=
  simple_arc_of_chord P s L hP hd.1 (by have := hd.2.1; omega) hd.2.2

/-- **The complementary arc of a diagonal is simple.** -/
theorem simple_arc_compl (hP : P.Simple) (hd : IsDiagonal P s L) :
    (P.arc ((s + L) % P.n) (P.n - L)).Simple :=
  simple_arc P _ _ hP (isDiagonal_compl P s L hd)

/-! ### Boundaries -/

/-- The boundary of the arc lies in the boundary of `P` together with the chord. -/
theorem boundary_arc_subset (hn : 0 < P.n) :
    (P.arc s L).boundary ⊆ P.boundary ∪ segment (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) := by
  intro p hp
  rcases (mem_boundary_arc_iff P s L).1 hp with ⟨i, _, hp⟩ | hp
  · exact Or.inl ⟨_, Nat.mod_lt _ hn, hp⟩
  · exact Or.inr hp

/-- The boundary of `P` lies in the union of the boundaries of the two arcs. -/
theorem boundary_subset_arcs (hL : L ≤ P.n) (hn : 0 < P.n) :
    P.boundary ⊆ (P.arc s L).boundary ∪ (P.arc ((s + L) % P.n) (P.n - L)).boundary := by
  rintro p ⟨j, hj, hp⟩
  obtain ⟨i, hi, hij⟩ := exists_rot_index hn s j hj
  rcases Nat.lt_or_ge i L with hiL | hiL
  · exact Or.inl ((mem_boundary_arc_iff P s L).2 (Or.inl ⟨i, hiL, by rw [hij]; exact hp⟩))
  · refine Or.inr ((mem_boundary_arc_iff P _ _).2 (Or.inl ⟨i - L, by omega, ?_⟩))
    rw [compl_arc_index, show s + L + (i - L) = s + i by omega, hij]
    exact hp

/-- The chord lies in the boundary of the arc. -/
theorem chord_subset_boundary_arc :
    segment (P.vtx ((s + L) % P.n)) (P.vtx (s % P.n)) ⊆ (P.arc s L).boundary :=
  fun _ hp => (mem_boundary_arc_iff P s L).2 (Or.inr hp)

/-! ### Triangles of an arc -/

/-- A triangle of the arc with indices `≤ L` has the same point set as its relabelling. -/
theorem triSet_arc {t : Polygon.Triangle} (h : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    (P.arc s L).triSet t = P.triSet (relabel s P.n t) := by
  unfold Polygon.triSet Polygon.triVertices
  rw [vtx_arc P s L h.1, vtx_arc P s L h.2.1, vtx_arc P s L h.2.2]
  rfl

/-- A triangle of the arc with indices `≤ L` has the same vertex set as its relabelling. -/
theorem triVertices_arc {t : Polygon.Triangle} (h : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    (P.arc s L).triVertices t = P.triVertices (relabel s P.n t) := by
  unfold Polygon.triVertices
  rw [vtx_arc P s L h.1, vtx_arc P s L h.2.1, vtx_arc P s L h.2.2]
  rfl

/-- The indices of a valid triangle of the arc are at most `L`. -/
theorem index_le_of_validTriangle_arc {t : Polygon.Triangle}
    (h : (P.arc s L).validTriangle t) : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L := by
  obtain ⟨h1, h2, h3, -⟩ := h
  rw [n_arc] at h1 h2 h3
  omega

/-- A valid triangle of the arc relabels to a valid triangle of `P`. -/
theorem validTriangle_arc (hn : 0 < P.n) {t : Polygon.Triangle}
    (h : (P.arc s L).validTriangle t) : P.validTriangle (relabel s P.n t) := by
  have hle := index_le_of_validTriangle_arc P s L h
  refine ⟨Nat.mod_lt _ hn, Nat.mod_lt _ hn, Nat.mod_lt _ hn, ?_⟩
  have h4 := h.2.2.2
  rw [vtx_arc P s L hle.1, vtx_arc P s L hle.2.1, vtx_arc P s L hle.2.2] at h4
  exact h4

end

end ArtGallery.Existence
