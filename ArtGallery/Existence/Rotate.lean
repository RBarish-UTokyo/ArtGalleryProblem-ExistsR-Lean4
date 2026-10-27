module

public import ArtGallery.Jordan.Parity
public import Mathlib.Data.Nat.ModEq

/-!
# Rotating the vertex list of a polygon

`P.rotate s` is the polygon with the same vertices as `P`, listed starting from vertex `s`:
its `i`-th vertex is `P.vtx ((s + i) % P.n)`.  Rotation changes nothing geometric: the edges
are the edges of `P` (reindexed by the bijection `i ↦ (s + i) % n` of `range n`), hence the
boundary, the filled region, simplicity, the crossing sum and the parity are all preserved,
and a triangulation of `P.rotate s` relabels (`Polygon.relabel s n`) to a triangulation of
`P`.

Index arithmetic helpers: `exists_rot_index` (surjectivity of `i ↦ (s + i) % n` on
`range n`), `rot_index_inj` (injectivity), `sum_range_rot` (reindexing a sum over `range n`).

Provenance: adapted from `Chazelle/Existence/Rotate.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open ArtGallery.Jordan

/-! ### Index arithmetic -/

/-- `(s + i) % n + 1` and `s + i + 1` agree modulo `n`. -/
theorem mod_add_one_mod (s i n : ℕ) : ((s + i) % n + 1) % n = (s + (i + 1)) % n := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Surjectivity of `i ↦ (s + i) % n` on `range n`. -/
theorem exists_rot_index {n : ℕ} (hn : 0 < n) (s j : ℕ) (hj : j < n) :
    ∃ i, i < n ∧ (s + i) % n = j := by
  refine ⟨(j + n - s % n) % n, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.add_mod_mod]
  have h1 : s % n < n := Nat.mod_lt s hn
  have h2 : n * (s / n) + s % n = s := Nat.div_add_mod s n
  have h3 : s + (j + n - s % n) = n * (s / n + 1) + j := by
    rw [Nat.mul_succ]; omega
  rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- Injectivity of `i ↦ (s + i) % n` on `range n`. -/
theorem rot_index_inj {n s i j : ℕ} (hi : i < n) (hj : j < n) (h : (s + i) % n = (s + j) % n) :
    i = j :=
  (Nat.ModEq.add_left_cancel' s h).eq_of_lt_of_lt hi hj

/-- Reindexing a sum over `range n` by the rotation `i ↦ (s + i) % n`. -/
theorem sum_range_rot {M : Type} [AddCommMonoid M] (f : ℕ → M) (s n : ℕ) :
    ∑ i ∈ Finset.range n, f ((s + i) % n) = ∑ i ∈ Finset.range n, f i := by
  induction s with
  | zero =>
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.zero_add, Nat.mod_eq_of_lt hi]
  | succ s ih =>
    rw [← ih, ← sum_range_succ_mod (fun i => f ((s + i) % n)) n]
    apply Finset.sum_congr rfl
    intro i _
    show f ((s + 1 + i) % n) = f ((s + (i + 1) % n) % n)
    rw [Nat.add_mod_mod, Nat.add_assoc, Nat.add_comm 1 i]

/-! ### The rotated polygon -/

/-- The polygon `P` with its vertex list rotated to start at vertex `s`. -/
def _root_.ArtGallery.Polygon.rotate (P : ArtGallery.Polygon) (s : ℕ) : ArtGallery.Polygon :=
  ⟨(List.range P.n).map fun i => P.vtx ((s + i) % P.n)⟩

/-- Relabelling a triangle by the index map `i ↦ (s + i) % n`. -/
def relabel (s n : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  ((s + t.1) % n, (s + t.2.1) % n, (s + t.2.2) % n)

@[simp] theorem relabel_fst (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).1 = (s + t.1) % n := rfl

@[simp] theorem relabel_snd_fst (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).2.1 = (s + t.2.1) % n := rfl

@[simp] theorem relabel_snd_snd (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).2.2 = (s + t.2.2) % n := rfl

variable (P : Polygon) (s : ℕ)

/-- The rotated polygon has the same number of vertices. -/
@[simp] theorem n_rotate : (P.rotate s).n = P.n := by
  simp [Polygon.rotate, Polygon.n]

/-- Vertex `i < n` of the rotated polygon is vertex `(s + i) % n` of `P`. -/
theorem vtx_rotate {i : ℕ} (hi : i < P.n) : (P.rotate s).vtx i = P.vtx ((s + i) % P.n) := by
  simp [Polygon.rotate, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- Vertex `i ≥ n` of the rotated polygon is the origin. -/
theorem vtx_rotate_of_le {i : ℕ} (hi : P.n ≤ i) : (P.rotate s).vtx i = (0, 0) := by
  unfold Polygon.vtx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simpa [Polygon.rotate] using hi

/-- The successor vertex of the rotated polygon (modulus written as `P.n`). -/
theorem vtx_rotate_succ_n {i : ℕ} (hi : i < P.n) :
    (P.rotate s).vtx ((i + 1) % P.n) = P.vtx (((s + i) % P.n + 1) % P.n) := by
  rw [vtx_rotate P s (Nat.mod_lt _ (by omega)), Nat.add_mod_mod, mod_add_one_mod]

/-- The successor vertex of the rotated polygon. -/
theorem vtx_rotate_succ {i : ℕ} (hi : i < P.n) :
    (P.rotate s).vtx ((i + 1) % (P.rotate s).n) = P.vtx (((s + i) % P.n + 1) % P.n) := by
  rw [n_rotate, vtx_rotate_succ_n P s hi]

/-- Edge `i < n` of the rotated polygon is edge `(s + i) % n` of `P`. -/
theorem edge_rotate {i : ℕ} (hi : i < P.n) : (P.rotate s).edge i = P.edge ((s + i) % P.n) := by
  unfold Polygon.edge
  rw [vtx_rotate P s hi, vtx_rotate_succ P s hi]

/-- The common endpoints of two edges of the rotated polygon. -/
theorem commonEndpoints_rotate {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    (P.rotate s).commonEndpoints i j =
      P.commonEndpoints ((s + i) % P.n) ((s + j) % P.n) := by
  unfold Polygon.commonEndpoints
  rw [vtx_rotate P s hi, vtx_rotate P s hj, vtx_rotate_succ P s hi, vtx_rotate_succ P s hj]

/-- The boundary of the rotated polygon is the boundary of `P`. -/
theorem boundary_rotate : (P.rotate s).boundary = P.boundary := by
  ext p
  simp only [Polygon.boundary, Set.mem_ofPred_eq, n_rotate]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨(s + i) % P.n, Nat.mod_lt _ (by omega), (edge_rotate P s hi) ▸ hp⟩
  · rintro ⟨j, hj, hp⟩
    obtain ⟨i, hi, hij⟩ := exists_rot_index (by omega) s j hj
    exact ⟨i, hi, by rw [edge_rotate P s hi, hij]; exact hp⟩

/-- The filled region of the rotated polygon is the filled region of `P`. -/
theorem filled_rotate : (P.rotate s).filled = P.filled := by
  unfold Polygon.filled
  rw [boundary_rotate]

/-- The rotated polygon has the same triangle sets, for triangles with indices in range. -/
theorem triSet_rotate {t : Polygon.Triangle}
    (h : t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n) :
    (P.rotate s).triSet t = P.triSet (relabel s P.n t) := by
  unfold Polygon.triSet Polygon.triVertices
  rw [vtx_rotate P s h.1, vtx_rotate P s h.2.1, vtx_rotate P s h.2.2]
  rfl

/-- The rotated polygon has the same triangle vertex sets, for triangles with indices in
range. -/
theorem triVertices_rotate {t : Polygon.Triangle}
    (h : t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n) :
    (P.rotate s).triVertices t = P.triVertices (relabel s P.n t) := by
  unfold Polygon.triVertices
  rw [vtx_rotate P s h.1, vtx_rotate P s h.2.1, vtx_rotate P s h.2.2]
  rfl

/-- A valid triangle of the rotated polygon relabels to a valid triangle of `P`. -/
theorem validTriangle_rotate {t : Polygon.Triangle}
    (h : (P.rotate s).validTriangle t) : P.validTriangle (relabel s P.n t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [n_rotate] at h1 h2 h3
  have hn : 0 < P.n := by omega
  refine ⟨Nat.mod_lt _ hn, Nat.mod_lt _ hn, Nat.mod_lt _ hn, ?_⟩
  rw [vtx_rotate P s h1, vtx_rotate P s h2, vtx_rotate P s h3] at h4
  exact h4

/-- Rotation preserves simplicity. -/
theorem simple_rotate (hP : P.Simple) : (P.rotate s).Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by rw [n_rotate]; exact h3, ?_, ?_⟩
  · intro i j hi hj hij
    rw [n_rotate] at hi hj
    rw [vtx_rotate P s hi, vtx_rotate P s hj] at hij
    exact rot_index_inj hi hj (hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hij)
  · intro i j hi hj hij
    rw [n_rotate] at hi hj
    rw [edge_rotate P s hi, edge_rotate P s hj, commonEndpoints_rotate P s hi hj]
    exact hedge _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
      (fun h => hij (rot_index_inj hi hj h))

/-- Rotation preserves the crossing sum. -/
theorem crossSum_rotate (z : Point) : crossSum (P.rotate s) z = crossSum P z := by
  unfold crossSum
  rw [n_rotate]
  rw [← sum_range_rot (fun i => crossInd z (P.vtx i) (P.vtx ((i + 1) % P.n))) s P.n]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [vtx_rotate P s hi, vtx_rotate_succ_n P s hi]

/-- Rotation preserves the parity. -/
theorem parity_rotate (z : Point) : parity (P.rotate s) z = parity P z := by
  unfold parity
  rw [crossSum_rotate]

/-- A triangulation of `P.rotate s` relabels to a triangulation of `P`. -/
theorem triangulates_rotate {T : List Polygon.Triangle}
    (hT : (P.rotate s).Triangulates T) : P.Triangulates (T.map (relabel s P.n)) := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hconf⟩ := hT
  have hidx : ∀ t ∈ T, t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n := by
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := hvalid t ht
    rw [n_rotate] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact validTriangle_rotate P s (hvalid t' ht')
  · rw [List.length_map, ← n_rotate P s]; exact hcount
  · rw [← filled_rotate P s, ← hunion]
    ext p
    simp only [Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩
      exact ⟨t, ht, by rw [triSet_rotate P s (hidx t ht)]; exact hp⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨_, ⟨t, ht, rfl⟩, by rw [← triSet_rotate P s (hidx t ht)]; exact hp⟩
  · rw [List.pairwise_map]
    refine hdisj.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_rotate P s (hidx a ha), triSet_rotate P s (hidx b hb)] at h
    exact h
  · rw [List.pairwise_map]
    refine hconf.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_rotate P s (hidx a ha), triSet_rotate P s (hidx b hb),
      triVertices_rotate P s (hidx a ha), triVertices_rotate P s (hidx b hb)] at h
    exact h

end

end ArtGallery.Existence
