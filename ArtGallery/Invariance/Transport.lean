module

public import ArtGallery.Existence.Main

/-!
# Invariance of `Triangulates` under relabelling

The specification's `Polygon.Triangulates P T` only looks at

* the number of vertices `P.n`,
* the vertex points `P.vtx i` for valid indices `i < P.n`, and
* the filled region `P.filled`,

so any two polygons that agree on these data up to a bijective relabelling of the indices have
"the same" triangulations.  This file proves that transport principle once
(`triangulates_transport`, `triangulates_transport_iff`) and derives the two invariances
that do not move the polygon at all:

* **permutations of the output list** (`triangulates_perm_iff`):
  `T.Perm T' → (P.Triangulates T ↔ P.Triangulates T')`;
* **permutations of the three indices of each triangle** (`triangulates_triPerm_iff`): if `T'`
  is obtained from `T` by permuting the corners of every triangle (`List.Forall₂ TriPerm T T'`,
  where `TriPerm t t'` says `[t.1, t.2.1, t.2.2]` is a permutation of `[t'.1, t'.2.1, t'.2.2]`),
  then `P.Triangulates T ↔ P.Triangulates T'`.

The geometric invariances (cyclic shift, reversal, affine maps) are in
`ArtGallery.Invariance.Shift` and `ArtGallery.Invariance.Affine`.

Provenance: adapted from `Chazelle/Hardening/Invariance/Transport.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery` and the directory is moved.
-/

@[expose] public section

namespace ArtGallery.Hardening.Invariance

open ArtGallery

/-! ### Relabelling triangles -/

/-- Apply an index map to the three corners of a triangle. -/
def triMap (σ : ℕ → ℕ) (t : Polygon.Triangle) : Polygon.Triangle := (σ t.1, σ t.2.1, σ t.2.2)

@[simp] theorem triMap_fst (σ : ℕ → ℕ) (t : Polygon.Triangle) : (triMap σ t).1 = σ t.1 := rfl

@[simp] theorem triMap_snd_fst (σ : ℕ → ℕ) (t : Polygon.Triangle) :
    (triMap σ t).2.1 = σ t.2.1 := rfl

@[simp] theorem triMap_snd_snd (σ : ℕ → ℕ) (t : Polygon.Triangle) :
    (triMap σ t).2.2 = σ t.2.2 := rfl

/-- Relabelling twice is relabelling by the composite. -/
theorem triMap_triMap (σ τ : ℕ → ℕ) (t : Polygon.Triangle) :
    triMap σ (triMap τ t) = triMap (σ ∘ τ) t := rfl

/-- The indices of a triangle are all below `n`. -/
def TriInRange (n : ℕ) (t : Polygon.Triangle) : Prop := t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

/-- A valid triangle has its indices in range. -/
theorem triInRange_of_valid {P : Polygon} {t : Polygon.Triangle} (h : P.validTriangle t) :
    TriInRange P.n t :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Relabelling by a map that is the identity on `range n` fixes in-range triangles. -/
theorem triMap_eq_self {n : ℕ} {σ : ℕ → ℕ} (hσ : ∀ i < n, σ i = i) {t : Polygon.Triangle}
    (ht : TriInRange n t) : triMap σ t = t := by
  obtain ⟨h1, h2, h3⟩ := ht
  simp only [triMap, hσ _ h1, hσ _ h2, hσ _ h3]

/-- Relabelling a list of in-range triangles by a map that is the identity on `range n`. -/
theorem map_triMap_eq_self {n : ℕ} {σ : ℕ → ℕ} (hσ : ∀ i < n, σ i = i)
    {T : List Polygon.Triangle} (hT : ∀ t ∈ T, TriInRange n t) : T.map (triMap σ) = T := by
  conv_rhs => rw [← List.map_id T]
  exact List.map_congr_left (fun t ht => triMap_eq_self hσ (hT t ht))

/-! ### The transport principle -/

section Transport

variable {P Q : Polygon} {σ : ℕ → ℕ}

theorem triVertices_transport (hv : ∀ i < P.n, Q.vtx i = P.vtx (σ i)) {t : Polygon.Triangle}
    (ht : TriInRange P.n t) : Q.triVertices t = P.triVertices (triMap σ t) := by
  unfold Polygon.triVertices
  rw [hv _ ht.1, hv _ ht.2.1, hv _ ht.2.2]
  rfl

theorem triSet_transport (hv : ∀ i < P.n, Q.vtx i = P.vtx (σ i)) {t : Polygon.Triangle}
    (ht : TriInRange P.n t) : Q.triSet t = P.triSet (triMap σ t) := by
  unfold Polygon.triSet
  rw [triVertices_transport hv ht]

theorem validTriangle_transport (hn : Q.n = P.n) (hσ : ∀ i < P.n, σ i < P.n)
    (hv : ∀ i < P.n, Q.vtx i = P.vtx (σ i)) {t : Polygon.Triangle} (h : Q.validTriangle t) :
    P.validTriangle (triMap σ t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hn] at h1 h2 h3
  refine ⟨hσ _ h1, hσ _ h2, hσ _ h3, ?_⟩
  rw [hv _ h1, hv _ h2, hv _ h3] at h4
  exact h4

/-- **Transport of triangulations.**  If `Q` has as many vertices as `P`, the same filled
region, and `Q.vtx i = P.vtx (σ i)` for every valid index `i`, where `σ` maps valid indices to
valid indices, then every triangulation `T` of `Q` relabels by `σ` to a triangulation of `P`. -/
theorem triangulates_transport (hn : Q.n = P.n) (hf : Q.filled = P.filled)
    (hσ : ∀ i < P.n, σ i < P.n) (hv : ∀ i < P.n, Q.vtx i = P.vtx (σ i))
    {T : List Polygon.Triangle} (hT : Q.Triangulates T) : P.Triangulates (T.map (triMap σ)) := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hconf⟩ := hT
  have hidx : ∀ t ∈ T, TriInRange P.n t := fun t ht => hn ▸ triInRange_of_valid (hvalid t ht)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact validTriangle_transport hn hσ hv (hvalid t' ht')
  · rw [List.length_map, ← hn]; exact hcount
  · rw [← hf, ← hunion]
    ext p
    simp only [Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩
      exact ⟨t, ht, by rw [triSet_transport hv (hidx t ht)]; exact hp⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨_, ⟨t, ht, rfl⟩, by rw [← triSet_transport hv (hidx t ht)]; exact hp⟩
  · rw [List.pairwise_map]
    refine hdisj.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_transport hv (hidx a ha), triSet_transport hv (hidx b hb)] at h
    exact h
  · rw [List.pairwise_map]
    refine hconf.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_transport hv (hidx a ha), triSet_transport hv (hidx b hb),
      triVertices_transport hv (hidx a ha), triVertices_transport hv (hidx b hb)] at h
    exact h

/-- **Transport of triangulations, both directions.**  With `σ`, `τ` mutually inverse
bijections of `range n` and `Q.vtx i = P.vtx (σ i)`, a list `T` of triangles triangulates `P`
iff its relabelling by `τ` triangulates `Q`, for lists whose indices are in range.  (Without the
range hypothesis the backward direction can fail: an out-of-range index may relabel to a valid
one.) -/
theorem triangulates_transport_iff (hn : Q.n = P.n) (hf : Q.filled = P.filled)
    {τ : ℕ → ℕ} (hσ : ∀ i < P.n, σ i < P.n) (hτ : ∀ i < P.n, τ i < P.n)
    (hστ : ∀ i < P.n, σ (τ i) = i) (hv : ∀ i < P.n, Q.vtx i = P.vtx (σ i))
    {T : List Polygon.Triangle} (hT : ∀ t ∈ T, TriInRange P.n t) :
    P.Triangulates T ↔ Q.Triangulates (T.map (triMap τ)) := by
  have hv' : ∀ i < Q.n, P.vtx i = Q.vtx (τ i) := by
    intro i hi
    rw [hn] at hi
    rw [hv _ (hτ i hi), hστ i hi]
  constructor
  · intro h
    exact triangulates_transport hn.symm hf.symm (fun i hi => hn ▸ hτ i (hn ▸ hi)) hv' h
  · intro h
    have := triangulates_transport hn hf hσ hv h
    rwa [List.map_map, show triMap σ ∘ triMap τ = triMap (σ ∘ τ) from rfl,
      map_triMap_eq_self (σ := σ ∘ τ) (fun i hi => hστ i hi) hT] at this

end Transport

/-! ### Permutations of the output list -/

/-- **Permuting the output list.**  Triangulating does not depend on the order of the
output triangles. -/
theorem triangulates_perm_iff {P : Polygon} {T T' : List Polygon.Triangle} (hp : T.Perm T') :
    P.Triangulates T ↔ P.Triangulates T' :=
  ⟨fun h => Existence.triangulates_of_perm h hp, fun h => Existence.triangulates_of_perm h hp.symm⟩

/-! ### Permutations of the corners of each triangle -/

/-- `t'` lists the same three corners as `t`, in some order. -/
def TriPerm (t t' : Polygon.Triangle) : Prop :=
  [t.1, t.2.1, t.2.2].Perm [t'.1, t'.2.1, t'.2.2]

/-- The six orders of three corners. -/
theorem triPerm_cases {t t' : Polygon.Triangle} (h : TriPerm t t') :
    t' = (t.1, t.2.1, t.2.2) ∨ t' = (t.1, t.2.2, t.2.1) ∨ t' = (t.2.1, t.1, t.2.2) ∨
      t' = (t.2.1, t.2.2, t.1) ∨ t' = (t.2.2, t.1, t.2.1) ∨ t' = (t.2.2, t.2.1, t.1) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨x, y, z⟩ := t'
  have := List.mem_permutations'.2 h.symm
  simp [List.permutations', List.permutations'Aux] at this
  simp only [Prod.mk.injEq]
  tauto

/-- Permuting the corners does not change the vertex set. -/
theorem triVertices_of_triPerm (P : Polygon) {t t' : Polygon.Triangle} (h : TriPerm t t') :
    P.triVertices t' = P.triVertices t := by
  rcases triPerm_cases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · unfold Polygon.triVertices; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;>
      tauto

/-- Permuting the corners does not change the closed triangle. -/
theorem triSet_of_triPerm (P : Polygon) {t t' : Polygon.Triangle} (h : TriPerm t t') :
    P.triSet t' = P.triSet t := by
  unfold Polygon.triSet; rw [triVertices_of_triPerm P h]

/-- Permuting the corners preserves validity (the determinant changes at most by sign). -/
theorem validTriangle_of_triPerm (P : Polygon) {t t' : Polygon.Triangle} (h : TriPerm t t')
    (hv : P.validTriangle t) : P.validTriangle t' := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  rcases triPerm_cases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h1, h2, h3, h4⟩
  · exact ⟨h1, h3, h2, by rw [Geometry.det_swap23]; exact neg_ne_zero.2 h4⟩
  · exact ⟨h2, h1, h3, by rw [Geometry.det_swap12]; exact neg_ne_zero.2 h4⟩
  · exact ⟨h2, h3, h1, by rw [Geometry.det_cyclic]; exact h4⟩
  · exact ⟨h3, h1, h2, by rw [Geometry.det_cyclic_right]; exact h4⟩
  · exact ⟨h3, h2, h1, by rw [Geometry.det_swap13]; exact neg_ne_zero.2 h4⟩

/-- `TriPerm` is symmetric. -/
theorem TriPerm.symm {t t' : Polygon.Triangle} (h : TriPerm t t') : TriPerm t' t :=
  List.Perm.symm h

/-- Lists related elementwise by a relation that preserves a function have equal images. -/
theorem map_eq_of_forall₂ {α β : Type} {R : α → α → Prop} (f : α → β)
    (hf : ∀ a b, R a b → f b = f a) {T T' : List α} (h : List.Forall₂ R T T') :
    T'.map f = T.map f := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hf _ _ hab, ih]

/-- **Permuting the corners of the triangles, one direction.** -/
theorem triangulates_of_triPerm {P : Polygon} {T T' : List Polygon.Triangle}
    (h : List.Forall₂ TriPerm T T') (hT : P.Triangulates T) : P.Triangulates T' := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hconf⟩ := hT
  have hV := map_eq_of_forall₂ P.triVertices (fun a b hab => triVertices_of_triPerm P hab) h
  have hS := map_eq_of_forall₂ P.triSet (fun a b hab => triSet_of_triPerm P hab) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- validity: every `t' ∈ T'` is a corner permutation of some `t ∈ T`
    have : ∀ t' ∈ T', ∃ t ∈ T, TriPerm t t' := by
      clear hV hS hunion hdisj hconf hcount hvalid
      induction h with
      | nil => simp
      | @cons a b l l' hab _ ih =>
        intro t' ht'
        rcases List.mem_cons.1 ht' with rfl | ht'
        · exact ⟨a, List.mem_cons_self .., hab⟩
        · obtain ⟨t, ht, htt⟩ := ih t' ht'
          exact ⟨t, List.mem_cons_of_mem _ ht, htt⟩
    intro t' ht'
    obtain ⟨t, ht, htt⟩ := this t' ht'
    exact validTriangle_of_triPerm P htt (hvalid t ht)
  · rw [← h.length_eq]; exact hcount
  · rw [← hunion]
    ext p
    simp only [Set.mem_ofPred_eq]
    have e : ∀ L : List Polygon.Triangle, (∃ t ∈ L, p ∈ P.triSet t) ↔ ∃ S ∈ L.map P.triSet, p ∈ S :=
      fun L => by simp
    rw [e, e, hS]
  · rw [← List.pairwise_map (f := P.triSet) (R := fun S S' => Disjoint (interior S) (interior S'))]
      at hdisj ⊢
    rw [hS]; exact hdisj
  · have e : ∀ L : List Polygon.Triangle,
        L.Pairwise (fun s t => P.triSet s ∩ P.triSet t =
          convexHull ℝ (P.triVertices s ∩ P.triVertices t)) ↔
        (L.map P.triVertices).Pairwise (fun S S' => convexHull ℝ S ∩ convexHull ℝ S' =
          convexHull ℝ (S ∩ S')) := fun L => by
      rw [List.pairwise_map]; rfl
    rw [e] at hconf ⊢
    rw [hV]; exact hconf

/-- **Permuting the corners of the triangles.**  If `T'` is obtained from `T` by permuting
the three indices of each triangle (possibly differently for different triangles), then `T`
triangulates `P` iff `T'` does. -/
theorem triangulates_triPerm_iff {P : Polygon} {T T' : List Polygon.Triangle}
    (h : List.Forall₂ TriPerm T T') : P.Triangulates T ↔ P.Triangulates T' :=
  ⟨triangulates_of_triPerm h,
    triangulates_of_triPerm (h.flip.imp fun _ _ hab => TriPerm.symm hab)⟩

end ArtGallery.Hardening.Invariance
