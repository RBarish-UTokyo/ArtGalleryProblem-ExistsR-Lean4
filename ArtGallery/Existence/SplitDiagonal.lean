module

public import ArtGallery.Existence.Split
public import ArtGallery.Existence.Combine

/-!
# Splitting along an interior diagonal

For a simple polygon `P` and a diagonal `(s, L)` (`IsDiagonal P s L`) whose chord lies in the
filled region of `P` (`hin`), the abstract splitting lemma `split_filled` applied to the two arcs
`A₁ = P.arc s L` and `A₂ = P.arc ((s + L) % n) (n - L)` yields the three geometric hypotheses of
`weakTriangulates_combine`:

* `filled_eq_union_arcs`: `P.filled = A₁.filled ∪ A₂.filled`;
* `filled_arcs_meet_on_chord`: the filled regions of the arcs meet only on the chord;
* `interior_arcs_disjoint`: the interiors of the filled regions of the arcs are disjoint.

The XOR hypothesis of the splitting lemma is `parity_split` combined with `mem_filled_iff` for
`P` and the two (simple) arcs, and the boundary hypotheses are `boundary_arc_subset` (with `hin`)
and `boundary_subset_arcs`.  The boundaries of the two arcs meet only on the chord
(`boundary_arc_inter`): the `P`-edges of the two arcs are distinct edges of `P`, which meet only
in common vertices, and the only vertices common to the two arcs are the chord's endpoints.

`weakTriangulates_of_diagonal` packages this with `weakTriangulates_combine`.

Provenance: adapted from `Chazelle/Existence/SplitDiagonal.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open ArtGallery.Jordan

variable (P : Polygon) (s L : ℕ)

/-! ### Vertices common to the two arcs -/

/-- A vertex `(s + k) % n` with `k ≤ L` which coincides with a vertex `(s + m) % n` with
`L ≤ m ≤ n` is an endpoint of the chord. -/
theorem vtx_eq_chord_endpoint_of_common {P : Polygon} (hP : P.Simple) {s L : ℕ}
    (hL : L ≤ P.n) {k m : ℕ} (hk : k ≤ L) (hm₁ : L ≤ m) (hm₂ : m ≤ P.n)
    (h : P.vtx ((s + k) % P.n) = P.vtx ((s + m) % P.n)) :
    P.vtx ((s + k) % P.n) = P.vtx (s % P.n) ∨ P.vtx ((s + k) % P.n) = P.vtx ((s + L) % P.n) := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hidx := hP.2.1 _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h
  by_cases hkL : k = L
  · exact Or.inr (by rw [hkL])
  rcases Nat.lt_or_ge m P.n with hm | hm
  · have := rot_index_inj (n := P.n) (s := s) (i := k) (j := m) (by omega) hm hidx
    omega
  · have hmn : m = P.n := by omega
    rw [hmn, Nat.add_mod_right] at hidx
    have := rot_index_inj (n := P.n) (s := s) (i := k) (j := 0) (by omega) hn
      (by rw [hidx, Nat.add_zero])
    subst this
    exact Or.inl (by rw [Nat.add_zero])

/-- **The boundaries of the two arcs meet only on the chord.** -/
theorem boundary_arc_inter {P : Polygon} (hP : P.Simple) {s L : ℕ} (hL : L ≤ P.n) :
    (P.arc s L).boundary ∩ (P.arc ((s + L) % P.n) (P.n - L)).boundary ⊆
      segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) := by
  have hn : 0 < P.n := by have := hP.1; omega
  rintro p ⟨hp₁, hp₂⟩
  rw [mem_boundary_arc_iff] at hp₁ hp₂
  rw [compl_arc_last_index P s L hL, Nat.mod_mod] at hp₂
  rcases hp₁ with ⟨i, hi, hpi⟩ | hpc
  · rcases hp₂ with ⟨j, hj, hpj⟩ | hpc
    · -- `p` lies on two distinct edges of `P`, hence is a common vertex
      rw [compl_arc_index] at hpj
      have hij : (s + i) % P.n ≠ (s + L + j) % P.n := by
        intro h
        rw [Nat.add_assoc] at h
        have := rot_index_inj (by omega) (by omega) h
        omega
      have hmem : p ∈ P.edge ((s + i) % P.n) ∩ P.edge ((s + L + j) % P.n) := ⟨hpi, hpj⟩
      rw [hP.2.2 _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hij] at hmem
      obtain ⟨h₁, h₂⟩ := hmem
      rw [mod_add_one_mod] at h₁
      rw [mod_add_one_mod] at h₂
      simp only [Nat.add_assoc] at h₂
      have key : ∀ k m, k ≤ L → L ≤ m → m ≤ P.n → p = P.vtx ((s + k) % P.n) →
          p = P.vtx ((s + m) % P.n) →
          p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) := by
        intro k m hk hm₁ hm₂ hpk hpm
        rw [hpk]
        rcases vtx_eq_chord_endpoint_of_common hP hL hk hm₁ hm₂ (hpk ▸ hpm) with h | h
        · rw [h]; exact left_mem_segment _ _
        · rw [h]; exact right_mem_segment _ _
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact key i (L + j) hi.le (by omega) (by omega) h₁ h₂
      · exact key i (L + (j + 1)) hi.le (by omega) (by omega) h₁ h₂
      · exact key (i + 1) (L + j) (by omega) (by omega) (by omega) h₁ h₂
      · exact key (i + 1) (L + (j + 1)) (by omega) (by omega) (by omega) h₁ h₂
    · exact hpc
  · rw [segment_comm]; exact hpc

/-! ### The hypotheses of the splitting lemma -/

/-- The boundaries of the two arcs lie in the filled region of `P` when the chord does. -/
theorem boundary_arcs_subset_filled (hn : 0 < P.n) (hL : L ≤ P.n)
    (hin : segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    (P.arc s L).boundary ∪ (P.arc ((s + L) % P.n) (P.n - L)).boundary ⊆ P.filled := by
  rintro p (hp | hp)
  · rcases boundary_arc_subset P s L hn hp with h | h
    · exact boundary_subset_filled P h
    · rw [segment_comm] at h; exact hin h
  · rcases boundary_arc_subset P _ _ hn hp with h | h
    · exact boundary_subset_filled P h
    · rw [compl_arc_last_index P s L hL, Nat.mod_mod] at h
      exact hin h

/-- Off the three boundaries, a point is filled in `P` exactly when it is filled in exactly one
of the two arcs. -/
theorem filled_xor_arcs (hP : P.Simple) (hd : IsDiagonal P s L) (z : Point)
    (hzP : z ∉ P.boundary) (hz₁ : z ∉ (P.arc s L).boundary)
    (hz₂ : z ∉ (P.arc ((s + L) % P.n) (P.n - L)).boundary) :
    (z ∈ P.filled ↔ (z ∈ (P.arc s L).filled ↔ z ∉ (P.arc ((s + L) % P.n) (P.n - L)).filled)) := by
  have hL : L ≤ P.n := by have := hd.2.1; omega
  rw [mem_filled_iff hP hzP, mem_filled_iff (simple_arc P s L hP hd) hz₁,
    mem_filled_iff (simple_arc_compl P s L hP hd) hz₂, parity_split P s L hL z]
  generalize parity (P.arc s L) z = a
  generalize parity (P.arc ((s + L) % P.n) (P.n - L)) z = b
  cases a <;> cases b <;> simp

/-- **The filled region of `P` is the union of the filled regions of the two arcs.** -/
theorem filled_eq_union_arcs (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    P.filled = (P.arc s L).filled ∪ (P.arc ((s + L) % P.n) (P.n - L)).filled := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hL : L ≤ P.n := by have := hd.2.1; omega
  exact split_filled_eq_union hP (simple_arc P s L hP hd) (simple_arc_compl P s L hP hd)
    (boundary_arcs_subset_filled P s L hn hL hin) (boundary_subset_arcs P s L hL hn)
    (filled_xor_arcs P s L hP hd)

/-- **The interiors of the filled regions of the two arcs are disjoint.** -/
theorem interior_arcs_disjoint (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    Disjoint (interior (P.arc s L).filled)
      (interior (P.arc ((s + L) % P.n) (P.n - L)).filled) := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hL : L ≤ P.n := by have := hd.2.1; omega
  exact split_interior_disjoint hP (simple_arc P s L hP hd) (simple_arc_compl P s L hP hd)
    (boundary_arcs_subset_filled P s L hn hL hin) (boundary_subset_arcs P s L hL hn)
    (filled_xor_arcs P s L hP hd)

/-- **The filled regions of the two arcs meet only on the chord.** -/
theorem filled_arcs_meet_on_chord (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ((s + L) % P.n) (P.n - L)).filled →
      p ∈ segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  have hL : L ≤ P.n := by have := hd.2.1; omega
  intro p hp₁ hp₂
  exact boundary_arc_inter hP hL
    (split_filled_inter_subset hP (simple_arc P s L hP hd) (simple_arc_compl P s L hP hd)
      (boundary_arcs_subset_filled P s L hn hL hin) (boundary_subset_arcs P s L hL hn)
      (filled_xor_arcs P s L hP hd) ⟨hp₁, hp₂⟩)

/-! ### Combining along an interior diagonal -/

/-- **Weak triangulations of the two arcs of an interior diagonal combine to a weak
triangulation of `P`.** -/
theorem weakTriangulates_of_diagonal {P : Polygon} {s L : ℕ} (hP : P.Simple)
    (hd : IsDiagonal P s L)
    (hin : segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled)
    {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates (P.arc s L) T₁)
    (h₂ : WeakTriangulates (P.arc ((s + L) % P.n) (P.n - L)) T₂) :
    WeakTriangulates P (T₁.map (relabel s P.n) ++ T₂.map (relabel ((s + L) % P.n) P.n)) :=
  weakTriangulates_combine hd h₁ h₂ (filled_eq_union_arcs P s L hP hd hin)
    (filled_arcs_meet_on_chord P s L hP hd hin) (interior_arcs_disjoint P s L hP hd hin)

end

end ArtGallery.Existence
