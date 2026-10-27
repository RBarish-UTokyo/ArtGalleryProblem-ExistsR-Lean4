module

public import ArtGallery.Hardness.Sec5.Corridor.CoverClassB

/-!
# Section 5: corridors — the floor slots (pieces)

* `Good.floor_edge_cases`: every edge of the floor chain is horizontal on `y = H` or one of the two
  sides of a witness slot (`dentS2 j`, `dentS4 j`);
* the **slot pieces** `hpSet (I.slot2Fs k)`, `hpSet (I.slot4Fs k)`: the slot triangles
  `{y ≤ H, κ − ε (y − H + 1/8) ≤ u₂ ≤ κ}` (`u₂ = x − (y − H)/2`) and
  `{y ≤ H, κ ≤ u₄ ≤ κ + (ε/2)(y − H + 1/4)}` (`u₄ = x − (y − H)/4`);
  `Good.slot2_subset`, `Good.slot4_subset`: they lie in the corridor region as soon as they contain
  an interior point of the corridor.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-- Edges of a dent chain started at a point of the line: horizontal, or a side of a dent. -/
theorem edges_dentChain {y₀ : ℝ} {c : Point} (hc : c.2 = y₀) :
    ∀ (ds : List Dent) (x : Point), x.2 = y₀ → (∀ d ∈ ds, d.A.2 = y₀ ∧ d.B.2 = y₀) →
      ∀ e ∈ edgesOf (x :: dentChain c ds), (e.1.2 = y₀ ∧ e.2.2 = y₀) ∨
        ∃ d ∈ ds, e = (d.A, d.T) ∨ e = (d.T, d.B) := by
  intro ds
  induction ds with
  | nil =>
    intro x hx _ e he
    simp only [dentChain, edgesOf_cons_cons, edgesOf_single, List.mem_cons, List.not_mem_nil,
      or_false] at he
    subst he; exact Or.inl ⟨hx, hc⟩
  | cons d ds ih =>
    intro x hx hds e he
    simp only [dentChain, edgesOf_cons_cons, List.mem_cons] at he
    have hdA := (hds d (by simp)).1
    have hdB := (hds d (by simp)).2
    rcases he with rfl | rfl | rfl | he
    · exact Or.inl ⟨hx, hdA⟩
    · exact Or.inr ⟨d, by simp, Or.inl rfl⟩
    · exact Or.inr ⟨d, by simp, Or.inr rfl⟩
    · rcases ih d.B hdB (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd')) e
        (by simpa [dentChain] using he) with h | ⟨d', hd', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', h⟩

namespace Input

variable {I : Input} {N : ℚ}

section Floor

variable (hg : I.Good N)
include hg

/-- The floor as a dent chain with explicit dents. -/
theorem Good.floor_dents : ∃ ds : List Dent,
    I.chainBefore.map ratPoint = ((I.S : ℝ), (I.H : ℝ)) :: dentChain ((I.S : ℝ) + 2, (I.H : ℝ)) ds ∧
      ∀ d ∈ ds, ∃ j < I.np, d = I.dentS2 j ∨ d = I.dentS4 j := by
  have hp := hg.np_pos
  have hp3 := hg.np_le
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with hnp | hnp | hnp
  · refine ⟨[I.dentS2 0, I.dentS4 0], ?_, ?_⟩
    · rw [chainBefore, floor_eq_one hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨0, by omega, Or.inl rfl⟩
      · exact ⟨0, by omega, Or.inr rfl⟩
  · refine ⟨[I.dentS2 1, I.dentS4 1, I.dentS2 0, I.dentS4 0], ?_, ?_⟩
    · rw [chainBefore, floor_eq_two hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨1, by omega, Or.inl rfl⟩
      · exact ⟨1, by omega, Or.inr rfl⟩
      · exact ⟨0, by omega, Or.inl rfl⟩
      · exact ⟨0, by omega, Or.inr rfl⟩
  · refine ⟨[I.dentS2 2, I.dentS2 1, I.dentS4 2, I.dentS4 1, I.dentS2 0, I.dentS4 0], ?_, ?_⟩
    · rw [chainBefore, floor_eq_three hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨2, by omega, Or.inl rfl⟩
      · exact ⟨1, by omega, Or.inl rfl⟩
      · exact ⟨2, by omega, Or.inr rfl⟩
      · exact ⟨1, by omega, Or.inr rfl⟩
      · exact ⟨0, by omega, Or.inl rfl⟩
      · exact ⟨0, by omega, Or.inr rfl⟩

/-- **The floor edges**: horizontal on `y = H`, or a side of a witness slot. -/
theorem Good.floor_edge_cases {e : Point × Point}
    (he : e ∈ edgesOf (I.chainBefore.map ratPoint)) :
    (e.1.2 = I.H ∧ e.2.2 = I.H) ∨ ∃ j < I.np,
      e = ((I.dentS2 j).A, (I.dentS2 j).T) ∨ e = ((I.dentS2 j).T, (I.dentS2 j).B) ∨
      e = ((I.dentS4 j).A, (I.dentS4 j).T) ∨ e = ((I.dentS4 j).T, (I.dentS4 j).B) := by
  obtain ⟨ds, hds, hmem⟩ := hg.floor_dents
  rw [hds] at he
  rcases edges_dentChain (y₀ := (I.H : ℝ)) (c := ((I.S : ℝ) + 2, (I.H : ℝ))) rfl ds _ rfl
    (fun d hd => by
      obtain ⟨j, -, rfl | rfl⟩ := hmem d hd
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩) e he with h | ⟨d, hd, h⟩
  · exact Or.inl h
  · obtain ⟨j, hj, rfl | rfl⟩ := hmem d hd
    · rcases h with h | h
      · exact Or.inr ⟨j, hj, Or.inl h⟩
      · exact Or.inr ⟨j, hj, Or.inr (Or.inl h)⟩
    · rcases h with h | h
      · exact Or.inr ⟨j, hj, Or.inr (Or.inr (Or.inl h))⟩
      · exact Or.inr ⟨j, hj, Or.inr (Or.inr (Or.inr h))⟩

end Floor

/-! ## The slot pieces -/

/-- The slope-2 slot of pair `k`: `y ≤ H`, `u₂ ≤ κ`, `u₂ ≥ κ − ε (y − H + 1/8)`. -/
noncomputable def slot2Fs (I : Input) (k : ℕ) : List Aff :=
  [⟨0, -1, (I.H : ℝ)⟩, ⟨-1, 1 / 2, (I.kx k 2 : ℝ) - (I.H : ℝ) / 2⟩,
    ⟨1, (I.ε : ℝ) - 1 / 2, (I.H : ℝ) / 2 - (I.kx k 2 : ℝ) - (I.ε : ℝ) * I.H + (I.ε : ℝ) / 8⟩]

/-- The slope-4 slot of pair `k`: `y ≤ H`, `u₄ ≥ κ`, `u₄ ≤ κ + (ε/2)(y − H + 1/4)`. -/
noncomputable def slot4Fs (I : Input) (k : ℕ) : List Aff :=
  [⟨0, -1, (I.H : ℝ)⟩, ⟨1, -1 / 4, (I.H : ℝ) / 4 - (I.kx k 4 : ℝ)⟩,
    ⟨-1, (I.ε : ℝ) / 2 + 1 / 4,
      -((I.ε : ℝ) / 2) * I.H + (I.ε : ℝ) / 8 - (I.H : ℝ) / 4 + (I.kx k 4 : ℝ)⟩]

theorem mem_slot2_iff {k : ℕ} {z : Point} :
    z ∈ hpSet (I.slot2Fs k) ↔ z.2 ≤ I.H ∧ z.1 - (z.2 - I.H) / 2 ≤ (I.kx k 2 : ℝ) ∧
      (I.kx k 2 : ℝ) - (I.ε : ℝ) * (z.2 - I.H + 1 / 8) ≤ z.1 - (z.2 - I.H) / 2 := by
  simp only [hpSet, slot2Fs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Aff.ev, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by nlinarith⟩

theorem mem_slot4_iff {k : ℕ} {z : Point} :
    z ∈ hpSet (I.slot4Fs k) ↔ z.2 ≤ I.H ∧ (I.kx k 4 : ℝ) ≤ z.1 - (z.2 - I.H) / 4 ∧
      z.1 - (z.2 - I.H) / 4 ≤ (I.kx k 4 : ℝ) + (I.ε : ℝ) / 2 * (z.2 - I.H + 1 / 4) := by
  simp only [hpSet, slot4Fs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Aff.ev, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by nlinarith⟩

section Slots

variable (hg : I.Good N)
include hg

/-- Key facts: positions and separation of the slot keys. -/
theorem Good.keys {j k : ℕ} (hj : j < I.np) (hk : k < I.np) :
    ((I.kx j 2 : ℝ) < (I.kx k 4 : ℝ) - 1 / 10 ∨ (I.kx k 4 : ℝ) + 1 / 2 < (I.kx j 2 : ℝ)) ∧
    (j ≠ k → (I.kx j 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx k 2 : ℝ) ∨
      (I.kx k 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 2 : ℝ)) ∧
    (j ≠ k → (I.kx j 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx k 4 : ℝ) ∨
      (I.kx k 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 4 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj1 <;> rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have a := hg.kx_zero_two hj; have b := hg.kx_zero_four hk
      have a' := rat_cast_le_of (abs_le.1 a).1; have a'' := rat_cast_le_of (abs_le.1 a).2
      have b' := rat_cast_le_of (abs_le.1 b).1; have b'' := rat_cast_le_of (abs_le.1 b).2
      push_cast at a' a'' b' b''
      left; linarith
    · have a := hg.kx_zero_two hj; have b := hg.kx_four hk hk1
      have a' := rat_cast_le_of (abs_le.1 a).1; have a'' := rat_cast_le_of (abs_le.1 a).2
      have b' := rat_cast_le_of (abs_le.1 b).1; have b'' := rat_cast_le_of (abs_le.1 b).2
      push_cast at a' a'' b' b''
      right; linarith
    · have a := hg.kx_two hj hj1; have b := hg.kx_zero_four hk
      have a' := rat_cast_le_of (abs_le.1 a).1; have a'' := rat_cast_le_of (abs_le.1 a).2
      have b' := rat_cast_le_of (abs_le.1 b).1; have b'' := rat_cast_le_of (abs_le.1 b).2
      push_cast at a' a'' b' b''
      left; linarith
    · have a := hg.kx_two hj hj1; have b := hg.kx_four hk hk1
      have a' := rat_cast_le_of (abs_le.1 a).1; have a'' := rat_cast_le_of (abs_le.1 a).2
      have b' := rat_cast_le_of (abs_le.1 b).1; have b'' := rat_cast_le_of (abs_le.1 b).2
      push_cast at a' a'' b' b''
      left; linarith
  · intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · right; have := hg.kx_sep (Or.inl rfl) h hk; exact_mod_cast this
    · left; have := hg.kx_sep (Or.inl rfl) h hj; exact_mod_cast this
  · intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · right; have := hg.kx_sep (Or.inr rfl) h hk; exact_mod_cast this
    · left; have := hg.kx_sep (Or.inr rfl) h hj; exact_mod_cast this

/-- The boundary of the corridor polygon is above the floor line except on the slot sides. -/
theorem Good.bd_floor_cases {w : Point} (hw : w ∈ I.poly.boundary) :
    (I.H : ℝ) ≤ w.2 ∨ ∃ j < I.np,
      w ∈ segOf ((I.dentS2 j).A, (I.dentS2 j).T) ∨ w ∈ segOf ((I.dentS2 j).T, (I.dentS2 j).B) ∨
      w ∈ segOf ((I.dentS4 j).A, (I.dentS4 j).T) ∨ w ∈ segOf ((I.dentS4 j).T, (I.dentS4 j).B) := by
  have hρ := hg.rhoR_pos
  rcases poly_boundary_cases hw with ⟨e, he, hwe⟩ | hwin | ⟨e, he, hwe⟩ | hent
  · rcases hg.floor_edge_cases he with ⟨h1, h2⟩ | ⟨j, hj, h⟩
    · left
      have := seg_affine_le (α := 0) (β := -1) (c := -(I.H : ℝ)) hwe (by simp [h1]) (by simp [h2])
      linarith
    · right; refine ⟨j, hj, ?_⟩
      rcases h with rfl | rfl | rfl | rfl
      · exact Or.inl hwe
      · exact Or.inr (Or.inl hwe)
      · exact Or.inr (Or.inr (Or.inl hwe))
      · exact Or.inr (Or.inr (Or.inr hwe))
  · left
    have := seg_affine_le (α := 0) (β := -1) (c := -(I.H : ℝ)) hwin
      (by rw [ratPoint_c1']; simp) (by rw [ratPoint_d1']; simp; linarith)
    linarith
  · left; have := hg.upper_edges_y he hwe; linarith
  · left
    have := seg_affine_le (α := 0) (β := -1) (c := -(I.H : ℝ)) hent
      (by rw [ratPoint_d0']; simp; linarith) (by rw [ratPoint_c0']; simp)
    linarith

end Slots

end Input

end ArtGallery.Sec5.Corridor

end
