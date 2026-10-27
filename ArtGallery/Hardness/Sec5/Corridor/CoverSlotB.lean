module

public import ArtGallery.Hardness.Sec5.Corridor.CoverSlotA

/-!
# Section 5: corridors — the slot pieces lie in the corridor region

`Good.slot2_subset`, `Good.slot4_subset`: the slot triangle of pair `k` lies in the corridor region
as soon as it contains an interior point of the corridor.  Boundary check: the boundary off the
slot sides is on or above the floor line; the sides of the slot itself are on the lines of the
piece; the sides of the other slots are separated by the slot keys (`Good.keys`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

theorem seg_check (f : Aff) {a b w : Point} (hw : w ∈ segOf (a, b)) (ha : f.ev a ≤ 0)
    (hb : f.ev b ≤ 0) : f.ev w ≤ 0 :=
  f.ev_le_of_segment hw ha hb

section Slots

variable (hg : I.Good N)
include hg

/-- **The slope-2 slot piece lies in the corridor region.** -/
theorem Good.slot2_subset {k : ℕ} (hk : k < I.np) {z : Point} (hz : z ∈ hpSet (I.slot2Fs k))
    (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary) :
    hpSet (I.slot2Fs k) ⊆ I.poly.filled := by
  obtain ⟨he, he1⟩ := hg.eps_real
  set κ : ℝ := (I.kx k 2 : ℝ)
  set ε : ℝ := (I.ε : ℝ)
  set H : ℝ := (I.H : ℝ)
  have m1 : (⟨0, -1, H⟩ : Aff) ∈ I.slot2Fs k := by simp [slot2Fs, H]
  have m2 : (⟨-1, 1 / 2, κ - H / 2⟩ : Aff) ∈ I.slot2Fs k := by simp [slot2Fs, κ, H]
  have m3 : (⟨1, ε - 1 / 2, H / 2 - κ - ε * H + ε / 8⟩ : Aff) ∈ I.slot2Fs k := by
    simp [slot2Fs, κ, H, ε]
  refine hpSet_subset_filled hg.poly_simple ?_ (c := (κ - ε / 16, H - ε / 64)) ?_ hz hzK hzb
  · intro w hw
    rcases hg.bd_floor_cases hw with hy | ⟨j, hj, h⟩
    · exact ⟨_, m1, by simp only [Aff.ev]; linarith⟩
    obtain ⟨hkey, h22, -⟩ := hg.keys hj hk
    obtain ⟨hkey', -, -⟩ := hg.keys hk hj
    simp only [dentS2, dent2, dentS4, dent4] at h
    rcases h with h | h | h | h
    · -- side `A T` of a slope-2 slot
      by_cases hjk : j = k
      · subst hjk
        exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; ring_nf; linarith)
          (by simp only [Aff.ev]; ring_nf; linarith)⟩
      · rcases h22 hjk with h' | h'
        · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
        · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `T B` of a slope-2 slot
      by_cases hjk : j = k
      · subst hjk
        exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; ring_nf; linarith)
          (by simp only [Aff.ev]; ring_nf; linarith)⟩
      · rcases h22 hjk with h' | h'
        · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
        · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `A T` of a slope-4 slot
      rcases hkey' with h' | h'
      · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
      · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `T B` of a slope-4 slot
      rcases hkey' with h' | h'
      · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
      · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
  · simp only [hpOpen, slot2Fs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Aff.ev, Set.mem_ofPred_eq]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **The slope-4 slot piece lies in the corridor region.** -/
theorem Good.slot4_subset {k : ℕ} (hk : k < I.np) {z : Point} (hz : z ∈ hpSet (I.slot4Fs k))
    (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary) :
    hpSet (I.slot4Fs k) ⊆ I.poly.filled := by
  obtain ⟨he, he1⟩ := hg.eps_real
  set κ : ℝ := (I.kx k 4 : ℝ)
  set ε : ℝ := (I.ε : ℝ)
  set H : ℝ := (I.H : ℝ)
  have m1 : (⟨0, -1, H⟩ : Aff) ∈ I.slot4Fs k := by simp [slot4Fs, H]
  have m2 : (⟨1, -1 / 4, H / 4 - κ⟩ : Aff) ∈ I.slot4Fs k := by simp [slot4Fs, κ, H]
  have m3 : (⟨-1, ε / 2 + 1 / 4, -(ε / 2) * H + ε / 8 - H / 4 + κ⟩ : Aff) ∈ I.slot4Fs k := by
    simp [slot4Fs, κ, H, ε]
  refine hpSet_subset_filled hg.poly_simple ?_ (c := (κ + ε / 32, H - ε / 64)) ?_ hz hzK hzb
  · intro w hw
    rcases hg.bd_floor_cases hw with hy | ⟨j, hj, h⟩
    · exact ⟨_, m1, by simp only [Aff.ev]; linarith⟩
    obtain ⟨hkey, -, h44⟩ := hg.keys hj hk
    simp only [dentS2, dent2, dentS4, dent4] at h
    rcases h with h | h | h | h
    · -- side `A T` of a slope-2 slot
      rcases hkey with h' | h'
      · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
      · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `T B` of a slope-2 slot
      rcases hkey with h' | h'
      · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
      · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
          (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `A T` of a slope-4 slot
      by_cases hjk : j = k
      · subst hjk
        exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; ring_nf; linarith)
          (by simp only [Aff.ev]; ring_nf; linarith)⟩
      · rcases h44 hjk with h' | h'
        · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
        · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
    · -- side `T B` of a slope-4 slot
      by_cases hjk : j = k
      · subst hjk
        exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; ring_nf; linarith)
          (by simp only [Aff.ev]; ring_nf; linarith)⟩
      · rcases h44 hjk with h' | h'
        · exact ⟨_, m2, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
        · exact ⟨_, m3, seg_check _ h (by simp only [Aff.ev]; nlinarith)
            (by simp only [Aff.ev]; nlinarith)⟩
  · simp only [hpOpen, slot4Fs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Aff.ev, Set.mem_ofPred_eq]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end Slots

end Input

end ArtGallery.Sec5.Corridor

end
