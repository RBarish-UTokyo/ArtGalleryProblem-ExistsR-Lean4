module

public import ArtGallery.Hardness.Sec5.Assemble.UnitChain
public import ArtGallery.Hardness.Sec5.Corridor.Member

/-!
# Section 5: the corridor polygon near the line `x = S`

Facts about the corridor polygon `I.poly` used to prove `CorridorClear` for the global polygon:

* `chainSet_before_subset`, `chainSet_after_subset`: the floor chain and the upper wall are parts of
  the boundary of `I.poly`;
* `Good.upper_fst_ge`: the upper-wall vertices lie right of `x = S + 3/4`;
* `Good.filled_left`: a point of the corridor region on the line `x = S` lies on the entrance
  `d0 c0` (the region lies in the half-planes `x + y ≥ S + H` and `y ≤ H + 2ρ + 2(x − S)`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The edges of a prefix of the vertex list are edges of the polygon. -/
theorem chainSet_prefix_subset_boundary (A B : List Point) :
    chainSet A ⊆ (Polygon.mk (A ++ B)).boundary := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := mem_chainSet_iff.1 hx
  refine ⟨i, by simp [Polygon.n]; omega, ?_⟩
  have hn : (Polygon.mk (A ++ B)).n = A.length + B.length := by simp [Polygon.n]
  simp only [Polygon.edge, hn, Nat.mod_eq_of_lt (show i + 1 < A.length + B.length by omega)]
  simp only [Polygon.vtx, getD_append_left' (show i < A.length by omega), getD_append_left' hi]
  exact hx

/-- The edges of a suffix of the vertex list are edges of the polygon. -/
theorem chainSet_suffix_subset_boundary (A B : List Point) :
    chainSet B ⊆ (Polygon.mk (A ++ B)).boundary := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := mem_chainSet_iff.1 hx
  refine ⟨A.length + i, by simp [Polygon.n]; omega, ?_⟩
  have hn : (Polygon.mk (A ++ B)).n = A.length + B.length := by simp [Polygon.n]
  simp only [Polygon.edge, hn, Nat.mod_eq_of_lt (show A.length + i + 1 < A.length + B.length by omega)]
  simp only [Polygon.vtx]
  rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
    show A.length + i - A.length = i by omega, show A.length + i + 1 - A.length = i + 1 by omega]
  exact hx

namespace Corridor.Input

variable {I : Input} {N : ℚ}

theorem chainSet_before_subset : chainSet (I.chainBefore.map ratPoint) ⊆ I.poly.boundary := by
  have := chainSet_prefix_subset_boundary (I.chainBefore.map ratPoint) (I.chainAfter.map ratPoint)
  rwa [← List.map_append] at this

theorem chainSet_after_subset : chainSet (I.chainAfter.map ratPoint) ⊆ I.poly.boundary := by
  have := chainSet_suffix_subset_boundary (I.chainBefore.map ratPoint) (I.chainAfter.map ratPoint)
  rwa [← List.map_append] at this

/-- The upper-wall vertices lie right of `x = S + 3/4`. -/
theorem Good.upper_fst_ge (hg : I.Good N) : ∀ x ∈ I.upper.map ratPoint, (I.S : ℝ) + 3 / 4 ≤ x.1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rcases hg.mem_upper hy with ⟨h1, -⟩ | rfl
  · have hS := hg.S_pos
    have hSe := hg.S_eq
    have hN := hg.N_ge
    rw [abs_le] at h1
    have h2 : 8 * I.S * (y.1 - (I.S + 1)) ≥ -(456 * N) := by
      have := h1.1; simp only [lX, O_eq] at this; linarith
    have h3 : y.1 ≥ I.S + 3 / 4 := by
      by_contra hc
      push Not at hc
      have : 8 * I.S * (y.1 - (I.S + 1)) < 8 * I.S * (-(1 / 4)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity); linarith
      nlinarith
    have := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at this
    simpa [ratPoint] using this
  · rw [hg.sgPt_zero_box.2]; linarith

/-- **The corridor region meets the line `x = S` only in the entrance.** -/
theorem Good.filled_left (hg : I.Good N) {z : Point} (hz : z ∈ I.poly.filled)
    (hzx : z.1 ≤ (I.S : ℝ)) : z ∈ I.entrance := by
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  have hbox := hg.poly_filled_box hz
  obtain ⟨b1, -, -, -⟩ := hbox
  have hx : z.1 = (I.S : ℝ) := le_antisymm hzx b1
  have hvtx : ∀ i < I.poly.n, I.poly.vtx i ∈ (I.chainBefore ++ I.chainAfter).map ratPoint := by
    intro i hi
    rw [poly_n] at hi
    rw [poly_vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
    exact List.getElem_mem _
  have hall : ∀ v ∈ (I.chainBefore ++ I.chainAfter).map ratPoint,
      (I.S : ℝ) + (I.H : ℝ) ≤ v.1 + v.2 ∧ v.2 ≤ (I.H : ℝ) + 2 * I.rhoR + 2 * (v.1 - I.S) := by
    intro v hv
    rw [List.map_append, chainBefore_map, chainAfter_map] at hv
    simp only [List.cons_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hv
    rcases hv with h | h | h | h | h | h
    · subst h; constructor <;> simp <;> linarith
    · obtain ⟨a, b, c, d⟩ := hg.floor_box v h; constructor <;> nlinarith
    · subst h; constructor <;> simp <;> linarith
    · subst h; constructor <;> simp <;> linarith
    · obtain ⟨a, b, c, d, -⟩ := hg.upper_box' v h
      have := hg.upper_fst_ge v h
      constructor <;> linarith
    · subst h; constructor <;> simp <;> linarith
  have h1 := filled_subset_halfplane (K := I.poly) (α := -1) (β := -1)
    (c := -((I.S : ℝ) + (I.H : ℝ)))
    (fun i hi => by have := (hall _ (hvtx i hi)).1; linarith)
    (v := ((I.S : ℝ) + 1, (I.H : ℝ) + 1)) (by simp; linarith) hz
  have h2 := filled_subset_halfplane (K := I.poly) (α := -2) (β := 1)
    (c := (I.H : ℝ) + 2 * I.rhoR - 2 * (I.S : ℝ))
    (fun i hi => by have := (hall _ (hvtx i hi)).2; linarith)
    (v := ((I.S : ℝ) + 1, (I.H : ℝ))) (by simp; linarith) hz
  simp only [mem_ofPred_eq] at h1 h2
  rw [hx] at h1 h2
  have hy1 : (I.H : ℝ) ≤ z.2 := by linarith
  have hy2 : z.2 ≤ (I.H : ℝ) + 2 * I.rhoR := by linarith
  -- the entrance is the vertical segment from `d0` to `c0`
  refine ⟨((I.H : ℝ) + 2 * I.rhoR - z.2) / (2 * I.rhoR), by
    apply div_nonneg <;> linarith, by rw [div_le_one (by linarith)]; linarith, ?_⟩
  rw [ratPoint_d0', ratPoint_c0']
  ext
  · simp [hx]
  · simp only
    field_simp
    ring

end Corridor.Input

end ArtGallery.Sec5

end
