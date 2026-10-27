module

public import ArtGallery.Hardness.Sec5.Corridor.Shape

/-!
# Section 5: corridors — the corridor polygon is simple

`I.poly` is the polygon `c0, slots…, c1, d1, upper wall…, d0` (the two corridor chains of a unit,
joined by the window `c1 d1` and closed by the entrance `d0 c0`).

* `Good.poly_simple`: it is simple (floor and upper wall are simple polylines separated by the
  horizontal strip `H < y < H + ρ`, the window and the entrance are vertical);
* `Good.poly_interiorLeft`: it is counter-clockwise (every vertex is left of the edge `d1 → p_0`
  on the line `x = S + 2`);
* `Good.poly_vtx_box`, `Good.poly_filled_box`: vertices and region lie in the corridor box
  `[S, S + 2] × [H − 1/4, H + 3/2]`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

/-- The corridor box `[S, S + 2] × [H − 1/4, H + 3/2]`. -/
def corridorBox (S H : ℝ) : Set Point :=
  {z | S ≤ z.1 ∧ z.1 ≤ S + 2 ∧ H - 1 / 4 ≤ z.2 ∧ z.2 ≤ H + 3 / 2}

namespace Input

variable {I : Input} {N : ℚ}

/-- `ρ` as a real number. -/
noncomputable def rhoR (I : Input) : ℝ := ((rho I.S : ℚ) : ℝ)

theorem rhoR_eq : I.rhoR = 3 / (2 * (I.S : ℝ)) := by simp [rhoR, rho]

theorem ratPoint_d1' : ratPoint (d1 I.S I.H) = ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) := by
  simp [ratPoint, d1, rhoR]

theorem ratPoint_d0' : ratPoint (d0 I.S I.H) = ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR) := by
  simp [ratPoint, d0, rhoR]

theorem chainBefore_map : I.chainBefore.map ratPoint =
    ((I.S : ℝ), (I.H : ℝ)) :: (I.floor.map ratPoint ++ [((I.S : ℝ) + 2, (I.H : ℝ))]) := by
  simp [chainBefore, ratPoint_c0', ratPoint_c1']

theorem chainAfter_map : I.chainAfter.map ratPoint =
    ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) :: (I.upper.map ratPoint ++
      [((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR)]) := by
  simp [chainAfter, ratPoint_d1', ratPoint_d0']

theorem poly_vtx (i : ℕ) : I.poly.vtx i = ((I.chainBefore ++ I.chainAfter).map ratPoint).getD i 0 :=
  rfl

theorem poly_n : I.poly.n = (I.chainBefore ++ I.chainAfter).length := by
  simp [poly, Polygon.n]

section Poly

variable (hg : I.Good N)
include hg

theorem Good.rhoR_pos : 0 < I.rhoR := by
  rw [rhoR_eq]; have : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  positivity

theorem Good.rhoR_small : I.rhoR < 1 / 1000 := by
  rw [rhoR_eq]
  have : (800000 : ℝ) ≤ I.S := by exact_mod_cast hg.scale.S_ge
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- Upper-wall vertices in real form: strictly between the lines `x = S`, `x = S + 2` (except
`p_0`), strictly above `y = H + ρ`. -/
theorem Good.upper_box' : ∀ x ∈ I.upper.map ratPoint,
    (I.S : ℝ) < x.1 ∧ x.1 ≤ (I.S : ℝ) + 2 ∧ (I.H : ℝ) + I.rhoR < x.2 ∧ x.2 ≤ (I.H : ℝ) + 3 / 2 ∧
      (x.1 < (I.S : ℝ) + 2 ∨ x = ratPoint (I.sgPt 0)) := by
  intro x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hg.upper_box x hx
  exact ⟨h1, h2, by rw [rhoR_eq]; exact h3, h4, h5⟩

/-- **The floor and the upper wall glued with the window form a simple polyline.** -/
theorem Good.poly_chainSimple : ChainSimple ((I.chainBefore ++ I.chainAfter).map ratPoint) := by
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  set c0R : Point := ((I.S : ℝ), (I.H : ℝ))
  set c1R : Point := ((I.S : ℝ) + 2, (I.H : ℝ))
  set d1R : Point := ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR)
  set d0R : Point := ((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR)
  set F := I.floor.map ratPoint
  set U := I.upper.map ratPoint
  have hF := hg.floor_box
  have hU := hg.upper_box'
  have hCB : ChainSimple (c0R :: F ++ [c1R]) := by
    have := hg.chainSimple_chainBefore; rw [chainBefore_map] at this; simpa using this
  have hCA : ChainSimple (d1R :: (U ++ [d0R])) := by
    have := hg.chainSimple_chainAfter; rw [chainAfter_map] at this; exact this
  -- the floor part is left of `x = S + 2` except `c1`
  have hFx : ∀ x ∈ c0R :: F, 1 * x.1 + 0 * x.2 < (I.S : ℝ) + 2 := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [c0R]
    · obtain ⟨-, h2, -, -⟩ := hF x hx; simp only [one_mul, zero_mul, add_zero]; linarith
  -- step 1: glue the window
  have step1 : ChainSimple ((c0R :: F) ++ c1R :: [d1R]) := by
    refine ChainSimple.append (by simpa using hCB) (chainSimple_pair ?_) ?_ ?_
    · intro h; have := congrArg Prod.snd h; simp [c1R, d1R] at this; linarith
    · intro x hx hx'
      have := hFx x hx
      rcases List.mem_cons.1 hx' with rfl | hx'
      · simp [c1R] at this
      · rw [List.mem_singleton] at hx'; subst hx'; simp [d1R] at this
    · intro e he f hf z ⟨hze, hzf⟩
      simp only [edgesOf_cons_cons, edgesOf_single, List.mem_singleton] at hf
      subst hf
      have hzx : z.1 = (I.S : ℝ) + 2 := by
        rw [seg_fst_of_vertical hzf (by simp [c1R, d1R])]
      rw [mem_singleton_iff]
      exact edges_level_last hFx (by simp [c1R]) e he z hze (by simp [hzx])
  -- the upper wall is above `y = H + ρ` except `d1`
  have hUy : ∀ x ∈ U ++ [d0R], 0 * x.1 + (-1) * x.2 < -((I.H : ℝ) + I.rhoR) := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨-, -, h3, -, -⟩ := hU x hx; linarith
    · rw [List.mem_singleton] at hx; subst hx; simp [d0R]; linarith
  -- the floor part (with the window) is below `y = H + ρ`
  have hFy : ∀ x ∈ (c0R :: F) ++ [c1R] ++ [d1R], 0 * x.1 + 1 * x.2 ≤ (I.H : ℝ) + I.rhoR := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp [c0R]; linarith
        · obtain ⟨-, -, -, h4⟩ := hF x hx; simp; linarith
      · rw [List.mem_singleton] at hx; subst hx; simp [c1R]; linarith
    · rw [List.mem_singleton] at hx; subst hx; simp [d1R]
  -- step 2: glue the upper wall
  have step2 : ChainSimple (((c0R :: F) ++ [c1R]) ++ d1R :: (U ++ [d0R])) := by
    refine ChainSimple.append (by simpa using step1) hCA ?_ ?_
    · intro x hx hx'
      have h2 : x.2 ≤ (I.H : ℝ) := by
        rcases List.mem_append.1 hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · simp [c0R]
          · exact (hF x hx).2.2.2
        · rw [List.mem_singleton] at hx; subst hx; simp [c1R]
      rcases List.mem_cons.1 hx' with rfl | hx'
      · simp [d1R] at h2; linarith
      · have := hUy x hx'
        linarith
    · intro e he f hf z ⟨hze, hzf⟩
      rw [mem_singleton_iff]
      have h1 := edges_affine_le hFy e he z hze
      exact edges_level_first hUy (by simp [d1R]) f hf z hzf (by linarith)
  have : (I.chainBefore ++ I.chainAfter).map ratPoint =
      ((c0R :: F) ++ [c1R]) ++ d1R :: (U ++ [d0R]) := by
    rw [List.map_append, chainBefore_map, chainAfter_map]
    simp [c0R, c1R, d1R, d0R, F, U]
  rw [this]; exact step2

/-- **The corridor polygon is simple.** -/
theorem Good.poly_simple : I.poly.Simple := by
  have hρ := hg.rhoR_pos
  have hU := hg.upper_box'
  have hF := hg.floor_box
  have hV := hg.poly_chainSimple
  have heq : (I.chainBefore ++ I.chainAfter).map ratPoint =
      ((I.S : ℝ), (I.H : ℝ)) :: (I.floor.map ratPoint ++ [((I.S : ℝ) + 2, (I.H : ℝ))] ++
        ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) :: I.upper.map ratPoint) ++
        [((I.S : ℝ), (I.H : ℝ) + 2 * I.rhoR)] := by
    rw [List.map_append, chainBefore_map, chainAfter_map]; simp
  show (Polygon.mk ((I.chainBefore ++ I.chainAfter).map ratPoint)).Simple
  rw [heq] at hV ⊢
  refine simple_of_chainSimple_vertical hV (by simp) rfl rfl ?_
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · have := (hF x hx).1; linarith
    · rw [List.mem_singleton] at hx; subst hx; simp
  · rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · exact (hU x hx).1

/-- All vertices of the corridor polygon lie weakly left of `x = S + 2`. -/
theorem Good.poly_vtx_le : ∀ x ∈ (I.chainBefore ++ I.chainAfter).map ratPoint,
    x.1 ≤ (I.S : ℝ) + 2 := by
  have hU := hg.upper_box'
  have hF := hg.floor_box
  intro x hx
  rw [List.map_append, chainBefore_map, chainAfter_map] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · rcases List.mem_append.1 hx with hx | hx
      · have := (hF x hx).2.1; linarith
      · rw [List.mem_singleton] at hx; subst hx; simp
  · rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hU x hx).2.1
      · rw [List.mem_singleton] at hx; subst hx; simp

/-- **The corridor polygon is counter-clockwise.** -/
theorem Good.poly_interiorLeft : I.poly.InteriorLeft := by
  have hK := hg.poly_simple
  obtain ⟨m, hm⟩ : ∃ m, I.chainBefore.length = m := ⟨_, rfl⟩
  have hn : I.poly.n = m + I.chainAfter.length := by rw [poly_n, List.length_append, hm]
  have hA : 2 ≤ I.chainAfter.length := by
    have h0 : 0 < I.np := by have := hg.np_pos; omega
    have : I.upper ≠ [] := by
      simp only [upper, ne_eq, List.flatMap_eq_nil_iff, List.mem_range, not_forall]
      exact ⟨0, h0, by simp [upperPair]⟩
    simp only [chainAfter, List.length_append, List.length_singleton]
    have := List.length_pos_iff.2 this
    omega
  have hvm : I.poly.vtx m = ((I.S : ℝ) + 2, (I.H : ℝ) + I.rhoR) := by
    rw [poly_vtx, List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by simp [hm]), List.length_map, hm, Nat.sub_self, chainAfter_map]
    simp
  have hvm1 : I.poly.vtx ((m + 1) % I.poly.n) = ratPoint (I.sgPt 0) := by
    rw [Nat.mod_eq_of_lt (by omega), poly_vtx, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp [hm]), List.length_map, hm,
      show m + 1 - m = 1 by omega, chainAfter_map]
    have h0 : 0 < I.np := by have := hg.np_pos; omega
    have h3 := hg.np_le
    have : I.upper = I.sgPt 0 :: I.upper.tail := by
      simp only [upper]
      rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with h | h | h <;>
        simp [h, List.range_succ, upperPair]
    rw [this]
    simp
  obtain ⟨⟨-, -, hy, -⟩, -⟩ := hg.sgPt_zero_box
  have hx0 := hg.sgPt_zero_box.2
  apply Polygon.interiorLeft_of_supporting_edge hK (i := m) (by omega)
  intro j hj
  rw [hvm, hvm1]
  have hle := hg.poly_vtx_le (I.poly.vtx j) (by
    rw [poly_vtx, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_map, ← poly_n]; exact hj)]
    simp only [Option.getD_some]; exact List.getElem_mem _)
  simp only [det, hx0]
  rw [rhoR_eq]
  nlinarith

/-- All vertices of the corridor polygon lie in the corridor box. -/
theorem Good.poly_vtx_box : ∀ x ∈ (I.chainBefore ++ I.chainAfter).map ratPoint,
    x ∈ corridorBox (I.S : ℝ) (I.H : ℝ) := by
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  have hU := hg.upper_box'
  have hF := hg.floor_box
  intro x hx
  rw [List.map_append, chainBefore_map, chainAfter_map] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨le_rfl, by linarith, by linarith, by linarith⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨h1, h2, h3, h4⟩ := hF x hx
        exact ⟨by linarith, by linarith, h3, by linarith⟩
      · rw [List.mem_singleton] at hx; subst hx
        refine ⟨by simp, le_rfl, by simp, by simp; linarith⟩
  · rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨by simp, le_rfl, by simp; linarith, by simp; linarith⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨h1, h2, h3, h4, -⟩ := hU x hx
        exact ⟨h1.le, h2, by linarith, h4⟩
      · rw [List.mem_singleton] at hx; subst hx
        refine ⟨le_rfl, by simp, by simp; linarith, by simp; linarith⟩

/-- **The region of the corridor polygon lies in the corridor box.** -/
theorem Good.poly_filled_box : I.poly.filled ⊆ corridorBox (I.S : ℝ) (I.H : ℝ) := by
  have hvb : ∀ i < I.poly.n, I.poly.vtx i ∈ corridorBox (I.S : ℝ) (I.H : ℝ) := by
    intro i hi
    apply hg.poly_vtx_box
    rw [poly_vtx, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_map, ← poly_n]; exact hi)]
    simp only [Option.getD_some]; exact List.getElem_mem _
  have h0 : 0 < I.poly.n := by have := hg.poly_simple.1; omega
  have hv0 : I.poly.vtx 0 = ((I.S : ℝ), (I.H : ℝ)) := by
    rw [poly_vtx, List.map_append, chainBefore_map]; simp
  -- the vertex `c1` is the right end of the floor
  have hc1 : ∃ i < I.poly.n, I.poly.vtx i = ((I.S : ℝ) + 2, (I.H : ℝ)) := by
    refine ⟨I.chainBefore.length - 1, by rw [poly_n, List.length_append]; simp [chainBefore]; omega,
      ?_⟩
    rw [poly_vtx, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [chainBefore]), chainBefore_map]
    simp [chainBefore]
  obtain ⟨i1, hi1, hv1⟩ := hc1
  intro z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := filled_subset_halfplane (α := -1) (β := 0) (c := -(I.S : ℝ))
      (fun i hi => by have := (hvb i hi).1; linarith) (v := I.poly.vtx i1)
      (by rw [hv1]; simp) hz
    simp only [mem_ofPred_eq] at this; linarith
  · have := filled_subset_halfplane (α := 1) (β := 0) (c := (I.S : ℝ) + 2)
      (fun i hi => by have := (hvb i hi).2.1; linarith) (v := I.poly.vtx 0)
      (by rw [hv0]; simp) hz
    simp only [mem_ofPred_eq] at this; linarith
  · have := filled_subset_halfplane (α := 0) (β := -1) (c := -((I.H : ℝ) - 1 / 4))
      (fun i hi => by have := (hvb i hi).2.2.1; linarith) (v := I.poly.vtx 0)
      (by rw [hv0]; simp) hz
    simp only [mem_ofPred_eq] at this; linarith
  · have := filled_subset_halfplane (α := 0) (β := 1) (c := (I.H : ℝ) + 3 / 2)
      (fun i hi => by have := (hvb i hi).2.2.2; linarith) (v := I.poly.vtx 0)
      (by rw [hv0]; simp) hz
    simp only [mem_ofPred_eq] at this; linarith

end Poly

end Input

end ArtGallery.Sec5.Corridor

end
