module

public import ArtGallery.Hardness.Sec5.Assemble.Clear

/-!
# Section 5: the two sides of the global polygon

* **Right side** (`rightSide`): the right units sit in the global polygon
  `polyC Φ n = Polygon.mk ((construct Φ n).map ratPoint)` from index `|bottomWall| + 2`.
* **Left side** (`leftSide`): the left units sit, in their working frame, in the mirrored polygon
  `polyM Φ n = mirrorPoly (54n − 12) (polyC Φ n)` (mirror `x ↦ 54n − 12 − x` with the vertex list
  reversed, so that it is again counter-clockwise; `Sees`, `filled`, `Simple` transfer by
  `Vis.Cert.sees_mirrorPoly_iff`, `filled_mirrorPoly`, `simple_mirrorPoly_iff`) from index `1`.

Consequently every unit `m` of either side has `CorridorAt`, `CorridorClear`, the template
`ChainAt` and the wall separation (`SideAt.corridorAt`, `SideAt.corridorClear`, `SideAt.chainAt`,
`SideAt.sep_walls`), in `polyC` for right units and in `polyM` for left units.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input CorridorAt c0 c1 d0 d1)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The global polygon. -/
noncomputable def polyC (Φ : List ETRINV.Constraint) (n : ℕ) : Polygon :=
  Polygon.mk ((construct Φ n).map ratPoint)

/-- The mirror image of the global polygon (vertex list reversed): the left units appear in their
working frame. -/
noncomputable def polyM (Φ : List ETRINV.Constraint) (n : ℕ) : Polygon :=
  Vis.Cert.mirrorPoly (54 * (n : ℝ) - 12) (polyC Φ n)

/-! ### Vertex lookup in a split list -/

theorem vtx_split {A C B : List Q2} {i : ℕ} (hi : i < C.length) :
    (Polygon.mk ((A ++ C ++ B).map ratPoint)).vtx (A.length + i) = ratPoint (C.getD i 0) := by
  simp only [Polygon.vtx, List.map_append]
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp),
    List.length_map, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

theorem flatten_split {cs : List (List Q2)} {m : ℕ} (hm : m < cs.length) :
    cs.flatten = (cs.take m).flatten ++ cs[m] ++ (cs.drop (m + 1)).flatten := by
  have e : cs = cs.take m ++ cs[m] :: cs.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  conv_lhs => rw [e]
  rw [List.flatten_append, List.flatten_cons, List.append_assoc]

theorem length_flatten_take (cs : List (List Q2)) (m : ℕ) :
    ((cs.take m).flatten).length = ((cs.take m).map List.length).sum := by
  simp [List.length_flatten]

/-- The vertices of a side from a decomposition `V = A ++ (unit chains).flatten ++ B`. -/
theorem side_vtx {V A B : List Q2} {n k : ℕ} {us : List UnitSpec}
    (hV : V = A ++ (unitChains n k 0 us).flatten ++ B) :
    ∀ m (hm : m < us.length), ∀ i < (unitChain n k m (us[m]'hm)).length,
      (Polygon.mk (V.map ratPoint)).vtx (unitStart n k us A.length m + i) =
        ratPoint ((unitChain n k m (us[m]'hm)).getD i 0) := by
  intro m hm i hi
  have hm' : m < (unitChains n k 0 us).length := by rw [length_unitChains]; exact hm
  have e := getElem_unitChains n k 0 us m hm'
  rw [Nat.zero_add] at e
  have hV' : V = (A ++ ((unitChains n k 0 us).take m).flatten) ++ unitChain n k m (us[m]'hm) ++
      (((unitChains n k 0 us).drop (m + 1)).flatten ++ B) := by
    rw [hV, flatten_split hm', e]; simp
  have hlen : (A ++ ((unitChains n k 0 us).take m).flatten).length = unitStart n k us A.length m := by
    simp only [List.length_append, length_flatten_take, unitStart]
  rw [hV', ← hlen]
  exact vtx_split hi

theorem side_fit {V A B : List Q2} {n k : ℕ} {us : List UnitSpec}
    (hV : V = A ++ (unitChains n k 0 us).flatten ++ B) :
    unitStart n k us A.length us.length ≤ (Polygon.mk (V.map ratPoint)).n := by
  have : unitStart n k us A.length us.length = A.length + ((unitChains n k 0 us).flatten).length := by
    simp only [unitStart]
    rw [show us.length = (unitChains n k 0 us).length from (length_unitChains _ _ _ _).symm,
      List.take_length, List.length_flatten]
  simp only [Polygon.n, List.length_map]
  rw [this, hV]; simp

/-! ### The right side -/

section Sides

variable {Φ : List ETRINV.Constraint} {n : ℕ}

theorem construct_right (hn : 0 < n) : construct Φ n = (bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++
    (unitChains n (numC Φ) 0 (unitSpecs n Φ).1).flatten ++
    ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++ [vL n (numC Φ)]) := by
  rw [construct_pos (by omega)]; simp [constructPos, rightPart]

/-- **The right side of the global polygon.** -/
theorem rightSide (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    SideAt (polyC Φ n) n (numC Φ) (unitSpecs n Φ).1 ((bottomWall n Φ).length + 2) := by
  obtain ⟨h1, h2, h3, -, -⟩ := construct_global hΦ hn
  have hok := unitSpecs_ok hΦ
  have hst : (bottomWall n Φ ++ [wR n, vR n (numC Φ)]).length = (bottomWall n Φ).length + 2 := by
    simp
  refine ⟨h1, h2, fun u hu => hok u (List.mem_append_left _ hu), length_unitSpecs_fst n Φ,
    four_n_le_bigN, ?_, ?_, h3⟩
  · have := side_fit (construct_right (Φ := Φ) hn)
    rwa [hst] at this
  · have := side_vtx (construct_right (Φ := Φ) hn)
    rwa [hst] at this

/-! ### The left side -/

theorem construct_mirror (hn : 0 < n) : (construct Φ n).reverse.map (mirror n) =
    [mirror n (vL n (numC Φ))] ++ (unitChains n (numC Φ) 0 (unitSpecs n Φ).2).flatten ++
      ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
        ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ).reverse.map (mirror n))) := by
  rw [construct_pos (by omega)]
  simp only [constructPos, leftPart, List.reverse_append, List.map_append, List.reverse_flatten,
    List.reverse_reverse, List.map_map, List.map_flatten, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.map_cons, List.map_nil]
  have hc : ∀ cs : List (List Q2),
      List.map (List.map (mirror n)) (List.map List.reverse (List.map (leftChain n) cs)) = cs := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, ih, List.cons.injEq, and_true]
      simp [leftChain, List.map_reverse, List.map_map, Function.comp_def, mirror_mirror]
  simp only [List.map_reverse, List.reverse_reverse]
  rw [hc]
  simp

theorem polyM_eq : polyM Φ n = Polygon.mk (((construct Φ n).reverse.map (mirror n)).map ratPoint) := by
  simp only [polyM, polyC, Vis.Cert.mirrorPoly, Vis.Cert.revPoly, Hardening.Invariance.mapPoly,
    List.map_map, List.map_reverse]
  congr 2
  apply List.map_congr_left
  intro p _
  exact (ratPoint_mirror n p).symm

/-- **The left side**: the left units in the mirrored polygon (working frame). -/
theorem leftSide (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    SideAt (polyM Φ n) n (numC Φ) (unitSpecs n Φ).2 1 := by
  obtain ⟨h1, h2, -, h4, h5⟩ := construct_global hΦ hn
  have hok := unitSpecs_ok hΦ
  have hsimple : (polyM Φ n).Simple := (Vis.Cert.simple_mirrorPoly_iff _ _).2 h1
  have hmirr : ∀ p : Point, mirrorR n p = Vis.Cert.reflX (54 * (n : ℝ) - 12) p := fun _ => rfl
  have hbd : (polyM Φ n).boundary = mirrorR n '' (polyC Φ n).boundary := by
    simp only [polyM, Vis.Cert.mirrorPoly, Vis.Cert.boundary_revPoly,
      Hardening.Invariance.boundary_mapPoly]
    rfl
  have hmir : ∀ p : Point, mirrorR n (mirrorR n p) = p := fun p => by
    simp only [mirrorR, Vis.Cert.reflX_apply]; ext <;> simp
  refine ⟨hsimple, ?_, fun u hu => hok u (List.mem_append_right _ hu), length_unitSpecs_snd n Φ,
    four_n_le_bigN, ?_, ?_, ?_⟩
  · -- orientation: the image of the top edge supports the mirrored polygon
    have hvb : ∀ v ∈ (polyC Φ n).vertices, v ∈ (polyC Φ n).boundary := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      refine ⟨i, hi, ?_⟩
      have : (polyC Φ n).vtx i = (polyC Φ n).vertices[i] := by
        simp [Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [Polygon.edge, ← this]
      exact Geometry.left_mem_segment _ _
    have hy : ∀ v ∈ (((construct Φ n).reverse.map (mirror n)).map ratPoint),
        v.2 ≤ (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ) := by
      intro v hv
      simp only [List.map_map, List.mem_map, List.mem_reverse, Function.comp] at hv
      obtain ⟨q, hq, rfl⟩ := hv
      have := h5 (ratPoint q) (hvb _ (List.mem_map_of_mem hq))
      simpa [ratPoint, mirror] using this
    rw [polyM_eq, construct_mirror hn] at hsimple ⊢
    rw [construct_mirror hn] at hy
    set A := [mirror n (vL n (numC Φ))] ++ (unitChains n (numC Φ) 0 (unitSpecs n Φ).2).flatten
    have hl : (A ++ ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
        ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ).reverse.map (mirror n)))).map
          ratPoint = A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
            ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++
              rightPart n Φ).reverse.map (mirror n)).map ratPoint := by simp
    rw [hl] at hsimple hy ⊢
    obtain ⟨g1, g2⟩ := getD_mid (A := A.map ratPoint) (x := ratPoint (mirror n (tL n (numC Φ))))
      (y := ratPoint (mirror n (tR n (numC Φ))))
      (C := ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ).reverse.map (mirror n)).map
        ratPoint)
    have hlen : (A.map ratPoint).length + 1 < (A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
        ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++
          rightPart n Φ).reverse.map (mirror n)).map ratPoint).length := by simp
    apply Polygon.interiorLeft_of_supporting_edge hsimple (i := (A.map ratPoint).length)
      (by simp only [Polygon.n]; omega)
    intro j hj
    have hyj := hy _ (show (A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
        ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++
          rightPart n Φ).reverse.map (mirror n)).map ratPoint).getD j (0, 0) ∈ _ by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem _)
    simp only [Polygon.vtx] at g1 g2 ⊢
    rw [Nat.mod_eq_of_lt (by simpa [Polygon.n] using hlen), g1, g2]
    have e1 : ratPoint (mirror n (tL n (numC Φ))) =
        ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
      simp [ratPoint, mirror, tL, XL]
    have e2 : ratPoint (mirror n (tR n (numC Φ))) =
        (54 * (n : ℝ) - 12 - (S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
      simp [ratPoint, mirror, tR, xMirror]
    rw [e1, e2] at hyj ⊢
    have hS1 : 54 * (n : ℝ) + 100000 ≤ (S n (numC Φ) : ℝ) := by
      have := slots_lt_S (n := n) (k := numC Φ)
      have : ((54 * (n : ℚ) + 100000 : ℚ) : ℝ) ≤ ((S n (numC Φ) : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at this; exact this
    simp only [det]
    nlinarith
  · have := side_fit (construct_mirror (Φ := Φ) hn)
    rw [polyM_eq]
    simpa using this
  · have := side_vtx (construct_mirror (Φ := Φ) hn)
    rw [polyM_eq]
    simpa using this
  · intro p hp
    rw [hbd] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rcases h4 q hq with h | h
    · left
      simp only [mirrorR, Vis.Cert.reflX_apply]
      linarith
    · right; exact h

end Sides

end ArtGallery.Sec5

end
