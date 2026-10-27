module

public import ArtGallery.Hardness.BP.Assemble.Side
public import ArtGallery.Hardness.Sec5.Assemble.Sides

/-!
# Boundary-point variant: the two sides of the global polygon

As `Sec5/Assemble/Sides.lean`:

* **Right side** (`rightSideBP`): the right units sit in the global polygon
  `polyCBP Φ n = Polygon.mk ((constructBP Φ n).map ratPoint)` from index `|bottomWallBP| + 2`.
* **Left side** (`leftSideBP`): the left units sit, in their working frame, in the mirrored
  polygon `polyMBP Φ n = mirrorPoly (54n − 12) (polyCBP Φ n)` from index `1`.

Consequently every unit of either side has `CorridorAt`, `CorridorClear`, the template `ChainAt`
and the wall separation (`SideAtBP.corridorAt`, `SideAtBP.corridorClear`, `SideAtBP.chainAt`,
`SideAtBP.sep_walls`), in `polyCBP` for right units and in `polyMBP` for left units.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The global polygon. -/
noncomputable def polyCBP (Φ : List ETRINV.Constraint) (n : ℕ) : Polygon :=
  Polygon.mk ((constructBP Φ n).map ratPoint)

/-- The mirror image of the global polygon (vertex list reversed): the left units appear in their
working frame. -/
noncomputable def polyMBP (Φ : List ETRINV.Constraint) (n : ℕ) : Polygon :=
  Vis.Cert.mirrorPoly (54 * (n : ℝ) - 12) (polyCBP Φ n)

/-- The vertices of a side from a decomposition `V = A ++ (unit chains).flatten ++ B`. -/
theorem side_vtxBP {V A B : List Q2} {n k : ℕ} {us : List UnitSpec}
    (hV : V = A ++ (unitChainsBP n k 0 us).flatten ++ B) :
    ∀ m (hm : m < us.length), ∀ i < (unitChainBP n k m (us[m]'hm)).length,
      (Polygon.mk (V.map ratPoint)).vtx (unitStartBP n k us A.length m + i) =
        ratPoint ((unitChainBP n k m (us[m]'hm)).getD i 0) := by
  intro m hm i hi
  have hm' : m < (unitChainsBP n k 0 us).length := by rw [length_unitChainsBP]; exact hm
  have e := getElem_unitChainsBP n k 0 us m hm'
  rw [Nat.zero_add] at e
  have hV' : V = (A ++ ((unitChainsBP n k 0 us).take m).flatten) ++ unitChainBP n k m (us[m]'hm) ++
      (((unitChainsBP n k 0 us).drop (m + 1)).flatten ++ B) := by
    rw [hV, flatten_split hm', e]; simp
  have hlen : (A ++ ((unitChainsBP n k 0 us).take m).flatten).length = unitStartBP n k us A.length m := by
    simp only [List.length_append, length_flatten_take, unitStartBP]
  rw [hV', ← hlen]
  exact vtx_split hi

theorem side_fitBP {V A B : List Q2} {n k : ℕ} {us : List UnitSpec}
    (hV : V = A ++ (unitChainsBP n k 0 us).flatten ++ B) :
    unitStartBP n k us A.length us.length ≤ (Polygon.mk (V.map ratPoint)).n := by
  have : unitStartBP n k us A.length us.length = A.length + ((unitChainsBP n k 0 us).flatten).length := by
    simp only [unitStartBP]
    rw [show us.length = (unitChainsBP n k 0 us).length from (length_unitChainsBP _ _ _ _).symm,
      List.take_length, List.length_flatten]
  simp only [Polygon.n, List.length_map]
  rw [this, hV]; simp

/-! ### The right side -/

section Sides

variable {Φ : List ETRINV.Constraint} {n : ℕ}

theorem constructBP_right (hn : 0 < n) : constructBP Φ n = (bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]) ++
    (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).1).flatten ++
    ([tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++ [vL n (numC Φ)]) := by
  rw [constructBP_pos (by omega)]; simp [constructPosBP, rightPartBP]

/-- **The right side of the global polygon.** -/
theorem rightSideBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    SideAtBP (polyCBP Φ n) n (numC Φ) (unitSpecs n Φ).1 ((bottomWallBP n Φ).length + 2) := by
  obtain ⟨h1, h2, h3, -, -⟩ := constructBP_global hΦ hn
  have hok := unitSpecs_ok hΦ
  have hst : (bottomWallBP n Φ ++ [wR n, vR n (numC Φ)]).length = (bottomWallBP n Φ).length + 2 := by
    simp
  refine ⟨h1, h2, fun u hu => hok u (List.mem_append_left _ hu), length_unitSpecs_fst n Φ,
    four_n_le_bigN, ?_, ?_, h3⟩
  · have := side_fitBP (constructBP_right (Φ := Φ) hn)
    rwa [hst] at this
  · have := side_vtxBP (constructBP_right (Φ := Φ) hn)
    rwa [hst] at this

/-! ### The left side -/

theorem constructBP_mirror (hn : 0 < n) : (constructBP Φ n).reverse.map (mirror n) =
    [mirror n (vL n (numC Φ))] ++ (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).2).flatten ++
      ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
        ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ).reverse.map (mirror n))) := by
  rw [constructBP_pos (by omega)]
  simp only [constructPosBP, leftPartBP, List.reverse_append, List.map_append, List.reverse_flatten,
    List.map_flatten, List.reverse_cons, List.reverse_nil,
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

theorem polyMBP_eq : polyMBP Φ n = Polygon.mk (((constructBP Φ n).reverse.map (mirror n)).map ratPoint) := by
  simp only [polyMBP, polyCBP, Vis.Cert.mirrorPoly, Vis.Cert.revPoly, Hardening.Invariance.mapPoly,
    List.map_map, List.map_reverse]
  congr 2
  apply List.map_congr_left
  intro p _
  exact (ratPoint_mirror n p).symm

/-- **The left side**: the left units in the mirrored polygon (working frame). -/
theorem leftSideBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    SideAtBP (polyMBP Φ n) n (numC Φ) (unitSpecs n Φ).2 1 := by
  obtain ⟨h1, h2, -, h4, h5⟩ := constructBP_global hΦ hn
  have hok := unitSpecs_ok hΦ
  have hsimple : (polyMBP Φ n).Simple := (Vis.Cert.simple_mirrorPoly_iff _ _).2 h1
  have hmirr : ∀ p : Point, mirrorR n p = Vis.Cert.reflX (54 * (n : ℝ) - 12) p := fun _ => rfl
  have hbd : (polyMBP Φ n).boundary = mirrorR n '' (polyCBP Φ n).boundary := by
    simp only [polyMBP, Vis.Cert.mirrorPoly, Vis.Cert.boundary_revPoly,
      Hardening.Invariance.boundary_mapPoly]
    rfl
  have hmir : ∀ p : Point, mirrorR n (mirrorR n p) = p := fun p => by
    simp only [mirrorR, Vis.Cert.reflX_apply]; ext <;> simp
  refine ⟨hsimple, ?_, fun u hu => hok u (List.mem_append_right _ hu), length_unitSpecs_snd n Φ,
    four_n_le_bigN, ?_, ?_, ?_⟩
  · -- orientation: the image of the top edge supports the mirrored polygon
    have hvb : ∀ v ∈ (polyCBP Φ n).vertices, v ∈ (polyCBP Φ n).boundary := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      refine ⟨i, hi, ?_⟩
      have : (polyCBP Φ n).vtx i = (polyCBP Φ n).vertices[i] := by
        simp [Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [Polygon.edge, ← this]
      exact Geometry.left_mem_segment _ _
    have hy : ∀ v ∈ (((constructBP Φ n).reverse.map (mirror n)).map ratPoint),
        v.2 ≤ (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ) := by
      intro v hv
      simp only [List.map_map, List.mem_map, List.mem_reverse, Function.comp] at hv
      obtain ⟨q, hq, rfl⟩ := hv
      have := h5 (ratPoint q) (hvb _ (List.mem_map_of_mem hq))
      simpa [ratPoint, mirror] using this
    rw [polyMBP_eq, constructBP_mirror hn] at hsimple ⊢
    rw [constructBP_mirror hn] at hy
    set A := [mirror n (vL n (numC Φ))] ++ (unitChainsBP n (numC Φ) 0 (unitSpecs n Φ).2).flatten
    have hl : (A ++ ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
        ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ).reverse.map (mirror n)))).map
          ratPoint = A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
            ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++
              rightPartBP n Φ).reverse.map (mirror n)).map ratPoint := by simp
    rw [hl] at hsimple hy ⊢
    obtain ⟨g1, g2⟩ := getD_mid (A := A.map ratPoint) (x := ratPoint (mirror n (tL n (numC Φ))))
      (y := ratPoint (mirror n (tR n (numC Φ))))
      (C := ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++ rightPartBP n Φ).reverse.map (mirror n)).map
        ratPoint)
    have hlen : (A.map ratPoint).length + 1 < (A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
        ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++
          rightPartBP n Φ).reverse.map (mirror n)).map ratPoint).length := by simp
    apply Polygon.interiorLeft_of_supporting_edge hsimple (i := (A.map ratPoint).length)
      (by simp only [Polygon.n]; omega)
    intro j hj
    have hyj := hy _ (show (A.map ratPoint ++ ratPoint (mirror n (tL n (numC Φ))) ::
        ratPoint (mirror n (tR n (numC Φ))) :: ((bottomWallBP n Φ ++ [wR n, vR n (numC Φ)] ++
          rightPartBP n Φ).reverse.map (mirror n)).map ratPoint).getD j (0, 0) ∈ _ by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem _)
    simp only [Polygon.vtx] at g1 g2 ⊢
    rw [Nat.mod_eq_of_lt (by simp [Polygon.n]), g1, g2]
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
  · have := side_fitBP (constructBP_mirror (Φ := Φ) hn)
    rw [polyMBP_eq]
    simpa using this
  · have := side_vtxBP (constructBP_mirror (Φ := Φ) hn)
    rw [polyMBP_eq]
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

end ArtGallery.BP

end