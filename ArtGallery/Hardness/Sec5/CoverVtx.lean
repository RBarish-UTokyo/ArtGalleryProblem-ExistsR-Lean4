module

public import ArtGallery.Hardness.Sec5.CoverSide

/-!
# Section 5, sufficiency (vi): special vertices and edges of the global polygon

The hexagon edges `w_r v_r`, `t_r t_l`, `v_l w_l` are edges of `polyC` (`diagR_bdry`,
`top_bdry`, `diagL_bdry`), and the two vertical unit lines satisfy the hypotheses of
`side_vertical` (`right_vertical` in `polyC`, `left_vertical` in the mirrored polygon `polyM`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.CoverM

open ArtGallery Set Polygon
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

variable {Φ : List ETRINV.Constraint} {n : ℕ}

theorem unitStart_end (k st : ℕ) (us : List UnitSpec) :
    unitStart n k us st us.length = st + ((unitChains n k 0 us).flatten).length := by
  simp only [unitStart]
  rw [show us.length = (unitChains n k 0 us).length from (length_unitChains _ _ _ _).symm,
    List.take_length, List.length_flatten]

theorem edge_of_vtx {P : Polygon} {i : ℕ} (hi : i + 1 < P.n) {a b : Point} (ha : P.vtx i = a)
    (hb : P.vtx (i + 1) = b) : ArtGallery.segment a b ⊆ P.boundary := by
  intro p hp
  refine ⟨i, by omega, ?_⟩
  rw [Polygon.edge, Nat.mod_eq_of_lt hi, ha, hb]; exact hp

theorem edge_of_vtx_last {P : Polygon} (hP : 0 < P.n) {a b : Point} (ha : P.vtx (P.n - 1) = a)
    (hb : P.vtx 0 = b) : ArtGallery.segment a b ⊆ P.boundary := by
  intro p hp
  refine ⟨P.n - 1, by omega, ?_⟩
  rw [Polygon.edge, show P.n - 1 + 1 = P.n by omega, Nat.mod_self, ha, hb]; exact hp

theorem vtx_mem_bdry {P : Polygon} {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.boundary :=
  ⟨i, hi, by rw [Polygon.edge]; exact Geometry.left_mem_segment _ _⟩

section
variable (hn : 0 < n)
include hn

/-- The right flatten of the unit chains. -/
abbrev rFl (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  (unitChains n (numC Φ) 0 (unitSpecs n Φ).1).flatten

/-- The left flatten of the unit chains. -/
abbrev lFl (Φ : List ETRINV.Constraint) (n : ℕ) : List Q2 :=
  (unitChains n (numC Φ) 0 (unitSpecs n Φ).2).flatten

theorem polyC_eq_right : polyC Φ n = Polygon.mk (((bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++
    rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++ [vL n (numC Φ)])).map ratPoint) := by
  rw [polyC, construct_right hn]

theorem polyC_n : (polyC Φ n).n = (bottomWall n Φ).length + 2 + (rFl Φ n).length + 2 +
    (leftPart n Φ).length + 1 := by
  rw [polyC_eq_right hn]
  simp only [Polygon.n, List.length_map, List.length_append, List.length_cons, List.length_nil]
  omega

theorem vtx_wR : (polyC Φ n).vtx (bottomWall n Φ).length = pwR n := by
  have := vtx_split (A := bottomWall n Φ) (C := [wR n, vR n (numC Φ)])
    (B := rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++ [vL n (numC Φ)]))
    (i := 0) (by simp)
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  rw [Nat.add_zero] at this
  rw [this]; simp [ratPoint, wR, pwR]

theorem vtx_vR : (polyC Φ n).vtx ((bottomWall n Φ).length + 1) = pvR Φ n := by
  have := vtx_split (A := bottomWall n Φ) (C := [wR n, vR n (numC Φ)])
    (B := rFl Φ n ++ ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ ++ [vL n (numC Φ)]))
    (i := 1) (by simp)
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  rw [this]; simp [ratPoint, vR, pvR, sS]

theorem vtx_tRL (i : ℕ) (hi : i < 2) : (polyC Φ n).vtx ((bottomWall n Φ).length + 2 +
    (rFl Φ n).length + i) = ratPoint ([tR n (numC Φ), tL n (numC Φ)].getD i 0) := by
  have := vtx_split (A := (bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n)
    (C := [tR n (numC Φ), tL n (numC Φ)]) (B := leftPart n Φ ++ [vL n (numC Φ)]) (i := i)
    (by simpa using hi)
  have hA : ((bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n).length =
      (bottomWall n Φ).length + 2 + (rFl Φ n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hA] at this
  rw [polyC_eq_right hn]
  simp only [List.append_assoc] at this ⊢
  exact this

theorem vtx_tR : (polyC Φ n).vtx (unitStart n (numC Φ) (unitSpecs n Φ).1
    ((bottomWall n Φ).length + 2) (unitSpecs n Φ).1.length) = ptR Φ n := by
  rw [unitStart_end, ← Nat.add_zero ((bottomWall n Φ).length + 2 + _), vtx_tRL hn 0 (by omega)]
  simp [ratPoint, tR, ptR, sTop, sS]

theorem vtx_tL : (polyC Φ n).vtx (unitStart n (numC Φ) (unitSpecs n Φ).1
    ((bottomWall n Φ).length + 2) (unitSpecs n Φ).1.length + 1) = ptL Φ n := by
  rw [unitStart_end, vtx_tRL hn 1 (by omega)]
  simp [ratPoint, tL, ptL, sTop, sS, XL, xMirror, sXL]

theorem vtx_vL : (polyC Φ n).vtx ((polyC Φ n).n - 1) = pvL Φ n := by
  have := vtx_split (A := (bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n ++
      ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ)) (C := [vL n (numC Φ)]) (B := [])
    (i := 0) (by simp)
  have hA : ((bottomWall n Φ ++ [wR n, vR n (numC Φ)]) ++ rFl Φ n ++
      ([tR n (numC Φ), tL n (numC Φ)] ++ leftPart n Φ)).length + 0 = (polyC Φ n).n - 1 := by
    rw [polyC_n hn]; simp; omega
  rw [hA] at this
  rw [polyC_eq_right hn]
  rw [polyC_eq_right hn] at this
  simp only [List.append_assoc, List.append_nil, List.cons_append, List.nil_append] at this ⊢
  rw [this]; simp [ratPoint, vL, pvL, sS, XL, xMirror, sXL]

theorem bottomWall_ne : bottomWall n Φ ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_bottomWall, List.length_nil] at this
  have h1 := pocketStart_succ (n := n) (Φ := Φ) 0
  have h2 := pocketStart_mono (n := n) (Φ := Φ) (show 0 + 1 ≤ 4 * n by omega)
  have h3 := length_pocketRel_pos (slotOne n Φ 0)
  omega

theorem vtx_wL : (polyC Φ n).vtx 0 = pwL := by
  have h := bottom_fst hn Φ
  obtain ⟨b, B', hB'⟩ := List.exists_cons_of_ne_nil (bottomWall_ne (Φ := Φ) hn)
  rw [hB'] at h
  rw [polyC_eq_right hn, Irrational.vtx_map_ratPoint, hB']
  simp only [List.cons_append, List.getD_cons_zero]
  simp only [List.cons_append, List.map_cons] at h
  exact h

/-- The right diagonal `w_r v_r` is an edge. -/
theorem diagR_bdry : ArtGallery.segment (pwR n) (pvR Φ n) ⊆ (polyC Φ n).boundary :=
  edge_of_vtx (by rw [polyC_n hn]; omega) (vtx_wR hn) (vtx_vR hn)

/-- The top `t_r t_l` is an edge. -/
theorem top_bdry : ArtGallery.segment (ptR Φ n) (ptL Φ n) ⊆ (polyC Φ n).boundary := by
  refine edge_of_vtx ?_ (vtx_tR hn) (vtx_tL hn)
  rw [unitStart_end, polyC_n hn]; simp only [rFl]; omega

/-- The left diagonal `v_l w_l` is an edge (the closing edge). -/
theorem diagL_bdry : ArtGallery.segment (pvL Φ n) pwL ⊆ (polyC Φ n).boundary :=
  edge_of_vtx_last (by rw [polyC_n hn]; omega) (vtx_vL hn) (vtx_wL hn)

/-- **The right vertical line** `x = S`: boundary or an entrance of a right unit. -/
theorem right_vertical (hΦ : ∀ c ∈ Φ, c.VarsLt n) {y : ℝ} (hy1 : sS Φ n ≤ y)
    (hy2 : y ≤ sTop Φ n) :
    (sS Φ n, y) ∈ (polyC Φ n).boundary ∨ ∃ m, ∃ hm : m < (unitSpecs n Φ).1.length,
      (sS Φ n, y) ∈ (unitInput n (numC Φ) m ((unitSpecs n Φ).1[m]'hm)).entrance := by
  have hQ := rightSide hΦ hn
  have hv0 : (polyC Φ n).vtx ((bottomWall n Φ).length + 2 - 1) =
      ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) := by
    rw [show (bottomWall n Φ).length + 2 - 1 = (bottomWall n Φ).length + 1 by omega, vtx_vR hn]
    rfl
  have hlt : unitStart n (numC Φ) (unitSpecs n Φ).1 ((bottomWall n Φ).length + 2)
      (unitSpecs n Φ).1.length < (polyC Φ n).n := by
    rw [unitStart_end, polyC_n hn]; simp only [rFl]; omega
  exact side_vertical hQ (by omega) hv0 (vtx_tR hn) hlt hy1 hy2

/-! ### The mirrored polygon -/

theorem polyM_eq' : polyM Φ n = Polygon.mk ((([mirror n (vL n (numC Φ))] ++ lFl Φ n) ++
    ([mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))] ++
      ((bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ).reverse.map (mirror n)))).map
        ratPoint) := by
  rw [polyM_eq, construct_mirror hn]

theorem polyM_n : (polyM Φ n).n = (polyC Φ n).n := by
  simp [polyM, Vis.Cert.mirrorPoly, Vis.Cert.revPoly, Hardening.Invariance.mapPoly, Polygon.n]

theorem polyM_bdry : (polyM Φ n).boundary = mirrorR n '' (polyC Φ n).boundary := by
  simp only [polyM, Vis.Cert.mirrorPoly, Vis.Cert.boundary_revPoly,
    Hardening.Invariance.boundary_mapPoly]
  rfl

theorem polyM_vtx0 : (polyM Φ n).vtx 0 = ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) := by
  rw [polyM_eq' hn, Irrational.vtx_map_ratPoint]
  simp [ratPoint, mirror, vL, XL, xMirror]

theorem polyM_vtx_t : (polyM Φ n).vtx (1 + (lFl Φ n).length) =
    ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
  have := vtx_split (A := [mirror n (vL n (numC Φ))] ++ lFl Φ n)
    (C := [mirror n (tL n (numC Φ)), mirror n (tR n (numC Φ))])
    (B := (bottomWall n Φ ++ [wR n, vR n (numC Φ)] ++ rightPart n Φ).reverse.map (mirror n))
    (i := 0) (by simp)
  have hA : ([mirror n (vL n (numC Φ))] ++ lFl Φ n).length + 0 = 1 + (lFl Φ n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [hA] at this
  rw [polyM_eq' hn]
  simp only [List.append_assoc] at this ⊢
  rw [this]; simp [ratPoint, mirror, tL, XL, xMirror]

/-- **The left vertical line** (working frame of the left units, in `polyM`). -/
theorem left_vertical (hΦ : ∀ c ∈ Φ, c.VarsLt n) {y : ℝ} (hy1 : sS Φ n ≤ y)
    (hy2 : y ≤ sTop Φ n) :
    (sS Φ n, y) ∈ (polyM Φ n).boundary ∨ ∃ m, ∃ hm : m < (unitSpecs n Φ).2.length,
      (sS Φ n, y) ∈ (unitInput n (numC Φ) m ((unitSpecs n Φ).2[m]'hm)).entrance := by
  have hQ := leftSide hΦ hn
  have hv0 : (polyM Φ n).vtx (1 - 1) = ((S n (numC Φ) : ℝ), (S n (numC Φ) : ℝ)) :=
    polyM_vtx0 hn
  have hvt : (polyM Φ n).vtx (unitStart n (numC Φ) (unitSpecs n Φ).2 1 (unitSpecs n Φ).2.length) =
      ((S n (numC Φ) : ℝ), sTop Φ n) := by
    rw [unitStart_end, polyM_vtx_t hn]; rfl
  have hlt : unitStart n (numC Φ) (unitSpecs n Φ).2 1 (unitSpecs n Φ).2.length < (polyM Φ n).n := by
    rw [unitStart_end, polyM_eq' hn]
    simp only [Polygon.n, List.length_map, List.length_append, List.length_cons, List.length_nil,
      lFl]
    omega
  exact side_vertical hQ le_rfl hv0 hvt hlt hy1 hy2

end

end ArtGallery.Sec5.CoverM

end
