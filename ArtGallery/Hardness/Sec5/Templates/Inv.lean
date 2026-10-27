module

public import ArtGallery.Hardness.Sec5.Templates.InvMech
public import ArtGallery.Vis.StationaryGuard

/-!
# Section 5: the inversion template `x_a · x_b = 1` — template facts

Integer template coordinates (`InvData.lean`: the template point `T` of
`docs/section5/07_template_vertices.md` is `invD · T`).  Positions of the template: the receiver
segments `r_i = conv invRi` (value `x`: guard `invGp x = (D x, 0)`), `r_j = conv invRj` (value
`y`: guard `invGq y = (D (159/10 − y), D/10)`) and the stationary guard `g` (chain vertex 36).
Witnesses: `t0, t1, u0, u1` of each receiver pocket (chain vertices 2, 11, 6, 7 and 24, 33, 28,
29) and the two slot tips `qa, qb` of `g` (chain vertices 16, 20).

All statements are about an arbitrary simple counter-clockwise polygon `P` containing the
template chain (`ChainAt P invV a`) whose other edges avoid the region `invR`
(`SepAt P invV a invR`); `invPT` (the chain closed by the fixed stub) is such a polygon
(`invPT_simple`, `invPT_ccw`, `invPT_chain`, `invPT_sep`).  In a unit of the construction the
same holds after the similarity `z ↦ m + z / (S · invD)` (`Unit.lean`).

* (T-simple) `invPT_simple`;
* (T-cones) `inv_cone`: the vertex cone lemma at every witness vertex;
* (T-W1) `inv_spot_ri`, `inv_spot_rj`, `inv_spot_g`: a point seeing all witnesses of a position
  lies on it; conversely the points of a position see its witnesses (`inv_sees_riT0`, … in
  `InvData.lean`);
* (T-W3) template-internal: `inv_w3_*` (`InvData.lean`): no point of one position sees a
  witness of another;
* (T-W2) template-internal: `inv_w2_ri_rj`, `inv_w2_ri_g`, `inv_w2_rj_g`: no point sees two of
  the main witnesses `t1(r_i)`, `t1(r_j)`, `qb`; `V(t1)` lies in the pocket room
  (`inv_riT1_room`, `inv_rjT1_room`);
* (T-mech) `inv_umbra_iff`, `inv_nook_iff` (`InvMech.lean`), and the critical sets are not seen
  by `g` (`inv_g_not_sees_umbra`, `inv_g_not_sees_nook`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)

/-! ### The template polygon -/

/-- The template polygon `P_T`: the chain closed by the stub. -/
def invPT : Polygon := ⟨invVT.map intPoint⟩

theorem invPT_simple : invPT.Simple := simple_of_simpleCheck (by decide +kernel)

theorem invPT_ccw : invPT.InteriorLeft :=
  interiorLeft_of_lowB invPT_simple (i := 28) (by decide +kernel)

theorem invPT_chain : ChainAt invPT invV 0 := chainAt_append _ _

theorem invPT_sep : SepAt invPT invV 0 invR := sepAt_append (by decide) (by decide +kernel)

/-! ### Cones -/

section General

variable {P : Polygon} {a : ℕ}

/-- The witness vertices (and `g`). -/
def invWit : List ℕ := [2, 11, 6, 7, 24, 33, 28, 29, 16, 20, 36]

/-- **Witness cones (T-cones).**  Every witness vertex (and `g`) is a convex vertex of the chain;
a point it sees lies in its cone. -/
theorem inv_cone (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {j : ℕ}
    (hj : j ∈ invWit) {x : Point} (h : P.Sees (intPoint (cv invV j)) x) :
    0 ≤ det (intPoint (cv invV (j - 1))) (intPoint (cv invV j)) x ∧
      0 ≤ det (intPoint (cv invV j)) (intPoint (cv invV (j + 1))) x := by
  have hb : ∀ j ∈ invWit, 1 ≤ j ∧ j + 1 < invV.length ∧
      0 < idet (cv invV (j - 1)) (cv invV j) (cv invV (j + 1)) := by decide +kernel
  obtain ⟨h1, h2, h3⟩ := hb j hj
  exact chain_cone hP hL hC h1 h2 h3 h

/-- A point seeing a witness, with the seeing relation in either direction. -/
theorem inv_cone' (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {j : ℕ}
    (hj : j ∈ invWit) {x : Point} (h : P.Sees x (intPoint (cv invV j))) :
    0 ≤ det (intPoint (cv invV (j - 1))) (intPoint (cv invV j)) x ∧
      0 ≤ det (intPoint (cv invV j)) (intPoint (cv invV (j + 1))) x :=
  inv_cone hP hL hC hj (Polygon.sees_comm.1 h)

/-! ### W1: the witnesses pin the positions -/

theorem mem_hull_horiz {A B : IPt} (hb : A.2 = B.2) (hab : A.1 < B.1) {x : Point}
    (h2 : x.2 = A.2) (h0 : (A.1 : ℝ) ≤ x.1) (h1 : x.1 ≤ B.1) :
    x ∈ convexHull ℝ (intSet [A, B]) := by
  have hab' : (A.1 : ℝ) < B.1 := by exact_mod_cast hab
  have e : x = Geometry.lerp (intPoint A) (intPoint B) ((x.1 - A.1) / (B.1 - A.1)) := by
    ext
    · have hne : (B.1 : ℝ) - A.1 ≠ 0 := by linarith
      simp only [Geometry.lerp, intPoint_fst]; rw [div_mul_cancel₀ _ hne]; ring
    · simp only [Geometry.lerp, intPoint_snd, h2, hb]; ring
  rw [e]
  exact mem_hull_pair (div_nonneg (by linarith) (by linarith))
    ((div_le_one (by linarith)).2 (by linarith))

/-- **W1 for `r_i`**: a point seeing `t0, t1, u0, u1` of `r_i` lies on `r_i`. -/
theorem inv_spot_ri (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h0 : P.Sees x (intPoint (cv invV 2))) (h1 : P.Sees x (intPoint (cv invV 11)))
    (h2 : P.Sees x (intPoint (cv invV 6))) (h3 : P.Sees x (intPoint (cv invV 7))) :
    x ∈ convexHull ℝ (intSet invRi) := by
  have c0 := (inv_cone' hP hL hC (by decide) h0).1
  have c1 := (inv_cone' hP hL hC (by decide) h1).1
  have c2 := (inv_cone' hP hL hC (by decide) h2).1
  have c3 := (inv_cone' hP hL hC (by decide) h3).2
  have e1 : cv invV 1 = (0, 0) := by decide +kernel
  have e2 : cv invV 2 = (-501495790400, 0) := by decide +kernel
  have e10 : cv invV 10 = (1253739476000, 0) := by decide +kernel
  have e11 : cv invV 11 = (1755235266400, 0) := by decide +kernel
  have e5 : cv invV 5 = (250747895200, -501495790400) := by decide +kernel
  have e6 : cv invV 6 = (250747895200, -2507478952000) := by decide +kernel
  have e7 : cv invV 7 = (1002991580800, -2507478952000) := by decide +kernel
  have e8 : cv invV 8 = (1002991580800, -501495790400) := by decide +kernel
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (11 : ℕ) - 1 = 10 from rfl,
    show (6 : ℕ) - 1 = 5 from rfl, show (7 : ℕ) + 1 = 8 from rfl, e1, e2, e10, e11, e5, e6, e7,
    e8, det, intPoint] at c0 c1 c2 c3
  push_cast at c0 c1 c2 c3
  have hy : x.2 = 0 := by nlinarith
  refine mem_hull_horiz (A := (250747895200, 0)) (B := (1002991580800, 0)) rfl (by norm_num)
    (by rw [hy]; norm_num) (by push_cast; nlinarith) (by push_cast; nlinarith)

/-- **W1 for `r_j`**: a point seeing `t0, t1, u0, u1` of `r_j` lies on `r_j`. -/
theorem inv_spot_rj (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h0 : P.Sees x (intPoint (cv invV 24))) (h1 : P.Sees x (intPoint (cv invV 33)))
    (h2 : P.Sees x (intPoint (cv invV 28))) (h3 : P.Sees x (intPoint (cv invV 29))) :
    x ∈ convexHull ℝ (intSet invRj) := by
  have c0 := (inv_cone' hP hL hC (by decide) h0).1
  have c1 := (inv_cone' hP hL hC (by decide) h1).1
  have c2 := (inv_cone' hP hL hC (by decide) h2).1
  have c3 := (inv_cone' hP hL hC (by decide) h3).2
  have e23 : cv invV 23 = (6720043591360, 50149579040) := by decide +kernel
  have e24 : cv invV 24 = (6218547800960, 50149579040) := by decide +kernel
  have e32 : cv invV 32 = (7973783067360, 50149579040) := by decide +kernel
  have e33 : cv invV 33 = (8475278857760, 50149579040) := by decide +kernel
  have e27 : cv invV 27 = (6720043591360, -451346211360) := by decide +kernel
  have e28 : cv invV 28 = (952842001760, -11985749390560) := by decide +kernel
  have e29 : cv invV 29 = (1705085687360, -11985749390560) := by decide +kernel
  have e30 : cv invV 30 = (7472287276960, -451346211360) := by decide +kernel
  simp only [show (24 : ℕ) - 1 = 23 from rfl, show (33 : ℕ) - 1 = 32 from rfl,
    show (28 : ℕ) - 1 = 27 from rfl, show (29 : ℕ) + 1 = 30 from rfl, e23, e24, e32, e33, e27,
    e28, e29, e30, det, intPoint] at c0 c1 c2 c3
  push_cast at c0 c1 c2 c3
  have hy : x.2 = 50149579040 := by nlinarith
  rw [hy] at c2 c3
  refine mem_hull_horiz (A := (6970791486560, 50149579040)) (B := (7723035172160, 50149579040)) rfl
    (by norm_num) (by rw [hy]; norm_num) (by push_cast; nlinarith) (by push_cast; nlinarith)

/-- **W1 for the stationary guard** (stationary-guard lemma): the only point seeing both slot
tips `qa`, `qb` is `g`. -/
theorem inv_spot_g (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (ha : P.Sees x (intPoint (cv invV 16))) (hb : P.Sees x (intPoint (cv invV 20))) :
    x = intPoint (cv invV 36) := by
  have hn := n_pos_of_simple hP
  have d : ∀ {u v w : IPt}, 0 < idet u v w → 0 < det (intPoint u) (intPoint v) (intPoint w) := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have d' : ∀ {u v w : IPt}, 0 ≤ idet u v w → 0 ≤ det (intPoint u) (intPoint v) (intPoint w) := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have dn : ∀ {u v w : IPt}, idet u v w < 0 → det (intPoint u) (intPoint v) (intPoint w) < 0 := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have hqa := hC.prev_vtx hP (j := 16) (by norm_num) (by decide)
  have hqb := hC.prev_vtx hP (j := 20) (by norm_num) (by decide)
  refine sg_unique_of_vertices hP hL (j₀ := (a + 35) % P.n) (j₁ := (a + 36) % P.n)
    (ia := (a + 16) % P.n) (ib := (a + 20) % P.n) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
    (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (hC.edge_vtx (j := 35) (by decide)).1
    (hC.edge_vtx (j := 35) (by decide)).2 (hC.edge_vtx (j := 36) (by decide)).1
    (hC.edge_vtx (j := 36) (by decide)).2 hqa (hC 16 (by decide)) (hC.edge_vtx (j := 16) (by decide)).2
    (d (by decide +kernel)) hqb (hC 20 (by decide)) (hC.edge_vtx (j := 20) (by decide)).2
    (d (by decide +kernel)) (d (by decide +kernel)) (d (by decide +kernel)) (d (by decide +kernel))
    (d (by decide +kernel)) (d (by decide +kernel)) (d' (by decide +kernel)) (d' (by decide +kernel))
    (d' (by decide +kernel)) (d' (by decide +kernel)) (dn (by decide +kernel)) (dn (by decide +kernel))
    (d (by decide +kernel)) (d (by decide +kernel)) ha hb

/-! ### The critical sets are not seen by `g` -/

theorem inv_g_det_axis (z : Point) :
    det (intPoint (cv invV 36)) (intPoint (cv invV 37)) z = -40335400 * invLu.val z := by
  have e36 : cv invV 36 = (8023932646400, 3396868759800) := by decide +kernel
  have e37 : cv invV 37 = (6268697380000, 2650784866000) := by decide +kernel
  rw [e36, e37]
  simp only [det, intPoint, invLu, Irrational.HP.val]; push_cast; ring

/-- `g` sees no point strictly above the umbra axis. -/
theorem inv_g_not_sees_umbra (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a)
    {z : Point} (hz : 0 < invLu.val z) : ¬ P.Sees (intPoint (cv invV 36)) z := by
  intro hs
  have := (inv_cone hP hL hC (j := 36) (by decide) hs).2
  rw [show (36 : ℕ) + 1 = 37 from rfl, inv_g_det_axis] at this
  linarith

/-- `g` sees no point of the nook zone. -/
theorem inv_g_not_sees_nook (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) :
    ∀ w ∈ convexHull ℝ (intSet invZn), ¬ P.Sees (intPoint (cv invV 36)) w :=
  not_sees_of_outCone hP hL hC (j := 36) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ### W2: the main witnesses have disjoint visibility sets -/

/-- The pocket room of `r_i`: chain vertices `0 … 13`, door `V13 → V0`. -/
def invKi : Polygon := ⟨(subList invV 0 13).map intPoint⟩

/-- The pocket room of `r_j`: chain vertices `22 … 35`, door `V35 → V22`. -/
def invKj : Polygon := ⟨(subList invV 22 13).map intPoint⟩

theorem invKi_simple : invKi.Simple := simple_of_simpleCheck (by decide +kernel)

theorem invKj_simple : invKj.Simple := simple_of_simpleCheck (by decide +kernel)

theorem invKi_ccw : invKi.InteriorLeft := interiorLeft_of_supportB invKi_simple (i := 13) (by decide +kernel)

theorem invKj_ccw : invKj.InteriorLeft := interiorLeft_of_supportB invKj_simple (i := 13) (by decide +kernel)

/-- **`V(t1)` of `r_i` lies in its pocket room.** -/
theorem inv_riT1_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h : P.Sees (intPoint (cv invV 11)) x) : x ∈ invKi.filled := by
  have hR := subList_isRoom hP hL hC (k := 0) (m := 13) (by decide) invKi_simple invKi_ccw
  have hn := n_pos_of_simple hP
  have hv : intPoint (cv invV 11) ∈ invKi.filled := by
    have : invKi.vtx 11 = intPoint (cv invV 11) := by
      rw [invKi, vtx_map_intPoint, subList_getD (by norm_num)]
    rw [← this]
    exact Or.inl ⟨11, by rw [invKi, n_map_intPoint, subList_length (by decide)]; norm_num,
      Geometry.left_mem_segment _ _⟩
  refine Polygon.sees_mem_room hP hL (i := (a + 11) % P.n) (Nat.mod_lt _ hn)
    (hC.prev_vtx hP (by norm_num) (by decide)) (hC 11 (by decide)) (hC.edge_vtx (by decide)).2
    (by rw [det_intPoint]; exact_mod_cast (show 0 < idet (cv invV 10) (cv invV 11) (cv invV 12) by
      decide +kernel)) hR hv ?_ h
  intro y hy
  refine cone_disjoint_segment_left ?_ ?_ y hy
  · rw [det_intPoint]; exact_mod_cast (show idet (cv invV 11) (cv invV 12) (cv invV 13) < 0 by
      decide +kernel)
  · rw [det_intPoint]; exact_mod_cast (show idet (cv invV 11) (cv invV 12) (cv invV 0) < 0 by
      decide +kernel)

/-- **`V(t1)` of `r_j` lies in its pocket room.** -/
theorem inv_rjT1_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h : P.Sees (intPoint (cv invV 33)) x) : x ∈ invKj.filled := by
  have hR := subList_isRoom hP hL hC (k := 22) (m := 13) (by decide) invKj_simple invKj_ccw
  have hn := n_pos_of_simple hP
  have hv : intPoint (cv invV 33) ∈ invKj.filled := by
    have : invKj.vtx 11 = intPoint (cv invV 33) := by
      rw [invKj, vtx_map_intPoint, subList_getD (by norm_num)]
    rw [← this]
    exact Or.inl ⟨11, by rw [invKj, n_map_intPoint, subList_length (by decide)]; norm_num,
      Geometry.left_mem_segment _ _⟩
  refine Polygon.sees_mem_room hP hL (i := (a + 33) % P.n) (Nat.mod_lt _ hn)
    (hC.prev_vtx hP (by norm_num) (by decide)) (hC 33 (by decide)) (hC.edge_vtx (by decide)).2
    (by rw [det_intPoint]; exact_mod_cast (show 0 < idet (cv invV 32) (cv invV 33) (cv invV 34) by
      decide +kernel)) hR hv ?_ h
  intro y hy
  refine cone_disjoint_segment_left ?_ ?_ y hy
  · rw [det_intPoint]; exact_mod_cast (show idet (cv invV 33) (cv invV 34) (cv invV 35) < 0 by
      decide +kernel)
  · rw [det_intPoint]; exact_mod_cast (show idet (cv invV 33) (cv invV 34) (cv invV 22) < 0 by
      decide +kernel)

/-- The pocket room of `r_i` lies left of the line `u0(r_j) → mouthL(r_j)`, with margin. -/
theorem invKi_side : invKi.filled ⊆ {x | 0 ≤ (lineHP (cv invV 28) (cv invV 22)).val x - 1} := by
  have := filled_subset_hp (subList invV 0 13) (c := ((lineHP (cv invV 28) (cv invV 22)).1,
    (lineHP (cv invV 28) (cv invV 22)).2.1, (lineHP (cv invV 28) (cv invV 22)).2.2 - 1))
    (by decide +kernel) (by decide +kernel)
  intro x hx
  have h := this hx
  simp only [mem_ofPred_eq, Irrational.HP.val] at h ⊢
  push_cast at h ⊢
  linarith

/-- The pocket room of `r_j` lies weakly right of the line `u0(r_j) → mouthL(r_j)`. -/
theorem invKj_side : invKj.filled ⊆ {x | (lineHP (cv invV 28) (cv invV 22)).val x ≤ 0} := by
  have := filled_subset_hp (subList invV 22 13) (c := negHP (lineHP (cv invV 28) (cv invV 22)))
    (by decide +kernel) (by decide +kernel)
  intro x hx
  have h := this hx
  simp only [mem_ofPred_eq, negHP_val] at h ⊢
  linarith

/-- **W2 (`r_i`, `r_j`)**: no point sees both `t1(r_i)` and `t1(r_j)`. -/
theorem inv_w2_ri_rj (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h1 : P.Sees (intPoint (cv invV 11)) x) (h2 : P.Sees (intPoint (cv invV 33)) x) : False := by
  have a1 := invKi_side (inv_riT1_room hP hL hC h1)
  have a2 := invKj_side (inv_rjT1_room hP hL hC h2)
  simp only [mem_ofPred_eq] at a1 a2
  linarith

/-- The cone of `qb` lies to the right of `x = qb.x` and above the line through `qb` with
direction `(5, 4)`. -/
theorem inv_qb_cone (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h : P.Sees (intPoint (cv invV 20)) x) :
    ((cv invV 20).1 : ℝ) ≤ x.1 ∧
      0 ≤ det (intPoint (cv invV 20)) (intPoint ((cv invV 20).1 + 5, (cv invV 20).2 + 4)) x := by
  have hc := inv_cone hP hL hC (j := 20) (by decide) h
  have hconv : 0 < det (intPoint (cv invV 19)) (intPoint (cv invV 20)) (intPoint (cv invV 21)) := by
    rw [det_intPoint]; exact_mod_cast (show 0 < idet (cv invV 19) (cv invV 20) (cv invV 21) by
      decide +kernel)
  have hx : x ∈ cornerCone (intPoint (cv invV 19)) (intPoint (cv invV 20)) (intPoint (cv invV 21)) :=
    hc
  constructor
  · have := det_le_of_mem_cone hconv hx (c := intPoint (0, 0)) (d := intPoint (0, -1))
      (by rw [det_intPoint, det_intPoint]; exact_mod_cast (show idet (0, 0) (0, -1) (cv invV 20) ≤
        idet (0, 0) (0, -1) (cv invV 19) by decide +kernel))
      (by rw [det_intPoint, det_intPoint]; exact_mod_cast (show idet (0, 0) (0, -1) (cv invV 20) ≤
        idet (0, 0) (0, -1) (cv invV 21) by decide +kernel))
    simp only [det, intPoint] at this; push_cast at this; linarith
  · have := det_le_of_mem_cone hconv hx (c := intPoint (cv invV 20))
      (d := intPoint ((cv invV 20).1 + 5, (cv invV 20).2 + 4))
      (by rw [det_intPoint, det_intPoint]; exact_mod_cast (show idet (cv invV 20)
        ((cv invV 20).1 + 5, (cv invV 20).2 + 4) (cv invV 20) ≤ idet (cv invV 20)
        ((cv invV 20).1 + 5, (cv invV 20).2 + 4) (cv invV 19) by decide +kernel))
      (by rw [det_intPoint, det_intPoint]; exact_mod_cast (show idet (cv invV 20)
        ((cv invV 20).1 + 5, (cv invV 20).2 + 4) (cv invV 20) ≤ idet (cv invV 20)
        ((cv invV 20).1 + 5, (cv invV 20).2 + 4) (cv invV 21) by decide +kernel))
    rwa [Geometry.det_self_outer] at this

/-- **W2 (`r_i`, `g`)**: no point sees both `t1(r_i)` and `qb`. -/
theorem inv_w2_ri_g (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h1 : P.Sees (intPoint (cv invV 11)) x) (h2 : P.Sees (intPoint (cv invV 20)) x) : False := by
  have a1 := filled_subset_hp (subList invV 0 13) (c := (-1, 0, (cv invV 20).1 - 1))
    (by decide +kernel) (by decide +kernel) (inv_riT1_room hP hL hC h1)
  have a2 := (inv_qb_cone hP hL hC h2).1
  simp only [mem_ofPred_eq, Irrational.HP.val] at a1
  push_cast at a1
  linarith

/-- **W2 (`r_j`, `g`)**: no point sees both `t1(r_j)` and `qb`. -/
theorem inv_w2_rj_g (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a) {x : Point}
    (h1 : P.Sees (intPoint (cv invV 33)) x) (h2 : P.Sees (intPoint (cv invV 20)) x) : False := by
  have a1 := filled_subset_hp (subList invV 22 13)
    (c := (let g := lineHP (cv invV 20) ((cv invV 20).1 + 5, (cv invV 20).2 + 4)
      (-g.1, -g.2.1, -g.2.2 - 1))) (by decide +kernel) (by decide +kernel)
    (inv_rjT1_room hP hL hC h1)
  have a2 := (inv_qb_cone hP hL hC h2).2
  rw [← lineHP_val] at a2
  simp only [mem_ofPred_eq, Irrational.HP.val] at a1 a2
  push_cast at a1 a2
  linarith

end General

end ArtGallery.Sec5.Tmpl

end
