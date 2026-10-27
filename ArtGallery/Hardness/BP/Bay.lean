module

public import ArtGallery.Hardness.Sec5.MainArea.Cover

/-!
# Boundary-point variant: bays

A **bay** carries a guard segment on a horizontal boundary edge (the *floor*, interior above)
between two low side walls; each wall has one pinning *spike* (a convex vertex pointing into the
exterior), and a bay of a `one` constraint has a second spike on each wall
(`docs/boundary_point/design.md` §3.1).

Relative coordinates (`x0 = y0 = 0`, scale `1`), boundary order, interior above:
```
LS = (-1, 1/8)   LT = (-1/2, 1/16)                       left shoulder, left rim
  [(-1/2, 3/64)  O1 = (-4/7, 45/896)  (-1/2, 5/128)]     spike o1 (only for `one`)
(-1/2, 1/64)  T1 = (-5/6, 7/384)  (-1/2, 1/128)          spike w1
FL = (-1/2, 0)   FR = (2, 0)                              floor, contains the segment [0, 3/2]
(2, 1/128)  T2 = (7/3, 7/384)  (2, 1/64)                 spike w2
  [(2, 5/128)  O2 = (33/16, 25/512)  (2, 3/64)]          spike o2 (only for `one`)
RT = (2, 1/16)   RS = (5/2, 1/8)                          right rim, right shoulder
```
The bay is placed by a *frame* `F` (origin `(x0, y0)`, scale `s > 0`): the point with relative
coordinates `q` is `F.abs q = (x0 + s q.1, y0 + s q.2)`, and `F.rel` is the inverse map.

All statements are about an arbitrary simple counter-clockwise polygon `P` containing the bay
chain as consecutive vertices (`BayAt P one F a`); the statements that involve the region of `P`
also need that no other edge of `P` meets the open box `(-1, 5/2) × (0, 1/8)` (relative,
`BaySep P one F a`).

* **Witness triangles** (`vis_w1`, `vis_w2`, `vis_o1`, `vis_o2`): every point seeing a spike tip
  lies in the triangle spanned by the tip and the two points where the rays through the mouth
  corners of the spike meet the floor line (`T1`: `x ∈ [-1/4, 3/2]`, `T2`: `[0, 7/4]`, `O1`:
  `[-1/4, 1/2]`, `O2`: `[1/2, 7/4]`): the vertex cone at the tip, cut off by the floor edge.
  All four triangles lie in the box `[-5/6, 7/3] × [0, 1/16]` (`vis_box`).
* **Pinning on the boundary** (`spot_bay`, `spot_bay_one`): a point of the boundary of `P` seeing
  `T1` and `T2` lies on the floor segment `[0, 3/2] × {0}`; a point of the boundary seeing `O1`
  and `O2` is the point `(1/2, 0)` of value `1`.  (In the plane the triangles of `T1` and `T2`
  overlap above the segment: the pinning holds only for boundary points.)
* **Transport** (`bayAt_place`, `bayAt_mirror`): a bay placed by a further similarity
  `z ↦ c + k z` (`k > 0`) is a bay (frame `F.place c k`); the mirror image `x ↦ X − x` of a bay
  without `one` spikes, with the chain reversed, is the bay of the mirrored segment (frame
  `F.mirrorX X`).

Coverage (the guard on the floor sees the whole bay) is in `BayCover.lean`.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Irrational (HP hp hpo qdet mem_hp_cons mem_hp_nil mem_hpo_cons mem_hpo_nil)
open ArtGallery.Geometry (lerp)
open ArtGallery.Sec5 (Q2)

/-! ### Frames -/

/-- A similarity frame: origin `(x0, y0)`, scale `s` (positive in all applications). -/
structure Frame where
  /-- The abscissa of the origin. -/
  x0 : ℝ
  /-- The ordinate of the origin. -/
  y0 : ℝ
  /-- The scale. -/
  s : ℝ

namespace Frame

/-- Absolute coordinates of the point with relative coordinates `q`. -/
def abs (F : Frame) (q : Point) : Point := (F.x0 + F.s * q.1, F.y0 + F.s * q.2)

/-- Relative coordinates of the point `p`. -/
noncomputable def rel (F : Frame) (p : Point) : Point := ((p.1 - F.x0) / F.s, (p.2 - F.y0) / F.s)

/-- The point with rational relative coordinates `q`. -/
def pt (F : Frame) (q : Q2) : Point := F.abs (ratPoint q)

/-- The closed convex piece `{p | rel p ∈ hp l}`. -/
def pc (F : Frame) (l : List HP) : Set Point := {p | F.rel p ∈ hp l}

/-- The open convex piece `{p | rel p ∈ hpo l}`. -/
def pco (F : Frame) (l : List HP) : Set Point := {p | F.rel p ∈ hpo l}

variable {F : Frame}

theorem rel_abs (hs : F.s ≠ 0) (q : Point) : F.rel (F.abs q) = q := by
  ext <;> simp only [rel, abs] <;> field_simp <;> ring

theorem abs_rel (hs : F.s ≠ 0) (p : Point) : F.abs (F.rel p) = p := by
  ext <;> simp only [rel, abs] <;> field_simp <;> ring

theorem rel_pt (hs : F.s ≠ 0) (q : Q2) : F.rel (F.pt q) = ratPoint q := rel_abs hs _

theorem rel_fst (p : Point) : (F.rel p).1 = (p.1 - F.x0) / F.s := rfl
theorem rel_snd (p : Point) : (F.rel p).2 = (p.2 - F.y0) / F.s := rfl

/-- Determinants scale by `s²`. -/
theorem det_eq (hs : F.s ≠ 0) (p q r : Point) :
    det p q r = F.s ^ 2 * det (F.rel p) (F.rel q) (F.rel r) := by
  simp only [det, rel]; field_simp; ring

theorem det_pt_pt (hs : F.s ≠ 0) (A B : Q2) (p : Point) :
    det (F.pt A) (F.pt B) p = F.s ^ 2 * det (ratPoint A) (ratPoint B) (F.rel p) := by
  rw [det_eq hs, rel_pt hs, rel_pt hs]

theorem det_pt_right (hs : F.s ≠ 0) (A : Q2) (p q : Point) :
    det p q (F.pt A) = F.s ^ 2 * det (F.rel p) (F.rel q) (ratPoint A) := by
  rw [det_eq hs, rel_pt hs]

theorem rel_lerp (p q : Point) (t : ℝ) : F.rel (lerp p q t) = lerp (F.rel p) (F.rel q) t := by
  ext <;> simp only [rel, lerp] <;> ring

theorem abs_lerp (p q : Point) (t : ℝ) : F.abs (lerp p q t) = lerp (F.abs p) (F.abs q) t := by
  ext <;> simp only [abs, lerp] <;> ring

theorem rel_mem_segment {a b p : Point} (h : p ∈ ArtGallery.segment a b) :
    F.rel p ∈ ArtGallery.segment (F.rel a) (F.rel b) := by
  obtain ⟨t, h0, h1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 h
  rw [rel_lerp]; exact Geometry.lerp_mem_segment _ _ h0 h1

theorem abs_mem_segment {a b q : Point} (h : q ∈ ArtGallery.segment a b) :
    F.abs q ∈ ArtGallery.segment (F.abs a) (F.abs b) := by
  obtain ⟨t, h0, h1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 h
  rw [abs_lerp]; exact Geometry.lerp_mem_segment _ _ h0 h1

theorem rel_mem_segment_pt (hs : F.s ≠ 0) {A B : Q2} {p : Point}
    (h : p ∈ ArtGallery.segment (F.pt A) (F.pt B)) :
    F.rel p ∈ ArtGallery.segment (ratPoint A) (ratPoint B) := by
  have := rel_mem_segment (F := F) h
  rwa [rel_pt hs, rel_pt hs] at this

theorem smul_add_eq_lerp {p q : Point} {s t : ℝ} (hst : s + t = 1) :
    s • p + t • q = lerp p q t := by
  have : s = 1 - t := by linarith
  subst this; ext <;> simp [lerp] <;> ring

theorem convex_pc (l : List HP) : Convex ℝ (F.pc l) := by
  intro p hp' q hq' s t hs ht hst
  show F.rel (s • p + t • q) ∈ hp l
  rw [smul_add_eq_lerp hst, rel_lerp, ← smul_add_eq_lerp hst]
  exact Irrational.convex_hp l hp' hq' hs ht hst

theorem convex_pco (l : List HP) : Convex ℝ (F.pco l) := by
  intro p hp' q hq' s t hs ht hst
  show F.rel (s • p + t • q) ∈ hpo l
  rw [smul_add_eq_lerp hst, rel_lerp, ← smul_add_eq_lerp hst]
  exact Irrational.convex_hpo l hp' hq' hs ht hst

theorem continuous_rel : Continuous F.rel := by
  unfold rel; fun_prop

theorem isClosed_pc (l : List HP) : IsClosed (F.pc l) :=
  (Irrational.isClosed_hp l).preimage continuous_rel

theorem isOpen_pco (l : List HP) : IsOpen (F.pco l) :=
  (Irrational.isOpen_hpo l).preimage continuous_rel

/-- The closed piece lies in the closure of the open one (if the open one is nonempty). -/
theorem pc_subset_closure_pco {l : List HP} {z : Point} (hz : z ∈ F.pco l) :
    F.pc l ⊆ closure (F.pco l) := by
  refine Sec5.subset_closure_of_lerp (z := z) fun q hq t ht0 ht1 => ?_
  show F.rel (lerp q z t) ∈ hpo l
  rw [rel_lerp]
  intro c hc
  rw [Irrational.HP.val_lerp]
  have h1 := hq c hc; have h2 := hz c hc
  nlinarith [mul_pos ht0 h2, mul_nonneg (sub_nonneg.2 ht1.le) h1]

/-- A point with prescribed relative coordinates. -/
theorem mem_pco_of {l : List HP} {q : Point} (hs : F.s ≠ 0) (h : q ∈ hpo l) :
    F.abs q ∈ F.pco l := by
  show F.rel (F.abs q) ∈ hpo l
  rwa [rel_abs hs]

theorem mem_pc_of {l : List HP} {q : Point} (hs : F.s ≠ 0) (h : q ∈ hp l) : F.abs q ∈ F.pc l := by
  show F.rel (F.abs q) ∈ hp l
  rwa [rel_abs hs]

end Frame

/-! ### The bay chain -/

/-- Left shoulder and left rim. -/
def bayL : List Q2 := [(-1, 1/8), (-1/2, 1/16)]
/-- The spike `o1` (tip `O1 = (-4/7, 45/896)`). -/
def bayO1 : List Q2 := [(-1/2, 3/64), (-4/7, 45/896), (-1/2, 5/128)]
/-- The spike `w1` (tip `T1 = (-5/6, 7/384)`). -/
def bayW1 : List Q2 := [(-1/2, 1/64), (-5/6, 7/384), (-1/2, 1/128)]
/-- The floor `FL = (-1/2, 0)`, `FR = (2, 0)`. -/
def bayF : List Q2 := [(-1/2, 0), (2, 0)]
/-- The spike `w2` (tip `T2 = (7/3, 7/384)`). -/
def bayW2 : List Q2 := [(2, 1/128), (7/3, 7/384), (2, 1/64)]
/-- The spike `o2` (tip `O2 = (33/16, 25/512)`). -/
def bayO2 : List Q2 := [(2, 5/128), (33/16, 25/512), (2, 3/64)]
/-- Right rim and right shoulder. -/
def bayR : List Q2 := [(2, 1/16), (5/2, 1/8)]

/-- **The bay chain** (relative coordinates, boundary order): 12 vertices, 18 with the `one`
spikes. -/
def bayRel (one : Bool) : List Q2 :=
  bayL ++ (if one then bayO1 else []) ++ bayW1 ++ bayF ++ bayW2 ++ (if one then bayO2 else []) ++
    bayR

theorem length_bayRel (one : Bool) : (bayRel one).length = if one then 18 else 12 := by
  cases one <;> rfl

/-- The tip `T1` of spike `w1`. -/
def w1Rel : Q2 := (-5/6, 7/384)
/-- The tip `T2` of spike `w2`. -/
def w2Rel : Q2 := (7/3, 7/384)
/-- The tip `O1` of spike `o1`. -/
def o1Rel : Q2 := (-4/7, 45/896)
/-- The tip `O2` of spike `o2`. -/
def o2Rel : Q2 := (33/16, 25/512)
/-- The point of value `1` on the floor. -/
def g1Rel : Q2 := (1/2, 0)

/-- Index of `T1`. -/
def idxW1 (one : Bool) : ℕ := if one then 6 else 3
/-- Index of `FL` (the floor edge is `idxF → idxF + 1`). -/
def idxF (one : Bool) : ℕ := if one then 8 else 5
/-- Index of `T2`. -/
def idxW2 (one : Bool) : ℕ := if one then 11 else 8
/-- Index of `O1` (with `one` spikes). -/
def idxO1 : ℕ := 3
/-- Index of `O2` (with `one` spikes). -/
def idxO2 : ℕ := 14

/-- The bay chain reversed and mirrored at `x = 3/4` is the bay chain (without `one` spikes): the
mirror image of a bay (as in the left units) is the bay of the mirrored segment. -/
theorem bayRel_false_mirror :
    ((bayRel false).map fun q => ((3/2 : ℚ) - q.1, q.2)).reverse = bayRel false := by
  decide +kernel

/-! ### A bay inside a polygon -/

/-- The bay chain (placed by the frame `F`, scale `s > 0`) is the chain of consecutive vertices
`P.vtx ((a + j) % P.n)`, `j < |bayRel one|`, of `P`. -/
structure BayAt (P : Polygon) (one : Bool) (F : Frame) (a : ℕ) : Prop where
  /-- The scale is positive. -/
  pos : 0 < F.s
  /-- The vertices. -/
  vtx : ∀ j < (bayRel one).length, P.vtx ((a + j) % P.n) = F.pt ((bayRel one).getD j 0)

/-- The open box `(-1, 5/2) × (0, 1/8)` (relative coordinates). -/
def bayBox : Set Point := {q | -1 < q.1 ∧ q.1 < 5/2 ∧ 0 < q.2 ∧ q.2 < 1/8}

/-- **Separation**: no edge of `P` other than the bay chain edges meets the open box
`(-1, 5/2) × (0, 1/8)` (relative coordinates). -/
def BaySep (P : Polygon) (one : Bool) (F : Frame) (a : ℕ) : Prop :=
  ∀ i < P.n, (∀ j, j + 1 < (bayRel one).length → (a + j) % P.n ≠ i) →
    ∀ p ∈ P.edge i, F.rel p ∉ bayBox

section BayAt

variable {P : Polygon} {one : Bool} {F : Frame} {a : ℕ}

theorem BayAt.ne (hB : BayAt P one F a) : F.s ≠ 0 := hB.pos.ne'

theorem BayAt.sq_pos (hB : BayAt P one F a) : 0 < F.s ^ 2 := by have := hB.pos; positivity

/-- The bay vertices lie in the region of `P`. -/
theorem BayAt.vtx_mem_filled (hB : BayAt P one F a) (hP : P.Simple) {j : ℕ}
    (hj : j < (bayRel one).length) : F.pt ((bayRel one).getD j 0) ∈ P.filled := by
  have hn : 0 < P.n := by have := hP.1; omega
  rw [← hB.vtx j hj]
  exact Or.inl ⟨_, Nat.mod_lt _ hn, Geometry.left_mem_segment _ _⟩

/-- The bay vertices lie on the boundary of `P`. -/
theorem BayAt.vtx_mem_boundary (hB : BayAt P one F a) (hP : P.Simple) {j : ℕ}
    (hj : j < (bayRel one).length) : F.pt ((bayRel one).getD j 0) ∈ P.boundary := by
  have hn : 0 < P.n := by have := hP.1; omega
  rw [← hB.vtx j hj]
  exact ⟨_, Nat.mod_lt _ hn, Geometry.left_mem_segment _ _⟩

/-- Chain edge `j` of the bay. -/
theorem BayAt.edge_eq (hB : BayAt P one F a) {j : ℕ} (hj : j + 1 < (bayRel one).length) :
    P.edge ((a + j) % P.n) = ArtGallery.segment (F.pt ((bayRel one).getD j 0))
      (F.pt ((bayRel one).getD (j + 1) 0)) := by
  rw [Polygon.edge, chain_succ, hB.vtx j (by omega), hB.vtx (j + 1) hj]

/-- The floor segments of the bay lie on the boundary of `P`. -/
theorem BayAt.floor_mem_boundary (hB : BayAt P one F a) (hP : P.Simple) {p : Point}
    (h1 : (F.rel p).2 = 0) (h2 : -1/2 ≤ (F.rel p).1) (h3 : (F.rel p).1 ≤ 2) : p ∈ P.boundary := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hj : idxF one + 1 < (bayRel one).length := by cases one <;> decide
  refine ⟨_, Nat.mod_lt (a + idxF one) hn, ?_⟩
  rw [hB.edge_eq hj]
  have e1 : (bayRel one).getD (idxF one) 0 = (-1/2, 0) := by cases one <;> rfl
  have e2 : (bayRel one).getD (idxF one + 1) 0 = (2, 0) := by cases one <;> rfl
  rw [e1, e2, ← Frame.abs_rel hB.ne p]
  refine Frame.abs_mem_segment ⟨((F.rel p).1 + 1/2) / (5/2), by
    apply div_nonneg <;> linarith, by rw [div_le_one (by norm_num)]; linarith, ?_⟩
  ext <;> simp only [ratPoint] <;> push_cast <;> [field_simp; rw [h1]] <;> ring

/-- **Vertex cone at a bay vertex.**  If the bay vertex `B = v_j` (`1 ≤ j`, `j + 1 < |bay|`, with
neighbours `A`, `C`) is convex, every point seen from it is in its cone (relative coordinates). -/
theorem BayAt.cone (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < (bayRel one).length) {A B C : Q2}
    (hA : (bayRel one).getD (j - 1) 0 = A) (hB' : (bayRel one).getD j 0 = B)
    (hC : (bayRel one).getD (j + 1) 0 = C) (hconv : 0 < qdet A B C) {p : Point}
    (h : P.Sees (F.pt B) p) :
    0 ≤ det (ratPoint A) (ratPoint B) (F.rel p) ∧ 0 ≤ det (ratPoint B) (ratPoint C) (F.rel p) := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hs := hB.ne
  have hs2 := hB.sq_pos
  have hu : P.vtx (((a + j) % P.n + P.n - 1) % P.n) = F.pt A := by
    have := chain_prev hn a hj1
    unfold Jordan.prevIdx at this
    rw [this, hB.vtx (j - 1) (by omega), hA]
  have hw : P.vtx (((a + j) % P.n + 1) % P.n) = F.pt C := by
    rw [chain_succ, hB.vtx (j + 1) hj, hC]
  have hc : 0 < det (F.pt A) (F.pt B) (F.pt C) := by
    rw [Frame.det_pt_pt hs, Frame.rel_pt hs, Irrational.det_ratPoint]
    exact mul_pos hs2 (by exact_mod_cast hconv)
  have := sees_subset_cone hP hL (Nat.mod_lt _ hn) hu (by rw [hB.vtx j (by omega), hB']) hw hc h
  rw [Frame.det_pt_pt hs, Frame.det_pt_pt hs] at this
  exact ⟨(mul_nonneg_iff_of_pos_left hs2).1 this.1, (mul_nonneg_iff_of_pos_left hs2).1 this.2⟩

/-- **Blocking by a bay edge.**  A segment properly crossing the bay edge `v_j v_{j+1}` is not
contained in the region. -/
theorem BayAt.not_sees_cross (hB : BayAt P one F a) (hP : P.Simple) {j : ℕ}
    (hj : j + 1 < (bayRel one).length) {A B : Q2} (hA : (bayRel one).getD j 0 = A)
    (hB' : (bayRel one).getD (j + 1) 0 = B) {p q : Point}
    (h₁ : det (ratPoint A) (ratPoint B) (F.rel p) * det (ratPoint A) (ratPoint B) (F.rel q) < 0)
    (h₂ : det (F.rel p) (F.rel q) (ratPoint A) * det (F.rel p) (F.rel q) (ratPoint B) < 0) :
    ¬ P.Sees p q := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hs := hB.ne
  have hs2 := hB.sq_pos
  have hs4 : 0 < F.s ^ 2 * F.s ^ 2 := mul_pos hs2 hs2
  refine not_sees_of_proper_cross hP (Nat.mod_lt (a + j) hn) ?_ ?_
  · rw [chain_succ, hB.vtx j (by omega), hB.vtx (j + 1) hj, hA, hB', Frame.det_pt_pt hs,
      Frame.det_pt_pt hs]
    nlinarith
  · rw [chain_succ, hB.vtx j (by omega), hB.vtx (j + 1) hj, hA, hB', Frame.det_pt_right hs,
      Frame.det_pt_right hs]
    nlinarith

/-- An open piece avoiding every bay edge (`chainAvoids`) and lying in the box `bayBox` avoids the
boundary of `P`. -/
theorem BayAt.not_mem_boundary (hB : BayAt P one F a) (hS : BaySep P one F a)
    {l : List HP} (hc : Sec5.chainAvoids (bayRel one) l = true) {p : Point}
    (hp : F.rel p ∈ hpo l) (hbox : F.rel p ∈ bayBox) : p ∉ P.boundary := by
  have hs := hB.ne
  rintro ⟨i, hi, hpi⟩
  by_cases hch : ∃ j, j + 1 < (bayRel one).length ∧ (a + j) % P.n = i
  · obtain ⟨j, hj, rfl⟩ := hch
    rw [hB.edge_eq hj] at hpi
    exact Sec5.not_mem_hpo_of_chainAvoids hc hj (Frame.rel_mem_segment_pt hs hpi) hp
  · push Not at hch
    exact hS i hi (fun j hj h => hch j hj h) p hpi hbox

/-- **The floor blocks the view downwards.**  A point `w` of the bay above the floor line does
not see a point `p` below it if the line `w p` separates the two floor corners. -/
theorem BayAt.floor_block (hB : BayAt P one F a) (hP : P.Simple) {w : Q2} {p : Point}
    (hw : (0 : ℝ) < (w.2 : ℝ)) (hy : (F.rel p).2 < 0)
    (hl : det (ratPoint w) (F.rel p) (ratPoint (-1/2, 0)) < 0)
    (hr : 0 < det (ratPoint w) (F.rel p) (ratPoint (2, 0))) : ¬ P.Sees (F.pt w) p := by
  have hj : idxF one + 1 < (bayRel one).length := by cases one <;> decide
  refine hB.not_sees_cross hP hj (A := (-1/2, 0)) (B := (2, 0)) (by cases one <;> rfl)
    (by cases one <;> rfl) ?_ ?_
  · rw [Frame.rel_pt hB.ne]
    apply mul_neg_of_pos_of_neg
    · simp only [det, ratPoint]; push_cast; nlinarith
    · simp only [det, ratPoint]; push_cast; nlinarith
  · rw [Frame.rel_pt hB.ne]
    exact mul_neg_of_neg_of_pos hl hr

end BayAt

/-! ### The witness triangles -/

/-- The triangle of `T1`: `-2x - 256y + 3 ≥ 0`, `4x + 128y + 1 ≥ 0`, `y ≥ 0`. -/
def triW1 : List HP := [(-2, -256, 3), (4, 128, 1), (0, 1, 0)]
/-- The triangle of `T2`: `2x - 256y ≥ 0`, `-4x + 128y + 7 ≥ 0`, `y ≥ 0`. -/
def triW2 : List HP := [(2, -256, 0), (-4, 128, 7), (0, 1, 0)]
/-- The triangle of `O1`: `-6x - 128y + 3 ≥ 0`, `20x + 128y + 5 ≥ 0`, `y ≥ 0`. -/
def triO1 : List HP := [(-6, -128, 3), (20, 128, 5), (0, 1, 0)]
/-- The triangle of `O2`: `2x - 64y - 1 ≥ 0`, `-20x + 128y + 35 ≥ 0`, `y ≥ 0`. -/
def triO2 : List HP := [(2, -64, -1), (-20, 128, 35), (0, 1, 0)]

/-- Unfold determinants of explicit rational points into linear expressions. -/
macro "bdet" " at " h:ident : tactic =>
  `(tactic| (simp only [det, ratPoint, w1Rel, w2Rel, o1Rel, o2Rel] at $h:ident
             norm_num at $h:ident))

/-- Unfold membership in an explicit piece. -/
macro "bpc" " at " h:ident : tactic =>
  `(tactic| (simp only [triW1, triW2, triO1, triO2, mem_hp_cons, mem_hp_nil, mem_hpo_cons,
                mem_hpo_nil, and_true] at $h:ident
             norm_num at $h:ident))

/-- Reduce membership in an explicit piece to linear goals. -/
macro "bpc_goal" : tactic =>
  `(tactic| (simp only [triW1, triW2, triO1, triO2, mem_hp_cons, mem_hp_nil, mem_hpo_cons,
                mem_hpo_nil, and_true]
             push_cast
             repeat' apply And.intro))

section Triangles

variable {P : Polygon} {one : Bool} {F : Frame} {a : ℕ}

/-- **Witness triangle of `T1`.** -/
theorem vis_w1 (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) {p : Point}
    (h : P.Sees (F.pt w1Rel) p) : F.rel p ∈ hp triW1 := by
  have key : 0 ≤ det (ratPoint (-1/2, 1/64)) (ratPoint w1Rel) (F.rel p) ∧
      0 ≤ det (ratPoint w1Rel) (ratPoint (-1/2, 1/128)) (F.rel p) := by
    cases one
    · exact hB.cone hP hL (j := 3) (A := (-1/2, 1/64)) (B := w1Rel) (C := (-1/2, 1/128))
        (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet, w1Rel]) h
    · exact hB.cone hP hL (j := 6) (A := (-1/2, 1/64)) (B := w1Rel) (C := (-1/2, 1/128))
        (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet, w1Rel]) h
  obtain ⟨h1, h2⟩ := key
  bdet at h1; bdet at h2
  have hy : 0 ≤ (F.rel p).2 := by
    by_contra hy
    push Not at hy
    refine hB.floor_block hP (w := w1Rel) (by norm_num [w1Rel]) hy ?_ ?_ h
    · simp only [det, ratPoint, w1Rel]; norm_num; linarith
    · simp only [det, ratPoint, w1Rel]; norm_num; linarith
  bpc_goal <;> linarith

/-- **Witness triangle of `T2`.** -/
theorem vis_w2 (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) {p : Point}
    (h : P.Sees (F.pt w2Rel) p) : F.rel p ∈ hp triW2 := by
  have key : 0 ≤ det (ratPoint (2, 1/128)) (ratPoint w2Rel) (F.rel p) ∧
      0 ≤ det (ratPoint w2Rel) (ratPoint (2, 1/64)) (F.rel p) := by
    cases one
    · exact hB.cone hP hL (j := 8) (A := (2, 1/128)) (B := w2Rel) (C := (2, 1/64))
        (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet, w2Rel]) h
    · exact hB.cone hP hL (j := 11) (A := (2, 1/128)) (B := w2Rel) (C := (2, 1/64))
        (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet, w2Rel]) h
  obtain ⟨h1, h2⟩ := key
  bdet at h1; bdet at h2
  have hy : 0 ≤ (F.rel p).2 := by
    by_contra hy
    push Not at hy
    refine hB.floor_block hP (w := w2Rel) (by norm_num [w2Rel]) hy ?_ ?_ h
    · simp only [det, ratPoint, w2Rel]; norm_num; linarith
    · simp only [det, ratPoint, w2Rel]; norm_num; linarith
  bpc_goal <;> linarith

/-- **Witness triangle of `O1`.** -/
theorem vis_o1 (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft) {p : Point}
    (h : P.Sees (F.pt o1Rel) p) : F.rel p ∈ hp triO1 := by
  have key : 0 ≤ det (ratPoint (-1/2, 3/64)) (ratPoint o1Rel) (F.rel p) ∧
      0 ≤ det (ratPoint o1Rel) (ratPoint (-1/2, 5/128)) (F.rel p) :=
    hB.cone hP hL (j := 3) (A := (-1/2, 3/64)) (B := o1Rel) (C := (-1/2, 5/128)) (by norm_num)
      (by decide) rfl rfl rfl (by norm_num [qdet, o1Rel]) h
  obtain ⟨h1, h2⟩ := key
  bdet at h1; bdet at h2
  have hy : 0 ≤ (F.rel p).2 := by
    by_contra hy
    push Not at hy
    refine hB.floor_block hP (w := o1Rel) (by norm_num [o1Rel]) hy ?_ ?_ h
    · simp only [det, ratPoint, o1Rel]; norm_num; linarith
    · simp only [det, ratPoint, o1Rel]; norm_num; linarith
  bpc_goal <;> linarith

/-- **Witness triangle of `O2`.** -/
theorem vis_o2 (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft) {p : Point}
    (h : P.Sees (F.pt o2Rel) p) : F.rel p ∈ hp triO2 := by
  have key : 0 ≤ det (ratPoint (2, 5/128)) (ratPoint o2Rel) (F.rel p) ∧
      0 ≤ det (ratPoint o2Rel) (ratPoint (2, 3/64)) (F.rel p) :=
    hB.cone hP hL (j := 14) (A := (2, 5/128)) (B := o2Rel) (C := (2, 3/64)) (by norm_num)
      (by decide) rfl rfl rfl (by norm_num [qdet, o2Rel]) h
  obtain ⟨h1, h2⟩ := key
  bdet at h1; bdet at h2
  have hy : 0 ≤ (F.rel p).2 := by
    by_contra hy
    push Not at hy
    refine hB.floor_block hP (w := o2Rel) (by norm_num [o2Rel]) hy ?_ ?_ h
    · simp only [det, ratPoint, o2Rel]; norm_num; linarith
    · simp only [det, ratPoint, o2Rel]; norm_num; linarith
  bpc_goal <;> linarith

/-- The witnesses of a bay: `T1`, `T2`, and `O1`, `O2` for a bay with `one` spikes. -/
def bayWit (one : Bool) (F : Frame) : Set Point :=
  {F.pt w1Rel, F.pt w2Rel} ∪ {p | one = true ∧ (p = F.pt o1Rel ∨ p = F.pt o2Rel)}

/-- The position of a bay: the floor segment `[0, 3/2] × {0}`, resp. the point `(1/2, 0)` of value
`1` for a bay with `one` spikes. -/
def baySpot (one : Bool) (F : Frame) : Set Point :=
  if one then {F.pt g1Rel} else {p | (F.rel p).2 = 0 ∧ 0 ≤ (F.rel p).1 ∧ (F.rel p).1 ≤ 3/2}

/-- **Visibility box**: every point seeing a witness of the bay lies in `[-5/6, 7/3] × [0, 1/16]`
(relative coordinates). -/
theorem vis_box (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) {w : Point}
    (hw : w ∈ bayWit one F) {p : Point} (h : P.Sees w p) :
    -5/6 ≤ (F.rel p).1 ∧ (F.rel p).1 ≤ 7/3 ∧ 0 ≤ (F.rel p).2 ∧ (F.rel p).2 ≤ 1/16 := by
  rcases hw with hw | ⟨rfl, hw⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · have t := vis_w1 hB hP hL h; bpc at t
      obtain ⟨c1, c2, c3⟩ := t
      refine ⟨by linarith, by linarith, c3, by linarith⟩
    · have t := vis_w2 hB hP hL h; bpc at t
      obtain ⟨c1, c2, c3⟩ := t
      refine ⟨by linarith, by linarith, c3, by linarith⟩
  · rcases hw with rfl | rfl
    · have t := vis_o1 hB hP hL h; bpc at t
      obtain ⟨c1, c2, c3⟩ := t
      refine ⟨by linarith, by linarith, c3, by linarith⟩
    · have t := vis_o2 hB hP hL h; bpc at t
      obtain ⟨c1, c2, c3⟩ := t
      refine ⟨by linarith, by linarith, c3, by linarith⟩

/-- The witnesses of the bay are vertices of `P`. -/
theorem bayWit_mem_boundary (hB : BayAt P one F a) (hP : P.Simple) {w : Point}
    (hw : w ∈ bayWit one F) : w ∈ P.boundary := by
  rcases hw with hw | ⟨rfl, hw⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · cases one
      · exact hB.vtx_mem_boundary hP (j := 3) (by decide)
      · exact hB.vtx_mem_boundary hP (j := 6) (by decide)
    · cases one
      · exact hB.vtx_mem_boundary hP (j := 8) (by decide)
      · exact hB.vtx_mem_boundary hP (j := 11) (by decide)
  · rcases hw with rfl | rfl
    · exact hB.vtx_mem_boundary hP (j := 3) (by decide)
    · exact hB.vtx_mem_boundary hP (j := 14) (by decide)

theorem bayWit_mem_filled (hB : BayAt P one F a) (hP : P.Simple) {w : Point}
    (hw : w ∈ bayWit one F) : w ∈ P.filled :=
  Or.inl (bayWit_mem_boundary hB hP hw)

theorem w1_mem_bayWit : F.pt w1Rel ∈ bayWit one F := Or.inl (by simp)
theorem w2_mem_bayWit : F.pt w2Rel ∈ bayWit one F := Or.inl (by simp)
theorem o1_mem_bayWit : F.pt o1Rel ∈ bayWit true F := Or.inr ⟨rfl, Or.inl rfl⟩
theorem o2_mem_bayWit : F.pt o2Rel ∈ bayWit true F := Or.inr ⟨rfl, Or.inr rfl⟩

/-! ### Pinning on the boundary -/

/-- The open column `(-1/2, 2) × (0, 1/8)` above the floor (relative coordinates). -/
def colO : List HP := [(2, 0, 1), (-1, 0, 2), (0, 1, 0), (0, -8, 1)]

theorem chainAvoids_colO (one : Bool) : Sec5.chainAvoids (bayRel one) colO = true := by
  cases one <;> decide +kernel

/-- **The open column above the floor avoids the boundary.** -/
theorem colO_not_mem_boundary (hB : BayAt P one F a) (hS : BaySep P one F a)
    {p : Point} (hp : F.rel p ∈ hpo colO) : p ∉ P.boundary := by
  refine hB.not_mem_boundary hS (chainAvoids_colO one) hp ?_
  simp only [colO, mem_hpo_cons, mem_hpo_nil, and_true] at hp
  push_cast at hp
  obtain ⟨c1, c2, c3, c4⟩ := hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Pinning of the guard segment** (W1 on the boundary): a point of the boundary seeing `T1` and
`T2` lies on the floor segment `[0, 3/2] × {0}`. -/
theorem spot_bay (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {p : Point} (hpb : p ∈ P.boundary) (h1 : P.Sees p (F.pt w1Rel))
    (h2 : P.Sees p (F.pt w2Rel)) :
    (F.rel p).2 = 0 ∧ 0 ≤ (F.rel p).1 ∧ (F.rel p).1 ≤ 3/2 := by
  have t1 := vis_w1 hB hP hL (sees_comm.1 h1)
  have t2 := vis_w2 hB hP hL (sees_comm.1 h2)
  bpc at t1; bpc at t2
  obtain ⟨a1, a2, a3⟩ := t1
  obtain ⟨b1, b2, b3⟩ := t2
  rcases eq_or_lt_of_le a3 with e | hy
  · refine ⟨e.symm, ?_, ?_⟩ <;> linarith
  · exfalso
    refine colO_not_mem_boundary hB hS ?_ hpb
    simp only [colO, mem_hpo_cons, mem_hpo_nil, and_true]
    push_cast
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Pinning of the value-`1` point** (W1 on the boundary, `one` spikes): a point of the boundary
seeing `O1` and `O2` is the point `(1/2, 0)`. -/
theorem spot_bay_one (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P true F a) {p : Point} (hpb : p ∈ P.boundary) (h1 : P.Sees p (F.pt o1Rel))
    (h2 : P.Sees p (F.pt o2Rel)) : p = F.pt g1Rel := by
  have t1 := vis_o1 hB hP hL (sees_comm.1 h1)
  have t2 := vis_o2 hB hP hL (sees_comm.1 h2)
  bpc at t1; bpc at t2
  obtain ⟨a1, a2, a3⟩ := t1
  obtain ⟨b1, b2, b3⟩ := t2
  rcases eq_or_lt_of_le a3 with e | hy
  · have ex : (F.rel p).1 = 1/2 := by
      rw [← e] at a1 b1; linarith
    rw [← Frame.abs_rel hB.ne p, Frame.pt]
    congr 1
    ext
    · rw [ex]; simp [ratPoint, g1Rel]
    · rw [← e]; simp [ratPoint, g1Rel]
  · exfalso
    refine colO_not_mem_boundary hB hS ?_ hpb
    simp only [colO, mem_hpo_cons, mem_hpo_nil, and_true]
    push_cast
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Pinning** (W1 on the boundary): a point of the boundary seeing all witnesses of the bay lies
on its position. -/
theorem spot_bayWit (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {p : Point} (hpb : p ∈ P.boundary)
    (hall : ∀ w ∈ bayWit one F, P.Sees p w) : p ∈ baySpot one F := by
  cases one
  · exact spot_bay hB hP hL hS hpb (hall _ w1_mem_bayWit) (hall _ w2_mem_bayWit)
  · exact spot_bay_one hB hP hL hS hpb (hall _ o1_mem_bayWit) (hall _ o2_mem_bayWit)

/-- The position of the bay lies on the floor segment. -/
theorem baySpot_rel {p : Point} (hs : F.s ≠ 0) (hp : p ∈ baySpot one F) :
    (F.rel p).2 = 0 ∧ 0 ≤ (F.rel p).1 ∧ (F.rel p).1 ≤ 3/2 := by
  cases one
  · exact hp
  · rcases hp with rfl
    rw [Frame.rel_pt hs]
    simp only [ratPoint, g1Rel]; norm_num

/-- **Visibility box, absolute coordinates**: every point seeing a witness of the bay lies in
`[x0 − 5s/6, x0 + 7s/3] × [y0, y0 + s/16]`. -/
theorem vis_abs_box (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) {w : Point}
    (hw : w ∈ bayWit one F) {p : Point} (h : P.Sees w p) :
    F.x0 - 5/6 * F.s ≤ p.1 ∧ p.1 ≤ F.x0 + 7/3 * F.s ∧ F.y0 ≤ p.2 ∧ p.2 ≤ F.y0 + 1/16 * F.s := by
  obtain ⟨b1, b2, b3, b4⟩ := vis_box hB hP hL hw h
  have hs := hB.pos
  simp only [Frame.rel_fst, Frame.rel_snd] at b1 b2 b3 b4
  rw [le_div_iff₀ hs] at b1 b3
  rw [div_le_iff₀ hs] at b2 b4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Triangles

/-! ### Transport: similarities and mirror images -/

namespace Frame

/-- The frame `F` followed by the similarity `z ↦ c + k z`. -/
def place (c : Point) (k : ℝ) (F : Frame) : Frame := ⟨c.1 + k * F.x0, c.2 + k * F.y0, k * F.s⟩

theorem place_abs (c : Point) (k : ℝ) (F : Frame) (q : Point) :
    (F.place c k).abs q = (c.1 + k * (F.abs q).1, c.2 + k * (F.abs q).2) := by
  simp only [place, abs]; ext <;> ring

/-- The mirror image (`x ↦ X − x`) of the frame of a bay: the bay of the mirrored segment. -/
noncomputable def mirrorX (X : ℝ) (F : Frame) : Frame := ⟨X - F.x0 - 3/2 * F.s, F.y0, F.s⟩

theorem mirrorX_pt (X : ℝ) (F : Frame) (q : Q2) :
    (F.mirrorX X).pt ((3/2 : ℚ) - q.1, q.2) = (X - (F.pt q).1, (F.pt q).2) := by
  simp only [mirrorX, pt, abs, ratPoint]; push_cast; ext <;> ring

end Frame

/-- **A bay placed by a similarity** is a bay. -/
theorem bayAt_place {P : Polygon} {one : Bool} {F : Frame} {a : ℕ} (c : Point) {k : ℝ}
    (hk : 0 < k) (hs : 0 < F.s)
    (h : ∀ j < (bayRel one).length, P.vtx ((a + j) % P.n) =
      (c.1 + k * (F.pt ((bayRel one).getD j 0)).1, c.2 + k * (F.pt ((bayRel one).getD j 0)).2)) :
    BayAt P one (F.place c k) a :=
  ⟨mul_pos hk hs, fun j hj => by rw [h j hj, Frame.pt, Frame.pt, Frame.place_abs]⟩

theorem bayRel_false_getD_mirror : ∀ j < 12,
    (bayRel false).getD j 0 = ((3/2 : ℚ) - ((bayRel false).getD (11 - j) 0).1,
      ((bayRel false).getD (11 - j) 0).2) := by
  decide +kernel

/-- **The mirror image of a bay** (without `one` spikes, chain reversed, as in the left units) is
the bay of the mirrored segment. -/
theorem bayAt_mirror {P : Polygon} {F : Frame} {a : ℕ} (X : ℝ) (hs : 0 < F.s)
    (h : ∀ j < 12, P.vtx ((a + j) % P.n) =
      (X - (F.pt ((bayRel false).getD (11 - j) 0)).1, (F.pt ((bayRel false).getD (11 - j) 0)).2)) :
    BayAt P false (F.mirrorX X) a :=
  ⟨hs, fun j hj => by
    rw [h j hj, bayRel_false_getD_mirror j hj, Frame.mirrorX_pt]⟩

end ArtGallery.BP

end
