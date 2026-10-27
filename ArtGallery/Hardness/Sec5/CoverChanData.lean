module

public import ArtGallery.Hardness.Sec5.CoverChanTools
public import ArtGallery.Hardness.Sec5.Corridor.Cover
public import ArtGallery.Stade.Exit

/-!
# Section 5, sufficiency (vi): the channel certificate of a template

For a template (chain `V`, scale `D`) the **channel** of its unit is, in template coordinates, the
quadrilateral `c1 V₀ V_l d1` with `c1 = (−D S, D S)`, `d1 = (−D S, D S + 3D/2)` (the window `c1 d1`
of the corridor).  The certificate `ChanD` lists, for every receiver `τ` (guard segment
`[R₀, R₁]`), a sub-segment `[M₂, M₁]` of the mouth `V_l V₀` and the convex piece
`A_τ = conv {R₀, R₁, M₂, M₁}`:

* `A_τ` lies in the region (`recv_hull_subset`): no chain edge meets its interior
  (`pieceAutoB`), it lies in the separation region of the template (`Region.check`), and an
  interior point lies in a cover piece of the template region;
* every segment from a point of the receiver to a point of the window crosses `[M₂, M₁]`
  (bilinear corner tests, quadratic in `S`), hence **every receiver guard sees the whole window**
  (`recv_sees_window`), given that the channel lies in the region;
* for the distinguished receiver `star` (with `[M₂, M₁]` the whole mouth) every point of the
  channel is seen (`star_sees_chan`).

`chanB` collects the checks; it is verified by `decide +kernel` for the four templates in
`CoverChanKinds.lean`.
-/

@[expose] public section

namespace ArtGallery.Sec5.CoverT

open ArtGallery Set Polygon Vis.Cert Tmpl
open ArtGallery.Irrational (HP)

/-! ### Certificate data -/

/-- The certificate of one receiver: the guard segment `[R₀, R₁]`, the mouth sub-segment
`[M₂, M₁]`, a triangle `a b c` of the piece containing the interior point `z₀`, and the index of
a cover piece of the template region containing `z₀`. -/
structure RecvD where
  /-- Left end of the receiver. -/
  R0 : IPt
  /-- Right end of the receiver. -/
  R1 : IPt
  /-- Mouth point (towards `V₀`). -/
  M1 : IPt
  /-- Mouth point (towards `V_l`). -/
  M2 : IPt
  /-- Triangle vertex. -/
  a : IPt
  /-- Triangle vertex. -/
  b : IPt
  /-- Triangle vertex. -/
  c : IPt
  /-- Interior point. -/
  z0 : IPt
  /-- Index of a cover piece containing `z₀`. -/
  piece : ℕ
  deriving Inhabited

/-- The convex piece `A_τ = conv {R₀, R₁, M₂, M₁}`. -/
def RecvD.hull (r : RecvD) : List IPt := [r.R0, r.R1, r.M2, r.M1]

/-- The channel certificate of a template. -/
structure ChanD where
  /-- The scale of the integer template coordinates. -/
  D : ℤ
  /-- The template chain. -/
  V : List IPt
  /-- Extra separating lines for chain edges near the mouth corners. -/
  extra : List HP
  /-- The receivers, by `τ`. -/
  recv : List RecvD
  /-- The receiver seeing the whole channel. -/
  star : ℕ

/-- The crossing tests for the receiver `r` and the target corners `ws`: the receiver lies on the
positive side of `M₂ M₁`, and `det(g, w, M₂) ≤ 0 ≤ det(g, w, M₁)` at all corners. -/
def crossB (r : RecvD) (ws : List SPt) : Bool :=
  [r.R0, r.R1].all (fun g => qps (qdet (sc r.M2) (sc r.M1) (sc g))) &&
    ws.all fun w => [r.R0, r.R1].all fun g =>
      qnn (qneg (qdet (sc g) w (sc r.M2))) && qnn (qdet (sc g) w (sc r.M1))

namespace ChanD

variable (d : ChanD)

/-- `c1 = (−D S, D S)`. -/
def c1 : SPt := ((0, 0), (-d.D, d.D))

/-- `d1 = (−D S, D S + 3D/2)`. -/
def d1 : SPt := ((0, 3 * d.D / 2), (-d.D, d.D))

/-- The first template vertex. -/
def v0 : SPt := sc (cv d.V 0)

/-- The last template vertex. -/
def vl : SPt := sc (cv d.V (d.V.length - 1))

/-- A point lies (weakly) in the channel. -/
def inChanB (p : SPt) : Bool :=
  qnn (qdet d.c1 d.v0 p) && qnn (qdet d.v0 d.vl p) && qnn (qdet d.vl d.d1 p) &&
    qnn (qdet d.d1 d.c1 p)

/-- The checks of one receiver. -/
def recvB (R : Region) (pieces : List (List IPt)) (r : RecvD) : Bool :=
  pieceAutoB d.V r.hull && R.check r.hull && interiorCheck r.hull r.a r.b r.c r.z0 &&
    Nat.blt r.piece pieces.length && fanB (pieces.getD r.piece []) &&
    inHullB (pieces.getD r.piece []) r.z0 && d.inChanB (sc r.M1) && d.inChanB (sc r.M2) &&
    [d.c1, d.d1].all (fun w => qps (qneg (qdet (sc r.M2) (sc r.M1) w))) &&
    crossB r [d.c1, d.d1]

/-- The checks of the distinguished receiver. -/
def starB : Bool :=
  Nat.blt d.star d.recv.length && (d.recv.getD d.star default).M1 == cv d.V 0 &&
    (d.recv.getD d.star default).M2 == cv d.V (d.V.length - 1) &&
    crossB (d.recv.getD d.star default) [d.c1, d.v0, d.vl, d.d1]

/-- **All checks.** -/
def chanB (R : Region) (pieces : List (List IPt)) : Bool :=
  (d.D % 2 == 0) && ipos d.D && cornersB d.c1 d.v0 d.vl d.d1 &&
    chainOutB d.c1 d.v0 d.vl d.d1 d.extra d.V && d.recv.all (d.recvB R pieces) && d.starB

end ChanD

/-! ### Soundness -/

section Sound

variable {d : ChanD} {R : Region} {pieces : List (List IPt)}

theorem ChanD.c1_pt (S : ℝ) : d.c1.pt S = (-((d.D : ℝ) * S), (d.D : ℝ) * S) := by
  simp only [SPt.pt, ChanD.c1]; push_cast; ext <;> simp <;> ring

theorem ChanD.d1_pt (h2 : d.D % 2 = 0) (S : ℝ) :
    d.d1.pt S = (-((d.D : ℝ) * S), (d.D : ℝ) * S + 3 / 2 * (d.D : ℝ)) := by
  obtain ⟨e, he⟩ : ∃ e, d.D = 2 * e := ⟨d.D / 2, by omega⟩
  have h3 : (((3 * d.D / 2 : ℤ)) : ℝ) = 3 / 2 * (d.D : ℝ) := by
    have : 3 * d.D / 2 = 3 * e := by rw [he]; omega
    rw [this, he]; push_cast; ring
  ext
  · simp only [SPt.pt, ChanD.d1]; push_cast; ring
  · simp only [SPt.pt, ChanD.d1]; rw [h3]; ring

theorem ChanD.v0_pt (S : ℝ) : d.v0.pt S = intPoint (cv d.V 0) := sc_pt _ _

theorem ChanD.vl_pt (S : ℝ) : d.vl.pt S = intPoint (cv d.V (d.V.length - 1)) := sc_pt _ _

/-- The channel at scale `S`. -/
noncomputable def ChanD.chan (d : ChanD) (S : ℝ) : Set Point :=
  chanSet (d.c1.pt S) (d.v0.pt S) (d.vl.pt S) (d.d1.pt S)

theorem chanB_parts (h : d.chanB R pieces = true) :
    d.D % 2 = 0 ∧ 0 < d.D ∧ cornersB d.c1 d.v0 d.vl d.d1 = true ∧
      chainOutB d.c1 d.v0 d.vl d.d1 d.extra d.V = true ∧
      (∀ r ∈ d.recv, d.recvB R pieces r = true) ∧ d.starB = true := by
  simp only [ChanD.chanB, Bool.and_eq_true, beq_iff_eq, ipos_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem inChan_sound {p : SPt} (h : d.inChanB p = true) {S : ℝ} (hS : 800000 ≤ S) :
    p.pt S ∈ d.chan S := by
  simp only [ChanD.inChanB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := h
  exact ⟨det_nonneg_of_qnn a hS, det_nonneg_of_qnn b hS, det_nonneg_of_qnn c hS,
    det_nonneg_of_qnn e hS⟩

theorem det_pos_of_ends {a b p q z : Point} (hp : 0 < det a b p) (hq : 0 < det a b q)
    (hz : z ∈ ArtGallery.segment p q) : 0 < det a b z := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rw [Geometry.det_lerp]
  exact pos_of_lerp hp hq ht0 ht1

theorem det_neg_of_ends {a b p q z : Point} (hp : det a b p < 0) (hq : det a b q < 0)
    (hz : z ∈ ArtGallery.segment p q) : det a b z < 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rw [Geometry.det_lerp]
  exact neg_of_lerp hp hq ht0 ht1

/-- The parts of `crossB`. -/
theorem crossB_parts {r : RecvD} {ws : List SPt} (h : crossB r ws = true) {S : ℝ}
    (hS : 800000 ≤ S) :
    (0 < det (intPoint r.M2) (intPoint r.M1) (intPoint r.R0)) ∧
      (0 < det (intPoint r.M2) (intPoint r.M1) (intPoint r.R1)) ∧
      ∀ w ∈ ws, ∀ g ∈ [r.R0, r.R1], det (intPoint g) (w.pt S) (intPoint r.M2) ≤ 0 ∧
        0 ≤ det (intPoint g) (w.pt S) (intPoint r.M1) := by
  simp only [crossB, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, ?_, fun w hw g hg => ?_⟩
  · have := det_pos_of_qps h0 hS; simpa using this
  · have := det_pos_of_qps h1 hS; simpa using this
  · obtain ⟨⟨a0, a1⟩, b0, b1⟩ := h2 w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · have x := det_nonpos_of_qnn a0 hS; have y := det_nonneg_of_qnn a1 hS
      simp only [sc_pt] at x y; exact ⟨x, y⟩
    · have x := det_nonpos_of_qnn b0 hS; have y := det_nonneg_of_qnn b1 hS
      simp only [sc_pt] at x y; exact ⟨x, y⟩

/-- `hull_subset_filled_of_auto` with the plain region check. -/
theorem hull_subset_filled_of_check {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple)
    (hC : ChainAt P V a) (hS : SepAt P V a R) {Q : List IPt} (hpc : pieceAutoB V Q = true)
    (hR : R.check Q = true) {z : Point} (hz : z ∈ interior (convexHull ℝ (intSet Q)))
    (hzP : z ∈ P.filled) : convexHull ℝ (intSet Q) ⊆ P.filled := by
  have hedge : ∀ i < P.n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i) := by
    intro i hi
    by_cases hc : ∃ j, j + 1 < V.length ∧ (a + j) % P.n = i
    · obtain ⟨j, hj, rfl⟩ := hc
      rw [hC.edge_eq hj]
      exact disjoint_of_pieceAutoB hpc hj
    · push Not at hc
      rw [Set.disjoint_left]
      intro x hx hxe
      exact hS i hi (fun j hj h => hc j hj h) x hxe (Region.interior_hull_subset hR hx)
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _) hedge hz hzP
  rwa [(isClosed_hull_intSet Q).closure_eq] at this

/-- **The piece of a receiver lies in the region.** -/
theorem recv_hull_subset {P : Polygon} {a : ℕ} (hP : P.Simple) (hC : ChainAt P d.V a)
    (hS : SepAt P d.V a R) (hTR : unionHull pieces ⊆ P.filled) {r : RecvD}
    (h : d.recvB R pieces r = true) : convexHull ℝ (intSet r.hull) ⊆ P.filled := by
  simp only [ChanD.recvB, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpa, hR⟩, hint⟩, hlt⟩, hfan⟩, hin⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine hull_subset_filled_of_check hP hC hS hpa hR (mem_interior_of_interiorCheck hint) ?_
  have hmem : pieces.getD r.piece [] ∈ pieces := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
  exact hTR ⟨pieces.getD r.piece [], hmem, mem_hull_of_inHullB hfan hin⟩

theorem mem_hull_of_mem {Q : List IPt} {q : IPt} (h : q ∈ Q) : intPoint q ∈ convexHull ℝ (intSet Q) :=
  mem_intSet_hull h

/-- `det g w M ≤ 0` for `g`, `w` on two segments if it holds at the four corners. -/
theorem det_nonpos_of_corners {g₀ g₁ w₀ w₁ M g w : Point}
    (h00 : det g₀ w₀ M ≤ 0) (h01 : det g₀ w₁ M ≤ 0) (h10 : det g₁ w₀ M ≤ 0)
    (h11 : det g₁ w₁ M ≤ 0) (hg : g ∈ ArtGallery.segment g₀ g₁)
    (hw : w ∈ ArtGallery.segment w₀ w₁) : det g w M ≤ 0 := by
  have := det_nonneg_of_corners (M := M) (g₀ := w₀) (g₁ := w₁) (w₀ := g₀) (w₁ := g₁)
    (by rw [Geometry.det_swap12]; linarith) (by rw [Geometry.det_swap12]; linarith)
    (by rw [Geometry.det_swap12]; linarith) (by rw [Geometry.det_swap12]; linarith) hw hg
  rw [Geometry.det_swap12] at this; linarith

/-- **Seeing through the mouth.**  If `g` lies in the piece of the receiver `r`, `z` in the channel,
`g` strictly on the positive side and `z` strictly on the negative side of `M₂ M₁`, and
`det(g, z, M₂) ≤ 0 ≤ det(g, z, M₁)`, then `g` sees `z`. -/
theorem sees_through {P : Polygon} {r : RecvD} {C : Set Point} (hC : Convex ℝ C)
    (hA : convexHull ℝ (intSet r.hull) ⊆ P.filled) (hCP : C ⊆ P.filled)
    (hM1 : intPoint r.M1 ∈ C) (hM2 : intPoint r.M2 ∈ C) {g z : Point}
    (hg : g ∈ convexHull ℝ (intSet r.hull)) (hz : z ∈ C)
    (hs1 : 0 < det (intPoint r.M2) (intPoint r.M1) g)
    (hs2 : det (intPoint r.M2) (intPoint r.M1) z < 0)
    (e0 : det g z (intPoint r.M2) ≤ 0) (e1 : 0 ≤ det g z (intPoint r.M1)) : P.Sees g z := by
  obtain ⟨m, hm, hmgz⟩ := exists_mem_segment_inter (mul_neg_of_pos_of_neg hs1 hs2) e0 e1
  have hmA : m ∈ convexHull ℝ (intSet r.hull) :=
    Geometry.segment_subset_convexHull (intPoint_mem_intSet (by simp [RecvD.hull]))
      (intPoint_mem_intSet (by simp [RecvD.hull])) hm
  have hmC : m ∈ C := Geometry.segment_subset_of_convex hC hM2 hM1 hm
  exact Stade.sees_of_two_convex (convex_convexHull ℝ _) hC hA hCP hg hz hmA hmC hmgz

theorem recvB_parts {r : RecvD} (h : d.recvB R pieces r = true) :
    d.inChanB (sc r.M1) = true ∧ d.inChanB (sc r.M2) = true ∧
      qps (qneg (qdet (sc r.M2) (sc r.M1) d.c1)) = true ∧
      qps (qneg (qdet (sc r.M2) (sc r.M1) d.d1)) = true ∧ crossB r [d.c1, d.d1] = true := by
  simp only [ChanD.recvB, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨-, hM1⟩, hM2⟩, hw0, hw1⟩, hcr⟩ := h
  exact ⟨hM1, hM2, hw0, hw1, hcr⟩

/-- **Every receiver guard sees the whole window**, if the channel lies in the region. -/
theorem recv_sees_window {P : Polygon} {a : ℕ} (hP : P.Simple) (hC : ChainAt P d.V a)
    (hS : SepAt P d.V a R) (hTR : unionHull pieces ⊆ P.filled) (hd : d.chanB R pieces = true)
    {S : ℝ} (hS8 : 800000 ≤ S) (hch : d.chan S ⊆ P.filled) {r : RecvD} (hr : r ∈ d.recv)
    {g w : Point} (hg : g ∈ ArtGallery.segment (intPoint r.R0) (intPoint r.R1))
    (hw : w ∈ ArtGallery.segment (d.c1.pt S) (d.d1.pt S)) : P.Sees g w := by
  obtain ⟨-, -, hcor, -, hrecv, -⟩ := chanB_parts hd
  have hb := hrecv r hr
  have hA := recv_hull_subset hP hC hS hTR hb
  have hCo := corners_of_B hcor hS8
  obtain ⟨hM1, hM2, hw0, hw1, hcr⟩ := recvB_parts hb
  obtain ⟨k0, k1, kc⟩ := crossB_parts hcr hS8
  have hgA : g ∈ convexHull ℝ (intSet r.hull) :=
    Geometry.segment_subset_convexHull (intPoint_mem_intSet (by simp [RecvD.hull]))
      (intPoint_mem_intSet (by simp [RecvD.hull])) hg
  have hwC : w ∈ d.chan S := hCo.segment_subset hCo.c1_mem hCo.d1_mem hw
  have h00 := kc d.c1 (by simp) r.R0 (by simp)
  have h01 := kc d.d1 (by simp) r.R0 (by simp)
  have h10 := kc d.c1 (by simp) r.R1 (by simp)
  have h11 := kc d.d1 (by simp) r.R1 (by simp)
  refine sees_through convex_chanSet hA hch ?_ ?_ hgA hwC (det_pos_of_ends k0 k1 hg) ?_
    (det_nonpos_of_corners h00.1 h01.1 h10.1 h11.1 hg hw)
    (det_nonneg_of_corners h00.2 h01.2 h10.2 h11.2 hg hw)
  · have := inChan_sound hM1 hS8; rwa [sc_pt] at this
  · have := inChan_sound hM2 hS8; rwa [sc_pt] at this
  · refine det_neg_of_ends ?_ ?_ hw
    · have := det_neg_of_qps hw0 hS8; simpa using this
    · have := det_neg_of_qps hw1 hS8; simpa using this

/-- The channel has an interior point. -/
theorem Corners.interior_nonempty {c1 v0 vl d1 : Point} (h : Corners c1 v0 vl d1) :
    (interior (chanSet c1 v0 vl d1)).Nonempty := by
  refine ⟨Geometry.lerp c1 (Geometry.lerp v0 vl (1 / 2)) (2 / 3), mem_interior_chanSet ?_⟩
  have := h.t0; have := h.t1; have := h.t2; have := h.t3
  simp only [Geometry.det_lerp, Geometry.det_self_right, Geometry.det_self_outer]
  have e1 := Geometry.det_cyclic c1 v0 vl
  have e2 := Geometry.det_cyclic v0 vl d1
  have e3 := Geometry.det_cyclic vl d1 c1
  have e4 := Geometry.det_cyclic d1 c1 v0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- `det g z M ≥ 0` for `g` on a segment and `z` in the channel, from the corners. -/
theorem chan_affine_nonneg {c1 v0 vl d1 : Point} (h : Corners c1 v0 vl d1) {R0 R1 M g z : Point}
    (hg : g ∈ ArtGallery.segment R0 R1) (hz : z ∈ chanSet c1 v0 vl d1)
    (hc : ∀ g' ∈ [R0, R1], ∀ w ∈ [c1, v0, vl, d1], 0 ≤ det g' w M) : 0 ≤ det g z M := by
  have hz0 : ∀ g' ∈ [R0, R1], 0 ≤ det g' z M := by
    intro g' hg'
    have hcv : Convex ℝ {y : Point | 0 ≤ det g' y M} := by
      have : {y : Point | 0 ≤ det g' y M} = {y | 0 ≤ det M g' y} := by
        ext y; simp only [mem_ofPred_eq]; rw [Geometry.det_cyclic]
      rw [this]; exact convex_halfdet _ _
    exact nonneg_on_chanSet h hcv (hc g' hg' _ (by simp)) (hc g' hg' _ (by simp))
      (hc g' hg' _ (by simp)) (hc g' hg' _ (by simp)) hz
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hg
  rw [Geometry.det_lerp_left]
  exact nonneg_lerp (hz0 _ (by simp)) (hz0 _ (by simp)) ht0 ht1

/-- `det g z M ≤ 0` for `g` on a segment and `z` in the channel, from the corners. -/
theorem chan_affine_nonpos {c1 v0 vl d1 : Point} (h : Corners c1 v0 vl d1) {R0 R1 M g z : Point}
    (hg : g ∈ ArtGallery.segment R0 R1) (hz : z ∈ chanSet c1 v0 vl d1)
    (hc : ∀ g' ∈ [R0, R1], ∀ w ∈ [c1, v0, vl, d1], det g' w M ≤ 0) : det g z M ≤ 0 := by
  have hz0 : ∀ g' ∈ [R0, R1], det g' z M ≤ 0 := by
    intro g' hg'
    have hcv : Convex ℝ {y : Point | 0 ≤ -det g' y M} := by
      have : {y : Point | 0 ≤ -det g' y M} = {y | 0 ≤ det g' M y} := by
        ext y; simp only [mem_ofPred_eq]
        rw [Geometry.det_swap23, neg_neg]
      rw [this]; exact convex_halfdet _ _
    have := nonneg_on_chanSet h hcv (by linarith [hc g' hg' c1 (by simp)])
      (by linarith [hc g' hg' v0 (by simp)]) (by linarith [hc g' hg' vl (by simp)])
      (by linarith [hc g' hg' d1 (by simp)]) hz
    linarith
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hg
  rw [Geometry.det_lerp_left]
  have a := hz0 _ (List.mem_cons_self ..)
  have b := hz0 R1 (by simp)
  have : 0 ≤ 1 - t := by linarith
  nlinarith [mul_nonneg this (neg_nonneg.2 a), mul_nonneg ht0 (neg_nonneg.2 b)]

/-- **The distinguished receiver sees the whole channel.** -/
theorem star_sees_chan {P : Polygon} {a : ℕ} (hP : P.Simple) (hC : ChainAt P d.V a)
    (hS : SepAt P d.V a R) (hTR : unionHull pieces ⊆ P.filled) (hd : d.chanB R pieces = true)
    {S : ℝ} (hS8 : 800000 ≤ S) (hch : d.chan S ⊆ P.filled) {g : Point}
    (hg : g ∈ ArtGallery.segment (intPoint (d.recv.getD d.star default).R0)
      (intPoint (d.recv.getD d.star default).R1)) :
    ∀ z ∈ d.chan S, P.Sees g z := by
  obtain ⟨-, -, hcor, -, hrecv, hstar⟩ := chanB_parts hd
  simp only [ChanD.starB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hstar
  set r := d.recv.getD d.star default with hrdef
  obtain ⟨⟨⟨hlt, e1⟩, e2⟩, hcr⟩ := hstar
  have hr : r ∈ d.recv := by
    rw [hrdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
  have hb := hrecv r hr
  have hA := recv_hull_subset hP hC hS hTR hb
  have hCo := corners_of_B hcor hS8
  obtain ⟨hM1, hM2, -, -, -⟩ := recvB_parts hb
  obtain ⟨k0, k1, kc⟩ := crossB_parts hcr hS8
  have hgA : g ∈ convexHull ℝ (intSet r.hull) :=
    Geometry.segment_subset_convexHull (intPoint_mem_intSet (by simp [RecvD.hull]))
      (intPoint_mem_intSet (by simp [RecvD.hull])) hg
  have eM1 : intPoint r.M1 = d.v0.pt S := by rw [ChanD.v0_pt, ← e1]
  have eM2 : intPoint r.M2 = d.vl.pt S := by rw [ChanD.vl_pt, ← e2]
  have kc' : ∀ g' ∈ [intPoint r.R0, intPoint r.R1],
      ∀ w ∈ [d.c1.pt S, d.v0.pt S, d.vl.pt S, d.d1.pt S],
        det g' w (intPoint r.M2) ≤ 0 ∧ 0 ≤ det g' w (intPoint r.M1) := by
    intro g' hg' w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg' hw
    rcases hg' with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      exact kc _ (by simp) _ (by simp)
  -- interior points of the channel
  have hint : ∀ z ∈ interior (d.chan S), P.Sees g z := by
    intro z hz
    have hzC : z ∈ d.chan S := interior_subset hz
    obtain ⟨-, j1, -, -⟩ := interior_chanSet hCo hz
    refine sees_through convex_chanSet hA hch ?_ ?_ hgA hzC (det_pos_of_ends k0 k1 hg) ?_
      (chan_affine_nonpos hCo hg hzC fun g' hg' w hw => (kc' g' hg' w hw).1)
      (chan_affine_nonneg hCo hg hzC fun g' hg' w hw => (kc' g' hg' w hw).2)
    · have := inChan_sound hM1 hS8; rwa [sc_pt] at this
    · have := inChan_sound hM2 hS8; rwa [sc_pt] at this
    · rw [eM1, eM2, Geometry.det_swap12]; linarith
  -- the closure
  intro z hz
  have hcl : d.chan S ⊆ closure (interior (d.chan S)) := by
    unfold ChanD.chan
    rw [convex_chanSet.closure_interior_eq_closure_of_nonempty_interior hCo.interior_nonempty,
      isClosed_chanSet.closure_eq]
  exact closure_minimal hint (Corridor.isClosed_setOf_sees P g) (hcl hz)

end Sound

end ArtGallery.Sec5.CoverT

end
