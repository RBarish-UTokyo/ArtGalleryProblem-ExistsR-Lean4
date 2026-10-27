module

public import ArtGallery.Hardness.Sec5.Templates.CoverTools
public import ArtGallery.Hardness.Sec5.CountTools

/-!
# Boundary-point templates: pinning on the boundary

In the boundary-point variant every guard segment of a template lies on a horizontal boundary
edge, the *floor* of a shallow bay whose two side walls carry one *spike* each
(`docs/boundary_point/design.md`, §3.1).  A spike is a convex chain vertex `T = V[j]` whose two
cone rays hit the interior of the floor edge `V[f] V[f+1]`.  The tools of this file (soundness
of Boolean certificates evaluated by `decide +kernel`):

* `spike_sees_hps`: a point seen from the spike tip satisfies the three constraints
  `spikeHPs V j f` (the two cone half-planes and the inner side of the floor line): every
  segment from the tip to a point beyond the floor line properly crosses the floor edge
  (`not_sees_through_edge`).  The visibility set of a spike tip thus lies in the triangle
  spanned by the tip and the two hit points;
* `bd_on_targets`: a point of `∂P` satisfying a list of linear constraints `cs` lies on one of
  the *target* chain edges, if the set `{cs ≥ 0}` lies in the separation region (`regB`, Farkas
  certificates) and every other chain edge is excluded by a nonnegative combination of `cs`
  that is negative at both ends of the edge (`edgesB`).  Only boundary points are pinned this
  way: in two dimensions the visibility triangles of the two spikes of a bay overlap above its
  floor;
* `floor_mem_hull`: the part of a horizontal floor edge satisfying `cs` is a sub-segment;
* `empty_of_emptyB`: a Farkas certificate that `{cs ≥ 0}` is empty.

`TFactsBd` collects the counting facts of a template for guards on the boundary
(allowed set `Ω = ∂P`, all ranks equal, see `PosSys.OKOn` in `Sec5/CountAbstract.lean`).
-/

@[expose] public section

namespace ArtGallery.BP.Tmpl

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl
open ArtGallery.Irrational (HP)

variable {P : Polygon} {V : List IPt} {a : ℕ}

/-! ### Spikes -/

/-- The cone decomposition identity: for the cone at `T` spanned by `U − T`, `W − T`,
`det U T W · det T Z x = det U T x · det T Z W + det T W x · det T Z U`. -/
theorem cone_identity (U T W Z x : Point) :
    det U T W * det T Z x = det U T x * det T Z W + det T W x * det T Z U := by
  simp only [det]; ring

/-- The same identity for a line `A B`: `det U T W · (det A B x − det A B T)` is a combination of
the two cone functionals. -/
theorem cone_identity_line (U T W A B x : Point) :
    det U T W * (det A B x - det A B T) =
      det U T x * (det A B W - det A B T) + det T W x * (det A B U - det A B T) := by
  simp only [det]; ring

/-- **A spike does not see through the floor.**  Let `T` be the apex of a convex angle
`U T W` (`det U T W > 0`) and `x` a point of its cone strictly beyond the line of the edge
`A B` of `P`, with `T` strictly on the other side.  If `A` and `B` lie on different sides of
both cone rays (so that the rays meet the line of `A B` strictly between `A` and `B`), the
segment `T x` crosses the edge properly and `T` does not see `x`. -/
theorem not_sees_through_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {T U W x : Point}
    (hc : 0 < det U T W) (hk1 : 0 ≤ det U T x) (hk2 : 0 ≤ det T W x)
    (hT : 0 < det (P.vtx i) (P.vtx ((i + 1) % P.n)) T)
    (hx : det (P.vtx i) (P.vtx ((i + 1) % P.n)) x < 0)
    (hs : (0 < det T (P.vtx i) W ∧ 0 < det T (P.vtx i) U ∧ det T (P.vtx ((i + 1) % P.n)) W < 0 ∧
        det T (P.vtx ((i + 1) % P.n)) U < 0) ∨
      (det T (P.vtx i) W < 0 ∧ det T (P.vtx i) U < 0 ∧ 0 < det T (P.vtx ((i + 1) % P.n)) W ∧
        0 < det T (P.vtx ((i + 1) % P.n)) U)) :
    ¬ P.Sees T x := by
  set A := P.vtx i
  set B := P.vtx ((i + 1) % P.n)
  have iA := cone_identity U T W A x
  have iB := cone_identity U T W B x
  have iL := cone_identity_line U T W A B x
  set k1 := det U T x
  set k2 := det T W x
  have hk : 0 < k1 + k2 := by
    by_contra hcon
    have e1 : k1 = 0 := by linarith
    have e2 : k2 = 0 := by linarith
    rw [e1, e2] at iL
    have : det U T W * (det A B x - det A B T) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
    linarith
  refine Polygon.not_sees_of_proper_cross hP hi (mul_neg_of_pos_of_neg hT hx) ?_
  rw [Geometry.det_swap23 T A x, Geometry.det_swap23 T B x]
  rcases hs with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have pA : 0 < det T A x := by
      have : 0 < det U T W * det T A x := by
        rw [iA]
        rcases lt_or_eq_of_le hk1 with hk1' | hk1'
        · nlinarith [mul_pos hk1' h1, mul_nonneg hk2 h2.le]
        · rw [← hk1'] at hk ⊢; nlinarith [mul_pos (by linarith : (0:ℝ) < k2) h2]
      exact pos_of_mul_pos_right this hc.le
    have pB : det T B x < 0 := by
      have : det U T W * det T B x < 0 := by
        rw [iB]
        rcases lt_or_eq_of_le hk1 with hk1' | hk1'
        · nlinarith [mul_neg_of_pos_of_neg hk1' h3, mul_nonpos_of_nonneg_of_nonpos hk2 h4.le]
        · rw [← hk1'] at hk ⊢; nlinarith [mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < k2) h4]
      by_contra hcon; push Not at hcon
      nlinarith [mul_nonneg hc.le hcon]
    nlinarith [mul_neg_of_pos_of_neg pA pB]
  · have pA : det T A x < 0 := by
      have : det U T W * det T A x < 0 := by
        rw [iA]
        rcases lt_or_eq_of_le hk1 with hk1' | hk1'
        · nlinarith [mul_neg_of_pos_of_neg hk1' h1, mul_nonpos_of_nonneg_of_nonpos hk2 h2.le]
        · rw [← hk1'] at hk ⊢; nlinarith [mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < k2) h2]
      by_contra hcon; push Not at hcon
      nlinarith [mul_nonneg hc.le hcon]
    have pB : 0 < det T B x := by
      have : 0 < det U T W * det T B x := by
        rw [iB]
        rcases lt_or_eq_of_le hk1 with hk1' | hk1'
        · nlinarith [mul_pos hk1' h3, mul_nonneg hk2 h4.le]
        · rw [← hk1'] at hk ⊢; nlinarith [mul_pos (by linarith : (0:ℝ) < k2) h4]
      exact pos_of_mul_pos_right this hc.le
    nlinarith [mul_neg_of_neg_of_pos pA pB]

/-- Spike data: `V[j]` is a convex chain vertex strictly on the inner side of the chain edge
`f` (the floor), and both floor ends lie strictly on different sides of both cone rays. -/
def spikeB (V : List IPt) (j f : ℕ) : Bool :=
  Nat.ble 1 j && Nat.blt (j + 1) V.length && Nat.blt (f + 1) V.length &&
    ipos (idet (cv V (j - 1)) (cv V j) (cv V (j + 1))) &&
    ipos (idet (cv V f) (cv V (f + 1)) (cv V j)) &&
    ((ipos (idet (cv V j) (cv V f) (cv V (j + 1))) && ipos (idet (cv V j) (cv V f) (cv V (j - 1))) &&
        ineg (idet (cv V j) (cv V (f + 1)) (cv V (j + 1))) &&
        ineg (idet (cv V j) (cv V (f + 1)) (cv V (j - 1)))) ||
      (ineg (idet (cv V j) (cv V f) (cv V (j + 1))) && ineg (idet (cv V j) (cv V f) (cv V (j - 1))) &&
        ipos (idet (cv V j) (cv V (f + 1)) (cv V (j + 1))) &&
        ipos (idet (cv V j) (cv V (f + 1)) (cv V (j - 1)))))

/-- The constraints of the visibility set of the spike `j` with floor `f`: the two cone
half-planes and the inner side of the floor line. -/
def spikeHPs (V : List IPt) (j f : ℕ) : List HP :=
  [lineHP (cv V (j - 1)) (cv V j), lineHP (cv V j) (cv V (j + 1)), lineHP (cv V f) (cv V (f + 1))]

/-- The two cone half-planes of the convex chain vertex `j`. -/
def coneHPs (V : List IPt) (j : ℕ) : List HP :=
  [lineHP (cv V (j - 1)) (cv V j), lineHP (cv V j) (cv V (j + 1))]

theorem dpos {u v w : IPt} (h : ipos (idet u v w) = true) :
    0 < det (intPoint u) (intPoint v) (intPoint w) := by
  rw [det_intPoint]; exact_mod_cast ipos_iff.1 h

theorem dneg {u v w : IPt} (h : ineg (idet u v w) = true) :
    det (intPoint u) (intPoint v) (intPoint w) < 0 := by
  rw [det_intPoint]; exact_mod_cast ineg_iff.1 h

/-- **The visibility set of a spike tip** lies in the triangle `spikeHPs ≥ 0`. -/
theorem spike_sees_hps (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j f : ℕ}
    (h : spikeB V j f = true) {x : Point} (hs : P.Sees (tpt V j) x) :
    ∀ c ∈ spikeHPs V j f, 0 ≤ c.val x := by
  simp only [spikeB, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hj1, hj⟩, hf⟩, hconv⟩, hT⟩, hside⟩ := h
  have hconv' := ipos_iff.1 hconv
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC hj1 hj hconv' hs
  have hfl : 0 ≤ det (intPoint (cv V f)) (intPoint (cv V (f + 1))) x := by
    by_contra hneg
    push Not at hneg
    obtain ⟨e1, e2⟩ := hC.edge_vtx hf
    refine not_sees_through_edge hP (Nat.mod_lt (a + f) (n_pos_of_simple hP))
      (U := intPoint (cv V (j - 1))) (W := intPoint (cv V (j + 1))) (dpos hconv) c1 c2
      (by rw [e1, e2]; exact dpos hT) (by rw [e1, e2]; exact hneg) ?_ hs
    rw [e1, e2]
    rcases hside with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact Or.inl ⟨dpos h1, dpos h2, dneg h3, dneg h4⟩
    · exact Or.inr ⟨dneg h1, dneg h2, dpos h3, dpos h4⟩
  intro c hc
  simp only [spikeHPs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rw [lineHP_val]
  exacts [c1, c2, hfl]

/-- The cone constraints of a convex chain vertex. -/
theorem cone_sees_hps (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < V.length) (hconv : 0 < idet (cv V (j - 1)) (cv V j) (cv V (j + 1)))
    {x : Point} (hs : P.Sees (tpt V j) x) : ∀ c ∈ coneHPs V j, 0 ≤ c.val x := by
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC hj1 hj hconv hs
  intro c hc
  simp only [coneHPs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rw [lineHP_val]
  exacts [c1, c2]

/-! ### Linear certificates -/

/-- `c • e = Σ λᵢ csᵢ + μ` with `c > 0`, `μ > 0`: `e > 0` follows from `cs ≥ 0`. -/
def implPosB (cs : List HP) (e : HP) (c : ℕ) (lam : List (ℕ × ℕ)) : Bool :=
  Nat.blt 0 c && ((c : ℤ) * e.1 == (combS cs lam).1) && ((c : ℤ) * e.2.1 == (combS cs lam).2.1) &&
    ilt (combS cs lam).2.2 ((c : ℤ) * e.2.2)

theorem implPosB_sound {cs : List HP} {e : HP} {c : ℕ} {lam : List (ℕ × ℕ)}
    (h : implPosB cs e c lam = true) {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) : 0 < e.val z := by
  simp only [implPosB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, ilt_iff] at h
  obtain ⟨⟨⟨hc, h1⟩, h2⟩, h3⟩ := h
  have hs := combS_val_nonneg cs hz lam
  set s := combS cs lam
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have key : (c : ℝ) * e.val z = s.val z + ((c : ℝ) * e.2.2 - s.2.2) := by
    simp only [Irrational.HP.val]
    have e1' : (c : ℝ) * (e.1 : ℝ) = (s.1 : ℝ) := by exact_mod_cast h1
    have e2' : (c : ℝ) * (e.2.1 : ℝ) = (s.2.1 : ℝ) := by exact_mod_cast h2
    linear_combination z.1 * e1' + z.2 * e2'
  have h3' : (s.2.2 : ℝ) < (c : ℝ) * e.2.2 := by exact_mod_cast h3
  have : 0 < (c : ℝ) * e.val z := by rw [key]; linarith
  exact (mul_pos_iff_of_pos_left hcr).1 this

/-- Infeasibility: `c • (0, 0, -1) = Σ λᵢ csᵢ + μ`, `μ ≥ 0`. -/
def emptyB (cs : List HP) (c : ℕ) (lam : List (ℕ × ℕ)) : Bool := implB cs (0, 0, -1) c lam

/-- **Farkas infeasibility.** -/
theorem empty_of_emptyB {cs : List HP} {c : ℕ} {lam : List (ℕ × ℕ)} (h : emptyB cs c lam = true)
    {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) : False := by
  have := implB_sound h hz
  simp only [Irrational.HP.val] at this
  push_cast at this
  linarith

/-- Region certificates: one strict certificate per box constraint, and per zone an index of a
constraint and a strict certificate of its negation. -/
abbrev RegCert : Type := List (ℕ × List (ℕ × ℕ)) × List (ℕ × ℕ × List (ℕ × ℕ))

/-- `{cs ≥ 0}` lies in the region `R`. -/
def regB (R : Region) (cs : List HP) (rc : RegCert) : Bool :=
  R.box.length == rc.1.length && R.zones.length == rc.2.length &&
    (List.zip R.box rc.1).all (fun bc => implPosB cs bc.1 bc.2.1 bc.2.2) &&
    (List.zip R.zones rc.2).all (fun wc => implPosB cs (negHP (wc.1.getD wc.2.1 (0, 0, 0)))
      wc.2.2.1 wc.2.2.2)

theorem regB_sound {R : Region} {cs : List HP} {rc : RegCert} (h : regB R cs rc = true)
    {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) : R.Mem z := by
  simp only [regB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hl1, hl2⟩, hb⟩, hw⟩ := h
  constructor
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < rc.1.length := hl1 ▸ hk
    have := hb (R.box[k], rc.1[k]) (List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩)
    exact implPosB_sound this hz
  · intro W hW
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hW
    have hk' : k < rc.2.length := hl2 ▸ hk
    have := hw (R.zones[k], rc.2[k]) (List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩)
    simp only at this
    have hpos := implPosB_sound this hz
    rw [negHP_val] at hpos
    set i := rc.2[k].1
    by_cases hi : i < R.zones[k].length
    · refine ⟨R.zones[k][i], List.getElem_mem hi, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hpos
      simp only [Option.getD_some] at hpos
      linarith
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hpos
      simp [Irrational.HP.val] at hpos

/-- Edge certificates: every chain edge is a target or is excluded by a nonnegative combination of
`cs` that is negative at both of its ends. -/
def edgesB (V : List IPt) (cs : List HP) (tg : List ℕ) (ec : List (Option (List (ℕ × ℕ)))) : Bool :=
  (List.range (V.length - 1)).all fun j => tg.contains j ||
    match ec.getD j none with
    | some lam => ineg (ivalHP (combS cs lam) (cv V j)) && ineg (ivalHP (combS cs lam) (cv V (j + 1)))
    | none => false

theorem edgesB_sound {cs : List HP} {tg : List ℕ} {ec : List (Option (List (ℕ × ℕ)))}
    (h : edgesB V cs tg ec = true) {j : ℕ} (hj : j + 1 < V.length) {z : Point}
    (hz : ∀ h ∈ cs, 0 ≤ h.val z) (hzj : z ∈ ArtGallery.segment (tpt V j) (tpt V (j + 1))) :
    j ∈ tg := by
  simp only [edgesB, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h j (by omega) with h | h
  · exact h
  · exfalso
    revert h
    cases hj' : ec.getD j none with
    | none => simp
    | some lam =>
      intro h
      simp only [Bool.and_eq_true, ineg_iff] at h
      have hs := combS_val_nonneg cs hz lam
      obtain ⟨t, ht0, ht1, hzt⟩ := Geometry.mem_segment_iff_lerp.1 hzj
      subst hzt
      rw [Irrational.HP.val_lerp, tpt, tpt, val_intPoint_HP, val_intPoint_HP] at hs
      have a1 : ((ivalHP (combS cs lam) (cv V j) : ℤ) : ℝ) < 0 := by exact_mod_cast h.1
      have a2 : ((ivalHP (combS cs lam) (cv V (j + 1)) : ℤ) : ℝ) < 0 := by exact_mod_cast h.2
      nlinarith [mul_nonneg ht0 (le_of_lt (neg_pos.2 a2)), mul_nonneg (sub_nonneg.2 ht1) (le_of_lt (neg_pos.2 a1))]

/-! ### Boundary points -/

/-- A point of the boundary in the separation region lies on a chain edge. -/
theorem chain_edge_of_boundary {R : Region} (hP : P.Simple) (hC : ChainAt P V a)
    (hS : SepAt P V a R) {x : Point} (hx : x ∈ P.boundary) (hR : R.Mem x) :
    ∃ j, j + 1 < V.length ∧ x ∈ ArtGallery.segment (tpt V j) (tpt V (j + 1)) := by
  obtain ⟨i, hi, hxi⟩ := hx
  by_contra hcon
  push Not at hcon
  refine hS i hi (fun j hj hji => ?_) x hxi hR
  subst hji
  rw [hC.edge_eq hj] at hxi
  exact hcon j hj hxi

/-- **Boundary points on target edges.**  A point of `∂P` satisfying `cs` lies on a target
chain edge. -/
theorem bd_on_targets {R : Region} (hP : P.Simple) (hC : ChainAt P V a) (hS : SepAt P V a R)
    {cs : List HP} {rc : RegCert} {tg : List ℕ} {ec : List (Option (List (ℕ × ℕ)))}
    (hr : regB R cs rc = true) (he : edgesB V cs tg ec = true) {x : Point} (hx : x ∈ P.boundary)
    (hz : ∀ h ∈ cs, 0 ≤ h.val x) :
    ∃ j ∈ tg, j + 1 < V.length ∧ x ∈ ArtGallery.segment (tpt V j) (tpt V (j + 1)) := by
  obtain ⟨j, hj, hxj⟩ := chain_edge_of_boundary hP hC hS hx (regB_sound hr hz)
  exact ⟨j, edgesB_sound he hj hz hxj, hj, hxj⟩

/-- **No boundary point** satisfies `cs` (no target edge). -/
theorem bd_none {R : Region} (hP : P.Simple) (hC : ChainAt P V a) (hS : SepAt P V a R)
    {cs : List HP} {rc : RegCert} {ec : List (Option (List (ℕ × ℕ)))}
    (hr : regB R cs rc = true) (he : edgesB V cs [] ec = true) {x : Point} (hx : x ∈ P.boundary)
    (hz : ∀ h ∈ cs, 0 ≤ h.val x) : False := by
  obtain ⟨j, hj, -⟩ := bd_on_targets hP hC hS hr he hx hz
  simp at hj

/-- Floor data: the chain edge `f` and the segment `[lo, hi]` are horizontal on the same line,
and `cs` together with the floor line bounds the abscissa by `lo.1` and `hi.1`. -/
def floorB (V : List IPt) (f : ℕ) (cs : List HP) (lo hi : IPt) (c1 : ℕ × List (ℕ × ℕ))
    (c2 : ℕ × List (ℕ × ℕ)) : Bool :=
  ((cv V f).2 == lo.2) && ((cv V (f + 1)).2 == lo.2) && (hi.2 == lo.2) && ilt lo.1 hi.1 &&
    ilt (cv V f).1 (cv V (f + 1)).1 &&
    implB (cs ++ [negHP (lineHP (cv V f) (cv V (f + 1)))]) (1, 0, -lo.1) c1.1 c1.2 &&
    implB (cs ++ [negHP (lineHP (cv V f) (cv V (f + 1)))]) (-1, 0, hi.1) c2.1 c2.2

/-- **The trace on the floor**: a point of the floor edge satisfying `cs` lies on `[lo, hi]`. -/
theorem floor_mem_hull {f : ℕ} {cs : List HP} {lo hi : IPt} {c1 c2 : ℕ × List (ℕ × ℕ)}
    (h : floorB V f cs lo hi c1 c2 = true) {x : Point}
    (hx : x ∈ ArtGallery.segment (tpt V f) (tpt V (f + 1))) (hz : ∀ h ∈ cs, 0 ≤ h.val x) :
    x ∈ convexHull ℝ (intSet [lo, hi]) := by
  simp only [floorB, Bool.and_eq_true, beq_iff_eq, ilt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hy : x.2 = lo.2 := by
    obtain ⟨t, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    simp only [Geometry.lerp, tpt, intPoint_snd, h1, h2]; ring
  have hL : (lineHP (cv V f) (cv V (f + 1))).val x = 0 := by
    rw [lineHP_val]
    obtain ⟨t, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    rw [Geometry.det_lerp]
    simp only [Geometry.det_self_right, tpt]
    rw [show det (intPoint (cv V f)) (intPoint (cv V (f + 1))) (intPoint (cv V f)) = 0 from
      Geometry.det_self_outer _ _]
    ring
  have hz' : ∀ h ∈ cs ++ [negHP (lineHP (cv V f) (cv V (f + 1)))], 0 ≤ h.val x := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hz c hc
    · simp only [List.mem_singleton] at hc; subst hc; rw [negHP_val, hL]; simp
  have a1 := implB_sound h6 hz'
  have a2 := implB_sound h7 hz'
  simp only [Irrational.HP.val] at a1 a2
  push_cast at a1 a2
  exact mem_segment_horiz_hull (A := lo) (B := hi) h3.symm (by exact_mod_cast h4) hy
    (by linarith) (by linarith)

/-! ### Counting facts with guards on the boundary -/

/-- The facts about the positions of a template needed for the counting when the guards lie on
the boundary (allowed set `Ω = ∂P`): all ranks are equal, so (W3) is required for all pairs of
positions; (W1) and (W3) only for points of `∂P`.  The separation hypothesis `SepAt` is needed:
in two dimensions the visibility sets of the two spikes of a bay overlap. -/
structure TFactsBd (V : List IPt) (D : ℕ) (R : Region) (T : TSys) : Prop where
  /-- The main witness is a witness. -/
  m_W : ∀ X, T.m X ∈ T.W X
  /-- Witnesses are chain vertices. -/
  idx : ∀ X, ∀ j ∈ T.W X, j < V.length
  /-- The positions lie in the template box. -/
  box : ∀ X, ∀ q ∈ T.spot X, -(50 * (D : ℤ)) ≤ q.1 ∧ q.1 ≤ 50 * D ∧ -(50 * (D : ℤ)) ≤ q.2 ∧
    q.2 ≤ 50 * D
  /-- Distinct positions are disjoint. -/
  spot_disj : ∀ X Y, X ≠ Y →
    Disjoint (convexHull ℝ (intSet (T.spot X))) (convexHull ℝ (intSet (T.spot Y)))
  /-- The positions lie on the boundary (on chain edges). -/
  spot_bd : ∀ {P : Polygon} {a : ℕ}, P.Simple → ChainAt P V a → ∀ X,
    convexHull ℝ (intSet (T.spot X)) ⊆ P.boundary
  /-- (W1, converse) the points of a position see its witnesses. -/
  sees : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → SepAt P V a R →
    ∀ X, ∀ x ∈ convexHull ℝ (intSet (T.spot X)), ∀ j ∈ T.W X, P.Sees x (tpt V j)
  /-- (W1) a point of `∂P` seeing all witnesses of `X` lies on `X`. -/
  spot : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → SepAt P V a R →
    ∀ X, ∀ x ∈ P.boundary, (∀ j ∈ T.W X, P.Sees x (tpt V j)) → x ∈ convexHull ℝ (intSet (T.spot X))
  /-- (W3, all pairs) no point of `∂P` sees the main witness of `Y` and a witness of `X ≠ Y`. -/
  late : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → SepAt P V a R →
    ∀ X Y, Y ≠ X → ∀ j ∈ T.W X, ∀ x ∈ P.boundary, P.Sees x (tpt V (T.m Y)) → ¬ P.Sees x (tpt V j)
  /-- The window sees no main witness. -/
  window : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X (S : ℝ),
    800000 ≤ S → ∀ y ∈ ArtGallery.segment (winT0 D S) (winT1 D S), ¬ P.Sees y (tpt V (T.m X))
  /-- The entrance sees no witness. -/
  entrance : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X,
    ∀ j ∈ T.W X, ∀ S : ℝ, 800000 ≤ S → ∀ y ∈ ArtGallery.segment (entT0 D S) (entT1 D S),
      ¬ P.Sees y (tpt V j)

/-- (W2) for boundary points: no point of `∂P` sees two main witnesses. -/
theorem TFactsBd.disj {D : ℕ} {R : Region} {T : TSys} (hF : TFactsBd V D R T)
    (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) (hS : SepAt P V a R) {X Y : Fin T.r}
    (h : X ≠ Y) {x : Point} (hx : x ∈ P.boundary) (h1 : P.Sees x (tpt V (T.m X))) :
    ¬ P.Sees x (tpt V (T.m Y)) :=
  hF.late hP hL hC hS Y X h (T.m Y) (hF.m_W Y) x hx h1

/-! ### Positions on chain edges -/

/-- The horizontal segment `[lo, hi]` lies on the horizontal chain edge `f`. -/
def floorInB (V : List IPt) (f : ℕ) (lo hi : IPt) : Bool :=
  Nat.blt (f + 1) V.length && ((cv V f).2 == lo.2) && ((cv V (f + 1)).2 == lo.2) && (hi.2 == lo.2) &&
    ile (cv V f).1 lo.1 && ile lo.1 hi.1 && ile hi.1 (cv V (f + 1)).1

theorem hull_sub_floor {f : ℕ} {lo hi : IPt} (h : floorInB V f lo hi = true) :
    convexHull ℝ (intSet [lo, hi]) ⊆ ArtGallery.segment (tpt V f) (tpt V (f + 1)) := by
  simp only [floorInB, Bool.and_eq_true, beq_iff_eq, ile_iff, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  intro x hx
  have a0 := zero_on_hull (Q := [lo, hi]) (g := (0, 1, -lo.2)) (by
    simp only [List.all_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl) <;> simp [ivalHP, h3]) x hx
  have a1 := nonneg_on_hull (Q := [lo, hi]) (g := (1, 0, -lo.1)) (by
    simp only [List.all_eq_true, inonneg_iff, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl) <;> simp [ivalHP] <;> omega) x hx
  have a2 := nonneg_on_hull (Q := [lo, hi]) (g := (-1, 0, hi.1)) (by
    simp only [List.all_eq_true, inonneg_iff, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl) <;> simp [ivalHP] <;> omega) x hx
  simp only [Irrational.HP.val] at a0 a1 a2
  push_cast at a0 a1 a2
  have b1 : ((cv V f).1 : ℝ) ≤ lo.1 := by exact_mod_cast h4
  have b2 : (hi.1 : ℝ) ≤ (cv V (f + 1)).1 := by exact_mod_cast h6
  have c1 : ((cv V f).2 : ℝ) = lo.2 := by exact_mod_cast h1
  have c2 : ((cv V (f + 1)).2 : ℝ) = lo.2 := by exact_mod_cast h2
  exact mem_segment_horiz (c := lo.2) (by simp only [tpt, intPoint_snd]; exact c1)
    (by simp only [tpt, intPoint_snd]; exact c2) (by linarith)
    (by simp only [tpt, intPoint_fst]; linarith) (by simp only [tpt, intPoint_fst]; linarith)

/-- The horizontal segment `[lo, hi]` on the chain edge `f` lies on the boundary. -/
theorem hull_sub_boundary (hP : P.Simple) (hC : ChainAt P V a) {f : ℕ} {lo hi : IPt}
    (h : floorInB V f lo hi = true) : convexHull ℝ (intSet [lo, hi]) ⊆ P.boundary := by
  have hf : f + 1 < V.length := by
    simp only [floorInB, Bool.and_eq_true, Nat.blt_eq] at h; exact h.1.1.1.1.1.1
  intro x hx
  refine ⟨(a + f) % P.n, Nat.mod_lt _ (n_pos_of_simple hP), ?_⟩
  rw [hC.edge_eq hf]
  exact hull_sub_floor h hx

/-- A chain vertex lies on the boundary. -/
theorem vertex_mem_boundary (hP : P.Simple) (hC : ChainAt P V a) {j : ℕ} (hj : j < V.length) :
    tpt V j ∈ P.boundary := by
  refine ⟨(a + j) % P.n, Nat.mod_lt _ (n_pos_of_simple hP), ?_⟩
  rw [Polygon.edge, hC j hj]
  exact Geometry.left_mem_segment _ _

/-- A one-point position at a chain vertex lies on the boundary. -/
theorem hull_single_sub_boundary (hP : P.Simple) (hC : ChainAt P V a) {j : ℕ} (hj : j < V.length)
    {L : List IPt} (hL : L = [cv V j]) : convexHull ℝ (intSet L) ⊆ P.boundary := by
  subst hL
  rw [intSet_cons, intSet_nil, insert_empty_eq, convexHull_singleton, Set.singleton_subset_iff]
  exact vertex_mem_boundary hP hC hj

end ArtGallery.BP.Tmpl

end
