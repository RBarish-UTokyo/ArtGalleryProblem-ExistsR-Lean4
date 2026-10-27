module

public import ArtGallery.Hardness.BP.Bay
public import ArtGallery.Hardness.Sec5.Templates.Tools

/-!
# Boundary-point variant: coverage of a bay

For a simple counter-clockwise polygon `P` containing a bay (`BayAt P one F a`) and no other edge
meeting the open box `(-1, 5/2) × (0, 1/8)` (relative coordinates, `BaySep P one F a`):

* the open column `(-1/2, 2) × (0, 1/8)` above the floor lies in the interior of `P`
  (`colO_subset_interior`); it is reached from an interior point next to the floor edge
  (`InteriorLeft`); hence the closed column `[-1/2, 2] × [0, 1/8]` lies in the region
  (`colC_subset_filled`);
* the four witness triangles (`Bay.lean`) lie in the region (`triW1_subset_filled`, …): their
  interiors meet no edge (chain edges by kernel-checked certificates `chainAvoids`, other edges by
  `BaySep`) and meet the open column;
* **the guard on the floor sees the whole bay** (`sees_bayRegion`): a point of the floor segment
  `[0, 3/2] × {0}` (resp. the point `(1/2, 0)` for a bay with `one` spikes) sees every point of
  the column and of the spikes; in particular it sees all witnesses of the bay
  (`sees_bayWit`);
* `sees_via_column`: a point of the closed column sees a point `q` of a convex subset `C` of the
  region when the segment meets `C` inside the column (sight lines leaving the bay upwards).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Irrational (HP hp hpo qdet mem_hp_cons mem_hp_nil mem_hpo_cons mem_hpo_nil)
open ArtGallery.Geometry (lerp)
open ArtGallery.Sec5 (Q2)

/-- The closed column `[-1/2, 2] × [0, 1/8]` above the floor (relative coordinates). -/
def colC : List HP := [(2, 0, 1), (-1, 0, 2), (0, 1, 0), (0, -8, 1)]

/-- The spike `w1` (closed triangle `(-1/2, 1/64), T1, (-1/2, 1/128)`). -/
def spW1 : List HP := [(-2, -256, 3), (4, 128, 1), (-2, 0, -1)]
/-- The spike `w2` (closed triangle `(2, 1/128), T2, (2, 1/64)`). -/
def spW2 : List HP := [(2, -256, 0), (-4, 128, 7), (1, 0, -2)]
/-- The spike `o1` (closed triangle `(-1/2, 3/64), O1, (-1/2, 5/128)`). -/
def spO1 : List HP := [(-6, -128, 3), (20, 128, 5), (-2, 0, -1)]
/-- The spike `o2` (closed triangle `(2, 5/128), O2, (2, 3/64)`). -/
def spO2 : List HP := [(2, -64, -1), (-20, 128, 35), (1, 0, -2)]

/-- **The bay** (as a region): the closed column and the spikes. -/
def bayRegion (one : Bool) (F : Frame) : Set Point :=
  F.pc colC ∪ F.pc spW1 ∪ F.pc spW2 ∪ {p | one = true ∧ (p ∈ F.pc spO1 ∨ p ∈ F.pc spO2)}

/-- Unfold membership in an explicit piece (column, spikes, triangles). -/
macro "bpc2" " at " h:ident : tactic =>
  `(tactic| (simp only [colC, colO, spW1, spW2, spO1, spO2, triW1, triW2, triO1, triO2,
                mem_hp_cons, mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true] at $h:ident
             norm_num at $h:ident))

/-- Reduce membership in an explicit piece to linear goals. -/
macro "bpc2_goal" : tactic =>
  `(tactic| (simp only [colC, colO, spW1, spW2, spO1, spO2, triW1, triW2, triO1, triO2,
                mem_hp_cons, mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true]
             push_cast
             repeat' apply And.intro))

theorem chainAvoids_triW1 (one : Bool) : Sec5.chainAvoids (bayRel one) triW1 = true := by
  cases one <;> decide +kernel
theorem chainAvoids_triW2 (one : Bool) : Sec5.chainAvoids (bayRel one) triW2 = true := by
  cases one <;> decide +kernel
theorem chainAvoids_triO1 : Sec5.chainAvoids (bayRel true) triO1 = true := by decide +kernel
theorem chainAvoids_triO2 : Sec5.chainAvoids (bayRel true) triO2 = true := by decide +kernel

section Cover

variable {P : Polygon} {one : Bool} {F : Frame} {a : ℕ}

/-- An interior point of `P` just above the middle of the floor edge. -/
theorem exists_floor_point (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft) :
    ∃ z, F.rel z ∈ hpo colO ∧ z ∈ P.filled \ P.boundary := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hs := hB.ne
  have hpos := hB.pos
  have hj : idxF one + 1 < (bayRel one).length := by cases one <;> decide
  have e1 : P.vtx ((a + idxF one) % P.n) = F.pt (-1/2, 0) := by
    rw [hB.vtx _ (by omega)]; cases one <;> rfl
  have e2 : P.vtx (((a + idxF one) % P.n + 1) % P.n) = F.pt (2, 0) := by
    rw [chain_succ, hB.vtx _ hj]; cases one <;> rfl
  obtain ⟨δ₀, hδ₀, hδ⟩ := hL _ (Nat.mod_lt (a + idxF one) hn) (1/2) (by norm_num) (by norm_num)
  set δ := min (δ₀ / 2) (1/40) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1/40 := min_le_right _ _
  obtain ⟨hin, -⟩ := hδ δ hδpos hδlt
  rw [e1, e2] at hin
  refine ⟨_, ?_, hin⟩
  have e : F.rel (F.pt (-1/2, 0) + (1 / 2 : ℝ) • (F.pt (2, 0) - F.pt (-1/2, 0)) +
      δ • leftNormal (F.pt (-1/2, 0)) (F.pt (2, 0))) = (3/4, 5/2 * δ) := by
    simp only [Frame.rel, Frame.pt, Frame.abs, ratPoint, leftNormal, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    push_cast
    ext <;> field_simp <;> ring
  rw [e]
  bpc2_goal <;> norm_num <;> linarith

/-- **The open column above the floor lies in the interior of `P`.** -/
theorem colO_subset_interior (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) : F.pco colO ⊆ P.filled \ P.boundary := by
  obtain ⟨z, hz, hzC⟩ := exists_floor_point hB hP hL
  exact Sec5.subset_interior_of_meets hP (Frame.convex_pco colO)
    (fun p hp => colO_not_mem_boundary hB hS hp) hz hzC

/-- A closed piece whose open part lies in the interior lies in the region. -/
theorem pc_subset_filled_of {l : List HP} (hO : F.pco l ⊆ P.filled \ P.boundary)
    {z : Point} (hz : z ∈ F.pco l) : F.pc l ⊆ P.filled :=
  calc F.pc l ⊆ closure (F.pco l) := Frame.pc_subset_closure_pco hz
    _ ⊆ closure P.filled := closure_mono (hO.trans sdiff_subset)
    _ = P.filled := (isClosed_filled P).closure_eq

/-- A point of the open column (relative coordinates `q`). -/
theorem abs_mem_colO {q : Point} (hs : F.s ≠ 0) (h : q ∈ hpo colO) : F.abs q ∈ F.pco colO :=
  Frame.mem_pco_of hs h

/-- **The closed column `[-1/2, 2] × [0, 1/8]` lies in the region.** -/
theorem colC_subset_filled (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) : F.pc colC ⊆ P.filled := by
  have hO := colO_subset_interior hB hP hL hS
  have e : F.pco colC = F.pco colO := rfl
  refine pc_subset_filled_of (l := colC) (e ▸ hO) (z := F.abs (1/2, 1/16)) ?_
  rw [e]; exact Frame.mem_pco_of hB.ne (by bpc2_goal <;> norm_num)

/-- An open piece avoiding the bay chain, lying in the box and meeting the open column, lies in
the interior of `P`. -/
theorem pco_subset_interior (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {l : List HP} (hc : Sec5.chainAvoids (bayRel one) l = true)
    (hbox : ∀ q ∈ hpo l, q ∈ bayBox) {q : Point} (hq : q ∈ hpo l) (hqc : q ∈ hpo colO) :
    F.pco l ⊆ P.filled \ P.boundary :=
  Sec5.subset_interior_of_meets hP (Frame.convex_pco l)
    (fun _ hp => hB.not_mem_boundary hS hc hp (hbox _ hp)) (Frame.mem_pco_of hB.ne hq)
    (colO_subset_interior hB hP hL hS (Frame.mem_pco_of hB.ne hqc))

/-- The triangle of `T1` lies in the region. -/
theorem triW1_subset_filled (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) : F.pc triW1 ⊆ P.filled := by
  have hq : ((1/2 : ℝ), (1/1000 : ℝ)) ∈ hpo triW1 := by bpc2_goal <;> norm_num
  refine pc_subset_filled_of (pco_subset_interior hB hP hL hS (chainAvoids_triW1 one) ?_ hq
    (by bpc2_goal <;> norm_num)) (Frame.mem_pco_of hB.ne hq)
  intro q h; bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The triangle of `T2` lies in the region. -/
theorem triW2_subset_filled (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) : F.pc triW2 ⊆ P.filled := by
  have hq : ((1 : ℝ), (1/1000 : ℝ)) ∈ hpo triW2 := by bpc2_goal <;> norm_num
  refine pc_subset_filled_of (pco_subset_interior hB hP hL hS (chainAvoids_triW2 one) ?_ hq
    (by bpc2_goal <;> norm_num)) (Frame.mem_pco_of hB.ne hq)
  intro q h; bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The triangle of `O1` lies in the region. -/
theorem triO1_subset_filled (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P true F a) : F.pc triO1 ⊆ P.filled := by
  have hq : ((0 : ℝ), (1/1000 : ℝ)) ∈ hpo triO1 := by bpc2_goal <;> norm_num
  refine pc_subset_filled_of (pco_subset_interior hB hP hL hS chainAvoids_triO1 ?_ hq
    (by bpc2_goal <;> norm_num)) (Frame.mem_pco_of hB.ne hq)
  intro q h; bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The triangle of `O2` lies in the region. -/
theorem triO2_subset_filled (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P true F a) : F.pc triO2 ⊆ P.filled := by
  have hq : ((1 : ℝ), (1/1000 : ℝ)) ∈ hpo triO2 := by bpc2_goal <;> norm_num
  refine pc_subset_filled_of (pco_subset_interior hB hP hL hS chainAvoids_triO2 ?_ hq
    (by bpc2_goal <;> norm_num)) (Frame.mem_pco_of hB.ne hq)
  intro q h; bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Two points of a closed piece contained in the region see each other. -/
theorem sees_of_mem_pc {l : List HP} (hl : F.pc l ⊆ P.filled) {g q : Point}
    (hg : g ∈ F.pc l) (hq : q ∈ F.pc l) : P.Sees g q :=
  (Geometry.segment_subset_of_convex (Frame.convex_pc l) hg hq).trans hl

theorem pc_mono {l l' : List HP} (h : ∀ q, q ∈ hp l → q ∈ hp l') : F.pc l ⊆ F.pc l' :=
  fun _ hp => h _ hp

/-- **The guard on the floor sees the whole bay.**  A point `g` of the floor segment
`[0, 3/2] × {0}` (for a bay with `one` spikes: the point `(1/2, 0)`) sees every point of the
column and of the spikes. -/
theorem sees_bayRegion (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : 0 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 3/2) (hone : one = true → (F.rel g).1 = 1/2) {q : Point}
    (hq : q ∈ bayRegion one F) : P.Sees g q := by
  rcases hq with ((hq | hq) | hq) | ⟨rfl, hq | hq⟩
  · exact sees_of_mem_pc (colC_subset_filled hB hP hL hS)
      (show F.rel g ∈ hp colC by bpc2_goal <;> linarith) hq
  · refine sees_of_mem_pc (triW1_subset_filled hB hP hL hS)
      (show F.rel g ∈ hp triW1 by bpc2_goal <;> linarith) ?_
    show F.rel q ∈ hp triW1
    have h := hq; change F.rel q ∈ hp spW1 at h
    bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
    bpc2_goal <;> linarith
  · refine sees_of_mem_pc (triW2_subset_filled hB hP hL hS)
      (show F.rel g ∈ hp triW2 by bpc2_goal <;> linarith) ?_
    show F.rel q ∈ hp triW2
    have h := hq; change F.rel q ∈ hp spW2 at h
    bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
    bpc2_goal <;> linarith
  · have hx := hone rfl
    refine sees_of_mem_pc (triO1_subset_filled hB hP hL hS)
      (show F.rel g ∈ hp triO1 by bpc2_goal <;> linarith) ?_
    show F.rel q ∈ hp triO1
    have h := hq; change F.rel q ∈ hp spO1 at h
    bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
    bpc2_goal <;> linarith
  · have hx := hone rfl
    refine sees_of_mem_pc (triO2_subset_filled hB hP hL hS)
      (show F.rel g ∈ hp triO2 by bpc2_goal <;> linarith) ?_
    show F.rel q ∈ hp triO2
    have h := hq; change F.rel q ∈ hp spO2 at h
    bpc2 at h; obtain ⟨c1, c2, c3⟩ := h
    bpc2_goal <;> linarith

/-- The witnesses lie in the bay. -/
theorem bayWit_mem_bayRegion (hs : F.s ≠ 0) {w : Point} (hw : w ∈ bayWit one F) :
    w ∈ bayRegion one F := by
  rcases hw with hw | ⟨rfl, hw⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · refine Or.inl (Or.inl (Or.inr ?_))
      show F.rel _ ∈ hp spW1
      rw [Frame.rel_pt hs]; simp only [ratPoint, w1Rel]; bpc2_goal <;> norm_num
    · refine Or.inl (Or.inr ?_)
      show F.rel _ ∈ hp spW2
      rw [Frame.rel_pt hs]; simp only [ratPoint, w2Rel]; bpc2_goal <;> norm_num
  · rcases hw with rfl | rfl
    · refine Or.inr ⟨rfl, Or.inl ?_⟩
      show F.rel _ ∈ hp spO1
      rw [Frame.rel_pt hs]; simp only [ratPoint, o1Rel]; bpc2_goal <;> norm_num
    · refine Or.inr ⟨rfl, Or.inr ?_⟩
      show F.rel _ ∈ hp spO2
      rw [Frame.rel_pt hs]; simp only [ratPoint, o2Rel]; bpc2_goal <;> norm_num

/-- **The guard on the floor sees all witnesses of its bay.** -/
theorem sees_bayWit (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : 0 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 3/2) (hone : one = true → (F.rel g).1 = 1/2) {w : Point}
    (hw : w ∈ bayWit one F) : P.Sees g w :=
  sees_bayRegion hB hP hL hS hg2 hg1 hg1' hone (bayWit_mem_bayRegion hB.ne hw)

/-- Every point of the position of the bay sees all its witnesses. -/
theorem baySpot_sees_bayWit (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {g : Point} (hg : g ∈ baySpot one F) {w : Point}
    (hw : w ∈ bayWit one F) : P.Sees g w := by
  obtain ⟨h1, h2, h3⟩ := baySpot_rel hB.ne hg
  refine sees_bayWit hB hP hL hS h1 h2 h3 (fun hone => ?_) hw
  subst hone
  rcases hg with rfl
  rw [Frame.rel_pt hB.ne]; simp [ratPoint, g1Rel]

/-- The position of the bay lies on the boundary of `P`. -/
theorem baySpot_mem_boundary (hB : BayAt P one F a) (hP : P.Simple) {g : Point}
    (hg : g ∈ baySpot one F) : g ∈ P.boundary := by
  obtain ⟨h1, h2, h3⟩ := baySpot_rel hB.ne hg
  exact hB.floor_mem_boundary hP h1 (by linarith) (by linarith)

/-- **Sight lines leaving the bay.**  A point `g` of the closed column sees a point `q` of a convex
subset `C` of the region if the segment `g q` contains a point `m` of `C` in the closed
column. -/
theorem sees_via_column (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {C : Set Point} (hC : Convex ℝ C) (hCP : C ⊆ P.filled) {g q m : Point}
    (hg : g ∈ F.pc colC) (hq : q ∈ C) (hmC : m ∈ C) (hm : m ∈ F.pc colC)
    (hmgq : m ∈ ArtGallery.segment g q) : P.Sees g q :=
  Sec5.Tmpl.sees_of_two_convex (Frame.convex_pc colC) hC (colC_subset_filled hB hP hL hS) hCP hg hq
    hm hmC hmgq

/-- A point of the floor line with abscissa in `[-1/4, 3/2]` sees `T1`. -/
theorem sees_w1 (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : -1/4 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 3/2) : P.Sees g (F.pt w1Rel) := by
  refine sees_of_mem_pc (triW1_subset_filled hB hP hL hS)
    (show F.rel g ∈ hp triW1 by bpc2_goal <;> linarith) ?_
  show F.rel _ ∈ hp triW1
  rw [Frame.rel_pt hB.ne]; simp only [ratPoint, w1Rel]; bpc2_goal <;> norm_num

/-- A point of the floor line with abscissa in `[0, 7/4]` sees `T2`. -/
theorem sees_w2 (hB : BayAt P one F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P one F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : 0 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 7/4) : P.Sees g (F.pt w2Rel) := by
  refine sees_of_mem_pc (triW2_subset_filled hB hP hL hS)
    (show F.rel g ∈ hp triW2 by bpc2_goal <;> linarith) ?_
  show F.rel _ ∈ hp triW2
  rw [Frame.rel_pt hB.ne]; simp only [ratPoint, w2Rel]; bpc2_goal <;> norm_num

/-- A point of the floor line with abscissa in `[-1/4, 1/2]` sees `O1`. -/
theorem sees_o1 (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P true F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : -1/4 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 1/2) : P.Sees g (F.pt o1Rel) := by
  refine sees_of_mem_pc (triO1_subset_filled hB hP hL hS)
    (show F.rel g ∈ hp triO1 by bpc2_goal <;> linarith) ?_
  show F.rel _ ∈ hp triO1
  rw [Frame.rel_pt hB.ne]; simp only [ratPoint, o1Rel]; bpc2_goal <;> norm_num

/-- A point of the floor line with abscissa in `[1/2, 7/4]` sees `O2`. -/
theorem sees_o2 (hB : BayAt P true F a) (hP : P.Simple) (hL : P.InteriorLeft)
    (hS : BaySep P true F a) {g : Point} (hg2 : (F.rel g).2 = 0) (hg1 : 1/2 ≤ (F.rel g).1)
    (hg1' : (F.rel g).1 ≤ 7/4) : P.Sees g (F.pt o2Rel) := by
  refine sees_of_mem_pc (triO2_subset_filled hB hP hL hS)
    (show F.rel g ∈ hp triO2 by bpc2_goal <;> linarith) ?_
  show F.rel _ ∈ hp triO2
  rw [Frame.rel_pt hB.ne]; simp only [ratPoint, o2Rel]; bpc2_goal <;> norm_num

end Cover

end ArtGallery.BP

end
