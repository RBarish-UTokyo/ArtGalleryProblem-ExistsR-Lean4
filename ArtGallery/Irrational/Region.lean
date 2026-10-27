module

public import ArtGallery.Irrational.Polygon
public import ArtGallery.Jordan.Jordan
public import ArtGallery.Jordan.Filled

/-!
# The region of the polygon

`filled_eq_U : P.filled = U`: the closed region of `𝒫` is the union of the 14 closed convex
pieces.  Consequently `𝒫` is x-monotone (`xMonotone_P`).

* `U ⊆ P.filled`: by the (proved) polygonal Jordan curve theorem, `P.filled \ P.boundary` is one
  connected component of the complement of the boundary.  A point of the open piece `R_ℓ` lies in
  it (`Jordan.edge_sides` at the leftmost edge, whose right side is reached by a ray to the left);
  the open pieces and the bridges are convex, meet no edge, and form a chain
  `R_ℓ → bridge → B → bridge → pocket`, so all open pieces lie in that component and the closed
  pieces in its closure.
* `P.filled ⊆ U`: the vertical sections of `U` are intervals (`mem_U_vert`), so from a point
  outside `U` one of the two vertical rays avoids `U ⊇ P.boundary`; the component of the point is
  unbounded.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set Filter Topology

/-! ### Unfolding membership in the pieces -/

theorem mem_U_iff {p : Point} : p ∈ U ↔ p ∈ hp cB ∨ p ∈ hp cTbl ∨ p ∈ hp cTbm ∨ p ∈ hp cPbl ∨
    p ∈ hp cPbr ∨ p ∈ hp cTbr ∨ p ∈ hp cTtl ∨ p ∈ hp cTtm ∨ p ∈ hp cTtr ∨ p ∈ hp cPtl ∨
    p ∈ hp cPtr ∨ p ∈ hp cRm ∨ p ∈ hp cRl ∨ p ∈ hp cRr := by
  simp [U, unionHP, pieces]

/-- Unfold membership in a closed piece, open piece or bridge into linear inequalities. -/
macro "piece_simp" " at " h:ident : tactic =>
  `(tactic| (simp only [cB, cTbl, cTbm, cPbl, cPbr, cTbr, cTtl, cTtm, cTtr, cPtl, cPtr, cRm, cRl,
      cRr, wTbl, wTbm, wPbl, wPbr, wTbr, wTtl, wTtm, wTtr, wPtl, wPtr, wRm, wRl, wRr, mem_hp_cons,
      mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true] at $h:ident; push_cast at $h:ident))

/-- Prove membership of an explicit point in a piece. -/
macro "piece_mem" : tactic =>
  `(tactic| (simp only [cB, cTbl, cTbm, cPbl, cPbr, cTbr, cTtl, cTtm, cTtr, cPtl, cPtr, cRm, cRl,
      cRr, wTbl, wTbm, wPbl, wPbr, wTbr, wTtl, wTtm, wTtr, wPtl, wPtr, wRm, wRl, wRr, mem_hp_cons,
      mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true]; push_cast; norm_num))

/-- Reduce membership of a point in a piece to linear inequality goals. -/
macro "piece_goal" : tactic =>
  `(tactic| (simp only [cB, cTbl, cTbm, cPbl, cPbr, cTbr, cTtl, cTtm, cTtr, cPtl, cPtr, cRm, cRl,
      cRr, wTbl, wTbm, wPbl, wPbr, wTbr, wTtl, wTtm, wTtr, wPtl, wPtr, wRm, wRl, wRr, mem_hp_cons,
      mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true]; push_cast; repeat' apply And.intro))

/-- Split a point of `U` into the 14 pieces, unfolded into linear inequalities. -/
macro "U_cases" h:ident : tactic =>
  `(tactic| (rcases mem_U_iff.1 $h:ident with $h | $h | $h | $h | $h | $h | $h | $h | $h | $h |
      $h | $h | $h | $h <;> piece_simp at $h <;> casesm* _ ∧ _))

/-- Prove that a point is in `U` by finding a piece whose inequalities follow by `linarith`. -/
macro "U_mem" : tactic =>
  `(tactic| (rw [mem_U_iff]; first
    | (left; piece_goal; all_goals linarith)
    | (right; left; piece_goal; all_goals linarith)
    | (right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; right; right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; right; right; right; right; left; piece_goal; all_goals linarith)
    | (right; right; right; right; right; right; right; right; left; piece_goal;
        all_goals linarith)
    | (right; right; right; right; right; right; right; right; right; left; piece_goal;
        all_goals linarith)
    | (right; right; right; right; right; right; right; right; right; right; left; piece_goal;
        all_goals linarith)
    | (right; right; right; right; right; right; right; right; right; right; right; left;
        piece_goal; all_goals linarith)
    | (right; right; right; right; right; right; right; right; right; right; right; right; left;
        piece_goal; all_goals linarith)
    | (right; right; right; right; right; right; right; right; right; right; right; right; right;
        piece_goal; all_goals linarith)))

/-- Bounds for the points of `U`. -/
theorem U_bounds {p : Point} (hp : p ∈ U) :
    -10 ≤ p.1 ∧ p.1 ≤ 30 ∧ -12/7 ≤ p.2 ∧ p.2 ≤ 8 := by
  U_cases hp <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem boundary_bounds {p : Point} (hp : p ∈ P.boundary) : -10 ≤ p.1 :=
  (U_bounds (boundary_subset_U hp)).1

/-! ### Vertical sections -/

theorem mem_U_of_lt_zero {p : Point} (hpU : p ∈ U) (h : p.1 < 0) : p ∈ hp cRl := by
  U_cases hpU <;> first | (exfalso; linarith) | (piece_goal <;> linarith)

theorem mem_U_of_gt_twenty {p : Point} (hpU : p ∈ U) (h : 20 < p.1) : p ∈ hp cRr := by
  U_cases hpU <;> first | (exfalso; linarith) | (piece_goal <;> linarith)

/-- Moving up from a point of `U` towards the line `y = 0` stays in `U`. -/
theorem mem_U_up {p : Point} (hp : p ∈ U) {y : ℝ} (h1 : p.2 ≤ y) (h2 : y ≤ 0) : (p.1, y) ∈ U := by
  have hp' := hp
  U_cases hp <;> first | (exfalso; linarith) | U_mem

/-- Moving down from a point of `U` towards the line `y = 4` stays in `U`. -/
theorem mem_U_down {p : Point} (hp : p ∈ U) {y : ℝ} (h1 : 4 ≤ y) (h2 : y ≤ p.2) :
    (p.1, y) ∈ U := by
  have hp' := hp
  U_cases hp <;> first | (exfalso; linarith) | U_mem

/-- **The vertical sections of `U` are intervals.** -/
theorem mem_U_vert {a y₁ y₂ y : ℝ} (h1 : (a, y₁) ∈ U) (h2 : (a, y₂) ∈ U) (hy1 : y₁ ≤ y)
    (hy2 : y ≤ y₂) : (a, y) ∈ U := by
  rcases lt_or_ge a 0 with ha | ha
  · have e1 := mem_U_of_lt_zero h1 ha
    have e2 := mem_U_of_lt_zero h2 ha
    piece_simp at e1; piece_simp at e2
    U_mem
  rcases lt_or_ge 20 a with ha' | ha'
  · have e1 := mem_U_of_gt_twenty h1 ha'
    have e2 := mem_U_of_gt_twenty h2 ha'
    piece_simp at e1; piece_simp at e2
    U_mem
  rcases lt_or_ge y 0 with hy | hy
  · exact mem_U_up h1 hy1 hy.le
  rcases le_or_gt y 4 with hy' | hy'
  · U_mem
  · exact mem_U_down h2 hy'.le hy2

/-! ### `P.filled ⊆ U` -/

/-- A point whose vertical upward or downward ray avoids `U` is not in the region. -/
theorem not_mem_filled_of_ray {q : Point} (hq : q ∉ U) {d : Point} (hd : d ≠ 0)
    (hray : ∀ s : ℝ, 0 ≤ s → q + s • d ∉ U) : q ∉ P.filled := by
  have hb : q ∉ P.boundary := fun h => hq (boundary_subset_U h)
  have hunb : ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ q) := by
    refine Jordan.not_isBoundedSet_connectedComponentIn_of_ray P hd ?_
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hray s hs (boundary_subset_U hmem)
  rintro (h | h)
  · exact hb h
  · exact hunb h

theorem filled_subset_U : P.filled ⊆ U := by
  intro q hq
  by_contra hqU
  by_cases hup : ∃ s : ℝ, 0 ≤ s ∧ (q.1, q.2 + s) ∈ U
  · by_cases hdown : ∃ s : ℝ, 0 ≤ s ∧ (q.1, q.2 - s) ∈ U
    · obtain ⟨s₁, hs₁, h₁⟩ := hup
      obtain ⟨s₂, hs₂, h₂⟩ := hdown
      exact hqU (mem_U_vert h₂ h₁ (by linarith) (by linarith))
    · push Not at hdown
      refine not_mem_filled_of_ray hqU (d := (0, -1)) (by simp) (fun s hs => ?_) hq
      have e : q + s • ((0 : ℝ), (-1 : ℝ)) = (q.1, q.2 - s) := by ext <;> simp; ring
      rw [e]; exact hdown s hs
  · push Not at hup
    refine not_mem_filled_of_ray hqU (d := (0, 1)) (by simp) (fun s hs => ?_) hq
    have e : q + s • ((0 : ℝ), (1 : ℝ)) = (q.1, q.2 + s) := by ext <;> simp
    rw [e]; exact hup s hs

/-! ### `U ⊆ P.filled` -/

/-- The interior region `P.filled \ P.boundary`. -/
def C : Set Point := P.filled \ P.boundary

/-- An open piece or bridge meeting the interior region lies in it. -/
theorem hpo_subset_C {l : List HP} (hl : l ∈ openSets) {z : Point} (hz : z ∈ hpo l)
    (hzC : z ∈ C) : hpo l ⊆ C := by
  have hC : C = connectedComponentIn P.boundaryᶜ z :=
    Jordan.filled_sdiff_boundary_eq_component simple_P hzC
  rw [hC]
  exact (convex_hpo l).isPreconnected.subset_connectedComponentIn hz
    (fun p hp => not_mem_boundary_of_mem_open hl hp)

theorem vtx47 : P.vtx 47 = ((-10 : ℝ), (9/5 : ℝ)) := by
  rw [P, vtx_map_ratPoint, show paperVerts.getD 47 0 = ((-10 : ℚ), (9/5 : ℚ)) from rfl]
  simp [ratPoint]

theorem vtx48 : P.vtx 48 = ((-10 : ℝ), (17/10 : ℝ)) := by
  rw [P, vtx_map_ratPoint, show paperVerts.getD 48 0 = ((-10 : ℚ), (17/10 : ℚ)) from rfl]
  simp [ratPoint]

/-- A point of the open piece `R_ℓ` lies in the interior region. -/
theorem exists_Rl_C : ∃ z, z ∈ hpo cRl ∧ z ∈ C := by
  have hes := Jordan.edge_sides simple_P (i := 47) (by rw [P_n]; norm_num) (t := 1 / 2)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨δ, hδ, hδ'⟩ := (hes.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have hL : Jordan.leftPoint P 47 (1 / 2) δ = (-10 + δ / 10, 7 / 4) := by
    simp only [Jordan.leftPoint, Jordan.offset, Jordan.nrm, P_n, Nat.reduceAdd, Nat.reduceMod,
      vtx47, vtx48]
    ext <;> simp [Geometry.lerp] <;> ring
  have hR : Jordan.rightPoint P 47 (1 / 2) δ = (-10 - δ / 10, 7 / 4) := by
    simp only [Jordan.rightPoint, Jordan.offset, Jordan.nrm, P_n, Nat.reduceAdd, Nat.reduceMod,
      vtx47, vtx48]
    ext <;> simp [Geometry.lerp] <;> ring
  rw [hL, hR] at hδ
  have hRout : ((-10 - δ / 10, 7 / 4) : Point) ∉ P.filled := by
    refine not_mem_filled_of_ray (d := (-1, 0)) ?_ (by simp) (fun s hs h => ?_)
    · intro h; have := (U_bounds h).1; linarith [hδ'.1]
    · have := (U_bounds h).1
      simp at this; linarith [hδ'.1]
  have hz : ((-10 + δ / 10, 7 / 4) : Point) ∈ hpo cRl := by
    piece_mem; refine ⟨?_, ?_⟩ <;> linarith [hδ'.1, hδ'.2]
  refine ⟨_, hz, hδ.2 hRout, not_mem_boundary_of_mem_open (by simp [openSets, pieces]) hz⟩

theorem hpo_B_subset_C : hpo cB ⊆ C := by
  obtain ⟨z, hz, hzC⟩ := exists_Rl_C
  have h1 : hpo cRl ⊆ C := hpo_subset_C (by simp [openSets, pieces]) hz hzC
  have h2 : hpo wRl ⊆ C :=
    hpo_subset_C (by simp [openSets]) (z := (-9, 7/4)) (by piece_mem) (h1 (by piece_mem))
  exact hpo_subset_C (by simp [openSets, pieces]) (z := (1, 7/4)) (by piece_mem)
    (h2 (by piece_mem))

/-- A pocket whose bridge contains explicit points of the open basic rectangle and of the open
pocket lies in the region. -/
theorem hp_subset_filled_of_bridge {cK wK : List HP} (hK : cK ∈ openSets) (hW : wK ∈ openSets)
    {zb zk : Point} (hzb : zb ∈ hpo cB) (hzbW : zb ∈ hpo wK) (hzkW : zk ∈ hpo wK)
    (hzk : zk ∈ hpo cK) : hp cK ⊆ P.filled := by
  have h1 : hpo wK ⊆ C := hpo_subset_C hW hzbW (hpo_B_subset_C hzb)
  have h2 : hpo cK ⊆ C := hpo_subset_C hK hzk (h1 hzkW)
  calc hp cK ⊆ closure (hpo cK) := hp_subset_closure_hpo hzk
    _ ⊆ closure P.filled := closure_mono (h2.trans sdiff_subset)
    _ = P.filled := (Jordan.isClosed_filled P).closure_eq

theorem hp_B_subset_filled : hp cB ⊆ P.filled := by
  have hz : ((1, 1) : Point) ∈ hpo cB := by piece_mem
  calc hp cB ⊆ closure (hpo cB) := hp_subset_closure_hpo hz
    _ ⊆ closure P.filled := closure_mono (hpo_B_subset_C.trans sdiff_subset)
    _ = P.filled := (Jordan.isClosed_filled P).closure_eq

theorem U_subset_filled : U ⊆ P.filled := by
  intro p hp
  have hO : ∀ l ∈ pieces, l ∈ openSets := fun l hl => List.mem_append_left _ hl
  rcases mem_U_iff.1 hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hp_B_subset_filled h
  · exact hp_subset_filled_of_bridge (wK := wTbl) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (3/2, 3)) (zk := (39/20, -1/5)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wTbm) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (4, 1)) (zk := (31/10, -1/10)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wPbl) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (5, 1)) (zk := (5, -1/2)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wPbr) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (13, 1)) (zk := (13, -1)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wTbr) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (37/2, 3)) (zk := (379/20, -1/5)) (by piece_mem)
      (by piece_mem) (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wTtl) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (5/2, 1)) (zk := (41/20, 21/5)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wTtm) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (7, 1)) (zk := (69/4, 41/10)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wTtr) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (39/2, 1)) (zk := (381/20, 21/5)) (by piece_mem)
      (by piece_mem) (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wPtl) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (5, 1)) (zk := (5, 5)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wPtr) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (13, 1)) (zk := (13, 5)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wRm) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (211/20, 1)) (zk := (211/20, 5)) (by piece_mem)
      (by piece_mem) (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wRl) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (1, 7/4)) (zk := (-9, 7/4)) (by piece_mem) (by piece_mem)
      (by piece_mem) (by piece_mem) h
  · exact hp_subset_filled_of_bridge (wK := wRr) (hO _ (by simp [pieces]))
      (by simp [openSets]) (zb := (19, 11/20)) (zk := (21, 11/20)) (by piece_mem)
      (by piece_mem) (by piece_mem) (by piece_mem) h

/-- **The region of `𝒫` is `U`.** -/
theorem filled_eq_U : P.filled = U := Subset.antisymm filled_subset_U U_subset_filled

/-- **`𝒫` is x-monotone.** -/
theorem xMonotone_P : P.XMonotone := by
  intro a
  have hS : {p ∈ P.filled | p.1 = a} = (fun y : ℝ => ((a, y) : Point)) '' {y | (a, y) ∈ U} := by
    ext p
    simp only [filled_eq_U, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hp, rfl⟩; exact ⟨p.2, hp, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, rfl⟩
  rw [hS]
  have hoc : OrdConnected {y | ((a, y) : Point) ∈ U} :=
    ⟨fun y₁ h₁ y₂ h₂ y hy => mem_U_vert h₁ h₂ hy.1 hy.2⟩
  exact hoc.isPreconnected.image _ (by fun_prop : Continuous fun y : ℝ => ((a, y) : Point)).continuousOn

end

end ArtGallery.Irrational
