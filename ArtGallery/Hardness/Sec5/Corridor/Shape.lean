module

public import ArtGallery.Hardness.Sec5.Corridor.Upper
public import ArtGallery.Existence.Base
public import ArtGallery.Vis.Rooms

/-!
# Section 5: corridors — the shape of the corridor

The **corridor polygon** `I.poly` has the vertex list `chainBefore ++ chainAfter`
(`c0, slots…, c1, d1, upper wall…, d0`), i.e. the corridor chains of the unit closed by the
window `c1 d1` and the entrance `d0 c0` (docs/section5/08_proof_plan.md §4, Lemma S4(c)).

* `Good.chainSimple_chainBefore`: the floor chain is a simple polyline (dented line);
* `Good.chainSimple_chainAfter` (in `Upper.lean`): the upper wall is `x`-monotone, hence simple;
* `Good.poly_simple`: the corridor polygon is simple;
* `Good.poly_interiorLeft`: it is counter-clockwise (all vertices are left of the edge
  `d1 → p_0` on the line `x = S + 2`);
* box: all vertices lie in `[S, S + 2] × [H − 1/4, H + 1/2]` (`Good.chainBefore_box`,
  `Good.chainAfter_box`), and so does the region (`Good.poly_filled_box`);
* the floor lies on or below `y = H`, the upper wall on or above `y = H + ρ`; only `c0`, `d0` lie on
  `x = S` and only `c1`, `d1`, `p_0` on `x = S + 2`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

/-! ## Generic facts on polylines -/

/-- If all vertices of a polyline other than the last one are strictly below the level `c` of an
affine functional at the last vertex `m`, every edge point at level `≥ c` is `m`. -/
theorem edges_level_last {L : List Point} {m : Point} {α β c : ℝ}
    (hL : ∀ x ∈ L, α * x.1 + β * x.2 < c) (hm : α * m.1 + β * m.2 = c) :
    ∀ e ∈ edgesOf (L ++ [m]), ∀ z ∈ segOf e, c ≤ α * z.1 + β * z.2 → z = m := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro e he z hz hzc
    cases L with
    | nil =>
      simp only [List.cons_append, List.nil_append, edgesOf_cons_cons, edgesOf_single,
        List.mem_singleton] at he
      subst he
      obtain ⟨t, h0, h1, rfl⟩ := hz
      have ha := hL a (by simp)
      simp only at hzc ⊢
      have ht : t = 1 := by
        by_contra hne
        have : t < 1 := lt_of_le_of_ne h1 hne
        nlinarith [mul_pos (sub_pos.2 this) (sub_pos.2 ha)]
      subst ht; ext <;> simp
    | cons b L =>
      simp only [List.cons_append, edgesOf_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exfalso
        have ha := hL a (by simp)
        have hb := hL b (by simp)
        obtain ⟨t, h0, h1, rfl⟩ := hz
        simp only at hzc
        nlinarith [mul_nonneg h0 (sub_pos.2 hb).le, mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 ha).le]
      · exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) e
          (by simpa [List.cons_append] using he) z hz hzc

/-- If all vertices of a polyline other than the first one `m` are strictly below the level of an
affine functional at `m`, every edge point at level `≥ c` is `m`. -/
theorem edges_level_first {L : List Point} {m : Point} {α β c : ℝ}
    (hL : ∀ x ∈ L, α * x.1 + β * x.2 < c) (hm : α * m.1 + β * m.2 = c) :
    ∀ e ∈ edgesOf (m :: L), ∀ z ∈ segOf e, c ≤ α * z.1 + β * z.2 → z = m := by
  intro e he z hz hzc
  cases L with
  | nil => simp at he
  | cons b L =>
    simp only [edgesOf_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · obtain ⟨t, h0, h1, rfl⟩ := hz
      have hb := hL b (by simp)
      simp only at hzc ⊢
      have ht : t = 0 := by
        by_contra hne
        have : 0 < t := lt_of_le_of_ne h0 (Ne.symm hne)
        nlinarith [mul_pos this (sub_pos.2 hb)]
      subst ht; ext <;> simp
    · exfalso
      have hm' := mem_of_mem_edgesOf he
      have h1 := hL _ hm'.1
      have h2 := hL _ hm'.2
      obtain ⟨t, h0, h1', rfl⟩ := hz
      simp only at hzc
      nlinarith [mul_nonneg h0 (sub_pos.2 h2).le, mul_nonneg (sub_nonneg.2 h1') (sub_pos.2 h1).le]

/-- Edges of a polyline whose vertices satisfy an affine inequality satisfy it. -/
theorem edges_affine_le {L : List Point} {α β c : ℝ} (hL : ∀ x ∈ L, α * x.1 + β * x.2 ≤ c) :
    ∀ e ∈ edgesOf L, ∀ z ∈ segOf e, α * z.1 + β * z.2 ≤ c := by
  intro e he z hz
  have hm := mem_of_mem_edgesOf he
  exact seg_affine_le hz (hL _ hm.1) (hL _ hm.2)

/-- **Closing a polyline at a vertical line.**  A simple polyline `a, W…, z` whose end points lie
on the line `x = c`, all other vertices strictly right of it, is a simple polygon. -/
theorem simple_of_chainSimple_vertical {a z : Point} {W : List Point}
    (hV : ChainSimple (a :: W ++ [z])) (hW : W ≠ []) {c : ℝ} (ha : a.1 = c) (hz : z.1 = c)
    (hWc : ∀ x ∈ W, c < x.1) : (Polygon.mk (a :: W ++ [z])).Simple := by
  set V := a :: W ++ [z] with hVdef
  have hlen : V.length = W.length + 2 := by simp [hVdef]
  have hWl : 1 ≤ W.length := List.length_pos_iff.2 hW
  have g0 : V.getD 0 0 = a := by simp [hVdef]
  have glast : V.getD (V.length - 1) 0 = z := by
    rw [hlen, show W.length + 2 - 1 = W.length + 1 by omega]
    simp [hVdef, List.getD_eq_getElem?_getD]
  have gmid : ∀ j, 1 ≤ j → j ≤ W.length → V.getD j 0 ∈ W := by
    intro j hj1 hj2
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [hVdef, List.cons_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    simp only [List.getElem?_eq_getElem (show i < W.length by omega), Option.getD_some]
    exact List.getElem_mem _
  have hclose : ∀ y ∈ ArtGallery.segment (V.getD (V.length - 1) 0) (V.getD 0 0), y.1 = c := by
    intro y hy
    rw [glast, g0] at hy
    rw [seg_fst_of_vertical hy (by rw [ha, hz])]; exact hz
  refine simple_of_chainSimple hV (by omega) ?_ ?_ ?_
  · intro y ⟨hy1, hy2⟩
    rw [mem_singleton_iff]
    have h1 : c < (V.getD 1 0).1 := hWc _ (gmid 1 le_rfl hWl)
    rw [g0] at hy2 ⊢
    exact seg_eq_left_of_fst hy2 (by rw [ha]; exact ne_of_lt h1) (by rw [hclose y hy1, ha])
  · intro y ⟨hy1, hy2⟩
    rw [mem_singleton_iff]
    have h1 : c < (V.getD (V.length - 2) 0).1 := hWc _ (gmid _ (by omega) (by omega))
    rw [glast] at hy2 ⊢
    exact seg_eq_right_of_fst hy2 (by rw [hz]; exact ne_of_gt h1) (by rw [hclose y hy1, hz])
  · intro k hk1 hk2
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have h1 := hWc _ (gmid k hk1 (by omega))
    have h2 := hWc _ (gmid (k + 1) (by omega) (by omega))
    have := Vis.Cert.seg_fst_lb hy2 h1.le h2.le
    have h3 := hclose y hy1
    have := Vis.Cert.seg_fst_lb hy2 h1.le h2.le
    -- strict: both endpoints strictly right
    obtain ⟨t, h0, ht1, hyeq⟩ := Irrational.mem_segment_coords hy2
    nlinarith [mul_nonneg h0 (sub_pos.2 h2).le, mul_nonneg (sub_nonneg.2 ht1) (sub_pos.2 h1).le]

/-- **Region in a half-plane.**  If every vertex satisfies `α x + β y ≤ c`, and some vertex `v`
satisfies it strictly, the region lies in the closed half-plane. -/
theorem filled_subset_halfplane {K : Polygon} {α β c : ℝ}
    (hK : ∀ i < K.n, α * (K.vtx i).1 + β * (K.vtx i).2 ≤ c) {v : Point}
    (hv : α * v.1 + β * v.2 < c) : K.filled ⊆ {z | α * z.1 + β * z.2 ≤ c} := by
  intro z hz
  by_contra hzc
  simp only [mem_ofPred_eq, not_le] at hzc
  set d := c - (α * v.1 + β * v.2) with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  refine Existence.not_mem_filled_of_neg_affine (T := {z | α * z.1 + β * z.2 ≤ c})
    (f := fun w => (c - (α * w.1 + β * w.2)) / d) ?_ ?_ (v := v) (z := z) ?_ ?_ ?_ hz
  · rintro x ⟨i, hi, hx⟩
    exact seg_affine_le hx (hK i hi) (hK _ (Nat.mod_lt _ (by omega)))
  · intro y hy
    apply div_nonneg _ hdpos.le
    simp only [mem_ofPred_eq] at hy
    linarith
  · intro t
    simp only [Geometry.lerp]
    field_simp
    ring
  · exact div_self (ne_of_gt (by linarith))
  · exact div_neg_of_neg_of_pos (by linarith) (by linarith)

namespace Input

variable {I : Input} {N : ℚ}

/-! ## The real dents of the floor -/

/-- The slope-2 slot of pair `k` as a dent of the line `y = H`. -/
noncomputable def dentS2 (I : Input) (k : ℕ) : Dent :=
  dent2 (I.kx k 2 : ℝ) (I.H : ℝ) (I.ε : ℝ)

/-- The slope-4 slot of pair `k` as a dent of the line `y = H`. -/
noncomputable def dentS4 (I : Input) (k : ℕ) : Dent :=
  dent4 (I.kx k 4 : ℝ) (I.H : ℝ) (I.ε : ℝ)

theorem slot2_map (k : ℕ) :
    (I.slot2 k).map ratPoint = [(I.dentS2 k).A, (I.dentS2 k).T, (I.dentS2 k).B] := by
  simp only [slot2, slotTip, List.map_cons, List.map_nil, dentS2, dent2, ratPoint]
  push_cast
  norm_num

theorem slot4_map (k : ℕ) :
    (I.slot4 k).map ratPoint = [(I.dentS4 k).A, (I.dentS4 k).T, (I.dentS4 k).B] := by
  simp only [slot4, slotTip, List.map_cons, List.map_nil, dentS4, dent4, ratPoint]
  push_cast
  norm_num

/-! ### Generic dent lists -/

section DentLists

variable {S H e : ℝ}

theorem disjoint_dent22 {κ κ' : ℝ} (h : κ < κ' - e / 8) :
    Disjoint (dent2 κ H e).R (dent2 κ' H e).R := disjoint_R2_R2 h

theorem disjoint_dent44 {κ κ' : ℝ} (h : κ + e / 8 < κ') :
    Disjoint (dent4 κ H e).R (dent4 κ' H e).R := disjoint_R4_R4 h

theorem disjoint_dent24 {κ κ' : ℝ} (h : κ < κ' - 1 / 16) :
    Disjoint (dent2 κ H e).R (dent4 κ' H e).R :=
  disjoint_of_fst (fun _ hz => (R2_fst hz).2) (fun _ hz => (R4_fst hz).1) h

theorem disjoint_dent42 {κ κ' : ℝ} (h : κ + e / 8 < κ' - e / 8 - 1 / 16) :
    Disjoint (dent4 κ H e).R (dent2 κ' H e).R :=
  disjoint_of_fst (fun _ hz => (R4_fst hz).2) (fun _ hz => (R2_fst hz).1) h

theorem dentsOK_one {k2 k4 : ℝ} (he : 0 < e) (he1 : e < 1 / 1000)
    (h2 : |k2 - (S + 3 / 2)| ≤ 1 / 1000) (h4 : |k4 - (S + 7 / 4)| ≤ 1 / 1000) :
    DentsOK H (S + 2, H) [dent2 k2 H e, dent4 k4 H e] := by
  rw [abs_le] at h2 h4
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl)
    · exact dent2_ok he (by linarith)
    · exact dent4_ok he (by linarith)
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, false_imp_iff, implies_true]
    exact disjoint_dent24 (by linarith)
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, dent2, dent4]
    linarith
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq, forall_eq', dent4]
    linarith

theorem dentsOK_two {a2 a4 k2 k4 : ℝ} (he : 0 < e) (he1 : e < 1 / 1000)
    (ha2 : |a2 - (S + 1 / 2)| ≤ 1 / 1000) (ha4 : |a4 - (S + 3 / 4)| ≤ 1 / 1000)
    (h2 : |k2 - (S + 3 / 2)| ≤ 1 / 1000) (h4 : |k4 - (S + 7 / 4)| ≤ 1 / 1000) :
    DentsOK H (S + 2, H) [dent2 a2 H e, dent4 a4 H e, dent2 k2 H e, dent4 k4 H e] := by
  rw [abs_le] at ha2 ha4 h2 h4
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl)
    · exact dent2_ok he (by linarith)
    · exact dent4_ok he (by linarith)
    · exact dent2_ok he (by linarith)
    · exact dent4_ok he (by linarith)
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    and_intros
    all_goals first
      | exact disjoint_dent22 (by linarith)
      | exact disjoint_dent44 (by linarith)
      | exact disjoint_dent24 (by linarith)
      | exact disjoint_dent42 (by linarith)
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, dent2, dent4]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq, forall_eq', dent4]
    linarith

theorem dentsOK_three {a2 a4 b2 b4 k2 k4 : ℝ} (he : 0 < e) (_he1 : e < 1 / 1000)
    (ha2 : |a2 - (S + 1 / 2)| ≤ 1 / 1000) (ha4 : |a4 - (S + 3 / 4)| ≤ 1 / 1000)
    (hb2 : |b2 - (S + 1 / 2)| ≤ 1 / 1000) (hb4 : |b4 - (S + 3 / 4)| ≤ 1 / 1000)
    (g2 : a2 + 100 * e ≤ b2) (g4 : a4 + 100 * e ≤ b4)
    (h2 : |k2 - (S + 3 / 2)| ≤ 1 / 1000) (h4 : |k4 - (S + 7 / 4)| ≤ 1 / 1000) :
    DentsOK H (S + 2, H) [dent2 a2 H e, dent2 b2 H e, dent4 a4 H e, dent4 b4 H e,
      dent2 k2 H e, dent4 k4 H e] := by
  rw [abs_le] at ha2 ha4 hb2 hb4 h2 h4
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact dent2_ok he (by linarith)
    · exact dent2_ok he (by linarith)
    · exact dent4_ok he (by linarith)
    · exact dent4_ok he (by linarith)
    · exact dent2_ok he (by linarith)
    · exact dent4_ok he (by linarith)
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    and_intros
    all_goals first
      | exact disjoint_dent22 (by linarith)
      | exact disjoint_dent44 (by linarith)
      | exact disjoint_dent24 (by linarith)
      | exact disjoint_dent42 (by linarith)
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, dent2, dent4]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq, forall_eq', dent4]
    linarith

end DentLists

/-! ### The floor chain -/

/-- The vertices of a dent chain are the end point or lie in a dent region. -/
theorem mem_dentChain {y₀ : ℝ} {e : Point} {ds : List Dent} (h : ∀ d ∈ ds, d.OK y₀) :
    ∀ x ∈ dentChain e ds, x = e ∨ ∃ d ∈ ds, x ∈ d.R := by
  induction ds with
  | nil => intro x hx; simp only [dentChain, List.mem_singleton] at hx; exact Or.inl hx
  | cons d ds ih =>
    intro x hx
    have hd := h d (by simp)
    simp only [dentChain, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact Or.inr ⟨_, by simp, hd.hAT (Geometry.left_mem_segment _ _)⟩
    · exact Or.inr ⟨_, by simp, hd.hAT (Geometry.right_mem_segment _ _)⟩
    · exact Or.inr ⟨_, by simp, hd.hTB (Geometry.right_mem_segment _ _)⟩
    · rcases ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) x hx with h1 | ⟨d', hd', h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', h2⟩

/-- The box of the floor slots. -/
def floorBox (S H : ℝ) : Set Point := {z | S + 1 / 4 ≤ z.1 ∧ z.1 ≤ S + 15 / 8 ∧ H - 1 / 4 ≤ z.2 ∧ z.2 ≤ H}

theorem dent2_R_box {S H e κ : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) (h1 : S + 2 / 5 ≤ κ)
    (h2 : κ ≤ S + 15 / 8) : (dent2 κ H e).R ⊆ floorBox S H := by
  intro z hz
  have := R2_fst hz
  obtain ⟨y1, y2, -, -⟩ := hz
  exact ⟨by linarith [this.1], by linarith [this.2], by linarith, y2⟩

theorem dent4_R_box {S H e κ : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) (h1 : S + 2 / 5 ≤ κ)
    (h2 : κ ≤ S + 7 / 4 + 1 / 100) : (dent4 κ H e).R ⊆ floorBox S H := by
  intro z hz
  have := R4_fst hz
  obtain ⟨y1, y2, -, -⟩ := hz
  exact ⟨by linarith [this.1], by linarith [this.2], y1, y2⟩

/-- The structure of the floor: a dent chain with explicit dents. -/
structure FloorData (I : Input) (ds : List Dent) : Prop where
  eq : I.chainBefore.map ratPoint =
    ((I.S : ℝ), (I.H : ℝ)) :: dentChain ((I.S : ℝ) + 2, (I.H : ℝ)) ds
  ok : DentsOK (I.H : ℝ) ((I.S : ℝ) + 2, (I.H : ℝ)) ds
  box : ∀ d ∈ ds, d.R ⊆ floorBox (I.S : ℝ) (I.H : ℝ)
  first : (I.S : ℝ) < firstX ((I.S : ℝ) + 2, (I.H : ℝ)) ds

theorem ratPoint_c1' : ratPoint (c1 I.S I.H) = ((I.S : ℝ) + 2, (I.H : ℝ)) := by
  simp [ratPoint, c1]

theorem ratPoint_c0' : ratPoint (c0 I.S I.H) = ((I.S : ℝ), (I.H : ℝ)) := by
  simp [ratPoint, c0]

section FloorChain

variable (hg : I.Good N)
include hg

theorem Good.eps_real : 0 < (I.ε : ℝ) ∧ (I.ε : ℝ) < 1 / 1000 := by
  obtain ⟨h1, h2⟩ := eps_small hg
  constructor
  · exact_mod_cast h1
  · have : (I.ε : ℝ) ≤ ((1 / 6400000 : ℚ) : ℝ) := by exact_mod_cast h2
    have h3 : ((1 / 6400000 : ℚ) : ℝ) < 1 / 1000 := by norm_num
    linarith

theorem Good.floorData : ∃ ds, FloorData I ds := by
  have hp := hg.np_pos
  have hp3 := hg.np_le
  have h0 : 0 < I.np := by omega
  obtain ⟨he, he1⟩ := hg.eps_real
  have k02 : |(I.kx 0 2 : ℝ) - ((I.S : ℝ) + 3 / 2)| ≤ 1 / 1000 := by
    have h := hg.kx_zero_two h0
    have : ((|I.kx 0 2 - (I.S + 3 / 2)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at this; exact this
  have k04 : |(I.kx 0 4 : ℝ) - ((I.S : ℝ) + 7 / 4)| ≤ 1 / 1000 := by
    have h := hg.kx_zero_four h0
    have : ((|I.kx 0 4 - (I.S + 7 / 4)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at this; exact this
  have k02' := k02; have k04' := k04
  rw [abs_le] at k02' k04'
  have b02 : (I.dentS2 0).R ⊆ floorBox (I.S : ℝ) (I.H : ℝ) :=
    dent2_R_box he he1 (by linarith) (by linarith)
  have b04 : (I.dentS4 0).R ⊆ floorBox (I.S : ℝ) (I.H : ℝ) :=
    dent4_R_box he he1 (by linarith) (by linarith)
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with hnp | hnp | hnp
  · refine ⟨[I.dentS2 0, I.dentS4 0], ?_, ?_, ?_, ?_⟩
    · rw [chainBefore, floor_eq_one hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · exact dentsOK_one he he1 k02 k04
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl) <;> assumption
    · simp only [firstX, dentS2, dent2]; linarith
  · have k12 : |(I.kx 1 2 : ℝ) - ((I.S : ℝ) + 1 / 2)| ≤ 1 / 1000 := by
      have h := hg.kx_two (k := 1) (by omega) le_rfl
      have : ((|I.kx 1 2 - (I.S + 1 / 2)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have k14 : |(I.kx 1 4 : ℝ) - ((I.S : ℝ) + 3 / 4)| ≤ 1 / 1000 := by
      have h := hg.kx_four (k := 1) (by omega) le_rfl
      have : ((|I.kx 1 4 - (I.S + 3 / 4)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have k12' := k12; have k14' := k14
    rw [abs_le] at k12' k14'
    refine ⟨[I.dentS2 1, I.dentS4 1, I.dentS2 0, I.dentS4 0], ?_, ?_, ?_, ?_⟩
    · rw [chainBefore, floor_eq_two hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · exact dentsOK_two he he1 k12 k14 k02 k04
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl)
      · exact dent2_R_box he he1 (by linarith) (by linarith)
      · exact dent4_R_box he he1 (by linarith) (by linarith)
      · assumption
      · assumption
    · simp only [firstX, dentS2, dent2]; linarith
  · have k12 : |(I.kx 1 2 : ℝ) - ((I.S : ℝ) + 1 / 2)| ≤ 1 / 1000 := by
      have h := hg.kx_two (k := 1) (by omega) le_rfl
      have : ((|I.kx 1 2 - (I.S + 1 / 2)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have k14 : |(I.kx 1 4 : ℝ) - ((I.S : ℝ) + 3 / 4)| ≤ 1 / 1000 := by
      have h := hg.kx_four (k := 1) (by omega) le_rfl
      have : ((|I.kx 1 4 - (I.S + 3 / 4)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have k22 : |(I.kx 2 2 : ℝ) - ((I.S : ℝ) + 1 / 2)| ≤ 1 / 1000 := by
      have h := hg.kx_two (k := 2) (by omega) (by norm_num)
      have : ((|I.kx 2 2 - (I.S + 1 / 2)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have k24 : |(I.kx 2 4 : ℝ) - ((I.S : ℝ) + 3 / 4)| ≤ 1 / 1000 := by
      have h := hg.kx_four (k := 2) (by omega) (by norm_num)
      have : ((|I.kx 2 4 - (I.S + 3 / 4)| : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have g2 : (I.kx 2 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx 1 2 : ℝ) := by
      exact_mod_cast hg.kx_two_succ (k := 1) le_rfl (by omega)
    have g4 : (I.kx 2 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx 1 4 : ℝ) := by
      exact_mod_cast hg.kx_four_succ (k := 1) le_rfl (by omega)
    have k12' := k12; have k14' := k14; have k22' := k22; have k24' := k24
    rw [abs_le] at k12' k14' k22' k24'
    refine ⟨[I.dentS2 2, I.dentS2 1, I.dentS4 2, I.dentS4 1, I.dentS2 0, I.dentS4 0],
      ?_, ?_, ?_, ?_⟩
    · rw [chainBefore, floor_eq_three hg hnp]
      simp [slot2_map, slot4_map, dentChain, ratPoint_c0', ratPoint_c1']
    · exact dentsOK_three he he1 k22 k24 k12 k14 g2 g4 k02 k04
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact dent2_R_box he he1 (by linarith) (by linarith)
      · exact dent2_R_box he he1 (by linarith) (by linarith)
      · exact dent4_R_box he he1 (by linarith) (by linarith)
      · exact dent4_R_box he he1 (by linarith) (by linarith)
      · assumption
      · assumption
    · simp only [firstX, dentS2, dent2]; linarith

/-- **The floor chain is a simple polyline.** -/
theorem Good.chainSimple_chainBefore : ChainSimple (I.chainBefore.map ratPoint) := by
  obtain ⟨ds, hd⟩ := hg.floorData
  rw [hd.eq]
  exact chainSimple_dents hd.ok rfl hd.first

/-- **The floor vertices** other than `c0`, `c1` lie in the slot box
`[S + 1/4, S + 15/8] × [H − 1/4, H]`. -/
theorem Good.floor_box : ∀ x ∈ I.floor.map ratPoint, x ∈ floorBox (I.S : ℝ) (I.H : ℝ) := by
  obtain ⟨ds, hd⟩ := hg.floorData
  have heq := hd.eq
  have hc : I.chainBefore.map ratPoint =
      ((I.S : ℝ), (I.H : ℝ)) :: (I.floor.map ratPoint ++ [((I.S : ℝ) + 2, (I.H : ℝ))]) := by
    simp [chainBefore, ratPoint_c0', ratPoint_c1']
  rw [hc] at heq
  have heq2 := (List.cons.inj heq).2
  intro x hx
  have hx' : x ∈ dentChain ((I.S : ℝ) + 2, (I.H : ℝ)) ds := by
    rw [← heq2]; exact List.mem_append_left _ hx
  rcases mem_dentChain hd.ok.ok x hx' with h1 | ⟨d, hd', h2⟩
  · -- `x = c1` is impossible: `c1` occurs once
    exfalso
    have hnd := (hg.chainSimple_chainBefore).nodup
    rw [hc] at hnd
    have := (List.nodup_cons.1 hnd).2
    rw [h1] at hx
    exact (List.nodup_append.1 this).2.2 _ hx _ (by simp) rfl
  · exact hd.box d hd' h2

end FloorChain

/-! ## The corridor polygon -/

/-- **The corridor polygon**: `c0, slots…, c1, d1, upper wall…, d0`, closed by the entrance. -/
def poly (I : Input) : Polygon := ⟨(I.chainBefore ++ I.chainAfter).map ratPoint⟩

/-- The upper-wall vertices other than `d1`, `d0`: in the window, or the guard `p_0`. -/
theorem Good.mem_upper (hg : I.Good N) {x : ℚ × ℚ} (hx : x ∈ I.upper) :
    InWindow I N x ∨ x = I.sgPt 0 := by
  simp only [upper, List.mem_flatMap, List.mem_range] at hx
  obtain ⟨k, hk, hx⟩ := hx
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [upperPair_zero] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (hg.feature_zp hk)
    · exact Or.inl (hg.feature_z1 hk)
    · exact Or.inl (hg.feature_n1 hk)
    · exact Or.inl (hg.feature_n0 hk)
    · exact Or.inl (hg.feature_z0 hk)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [upperPair_succ] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hg.feature_valley hk (by omega))
    · exact Or.inl (hg.feature_sgPt hk (by omega))
    · exact Or.inl (hg.feature_zp hk)
    · exact Or.inl (hg.feature_z1 hk)
    · exact Or.inl (hg.feature_n1 hk)
    · exact Or.inl (hg.feature_n0 hk)
    · exact Or.inl (hg.feature_z0 hk)

/-- The box of the upper wall: `(S, S + 2] × (H + ρ, H + 3/2]`. -/
def upperBox (S H : ℝ) : Set Point :=
  {z | S < z.1 ∧ z.1 ≤ S + 2 ∧ H + 3 / (2 * S) < z.2 ∧ z.2 ≤ H + 3 / 2}

theorem Good.window_box (hg : I.Good N) {x : ℚ × ℚ} (hx : InWindow I N x) :
    ratPoint x ∈ upperBox (I.S : ℝ) (I.H : ℝ) ∧ (ratPoint x).1 < (I.S : ℝ) + 2 := by
  obtain ⟨h1, h2⟩ := hx
  have hS := hg.S_pos
  have hS8 := hg.scale.S_ge
  have hN := hg.N_ge
  have hSe := hg.S_eq
  rw [abs_le] at h1 h2
  have ex := fst_eq_of_lX hg x
  have ey := snd_eq_of_lY hg x
  have q1 : I.S < x.1 := by
    rw [ex]
    have : -1 < I.lX x / (8 * I.S) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  have q2 : x.1 < I.S + 2 := by
    rw [ex]
    have : I.lX x / (8 * I.S) < 1 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have q3 : I.H + 3 / (2 * I.S) < x.2 := by
    rw [ey]
    have : -1 + 3 / (2 * I.S) < I.lY x / (8 * I.S) := by
      rw [show -1 + 3 / (2 * I.S) = (-(8 * I.S) + 12) / (8 * I.S) by field_simp; ring,
        div_lt_div_iff_of_pos_right (by positivity)]
      nlinarith
    linarith
  have q4 : x.2 ≤ I.H + 3 / 2 := by
    rw [ey]
    have : I.lY x / (8 * I.S) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [ratPoint_fst, ratPoint_snd]
  · exact_mod_cast q1
  · exact_mod_cast q2.le
  · have : ((I.H + 3 / (2 * I.S) : ℚ) : ℝ) < (x.2 : ℝ) := by exact_mod_cast q3
    push_cast at this; exact this
  · have : (x.2 : ℝ) ≤ ((I.H + 3 / 2 : ℚ) : ℝ) := by exact_mod_cast q4
    push_cast at this; exact this
  · exact_mod_cast q2

theorem Good.sgPt_zero_box (hg : I.Good N) :
    ratPoint (I.sgPt 0) ∈ upperBox (I.S : ℝ) (I.H : ℝ) ∧
      (ratPoint (I.sgPt 0)).1 = (I.S : ℝ) + 2 := by
  have h0 : 0 < I.np := by have := hg.np_pos; omega
  have h2 := hg.lY_sgPt_zero_abs h0
  have hS := hg.S_pos
  have hS8 := hg.scale.S_ge
  have hN := hg.N_ge
  have hSe := hg.S_eq
  rw [abs_le] at h2
  have ex : (I.sgPt 0).1 = I.S + 2 := by simp [sgPt, base_zero, onUmbra, d1]
  have ey := snd_eq_of_lY hg (I.sgPt 0)
  have q3 : I.H + 3 / (2 * I.S) < (I.sgPt 0).2 := by
    rw [ey]
    have : -1 + 3 / (2 * I.S) < I.lY (I.sgPt 0) / (8 * I.S) := by
      rw [show -1 + 3 / (2 * I.S) = (-(8 * I.S) + 12) / (8 * I.S) by field_simp; ring,
        div_lt_div_iff_of_pos_right (by positivity)]
      nlinarith
    linarith
  have q4 : (I.sgPt 0).2 ≤ I.H + 3 / 2 := by
    rw [ey]
    have : I.lY (I.sgPt 0) / (8 * I.S) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [ratPoint_fst, ratPoint_snd, ex]
  · push_cast; linarith
  · push_cast; linarith
  · have : ((I.H + 3 / (2 * I.S) : ℚ) : ℝ) < ((I.sgPt 0).2 : ℝ) := by exact_mod_cast q3
    push_cast at this; exact this
  · have : ((I.sgPt 0).2 : ℝ) ≤ ((I.H + 3 / 2 : ℚ) : ℝ) := by exact_mod_cast q4
    push_cast at this; exact this
  · push_cast; ring

/-- **The upper-wall vertices** other than `d1`, `d0` lie in `(S, S + 2] × (H + ρ, H + 3/2]`, and
only `p_0` is on the line `x = S + 2`. -/
theorem Good.upper_box (hg : I.Good N) : ∀ x ∈ I.upper.map ratPoint,
    x ∈ upperBox (I.S : ℝ) (I.H : ℝ) ∧ (x.1 < (I.S : ℝ) + 2 ∨ x = ratPoint (I.sgPt 0)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rcases hg.mem_upper hy with h | rfl
  · exact ⟨(hg.window_box h).1, Or.inl (hg.window_box h).2⟩
  · exact ⟨hg.sgPt_zero_box.1, Or.inr rfl⟩

end Input

end ArtGallery.Sec5.Corridor


end
