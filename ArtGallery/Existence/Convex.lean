module

public import ArtGallery.Jordan.Jordan
public import ArtGallery.Geometry.Triangle
public import ArtGallery.Existence.Rotate
public import ArtGallery.Geometry.Lex

/-!
# The lexicographically smallest vertex

Let `P` be a simple polygon whose vertex `0` is lexicographically smallest (smallest abscissa,
ties broken by smallest ordinate; the order is `ArtGallery.Programs.lexLE`).  Write
`u = P.vtx (P.n - 1)`, `v = P.vtx 0`, `w = P.vtx 1`.

* `exists_lexMin`, `rotate_lexMin`: every polygon has a lexicographically smallest vertex and
  rotating the vertex list puts it at index `0`.
* `not_mem_boundary_of_fst_lt`, `parity_eq_false_of_fst_lt`: a point strictly to the left of
  `v` is off the boundary and has crossing parity `false` (it is exterior).
* `det_ne_zero_of_lexMin`: the corner at `v` is strictly convex, `det u v w ≠ 0`.
* `boundary_near_vtx`: in a small ball around a vertex the boundary consists of the two
  incident edges.
* `sector_subset_interior`: for `σ = ±1` with `0 < σ * det u v w`, every point of a small ball
  around `v` with `0 < σ * det u v x` and `0 < σ * det v w x` (the open convex sector at `v`)
  lies in `P.filled \ P.boundary`.

Provenance: adapted from `Chazelle/Existence/Convex.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`; the lexicographic order is imported from `ArtGallery.Geometry.Lex`.
-/

namespace ArtGallery.Existence
open ArtGallery.Programs (lexLE lexLT)

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan

open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp det_cyclic det_cyclic_right det_swap12
  det_swap13 det_swap23 det_self_left det_self_right det_self_outer exists_lerp_of_det_eq_zero
  det_eq_zero_of_mem_segment continuous_det_right lerp_zero lerp_one lerp_injective
  lerp_mem_segment point_ext point_ext_iff mem_segment_iff_lerp ne_of_det_ne_zero add_fst add_snd
  smul_fst smul_snd sub_fst sub_snd)

/-! ### The lexicographic order and the smallest vertex -/

/-- `ArtGallery.Programs.lexLE` is the order of `Lex (ℝ × ℝ)`. -/
theorem lexLE_iff_toLex_le {p q : Point} : lexLE p q ↔ toLex p ≤ toLex q := by
  rw [Prod.Lex.toLex_le_toLex]; rfl

/-- A lexicographically smaller point has a smaller or equal abscissa. -/
theorem fst_le_of_lexLE {p q : Point} (h : lexLE p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- A lexicographically smaller point with the same abscissa has a smaller or equal ordinate. -/
theorem snd_le_of_lexLE_of_fst_eq {p q : Point} (h : lexLE p q) (h1 : p.1 = q.1) : p.2 ≤ q.2 := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h1 h.ne
  · exact h

/-- Every polygon with at least one vertex has a lexicographically smallest vertex. -/
theorem exists_lexMin (P : Polygon) (hn : 0 < P.n) :
    ∃ m, m < P.n ∧ ∀ i, i < P.n → lexLE (P.vtx m) (P.vtx i) := by
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.range P.n)
    (fun i => toLex (P.vtx i)) ⟨0, Finset.mem_range.2 hn⟩
  exact ⟨m, Finset.mem_range.1 hm,
    fun i hi => lexLE_iff_toLex_le.2 (hmin i (Finset.mem_range.2 hi))⟩

/-- Rotating the vertex list to start at a lexicographically smallest vertex makes vertex `0`
lexicographically smallest. -/
theorem rotate_lexMin (P : Polygon) {m : ℕ} (hm : m < P.n)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx m) (P.vtx i)) :
    ∀ i, i < P.n → lexLE ((P.rotate m).vtx 0) ((P.rotate m).vtx i) := by
  intro i hi
  rw [vtx_rotate P m (by omega), vtx_rotate P m hi, Nat.add_zero, Nat.mod_eq_of_lt hm]
  exact hmin _ (Nat.mod_lt _ (by omega))

/-! ### Index bookkeeping at vertex `0` -/

/-- The successor of vertex `0` is vertex `1`. -/
theorem succ_zero_mod (P : Polygon) (hn : 2 ≤ P.n) : (0 + 1) % P.n = 1 :=
  Nat.mod_eq_of_lt (by omega)

/-- The successor of vertex `n - 1` is vertex `0`. -/
theorem succ_last_mod (P : Polygon) (hn : 1 ≤ P.n) : (P.n - 1 + 1) % P.n = 0 := by
  rw [Nat.sub_add_cancel hn, Nat.mod_self]

/-- The edge entering vertex `0` is edge `n - 1`. -/
theorem prevIdx_zero (P : Polygon) (hn : 1 ≤ P.n) : prevIdx P 0 = P.n - 1 := by
  rw [prevIdx_eq P (by omega)]; simp

/-- Edge `0` is the segment from vertex `0` to vertex `1`. -/
theorem edge_zero (P : Polygon) (hn : 2 ≤ P.n) :
    P.edge 0 = ArtGallery.segment (P.vtx 0) (P.vtx 1) := by
  unfold Polygon.edge; rw [succ_zero_mod P hn]

/-- Edge `n - 1` is the segment from vertex `n - 1` to vertex `0`. -/
theorem edge_last (P : Polygon) (hn : 1 ≤ P.n) :
    P.edge (P.n - 1) = ArtGallery.segment (P.vtx (P.n - 1)) (P.vtx 0) := by
  unfold Polygon.edge; rw [succ_last_mod P hn]

/-- The two edges at vertex `0` of a simple polygon meet only in vertex `0`. -/
theorem edges_at_zero_meet {P : Polygon} (hP : P.Simple) :
    ArtGallery.segment (P.vtx (P.n - 1)) (P.vtx 0) ∩ ArtGallery.segment (P.vtx 0) (P.vtx 1) ⊆
      {P.vtx 0} := by
  have hn := simple_three_le hP
  intro p hp
  have hmem : p ∈ P.edge (P.n - 1) ∩ P.edge 0 := by
    rw [edge_last P (by omega), edge_zero P (by omega)]; exact hp
  rw [simple_edge_inter hP (by omega) (by omega) (by omega)] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [succ_last_mod P (by omega)] at h1
  rw [succ_zero_mod P (by omega)] at h2
  rcases h1 with rfl | rfl
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (simple_vtx_inj hP (by omega) (by omega) h2) (by omega)
  · rfl

/-! ### Points to the left of the smallest vertex are exterior -/

/-- No boundary point lies strictly to the left of a lexicographically smallest vertex. -/
theorem not_mem_boundary_of_fst_lt (P : Polygon)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) {z : Point} (hz : z.1 < (P.vtx 0).1) :
    z ∉ P.boundary := by
  rintro ⟨i, hi, t, ht0, ht1, rfl⟩
  have h1 := fst_le_of_lexLE (hmin i hi)
  have h2 := fst_le_of_lexLE (hmin _ (Nat.mod_lt (i + 1) (by omega)))
  simp only at hz
  nlinarith

/-- A point strictly to the left of a lexicographically smallest vertex has parity `false`. -/
theorem parity_eq_false_of_fst_lt (P : Polygon)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) {z : Point} (hz : z.1 < (P.vtx 0).1) :
    parity P z = false := by
  rw [parity_eq_false_iff]
  unfold crossSum
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < P.n := Finset.mem_range.1 hi
  apply crossInd_of_not_crosses
  exact not_crosses_of_lt (hz.trans_le (fst_le_of_lexLE (hmin i hi')))
    (hz.trans_le (fst_le_of_lexLE (hmin _ (Nat.mod_lt (i + 1) (by omega)))))

/-! ### Strict convexity at the smallest vertex -/

/-- **The corner at a lexicographically smallest vertex is strictly convex**: for a simple
polygon whose vertex `0` is lexicographically smallest, `det (vtx (n-1)) (vtx 0) (vtx 1) ≠ 0`. -/
theorem det_ne_zero_of_lexMin {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) :
    det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0 := by
  intro h
  have hn := simple_three_le hP
  have hav : P.vtx (P.n - 1) ≠ P.vtx 0 := simple_vtx_ne hP (by omega) (by omega) (by omega)
  have hvb : P.vtx 0 ≠ P.vtx 1 := simple_vtx_ne hP (by omega) (by omega) (by omega)
  have hdir := dir_pos_of_collinear hav hvb (edges_at_zero_meet hP) h
  have hu := hmin (P.n - 1) (by omega)
  have hw := hmin 1 (by omega)
  set u := P.vtx (P.n - 1)
  set v := P.vtx 0
  set w := P.vtx 1
  have hu1 : v.1 ≤ u.1 := fst_le_of_lexLE hu
  have hw1 : v.1 ≤ w.1 := fst_le_of_lexLE hw
  unfold det at h
  rcases hu1.lt_or_eq with hu1 | hu1 <;> rcases hw1.lt_or_eq with hw1 | hw1
  · -- both neighbours strictly to the right: the dot product is negative
    have hb : 0 < w.1 - v.1 := sub_pos.2 hw1
    have hkey : (w.1 - v.1) * ((v.1 - u.1) * (w.1 - v.1) + (v.2 - u.2) * (w.2 - v.2)) =
        (v.1 - u.1) * ((w.1 - v.1) ^ 2 + (w.2 - v.2) ^ 2) := by
      linear_combination (-(w.2 - v.2)) * h
    have hneg : (v.1 - u.1) * ((w.1 - v.1) ^ 2 + (w.2 - v.2) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by positivity)
    nlinarith [mul_pos hb hdir]
  · -- `w` on the vertical line through `v`, above it; `u` strictly to the right
    have hw2 : v.2 ≤ w.2 := snd_le_of_lexLE_of_fst_eq hw hw1
    have hw2' : v.2 < w.2 := by
      rcases hw2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (point_ext hw1 h') hvb
    have : (v.1 - u.1) * (w.2 - v.2) = 0 := by rw [hw1] at h ⊢; linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · -- `u` on the vertical line through `v`, above it; `w` strictly to the right
    have hu2 : v.2 ≤ u.2 := snd_le_of_lexLE_of_fst_eq hu hu1
    have hu2' : v.2 < u.2 := by
      rcases hu2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (point_ext hu1 h').symm hav
    have : (w.1 - v.1) * (v.2 - u.2) = 0 := by rw [← hu1] at h; linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · -- all three on a vertical line
    have hu2 : v.2 ≤ u.2 := snd_le_of_lexLE_of_fst_eq hu hu1
    have hw2 : v.2 ≤ w.2 := snd_le_of_lexLE_of_fst_eq hw hw1
    rw [hu1] at hdir
    rw [← hw1] at hdir
    nlinarith [mul_nonneg (sub_nonneg.2 hu2) (sub_nonneg.2 hw2)]

/-! ### The boundary near a vertex -/

/-- Around a vertex of a simple polygon there is a ball in which the boundary consists of the
two incident edges. -/
theorem boundary_near_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) :
    ∃ r > 0, ∀ x ∈ ball (P.vtx i) r, x ∈ P.boundary →
      x ∈ ArtGallery.segment (P.vtx (prevIdx P i)) (P.vtx i) ∨
        x ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) := by
  set j := prevIdx P i with hj
  have hother : ∀ k ∈ ((Finset.range P.n).erase i).erase j, P.vtx i ∉ P.edge k := by
    intro k hk hmem
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases (simple_vtx_mem_edge_iff hP hi hk.2.2).1 hmem with h | h
    · exact hk.2.1 h
    · exact hk.1 h
  obtain ⟨r, hr, hball⟩ := exists_ball_disjoint_edges P _ hother
  refine ⟨r, hr, ?_⟩
  rintro x hx ⟨k, hk, hxk⟩
  by_cases hki : k = i
  · subst hki; exact Or.inr hxk
  · by_cases hkj : k = j
    · subst hkj
      left
      rw [← edge_prevIdx P hi]
      exact hxk
    · exact absurd hxk (hball x hx k (by simp [Finset.mem_erase, hki, hkj, hk]))

/-! ### The convex sector at the smallest vertex is interior -/

/-- **The open sector at a lexicographically smallest vertex is interior.**  Let `P` be simple
with vertex `0` lexicographically smallest, `u = vtx (n-1)`, `v = vtx 0`, `w = vtx 1`, and let
`σ = ±1` with `0 < σ * det u v w`.  Then there is `r > 0` such that every point `x` of the ball
of radius `r` around `v` with `0 < σ * det u v x` and `0 < σ * det v w x` lies in the interior
region `P.filled \ P.boundary`. -/
theorem sector_subset_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE (P.vtx 0) (P.vtx i)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1)) :
    ∃ r > 0, ∀ x ∈ ball (P.vtx 0) r,
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) x → 0 < σ * det (P.vtx 0) (P.vtx 1) x →
        x ∈ P.filled \ P.boundary := by
  have hn := simple_three_le hP
  have h0 : 0 < P.n := by omega
  have h1n : (0 + 1) % P.n = 1 := succ_zero_mod P (by omega)
  have hprev : prevIdx P 0 = P.n - 1 := prevIdx_zero P (by omega)
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, hball⟩ := boundary_near_vtx hP h0
  rw [hprev, h1n] at hball
  set u := P.vtx (P.n - 1) with hu
  set v := P.vtx 0 with hv
  set w := P.vtx 1 with hw
  have hdet : det u v w ≠ 0 := by
    intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hvw : v ≠ w := (ne_of_det_ne_zero hdet).2.1
  have hsq := sqLen_pos hvw
  -- the open convex sector and the half-disk on the far side of edge `v w`
  set Splus : Set Point := ball v r ∩ ({x | 0 < σ * det u v x} ∩ {x | 0 < σ * det v w x})
    with hSplus
  set D : Set Point := ball v r ∩ {x | 0 < (-σ) * det v w x} with hD
  have hSplus_conn : IsPreconnected Splus :=
    ((convex_ball v r).inter ((convex_det_pos u v σ).inter (convex_det_pos v w σ))).isPreconnected
  have hSplus_compl : Splus ⊆ P.boundaryᶜ := by
    rintro x ⟨hxb, hx1, hx2⟩ hxB
    have hx1' : 0 < σ * det u v x := hx1
    have hx2' : 0 < σ * det v w x := hx2
    rcases hball x hxb hxB with h | h
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx1'; exact lt_irrefl _ hx1'
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx2'; exact lt_irrefl _ hx2'
  have hD_conn : IsPreconnected D :=
    ((convex_ball v r).inter (convex_det_pos v w (-σ))).isPreconnected
  have hD_compl : D ⊆ P.boundaryᶜ := by
    rintro x ⟨hxb, hx⟩ hxB
    have hx' : 0 < (-σ) * det v w x := hx
    rcases hball x hxb hxB with h | h
    · obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 h
      rw [det_lerp, det_self_outer, det_cyclic] at hx'
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) hpos.le]
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx'; exact lt_irrefl _ hx'
  -- the reflex direction at `v` points strictly to the left
  have hfst : 0 < (u.1 - v.1) + (w.1 - v.1) := by
    have h1 : v.1 ≤ u.1 := fst_le_of_lexLE (hmin _ (by omega))
    have h2 : v.1 ≤ w.1 := fst_le_of_lexLE (hmin _ (by omega))
    by_contra hle
    have hu1 : u.1 = v.1 := by linarith
    have hw1 : w.1 = v.1 := by linarith
    apply hdet
    unfold det; rw [hu1, hw1]; ring
  have hqfst : ∀ ε : ℝ, 0 < ε → (v + ε • ((v - u) - (w - v))).1 < v.1 := by
    intro ε hε
    simp only [add_fst, smul_fst, sub_fst]
    nlinarith
  have htq : Tendsto (fun ε : ℝ => v + ε • ((v - u) - (w - v))) (𝓝[>] 0) (𝓝 v) := by
    have hc : Continuous fun ε : ℝ => v + ε • ((v - u) - (w - v)) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεb, hε0⟩ :=
    ((htq.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).and self_mem_nhdsWithin).exists
  have hε0' : (0 : ℝ) < ε := hε0
  have hqD : v + ε • ((v - u) - (w - v)) ∈ D := by
    refine ⟨hεb, ?_⟩
    show 0 < (-σ) * det v w (v + ε • ((v - u) - (w - v)))
    rw [(det_reflex_point u v w ε).2]
    nlinarith [mul_pos hε0' hpos]
  have hqpar : parity P (v + ε • ((v - u) - (w - v))) = false :=
    parity_eq_false_of_fst_lt P hmin (hqfst ε hε0')
  have hDpar : ∀ x ∈ D, parity P x = false := fun x hx =>
    (parity_eq_of_isPreconnected P hD_conn hD_compl hx hqD).trans hqpar
  -- a point of the open edge `v w` close to `v`
  have hW1 : IsOpen (ball v r ∩ {x | 0 < σ * det u v x}) :=
    isOpen_ball.inter (isOpen_det_pos u v σ)
  have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      lerp v w t ∈ ball v r ∩ {x | 0 < σ * det u v x} ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_zero v w).eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t htb ht
    refine ⟨⟨htb, ?_⟩, ht⟩
    show 0 < σ * det u v (lerp v w t)
    rw [det_lerp, det_self_right]
    nlinarith [mul_pos ht.1 hpos]
  obtain ⟨t, htW, ht01⟩ := ht_ev.exists
  -- offsets of that point to both sides
  obtain ⟨δ, hplus, hminus, hsides, hδ0⟩ :=
    ((eventually_offset_mem σ hW1 htW).and ((eventually_offset_mem (-σ) isOpen_ball htW.1).and
      ((edge_sides hP h0 ht01).and self_mem_nhdsWithin))).exists
  have hδ0' : (0 : ℝ) < δ := hδ0
  unfold leftPoint rightPoint at hsides
  rw [h1n] at hsides
  have hxplus : offset v w t (σ * δ) ∈ Splus := by
    refine ⟨hplus.1, hplus.2, ?_⟩
    show 0 < σ * det v w (offset v w t (σ * δ))
    rw [det_offset, show σ * (σ * δ * sqLen v w) = (σ * σ) * (δ * sqLen v w) by ring, hσ2,
      one_mul]
    exact mul_pos hδ0' hsq
  have hxminus : offset v w t (-σ * δ) ∈ D := by
    refine ⟨hminus, ?_⟩
    show 0 < (-σ) * det v w (offset v w t (-σ * δ))
    rw [det_offset, show (-σ) * (-σ * δ * sqLen v w) = (σ * σ) * (δ * sqLen v w) by ring, hσ2,
      one_mul]
    exact mul_pos hδ0' hsq
  have hminus_not : offset v w t (-σ * δ) ∉ P.filled := by
    intro hf
    have := (mem_filled_iff hP (hD_compl hxminus)).1 hf
    rw [hDpar _ hxminus] at this
    exact Bool.false_ne_true this
  have hplus_filled : offset v w t (σ * δ) ∈ P.filled := by
    rcases hσ with rfl | rfl
    · rw [one_mul]
      rw [neg_one_mul] at hminus_not
      exact hsides.2 hminus_not
    · rw [neg_one_mul]
      rw [neg_neg, one_mul] at hminus_not
      by_contra hcon
      exact hminus_not (hsides.2 hcon)
  have hplus_par : parity P (offset v w t (σ * δ)) = true :=
    (mem_filled_iff hP (hSplus_compl hxplus)).1 hplus_filled
  refine ⟨r, hr, fun x hxb hx1 hx2 => ?_⟩
  have hxS : x ∈ Splus := ⟨hxb, hx1, hx2⟩
  have hxB : x ∉ P.boundary := hSplus_compl hxS
  refine ⟨(mem_filled_iff hP hxB).2 ?_, hxB⟩
  rw [parity_eq_of_isPreconnected P hSplus_conn hSplus_compl hxS hxplus, hplus_par]

end

end ArtGallery.Existence
