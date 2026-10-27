module

public import ArtGallery.Stade.LowerCopy
public import ArtGallery.Stade.Generic.Glue

/-!
# Generic tools for the region decomposition (proof plan L2.3)

* `piece_aff_nonneg` (**hull lemma**): an affine function that is nonnegative at the vertices of a
  convex piece is nonnegative on the piece (a ray in the direction of steepest descent leaves the
  piece through a side; `cyc_mono` rules out pieces without such a side);
* `mem_interior_union_horiz` (**two half-discs on a horizontal line**): a point in the relative
  interior of a horizontal side of `K` and of a horizontal side of `K'` traversed in the opposite
  direction is an interior point of `piece K ∪ piece K'`;
* `filled_eq_of_sides` (**exact region**): a finite family of pieces of the region covering the
  boundary, such that every point of every side is on the boundary or interior to the union, has
  the region as its union;
* `segment_subset_chainSet`, `chainSet_subset_boundary`, `boundary_subset_chainSet`: chains and
  the boundary of a polygon given by its vertex list;
* `comb_floor_cover`: the floor line of a comb is covered by the comb chain and the open mouths
  of its features.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric ArtGallery.Stade.Chain
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

/-! ### The hull lemma -/

/-- A cyclically monotone sequence is constant. -/
theorem cyc_mono {n : ℕ} (hn : 0 < n) {h : ℕ → ℝ} (hm : ∀ j < n, h j ≤ h ((j + 1) % n)) :
    ∀ j < n, h j = h 0 := by
  have step : ∀ i j, i ≤ j → j < n → h i ≤ h j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ j hij ih =>
      have := hm j (by omega)
      rw [Nat.mod_eq_of_lt hj] at this
      exact (ih (by omega)).trans this
  intro j hj
  have h1 := step 0 j (Nat.zero_le _) hj
  have h2 := step j (n - 1) (by omega) (by omega)
  have h3 := hm (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, Nat.mod_self] at h3
  linarith

/-- A cyclically strictly increasing sequence does not exist. -/
theorem cyc_strict_false {n : ℕ} (hn : 0 < n) {h : ℕ → ℝ}
    (hm : ∀ j < n, h j < h ((j + 1) % n)) : False := by
  have hc := cyc_mono hn (fun j hj => (hm j hj).le)
  have h0 := hm 0 hn
  rw [hc ((0 + 1) % n) (Nat.mod_lt _ hn)] at h0
  exact lt_irrefl _ h0

/-- An affine function nonnegative at both ends of a segment is nonnegative on it. -/
theorem aff_nonneg_seg {a b z : Point} (hz : z ∈ segment a b) {α β γ : ℝ}
    (ha : 0 ≤ α * a.1 + β * a.2 + γ) (hb : 0 ≤ α * b.1 + β * b.2 + γ) :
    0 ≤ α * z.1 + β * z.2 + γ := by
  obtain ⟨t, h0, h1, rfl⟩ := hz
  simp only
  nlinarith [mul_nonneg h0 hb, mul_nonneg (sub_nonneg.2 h1) ha]

/-- **Hull lemma.** An affine function that is nonnegative at all vertices of a convex piece is
nonnegative on the piece. -/
theorem piece_aff_nonneg {K : Polygon} (hK : IsPiece K) (hn : 0 < K.n) {α β γ : ℝ}
    (hv : ∀ k < K.n, 0 ≤ α * (K.vtx k).1 + β * (K.vtx k).2 + γ) {y : Point}
    (hy : y ∈ piece K) : 0 ≤ α * y.1 + β * y.2 + γ := by
  by_contra hneg
  push Not at hneg
  have hd : 0 < α ^ 2 + β ^ 2 := by
    rcases eq_or_ne α 0 with ha | ha
    · rcases eq_or_ne β 0 with hb | hb
      · exfalso
        have := hv 0 hn
        rw [ha, hb] at this hneg
        simp at this hneg
        linarith
      · have := pow_pos (abs_pos.2 hb) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 ha) 2; rw [sq_abs] at this; positivity
  set n := K.n with hn_def
  set v := K.vtx with hv_def
  -- slope of the constraint of side `j` along the direction `(−α, −β)`
  set σ : ℕ → ℝ := fun j =>
    ((v ((j + 1) % n)).1 * (-β) - (v ((j + 1) % n)).2 * (-α)) - ((v j).1 * (-β) - (v j).2 * (-α))
    with hσ
  have hdet : ∀ j (s : ℝ), det (v j) (v ((j + 1) % n)) (y.1 + s * (-α), y.2 + s * (-β)) =
      det (v j) (v ((j + 1) % n)) y + s * σ j := by
    intro j s; simp only [det, hσ]; ring
  -- some side has a negative slope
  have hslope : ∃ j < n, σ j < 0 := by
    by_contra hall
    push Not at hall
    set hf : ℕ → ℝ := fun j => (v j).1 * (-β) - (v j).2 * (-α) with hhf
    have hmono := cyc_mono hn (h := hf) (fun j hj => by
      have := hall j hj; rw [hσ] at this; rw [hhf]; dsimp only at this ⊢; linarith)
    obtain ⟨o, ho⟩ := hK.center
    set g : ℕ → ℝ := fun j => (v j).1 * (-α) + (v j).2 * (-β) with hg
    have key : ∀ j < n, (g ((j + 1) % n) - g j) * (hf j - (o.1 * (-β) - o.2 * (-α))) =
        (α ^ 2 + β ^ 2) * det (v j) (v ((j + 1) % n)) o := by
      intro j hj
      have e : hf ((j + 1) % n) = hf j := by
        rw [hmono j hj, hmono _ (Nat.mod_lt _ hn)]
      simp only [hhf, hg, det] at e ⊢
      linear_combination (-((o.1 - (v j).1) * (-α) + (o.2 - (v j).2) * (-β))) * e
    set C := hf 0 - (o.1 * (-β) - o.2 * (-α))
    have hpos : ∀ j < n, 0 < (g ((j + 1) % n) - g j) * C := by
      intro j hj
      have := key j hj
      rw [hmono j hj] at this
      rw [this]
      exact mul_pos hd (ho j hj)
    rcases lt_trichotomy C 0 with hC | hC | hC
    · exact cyc_strict_false hn (h := fun j => -g j) (fun j hj => by
        have := hpos j hj
        show -g j < -g ((j + 1) % n)
        nlinarith)
    · have := hpos 0 hn; rw [hC, mul_zero] at this; exact lt_irrefl _ this
    · exact cyc_strict_false hn (h := g) (fun j hj => by
        have := hpos j hj
        by_contra h'; push Not at h'
        nlinarith)
  classical
  set J := (Finset.range n).filter (fun j => σ j < 0)
  have hJ : J.Nonempty := by
    obtain ⟨j, hj, hσj⟩ := hslope
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hσj⟩⟩
  set sj : ℕ → ℝ := fun j => det (v j) (v ((j + 1) % n)) y / (-σ j)
  obtain ⟨j₀, hj₀J, hj₀min⟩ := J.exists_min_image sj hJ
  rw [Finset.mem_filter, Finset.mem_range] at hj₀J
  obtain ⟨hj₀n, hσ₀⟩ := hj₀J
  set s := sj j₀
  have hs0 : 0 ≤ s := div_nonneg (hy j₀ hj₀n) (by linarith)
  set z : Point := (y.1 + s * (-α), y.2 + s * (-β))
  have hz : z ∈ piece K := by
    intro j hj
    show 0 ≤ det (v j) (v ((j + 1) % n)) z
    rw [hdet]
    by_cases hσj : σ j < 0
    · have hle : s ≤ sj j := hj₀min j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hσj⟩)
      have : s * (-σ j) ≤ det (v j) (v ((j + 1) % n)) y := by
        have h' := (le_div_iff₀ (by linarith : (0 : ℝ) < -σ j)).1 hle
        exact h'
      linarith
    · push Not at hσj
      nlinarith [hy j hj, mul_nonneg hs0 hσj]
  have hz0 : det (v j₀) (v ((j₀ + 1) % n)) z = 0 := by
    show det (v j₀) (v ((j₀ + 1) % n)) (y.1 + s * (-α), y.2 + s * (-β)) = 0
    rw [hdet]
    have : s * (-σ j₀) = det (v j₀) (v ((j₀ + 1) % n)) y := div_mul_cancel₀ _ (by linarith)
    linarith
  obtain ⟨k, hk, hzk⟩ := mem_edge_of_det_eq_zero hK hz hj₀n hz0
  have hfz := aff_nonneg_seg hzk (hv k hk) (hv _ (Nat.mod_lt _ hn))
  have : α * z.1 + β * z.2 + γ = α * y.1 + β * y.2 + γ - s * (α ^ 2 + β ^ 2) := by
    simp only [z]; ring
  nlinarith [mul_nonneg hs0 hd.le]

/-- The interior of a set contained in a closed half-plane `0 ≤ α x + β y + γ` (with
`(α, β) ≠ 0`) lies in the open half-plane. -/
theorem pos_of_mem_interior_aff {S : Set Point} {α β γ : ℝ} (hαβ : 0 < α ^ 2 + β ^ 2)
    (hS : ∀ x ∈ S, 0 ≤ α * x.1 + β * x.2 + γ) {x : Point} (hx : x ∈ interior S) :
    0 < α * x.1 + β * x.2 + γ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set δ := ε / (2 * (|α| + |β| + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hmem : (x.1 - δ * α, x.2 - δ * β) ∈ S := by
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hδ0]
    refine max_lt ?_ ?_
    · have : δ * |α| < ε := by
        rw [hδ]; rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg α,
          abs_nonneg β]
      exact this
    · have : δ * |β| < ε := by
        rw [hδ]; rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg α,
          abs_nonneg β]
      exact this
  have := hS _ hmem
  simp only at this
  nlinarith [mul_pos hδ0 hαβ]

/-- **Separation by an affine function.** If an affine function is nonnegative at the vertices of
a piece and nonpositive at both ends of a segment, the segment misses the interior of the
piece. -/
theorem disjoint_interior_of_aff {K : Polygon} (hK : IsPiece K) (hn : 0 < K.n) {α β γ : ℝ}
    (hαβ : 0 < α ^ 2 + β ^ 2) (hv : ∀ k < K.n, 0 ≤ α * (K.vtx k).1 + β * (K.vtx k).2 + γ)
    {a b : Point} (ha : α * a.1 + β * a.2 + γ ≤ 0) (hb : α * b.1 + β * b.2 + γ ≤ 0) :
    Disjoint (interior (piece K)) (segment a b) := by
  rw [Set.disjoint_left]
  intro x hx hxs
  have h1 := pos_of_mem_interior_aff hαβ (fun y hy => piece_aff_nonneg hK hn hv hy) hx
  have h2 := aff_nonneg_seg (α := -α) (β := -β) (γ := -γ) hxs (by linarith) (by linarith)
  linarith

/-! ### Two half-discs on a horizontal line -/

/-- A point of the relative interior of a horizontal side of `K` and of a horizontal side of `K'`
traversed in the opposite direction is an interior point of `piece K ∪ piece K'`. -/
theorem mem_interior_union_horiz {K K' : Polygon} (hK : IsPiece K) (hK' : IsPiece K') {j j' : ℕ}
    (hj : j < K.n) (hj' : j' < K'.n) {Y a b a' b' x : ℝ} (h1 : K.vtx j = (a, Y))
    (h2 : K.vtx ((j + 1) % K.n) = (b, Y)) (h3 : K'.vtx j' = (a', Y))
    (h4 : K'.vtx ((j' + 1) % K'.n) = (b', Y)) (hx1 : a < x) (hx2 : x < b) (hx3 : b' < x)
    (hx4 : x < a') : ((x, Y) : Point) ∈ interior (piece K ∪ piece K') := by
  have ht0 : 0 < (x - a) / (b - a) := div_pos (by linarith) (by linarith)
  have ht1 : (x - a) / (b - a) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have ht0' : 0 < (a' - x) / (a' - b') := div_pos (by linarith) (by linarith)
  have ht1' : (a' - x) / (a' - b') < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨r₁, hr₁, k₁⟩ := near_open_side hK hj ht0 ht1
  obtain ⟨r₂, hr₂, k₂⟩ := near_open_side hK' hj' ht0' ht1'
  have hba : b - a ≠ 0 := ne_of_gt (by linarith)
  have hba' : a' - b' ≠ 0 := ne_of_gt (by linarith)
  have e1 : lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) ((x - a) / (b - a)) = (x, Y) := by
    rw [h1, h2]; simp only [lerp]; ext
    · simp only; field_simp; ring
    · simp
  have e2 : lerp (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) ((a' - x) / (a' - b')) = (x, Y) := by
    rw [h3, h4]; simp only [lerp]; ext
    · simp only; field_simp; ring
    · simp
  rw [e1] at k₁
  rw [e2] at k₂
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [mem_ball] at hz
  rcases le_total Y z.2 with h | h
  · refine Or.inl (k₁ z (lt_of_lt_of_le hz (min_le_left _ _)) ?_)
    rw [h1, h2]; simp only [det]; nlinarith
  · refine Or.inr (k₂ z (lt_of_lt_of_le hz (min_le_right _ _)) ?_)
    rw [h3, h4]; simp only [det]; nlinarith

/-! ### The exact region from sides -/

/-- **Exact region (L2.3).** Let `S` be a finite nonempty list of pieces of the region of the
simple polygon `P` covering the boundary, such that every point of every side of every piece lies
on the boundary or in the interior of the union of the pieces.  Then the region is the union. -/
theorem filled_eq_of_sides {P : Polygon} (hP : P.Simple) (S : List Polygon)
    (hpc : ∀ K ∈ S, IsPiece K) (hsub : ∀ K ∈ S, piece K ⊆ P.filled)
    (hbd : P.boundary ⊆ pieceUnion {K | K ∈ S})
    (hside : ∀ K ∈ S, ∀ j < K.n, ∀ y ∈ K.edge j,
      y ∈ P.boundary ∨ y ∈ interior (pieceUnion {K | K ∈ S}))
    (hne : S ≠ []) : P.filled = pieceUnion {K | K ∈ S} := by
  have hfin : ({K | K ∈ S} : Set Polygon).Finite := S.finite_toSet
  have hU : pieceUnion {K | K ∈ S} ⊆ P.filled := by
    intro x hx
    obtain ⟨K, hKS, hxK⟩ := mem_pieceUnion.1 hx
    exact hsub K hKS hxK
  have hne' : (pieceUnion {K | K ∈ S} \ P.boundary).Nonempty := by
    obtain ⟨K, hKS⟩ := List.exists_mem_of_ne_nil S hne
    obtain ⟨o, ho⟩ := center_mem_interior (hpc K hKS)
    have h1 : o ∈ interior P.filled := interior_mono (hsub K hKS) ho
    rw [Jordan.interior_filled hP] at h1
    exact ⟨o, piece_subset_pieceUnion (S := {K | K ∈ S}) hKS (interior_subset ho), h1.2⟩
  refine Polygon.filled_eq_of_frontier_subset hP (isClosed_pieceUnion hfin) hbd ?_ hU hne'
  intro y hy
  by_contra hyb
  have hyU : y ∈ pieceUnion {K | K ∈ S} := (isClosed_pieceUnion hfin).frontier_subset hy
  obtain ⟨K, hKS, hyK⟩ := mem_pieceUnion.1 hyU
  have hnint : y ∉ interior (pieceUnion {K | K ∈ S}) := hy.2
  by_cases hyi : y ∈ interior (piece K)
  · exact hnint (interior_mono (piece_subset_pieceUnion (S := {K | K ∈ S}) hKS) hyi)
  have hyfr : y ∈ frontier (piece K) := ⟨subset_closure hyK, hyi⟩
  obtain ⟨k, hk, hyk⟩ := mem_edge_of_mem_frontier (hpc K hKS) hyfr
  rcases hside K hKS k hk y hyk with h | h
  · exact hyb h
  · exact hnint h

/-! ### Chains and boundaries -/

/-- A segment between consecutive points of a list lies on its chain. -/
theorem segment_subset_chainSet : ∀ (M : List Point) (j : ℕ) (hj : j + 1 < M.length),
    segment M[j] M[j + 1] ⊆ chainSet M
  | a :: b :: l, 0, _ => by simp only [chainSet_cons_cons]; exact subset_union_left
  | a :: b :: l, j + 1, hj => by
    rw [chainSet_cons_cons]
    have := segment_subset_chainSet (b :: l) j (by simp at hj ⊢; omega)
    simp only [List.getElem_cons_succ] at this ⊢
    exact this.trans subset_union_right

/-- The chain of a contiguous part of a vertex list lies on the boundary. -/
theorem chainSet_subset_boundary {L : List Point} :
    ∀ {M : List Point}, M <:+: L → chainSet M ⊆ (Polygon.mk L).boundary
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [chainSet_cons_cons]
    refine union_subset ?_ (chainSet_subset_boundary ((List.infix_cons
      (List.infix_refl _)).trans h))
    simpa using seg_subset_boundary h (j := 0) (by simp)

/-- The boundary of a polygon lies on the closed chain of its vertex list. -/
theorem boundary_subset_chainSet {L : List Point} (hL : L ≠ []) :
    (Polygon.mk L).boundary ⊆ chainSet (L ++ [L.headD 0]) := by
  rintro y ⟨i, hi, hy⟩
  have hn : (Polygon.mk L).n = L.length := rfl
  rw [hn] at hi
  have hy' : y ∈ segment (L.getD i 0) (L.getD ((i + 1) % L.length) 0) := hy
  have hlen : (L ++ [L.headD 0]).length = L.length + 1 := by simp
  have h1 : L.getD i 0 = (L ++ [L.headD 0])[i]'(by rw [hlen]; omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getElem_append_left hi]
  have h2 : L.getD ((i + 1) % L.length) 0 = (L ++ [L.headD 0])[i + 1]'(by rw [hlen]; omega) := by
    rcases Nat.lt_or_ge (i + 1) L.length with h | h
    · rw [Nat.mod_eq_of_lt h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
        Option.getD_some, List.getElem_append_left h]
    · have hi' : i + 1 = L.length := by omega
      have hget : (L ++ [L.headD 0])[i + 1]'(by rw [hlen]; omega) = L.headD 0 := by
        simp [hi']
      rw [hget, hi', Nat.mod_self]
      cases L with
      | nil => exact absurd rfl hL
      | cons a l => simp
  rw [h1, h2] at hy'
  exact segment_subset_chainSet _ i (by rw [hlen]; omega) hy'

/-- **Comb cover (floor).** A point of the floor line between `s` and `x_hi` lies on the comb
chain or in the open mouth of one of its features. -/
theorem comb_floor_cover {y₀ xlo xhi : ℝ} : ∀ (fs : List (List Point)) (s : ℝ), s ≤ xhi →
    (∀ f ∈ fs, FloorFeature y₀ xlo xhi f) → (∀ f ∈ fs, s < (fstPt f).1) →
    fs.Pairwise (fun f g => (lstPt f).1 < (fstPt g).1) → ∀ x, s ≤ x → x ≤ xhi →
    ((x, y₀) : Point) ∈ chainSet ((s, y₀) :: fs.flatten ++ [(xhi, y₀)]) ∨
      ∃ f ∈ fs, (fstPt f).1 < x ∧ x < (lstPt f).1
  | [], s, hs, _, _, _, x, hx1, hx2 => by
    left
    simp only [List.flatten_nil, List.nil_append, List.cons_append, chainSet_cons_cons,
      chainSet_single, union_empty]
    rcases eq_or_lt_of_le hs with h | h
    · subst h
      have : x = s := le_antisymm hx2 hx1
      subst this; exact Geometry.left_mem_segment _ _
    · refine ⟨(x - s) / (xhi - s), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext <;> simp <;> field_simp <;> ring
  | f :: fs, s, hs, hF, hfst, hpw, x, hx1, hx2 => by
    obtain ⟨hlen, -, hfy, hly, hfl, -, hxs⟩ := hF f (by simp)
    set a := fstPt f
    set q := lstPt f
    have hqx := (hxs q (lstPt_mem hlen)).2
    have hsa : s < a.1 := hfst f (by simp)
    have hpw' := List.pairwise_cons.1 hpw
    set f' := f.tail.dropLast
    have hfdec : f = a :: (f' ++ [q]) := decomp_of_two_le hlen
    have e : (s, y₀) :: (f :: fs).flatten ++ [(xhi, y₀)] =
        ((s, y₀) :: (a :: f')) ++ q :: (fs.flatten ++ [(xhi, y₀)]) := by
      conv_lhs => rw [List.flatten_cons, hfdec]
      simp
    rw [e, chainSet_append_cons]
    by_cases hxa : x ≤ a.1
    · left; left
      have e2 : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: a :: (f' ++ [q]) := rfl
      rw [e2, chainSet_cons_cons]
      left
      have ha : a = (a.1, y₀) := Prod.ext rfl hfy
      rw [ha]
      have hne : a.1 - s ≠ 0 := ne_of_gt (by linarith)
      refine ⟨(x - s) / (a.1 - s), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only; field_simp; ring
      · simp
    · push Not at hxa
      by_cases hxq : x < q.1
      · exact Or.inr ⟨f, by simp, hxa, hxq⟩
      · push Not at hxq
        have ih := comb_floor_cover fs q.1 (by linarith) (fun g hg => hF g (by simp [hg]))
          (fun g hg => hpw'.1 g hg) hpw'.2 x hxq hx2
        rcases ih with h | ⟨g, hg, hg1, hg2⟩
        · left; right
          have hq : q = (q.1, y₀) := Prod.ext rfl hly
          rw [hq]; simpa using h
        · exact Or.inr ⟨g, by simp [hg], hg1, hg2⟩

end ArtGallery.Stade

end
