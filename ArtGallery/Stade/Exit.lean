module

public import ArtGallery.Stade.Generic.Piece

/-!
# The exit lemma and its corollaries (proof plan L1.2–L1.8)

Let `P` be a simple polygon with its interior to the left of every edge (`P.InteriorLeft`) and
`K` a convex piece (`IsPiece K`, file `Stade/Generic/Piece.lean`).  Each side `j` of `K` is either
a **wall** (`IsWall P K j`: an edge of `P`, traversed in the same direction) or an **opening**
(`O j`, for a predicate `O` chosen by the user); the openings form the **door**
`door K O = ⋃_{O j} K.edge j`.

* `isRoom_piece` (L1.2, room form): `piece K` is a room of `P` with door `door K O`, i.e. near
  every point of the piece off the door, the region of `P` lies in the piece.  (At a vertex where
  two walls meet, the two walls are consecutive edges of `P` by simplicity.)
* `exists_last_exit` (L1.2): a sight line from a point of `K` to a point outside `K` leaves `K`
  for the last time through the door; `exists_exit_ray` gives `p = s + t (q − s)`, `t ≥ 1`, for
  the exit point `q`; `sees_through_opening` (L1.5, general form) gives the sign conditions
  "`s` lies between the projections of `p` through the endpoints of the opening".
* `sees_vtx_cone` (L1.3): a point seeing a convex vertex lies in its cone (from the vertex cone
  lemma of `Vis/Cones.lean`).
* `pocket_exit`, `pocket_pv`, `pocket_projection` (L1.4, L1.5): the nook lemmas for a convex
  quadrilateral pocket `lo, dn, up, hi` with walls `lo dn`, `up hi`, `hi lo` and mouth `dn up`.
* `exit_after_crossing` (L1.6): continuing through an opening crossed in its relative interior.
* `piece_subset_filled` (L1.7): a piece whose interior meets no edge and which has a wall lies in
  the region; `disjoint_interior_of_side` / `disjoint_interior_of_halfplane` (Piece file) give
  the separation hypotheses.
* `sees_of_convex`, `sees_of_mem_segment` (L1.8): sight lines through chains of convex sets.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

variable {P K : Polygon}

/-! ### Walls and doors -/

/-- Side `j` of the piece `K` is a **wall** of `P`: it is an edge of `P`, traversed in the same
direction. -/
def IsWall (P K : Polygon) (j : ℕ) : Prop :=
  ∃ i < P.n, P.vtx i = K.vtx j ∧ P.vtx ((i + 1) % P.n) = K.vtx ((j + 1) % K.n)

/-- The **door** of the piece `K` for the opening predicate `O`: the union of the sides `j` with
`O j`. -/
def door (K : Polygon) (O : ℕ → Prop) : Set Point := {y | ∃ j < K.n, O j ∧ y ∈ K.edge j}

/-- The door of a piece lies in the piece. -/
theorem door_subset_piece (hK : IsPiece K) (O : ℕ → Prop) : door K O ⊆ piece K := by
  rintro y ⟨j, hj, -, hy⟩
  exact edge_subset_piece hK hj hy

/-! ### The room lemma for a piece -/

/-- Near a vertex of a piece that is off the door, the region lies in the piece. -/
theorem near_full_vertex (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K)
    {O : ℕ → Prop} (hWO : ∀ j < K.n, O j ∨ IsWall P K j) {a : ℕ} (ha : a < K.n)
    (hyD : K.vtx a ∉ door K O) :
    ∃ ε > 0, ∀ z ∈ P.filled, dist z (K.vtx a) < ε → z ∈ piece K := by
  set a' := Jordan.prevIdx K a with ha'
  have ha'n : a' < K.n := Jordan.prevIdx_lt K ha
  have ha's : (a' + 1) % K.n = a := prev_succ ha
  obtain ⟨i, hi, hPi, hPi1⟩ := (hWO a ha).resolve_left
    (fun hO => hyD ⟨a, ha, hO, Geometry.left_mem_segment _ _⟩)
  have hmem' : K.vtx a ∈ K.edge a' := by
    unfold Polygon.edge; rw [ha's]; exact Geometry.right_mem_segment _ _
  obtain ⟨i', hi', hPi', hPi'1⟩ := (hWO a' ha'n).resolve_left
    (fun hO => hyD ⟨a', ha'n, hO, hmem'⟩)
  rw [ha's] at hPi'1
  have hsucc : (i' + 1) % P.n = i :=
    Jordan.simple_vtx_inj hP (Nat.mod_lt _ (by omega)) hi (hPi'1.trans hPi.symm)
  have hprev : (i + P.n - 1) % P.n = i' := (Jordan.eq_prevIdx_of_succ P hi hi' hsucc).symm
  obtain ⟨r₁, hr₁, hloc⟩ := Polygon.local_wedge hP hL hi
  obtain ⟨r₂, hr₂, hnear⟩ := near_vertex hK ha
  have hD : 0 ≤ det (K.vtx a') (K.vtx a) (K.vtx ((a + 1) % K.n)) := by
    have := hK.vtx_mem a' ha'n _ (succ_mod_lt ha); rwa [ha's] at this
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz hzy => ?_⟩
  have h := (hloc z (by rw [hPi]; exact lt_of_lt_of_le hzy (min_le_left _ _))).1 hz
  simp only [hprev, hPi', hPi, hPi1] at h
  have hz2 := lt_of_lt_of_le hzy (min_le_right _ _)
  split_ifs at h with h1 h2
  · exact hnear z hz2 h.1 h.2
  · exact absurd hD (not_le.2 h2)
  · have hD0 : det (K.vtx a') (K.vtx a) (K.vtx ((a + 1) % K.n)) = 0 :=
      le_antisymm (not_lt.1 h1) hD
    exact hnear z hz2 h (straight_side_nonneg hK ha hD0 h)

/-- **Room lemma for a piece (L1.2).** If every side of the piece `K` is a wall of `P` or an
opening, then `piece K` is a room of `P` whose door is the union of the openings. -/
theorem isRoom_piece (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K) {O : ℕ → Prop}
    (hWO : ∀ j < K.n, O j ∨ IsWall P K j) : P.IsRoom (piece K) (door K O) := by
  refine ⟨isClosed_piece K, fun y hyK _ hyD => ?_⟩
  by_cases hact : ∃ j < K.n, det (K.vtx j) (K.vtx ((j + 1) % K.n)) y = 0
  · obtain ⟨j, hj, hyj⟩ := hact
    obtain ⟨k, hk, hyk⟩ := mem_edge_of_det_eq_zero hK hyK hj hyj
    have hwall : IsWall P K k := (hWO k hk).resolve_left (fun hO => hyD ⟨k, hk, hO, hyk⟩)
    obtain ⟨i, hi, hPi, hPi1⟩ := hwall
    obtain ⟨t, ht0, ht1, hyt⟩ := hyk
    have hyt' : y = lerp (K.vtx k) (K.vtx ((k + 1) % K.n)) t := hyt
    rcases ht0.lt_or_eq with ht0' | ht0'
    · rcases ht1.lt_or_eq with ht1' | ht1'
      · obtain ⟨r₁, hr₁, h₁⟩ := Polygon.local_halfplane hP hL hi ht0' ht1'
        obtain ⟨r₂, hr₂, h₂⟩ := near_open_side hK hk ht0' ht1'
        rw [hPi, hPi1, ← Geometry.lerp_eq_add_smul] at h₁
        refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz hzy => ?_⟩
        rw [hyt'] at hzy
        exact h₂ z (lt_of_lt_of_le hzy (min_le_right _ _))
          ((h₁ z (lt_of_lt_of_le hzy (min_le_left _ _))).1 hz)
      · rw [ht1', Geometry.lerp_one] at hyt'
        rw [hyt'] at hyD ⊢
        exact near_full_vertex hP hL hK hWO (succ_mod_lt hk) hyD
    · rw [← ht0', Geometry.lerp_zero] at hyt'
      rw [hyt'] at hyD ⊢
      exact near_full_vertex hP hL hK hWO hk hyD
  · push Not at hact
    obtain ⟨r, hr, hnear⟩ := near_mem_piece hyK
    exact ⟨r, hr, fun z _ hz => hnear z hz fun k hk h => absurd h (hact k hk)⟩

/-! ### The exit lemma -/

/-- Composition of `lerp` along a segment. -/
theorem lerp_lerp_right (s p : Point) (τ μ : ℝ) :
    lerp (lerp s p τ) p μ = lerp s p (τ + μ * (1 - τ)) := by
  ext <;> simp [lerp] <;> ring

/-- A segment from a point of `segment s p` to `p` lies in `segment s p`. -/
theorem segment_lerp_subset (s p : Point) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ArtGallery.segment (lerp s p τ) p ⊆ ArtGallery.segment s p :=
  Geometry.segment_subset_of_convex (Geometry.segment_convex s p) (lerp_mem_segment _ _ h0 h1)
    (Geometry.right_mem_segment s p)

/-- **Last exit from a room.** For a room `R` of `P` whose door `D` lies in `R`, a sight line from
`s ∈ R` to `p ∉ R` leaves `R` for the last time at a point `lerp s p τ` of the door; beyond it the
sight line stays outside `R`. -/
theorem exists_last_exit_of_isRoom {R D : Set Point} (hR : P.IsRoom R D) (hDR : D ⊆ R)
    {s p : Point} (hs : s ∈ R) (hp : p ∉ R) (hsp : P.Sees s p) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ lerp s p τ ∈ D ∧
      ∀ τ' : ℝ, τ < τ' → τ' ≤ 1 → lerp s p τ' ∉ R := by
  set T : Set ℝ := Icc 0 1 ∩ lerp s p ⁻¹' R with hT
  have hTc : IsCompact T :=
    isCompact_Icc.inter_right (hR.1.preimage (Geometry.continuous_lerp s p))
  have hT0 : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by simp [Geometry.lerp_zero, hs]⟩
  have hmem := hTc.sSup_mem ⟨0, hT0⟩
  set τ := sSup T with hτ
  have hle : ∀ x ∈ T, x ≤ τ := fun x hx => le_csSup hTc.bddAbove hx
  obtain ⟨⟨hτ0, hτ1⟩, hτK⟩ := hmem
  have hτ1' : τ < 1 := by
    rcases hτ1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hp; have := hτK; rw [mem_preimage, h, Geometry.lerp_one] at this; exact this
  refine ⟨τ, hτ0, hτ1', ?_, fun τ' h1 h2 hK' => ?_⟩
  · have hsees : P.Sees (lerp s p τ) p := (segment_lerp_subset s p hτ0 hτ1).trans hsp
    obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door hR hτK hp hsees
    obtain ⟨μ, hμ0, hμ1, rfl⟩ := hy
    have e : ((lerp s p τ).1 + μ * (p.1 - (lerp s p τ).1),
        (lerp s p τ).2 + μ * (p.2 - (lerp s p τ).2)) = lerp s p (τ + μ * (1 - τ)) :=
      lerp_lerp_right s p τ μ
    rw [e] at hyD
    have hin : τ + μ * (1 - τ) ∈ T := by
      refine ⟨⟨by nlinarith, by nlinarith⟩, hDR hyD⟩
    have := hle _ hin
    have hμ : μ = 0 := by nlinarith
    rw [hμ, zero_mul, add_zero] at hyD
    exact hyD
  · have := hle τ' ⟨⟨by linarith, h2⟩, hK'⟩
    linarith

/-- **Exit lemma (L1.2), last-exit form.** A sight line from `s ∈ K` to `p ∉ K` leaves `K` for
the last time at a point `lerp s p τ` of the door; beyond it the sight line stays outside `K`. -/
theorem exists_last_exit (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K)
    {O : ℕ → Prop} (hWO : ∀ j < K.n, O j ∨ IsWall P K j) {s p : Point} (hs : s ∈ piece K)
    (hp : p ∉ piece K) (hsp : P.Sees s p) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ lerp s p τ ∈ door K O ∧
      ∀ τ' : ℝ, τ < τ' → τ' ≤ 1 → lerp s p τ' ∉ piece K :=
  exists_last_exit_of_isRoom (isRoom_piece hP hL hK hWO) (door_subset_piece hK O) hs hp hsp

/-- **Exit lemma (L1.2), simple form.** A sight line from a point of the piece to a point outside
meets the door. -/
theorem exists_exit (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K) {O : ℕ → Prop}
    (hWO : ∀ j < K.n, O j ∨ IsWall P K j) {s p : Point} (hs : s ∈ piece K) (hp : p ∉ piece K)
    (hsp : P.Sees s p) : ∃ j < K.n, O j ∧ ∃ q ∈ K.edge j, q ∈ ArtGallery.segment s p := by
  obtain ⟨τ, hτ0, hτ1, ⟨j, hj, hO, hq⟩, -⟩ := exists_last_exit hP hL hK hWO hs hp hsp
  exact ⟨j, hj, hO, _, hq, lerp_mem_segment _ _ hτ0 hτ1.le⟩

/-- `lerp s (lerp s p τ) (1/τ) = p` for `τ ≠ 0`. -/
theorem lerp_lerp_inv (s p : Point) {τ : ℝ} (hτ : τ ≠ 0) : lerp s (lerp s p τ) (1 / τ) = p := by
  ext <;> simp [lerp] <;> field_simp <;> ring

/-- **Exit ray.** For `s ∈ K` off the door and `p ∉ K` seen from `s`, the last exit point `q` lies on
an opening side `j`, and `p = s + t (q − s)` with `t ≥ 1`. -/
theorem exists_exit_ray (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K) {O : ℕ → Prop}
    (hWO : ∀ j < K.n, O j ∨ IsWall P K j) {s p : Point} (hs : s ∈ piece K) (hsD : s ∉ door K O)
    (hp : p ∉ piece K) (hsp : P.Sees s p) :
    ∃ j < K.n, O j ∧ ∃ q ∈ K.edge j, q ∈ ArtGallery.segment s p ∧
      ∃ t : ℝ, 1 ≤ t ∧ p = lerp s q t := by
  obtain ⟨τ, hτ0, hτ1, hqD, -⟩ := exists_last_exit hP hL hK hWO hs hp hsp
  have hτ : τ ≠ 0 := by
    rintro rfl; rw [Geometry.lerp_zero] at hqD; exact hsD hqD
  obtain ⟨j, hj, hO, hq⟩ := hqD
  refine ⟨j, hj, hO, _, hq, lerp_mem_segment _ _ hτ0 hτ1.le, 1 / τ, ?_,
    (lerp_lerp_inv s p hτ).symm⟩
  rw [le_div_iff₀ (lt_of_le_of_ne hτ0 (Ne.symm hτ))]
  linarith

/-- The sign conditions of a sight line through an opening: if `q ∈ [a, b]`, `p = s + t (q − s)`
with `t ≥ 0` and `s` weakly left of `a → b`, then `s` lies between the rays from `p` through `a`
and `b`: `det p a s ≤ 0 ≤ det p b s`. -/
theorem det_signs_of_through {a b s q p : Point} (hq : q ∈ ArtGallery.segment a b) {t : ℝ}
    (ht : 0 ≤ t) (hp : p = lerp s q t) (hs : 0 ≤ det a b s) :
    det p a s ≤ 0 ∧ 0 ≤ det p b s := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := hq
  subst hp
  have e1 : det (lerp s (a.1 + μ * (b.1 - a.1), a.2 + μ * (b.2 - a.2)) t) a s =
      -(t * μ) * det a b s := by unfold det lerp; simp only; ring
  have e2 : det (lerp s (a.1 + μ * (b.1 - a.1), a.2 + μ * (b.2 - a.2)) t) b s =
      (t * (1 - μ)) * det a b s := by unfold det lerp; simp only; ring
  rw [e1, e2]
  constructor
  · nlinarith [mul_nonneg (mul_nonneg ht hμ0) hs]
  · exact mul_nonneg (mul_nonneg ht (by linarith)) hs

/-- **Sight lines through an opening (L1.5, general form).** If `s ∈ K` is off the door and sees
`p ∉ K`, the sight line leaves `K` through an opening side `j` from `c = K.vtx j` to
`c' = K.vtx (j+1)` at a point `q`, with `p = s + t (q − s)`, `t ≥ 1`, and `s` lies between the
rays from `p` through `c` and `c'`: `det p c s ≤ 0 ≤ det p c' s`. -/
theorem sees_through_opening (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K)
    {O : ℕ → Prop} (hWO : ∀ j < K.n, O j ∨ IsWall P K j) {s p : Point} (hs : s ∈ piece K)
    (hsD : s ∉ door K O) (hp : p ∉ piece K) (hsp : P.Sees s p) :
    ∃ j < K.n, O j ∧ ∃ q ∈ K.edge j, q ∈ ArtGallery.segment s p ∧
      (∃ t : ℝ, 1 ≤ t ∧ p = lerp s q t) ∧
      det p (K.vtx j) s ≤ 0 ∧ 0 ≤ det p (K.vtx ((j + 1) % K.n)) s := by
  obtain ⟨j, hj, hO, q, hq, hqs, t, ht, hpt⟩ := exists_exit_ray hP hL hK hWO hs hsD hp hsp
  exact ⟨j, hj, hO, q, hq, hqs, ⟨t, ht, hpt⟩,
    det_signs_of_through hq (by linarith) hpt (hs j hj)⟩

/-! ### Wedge cones (L1.3) -/

/-- **Wedge cone (L1.3).** A point seeing a convex vertex `v` of `P` (predecessor `u`, successor
`w`) lies in the cone `v + λ (w − v) + μ (u − v)`, `λ, μ ≥ 0`. -/
theorem sees_vtx_cone (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {p : Point} (h : P.Sees p v) :
    ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧
      p = (v.1 + l * (w.1 - v.1) + m * (u.1 - v.1), v.2 + l * (w.2 - v.2) + m * (u.2 - v.2)) := by
  obtain ⟨hA, hB⟩ := Polygon.sees_subset_cone' hP hL hi hu hv hw hconv h
  obtain ⟨d1, d2⟩ := Polygon.cone_decomp_coord u v w p
  refine ⟨det u v p / det u v w, det v w p / det u v w, div_nonneg hA hconv.le,
    div_nonneg hB hconv.le, Prod.ext ?_ ?_⟩
  · simp only
    field_simp
    linarith
  · simp only
    field_simp
    linarith

/-! ### Pockets (L1.4, L1.5) -/

/-- A convex combination of two positive numbers is positive. -/
theorem convex_comb_pos {l X Y : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hX : 0 < X) (hY : 0 < Y) :
    0 < (1 - l) * X + l * Y := by
  rcases hl0.lt_or_eq with h | h
  · nlinarith [mul_pos h hY, mul_nonneg (sub_nonneg.2 hl1) hX.le]
  · rw [← h]; simp [hX]

section Pocket

variable {lo dn up hi : Point}

/-- The door of the pocket quadrilateral (opening: side `1`) is its mouth. -/
theorem door_quad_one : door (quad lo dn up hi) (· = 1) = ArtGallery.segment dn up := by
  ext y
  constructor
  · rintro ⟨j, -, rfl, hy⟩
    simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n] using hy
  · intro hy
    exact ⟨1, by simp [quad, Polygon.n], rfl, by simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n]⟩

/-- The wall/opening labelling of the pocket quadrilateral. -/
theorem pocket_hWO (hw0 : ∃ i < P.n, P.vtx i = lo ∧ P.vtx ((i + 1) % P.n) = dn)
    (hw2 : ∃ i < P.n, P.vtx i = up ∧ P.vtx ((i + 1) % P.n) = hi)
    (hw3 : ∃ i < P.n, P.vtx i = hi ∧ P.vtx ((i + 1) % P.n) = lo) :
    ∀ j < (quad lo dn up hi).n, j = 1 ∨ IsWall P (quad lo dn up hi) j := by
  intro j hj
  simp only [quad, Polygon.n, List.length_cons, List.length_nil] at hj
  interval_cases j
  · right; simpa [IsWall, quad, Polygon.vtx, Polygon.n] using hw0
  · left; rfl
  · right; simpa [IsWall, quad, Polygon.vtx, Polygon.n] using hw2
  · right; simpa [IsWall, quad, Polygon.vtx, Polygon.n] using hw3

/-- **Nook exit (L1.4).** Let `lo, dn, up, hi` be a strictly convex counter-clockwise pocket whose
sides `lo → dn`, `up → hi`, `hi → lo` are edges of `P` (the mouth `dn up` is the opening).  A
point `p` seen from a point `s` of the nook segment `[hi, lo]` is in the pocket, or
`p = s + t (q − s)` for a point `q` of the mouth and `t ≥ 1`. -/
theorem pocket_exit (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : ∃ i < P.n, P.vtx i = lo ∧ P.vtx ((i + 1) % P.n) = dn)
    (hw2 : ∃ i < P.n, P.vtx i = up ∧ P.vtx ((i + 1) % P.n) = hi)
    (hw3 : ∃ i < P.n, P.vtx i = hi ∧ P.vtx ((i + 1) % P.n) = lo)
    {s p : Point} (hs : s ∈ ArtGallery.segment hi lo) (hsp : P.Sees s p) :
    p ∈ piece (quad lo dn up hi) ∨
      ∃ q ∈ ArtGallery.segment dn up, ∃ t : ℝ, 1 ≤ t ∧ p = lerp s q t := by
  have hK := isPiece_quad h1 h2 h3 h4
  by_cases hp : p ∈ piece (quad lo dn up hi)
  · exact Or.inl hp
  right
  have hsK : s ∈ piece (quad lo dn up hi) := edge_subset_piece hK (j := 3)
    (by simp [quad, Polygon.n]) (by simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n] using hs)
  have hpos : 0 < det dn up s := by
    obtain ⟨l, hl0, hl1, rfl⟩ := hs
    change 0 < det dn up (lerp hi lo l)
    rw [det_lerp, Geometry.det_cyclic lo dn up]
    exact convex_comb_pos hl0 hl1 h2 h1
  have hsD : s ∉ door (quad lo dn up hi) (· = 1) := by
    rw [door_quad_one]
    intro h
    rw [Geometry.det_eq_zero_of_mem_segment h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨j, -, rfl, q, hq, -, t, ht, hpt⟩ :=
    exists_exit_ray hP hL hK (pocket_hWO hw0 hw2 hw3) hsK hsD hp hsp
  exact ⟨q, by simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n] using hq, t, ht, hpt⟩

/-- **Nook partial-visibility region (L1.4).** Under the hypotheses of `pocket_exit`, a point `p`
seen from the nook segment is in the pocket or in `PV`: beyond the mouth line
(`det dn up p ≤ 0`), on the side of the diagonal `hi dn` containing `up` (`0 ≤ det hi dn p`) and on
the side of the diagonal `lo up` containing `dn` (`det lo up p ≤ 0`). -/
theorem pocket_pv (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : ∃ i < P.n, P.vtx i = lo ∧ P.vtx ((i + 1) % P.n) = dn)
    (hw2 : ∃ i < P.n, P.vtx i = up ∧ P.vtx ((i + 1) % P.n) = hi)
    (hw3 : ∃ i < P.n, P.vtx i = hi ∧ P.vtx ((i + 1) % P.n) = lo)
    {s p : Point} (hs : s ∈ ArtGallery.segment hi lo) (hsp : P.Sees s p) :
    p ∈ piece (quad lo dn up hi) ∨
      (det dn up p ≤ 0 ∧ 0 ≤ det hi dn p ∧ det lo up p ≤ 0) := by
  rcases pocket_exit hP hL h1 h2 h3 h4 hw0 hw2 hw3 hs hsp with h | ⟨q, hq, t, ht, rfl⟩
  · exact Or.inl h
  right
  obtain ⟨l, hl0, hl1, rfl⟩ := hs
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := hq
  change det dn up (lerp (lerp hi lo l) (lerp dn up μ) t) ≤ 0 ∧
    0 ≤ det hi dn (lerp (lerp hi lo l) (lerp dn up μ) t) ∧
    det lo up (lerp (lerp hi lo l) (lerp dn up μ) t) ≤ 0
  simp only [det_lerp, Geometry.det_self_right, Geometry.det_self_outer]
  have a1 : det dn up lo = det lo dn up := Geometry.det_cyclic lo dn up
  have a2 : det hi dn lo = -det hi lo dn := by unfold det; ring
  have a3 : det hi dn up = det dn up hi := Geometry.det_cyclic_right dn up hi
  have a4 : det lo up hi = det up hi lo := Geometry.det_cyclic_right up hi lo
  have a5 : det lo up dn = -det lo dn up := Geometry.det_swap23 lo dn up
  rw [a1, a2, a3, a4, a5]
  have ht1 : 0 ≤ t - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ht1 (mul_nonneg (sub_nonneg.2 hl1) h2.le),
      mul_nonneg ht1 (mul_nonneg hl0 h1.le)]
  · nlinarith [mul_nonneg ht1 (mul_nonneg hl0 h4.le),
      mul_nonneg (by linarith : (0:ℝ) ≤ t) (mul_nonneg hμ0 h2.le)]
  · nlinarith [mul_nonneg ht1 (mul_nonneg (sub_nonneg.2 hl1) h3.le),
      mul_nonneg (by linarith : (0:ℝ) ≤ t) (mul_nonneg (sub_nonneg.2 hμ1) h1.le)]

/-- **Projection bound (L1.5).** Under the hypotheses of `pocket_exit`, if `p` is outside the
pocket (e.g. strictly beyond the mouth line, `pocket_projection'`) and sees the point `s` of the
nook segment, then `s` lies between the rays from `p` through the mouth corners:
`det p dn s ≤ 0 ≤ det p up s`. -/
theorem pocket_projection (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : ∃ i < P.n, P.vtx i = lo ∧ P.vtx ((i + 1) % P.n) = dn)
    (hw2 : ∃ i < P.n, P.vtx i = up ∧ P.vtx ((i + 1) % P.n) = hi)
    (hw3 : ∃ i < P.n, P.vtx i = hi ∧ P.vtx ((i + 1) % P.n) = lo)
    {s p : Point} (hs : s ∈ ArtGallery.segment hi lo) (hp : p ∉ piece (quad lo dn up hi))
    (hsp : P.Sees s p) : det p dn s ≤ 0 ∧ 0 ≤ det p up s := by
  rcases pocket_exit hP hL h1 h2 h3 h4 hw0 hw2 hw3 hs hsp with h | ⟨q, hq, t, ht, hpt⟩
  · exact absurd h hp
  have hpos : 0 ≤ det dn up s := by
    obtain ⟨l, hl0, hl1, rfl⟩ := hs
    change 0 ≤ det dn up (lerp hi lo l)
    rw [det_lerp, Geometry.det_cyclic lo dn up]
    exact (convex_comb_pos hl0 hl1 h2 h1).le
  exact det_signs_of_through hq (by linarith) hpt hpos

/-- `pocket_projection` for a point strictly beyond the mouth line. -/
theorem pocket_projection' (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : ∃ i < P.n, P.vtx i = lo ∧ P.vtx ((i + 1) % P.n) = dn)
    (hw2 : ∃ i < P.n, P.vtx i = up ∧ P.vtx ((i + 1) % P.n) = hi)
    (hw3 : ∃ i < P.n, P.vtx i = hi ∧ P.vtx ((i + 1) % P.n) = lo)
    {s p : Point} (hs : s ∈ ArtGallery.segment hi lo) (hp : det dn up p < 0)
    (hsp : P.Sees s p) : det p dn s ≤ 0 ∧ 0 ≤ det p up s := by
  refine pocket_projection hP hL h1 h2 h3 h4 hw0 hw2 hw3 hs (fun h => ?_) hsp
  exact absurd ((mem_piece_quad.1 h).2.1) (not_le.2 hp)

end Pocket

/-! ### Chains of pieces (L1.6) -/

/-- **Continuing through an opening (L1.6).** Let `q` be a point of the open side `j'` of the
piece `K'` and `p` a point strictly on the inner side of that side, outside `K'`, seen from `q`.
Then the sight line `q p` leaves `K'` for the last time at a point `lerp q p μ` (`0 < μ < 1`) of
the door of `K'`, strictly on the inner side of side `j'`. -/
theorem exit_after_crossing (hP : P.Simple) (hL : P.InteriorLeft) {K' : Polygon}
    (hK' : IsPiece K') {O' : ℕ → Prop} (hWO' : ∀ j < K'.n, O' j ∨ IsWall P K' j) {j' : ℕ}
    (hj' : j' < K'.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {q p : Point}
    (hq : q = lerp (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) t)
    (hpj : 0 < det (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) p) (hp : p ∉ piece K')
    (hqp : P.Sees q p) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ lerp q p μ ∈ door K' O' ∧
      0 < det (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) (lerp q p μ) ∧
      ∀ μ' : ℝ, μ < μ' → μ' ≤ 1 → lerp q p μ' ∉ piece K' := by
  have hqK : q ∈ piece K' := by
    rw [hq]; exact edge_subset_piece hK' hj' (lerp_mem_segment _ _ ht0.le ht1.le)
  have hq0 : det (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) q = 0 := by
    rw [hq]; exact Geometry.det_lerp_self _ _ _
  obtain ⟨μ, hμ0, hμ1, hD, hout⟩ := exists_last_exit hP hL hK' hWO' hqK hp hqp
  have hval : ∀ μ' : ℝ, det (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) (lerp q p μ') =
      μ' * det (K'.vtx j') (K'.vtx ((j' + 1) % K'.n)) p := by
    intro μ'; rw [det_lerp, hq0]; ring
  have hμpos : 0 < μ := by
    rcases hμ0.lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨r, hr, hnear⟩ := near_open_side hK' hj' ht0 ht1
    rw [← hq] at hnear
    obtain ⟨μ', hμ'0, hμ'1, hd⟩ := Polygon.exists_lerp_mem_ball q p hr
    refine hout μ' (by rw [← h]; exact hμ'0) hμ'1 (hnear _ hd ?_)
    rw [hval]; exact (mul_pos hμ'0 hpj).le
  exact ⟨μ, hμpos, hμ1, hD, by rw [hval]; exact mul_pos hμpos hpj, hout⟩

/-! ### Pieces in the region (L1.7) -/

/-- **Pieces in the region (L1.7).** A piece whose interior meets no edge of `P` and which has a
wall lies in the region of `P`. -/
theorem piece_subset_filled (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K)
    (hedge : ∀ i < P.n, Disjoint (interior (piece K)) (P.edge i)) {j : ℕ} (hj : j < K.n)
    (hwall : IsWall P K j) : piece K ⊆ P.filled := by
  obtain ⟨i, hi, hPi, hPi1⟩ := hwall
  set a := K.vtx j with ha
  set b := K.vtx ((j + 1) % K.n) with hb
  have hab : a ≠ b := vtx_ne hK hj
  obtain ⟨δ₀, hδ₀, hoff⟩ := hL i hi (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨r, hr, hnear⟩ := near_open_side hK hj (t := 1 / 2) (by norm_num) (by norm_num)
  set m := lerp a b (1 / 2) with hm
  set N := Polygon.leftNormal a b with hN
  set δ := min (δ₀ / 2) (r / (2 * (‖N‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos hr (by positivity))
  have hδ1 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set z := m + δ • N with hz
  have hzf : z ∈ P.filled := by
    have := (hoff δ hδ0 hδ1).1.1
    rw [hPi, hPi1, ← Geometry.lerp_eq_add_smul] at this
    exact this
  have hdist : dist z m < r := by
    rw [hz, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ0.le]
    have h1 : δ ≤ r / (2 * (‖N‖ + 1)) := min_le_right _ _
    have h2 : δ * ‖N‖ ≤ r / (2 * (‖N‖ + 1)) * ‖N‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : r / (2 * (‖N‖ + 1)) * ‖N‖ < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg N]
    linarith
  have hzj : 0 < det a b z := by
    rw [hz, Geometry.det_add_smul, hm, Geometry.det_lerp_self, zero_add]
    have : det a b (a + N) = (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
      rw [hN]; unfold det Polygon.leftNormal; simp only [Prod.fst_add, Prod.snd_add]; ring
    rw [this]
    exact mul_pos hδ0 (Jordan.sqLen_pos hab)
  have hzint : z ∈ interior (piece K) := by
    rw [mem_interior_iff_mem_nhds]
    have h1 : ∀ᶠ w in 𝓝 z, dist w m < r := isOpen_ball.mem_nhds (mem_ball.2 hdist)
    have h2 : ∀ᶠ w in 𝓝 z, 0 < det a b w :=
      (Geometry.continuous_det_right a b).continuousAt.eventually (lt_mem_nhds hzj)
    filter_upwards [h1, h2] with w hw1 hw2 using hnear w hw1 hw2.le
  have := Polygon.closure_subset_filled_of_convex hP (convex_piece K) hedge hzint hzf
  rwa [(isClosed_piece K).closure_eq] at this

/-- A wall side of a piece misses the interior of the piece. -/
theorem disjoint_interior_of_wall (hK : IsPiece K) {j : ℕ} (hj : j < K.n) :
    Disjoint (interior (piece K)) (ArtGallery.segment (K.vtx j) (K.vtx ((j + 1) % K.n))) :=
  disjoint_interior_of_side hK hj (le_of_eq (Geometry.det_self_outer _ _))
    (le_of_eq (Geometry.det_self_right _ _))

/-- **Pieces in the region, separation form (L1.7).** A piece with a wall lies in the region if
every edge of `P` has both endpoints weakly to the right of the line of some side of the piece
(the walls of the piece themselves qualify, with the side they lie on). -/
theorem piece_subset_filled_of_sides (hP : P.Simple) (hL : P.InteriorLeft) (hK : IsPiece K)
    (hsep : ∀ i < P.n, ∃ j < K.n, det (K.vtx j) (K.vtx ((j + 1) % K.n)) (P.vtx i) ≤ 0 ∧
      det (K.vtx j) (K.vtx ((j + 1) % K.n)) (P.vtx ((i + 1) % P.n)) ≤ 0)
    {j : ℕ} (hj : j < K.n) (hwall : IsWall P K j) : piece K ⊆ P.filled := by
  refine piece_subset_filled hP hL hK (fun i hi => ?_) hj hwall
  obtain ⟨k, hk, h1, h2⟩ := hsep i hi
  exact disjoint_interior_of_side hK hk h1 h2

/-! ### Visibility through chains of convex sets (L1.8) -/

/-- Two points of a convex subset of the region see each other. -/
theorem sees_of_convex {C : Set Point} (hC : Convex ℝ C) (hCP : C ⊆ P.filled) {p q : Point}
    (hp : p ∈ C) (hq : q ∈ C) : P.Sees p q :=
  (Geometry.segment_subset_of_convex hC hp hq).trans hCP

/-- Two points of a piece contained in the region see each other. -/
theorem sees_of_mem_piece (hKP : piece K ⊆ P.filled) {p q : Point} (hp : p ∈ piece K)
    (hq : q ∈ piece K) : P.Sees p q :=
  sees_of_convex (convex_piece K) hKP hp hq

/-- A segment through a point `x` of it splits into the two sub-segments. -/
theorem segment_subset_union_of_mem {p q x : Point} (hx : x ∈ ArtGallery.segment p q) :
    ArtGallery.segment p q ⊆ ArtGallery.segment p x ∪ ArtGallery.segment x q := by
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := hx
  rintro y ⟨s, hs0, hs1, rfl⟩
  change lerp p q s ∈ ArtGallery.segment p (lerp p q τ) ∪ ArtGallery.segment (lerp p q τ) q
  by_cases hsτ : s ≤ τ
  · left
    have hτ : 0 < τ ∨ τ = 0 := hτ0.lt_or_eq.imp id Eq.symm
    rcases hτ with hτ | hτ
    · refine ⟨s / τ, div_nonneg hs0 hτ.le, (div_le_one hτ).2 hsτ, ?_⟩
      change lerp p q s = lerp p (lerp p q τ) (s / τ)
      ext <;> simp [lerp] <;> field_simp
    · have : s = 0 := by linarith
      subst this; subst hτ
      exact ⟨0, le_rfl, zero_le_one, by simp [lerp]⟩
  · right
    push Not at hsτ
    have hτ1' : τ < 1 := lt_of_lt_of_le hsτ hs1
    refine ⟨(s - τ) / (1 - τ), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    change lerp p q s = lerp (lerp p q τ) q ((s - τ) / (1 - τ))
    rw [lerp_lerp_right]
    congr 1
    have : (s - τ) / (1 - τ) * (1 - τ) = s - τ := div_mul_cancel₀ _ (by linarith)
    linarith

/-- **Concatenating sight lines (L1.8).** If `x` lies on the segment `p q`, and `p` sees `x` and `x`
sees `q`, then `p` sees `q`. -/
theorem sees_of_mem_segment {p q x : Point} (hx : x ∈ ArtGallery.segment p q)
    (hpx : P.Sees p x) (hxq : P.Sees x q) : P.Sees p q := fun _ hy =>
  (segment_subset_union_of_mem hx hy).elim (fun h => hpx h) (fun h => hxq h)

/-- **Visibility through two convex pieces (L1.8).** If `p ∈ C₁`, `q ∈ C₂` and the segment `p q`
passes through a point `x ∈ C₁ ∩ C₂`, with `C₁, C₂` convex subsets of the region, then `p` sees
`q`. -/
theorem sees_of_two_convex {C₁ C₂ : Set Point} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (h₁P : C₁ ⊆ P.filled) (h₂P : C₂ ⊆ P.filled) {p q x : Point} (hp : p ∈ C₁) (hq : q ∈ C₂)
    (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) (hx : x ∈ ArtGallery.segment p q) : P.Sees p q :=
  sees_of_mem_segment hx (sees_of_convex h₁ h₁P hp hx₁) (sees_of_convex h₂ h₂P hx₂ hq)

end ArtGallery.Stade

end
