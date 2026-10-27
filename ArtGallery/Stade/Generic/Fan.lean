module

public import ArtGallery.Stade.Generic.Glue

/-!
# Rooms made of glued pieces (proof plan L1.6)

Exit lemmas for a union of pieces that does not require the region to be known.

* `near_full_fan` (**two-piece fan**): at a common vertex `v` of two pieces `K, K'`, where the
  side of `K` leaving `v` is glued to the side of `K'` entering `v`, and the other two sides at
  `v` are walls of `P` (consecutive edges of `P`), the region of `P` near `v` lies in
  `piece K ∪ piece K'`.  The proof compares the local wedge of `P` at `v` (`local_wedge`) with the
  two corner wedges, using two determinant identities.
* `isRoom_star` (**star rooms**): a central piece `K` with satellites `Ks r` glued along sides of
  `K` that are pairwise non-adjacent; the union is a room whose door consists of the openings of
  `K` and of the satellites (all sides other than walls and glued sides).  For example: an
  addition room with its pockets, its aux wedge and its needles, or the hall with a wedge.
* `exists_last_exit_star`: the last-exit lemma for star rooms.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

variable {P K : Polygon}

/-- The successor of a side index is a different side. -/
theorem succ_mod_ne {K : Polygon} (hK : IsPiece K) {j : ℕ} (hj : j < K.n) :
    (j + 1) % K.n ≠ j := by
  intro h
  have := vtx_ne hK hj
  rw [h] at this
  exact this rfl

/-- The predecessor of the successor of a side index. -/
theorem prev_succ_mod {K : Polygon} {j : ℕ} (hj : j < K.n) :
    Jordan.prevIdx K ((j + 1) % K.n) = j :=
  (Jordan.eq_prevIdx_of_succ K (succ_mod_lt hj) hj rfl).symm

/-- **Two-piece fan.** Let `v = K.vtx a = K'.vtx a'`, where the side `a` of `K` (leaving `v`) is
glued to the side of `K'` entering `v` (`K'.vtx (prev a') = K.vtx (a+1)`), the side of `K`
entering `v` is a wall and the side `a'` of `K'` leaving `v` is a wall.  Then near `v` the region
of `P` lies in `piece K ∪ piece K'`. -/
theorem near_full_fan (hP : P.Simple) (hL : P.InteriorLeft) {K K' : Polygon} (hK : IsPiece K)
    (hK' : IsPiece K') {a a' : ℕ} (ha : a < K.n) (ha' : a' < K'.n)
    (hv : K'.vtx a' = K.vtx a) (hb : K'.vtx (Jordan.prevIdx K' a') = K.vtx ((a + 1) % K.n))
    (hwK : IsWall P K (Jordan.prevIdx K a)) (hwK' : IsWall P K' a') :
    ∃ ε > 0, ∀ z ∈ P.filled, dist z (K.vtx a) < ε → z ∈ piece K ∪ piece K' := by
  set u := K.vtx (Jordan.prevIdx K a) with hu
  set v := K.vtx a with hvv
  set b := K.vtx ((a + 1) % K.n) with hbb
  set w := K'.vtx ((a' + 1) % K'.n) with hw
  have hpa := Jordan.prevIdx_lt K ha
  have hpa' := Jordan.prevIdx_lt K' ha'
  have hps : (Jordan.prevIdx K a + 1) % K.n = a := prev_succ ha
  have hps' : (Jordan.prevIdx K' a' + 1) % K'.n = a' := prev_succ ha'
  -- the two walls are consecutive edges of `P`
  obtain ⟨i', hi', hPi', hPi'1⟩ := hwK
  obtain ⟨i, hi, hPi, hPi1⟩ := hwK'
  rw [hps] at hPi'1
  have hsucc : (i' + 1) % P.n = i :=
    Jordan.simple_vtx_inj hP (Nat.mod_lt _ (by omega)) hi (by rw [hPi'1, hPi, hv])
  have hprev : (i + P.n - 1) % P.n = i' := (Jordan.eq_prevIdx_of_succ P hi hi' hsucc).symm
  obtain ⟨r₀, hr₀, hloc⟩ := Polygon.local_wedge hP hL hi
  -- the corner wedges of the two pieces
  obtain ⟨r₁, hr₁, h₁⟩ := near_vertex hK ha
  obtain ⟨r₂, hr₂, h₂⟩ := near_vertex hK' ha'
  rw [hb, hv] at h₂
  -- convexity at `v` and the centers
  have F1 : 0 ≤ det u v b := by
    have := hK.vtx_mem _ hpa _ (succ_mod_lt ha); rwa [hps] at this
  have F2 : 0 ≤ det b v w := by
    have := hK'.vtx_mem _ hpa' _ (succ_mod_lt ha'); rwa [hps', hb, hv] at this
  obtain ⟨o, ho⟩ := hK.center
  have hAo : 0 < det u v o := by have := ho _ hpa; rwa [hps] at this
  have hBo : 0 < det v b o := ho a ha
  refine ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂), fun z hz hzv => ?_⟩
  have hz₀ : dist z v < r₀ := lt_of_lt_of_le hzv (min_le_left _ _)
  have hz₁ : dist z v < r₁ := lt_of_lt_of_le hzv ((min_le_right _ _).trans (min_le_left _ _))
  have hz₂ : dist z v < r₂ := lt_of_lt_of_le hzv ((min_le_right _ _).trans (min_le_right _ _))
  have h := (hloc z (by rw [hPi, hv]; exact hz₀)).1 hz
  simp only [hprev, hPi', hPi, hPi1, hv] at h
  -- the two determinant identities
  have I1 : det u v b * det v w z = det u v z * det b v w + det v b z * det u v w := by
    unfold det; ring
  have I2 : det v b z * det u v o - det u v z * det v b o = -det u v b * det v z o := by
    unfold det; ring
  have hswap : det b v z = -det v b z := Geometry.det_swap12 v b z
  -- `K` contains the points left of `u v` and `v b`, `K'` those left of `b v` and `v w`
  have hK1 : 0 ≤ det u v z → 0 ≤ det v b z → z ∈ piece K ∪ piece K' :=
    fun h1 h2 => Or.inl (h₁ z hz₁ h1 h2)
  have hK2 : det v b z ≤ 0 → 0 ≤ det v w z → z ∈ piece K ∪ piece K' :=
    fun h1 h2 => Or.inr (h₂ z hz₂ (by rw [hswap]; linarith) h2)
  split_ifs at h with hD hD'
  · -- convex corner of `P`
    rcases le_total 0 (det v b z) with hB | hB
    · exact hK1 h.1 hB
    · exact hK2 hB h.2
  · -- reflex corner of `P`
    rcases le_total 0 (det v b z) with hB | hB
    · by_cases hA : 0 ≤ det u v z
      · exact hK1 hA hB
      · have hC : 0 ≤ det v w z := h.resolve_left hA
        rcases hB.lt_or_eq with hB' | hB'
        · exfalso
          push Not at hA
          have : det u v b * det v w z ≥ 0 := mul_nonneg F1 hC
          nlinarith [mul_nonneg (neg_nonneg.2 hA.le) F2, mul_pos hB' (neg_pos.2 hD')]
        · exact hK2 hB'.symm.le hC
    · by_cases hC : 0 ≤ det v w z
      · exact hK2 hB hC
      · push Not at hC
        have hA : 0 ≤ det u v z := h.resolve_right (not_le.2 hC)
        rcases hB.lt_or_eq with hB' | hB'
        · exfalso
          have : det u v b * det v w z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos F1 hC.le
          nlinarith [mul_nonneg hA F2, mul_pos (neg_pos.2 hB') (neg_pos.2 hD')]
        · exact hK1 hA hB'.ge
  · -- straight corner of `P`
    have hD0 : det u v w = 0 := le_antisymm (not_lt.1 hD) (not_lt.1 hD')
    rcases le_total 0 (det v b z) with hB | hB
    · exact hK1 h hB
    · rcases hB.lt_or_eq with hB' | hB'
      · rcases F1.lt_or_eq with hF1 | hF1
        · rw [hD0, mul_zero, add_zero] at I1
          have hC : 0 ≤ det v w z := by
            have := mul_nonneg h F2
            rw [← I1] at this
            exact (mul_nonneg_iff_of_pos_left hF1).1 this
          exact hK2 hB hC
        · exfalso
          rw [← hF1, neg_zero, zero_mul] at I2
          nlinarith [mul_pos (neg_pos.2 hB') hAo, mul_nonneg h hBo.le]
      · exact hK1 h hB'.symm.le

/-- The union of a central piece and its satellites. -/
def starSet (K : Polygon) {ι : Type*} (Ks : ι → Polygon) : Set Point :=
  piece K ∪ ⋃ r, piece (Ks r)

/-- The door of a star: the openings of the central piece and of the satellites. -/
def starDoor (K : Polygon) (O : ℕ → Prop) {ι : Type*} (Ks : ι → Polygon) (Os : ι → ℕ → Prop) :
    Set Point :=
  door K O ∪ ⋃ r, door (Ks r) (Os r)

/-- **Star rooms (L1.6).** Let `K` be a piece and `Ks r` (`r : ι`, finite) pieces, the side `h r`
of `Ks r` being glued to the side `g r` of `K`.  Suppose that every side of `K` is an opening
(`O`), a wall or a glued side, that every side of `Ks r` is an opening (`Os r`), a wall or the side
`h r`, and that no two glued sides of `K` are adjacent.  Then `piece K ∪ ⋃ r, piece (Ks r)` is a
room of `P` whose door is the union of the openings. -/
theorem isRoom_star (hP : P.Simple) (hL : P.InteriorLeft) {K : Polygon} (hK : IsPiece K)
    {ι : Type*} [Finite ι] {Ks : ι → Polygon} (hKs : ∀ r, IsPiece (Ks r)) {g h : ι → ℕ}
    (hglue : ∀ r, g r < K.n ∧ Glued K (Ks r) (g r) (h r)) {O : ℕ → Prop} {Os : ι → ℕ → Prop}
    (hWO : ∀ j < K.n, O j ∨ IsWall P K j ∨ ∃ r, g r = j)
    (hWOs : ∀ r, ∀ j < (Ks r).n, Os r j ∨ IsWall P (Ks r) j ∨ j = h r)
    (hadj : ∀ r r', (g r + 1) % K.n ≠ g r') :
    P.IsRoom (starSet K Ks) (starDoor K O Ks Os) := by
  have hcl : IsClosed (starSet K Ks) :=
    (isClosed_piece K).union (isClosed_iUnion_of_finite fun r => isClosed_piece (Ks r))
  have hKU : piece K ⊆ starSet K Ks := subset_union_left
  have hKsU : ∀ r, piece (Ks r) ⊆ starSet K Ks :=
    fun r => (subset_iUnion (fun r => piece (Ks r)) r).trans subset_union_right
  have hDK : door K O ⊆ starDoor K O Ks Os := subset_union_left
  have hDKs : ∀ r, door (Ks r) (Os r) ⊆ starDoor K O Ks Os :=
    fun r => (subset_iUnion (fun r => door (Ks r) (Os r)) r).trans subset_union_right
  -- the glued side of a satellite lies in the central piece
  have hside : ∀ r, (Ks r).edge (h r) ⊆ piece K := by
    intro r
    obtain ⟨hg, hh, e1, e2⟩ := hglue r
    unfold Polygon.edge
    rw [e1, e2, Geometry.segment_comm]
    exact edge_subset_piece hK hg
  refine ⟨hcl, fun y hyU hyf hyD => ?_⟩
  by_cases hyK : y ∈ piece K
  · -- the central piece, with the glued sides counted as openings
    have hWO₁ : ∀ j < K.n, (O j ∨ ∃ r, g r = j) ∨ IsWall P K j := by
      intro j hj
      rcases hWO j hj with h1 | h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
      · exact Or.inl (Or.inr h1)
    by_cases hyD₁ : y ∈ door K (fun j => O j ∨ ∃ r, g r = j)
    · obtain ⟨j, hj, hOj, hyj⟩ := hyD₁
      rcases hOj with hOj | ⟨r, rfl⟩
      · exact absurd (hDK ⟨j, hj, hOj, hyj⟩) hyD
      obtain ⟨hg, hgl⟩ := hglue r
      obtain ⟨hh, e1, e2⟩ := hgl
      have hKr := hKs r
      obtain ⟨t, ht0, ht1, hyt⟩ := hyj
      have hyt' : y = lerp (K.vtx (g r)) (K.vtx ((g r + 1) % K.n)) t := hyt
      rcases ht0.lt_or_eq with ht0' | ht0'
      · rcases ht1.lt_or_eq with ht1' | ht1'
        · -- relative interior of the glued side
          have hint := mem_interior_union_of_glued hK hKr hg ⟨hh, e1, e2⟩ ht0' ht1'
          rw [← hyt'] at hint
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hint
          refine ⟨ε, hε, fun z _ hz => ?_⟩
          rcases interior_subset (hball (mem_ball.2 hz)) with h1 | h1
          · exact hKU h1
          · exact hKsU r h1
        · -- end vertex of the glued side: fan `(Ks r, K)`
          rw [ht1', Geometry.lerp_one] at hyt'
          have hhn := hh
          have hwK : IsWall P (Ks r) (Jordan.prevIdx (Ks r) (h r)) := by
            have hpn := Jordan.prevIdx_lt (Ks r) hhn
            rcases hWOs r _ hpn with h1 | h1 | h1
            · exfalso; apply hyD; apply hDKs r
              refine ⟨_, hpn, h1, ?_⟩
              unfold Polygon.edge
              rw [prev_succ hhn, e1, ← hyt']
              exact Geometry.right_mem_segment _ _
            · exact h1
            · exfalso
              have := prev_succ (K := Ks r) hhn
              rw [h1] at this
              exact succ_mod_ne hKr hhn this
          have hwK' : IsWall P K ((g r + 1) % K.n) := by
            rcases hWO _ (succ_mod_lt hg) with h1 | h1 | ⟨r', h1⟩
            · exfalso; apply hyD; apply hDK
              exact ⟨_, succ_mod_lt hg, h1, by rw [hyt']; exact Geometry.left_mem_segment _ _⟩
            · exact h1
            · exact absurd h1.symm (hadj r r')
          obtain ⟨ε, hε, hfan⟩ := near_full_fan hP hL hKr hK hhn (succ_mod_lt hg)
            (by rw [e1]) (by rw [prev_succ_mod hg, e2]) hwK hwK'
          rw [e1, ← hyt'] at hfan
          refine ⟨ε, hε, fun z hz hzy => ?_⟩
          rcases hfan z hz hzy with h1 | h1
          · exact hKsU r h1
          · exact hKU h1
      · -- start vertex of the glued side: fan `(K, Ks r)`
        rw [← ht0', Geometry.lerp_zero] at hyt'
        have hwK : IsWall P K (Jordan.prevIdx K (g r)) := by
          have hpn := Jordan.prevIdx_lt K hg
          rcases hWO _ hpn with h1 | h1 | ⟨r', h1⟩
          · exfalso; apply hyD; apply hDK
            refine ⟨_, hpn, h1, ?_⟩
            unfold Polygon.edge
            rw [prev_succ hg, ← hyt']
            exact Geometry.right_mem_segment _ _
          · exact h1
          · exfalso
            apply hadj r' r
            rw [h1, prev_succ hg]
        have hwK' : IsWall P (Ks r) ((h r + 1) % (Ks r).n) := by
          rcases hWOs r _ (succ_mod_lt hh) with h1 | h1 | h1
          · exfalso; apply hyD; apply hDKs r
            refine ⟨_, succ_mod_lt hh, h1, ?_⟩
            unfold Polygon.edge
            rw [e2, ← hyt']
            exact Geometry.left_mem_segment _ _
          · exact h1
          · exact absurd h1 (succ_mod_ne hKr hh)
        obtain ⟨ε, hε, hfan⟩ := near_full_fan hP hL hK hKr hg (succ_mod_lt hh)
          e2 (by rw [prev_succ_mod hh, e1]) hwK hwK'
        rw [← hyt'] at hfan
        refine ⟨ε, hε, fun z hz hzy => ?_⟩
        rcases hfan z hz hzy with h1 | h1
        · exact hKU h1
        · exact hKsU r h1
    · obtain ⟨ε, hε, hball⟩ := (isRoom_piece hP hL hK hWO₁).2 y hyK hyf hyD₁
      exact ⟨ε, hε, fun z hz hzy => hKU (hball z hz hzy)⟩
  · -- a satellite, away from the central piece
    have hyU' := hyU
    rcases hyU' with h1 | h1
    · exact absurd h1 hyK
    obtain ⟨r, hyr⟩ := mem_iUnion.1 h1
    have hWO₂ : ∀ j < (Ks r).n, (Os r j ∨ j = h r) ∨ IsWall P (Ks r) j := by
      intro j hj
      rcases hWOs r j hj with h1 | h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
      · exact Or.inl (Or.inr h1)
    have hyD₂ : y ∉ door (Ks r) (fun j => Os r j ∨ j = h r) := by
      rintro ⟨j, hj, hOj, hyj⟩
      rcases hOj with hOj | rfl
      · exact hyD (hDKs r ⟨j, hj, hOj, hyj⟩)
      · exact hyK (hside r hyj)
    obtain ⟨ε, hε, hball⟩ := (isRoom_piece hP hL (hKs r) hWO₂).2 y hyr hyf hyD₂
    exact ⟨ε, hε, fun z hz hzy => hKsU r (hball z hz hzy)⟩

/-- The door of a star lies in the star. -/
theorem starDoor_subset (hK : IsPiece K) {ι : Type*} {Ks : ι → Polygon}
    (hKs : ∀ r, IsPiece (Ks r)) (O : ℕ → Prop) (Os : ι → ℕ → Prop) :
    starDoor K O Ks Os ⊆ starSet K Ks := by
  rintro y (hy | hy)
  · exact Or.inl (door_subset_piece hK O hy)
  · obtain ⟨r, hr⟩ := mem_iUnion.1 hy
    exact Or.inr (mem_iUnion.2 ⟨r, door_subset_piece (hKs r) (Os r) hr⟩)

/-- **Last exit from a star room.** Under the hypotheses of `isRoom_star`, a sight line from a
point of the star to a point outside leaves the star for the last time through its door. -/
theorem exists_last_exit_star (hP : P.Simple) (hL : P.InteriorLeft) {K : Polygon}
    (hK : IsPiece K) {ι : Type*} [Finite ι] {Ks : ι → Polygon} (hKs : ∀ r, IsPiece (Ks r))
    {g h : ι → ℕ} (hglue : ∀ r, g r < K.n ∧ Glued K (Ks r) (g r) (h r)) {O : ℕ → Prop}
    {Os : ι → ℕ → Prop} (hWO : ∀ j < K.n, O j ∨ IsWall P K j ∨ ∃ r, g r = j)
    (hWOs : ∀ r, ∀ j < (Ks r).n, Os r j ∨ IsWall P (Ks r) j ∨ j = h r)
    (hadj : ∀ r r', (g r + 1) % K.n ≠ g r') {s p : Point} (hs : s ∈ starSet K Ks)
    (hp : p ∉ starSet K Ks) (hsp : P.Sees s p) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ lerp s p τ ∈ starDoor K O Ks Os ∧
      ∀ τ' : ℝ, τ < τ' → τ' ≤ 1 → lerp s p τ' ∉ starSet K Ks :=
  exists_last_exit_of_isRoom (isRoom_star hP hL hK hKs hglue hWO hWOs hadj)
    (starDoor_subset hK hKs O Os) hs hp hsp

end ArtGallery.Stade

end
