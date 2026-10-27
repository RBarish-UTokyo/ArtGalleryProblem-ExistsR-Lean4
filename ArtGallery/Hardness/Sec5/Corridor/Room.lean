module

public import ArtGallery.Hardness.Sec5.Corridor.NookEdge

/-!
# Section 5: corridors — the corridor is a room with two doors

Let `P` be a simple counter-clockwise polygon containing the two corridor chains of `I` as
contiguous vertex chains (`CorridorAt P I a b`: the floor chain `c0, slots…, c1` from index `a`,
the upper wall `d1, …, d0` from index `b`, indices mod `P.n`).  Then the region of the corridor
polygon `I.poly` is a **room of `P` whose door is the window `c1 d1` together with the entrance
`d0 c0`** (`Good.corridor_isRoom`): near every point of the corridor off the doors, the regions of
`P` and of `I.poly` coincide.  No hypothesis on the other edges of `P` is needed.

Consequences (`Good.sees_crosses_door`): a segment of `P` from a point outside the corridor to a
point of the corridor crosses the window or the entrance.

The local coincidence lemmas `filled_iff_near_vertex`, `filled_iff_near_edge` (two polygons sharing
the incident edges at a point) are generic.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon
open ArtGallery.Geometry (lerp)

/-! ## Local coincidence of two polygons -/

section Local

variable {P K : Polygon}

/-- Two simple counter-clockwise polygons sharing a vertex and its two incident edges coincide
near that vertex. -/
theorem filled_iff_near_vertex (hP : P.Simple) (hL : P.InteriorLeft) (hK : K.Simple)
    (hKL : K.InteriorLeft) {i k : ℕ} (hi : i < P.n) (hk : k < K.n)
    (hprev : K.vtx ((k + K.n - 1) % K.n) = P.vtx ((i + P.n - 1) % P.n))
    (hv : K.vtx k = P.vtx i) (hnext : K.vtx ((k + 1) % K.n) = P.vtx ((i + 1) % P.n)) :
    ∃ ε > 0, ∀ z : Point, dist z (P.vtx i) < ε → (z ∈ P.filled ↔ z ∈ K.filled) := by
  obtain ⟨r₁, hr₁, h₁⟩ := Vis.local_wedge hK hKL hk
  obtain ⟨r₂, hr₂, h₂⟩ := Vis.local_wedge hP hL hi
  unfold Jordan.prevIdx at h₁ h₂
  rw [hprev, hv, hnext] at h₁
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [h₂ z (lt_of_lt_of_le hz (min_le_right _ _)), h₁ z (lt_of_lt_of_le hz (min_le_left _ _))]

/-- Two simple counter-clockwise polygons sharing an edge coincide near its interior points. -/
theorem filled_iff_near_edge (hP : P.Simple) (hL : P.InteriorLeft) (hK : K.Simple)
    (hKL : K.InteriorLeft) {i k : ℕ} (hi : i < P.n) (hk : k < K.n) (hv : K.vtx k = P.vtx i)
    (hnext : K.vtx ((k + 1) % K.n) = P.vtx ((i + 1) % P.n)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ε > 0, ∀ z : Point, dist z (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t) < ε →
      (z ∈ P.filled ↔ z ∈ K.filled) := by
  obtain ⟨r₁, hr₁, h₁⟩ := Polygon.local_halfplane hK hKL hk ht0 ht1
  obtain ⟨r₂, hr₂, h₂⟩ := Polygon.local_halfplane hP hL hi ht0 ht1
  rw [hv, hnext] at h₁
  rw [← Geometry.lerp_eq_add_smul] at h₁ h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [h₂ z (lt_of_lt_of_le hz (min_le_right _ _)), h₁ z (lt_of_lt_of_le hz (min_le_left _ _))]

end Local

/-! ## Corridors inside a polygon -/

/-- The corridor chains of `I` are contiguous vertex chains of `P`: the floor chain
`c0, slots…, c1` starts at index `a`, the upper wall `d1, …, d0` at index `b` (indices mod
`P.n`). -/
structure CorridorAt (P : Polygon) (I : Input) (a b : ℕ) : Prop where
  /-- The floor chain. -/
  before : ∀ j < I.chainBefore.length,
    P.vtx ((a + j) % P.n) = ratPoint (I.chainBefore.getD j 0)
  /-- The upper wall. -/
  after : ∀ j < I.chainAfter.length, P.vtx ((b + j) % P.n) = ratPoint (I.chainAfter.getD j 0)

namespace Input

variable {I : Input} {N : ℚ}

/-- The window `c1 d1`. -/
noncomputable def window (I : Input) : Set Point :=
  ArtGallery.segment (ratPoint (c1 I.S I.H)) (ratPoint (d1 I.S I.H))

/-- The entrance `d0 c0`. -/
noncomputable def entrance (I : Input) : Set Point :=
  ArtGallery.segment (ratPoint (d0 I.S I.H)) (ratPoint (c0 I.S I.H))

/-- The doors of the corridor room. -/
noncomputable def doors (I : Input) : Set Point := I.window ∪ I.entrance

theorem poly_vtx_before {j : ℕ} (hj : j < I.chainBefore.length) :
    I.poly.vtx j = ratPoint (I.chainBefore.getD j 0) := by
  rw [poly_vtx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_left hj]
  rcases h : I.chainBefore[j]? with _ | x
  · simp at h; omega
  · simp

theorem poly_vtx_after {j : ℕ} (hj1 : I.chainBefore.length ≤ j)
    (hj2 : j < I.chainBefore.length + I.chainAfter.length) :
    I.poly.vtx j = ratPoint (I.chainAfter.getD (j - I.chainBefore.length) 0) := by
  rw [poly_vtx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_right hj1]
  rcases h : I.chainAfter[j - I.chainBefore.length]? with _ | x
  · simp at h; omega
  · simp

theorem chainBefore_length : I.chainBefore.length = I.floor.length + 2 := by
  simp [chainBefore]

theorem chainAfter_length : I.chainAfter.length = I.upper.length + 2 := by
  simp [chainAfter]

theorem chainBefore_getD_zero : I.chainBefore.getD 0 0 = c0 I.S I.H := by simp [chainBefore]

theorem chainBefore_getD_last :
    I.chainBefore.getD (I.chainBefore.length - 1) 0 = c1 I.S I.H := by
  rw [chainBefore_length]
  simp [chainBefore, List.getD_eq_getElem?_getD]

theorem chainAfter_getD_zero : I.chainAfter.getD 0 0 = d1 I.S I.H := by simp [chainAfter]

theorem chainAfter_getD_last :
    I.chainAfter.getD (I.chainAfter.length - 1) 0 = d0 I.S I.H := by
  rw [chainAfter_length]
  simp [chainAfter, List.getD_eq_getElem?_getD]

section Room

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b)
include hg hP hL hC

/-- **The corridor is a room of `P`** with the window and the entrance as door. -/
theorem Good.corridor_isRoom : P.IsRoom I.poly.filled I.doors := by
  have hK := hg.poly_simple
  have hKL := hg.poly_interiorLeft
  have hPn : 0 < P.n := by have := hP.1; omega
  set m := I.chainBefore.length with hm
  set m' := I.chainAfter.length with hm'
  have hn : I.poly.n = m + m' := by rw [poly_n, List.length_append]
  have hm2 : 2 ≤ m := by rw [hm, chainBefore_length]; omega
  have hm'2 : 2 ≤ m' := by rw [hm', chainAfter_length]; omega
  -- the index map
  have hB : ∀ j < m, I.poly.vtx j = P.vtx ((a + j) % P.n) := fun j hj => by
    rw [poly_vtx_before hj, hC.before j hj]
  have hA : ∀ j, m ≤ j → j < m + m' → I.poly.vtx j = P.vtx ((b + (j - m)) % P.n) := by
    intro j hj1 hj2
    rw [poly_vtx_after hj1 hj2, hC.after _ (by omega)]
  have hsuccK : ∀ j, j + 1 < I.poly.n → (j + 1) % I.poly.n = j + 1 :=
    fun j hj => Nat.mod_eq_of_lt hj
  have hprevK : ∀ j, 1 ≤ j → j < I.poly.n → (j + I.poly.n - 1) % I.poly.n = j - 1 := by
    intro j hj1 hj2
    rw [show j + I.poly.n - 1 = (j - 1) + I.poly.n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  -- endpoints of the doors
  have hc0 : I.poly.vtx 0 = ratPoint (c0 I.S I.H) := by
    rw [poly_vtx_before (by omega), chainBefore_getD_zero]
  have hc1 : I.poly.vtx (m - 1) = ratPoint (c1 I.S I.H) := by
    rw [poly_vtx_before (by omega), chainBefore_getD_last]
  have hd1 : I.poly.vtx m = ratPoint (d1 I.S I.H) := by
    rw [poly_vtx_after le_rfl (by omega), Nat.sub_self, chainAfter_getD_zero]
  have hd0 : I.poly.vtx (m + m' - 1) = ratPoint (d0 I.S I.H) := by
    rw [poly_vtx_after (by omega) (by omega), show m + m' - 1 - m = m' - 1 by omega,
      chainAfter_getD_last]
  have hc1D : ratPoint (c1 I.S I.H) ∈ I.doors := Or.inl (Geometry.left_mem_segment _ _)
  have hd1D : ratPoint (d1 I.S I.H) ∈ I.doors := Or.inl (Geometry.right_mem_segment _ _)
  have hd0D : ratPoint (d0 I.S I.H) ∈ I.doors := Or.inr (Geometry.left_mem_segment _ _)
  have hc0D : ratPoint (c0 I.S I.H) ∈ I.doors := Or.inr (Geometry.right_mem_segment _ _)
  -- local coincidence at chain vertices
  have hvert : ∀ j, j < I.poly.n → I.poly.vtx j ∉ I.doors →
      ∃ ε > 0, ∀ z : Point, dist z (I.poly.vtx j) < ε → (z ∈ P.filled ↔ z ∈ I.poly.filled) := by
    intro j hj hjD
    have hj0 : j ≠ 0 := by rintro rfl; exact hjD (hc0 ▸ hc0D)
    have hj1 : j ≠ m - 1 := by rintro rfl; exact hjD (hc1 ▸ hc1D)
    have hj2 : j ≠ m := by rintro rfl; exact hjD (hd1 ▸ hd1D)
    have hj3 : j ≠ m + m' - 1 := by rintro rfl; exact hjD (hd0 ▸ hd0D)
    rcases lt_or_ge j m with hjm | hjm
    · -- an interior vertex of the floor chain
      have e := hB j hjm
      rw [e] at hjD ⊢
      refine filled_iff_near_vertex hP hL hK hKL (Nat.mod_lt _ hPn) hj ?_ e ?_
      · rw [hprevK j (by omega) hj, hB (j - 1) (by omega)]
        have := chain_prev (Q := P) hPn a (j := j) (by omega)
        unfold Jordan.prevIdx at this
        rw [this]
      · rw [hsuccK j (by omega), hB (j + 1) (by omega), chain_succ]
    · -- an interior vertex of the upper wall
      have e := hA j hjm (by omega)
      rw [e] at hjD ⊢
      refine filled_iff_near_vertex hP hL hK hKL (Nat.mod_lt _ hPn) hj ?_ e ?_
      · rw [hprevK j (by omega) hj, hA (j - 1) (by omega) (by omega)]
        have := chain_prev (Q := P) hPn b (j := j - m) (by omega)
        unfold Jordan.prevIdx at this
        rw [this, show j - 1 - m = j - m - 1 by omega]
      · rw [hsuccK j (by omega), hA (j + 1) (by omega) (by omega), chain_succ,
          show j + 1 - m = j - m + 1 by omega]
  refine ⟨Jordan.isClosed_filled _, fun y hy _ hyD => ?_⟩
  by_cases hyb : y ∈ I.poly.boundary
  · obtain ⟨j, hj, τ, hτ0, hτ1, hyj⟩ := hyb
    have hyl : y = lerp (I.poly.vtx j) (I.poly.vtx ((j + 1) % I.poly.n)) τ := hyj
    -- the door edges are excluded
    have hjw : j ≠ m - 1 := by
      rintro rfl
      apply hyD; left
      rw [hsuccK _ (by omega), show m - 1 + 1 = m by omega, hc1, hd1] at hyl
      rw [hyl]; exact Geometry.lerp_mem_segment _ _ hτ0 hτ1
    have hje : j ≠ m + m' - 1 := by
      rintro rfl
      apply hyD; right
      rw [show (m + m' - 1 + 1) % I.poly.n = 0 by rw [hn, show m + m' - 1 + 1 = m + m' by omega,
        Nat.mod_self], hd0, hc0] at hyl
      rw [hyl]; exact Geometry.lerp_mem_segment _ _ hτ0 hτ1
    have fin : ∀ x : Point, (∃ ε > 0, ∀ z : Point, dist z x < ε →
        (z ∈ P.filled ↔ z ∈ I.poly.filled)) → y = x →
        ∃ ε > 0, ∀ z ∈ P.filled, dist z y < ε → z ∈ I.poly.filled := by
      rintro x ⟨ε, hε, h⟩ rfl
      exact ⟨ε, hε, fun z hz hzy => (h z hzy).1 hz⟩
    rcases hτ0.lt_or_eq with hτ0' | hτ0'
    · rcases hτ1.lt_or_eq with hτ1' | hτ1'
      · -- an interior point of a chain edge
        rcases lt_or_ge j m with hjm | hjm
        · have e0 := hB j hjm
          have e1 : I.poly.vtx ((j + 1) % I.poly.n) = P.vtx (((a + j) % P.n + 1) % P.n) := by
            rw [hsuccK j (by omega), hB (j + 1) (by omega), chain_succ]
          rw [e0, e1] at hyl
          exact fin _ (filled_iff_near_edge hP hL hK hKL (Nat.mod_lt _ hPn) hj e0 e1 hτ0' hτ1')
            hyl
        · have e0 := hA j hjm (by omega)
          have e1 : I.poly.vtx ((j + 1) % I.poly.n) = P.vtx (((b + (j - m)) % P.n + 1) % P.n) := by
            rw [hsuccK j (by omega), hA (j + 1) (by omega) (by omega), chain_succ,
              show j + 1 - m = j - m + 1 by omega]
          rw [e0, e1] at hyl
          exact fin _ (filled_iff_near_edge hP hL hK hKL (Nat.mod_lt _ hPn) hj e0 e1 hτ0' hτ1')
            hyl
      · -- the end vertex of the edge
        rw [hτ1', Geometry.lerp_one] at hyl
        have hj1 : j + 1 < I.poly.n := by omega
        rw [hsuccK j hj1] at hyl
        exact fin _ (hvert (j + 1) hj1 (by rw [← hyl]; exact hyD)) hyl
    · rw [← hτ0', Geometry.lerp_zero] at hyl
      exact fin _ (hvert j hj (by rw [← hyl]; exact hyD)) hyl
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (Jordan.isOpen_filled_sdiff_boundary hK) y
      ⟨hy, hyb⟩
    exact ⟨ε, hε, fun z _ hz => (hball hz).1⟩

/-- **Room lemma for the corridor**: a segment of `P` from a point outside the corridor to a
point of the corridor meets the window or the entrance. -/
theorem Good.sees_crosses_door {g z : Point} (hgK : g ∉ I.poly.filled) (hz : z ∈ I.poly.filled)
    (hs : P.Sees g z) : ∃ y ∈ I.doors, y ∈ ArtGallery.segment g z :=
  Polygon.sees_crosses_door (hg.corridor_isRoom hP hL hC) (R := I.poly.filled)
    (t := z) (p := g) hz hgK (Polygon.sees_comm.1 hs) |>.imp fun y ⟨hyD, hy⟩ =>
      ⟨hyD, by rw [Geometry.segment_comm]; exact hy⟩

end Room

end Input

end ArtGallery.Sec5.Corridor

end
