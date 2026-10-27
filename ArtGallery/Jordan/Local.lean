module

public import ArtGallery.Jordan.Filled
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local structure of the boundary of a simple polygon

* `nrm u v` is the left normal of the directed segment `u → v`, and
  `offset u v t δ = lerp u v t + δ • nrm u v` is the point at parameter `t` pushed by `δ` to the
  left (`δ > 0`) or to the right (`δ < 0`); `det u v (offset u v t δ) = δ * sqLen u v`.
* Index bookkeeping for a polygon: `prevIdx P i = (i + n - 1) % n` is the index of the edge
  entering vertex `i`.
* Consequences of simplicity: a point of an open edge lies on no other edge and is not a
  vertex (`openEdge_not_mem_other`, `openEdge_ne_vtx`); a vertex lies exactly on its two incident
  edges (`vtx_mem_edge_iff`).
* **Strip lemma** (`strip`): around a point of an open edge there is a ball in which the boundary
  is exactly the line of the edge.
* **Sector lemma** (`vertex_sector`): around a vertex, the left sides of the two incident edges
  are joined by a preconnected set avoiding the boundary, and likewise the right sides
  (`SectorSide`).

Provenance: adapted from `Chazelle/Jordan/Local.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Jordan

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp det_add_smul continuous_lerp
  exists_lerp_of_det_eq_zero det_eq_zero_of_mem_segment continuous_det_right lerp_zero lerp_one
  lerp_injective lerp_mem_segment point_ext point_ext_iff det_lerp_self)

/-! ### Normals and offset points -/

/-- The left normal of the directed segment from `u` to `v`. -/
def nrm (u v : Point) : Point := (-(v.2 - u.2), v.1 - u.1)

/-- The squared length of the segment from `u` to `v`. -/
def sqLen (u v : Point) : ℝ := (v.1 - u.1) ^ 2 + (v.2 - u.2) ^ 2

/-- The point of the line through `u, v` at parameter `t`, offset by `δ` along the left
normal: `lerp u v t + δ • nrm u v`. -/
def offset (u v : Point) (t δ : ℝ) : Point := lerp u v t + δ • nrm u v

theorem offset_fst (u v : Point) (t δ : ℝ) :
    (offset u v t δ).1 = u.1 + t * (v.1 - u.1) - δ * (v.2 - u.2) := by
  simp [offset, nrm, lerp]; ring

theorem offset_snd (u v : Point) (t δ : ℝ) :
    (offset u v t δ).2 = u.2 + t * (v.2 - u.2) + δ * (v.1 - u.1) := by
  simp [offset, nrm, lerp]

/-- The squared length of a nondegenerate segment is positive. -/
theorem sqLen_pos {u v : Point} (h : u ≠ v) : 0 < sqLen u v := by
  by_contra h'
  apply h
  unfold sqLen at h'
  rw [not_lt] at h'
  have h1 : (v.1 - u.1) ^ 2 = 0 := by nlinarith [sq_nonneg (v.1 - u.1), sq_nonneg (v.2 - u.2)]
  have h2 : (v.2 - u.2) ^ 2 = 0 := by nlinarith [sq_nonneg (v.1 - u.1), sq_nonneg (v.2 - u.2)]
  rw [pow_eq_zero_iff (by norm_num)] at h1 h2
  exact point_ext (by linarith) (by linarith)

/-- The offset point lies on the `δ`-side of the line: `det u v (offset u v t δ) = δ * sqLen`. -/
theorem det_offset (u v : Point) (t δ : ℝ) : det u v (offset u v t δ) = δ * sqLen u v := by
  unfold det offset nrm lerp sqLen; simp; ring

/-- `det p q` of an offset point in terms of the base point and the normal. -/
theorem det_offset_gen (p q u v : Point) (t δ : ℝ) :
    det p q (offset u v t δ) = det p q (lerp u v t) + δ * det p q (p + nrm u v) :=
  det_add_smul _ _ _ _ _

@[simp] theorem offset_zero (u v : Point) (t : ℝ) : offset u v t 0 = lerp u v t := by
  simp [offset]

/-- Reversing the segment exchanges the two sides. -/
theorem offset_reverse (u v : Point) (s δ : ℝ) : offset v u s δ = offset u v (1 - s) (-δ) := by
  apply point_ext <;> simp only [offset_fst, offset_snd] <;> ring

theorem continuous_offset (u v : Point) (t : ℝ) : Continuous (offset u v t) := by
  unfold offset; fun_prop

/-- If the base point lies in an open set, so do the offset points for small `δ`. -/
theorem eventually_offset_mem (σ : ℝ) {u v : Point} {t : ℝ} {W : Set Point} (hW : IsOpen W)
    (h : lerp u v t ∈ W) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t (σ * δ) ∈ W := by
  have hc : Continuous fun δ : ℝ => offset u v t (σ * δ) :=
    (continuous_offset u v t).comp (continuous_const.mul continuous_id)
  have ht : Tendsto (fun δ : ℝ => offset u v t (σ * δ)) (𝓝[>] 0) (𝓝 (lerp u v t)) := by
    have := hc.tendsto 0
    simp only [mul_zero, offset_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ht.eventually (hW.mem_nhds h)

/-- `lerp a v (1 - s) → v` as `s → 0⁺`. -/
theorem tendsto_lerp_one_sub (a v : Point) :
    Tendsto (fun s : ℝ => lerp a v (1 - s)) (𝓝[>] 0) (𝓝 v) := by
  have hc : Continuous fun s : ℝ => lerp a v (1 - s) :=
    (continuous_lerp a v).comp (continuous_const.sub continuous_id)
  have := hc.tendsto 0
  simp only [sub_zero, lerp_one] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `lerp v b s → v` as `s → 0⁺`. -/
theorem tendsto_lerp_zero (v b : Point) :
    Tendsto (fun s : ℝ => lerp v b s) (𝓝[>] 0) (𝓝 v) := by
  have := (continuous_lerp v b).tendsto 0
  simp only [lerp_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### Half-planes -/

/-- `det a b` is affine: its value at a convex combination. -/
theorem det_combo (a b x y : Point) (s t : ℝ) (hst : s + t = 1) :
    det a b (s • x + t • y) = s * det a b x + t * det a b y := by
  unfold det
  simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst, Geometry.smul_snd]
  have : t = 1 - s := by linarith
  subst this; ring

/-- An open half-plane `{0 < σ * det a b x}` is convex. -/
theorem convex_det_pos (a b : Point) (σ : ℝ) : Convex ℝ {x : Point | 0 < σ * det a b x} := by
  intro x hx y hy s t hs ht hst
  have hx' : 0 < σ * det a b x := hx
  have hy' : 0 < σ * det a b y := hy
  show 0 < σ * det a b (s • x + t • y)
  rw [det_combo a b x y s t hst]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have : t = 1 := by linarith
    subst this; simpa using hy'
  · nlinarith [mul_nonneg ht hy'.le, mul_pos h hx']

theorem isOpen_det_pos (a b : Point) (σ : ℝ) : IsOpen {x : Point | 0 < σ * det a b x} :=
  isOpen_lt continuous_const (continuous_const.mul (continuous_det_right a b))

/-- Balls of the plane: the sup-norm description. -/
theorem mem_ball_iff_abs {x q : Point} {r : ℝ} :
    x ∈ ball q r ↔ |x.1 - q.1| < r ∧ |x.2 - q.2| < r := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]

/-! ### Index bookkeeping -/

/-- The index of the edge entering vertex `i`: `(i + n - 1) % n`. -/
def prevIdx (P : Polygon) (i : ℕ) : ℕ := (i + P.n - 1) % P.n

theorem prevIdx_eq (P : Polygon) {i : ℕ} (hi : i < P.n) :
    prevIdx P i = if i = 0 then P.n - 1 else i - 1 := by
  unfold prevIdx
  split_ifs with h
  · subst h
    have : 0 + P.n - 1 = P.n - 1 := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  · have : i + P.n - 1 = (i - 1) + P.n := by omega
    rw [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem succIdx_eq (P : Polygon) {i : ℕ} (hi : i < P.n) :
    (i + 1) % P.n = if i + 1 = P.n then 0 else i + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem prevIdx_lt (P : Polygon) {i : ℕ} (hi : i < P.n) : prevIdx P i < P.n := by
  rw [prevIdx_eq P hi]; split_ifs <;> omega

theorem succIdx_lt (P : Polygon) {i : ℕ} (hi : i < P.n) : (i + 1) % P.n < P.n :=
  Nat.mod_lt _ (by omega)

/-- The edge `prevIdx P i` ends at vertex `i`. -/
theorem prevIdx_succ (P : Polygon) {i : ℕ} (hi : i < P.n) : (prevIdx P i + 1) % P.n = i := by
  rw [prevIdx_eq P hi]
  split_ifs with h
  · subst h
    have : P.n - 1 + 1 = P.n := by omega
    rw [this, Nat.mod_self]
  · have : i - 1 + 1 = i := by omega
    rw [this]; exact Nat.mod_eq_of_lt hi

theorem prevIdx_ne (P : Polygon) (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) : prevIdx P i ≠ i := by
  rw [prevIdx_eq P hi]; split_ifs <;> omega

theorem succIdx_ne (P : Polygon) (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) : (i + 1) % P.n ≠ i := by
  rw [succIdx_eq P hi]; split_ifs <;> omega

theorem prevIdx_ne_succIdx (P : Polygon) (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) :
    prevIdx P i ≠ (i + 1) % P.n := by
  rw [prevIdx_eq P hi, succIdx_eq P hi]; split_ifs <;> omega

/-- If edge `j` ends at vertex `i` then `j = prevIdx P i`. -/
theorem eq_prevIdx_of_succ (P : Polygon) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : (j + 1) % P.n = i) : j = prevIdx P i := by
  rw [succIdx_eq P hj] at h
  rw [prevIdx_eq P hi]
  split_ifs at h ⊢ <;> omega

/-- The successor index of the successor of `prevIdx` is `(i+1) % n`; convenience. -/
theorem edge_prevIdx (P : Polygon) {i : ℕ} (hi : i < P.n) :
    P.edge (prevIdx P i) = ArtGallery.segment (P.vtx (prevIdx P i)) (P.vtx i) := by
  unfold Polygon.edge; rw [prevIdx_succ P hi]

/-! ### Consequences of simplicity -/

theorem simple_three_le {P : Polygon} (hP : P.Simple) : 3 ≤ P.n := hP.1

theorem simple_vtx_inj {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.vtx i = P.vtx j) : i = j := hP.2.1 i j hi hj h

theorem simple_vtx_ne {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : i ≠ j) : P.vtx i ≠ P.vtx j := fun h' => h (simple_vtx_inj hP hi hj h')

theorem simple_edge_inter {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : i ≠ j) : P.edge i ∩ P.edge j = P.commonEndpoints i j := hP.2.2 i j hi hj h

/-- A point on two distinct edges is an endpoint of the first. -/
theorem simple_endpoint_of_mem_two {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) (h : i ≠ j) {p : Point} (hpi : p ∈ P.edge i) (hpj : p ∈ P.edge j) :
    p = P.vtx i ∨ p = P.vtx ((i + 1) % P.n) := by
  have : p ∈ P.edge i ∩ P.edge j := ⟨hpi, hpj⟩
  rw [simple_edge_inter hP hi hj h] at this
  exact this.1

/-- The two endpoints of an edge are distinct. -/
theorem simple_vtx_succ_ne {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) :
    P.vtx i ≠ P.vtx ((i + 1) % P.n) :=
  simple_vtx_ne hP hi (succIdx_lt P hi) (succIdx_ne P (simple_three_le hP) hi).symm

theorem lerp_ne_left {u v : Point} (huv : u ≠ v) {t : ℝ} (ht : 0 < t) : lerp u v t ≠ u := by
  intro h
  have h' : lerp u v t = lerp u v 0 := by rw [lerp_zero]; exact h
  exact ht.ne' (lerp_injective huv h')

theorem lerp_ne_right {u v : Point} (huv : u ≠ v) {t : ℝ} (ht : t < 1) : lerp u v t ≠ v := by
  intro h
  have h' : lerp u v t = lerp u v 1 := by rw [lerp_one]; exact h
  exact ht.ne (lerp_injective huv h')

/-- A point of the open edge `i` lies on no other edge. -/
theorem simple_openEdge_not_mem_other {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j < P.n) (hij : j ≠ i) :
    lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t ∉ P.edge j := by
  intro hmem
  have hne := simple_vtx_succ_ne hP hi
  rcases simple_endpoint_of_mem_two hP hi hj (Ne.symm hij) (lerp_mem_segment _ _ ht.1.le ht.2.le) hmem
    with h | h
  · exact lerp_ne_left hne ht.1 h
  · exact lerp_ne_right hne ht.2 h

/-- A point of the open edge `i` is not a vertex. -/
theorem simple_openEdge_ne_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j < P.n) :
    lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t ≠ P.vtx j := by
  intro h
  by_cases hij : j = i
  · subst hij
    exact lerp_ne_left (simple_vtx_succ_ne hP hi) ht.1 h
  · apply simple_openEdge_not_mem_other hP hi ht hj hij
    rw [h]
    exact Geometry.left_mem_segment _ _

/-- A vertex lies exactly on its two incident edges. -/
theorem simple_vtx_mem_edge_iff {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) : P.vtx i ∈ P.edge j ↔ j = i ∨ j = prevIdx P i := by
  constructor
  · intro h
    by_cases hij : j = i
    · exact Or.inl hij
    · right
      rcases simple_endpoint_of_mem_two hP hj hi hij h (Geometry.left_mem_segment _ _) with h' | h'
      · exact absurd (simple_vtx_inj hP hi hj h') (Ne.symm hij)
      · exact eq_prevIdx_of_succ P hi hj (simple_vtx_inj hP (succIdx_lt P hj) hi h'.symm)
  · rintro (rfl | rfl)
    · exact Geometry.left_mem_segment _ _
    · rw [edge_prevIdx P hi]
      exact Geometry.right_mem_segment _ _

/-- Every point of the boundary that is not a vertex lies on an open edge. -/
theorem exists_openEdge_of_mem_boundary (P : Polygon) {q : Point} (hq : q ∈ P.boundary)
    (hv : ∀ j, j < P.n → q ≠ P.vtx j) :
    ∃ i, i < P.n ∧ ∃ t ∈ Ioo (0 : ℝ) 1, q = lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hq
  refine ⟨i, hi, t, ⟨?_, ?_⟩, rfl⟩
  · rcases ht0.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; exact lerp_zero _ _) (hv i hi)
  · rcases ht1.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [h]; exact lerp_one _ _) (hv _ (succIdx_lt P hi))

/-- A ball around a point avoiding finitely many edges avoids them entirely. -/
theorem exists_ball_disjoint_edges (P : Polygon) (J : Finset ℕ) {q : Point}
    (hq : ∀ j ∈ J, q ∉ P.edge j) : ∃ r > 0, ∀ x ∈ ball q r, ∀ j ∈ J, x ∉ P.edge j := by
  have hc : IsClosed (⋃ j ∈ J, P.edge j) := isClosed_biUnion_finset fun j _ => isClosed_edge P j
  have hq' : q ∈ (⋃ j ∈ J, P.edge j)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact fun j hj h => hq j hj h
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hc.isOpen_compl q hq'
  refine ⟨r, hr, fun x hx j hj hxj => hsub hx ?_⟩
  simp only [mem_iUnion]
  exact ⟨j, hj, hxj⟩

/-! ### The strip lemma -/

/-- The signed projection of `x - u` on `v - u`. -/
def along (u v x : Point) : ℝ := (x.1 - u.1) * (v.1 - u.1) + (x.2 - u.2) * (v.2 - u.2)

theorem along_lerp (u v : Point) (s : ℝ) : along u v (lerp u v s) = s * sqLen u v := by
  unfold along sqLen lerp; simp; ring

theorem along_rev_lerp (u v : Point) (s : ℝ) : along v u (lerp u v s) = (1 - s) * sqLen u v := by
  unfold along sqLen lerp; simp; ring

theorem continuous_along (u v : Point) : Continuous (along u v) := by
  unfold along; fun_prop

/-- **Strip lemma.**  Around a point of the open edge `i` of a simple polygon there is a ball in
which the boundary is exactly the line through the edge. -/
theorem strip {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t₀) r,
      (x ∈ P.boundary ↔ det (P.vtx i) (P.vtx ((i + 1) % P.n)) x = 0) := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  have huv : u ≠ v := simple_vtx_succ_ne hP hi
  have hsq := sqLen_pos huv
  set q := lerp u v t₀ with hq
  -- the closed set to avoid
  set C : Set Point := (⋃ j ∈ (Finset.range P.n).erase i, P.edge j) ∪
    ({x | det u v x = 0 ∧ along u v x ≤ 0} ∪ {x | det u v x = 0 ∧ along v u x ≤ 0}) with hC
  have hCc : IsClosed C := by
    refine (isClosed_biUnion_finset fun j _ => isClosed_edge P j).union (IsClosed.union ?_ ?_)
    · exact (isClosed_eq (continuous_det_right u v) continuous_const).inter
        (isClosed_le (continuous_along u v) continuous_const)
    · exact (isClosed_eq (continuous_det_right u v) continuous_const).inter
        (isClosed_le (continuous_along v u) continuous_const)
  have hqC : q ∉ C := by
    rintro (h | h | h)
    · simp only [mem_iUnion, Finset.mem_erase, Finset.mem_range] at h
      obtain ⟨j, ⟨hji, hj⟩, hmem⟩ := h
      exact simple_openEdge_not_mem_other hP hi ht₀ hj hji hmem
    · have := h.2
      rw [hq, along_lerp] at this
      nlinarith [mul_pos ht₀.1 hsq]
    · have := h.2
      rw [hq, along_rev_lerp] at this
      nlinarith [mul_pos (sub_pos.2 ht₀.2) hsq]
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hCc.isOpen_compl q hqC
  refine ⟨r, hr, fun x hx => ?_⟩
  have hxC : x ∉ C := hsub hx
  constructor
  · rintro ⟨j, hj, hxj⟩
    by_cases hji : j = i
    · subst hji
      exact det_eq_zero_of_mem_segment hxj
    · exfalso
      apply hxC
      left
      simp only [mem_iUnion, Finset.mem_erase, Finset.mem_range]
      exact ⟨j, ⟨hji, hj⟩, hxj⟩
  · intro hdet
    obtain ⟨s, rfl⟩ := exists_lerp_of_det_eq_zero huv hdet
    have h1 : 0 < s := by
      by_contra h
      apply hxC
      right; left
      refine ⟨hdet, ?_⟩
      rw [along_lerp]
      nlinarith [not_lt.1 h]
    have h2 : s < 1 := by
      by_contra h
      apply hxC
      right; right
      refine ⟨hdet, ?_⟩
      rw [along_rev_lerp]
      nlinarith [not_lt.1 h]
    exact ⟨i, hi, lerp_mem_segment u v h1.le h2.le⟩

/-! ### The sector lemma -/

/-- `U` is a preconnected set avoiding `S` which contains, for all small `s > 0` and all small
`δ > 0`, the points of the edge `a → v` at parameter `1 - s` and of the edge `v → b` at
parameter `s`, both offset by `σ * δ` (so `σ = 1` is the left side, `σ = -1` the right side). -/
def SectorSide (S U : Set Point) (a v b : Point) (σ : ℝ) : Prop :=
  U ⊆ Sᶜ ∧ IsPreconnected U ∧
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset a v (1 - s) (σ * δ) ∈ U ∧ offset v b s (σ * δ) ∈ U

/-- Reversing the orientation exchanges the sides. -/
theorem SectorSide.reverse {S U : Set Point} {a v b : Point} {σ : ℝ}
    (h : SectorSide S U b v a σ) : SectorSide S U a v b (-σ) := by
  refine ⟨h.1, h.2.1, ?_⟩
  filter_upwards [h.2.2] with s hs
  filter_upwards [hs] with δ hδ
  rw [offset_reverse v b, offset_reverse a v] at hδ
  simp only [sub_sub_cancel, neg_mul] at hδ ⊢
  exact ⟨hδ.2, hδ.1⟩

/-- Left turn, left side: the convex sector. -/
theorem sectorSide_pos_left {a v b : Point} (h : 0 < det a v b) (hav : a ≠ v) (hvb : v ≠ b)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ ArtGallery.segment a v ∨ x ∈ ArtGallery.segment v b) :
    SectorSide S (ball v r ∩ ({x | 0 < 1 * det a v x} ∩ {x | 0 < 1 * det v b x})) a v b 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hxb, hx1, hx2⟩ hxS
    have hx1' : 0 < 1 * det a v x := hx1
    have hx2' : 0 < 1 * det v b x := hx2
    rcases hS x hxb hxS with hx | hx
    · rw [det_eq_zero_of_mem_segment hx] at hx1'; simp at hx1'
    · rw [det_eq_zero_of_mem_segment hx] at hx2'; simp at hx2'
  · exact ((convex_ball v r).inter ((convex_det_pos a v 1).inter (convex_det_pos v b 1))).isPreconnected
  · have hW1 : IsOpen (ball v r ∩ {x | 0 < 1 * det v b x}) :=
      isOpen_ball.inter (isOpen_det_pos v b 1)
    have hW2 : IsOpen (ball v r ∩ {x | 0 < 1 * det a v x}) :=
      isOpen_ball.inter (isOpen_det_pos a v 1)
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v (1 - s) ∈ ball v r ∩ {x | 0 < 1 * det v b x} := by
      filter_upwards [(tendsto_lerp_one_sub a v).eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
        self_mem_nhdsWithin] with s hs hs0
      refine ⟨hs, ?_⟩
      show 0 < 1 * det v b (lerp a v (1 - s))
      rw [det_lerp, Geometry.det_self_outer, Geometry.det_cyclic]
      have hs0' : (0 : ℝ) < s := hs0
      nlinarith [mul_pos hs0' h]
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp v b s ∈ ball v r ∩ {x | 0 < 1 * det a v x} := by
      filter_upwards [(tendsto_lerp_zero v b).eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
        self_mem_nhdsWithin] with s hs hs0
      refine ⟨hs, ?_⟩
      show 0 < 1 * det a v (lerp v b s)
      rw [det_lerp, Geometry.det_self_right]
      have hs0' : (0 : ℝ) < s := hs0
      nlinarith [mul_pos hs0' h]
    filter_upwards [h1, h2] with s hs1 hs2
    filter_upwards [eventually_offset_mem 1 hW1 hs1, eventually_offset_mem 1 hW2 hs2,
      self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine ⟨⟨hδ1.1, ?_, hδ1.2⟩, ⟨hδ2.1, hδ2.2, ?_⟩⟩
    · show 0 < 1 * det a v (offset a v (1 - s) (1 * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos hav)]
    · show 0 < 1 * det v b (offset v b s (1 * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos hvb)]

/-- The point `v + ε • ((v - a) - (b - v))` is strictly to the right of both edges of a left
turn. -/
theorem det_reflex_point (a v b : Point) (ε : ℝ) :
    det a v (v + ε • ((v - a) - (b - v))) = -(ε * det a v b) ∧
    det v b (v + ε • ((v - a) - (b - v))) = -(ε * det a v b) := by
  unfold det
  simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst, Geometry.smul_snd,
    Geometry.sub_fst, Geometry.sub_snd]
  constructor <;> ring

/-- Left turn, right side: the union of the two right half-disks. -/
theorem sectorSide_pos_right {a v b : Point} (h : 0 < det a v b) (hav : a ≠ v) (hvb : v ≠ b)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ ArtGallery.segment a v ∨ x ∈ ArtGallery.segment v b) :
    SectorSide S ((ball v r ∩ {x | 0 < (-1) * det a v x}) ∪
      (ball v r ∩ {x | 0 < (-1) * det v b x})) a v b (-1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (⟨hxb, hx⟩ | ⟨hxb, hx⟩) hxS
    · have hx' : 0 < (-1) * det a v x := hx
      rcases hS x hxb hxS with hx1 | hx1
      · rw [det_eq_zero_of_mem_segment hx1] at hx'; simp at hx'
      · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx1
        rw [det_lerp, Geometry.det_self_right] at hx'
        nlinarith [mul_nonneg ht0 h.le]
    · have hx' : 0 < (-1) * det v b x := hx
      rcases hS x hxb hxS with hx1 | hx1
      · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx1
        rw [det_lerp, Geometry.det_self_outer, Geometry.det_cyclic] at hx'
        nlinarith [mul_nonneg (sub_nonneg.2 ht1) h.le]
      · rw [det_eq_zero_of_mem_segment hx1] at hx'; simp at hx'
  · -- a common point of the two half-disks
    have ht : Tendsto (fun ε : ℝ => v + ε • ((v - a) - (b - v))) (𝓝[>] 0) (𝓝 v) := by
      have hc : Continuous fun ε : ℝ => v + ε • ((v - a) - (b - v)) := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεb, hε0⟩ :=
      (ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).and self_mem_nhdsWithin |>.exists
    have hε0' : (0 : ℝ) < ε := hε0
    obtain ⟨hd1, hd2⟩ := det_reflex_point a v b ε
    refine IsPreconnected.union (v + ε • ((v - a) - (b - v))) ⟨hεb, ?_⟩ ⟨hεb, ?_⟩
      ((convex_ball v r).inter (convex_det_pos a v (-1))).isPreconnected
      ((convex_ball v r).inter (convex_det_pos v b (-1))).isPreconnected
    · show 0 < (-1) * det a v (v + ε • ((v - a) - (b - v)))
      rw [hd1]; nlinarith [mul_pos hε0' h]
    · show 0 < (-1) * det v b (v + ε • ((v - a) - (b - v)))
      rw [hd2]; nlinarith [mul_pos hε0' h]
  · have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v (1 - s) ∈ ball v r :=
      (tendsto_lerp_one_sub a v).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp v b s ∈ ball v r :=
      (tendsto_lerp_zero v b).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [h1, h2] with s hs1 hs2
    filter_upwards [eventually_offset_mem (-1) isOpen_ball hs1,
      eventually_offset_mem (-1) isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine ⟨Or.inl ⟨hδ1, ?_⟩, Or.inr ⟨hδ2, ?_⟩⟩
    · show 0 < (-1) * det a v (offset a v (1 - s) ((-1) * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos hav)]
    · show 0 < (-1) * det v b (offset v b s ((-1) * δ))
      rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos hvb)]

/-- Straight angle: both sides are half-disks of the common line.  The hypothesis `hdir` says
that `b` lies beyond `v` on the ray from `a` through `v`. -/
theorem sectorSide_zero {a v b : Point} (h : det a v b = 0)
    (hdir : 0 < (v.1 - a.1) * (b.1 - v.1) + (v.2 - a.2) * (b.2 - v.2)) (hav : a ≠ v)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ ArtGallery.segment a v ∨ x ∈ ArtGallery.segment v b)
    {σ : ℝ} (hσ : σ ≠ 0) :
    SectorSide S (ball v r ∩ {x | 0 < σ * det a v x}) a v b σ := by
  have hnrm : det a v (a + nrm v b) =
      (v.1 - a.1) * (b.1 - v.1) + (v.2 - a.2) * (b.2 - v.2) := by
    unfold det nrm; simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hxb, hx⟩ hxS
    have hx' : 0 < σ * det a v x := hx
    rcases hS x hxb hxS with hx1 | hx1
    · rw [det_eq_zero_of_mem_segment hx1] at hx'; simp at hx'
    · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx1
      rw [det_lerp, Geometry.det_self_right, h] at hx'; simp at hx'
  · exact ((convex_ball v r).inter (convex_det_pos a v σ)).isPreconnected
  · have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v (1 - s) ∈ ball v r :=
      (tendsto_lerp_one_sub a v).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp v b s ∈ ball v r :=
      (tendsto_lerp_zero v b).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hσ2 : 0 < σ * σ := mul_self_pos.2 hσ
    filter_upwards [h1, h2] with s hs1 hs2
    filter_upwards [eventually_offset_mem σ isOpen_ball hs1,
      eventually_offset_mem σ isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine ⟨⟨hδ1, ?_⟩, ⟨hδ2, ?_⟩⟩
    · show 0 < σ * det a v (offset a v (1 - s) (σ * δ))
      rw [det_offset]
      have := mul_pos hδ0' (sqLen_pos hav)
      nlinarith [mul_pos hσ2 this]
    · show 0 < σ * det a v (offset v b s (σ * δ))
      rw [det_offset_gen, det_lerp, Geometry.det_self_right, h, hnrm]
      have := mul_pos hδ0' hdir
      nlinarith [mul_pos hσ2 this]

/-- In the collinear case, simplicity forces `b` to lie beyond `v` on the ray from `a`. -/
theorem dir_pos_of_collinear {a v b : Point} (hav : a ≠ v) (hvb : v ≠ b)
    (hmeet : ArtGallery.segment a v ∩ ArtGallery.segment v b ⊆ {v}) (h : det a v b = 0) :
    0 < (v.1 - a.1) * (b.1 - v.1) + (v.2 - a.2) * (b.2 - v.2) := by
  obtain ⟨s, rfl⟩ := exists_lerp_of_det_eq_zero hav h
  have hsq := sqLen_pos hav
  have hexpr : (v.1 - a.1) * ((lerp a v s).1 - v.1) + (v.2 - a.2) * ((lerp a v s).2 - v.2) =
      (s - 1) * sqLen a v := by
    unfold sqLen; simp [lerp]; ring
  rw [hexpr]
  have hs : 1 < s := by
    by_contra hs
    rw [not_lt] at hs
    rcases le_or_gt 0 s with h0 | h0
    · have : lerp a v s ∈ ArtGallery.segment a v ∩ ArtGallery.segment v (lerp a v s) :=
        ⟨lerp_mem_segment a v h0 hs, Geometry.right_mem_segment _ _⟩
      exact hvb (hmeet this).symm
    · have hτ : lerp v (lerp a v s) (1 / (1 - s)) = a := by
        have h1s : (1 - s) ≠ 0 := by intro h'; linarith
        apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring
      have hmem : lerp v (lerp a v s) (1 / (1 - s)) ∈ ArtGallery.segment v (lerp a v s) := by
        apply lerp_mem_segment
        · positivity
        · rw [div_le_one (by linarith)]; linarith
      rw [hτ] at hmem
      have : a ∈ ArtGallery.segment a v ∩ ArtGallery.segment v (lerp a v s) :=
        ⟨Geometry.left_mem_segment _ _, hmem⟩
      exact hav (hmeet this)
  nlinarith [mul_pos (sub_pos.2 hs) hsq]

/-- **Abstract sector lemma.**  For two nondegenerate segments `a → v → b` meeting only at `v`,
and a set `S` whose trace on a ball around `v` lies in the two segments, each side of the corner
at `v` is joined by a preconnected set avoiding `S`. -/
theorem sectorSide_exists {a v b : Point} (hav : a ≠ v) (hvb : v ≠ b)
    (hmeet : ArtGallery.segment a v ∩ ArtGallery.segment v b ⊆ {v}) {S : Set Point} {r : ℝ}
    (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ ArtGallery.segment a v ∨ x ∈ ArtGallery.segment v b)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : ∃ U, SectorSide S U a v b σ := by
  rcases lt_trichotomy (det a v b) 0 with hneg | hzero | hpos
  · have hpos' : 0 < det b v a := by rw [Geometry.det_swap13]; linarith
    have hS' : ∀ x ∈ ball v r, x ∈ S → x ∈ ArtGallery.segment b v ∨ x ∈ ArtGallery.segment v a := by
      intro x hx hxS
      rcases hS x hx hxS with h | h
      · right; rwa [Geometry.segment_comm]
      · left; rwa [Geometry.segment_comm]
    rcases hσ with rfl | rfl
    · have := (sectorSide_pos_right hpos' hvb.symm hav.symm hr hS').reverse
      rw [neg_neg] at this
      exact ⟨_, this⟩
    · exact ⟨_, (sectorSide_pos_left hpos' hvb.symm hav.symm hr hS').reverse⟩
  · exact ⟨_, sectorSide_zero hzero (dir_pos_of_collinear hav hvb hmeet hzero) hav hr hS
      (by rcases hσ with rfl | rfl <;> norm_num)⟩
  · rcases hσ with rfl | rfl
    · exact ⟨_, sectorSide_pos_left hpos hav hvb hr hS⟩
    · exact ⟨_, sectorSide_pos_right hpos hav hvb hr hS⟩

/-- **Sector lemma for a simple polygon.**  At vertex `i`, with incoming edge `prevIdx P i` (from
`a = vtx (prevIdx P i)`) and outgoing edge `i` (to `b = vtx ((i+1) % n)`), each side of the
corner is joined by a preconnected set avoiding the boundary. -/
theorem vertex_sector {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ U, SectorSide P.boundary U (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) σ := by
  have hn := simple_three_le hP
  set j := prevIdx P i with hj
  have hjn : j < P.n := prevIdx_lt P hi
  have hji : j ≠ i := prevIdx_ne P hn hi
  have hjs : j ≠ (i + 1) % P.n := prevIdx_ne_succIdx P hn hi
  have hsucc : (j + 1) % P.n = i := prevIdx_succ P hi
  have hav : P.vtx j ≠ P.vtx i := simple_vtx_ne hP hjn hi hji
  have hvb : P.vtx i ≠ P.vtx ((i + 1) % P.n) := simple_vtx_succ_ne hP hi
  have hab : P.vtx j ≠ P.vtx ((i + 1) % P.n) := simple_vtx_ne hP hjn (succIdx_lt P hi) hjs
  have hmeet : ArtGallery.segment (P.vtx j) (P.vtx i) ∩
      ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) ⊆ {P.vtx i} := by
    intro p hp
    have : p ∈ P.edge j ∩ P.edge i := by
      rw [edge_prevIdx P hi]; exact hp
    rw [simple_edge_inter hP hjn hi hji] at this
    obtain ⟨h1, h2⟩ := this
    rw [hsucc] at h1
    rcases h1 with rfl | rfl
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 hab
    · rfl
  have hother : ∀ k ∈ ((Finset.range P.n).erase i).erase j, P.vtx i ∉ P.edge k := by
    intro k hk hmem
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases (simple_vtx_mem_edge_iff hP hi hk.2.2).1 hmem with h | h
    · exact hk.2.1 h
    · exact hk.1 h
  obtain ⟨r, hr, hball⟩ := exists_ball_disjoint_edges P _ hother
  have hS : ∀ x ∈ ball (P.vtx i) r, x ∈ P.boundary →
      x ∈ ArtGallery.segment (P.vtx j) (P.vtx i) ∨
        x ∈ ArtGallery.segment (P.vtx i) (P.vtx ((i + 1) % P.n)) := by
    rintro x hx ⟨k, hk, hxk⟩
    by_cases hki : k = i
    · subst hki; exact Or.inr hxk
    · by_cases hkj : k = j
      · subst hkj
        left
        rw [← edge_prevIdx P hi]
        exact hxk
      · exact absurd hxk (hball x hx k (by simp [Finset.mem_erase, hki, hkj, hk]))
  exact sectorSide_exists hav hvb hmeet hr hS hσ

end

end ArtGallery.Jordan
