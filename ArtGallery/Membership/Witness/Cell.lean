module

public import ArtGallery.Membership.Witness.Basic
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# The witness lemma: cells of a line arrangement

For a list `L` of lines and a point `p` on none of the (nondegenerate) lines, the *cell* of `p`
is the set of points strictly on the same side as `p` of every nondegenerate line of `L`; its
*closed cell* is the set of points weakly on the same side.

* the cell is open, convex and contains `p`; the closed cell is closed and convex and lies in the
  closure of the cell (`isOpen_cell`, `convex_cell`, `ccell_subset_closure_cell`, …);
* every extreme point of the closed cell is the intersection of two non-parallel lines of `L`
  (`exists_active_pair`);
* if the cell is bounded, the closed cell has three non-collinear extreme points
  (`exists_noncollinear_extremePoints`, by the Krein–Milman theorem);
* the centroid of three non-collinear points of the closed cell lies in the cell
  (`cen_mem_cell`).
-/

namespace ArtGallery.Membership.Witness

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp continuous_lerp lerp_zero lerp_one
  continuous_det_right)

/-- The cell of `p`: the points strictly on the side of `p` of every nondegenerate line of
`L`. -/
def cell (L : List (Point × Point)) (p : Point) : Set Point :=
  {q | ∀ ℓ ∈ L, ℓ.1 ≠ ℓ.2 → 0 < det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p}

/-- The closed cell of `p`: the points weakly on the side of `p` of every line of `L`. -/
def ccell (L : List (Point × Point)) (p : Point) : Set Point :=
  {q | ∀ ℓ ∈ L, 0 ≤ det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p}

/-- The cross product of the directions of two lines (zero iff they are parallel or one of them
is degenerate). -/
def crossDir (ℓ₁ ℓ₂ : Point × Point) : ℝ :=
  (ℓ₁.2 - ℓ₁.1).1 * (ℓ₂.2 - ℓ₂.1).2 - (ℓ₁.2 - ℓ₁.1).2 * (ℓ₂.2 - ℓ₂.1).1

variable {L : List (Point × Point)} {p : Point}

/-- The cell is open. -/
theorem isOpen_cell (L : List (Point × Point)) (p : Point) : IsOpen (cell L p) :=
  isOpen_forall_list L (fun ℓ => ℓ.1 ≠ ℓ.2) (fun ℓ q => det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p)
    fun _ => (continuous_det_right _ _).mul continuous_const

/-- The closed cell is closed. -/
theorem isClosed_ccell (L : List (Point × Point)) (p : Point) : IsClosed (ccell L p) :=
  isClosed_forall_list L (fun ℓ q => det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p)
    fun _ => (continuous_det_right _ _).mul continuous_const

/-- A convex combination of two positive numbers is positive. -/
theorem combo_pos {X Y a b : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * X + b * Y := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have : b = 1 := by linarith
    subst this
    simpa using hY
  · nlinarith [mul_nonneg hb hY.le, mul_pos h hX]

/-- The cell is convex. -/
theorem convex_cell (L : List (Point × Point)) (p : Point) : Convex ℝ (cell L p) := by
  intro x hx y hy a b ha hb hab ℓ hℓ hne
  rw [Jordan.det_combo _ _ _ _ _ _ hab]
  have hx' := hx ℓ hℓ hne
  have hy' := hy ℓ hℓ hne
  have e : (a * det ℓ.1 ℓ.2 x + b * det ℓ.1 ℓ.2 y) * det ℓ.1 ℓ.2 p =
      a * (det ℓ.1 ℓ.2 x * det ℓ.1 ℓ.2 p) + b * (det ℓ.1 ℓ.2 y * det ℓ.1 ℓ.2 p) := by ring
  rw [e]
  exact combo_pos hx' hy' ha hb hab

/-- The closed cell is convex. -/
theorem convex_ccell (L : List (Point × Point)) (p : Point) : Convex ℝ (ccell L p) := by
  intro x hx y hy a b ha hb hab ℓ hℓ
  rw [Jordan.det_combo _ _ _ _ _ _ hab]
  have hx' := hx ℓ hℓ
  have hy' := hy ℓ hℓ
  have e : (a * det ℓ.1 ℓ.2 x + b * det ℓ.1 ℓ.2 y) * det ℓ.1 ℓ.2 p =
      a * (det ℓ.1 ℓ.2 x * det ℓ.1 ℓ.2 p) + b * (det ℓ.1 ℓ.2 y * det ℓ.1 ℓ.2 p) := by ring
  rw [e]
  exact add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')

/-- A generic point lies in its own cell. -/
theorem mem_cell_self (hp : Generic L p) : p ∈ cell L p := fun ℓ hℓ hne =>
  mul_self_pos.2 (hp ℓ hℓ hne)

/-- The cell lies in the closed cell. -/
theorem cell_subset_ccell : cell L p ⊆ ccell L p := by
  intro q hq ℓ hℓ
  by_cases hne : ℓ.1 = ℓ.2
  · obtain ⟨a, b⟩ := ℓ
    simp only at hne
    subst hne
    simp
  · exact (hq ℓ hℓ hne).le

/-- Points of a closed cell are limits of points of the cell. -/
theorem ccell_subset_closure_cell (hp : Generic L p) : ccell L p ⊆ closure (cell L p) := by
  intro q hq
  have htend : Tendsto (fun t : ℝ => lerp q p t) (𝓝[>] 0) (𝓝 q) := by
    have := (continuous_lerp q p).tendsto 0
    simp only [lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht ℓ hℓ hne
  rw [det_lerp]
  have h1 := hq ℓ hℓ
  have h2 : 0 < det ℓ.1 ℓ.2 p * det ℓ.1 ℓ.2 p := mul_self_pos.2 (hp ℓ hℓ hne)
  have e : ((1 - t) * det ℓ.1 ℓ.2 q + t * det ℓ.1 ℓ.2 p) * det ℓ.1 ℓ.2 p =
      (1 - t) * (det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p) + t * (det ℓ.1 ℓ.2 p * det ℓ.1 ℓ.2 p) := by ring
  rw [e]
  have := ht.1
  have := ht.2
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) h1, mul_pos ht.1 h2]

/-- If the cell is bounded, the closed cell is compact. -/
theorem isCompact_ccell (hp : Generic L p) (hb : Bornology.IsBounded (cell L p)) :
    IsCompact (ccell L p) :=
  isCompact_of_isClosed_isBounded (isClosed_ccell L p)
    (hb.closure.subset (ccell_subset_closure_cell hp))

/-- **Extreme points are arrangement vertices.**  Every extreme point of the closed cell lies on
two non-parallel lines of `L`. -/
theorem exists_active_pair (hp : Generic L p) {e : Point} (he : e ∈ (ccell L p).extremePoints ℝ) :
    ∃ ℓ₁ ∈ L, ∃ ℓ₂ ∈ L, crossDir ℓ₁ ℓ₂ ≠ 0 ∧ det ℓ₁.1 ℓ₁.2 e = 0 ∧ det ℓ₂.1 ℓ₂.2 e = 0 := by
  by_contra hcon
  have hcon' : ∀ ℓ₁ ∈ L, ∀ ℓ₂ ∈ L, det ℓ₁.1 ℓ₁.2 e = 0 → det ℓ₂.1 ℓ₂.2 e = 0 →
      crossDir ℓ₁ ℓ₂ = 0 := by
    intro ℓ₁ h₁ ℓ₂ h₂ e₁ e₂
    by_contra hne
    exact hcon ⟨ℓ₁, h₁, ℓ₂, h₂, hne, e₁, e₂⟩
  rw [mem_extremePoints] at he
  -- a direction `d ≠ 0` along which all active lines are parallel
  obtain ⟨d, hd0, hd⟩ : ∃ d : Point, d ≠ 0 ∧ ∀ ℓ ∈ L, det ℓ.1 ℓ.2 e = 0 →
      ∀ t : ℝ, det ℓ.1 ℓ.2 (e + t • d) = 0 := by
    by_cases hact : ∃ ℓ₀ ∈ L, ℓ₀.1 ≠ ℓ₀.2 ∧ det ℓ₀.1 ℓ₀.2 e = 0
    · obtain ⟨ℓ₀, h₀, hne₀, he₀⟩ := hact
      refine ⟨ℓ₀.2 - ℓ₀.1, sub_ne_zero.2 (Ne.symm hne₀), fun ℓ hℓ heℓ t => ?_⟩
      have hc := hcon' ℓ hℓ ℓ₀ h₀ heℓ he₀
      rw [Geometry.det_add_smul, heℓ]
      unfold crossDir at hc
      unfold det
      simp only [Geometry.add_fst, Geometry.add_snd, Geometry.sub_fst, Geometry.sub_snd] at hc ⊢
      linear_combination t * hc
    · push Not at hact
      refine ⟨(1, 0), by simp [Prod.ext_iff], fun ℓ hℓ heℓ t => ?_⟩
      by_cases hne : ℓ.1 = ℓ.2
      · obtain ⟨a, b⟩ := ℓ
        simp only at hne
        subst hne
        simp
      · exact absurd heℓ (hact ℓ hℓ hne)
  -- the inactive lines stay inactive nearby
  have hO : IsOpen {q : Point | ∀ ℓ ∈ L, det ℓ.1 ℓ.2 e ≠ 0 →
      0 < det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p} :=
    isOpen_forall_list L (fun ℓ => det ℓ.1 ℓ.2 e ≠ 0) (fun ℓ q => det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p)
      fun _ => (continuous_det_right _ _).mul continuous_const
  have heO : e ∈ {q : Point | ∀ ℓ ∈ L, det ℓ.1 ℓ.2 e ≠ 0 →
      0 < det ℓ.1 ℓ.2 q * det ℓ.1 ℓ.2 p} := by
    intro ℓ hℓ hne
    have hne' : ℓ.1 ≠ ℓ.2 := by
      intro h
      apply hne
      obtain ⟨a, b⟩ := ℓ
      simp only at h
      subst h
      simp
    exact lt_of_le_of_ne (he.1 ℓ hℓ) (Ne.symm (mul_ne_zero hne (hp ℓ hℓ hne')))
  have htend : Tendsto (fun t : ℝ => e + t • d) (𝓝 0) (𝓝 e) := by
    have hc : Continuous (fun t : ℝ => e + t • d) := by fun_prop
    simpa using hc.tendsto 0
  obtain ⟨ε, hε, hεO⟩ := Metric.eventually_nhds_iff.1 (htend.eventually_mem (hO.mem_nhds heO))
  have hmem : ∀ t : ℝ, |t| < ε → e + t • d ∈ ccell L p := by
    intro t ht ℓ hℓ
    by_cases hact : det ℓ.1 ℓ.2 e = 0
    · rw [hd ℓ hℓ hact t, zero_mul]
    · have : dist t 0 < ε := by simpa [Real.dist_eq] using ht
      exact (hεO this ℓ hℓ hact).le
  have hε2 : |ε / 2| < ε := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hε2' : |-(ε / 2)| < ε := by rwa [abs_neg]
  have hseg : e ∈ openSegment ℝ (e + (ε / 2) • d) (e + (-(ε / 2)) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext <;> simp <;> ring
  have := (he.2 _ (hmem _ hε2) _ (hmem _ hε2') hseg).1
  have h0 : (ε / 2) • d = 0 := by
    have h' : e + (ε / 2) • d = e + 0 := by rw [add_zero]; exact this
    exact add_left_cancel h'
  rcases smul_eq_zero.1 h0 with h | h
  · linarith
  · exact hd0 h

/-- A closed convex set containing the extreme points of a compact convex set contains the
set. -/
theorem subset_of_extremePoints_subset {K C : Set Point} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hC : IsClosed C) (hCc : Convex ℝ C) (h : K.extremePoints ℝ ⊆ C) : K ⊆ C := by
  rw [← closure_convexHull_extremePoints hK hKc]
  exact closure_minimal (convexHull_min h hCc) hC

/-- The zero set of `det a b` is closed. -/
theorem isClosed_det_eq_zero (a b : Point) : IsClosed {x : Point | det a b x = 0} :=
  isClosed_eq (continuous_det_right a b) continuous_const

/-- The zero set of `det a b` is convex. -/
theorem convex_det_eq_zero (a b : Point) : Convex ℝ {x : Point | det a b x = 0} := by
  intro x hx y hy s t _ _ hst
  show det a b (s • x + t • y) = 0
  rw [Jordan.det_combo _ _ _ _ _ _ hst, show det a b x = 0 from hx, show det a b y = 0 from hy]
  ring

/-- **Three non-collinear extreme points.**  If the cell is bounded (and nonempty, as `p` lies
in it), the closed cell has three non-collinear extreme points. -/
theorem exists_noncollinear_extremePoints (hp : Generic L p)
    (hb : Bornology.IsBounded (cell L p)) :
    ∃ a ∈ (ccell L p).extremePoints ℝ, ∃ b ∈ (ccell L p).extremePoints ℝ,
      ∃ c ∈ (ccell L p).extremePoints ℝ, det a b c ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set E := (ccell L p).extremePoints ℝ with hE
  have hK := isCompact_ccell hp hb
  have hKc := convex_ccell L p
  have hsub : ∀ a b : Point, (∀ x ∈ E, det a b x = 0) → ∀ x ∈ ccell L p, det a b x = 0 :=
    fun a b h => subset_of_extremePoints_subset hK hKc (isClosed_det_eq_zero a b)
      (convex_det_eq_zero a b) h
  have step1 : ∀ b ∈ E, ∀ c ∈ E, ∀ x ∈ ccell L p, det b c x = 0 :=
    fun b hb c hc => hsub b c (fun x hx => hcon b hb c hc x hx)
  have step2 : ∀ c ∈ E, ∀ x ∈ ccell L p, ∀ y ∈ ccell L p, det c x y = 0 := by
    intro c hc x hx
    refine hsub c x (fun b hb => ?_)
    rw [Geometry.det_cyclic]
    exact step1 b hb c hc x hx
  have step3 : ∀ x ∈ ccell L p, ∀ y ∈ ccell L p, ∀ z ∈ ccell L p, det x y z = 0 := by
    intro x hx y hy
    refine hsub x y (fun c hc => ?_)
    rw [← Geometry.det_cyclic_right]
    exact step2 c hc x hx y hy
  -- three non-collinear points of the (open, nonempty) cell
  have hne : (cell L p).Nonempty := ⟨p, mem_cell_self hp⟩
  obtain ⟨x, hx, hx0⟩ := exists_det_ne_zero (isOpen_cell L p) hne
    (a := p) (b := p + (1, 0)) (by simp [Prod.ext_iff])
  have hpx : p ≠ x := (Geometry.ne_of_det_ne_zero hx0).2.2
  obtain ⟨z, hz, hz0⟩ := exists_det_ne_zero (isOpen_cell L p) hne hpx
  exact hz0 (step3 p (cell_subset_ccell (mem_cell_self hp)) x (cell_subset_ccell hx) z
    (cell_subset_ccell hz))

/-- **The centroid lies in the cell.**  The centroid of three non-collinear points of the closed
cell lies in the cell. -/
theorem cen_mem_cell (hp : Generic L p) {a b c : Point} (ha : a ∈ ccell L p) (hb : b ∈ ccell L p)
    (hc : c ∈ ccell L p) (habc : det a b c ≠ 0) : cen a b c ∈ cell L p := by
  intro ℓ hℓ hne
  rw [det_cen]
  have h1 := ha ℓ hℓ
  have h2 := hb ℓ hℓ
  have h3 := hc ℓ hℓ
  have e : (det ℓ.1 ℓ.2 a + det ℓ.1 ℓ.2 b + det ℓ.1 ℓ.2 c) / 3 * det ℓ.1 ℓ.2 p =
      (det ℓ.1 ℓ.2 a * det ℓ.1 ℓ.2 p + det ℓ.1 ℓ.2 b * det ℓ.1 ℓ.2 p +
        det ℓ.1 ℓ.2 c * det ℓ.1 ℓ.2 p) / 3 := by ring
  rw [e]
  by_contra hle
  push Not at hle
  have hpz := hp ℓ hℓ hne
  have z1 : det ℓ.1 ℓ.2 a * det ℓ.1 ℓ.2 p = 0 := by linarith
  have z2 : det ℓ.1 ℓ.2 b * det ℓ.1 ℓ.2 p = 0 := by linarith
  have z3 : det ℓ.1 ℓ.2 c * det ℓ.1 ℓ.2 p = 0 := by linarith
  exact habc (det_eq_zero_of_collinear hne ((mul_eq_zero.1 z1).resolve_right hpz)
    ((mul_eq_zero.1 z2).resolve_right hpz) ((mul_eq_zero.1 z3).resolve_right hpz))

end

end ArtGallery.Membership.Witness
