module

public import ArtGallery.Hardness.Sec5.CoverMain

/-!
# Section 5, sufficiency (vi): the main hexagon

The main hexagon `hexSet` (corners `w_l, w_r, v_r, t_r, t_l, v_l`) of the global polygon:

* `hex_subset`: it lies in the region (its interior meets no edge, `polyC_bdry`);
* `base_sees_hex`: a point `g` of the guard segment of slot `σ` sees every point `q` of the
  hexagon for which the segment `g q` crosses `y = 1` inside the door of the pocket of `σ`
  (through the mouth of the pocket, `sees_column`);
* `hex_covered`: every point of the hexagon is seen by one of the base guards;
* `base_sees_entrance_right`, `base_sees_entrance_left`: every base guard sees every point of the
  lines `x = S` and `x = X_L` between `y = S` and `y = S + 3N` (the unit entrances).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.CoverM

open ArtGallery Set Polygon
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-- The main hexagon. -/
def hexSet (Φ : List ETRINV.Constraint) (n : ℕ) : Set Point :=
  {z | 0 ≤ det (pwR n) (pvR Φ n) z ∧ 0 ≤ det (pvL Φ n) pwL z ∧ 1 ≤ z.2 ∧ z.2 ≤ sTop Φ n ∧
    sXL Φ n ≤ z.1 ∧ z.1 ≤ sS Φ n}

/-- An affine function nonnegative on a set is positive at its interior points. -/
theorem affine_pos_of_interior {C : Set Point} {α β γ : ℝ} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hC : ∀ w ∈ C, 0 ≤ α * w.1 + β * w.2 + γ) {z : Point} (hz : z ∈ interior C) :
    0 < α * z.1 + β * z.2 + γ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hz0 := hC z (interior_subset hz)
  rcases hz0.lt_or_eq with h | h
  · exact h
  exfalso
  have hn2 : 0 < α ^ 2 + β ^ 2 := by rcases hαβ with h | h <;> positivity
  set r : ℝ := ε / (2 * (|α| + |β| + 1))
  have hr : 0 < r := by positivity
  have hmem : z - r • ((α, β) : Point) ∈ interior C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    have hnn : ‖((α, β) : Point)‖ ≤ |α| + |β| := by
      rw [Prod.norm_def]
      exact max_le (by rw [Real.norm_eq_abs]; linarith [abs_nonneg β])
        (by rw [Real.norm_eq_abs]; linarith [abs_nonneg α])
    have h1 : r * ‖((α, β) : Point)‖ ≤ r * (|α| + |β|) := mul_le_mul_of_nonneg_left hnn hr.le
    have h2 : r * (|α| + |β|) < ε := by
      simp only [r]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg α, abs_nonneg β]
    linarith
  have := hC _ (interior_subset hmem)
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this
  nlinarith [mul_pos hr hn2]

theorem det_affine (a b z : Point) : det a b z =
    (-(b.2 - a.2)) * z.1 + (b.1 - a.1) * z.2 + ((b.2 - a.2) * a.1 - (b.1 - a.1) * a.2) := by
  simp only [det]; ring

theorem convex_hexSet : Convex ℝ (hexSet Φ n) := by
  have e : hexSet Φ n = {z | 0 ≤ det (pwR n) (pvR Φ n) z} ∩ {z | 0 ≤ det (pvL Φ n) pwL z} ∩
      {z : Point | 1 ≤ z.2} ∩ {z : Point | z.2 ≤ sTop Φ n} ∩ {z : Point | sXL Φ n ≤ z.1} ∩
      {z : Point | z.1 ≤ sS Φ n} := by
    ext z; simp [hexSet, and_assoc]
  rw [e]
  refine (((((CoverT.convex_halfdet _ _).inter (CoverT.convex_halfdet _ _)).inter ?_).inter ?_).inter
    ?_).inter ?_
  · exact convex_halfSpace_ge (f := fun z : Point => z.2) (by
      constructor <;> intros <;> simp) 1
  · exact convex_halfSpace_le (f := fun z : Point => z.2) (by
      constructor <;> intros <;> simp) _
  · exact convex_halfSpace_ge (f := fun z : Point => z.1) (by
      constructor <;> intros <;> simp) _
  · exact convex_halfSpace_le (f := fun z : Point => z.1) (by
      constructor <;> intros <;> simp) _

theorem isClosed_hexSet : IsClosed (hexSet Φ n) := by
  have e : hexSet Φ n = {z | 0 ≤ det (pwR n) (pvR Φ n) z} ∩ {z | 0 ≤ det (pvL Φ n) pwL z} ∩
      {z : Point | 1 ≤ z.2} ∩ {z : Point | z.2 ≤ sTop Φ n} ∩ {z : Point | sXL Φ n ≤ z.1} ∩
      {z : Point | z.1 ≤ sS Φ n} := by
    ext z; simp [hexSet, and_assoc]
  rw [e]
  refine (((((CoverT.isClosed_halfdet _ _).inter (CoverT.isClosed_halfdet _ _)).inter ?_).inter
    ?_).inter ?_).inter ?_
  · exact isClosed_le continuous_const continuous_snd
  · exact isClosed_le continuous_snd continuous_const
  · exact isClosed_le continuous_const continuous_fst
  · exact isClosed_le continuous_fst continuous_const

/-- The strict inequalities at interior points. -/
theorem interior_hexSet {z : Point} (hz : z ∈ interior (hexSet Φ n)) :
    0 < det (pwR n) (pvR Φ n) z ∧ 0 < det (pvL Φ n) pwL z ∧ 1 < z.2 ∧ z.2 < sTop Φ n ∧
      sXL Φ n < z.1 ∧ z.1 < sS Φ n := by
  have hS := sS_big (Φ := Φ) (n := n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := -((pvR Φ n).2 - (pwR n).2))
      (β := (pvR Φ n).1 - (pwR n).1)
      (γ := ((pvR Φ n).2 - (pwR n).2) * (pwR n).1 - ((pvR Φ n).1 - (pwR n).1) * (pwR n).2)
      (Or.inr (by simp [pvR, pwR]; linarith)) (fun w hw => by rw [← det_affine]; exact hw.1) hz
    rwa [← det_affine] at this
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := -(pwL.2 - (pvL Φ n).2))
      (β := pwL.1 - (pvL Φ n).1)
      (γ := (pwL.2 - (pvL Φ n).2) * (pvL Φ n).1 - (pwL.1 - (pvL Φ n).1) * (pvL Φ n).2)
      (Or.inr (by simp [pvL, pwL, sXL]; linarith)) (fun w hw => by rw [← det_affine]; exact hw.2.1)
      hz
    rwa [← det_affine] at this
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := 0) (β := 1) (γ := -1)
      (Or.inr one_ne_zero) (fun w hw => by have := hw.2.2.1; linarith) hz
    linarith
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := 0) (β := -1) (γ := sTop Φ n)
      (Or.inr (by norm_num)) (fun w hw => by have := hw.2.2.2.1; linarith) hz
    linarith
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := 1) (β := 0) (γ := -sXL Φ n)
      (Or.inl one_ne_zero) (fun w hw => by have := hw.2.2.2.2.1; linarith) hz
    linarith
  · have := affine_pos_of_interior (C := hexSet Φ n) (α := -1) (β := 0) (γ := sS Φ n)
      (Or.inl (by norm_num)) (fun w hw => by have := hw.2.2.2.2.2; linarith) hz
    linarith

/-! ### The hexagon lies in the region -/

theorem slotX_real_nonneg (σ : ℕ) : (0 : ℝ) ≤ slotX σ := by exact_mod_cast slotX_nonneg σ

/-- **The column of slot `σ` is seen from the guard segment** (`sees_column`, `T = 2`). -/
theorem sees_col (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) {g q : Point}
    (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    (hq1 : (slotX σ : ℝ) - 6 ≤ q.1) (hq1' : q.1 ≤ slotX σ + 15 / 2) (hq2 : 1 ≤ q.2)
    (hq2' : q.2 ≤ 2) : (polyC Φ n).Sees g q := by
  have hS := sS_big (Φ := Φ) (n := n)
  exact sees_column (Count.mainHyp hΦ hn).simple (Count.mainHyp hΦ hn).ccw
    ((Count.mainHyp hΦ hn).pocket σ hσ) (boxSep hΦ hn hσ (T := 2) (by linarith)) le_rfl
    hg2 hg1 hg1' hq1 hq1' hq2 hq2'

/-- A point satisfying the hexagon inequalities strictly is not on the boundary. -/
theorem strict_not_bdry (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {x : Point}
    (k1 : 0 < det (pwR n) (pvR Φ n) x) (k2 : 0 < det (pvL Φ n) pwL x) (k3 : 1 < x.2)
    (k4 : x.2 < sTop Φ n) (k5 : sXL Φ n < x.1) (k6 : x.1 < sS Φ n) :
    x ∉ (polyC Φ n).boundary := by
  intro hxe
  have hok := unitSpecs_ok hΦ
  have hS := sS_big (Φ := Φ) (n := n)
  rcases polyC_bdry hΦ hn hxe with ⟨σ, -, h⟩ | h | h | ⟨f, hf, h⟩ | h | h | ⟨f, hf, h⟩ | h
  · have := (pocket_chain_bounds _ σ x h).2.2.1; linarith
  · rw [CoverU.det_eq_zero_of_mem h] at k1; exact lt_irrefl _ k1
  · linarith [h.1]
  · have := (unit_chain_right (fun u hu => hok u (List.mem_append_left _ hu))
      (length_unitSpecs_fst n Φ) hf h).1
    linarith
  · have := (seg_bounds h).2.2.1
    simp only [ptR, ptL, min_self] at this
    linarith
  · linarith [h.1]
  · have := (unit_chain_right (fun u hu => hok u (List.mem_append_right _ hu))
      (length_unitSpecs_snd n Φ) hf h).1
    simp only [mirrorR, Vis.Cert.reflX_apply] at this
    simp only [sXL] at k5
    linarith
  · rw [CoverU.det_eq_zero_of_mem h] at k2; exact lt_irrefl _ k2

/-- **The hexagon lies in the region.** -/
theorem hex_subset (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) : hexSet Φ n ⊆ (polyC Φ n).filled := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hP := (Count.mainHyp hΦ hn).simple
  have hedge : ∀ i < (polyC Φ n).n, Disjoint (interior (hexSet Φ n)) ((polyC Φ n).edge i) := by
    intro i hi
    rw [Set.disjoint_left]
    intro x hx hxe
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := interior_hexSet hx
    exact strict_not_bdry hΦ hn k1 k2 k3 k4 k5 k6 ⟨i, hi, hxe⟩
  -- an interior point
  have hz : ((1 : ℝ) / 2, (3 : ℝ) / 2) ∈ interior (hexSet Φ n) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hN2 : (2 : ℝ) ≤ bigN n (numC Φ) := by exact_mod_cast two_le_bigN
    have hopen : IsOpen {z : Point | 0 < det (pwR n) (pvR Φ n) z ∧ 0 < det (pvL Φ n) pwL z ∧
        1 < z.2 ∧ z.2 < sTop Φ n ∧ sXL Φ n < z.1 ∧ z.1 < sS Φ n} := by
      refine (isOpen_lt continuous_const (CoverU.continuous_det _ _)).inter
        ((isOpen_lt continuous_const (CoverU.continuous_det _ _)).inter
        ((isOpen_lt continuous_const continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)))))
    refine interior_maximal (fun w hw => (⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.1.le,
      hw.2.2.2.2.1.le, hw.2.2.2.2.2.le⟩ : w ∈ hexSet Φ n)) hopen ?_
    simp only [mem_ofPred_eq, det, pwR, pvR, pvL, pwL, sXL, sTop]
    refine ⟨by nlinarith, by nlinarith, by norm_num, by linarith, by linarith, by linarith⟩
  have hzP : ((1 : ℝ) / 2, (3 : ℝ) / 2) ∈ (polyC Φ n).filled := by
    have h0 : (0 : ℕ) < 4 * n := by omega
    have hs := sees_col hΦ hn h0 (g := (0, 0)) (q := ((1 : ℝ) / 2, (3 : ℝ) / 2)) rfl
      (by norm_num [slotX]) (by norm_num [slotX]) (by norm_num [slotX]) (by norm_num [slotX])
      (by norm_num) (by norm_num)
    exact hs (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  exact subset_closure.trans (Polygon.closure_subset_filled_of_convex hP convex_hexSet hedge hz hzP)

/-! ### Base guards see the hexagon -/

/-- **A base guard sees a point of the hexagon** if the sight line crosses `y = 1` inside the door
of its pocket. -/
theorem base_sees_hex (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n)
    {g q : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    (hq : q ∈ hexSet Φ n) (hc0 : (slotX σ : ℝ) - 6 ≤ g.1 + (q.1 - g.1) / q.2)
    (hc1 : g.1 + (q.1 - g.1) / q.2 ≤ slotX σ + 15 / 2) : (polyC Φ n).Sees g q := by
  have hq2 : 1 ≤ q.2 := hq.2.2.1
  have hq0 : 0 < q.2 := by linarith
  set m : Point := (g.1 + (q.1 - g.1) / q.2, 1) with hm
  have hmseg : m ∈ ArtGallery.segment g q := by
    have : m = Geometry.lerp g q (1 / q.2) := by
      simp only [hm, Geometry.lerp, hg2]
      ext <;> simp <;> field_simp
    rw [this]
    exact Geometry.lerp_mem_segment _ _ (by positivity) (by rw [div_le_one hq0]; exact hq2)
  have hS := sS_big (Φ := Φ) (n := n)
  have hX := slotX_add_le_real (n := n) hσ
  have ha0 := slotX_real_nonneg σ
  have hmH : m ∈ hexSet Φ n := by
    have hN2 : (2 : ℝ) ≤ bigN n (numC Φ) := by exact_mod_cast two_le_bigN
    simp only [hexSet, mem_ofPred_eq, hm, det, pwR, pvR, pvL, pwL, sXL, sTop]
    refine ⟨by nlinarith, by nlinarith, le_rfl, by linarith, by linarith, by linarith⟩
  have h1 := sees_col hΦ hn hσ hg2 hg1 hg1' (q := m) hc0 hc1 le_rfl (by norm_num)
  have h2 : (polyC Φ n).Sees m q := Stade.sees_of_convex convex_hexSet (hex_subset hΦ hn) hmH hq
  exact Stade.sees_of_mem_segment hmseg h1 h2

/-- The crossing abscissa is a convex combination. -/
theorem cross_eq {g q : Point} (hq : 0 < q.2) :
    g.1 + (q.1 - g.1) / q.2 = (1 - 1 / q.2) * g.1 + (1 / q.2) * q.1 := by
  field_simp; ring

/-- **Every point of the hexagon is seen by a base guard** (any guards `g σ` on the guard
segments). -/
theorem hex_covered (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (g : ℕ → Point)
    (hg : ∀ σ, (g σ).2 = 0 ∧ (slotX σ : ℝ) ≤ (g σ).1 ∧ (g σ).1 ≤ slotX σ + 3 / 2) :
    ∀ q ∈ hexSet Φ n, ∃ σ < 4 * n, (polyC Φ n).Sees (g σ) q := by
  intro q hq
  have hS := sS_big (Φ := Φ) (n := n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨d1, d2, hq2, hq2', hq3, hq4⟩ := hq
  have hq0 : 0 < q.2 := by linarith
  set t := 1 / q.2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hq0]; exact hq2
  have htq : t * q.2 = 1 := by rw [ht]; field_simp
  by_cases hL : q.1 ≤ -6
  · -- the left triangle: slot 0
    refine ⟨0, by omega, ?_⟩
    obtain ⟨g2, g1, g1'⟩ := hg 0
    simp only [slotX, Nat.cast_zero, mul_zero, zero_div, Rat.cast_zero, zero_add] at g1 g1'
    have hw : -6 - q.1 ≤ q.2 - 1 := by
      simp only [det, pvL, pwL, sXL] at d2
      nlinarith
    have h1t : 0 ≤ 1 - t := by linarith
    refine base_sees_hex hΦ hn (σ := 0) (by omega) g2 (by simp [slotX]; linarith)
      (by simp [slotX]; linarith) ⟨d1, d2, hq2, hq2', hq3, hq4⟩ ?_ ?_ <;>
      rw [cross_eq hq0, ← ht] <;> simp only [slotX, Nat.cast_zero, mul_zero, zero_div,
        Rat.cast_zero, zero_sub, zero_add]
    · nlinarith [mul_le_mul_of_nonneg_left hw ht0.le, mul_nonneg h1t g1]
    · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ 3 / 2 - (g 0).1 by linarith),
        mul_nonneg ht0.le (show (0 : ℝ) ≤ -6 - q.1 by linarith)]
  by_cases hR : 54 * (n : ℝ) - 6 ≤ q.1
  · -- the right triangle: slot `4n − 1`
    refine ⟨4 * n - 1, by omega, ?_⟩
    obtain ⟨g2, g1, g1'⟩ := hg (4 * n - 1)
    have ea : (slotX (4 * n - 1) : ℝ) = 54 * (n : ℝ) - 27 / 2 := by
      have : ((4 * n - 1 : ℕ) : ℝ) = 4 * (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      simp only [slotX]; push_cast; rw [this]; ring
    rw [ea] at g1 g1'
    have hu : q.1 - (54 * (n : ℝ) - 6) ≤ q.2 - 1 := by
      simp only [det, pwR, pvR] at d1
      nlinarith
    have h1t : 0 ≤ 1 - t := by linarith
    refine base_sees_hex hΦ hn (σ := 4 * n - 1) (by omega) g2 (by rw [ea]; exact g1)
      (by rw [ea]; exact g1') ⟨d1, d2, hq2, hq2', hq3, hq4⟩ ?_ ?_ <;> rw [cross_eq hq0, ← ht, ea]
    · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ (g (4 * n - 1)).1 - (54 * n - 27 / 2) by linarith),
        mul_nonneg ht0.le (show (0 : ℝ) ≤ q.1 - (54 * n - 27 / 2) by linarith)]
    · nlinarith [mul_le_mul_of_nonneg_left hu ht0.le,
        mul_nonneg h1t (show (0 : ℝ) ≤ 54 * n - 6 - (g (4 * n - 1)).1 - 1 by linarith)]
  -- a column
  push Not at hL hR
  have hpos : 0 ≤ (q.1 + 6) / (27 / 2) := by apply div_nonneg <;> linarith
  obtain ⟨σ, hfl, hlt⟩ : ∃ σ : ℕ, (σ : ℝ) ≤ (q.1 + 6) / (27 / 2) ∧
      (q.1 + 6) / (27 / 2) < σ + 1 :=
    ⟨_, Nat.floor_le hpos, Nat.lt_floor_add_one _⟩
  have hσn : σ < 4 * n := by
    have : (σ : ℝ) < 4 * n := by
      calc (σ : ℝ) ≤ (q.1 + 6) / (27 / 2) := hfl
        _ < 4 * n := by rw [div_lt_iff₀ (by norm_num)]; linarith
    exact_mod_cast this
  refine ⟨σ, hσn, ?_⟩
  obtain ⟨g2, g1, g1'⟩ := hg σ
  have es : (slotX σ : ℝ) = 27 * (σ : ℝ) / 2 := by simp [slotX]
  rw [es] at g1 g1'
  have c1 : 27 * (σ : ℝ) / 2 - 6 ≤ q.1 := by
    have := hfl; rw [le_div_iff₀ (by norm_num)] at this; linarith
  have c2 : q.1 ≤ 27 * (σ : ℝ) / 2 + 15 / 2 := by
    have := hlt; rw [div_lt_iff₀ (by norm_num)] at this; linarith
  have h1t : 0 ≤ 1 - t := by linarith
  refine base_sees_hex hΦ hn hσn g2 (by rw [es]; exact g1) (by rw [es]; exact g1')
    ⟨d1, d2, hq2, hq2', hq3, hq4⟩ ?_ ?_ <;> rw [cross_eq hq0, ← ht, es]
  · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ (g σ).1 - (27 * σ / 2 - 6) by linarith),
      mul_nonneg ht0.le (show (0 : ℝ) ≤ q.1 - (27 * σ / 2 - 6) by linarith)]
  · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ 27 * σ / 2 + 15 / 2 - (g σ).1 by linarith),
      mul_nonneg ht0.le (show (0 : ℝ) ≤ 27 * σ / 2 + 15 / 2 - q.1 by linarith)]

/-- **A base guard sees the right line `x = S`** between `y = S` and `y = S + 3N`. -/
theorem base_sees_right (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n)
    {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    {y : ℝ} (hy1 : sS Φ n ≤ y) (hy2 : y ≤ sTop Φ n) : (polyC Φ n).Sees g (sS Φ n, y) := by
  have hS := sS_big (Φ := Φ) (n := n)
  have ha0 := slotX_real_nonneg σ
  have hX := slotX_add_le_real (n := n) hσ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  have hq : (sS Φ n, y) ∈ hexSet Φ n := by
    simp only [hexSet, mem_ofPred_eq, det, pwR, pvR, pvL, pwL, sXL]
    refine ⟨by nlinarith, by nlinarith, by linarith, hy2, by linarith, le_rfl⟩
  have hfrac : (sS Φ n - g.1) / y ≤ 1 := by rw [div_le_one hy0]; linarith
  have hfrac0 : 0 ≤ (sS Φ n - g.1) / y := div_nonneg (by linarith) hy0.le
  exact base_sees_hex hΦ hn hσ hg2 hg1 hg1' hq (by simp only; linarith) (by simp only; linarith)

/-- **A base guard sees the left line `x = X_L`** between `y = S` and `y = S + 3N`. -/
theorem base_sees_left (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n)
    {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    {y : ℝ} (hy1 : sS Φ n ≤ y) (hy2 : y ≤ sTop Φ n) : (polyC Φ n).Sees g (sXL Φ n, y) := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hX := slotX_add_le_real (n := n) hσ
  have ha0 := slotX_real_nonneg σ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  have hq : (sXL Φ n, y) ∈ hexSet Φ n := by
    simp only [hexSet, mem_ofPred_eq, det, pwR, pvR, pvL, pwL, sXL]
    refine ⟨by nlinarith, by nlinarith, by linarith, hy2, le_rfl, by linarith⟩
  have hfrac : -2 ≤ (sXL Φ n - g.1) / y := by
    rw [le_div_iff₀ hy0]; simp only [sXL]; linarith
  have hfrac0 : (sXL Φ n - g.1) / y ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by simp only [sXL]; linarith) hy0.le
  exact base_sees_hex hΦ hn hσ hg2 hg1 hg1' hq (by simp only; linarith) (by simp only; linarith)

end ArtGallery.Sec5.CoverM

end
