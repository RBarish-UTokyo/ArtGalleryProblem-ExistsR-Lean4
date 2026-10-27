module

public import ArtGallery.Hardness.BP.MainAreaRoom
public import ArtGallery.Hardness.Sec5.CoverHex

/-!
# Boundary-point variant: the main hexagon is seen by the base guards

The main hexagon `CoverM.hexSet Φ n` (corners `w_l, w_r, v_r, t_r, t_l, v_l`, unchanged from
Section 5) in a simple counter-clockwise polygon `P` that contains the closed pocket chains with
bays of all slots (`PocketAtBP`) such that no other edge meets the open box
`(a_σ.x − 6, a_σ.x + 15/2) × (0, 2)` (`BoxSepBP … 2`), as in `Sec5/CoverHex.lean`:

* `hex_subset_of`: the hexagon lies in the region if its interior meets no edge;
* `base_sees_hexBP`: a point `g` of the guard segment of slot `σ` sees every point `q` of the
  hexagon for which the segment `g q` crosses `y = 1` inside the door of slot `σ` (through the
  mouth and the bay column, `sees_columnBP`);
* `hex_coveredBP`: every point of the hexagon is seen by one of the base guards;
* `base_sees_rightBP`, `base_sees_leftBP`: every base guard sees every point of the lines `x = S`
  and `x = X_L` between `y = S` and `y = S + 3N` (the unit entrances).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Sec5 (slotX bigN two_le_bigN numC)
open ArtGallery.Sec5.CoverM (hexSet sS sTop sXL pwR pvR pvL pwL sS_big convex_hexSet
  interior_hexSet slotX_real_nonneg slotX_add_le_real cross_eq)

/-- The hypotheses on the main area for the coverage of the hexagon: the closed pocket chains of
all slots, separated up to height `2`, and the hexagon in the region. -/
structure HexHypBP (P : Polygon) (Φ : List ETRINV.Constraint) (n : ℕ) (one : ℕ → Bool)
    (start : ℕ → ℕ) : Prop where
  simple : P.Simple
  ccw : P.InteriorLeft
  pocket : ∀ σ < 4 * n, PocketAtBP P (one σ) σ (start σ)
  sep : ∀ σ < 4 * n, BoxSepBP P (one σ) σ (start σ) 2
  hex : hexSet Φ n ⊆ P.filled

variable {P : Polygon} {Φ : List ETRINV.Constraint} {n : ℕ} {one : ℕ → Bool} {start : ℕ → ℕ}

/-- **The hexagon lies in the region** if its interior meets no edge (the seed `(1/2, 3/2)` is seen
from the guard segment of slot `0`). -/
theorem hex_subset_of (hP : P.Simple) (hL : P.InteriorLeft) (hn : 0 < n)
    (hK : PocketAtBP P (one 0) 0 (start 0)) (hsep : BoxSepBP P (one 0) 0 (start 0) 2)
    (hedge : ∀ x ∈ interior (hexSet Φ n), x ∉ P.boundary) : hexSet Φ n ⊆ P.filled := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hedge' : ∀ i < P.n, Disjoint (interior (hexSet Φ n)) (P.edge i) := by
    intro i hi
    rw [Set.disjoint_left]
    intro x hx hxe
    exact hedge x hx ⟨i, hi, hxe⟩
  have hz : ((1 : ℝ) / 2, (3 : ℝ) / 2) ∈ interior (hexSet Φ n) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hN2 : (2 : ℝ) ≤ bigN n (numC Φ) := by exact_mod_cast two_le_bigN
    have hopen : IsOpen {z : Point | 0 < det (pwR n) (pvR Φ n) z ∧ 0 < det (pvL Φ n) pwL z ∧
        1 < z.2 ∧ z.2 < sTop Φ n ∧ sXL Φ n < z.1 ∧ z.1 < sS Φ n} := by
      refine (isOpen_lt continuous_const (Sec5.CoverU.continuous_det _ _)).inter
        ((isOpen_lt continuous_const (Sec5.CoverU.continuous_det _ _)).inter
        ((isOpen_lt continuous_const continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)))))
    refine interior_maximal (fun w hw => (⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.1.le,
      hw.2.2.2.2.1.le, hw.2.2.2.2.2.le⟩ : w ∈ hexSet Φ n)) hopen ?_
    simp only [mem_ofPred_eq, det, pwR, pvR, pvL, pwL, sXL, sTop]
    refine ⟨by nlinarith, by nlinarith, by norm_num, by linarith, by linarith, by linarith⟩
  have hzP : ((1 : ℝ) / 2, (3 : ℝ) / 2) ∈ P.filled := by
    have hs := sees_columnBP hP hL hK hsep (by norm_num) (g := (0, 0))
      (q := ((1 : ℝ) / 2, (3 : ℝ) / 2)) rfl
      (by norm_num [slotX]) (by norm_num [slotX]) (by norm_num [slotX]) (by norm_num [slotX])
      (by norm_num) (by norm_num)
    exact hs (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)
  exact subset_closure.trans
    (Polygon.closure_subset_filled_of_convex hP convex_hexSet hedge' hz hzP)

namespace HexHypBP

variable (hH : HexHypBP P Φ n one start)
include hH

/-- **The column of slot `σ` is seen from the guard segment** (`sees_columnBP`, `T = 2`). -/
theorem sees_col {σ : ℕ} (hσ : σ < 4 * n) {g q : Point}
    (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    (hq1 : (slotX σ : ℝ) - 6 ≤ q.1) (hq1' : q.1 ≤ slotX σ + 15 / 2) (hq2 : 1 ≤ q.2)
    (hq2' : q.2 ≤ 2) : P.Sees g q :=
  sees_columnBP hH.simple hH.ccw (hH.pocket σ hσ) (hH.sep σ hσ) (by norm_num) hg2 hg1 hg1' hq1 hq1'
    hq2 hq2'

/-! ### Base guards see the hexagon -/

/-- **A base guard sees a point of the hexagon** if the sight line crosses `y = 1` inside the door
of its pocket. -/
theorem base_sees_hexBP {σ : ℕ} (hσ : σ < 4 * n)
    {g q : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    (hq : q ∈ hexSet Φ n) (hc0 : (slotX σ : ℝ) - 6 ≤ g.1 + (q.1 - g.1) / q.2)
    (hc1 : g.1 + (q.1 - g.1) / q.2 ≤ slotX σ + 15 / 2) : P.Sees g q := by
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
  have h1 := hH.sees_col hσ hg2 hg1 hg1' (q := m) hc0 hc1 le_rfl (by norm_num)
  have h2 : P.Sees m q := Stade.sees_of_convex convex_hexSet hH.hex hmH hq
  exact Stade.sees_of_mem_segment hmseg h1 h2

/-- **Every point of the hexagon is seen by a base guard** (any guards `g σ` on the guard
segments). -/
theorem hex_coveredBP (hn : 0 < n) (g : ℕ → Point)
    (hg : ∀ σ, (g σ).2 = 0 ∧ (slotX σ : ℝ) ≤ (g σ).1 ∧ (g σ).1 ≤ slotX σ + 3 / 2) :
    ∀ q ∈ hexSet Φ n, ∃ σ < 4 * n, P.Sees (g σ) q := by
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
    refine hH.base_sees_hexBP (σ := 0) (by omega) g2 (by simp [slotX]; linarith)
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
    refine hH.base_sees_hexBP (σ := 4 * n - 1) (by omega) g2 (by rw [ea]; exact g1)
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
  refine hH.base_sees_hexBP hσn g2 (by rw [es]; exact g1) (by rw [es]; exact g1')
    ⟨d1, d2, hq2, hq2', hq3, hq4⟩ ?_ ?_ <;> rw [cross_eq hq0, ← ht, es]
  · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ (g σ).1 - (27 * σ / 2 - 6) by linarith),
      mul_nonneg ht0.le (show (0 : ℝ) ≤ q.1 - (27 * σ / 2 - 6) by linarith)]
  · nlinarith [mul_nonneg h1t (show (0 : ℝ) ≤ 27 * σ / 2 + 15 / 2 - (g σ).1 by linarith),
      mul_nonneg ht0.le (show (0 : ℝ) ≤ 27 * σ / 2 + 15 / 2 - q.1 by linarith)]

/-- **A base guard sees the right line `x = S`** between `y = S` and `y = S + 3N`. -/
theorem base_sees_rightBP (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n)
    {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    {y : ℝ} (hy1 : sS Φ n ≤ y) (hy2 : y ≤ sTop Φ n) : P.Sees g (sS Φ n, y) := by
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
  exact hH.base_sees_hexBP hσ hg2 hg1 hg1' hq (by simp only; linarith) (by simp only; linarith)

/-- **A base guard sees the left line `x = X_L`** between `y = S` and `y = S + 3N`. -/
theorem base_sees_leftBP (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n)
    {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3 / 2)
    {y : ℝ} (hy1 : sS Φ n ≤ y) (hy2 : y ≤ sTop Φ n) : P.Sees g (sXL Φ n, y) := by
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
  exact hH.base_sees_hexBP hσ hg2 hg1 hg1' hq (by simp only; linarith) (by simp only; linarith)

end HexHypBP

end ArtGallery.BP

end
