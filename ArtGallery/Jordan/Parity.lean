module

public import ArtGallery.Jordan.SegmentFacts
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Crossing parity of a point with respect to a polygon

For a point `z` and a directed edge from `u` to `v`:

* the edge **straddles** the abscissa of `z` (half-open rule) when exactly one endpoint has
  abscissa `≤ z.1`: `straddles z u v := (u.1 ≤ z.1 ∧ z.1 < v.1) ∨ (v.1 ≤ z.1 ∧ z.1 < u.1)`;
  a vertical (or degenerate) edge never straddles;
* the edge **crosses** the upward vertical ray from `z` when it straddles and `z` is strictly
  below the line through `u` and `v` at abscissa `z.1`; in division-free form, when
  `u.1 ≤ z.1 < v.1` this reads `(z.2 - u.2) * (v.1 - u.1) < (v.2 - u.2) * (z.1 - u.1)`, and
  when `v.1 ≤ z.1 < u.1` it reads the same with `u` and `v` exchanged.  `crosses` is symmetric
  in `u, v` (`crosses_comm`);
* `crossBit z u v : Bool` and `crossInd z u v : ZMod 2` are the indicator of `crosses`;
* `crossSum P z : ZMod 2` is the sum of `crossInd` over the edges of `P`, and
  `parity P z : Bool` is `crossSum P z = 1`.

Main results:

* `crossInd_eventually`: for `z ∉ segment u v`, near `z` the bit of the edge is
  `crossInd z u v + (if z'.1 < z.1 then aboveInd z u + aboveInd z v else 0)`, where
  `aboveInd z w` indicates that `w` has abscissa `z.1` and lies strictly above `z`.  So the bit
  is right-continuous everywhere off the edge, and moving to the left across the abscissa of an
  endpoint changes it exactly when that endpoint is above `z`.
* `crossSum_eventually_eq` / `parity_eventually_eq`: off the boundary the parity is locally
  constant (the endpoint contributions telescope around the closed walk).
* `continuousOn_parity`, `parity_eq_of_isPreconnected`: constancy on preconnected subsets of the
  complement of the boundary.
* `parity_flip`: crossing a non-vertical edge at a non-vertex point lying on no other edge
  flips the parity.
* `crossSum_eq_zero_of_far` / `parity_eq_false_of_far`: far away the parity is `false`.

Provenance: adapted from `Chazelle/Jordan/Parity.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Jordan

@[expose] public section

open Set Filter Topology

/-! ### Definitions -/

/-- The edge `u v` straddles the abscissa of `z` (half-open rule): exactly one endpoint has
abscissa `≤ z.1`. -/
def straddles (z u v : Point) : Prop :=
  (u.1 ≤ z.1 ∧ z.1 < v.1) ∨ (v.1 ≤ z.1 ∧ z.1 < u.1)

/-- The edge `u v` crosses the upward vertical ray from `z`: it straddles the abscissa of `z`
and `z` is strictly below the line through `u` and `v` at abscissa `z.1` (division-free form,
oriented left to right). -/
def crosses (z u v : Point) : Prop :=
  (u.1 ≤ z.1 ∧ z.1 < v.1 ∧ (z.2 - u.2) * (v.1 - u.1) < (v.2 - u.2) * (z.1 - u.1)) ∨
  (v.1 ≤ z.1 ∧ z.1 < u.1 ∧ (z.2 - v.2) * (u.1 - v.1) < (u.2 - v.2) * (z.1 - v.1))

noncomputable instance instDecidableStraddles (z u v : Point) : Decidable (straddles z u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

noncomputable instance instDecidableCrosses (z u v : Point) : Decidable (crosses z u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The crossing bit of the edge `u v` at `z`. -/
noncomputable def crossBit (z u v : Point) : Bool := decide (crosses z u v)

/-- The crossing indicator of the edge `u v` at `z`, in `ZMod 2`. -/
noncomputable def crossInd (z u v : Point) : ZMod 2 := if crosses z u v then 1 else 0

/-- Indicator (in `ZMod 2`) that the point `w` has the abscissa of `z` and lies strictly above
`z`.  This is the change of the crossing bit of an edge with endpoint `w` when the test point
moves to the left across the abscissa of `w`. -/
noncomputable def aboveInd (z w : Point) : ZMod 2 := if w.1 = z.1 ∧ z.2 < w.2 then 1 else 0

/-- The number of edges of `P` crossing the upward ray from `z`, modulo 2. -/
noncomputable def crossSum (P : Polygon) (z : Point) : ZMod 2 :=
  ∑ i ∈ Finset.range P.n, crossInd z (P.vtx i) (P.vtx ((i + 1) % P.n))

/-- The crossing parity of `z` with respect to `P`: `true` iff an odd number of edges cross
the upward ray from `z`. -/
noncomputable def parity (P : Polygon) (z : Point) : Bool := decide (crossSum P z = 1)

/-! ### Basic lemmas -/

theorem straddles_comm {z u v : Point} : straddles z u v ↔ straddles z v u :=
  Or.comm

/-- `crosses` does not depend on the direction of the edge. -/
theorem crosses_comm {z u v : Point} : crosses z u v ↔ crosses z v u :=
  Or.comm

theorem crosses_straddles {z u v : Point} (h : crosses z u v) : straddles z u v := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- For an edge oriented left to right, `crosses` reduces to its first disjunct. -/
theorem crosses_iff_of_lt {z u v : Point} (huv : u.1 < v.1) :
    crosses z u v ↔
      u.1 ≤ z.1 ∧ z.1 < v.1 ∧ (z.2 - u.2) * (v.1 - u.1) < (v.2 - u.2) * (z.1 - u.1) := by
  constructor
  · rintro (h | ⟨h1, h2, -⟩)
    · exact h
    · exact absurd (h1.trans_lt h2) (not_lt.2 huv.le)
  · exact Or.inl

/-- `crosses` in terms of `det`: when `u.1 ≤ z.1 < v.1` the edge crosses iff `det u v z < 0`. -/
theorem crosses_iff_det_of_lt {z u v : Point} (huv : u.1 < v.1) :
    crosses z u v ↔ u.1 ≤ z.1 ∧ z.1 < v.1 ∧ det u v z < 0 := by
  rw [crosses_iff_of_lt huv]
  unfold det
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by nlinarith⟩

/-- A vertical (or degenerate) edge never crosses. -/
theorem not_crosses_of_eq {z u v : Point} (huv : u.1 = v.1) : ¬ crosses z u v := by
  rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> linarith

/-- An edge entirely to the right of `z` does not cross. -/
theorem not_crosses_of_lt {z u v : Point} (hu : z.1 < u.1) (hv : z.1 < v.1) :
    ¬ crosses z u v := by
  rintro (⟨h1, -, -⟩ | ⟨h1, -, -⟩) <;> linarith

/-- An edge entirely at or to the left of `z` does not cross. -/
theorem not_crosses_of_le {z u v : Point} (hu : u.1 ≤ z.1) (hv : v.1 ≤ z.1) :
    ¬ crosses z u v := by
  rintro (⟨-, h2, -⟩ | ⟨-, h2, -⟩) <;> linarith

/-- An edge entirely strictly below `z` does not cross. -/
theorem not_crosses_of_below {z u v : Point} (hu : u.2 < z.2) (hv : v.2 < z.2) :
    ¬ crosses z u v := by
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · nlinarith [mul_pos (sub_pos.2 hu) (sub_pos.2 h2), mul_nonneg (sub_pos.2 hv).le (sub_nonneg.2 h1)]
  · nlinarith [mul_pos (sub_pos.2 hv) (sub_pos.2 h2), mul_nonneg (sub_pos.2 hu).le (sub_nonneg.2 h1)]

@[simp] theorem crossBit_eq_true_iff {z u v : Point} : crossBit z u v = true ↔ crosses z u v := by
  simp [crossBit]

@[simp] theorem crossBit_eq_false_iff {z u v : Point} :
    crossBit z u v = false ↔ ¬ crosses z u v := by
  simp [crossBit]

theorem crossBit_comm {z u v : Point} : crossBit z u v = crossBit z v u := by
  simp only [crossBit]
  exact decide_eq_decide.2 crosses_comm

theorem crossInd_eq_ite_crossBit {z u v : Point} :
    crossInd z u v = if crossBit z u v then 1 else 0 := by
  simp [crossInd, crossBit]

theorem crossInd_comm {z u v : Point} : crossInd z u v = crossInd z v u := by
  simp only [crossInd]
  exact if_congr crosses_comm rfl rfl

theorem crossInd_of_crosses {z u v : Point} (h : crosses z u v) : crossInd z u v = 1 :=
  ite_eq_left h

theorem crossInd_of_not_crosses {z u v : Point} (h : ¬ crosses z u v) : crossInd z u v = 0 :=
  ite_eq_right h

@[simp] theorem crossInd_eq_one_iff {z u v : Point} : crossInd z u v = 1 ↔ crosses z u v := by
  unfold crossInd; split_ifs with h <;> simp [h]

@[simp] theorem crossInd_eq_zero_iff {z u v : Point} : crossInd z u v = 0 ↔ ¬ crosses z u v := by
  unfold crossInd; split_ifs with h <;> simp [h]

theorem aboveInd_of_ne {z w : Point} (h : w.1 ≠ z.1) : aboveInd z w = 0 := by
  simp [aboveInd, h]

theorem aboveInd_of_le {z w : Point} (h : w.2 ≤ z.2) : aboveInd z w = 0 := by
  simp [aboveInd, not_lt.2 h]

theorem aboveInd_of_lt {z w : Point} (h1 : w.1 = z.1) (h2 : z.2 < w.2) : aboveInd z w = 1 := by
  simp [aboveInd, h1, h2]

theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

theorem zmod_two_add_one_ne (x : ZMod 2) : x + 1 ≠ x := by
  revert x; decide

theorem zmod_two_decide_eq_one_iff (a b : ZMod 2) :
    (decide (a = 1) = decide (b = 1)) ↔ a = b := by
  revert a b; decide

/-- Two points have the same parity iff they have the same crossing sum. -/
theorem parity_eq_iff {P : Polygon} {z z' : Point} :
    parity P z = parity P z' ↔ crossSum P z = crossSum P z' :=
  zmod_two_decide_eq_one_iff _ _

theorem parity_eq_true_iff {P : Polygon} {z : Point} : parity P z = true ↔ crossSum P z = 1 := by
  simp [parity]

theorem parity_eq_false_iff {P : Polygon} {z : Point} :
    parity P z = false ↔ crossSum P z = 0 := by
  simp only [parity, decide_eq_false_iff_not]
  generalize crossSum P z = a
  revert a
  decide

/-- The crossing sum with the crossing bits. -/
theorem crossSum_eq_sum_crossBit (P : Polygon) (z : Point) :
    crossSum P z =
      ∑ i ∈ Finset.range P.n,
        (if crossBit z (P.vtx i) (P.vtx ((i + 1) % P.n)) then (1 : ZMod 2) else 0) := by
  unfold crossSum
  exact Finset.sum_congr rfl fun i _ => crossInd_eq_ite_crossBit

/-! ### Local behaviour of a single edge -/

/-- For a vertical edge and a point off it, the two endpoint contributions cancel. -/
theorem aboveInd_add_aboveInd_of_eq {z u v : Point} (huv : u.1 = v.1) (hz : z ∉ segment u v) :
    aboveInd z u + aboveInd z v = 0 := by
  by_cases hu : u.1 = z.1
  · have hv : v.1 = z.1 := huv ▸ hu
    by_cases h1 : z.2 < u.2 <;> by_cases h2 : z.2 < v.2
    · rw [aboveInd_of_lt hu h1, aboveInd_of_lt hv h2]; decide
    · exact absurd (mem_segment_of_vertical huv.symm hv.symm (not_lt.1 h2) h1.le)
        (segment_comm u v ▸ hz)
    · exact absurd (mem_segment_of_vertical huv hu.symm (not_lt.1 h1) h2.le) hz
    · rw [aboveInd_of_le (not_lt.1 h1), aboveInd_of_le (not_lt.1 h2)]; decide
  · rw [aboveInd_of_ne hu, aboveInd_of_ne (huv ▸ hu)]; decide

/-- The affine function whose sign decides "below the line through `u` and `v`". -/
theorem continuous_lineFun (u v : Point) :
    Continuous fun z' : Point => (z'.2 - u.2) * (v.1 - u.1) - (v.2 - u.2) * (z'.1 - u.1) := by
  fun_prop

/-- Local behaviour of the crossing indicator of a left-to-right edge near a point off it. -/
theorem crossInd_eventually_of_lt {z u v : Point} (huv : u.1 < v.1) (hz : z ∉ segment u v) :
    ∀ᶠ z' in 𝓝 z, crossInd z' u v =
      crossInd z u v + if z'.1 < z.1 then aboveInd z u + aboveInd z v else 0 := by
  set L : Point → ℝ := fun z' => (z'.2 - u.2) * (v.1 - u.1) - (v.2 - u.2) * (z'.1 - u.1) with hL
  have hLc : Continuous L := continuous_lineFun u v
  have hLt : Tendsto L (𝓝 z) (𝓝 (L z)) := hLc.tendsto z
  have hfst : Tendsto (fun z' : Point => z'.1) (𝓝 z) (𝓝 z.1) := continuous_fst.tendsto z
  have hcr : ∀ z' : Point, crosses z' u v ↔ u.1 ≤ z'.1 ∧ z'.1 < v.1 ∧ L z' < 0 := by
    intro z'
    rw [crosses_iff_of_lt huv]
    simp only [hL, sub_neg]
  have hvz : v.1 ≠ u.1 := huv.ne'
  rcases lt_trichotomy z.1 u.1 with hA | hB | hC
  · -- z strictly to the left of the edge
    filter_upwards [hfst.eventually_lt_const hA] with z' hz'
    rw [crossInd_of_not_crosses (not_crosses_of_lt hz' (hz'.trans huv)),
      crossInd_of_not_crosses (not_crosses_of_lt hA (hA.trans huv)),
      aboveInd_of_ne hA.ne', aboveInd_of_ne (hA.trans huv).ne']
    simp
  · -- z on the abscissa of u
    have hzu2 : z.2 ≠ u.2 := by
      intro h
      apply hz
      have : z = u := Prod.ext hB h
      rw [this]; exact left_mem_segment u v
    have hLz : L z = (z.2 - u.2) * (v.1 - u.1) := by simp [hL, hB]
    have hd : 0 < v.1 - u.1 := sub_pos.2 huv
    have hav : aboveInd z v = 0 := aboveInd_of_ne (by rw [hB]; exact hvz)
    rcases lt_or_gt_of_ne hzu2 with h1 | h1
    · -- u above z: the bit is 1 at and to the right of z, 0 to the left
      have hLneg : L z < 0 := by rw [hLz]; exact mul_neg_of_neg_of_pos (sub_neg.2 h1) hd
      have hau : aboveInd z u = 1 := aboveInd_of_lt hB.symm h1
      have hcz : crosses z u v := (hcr z).2 ⟨hB.ge, hB ▸ huv, hLneg⟩
      filter_upwards [hfst.eventually_lt_const (hB ▸ huv), hLt.eventually_lt_const hLneg]
        with z' hz'1 hz'2
      rw [crossInd_of_crosses hcz, hau, hav]
      by_cases hlt : z'.1 < z.1
      · rw [crossInd_of_not_crosses (fun h => absurd ((hcr z').1 h).1 (not_le.2 (hB ▸ hlt))),
          ite_eq_left hlt]
        decide
      · rw [crossInd_of_crosses ((hcr z').2 ⟨hB ▸ not_lt.1 hlt, hz'1, hz'2⟩), ite_eq_right hlt]
        decide
    · -- u below z: the bit is 0 near z
      have hLpos : 0 < L z := by rw [hLz]; exact mul_pos (sub_pos.2 h1) hd
      have hau : aboveInd z u = 0 := aboveInd_of_le h1.le
      filter_upwards [hLt.eventually_const_lt hLpos] with z' hz'
      rw [crossInd_of_not_crosses (fun h => absurd ((hcr z').1 h).2.2 (not_lt.2 hz'.le)),
        crossInd_of_not_crosses (fun h => absurd ((hcr z).1 h).2.2 (not_lt.2 hLpos.le)),
        hau, hav]
      simp
  · rcases lt_trichotomy z.1 v.1 with hC1 | hD | hE
    · -- strictly between the abscissae of the endpoints
      have hLz : L z ≠ 0 := by
        intro h
        apply hz
        rw [mem_segment_iff_of_lt huv]
        exact ⟨hC.le, hC1.le, by simpa [hL, sub_eq_zero] using h⟩
      have hau : aboveInd z u = 0 := aboveInd_of_ne hC.ne
      have hav : aboveInd z v = 0 := aboveInd_of_ne hC1.ne'
      rw [hau, hav]
      rcases lt_or_gt_of_ne hLz with h1 | h1
      · filter_upwards [hfst.eventually_const_lt hC, hfst.eventually_lt_const hC1,
          hLt.eventually_lt_const h1] with z' hz'1 hz'2 hz'3
        rw [crossInd_of_crosses ((hcr z').2 ⟨hz'1.le, hz'2, hz'3⟩),
          crossInd_of_crosses ((hcr z).2 ⟨hC.le, hC1, h1⟩)]
        simp
      · filter_upwards [hLt.eventually_const_lt h1] with z' hz'
        rw [crossInd_of_not_crosses (fun h => absurd ((hcr z').1 h).2.2 (not_lt.2 hz'.le)),
          crossInd_of_not_crosses (fun h => absurd ((hcr z).1 h).2.2 (not_lt.2 h1.le))]
        simp
    · -- z on the abscissa of v
      have hzv2 : z.2 ≠ v.2 := by
        intro h
        apply hz
        have : z = v := Prod.ext hD h
        rw [this]; exact right_mem_segment u v
      have hLz : L z = (z.2 - v.2) * (v.1 - u.1) := by simp only [hL]; rw [hD]; ring
      have hd : 0 < v.1 - u.1 := sub_pos.2 huv
      have hau : aboveInd z u = 0 := aboveInd_of_ne (by rw [hD]; exact hvz.symm)
      have hcz : ¬ crosses z u v := fun h => absurd ((hcr z).1 h).2.1 (not_lt.2 hD.ge)
      rcases lt_or_gt_of_ne hzv2 with h1 | h1
      · -- v above z: the bit is 1 to the left of z, 0 at and to the right
        have hLneg : L z < 0 := by rw [hLz]; exact mul_neg_of_neg_of_pos (sub_neg.2 h1) hd
        have hav : aboveInd z v = 1 := aboveInd_of_lt hD.symm h1
        filter_upwards [hfst.eventually_const_lt hC, hLt.eventually_lt_const hLneg]
          with z' hz'1 hz'2
        rw [crossInd_of_not_crosses hcz, hau, hav]
        by_cases hlt : z'.1 < z.1
        · rw [crossInd_of_crosses ((hcr z').2 ⟨hz'1.le, hD ▸ hlt, hz'2⟩), ite_eq_left hlt]
          decide
        · rw [crossInd_of_not_crosses (fun h => absurd ((hcr z').1 h).2.1 (hD ▸ hlt)),
            ite_eq_right hlt]
          decide
      · -- v below z: the bit is 0 near z
        have hLpos : 0 < L z := by rw [hLz]; exact mul_pos (sub_pos.2 h1) hd
        have hav : aboveInd z v = 0 := aboveInd_of_le h1.le
        filter_upwards [hLt.eventually_const_lt hLpos] with z' hz'
        rw [crossInd_of_not_crosses (fun h => absurd ((hcr z').1 h).2.2 (not_lt.2 hz'.le)),
          crossInd_of_not_crosses hcz, hau, hav]
        simp
    · -- z strictly to the right of the edge
      filter_upwards [hfst.eventually_const_lt hE] with z' hz'
      rw [crossInd_of_not_crosses (not_crosses_of_le (huv.trans hz').le hz'.le),
        crossInd_of_not_crosses (not_crosses_of_le hC.le hE.le),
        aboveInd_of_ne hC.ne, aboveInd_of_ne hE.ne]
      simp

/-- **Local behaviour of one edge.**  For `z` off the edge `u v`, the crossing indicator at a
nearby point `z'` is the indicator at `z`, plus, when `z'` is strictly to the left of `z`,
the number (mod 2) of endpoints of the edge that have abscissa `z.1` and lie above `z`.  In
particular the bit is unchanged to the right of `z` and above/below `z`. -/
theorem crossInd_eventually {z u v : Point} (hz : z ∉ segment u v) :
    ∀ᶠ z' in 𝓝 z, crossInd z' u v =
      crossInd z u v + if z'.1 < z.1 then aboveInd z u + aboveInd z v else 0 := by
  rcases lt_trichotomy u.1 v.1 with h | h | h
  · exact crossInd_eventually_of_lt h hz
  · have h0 : aboveInd z u + aboveInd z v = 0 := aboveInd_add_aboveInd_of_eq h hz
    filter_upwards with z'
    rw [crossInd_of_not_crosses (not_crosses_of_eq h), crossInd_of_not_crosses (not_crosses_of_eq h),
      h0]
    simp
  · have hz' : z ∉ segment v u := segment_comm u v ▸ hz
    filter_upwards [crossInd_eventually_of_lt h hz'] with z' hz'
    rw [crossInd_comm, hz', ← crossInd_comm, add_comm (aboveInd z v)]

/-- (a) Off the edge and away from the abscissae of its endpoints, the crossing bit is
locally constant. -/
theorem crossBit_locally_constant_of_abscissa_ne {z u v : Point} (hz : z ∉ segment u v)
    (hu : z.1 ≠ u.1) (hv : z.1 ≠ v.1) :
    ∀ᶠ z' in 𝓝 z, crossBit z' u v = crossBit z u v := by
  filter_upwards [crossInd_eventually hz] with z' hz'
  rw [aboveInd_of_ne hu.symm, aboveInd_of_ne hv.symm, add_zero, ite_self, add_zero] at hz'
  rw [crossInd_eq_ite_crossBit, crossInd_eq_ite_crossBit] at hz'
  revert hz'
  cases crossBit z' u v <;> cases crossBit z u v <;> decide

/-- (b, right limit) The crossing bit is right-continuous in the abscissa: for `z` off the edge
and small `ε > 0`, the bit at `(z.1 + ε, z.2)` equals the bit at `z`. -/
theorem crossInd_right_limit {z u v : Point} (hz : z ∉ segment u v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), crossInd (z.1 + ε, z.2) u v = crossInd z u v := by
  have ht : Tendsto (fun ε : ℝ => ((z.1 + ε, z.2) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1 + ε, z.2) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  filter_upwards [ht.eventually (crossInd_eventually hz), self_mem_nhdsWithin] with ε hε hε0
  have hlt : ¬ (((z.1 + ε, z.2) : Point).1 < z.1) := by
    show ¬ (z.1 + ε < z.1); linarith [mem_Ioi.1 hε0]
  rw [hε, ite_eq_right hlt, add_zero]

/-- (b, left limit) For `z` off the edge and small `ε > 0`, the bit at `(z.1 - ε, z.2)` is the
bit at `z` plus the contributions of the endpoints of abscissa `z.1` lying above `z`. -/
theorem crossInd_left_limit {z u v : Point} (hz : z ∉ segment u v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      crossInd (z.1 - ε, z.2) u v = crossInd z u v + aboveInd z u + aboveInd z v := by
  have ht : Tendsto (fun ε : ℝ => ((z.1 - ε, z.2) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1 - ε, z.2) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  filter_upwards [ht.eventually (crossInd_eventually hz), self_mem_nhdsWithin] with ε hε hε0
  have hlt : ((z.1 - ε, z.2) : Point).1 < z.1 := by
    show z.1 - ε < z.1; linarith [mem_Ioi.1 hε0]
  rw [hε, ite_eq_left hlt, add_assoc]

/-! ### Telescoping around the closed walk -/

/-- Cyclic reindexing of a sum over `range n`. -/
theorem sum_range_succ_mod {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f ((i + 1) % n) = ∑ i ∈ Finset.range n, f i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ' f, Nat.mod_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mod_eq_of_lt (by omega)]

/-- The endpoint contributions telescope around the closed walk. -/
theorem sum_aboveInd_edges (P : Polygon) (z : Point) :
    ∑ i ∈ Finset.range P.n, (aboveInd z (P.vtx i) + aboveInd z (P.vtx ((i + 1) % P.n))) = 0 := by
  rw [Finset.sum_add_distrib, sum_range_succ_mod (fun i => aboveInd z (P.vtx i)) P.n]
  exact zmod_two_add_self _

/-- **Local constancy of the crossing sum** off the boundary. -/
theorem crossSum_eventually_eq (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    ∀ᶠ z' in 𝓝 z, crossSum P z' = crossSum P z := by
  have h : ∀ i ∈ Finset.range P.n, ∀ᶠ z' in 𝓝 z,
      crossInd z' (P.vtx i) (P.vtx ((i + 1) % P.n)) =
        crossInd z (P.vtx i) (P.vtx ((i + 1) % P.n)) +
          if z'.1 < z.1 then aboveInd z (P.vtx i) + aboveInd z (P.vtx ((i + 1) % P.n)) else 0 :=
    fun i hi => crossInd_eventually fun hmem => hz ⟨i, Finset.mem_range.1 hi, hmem⟩
  rw [← Filter.eventually_all_finset] at h
  filter_upwards [h] with z' hz'
  unfold crossSum
  rw [Finset.sum_congr rfl hz', Finset.sum_add_distrib]
  by_cases hlt : z'.1 < z.1
  · simp only [ite_eq_left hlt]
    rw [sum_aboveInd_edges, add_zero]
  · simp only [ite_eq_right hlt, Finset.sum_const_zero, add_zero]

/-- **Local constancy of the parity** off the boundary. -/
theorem parity_eventually_eq (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    ∀ᶠ z' in 𝓝 z, parity P z' = parity P z := by
  filter_upwards [crossSum_eventually_eq P hz] with z' hz'
  exact parity_eq_iff.2 hz'

/-- The parity is continuous (into the discrete space `Bool`) on the complement of the
boundary. -/
theorem continuousOn_parity (P : Polygon) : ContinuousOn (parity P) P.boundaryᶜ := by
  rw [(isOpen_boundary_compl P).continuousOn_iff]
  intro z hz
  exact continuousAt_const.congr_of_eventuallyEq (parity_eventually_eq P hz)

/-- The parity, restricted to the complement of the boundary, is locally constant. -/
theorem isLocallyConstant_parity (P : Polygon) :
    IsLocallyConstant (fun z : (P.boundaryᶜ : Set Point) => parity P z) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  have h := parity_eventually_eq P z.2
  exact (continuous_subtype_val.tendsto z).eventually h

/-- **Constancy on connected sets**: the parity is constant on every preconnected set avoiding
the boundary. -/
theorem parity_eq_of_isPreconnected (P : Polygon) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ P.boundaryᶜ) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    parity P x = parity P y :=
  hS.constant ((continuousOn_parity P).mono hSb) hx hy

/-- The crossing sum is constant on every preconnected set avoiding the boundary. -/
theorem crossSum_eq_of_isPreconnected (P : Polygon) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ P.boundaryᶜ) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    crossSum P x = crossSum P y :=
  parity_eq_iff.1 (parity_eq_of_isPreconnected P hS hSb hx hy)

/-! ### Flip across an edge -/

/-- Crossing a non-vertical edge vertically at a non-endpoint point flips its bit: for every
`ε > 0`, the point above does not cross, the point below does, and neither lies on the edge. -/
theorem crossInd_flip_edge {z u v : Point} (huv : u.1 ≠ v.1) (hz : z ∈ segment u v)
    (hzu : z ≠ u) (hzv : z ≠ v) {ε : ℝ} (hε : 0 < ε) :
    (z.1, z.2 + ε) ∉ segment u v ∧ (z.1, z.2 - ε) ∉ segment u v ∧
      crossInd (z.1, z.2 + ε) u v + 1 = crossInd (z.1, z.2 - ε) u v := by
  -- reduce to the left-to-right orientation
  suffices key : ∀ u v : Point, u.1 < v.1 → z ∈ segment u v → z ≠ u → z ≠ v →
      (z.1, z.2 + ε) ∉ segment u v ∧ (z.1, z.2 - ε) ∉ segment u v ∧
        crossInd (z.1, z.2 + ε) u v + 1 = crossInd (z.1, z.2 - ε) u v by
    rcases lt_or_gt_of_ne huv with h | h
    · exact key u v h hz hzu hzv
    · obtain ⟨h1, h2, h3⟩ := key v u h (segment_comm u v ▸ hz) hzv hzu
      rw [segment_comm] at h1 h2
      rw [crossInd_comm, h3, crossInd_comm]
      exact ⟨h1, h2, rfl⟩
  intro u v huv hz hzu hzv
  rw [mem_segment_iff_of_lt huv] at hz
  obtain ⟨h0, h1, hl⟩ := hz
  have hd : 0 < v.1 - u.1 := sub_pos.2 huv
  have h0' : u.1 < z.1 := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hzu
      have : z.2 = u.2 := by
        have : (z.2 - u.2) * (v.1 - u.1) = 0 := by rw [hl, ← h]; ring
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · linarith
      exact Prod.ext h.symm this
  have h1' : z.1 < v.1 := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hzv
      have : z.2 = v.2 := by
        have : (z.2 - v.2) * (v.1 - u.1) = 0 := by
          rw [h] at hl; nlinarith [hl]
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · linarith
      exact Prod.ext h this
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_segment_iff_of_lt huv]
    rintro ⟨-, -, h⟩
    simp only at h
    nlinarith [mul_pos hε hd]
  · rw [mem_segment_iff_of_lt huv]
    rintro ⟨-, -, h⟩
    simp only at h
    nlinarith [mul_pos hε hd]
  · have hnc : ¬ crosses (z.1, z.2 + ε) u v := by
      rw [crosses_iff_of_lt huv]
      rintro ⟨-, -, h⟩
      simp only at h
      nlinarith [mul_pos hε hd]
    have hc : crosses (z.1, z.2 - ε) u v := by
      rw [crosses_iff_of_lt huv]
      refine ⟨h0, h1', ?_⟩
      simp only
      nlinarith [mul_pos hε hd]
    rw [crossInd_of_not_crosses hnc, crossInd_of_crosses hc, zero_add]

/-- **Flip.**  Let `z` be a point of edge `i` of `P` that is not an endpoint of that edge,
with edge `i` non-vertical and `z` on no other edge.  Then for all sufficiently small `ε > 0`
the points `(z.1, z.2 ± ε)` lie off the boundary and have different parities. -/
theorem parity_flip (P : Polygon) {i : ℕ} (hi : i < P.n) {z : Point} (hz : z ∈ P.edge i)
    (hne : (P.vtx i).1 ≠ (P.vtx ((i + 1) % P.n)).1)
    (hzu : z ≠ P.vtx i) (hzv : z ≠ P.vtx ((i + 1) % P.n))
    (hother : ∀ j, j < P.n → j ≠ i → z ∉ P.edge j) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      (z.1, z.2 + ε) ∉ P.boundary ∧ (z.1, z.2 - ε) ∉ P.boundary ∧
        parity P (z.1, z.2 + ε) ≠ parity P (z.1, z.2 - ε) := by
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 + ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 - ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  -- for every other edge: eventually off the edge, and the bit is unchanged
  have hj : ∀ j ∈ (Finset.range P.n).erase i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((z.1, z.2 + ε) : Point) ∉ P.edge j ∧ ((z.1, z.2 - ε) : Point) ∉ P.edge j ∧
        crossInd (z.1, z.2 + ε) (P.vtx j) (P.vtx ((j + 1) % P.n)) =
          crossInd z (P.vtx j) (P.vtx ((j + 1) % P.n)) ∧
        crossInd (z.1, z.2 - ε) (P.vtx j) (P.vtx ((j + 1) % P.n)) =
          crossInd z (P.vtx j) (P.vtx ((j + 1) % P.n)) := by
    intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    have hzj : z ∉ P.edge j := hother j hj.2 hj.1
    have hopen : (P.edge j)ᶜ ∈ 𝓝 z := (isClosed_edge P j).isOpen_compl.mem_nhds hzj
    filter_upwards [hup.eventually hopen, hdn.eventually hopen,
      hup.eventually (crossInd_eventually hzj), hdn.eventually (crossInd_eventually hzj)]
      with ε h1 h2 h3 h4
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [h3, ite_eq_right (lt_irrefl _), add_zero]
    · rw [h4, ite_eq_right (lt_irrefl _), add_zero]
  rw [← Filter.eventually_all_finset] at hj
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (z.1, z.2 + ε) ∉ P.boundary ∧ (z.1, z.2 - ε) ∉ P.boundary ∧
        parity P (z.1, z.2 + ε) ≠ parity P (z.1, z.2 - ε) := by
    filter_upwards [hj, self_mem_nhdsWithin] with ε hε hε0
    have hε0' : 0 < ε := mem_Ioi.1 hε0
    obtain ⟨hi1, hi2, hi3⟩ := crossInd_flip_edge hne hz hzu hzv hε0'
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨j, hjn, hjm⟩
      by_cases hji : j = i
      · exact hi1 (hji ▸ hjm)
      · exact (hε j (Finset.mem_erase.2 ⟨hji, Finset.mem_range.2 hjn⟩)).1 hjm
    · rintro ⟨j, hjn, hjm⟩
      by_cases hji : j = i
      · exact hi2 (hji ▸ hjm)
      · exact (hε j (Finset.mem_erase.2 ⟨hji, Finset.mem_range.2 hjn⟩)).2.1 hjm
    · intro heq
      rw [parity_eq_iff] at heq
      have hmem : i ∈ Finset.range P.n := Finset.mem_range.2 hi
      unfold crossSum at heq
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at heq
      have hrest : ∑ j ∈ (Finset.range P.n).erase i,
            crossInd (z.1, z.2 + ε) (P.vtx j) (P.vtx ((j + 1) % P.n)) =
          ∑ j ∈ (Finset.range P.n).erase i,
            crossInd (z.1, z.2 - ε) (P.vtx j) (P.vtx ((j + 1) % P.n)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(hε j hj).2.2.1, (hε j hj).2.2.2]
      rw [hrest, add_left_inj, ← hi3] at heq
      exact zmod_two_add_one_ne _ heq.symm
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  exact ⟨ε₀, mem_Ioi.1 hε₀, fun ε h1 h2 => hsub ⟨h1, h2⟩⟩

/-! ### Far away -/

/-- A bound on all vertex coordinates of `P`. -/
noncomputable def coordBound (P : Polygon) : ℝ :=
  ∑ i ∈ Finset.range P.n, (|(P.vtx i).1| + |(P.vtx i).2|)

theorem abs_fst_vtx_le_coordBound (P : Polygon) {i : ℕ} (hi : i < P.n) :
    |(P.vtx i).1| ≤ coordBound P := by
  unfold coordBound
  calc |(P.vtx i).1| ≤ |(P.vtx i).1| + |(P.vtx i).2| := by
        linarith [abs_nonneg (P.vtx i).2]
    _ ≤ _ := Finset.single_le_sum (f := fun i => |(P.vtx i).1| + |(P.vtx i).2|)
        (fun j _ => by positivity) (Finset.mem_range.2 hi)

theorem abs_snd_vtx_le_coordBound (P : Polygon) {i : ℕ} (hi : i < P.n) :
    |(P.vtx i).2| ≤ coordBound P := by
  unfold coordBound
  calc |(P.vtx i).2| ≤ |(P.vtx i).1| + |(P.vtx i).2| := by
        linarith [abs_nonneg (P.vtx i).1]
    _ ≤ _ := Finset.single_le_sum (f := fun i => |(P.vtx i).1| + |(P.vtx i).2|)
        (fun j _ => by positivity) (Finset.mem_range.2 hi)

/-- **Far away**: a point to the right of, to the left of, or above every vertex has crossing
sum `0`. -/
theorem crossSum_eq_zero_of_far (P : Polygon) {z : Point}
    (hz : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2) :
    crossSum P z = 0 := by
  unfold crossSum
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < P.n := Finset.mem_range.1 hi
  have hi2 : (i + 1) % P.n < P.n := Nat.mod_lt _ (by omega)
  apply crossInd_of_not_crosses
  rcases hz with h | h | h
  · exact not_crosses_of_le ((abs_le.1 (abs_fst_vtx_le_coordBound P hi')).2.trans h.le)
      ((abs_le.1 (abs_fst_vtx_le_coordBound P hi2)).2.trans h.le)
  · exact not_crosses_of_lt (h.trans_le (abs_le.1 (abs_fst_vtx_le_coordBound P hi')).1)
      (h.trans_le (abs_le.1 (abs_fst_vtx_le_coordBound P hi2)).1)
  · exact not_crosses_of_below ((abs_le.1 (abs_snd_vtx_le_coordBound P hi')).2.trans_lt h)
      ((abs_le.1 (abs_snd_vtx_le_coordBound P hi2)).2.trans_lt h)

/-- **Far away**: there is `R` such that every point with `R < z.1`, `z.1 < -R` or `R < z.2`
has parity `false`. -/
theorem parity_eq_false_of_far (P : Polygon) :
    ∃ R : ℝ, ∀ z : Point, (R < z.1 ∨ z.1 < -R ∨ R < z.2) → parity P z = false :=
  ⟨coordBound P, fun _ hz => parity_eq_false_iff.2 (crossSum_eq_zero_of_far P hz)⟩

end

end ArtGallery.Jordan
