module

public import ArtGallery.Hardness.Sec5.CountGlobal

/-!
# Section 5, constraints (iv)/(v): tools

Generic visibility facts used to show that the critical sets of a unit (the umbra and nook
critical points of the corridor, the zones `Γ` and the nooks of the templates) are seen only by
the guards of the designated positions.

* `mem_room_of_sees`: a point seen from a point of a room by a segment avoiding the door lies in
  the room.
* **Foreign guards** (`Foreign`: a point in the box of another unit of the same side, at least `3`
  higher or lower, or in the region `x ≤ −S/2`, `S − 1 ≤ y ≤ S + 3N + 3` of the units of the other
  side): `Good.foreign_not_sees_corr` (a corridor point near the middle of the window region is not
  seen; through the window the segment would leave the unit room, through the entrance it would
  have to be a point of the entrance), `foreign_not_sees_tmpl` (a point of the unit room in the
  template area is not seen by a foreign point nor by a base guard: the segment crosses the
  entrance).
* **Template points and the corridor** (`Good.tmpl_band`, `Good.tmpl_not_sees_band`): a point
  `m + T/S` of the template area sees a corridor point of the window only inside the `ξ`-band
  `(−T_sum/S − ε/4, −T_sum/S + 3/S + ε/4)`, hence nothing of the receiver band of `τ` if the
  coordinate sum `T.x + T.y` differs enough from that of the receiver `T_τ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon
open Corridor (Input CorridorAt c0 c1 d0 d1 place Oc xiOf Xis RecvHyp)
open Corridor.Input
open ArtGallery.Sec5.Count (unitBox)

/-! ### Rooms and sub-segments -/

/-- A point seen from a point of a room by a segment avoiding the door lies in the room. -/
theorem mem_room_of_sees {P : Polygon} {R D : Set Point} (hR : P.IsRoom R D) {t p : Point}
    (ht : t ∈ R) (hs : P.Sees t p) (hD : ∀ y ∈ ArtGallery.segment t p, y ∉ D) : p ∈ R := by
  by_contra hp
  obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door hR ht hp hs
  exact hD y hy hyD

/-- A point of a seen segment sees the far end. -/
theorem sees_sub_right {P : Polygon} {w p y : Point} (hs : P.Sees w p)
    (hy : y ∈ ArtGallery.segment w p) : P.Sees y p := fun _ hz =>
  hs (Geometry.segment_subset_of_convex (Geometry.segment_convex w p) hy
    (Geometry.right_mem_segment w p) hz)

/-! ### The doors -/

section Doors

variable {I : Input}

/-- A point of the entrance `d0 c0`. -/
theorem mem_entrance (hρ : 0 ≤ I.rhoR) {y : Point} (hy : y ∈ I.entrance) :
    y.1 = (I.S : ℝ) ∧ (I.H : ℝ) ≤ y.2 ∧ y.2 ≤ (I.H : ℝ) + 2 * I.rhoR := by
  rw [entrance, ratPoint_d0', ratPoint_c0'] at hy
  obtain ⟨t, h0, h1, hx, hy'⟩ := Irrational.mem_segment_coords hy
  simp only at hx hy'
  refine ⟨by rw [hx]; ring, ?_, ?_⟩ <;> nlinarith [mul_nonneg (sub_nonneg.2 h1) hρ]

/-- A point of the window `c1 d1`. -/
theorem mem_window (hρ : 0 ≤ I.rhoR) {y : Point} (hy : y ∈ I.window) :
    y.1 = (I.S : ℝ) + 2 ∧ (I.H : ℝ) ≤ y.2 ∧ y.2 ≤ (I.H : ℝ) + I.rhoR := by
  rw [window, ratPoint_c1', ratPoint_d1'] at hy
  obtain ⟨t, h0, h1, hx, hy'⟩ := Irrational.mem_segment_coords hy
  simp only at hx hy'
  refine ⟨by rw [hx]; ring, ?_, ?_⟩ <;> nlinarith [mul_nonneg h0 hρ]

end Doors

/-! ### Foreign points -/

/-- A point of another unit box of the same side (at least `3` higher or lower) or of the region
of the units of the other side. -/
def Foreign (S H N : ℝ) (g : Point) : Prop :=
  (∃ H' : ℝ, (H' + 3 ≤ H ∨ H + 3 ≤ H') ∧ g ∈ unitBox S H') ∨
    (g.1 ≤ -(S / 2) ∧ S - 1 ≤ g.2 ∧ g.2 ≤ S + 3 * N + 3)

/-- A foreign point is not in the unit box. -/
theorem Foreign.not_mem_box {S H N : ℝ} (hS : 0 < S) {g : Point} (h : Foreign S H N g) :
    g ∉ unitBox S H := by
  rintro ⟨b1, b2, b3, b4⟩
  rcases h with ⟨H', hH', c1, c2, c3, c4⟩ | ⟨h1, -, -⟩
  · rcases hH' with h | h <;> linarith
  · linarith


/-! ### Foreign points and the corridor -/

/-- The corridor box lies in the unit box. -/
theorem corridorBox_sub_unitBox {S H : ℝ} {z : Point} (hz : z ∈ Corridor.corridorBox S H) :
    z ∈ unitBox S H := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  exact ⟨z1, by linarith, by linarith, z4⟩

section ForeignCorr

variable {I : Input} {N : ℚ} (hg : I.Good N)
include hg

/-- The window is an edge of the corridor polygon. -/
theorem Good.window_sub_poly : I.window ⊆ I.poly.filled := by
  intro y hy
  have hm2 : 2 ≤ I.chainBefore.length := by rw [chainBefore_length]; omega
  have hA2 : 2 ≤ I.chainAfter.length := by rw [chainAfter_length]; omega
  have hn : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
    rw [poly_n, List.length_append]
  refine Or.inl ⟨I.chainBefore.length - 1, by omega, ?_⟩
  have e : (I.chainBefore.length - 1 + 1) % I.poly.n = I.chainBefore.length := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [Polygon.edge, poly_vtx_before (by omega), chainBefore_getD_last, e,
    poly_vtx_after le_rfl (by omega), Nat.sub_self, chainAfter_getD_zero]
  exact hy

/-- The real scale facts of a good corridor. -/
theorem Good.realFacts : (800000 : ℝ) ≤ I.S ∧ (2 : ℝ) ≤ N ∧ (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 ∧
    (I.S : ℝ) + 1 ≤ I.H ∧ (I.H : ℝ) ≤ I.S + 3 * N ∧ 0 < I.rhoR ∧ I.rhoR < 1 / 1000 := by
  have h := hg.scaleR
  exact ⟨by exact_mod_cast hg.scale.S_ge, h.two_le, h.hS, h.hH1, h.hH2, hg.rhoR_pos,
    hg.rhoR_small⟩

variable {Q : Polygon} {a b : ℕ} (hP : Q.Simple) (hL : Q.InteriorLeft) (hC : CorridorAt Q I a b)
  (hcl : CorridorClear Q I) {K : Set Point} (hK : Q.IsRoom K I.entrance)
  (hKb : K ⊆ unitBox I.S I.H) (hc1K : ratPoint (c1 I.S I.H) ∈ K)
include hP hL hC hcl hK hKb hc1K

/-- **Foreign points do not see the middle of a corridor.**  A point `z` of the corridor within
`1/5` of `O_c` (all critical points of the corridor) is seen by no foreign point. -/
theorem Good.foreign_not_sees_corr {z g : Point} (hz : z ∈ I.poly.filled)
    (hzx : |z.1 - ((I.S : ℝ) + 1)| ≤ 1 / 5) (hzy : |z.2 - ((I.H : ℝ) + 1)| ≤ 1 / 5)
    (hfg : Foreign (I.S : ℝ) (I.H : ℝ) (N : ℝ) g) : ¬ Q.Sees g z := by
  intro hs
  obtain ⟨hS8, hN, hSN, hH1, hH2, hρ0, hρ1⟩ := Good.realFacts hg
  rw [abs_le] at hzx hzy
  have hgB := hfg.not_mem_box (by linarith)
  have hgK : g ∉ I.poly.filled := by
    intro hgin
    exact hgB (corridorBox_sub_unitBox (hg.poly_filled_box hgin))
  obtain ⟨y, hyD, hyg⟩ := hg.sees_crosses_door hP hL hC hgK hz hs
  obtain ⟨s, hs0, hs1, hy1, hy2⟩ := Irrational.mem_segment_coords hyg
  rcases hyD with hyw | hye
  · -- through the window: `y` lies in the unit room, `g` beyond it does not
    obtain ⟨w1, w2, w3⟩ := mem_window hρ0.le hyw
    have hfill : Q.Sees (ratPoint (c1 I.S I.H)) y := by
      intro w hw
      have hw' : w ∈ I.window :=
        Geometry.segment_subset_of_convex (Geometry.segment_convex _ _)
          (Geometry.left_mem_segment _ _) hyw hw
      exact hg.poly_subset hP hL hC hcl (Good.window_sub_poly hg hw')
    have hyK : y ∈ K := by
      refine mem_room_of_sees hK hc1K hfill fun w hw hwE => ?_
      obtain ⟨e1, -, -⟩ := mem_entrance hρ0.le hwE
      have := Irrational.seg_fst_ge hw
      rw [ratPoint_c1'] at this
      simp only at this
      rw [w1] at this
      rcases le_total ((I.S : ℝ) + 2) ((I.S : ℝ) + 2) with h | h <;>
        simp only [min_self] at this <;> linarith
    have hgx : (I.S : ℝ) + 2 ≤ g.1 := by
      by_contra hc
      push Not at hc
      have h1 : (1 - s) * g.1 ≤ (1 - s) * ((I.S : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hc.le (by linarith)
      have h2 : s * z.1 ≤ s * ((I.S : ℝ) + 2) := mul_le_mul_of_nonneg_left (by linarith) hs0
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · subst h0; simp at hy1; linarith
      · have h3 : s * z.1 < s * ((I.S : ℝ) + 2) := mul_lt_mul_of_pos_left (by linarith) h0
        nlinarith
    have hyg' : Q.Sees y g := by
      rw [Geometry.segment_comm] at hyg
      exact sees_sub_right (Polygon.sees_comm.1 hs) hyg
    obtain ⟨w, hwE, hw⟩ := Polygon.sees_crosses_door hK hyK (fun h => hgB (hKb h)) hyg'
    obtain ⟨e1, -, -⟩ := mem_entrance hρ0.le hwE
    have := Irrational.seg_fst_ge hw
    rw [w1] at this
    rcases le_total ((I.S : ℝ) + 2) g.1 with h | h
    · rw [min_eq_left h] at this; linarith
    · rw [min_eq_right h] at this; linarith
  · -- through the entrance
    obtain ⟨e1, e2, e3⟩ := mem_entrance hρ0.le hye
    rcases hfg with ⟨H', hH', b1, b2, b3, b4⟩ | ⟨f1, f2, f3⟩
    · -- a unit of the same side: `y = g`
      have hs0' : s = 0 := by
        have : (1 - s) * g.1 + s * z.1 ≥ (I.S : ℝ) + 4 / 5 * s := by nlinarith
        nlinarith
      rw [hs0'] at hy2
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hy2
      rw [hy2] at e2 e3
      rcases hH' with h | h <;> linarith
    · -- the other side: the segment is nearly horizontal there
      have hu : (1 - s) * (z.1 - g.1) = z.1 - (I.S : ℝ) := by rw [← e1, hy1]; ring
      have hu0 : 0 ≤ 1 - s := by linarith
      have hzg : (I.S : ℝ) ≤ z.1 - g.1 := by linarith
      have h1 : (1 - s) * (I.S : ℝ) ≤ 6 / 5 := by
        have := mul_le_mul_of_nonneg_left hzg hu0
        linarith
      have hv : (1 - s) * (g.2 - z.2) = y.2 - z.2 := by rw [hy2]; ring
      have h2 : (1 - s) * (z.2 - g.2) ≥ 3 / 4 := by nlinarith
      have hzg2 : z.2 - g.2 ≤ 3 * N + 3 := by linarith
      have h3 : (1 - s) * (z.2 - g.2) ≤ (1 - s) * (3 * N + 3) :=
        mul_le_mul_of_nonneg_left hzg2 hu0
      have h4 : 3 / 4 * (I.S : ℝ) ≤ 6 / 5 * (3 * N + 3) := by nlinarith
      nlinarith

end ForeignCorr


/-! ### Foreign points and the template area -/

section ForeignTmpl

variable {I : Input} {N : ℚ} (hg : I.Good N) {Q : Polygon} {K : Set Point}
  (hK : Q.IsRoom K I.entrance) (hKb : K ⊆ unitBox I.S I.H)
include hg hK hKb

/-- **Foreign points and base guards do not see the template area.**  A point `z` of the unit
room east of the window and below `H − 1/2` is seen neither by a foreign point nor by a point of
the base line `y = 0` left of `x = S`: the segment would cross the entrance. -/
theorem Good.foreign_not_sees_tmpl {z g : Point} (hzK : z ∈ K) (hzx : (I.S : ℝ) + 2 ≤ z.1)
    (hzy : z.2 ≤ (I.H : ℝ) - 1 / 2)
    (hfg : Foreign (I.S : ℝ) (I.H : ℝ) (N : ℝ) g ∨ (g.2 = 0 ∧ g.1 < (I.S : ℝ))) :
    ¬ Q.Sees g z := by
  intro hs
  obtain ⟨hS8, hN, hSN, hH1, hH2, hρ0, hρ1⟩ := Good.realFacts hg
  obtain ⟨z1, z2, z3, z4⟩ := hKb hzK
  have hgK : g ∉ K := by
    intro hgK
    obtain ⟨b1, b2, b3, b4⟩ := hKb hgK
    rcases hfg with hf | ⟨h1, h2⟩
    · exact hf.not_mem_box (by linarith) ⟨b1, b2, b3, b4⟩
    · linarith
  obtain ⟨y, hyE, hy⟩ := Polygon.sees_crosses_door hK hzK hgK (Polygon.sees_comm.1 hs)
  obtain ⟨e1, e2, e3⟩ := mem_entrance hρ0.le hyE
  obtain ⟨s, hs0, hs1, hy1, hy2⟩ := Irrational.mem_segment_coords hy
  rcases hfg with (⟨H', hH', b1, b2, b3, b4⟩ | ⟨f1, f2, f3⟩) | ⟨g1, g2⟩
  · -- another unit of the same side: `y = g`
    have hs1' : s = 1 := by nlinarith
    rw [hs1'] at hy2
    simp only [sub_self, zero_mul, one_mul, zero_add] at hy2
    rw [hy2] at e2 e3
    rcases hH' with h | h <;> linarith
  · -- the other side
    have hu : s * (z.1 - g.1) = z.1 - (I.S : ℝ) := by rw [← e1, hy1]; ring
    have hzg : (I.S : ℝ) ≤ z.1 - g.1 := by linarith
    have h1 : s * (I.S : ℝ) ≤ 5 := by
      have := mul_le_mul_of_nonneg_left hzg hs0
      linarith
    have hv : s * (g.2 - z.2) = y.2 - z.2 := by rw [hy2]; ring
    have h2 : s * (g.2 - z.2) ≥ 1 / 2 := by linarith
    have hzg2 : g.2 - z.2 ≤ 3 * N + 5 := by linarith
    have h3 : s * (g.2 - z.2) ≤ s * (3 * N + 5) := mul_le_mul_of_nonneg_left hzg2 hs0
    have h4 : 1 / 2 * (I.S : ℝ) ≤ 5 * (3 * N + 5) := by nlinarith
    nlinarith
  · -- the base line
    rw [g1] at hy2
    have : y.2 ≤ z.2 := by nlinarith
    linarith

end ForeignTmpl

/-! ### Template points and the corridor -/

section TmplBand

variable {I : Input} {N : ℚ} (hg : I.Good N) {Q : Polygon} {a b : ℕ} (hP : Q.Simple)
  (hL : Q.InteriorLeft) (hC : CorridorAt Q I a b)
include hg hP hL hC

/-- **Band lemma for template points.**  A point `m + T/S` of the template area (`|T| ≤ 50`)
sees a corridor point of the window region only in the `ξ`-band of the receiver with left
endpoint `T` and offset `0`. -/
theorem Good.tmpl_band {T : Point} (h1 : -50 ≤ T.1) (h2 : T.1 ≤ 50) (h3 : -50 ≤ T.2)
    (h4 : T.2 ≤ 50) {z : Point} (hz : z ∈ I.poly.filled)
    (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hs : Q.Sees (place (I.S : ℝ) (I.H : ℝ) T) z) :
    Xis (I.S : ℝ) T 0 1 - Corridor.eps (I.S : ℝ) / 4 < xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z < Xis (I.S : ℝ) T 0 3 + Corridor.eps (I.S : ℝ) / 4 := by
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hr : RecvHyp T T 0 (0 : ℝ) := ⟨h1, h2, h3, h4, le_rfl, by norm_num, by simp⟩
  have eT : place (I.S : ℝ) (I.H : ℝ) T = place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2) := by
    simp
  rw [eT] at hs
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by simpa [Oc] using hX
  have hzx : (I.S : ℝ) < z.1 := by
    have h57 : 57 * (N : ℝ) / I.S < 1 := by
      rw [div_lt_one hS]; have := hsc.hS; have := hsc.two_le; nlinarith
    rw [abs_le] at hX; linarith
  have hu : -1 < (T.1 + 0) / (I.S : ℝ) := by
    rw [lt_div_iff₀ hS]; have := hsc.hS; have := hsc.two_le; nlinarith
  have hqx : (I.S : ℝ) + 2 < (place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2)).1 := by
    simp only [place]; linarith
  obtain ⟨k1, k2⟩ := hg.sees_through_window hP hL hC hqx hz hzx hs
  have hc : (c1 (I.S : ℝ) (I.H : ℝ)).1 - (place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2)).1 < 0 := by
    simp only [Corridor.c1, place]; linarith
  have hd : (d1 (I.S : ℝ) (I.H : ℝ)).1 - (place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2)).1 < 0 := by
    simp only [Corridor.d1, place]; linarith
  rw [Corridor.ratPoint_c1, Corridor.det_eq_det2, Corridor.det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ))
    _ _ _ hc.ne] at k1
  rw [Corridor.ratPoint_d1, Corridor.det_eq_det2, Corridor.det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ))
    _ _ _ hd.ne] at k2
  have b1 := Corridor.band_c1 hsc hr hX'
  have b2 := Corridor.band_d1 hsc hr hX'
  rw [abs_lt] at b1 b2
  have l1 : 0 ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z - Corridor.lineXi (Oc (I.S : ℝ) (I.H : ℝ))
      (place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2)) (c1 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) := by
    by_contra hc'
    push Not at hc'
    have := mul_pos_of_neg_of_neg hc hc'
    linarith
  have l2 : xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z - Corridor.lineXi (Oc (I.S : ℝ) (I.H : ℝ))
      (place (I.S : ℝ) (I.H : ℝ) (T.1 + 0, T.2)) (d1 (I.S : ℝ) (I.H : ℝ))
      (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) ≤ 0 := by
    by_contra hc'
    push Not at hc'
    have := mul_neg_of_neg_of_pos hd hc'
    linarith
  simp only [mul_zero, zero_div, sub_zero, add_zero, Prod.mk.eta] at b1 b2 l1 l2
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- **Template points far from a receiver strip do not see its band.** -/
theorem Good.tmpl_not_sees_band {T : Point} (h1 : -50 ≤ T.1) (h2 : T.1 ≤ 50) (h3 : -50 ≤ T.2)
    (h4 : T.2 ≤ 50) {τ : ℕ}
    (hfar : (I.T0.1 : ℝ) + I.T0.2 - 27 * τ / 2 + 5 ≤ T.1 + T.2 ∨
      T.1 + T.2 ≤ (I.T0.1 : ℝ) + I.T0.2 - 27 * τ / 2 - 4)
    {z : Point} (hz : z ∈ I.poly.filled) (hX : |z.1 - ((I.S : ℝ) + 1)| ≤ 57 * N / I.S)
    (hxi : Xis (I.S : ℝ) (ratPoint I.T0) τ 0 - Corridor.eps (I.S : ℝ) ≤ xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ∧
      xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z ≤ Xis (I.S : ℝ) (ratPoint I.T0) τ 3 + Corridor.eps (I.S : ℝ)) :
    ¬ Q.Sees (place (I.S : ℝ) (I.H : ℝ) T) z := by
  intro hs
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  obtain ⟨k1, k2⟩ := Good.tmpl_band hg hP hL hC h1 h2 h3 h4 hz hX hs
  simp only [Xis, Corridor.xiRef, Corridor.delta, Corridor.rho, Corridor.eps, ratPoint] at k1 k2 hxi
  obtain ⟨x1, x2⟩ := hxi
  push_cast at k1 k2 x1 x2
  set X := xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z
  have q1 : -(T.1 + 3 / 2 + T.2) + 3 / 2 - 1 / 32 < (I.S : ℝ) * X := by
    have := mul_lt_mul_of_pos_left k1 hS
    field_simp at this ⊢; linarith
  have q2 : (I.S : ℝ) * X < -(T.1 + 3 / 2 + T.2) + 9 / 2 + 1 / 32 := by
    have := mul_lt_mul_of_pos_left k2 hS
    field_simp at this ⊢; linarith
  have q3 : -((I.T0.1 : ℝ) + 3 / 2 + I.T0.2) + 27 * τ / 2 - 1 / 8 ≤ (I.S : ℝ) * X := by
    have := mul_le_mul_of_nonneg_left x1 hS.le
    field_simp at this ⊢; linarith
  have q4 : (I.S : ℝ) * X ≤ -((I.T0.1 : ℝ) + 3 / 2 + I.T0.2) + 27 * τ / 2 + 9 / 2 + 1 / 8 := by
    have := mul_le_mul_of_nonneg_left x2 hS.le
    field_simp at this ⊢; linarith
  rcases hfar with h | h <;> linarith

end TmplBand


/-! ### Seeing a point of a pocket's top edge -/

section Pocket

variable {Q : Polygon} (hP : Q.Simple) (hL : Q.InteriorLeft)
include hP hL

/-- **West wall.**  Let `A → B` be an edge of `Q` running west (`B.x < A.x`) and `B → C` a wall
running straight down (`C.x = B.x`, `C.y < B.y`).  A point `p` west of the wall that sees a point
`z` of the open edge `A B` sees it past the corner `C`: `det(p, C, z) ≤ 0`. -/
theorem west_wall {i0 i1 : ℕ} (hi0 : i0 < Q.n) (hi1 : i1 < Q.n) {A B C : Point}
    (hu : Q.vtx ((i0 + Q.n - 1) % Q.n) = A) (hv : Q.vtx i0 = B) (hw : Q.vtx ((i0 + 1) % Q.n) = C)
    (he1 : Q.vtx i1 = A) (he2 : Q.vtx ((i1 + 1) % Q.n) = B)
    (hBC : B.1 = C.1) (hCB : C.2 < B.2) (hBA : B.1 < A.1) {p z : Point} (hp : p.1 < B.1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz : z = Geometry.lerp A B t) (hs : Q.Sees p z) :
    det p C z ≤ 0 := by
  have h0 : 0 ≤ det A B p := by
    rw [hz] at hs
    exact Polygon.sees_edge_point hP hL hi1 he1 he2 ht0 ht1 (Polygon.sees_comm.1 hs)
  have hzx : z.1 = A.1 + t * (B.1 - A.1) := by rw [hz]; rfl
  have hzy : z.2 = A.2 + t * (B.2 - A.2) := by rw [hz]; rfl
  have hzB : B.1 < z.1 := by rw [hzx]; nlinarith
  by_contra hd
  push Not at hd
  set l := (B.1 - p.1) / (z.1 - p.1) with hl
  have hzp : 0 < z.1 - p.1 := by linarith
  have hl0 : 0 < l := div_pos (by linarith) hzp
  have hl1 : l < 1 := by rw [hl, div_lt_one hzp]; linarith
  have hcx : p.1 + l * (z.1 - p.1) = B.1 := by rw [hl]; field_simp; ring
  set c2 := p.2 + l * (z.2 - p.2) with hc2
  -- `c` is at most the top edge, and above `C`
  have hdz : det A B z = 0 := by rw [hz]; exact Geometry.det_lerp_self _ _ _
  have k1 : 0 ≤ (B.1 - A.1) * (c2 - B.2) := by
    have e : det A B (Geometry.lerp p z l) = (1 - l) * det A B p + l * det A B z :=
      Geometry.det_lerp _ _ _ _ _
    have e2 : det A B (Geometry.lerp p z l) = (B.1 - A.1) * (c2 - B.2) := by
      simp only [det, Geometry.lerp, hc2]
      rw [show p.1 + l * (z.1 - p.1) = B.1 from hcx]; ring
    rw [hdz, mul_zero, add_zero] at e
    rw [← e2, e]; exact mul_nonneg (by linarith) h0
  have k2 : 0 < (C.1 - p.1) * (c2 - C.2) := by
    have e : det p C (Geometry.lerp p z l) = (1 - l) * det p C p + l * det p C z :=
      Geometry.det_lerp _ _ _ _ _
    have e2 : det p C (Geometry.lerp p z l) = (C.1 - p.1) * (c2 - C.2) := by
      simp only [det, Geometry.lerp, hc2]
      rw [show p.1 + l * (z.1 - p.1) = B.1 from hcx, hBC]; ring
    have e3 : det p C p = 0 := by simp only [det]; ring
    rw [e3, mul_zero, zero_add] at e
    rw [← e2, e]; exact mul_pos hl0 hd
  have hc2B : c2 ≤ B.2 := by nlinarith
  have hc2C : C.2 < c2 := by
    have : 0 < C.1 - p.1 := by linarith
    nlinarith
  rcases lt_or_eq_of_le hc2B with hlt | heq
  · -- a proper crossing of the wall `B C`
    refine Polygon.not_sees_of_proper_cross hP hi0 ?_ ?_ hs
    · rw [hv, hw]
      have e1 : det B C p = (p.1 - B.1) * (B.2 - C.2) := by
        simp only [det]; rw [← hBC]; ring
      have e2 : det B C z = (z.1 - B.1) * (B.2 - C.2) := by
        simp only [det]; rw [← hBC]; ring
      rw [e1, e2]
      have a1 : (p.1 - B.1) * (B.2 - C.2) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      have a2 : 0 < (z.1 - B.1) * (B.2 - C.2) := mul_pos (by linarith) (by linarith)
      nlinarith
    · rw [hv, hw]
      have e1 : det p z B = (z.1 - p.1) * (B.2 - c2) := by
        have : (B.1 - p.1) * (z.2 - p.2) = (z.1 - p.1) * (c2 - p.2) := by
          rw [hc2, ← hcx]; ring
        simp only [det]; linarith
      have e2 : det p z C = - det p C z := by simp only [det]; ring
      rw [e1, e2]
      have a1 : 0 < (z.1 - p.1) * (B.2 - c2) := mul_pos hzp (by linarith)
      nlinarith
  · -- through the corner `B`: outside its cone
    have hcB : Geometry.lerp p z l = B := by
      ext
      · simp only [Geometry.lerp]; linarith
      · simp only [Geometry.lerp]; rw [← hc2]; exact heq
    have hsB : Q.Sees p B := by
      rw [← hcB]; exact Count.sees_sub hs (Geometry.lerp_mem_segment _ _ hl0.le hl1.le)
    have hconv : 0 < det A B C := by
      have : det A B C = (B.1 - A.1) * (C.2 - B.2) := by simp only [det]; rw [← hBC]; ring
      rw [this]; exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    obtain ⟨-, c2'⟩ := Polygon.sees_subset_cone' hP hL hi0 hu hv hw hconv hsB
    have : det B C p = (p.1 - B.1) * (B.2 - C.2) := by simp only [det]; rw [← hBC]; ring
    rw [this] at c2'
    have : (p.1 - B.1) * (B.2 - C.2) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith

/-- **East wall** (mirror of `west_wall`).  Let `B → A` be an edge running west (`A.x < B.x`) and
`C → B` a wall running straight up (`C.x = B.x`, `C.y < B.y`).  A point `q` east of the wall
that sees a point `z` of the open edge `B A` sees it past the corner `C`: `0 ≤ det(q, C, z)`. -/
theorem east_wall {iB j : ℕ} (hiB : iB < Q.n) (hj : j < Q.n) {A B C : Point}
    (hu : Q.vtx ((iB + Q.n - 1) % Q.n) = C) (hv : Q.vtx iB = B) (hw : Q.vtx ((iB + 1) % Q.n) = A)
    (he1 : Q.vtx j = C) (he2 : Q.vtx ((j + 1) % Q.n) = B)
    (hBC : B.1 = C.1) (hCB : C.2 < B.2) (hAB : A.1 < B.1) {q z : Point} (hq : B.1 < q.1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz : z = Geometry.lerp B A t) (hs : Q.Sees q z) :
    0 ≤ det q C z := by
  have h0 : 0 ≤ det B A q := by
    rw [hz] at hs
    exact Polygon.sees_edge_point hP hL hiB hv hw ht0 ht1 (Polygon.sees_comm.1 hs)
  have hzx : z.1 = B.1 + t * (A.1 - B.1) := by rw [hz]; rfl
  have hzB : z.1 < B.1 := by rw [hzx]; nlinarith
  by_contra hd
  push Not at hd
  set l := (B.1 - q.1) / (z.1 - q.1) with hl
  have hzq : z.1 - q.1 < 0 := by linarith
  have hl0 : 0 < l := div_pos_of_neg_of_neg (by linarith) hzq
  have hl1 : l < 1 := by rw [hl, div_lt_one_of_neg hzq]; linarith
  have hcx : q.1 + l * (z.1 - q.1) = B.1 := by
    have hne : z.1 - q.1 ≠ 0 := hzq.ne
    rw [hl]; field_simp; ring
  set c2 := q.2 + l * (z.2 - q.2) with hc2
  have hdz : det B A z = 0 := by rw [hz]; exact Geometry.det_lerp_self _ _ _
  have k1 : 0 ≤ (A.1 - B.1) * (c2 - B.2) := by
    have e : det B A (Geometry.lerp q z l) = (1 - l) * det B A q + l * det B A z :=
      Geometry.det_lerp _ _ _ _ _
    have e2 : det B A (Geometry.lerp q z l) = (A.1 - B.1) * (c2 - B.2) := by
      simp only [det, Geometry.lerp, hc2]
      rw [show q.1 + l * (z.1 - q.1) = B.1 from hcx]; ring
    rw [hdz, mul_zero, add_zero] at e
    rw [← e2, e]; exact mul_nonneg (by linarith) h0
  have k2 : (C.1 - q.1) * (c2 - C.2) < 0 := by
    have e : det q C (Geometry.lerp q z l) = (1 - l) * det q C q + l * det q C z :=
      Geometry.det_lerp _ _ _ _ _
    have e2 : det q C (Geometry.lerp q z l) = (C.1 - q.1) * (c2 - C.2) := by
      simp only [det, Geometry.lerp, hc2]
      rw [show q.1 + l * (z.1 - q.1) = B.1 from hcx, hBC]; ring
    have e3 : det q C q = 0 := by simp only [det]; ring
    rw [e3, mul_zero, zero_add] at e
    rw [← e2, e]; exact mul_neg_of_pos_of_neg hl0 hd
  have hc2B : c2 ≤ B.2 := by nlinarith
  have hc2C : C.2 < c2 := by
    have : C.1 - q.1 < 0 := by linarith
    nlinarith
  rcases lt_or_eq_of_le hc2B with hlt | heq
  · refine Polygon.not_sees_of_proper_cross hP hj ?_ ?_ hs
    · rw [he1, he2]
      have e1 : det C B q = -((q.1 - B.1) * (B.2 - C.2)) := by
        simp only [det]; rw [← hBC]; ring
      have e2 : det C B z = -((z.1 - B.1) * (B.2 - C.2)) := by
        simp only [det]; rw [← hBC]; ring
      rw [e1, e2]
      have a1 : 0 < (q.1 - B.1) * (B.2 - C.2) := mul_pos (by linarith) (by linarith)
      have a2 : (z.1 - B.1) * (B.2 - C.2) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      nlinarith
    · rw [he1, he2]
      have e1 : det q z B = (z.1 - q.1) * (B.2 - c2) := by
        have : (B.1 - q.1) * (z.2 - q.2) = (z.1 - q.1) * (c2 - q.2) := by
          rw [hc2, ← hcx]; ring
        simp only [det]; linarith
      have e2 : det q z C = - det q C z := by simp only [det]; ring
      rw [e1, e2]
      have a1 : (z.1 - q.1) * (B.2 - c2) < 0 := mul_neg_of_neg_of_pos hzq (by linarith)
      nlinarith
  · have hcB : Geometry.lerp q z l = B := by
      ext
      · simp only [Geometry.lerp]; linarith
      · simp only [Geometry.lerp]; rw [← hc2]; exact heq
    have hsB : Q.Sees q B := by
      rw [← hcB]; exact Count.sees_sub hs (Geometry.lerp_mem_segment _ _ hl0.le hl1.le)
    have hconv : 0 < det C B A := by
      have : det C B A = (A.1 - B.1) * (C.2 - B.2) := by simp only [det]; rw [← hBC]; ring
      rw [this]; exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    obtain ⟨c1', -⟩ := Polygon.sees_subset_cone' hP hL hiB hu hv hw hconv hsB
    have : det C B q = -((q.1 - B.1) * (B.2 - C.2)) := by simp only [det]; rw [← hBC]; ring
    rw [this] at c1'
    have : 0 < (q.1 - B.1) * (B.2 - C.2) := mul_pos (by linarith) (by linarith)
    linarith

end Pocket

end ArtGallery.Sec5.Constraint

end
