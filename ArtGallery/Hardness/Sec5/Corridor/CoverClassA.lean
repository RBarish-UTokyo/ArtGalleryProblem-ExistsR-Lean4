module

public import ArtGallery.Hardness.Sec5.Corridor.CoverNook

/-!
# Section 5: corridors — locating the interior points of the corridor (preparation)

* `Good.interior_x`: interior points of the corridor are strictly between the doors;
* `Good.upper_point`: above an interior point on or above the floor line there is a point of the
  upper wall on the same vertical line (the upward ray meets the boundary);
* `Good.mid_edge`: an upper-wall point strictly inside the strip of pair `k` lies on one of the six
  edges `p_k → z'_k → z1 → n1 → n0 → z0 → nxt_k`;
* `Good.wall_below_axis`: points east of `z'_k` below the axis are inside the left wall of `k`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Locate

variable (hg : I.Good N)
include hg

/-- Interior points of the corridor are strictly between the doors. -/
theorem Good.interior_x {z : Point} (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary) :
    (I.S : ℝ) < z.1 ∧ z.1 < (I.S : ℝ) + 2 := by
  have hopen := Jordan.isOpen_filled_sdiff_boundary hg.poly_simple
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hzK, hzb⟩
  have h1 : ((z.1 - δ / 2, z.2) : Point) ∈ I.poly.filled := by
    refine (hball ?_).1
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, sub_self, abs_zero]
    rw [abs_of_pos (by linarith)]
    exact max_lt (by linarith) hδ
  have h2 : ((z.1 + δ / 2, z.2) : Point) ∈ I.poly.filled := by
    refine (hball ?_).1
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, add_sub_cancel_left, sub_self, abs_zero]
    rw [abs_of_pos (by linarith)]
    exact max_lt (by linarith) hδ
  have b1 := hg.poly_filled_box h1
  have b2 := hg.poly_filled_box h2
  simp only [corridorBox, Set.mem_ofPred_eq] at b1 b2
  constructor <;> linarith [b1.1, b2.2.1]

/-- **A point of the upper wall above an interior point.** -/
theorem Good.upper_point {z : Point} (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hzH : (I.H : ℝ) ≤ z.2) :
    ∃ e ∈ edgesOf (I.chainAfter.map ratPoint), ∃ w ∈ segOf e, w.1 = z.1 ∧ z.2 < w.2 := by
  obtain ⟨hx1, hx2⟩ := hg.interior_x hzK hzb
  obtain ⟨s, hs, hb⟩ := exists_boundary_on_ray (d := ((0 : ℝ), (1 : ℝ))) (by simp) hzK hzb
  set w := z + s • ((0 : ℝ), (1 : ℝ)) with hwdef
  have hw1 : w.1 = z.1 := by simp [w]
  have hw2 : w.2 = z.2 + s := by simp [w]
  rcases poly_boundary_cases hb with ⟨e, he, hwe⟩ | hwin | ⟨e, he, hwe⟩ | hent
  · have := hg.floor_edges_le he hwe; linarith
  · exfalso
    have := seg_affine_le (α := -1) (β := 0) (c := -((I.S : ℝ) + 2)) hwin
      (by rw [ratPoint_c1']; simp) (by rw [ratPoint_d1']; simp)
    linarith
  · exact ⟨e, he, w, hwe, hw1, by linarith⟩
  · exfalso
    have := seg_affine_le (α := 1) (β := 0) (c := (I.S : ℝ)) hent
      (by rw [ratPoint_d0']; simp) (by rw [ratPoint_c0']; simp)
    linarith

/-- **The upper wall inside the strip of pair `k`.** -/
theorem Good.mid_edge {k : ℕ} (hk : k < I.np) {e : Point × Point}
    (he : e ∈ edgesOf (I.chainAfter.map ratPoint)) {w : Point} (hwe : w ∈ segOf e)
    (h1 : I.lXR (ratPoint (I.nxt k)) < I.lXR w) (h2 : I.lXR w < I.lXR (ratPoint (I.sgPt k))) :
    e = (ratPoint (I.sgPt k), ratPoint (I.zp k)) ∨ e = (ratPoint (I.zp k), ratPoint (I.z1 k)) ∨
      e = (ratPoint (I.z1 k), ratPoint (I.n1 k)) ∨ e = (ratPoint (I.n1 k), ratPoint (I.n0 k)) ∨
      e = (ratPoint (I.n0 k), ratPoint (I.z0 k)) ∨ e = (ratPoint (I.z0 k), ratPoint (I.nxt k)) := by
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
  have hmono := hg.xMonoQ_chainAfter
  rw [hA] at hmono he
  have hsplit : (A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂).map
      ratPoint = ((A₁.map ratPoint) ++ ratPoint (I.sgPt k) ::
        ([ratPoint (I.zp k), ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k),
          ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint)) := by simp
  rw [hsplit, edgesOf_append, List.mem_append] at he
  rcases he with he | he
  · -- east part
    exfalso
    have hpre := XMonoQ.prefix_ge (A := A₁) (m := I.sgPt k)
      (B := [I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂) (by simpa using hmono)
    have := Aff.ge_ev_of_segment (I.cA 1 0 0) hwe (c := I.lXR (ratPoint (I.sgPt k)))
      (by
        have hm := (mem_of_mem_edgesOf he).1
        rw [ev_cA]
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨y, hy, hyeq⟩ := List.mem_map.1 hm
          rw [← hyeq]
          have := (lXR_le_iff' hg).2 (show (ratPoint (I.sgPt k)).1 ≤ (ratPoint y).1 by
            simp only [ratPoint]; exact_mod_cast hpre y hy)
          linarith
        · rw [List.mem_singleton] at hm; rw [hm]; ring_nf; linarith)
      (by
        have hm := (mem_of_mem_edgesOf he).2
        rw [ev_cA]
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨y, hy, hyeq⟩ := List.mem_map.1 hm
          rw [← hyeq]
          have := (lXR_le_iff' hg).2 (show (ratPoint (I.sgPt k)).1 ≤ (ratPoint y).1 by
            simp only [ratPoint]; exact_mod_cast hpre y hy)
          linarith
        · rw [List.mem_singleton] at hm; rw [hm]; ring_nf; linarith)
    rw [ev_cA] at this
    linarith
  rw [show ratPoint (I.sgPt k) :: ([ratPoint (I.zp k), ratPoint (I.z1 k), ratPoint (I.n1 k),
      ratPoint (I.n0 k), ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint) =
      [ratPoint (I.sgPt k), ratPoint (I.zp k), ratPoint (I.z1 k), ratPoint (I.n1 k),
        ratPoint (I.n0 k), ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint from rfl,
    edgesOf_append, List.mem_append] at he
  rcases he with he | he
  · simp only [List.cons_append, List.nil_append, edgesOf_cons_cons, edgesOf_single,
      List.mem_cons, List.not_mem_nil, or_false] at he
    exact he
  · -- west part
    exfalso
    have hsuf : XMonoQ (I.nxt k :: A₂) := by
      have := XMonoQ.of_append (A := A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k])
        (B := I.nxt k :: A₂) (by simpa using hmono)
      exact this
    have hle := hsuf.le_head
    have key : ∀ v ∈ ratPoint (I.nxt k) :: A₂.map ratPoint,
        (I.cA 1 0 0).ev v ≤ I.lXR (ratPoint (I.nxt k)) := by
      intro v hv
      rw [← List.map_cons] at hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      rw [ev_cA]
      have := (lXR_le_iff' hg).2 (show (ratPoint y).1 ≤ (ratPoint (I.nxt k)).1 by
        simp only [ratPoint]; exact_mod_cast hle y hy)
      linarith
    have hm := mem_of_mem_edgesOf he
    have := Aff.ev_le_of_segment (I.cA 1 0 0) hwe (key _ hm.1) (key _ hm.2)
    rw [ev_cA] at this
    linarith

/-- Points east of `z'_k` below the axis are inside the left wall of `k`. -/
theorem Good.wall_below_axis {k : ℕ} (hk : k < I.np) {z : Point}
    (hx : I.lXR (ratPoint (I.zp k)) ≤ I.lXR z) (hA : I.AR k z ≤ 0) :
    0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z := by
  obtain ⟨-, hS, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨zx, zy, -, -, zA0⟩ := hg.rl_zp hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1, n2⟩ := hg.rl_nxt hk
  obtain ⟨l1, l2, r1, r2, hN, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx zy hw2 hh
  -- `Y_z − Y' ≤ (X_z − X')/2`
  have hslope : I.lYR z - I.lYR (ratPoint (I.zp k)) ≤
      (I.lXR z - I.lXR (ratPoint (I.zp k))) / 2 := by
    simp only [AR] at hA zA0
    have hd : 0 ≤ I.lXR z - I.lXR (ratPoint (I.zp k)) := by linarith
    have h1 : ((I.DD k : ℚ) : ℝ) * (I.lYR z - I.lYR (ratPoint (I.zp k))) ≤
        ((I.hh k : ℚ) : ℝ) * (I.lXR z - I.lXR (ratPoint (I.zp k))) := by linarith
    have h2 : ((I.hh k : ℚ) : ℝ) * (I.lXR z - I.lXR (ratPoint (I.zp k))) ≤
        ((I.DD k : ℚ) : ℝ) / 2 * (I.lXR z - I.lXR (ratPoint (I.zp k))) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hd
    have hDp : (0 : ℝ) < ((I.DD k : ℚ) : ℝ) := by linarith
    by_contra hc; push Not at hc
    have := mul_lt_mul_of_pos_left hc hDp
    nlinarith
  -- the wall as `−a (Y − Y₀) + b (X − X₀)` with `b ≥ a/2 ≥ 0`
  refine nonneg_of_mul_nonneg_c h64 ?_
  rw [det_lXR]
  have hY : I.lYR z - I.lYR (ratPoint (I.z0 k)) ≤ (I.lXR z - I.lXR (ratPoint (I.z0 k))) / 2 := by
    rw [z0x, z0y]; linarith
  have hX : 0 ≤ I.lXR z - I.lXR (ratPoint (I.z0 k)) := by rw [z0x]; linarith
  have hab : 0 ≤ I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k)) ∧
      (I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k))) / 2 ≤
        I.lYR (ratPoint (I.z0 k)) - I.lYR (ratPoint (I.nxt k)) := by
    rw [z0x, z0y]
    by_cases h : k + 1 < I.np
    · rw [(n1 h).1, (n1 h).2]; constructor <;> linarith
    · rw [(n2 h).1, (n2 h).2]; constructor <;> nlinarith
  obtain ⟨ha, hb⟩ := hab
  set a := I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k))
  set b := I.lYR (ratPoint (I.z0 k)) - I.lYR (ratPoint (I.nxt k))
  have e : (I.lXR (ratPoint (I.nxt k)) - I.lXR (ratPoint (I.z0 k))) *
      (I.lYR z - I.lYR (ratPoint (I.z0 k))) - (I.lXR z - I.lXR (ratPoint (I.z0 k))) *
      (I.lYR (ratPoint (I.nxt k)) - I.lYR (ratPoint (I.z0 k))) =
      -a * (I.lYR z - I.lYR (ratPoint (I.z0 k))) + b * (I.lXR z - I.lXR (ratPoint (I.z0 k))) := by
    simp only [a, b]; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hY ha, mul_le_mul_of_nonneg_right hb hX]

end Locate

end Input

end ArtGallery.Sec5.Corridor

end
