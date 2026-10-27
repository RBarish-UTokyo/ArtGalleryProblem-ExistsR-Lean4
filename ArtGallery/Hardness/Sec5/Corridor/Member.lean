module

public import ArtGallery.Hardness.Sec5.Corridor.Critical

/-!
# Section 5: corridors — points of the corridor region

* **Vertical access** (`Good.mem_poly_of_vertical`): a point `z` with `S + 4/5 ≤ z.x ≤ S + 7/5`
  above the floor, below every boundary point of the corridor polygon on its vertical line, is an
  interior point of the corridor (the vertical segment down to the floor stays off the boundary and
  ends just above a floor edge, where the region lies above the floor).
* **Boundary of the corridor polygon** (`Good.poly_boundary_cases`): a boundary point is on a
  floor edge, on the window, on an upper-wall edge or on the entrance.
* **The upper wall near pair `k`** (`chainAfter_inner`): `… p_k, z'_k, z1, n1, n0, z0, nxt_k, …`
  with `nxt_k = valley_{k+1}` (or `d0` for the last pair); by monotonicity the other upper edges
  are strictly right of `z'_k` or left of `nxt_k`.
* **Umbra critical points are corridor points** (`Good.umbra_crit_mem`).
* **The corridor region lies in `P`** (`Good.poly_subset`), provided the boundary of `P` meets the
  open corridor box only in the corridor polygon's boundary (`CorridorClear`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-! ## Monotone chains: prefixes and suffixes -/

theorem XMonoQ.le_head {b : ℚ × ℚ} {l : List (ℚ × ℚ)} (h : XMonoQ (b :: l)) :
    ∀ x ∈ b :: l, x.1 ≤ b.1 := by
  induction l generalizing b with
  | nil => intro x hx; simp at hx; rw [hx]
  | cons c l ih =>
    intro x hx
    have hbc : c.1 ≤ b.1 := by
      rcases h.1 with h1 | h1
      · exact h1.le
      · exact h1.1.le
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact (ih h.2 x hx).trans hbc

theorem XMonoQ.tail {a : ℚ × ℚ} {l : List (ℚ × ℚ)} (h : XMonoQ (a :: l)) : XMonoQ l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2

theorem XMonoQ.of_append {A B : List (ℚ × ℚ)} (h : XMonoQ (A ++ B)) : XMonoQ B := by
  induction A with
  | nil => simpa using h
  | cons a A ih => exact ih h.tail

/-- In a monotone chain, every vertex before `m` is weakly right of `m`. -/
theorem XMonoQ.prefix_ge {A B : List (ℚ × ℚ)} {m : ℚ × ℚ} (h : XMonoQ (A ++ m :: B)) :
    ∀ x ∈ A, m.1 ≤ x.1 := by
  induction A with
  | nil => simp
  | cons a A ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.le_head m (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self)))
    · exact ih h.tail x hx

/-! ## A segment lemma -/

/-- On a segment `a b` going west (`lX` decreasing) with slope bounded by `c`, the height at
abscissa `lX w` is at least `lY a − c (lX a − lX w)`. -/
theorem seg_height_ge {f g : Point → ℝ} (hf : ∀ p q : Point, ∀ t : ℝ,
      f (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) = f p + t * (f q - f p))
    (hg' : ∀ p q : Point, ∀ t : ℝ,
      g (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) = g p + t * (g q - g p))
    {a b w : Point} (hw : w ∈ ArtGallery.segment a b) {c : ℝ}
    (hs : g a - g b ≤ c * (f a - f b)) :
    g a - c * (f a - f w) ≤ g w := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hw
  rw [hf, hg']
  have : t * (g a - g b) ≤ t * (c * (f a - f b)) := mul_le_mul_of_nonneg_left hs ht0
  nlinarith

/-! ## Affine functionals on segments -/

/-- `f` is affine along segments. -/
def Lerp (f : Point → ℝ) : Prop := ∀ p q : Point, ∀ t : ℝ,
  f (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) = f p + t * (f q - f p)

/-- An affine functional bounded below at both ends of a segment is bounded below on it. -/
theorem seg_lerp_ge {f : Point → ℝ} (hf : Lerp f) {a b w : Point}
    (hw : w ∈ ArtGallery.segment a b) {c : ℝ} (ha : c ≤ f a) (hb : c ≤ f b) : c ≤ f w := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hw
  rw [hf]
  have e : f a + t * (f b - f a) - c = (1 - t) * (f a - c) + t * (f b - c) := by ring
  have := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ha)
  have := mul_nonneg ht0 (sub_nonneg.2 hb)
  linarith

/-- An affine functional bounded below at the vertices of a polyline is bounded below on it. -/
theorem edges_lerp_ge {f : Point → ℝ} (hf : Lerp f) {L : List Point} {c : ℝ}
    (hL : ∀ x ∈ L, c ≤ f x) : ∀ e ∈ edgesOf L, ∀ w ∈ segOf e, c ≤ f w := by
  intro e he w hw
  have hm := mem_of_mem_edgesOf he
  exact seg_lerp_ge hf hw (hL _ hm.1) (hL _ hm.2)

namespace Input

variable {I : Input} {N : ℚ}

theorem lXR_lerp : Lerp I.lXR := by
  intro p q t
  simp only [lXR]; ring

theorem lYR_lerp : Lerp I.lYR := by
  intro p q t
  simp only [lYR]; ring

/-! ## The gap floor edge -/

section Gap

variable (hg : I.Good N)
include hg

/-- The floor edge in the middle of the corridor: between the slots of the later pairs (near
`x = S + 3/4`) and the slope-2 slot of the first pair (near `x = S + 3/2`). -/
theorem Good.gap_edge : ∃ i, i + 1 < I.chainBefore.length ∧
    (I.chainBefore.getD i 0).2 = I.H ∧ (I.chainBefore.getD (i + 1) 0).2 = I.H ∧
    (I.chainBefore.getD i 0).1 < I.S + 4 / 5 ∧ I.S + 7 / 5 < (I.chainBefore.getD (i + 1) 0).1 := by
  have hp := hg.np_pos
  have hp3 := hg.np_le
  have h0 : 0 < I.np := by omega
  obtain ⟨he, he1⟩ := eps_small hg
  have a := hg.kx_zero_two h0
  rw [abs_le] at a
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with hnp | hnp | hnp
  · refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [chainBefore, floor_eq_one hg hnp, slot2, slot4, c0]; linarith
  · have b := hg.kx_four (k := 1) (by omega) le_rfl
    rw [abs_le] at b
    refine ⟨6, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [chainBefore, floor_eq_two hg hnp, slot2, slot4, c0] <;> linarith
  · have b := hg.kx_four (k := 1) (by omega) le_rfl
    rw [abs_le] at b
    refine ⟨12, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [chainBefore, floor_eq_three hg hnp, slot2, slot4, c0] <;> linarith

/-- **Vertical access to the corridor.** -/
theorem Good.mem_poly_of_vertical {z : Point} (h1 : (I.S : ℝ) + 4 / 5 ≤ z.1)
    (h2 : z.1 ≤ (I.S : ℝ) + 7 / 5) (h3 : (I.H : ℝ) < z.2)
    (h4 : ∀ w ∈ I.poly.boundary, w.1 = z.1 → (I.H : ℝ) < w.2 → z.2 < w.2) :
    z ∈ I.poly.filled \ I.poly.boundary := by
  have hK := hg.poly_simple
  have hKL := hg.poly_interiorLeft
  obtain ⟨i, hi, ya, yb, xa, xb⟩ := hg.gap_edge
  have hn : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
    rw [poly_n, List.length_append]
  have vi := poly_vtx_before (I := I) (j := i) (by omega)
  have vi1 := poly_vtx_before (I := I) (j := i + 1) hi
  set A := I.chainBefore.getD i 0
  set B := I.chainBefore.getD (i + 1) 0
  have xa' : (A.1 : ℝ) < (I.S : ℝ) + 4 / 5 := by
    have := rat_cast_le_of xa.le; push_cast at this
    have h' : ((A.1 : ℚ) : ℝ) ≠ ((I.S + 4 / 5 : ℚ) : ℝ) := by
      rw [Ne, Rat.cast_inj]; exact ne_of_lt xa
    push_cast at h'; exact lt_of_le_of_ne this h'
  have xb' : (I.S : ℝ) + 7 / 5 < (B.1 : ℝ) := by
    have := rat_cast_le_of xb.le; push_cast at this
    have h' : ((I.S + 7 / 5 : ℚ) : ℝ) ≠ ((B.1 : ℚ) : ℝ) := by
      rw [Ne, Rat.cast_inj]; exact ne_of_lt xb
    push_cast at h'; exact lt_of_le_of_ne this h'
  have hAB : (0 : ℝ) < B.1 - A.1 := by linarith
  -- the interior point just above the gap edge
  set t : ℝ := (z.1 - A.1) / (B.1 - A.1)
  have ht0 : 0 < t := div_pos (by linarith) hAB
  have ht1 : t < 1 := by rw [div_lt_one hAB]; linarith
  have hsucc : (i + 1) % I.poly.n = i + 1 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨δ₀, hδ₀, hδ⟩ := hKL i (by omega) t ht0 ht1
  rw [hsucc, vi, vi1] at hδ
  set δ := min (δ₀ / 2) ((z.2 - I.H) / (2 * (B.1 - A.1)))
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  have hc := (hδ δ hδpos (lt_of_le_of_lt (min_le_left _ _) (by linarith))).1
  have hceq : ratPoint A + t • (ratPoint B - ratPoint A) + δ • leftNormal (ratPoint A)
      (ratPoint B) = (z.1, (I.H : ℝ) + δ * (B.1 - A.1)) := by
    simp only [leftNormal, ratPoint, ya, yb]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, sub_self, neg_zero,
        mul_zero, add_zero, t]
      field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, sub_self, mul_zero,
        add_zero]
  rw [hceq] at hc
  -- the vertical segment
  set V : Set Point := (fun y : ℝ => (z.1, y)) '' Ioc (I.H : ℝ) z.2
  have hVc : IsPreconnected V :=
    isPreconnected_Ioc.image _ (Continuous.continuousOn (by fun_prop))
  have hVb : V ⊆ I.poly.boundaryᶜ := by
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩ hb
    have := h4 _ hb rfl hy1
    simp only at this; linarith
  have hδle : δ * (B.1 - A.1) ≤ (z.2 - I.H) / 2 := by
    have := min_le_right (δ₀ / 2) ((z.2 - I.H) / (2 * (B.1 - A.1)))
    calc δ * (B.1 - A.1) ≤ (z.2 - I.H) / (2 * (B.1 - A.1)) * (B.1 - A.1) :=
          mul_le_mul_of_nonneg_right this hAB.le
      _ = (z.2 - I.H) / 2 := by field_simp
  have hcV : (z.1, (I.H : ℝ) + δ * (B.1 - A.1)) ∈ V :=
    ⟨_, ⟨by nlinarith, by linarith⟩, rfl⟩
  have := Vis.subset_interior_of_preconnected I.poly hVc hVb hcV hc.1
  exact this ⟨z.2, ⟨h3, le_rfl⟩, rfl⟩

end Gap

/-! ## The boundary of the corridor polygon -/

/-- The edges of the corridor polygon's vertex list: the floor edges, the window, the upper-wall
edges. -/
theorem edgesOf_poly : edgesOf ((I.chainBefore ++ I.chainAfter).map ratPoint) =
    edgesOf (I.chainBefore.map ratPoint) ++ [(ratPoint (c1 I.S I.H), ratPoint (d1 I.S I.H))] ++
      edgesOf (I.chainAfter.map ratPoint) := by
  have hcb : I.chainBefore.map ratPoint =
      (ratPoint (c0 I.S I.H) :: I.floor.map ratPoint) ++ [ratPoint (c1 I.S I.H)] := by
    simp [chainBefore]
  have hca : I.chainAfter.map ratPoint =
      ratPoint (d1 I.S I.H) :: (I.upper.map ratPoint ++ [ratPoint (d0 I.S I.H)]) := by
    simp [chainAfter]
  rw [List.map_append, hcb, hca, edgesOf_append, List.append_assoc, List.singleton_append,
    edgesOf_append]
  simp

section Boundary

variable (hg : I.Good N)
include hg

omit hg in
/-- **Cases for boundary points of the corridor polygon.** -/
theorem poly_boundary_cases {w : Point} (hw : w ∈ I.poly.boundary) :
    (∃ e ∈ edgesOf (I.chainBefore.map ratPoint), w ∈ segOf e) ∨ w ∈ I.window ∨
      (∃ e ∈ edgesOf (I.chainAfter.map ratPoint), w ∈ segOf e) ∨ w ∈ I.entrance := by
  obtain ⟨i, hi, hwi⟩ := hw
  set V := (I.chainBefore ++ I.chainAfter).map ratPoint with hVdef
  have hn : I.poly.n = V.length := by simp [hVdef, poly_n]
  by_cases hlast : i + 1 < I.poly.n
  · -- an edge of the polyline
    have he := mem_edgesOf_getD (L := V) (k := i) (by rw [← hn]; exact hlast)
    have hwi' : w ∈ segOf (V.getD i 0, V.getD (i + 1) 0) := by
      have : (i + 1) % I.poly.n = i + 1 := Nat.mod_eq_of_lt hlast
      rw [Polygon.edge, this] at hwi; exact hwi
    rw [hVdef, edgesOf_poly] at he
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact Or.inl ⟨_, he, hwi'⟩
      · rw [List.mem_singleton] at he
        rw [he] at hwi'
        exact Or.inr (Or.inl hwi')
    · exact Or.inr (Or.inr (Or.inl ⟨_, he, hwi'⟩))
  · -- the closing edge
    have hi' : i = I.poly.n - 1 := by omega
    have hn' : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
      rw [poly_n, List.length_append]
    have hA : 2 ≤ I.chainAfter.length := by rw [chainAfter_length]; omega
    have hB : 2 ≤ I.chainBefore.length := by rw [chainBefore_length]; omega
    rw [Polygon.edge, hi', show (I.poly.n - 1 + 1) % I.poly.n = 0 by
      rw [show I.poly.n - 1 + 1 = I.poly.n by omega, Nat.mod_self]] at hwi
    rw [poly_vtx_after (by omega) (by omega), show I.poly.n - 1 - I.chainBefore.length =
      I.chainAfter.length - 1 by omega, chainAfter_getD_last,
      poly_vtx_before (by omega), chainBefore_getD_zero] at hwi
    exact Or.inr (Or.inr (Or.inr hwi))

/-- The floor edges are on or below the floor line. -/
theorem Good.floor_edges_le {e : Point × Point} (he : e ∈ edgesOf (I.chainBefore.map ratPoint))
    {w : Point} (hw : w ∈ segOf e) : w.2 ≤ (I.H : ℝ) := by
  have hF := hg.floor_box
  have := edges_affine_le (α := 0) (β := 1) (c := (I.H : ℝ)) (L := I.chainBefore.map ratPoint)
    (by
      intro x hx
      rw [chainBefore_map] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · rcases List.mem_append.1 hx with hx | hx
        · have := (hF x hx).2.2.2; simp; linarith
        · rw [List.mem_singleton] at hx; subst hx; simp) e he w hw
  simpa using this

end Boundary

/-! ## The upper wall near pair `k` -/

/-- The vertex after `z0_k` on the upper wall. -/
def nxt (I : Input) (k : ℕ) : ℚ × ℚ := if k + 1 < I.np then I.valley (k + 1) else d0 I.S I.H

theorem chainAfter_inner (hg : I.Good N) {k : ℕ} (hk : k < I.np) :
    ∃ A₁ A₂, I.chainAfter = A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂ := by
  have hp := hg.np_pos
  have hp3 := hg.np_le
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with hnp | hnp | hnp
  · obtain rfl : k = 0 := by omega
    refine ⟨[d1 I.S I.H], [], ?_⟩
    simp [chainAfter, upper_one hnp, upperPair_zero, nxt, hnp]
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine ⟨[d1 I.S I.H], [I.sgPt 1, I.zp 1, I.z1 1, I.n1 1, I.n0 1, I.z0 1, d0 I.S I.H], ?_⟩
      simp [chainAfter, upper_two hnp, upperPair_zero, upperPair_succ, nxt, hnp]
    · refine ⟨[d1 I.S I.H] ++ I.upperPair 0 ++ [I.valley 1], [], ?_⟩
      simp [chainAfter, upper_two hnp, upperPair_zero, upperPair_succ, nxt, hnp]
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · refine ⟨[d1 I.S I.H], [I.sgPt 1, I.zp 1, I.z1 1, I.n1 1, I.n0 1, I.z0 1] ++
        I.upperPair 2 ++ [d0 I.S I.H], ?_⟩
      simp [chainAfter, upper_three hnp, upperPair_zero, upperPair_succ, nxt, hnp]
    · refine ⟨[d1 I.S I.H] ++ I.upperPair 0 ++ [I.valley 1],
        [I.sgPt 2, I.zp 2, I.z1 2, I.n1 2, I.n0 2, I.z0 2, d0 I.S I.H], ?_⟩
      simp [chainAfter, upper_three hnp, upperPair_zero, upperPair_succ, nxt, hnp]
    · refine ⟨[d1 I.S I.H] ++ I.upperPair 0 ++ I.upperPair 1 ++ [I.valley 2], [], ?_⟩
      simp [chainAfter, upper_three hnp, upperPair_zero, upperPair_succ, nxt, hnp]

/-! ## Umbra critical points are corridor points -/

section UmbraMem

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The successor `nxt_k` of `z0_k` is far west of the apex. -/
theorem Good.lX_nxt : I.lX (I.nxt k) ≤ (I.rwE k - I.lwE k) / 2 - 53 := by
  by_cases h : k + 1 < I.np
  · rw [nxt, ite_eq_left h, lX_valley hg h, hg.rwE_succ h,
      show k + 1 - 1 = k by omega]
    linarith
  · rw [nxt, ite_eq_right h, lX_d0]
    have := hg.window_apex hk; have := hg.scale.S_ge; have := hg.N_ge; have := hg.S_eq
    rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nlinarith

/-- The edge `z0_k → nxt_k` has slope at most `101/100` (in local coordinates). -/
theorem Good.nxt_slope : I.lY (I.z0 k) - I.lY (I.nxt k) ≤
    101 / 100 * (I.lX (I.z0 k) - I.lX (I.nxt k)) ∧ 0 ≤ I.lX (I.z0 k) - I.lX (I.nxt k) := by
  have hn := hg.lX_nxt hk
  rw [lX_z0 hg hk, lY_z0 hg hk]
  refine ⟨?_, by linarith⟩
  by_cases h : k + 1 < I.np
  · rw [nxt, ite_eq_left h, lX_valley hg h, lY_valley hg h, hg.rwE_succ h,
      show k + 1 - 1 = k by omega]
    linarith
  · rw [nxt, ite_eq_right h, lX_d0, lY_d0 hg]
    have := hg.window_apex hk; have := hg.ab_bound hk
    have := hg.scale.S_ge; have := hg.N_ge; have := hg.S_eq
    rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((I.lwE k + I.rwE k) / 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> nlinarith

omit hk in
/-- `lX` is monotone in the abscissa. -/
theorem lX_mono {p q : ℚ × ℚ} (h : p.1 ≤ q.1) : I.lX p ≤ I.lX q := by
  have hS := hg.S_pos
  simp only [lX_def]
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

omit hk in
/-- A point whose local abscissa is in the window is within `1/5` of the corridor's middle. -/
theorem Good.near_of_lXR {z : Point} (h : |I.lXR z| ≤ 456 * (N : ℝ)) :
    |z.1 - ((I.S : ℝ) + 1)| ≤ 1 / 5 := by
  have hS8 : (800000 : ℝ) ≤ I.S := by exact_mod_cast hg.scale.S_ge
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hSe : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  have h8 : (0 : ℝ) < 8 * I.S := by linarith
  have e : z.1 - ((I.S : ℝ) + 1) = I.lXR z / (8 * I.S) := by
    simp only [lXR]; field_simp
  rw [e, abs_div, abs_of_pos h8, div_le_iff₀ h8]
  nlinarith

omit hk in
/-- Same for the local ordinate. -/
theorem Good.near_of_lYR {z : Point} (h : |I.lYR z| ≤ 456 * (N : ℝ)) :
    |z.2 - ((I.H : ℝ) + 1)| ≤ 1 / 5 := by
  have hS8 : (800000 : ℝ) ≤ I.S := by exact_mod_cast hg.scale.S_ge
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hSe : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  have h8 : (0 : ℝ) < 8 * I.S := by linarith
  have e : z.2 - ((I.H : ℝ) + 1) = I.lYR z / (8 * I.S) := by
    simp only [lYR]; field_simp
  rw [e, abs_div, abs_of_pos h8, div_le_iff₀ h8]
  nlinarith

/-- **The upper wall above the umbra critical points.**  A point `w` of the upper wall whose local
abscissa is within `31/5` of the apex has local ordinate at least `Y_a − 7`. -/
theorem Good.upper_above {w : Point} {e : Point × Point}
    (he : e ∈ edgesOf (I.chainAfter.map ratPoint)) (hwe : w ∈ segOf e)
    (hx : |I.lXR w - (((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2| ≤ 31 / 5) :
    (((I.lwE k : ℚ) : ℝ) + ((I.rwE k : ℚ) : ℝ)) / 2 - 7 ≤ I.lYR w := by
  rw [abs_le] at hx
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
  have hmono := hg.xMonoQ_chainAfter
  rw [hA] at hmono he
  have hsplit : (A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂).map
      ratPoint = ((A₁ ++ [I.sgPt k]).map ratPoint) ++ ratPoint (I.zp k) ::
        ([ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k), ratPoint (I.z0 k)] ++
          ratPoint (I.nxt k) :: A₂.map ratPoint) := by simp
  rw [hsplit, edgesOf_append, List.mem_append] at he
  rcases he with he | he
  · -- right part: all vertices weakly right of `z'_k`
    exfalso
    have hpre := XMonoQ.prefix_ge (A := A₁ ++ [I.sgPt k]) (m := I.zp k)
      (B := [I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂) (by simpa using hmono)
    have hzp : (I.rwE k - I.lwE k) / 2 + 16 - 3 / 16 ≤ I.lX (I.zp k) := by
      have := hg.lX_zp hk; rw [abs_le] at this; linarith
    have key : (((I.rwE k - I.lwE k) / 2 + 16 - 3 / 16 : ℚ) : ℝ) ≤ I.lXR w := by
      refine edges_lerp_ge lXR_lerp ?_ e he w hwe
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        rw [lXR_ratPoint]; exact_mod_cast hzp.trans (lX_mono hg (hpre y hy))
      · rw [List.mem_singleton] at hx; subst hx; rw [lXR_ratPoint]; exact_mod_cast hzp
    push_cast at key; linarith
  rw [show ratPoint (I.zp k) :: ([ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k),
      ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint) =
      [ratPoint (I.zp k), ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k),
        ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint from rfl,
    edgesOf_append, List.mem_append] at he
  rcases he with he | he
  · -- the five local edges
    simp only [List.cons_append, List.nil_append, edgesOf_cons_cons, edgesOf_single,
      List.mem_cons, List.not_mem_nil, or_false] at he
    have z1y : (((I.lwE k + I.rwE k) / 2 - 3 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.z1 k)) := by
      rw [lYR_ratPoint, lY_z1 hg hk]
    have z0y : (((I.lwE k + I.rwE k) / 2 - 3 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.z0 k)) := by
      rw [lYR_ratPoint, lY_z0 hg hk]
    have n1y : (((I.lwE k + I.rwE k) / 2 - 3 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.n1 k)) := by
      rw [lYR_ratPoint]; have := hg.lY_n1 hk; rw [abs_le] at this
      exact rat_cast_le_of (by linarith)
    have n0y : (((I.lwE k + I.rwE k) / 2 - 3 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.n0 k)) := by
      rw [lYR_ratPoint]; have := hg.lY_n0 hk; rw [abs_le] at this
      exact rat_cast_le_of (by linarith)
    push_cast at z1y z0y n1y n0y
    rcases he with rfl | rfl | rfl | rfl | rfl
    · -- `z'_k → z1`: `ξ ≥ r − 5/16`
      have hsum : Lerp (fun p => I.lYR p + I.lXR p) := by
        intro p q t; simp only [lXR, lYR]; ring
      have a1 : ((I.rwE k - 5 / 16 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.zp k)) +
          I.lXR (ratPoint (I.zp k)) := by
        rw [lYR_ratPoint, lXR_ratPoint, ← Rat.cast_add]
        have h1 := hg.lX_zp hk; have h2 := hg.lY_zp hk; rw [abs_le] at h1 h2
        exact rat_cast_le_of (by linarith)
      have a2 : ((I.rwE k - 5 / 16 : ℚ) : ℝ) ≤ I.lYR (ratPoint (I.z1 k)) +
          I.lXR (ratPoint (I.z1 k)) := by
        rw [lYR_ratPoint, lXR_ratPoint, ← Rat.cast_add, lX_z1 hg hk, lY_z1 hg hk]
        exact rat_cast_le_of (by linarith)
      have := seg_lerp_ge hsum hwe a1 a2
      push_cast at this; linarith
    · have := seg_lerp_ge lYR_lerp hwe z1y n1y; linarith
    · have := seg_lerp_ge lYR_lerp hwe n1y n0y; linarith
    · have := seg_lerp_ge lYR_lerp hwe n0y z0y; linarith
    · -- `z0 → nxt`: slope at most `101/100`
      obtain ⟨sl1, sl2⟩ := hg.nxt_slope hk
      have s1 := rat_cast_le_of sl1
      have s2 := rat_cast_le_of sl2
      push_cast at s1 s2
      rw [← lXR_ratPoint, ← lXR_ratPoint, ← lYR_ratPoint, ← lYR_ratPoint] at s1
      rw [← lXR_ratPoint, ← lXR_ratPoint] at s2
      have := seg_height_ge (f := I.lXR) (g := I.lYR) lXR_lerp lYR_lerp hwe s1
      have z0x : I.lXR (ratPoint (I.z0 k)) =
          (((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2 - 3 := by
        rw [lXR_ratPoint, lX_z0 hg hk]; push_cast; ring
      rw [z0x] at this
      linarith
  · -- the left part: all vertices weakly left of `nxt_k`
    exfalso
    have hsuf : XMonoQ (I.nxt k :: A₂) := XMonoQ.of_append
      (A := A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k]) (by simpa using hmono)
    have hle := hsuf.le_head
    have hneg : Lerp (fun p => -I.lXR p) := by
      intro p q t; simp only [lXR]; ring
    have hnx := hg.lX_nxt hk
    have key : -(((I.rwE k - I.lwE k) / 2 - 53 : ℚ) : ℝ) ≤ -I.lXR w := by
      refine edges_lerp_ge hneg ?_ e he w hwe
      intro x hx
      rw [← List.map_cons] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [lXR_ratPoint, neg_le_neg_iff]
      exact rat_cast_le_of ((lX_mono hg (hle y hy)).trans hnx)
    push_cast at key; linarith

/-- **Umbra critical points are interior points of the corridor.** -/
theorem Good.umbra_crit_mem {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁)
    (h₁' : v₁ ≤ 3 / 2) : (I.umbraR k).X v₀ v₁ ∈ I.poly.filled \ I.poly.boundary := by
  obtain ⟨-, -, -, -, hzX, hzY1, hzY2⟩ := hg.umbra_crit_eps hk h₀ h₀' h₁ h₁'
  set z := (I.umbraR k).X v₀ v₁ with hz
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hw : |(((I.rwE k - I.lwE k) / 2 : ℚ) : ℝ)| + 20 ≤ 456 * (N : ℝ) := by
    have h' := rat_cast_le_of (hg.window_apex hk)
    push_cast at h' ⊢; exact h'
  have hab : |(((I.lwE k + I.rwE k) / 2 : ℚ) : ℝ)| ≤ 68 * (N : ℝ) + 410 := by
    have h' := rat_cast_le_of (hg.ab_bound hk)
    push_cast at h' ⊢; exact h'
  push_cast at hw hab
  have hzX' := hzX
  have hw2 : |(((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2| ≤ 456 * (N : ℝ) - 20 := by
    linarith
  rw [abs_le] at hzX hw2 hab
  have hx := hg.near_of_lXR (z := z) (by rw [abs_le]; constructor <;> linarith)
  have hy := hg.near_of_lYR (z := z) (by rw [abs_le]; constructor <;> linarith)
  rw [abs_le] at hx hy
  refine hg.mem_poly_of_vertical (by linarith) (by linarith) (by linarith) ?_
  -- boundary points above `z` on its vertical
  intro w hwb hwx hwy
  have hwxl : I.lXR w = I.lXR z := by simp only [lXR, hwx]
  rcases poly_boundary_cases hwb with ⟨e, he, hwe⟩ | hwin | ⟨e, he, hwe⟩ | hent
  · exact absurd (hg.floor_edges_le he hwe) (not_le.2 hwy)
  · exfalso
    rw [window, ratPoint_c1', ratPoint_d1'] at hwin
    have := seg_fst_of_vertical hwin rfl
    simp only at this
    rw [hwx] at this; linarith
  · have h1 := hg.upper_above hk he hwe (by rw [hwxl]; exact hzX')
    have h8 : (0 : ℝ) < 8 * I.S := by
      have := hg.S_pos; have : (0 : ℝ) < I.S := by exact_mod_cast this
      linarith
    have h2 : 0 < 8 * (I.S : ℝ) * (w.2 - z.2) := by
      have : I.lYR z < I.lYR w := by linarith
      simp only [lYR] at this; linarith
    have := (mul_pos_iff_of_pos_left h8).1 h2
    linarith
  · exfalso
    rw [entrance, ratPoint_d0', ratPoint_c0'] at hent
    have := seg_fst_of_vertical hent rfl
    simp only at this
    rw [hwx] at this; linarith

end UmbraMem

/-! ## The nook top edge is on the boundary -/

/-- The nook top edge `[n0_k, n1_k]` is an edge of the corridor polygon. -/
theorem Good.nook_edge_boundary (hg : I.Good N) {k : ℕ} (hk : k < I.np) {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    z ∈ I.poly.boundary := by
  have hKn : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
    rw [poly_n, List.length_append]
  have hA2 : 2 ≤ I.chainAfter.length := by rw [chainAfter_length]; omega
  have hn : 0 < I.poly.n := by omega
  have hch : ∀ j < I.chainAfter.length, I.poly.vtx ((I.chainBefore.length + j) % I.poly.n) =
      ratPoint (I.chainAfter.getD j 0) := by
    intro j hj
    rw [Nat.mod_eq_of_lt (by omega), poly_vtx_after (by omega) (by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
  have hA' : I.chainAfter = (A₁ ++ [I.sgPt k, I.zp k, I.z1 k]) ++ [I.n1 k, I.n0 k, I.z0 k] ++
      ([I.nxt k] ++ A₂) := by rw [hA]; simp
  obtain ⟨-, -, -, h4, h5⟩ := vtx_triple hn hch hA'
  refine ⟨(I.chainBefore.length + (A₁ ++ [I.sgPt k, I.zp k, I.z1 k]).length) % I.poly.n,
    Nat.mod_lt _ hn, ?_⟩
  rw [Polygon.edge, h4, h5, Geometry.segment_comm]
  exact hz

/-! ## The corridor region lies in `P` -/

/-- **Clearance of the corridor.** The boundary of `P` meets the corridor region only in the
corridor polygon's boundary. -/
def CorridorClear (P : Polygon) (I : Input) : Prop :=
  ∀ w ∈ P.boundary, w ∈ I.poly.filled → w ∈ I.poly.boundary

section Subset

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b)
include hg hP hL hC

/-- An interior point of the corridor polygon just above its first floor edge lies in `P`. -/
theorem Good.exists_interior_mem :
    ∃ c ∈ I.poly.filled \ I.poly.boundary, c ∈ P.filled := by
  have hK := hg.poly_simple
  have hKL := hg.poly_interiorLeft
  have hn : 0 < P.n := by have := hP.1; omega
  have hB2 : 2 ≤ I.chainBefore.length := by rw [chainBefore_length]; omega
  have hKn3 := hK.1
  have hKn : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
    rw [poly_n, List.length_append]
  have hv : I.poly.vtx 0 = P.vtx ((a + 0) % P.n) := by
    rw [poly_vtx_before (by omega), hC.before 0 (by omega)]
  have hnext : I.poly.vtx ((0 + 1) % I.poly.n) = P.vtx (((a + 0) % P.n + 1) % P.n) := by
    rw [Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega : 0 + 1 < I.poly.n),
      poly_vtx_before (by omega), hC.before 1 (by omega)]
  obtain ⟨ε, hε, hnear⟩ := filled_iff_near_edge hP hL hK hKL (Nat.mod_lt _ hn) (by omega) hv hnext
    (t := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨δ₀, hδ₀, hδ⟩ := hKL 0 (by omega) (1 / 2) (by norm_num) (by norm_num)
  set nv := leftNormal (I.poly.vtx 0) (I.poly.vtx ((0 + 1) % I.poly.n))
  set δ := min (δ₀ / 2) (ε / (2 * (‖nv‖ + 1)))
  have hn1 : 0 < ‖nv‖ + 1 := by positivity
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos hε (by positivity))
  have hc := (hδ δ hδpos (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  refine ⟨_, hc.1, (hnear _ ?_).2 hc.1.1⟩
  rw [← hv, ← hnext, Geometry.lerp_eq_add_smul, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hδpos]
  have h1 : δ ≤ ε / (2 * (‖nv‖ + 1)) := min_le_right _ _
  have h2 : δ * ‖nv‖ ≤ ε / (2 * (‖nv‖ + 1)) * ‖nv‖ :=
    mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have h3 : ε / (2 * (‖nv‖ + 1)) * ‖nv‖ < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg nv]
  linarith

/-- **The corridor region lies in `P`**, provided the boundary of `P` meets it only in the
corridor polygon's boundary. -/
theorem Good.poly_subset (hcl : CorridorClear P I) : I.poly.filled ⊆ P.filled := by
  have hK := hg.poly_simple
  obtain ⟨c, hcK, hcP⟩ := hg.exists_interior_mem hP hL hC
  have hsub : I.poly.filled \ I.poly.boundary ⊆ P.boundaryᶜ := by
    rintro w ⟨hwK, hwnb⟩ hwP
    exact hwnb (hcl w hwP hwK)
  have hint := Vis.subset_interior_of_preconnected P (Jordan.filled_sdiff_boundary_connected hK)
    hsub hcK hcP
  calc I.poly.filled ⊆ closure (I.poly.filled \ I.poly.boundary) :=
        Polygon.filled_subset_closure_interior hK
    _ ⊆ closure P.filled := closure_mono (hint.trans sdiff_subset)
    _ = P.filled := (Polygon.isClosed_filled P).closure_eq

end Subset

end Input

end ArtGallery.Sec5.Corridor


end
