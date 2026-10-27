module

public import ArtGallery.Hardness.Sec5.CoverCanon

/-!
# Section 5, sufficiency (vi): tools for the channel of a unit (template coordinates)

In the template coordinates of a unit (`Tmpl.ChainAt`, integer template points scaled by `D`) the
window `c1 d1` of the corridor is at `x = −D S`, `y ∈ [D S, D S + 3D/2]`.  Points depending on
the scale `S` are written `p₀ + S p₁` with integer `p₀, p₁` (`SPt`); the orientation determinant of
three such points is a quadratic polynomial in `S` with integer coefficients (`qdet`), whose sign
for all `S ≥ 800000` is checked by `qnn` / `qps` (`qnn_sound`, `qps_sound`).

* **The channel** `chanSet c1 V₀ V_l d1` (`V₀`, `V_l` the first and last template vertex): the
  convex quadrilateral bounded by the lower channel wall `c1 V₀`, the mouth `V₀ V_l`, the upper
  wall `V_l d1` and the window `d1 c1`.  `chanSet_subset_hull`: it is the hull of its corners;
  `interior_chanSet`: its interior points satisfy the four strict inequalities.
* **Chain edges outside the channel** (`edgeOutB`): a chain edge has both ends weakly outside one
  side of the channel, or strictly outside an extra separating line.
* **Bilinear corner tests** (`det_nonneg_of_corners`): `det g w M` for `g`, `w` on two segments is
  nonnegative if it is at the four corners.
-/

@[expose] public section

namespace ArtGallery.Sec5.CoverT

open ArtGallery Set Polygon Vis.Cert Tmpl
open ArtGallery.Irrational (HP)

/-! ### Points affine in the scale -/

/-- A point `p₀ + S p₁` with integer `p₀`, `p₁`. -/
abbrev SPt : Type := IPt × IPt

/-- The real point `p₀ + S p₁`. -/
noncomputable def SPt.pt (p : SPt) (S : ℝ) : Point :=
  ((p.1.1 : ℝ) + S * p.2.1, (p.1.2 : ℝ) + S * p.2.2)

/-- A constant point. -/
def sc (p : IPt) : SPt := (p, (0, 0))

@[simp] theorem sc_pt (p : IPt) (S : ℝ) : (sc p).pt S = intPoint p := by
  simp [SPt.pt, sc, intPoint]

/-- The cross product of integer vectors. -/
def icross (u v : IPt) : ℤ := u.1 * v.2 - u.2 * v.1

/-- The difference of integer vectors. -/
def isub (u v : IPt) : IPt := (u.1 - v.1, u.2 - v.2)

/-- The coefficients `(a₀, a₁, a₂)` of `det a b c = a₀ + a₁ S + a₂ S²`. -/
def qdet (a b c : SPt) : ℤ × ℤ × ℤ :=
  (icross (isub b.1 a.1) (isub c.1 a.1),
    icross (isub b.1 a.1) (isub c.2 a.2) + icross (isub b.2 a.2) (isub c.1 a.1),
    icross (isub b.2 a.2) (isub c.2 a.2))

/-- The value of a quadratic polynomial. -/
noncomputable def qval (q : ℤ × ℤ × ℤ) (S : ℝ) : ℝ := q.1 + q.2.1 * S + q.2.2 * S ^ 2

theorem det_pt (a b c : SPt) (S : ℝ) : det (a.pt S) (b.pt S) (c.pt S) = qval (qdet a b c) S := by
  simp only [det, SPt.pt, qval, qdet, icross, isub]
  push_cast; ring

/-- The negated polynomial. -/
def qneg (q : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-q.1, -q.2.1, -q.2.2)

theorem qval_qneg (q : ℤ × ℤ × ℤ) (S : ℝ) : qval (qneg q) S = - qval q S := by
  simp only [qval, qneg]; push_cast; ring

/-- The lower bound of the scale. -/
def S0 : ℤ := 800000

/-- `a₀ + a₁ S + a₂ S² ≥ 0` for all `S ≥ S₀` (sufficient test). -/
def qnn (q : ℤ × ℤ × ℤ) : Bool :=
  inonneg q.2.2 && inonneg (2 * q.2.2 * S0 + q.2.1) && inonneg (q.2.2 * S0 * S0 + q.2.1 * S0 + q.1)

/-- `a₀ + a₁ S + a₂ S² > 0` for all `S ≥ S₀` (sufficient test). -/
def qps (q : ℤ × ℤ × ℤ) : Bool :=
  inonneg q.2.2 && inonneg (2 * q.2.2 * S0 + q.2.1) && ipos (q.2.2 * S0 * S0 + q.2.1 * S0 + q.1)

theorem quad_ge {a0 a1 a2 S : ℝ} (h2 : 0 ≤ a2) (h1 : 0 ≤ 2 * a2 * 800000 + a1)
    (hS : 800000 ≤ S) :
    a2 * 800000 * 800000 + a1 * 800000 + a0 ≤ a0 + a1 * S + a2 * S ^ 2 := by
  have e : a0 + a1 * S + a2 * S ^ 2 - (a2 * 800000 * 800000 + a1 * 800000 + a0) =
      (S - 800000) * (a2 * (S + 800000) + a1) := by ring
  have k1 : 0 ≤ S - 800000 := by linarith
  have k2 : 0 ≤ a2 * (S + 800000) + a1 := by nlinarith
  nlinarith [mul_nonneg k1 k2]

theorem qnn_sound {q : ℤ × ℤ × ℤ} (h : qnn q = true) {S : ℝ} (hS : 800000 ≤ S) :
    0 ≤ qval q S := by
  simp only [qnn, Bool.and_eq_true, inonneg_iff, S0] at h
  obtain ⟨⟨h2, h1⟩, h0⟩ := h
  have h2' : (0 : ℝ) ≤ q.2.2 := by exact_mod_cast h2
  have h1' : (0 : ℝ) ≤ 2 * q.2.2 * 800000 + q.2.1 := by exact_mod_cast h1
  have h0' : (0 : ℝ) ≤ q.2.2 * 800000 * 800000 + q.2.1 * 800000 + q.1 := by exact_mod_cast h0
  have := quad_ge h2' h1' hS (a0 := (q.1 : ℝ))
  simp only [qval]; linarith

theorem qps_sound {q : ℤ × ℤ × ℤ} (h : qps q = true) {S : ℝ} (hS : 800000 ≤ S) :
    0 < qval q S := by
  simp only [qps, Bool.and_eq_true, inonneg_iff, ipos_iff, S0] at h
  obtain ⟨⟨h2, h1⟩, h0⟩ := h
  have h2' : (0 : ℝ) ≤ q.2.2 := by exact_mod_cast h2
  have h1' : (0 : ℝ) ≤ 2 * q.2.2 * 800000 + q.2.1 := by exact_mod_cast h1
  have h0' : (0 : ℝ) < q.2.2 * 800000 * 800000 + q.2.1 * 800000 + q.1 := by exact_mod_cast h0
  have := quad_ge h2' h1' hS (a0 := (q.1 : ℝ))
  simp only [qval]; linarith

/-- `det a b c ≥ 0` for all `S ≥ S₀`. -/
theorem det_nonneg_of_qnn {a b c : SPt} (h : qnn (qdet a b c) = true) {S : ℝ}
    (hS : 800000 ≤ S) : 0 ≤ det (a.pt S) (b.pt S) (c.pt S) := by
  rw [det_pt]; exact qnn_sound h hS

/-- `det a b c ≤ 0` for all `S ≥ S₀`. -/
theorem det_nonpos_of_qnn {a b c : SPt} (h : qnn (qneg (qdet a b c)) = true) {S : ℝ}
    (hS : 800000 ≤ S) : det (a.pt S) (b.pt S) (c.pt S) ≤ 0 := by
  have := qnn_sound h hS
  rw [qval_qneg] at this; rw [det_pt]; linarith

/-- `det a b c > 0` for all `S ≥ S₀`. -/
theorem det_pos_of_qps {a b c : SPt} (h : qps (qdet a b c) = true) {S : ℝ}
    (hS : 800000 ≤ S) : 0 < det (a.pt S) (b.pt S) (c.pt S) := by
  rw [det_pt]; exact qps_sound h hS

/-- `det a b c < 0` for all `S ≥ S₀`. -/
theorem det_neg_of_qps {a b c : SPt} (h : qps (qneg (qdet a b c)) = true) {S : ℝ}
    (hS : 800000 ≤ S) : det (a.pt S) (b.pt S) (c.pt S) < 0 := by
  have := qps_sound h hS
  rw [qval_qneg] at this; rw [det_pt]; linarith

/-- The value of a half-plane at an affine point: `(g(p₀), g₁ · p₁, 0)`. -/
def qhp (g : HP) (p : SPt) : ℤ × ℤ × ℤ :=
  (g.1 * p.1.1 + g.2.1 * p.1.2 + g.2.2, g.1 * p.2.1 + g.2.1 * p.2.2, 0)

theorem val_pt (g : HP) (p : SPt) (S : ℝ) : g.val (p.pt S) = qval (qhp g p) S := by
  simp only [Irrational.HP.val, SPt.pt, qval, qhp]; push_cast; ring

/-! ### Affine functions on segments -/

theorem nonneg_lerp {f₀ f₁ t : ℝ} (h₀ : 0 ≤ f₀) (h₁ : 0 ≤ f₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) * f₀ + t * f₁ := by
  have : 0 ≤ 1 - t := by linarith
  positivity

/-- **Bilinear corner test.**  `det g w M ≥ 0` for `g ∈ [g₀, g₁]`, `w ∈ [w₀, w₁]` if it holds at
the four corners. -/
theorem det_nonneg_of_corners {g₀ g₁ w₀ w₁ M g w : Point}
    (h00 : 0 ≤ det g₀ w₀ M) (h01 : 0 ≤ det g₀ w₁ M) (h10 : 0 ≤ det g₁ w₀ M)
    (h11 : 0 ≤ det g₁ w₁ M) (hg : g ∈ ArtGallery.segment g₀ g₁)
    (hw : w ∈ ArtGallery.segment w₀ w₁) : 0 ≤ det g w M := by
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hg
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hw
  rw [Geometry.det_lerp_left, Geometry.det_lerp_mid, Geometry.det_lerp_mid]
  exact nonneg_lerp (nonneg_lerp h00 h01 ht0 ht1) (nonneg_lerp h10 h11 ht0 ht1) hs0 hs1

/-- An affine function nonnegative at the ends is nonnegative on the segment (for `det a b ·`). -/
theorem det_nonneg_of_ends {a b p q z : Point} (hp : 0 ≤ det a b p) (hq : 0 ≤ det a b q)
    (hz : z ∈ ArtGallery.segment p q) : 0 ≤ det a b z := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rw [Geometry.det_lerp]; exact nonneg_lerp hp hq ht0 ht1

theorem det_nonpos_of_ends {a b p q z : Point} (hp : det a b p ≤ 0) (hq : det a b q ≤ 0)
    (hz : z ∈ ArtGallery.segment p q) : det a b z ≤ 0 := by
  have := det_nonneg_of_ends (a := b) (b := a) (p := p) (q := q)
    (by rw [Geometry.det_swap12]; linarith) (by rw [Geometry.det_swap12]; linarith) hz
  rw [Geometry.det_swap12] at this; linarith

theorem val_neg_of_ends {g : HP} {p q z : Point} (hp : g.val p < 0) (hq : g.val q < 0)
    (hz : z ∈ ArtGallery.segment p q) : g.val z < 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rw [Irrational.HP.val_lerp]
  exact neg_of_lerp hp hq ht0 ht1

/-! ### The channel -/

/-- The convex quadrilateral `c1 V₀ V_l d1` (counter-clockwise). -/
def chanSet (c1 v0 vl d1 : Point) : Set Point :=
  {z | 0 ≤ det c1 v0 z ∧ 0 ≤ det v0 vl z ∧ 0 ≤ det vl d1 z ∧ 0 ≤ det d1 c1 z}

section Chan

variable {c1 v0 vl d1 : Point}

/-- The corners turn left. -/
structure Corners (c1 v0 vl d1 : Point) : Prop where
  t0 : 0 < det c1 v0 vl
  t1 : 0 < det v0 vl d1
  t2 : 0 < det vl d1 c1
  t3 : 0 < det d1 c1 v0

theorem convex_halfdet (a b : Point) : Convex ℝ {z : Point | 0 ≤ det a b z} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  have hs' : s = 1 - t := by linarith
  subst hs'
  have e : (1 - t) • x + t • y = Geometry.lerp x y t := by
    simp only [Geometry.lerp]; ext <;> simp <;> ring
  rw [e, Geometry.det_lerp]
  positivity

theorem isClosed_halfdet (a b : Point) : IsClosed {z : Point | 0 ≤ det a b z} :=
  isClosed_le continuous_const (by unfold det; fun_prop)

theorem convex_chanSet : Convex ℝ (chanSet c1 v0 vl d1) := by
  have : chanSet c1 v0 vl d1 = {z | 0 ≤ det c1 v0 z} ∩ {z | 0 ≤ det v0 vl z} ∩
      {z | 0 ≤ det vl d1 z} ∩ {z | 0 ≤ det d1 c1 z} := by
    ext z; simp [chanSet, and_assoc]
  rw [this]
  exact (((convex_halfdet _ _).inter (convex_halfdet _ _)).inter (convex_halfdet _ _)).inter
    (convex_halfdet _ _)

theorem isClosed_chanSet : IsClosed (chanSet c1 v0 vl d1) := by
  have : chanSet c1 v0 vl d1 = {z | 0 ≤ det c1 v0 z} ∩ {z | 0 ≤ det v0 vl z} ∩
      {z | 0 ≤ det vl d1 z} ∩ {z | 0 ≤ det d1 c1 z} := by
    ext z; simp [chanSet, and_assoc]
  rw [this]
  exact (((isClosed_halfdet _ _).inter (isClosed_halfdet _ _)).inter (isClosed_halfdet _ _)).inter
    (isClosed_halfdet _ _)

/-- An interior point of a closed half-plane `{det a b · ≥ 0}` (`a ≠ b`) is strictly inside. -/
theorem det_pos_of_interior {a b z : Point} {C : Set Point} (hab : a ≠ b)
    (hC : C ⊆ {w | 0 ≤ det a b w}) (hz : z ∈ interior C) : 0 < det a b z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hz0 : 0 ≤ det a b z := hC (interior_subset hz)
  rcases hz0.lt_or_eq with h | h
  · exact h
  exfalso
  -- move along the right normal
  set n : Point := (b.2 - a.2, -(b.1 - a.1)) with hn
  have hn2 : 0 < n.1 ^ 2 + n.2 ^ 2 := by
    rcases ne_or_eq a.1 b.1 with h1 | h1
    · have : n.2 ≠ 0 := by simp only [hn]; intro h'; apply h1; linarith
      positivity
    · have h2 : a.2 ≠ b.2 := fun h2 => hab (Prod.ext h1 h2)
      have : n.1 ≠ 0 := by simp only [hn]; intro h'; apply h2; linarith
      positivity
  set r : ℝ := ε / (2 * (|n.1| + |n.2| + 1))
  have hr : 0 < r := by positivity
  have hmem : z + r • n ∈ interior C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    have hnn : ‖n‖ ≤ |n.1| + |n.2| := by
      rw [Prod.norm_def]
      exact max_le (by rw [Real.norm_eq_abs]; linarith [abs_nonneg n.2])
        (by rw [Real.norm_eq_abs]; linarith [abs_nonneg n.1])
    have h1 : r * ‖n‖ ≤ r * (|n.1| + |n.2|) := mul_le_mul_of_nonneg_left hnn hr.le
    have h2 : r * (|n.1| + |n.2|) < ε := by
      simp only [r]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg n.1, abs_nonneg n.2]
    linarith
  have := hC (interior_subset hmem)
  simp only [mem_ofPred_eq, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, hn] at this h
  nlinarith [mul_pos hr hn2]

theorem Corners.ne01 (h : Corners c1 v0 vl d1) : c1 ≠ v0 := fun e => by
  have := h.t0; rw [e, Geometry.det_self_left] at this; exact lt_irrefl _ this
theorem Corners.ne12 (h : Corners c1 v0 vl d1) : v0 ≠ vl := fun e => by
  have := h.t1; rw [e, Geometry.det_self_left] at this; exact lt_irrefl _ this
theorem Corners.ne23 (h : Corners c1 v0 vl d1) : vl ≠ d1 := fun e => by
  have := h.t2; rw [e, Geometry.det_self_left] at this; exact lt_irrefl _ this
theorem Corners.ne30 (h : Corners c1 v0 vl d1) : d1 ≠ c1 := fun e => by
  have := h.t3; rw [e, Geometry.det_self_left] at this; exact lt_irrefl _ this

/-- **Interior points of the channel** satisfy the four strict inequalities. -/
theorem interior_chanSet (h : Corners c1 v0 vl d1) {z : Point}
    (hz : z ∈ interior (chanSet c1 v0 vl d1)) :
    0 < det c1 v0 z ∧ 0 < det v0 vl z ∧ 0 < det vl d1 z ∧ 0 < det d1 c1 z :=
  ⟨det_pos_of_interior h.ne01 (fun _ hw => hw.1) hz,
    det_pos_of_interior h.ne12 (fun _ hw => hw.2.1) hz,
    det_pos_of_interior h.ne23 (fun _ hw => hw.2.2.1) hz,
    det_pos_of_interior h.ne30 (fun _ hw => hw.2.2.2) hz⟩

/-- The open quadrilateral is open. -/
theorem isOpen_chanStrict : IsOpen {z : Point | 0 < det c1 v0 z ∧ 0 < det v0 vl z ∧
    0 < det vl d1 z ∧ 0 < det d1 c1 z} := by
  have hc : ∀ a b : Point, Continuous fun z : Point => det a b z := fun a b => by
    unfold det; fun_prop
  exact ((isOpen_lt continuous_const (hc _ _)).inter ((isOpen_lt continuous_const (hc _ _)).inter
    ((isOpen_lt continuous_const (hc _ _)).inter (isOpen_lt continuous_const (hc _ _)))))

/-- Points satisfying the strict inequalities are interior points. -/
theorem mem_interior_chanSet {z : Point}
    (hz : 0 < det c1 v0 z ∧ 0 < det v0 vl z ∧ 0 < det vl d1 z ∧ 0 < det d1 c1 z) :
    z ∈ interior (chanSet c1 v0 vl d1) :=
  interior_maximal (fun w hw => (⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩ :
    w ∈ chanSet c1 v0 vl d1)) isOpen_chanStrict hz

/-- **The channel is the hull of its corners.** -/
theorem chanSet_subset_hull (h : Corners c1 v0 vl d1) :
    chanSet c1 v0 vl d1 ⊆ convexHull ℝ {c1, v0, vl, d1} := by
  intro z ⟨h0, h1, h2, h3⟩
  have k1 : 0 < det c1 vl d1 := by rw [← Geometry.det_cyclic]; exact h.t2
  have s1 : ({c1, v0, vl} : Set Point) ⊆ {c1, v0, vl, d1} := by
    intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto
  have s2 : ({c1, vl, d1} : Set Point) ⊆ {c1, v0, vl, d1} := by
    intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto
  rcases le_total (det c1 vl z) 0 with hz | hz
  · refine convexHull_mono s1 ((Geometry.mem_triangle_iff_bary h.t0.ne').2 ⟨?_, ?_, ?_⟩)
    · unfold Geometry.bary₁; rw [← Geometry.det_cyclic]; exact div_nonneg h1 h.t0.le
    · unfold Geometry.bary₂
      refine div_nonneg ?_ h.t0.le
      linarith [Geometry.det_swap23 c1 vl z]
    · unfold Geometry.bary₃; exact div_nonneg h0 h.t0.le
  · refine convexHull_mono s2 ((Geometry.mem_triangle_iff_bary k1.ne').2 ⟨?_, ?_, ?_⟩)
    · unfold Geometry.bary₁; rw [← Geometry.det_cyclic]; exact div_nonneg h2 k1.le
    · unfold Geometry.bary₂
      refine div_nonneg ?_ k1.le
      linarith [Geometry.det_cyclic d1 c1 z]
    · unfold Geometry.bary₃; exact div_nonneg hz k1.le

/-- An affine function (of the form `det a b ·` or `g.val`) nonnegative at the corners is
nonnegative on the channel. -/
theorem nonneg_on_chanSet (h : Corners c1 v0 vl d1) {f : Point → ℝ}
    (hf : Convex ℝ {z | 0 ≤ f z}) (h0 : 0 ≤ f c1) (h1 : 0 ≤ f v0) (h2 : 0 ≤ f vl)
    (h3 : 0 ≤ f d1) {z : Point} (hz : z ∈ chanSet c1 v0 vl d1) : 0 ≤ f z := by
  have := convexHull_min (s := ({c1, v0, vl, d1} : Set Point)) (t := {z | 0 ≤ f z}) ?_ hf
    (chanSet_subset_hull h hz)
  · exact this
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem convex_valHP (g : HP) : Convex ℝ {z : Point | 0 ≤ g.val z} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq, Irrational.HP.val] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : (g.2.2 : ℝ) = s * g.2.2 + t * g.2.2 := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_nonneg hs hx, mul_nonneg ht hy]

/-- The corners lie in the channel. -/
theorem Corners.c1_mem (h : Corners c1 v0 vl d1) : c1 ∈ chanSet c1 v0 vl d1 := by
  have a := h.t0; have b := h.t2
  refine ⟨by rw [Geometry.det_self_outer], ?_, ?_, by rw [Geometry.det_self_right]⟩
  · linarith [Geometry.det_cyclic c1 v0 vl]
  · linarith [Geometry.det_cyclic c1 vl d1, Geometry.det_cyclic vl d1 c1]

theorem Corners.v0_mem (h : Corners c1 v0 vl d1) : v0 ∈ chanSet c1 v0 vl d1 := by
  have a := h.t1; have b := h.t3
  refine ⟨by rw [Geometry.det_self_right], by rw [Geometry.det_self_outer], ?_, ?_⟩
  · linarith [Geometry.det_cyclic v0 vl d1]
  · linarith [Geometry.det_cyclic v0 d1 c1, Geometry.det_cyclic d1 c1 v0]

theorem Corners.vl_mem (h : Corners c1 v0 vl d1) : vl ∈ chanSet c1 v0 vl d1 := by
  have a := h.t0; have b := h.t2
  refine ⟨?_, by rw [Geometry.det_self_right], by rw [Geometry.det_self_outer], ?_⟩
  · linarith [Geometry.det_cyclic c1 v0 vl, Geometry.det_cyclic v0 vl c1]
  · linarith [Geometry.det_cyclic vl d1 c1]

theorem Corners.d1_mem (h : Corners c1 v0 vl d1) : d1 ∈ chanSet c1 v0 vl d1 := by
  have a := h.t1; have b := h.t3
  refine ⟨?_, ?_, by rw [Geometry.det_self_right], by rw [Geometry.det_self_outer]⟩
  · linarith [Geometry.det_cyclic d1 c1 v0]
  · linarith [Geometry.det_cyclic v0 vl d1, Geometry.det_cyclic vl d1 v0]

/-- The sides lie in the channel. -/
theorem Corners.segment_subset (_h : Corners c1 v0 vl d1) {p q : Point}
    (hp : p ∈ chanSet c1 v0 vl d1) (hq : q ∈ chanSet c1 v0 vl d1) :
    ArtGallery.segment p q ⊆ chanSet c1 v0 vl d1 :=
  Geometry.segment_subset_of_convex convex_chanSet hp hq

end Chan

/-! ### Chain edges outside the channel -/

/-- The four sides of the channel `c1 V₀ V_l d1` (affine points). -/
def chanSides (c1 v0 vl d1 : SPt) : List (SPt × SPt) := [(c1, v0), (v0, vl), (vl, d1), (d1, c1)]

/-- The chain edge `A B` misses the open channel: both ends weakly outside a side, or strictly
outside an extra line `g` which is nonnegative at the four corners. -/
def edgeOutB (c1 v0 vl d1 : SPt) (extra : List HP) (A B : IPt) : Bool :=
  (chanSides c1 v0 vl d1).any (fun s => qnn (qneg (qdet s.1 s.2 (sc A))) &&
      qnn (qneg (qdet s.1 s.2 (sc B)))) ||
    extra.any fun g => ineg (ivalHP g A) && ineg (ivalHP g B) &&
      ([c1, v0, vl, d1].all fun p => qnn (qhp g p))

/-- All chain edges miss the open channel. -/
def chainOutB (c1 v0 vl d1 : SPt) (extra : List HP) (V : List IPt) : Bool :=
  (List.range (V.length - 1)).all fun j => edgeOutB c1 v0 vl d1 extra (cv V j) (cv V (j + 1))

/-- The corners of the channel turn left for all `S ≥ S₀`. -/
def cornersB (c1 v0 vl d1 : SPt) : Bool :=
  qps (qdet c1 v0 vl) && qps (qdet v0 vl d1) && qps (qdet vl d1 c1) && qps (qdet d1 c1 v0)

theorem corners_of_B {c1 v0 vl d1 : SPt} (h : cornersB c1 v0 vl d1 = true) {S : ℝ}
    (hS : 800000 ≤ S) : Corners (c1.pt S) (v0.pt S) (vl.pt S) (d1.pt S) := by
  simp only [cornersB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨det_pos_of_qps a hS, det_pos_of_qps b hS, det_pos_of_qps c hS, det_pos_of_qps d hS⟩

theorem ineg_iff' {a : ℤ} : ineg a = true ↔ a < 0 := by
  cases a <;> simp [ineg, Int.negSucc_lt_zero]

/-- **A chain edge misses the open channel.** -/
theorem edgeOut_sound {c1 v0 vl d1 : SPt} {extra : List HP} {A B : IPt}
    (hc : cornersB c1 v0 vl d1 = true) (h : edgeOutB c1 v0 vl d1 extra A B = true) {S : ℝ}
    (hS : 800000 ≤ S) {z : Point} (hz : z ∈ ArtGallery.segment (intPoint A) (intPoint B)) :
    ¬ (0 < det (c1.pt S) (v0.pt S) z ∧ 0 < det (v0.pt S) (vl.pt S) z ∧
      0 < det (vl.pt S) (d1.pt S) z ∧ 0 < det (d1.pt S) (c1.pt S) z) := by
  rintro ⟨k0, k1, k2, k3⟩
  simp only [edgeOutB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨s, hs, ha, hb⟩ | ⟨g, -, ⟨ha, hb⟩, hall⟩
  · have ha' := det_nonpos_of_qnn ha hS
    have hb' := det_nonpos_of_qnn hb hS
    rw [sc_pt] at ha' hb'
    have := det_nonpos_of_ends ha' hb' hz
    simp only [chanSides, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp only at this <;> linarith
  · have hval : g.val z < 0 := by
      refine val_neg_of_ends ?_ ?_ hz
      · rw [val_intPoint_HP]; exact_mod_cast ineg_iff'.1 ha
      · rw [val_intPoint_HP]; exact_mod_cast ineg_iff'.1 hb
    have hC := corners_of_B hc hS
    simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hall
    obtain ⟨g0, g1, g2, g3⟩ := hall
    have hnn := nonneg_on_chanSet hC (f := g.val) (convex_valHP g)
      (by rw [val_pt]; exact qnn_sound g0 hS) (by rw [val_pt]; exact qnn_sound g1 hS)
      (by rw [val_pt]; exact qnn_sound g2 hS) (by rw [val_pt]; exact qnn_sound g3 hS)
      (z := z) ⟨k0.le, k1.le, k2.le, k3.le⟩
    linarith

/-- **The template chain misses the open channel.** -/
theorem chainOut_sound {c1 v0 vl d1 : SPt} {extra : List HP} {V : List IPt}
    (hc : cornersB c1 v0 vl d1 = true) (h : chainOutB c1 v0 vl d1 extra V = true) {S : ℝ}
    (hS : 800000 ≤ S) {j : ℕ} (hj : j + 1 < V.length) {z : Point}
    (hz : z ∈ ArtGallery.segment (intPoint (cv V j)) (intPoint (cv V (j + 1)))) :
    ¬ (0 < det (c1.pt S) (v0.pt S) z ∧ 0 < det (v0.pt S) (vl.pt S) z ∧
      0 < det (vl.pt S) (d1.pt S) z ∧ 0 < det (d1.pt S) (c1.pt S) z) := by
  simp only [chainOutB, List.all_eq_true, List.mem_range] at h
  exact edgeOut_sound hc (h j (by omega)) hS hz

end ArtGallery.Sec5.CoverT

end
