module

public import ArtGallery.Hardness.Sec5.Templates.Tools

/-!
# Section 5, counting: template position systems and certificate tools

The guard positions of a gadget template (its guard segments and stationary guards) in template
coordinates (`TSys`): main witness, witness vertices, the position (hull of an integer list) and
the pinning rank.  `TSys.Facts V D T` collects what the counting argument needs, for every simple
counter-clockwise polygon containing the template chain `V` (`ChainAt`):

* (W1) a point seeing all witnesses of `X` lies on `X`;
* (W2) no point sees two main witnesses;
* (W3) points of an earlier position see no witness of a later one; no point sees the main
  witness of a later position and a witness of an earlier one;
* no point of the unit window sees a main witness, no point of the unit entrance sees a witness
  (in template coordinates the window is `x = −DS`, `y ∈ [DS, DS + 3D/2]`, the entrance
  `x = −3DS`, `y ∈ [DS, DS + 3D]`, `S ≥ 800000`).

Certificate tools for the last items: `not_sees_seg_cone` (the segment misses the cone of the
witness), `not_sees_seg_cross` (every segment from the witness to the door properly crosses a
chain edge), `not_sees_of_room` (a point of a room with door `D` sees no point outside the room
that is seen by no point of `D`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)

/-- The template point with index `j`. -/
abbrev tpt (V : List IPt) (j : ℕ) : Point := intPoint (cv V j)

/-! ### Affine dependence on a segment point -/

theorem det_lerp_right (a b y₀ y₁ : Point) (t : ℝ) :
    det a b (Geometry.lerp y₀ y₁ t) = (1 - t) * det a b y₀ + t * det a b y₁ := by
  simp only [det, Geometry.lerp]; ring

theorem det_lerp_mid (a c y₀ y₁ : Point) (t : ℝ) :
    det a (Geometry.lerp y₀ y₁ t) c = (1 - t) * det a y₀ c + t * det a y₁ c := by
  simp only [det, Geometry.lerp]; ring

theorem neg_of_lerp {f₀ f₁ t : ℝ} (h₀ : f₀ < 0) (h₁ : f₁ < 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * f₀ + t * f₁ < 0 := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simpa using h₀
  · nlinarith [mul_neg_of_pos_of_neg ht h₁, mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - t) h₀.le]

theorem pos_of_lerp {f₀ f₁ t : ℝ} (h₀ : 0 < f₀) (h₁ : 0 < f₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1 - t) * f₀ + t * f₁ := by
  have := neg_of_lerp (neg_neg_of_pos h₀) (neg_neg_of_pos h₁) ht0 ht1
  linarith

/-! ### Doors seen from no point -/

variable {P : Polygon} {V : List IPt} {a : ℕ}

/-- **A segment outside the cone.** If both end points of `[y₀, y₁]` lie strictly outside one of
the two half-planes of the cone at the convex chain vertex `j`, no point of the segment sees
`V[j]`. -/
theorem not_sees_seg_cone (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < V.length) (hconv : 0 < idet (cv V (j - 1)) (cv V j) (cv V (j + 1)))
    {y₀ y₁ : Point}
    (h : (det (tpt V (j - 1)) (tpt V j) y₀ < 0 ∧ det (tpt V (j - 1)) (tpt V j) y₁ < 0) ∨
      (det (tpt V j) (tpt V (j + 1)) y₀ < 0 ∧ det (tpt V j) (tpt V (j + 1)) y₁ < 0)) :
    ∀ y ∈ ArtGallery.segment y₀ y₁, ¬ P.Sees y (tpt V j) := by
  intro y hy hs
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hy
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC hj1 hj hconv (Polygon.sees_comm.1 hs)
  rw [det_lerp_right] at c1 c2
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · linarith [neg_of_lerp h0 h1 ht0 ht1]
  · linarith [neg_of_lerp h0 h1 ht0 ht1]

/-- **A door behind a chain edge.** If every segment from `w` to an end point of `[y₀, y₁]`
properly crosses the chain edge `e` (signs `s₁`, `s₂`), no point of the segment sees `w`. -/
theorem not_sees_seg_cross (hP : P.Simple) (hC : ChainAt P V a) {e : ℕ} (he : e + 1 < V.length)
    {w y₀ y₁ : Point} {s₁ s₂ : ℝ}
    (h1 : 0 < s₁ * det (tpt V e) (tpt V (e + 1)) w)
    (h2 : s₁ * det (tpt V e) (tpt V (e + 1)) y₀ < 0) (h3 : s₁ * det (tpt V e) (tpt V (e + 1)) y₁ < 0)
    (h4 : s₂ * det w y₀ (tpt V e) < 0) (h5 : s₂ * det w y₁ (tpt V e) < 0)
    (h6 : 0 < s₂ * det w y₀ (tpt V (e + 1))) (h7 : 0 < s₂ * det w y₁ (tpt V (e + 1))) :
    ∀ y ∈ ArtGallery.segment y₀ y₁, ¬ P.Sees y w := by
  intro y hy hs
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hy
  have hn := n_pos_of_simple hP
  obtain ⟨e1, e2⟩ := hC.edge_vtx he
  have k1 : s₁ * det (tpt V e) (tpt V (e + 1)) (Geometry.lerp y₀ y₁ t) < 0 := by
    rw [det_lerp_right, mul_add, ← mul_assoc, ← mul_assoc, mul_comm s₁ (1 - t), mul_comm s₁ t,
      mul_assoc, mul_assoc]
    exact neg_of_lerp h2 h3 ht0 ht1
  have k2 : s₂ * det w (Geometry.lerp y₀ y₁ t) (tpt V e) < 0 := by
    rw [det_lerp_mid, mul_add, ← mul_assoc, ← mul_assoc, mul_comm s₂ (1 - t), mul_comm s₂ t,
      mul_assoc, mul_assoc]
    exact neg_of_lerp h4 h5 ht0 ht1
  have k3 : 0 < s₂ * det w (Geometry.lerp y₀ y₁ t) (tpt V (e + 1)) := by
    rw [det_lerp_mid, mul_add, ← mul_assoc, ← mul_assoc, mul_comm s₂ (1 - t), mul_comm s₂ t,
      mul_assoc, mul_assoc]
    exact pos_of_lerp h6 h7 ht0 ht1
  refine Polygon.not_sees_of_proper_cross hP (i := (a + e) % P.n) (Nat.mod_lt _ hn) ?_ ?_
    (Polygon.sees_comm.1 hs)
  · rw [e1, e2]
    have := mul_neg_of_pos_of_neg h1 k1
    nlinarith [sq_nonneg s₁]
  · rw [e1, e2]
    have := mul_neg_of_neg_of_pos k2 k3
    nlinarith [sq_nonneg s₂]

/-- **Room and door.** A point of the room `R` does not see a point `w` outside `R` that no point
of the door sees. -/
theorem not_sees_of_room {R D : Set Point} (hR : P.IsRoom R D) {w p : Point} (hw : w ∉ R)
    (hp : p ∈ R) (hD : ∀ y ∈ D, ¬ P.Sees y w) : ¬ P.Sees p w := by
  intro hs
  obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door hR hp hw hs
  refine hD y hyD fun z hz => hs ?_
  exact Geometry.segment_subset_of_convex (Geometry.segment_convex p w) hy
    (Geometry.right_mem_segment p w) hz

/-- Two hulls separated by a half-plane are disjoint. -/
theorem hull_disjoint {L₁ L₂ : List IPt} {g : HP}
    (h₁ : (L₁.all fun q => inonneg (ivalHP g q)) = true)
    (h₂ : (L₂.all fun q => ipos (ivalHP (Vis.Cert.negHP g) q)) = true) :
    Disjoint (convexHull ℝ (intSet L₁)) (convexHull ℝ (intSet L₂)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have a1 := nonneg_on_hull h₁ x hx1
  have a2 := pos_on_hull h₂ x hx2
  simp only [Irrational.HP.val, Vis.Cert.negHP] at a1 a2
  push_cast at a2
  linarith

/-! ### Template position systems -/

/-- The guard positions of a template (template coordinates, vertex indices of the chain). -/
structure TSys where
  /-- The number of positions. -/
  r : ℕ
  /-- The main witness. -/
  m : Fin r → ℕ
  /-- The witnesses. -/
  W : Fin r → List ℕ
  /-- The position: the hull of an integer list. -/
  spot : Fin r → List IPt
  /-- The pinning rank. -/
  rank : Fin r → ℕ

/-- Lower end of the unit window in template coordinates. -/
noncomputable def winT0 (D S : ℝ) : Point := (-(D * S), D * S)
/-- Upper end of the unit window in template coordinates. -/
noncomputable def winT1 (D S : ℝ) : Point := (-(D * S), D * S + 3 / 2 * D)
/-- Lower end of the unit entrance in template coordinates. -/
noncomputable def entT0 (D S : ℝ) : Point := (-(3 * D * S), D * S)
/-- Upper end of the unit entrance in template coordinates. -/
noncomputable def entT1 (D S : ℝ) : Point := (-(3 * D * S), D * S + 3 * D)

/-- The facts about the positions of a template needed for the counting. -/
structure TSys.Facts (V : List IPt) (D : ℕ) (T : TSys) : Prop where
  /-- The main witness is a witness. -/
  m_W : ∀ X, T.m X ∈ T.W X
  /-- Witnesses are chain vertices. -/
  idx : ∀ X, ∀ j ∈ T.W X, j < V.length
  /-- The positions lie in the template box. -/
  box : ∀ X, ∀ q ∈ T.spot X, -(50 * (D : ℤ)) ≤ q.1 ∧ q.1 ≤ 50 * D ∧ -(50 * (D : ℤ)) ≤ q.2 ∧
    q.2 ≤ 50 * D
  /-- Distinct positions are disjoint. -/
  spot_disj : ∀ X Y, X ≠ Y →
    Disjoint (convexHull ℝ (intSet (T.spot X))) (convexHull ℝ (intSet (T.spot Y)))
  /-- (W1) -/
  spot : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X x,
    (∀ j ∈ T.W X, P.Sees x (tpt V j)) → x ∈ convexHull ℝ (intSet (T.spot X))
  /-- (W2) -/
  disj : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X Y, X ≠ Y →
    ∀ x, P.Sees x (tpt V (T.m X)) → ¬ P.Sees x (tpt V (T.m Y))
  /-- (W3, earlier positions) -/
  early : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X Y, Y ≠ X →
    T.rank Y < T.rank X → ∀ j ∈ T.W X, ∀ x ∈ convexHull ℝ (intSet (T.spot Y)),
      ¬ P.Sees x (tpt V j)
  /-- (W3, later positions) -/
  late : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X Y, Y ≠ X →
    ¬ T.rank Y < T.rank X → ∀ j ∈ T.W X, ∀ x, P.Sees x (tpt V (T.m Y)) → ¬ P.Sees x (tpt V j)
  /-- The window sees no main witness. -/
  window : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X (S : ℝ),
    800000 ≤ S → ∀ y ∈ ArtGallery.segment (winT0 D S) (winT1 D S), ¬ P.Sees y (tpt V (T.m X))
  /-- The entrance sees no witness. -/
  entrance : ∀ {P : Polygon} {a : ℕ}, P.Simple → P.InteriorLeft → ChainAt P V a → ∀ X,
    ∀ j ∈ T.W X, ∀ S : ℝ, 800000 ≤ S → ∀ y ∈ ArtGallery.segment (entT0 D S) (entT1 D S),
      ¬ P.Sees y (tpt V j)

end ArtGallery.Sec5.Tmpl

end
