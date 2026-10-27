module

public import ArtGallery.Stade.NookAlg

/-!
# Stade construction, §7: algebra of the addition gadgets

The algebraic core of the two addition gadgets of `docs/stade/construction.md` §7.1, in the
coordinates of a slot with origin `G` (local coordinates of the templates translated by `G`;
ordinates are not translated).  The three nook segments lie on the vertical line `x = G + 30`;
the openings of the aux guard `P, Q, R` lie on `x = G + 50` with `Q = (2/3) P + (1/3) R`; the
openings `N1, N2, N3` of the inputs `x, z, y` lie on `x = G + 50` as well, except for the
recessed opening `N2 = (G + 65/2, −5977/100)` of `addGe` (the bay).

* `vproj_comb` (**projection identity**, L7.1): the projection of a point `a` through a point of
  a vertical opening line onto the nook line is affine in the ordinate of the opening; hence
  `π_Q(a) = (2/3) π_P(a) + (1/3) π_R(a)` for every `a` (`al_proj_Q`, `ag_proj_Q`).
* **Input shadows** (L7.2): the input of value `v` projects through its opening to
  `s_i(v) = c_i − 4 k_i v` with the scales `k_x, k_y, k_z = 1/16, 1/8, 1/24`
  (`al_shadow_x`, …, `ag_shadow_z`); the projections through the other mouth corner do not
  restrict the input (`al_input_x_P`, …).
* **Coverage ⇒ relation** (L7.4): `le_of_cover_below`, `le_of_cover_above` (a nook segment
  covered by two guards seeing the parts above / below their shadows), `al_rel_of_cover_alg`
  (`v_x + v_y ≤ v_z`) and `ag_rel_of_cover_alg` (`v_z ≤ v_x + v_y`).
* **Canonical aux point** (L7.5): `alI G v_x v_y`, `agI G v_x v_y` with `π_P(I) = s_x(v_x)`,
  `π_R(I) = s_y(v_y)` (`alI_P`, `alI_R`, …); the remaining conditions on `I` (non-restriction
  through the input openings, membership in the room and the aux cone, position with respect to
  the bay) are rational functions of `(v_x, v_y)` which become **affine** after multiplication
  by `s − 1 > 0` (`alI_lin`, `agI_lin`), so they are proved by `linarith` on the box
  `[1/2, 2]²` (for `addLe`: the triangle `v_x, v_y ≥ 1/2`, `v_x + v_y ≤ 2`).
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

/-! ### Generic lemmas -/

/-- **Projection identity (L7.1).** The projection of `a` through the point `(d, o)` onto the
vertical line `x = c` is affine in the ordinate `o`. -/
theorem vproj_comb (a : Point) (d c μ p r : ℝ) :
    vproj a (d, μ * p + (1 - μ) * r) c = μ * vproj a (d, p) c + (1 - μ) * vproj a (d, r) c := by
  unfold vproj; ring

/-- A nook point `(c, h)` with `det g O (c, h) ≤ 0`, the mouth corner `O` strictly left of `g`,
lies at or above the shadow of `g` through `O`. -/
theorem vproj_le_of_det_nonpos {g O : Point} {c h : ℝ} (hO : O.1 < g.1)
    (hd : det g O (c, h) ≤ 0) : vproj g O c ≤ h := by
  rw [det_vert g O c h hO.ne] at hd
  by_contra hc
  push Not at hc
  have : 0 < (O.1 - g.1) * (h - vproj g O c) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-- A nook point `(c, h)` with `0 ≤ det g O (c, h)`, the mouth corner `O` strictly left of `g`,
lies at or below the shadow of `g` through `O`. -/
theorem le_vproj_of_det_nonneg {g O : Point} {c h : ℝ} (hO : O.1 < g.1)
    (hd : 0 ≤ det g O (c, h)) : h ≤ vproj g O c := by
  rw [det_vert g O c h hO.ne] at hd
  by_contra hc
  push Not at hc
  have : (O.1 - g.1) * (h - vproj g O c) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  linarith

/-- **Covering an interval, guard below.** If every `h ∈ [lo, hi]` satisfies `α ≤ h` or
`h ≤ β`, where `lo ≤ β < hi`, then `α ≤ β`. -/
theorem le_of_cover_below {lo hi α β : ℝ} (hβ1 : lo ≤ β) (hβ2 : β < hi)
    (hcov : ∀ h, lo ≤ h → h ≤ hi → α ≤ h ∨ h ≤ β) : α ≤ β := by
  by_contra hlt
  push Not at hlt
  have hm1 : min hi ((α + β) / 2) ≤ (α + β) / 2 := min_le_right _ _
  have hm2 : β < min hi ((α + β) / 2) := lt_min hβ2 (by linarith)
  rcases hcov (min hi ((α + β) / 2)) (by linarith) (min_le_left _ _) with h | h
  · linarith
  · linarith

/-- **Covering an interval, guard above.** If every `h ∈ [lo, hi]` satisfies `h ≤ α` or
`β ≤ h`, where `lo < β ≤ hi`, then `β ≤ α`. -/
theorem le_of_cover_above {lo hi α β : ℝ} (hβ1 : lo < β) (hβ2 : β ≤ hi)
    (hcov : ∀ h, lo ≤ h → h ≤ hi → h ≤ α ∨ β ≤ h) : β ≤ α := by
  by_contra hlt
  push Not at hlt
  have hm1 : (α + β) / 2 ≤ max lo ((α + β) / 2) := le_max_right _ _
  have hm2 : max lo ((α + β) / 2) < β := max_lt hβ1 (by linarith)
  rcases hcov (max lo ((α + β) / 2)) (le_max_left _ _) (by linarith) with h | h
  · linarith
  · linarith

/-- The projection of a point onto `x = G + 30` through `(G + 50, o)`, explicitly. -/
theorem vproj_fifty (G o : ℝ) (a : Point) (ha : a.1 ≠ G + 50) :
    vproj a (G + 50, o) (G + 30) = (o * (a.1 - G - 30) - 20 * a.2) / (a.1 - G - 50) := by
  have h1 : a.1 - G - 50 ≠ 0 := by intro h; apply ha; linarith
  have h2 : G + 50 - a.1 ≠ 0 := by intro h; apply ha; linarith
  unfold vproj
  simp only
  field_simp
  ring

/-! ## `addLe` (`v_x + v_y ≤ v_z`) -/

section addLe

variable (G : ℝ)

/-- `addLe`: aux opening `P` of the x-nook. -/
noncomputable def alP : Point := (G + 50, -113)
/-- `addLe`: aux opening `Q` of the z-nook (`Q = (2/3) P + (1/3) R`). -/
noncomputable def alQ : Point := (G + 50, -118)
/-- `addLe`: aux opening `R` of the y-nook. -/
noncomputable def alR : Point := (G + 50, -128)
/-- `addLe`: input opening `N1` of the x-nook. -/
noncomputable def alN1 : Point := (G + 50, -445 / 4)
/-- `addLe`: input opening `N2` of the z-nook. -/
noncomputable def alN2 : Point := (G + 50, -2994 / 25)
/-- `addLe`: input opening `N3` of the y-nook. -/
noncomputable def alN3 : Point := (G + 50, -491 / 4)
/-- `addLe`: lower end of the x-nook segment. -/
noncomputable def alXlo : Point := (G + 30, -7589 / 64)
/-- `addLe`: upper end of the x-nook segment. -/
noncomputable def alXhi : Point := (G + 30, -7561 / 64)
/-- `addLe`: lower end of the y-nook segment. -/
noncomputable def alYlo : Point := (G + 30, -4443 / 32)
/-- `addLe`: upper end of the y-nook segment. -/
noncomputable def alYhi : Point := (G + 30, -4417 / 32)
/-- `addLe`: lower end of the z-nook segment. -/
noncomputable def alZlo : Point := (G + 30, -2001 / 16)
/-- `addLe`: upper end of the z-nook segment. -/
noncomputable def alZhi : Point := (G + 30, -499 / 4)

/-- `addLe`: shadow of the x-input of value `v` through `N1` (`c_x − v/4`). -/
noncomputable def alSx (v : ℝ) : ℝ := -7557 / 64 - v / 4
/-- `addLe`: shadow of the y-input of value `v` through `N3` (`c_y − v/2`). -/
noncomputable def alSy (v : ℝ) : ℝ := -4411 / 32 - v / 2
/-- `addLe`: shadow of the z-input of value `v` through `N2` (`c_z − v/6`). -/
noncomputable def alSz (v : ℝ) : ℝ := -374 / 3 - v / 6

/-- `addLe`: the scale `s = (s_x − s_y)/(p − r)` of the canonical aux point. -/
noncomputable def alS (vx vy : ℝ) : ℝ := (alSx vx - alSy vy) / 15

/-- `addLe`: the canonical aux point `I(v_x, v_y)`, whose projections through `P` and `R` are
the shadows `s_x(v_x)`, `s_y(v_y)`. -/
noncomputable def alI (vx vy : ℝ) : Point :=
  (G + 50 + 20 / (alS vx vy - 1), (-113 * alS vx vy - alSx vx) / (alS vx vy - 1))

variable {G}

/-- **Projection identity for `addLe`**: `π_Q = (2/3) π_P + (1/3) π_R`. -/
theorem al_proj_Q (a : Point) :
    vproj a (alQ G) (G + 30) =
      2 / 3 * vproj a (alP G) (G + 30) + 1 / 3 * vproj a (alR G) (G + 30) := by
  have e : alQ G = (G + 50, 2 / 3 * (-113) + (1 - 2 / 3) * (-128)) := by
    unfold alQ; norm_num
  rw [e, vproj_comb]
  unfold alP alR
  norm_num

/-! ### Input shadows -/

/-- `addLe`: the x-input (at `G + 370`) projects through `N1` to `s_x(v)`. -/
theorem al_shadow_x (v : ℝ) : vproj (inPt (G + 370) v) (alN1 G) (G + 30) = alSx v := by
  have h : (alN1 G).1 - (inPt (G + 370) v).1 = -320 := by simp only [alN1, inPt]; ring
  rw [vproj_eq_of h]; simp only [alN1, inPt, alSx]; ring

/-- `addLe`: the y-input (at `G + 210`) projects through `N3` to `s_y(v)`. -/
theorem al_shadow_y (v : ℝ) : vproj (inPt (G + 210) v) (alN3 G) (G + 30) = alSy v := by
  have h : (alN3 G).1 - (inPt (G + 210) v).1 = -160 := by simp only [alN3, inPt]; ring
  rw [vproj_eq_of h]; simp only [alN3, inPt, alSy]; ring

/-- `addLe`: the z-input (at `G + 530`) projects through `N2` to `s_z(v)`. -/
theorem al_shadow_z (v : ℝ) : vproj (inPt (G + 530) v) (alN2 G) (G + 30) = alSz v := by
  have h : (alN2 G).1 - (inPt (G + 530) v).1 = -480 := by simp only [alN2, inPt]; ring
  rw [vproj_eq_of h]; simp only [alN2, inPt, alSz]; ring

/-- `addLe`: the projection of the x-input through `P` lies below the x-nook. -/
theorem al_input_x_P {v : ℝ} (hv : 0 ≤ v) :
    vproj (inPt (G + 370) v) (alP G) (G + 30) ≤ -7589 / 64 := by
  have h : (alP G).1 - (inPt (G + 370) v).1 = -320 := by simp only [alP, inPt]; ring
  rw [vproj_eq_of h]; simp only [alP, inPt]; ring_nf; linarith

/-- `addLe`: the projection of the y-input through `R` lies below the y-nook. -/
theorem al_input_y_R {v : ℝ} (hv : 0 ≤ v) :
    vproj (inPt (G + 210) v) (alR G) (G + 30) ≤ -4443 / 32 := by
  have h : (alR G).1 - (inPt (G + 210) v).1 = -160 := by simp only [alR, inPt]; ring
  rw [vproj_eq_of h]; simp only [alR, inPt]; ring_nf; linarith

/-- `addLe`: the projection of the z-input through `Q` lies above the z-nook. -/
theorem al_input_z_Q {v : ℝ} (hv : v ≤ 2) :
    -499 / 4 ≤ vproj (inPt (G + 530) v) (alQ G) (G + 30) := by
  have h : (alQ G).1 - (inPt (G + 530) v).1 = -480 := by simp only [alQ, inPt]; ring
  rw [vproj_eq_of h]; simp only [alQ, inPt]; ring_nf; linarith

/-- `addLe`: the shadows of the inputs lie in the nook segments; the x- and y-shadows strictly
below the upper ends, the z-shadow strictly above the lower end (the margins). -/
theorem al_shadows_mem {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    (-7589 / 64 ≤ alSx v ∧ alSx v < -7561 / 64) ∧ (-4443 / 32 ≤ alSy v ∧ alSy v < -4417 / 32) ∧
      (-2001 / 16 < alSz v ∧ alSz v ≤ -499 / 4) := by
  unfold alSx alSy alSz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ### Coverage ⇒ relation (L7.4) -/

/-- **`addLe`, coverage ⇒ `v_x + v_y ≤ v_z` (algebraic form).**  Let `a` be the aux guard.  If
every height of the x-nook is above `π_P(a)` or below `s_x(v_x)`, every height of the y-nook
above `π_R(a)` or below `s_y(v_y)`, and every height of the z-nook below `π_Q(a)` or above
`s_z(v_z)`, then `v_x + v_y ≤ v_z`. -/
theorem al_rel_of_cover_alg (a : Point) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2)
    (hcx : ∀ h, -7589 / 64 ≤ h → h ≤ -7561 / 64 → vproj a (alP G) (G + 30) ≤ h ∨ h ≤ alSx vx)
    (hcy : ∀ h, -4443 / 32 ≤ h → h ≤ -4417 / 32 → vproj a (alR G) (G + 30) ≤ h ∨ h ≤ alSy vy)
    (hcz : ∀ h, -2001 / 16 ≤ h → h ≤ -499 / 4 → h ≤ vproj a (alQ G) (G + 30) ∨ alSz vz ≤ h) :
    vx + vy ≤ vz := by
  obtain ⟨⟨ax1, ax2⟩, -, -⟩ := al_shadows_mem hx1 hx2
  obtain ⟨-, ⟨ay1, ay2⟩, -⟩ := al_shadows_mem hy1 hy2
  obtain ⟨-, -, ⟨az1, az2⟩⟩ := al_shadows_mem hz1 hz2
  have h1 := le_of_cover_below ax1 ax2 hcx
  have h2 := le_of_cover_below ay1 ay2 hcy
  have h3 := le_of_cover_above az1 az2 hcz
  rw [al_proj_Q] at h3
  unfold alSx alSy alSz at *
  linarith

/-! ### The canonical aux point (L7.5) -/

/-- `addLe`: `s > 1` on the domain. -/
theorem alS_sub_one_pos {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) : 0 < alS vx vy - 1 := by
  unfold alS alSx alSy; linarith

/-- `addLe`: the canonical aux point lies strictly right of the opening line `x = G + 50`. -/
theorem alI_fst {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) : G + 50 < (alI G vx vy).1 := by
  have := alS_sub_one_pos hx hy
  unfold alI
  have : 0 < 20 / (alS vx vy - 1) := div_pos (by norm_num) this
  simp only
  linarith

/-- `addLe`: projection of the canonical aux point through `(G + 50, o)`. -/
theorem alI_vproj {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) (o : ℝ) :
    vproj (alI G vx vy) (G + 50, o) (G + 30) = alSx vx - alS vx vy * (-113 - o) := by
  have hu := (alS_sub_one_pos hx hy).ne'
  rw [vproj_fifty G o _ (alI_fst hx hy).ne']
  unfold alI
  simp only
  have e1 : G + 50 + 20 / (alS vx vy - 1) - G - 30 = 20 * alS vx vy / (alS vx vy - 1) := by
    field_simp; ring
  have e2 : G + 50 + 20 / (alS vx vy - 1) - G - 50 = 20 / (alS vx vy - 1) := by ring
  rw [e1, e2]
  field_simp
  ring

/-- `addLe`: `π_P(I) = s_x(v_x)`. -/
theorem alI_P {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (alI G vx vy) (alP G) (G + 30) = alSx vx := by
  rw [alP, alI_vproj hx hy]; ring

/-- `addLe`: `π_R(I) = s_y(v_y)`. -/
theorem alI_R {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (alI G vx vy) (alR G) (G + 30) = alSy vy := by
  rw [alR, alI_vproj hx hy]; unfold alS; ring

/-- `addLe`: `π_Q(I) = (2/3) s_x(v_x) + (1/3) s_y(v_y)`. -/
theorem alI_Q {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (alI G vx vy) (alQ G) (G + 30) = 2 / 3 * alSx vx + 1 / 3 * alSy vy := by
  rw [al_proj_Q, alI_P hx hy, alI_R hx hy]

/-- `addLe`: `π_Q(I) ≥ s_z(v_z)` iff `v_x + v_y ≤ v_z`. -/
theorem alI_Q_ge_iff {vx vy vz : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    alSz vz ≤ vproj (alI G vx vy) (alQ G) (G + 30) ↔ vx + vy ≤ vz := by
  rw [alI_Q hx hy]
  unfold alSx alSy alSz
  constructor <;> intro h <;> linarith

/-- `addLe`: the aux guard at `I` is not restricted by `N1`: `π_{N1}(I)` is above the x-nook. -/
theorem alI_N1 {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) :
    -7561 / 64 ≤ vproj (alI G vx vy) (alN1 G) (G + 30) := by
  rw [alN1, alI_vproj hx (by linarith)]; unfold alS alSx alSy; nlinarith

/-- `addLe`: the aux guard at `I` is not restricted by `N3`: `π_{N3}(I)` is above the y-nook. -/
theorem alI_N3 {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) :
    -4417 / 32 ≤ vproj (alI G vx vy) (alN3 G) (G + 30) := by
  rw [alN3, alI_vproj hx (by linarith)]; unfold alS alSx alSy; nlinarith

/-- `addLe`: the aux guard at `I` is not restricted by `N2`: `π_{N2}(I)` is below the z-nook. -/
theorem alI_N2 {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (_hy2 : vy ≤ 2) :
    vproj (alI G vx vy) (alN2 G) (G + 30) ≤ -2001 / 16 := by
  rw [alN2, alI_vproj hx (by linarith)]; unfold alS alSx alSy; nlinarith

/-- `addLe`: an affine functional of `I`, multiplied by `s − 1`, is affine in `(v_x, v_y)`. -/
theorem alI_lin {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) (α β γ : ℝ) :
    (alS vx vy - 1) * (α * ((alI G vx vy).1 - G - 50) + β * (alI G vx vy).2 + γ) =
      20 * α + β * (-113 * alS vx vy - alSx vx) + γ * (alS vx vy - 1) := by
  have hu := (alS_sub_one_pos hx hy).ne'
  unfold alI
  simp only
  field_simp
  ring

/-- Positivity of an affine functional of `I` from positivity of its `(s − 1)`-multiple. -/
theorem alI_lin_pos {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) {α β γ : ℝ}
    (h : 0 < 20 * α + β * (-113 * alS vx vy - alSx vx) + γ * (alS vx vy - 1)) :
    0 < α * ((alI G vx vy).1 - G - 50) + β * (alI G vx vy).2 + γ := by
  have hu := alS_sub_one_pos hx hy
  rw [← alI_lin hx hy] at h
  exact pos_of_mul_pos_right h hu.le

/-- **`addLe`: position of the canonical aux point** (for `v_x, v_y ≥ 1/2`, `v_x + v_y ≤ 2`):
strictly inside the room `[(G+200, −1), (G+50, −445/4), (G+50, −128), (G+527, −128),
(G+527, −1)]` and strictly inside the aux cone with tip `(G+110, −519/4)` through
`(G+439/4, −128)`, `(G+441/4, −128)`; in coordinates `X = I.1 − G − 50`, `Y = I.2`:
the wall `WL T0`, `X < 477`, `Y > −128`, `Y < −1` and the two cone rays. -/
theorem alI_pos {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2) :
    let X := (alI G vx vy).1 - G - 50
    let Y := (alI G vx vy).2
    0 < 441 / 4 * X - 150 * Y - 33375 / 2 ∧ 0 < -X + 477 ∧ 0 < Y + 128 ∧ 0 < -Y - 1 ∧
      0 < 7 / 4 * X + 1 / 4 * Y - 1161 / 16 ∧ 0 < -(7 / 4) * X + 1 / 4 * Y + 2199 / 16 := by
  have hx : vx ≤ 2 := by linarith
  have hy : (0 : ℝ) ≤ vy := by linarith
  have l := fun α β γ h => alI_lin_pos (G := G) hx hy (α := α) (β := β) (γ := γ) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := l (441 / 4) (-150) (-33375 / 2) (by unfold alS alSx alSy; linarith); linarith
  · have := l (-1) 0 477 (by unfold alS alSx alSy; linarith); linarith
  · have := l 0 1 128 (by unfold alS alSx alSy; linarith); linarith
  · have := l 0 (-1) (-1) (by unfold alS alSx alSy; linarith); linarith
  · have := l (7 / 4) (1 / 4) (-1161 / 16) (by unfold alS alSx alSy; linarith); linarith
  · have := l (-(7 / 4)) (1 / 4) (2199 / 16) (by unfold alS alSx alSy; linarith); linarith

end addLe

/-! ## `addGe` (`v_z ≤ v_x + v_y`) -/

section addGe

variable (G : ℝ)

/-- `addGe`: aux opening `P` of the x-nook. -/
noncomputable def agP : Point := (G + 50, -37)
/-- `addGe`: aux opening `Q` of the z-nook (`Q = (2/3) P + (1/3) R`). -/
noncomputable def agQ : Point := (G + 50, -151 / 3)
/-- `addGe`: aux opening `R` of the y-nook. -/
noncomputable def agR : Point := (G + 50, -77)
/-- `addGe`: input opening `N1` of the x-nook. -/
noncomputable def agN1 : Point := (G + 50, -153 / 4)
/-- `addGe`: the recessed input opening `N2` of the z-nook (the bay `N1 N2 Q`). -/
noncomputable def agN2 : Point := (G + 65 / 2, -5977 / 100)
/-- `addGe`: input opening `N3` of the y-nook. -/
noncomputable def agN3 : Point := (G + 50, -94)
/-- `addGe`: lower end of the x-nook segment. -/
noncomputable def agXlo : Point := (G + 30, -2649 / 64)
/-- `addGe`: upper end of the x-nook segment. -/
noncomputable def agXhi : Point := (G + 30, -2601 / 64)
/-- `addGe`: lower end of the y-nook segment. -/
noncomputable def agYlo : Point := (G + 30, -855 / 8)
/-- `addGe`: upper end of the y-nook segment. -/
noncomputable def agYhi : Point := (G + 30, -423 / 4)
/-- `addGe`: lower end of the z-nook segment. -/
noncomputable def agZlo : Point := (G + 30, -6001 / 96)
/-- `addGe`: upper end of the z-nook segment. -/
noncomputable def agZhi : Point := (G + 30, -5941 / 96)

/-- `addGe`: shadow of the x-input of value `v` through `N1` (`c_x − v/4`). -/
noncomputable def agSx (v : ℝ) : ℝ := -2593 / 64 - v / 4
/-- `addGe`: shadow of the y-input of value `v` through `N3` (`c_y − v/2`). -/
noncomputable def agSy (v : ℝ) : ℝ := -211 / 2 - v / 2
/-- `addGe`: shadow of the z-input of value `v` through `N2` (`c_z − v/6`). -/
noncomputable def agSz (v : ℝ) : ℝ := -5969 / 96 - v / 6

/-- `addGe`: the scale `s = (s_x − s_y)/(p − r)` of the canonical aux point. -/
noncomputable def agS (vx vy : ℝ) : ℝ := (agSx vx - agSy vy) / 40

/-- `addGe`: the canonical aux point `I(v_x, v_y)`, whose projections through `P` and `R` are
the shadows `s_x(v_x)`, `s_y(v_y)`. -/
noncomputable def agI (vx vy : ℝ) : Point :=
  (G + 50 + 20 / (agS vx vy - 1), (-37 * agS vx vy - agSx vx) / (agS vx vy - 1))

variable {G}

/-- **Projection identity for `addGe`**: `π_Q = (2/3) π_P + (1/3) π_R`. -/
theorem ag_proj_Q (a : Point) :
    vproj a (agQ G) (G + 30) =
      2 / 3 * vproj a (agP G) (G + 30) + 1 / 3 * vproj a (agR G) (G + 30) := by
  have e : agQ G = (G + 50, 2 / 3 * (-37) + (1 - 2 / 3) * (-77)) := by
    unfold agQ; norm_num
  rw [e, vproj_comb]
  unfold agP agR
  norm_num

/-! ### Input shadows -/

/-- `addGe`: the x-input (at `G + 370`) projects through `N1` to `s_x(v)`. -/
theorem ag_shadow_x (v : ℝ) : vproj (inPt (G + 370) v) (agN1 G) (G + 30) = agSx v := by
  have h : (agN1 G).1 - (inPt (G + 370) v).1 = -320 := by simp only [agN1, inPt]; ring
  rw [vproj_eq_of h]; simp only [agN1, inPt, agSx]; ring

/-- `addGe`: the y-input (at `G + 210`) projects through `N3` to `s_y(v)`. -/
theorem ag_shadow_y (v : ℝ) : vproj (inPt (G + 210) v) (agN3 G) (G + 30) = agSy v := by
  have h : (agN3 G).1 - (inPt (G + 210) v).1 = -160 := by simp only [agN3, inPt]; ring
  rw [vproj_eq_of h]; simp only [agN3, inPt, agSy]; ring

/-- `addGe`: the z-input (at `G + 185/2`) projects through the recessed `N2` to `s_z(v)`. -/
theorem ag_shadow_z (v : ℝ) : vproj (inPt (G + 185 / 2) v) (agN2 G) (G + 30) = agSz v := by
  have h : (agN2 G).1 - (inPt (G + 185 / 2) v).1 = -60 := by simp only [agN2, inPt]; ring
  rw [vproj_eq_of h]; simp only [agN2, inPt, agSz]; ring

/-- `addGe`: the projection of the x-input through `P` lies above the x-nook. -/
theorem ag_input_x_P {v : ℝ} (hv : v ≤ 2) :
    -2601 / 64 ≤ vproj (inPt (G + 370) v) (agP G) (G + 30) := by
  have h : (agP G).1 - (inPt (G + 370) v).1 = -320 := by simp only [agP, inPt]; ring
  rw [vproj_eq_of h]; simp only [agP, inPt]; ring_nf; linarith

/-- `addGe`: the projection of the y-input through `R` lies above the y-nook. -/
theorem ag_input_y_R {v : ℝ} (hv : v ≤ 2) :
    -423 / 4 ≤ vproj (inPt (G + 210) v) (agR G) (G + 30) := by
  have h : (agR G).1 - (inPt (G + 210) v).1 = -160 := by simp only [agR, inPt]; ring
  rw [vproj_eq_of h]; simp only [agR, inPt]; ring_nf; linarith

/-- `addGe`: the projection of the z-input through `Q` lies below the z-nook. -/
theorem ag_input_z_Q {v : ℝ} (hv : 0 ≤ v) :
    vproj (inPt (G + 185 / 2) v) (agQ G) (G + 30) ≤ -6001 / 96 := by
  have h : (agQ G).1 - (inPt (G + 185 / 2) v).1 = -85 / 2 := by simp only [agQ, inPt]; ring
  rw [vproj_eq_of h]; simp only [agQ, inPt]; ring_nf; linarith

/-- `addGe`: the projection of the z-input through `N1` lies above the z-nook (its sight lines
to the z-nook cross `x = G + 50` between `Q` and `N1`, i.e. into the bay). -/
theorem ag_input_z_N1 {v : ℝ} (hv : v ≤ 2) :
    -5941 / 96 ≤ vproj (inPt (G + 185 / 2) v) (agN1 G) (G + 30) := by
  have h : (agN1 G).1 - (inPt (G + 185 / 2) v).1 = -85 / 2 := by simp only [agN1, inPt]; ring
  rw [vproj_eq_of h]; simp only [agN1, inPt]; ring_nf; linarith

/-- `addGe`: the shadows of the inputs lie in the nook segments; the x- and y-shadows strictly
above the lower ends, the z-shadow strictly below the upper end (the margins). -/
theorem ag_shadows_mem {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    (-2649 / 64 < agSx v ∧ agSx v ≤ -2601 / 64) ∧ (-855 / 8 < agSy v ∧ agSy v ≤ -423 / 4) ∧
      (-6001 / 96 ≤ agSz v ∧ agSz v < -5941 / 96) := by
  unfold agSx agSy agSz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ### Coverage ⇒ relation (L7.4) -/

/-- **`addGe`, coverage ⇒ `v_z ≤ v_x + v_y` (algebraic form).**  Let `a` be the aux guard.  If
every height of the x-nook is below `π_P(a)` or above `s_x(v_x)`, every height of the y-nook
below `π_R(a)` or above `s_y(v_y)`, and every height of the z-nook above `π_Q(a)` or below
`s_z(v_z)`, then `v_z ≤ v_x + v_y`. -/
theorem ag_rel_of_cover_alg (a : Point) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2)
    (hcx : ∀ h, -2649 / 64 ≤ h → h ≤ -2601 / 64 → h ≤ vproj a (agP G) (G + 30) ∨ agSx vx ≤ h)
    (hcy : ∀ h, -855 / 8 ≤ h → h ≤ -423 / 4 → h ≤ vproj a (agR G) (G + 30) ∨ agSy vy ≤ h)
    (hcz : ∀ h, -6001 / 96 ≤ h → h ≤ -5941 / 96 → vproj a (agQ G) (G + 30) ≤ h ∨ h ≤ agSz vz) :
    vz ≤ vx + vy := by
  obtain ⟨⟨ax1, ax2⟩, -, -⟩ := ag_shadows_mem hx1 hx2
  obtain ⟨-, ⟨ay1, ay2⟩, -⟩ := ag_shadows_mem hy1 hy2
  obtain ⟨-, -, ⟨az1, az2⟩⟩ := ag_shadows_mem hz1 hz2
  have h1 := le_of_cover_above ax1 ax2 hcx
  have h2 := le_of_cover_above ay1 ay2 hcy
  have h3 := le_of_cover_below az1 az2 hcz
  rw [ag_proj_Q] at h3
  unfold agSx agSy agSz at *
  linarith

/-! ### The canonical aux point (L7.5) -/

/-- `addGe`: `s > 1` on the domain. -/
theorem agS_sub_one_pos {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) : 0 < agS vx vy - 1 := by
  unfold agS agSx agSy; linarith

/-- `addGe`: the canonical aux point lies strictly right of the opening line `x = G + 50`. -/
theorem agI_fst {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) : G + 50 < (agI G vx vy).1 := by
  have := agS_sub_one_pos hx hy
  unfold agI
  have : 0 < 20 / (agS vx vy - 1) := div_pos (by norm_num) this
  simp only
  linarith

/-- `addGe`: projection of the canonical aux point through `(G + 50, o)`. -/
theorem agI_vproj {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) (o : ℝ) :
    vproj (agI G vx vy) (G + 50, o) (G + 30) = agSx vx - agS vx vy * (-37 - o) := by
  have hu := (agS_sub_one_pos hx hy).ne'
  rw [vproj_fifty G o _ (agI_fst hx hy).ne']
  unfold agI
  simp only
  have e1 : G + 50 + 20 / (agS vx vy - 1) - G - 30 = 20 * agS vx vy / (agS vx vy - 1) := by
    field_simp; ring
  have e2 : G + 50 + 20 / (agS vx vy - 1) - G - 50 = 20 / (agS vx vy - 1) := by ring
  rw [e1, e2]
  field_simp
  ring

/-- `addGe`: `π_P(I) = s_x(v_x)`. -/
theorem agI_P {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (agI G vx vy) (agP G) (G + 30) = agSx vx := by
  rw [agP, agI_vproj hx hy]; ring

/-- `addGe`: `π_R(I) = s_y(v_y)`. -/
theorem agI_R {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (agI G vx vy) (agR G) (G + 30) = agSy vy := by
  rw [agR, agI_vproj hx hy]; unfold agS; ring

/-- `addGe`: `π_Q(I) = (2/3) s_x(v_x) + (1/3) s_y(v_y)`. -/
theorem agI_Q {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (agI G vx vy) (agQ G) (G + 30) = 2 / 3 * agSx vx + 1 / 3 * agSy vy := by
  rw [ag_proj_Q, agI_P hx hy, agI_R hx hy]

/-- `addGe`: `π_Q(I) ≤ s_z(v_z)` iff `v_z ≤ v_x + v_y`. -/
theorem agI_Q_le_iff {vx vy vz : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (agI G vx vy) (agQ G) (G + 30) ≤ agSz vz ↔ vz ≤ vx + vy := by
  rw [agI_Q hx hy]
  unfold agSx agSy agSz
  constructor <;> intro h <;> linarith

/-- `addGe`: the aux guard at `I` is not restricted by `N1`: `π_{N1}(I)` is below the x-nook. -/
theorem agI_N1 {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (_hy2 : vy ≤ 2) :
    vproj (agI G vx vy) (agN1 G) (G + 30) ≤ -2649 / 64 := by
  rw [agN1, agI_vproj hx (by linarith)]; unfold agS agSx agSy; nlinarith

/-- `addGe`: the aux guard at `I` is not restricted by `N3`: `π_{N3}(I)` is below the y-nook. -/
theorem agI_N3 {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (_hy2 : vy ≤ 2) :
    vproj (agI G vx vy) (agN3 G) (G + 30) ≤ -855 / 8 := by
  rw [agN3, agI_vproj hx (by linarith)]; unfold agS agSx agSy; nlinarith

/-- `addGe`: `π_{N1}(I)` is above the z-nook (sight lines from `I` to the z-nook enter the bay
between `Q` and `N1`). -/
theorem agI_N1_z {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) :
    -5941 / 96 ≤ vproj (agI G vx vy) (agN1 G) (G + 30) := by
  rw [agN1, agI_vproj hx (by linarith)]; unfold agS agSx agSy; nlinarith

/-- `addGe`: an affine functional of `I`, multiplied by `s − 1`, is affine in `(v_x, v_y)`. -/
theorem agI_lin {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) (α β γ : ℝ) :
    (agS vx vy - 1) * (α * ((agI G vx vy).1 - G - 50) + β * (agI G vx vy).2 + γ) =
      20 * α + β * (-37 * agS vx vy - agSx vx) + γ * (agS vx vy - 1) := by
  have hu := (agS_sub_one_pos hx hy).ne'
  unfold agI
  simp only
  field_simp
  ring

/-- Positivity of an affine functional of `I` from positivity of its `(s − 1)`-multiple. -/
theorem agI_lin_pos {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) {α β γ : ℝ}
    (h : 0 < 20 * α + β * (-37 * agS vx vy - agSx vx) + γ * (agS vx vy - 1)) :
    0 < α * ((agI G vx vy).1 - G - 50) + β * (agI G vx vy).2 + γ := by
  have hu := agS_sub_one_pos hx hy
  rw [← agI_lin hx hy] at h
  exact pos_of_mul_pos_right h hu.le

/-- **`addGe`: position of the canonical aux point** (for `(v_x, v_y) ∈ [1/2, 2]²`): strictly
inside the room `[(G+85, −1), (G+50, −37), (G+50, −94), (G+363, −94), (G+363, −1)]`, strictly
inside the aux cone with tip `(G+82, −113)` through `(G+327/4, −94)`, `(G+329/4, −94)`, and
strictly beyond the line `Q N2` of the z-mouth; in coordinates `X = I.1 − G − 50`, `Y = I.2`:
the wall `WL T0`, `X < 313`, `Y > −94`, `Y < −1`, the two cone rays and the mouth line. -/
theorem agI_pos {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hy2 : vy ≤ 2) :
    let X := (agI G vx vy).1 - G - 50
    let Y := (agI G vx vy).2
    0 < 36 * X - 35 * Y - 1295 ∧ 0 < -X + 313 ∧ 0 < Y + 94 ∧ 0 < -Y - 1 ∧
      0 < 19 * X + 1 / 4 * Y - 2319 / 4 ∧ 0 < -19 * X + 1 / 4 * Y + 2545 / 4 ∧
      0 < -(2831 / 300) * X + 35 / 2 * Y + 5285 / 6 := by
  have hx : vx ≤ 2 := hx2
  have hy : (0 : ℝ) ≤ vy := by linarith
  have l := fun α β γ h => agI_lin_pos (G := G) hx hy (α := α) (β := β) (γ := γ) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := l 36 (-35) (-1295) (by unfold agS agSx agSy; linarith); linarith
  · have := l (-1) 0 313 (by unfold agS agSx agSy; linarith); linarith
  · have := l 0 1 94 (by unfold agS agSx agSy; linarith); linarith
  · have := l 0 (-1) (-1) (by unfold agS agSx agSy; linarith); linarith
  · have := l 19 (1 / 4) (-2319 / 4) (by unfold agS agSx agSy; linarith); linarith
  · have := l (-19) (1 / 4) (2545 / 4) (by unfold agS agSx agSy; linarith); linarith
  · have := l (-(2831 / 300)) (35 / 2) (5285 / 6) (by unfold agS agSx agSy; linarith); linarith

/-- `addGe`: projection of the canonical aux point through the recessed opening `N2`. -/
theorem agI_vproj_N2 {vx vy : ℝ} (hx : vx ≤ 2) (hy : 0 ≤ vy) :
    vproj (agI G vx vy) (agN2 G) (G + 30) =
      (-(5 / 2) * (-37 * agS vx vy - agSx vx) + (-5977 / 100) * (20 * agS vx vy)) /
        (35 / 2 * (agS vx vy - 1) + 20) := by
  have hu := agS_sub_one_pos hx hy
  have hu' := hu.ne'
  have hd : 35 / 2 * (agS vx vy - 1) + 20 ≠ 0 := by positivity
  have h : (agN2 G).1 - (agI G vx vy).1 = -(35 / 2 * (agS vx vy - 1) + 20) / (agS vx vy - 1) := by
    unfold agN2 agI; simp only; field_simp; ring
  rw [vproj_eq_of h]
  unfold agN2 agI
  simp only
  have hd' : -(35 / 2 * (agS vx vy - 1) + 20) ≠ 0 := neg_ne_zero.2 hd
  field_simp
  ring

/-- `addGe`: the aux guard at `I` is not restricted by `N2`: `π_{N2}(I)` is above the z-nook. -/
theorem agI_N2 {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx : vx ≤ 2) (hy : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) :
    -5941 / 96 ≤ vproj (agI G vx vy) (agN2 G) (G + 30) := by
  have hu := agS_sub_one_pos hx (by linarith : (0 : ℝ) ≤ vy)
  rw [agI_vproj_N2 hx (by linarith), le_div_iff₀ (by positivity)]
  unfold agS agSx agSy at *
  nlinarith

end addGe

end Stade

end ArtGallery

end
