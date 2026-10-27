module

public import ArtGallery.Stade.NookAlg

/-!
# Stade construction, §6: algebra of the inversion gadgets

The two inversion gadgets of `docs/stade/construction.md` §6, translated by the slot origin `g`
(local coordinates `x − g`; floor `y = −1`; inputs `{b} × [0, 6]` with guards `inPt b v`,
value map `v ↦ (b, 4v − 2)`).  Each gadget realises a *perspectivity* between its two input
segments through a common nook segment (this replaces [Stade, Lemmas 5.3–5.6]).

### `invGe x y` (`1 ≤ v_x v_y`)
x-input at `g + 40`, y-input at `g + 100`, mouth `P = (g+43, −6)`, `Q = (g+97, −6)`, nook
`J = (g+61, −78)`, `I = (g+79, −78)`, corridor ends `(g + 81/2, −1)`, `(g + 199/2, −1)`.
Shadows on the nook line `y = −78`: x-guard through `P`: `igShX g v = g + 43 + 54/(v+1)`,
y-guard through `Q`: `igShY g w = g + 97 − 54/(w+1)`; the x-guard sees only `[igShX, I]`,
the y-guard only `[J, igShY]`, and `igShX ≤ igShY ↔ 1 ≤ v w` (`igSh_le_iff`).

### `invRevLe x y` (`v_x (5/2 − v_y) ≤ 1`)
x-input at `g + 60`, y-input at `g + 104`, mouth `P = (g+59, −1)` (on the floor),
`Q = (g+80, −8)`, nook `J = (g+38, −22)`, `I = (g+56, −22)`, corridor end `Q' = (g+101, −1)`.
Shadows on `y = −22`: `irShX g v = g + 59 − 21/(4v − 1)`, `irShY g w = g + 80 − 168/(2w + 3)`;
`irShX ≤ irShY ↔ v (5/2 − w) ≤ 1` (`irSh_le_iff`).

For each gadget: shadow identities, non-restriction (the shadow through the other mouth end lies
beyond the nook), what each guard sees through the mouth (`ig_x_seen`, …), coverage ⇒ relation
(`ig_rel_of_shadows`, `ir_rel_of_shadows`), positive visibility (`ig_x_cross`, …), and the
partial-visibility region (`igPV`, `irPV`, `mem_igPV_of_cross`, `mem_irPV_of_cross`).
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

/-! ## `invGe` -/

/-- `invGe`: left mouth corner `P = (g + 43, −6)`. -/
def igP (g : ℝ) : Point := (g + 43, -6)
/-- `invGe`: right mouth corner `Q = (g + 97, −6)`. -/
def igQ (g : ℝ) : Point := (g + 97, -6)
/-- `invGe`: left end `J = (g + 61, −78)` of the nook segment. -/
def igJ (g : ℝ) : Point := (g + 61, -78)
/-- `invGe`: right end `I = (g + 79, −78)` of the nook segment. -/
def igI (g : ℝ) : Point := (g + 79, -78)
/-- `invGe`: left end `(g + 81/2, −1)` of the corridor opening on the floor. -/
noncomputable def igC1 (g : ℝ) : Point := (g + 81 / 2, -1)
/-- `invGe`: right end `(g + 199/2, −1)` of the corridor opening on the floor. -/
noncomputable def igC2 (g : ℝ) : Point := (g + 199 / 2, -1)

/-- `invGe`: shadow of the x-guard of value `v` through `P` on the nook line. -/
noncomputable def igShX (g v : ℝ) : ℝ := g + 43 + 54 / (v + 1)
/-- `invGe`: shadow of the y-guard of value `w` through `Q` on the nook line. -/
noncomputable def igShY (g w : ℝ) : ℝ := g + 97 - 54 / (w + 1)

section invGe

variable {g : ℝ}

/-- Shadow of the x-guard through `P`. -/
theorem ig_hproj_xP {v : ℝ} (hv : 0 ≤ v) : hproj (inPt (g + 40) v) (igP g) (-78) = igShX g v := by
  have : v + 1 ≠ 0 := by linarith
  have : -6 - (4 * v - 2) ≠ 0 := by linarith
  unfold hproj igShX igP inPt
  field_simp
  ring

/-- Shadow of the x-guard through `Q` (non-restriction: it lies right of `I`). -/
theorem ig_hproj_xQ {v : ℝ} (hv : 0 ≤ v) :
    hproj (inPt (g + 40) v) (igQ g) (-78) = g + 97 + 1026 / (v + 1) := by
  have : v + 1 ≠ 0 := by linarith
  have : -6 - (4 * v - 2) ≠ 0 := by linarith
  unfold hproj igQ inPt
  field_simp
  ring

/-- Shadow of the y-guard through `Q`. -/
theorem ig_hproj_yQ {w : ℝ} (hw : 0 ≤ w) :
    hproj (inPt (g + 100) w) (igQ g) (-78) = igShY g w := by
  have : w + 1 ≠ 0 := by linarith
  have : -6 - (4 * w - 2) ≠ 0 := by linarith
  unfold hproj igShY igQ inPt
  field_simp
  ring

/-- Shadow of the y-guard through `P` (non-restriction: it lies left of `J`). -/
theorem ig_hproj_yP {w : ℝ} (hw : 0 ≤ w) :
    hproj (inPt (g + 100) w) (igP g) (-78) = g + 43 - 1026 / (w + 1) := by
  have : w + 1 ≠ 0 := by linarith
  have : -6 - (4 * w - 2) ≠ 0 := by linarith
  unfold hproj igP inPt
  field_simp
  ring

/-- The shadow of a value in `[1/2, 2]` lies on the nook segment `[g + 61, g + 79]`. -/
theorem igShX_mem {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    g + 61 ≤ igShX g v ∧ igShX g v ≤ g + 79 := by
  unfold igShX
  have hp : 0 < v + 1 := by linarith
  constructor
  · have : 18 ≤ 54 / (v + 1) := by rw [le_div_iff₀ hp]; linarith
    linarith
  · have : 54 / (v + 1) ≤ 36 := by rw [div_le_iff₀ hp]; linarith
    linarith

/-- The shadow of a value in `[1/2, 2]` lies on the nook segment `[g + 61, g + 79]`. -/
theorem igShY_mem {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    g + 61 ≤ igShY g w ∧ igShY g w ≤ g + 79 := by
  unfold igShY
  have hp : 0 < w + 1 := by linarith
  constructor
  · have : 54 / (w + 1) ≤ 36 := by rw [div_le_iff₀ hp]; linarith
    linarith
  · have : 18 ≤ 54 / (w + 1) := by rw [le_div_iff₀ hp]; linarith
    linarith

/-- **The `invGe` perspectivity.** The shadows are in order iff `1 ≤ v w`. -/
theorem igSh_le_iff {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) : igShX g v ≤ igShY g w ↔ 1 ≤ v * w := by
  unfold igShX igShY
  have hv1 : 0 < v + 1 := by linarith
  have hw1 : 0 < w + 1 := by linarith
  have e : 54 / (v + 1) + 54 / (w + 1) = 54 * (v + w + 2) / ((v + 1) * (w + 1)) := by
    field_simp; ring
  constructor
  · intro h
    have h' : 54 * (v + w + 2) / ((v + 1) * (w + 1)) ≤ 54 := by rw [← e]; linarith
    rw [div_le_iff₀ (mul_pos hv1 hw1)] at h'
    nlinarith
  · intro h
    have h' : 54 * (v + w + 2) / ((v + 1) * (w + 1)) ≤ 54 := by
      rw [div_le_iff₀ (mul_pos hv1 hw1)]; nlinarith
    rw [← e] at h'
    linarith

/-- **x-guard of `invGe`.** A nook point `(h, −78)` (`h ≤ g + 79`) seen from the x-guard through
the mouth lies at or right of `igShX g v`. -/
theorem ig_x_seen {v h : ℝ} (hv : 0 ≤ v) (hh : h ≤ g + 79) {q : Point}
    (hq : q ∈ segment (igP g) (igQ g)) (hqs : q ∈ segment (inPt (g + 40) v) (h, -78)) :
    igShX g v ≤ h := by
  have hc := between_of_cross_horiz hq hqs (by simp [igP, inPt]; linarith)
    (by simp [igQ, inPt]; linarith)
  rw [ig_hproj_xP hv, ig_hproj_xQ hv] at hc
  have : 0 ≤ 1026 / (v + 1) := div_nonneg (by norm_num) (by linarith)
  by_contra hcon; push Not at hcon
  nlinarith

/-- **y-guard of `invGe`.** A nook point `(h, −78)` (`g + 61 ≤ h`) seen from the y-guard through
the mouth lies at or left of `igShY g w`. -/
theorem ig_y_seen {w h : ℝ} (hw : 0 ≤ w) (hh : g + 61 ≤ h) {q : Point}
    (hq : q ∈ segment (igP g) (igQ g)) (hqs : q ∈ segment (inPt (g + 100) w) (h, -78)) :
    h ≤ igShY g w := by
  have hc := between_of_cross_horiz hq hqs (by simp [igP, inPt]; linarith)
    (by simp [igQ, inPt]; linarith)
  rw [ig_hproj_yP hw, ig_hproj_yQ hw] at hc
  have : 0 ≤ 1026 / (w + 1) := div_nonneg (by norm_num) (by linarith)
  by_contra hcon; push Not at hcon
  nlinarith

/-- **Coverage ⇒ `invGe` relation.** If every point of the nook segment is right of the x-shadow
or left of the y-shadow, then `1 ≤ v w`. -/
theorem ig_rel_of_shadows {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w)
    (hw2 : w ≤ 2)
    (hcov : ∀ h, g + 61 ≤ h → h ≤ g + 79 → igShX g v ≤ h ∨ h ≤ igShY g w) : 1 ≤ v * w := by
  rw [← igSh_le_iff (g := g) (by linarith) (by linarith)]
  by_contra hlt; push Not at hlt
  have hx := igShX_mem (g := g) hv1 hv2
  have hy := igShY_mem (g := g) hw1 hw2
  rcases hcov ((igShX g v + igShY g w) / 2) (by linarith) (by linarith) with h | h <;> linarith

/-- The mouth line of `invGe`: `det P Q p = 54 (p.2 + 6)`. -/
theorem ig_det_mouth (p : Point) : det (igP g) (igQ g) p = 54 * (p.2 + 6) := by
  unfold det igP igQ; ring

/-- **Positive visibility, x-guard of `invGe`.** -/
theorem ig_x_cross {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hh1 : igShX g v ≤ h) (hh2 : h ≤ g + 79) :
    ∃ q ∈ segment (igP g) (igQ g), q ∈ segment (inPt (g + 40) v) (h, -78) := by
  have hv : 0 ≤ v := by linarith
  refine exists_cross_horiz ?_ (by simp [igP, inPt]; linarith) (by simp [igQ, inPt]; linarith) ?_
  · rw [ig_det_mouth, ig_det_mouth]; simp only [inPt_snd]; nlinarith
  · rw [ig_hproj_xP hv, ig_hproj_xQ hv]
    have : 0 ≤ 1026 / (v + 1) := div_nonneg (by norm_num) (by linarith)
    nlinarith

/-- **Positive visibility, y-guard of `invGe`.** -/
theorem ig_y_cross {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hh1 : g + 61 ≤ h) (hh2 : h ≤ igShY g w) :
    ∃ q ∈ segment (igP g) (igQ g), q ∈ segment (inPt (g + 100) w) (h, -78) := by
  have hw : 0 ≤ w := by linarith
  refine exists_cross_horiz ?_ (by simp [igP, inPt]; linarith) (by simp [igQ, inPt]; linarith) ?_
  · rw [ig_det_mouth, ig_det_mouth]; simp only [inPt_snd]; nlinarith
  · rw [ig_hproj_yP hw, ig_hproj_yQ hw]
    have : 0 ≤ 1026 / (w + 1) := div_nonneg (by norm_num) (by linarith)
    nlinarith

/-- The partial-visibility region of the `invGe` nook: above the mouth line `y = −6` and between
the arms `y = −2(x − g − 40)` (line `I P`) and `y = 2(x − g − 100)` (line `J Q`). -/
def igPV (g : ℝ) : Set Point :=
  {p | -6 ≤ p.2 ∧ -2 * (p.1 - g - 40) ≤ p.2 ∧ 2 * (p.1 - g - 100) ≤ p.2}

/-- **Viewers of the `invGe` nook lie in `igPV`.** -/
theorem mem_igPV_of_cross {s q p : Point} (hs : s ∈ segment (igJ g) (igI g))
    (hq : q ∈ segment (igP g) (igQ g)) (hqp : q ∈ segment s p) : p ∈ igPV g := by
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := hs
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := hq
  simp only [igJ, igI, igP, igQ] at hqp ⊢
  have hqs : ((g + 43 + τ * (g + 97 - (g + 43)), -6 + τ * (-6 - -6)) : Point) ≠
      (g + 61 + σ * (g + 79 - (g + 61)), -78 + σ * (-78 - -78)) := by
    intro h; have := congrArg Prod.snd h; simp only at this; linarith
  refine ⟨?_, ?_, ?_⟩
  · have := lin_nonneg_of_beyond 0 1 6 hqp hqs (by simp; norm_num) (by simp)
    linarith
  · have := lin_nonneg_of_beyond 2 1 (-2 * g - 80) hqp hqs (by simp only; nlinarith)
      (by simp only; nlinarith)
    linarith
  · have := lin_nonneg_of_beyond (-2) 1 (2 * g + 200) hqp hqs (by simp only; nlinarith)
      (by simp only; nlinarith)
    linarith

/-- Points of `igPV` at the input band `y ∈ [0, 6]` have `x ∈ [g + 37, g + 103]`. -/
theorem igPV_in_band {p : Point} (hp : p ∈ igPV g) (hy : p.2 ≤ 6) :
    g + 37 ≤ p.1 ∧ p.1 ≤ g + 103 := by
  obtain ⟨-, h2, h3⟩ := hp
  constructor <;> linarith

end invGe

/-! ## `invRevLe` -/

/-- `invRevLe`: mouth corner `P = (g + 59, −1)` (on the floor). -/
def irP (g : ℝ) : Point := (g + 59, -1)
/-- `invRevLe`: mouth corner `Q = (g + 80, −8)`. -/
def irQ (g : ℝ) : Point := (g + 80, -8)
/-- `invRevLe`: left end `J = (g + 38, −22)` of the nook segment. -/
def irJ (g : ℝ) : Point := (g + 38, -22)
/-- `invRevLe`: right end `I = (g + 56, −22)` of the nook segment. -/
def irI (g : ℝ) : Point := (g + 56, -22)
/-- `invRevLe`: corridor corner `Q' = (g + 101, −1)` on the floor (on the line `J Q`). -/
def irQ' (g : ℝ) : Point := (g + 101, -1)

/-- `invRevLe`: shadow of the x-guard of value `v` through `P` on the nook line. -/
noncomputable def irShX (g v : ℝ) : ℝ := g + 59 - 21 / (4 * v - 1)
/-- `invRevLe`: shadow of the y-guard of value `w` through `Q` on the nook line. -/
noncomputable def irShY (g w : ℝ) : ℝ := g + 80 - 168 / (2 * w + 3)

section invRevLe

variable {g : ℝ}

/-- Shadow of the x-guard through `P`. -/
theorem ir_hproj_xP {v : ℝ} (hv : 1 / 2 ≤ v) :
    hproj (inPt (g + 60) v) (irP g) (-22) = irShX g v := by
  have : 4 * v - 1 ≠ 0 := by linarith
  have : -1 - (4 * v - 2) ≠ 0 := by linarith
  unfold hproj irShX irP inPt
  field_simp
  ring

/-- Shadow of the x-guard through `Q` (non-restriction: it lies right of `I`). -/
theorem ir_hproj_xQ {v : ℝ} (hv : 1 / 2 ≤ v) :
    hproj (inPt (g + 60) v) (irQ g) (-22) = g + 60 + 40 * (v + 5) / (2 * v + 3) := by
  have : 2 * v + 3 ≠ 0 := by linarith
  have : -8 - (4 * v - 2) ≠ 0 := by linarith
  unfold hproj irQ inPt
  field_simp
  ring

/-- Shadow of the y-guard through `Q`. -/
theorem ir_hproj_yQ {w : ℝ} (hw : 1 / 2 ≤ w) :
    hproj (inPt (g + 104) w) (irQ g) (-22) = irShY g w := by
  have : 2 * w + 3 ≠ 0 := by linarith
  have : -8 - (4 * w - 2) ≠ 0 := by linarith
  unfold hproj irShY irQ inPt
  field_simp
  ring

/-- Shadow of the y-guard through `P` (non-restriction: it lies left of `J`). -/
theorem ir_hproj_yP {w : ℝ} (hw : 1 / 2 ≤ w) :
    hproj (inPt (g + 104) w) (irP g) (-22) = g + 104 - 45 * (4 * w + 20) / (4 * w - 1) := by
  have : 4 * w - 1 ≠ 0 := by linarith
  have : -1 - (4 * w - 2) ≠ 0 := by linarith
  unfold hproj irP inPt
  field_simp
  ring

/-- The x-shadow of a value in `[1/2, 2]` lies on the nook segment `[g + 38, g + 56]`. -/
theorem irShX_mem {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    g + 38 ≤ irShX g v ∧ irShX g v ≤ g + 56 := by
  unfold irShX
  have hp : 0 < 4 * v - 1 := by linarith
  constructor
  · have : 21 / (4 * v - 1) ≤ 21 := by rw [div_le_iff₀ hp]; linarith
    linarith
  · have : 3 ≤ 21 / (4 * v - 1) := by rw [le_div_iff₀ hp]; linarith
    linarith

/-- The y-shadow of a value in `[1/2, 2]` lies on the nook segment `[g + 38, g + 56]`. -/
theorem irShY_mem {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    g + 38 ≤ irShY g w ∧ irShY g w ≤ g + 56 := by
  unfold irShY
  have hp : 0 < 2 * w + 3 := by linarith
  constructor
  · have : 168 / (2 * w + 3) ≤ 42 := by rw [div_le_iff₀ hp]; linarith
    linarith
  · have : 24 ≤ 168 / (2 * w + 3) := by rw [le_div_iff₀ hp]; linarith
    linarith

/-- **The `invRevLe` perspectivity.** The shadows are in order iff `v (5/2 − w) ≤ 1`. -/
theorem irSh_le_iff {v w : ℝ} (hv : 1 / 2 ≤ v) (hw : 0 ≤ w) :
    irShX g v ≤ irShY g w ↔ v * (5 / 2 - w) ≤ 1 := by
  unfold irShX irShY
  have hv1 : 0 < 4 * v - 1 := by linarith
  have hw1 : 0 < 2 * w + 3 := by linarith
  have e : 168 / (2 * w + 3) - 21 / (4 * v - 1) - 21 =
      -(84 * (2 * v * w - 5 * v + 2)) / ((2 * w + 3) * (4 * v - 1)) := by
    field_simp; ring
  constructor
  · intro h
    have h' : -(84 * (2 * v * w - 5 * v + 2)) / ((2 * w + 3) * (4 * v - 1)) ≤ 0 := by
      rw [← e]; linarith
    rw [div_nonpos_iff] at h'
    rcases h' with ⟨-, h2⟩ | ⟨h1, -⟩
    · nlinarith [mul_pos hw1 hv1]
    · nlinarith
  · intro h
    have h' : -(84 * (2 * v * w - 5 * v + 2)) / ((2 * w + 3) * (4 * v - 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (mul_pos hw1 hv1).le
    rw [← e] at h'
    linarith

/-- **x-guard of `invRevLe`.** A nook point `(h, −22)` (`h ≤ g + 56`) seen from the x-guard
through the mouth lies at or right of `irShX g v`. -/
theorem ir_x_seen {v h : ℝ} (hv : 1 / 2 ≤ v) (hh : h ≤ g + 56) {q : Point}
    (hq : q ∈ segment (irP g) (irQ g)) (hqs : q ∈ segment (inPt (g + 60) v) (h, -22)) :
    irShX g v ≤ h := by
  have hc := between_of_cross_horiz hq hqs (by simp [irP, inPt]; linarith)
    (by simp [irQ, inPt]; linarith)
  rw [ir_hproj_xP hv, ir_hproj_xQ hv] at hc
  have : 0 ≤ 40 * (v + 5) / (2 * v + 3) := div_nonneg (by nlinarith) (by linarith)
  by_contra hcon; push Not at hcon
  nlinarith

/-- **y-guard of `invRevLe`.** A nook point `(h, −22)` (`g + 38 ≤ h`) seen from the y-guard
through the mouth lies at or left of `irShY g w`. -/
theorem ir_y_seen {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hh : g + 38 ≤ h) {q : Point}
    (hq : q ∈ segment (irP g) (irQ g)) (hqs : q ∈ segment (inPt (g + 104) w) (h, -22)) :
    h ≤ irShY g w := by
  have hc := between_of_cross_horiz hq hqs (by simp [irP, inPt]; linarith)
    (by simp [irQ, inPt]; linarith)
  rw [ir_hproj_yP hw1, ir_hproj_yQ hw1] at hc
  have hp : 0 < 4 * w - 1 := by linarith
  have : 135 ≤ 45 * (4 * w + 20) / (4 * w - 1) := by rw [le_div_iff₀ hp]; nlinarith
  by_contra hcon; push Not at hcon
  nlinarith

/-- **Coverage ⇒ `invRevLe` relation.** If every point of the nook segment is right of the
x-shadow or left of the y-shadow, then `v (5/2 − w) ≤ 1`. -/
theorem ir_rel_of_shadows {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w)
    (hw2 : w ≤ 2)
    (hcov : ∀ h, g + 38 ≤ h → h ≤ g + 56 → irShX g v ≤ h ∨ h ≤ irShY g w) :
    v * (5 / 2 - w) ≤ 1 := by
  rw [← irSh_le_iff (g := g) hv1 (by linarith)]
  by_contra hlt; push Not at hlt
  have hx := irShX_mem (g := g) hv1 hv2
  have hy := irShY_mem (g := g) hw1 hw2
  rcases hcov ((irShX g v + irShY g w) / 2) (by linarith) (by linarith) with h | h <;> linarith

/-- The mouth line of `invRevLe`: `det P Q p = 21 (p.2 + 1) + 7 (p.1 − g − 59)`. -/
theorem ir_det_mouth (p : Point) : det (irP g) (irQ g) p = 21 * (p.2 + 1) + 7 * (p.1 - g - 59) := by
  unfold det irP irQ; ring

/-- **Positive visibility, x-guard of `invRevLe`.** -/
theorem ir_x_cross {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hh1 : irShX g v ≤ h) (hh2 : h ≤ g + 56) :
    ∃ q ∈ segment (irP g) (irQ g), q ∈ segment (inPt (g + 60) v) (h, -22) := by
  refine exists_cross_horiz ?_ (by simp [irP, inPt]; linarith) (by simp [irQ, inPt]; linarith) ?_
  · rw [ir_det_mouth, ir_det_mouth]; simp only [inPt_snd, inPt_fst]; nlinarith
  · rw [ir_hproj_xP hv1, ir_hproj_xQ hv1]
    have : 0 ≤ 40 * (v + 5) / (2 * v + 3) := div_nonneg (by nlinarith) (by linarith)
    nlinarith

/-- **Positive visibility, y-guard of `invRevLe`.** -/
theorem ir_y_cross {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hh1 : g + 38 ≤ h)
    (hh2 : h ≤ irShY g w) :
    ∃ q ∈ segment (irP g) (irQ g), q ∈ segment (inPt (g + 104) w) (h, -22) := by
  have hm := irShY_mem (g := g) hw1 hw2
  refine exists_cross_horiz ?_ (by simp [irP, inPt]; linarith) (by simp [irQ, inPt]; linarith) ?_
  · rw [ir_det_mouth, ir_det_mouth]; simp only [inPt_snd, inPt_fst]; nlinarith
  · rw [ir_hproj_yP hw1, ir_hproj_yQ hw1]
    have hp : 0 < 4 * w - 1 := by linarith
    have : 135 ≤ 45 * (4 * w + 20) / (4 * w - 1) := by rw [le_div_iff₀ hp]; nlinarith
    nlinarith

/-- The partial-visibility region of the `invRevLe` nook: beyond the mouth line
`x + 3y = g + 56`, left of the line `J Q` (`x ≤ g + 104 + 3y`) and right of the line `I P`
(`y + 414 ≤ 7 (x − g)`). -/
def irPV (g : ℝ) : Set Point :=
  {p | 56 ≤ p.1 - g + 3 * p.2 ∧ p.1 - g ≤ 3 * p.2 + 104 ∧ p.2 + 414 ≤ 7 * (p.1 - g)}

/-- **Viewers of the `invRevLe` nook lie in `irPV`.** -/
theorem mem_irPV_of_cross {s q p : Point} (hs : s ∈ segment (irJ g) (irI g))
    (hq : q ∈ segment (irP g) (irQ g)) (hqp : q ∈ segment s p) : p ∈ irPV g := by
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := hs
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := hq
  simp only [irJ, irI, irP, irQ] at hqp ⊢
  have hqs : ((g + 59 + τ * (g + 80 - (g + 59)), -1 + τ * (-8 - -1)) : Point) ≠
      (g + 38 + σ * (g + 56 - (g + 38)), -22 + σ * (-22 - -22)) := by
    intro h; have := congrArg Prod.snd h; simp only at this; linarith
  refine ⟨?_, ?_, ?_⟩
  · have := lin_nonneg_of_beyond 1 3 (-g - 56) hqp hqs (by simp only; nlinarith)
      (by simp only; nlinarith)
    linarith
  · have := lin_nonneg_of_beyond (-1) 3 (g + 104) hqp hqs (by simp only; nlinarith)
      (by simp only; nlinarith)
    linarith
  · have := lin_nonneg_of_beyond 7 (-1) (-7 * g - 414) hqp hqs (by simp only; nlinarith)
      (by simp only; nlinarith)
    linarith

/-- Points of `irPV` lie at `y ≥ −8` and `x ≥ g + 58` (up-right of the gadget). -/
theorem irPV_bounds {p : Point} (hp : p ∈ irPV g) : -8 ≤ p.2 ∧ g + 58 ≤ p.1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  constructor <;> linarith

/-- Points of `irPV` at the input band `y ∈ [0, 6]` have `x ∈ [g + 59, g + 122]`. -/
theorem irPV_in_band {p : Point} (hp : p ∈ irPV g) (hy1 : 0 ≤ p.2) (hy2 : p.2 ≤ 6) :
    g + 59 ≤ p.1 ∧ p.1 ≤ g + 122 := by
  obtain ⟨h1, h2, h3⟩ := hp
  constructor <;> linarith

end invRevLe

end Stade

end ArtGallery

end
