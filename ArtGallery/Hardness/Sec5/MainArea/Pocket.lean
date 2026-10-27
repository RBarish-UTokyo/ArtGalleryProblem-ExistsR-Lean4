module

public import ArtGallery.Hardness.Sec5.MainArea
public import ArtGallery.Irrational.Checker
public import ArtGallery.Jordan.Filled
public import ArtGallery.Invariance.Affine
public import ArtGallery.Vis.Rooms

/-!
# Section 5: the pocket polygon

The pocket room of slot `σ` is the polygon `pocketPoly one σ` whose vertices are the pocket
chain `pocketClosed one σ` (the pocket followed by its right mouth corner `m_R`); its last edge
is the door `m_R → m_L` on `y = 1`.  It is the translate by `a_σ` of the fixed polygon
`K0 one` (vertices `pocketClosedRel one`).

* `K0` is simple (kernel-checked, `simpleCheck`), hence so is every `pocketPoly one σ`
  (`simple_pocketPoly`, affine invariance), and it is counter-clockwise
  (`interiorLeft_pocketPoly`: all vertices lie below the door line).
* **Convex pieces** (relative coordinates, integer half-planes `a x + b y + c ≥ 0`): the mouth
  `pcM = conv{m_L, H', H, K, m_R}`, the floor spike `pcF = conv{(0,0), t1, K}`, the roof spike
  `pcR = conv{t0, K', (3/2,0)}`, the chamber `pcC = [-1,2] × [-1,0]`, the shaft
  `pcSh = [0,3/2] × [-5,0]`, and with the `one` spikes `pcQ1 = conv{g1, q1, Q'}`,
  `pcQ2 = conv{g1, u0, q2}`.  Their union is `U0 one`.
* `K0.filled ⊆ U0` (`filled_K0_subset`): the boundary lies in `U0` (kernel-checked), and the
  horizontal sections of `U0` are intervals, so from a point outside `U0` a horizontal ray
  avoids `U0`.  Translated: `filled_pocketPoly_subset`.
* Bounds for the points of `U0` (`U0_bounds`): the pocket room lies in the box
  `[−6, 15/2] × [−6, 1]` (relative), below `y = 0` in `[−3/2, 2] × [−6, 0]`, and on `y = 0` in
  `[−3/2, 3]`.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open ArtGallery.Irrational (HP hp hpo unionHP simpleCheck simple_of_simpleCheck edgesInPieces
  boundary_subset_of_edgesInPieces mem_hp_cons mem_hp_nil)

/-! ### The fixed pocket polygon -/

/-- The pocket polygon in relative coordinates (slot `0`). -/
def K0 (one : Bool) : Polygon := ⟨(pocketClosedRel one).map ratPoint⟩

/-- The pocket room of slot `σ`: the polygon with vertices `pocketClosed one σ`. -/
def pocketPoly (one : Bool) (σ : ℕ) : Polygon := ⟨(pocketClosed one σ).map ratPoint⟩

theorem simpleCheck_K0_false : simpleCheck (pocketClosedRel false) = true := by decide +kernel

theorem simpleCheck_K0_true : simpleCheck (pocketClosedRel true) = true := by decide +kernel

/-- The fixed pocket polygon is simple. -/
theorem simple_K0 (one : Bool) : (K0 one).Simple := by
  cases one
  · exact simple_of_simpleCheck simpleCheck_K0_false
  · exact simple_of_simpleCheck simpleCheck_K0_true

/-- The translation by `a_σ`. -/
noncomputable def slotShift (σ : ℕ) : Point ≃ᵃ[ℝ] Point :=
  AffineEquiv.constVAdd ℝ Point (ratPoint (slotA σ))

theorem slotShift_apply (σ : ℕ) (p : Point) :
    slotShift σ p = ((slotX σ : ℝ) + p.1, p.2) := by
  ext <;> simp [slotShift, ratPoint, slotA, vadd_eq_add]

theorem ratPoint_add_slotA (q : Q2) (σ : ℕ) :
    ratPoint (q + slotA σ) = slotShift σ (ratPoint q) := by
  rw [slotShift_apply]
  simp only [ratPoint, slotA, Prod.fst_add, Prod.snd_add, add_zero, Rat.cast_add]
  ext <;> simp [add_comm]

/-- The pocket room of slot `σ` is the translate of `K0`. -/
theorem pocketPoly_eq_mapPoly (one : Bool) (σ : ℕ) :
    pocketPoly one σ = Hardening.Invariance.mapPoly (slotShift σ) (K0 one) := by
  simp only [pocketPoly, K0, Hardening.Invariance.mapPoly, pocketClosed, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact ratPoint_add_slotA q σ

/-- **The pocket room is a simple polygon.** -/
theorem simple_pocketPoly (one : Bool) (σ : ℕ) : (pocketPoly one σ).Simple := by
  rw [pocketPoly_eq_mapPoly]
  exact Hardening.Invariance.simple_mapPoly _ _ (simple_K0 one)

theorem n_pocketPoly (one : Bool) (σ : ℕ) :
    (pocketPoly one σ).n = (pocketRel one).length + 1 := by
  simp [pocketPoly, Polygon.n, pocketClosed, length_pocketClosedRel]

theorem vtx_pocketPoly (one : Bool) (σ j : ℕ) :
    (pocketPoly one σ).vtx j = ratPoint ((pocketClosed one σ).getD j 0) :=
  Irrational.vtx_map_ratPoint _ j

/-- All pocket vertices lie weakly below the door line `y = 1`. -/
theorem pocketClosedRel_snd_le (one : Bool) :
    ∀ j < (pocketClosedRel one).length, ((pocketClosedRel one).getD j 0).2 ≤ 1 := by
  cases one <;> decide +kernel

/-- **The pocket room is counter-clockwise** (the door `m_R → m_L` is a supporting edge). -/
theorem interiorLeft_pocketPoly (one : Bool) (σ : ℕ) : (pocketPoly one σ).InteriorLeft := by
  have hn := n_pocketPoly one σ
  refine Polygon.interiorLeft_of_supporting_edge (simple_pocketPoly one σ)
    (i := (pocketRel one).length) (by omega) fun j hj => ?_
  rw [hn, Nat.mod_self, vtx_pocketPoly, vtx_pocketPoly, vtx_pocketPoly]
  have hlen : j < (pocketClosedRel one).length := by rw [length_pocketClosedRel]; omega
  have hy := pocketClosedRel_snd_le one j hlen
  have e1 : (pocketClosed one σ).getD (pocketRel one).length 0 = mR σ := by
    rw [pocketClosed_eq, List.getD_append_right _ _ _ _ (by rw [length_pocket]), length_pocket,
      Nat.sub_self, List.getD_cons_zero]
  have e0 : (pocketClosed one σ).getD 0 0 = mL σ := by cases one <;> rfl
  have ej : ((pocketClosed one σ).getD j 0).2 = ((pocketClosedRel one).getD j 0).2 := by
    rw [List.getD_eq_getElem _ _ (by simpa [pocketClosed] using hlen),
      List.getD_eq_getElem _ _ hlen]
    simp [pocketClosed, slotA]
  rw [e1, e0]
  simp only [det, ratPoint, mR, mL, mouthR, mouthL, slotA, Prod.fst_add, Prod.snd_add]
  have : ((((pocketClosed one σ).getD j 0).2 : ℚ) : ℝ) ≤ 1 := by rw [ej]; exact_mod_cast hy
  push_cast
  nlinarith

/-! ### The convex pieces (relative coordinates) -/

/-- The mouth `conv{m_L, H', H, K, m_R}`. -/
def pcM : List HP := [(2, 11, 1), (0, 1, 0), (-1, 10, 2), (-38, 200, 85), (0, -1, 1)]
/-- The floor spike `conv{(0,0), t1, K}`. -/
def pcF : List HP := [(0, 1, 0), (-1, -10, 3), (1, -50, 0)]
/-- The roof spike `conv{t0, K', (3/2,0)}`. -/
def pcR : List HP := [(2, 20, 3), (-2, 100, 3), (0, -1, 0)]
/-- The chamber `[-1,2] × [-1,0]`. -/
def pcC : List HP := [(1, 0, 1), (-1, 0, 2), (0, 1, 1), (0, -1, 0)]
/-- The shaft together with the guard segment, `[0,3/2] × [-5,0]`. -/
def pcSh : List HP := [(1, 0, 0), (-2, 0, 3), (0, 1, 5), (0, -1, 0)]
/-- The `q1` spike with the value-`1` point, `conv{g1, q1, Q'}`. -/
def pcQ1 : List HP := [(4, -1, -2), (2, 5, 21), (-42, 5, 21), (0, -1, 0)]
/-- The `q2` spike with the value-`1` point, `conv{g1, u0, q2}`. -/
def pcQ2 : List HP := [(10, -1, -5), (2, 1, 5), (-2, 0, 1), (0, -1, 0)]

/-- The pieces of the pocket room. -/
def piecesRel (one : Bool) : List (List HP) :=
  [pcM, pcF, pcR, pcC, pcSh] ++ (if one then [pcQ1, pcQ2] else [])

/-- The union of the pieces (relative coordinates). -/
def U0 (one : Bool) : Set Point := unionHP (piecesRel one)

theorem edgesInPieces_K0_false :
    edgesInPieces (pocketClosedRel false) (piecesRel false) = true := by
  decide +kernel

theorem edgesInPieces_K0_true :
    edgesInPieces (pocketClosedRel true) (piecesRel true) = true := by
  decide +kernel

/-- The boundary of the fixed pocket polygon lies in `U0`. -/
theorem boundary_K0_subset (one : Bool) : (K0 one).boundary ⊆ U0 one := by
  cases one
  · exact boundary_subset_of_edgesInPieces edgesInPieces_K0_false
  · exact boundary_subset_of_edgesInPieces edgesInPieces_K0_true

theorem mem_U0_false {p : Point} : p ∈ U0 false ↔
    p ∈ hp pcM ∨ p ∈ hp pcF ∨ p ∈ hp pcR ∨ p ∈ hp pcC ∨ p ∈ hp pcSh := by
  simp [U0, unionHP, piecesRel]

theorem mem_U0_true {p : Point} : p ∈ U0 true ↔
    p ∈ hp pcM ∨ p ∈ hp pcF ∨ p ∈ hp pcR ∨ p ∈ hp pcC ∨ p ∈ hp pcSh ∨ p ∈ hp pcQ1 ∨
      p ∈ hp pcQ2 := by
  simp [U0, unionHP, piecesRel]

/-- Unfold membership in a piece into linear inequalities. -/
macro "pc_simp" " at " h:ident : tactic =>
  `(tactic| (simp only [pcM, pcF, pcR, pcC, pcSh, pcQ1, pcQ2, mem_hp_cons, mem_hp_nil,
      and_true] at $h:ident; push_cast at $h:ident))

/-- Reduce membership in a piece to linear inequality goals. -/
macro "pc_goal" : tactic =>
  `(tactic| (simp only [pcM, pcF, pcR, pcC, pcSh, pcQ1, pcQ2, mem_hp_cons, mem_hp_nil,
      and_true]; push_cast; repeat' apply And.intro))

/-! ### Horizontal sections of `U0` -/

section Sections

variable {x y : ℝ}

/-- The sections of `U0 false`, from the pieces. -/
theorem U0_false_sec (h : (x, y) ∈ U0 false) :
    -5 ≤ y ∧ y ≤ 1 ∧
    (1/20 < y → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ (85 + 200 * y) / 38) ∧
    (0 < y → y ≤ 1/20 → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ 3 - 10 * y) ∧
    (y = 0 → -3/2 ≤ x ∧ x ≤ 3) ∧
    (-1/20 ≤ y → y < 0 → -3/2 - 10 * y ≤ x ∧ x ≤ 2) ∧
    (-1 ≤ y → y < -1/20 → -1 ≤ x ∧ x ≤ 2) ∧
    (y < -1 → 0 ≤ x ∧ x ≤ 3/2) := by
  rcases mem_U0_false.1 h with h | h | h | h | h <;> pc_simp at h <;> casesm* _ ∧ _ <;>
    refine ⟨by linarith, by linarith, fun h1 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 h2 => ⟨by linarith, by linarith⟩,
      fun h1 => ⟨by linarith, by linarith⟩⟩

/-- The sections of `U0 true`, from the pieces. -/
theorem U0_true_sec (h : (x, y) ∈ U0 true) :
    -6 ≤ y ∧ y ≤ 1 ∧
    (1/20 < y → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ (85 + 200 * y) / 38) ∧
    (0 < y → y ≤ 1/20 → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ 3 - 10 * y) ∧
    (y = 0 → -3/2 ≤ x ∧ x ≤ 3) ∧
    (-1/20 ≤ y → y < 0 → -3/2 - 10 * y ≤ x ∧ x ≤ 2) ∧
    (-1 ≤ y → y < -1/20 → -1 ≤ x ∧ x ≤ 2) ∧
    (-2 ≤ y → y < -1 → 0 ≤ x ∧ x ≤ 3/2) ∧
    (-4 ≤ y → y < -2 → (y + 2) / 4 ≤ x ∧ x ≤ 3/2) ∧
    (-21/5 ≤ y → y < -4 → -(5 * y + 21) / 2 ≤ x ∧ x ≤ 3/2) ∧
    (-5 ≤ y → y < -21/5 → 0 ≤ x ∧ x ≤ 3/2) ∧
    (y < -5 → -(y + 5) / 2 ≤ x ∧ x ≤ 1/2) := by
  rcases mem_U0_true.1 h with h | h | h | h | h | h | h <;> pc_simp at h <;> casesm* _ ∧ _ <;>
    refine ⟨by linarith, by linarith, fun h1 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 h2 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 h2 => ⟨by linarith, by linarith⟩,
      fun h1 h2 => ⟨by linarith, by linarith⟩, fun h1 h2 => ⟨by linarith, by linarith⟩,
      fun h1 => ⟨by linarith, by linarith⟩⟩

/-- Points of the bands of `y ∈ [−1, 1]` (common to both pockets) lie in `U0 false`. -/
theorem mem_U0_false_upper (hy1 : y ≤ 1)
    (h1 : 1/20 < y → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ (85 + 200 * y) / 38)
    (h2 : 0 < y → y ≤ 1/20 → -(1 + 11 * y) / 2 ≤ x ∧ x ≤ 3 - 10 * y)
    (h3 : y = 0 → -3/2 ≤ x ∧ x ≤ 3)
    (h4 : -1/20 ≤ y → y < 0 → -3/2 - 10 * y ≤ x ∧ x ≤ 2)
    (h5 : -1 ≤ y → y < -1/20 → -1 ≤ x ∧ x ≤ 2) (hy : -1 ≤ y) : (x, y) ∈ U0 false := by
  rw [mem_U0_false]
  rcases lt_or_ge (1/20) y with hb | hb
  · obtain ⟨a, b⟩ := h1 hb
    left; pc_goal <;> linarith
  rcases lt_or_ge 0 y with hc | hc
  · obtain ⟨a, b⟩ := h2 hc hb
    rcases le_or_gt x (2 + 10 * y) with hd | hd
    · left; pc_goal <;> linarith
    · right; left; pc_goal <;> linarith
  rcases eq_or_lt_of_le hc with hc | hc
  · obtain ⟨a, b⟩ := h3 hc
    rcases le_or_gt x (3/2) with hd | hd
    · right; right; left; pc_goal <;> linarith
    · right; left; pc_goal <;> linarith
  rcases le_or_gt (-1/20) y with he | he
  · obtain ⟨a, b⟩ := h4 he hc
    rcases le_or_gt x (-1) with hd | hd
    · right; right; left; pc_goal <;> linarith
    · right; right; right; left; pc_goal <;> linarith
  · obtain ⟨a, b⟩ := h5 hy he
    right; right; right; left; pc_goal <;> linarith

theorem U0_false_subset_true {p : Point} (h : p ∈ U0 false) : p ∈ U0 true := by
  rw [mem_U0_true]; rw [mem_U0_false] at h; tauto

/-- **The horizontal sections of `U0 false` are intervals.** -/
theorem U0_false_horiz {x₁ x₂ : ℝ} (h₁ : (x₁, y) ∈ U0 false) (h₂ : (x₂, y) ∈ U0 false)
    (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) : (x, y) ∈ U0 false := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := U0_false_sec h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := U0_false_sec h₂
  rcases le_or_gt (-1) y with hy | hy
  · exact mem_U0_false_upper b2
      (fun h => ⟨by linarith [(a3 h).1], by linarith [(b3 h).2]⟩)
      (fun h h' => ⟨by linarith [(a4 h h').1], by linarith [(b4 h h').2]⟩)
      (fun h => ⟨by linarith [(a5 h).1], by linarith [(b5 h).2]⟩)
      (fun h h' => ⟨by linarith [(a6 h h').1], by linarith [(b6 h h').2]⟩)
      (fun h h' => ⟨by linarith [(a7 h h').1], by linarith [(b7 h h').2]⟩) hy
  · obtain ⟨c, _⟩ := a8 hy
    obtain ⟨_, d⟩ := b8 hy
    rw [mem_U0_false]; right; right; right; right; pc_goal <;> linarith

/-- **The horizontal sections of `U0 true` are intervals.** -/
theorem U0_true_horiz {x₁ x₂ : ℝ} (h₁ : (x₁, y) ∈ U0 true) (h₂ : (x₂, y) ∈ U0 true)
    (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) : (x, y) ∈ U0 true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := U0_true_sec h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := U0_true_sec h₂
  rcases le_or_gt (-1) y with hy | hy
  · exact U0_false_subset_true (mem_U0_false_upper b2
      (fun h => ⟨by linarith [(a3 h).1], by linarith [(b3 h).2]⟩)
      (fun h h' => ⟨by linarith [(a4 h h').1], by linarith [(b4 h h').2]⟩)
      (fun h => ⟨by linarith [(a5 h).1], by linarith [(b5 h).2]⟩)
      (fun h h' => ⟨by linarith [(a6 h h').1], by linarith [(b6 h h').2]⟩)
      (fun h h' => ⟨by linarith [(a7 h h').1], by linarith [(b7 h h').2]⟩) hy)
  rw [mem_U0_true]
  rcases le_or_gt (-2) y with h2 | h2
  · obtain ⟨c, _⟩ := a8 h2 hy; obtain ⟨_, d⟩ := b8 h2 hy
    right; right; right; right; left; pc_goal <;> linarith
  rcases le_or_gt (-4) y with h4 | h4
  · obtain ⟨c, _⟩ := a9 h4 h2; obtain ⟨_, d⟩ := b9 h4 h2
    rcases le_or_gt 0 x with h0 | h0
    · right; right; right; right; left; pc_goal <;> linarith
    · right; right; right; right; right; left; pc_goal <;> linarith
  rcases le_or_gt (-21/5) y with h5 | h5
  · obtain ⟨c, _⟩ := a10 h5 h4; obtain ⟨_, d⟩ := b10 h5 h4
    rcases le_or_gt 0 x with h0 | h0
    · right; right; right; right; left; pc_goal <;> linarith
    · right; right; right; right; right; left; pc_goal <;> linarith
  rcases le_or_gt (-5) y with h6 | h6
  · obtain ⟨c, _⟩ := a11 h6 h5; obtain ⟨_, d⟩ := b11 h6 h5
    right; right; right; right; left; pc_goal <;> linarith
  · obtain ⟨c, _⟩ := a12 h6; obtain ⟨_, d⟩ := b12 h6
    right; right; right; right; right; right; pc_goal <;> linarith

/-- The horizontal sections of `U0` are intervals. -/
theorem U0_horiz (one : Bool) {x₁ x₂ : ℝ} (h₁ : (x₁, y) ∈ U0 one) (h₂ : (x₂, y) ∈ U0 one)
    (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) : (x, y) ∈ U0 one := by
  cases one
  · exact U0_false_horiz h₁ h₂ hx₁ hx₂
  · exact U0_true_horiz h₁ h₂ hx₁ hx₂

end Sections

/-! ### The region of the fixed pocket polygon -/

/-- A point whose ray avoids `U0` is not in the region of `K0`. -/
theorem not_mem_filled_K0_of_ray (one : Bool) {q : Point} (hq : q ∉ U0 one) {d : Point}
    (hd : d ≠ 0) (hray : ∀ s : ℝ, 0 ≤ s → q + s • d ∉ U0 one) : q ∉ (K0 one).filled := by
  have hb : q ∉ (K0 one).boundary := fun h => hq (boundary_K0_subset one h)
  have hunb : ¬ IsBoundedSet (connectedComponentIn (K0 one).boundaryᶜ q) := by
    refine Jordan.not_isBoundedSet_connectedComponentIn_of_ray (K0 one) hd ?_
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hray s hs (boundary_K0_subset one hmem)
  rintro (h | h)
  · exact hb h
  · exact hunb h

/-- **The region of the fixed pocket polygon lies in `U0`.** -/
theorem filled_K0_subset (one : Bool) : (K0 one).filled ⊆ U0 one := by
  intro q hq
  by_contra hqU
  by_cases hleft : ∃ s : ℝ, 0 ≤ s ∧ (q.1 - s, q.2) ∈ U0 one
  · by_cases hright : ∃ s : ℝ, 0 ≤ s ∧ (q.1 + s, q.2) ∈ U0 one
    · obtain ⟨s₁, hs₁, h₁⟩ := hleft
      obtain ⟨s₂, hs₂, h₂⟩ := hright
      exact hqU (U0_horiz one h₁ h₂ (by linarith) (by linarith))
    · push Not at hright
      refine not_mem_filled_K0_of_ray one hqU (d := (1, 0)) (by simp) (fun s hs => ?_) hq
      have e : q + s • ((1 : ℝ), (0 : ℝ)) = (q.1 + s, q.2) := by ext <;> simp
      rw [e]; exact hright s hs
  · push Not at hleft
    refine not_mem_filled_K0_of_ray one hqU (d := (-1, 0)) (by simp) (fun s hs => ?_) hq
    have e : q + s • ((-1 : ℝ), (0 : ℝ)) = (q.1 - s, q.2) := by ext <;> simp; ring
    rw [e]; exact hleft s hs

/-- **Bounds of the pocket room** (relative coordinates). -/
theorem U0_bounds (one : Bool) {p : Point} (h : p ∈ U0 one) :
    -6 ≤ p.1 ∧ p.1 ≤ 15/2 ∧ -6 ≤ p.2 ∧ p.2 ≤ 1 ∧ (p.2 < 0 → -3/2 ≤ p.1 ∧ p.1 ≤ 2) ∧
      (p.2 ≤ 0 → -3/2 ≤ p.1 ∧ p.1 ≤ 3) ∧ (one = false → -5 ≤ p.2) := by
  cases one
  · rcases mem_U0_false.1 h with h | h | h | h | h <;> pc_simp at h <;> casesm* _ ∧ _ <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith,
        fun h' => ⟨by linarith, by linarith⟩, fun h' => ⟨by linarith, by linarith⟩,
        fun _ => by linarith⟩
  · rcases mem_U0_true.1 h with h | h | h | h | h | h | h <;> pc_simp at h <;>
      casesm* _ ∧ _ <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith,
        fun h' => ⟨by linarith, by linarith⟩, fun h' => ⟨by linarith, by linarith⟩,
        fun h' => absurd h' (by simp)⟩

/-! ### The pocket room of slot `σ` -/

/-- **The region of the pocket room of slot `σ` lies in the translated pieces.** -/
theorem filled_pocketPoly_subset (one : Bool) (σ : ℕ) {p : Point}
    (hp : p ∈ (pocketPoly one σ).filled) : (p.1 - (slotX σ : ℝ), p.2) ∈ U0 one := by
  rw [pocketPoly_eq_mapPoly] at hp
  have e : p = slotShift σ (p.1 - (slotX σ : ℝ), p.2) := by
    rw [slotShift_apply]; ext <;> simp
  rw [e] at hp
  exact filled_K0_subset one ((Hardening.Invariance.mem_filled_mapPoly_iff _ _).1 hp)

/-- **The pocket room lies in its box**: `[a − 6, a + 15/2] × [−6, 1]`, and below the base
line in `[a − 3/2, a + 2] × [−6, 0]` (`a = 27σ/2`); without spikes, `y ≥ −5`. -/
theorem pocketPoly_bounds (one : Bool) (σ : ℕ) {p : Point}
    (hp : p ∈ (pocketPoly one σ).filled) :
    (slotX σ : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ (slotX σ : ℝ) + 15/2 ∧ -6 ≤ p.2 ∧ p.2 ≤ 1 ∧
      (p.2 < 0 → (slotX σ : ℝ) - 3/2 ≤ p.1 ∧ p.1 ≤ (slotX σ : ℝ) + 2) ∧
      (p.2 ≤ 0 → (slotX σ : ℝ) - 3/2 ≤ p.1 ∧ p.1 ≤ (slotX σ : ℝ) + 3) ∧
      (one = false → -5 ≤ p.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := U0_bounds one (filled_pocketPoly_subset one σ hp)
  exact ⟨by simp at h1; linarith, by simp at h2; linarith, h3, h4,
    fun h => ⟨by have := (h5 h).1; simp at this; linarith,
      by have := (h5 h).2; simp at this; linarith⟩,
    fun h => ⟨by have := (h6 h).1; simp at this; linarith,
      by have := (h6 h).2; simp at this; linarith⟩, h7⟩

end ArtGallery.Sec5

end
