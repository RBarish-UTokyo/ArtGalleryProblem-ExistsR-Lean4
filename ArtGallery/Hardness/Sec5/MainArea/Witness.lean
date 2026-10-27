module

public import ArtGallery.Hardness.Sec5.MainArea.Pocket

/-!
# Section 5: pocket witnesses, the pocket room, the guard-segment lemma

All statements are about an arbitrary simple counter-clockwise polygon `P` containing the closed
pocket chain of slot `σ` as the contiguous chain of vertices `P.vtx (a + j)`, `j ≤ |pocket|`
(indices mod `P.n`), i.e. `PocketAt P one σ a`.  Coordinates relative to `a_σ` are written
`x' = p.1 − 27σ/2`, `y = p.2`.

* **Witness cones** (vertex cone lemma, `Vis/Cones`): `cone_t0`, `cone_t1`, `cone_u0`, `cone_u1`,
  `cone_q1`, `cone_q2`:
  | witness | cone (relative) |
  |---|---|
  | `t0 = (−3/2, 0)` | `y ≤ 0`, `x' + 10y + 3/2 ≥ 0` |
  | `t1 = (3, 0)` | `y ≥ 0`, `x' + 10y ≤ 3` |
  | `u0 = (0, −5)` | `x' ≥ 0`, `y ≥ −5` |
  | `u1 = (3/2, −5)` | `x' ≤ 3/2`, `y ≥ −5` |
  | `q1 = (−1/2, −4)` | `4x' ≥ y + 2`, `2x' + 5y + 21 ≥ 0` |
  | `q2 = (1/2, −6)` | `x' ≤ 1/2`, `2x' + y + 5 ≥ 0` |
* **Pocket room** (`pocket_isRoom`, via `isRoom_of_chain`): the region of `pocketPoly one σ` is a
  room of `P` with the door `m_R m_L` on `y = 1`.  The cones of `t0` and `t1` miss the door, so
  `V(t0), V(t1)` lie in the pocket room (`sees_t0_mem_room`, `sees_t1_mem_room`), hence in
  explicit boxes (`sees_t0_box`, `sees_t1_box`).
* **Guard-segment lemma** (Lemma 23 instance, `guard_segment`): a point seeing `t0, t1, u0, u1`
  lies on `s_σ = [a_σ, a_σ + (3/2, 0)]`; with the `one` spikes (`guard_segment_one`), a point
  seeing also `q1, q2` is `g1 = a_σ + (1/2, 0)`.
* **Separation between slots** (W2/W3 for base positions): `not_sees_t1_t1` (no point sees the
  `t1` of two different slots), and `farZone_not_sees_*`: a point of the zone where `V(t1)` of
  another slot lives sees no witness of slot `σ`.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set Polygon
open ArtGallery.Irrational (qdet)

/-! ### The pocket inside a polygon -/

/-- The closed pocket chain of slot `σ` (with or without `one` spikes) is the contiguous chain of
vertices `P.vtx (a + j)`, `j ≤ |pocket|`, of `P` (indices mod `P.n`). -/
def PocketAt (P : Polygon) (one : Bool) (σ a : ℕ) : Prop :=
  ∀ j ≤ (pocketRel one).length, P.vtx ((a + j) % P.n) = ratPoint ((pocketClosed one σ).getD j 0)

/-- **The pockets of the bottom wall are chains of the polygon.**  In the polygon whose vertex
list is the bottom wall followed by a list starting with `w_r`, the closed pocket chain of every
slot `σ < 4n` starts at index `pocketStart n Φ σ`. -/
theorem pocketAt_of_bottomWall {n : ℕ} {Φ : List ETRINV.Constraint} {rest : List Q2}
    (hrest : rest.getD 0 0 = wR n) {σ : ℕ} (hσ : σ < 4 * n) :
    PocketAt ⟨(bottomWall n Φ ++ rest).map ratPoint⟩ (slotOne n Φ σ) σ (pocketStart n Φ σ) := by
  intro j hj
  have hne : rest ≠ [] := by
    rintro rfl
    have := congrArg Prod.snd hrest
    simp [wR] at this
  have hlen : pocketStart n Φ σ + j < (bottomWall n Φ ++ rest).length := by
    have h1 := pocketStart_succ (n := n) (Φ := Φ) σ
    have h2 := pocketStart_mono (n := n) (Φ := Φ) (show σ + 1 ≤ 4 * n by omega)
    have h3 := length_bottomWall (n := n) (Φ := Φ)
    have h4 : 0 < rest.length := List.length_pos_iff.2 hne
    rw [List.length_append]; omega
  have hn : (Polygon.mk ((bottomWall n Φ ++ rest).map ratPoint)).n =
      (bottomWall n Φ ++ rest).length := by simp [Polygon.n]
  rw [Irrational.vtx_map_ratPoint, hn, Nat.mod_eq_of_lt hlen, bottomWall_append_getD hrest hσ hj]

/-- Relative coordinates `(p.1 − 27σ/2, p.2)`. -/
def rel (σ : ℕ) (p : Point) : Point := (p.1 - (slotX σ : ℝ), p.2)

/-- The point with relative coordinates `q` in slot `σ`. -/
def absPt (σ : ℕ) (q : Q2) : Point := ratPoint (q + slotA σ)

/-- Coordinates of a translated point. -/
theorem absPt_eq (σ : ℕ) (q : Q2) : absPt σ q = ((slotX σ : ℝ) + (q.1 : ℝ), (q.2 : ℝ)) := by
  simp [absPt, ratPoint, slotA, add_comm]

theorem rel_absPt (σ : ℕ) (q : Q2) : rel σ (absPt σ q) = ratPoint q := by
  rw [absPt_eq]; simp [rel, ratPoint]

/-- Vertices of the closed pocket chain. -/
theorem pocketClosed_getD (one : Bool) (σ : ℕ) {j : ℕ} (hj : j < (pocketClosedRel one).length) :
    (pocketClosed one σ).getD j 0 = (pocketClosedRel one).getD j 0 + slotA σ := by
  rw [List.getD_eq_getElem _ _ (by simpa [pocketClosed] using hj), List.getD_eq_getElem _ _ hj]
  simp [pocketClosed]

/-- Determinants are translation invariant (in relative coordinates). -/
theorem det_absPt_absPt (σ : ℕ) (A B : Q2) (p : Point) :
    det (absPt σ A) (absPt σ B) p = det (ratPoint A) (ratPoint B) (rel σ p) := by
  rw [absPt_eq, absPt_eq]; simp only [det, rel, ratPoint]; ring

theorem det_absPt_left (σ : ℕ) (A : Q2) (p q : Point) :
    det (absPt σ A) p q = det (ratPoint A) (rel σ p) (rel σ q) := by
  rw [absPt_eq]; simp only [det, rel, ratPoint]; ring

theorem det_absPt_right (σ : ℕ) (A : Q2) (p q : Point) :
    det p q (absPt σ A) = det (rel σ p) (rel σ q) (ratPoint A) := by
  rw [absPt_eq]; simp only [det, rel, ratPoint]; ring

section General

variable {P : Polygon} {one : Bool} {σ a : ℕ}

theorem PocketAt.vtx (hK : PocketAt P one σ a) {j : ℕ} (hj : j ≤ (pocketRel one).length) :
    P.vtx ((a + j) % P.n) = absPt σ ((pocketClosedRel one).getD j 0) := by
  rw [hK j hj, pocketClosed_getD one σ (by rw [length_pocketClosedRel]; omega)]; rfl

/-- The pocket room is the sub-polygon cut off by the door: its vertices are a chain of `P`. -/
theorem PocketAt.chain (hK : PocketAt P one σ a) :
    ∀ j ≤ (pocketRel one).length, (pocketPoly one σ).vtx j = P.vtx ((a + j) % P.n) := by
  intro j hj; rw [vtx_pocketPoly, hK j hj]

/-- **The pocket room is a room** of `P`; its door is the mouth `m_R m_L` on `y = 1`. -/
theorem pocket_isRoom (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) :
    P.IsRoom (pocketPoly one σ).filled
      (ArtGallery.segment (ratPoint (mR σ)) (ratPoint (mL σ))) := by
  have h := isRoom_of_chain hP hL (simple_pocketPoly one σ) (interiorLeft_pocketPoly one σ)
    (n_pocketPoly one σ) hK.chain
  have e1 : (pocketPoly one σ).vtx (pocketRel one).length = ratPoint (mR σ) := by
    rw [vtx_pocketPoly, pocketClosed_eq, List.getD_append_right _ _ _ _ (by rw [length_pocket]),
      length_pocket, Nat.sub_self, List.getD_cons_zero]
  have e0 : (pocketPoly one σ).vtx 0 = ratPoint (mL σ) := by
    rw [vtx_pocketPoly]; cases one <;> rfl
  rwa [e1, e0] at h

/-- The chain vertices lie in the pocket room. -/
theorem pocket_vtx_mem_room {j : ℕ} (hj : j ≤ (pocketRel one).length) :
    absPt σ ((pocketClosedRel one).getD j 0) ∈ (pocketPoly one σ).filled := by
  have : (pocketPoly one σ).vtx j ∈ (pocketPoly one σ).filled :=
    Or.inl ⟨j, by rw [n_pocketPoly]; omega, Geometry.left_mem_segment _ _⟩
  rwa [vtx_pocketPoly, pocketClosed_getD one σ (by rw [length_pocketClosedRel]; omega)] at this

/-- The chain vertices lie in the region of `P`. -/
theorem PocketAt.vtx_mem_filled (hK : PocketAt P one σ a) (hP : P.Simple) {j : ℕ}
    (hj : j ≤ (pocketRel one).length) :
    absPt σ ((pocketClosedRel one).getD j 0) ∈ P.filled := by
  have hn : 0 < P.n := by have := hP.1; omega
  rw [← hK.vtx hj]
  exact Or.inl ⟨_, Nat.mod_lt _ hn, Geometry.left_mem_segment _ _⟩

/-- **Vertex cone at a pocket vertex.**  If the pocket vertex `B = v_j` (`1 ≤ j < |pocket|`, with
neighbours `A = v_{j−1}`, `C = v_{j+1}`) is convex, every point seen from it is in its cone. -/
theorem pocket_cone (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {j : ℕ}
    (hj1 : 1 ≤ j) (hjm : j < (pocketRel one).length) {A B C : Q2}
    (hA : (pocketClosedRel one).getD (j - 1) 0 = A) (hB : (pocketClosedRel one).getD j 0 = B)
    (hC : (pocketClosedRel one).getD (j + 1) 0 = C) (hconv : 0 < qdet A B C) {p : Point}
    (h : P.Sees (absPt σ B) p) :
    0 ≤ det (ratPoint A) (ratPoint B) (rel σ p) ∧ 0 ≤ det (ratPoint B) (ratPoint C) (rel σ p) := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hu : P.vtx (((a + j) % P.n + P.n - 1) % P.n) = absPt σ A := by
    have := chain_prev hn a hj1
    unfold Jordan.prevIdx at this
    rw [this, hK.vtx (by omega), hA]
  have hw : P.vtx (((a + j) % P.n + 1) % P.n) = absPt σ C := by
    rw [chain_succ, hK.vtx (by omega), hC]
  have hc : 0 < det (absPt σ A) (absPt σ B) (absPt σ C) := by
    rw [det_absPt_absPt, rel_absPt, Irrational.det_ratPoint]; exact_mod_cast hconv
  have := sees_subset_cone hP hL (Nat.mod_lt _ hn) hu (by rw [hK.vtx hjm.le, hB]) hw hc h
  rwa [det_absPt_absPt, det_absPt_absPt] at this

/-- **Blocking by a pocket edge.**  A segment properly crossing the pocket edge `v_j v_{j+1}`
(`j < |pocket|`) is not contained in the region. -/
theorem pocket_not_sees_cross (hP : P.Simple) (hK : PocketAt P one σ a) {j : ℕ}
    (hjm : j < (pocketRel one).length) {A B : Q2}
    (hA : (pocketClosedRel one).getD j 0 = A) (hB : (pocketClosedRel one).getD (j + 1) 0 = B)
    {p q : Point}
    (h₁ : det (ratPoint A) (ratPoint B) (rel σ p) * det (ratPoint A) (ratPoint B) (rel σ q) < 0)
    (h₂ : det (rel σ p) (rel σ q) (ratPoint A) * det (rel σ p) (rel σ q) (ratPoint B) < 0) :
    ¬ P.Sees p q := by
  have hn : 0 < P.n := by have := hP.1; omega
  refine not_sees_of_proper_cross hP (Nat.mod_lt (a + j) hn) ?_ ?_
  · rw [chain_succ, hK.vtx hjm.le, hK.vtx (by omega), hA, hB, det_absPt_absPt, det_absPt_absPt]
    exact h₁
  · rw [chain_succ, hK.vtx hjm.le, hK.vtx (by omega), hA, hB, det_absPt_right, det_absPt_right]
    exact h₂

end General

/-! ### The witnesses -/

/-- `t0` as a point of slot `σ`. -/
def t0Pt (σ : ℕ) : Point := absPt σ t0Rel
/-- `t1` as a point of slot `σ`. -/
def t1Pt (σ : ℕ) : Point := absPt σ t1Rel
/-- `u0` as a point of slot `σ`. -/
def u0Pt (σ : ℕ) : Point := absPt σ u0Rel
/-- `u1` as a point of slot `σ`. -/
def u1Pt (σ : ℕ) : Point := absPt σ u1Rel
/-- `q1` as a point of slot `σ`. -/
def q1Pt (σ : ℕ) : Point := absPt σ q1Rel
/-- `q2` as a point of slot `σ`. -/
def q2Pt (σ : ℕ) : Point := absPt σ q2Rel
/-- The value-`1` point `g1 = a_σ + (1/2, 0)` of slot `σ`. -/
def g1Pt (σ : ℕ) : Point := absPt σ g1Rel

/-- Unfold determinants of explicit rational points into linear expressions. -/
macro "det_simp" " at " h:ident : tactic =>
  `(tactic| (simp only [det, rel, ratPoint] at $h:ident; norm_num at $h:ident))

section Witnesses

variable {P : Polygon} {one : Bool} {σ a : ℕ}

/-- **Cone of `t0`.** -/
theorem cone_t0 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {p : Point}
    (h : P.Sees (t0Pt σ) p) :
    p.2 ≤ 0 ∧ 0 ≤ (p.1 - slotX σ) + 10 * p.2 + 3/2 := by
  have key : 0 ≤ det (ratPoint (-1/2, 0)) (ratPoint (-3/2, 0)) (rel σ p) ∧
      0 ≤ det (ratPoint (-3/2, 0)) (ratPoint (-1, -1/20)) (rel σ p) := by
    cases one
    · exact pocket_cone hP hL hK (A := (-1/2, 0)) (B := (-3/2, 0)) (C := (-1, -1/20))
        (j := 2) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
    · exact pocket_cone hP hL hK (A := (-1/2, 0)) (B := (-3/2, 0)) (C := (-1, -1/20))
        (j := 2) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
  obtain ⟨h1, h2⟩ := key
  det_simp at h1; det_simp at h2
  constructor <;> linarith

/-- **Cone of `t1`.** -/
theorem cone_t1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {p : Point}
    (h : P.Sees (t1Pt σ) p) :
    0 ≤ p.2 ∧ (p.1 - slotX σ) + 10 * p.2 ≤ 3 := by
  have key : 0 ≤ det (ratPoint (2, 0)) (ratPoint (3, 0)) (rel σ p) ∧
      0 ≤ det (ratPoint (3, 0)) (ratPoint (5/2, 1/20)) (rel σ p) := by
    cases one
    · exact pocket_cone hP hL hK (A := (2, 0)) (B := (3, 0)) (C := (5/2, 1/20))
        (j := 11) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
    · exact pocket_cone hP hL hK (A := (2, 0)) (B := (3, 0)) (C := (5/2, 1/20))
        (j := 16) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
  obtain ⟨h1, h2⟩ := key
  det_simp at h1; det_simp at h2
  constructor <;> linarith

/-- **Cone of `u0`** (`x' ≥ 0`; without spikes `y ≥ −5`, with spikes `2x' + y + 5 ≥ 0`). -/
theorem cone_u0 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {p : Point}
    (h : P.Sees (u0Pt σ) p) :
    slotX σ ≤ p.1 ∧ (one = false → -5 ≤ p.2) ∧
      (one = true → 0 ≤ 2 * (p.1 - slotX σ) + p.2 + 5) := by
  cases one
  · have key : 0 ≤ det (ratPoint (0, -1)) (ratPoint (0, -5)) (rel σ p) ∧
        0 ≤ det (ratPoint (0, -5)) (ratPoint (3/2, -5)) (rel σ p) :=
      pocket_cone hP hL hK (A := (0, -1)) (B := (0, -5)) (C := (3/2, -5))
        (j := 6) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
    obtain ⟨h1, h2⟩ := key
    det_simp at h1; det_simp at h2
    exact ⟨by linarith, fun _ => by linarith, fun h => by simp at h⟩
  · have key : 0 ≤ det (ratPoint (0, -21/5)) (ratPoint (0, -5)) (rel σ p) ∧
        0 ≤ det (ratPoint (0, -5)) (ratPoint (1/2, -6)) (rel σ p) :=
      pocket_cone hP hL hK (A := (0, -21/5)) (B := (0, -5)) (C := (1/2, -6))
        (j := 9) (by norm_num) (by decide) rfl rfl rfl
        (by norm_num [qdet]) h
    obtain ⟨h1, h2⟩ := key
    det_simp at h1; det_simp at h2
    exact ⟨by linarith, fun h => by simp at h, fun _ => by linarith⟩

/-- **Cone of `u1`** (`x' ≤ 3/2`, `y ≥ −5`). -/
theorem cone_u1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) {p : Point}
    (h : P.Sees (u1Pt σ) p) :
    p.1 ≤ slotX σ + 3/2 ∧ -5 ≤ p.2 := by
  cases one
  · have key : 0 ≤ det (ratPoint (0, -5)) (ratPoint (3/2, -5)) (rel σ p) ∧
        0 ≤ det (ratPoint (3/2, -5)) (ratPoint (3/2, -1)) (rel σ p) :=
      pocket_cone hP hL hK (A := (0, -5)) (B := (3/2, -5)) (C := (3/2, -1))
        (j := 7) (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet]) h
    obtain ⟨h1, h2⟩ := key
    det_simp at h1; det_simp at h2
    constructor <;> linarith
  · have key : 0 ≤ det (ratPoint (1/2, -5)) (ratPoint (3/2, -5)) (rel σ p) ∧
        0 ≤ det (ratPoint (3/2, -5)) (ratPoint (3/2, -1)) (rel σ p) :=
      pocket_cone hP hL hK (A := (1/2, -5)) (B := (3/2, -5)) (C := (3/2, -1))
        (j := 12) (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet]) h
    obtain ⟨h1, h2⟩ := key
    det_simp at h1; det_simp at h2
    constructor <;> linarith

end Witnesses

section Spikes

variable {P : Polygon} {σ a : ℕ}

/-- **Cone of `q1`** (`4x' ≥ y + 2`: the upper boundary passes through `R0` and `g1`;
`2x' + 5y + 21 ≥ 0`). -/
theorem cone_q1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a) {p : Point}
    (h : P.Sees (q1Pt σ) p) :
    p.2 + 2 ≤ 4 * (p.1 - slotX σ) ∧ 0 ≤ 2 * (p.1 - slotX σ) + 5 * p.2 + 21 := by
  have key : 0 ≤ det (ratPoint (0, -2)) (ratPoint (-1/2, -4)) (rel σ p) ∧
      0 ≤ det (ratPoint (-1/2, -4)) (ratPoint (0, -21/5)) (rel σ p) :=
    pocket_cone hP hL hK (A := (0, -2)) (B := (-1/2, -4)) (C := (0, -21/5))
      (j := 7) (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet]) h
  obtain ⟨h1, h2⟩ := key
  det_simp at h1; det_simp at h2
  constructor <;> linarith

/-- **Cone of `q2`** (`x' ≤ 1/2`, `2x' + y + 5 ≥ 0`). -/
theorem cone_q2 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a) {p : Point}
    (h : P.Sees (q2Pt σ) p) :
    p.1 ≤ slotX σ + 1/2 ∧ 0 ≤ 2 * (p.1 - slotX σ) + p.2 + 5 := by
  have key : 0 ≤ det (ratPoint (0, -5)) (ratPoint (1/2, -6)) (rel σ p) ∧
      0 ≤ det (ratPoint (1/2, -6)) (ratPoint (1/2, -5)) (rel σ p) :=
    pocket_cone hP hL hK (A := (0, -5)) (B := (1/2, -6)) (C := (1/2, -5))
      (j := 10) (by norm_num) (by decide) rfl rfl rfl (by norm_num [qdet]) h
  obtain ⟨h1, h2⟩ := key
  det_simp at h1; det_simp at h2
  constructor <;> linarith

end Spikes

/-! ### The guard-segment lemma -/

section GuardSegment

variable {P : Polygon} {one : Bool} {σ a : ℕ}

/-- **Guard-segment lemma** (Lemma 23 instance): a point seeing `t0, t1, u0, u1` of slot `σ`
lies on the guard segment `s_σ = [a_σ, a_σ + (3/2, 0)]`. -/
theorem guard_segment (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h0 : P.Sees p (t0Pt σ)) (h1 : P.Sees p (t1Pt σ)) (h2 : P.Sees p (u0Pt σ))
    (h3 : P.Sees p (u1Pt σ)) :
    p.2 = 0 ∧ (slotX σ : ℝ) ≤ p.1 ∧ p.1 ≤ slotX σ + 3/2 := by
  obtain ⟨a0, -⟩ := cone_t0 hP hL hK (sees_comm.1 h0)
  obtain ⟨a1, -⟩ := cone_t1 hP hL hK (sees_comm.1 h1)
  obtain ⟨a2, -⟩ := cone_u0 hP hL hK (sees_comm.1 h2)
  obtain ⟨a3, -⟩ := cone_u1 hP hL hK (sees_comm.1 h3)
  exact ⟨le_antisymm a0 a1, a2, a3⟩

/-- **Guard-segment lemma with `one` spikes**: a point seeing `t0, t1, u0, u1, q1, q2` is the
value-`1` point `g1 = a_σ + (1/2, 0)`. -/
theorem guard_segment_one (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    {p : Point} (h0 : P.Sees p (t0Pt σ)) (h1 : P.Sees p (t1Pt σ)) (h2 : P.Sees p (u0Pt σ))
    (h3 : P.Sees p (u1Pt σ)) (h4 : P.Sees p (q1Pt σ)) (h5 : P.Sees p (q2Pt σ)) :
    p = g1Pt σ := by
  obtain ⟨e, -, -⟩ := guard_segment hP hL hK h0 h1 h2 h3
  obtain ⟨b1, -⟩ := cone_q1 hP hL hK (sees_comm.1 h4)
  obtain ⟨b2, -⟩ := cone_q2 hP hL hK (sees_comm.1 h5)
  rw [g1Pt, absPt_eq]
  refine Prod.ext ?_ ?_
  · simp only [g1Rel]; push_cast; linarith
  · simp only [g1Rel]; push_cast; exact e

end GuardSegment

/-! ### The pocket room contains the visibility sets of `t0` and `t1` -/

section Room

variable {P : Polygon} {one : Bool} {σ a : ℕ}

/-- Points of the door: `y = 1`, `x' ∈ [−6, 15/2]`. -/
theorem mem_door {y : Point} (hy : y ∈ ArtGallery.segment (ratPoint (mR σ)) (ratPoint (mL σ))) :
    y.2 = 1 ∧ (slotX σ : ℝ) - 6 ≤ y.1 ∧ y.1 ≤ slotX σ + 15/2 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hy
  simp only [mR, mL, mouthR, mouthL, slotA, ratPoint, Prod.fst_add, Prod.snd_add]
  push_cast
  refine ⟨by ring, by nlinarith, by nlinarith⟩

/-- A segment seen from `t` contains only points seen from `t`. -/
theorem sees_of_mem_segment {t p y : Point} (hs : P.Sees t p) (hy : y ∈ ArtGallery.segment t p) :
    P.Sees t y :=
  fun _ hz => hs (Geometry.segment_subset_of_convex (Geometry.segment_convex t p)
    (Geometry.left_mem_segment t p) hy hz)

/-- **Room lemma for the pocket**: if no point of the door is seen from the point `t` of the
pocket room, every point seen from `t` lies in the pocket room. -/
theorem sees_mem_room_of_door (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {t p : Point} (ht : t ∈ (pocketPoly one σ).filled) (hs : P.Sees t p)
    (hdoor : ∀ y : Point, P.Sees t y → y.2 = 1 → (slotX σ : ℝ) - 6 ≤ y.1 →
      y.1 ≤ slotX σ + 15/2 → False) :
    p ∈ (pocketPoly one σ).filled := by
  by_contra hp
  obtain ⟨y, hyD, hy⟩ := sees_crosses_door (pocket_isRoom hP hL hK) ht hp hs
  obtain ⟨e1, e2, e3⟩ := mem_door hyD
  exact hdoor y (sees_of_mem_segment hs hy) e1 e2 e3

theorem t0Pt_mem_room : t0Pt σ ∈ (pocketPoly one σ).filled := by
  have := pocket_vtx_mem_room (one := one) (σ := σ) (j := 2)
    (by rw [length_pocketRel]; split <;> omega)
  cases one <;> exact this

theorem t1Pt_mem_room : t1Pt σ ∈ (pocketPoly one σ).filled := by
  cases one
  · exact pocket_vtx_mem_room (one := false) (σ := σ) (j := 11) (by decide)
  · exact pocket_vtx_mem_room (one := true) (σ := σ) (j := 16) (by decide)

/-- **`V(t0)` lies in the pocket room** (the cone of `t0` lies below `y = 0`). -/
theorem sees_t0_mem_room (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (t0Pt σ) p) : p ∈ (pocketPoly one σ).filled :=
  sees_mem_room_of_door hP hL hK t0Pt_mem_room h fun y hy e1 _ _ => by
    have := (cone_t0 hP hL hK hy).1; linarith

/-- **`V(t1)` lies in the pocket room** (the cone of `t1` meets `y = 1` only at `x' ≤ −7`). -/
theorem sees_t1_mem_room (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (t1Pt σ) p) : p ∈ (pocketPoly one σ).filled :=
  sees_mem_room_of_door hP hL hK t1Pt_mem_room h fun y hy e1 e2 _ => by
    have := (cone_t1 hP hL hK hy).2; linarith

/-- **`V(t1)` box**: `y ∈ [0, 1]`, `x' ∈ [−6, 3]`. -/
theorem sees_t1_box (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (t1Pt σ) p) :
    0 ≤ p.2 ∧ p.2 ≤ 1 ∧ (slotX σ : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ slotX σ + 3 := by
  obtain ⟨b1, b2, -, b4, -⟩ := pocketPoly_bounds one σ (sees_t1_mem_room hP hL hK h)
  obtain ⟨c1, c2⟩ := cone_t1 hP hL hK h
  exact ⟨c1, b4, b1, by linarith⟩

/-- **`V(t0)` box**: `y ∈ [−6, 0]`, `x' ∈ [−3/2, 3]`. -/
theorem sees_t0_box (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (h : P.Sees (t0Pt σ) p) :
    -6 ≤ p.2 ∧ p.2 ≤ 0 ∧ (slotX σ : ℝ) - 3/2 ≤ p.1 ∧ p.1 ≤ slotX σ + 3 := by
  obtain ⟨-, -, b3, -, -, b6, -⟩ := pocketPoly_bounds one σ (sees_t0_mem_room hP hL hK h)
  obtain ⟨c1, -⟩ := cone_t0 hP hL hK h
  exact ⟨b3, c1, (b6 c1).1, (b6 c1).2⟩

end Room


/-! ### Separation between slots -/

section Separation

variable {P : Polygon} {one one' : Bool} {σ σ' a a' : ℕ}

/-- Distinct slots are `27/2` apart. -/
theorem slotX_sep_real {σ σ' : ℕ} (h : σ ≠ σ') :
    (slotX σ : ℝ) + 27/2 ≤ slotX σ' ∨ (slotX σ' : ℝ) + 27/2 ≤ slotX σ := by
  rcases lt_or_gt_of_ne h with h | h
  · left
    have h' : ((slotX σ + 27/2 : ℚ) : ℝ) ≤ ((slotX σ' : ℚ) : ℝ) := Rat.cast_le.2 (slotX_lt h)
    push_cast at h'; exact h'
  · right
    have h' : ((slotX σ' + 27/2 : ℚ) : ℝ) ≤ ((slotX σ : ℚ) : ℝ) := Rat.cast_le.2 (slotX_lt h)
    push_cast at h'; exact h'

/-- **(W2) for base positions**: no point sees the `t1` witnesses of two different slots. -/
theorem not_sees_t1_t1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    (hK' : PocketAt P one' σ' a') (hne : σ ≠ σ') {p : Point} (h : P.Sees p (t1Pt σ)) :
    ¬ P.Sees p (t1Pt σ') := fun h' => by
  obtain ⟨-, -, b1, b2⟩ := sees_t1_box hP hL hK (sees_comm.1 h)
  obtain ⟨-, -, c1, c2⟩ := sees_t1_box hP hL hK' (sees_comm.1 h')
  rcases slotX_sep_real hne with e | e <;> linarith

/-- The zone of slot `σ` where the `t1`-visibility sets of the other slots live:
`y ∈ [0, 1]` and `x' ≤ −21/2` or `x' ≥ 15/2`. -/
def FarZone (σ : ℕ) (p : Point) : Prop :=
  0 ≤ p.2 ∧ p.2 ≤ 1 ∧ (p.1 ≤ (slotX σ : ℝ) - 21/2 ∨ (slotX σ : ℝ) + 15/2 ≤ p.1)

/-- `V(t1)` of a slot `σ' ≠ σ` lies in the far zone of `σ`. -/
theorem sees_t1_farZone (hP : P.Simple) (hL : P.InteriorLeft) (hK' : PocketAt P one' σ' a')
    (hne : σ' ≠ σ) {p : Point} (h : P.Sees p (t1Pt σ')) : FarZone σ p := by
  obtain ⟨b1, b2, b3, b4⟩ := sees_t1_box hP hL hK' (sees_comm.1 h)
  refine ⟨b1, b2, ?_⟩
  rcases slotX_sep_real hne with e | e
  · left; linarith
  · right; linarith

/-- A far-zone point does not see `t0` (`V(t0)` lies in the pocket room, below `y = 0`). -/
theorem farZone_not_sees_t0 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (t0Pt σ) := fun h => by
  obtain ⟨-, b2, b3, b4⟩ := sees_t0_box hP hL hK (sees_comm.1 h)
  obtain ⟨z1, -, z3⟩ := hz
  rcases z3 with z | z <;> linarith

/-- A far-zone point does not see `t1` (`V(t1)` lies in its box). -/
theorem farZone_not_sees_t1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (t1Pt σ) := fun h => by
  obtain ⟨-, -, b3, b4⟩ := sees_t1_box hP hL hK (sees_comm.1 h)
  obtain ⟨-, -, z3⟩ := hz
  rcases z3 with z | z <;> linarith

/-- Index of the shaft wall `u1 → E`. -/
theorem idxU1_lt (one : Bool) : idxU1 one < (pocketRel one).length := by cases one <;> decide

/-- A far-zone point does not see `u0` (cone, or the segment crosses the wall `u1 → E`). -/
theorem farZone_not_sees_u0 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (u0Pt σ) := fun h => by
  obtain ⟨c1, -, -⟩ := cone_u0 hP hL hK (sees_comm.1 h)
  obtain ⟨z1, z2, z3⟩ := hz
  rcases z3 with z | z
  · linarith
  -- the segment from `u0` crosses the shaft wall `u1 → E`
  refine pocket_not_sees_cross hP hK (j := idxU1 one) (idxU1_lt one) (A := (3/2, -5))
    (B := (3/2, -1)) (by cases one <;> rfl) (by cases one <;> rfl) ?_ ?_ (sees_comm.1 h)
  · rw [u0Pt, rel_absPt]
    apply mul_neg_of_pos_of_neg
    · simp only [det, ratPoint, u0Rel]; norm_num
    · simp only [det, rel, ratPoint]; norm_num; linarith
  · rw [u0Pt, rel_absPt]
    apply mul_neg_of_neg_of_pos
    · simp only [det, rel, ratPoint, u0Rel]; norm_num; linarith
    · simp only [det, rel, ratPoint, u0Rel]; norm_num; linarith

/-- A far-zone point does not see `u1` (cone, or the segment crosses the wall `x' = 0`). -/
theorem farZone_not_sees_u1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (u1Pt σ) := fun h => by
  obtain ⟨c1, -⟩ := cone_u1 hP hL hK (sees_comm.1 h)
  obtain ⟨z1, z2, z3⟩ := hz
  rcases z3 with z | z
  swap
  · linarith
  -- the segment from `u1` crosses the wall `x' = 0` below `D` (edge `D → u0` resp. `Q' → u0`)
  cases one
  · refine pocket_not_sees_cross hP hK (j := 5) (by decide) (A := (0, -1)) (B := (0, -5))
      rfl rfl ?_ ?_ (sees_comm.1 h)
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · simp only [det, ratPoint, u1Rel]; norm_num
      · simp only [det, rel, ratPoint]; norm_num; linarith
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_neg_of_pos
      · simp only [det, rel, ratPoint, u1Rel]; norm_num; linarith
      · simp only [det, rel, ratPoint, u1Rel]; norm_num; linarith
  · refine pocket_not_sees_cross hP hK (j := 8) (by decide) (A := (0, -21/5)) (B := (0, -5))
      rfl rfl ?_ ?_ (sees_comm.1 h)
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_pos_of_neg
      · simp only [det, ratPoint, u1Rel]; norm_num
      · simp only [det, rel, ratPoint]; norm_num; linarith
    · rw [u1Pt, rel_absPt]
      apply mul_neg_of_neg_of_pos
      · simp only [det, rel, ratPoint, u1Rel]; norm_num; linarith
      · simp only [det, rel, ratPoint, u1Rel]; norm_num; linarith

/-- A far-zone point does not see `q1` (cone, or the segment crosses `u1 → E`). -/
theorem farZone_not_sees_q1 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (q1Pt σ) := fun h => by
  obtain ⟨c1, -⟩ := cone_q1 hP hL hK (sees_comm.1 h)
  obtain ⟨z1, z2, z3⟩ := hz
  rcases z3 with z | z
  · linarith
  -- the segment from `q1` crosses the shaft wall `u1 → E`
  refine pocket_not_sees_cross hP hK (j := 12) (by decide) (A := (3/2, -5)) (B := (3/2, -1))
    rfl rfl ?_ ?_ (sees_comm.1 h)
  · rw [q1Pt, rel_absPt]
    apply mul_neg_of_pos_of_neg
    · simp only [det, ratPoint, q1Rel]; norm_num
    · simp only [det, rel, ratPoint]; norm_num; linarith
  · rw [q1Pt, rel_absPt]
    apply mul_neg_of_neg_of_pos
    · simp only [det, rel, ratPoint, q1Rel]; norm_num; linarith
    · simp only [det, rel, ratPoint, q1Rel]; norm_num; linarith

/-- A far-zone point does not see `q2` (cone). -/
theorem farZone_not_sees_q2 (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    {p : Point} (hz : FarZone σ p) : ¬ P.Sees p (q2Pt σ) := fun h => by
  obtain ⟨c1, c2⟩ := cone_q2 hP hL hK (sees_comm.1 h)
  obtain ⟨z1, z2, z3⟩ := hz
  rcases z3 with z | z <;> linarith

/-- **(W3) for base positions**: a point seeing the `t1` witness of another slot sees none of the
witnesses `t0, t1, u0, u1` of slot `σ`. -/
theorem sees_t1_other_not_sees (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    (hK' : PocketAt P one' σ' a') (hne : σ' ≠ σ) {p : Point} (h : P.Sees p (t1Pt σ')) :
    ¬ P.Sees p (t0Pt σ) ∧ ¬ P.Sees p (t1Pt σ) ∧ ¬ P.Sees p (u0Pt σ) ∧ ¬ P.Sees p (u1Pt σ) := by
  have hz := sees_t1_farZone hP hL hK' hne h
  exact ⟨farZone_not_sees_t0 hP hL hK hz, farZone_not_sees_t1 hP hL hK hz,
    farZone_not_sees_u0 hP hL hK hz, farZone_not_sees_u1 hP hL hK hz⟩

/-- **(W3) for base positions with spikes**: a point seeing the `t1` witness of another slot sees
neither `q1` nor `q2` of slot `σ`. -/
theorem sees_t1_other_not_sees_q (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    (hK' : PocketAt P one' σ' a') (hne : σ' ≠ σ) {p : Point} (h : P.Sees p (t1Pt σ')) :
    ¬ P.Sees p (q1Pt σ) ∧ ¬ P.Sees p (q2Pt σ) := by
  have hz := sees_t1_farZone hP hL hK' hne h
  exact ⟨farZone_not_sees_q1 hP hL hK hz, farZone_not_sees_q2 hP hL hK hz⟩

end Separation

end ArtGallery.Sec5

end
