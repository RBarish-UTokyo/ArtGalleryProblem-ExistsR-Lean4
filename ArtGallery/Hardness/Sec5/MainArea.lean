module

public import ArtGallery.Hardness.Sec5.Params
public import Mathlib.Data.List.GetD

/-!
# Section 5: the main area — pockets, bottom wall, main hexagon (definitions)

The data of `docs/section5/02_main_area.md`.

* **Pockets.**  The pocket of slot `σ` is the list `pocketRel one` (vertices relative to
  `a_σ = (27σ/2, 0)`, boundary order of the counter-clockwise polygon) translated by `a_σ`:
  ```
  m_L=(-6,1)  H'=(-1/2,0)  t0=(-3/2,0)  K'=(-1,-1/20)  C=(-1,-1)  D=(0,-1)
    [R0=(0,-2)  q1=(-1/2,-4)  Q'=(0,-21/5)]                       (only if `one`)
  u0=(0,-5)
    [q2=(1/2,-6)  (1/2,-5)]                                       (only if `one`)
  u1=(3/2,-5)  E=(3/2,-1)  G=(2,-1)  H=(2,0)  t1=(3,0)  K=(5/2,1/20)
  ```
  followed by the right mouth corner `m_R = (15/2, 1)`, which is the next pocket's `m_L`
  (pitch `27/2`).  `pocketClosed one σ` is the pocket followed by `m_R`: the vertex chain of the
  pocket room, closed by the door `m_R → m_L` on `y = 1`.
* **Witnesses** (relative): `t0, t1, u0, u1, q1, q2` and the value-`1` point `g1 = (1/2, 0)`,
  with their indices in `pocketClosedRel one`.
* **Bottom wall**: the pockets of slots `0, …, 4n−1`, left to right (`bottom_wall`), and the
  index `pocketStart n Φ σ` of the first vertex of pocket `σ` in it (`bottomWall_getD`).
* **Main hexagon**: `w_l = (−6, 1)`, `w_r = (54n − 6, 1)`, `v_r = (S, S)`, `t_r = (S, S + 3N)`,
  `t_l = (X_L, S + 3N)`, `v_l = (X_L, S)` (`mainarea.corners`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery

/-! ### The pocket (relative coordinates) -/

/-- The first six pocket vertices `m_L, H', t0, K', C, D`. -/
def pocketHead : List Q2 := [(-6, 1), (-1/2, 0), (-3/2, 0), (-1, -1/20), (-1, -1), (0, -1)]

/-- The `one` spike with tip `q1`: `R0, q1, Q'`. -/
def pocketQ1 : List Q2 := [(0, -2), (-1/2, -4), (0, -21/5)]

/-- The vertex `u0`. -/
def pocketU0 : List Q2 := [(0, -5)]

/-- The `one` spike with tip `q2`: `q2, (1/2, −5)`. -/
def pocketQ2 : List Q2 := [(1/2, -6), (1/2, -5)]

/-- The last six pocket vertices `u1, E, G, H, t1, K`. -/
def pocketTail : List Q2 := [(3/2, -5), (3/2, -1), (2, -1), (2, 0), (3, 0), (5/2, 1/20)]

/-- **The pocket** relative to `a_σ` (13 vertices, 18 with the `one` spikes). -/
def pocketRel (one : Bool) : List Q2 :=
  pocketHead ++ (if one then pocketQ1 else []) ++ pocketU0 ++ (if one then pocketQ2 else []) ++
    pocketTail

/-- The right mouth corner `m_R = (15/2, 1)` (relative). -/
def mouthR : Q2 := (15/2, 1)

/-- The left mouth corner `m_L = (−6, 1)` (relative). -/
def mouthL : Q2 := (-6, 1)

/-- The pocket followed by the right mouth corner: the chain of the pocket room. -/
def pocketClosedRel (one : Bool) : List Q2 := pocketRel one ++ [mouthR]

/-- The pocket of slot `σ` (absolute coordinates). -/
def pocket (one : Bool) (σ : ℕ) : List Q2 := (pocketRel one).map (· + slotA σ)

/-- The pocket of slot `σ` followed by its right mouth corner. -/
def pocketClosed (one : Bool) (σ : ℕ) : List Q2 := (pocketClosedRel one).map (· + slotA σ)

/-- The left mouth corner of slot `σ`. -/
def mL (σ : ℕ) : Q2 := mouthL + slotA σ

/-- The right mouth corner of slot `σ`. -/
def mR (σ : ℕ) : Q2 := mouthR + slotA σ

theorem length_pocketRel (one : Bool) :
    (pocketRel one).length = if one then 18 else 13 := by
  cases one <;> rfl

theorem length_pocketClosedRel (one : Bool) :
    (pocketClosedRel one).length = (pocketRel one).length + 1 := by
  simp [pocketClosedRel]

theorem length_pocket (one : Bool) (σ : ℕ) : (pocket one σ).length = (pocketRel one).length := by
  simp [pocket]

theorem pocketClosed_eq (one : Bool) (σ : ℕ) : pocketClosed one σ = pocket one σ ++ [mR σ] := by
  simp [pocketClosed, pocket, pocketClosedRel, mR]

/-! ### Witnesses (relative coordinates) and their indices -/

/-- The roof-spike tip `t0 = (−3/2, 0)`. -/
def t0Rel : Q2 := (-3/2, 0)
/-- The floor-spike tip `t1 = (3, 0)`. -/
def t1Rel : Q2 := (3, 0)
/-- The shaft corner `u0 = (0, −5)`. -/
def u0Rel : Q2 := (0, -5)
/-- The shaft corner `u1 = (3/2, −5)`. -/
def u1Rel : Q2 := (3/2, -5)
/-- The `one`-spike tip `q1 = (−1/2, −4)`. -/
def q1Rel : Q2 := (-1/2, -4)
/-- The `one`-spike tip `q2 = (1/2, −6)`. -/
def q2Rel : Q2 := (1/2, -6)
/-- The value-`1` point `g1 = (1/2, 0)` of the guard segment. -/
def g1Rel : Q2 := (1/2, 0)

/-- Index of `t0` in the pocket. -/
def idxT0 : ℕ := 2
/-- Index of `u0` in the pocket. -/
def idxU0 (one : Bool) : ℕ := if one then 9 else 6
/-- Index of `u1` in the pocket. -/
def idxU1 (one : Bool) : ℕ := if one then 12 else 7
/-- Index of `t1` in the pocket. -/
def idxT1 (one : Bool) : ℕ := if one then 16 else 11
/-- Index of `q1` in the pocket (with spikes). -/
def idxQ1 : ℕ := 7
/-- Index of `q2` in the pocket (with spikes). -/
def idxQ2 : ℕ := 10

/-! ### The bottom wall -/

/-- **The bottom wall**: the pockets of slots `0, …, 4n − 1`, left to right. -/
def bottomWall (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  (List.range (4 * n)).flatMap fun σ => pocket (slotOne n Φ σ) σ

/-- The index of the first vertex (`m_L`) of pocket `σ` in the bottom wall. -/
def pocketStart (n : ℕ) (Φ : List ETRINV.Constraint) (σ : ℕ) : ℕ :=
  ((List.range σ).map fun s => (pocketRel (slotOne n Φ s)).length).sum

/-! ### The main hexagon -/

/-- `w_l = (−6, 1)`, the left mouth corner of slot `0`. -/
def wL : Q2 := (-6, 1)
/-- `w_r = (54n − 6, 1)`, the right mouth corner of slot `4n − 1`. -/
def wR (n : ℕ) : Q2 := (54 * (n : ℚ) - 6, 1)
/-- `v_r = (S, S)`. -/
def vR (n k : ℕ) : Q2 := ((S n k : ℚ), (S n k : ℚ))
/-- `t_r = (S, S + 3N)`. -/
def tR (n k : ℕ) : Q2 := ((S n k : ℚ), (S n k : ℚ) + 3 * (bigN n k : ℚ))
/-- `t_l = (X_L, S + 3N)`. -/
def tL (n k : ℕ) : Q2 := (XL n k, (S n k : ℚ) + 3 * (bigN n k : ℚ))
/-- `v_l = (X_L, S)`. -/
def vL (n k : ℕ) : Q2 := (XL n k, (S n k : ℚ))

/-- The top `y = S + 3N` of the main hexagon. -/
def hexTop (n k : ℕ) : ℚ := (S n k : ℚ) + 3 * (bigN n k : ℚ)

/-- The six corners of the main hexagon `H_M` in counter-clockwise order. -/
def hexagon (n k : ℕ) : List Q2 := [wL, wR n, vR n k, tR n k, tL n k, vL n k]

/-! ### Placement of the pockets in the bottom wall -/

section Placement

variable {α : Type*}

/-- Lookup in a concatenation `f 0 ++ … ++ f (m−1)` at offset `Σ_{s<σ} |f s| + j`. -/
theorem getD_flatMap_range (f : ℕ → List α) (d : α) {m σ j : ℕ} (hσ : σ < m)
    (hj : j < (f σ).length) :
    ((List.range m).flatMap f).getD (((List.range σ).map fun s => (f s).length).sum + j) d =
      (f σ).getD j d := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen : ∀ r, ((List.range r).flatMap f).length =
        ((List.range r).map fun s => (f s).length).sum := by
      intro r; simp [List.length_flatMap]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hσ with h | rfl
    · have hlt : ((List.range σ).map fun s => (f s).length).sum + j <
          ((List.range m).flatMap f).length := by
        rw [hlen]
        have key : ∀ r, σ < r → ((List.range σ).map fun s => (f s).length).sum + (f σ).length ≤
            ((List.range r).map fun s => (f s).length).sum := by
          intro r hr
          induction r with
          | zero => omega
          | succ r ihr =>
            rw [List.range_succ, List.map_append, List.sum_append]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h' | rfl
            · have := ihr h'; simp; omega
            · simp
        have := key m h; omega
      rw [List.getD_append _ _ _ _ hlt, ih h]
    · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1; omega

/-- The length of `f 0 ++ … ++ f (m−1)`. -/
theorem length_flatMap_range (f : ℕ → List α) (m : ℕ) :
    ((List.range m).flatMap f).length = ((List.range m).map fun s => (f s).length).sum := by
  simp [List.length_flatMap]

end Placement

variable {n : ℕ} {Φ : List ETRINV.Constraint}

/-- The bottom wall has `pocketStart n Φ (4n)` vertices. -/
theorem length_bottomWall : (bottomWall n Φ).length = pocketStart n Φ (4 * n) := by
  unfold bottomWall pocketStart
  rw [length_flatMap_range]
  simp [length_pocket]

/-- Pocket `σ + 1` starts right after pocket `σ`. -/
theorem pocketStart_succ (σ : ℕ) :
    pocketStart n Φ (σ + 1) = pocketStart n Φ σ + (pocketRel (slotOne n Φ σ)).length := by
  simp [pocketStart, List.range_succ]

/-- **Placement.** Vertex `j` of pocket `σ` is vertex `pocketStart σ + j` of the bottom wall. -/
theorem bottomWall_getD {σ j : ℕ} (hσ : σ < 4 * n) (hj : j < (pocketRel (slotOne n Φ σ)).length) :
    (bottomWall n Φ).getD (pocketStart n Φ σ + j) 0 = (pocket (slotOne n Φ σ) σ).getD j 0 := by
  have := getD_flatMap_range (fun σ => pocket (slotOne n Φ σ) σ) (0 : Q2) hσ
    (by rw [length_pocket]; exact hj)
  simpa [bottomWall, pocketStart, length_pocket] using this

/-- The left mouth corner of pocket `σ + 1` is the right mouth corner of pocket `σ`. -/
theorem mL_succ (σ : ℕ) : mL (σ + 1) = mR σ := by
  have h := slotX_succ σ
  simp only [mL, mR, mouthL, mouthR, slotA, Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true]
  rw [h]; ring

/-- The right mouth corner of the last pocket is `w_r`. -/
theorem mR_last (hn : 0 < n) : mR (4 * n - 1) = wR n := by
  have e : ((4 * n - 1 : ℕ) : ℚ) = 4 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [mR, mouthR, slotA, slotX, wR, e, Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true]
  ring

/-- The first vertex of pocket `σ` is `m_L(σ)`. -/
theorem pocket_getD_zero (one : Bool) (σ : ℕ) : (pocket one σ).getD 0 0 = mL σ := by
  cases one <;> rfl

/-- Every pocket has at least one vertex. -/
theorem length_pocketRel_pos (one : Bool) : 0 < (pocketRel one).length := by
  rw [length_pocketRel]; split <;> omega

/-- `pocketStart` is monotone. -/
theorem pocketStart_mono {σ σ' : ℕ} (h : σ ≤ σ') : pocketStart n Φ σ ≤ pocketStart n Φ σ' := by
  induction σ' with
  | zero => rw [Nat.le_zero.1 h]
  | succ r ih =>
    rcases Nat.lt_or_ge σ (r + 1) with h' | h'
    · have := ih (by omega); rw [pocketStart_succ]; omega
    · rw [show σ = r + 1 by omega]

/-- **Placement of the closed pocket chain.** If the bottom wall is followed by a list starting
with `w_r`, the vertices `pocketStart σ + j` (`j ≤ |pocket σ|`) of the concatenation are the
vertices of `pocketClosed σ` (the pocket followed by its right mouth corner). -/
theorem bottomWall_append_getD {rest : List Q2} (hrest : rest.getD 0 0 = wR n) {σ j : ℕ}
    (hσ : σ < 4 * n) (hj : j ≤ (pocketRel (slotOne n Φ σ)).length) :
    (bottomWall n Φ ++ rest).getD (pocketStart n Φ σ + j) 0 =
      (pocketClosed (slotOne n Φ σ) σ).getD j 0 := by
  have hs1 := pocketStart_succ (n := n) (Φ := Φ) σ
  have hmono := pocketStart_mono (n := n) (Φ := Φ) (show σ + 1 ≤ 4 * n by omega)
  rw [pocketClosed_eq]
  rcases Nat.lt_or_ge j (pocketRel (slotOne n Φ σ)).length with hj' | hj'
  · rw [List.getD_append _ _ _ _ (by rw [length_bottomWall]; omega), bottomWall_getD hσ hj',
      List.getD_append _ _ _ _ (by rw [length_pocket]; exact hj')]
  · have hjeq : j = (pocketRel (slotOne n Φ σ)).length := le_antisymm hj hj'
    subst hjeq
    rw [List.getD_append_right (pocket (slotOne n Φ σ) σ) [mR σ] 0 _ (by rw [length_pocket]),
      length_pocket, Nat.sub_self, List.getD_cons_zero, ← hs1]
    rcases Nat.lt_or_ge (σ + 1) (4 * n) with hσ' | hσ'
    · have hs2 := pocketStart_succ (n := n) (Φ := Φ) (σ + 1)
      have hmono2 := pocketStart_mono (n := n) (Φ := Φ) (show σ + 1 + 1 ≤ 4 * n by omega)
      have hpos := length_pocketRel_pos (slotOne n Φ (σ + 1))
      have h0 := bottomWall_getD (n := n) (Φ := Φ) hσ' hpos
      rw [Nat.add_zero, pocket_getD_zero, mL_succ] at h0
      rw [List.getD_append _ _ _ _ (by rw [length_bottomWall]; omega), h0]
    · have hσl : σ = 4 * n - 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [length_bottomWall, show σ + 1 = 4 * n by omega]),
        length_bottomWall, show σ + 1 = 4 * n by omega, Nat.sub_self, hrest, hσl,
        mR_last (by omega)]

end ArtGallery.Sec5

end
