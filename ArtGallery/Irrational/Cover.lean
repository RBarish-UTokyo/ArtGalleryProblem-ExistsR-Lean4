module

public import ArtGallery.Irrational.Sees

/-!
# Guards that see all of `𝒫`

Guards on the three lines `l_ℓ : x = 2`, `l_m : y = 0.3 x - 1.05`, `l_r : x = 19`:
`gL h = (2, h)`, `gM x = (x, 0.3 x - 1.05)`, `gR k = (19, k)`.

`cover`: if `h ∈ [0.5, 0.6]`, `k ∈ [1.7, 1.8]`, `x₁, x₂ ∈ [10.5, 10.6]` and

* (A) `x₁ (50 - 14 h) ≤ 535 - 159 h`, (B) `2 x₁ (1 - h) ≤ 3 h + 7` (`gL h` and `gM x₁` together see
  the left quadrilateral pockets `P_t^ℓ`, `P_b^ℓ`),
* (C) `490 k - 243 ≤ x₂ (20 k + 22)`, (D) `34 k - 7 ≤ x₂ (4 k - 2)` (`gM x₂` and `gR k` together
  see the right quadrilateral pockets `P_t^r`, `P_b^r`),

then every point of `𝒫` is seen by one of `gL h, gM x₁, gM x₂, gR k`.  For a quadrilateral pocket,
a point unseen by both guards would lie strictly above two lines and below the non-axis-parallel
edge of the pocket; an explicit nonnegative combination of the three constraints (a Farkas
certificate, polynomial in the guard parameters) shows that this is impossible under (A)–(D).
These conditions are (A)–(D) of the paper's Lemmas 11 and 12 (see `Lower.lean`): (A) and (B)
are `x ≤ (28355 - 8427 h)/(2650 - 742 h)` and `x (1 - h) ≤ (81 h + 189)/54`.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set

/-- A guard on `l_ℓ : x = 2`. -/
def gL (h : ℝ) : Point := (2, h)

/-- A guard on `l_m : y = 0.3 x - 1.05`. -/
noncomputable def gM (x : ℝ) : Point := (x, 3 / 10 * x - 21 / 20)

/-- A guard on `l_r : x = 19`. -/
def gR (k : ℝ) : Point := (19, k)

theorem mem_pieces_B : cB ∈ pieces := by simp [pieces]

theorem B_subset_U : hp cB ⊆ U := hp_subset_U mem_pieces_B

theorem gL_mem_B {h : ℝ} (hh : 0 ≤ h ∧ h ≤ 4) : gL h ∈ hp cB := by
  simp only [gL]; piece_goal <;> linarith [hh.1, hh.2]

theorem gM_mem_B {x : ℝ} (hx : 7 / 2 ≤ x ∧ x ≤ 101 / 6) : gM x ∈ hp cB := by
  simp only [gM]; piece_goal <;> linarith [hx.1, hx.2]

theorem gR_mem_B {k : ℝ} (hk : 0 ≤ k ∧ k ≤ 4) : gR k ∈ hp cB := by
  simp only [gR]; piece_goal <;> linarith [hk.1, hk.2]

/-! ### Triangular and rectangular pockets -/

theorem sees_Tbl {h : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) {p : Point} (hp' : p ∈ hp cTbl) :
    P.Sees (gL h) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hh
  refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
    (hp_subset_U (by simp [pieces])) B_subset_U hp' (gL_mem_B ⟨by linarith, by linarith⟩)
    (yo := 0) (a := 19 / 10) (b := 2) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gL]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ h by linarith) c3,
      mul_nonneg (show (0 : ℝ) ≤ -p.2 by linarith) (show (0 : ℝ) ≤ h by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ h by linarith) c2]

theorem sees_Tbr {k : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) {p : Point} (hp' : p ∈ hp cTbr) :
    P.Sees (gR k) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hk
  refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
    (hp_subset_U (by simp [pieces])) B_subset_U hp' (gR_mem_B ⟨by linarith, by linarith⟩)
    (yo := 0) (a := 189 / 10) (b := 19) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gR]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by linarith) c3,
      mul_nonneg (show (0 : ℝ) ≤ -p.2 by linarith) (show (0 : ℝ) ≤ k by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by linarith) c2]

theorem sees_Tbm {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) {p : Point} (hp' : p ∈ hp cTbm) :
    P.Sees (gM x) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hx
  refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
    (hp_subset_U (by simp [pieces])) B_subset_U hp' (gM_mem_B ⟨by linarith, by linarith⟩)
    (yo := 0) (a := 3) (b := 7 / 2) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gM]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 / 10 * x - 21 / 20 by linarith)
      (show (0 : ℝ) ≤ p.1 - 3 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ -p.2 by linarith) (show (0 : ℝ) ≤ x - 3 by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 7 / 2 by linarith) c3]

theorem sees_Ttl {h : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) {p : Point} (hp' : p ∈ hp cTtl) :
    P.Sees (gL h) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hh
  refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
    (hp_subset_U (by simp [pieces])) (gL_mem_B ⟨by linarith, by linarith⟩) hp'
    (yo := 4) (a := 2) (b := 21 / 10) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gL]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 - h by linarith) (show (0 : ℝ) ≤ p.1 - 2 by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 - h by linarith) c3,
      mul_nonneg (show (0 : ℝ) ≤ p.2 - 4 by linarith) (show (0 : ℝ) ≤ 9 / 10 - h / 5 by linarith)]

theorem sees_Ttr {k : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) {p : Point} (hp' : p ∈ hp cTtr) :
    P.Sees (gR k) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hk
  refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
    (hp_subset_U (by simp [pieces])) (gR_mem_B ⟨by linarith, by linarith⟩) hp'
    (yo := 4) (a := 19) (b := 191 / 10) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gR]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 - k by linarith) (show (0 : ℝ) ≤ p.1 - 19 by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 - k by linarith) c3,
      mul_nonneg (show (0 : ℝ) ≤ p.2 - 4 by linarith) (show (0 : ℝ) ≤ 9 / 10 - k / 5 by linarith)]

theorem sees_Ttm {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) {p : Point} (hp' : p ∈ hp cTtm) :
    P.Sees (gM x) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3⟩ := hq
  obtain ⟨h1, h2⟩ := hx
  refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
    (hp_subset_U (by simp [pieces])) (gM_mem_B ⟨by linarith, by linarith⟩) hp'
    (yo := 4) (a := 101 / 6) (b := 52 / 3) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gM]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 101 / 6 - x by linarith) c3]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 52 / 3 - x by linarith)
      (show (0 : ℝ) ≤ p.2 - 4 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 52 / 3 - p.1 by linarith)
        (show (0 : ℝ) ≤ 4 - (3 / 10 * x - 21 / 20) by linarith)]

theorem sees_Rm {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) {p : Point} (hp' : p ∈ hp cRm) :
    P.Sees (gM x) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨h1, h2⟩ := hx
  refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
    (hp_subset_U (by simp [pieces])) (gM_mem_B ⟨by linarith, by linarith⟩) hp'
    (yo := 4) (a := 21 / 2) (b := 53 / 5) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gM]
  · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 21 / 2 by linarith)
      (show (0 : ℝ) ≤ p.2 - 4 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ p.1 - 21 / 2 by linarith)
        (show (0 : ℝ) ≤ 4 - (3 / 10 * x - 21 / 20) by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 53 / 5 - x by linarith)
      (show (0 : ℝ) ≤ p.2 - 4 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 53 / 5 - p.1 by linarith)
        (show (0 : ℝ) ≤ 4 - (3 / 10 * x - 21 / 20) by linarith)]

theorem sees_Rl {k : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) {p : Point} (hp' : p ∈ hp cRl) :
    P.Sees (gR k) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨h1, h2⟩ := hk
  refine sees_symm (sees_through_vertical (convex_hp _) (convex_hp _)
    (hp_subset_U (by simp [pieces])) B_subset_U hp' (gR_mem_B ⟨by linarith, by linarith⟩)
    (xo := 0) (a := 17 / 10) (b := 9 / 5) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gR]
  · intro y hy1 hy2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ -p.1 by linarith) (show (0 : ℝ) ≤ k - 17 / 10 by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ -p.1 by linarith) (show (0 : ℝ) ≤ 9 / 5 - k by linarith)]

theorem sees_Rr {h : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) {p : Point} (hp' : p ∈ hp cRr) :
    P.Sees (gL h) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨h1, h2⟩ := hh
  refine sees_through_vertical (convex_hp _) (convex_hp _) B_subset_U
    (hp_subset_U (by simp [pieces])) (gL_mem_B ⟨by linarith, by linarith⟩) hp'
    (xo := 20) (a := 1 / 2) (b := 3 / 5) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gL]
  · intro y hy1 hy2; constructor <;> piece_goal <;> linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.1 - 20 by linarith) (show (0 : ℝ) ≤ h - 1 / 2 by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.1 - 20 by linarith) (show (0 : ℝ) ≤ 3 / 5 - h by linarith)]

/-! ### Quadrilateral pockets -/

theorem sees_Ptl {h x : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hA : x * (50 - 14 * h) ≤ 535 - 159 * h) {p : Point} (hp' : p ∈ hp cPtl) :
    P.Sees (gL h) p ∨ P.Sees (gM x) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨h1, h2⟩ := hh; obtain ⟨x1, x2⟩ := hx
  by_cases hL : 4 * (p.2 - h) ≤ 2 * (p.2 - 4) + p.1 * (4 - h)
  · left
    refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
      (hp_subset_U (by simp [pieces])) (gL_mem_B ⟨by linarith, by linarith⟩) hp'
      (yo := 4) (a := 4) (b := 8) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gL]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · exact hL
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 - p.1 by linarith) (show (0 : ℝ) ≤ 4 - h by linarith)]
  · right
    push Not at hL
    refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
      (hp_subset_U (by simp [pieces])) (gM_mem_B ⟨by linarith, by linarith⟩) hp'
      (yo := 4) (a := 4) (b := 8) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gM]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 4 by linarith) (show (0 : ℝ) ≤ p.2 - 4 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ p.1 - 4 by linarith)
          (show (0 : ℝ) ≤ 4 - (3 / 10 * x - 21 / 20) by linarith)]
    · by_contra hM
      push Not at hM
      have key : 53 * (79 - 4 * x) * (4 * (p.2 - h) - (2 * (p.2 - 4) + p.1 * (4 - h))) +
          20 * (181 - 47 * h) * ((x * (p.2 - 4) + p.1 * (4 - (3 / 10 * x - 21 / 20))) -
            8 * (p.2 - (3 / 10 * x - 21 / 20))) +
          (-10 * h * x + 80 * h + 34 * x - 219) * (7 * p.1 - 94 * p.2 + 532) =
          -212 * (14 * h * x - 159 * h - 50 * x + 535) := by ring
      have m1 : 0 < 53 * (79 - 4 * x) := by linarith
      have m2 : 0 < 20 * (181 - 47 * h) := by linarith
      have m3 : 0 ≤ -10 * h * x + 80 * h + 34 * x - 219 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 21 / 2 by linarith)
          (show (0 : ℝ) ≤ 3 / 5 - h by linarith)]
      have hK : 0 ≤ 14 * h * x - 159 * h - 50 * x + 535 := by nlinarith
      nlinarith [mul_pos m1 (sub_pos.2 hL), mul_pos m2 (sub_pos.2 hM),
        mul_nonneg m3 (show (0 : ℝ) ≤ 7 * p.1 - 94 * p.2 + 532 by linarith)]

theorem sees_Pbl {h x : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hB : 2 * x * (1 - h) ≤ 3 * h + 7) {p : Point} (hp' : p ∈ hp cPbl) :
    P.Sees (gL h) p ∨ P.Sees (gM x) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨h1, h2⟩ := hh; obtain ⟨x1, x2⟩ := hx
  by_cases hL : 4 * (h - p.2) ≤ p.1 * (h - 0) + 2 * (0 - p.2)
  · left
    refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
      (hp_subset_U (by simp [pieces])) B_subset_U hp' (gL_mem_B ⟨by linarith, by linarith⟩)
      (yo := 0) (a := 4) (b := 8) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gL]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · exact hL
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 - p.1 by linarith) (show (0 : ℝ) ≤ h by linarith)]
  · right
    push Not at hL
    refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
      (hp_subset_U (by simp [pieces])) B_subset_U hp' (gM_mem_B ⟨by linarith, by linarith⟩)
      (yo := 0) (a := 4) (b := 8) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gM]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 4 by linarith) (show (0 : ℝ) ≤ -p.2 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ p.1 - 4 by linarith)
          (show (0 : ℝ) ≤ 3 / 10 * x - 21 / 20 by linarith)]
    · by_contra hM
      push Not at hM
      have key : 9 * (16 * x - 71) * (4 * (h - p.2) - (p.1 * (h - 0) + 2 * (0 - p.2))) +
          20 * (19 * h - 3) * ((p.1 * ((3 / 10 * x - 21 / 20) - 0) + x * (0 - p.2)) -
            8 * ((3 / 10 * x - 21 / 20) - p.2)) +
          (10 * h * x - 80 * h + 6 * x - 21) * (3 * p.1 + 38 * p.2 + 12) =
          -108 * (2 * h * x + 3 * h - 2 * x + 7) := by ring
      have m1 : 0 < 9 * (16 * x - 71) := by linarith
      have m2 : 0 < 20 * (19 * h - 3) := by linarith
      have m3 : 0 ≤ 10 * h * x - 80 * h + 6 * x - 21 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 21 / 2 by linarith)
          (show (0 : ℝ) ≤ h - 1 / 2 by linarith)]
      have hK : 0 ≤ 2 * h * x + 3 * h - 2 * x + 7 := by nlinarith
      nlinarith [mul_pos m1 (sub_pos.2 hL), mul_pos m2 (sub_pos.2 hM),
        mul_nonneg m3 (show (0 : ℝ) ≤ 3 * p.1 + 38 * p.2 + 12 by linarith)]

theorem sees_Ptr {k x : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hC : 490 * k - 243 ≤ x * (20 * k + 22)) {p : Point} (hp' : p ∈ hp cPtr) :
    P.Sees (gM x) p ∨ P.Sees (gR k) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨k1, k2⟩ := hk; obtain ⟨x1, x2⟩ := hx
  by_cases hM : 12 * (p.2 - (3 / 10 * x - 21 / 20)) ≤
      x * (p.2 - 4) + p.1 * (4 - (3 / 10 * x - 21 / 20))
  · left
    refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
      (hp_subset_U (by simp [pieces])) (gM_mem_B ⟨by linarith, by linarith⟩) hp'
      (yo := 4) (a := 12) (b := 16) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gM]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · exact hM
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 - x by linarith) (show (0 : ℝ) ≤ p.2 - 4 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ 16 - p.1 by linarith)
          (show (0 : ℝ) ≤ 4 - (3 / 10 * x - 21 / 20) by linarith)]
  · right
    push Not at hM
    refine sees_through_horizontal (convex_hp _) (convex_hp _) B_subset_U
      (hp_subset_U (by simp [pieces])) (gR_mem_B ⟨by linarith, by linarith⟩) hp'
      (yo := 4) (a := 12) (b := 16) ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [gR]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.1 - 12 by linarith) (show (0 : ℝ) ≤ 4 - k by linarith)]
    · by_contra hR
      push Not at hR
      have key : 1450 * (111 - 8 * x) * ((19 * (p.2 - 4) + p.1 * (4 - k)) - 16 * (p.2 - k)) +
          300 * (129 - 50 * k) * (12 * (p.2 - (3 / 10 * x - 21 / 20)) -
            (x * (p.2 - 4) + p.1 * (4 - (3 / 10 * x - 21 / 20)))) +
          (20 * k * x - 240 * k - 98 * x + 1263) * (-355 * p.1 - 750 * p.2 + 9232) =
          -348 * (20 * k * x - 490 * k + 22 * x + 243) := by ring
      have m1 : 0 < 1450 * (111 - 8 * x) := by linarith
      have m2 : 0 < 300 * (129 - 50 * k) := by linarith
      have m3 : 0 ≤ 20 * k * x - 240 * k - 98 * x + 1263 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 53 / 5 - x by linarith)
          (show (0 : ℝ) ≤ k - 17 / 10 by linarith)]
      have hK : 0 ≤ 20 * k * x - 490 * k + 22 * x + 243 := by nlinarith
      nlinarith [mul_pos m1 (sub_pos.2 hR), mul_pos m2 (sub_pos.2 hM),
        mul_nonneg m3 (show (0 : ℝ) ≤ -355 * p.1 - 750 * p.2 + 9232 by linarith)]

theorem sees_Pbr {k x : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hD : 34 * k - 7 ≤ x * (4 * k - 2)) {p : Point} (hp' : p ∈ hp cPbr) :
    P.Sees (gM x) p ∨ P.Sees (gR k) p := by
  have hq := hp'; piece_simp at hq; obtain ⟨c1, c2, c3, c4⟩ := hq
  obtain ⟨k1, k2⟩ := hk; obtain ⟨x1, x2⟩ := hx
  by_cases hM : 12 * ((3 / 10 * x - 21 / 20) - p.2) ≤
      p.1 * ((3 / 10 * x - 21 / 20) - 0) + x * (0 - p.2)
  · left
    refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
      (hp_subset_U (by simp [pieces])) B_subset_U hp' (gM_mem_B ⟨by linarith, by linarith⟩)
      (yo := 0) (a := 12) (b := 16) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gM]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · exact hM
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 - x by linarith) (show (0 : ℝ) ≤ -p.2 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ 16 - p.1 by linarith)
          (show (0 : ℝ) ≤ 3 / 10 * x - 21 / 20 by linarith)]
  · right
    push Not at hM
    refine sees_symm (sees_through_horizontal (convex_hp _) (convex_hp _)
      (hp_subset_U (by simp [pieces])) B_subset_U hp' (gR_mem_B ⟨by linarith, by linarith⟩)
      (yo := 0) (a := 12) (b := 16) ?_ ?_ ?_ ?_ ?_ ?_) <;> try simp only [gR]
    · intro x hx1 hx2; constructor <;> piece_goal <;> linarith
    · linarith
    · linarith
    · linarith
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.1 - 12 by linarith) (show (0 : ℝ) ≤ k by linarith)]
    · by_contra hR
      push Not at hR
      have key : 34 * (8 * x - 33) * ((p.1 * (k - 0) + 19 * (0 - p.2)) - 16 * (k - p.2)) +
          60 * (14 * k + 1) * (12 * ((3 / 10 * x - 21 / 20) - p.2) -
            (p.1 * ((3 / 10 * x - 21 / 20) - 0) + x * (0 - p.2))) +
          (-(20 * k * x - 240 * k - 18 * x + 63)) * (p.1 + 42 * p.2 + 56) =
          -612 * (4 * k * x - 34 * k - 2 * x + 7) := by ring
      have m1 : 0 < 34 * (8 * x - 33) := by linarith
      have m2 : 0 < 60 * (14 * k + 1) := by linarith
      have m3 : 0 ≤ -(20 * k * x - 240 * k - 18 * x + 63) := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 53 / 5 - x by linarith)
          (show (0 : ℝ) ≤ k - 17 / 10 by linarith)]
      have hK : 0 ≤ 4 * k * x - 34 * k - 2 * x + 7 := by nlinarith
      nlinarith [mul_pos m1 (sub_pos.2 hR), mul_pos m2 (sub_pos.2 hM),
        mul_nonneg m3 (show (0 : ℝ) ≤ p.1 + 42 * p.2 + 56 by linarith)]

/-! ### The coverage theorem -/

/-- **Coverage.** Under (A)–(D), the guards `gL h, gM x₁, gM x₂, gR k` see all of `𝒫`. -/
theorem cover {h x₁ x₂ k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5)
    (hx₁ : 21 / 2 ≤ x₁ ∧ x₁ ≤ 53 / 5) (hx₂ : 21 / 2 ≤ x₂ ∧ x₂ ≤ 53 / 5)
    (hA : x₁ * (50 - 14 * h) ≤ 535 - 159 * h) (hB : 2 * x₁ * (1 - h) ≤ 3 * h + 7)
    (hC : 490 * k - 243 ≤ x₂ * (20 * k + 22)) (hD : 34 * k - 7 ≤ x₂ * (4 * k - 2))
    {p : Point} (hp' : p ∈ P.filled) :
    P.Sees (gL h) p ∨ P.Sees (gM x₁) p ∨ P.Sees (gM x₂) p ∨ P.Sees (gR k) p := by
  rw [filled_eq_U] at hp'
  rcases mem_U_iff.1 hp' with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  · exact Or.inl (sees_of_convex (convex_hp _) B_subset_U
      (gL_mem_B ⟨by linarith [hh.1], by linarith [hh.2]⟩) h')
  · exact Or.inl (sees_Tbl hh h')
  · exact Or.inr (Or.inl (sees_Tbm hx₁ h'))
  · rcases sees_Pbl hh hx₁ hB h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · rcases sees_Pbr hk hx₂ hD h' with h'' | h''
    · exact Or.inr (Or.inr (Or.inl h''))
    · exact Or.inr (Or.inr (Or.inr h''))
  · exact Or.inr (Or.inr (Or.inr (sees_Tbr hk h')))
  · exact Or.inl (sees_Ttl hh h')
  · exact Or.inr (Or.inl (sees_Ttm hx₁ h'))
  · exact Or.inr (Or.inr (Or.inr (sees_Ttr hk h')))
  · rcases sees_Ptl hh hx₁ hA h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · rcases sees_Ptr hk hx₂ hC h' with h'' | h''
    · exact Or.inr (Or.inr (Or.inl h''))
    · exact Or.inr (Or.inr (Or.inr h''))
  · exact Or.inr (Or.inl (sees_Rm hx₁ h'))
  · exact Or.inr (Or.inr (Or.inr (sees_Rl hk h')))
  · exact Or.inl (sees_Rr hh h')

end

end ArtGallery.Irrational
