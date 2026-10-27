module

public import ArtGallery.Irrational.Lower
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The quadrilateral pockets force irrational guards (Lemmas 7, 8, 10, 11, 12)

Let the three guards be `gL h = (2, h)`, `gM x = (x, 0.3 x - 1.05)` and `gR k = (19, k)` with
`h ∈ [0.5, 0.6]`, `x ∈ [10.5, 10.6]`, `k ∈ [1.7, 1.8]` (`guard_ranges`), and suppose that they
see all of `𝒫`.

For each of the four non-axis-parallel edges `e_t^ℓ, e_b^ℓ, e_t^r, e_b^r` (parametrised by the
abscissa: `eTL`, `eBL`, `eTR`, `eBR`) we exhibit an open interval of points that neither `gL h`
nor `gR k` sees (proper crossings with vertical edges of the pockets; these are the computations
of Lemmas 7, 8 and 10).  So `gM x` sees all of them, hence (the seen set being closed) the
endpoint `s₀` of the interval, which is the last point seen by `gL h` (for the left pockets) or
by `gR k` (for the right pockets).  This forces (`condA` … `condD`)

* (A) `x (50 - 14 h) ≤ 535 - 159 h`   (paper: `x ≤ (28355 - 8427 h)/(2650 - 742 h)`),
* (B) `2 x (1 - h) ≤ 3 h + 7`          (paper: `x (1 - h) ≤ (81 h + 189)/54`),
* (C) `490 k - 243 ≤ x (20 k + 22)`,
* (D) `34 k - 7 ≤ x (4 k - 2)`.

(A), (B) and `x ≥ 3.5 + 5√2` force `h = 2 - √2`; (C), (D) and `x ≤ 3.5 + 5√2` force
`k = 1 + √2/2` (Lemmas 11 and 12).  Hence `h` or `k` is irrational (`irrational_of_ABCD`).

Remark: unlike the paper (Lemma 10, "if three guards together see one of these edges, then two
do as well"), the argument uses explicit intervals.  Note that `gR k` may see a short piece of
`e_b^ℓ` near its left endpoint (up to the abscissa `(304 k - 132)/(38 k + 33) ≤ 2076/507`, as in
the paper), so the interval used for `e_b^ℓ` starts at `4.1`.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set

/-- The edge `e_t^ℓ` of `P_t^ℓ`, parametrised by the abscissa. -/
noncomputable def eTL (s : ℝ) : Point := (s, 7 / 94 * s + 266 / 47)
/-- The edge `e_b^ℓ` of `P_b^ℓ`, parametrised by the abscissa. -/
noncomputable def eBL (s : ℝ) : Point := (s, -3 / 38 * s - 6 / 19)
/-- The edge `e_t^r` of `P_t^r`, parametrised by the abscissa. -/
noncomputable def eTR (s : ℝ) : Point := (s, -71 / 150 * s + 4616 / 375)
/-- The edge `e_b^r` of `P_b^r`, parametrised by the abscissa. -/
noncomputable def eBR (s : ℝ) : Point := (s, -1 / 42 * s - 4 / 3)

theorem eTL_mem {s : ℝ} (h1 : 4 ≤ s) (h2 : s ≤ 8) : eTL s ∈ P.filled :=
  mem_filled_of_edge (i := 39) (by norm_num) vtx39 vtx40 (t := (8 - s) / 4) (by linarith)
    (by linarith) (by simp only [eTL, Prod.mk.injEq]; constructor <;> ring)

theorem eBL_mem {s : ℝ} (h1 : 4 ≤ s) (h2 : s ≤ 8) : eBL s ∈ P.filled :=
  mem_filled_of_edge (i := 8) (by norm_num) vtx8 vtx9 (t := (s - 4) / 4) (by linarith)
    (by linarith) (by simp only [eBL, Prod.mk.injEq]; constructor <;> ring)

theorem eTR_mem {s : ℝ} (h1 : 12 ≤ s) (h2 : s ≤ 16) : eTR s ∈ P.filled :=
  mem_filled_of_edge (i := 31) (by norm_num) vtx31 vtx32 (t := (16 - s) / 4) (by linarith)
    (by linarith) (by simp only [eTR, Prod.mk.injEq]; constructor <;> ring)

theorem eBR_mem {s : ℝ} (h1 : 12 ≤ s) (h2 : s ≤ 16) : eBR s ∈ P.filled :=
  mem_filled_of_edge (i := 12) (by norm_num) vtx12 vtx13 (t := (s - 12) / 4) (by linarith)
    (by linarith) (by simp only [eBR, Prod.mk.injEq]; constructor <;> ring)

/-! ### Who sees which part of the four edges -/

theorem nAl {h s : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hs : 4 < s)
    (hs0 : (181 - 47 * h) * s < 908 - 188 * h) : ¬ P.Sees (gL h) (eTL s) := by
  refine block_v (i := 40) (by norm_num) vtx40 vtx41 (by simp only [gL]; norm_num)
    (by simp only [eTL]; linarith) ?_
  right; simp only [gL, eTL]
  constructor
  · nlinarith
  · nlinarith [mul_pos (show (0 : ℝ) < 273 - 47 * h by linarith) (show (0 : ℝ) < s - 4 by linarith)]

theorem nAr {k s : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hs : 4 < s) (hs' : s < 8) :
    ¬ P.Sees (eTL s) (gR k) := by
  refine block_v (i := 38) (by norm_num) vtx38 vtx39 (by simp only [eTL]; linarith)
    (by simp only [gR]; norm_num) ?_
  left; simp only [gR, eTL]
  constructor
  · nlinarith [mul_neg_of_neg_of_pos (show 94 * k - 453 < 0 by linarith)
      (show (0 : ℝ) < s - 4 by linarith)]
  · nlinarith [mul_pos_of_neg_of_neg (show 94 * k - 665 < 0 by linarith)
      (show s - 8 < 0 by linarith)]

theorem nAm {h x s₀ : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hrel : (181 - 47 * h) * s₀ = 908 - 188 * h) (hs : s₀ < 8)
    (hnA : 535 - 159 * h < x * (50 - 14 * h)) : ¬ P.Sees (eTL s₀) (gM x) := by
  refine block_v (i := 38) (by norm_num) vtx38 vtx39 (by simp only [eTL]; linarith)
    (by simp only [gM]; linarith [hx.1]) ?_
  left; simp only [gM, eTL]
  have key : (181 - 47 * h) * (((7 / 94 * s₀ + 266 / 47) * (x - s₀) + (8 - s₀) *
      ((3 / 10 * x - 21 / 20) - (7 / 94 * s₀ + 266 / 47))) - 4 * (x - s₀)) =
      -53 / 5 * (14 * h * x - 159 * h - 50 * x + 535) := by
    linear_combination (-53 * (4 * x - 79) / 940) * hrel
  have hE : 0 < ((7 / 94 * s₀ + 266 / 47) * (x - s₀) + (8 - s₀) *
      ((3 / 10 * x - 21 / 20) - (7 / 94 * s₀ + 266 / 47))) - 4 * (x - s₀) := by
    by_contra hc; push Not at hc
    have : (181 - 47 * h) * (((7 / 94 * s₀ + 266 / 47) * (x - s₀) + (8 - s₀) *
        ((3 / 10 * x - 21 / 20) - (7 / 94 * s₀ + 266 / 47))) - 4 * (x - s₀)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    nlinarith
  constructor
  · linarith
  · nlinarith [mul_pos_of_neg_of_neg (show s₀ - 8 < 0 by linarith)
      (show 4 * x - 119 < 0 by linarith)]

theorem nBl {h s : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hs : 4 < s)
    (hs0 : (19 * h - 3) * s < 76 * h + 12) : ¬ P.Sees (gL h) (eBL s) := by
  refine block_v (i := 7) (by norm_num) vtx7 vtx8 (by simp only [gL]; norm_num)
    (by simp only [eBL]; linarith) ?_
  right; simp only [gL, eBL]
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < 19 * h + 9 by linarith) (show (0 : ℝ) < s - 4 by linarith)]
  · nlinarith

theorem nBr {k s : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hs : 41 / 10 < s) (hs' : s < 8) :
    ¬ P.Sees (eBL s) (gR k) := by
  refine block_v (i := 9) (by norm_num) vtx9 vtx10 (by simp only [eBL]; linarith)
    (by simp only [gR]; norm_num) ?_
  left; simp only [gR, eBL]
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < 38 * k + 69 by linarith) (show (0 : ℝ) < 8 - s by linarith)]
  · nlinarith [mul_pos (show (0 : ℝ) < 38 * k + 33 by linarith)
      (show (0 : ℝ) < s - 41 / 10 by linarith)]

theorem nBm {h x s₀ : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hrel : (19 * h - 3) * s₀ = 76 * h + 12) (hs : s₀ < 8)
    (hnB : 3 * h + 7 < 2 * x * (1 - h)) : ¬ P.Sees (eBL s₀) (gM x) := by
  refine block_v (i := 9) (by norm_num) vtx9 vtx10 (by simp only [eBL]; linarith)
    (by simp only [gM]; linarith [hx.1]) ?_
  left; simp only [gM, eBL]
  have key : (19 * h - 3) * (-((-3 / 38 * s₀ - 6 / 19) * (x - s₀) + (8 - s₀) *
      ((3 / 10 * x - 21 / 20) - (-3 / 38 * s₀ - 6 / 19)))) =
      -27 / 5 * (2 * h * x + 3 * h - 2 * x + 7) := by
    linear_combination (9 * (16 * x - 71) / 380) * hrel
  have hE : 0 < -((-3 / 38 * s₀ - 6 / 19) * (x - s₀) + (8 - s₀) *
      ((3 / 10 * x - 21 / 20) - (-3 / 38 * s₀ - 6 / 19))) := by
    by_contra hc; push Not at hc
    have : (19 * h - 3) * (-((-3 / 38 * s₀ - 6 / 19) * (x - s₀) + (8 - s₀) *
        ((3 / 10 * x - 21 / 20) - (-3 / 38 * s₀ - 6 / 19)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    nlinarith
  constructor
  · nlinarith [mul_pos_of_neg_of_neg (show s₀ - 8 < 0 by linarith)
      (show 31 - 16 * x < 0 by linarith)]
  · linarith

theorem nCr {k s s₀ : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5)
    (hrel : (645 - 250 * k) * s₀ = 9768 - 4000 * k) (hs : s₀ < s) (hs' : s < 16) :
    ¬ P.Sees (eTR s) (gR k) := by
  refine block_v (i := 30) (by norm_num) vtx30 vtx31 (by simp only [eTR]; linarith)
    (by simp only [gR]; norm_num) ?_
  left; simp only [gR, eTR]
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < 645 - 250 * k by linarith) (show (0 : ℝ) < s - s₀ by linarith)]
  · nlinarith [mul_pos_of_neg_of_neg (show 250 * k - 829 < 0 by linarith)
      (show s - 16 < 0 by linarith)]

theorem nCl {h s : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hs : 12 < s) (hs' : s < 14) :
    ¬ P.Sees (gL h) (eTR s) := by
  refine block_v (i := 32) (by norm_num) vtx32 vtx33 (by simp only [gL]; norm_num)
    (by simp only [eTR]; linarith) ?_
  right; simp only [gL, eTR]
  constructor
  · nlinarith [mul_pos_of_neg_of_neg (show 75 * h - 655 < 0 by linarith)
      (show s - 14 < 0 by linarith)]
  · nlinarith [mul_pos (show (0 : ℝ) < 4261 - 375 * h by linarith) (show (0 : ℝ) < s - 12 by linarith)]

theorem nCm {k x s₀ : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hrel : (645 - 250 * k) * s₀ = 9768 - 4000 * k) (hs : 12 < s₀)
    (hnC : x * (20 * k + 22) < 490 * k - 243) : ¬ P.Sees (gM x) (eTR s₀) := by
  refine block_v (i := 32) (by norm_num) vtx32 vtx33 (by simp only [gM]; linarith [hx.2])
    (by simp only [eTR]; linarith) ?_
  right; simp only [gM, eTR]
  have key : (645 - 250 * k) * (((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
      ((-71 / 150 * s₀ + 4616 / 375) - (3 / 10 * x - 21 / 20))) - 4 * (s₀ - x)) =
      -29 / 5 * (20 * k * x - 490 * k + 22 * x + 243) := by
    linear_combination (29 * (8 * x - 111) / 300) * hrel
  have hE : 0 < ((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
      ((-71 / 150 * s₀ + 4616 / 375) - (3 / 10 * x - 21 / 20))) - 4 * (s₀ - x) := by
    by_contra hc; push Not at hc
    have : (645 - 250 * k) * (((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
        ((-71 / 150 * s₀ + 4616 / 375) - (3 / 10 * x - 21 / 20))) - 4 * (s₀ - x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    nlinarith
  constructor
  · linarith
  · nlinarith [mul_pos (show (0 : ℝ) < s₀ - 12 by linarith) (show (0 : ℝ) < 691 - 40 * x by linarith)]

theorem nDr {k s s₀ : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5)
    (hrel : (14 * k + 1) * s₀ = 224 * k - 56) (hs : s₀ < s) (hs' : s < 16) :
    ¬ P.Sees (eBR s) (gR k) := by
  refine block_v (i := 13) (by norm_num) vtx13 vtx14 (by simp only [eBR]; linarith)
    (by simp only [gR]; norm_num) ?_
  left; simp only [gR, eBR]
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < 14 * k + 25 by linarith) (show (0 : ℝ) < 16 - s by linarith)]
  · nlinarith [mul_pos (show (0 : ℝ) < 14 * k + 1 by linarith) (show (0 : ℝ) < s - s₀ by linarith)]

theorem nDl {h s : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hs : 12 < s) (hs' : s < 16) :
    ¬ P.Sees (gL h) (eBR s) := by
  refine block_v (i := 11) (by norm_num) vtx11 vtx12 (by simp only [gL]; norm_num)
    (by simp only [eBR]; linarith) ?_
  right; simp only [gL, eBR]
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < 21 * h + 29 by linarith) (show (0 : ℝ) < s - 12 by linarith)]
  · nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < 21 * h - 5 by linarith)
      (show s - 16 < 0 by linarith)]

theorem nDm {k x s₀ : ℝ} (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hrel : (14 * k + 1) * s₀ = 224 * k - 56) (hs : 12 < s₀)
    (hnD : x * (4 * k - 2) < 34 * k - 7) : ¬ P.Sees (gM x) (eBR s₀) := by
  refine block_v (i := 11) (by norm_num) vtx11 vtx12 (by simp only [gM]; linarith [hx.2])
    (by simp only [eBR]; linarith) ?_
  right; simp only [gM, eBR]
  have key : (14 * k + 1) * (-((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
      ((-1 / 42 * s₀ - 4 / 3) - (3 / 10 * x - 21 / 20)))) =
      -51 / 5 * (4 * k * x - 34 * k - 2 * x + 7) := by
    linear_combination (-17 * (8 * x - 33) / 420) * hrel
  have hE : 0 < -((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
      ((-1 / 42 * s₀ - 4 / 3) - (3 / 10 * x - 21 / 20))) := by
    by_contra hc; push Not at hc
    have : (14 * k + 1) * (-((3 / 10 * x - 21 / 20) * (s₀ - x) + (12 - x) *
        ((-1 / 42 * s₀ - 4 / 3) - (3 / 10 * x - 21 / 20)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    nlinarith
  constructor
  · nlinarith [mul_pos (show (0 : ℝ) < s₀ - 12 by linarith) (show (0 : ℝ) < 8 * x + 7 by linarith)]
  · linarith

/-! ### The conditions (A)–(D) -/

/-- Three guards on the three lines that see all of `𝒫`. -/
def SeesAll (h x k : ℝ) : Prop :=
  ∀ q ∈ P.filled, P.Sees (gL h) q ∨ P.Sees (gM x) q ∨ P.Sees (gR k) q

theorem condA {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hall : SeesAll h x k) :
    x * (50 - 14 * h) ≤ 535 - 159 * h := by
  by_contra hnA; push Not at hnA
  have hd : 0 < 181 - 47 * h := by linarith [hh.2]
  set s₀ := (908 - 188 * h) / (181 - 47 * h) with hs₀
  have hrel : (181 - 47 * h) * s₀ = 908 - 188 * h := by rw [hs₀]; field_simp
  have h4 : 4 < s₀ := by nlinarith
  have h8 : s₀ < 8 := by nlinarith
  have hsee : P.Sees (gM x) (eTL s₀) := by
    refine sees_of_limit (f := eTL) (by unfold eTL; fun_prop) h4 ⟨h4.le, le_rfl⟩ ?_
    intro s hs1 hs2
    rcases hall _ (eTL_mem hs1.le (by linarith)) with h' | h' | h'
    · exact absurd h' (nAl hh hs1 (by nlinarith))
    · exact h'
    · exact absurd (sees_symm h') (nAr hk hs1 (by linarith))
  exact nAm hh hx hrel h8 hnA (sees_symm hsee)

theorem condB {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hall : SeesAll h x k) : 2 * x * (1 - h) ≤ 3 * h + 7 := by
  by_contra hnB; push Not at hnB
  have hd : 0 < 19 * h - 3 := by linarith [hh.1]
  set s₀ := (76 * h + 12) / (19 * h - 3) with hs₀
  have hrel : (19 * h - 3) * s₀ = 76 * h + 12 := by rw [hs₀]; field_simp
  have h4 : 41 / 10 < s₀ := by nlinarith
  have h8 : s₀ < 8 := by nlinarith
  have hsee : P.Sees (gM x) (eBL s₀) := by
    refine sees_of_limit (f := eBL) (by unfold eBL; fun_prop) h4 ⟨h4.le, le_rfl⟩ ?_
    intro s hs1 hs2
    rcases hall _ (eBL_mem (by linarith) (by linarith)) with h' | h' | h'
    · exact absurd h' (nBl hh (by linarith) (by nlinarith))
    · exact h'
    · exact absurd (sees_symm h') (nBr hk hs1 (by linarith))
  exact nBm hh hx hrel h8 hnB (sees_symm hsee)

theorem condC {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hall : SeesAll h x k) :
    490 * k - 243 ≤ x * (20 * k + 22) := by
  by_contra hnC; push Not at hnC
  have hd : 0 < 645 - 250 * k := by linarith [hk.2]
  set s₀ := (9768 - 4000 * k) / (645 - 250 * k) with hs₀
  have hrel : (645 - 250 * k) * s₀ = 9768 - 4000 * k := by rw [hs₀]; field_simp
  have h12 : 12 < s₀ := by nlinarith
  have h14 : s₀ < 14 := by nlinarith
  have hsee : P.Sees (gM x) (eTR s₀) := by
    refine sees_of_limit (f := eTR) (by unfold eTR; fun_prop) h14 ⟨le_rfl, h14.le⟩ ?_
    intro s hs1 hs2
    rcases hall _ (eTR_mem (by linarith) (by linarith)) with h' | h' | h'
    · exact absurd h' (nCl hh (by linarith) hs2)
    · exact h'
    · exact absurd (sees_symm h') (nCr hk hrel hs1 (by linarith))
  exact nCm hk hx hrel h12 hnC hsee

theorem condD {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5)
    (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hall : SeesAll h x k) :
    34 * k - 7 ≤ x * (4 * k - 2) := by
  by_contra hnD; push Not at hnD
  have hd : 0 < 14 * k + 1 := by linarith [hk.1]
  set s₀ := (224 * k - 56) / (14 * k + 1) with hs₀
  have hrel : (14 * k + 1) * s₀ = 224 * k - 56 := by rw [hs₀]; field_simp
  have h12 : 12 < s₀ := by nlinarith
  have h16 : s₀ < 16 := by nlinarith
  have hsee : P.Sees (gM x) (eBR s₀) := by
    refine sees_of_limit (f := eBR) (by unfold eBR; fun_prop) h16 ⟨le_rfl, h16.le⟩ ?_
    intro s hs1 hs2
    rcases hall _ (eBR_mem (by linarith) (by linarith)) with h' | h' | h'
    · exact absurd h' (nDl hh (by linarith) hs2)
    · exact h'
    · exact absurd (sees_symm h') (nDr hk hrel hs1 hs2)
  exact nDm hk hx hrel h12 hnD hsee

/-! ### Lemmas 11 and 12: the unique solution is irrational -/

/-- **Lemmas 11 and 12.** Under (A)–(D), `h = 2 - √2` or `k = 1 + √2 / 2`. -/
theorem sqrt_of_ABCD {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5)
    (hA : x * (50 - 14 * h) ≤ 535 - 159 * h) (hB : 2 * x * (1 - h) ≤ 3 * h + 7)
    (hC : 490 * k - 243 ≤ x * (20 * k + 22)) (hD : 34 * k - 7 ≤ x * (4 * k - 2)) :
    h = 2 - √2 ∨ k = 1 + √2 / 2 := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hlo : 1.41 < √2 := by nlinarith
  have hhi : √2 < 1.42 := by nlinarith
  rcases le_total (7 / 2 + 5 * √2) x with hX | hX
  · left
    have e1 : (110 - 70 * √2) * (h - (2 - √2)) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ 50 - 14 * h by linarith)]
    have e2 : 0 ≤ (1 + √2) * (h - (2 - √2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ 2 * (1 - h) by linarith)]
    have f1 : h - (2 - √2) ≤ 0 := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show (0 : ℝ) < 110 - 70 * √2 by linarith) hc]
    have f2 : 0 ≤ h - (2 - √2) := by
      by_contra hc; push Not at hc
      nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < 1 + √2 by linarith) hc]
    linarith
  · right
    have e1 : (420 - 100 * √2) * (k - (1 + √2 / 2)) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ 20 * k + 22 by linarith)]
    have e2 : 0 ≤ (√2 - 1) * (k - (1 + √2 / 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ 4 * k - 2 by linarith)]
    have f1 : k - (1 + √2 / 2) ≤ 0 := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show (0 : ℝ) < 420 - 100 * √2 by linarith) hc]
    have f2 : 0 ≤ k - (1 + √2 / 2) := by
      by_contra hc; push Not at hc
      nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < √2 - 1 by linarith) hc]
    linarith

/-- Under (A)–(D), the heights `h` and `k` are not both rational. -/
theorem irrational_of_ABCD {h x k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5) (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5)
    (hA : x * (50 - 14 * h) ≤ 535 - 159 * h) (hB : 2 * x * (1 - h) ≤ 3 * h + 7)
    (hC : 490 * k - 243 ≤ x * (20 * k + 22)) (hD : 34 * k - 7 ≤ x * (4 * k - 2))
    (qh : ℚ) (hqh : h = qh) (qk : ℚ) (hqk : k = qk) : False := by
  rcases sqrt_of_ABCD hh hk hA hB hC hD with e | e
  · exact irrational_sqrt_two ⟨2 - qh, by push_cast; linarith⟩
  · exact irrational_sqrt_two ⟨2 * qk - 2, by push_cast; linarith⟩

/-- **Every guard set of `𝒫` consisting of rational points has at least four guards.** -/
theorem four_le_card_of_rational {G : Finset Point} (hG : P.IsGuardSet (G : Set Point))
    (hrat : ∀ p ∈ G, IsRationalPoint p) : 4 ≤ G.card := by
  by_contra hc; push Not at hc
  obtain ⟨h, x, k, hall, hLG, hMG, hRG, hh, hx, hk⟩ := guard_ranges hG (by omega)
  have seen : SeesAll h x k := by
    intro q hq
    obtain ⟨g, hg, hs⟩ := hG.2 q hq
    rcases hall g hg with rfl | rfl | rfl
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  obtain ⟨a, b, hab⟩ := hrat _ hLG
  obtain ⟨a', b', hab'⟩ := hrat _ hRG
  simp only [gL, gR, Prod.mk.injEq] at hab hab'
  exact irrational_of_ABCD hh hk (condA hh hx hk seen) (condB hh hx hk seen)
    (condC hh hx hk seen) (condD hh hx hk seen) b hab.2 b' hab'.2

end

end ArtGallery.Irrational
