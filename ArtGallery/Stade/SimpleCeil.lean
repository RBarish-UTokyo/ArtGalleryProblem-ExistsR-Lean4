module

public import ArtGallery.Stade.SimpleFloor

/-!
# Simplicity of Stade's polygon: the ceiling

The ceiling features of `poly n Φ` (wedges of the segment regions and copy nooks) are ceiling
features of the line `y = 2H` inside `x_L < x < x_R` (`ceil_feature`), pairwise disjoint and
ordered from right to left (`ceil_pw`).

Bounds used (for `H ≥ 1000`): the wedges of a segment region at abscissa `s` lie in
`[s − 1, s + 1/2]` (`W1`: `[s, s + 1/4]` or `[s − 1/4, s]`; `W3`: `[s − 1/2, s − 1/5]` or
`[s + 1/5, s + 1/2]`; `W4`: `[s − 3/4, s − 1/3]`; `W5`: `[s − 1, s − 3/8]`); the wedges `W3, W4, W5`
of a variable are separated by the strip lemma `needles_strip`; a copy nook with abscissa
`x_N` lies in `[x_N, x_N + 3]`.
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Fractions -/

theorem frac3_bounds {H : ℚ} (hH : 1000 ≤ H) :
    1 / 5 < (H - 3) / (2 * (2 * H - 3)) ∧ (H - 3) / (2 * (2 * H - 3)) < 1 / 4 := by
  have hd : 0 < 2 * (2 * H - 3) := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

theorem frac4_bounds {H : ℚ} (hH : 1000 ≤ H) :
    1 / 3 < 3 * (H - 1) / (4 * (2 * H - 1)) ∧ 3 * (H - 1) / (4 * (2 * H - 1)) < 3 / 8 := by
  have hd : 0 < 4 * (2 * H - 1) := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

theorem frac5_bounds {H : ℚ} (hH : 1000 ≤ H) :
    3 / 8 < (H - 3) / (2 * H - 3) ∧ (H - 3) / (2 * H - 3) < (H - 1) / (2 * H - 1) ∧
      (H - 1) / (2 * H - 1) < 1 / 2 := by
  have hd1 : 0 < 2 * H - 3 := by linarith
  have hd2 : 0 < 2 * H - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hd1]; linarith
  · rw [div_lt_div_iff₀ hd1 hd2]; nlinarith
  · rw [div_lt_iff₀ hd2]; linarith

/-! ### Wedges -/

/-- The pairwise relation of ceiling features (the first one is to the right). -/
def CeilRel (f g : List (ℚ × ℚ)) : Prop :=
  Disjoint (chainSet (f.map ratPoint)) (chainSet (g.map ratPoint)) ∧
    (fstPt (g.map ratPoint)).1 < (lstPt (f.map ratPoint)).1

section Wedges

variable {H s lo hi : ℚ}

theorem wedgeW1_feature (hH : 1000 ≤ H) (pos : Bool) (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) ((wedgeW1 s pos H).map ratPoint) := by
  cases pos
  · exact needle_ceil (by linarith) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩
  · exact needle_ceil (by linarith) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩

theorem wedgeW3_feature (hH : 1000 ≤ H) (pos : Bool) {T : ℚ} (hT : 2 * H < T)
    (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) ((wedgeW3 s pos T H).map ratPoint) := by
  have := frac3_bounds hH
  cases pos
  · exact needle_ceil (by linarith) hT ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  · exact needle_ceil (by linarith) hT ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

theorem wedgeW4_feature (hH : 1000 ≤ H) (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) ((wedgeW4 s H).map ratPoint) := by
  have := frac4_bounds hH
  exact needle_ceil (by linarith) (by linarith) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩

theorem wedgeW5_feature (hH : 1000 ≤ H) (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) ((wedgeW5 s H).map ratPoint) := by
  have := frac5_bounds hH
  exact needle_ceil (by linarith) (by linarith) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩

theorem wedgeW1_pos_x : ∀ p ∈ wedgeW1 s true H, s ≤ p.1 ∧ p.1 ≤ s + 1 / 4 := by
  intro p hp
  simp only [wedgeW1, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedgeW1_neg_x : ∀ p ∈ wedgeW1 s false H, s - 1 / 4 ≤ p.1 ∧ p.1 ≤ s := by
  intro p hp
  simp only [wedgeW1, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedgeW3_pos_x (hH : 1000 ≤ H) {T : ℚ} :
    ∀ p ∈ wedgeW3 s true T H, s - 1 / 2 ≤ p.1 ∧ p.1 ≤ s - 1 / 5 := by
  have := frac3_bounds hH
  intro p hp
  simp only [wedgeW3, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedgeW3_neg_x (hH : 1000 ≤ H) {T : ℚ} :
    ∀ p ∈ wedgeW3 s false T H, s + 1 / 5 ≤ p.1 ∧ p.1 ≤ s + 1 / 2 := by
  have := frac3_bounds hH
  intro p hp
  simp only [wedgeW3, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedgeW4_x (hH : 1000 ≤ H) : ∀ p ∈ wedgeW4 s H, s - 3 / 4 ≤ p.1 ∧ p.1 ≤ s - 1 / 3 := by
  have := frac4_bounds hH
  intro p hp
  simp only [wedgeW4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedgeW5_x (hH : 1000 ≤ H) : ∀ p ∈ wedgeW5 s H, s - 1 ≤ p.1 ∧ p.1 ≤ s - 3 / 8 := by
  have := frac5_bounds hH
  intro p hp
  simp only [wedgeW5, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

theorem wedge_len_W1 (pos : Bool) : (wedgeW1 s pos H).length = 3 := by cases pos <;> rfl
theorem wedge_len_W3 (pos : Bool) {T : ℚ} : (wedgeW3 s pos T H).length = 3 := by
  cases pos <;> rfl

/-- The features of an input region. -/
theorem inputCeil_feature (hH : 1000 ≤ H) (pos : Bool) (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    ∀ f ∈ inputCeil s pos H, CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) (f.map ratPoint) := by
  intro f hf
  have hT : 2 * H < 4 * H := by linarith
  cases pos <;> simp only [inputCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hf <;> rcases hf with rfl | rfl
  · exact wedgeW3_feature hH false hT hlo hhi
  · exact wedgeW1_feature hH false hlo hhi
  · exact wedgeW1_feature hH true hlo hhi
  · exact wedgeW3_feature hH true hT hlo hhi

theorem inputCeil_x (hH : 1000 ≤ H) (pos : Bool) :
    ∀ f ∈ inputCeil s pos H, ∀ p ∈ f, s - 1 / 2 ≤ p.1 ∧ p.1 ≤ s + 1 / 2 := by
  intro f hf p hp
  cases pos <;> simp only [inputCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hf <;> rcases hf with rfl | rfl
  · have := wedgeW3_neg_x hH p hp; constructor <;> linarith [this.1, this.2]
  · have := wedgeW1_neg_x p hp; constructor <;> linarith [this.1, this.2]
  · have := wedgeW1_pos_x p hp; constructor <;> linarith [this.1, this.2]
  · have := wedgeW3_pos_x hH p hp; constructor <;> linarith [this.1, this.2]

theorem inputCeil_len (pos : Bool) : ∀ f ∈ inputCeil s pos H, 2 ≤ f.length := by
  intro f hf
  cases pos <;> simp only [inputCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hf <;> rcases hf with rfl | rfl <;>
    simp [wedge_len_W1, wedge_len_W3]

theorem inputCeil_pw (hH : 1000 ≤ H) (pos : Bool) : (inputCeil s pos H).Pairwise CeilRel := by
  cases pos
  · show List.Pairwise CeilRel [wedgeW3 s false (4 * H) H, wedgeW1 s false H]
    exact List.pairwise_pair.2 (sep_ceil (U := s) (L := s + 1 / 5)
      (fun p hp => (wedgeW3_neg_x hH p hp).1) (fun q hq => (wedgeW1_neg_x q hq).2) (by linarith)
      (by simp [wedge_len_W3]) (by simp [wedge_len_W1]))
  · show List.Pairwise CeilRel [wedgeW1 s true H, wedgeW3 s true (4 * H) H]
    exact List.pairwise_pair.2 (sep_ceil (U := s - 1 / 5) (L := s)
      (fun p hp => (wedgeW1_pos_x p hp).1) (fun q hq => (wedgeW3_pos_x hH q hq).2) (by linarith)
      (by simp [wedge_len_W1]) (by simp [wedge_len_W3]))

/-- The features of a variable region. -/
theorem varCeil_feature (hH : 1000 ≤ H) (one : Bool) (hlo : lo < s - 1) (hhi : s + 1 < hi) :
    ∀ f ∈ varCeil s one H, CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) (f.map ratPoint) := by
  intro f hf
  have hT : 2 * H < 3 * H := by linarith
  cases one <;> simp only [varCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  · rcases hf with rfl | rfl
    · exact wedgeW1_feature hH true hlo hhi
    · exact wedgeW3_feature hH true hT hlo hhi
  · rcases hf with (rfl | rfl) | rfl | rfl
    · exact wedgeW1_feature hH true hlo hhi
    · exact wedgeW3_feature hH true hT hlo hhi
    · exact wedgeW4_feature hH hlo hhi
    · exact wedgeW5_feature hH hlo hhi

theorem varCeil_x (hH : 1000 ≤ H) (one : Bool) :
    ∀ f ∈ varCeil s one H, ∀ p ∈ f, s - 1 ≤ p.1 ∧ p.1 ≤ s + 1 / 4 := by
  intro f hf p hp
  cases one <;> simp only [varCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  · rcases hf with rfl | rfl
    · have := wedgeW1_pos_x p hp; constructor <;> linarith [this.1, this.2]
    · have := wedgeW3_pos_x hH p hp; constructor <;> linarith [this.1, this.2]
  · rcases hf with (rfl | rfl) | rfl | rfl
    · have := wedgeW1_pos_x p hp; constructor <;> linarith [this.1, this.2]
    · have := wedgeW3_pos_x hH p hp; constructor <;> linarith [this.1, this.2]
    · have := wedgeW4_x hH p hp; constructor <;> linarith [this.1, this.2]
    · have := wedgeW5_x hH p hp; constructor <;> linarith [this.1, this.2]

theorem varCeil_len (one : Bool) : ∀ f ∈ varCeil s one H, 2 ≤ f.length := by
  intro f hf
  cases one <;> simp only [varCeil, Bool.false_eq_true, ite_false, ite_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  · rcases hf with rfl | rfl <;> simp [wedge_len_W1, wedge_len_W3]
  · rcases hf with (rfl | rfl) | rfl | rfl <;> simp [wedge_len_W1, wedge_len_W3, wedgeW4, wedgeW5]

theorem varCeil_pw (hH : 1000 ≤ H) (one : Bool) : (varCeil s one H).Pairwise CeilRel := by
  have h3 := frac3_bounds hH
  have h4 := frac4_bounds hH
  have h5 := frac5_bounds hH
  have hT : 2 * H < 3 * H := by linarith
  have r13 : CeilRel (wedgeW1 s true H) (wedgeW3 s true (3 * H) H) :=
    sep_ceil (U := s - 1 / 5) (L := s) (fun p hp => (wedgeW1_pos_x p hp).1)
      (fun q hq => (wedgeW3_pos_x hH q hq).2) (by linarith) (by simp [wedge_len_W1])
      (by simp [wedge_len_W3])
  cases one
  · show List.Pairwise CeilRel [wedgeW1 s true H, wedgeW3 s true (3 * H) H]
    exact List.pairwise_pair.2 r13
  · have r14 : CeilRel (wedgeW1 s true H) (wedgeW4 s H) :=
      sep_ceil (U := s - 1 / 3) (L := s) (fun p hp => (wedgeW1_pos_x p hp).1)
        (fun q hq => (wedgeW4_x hH q hq).2) (by linarith) (by simp [wedge_len_W1])
        (by simp [wedgeW4])
    have r15 : CeilRel (wedgeW1 s true H) (wedgeW5 s H) :=
      sep_ceil (U := s - 3 / 8) (L := s) (fun p hp => (wedgeW1_pos_x p hp).1)
        (fun q hq => (wedgeW5_x hH q hq).2) (by linarith) (by simp [wedge_len_W1])
        (by simp [wedgeW5])
    have r34 : CeilRel (wedgeW3 s true (3 * H) H) (wedgeW4 s H) :=
      needles_strip hT (by linarith) (by linarith) (by linarith) (by linarith)
    have r35 : CeilRel (wedgeW3 s true (3 * H) H) (wedgeW5 s H) :=
      needles_strip hT (by linarith) (by linarith) (by linarith) (by linarith)
    have r45 : CeilRel (wedgeW4 s H) (wedgeW5 s H) :=
      needles_strip hT (by linarith) (by linarith) (by linarith) (by linarith)
    show List.Pairwise CeilRel
      [wedgeW1 s true H, wedgeW3 s true (3 * H) H, wedgeW4 s H, wedgeW5 s H]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.pairwise_singleton _ _)))
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exacts [r13, r14, r15]
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      exacts [r34, r35]
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact r45

end Wedges

/-! ### Copy nooks -/

section Nooks

variable {a b H : ℚ}

theorem copyE_bounds (ge : Bool) : -16 ≤ copyE ge ∧ copyE ge ≤ 12 := by
  cases ge <;> norm_num [copyE]

/-- The copy nook lies in `[x_N, x_N + 3]` and is a ceiling feature, for `H ≥ 1000` and
`H + 30 ≤ b − a ≤ 2H − 600`. -/
theorem copyNook_feature (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600)
    (ge : Bool) :
    (∀ p ∈ copyNook a b ge H, nookX a b ge ≤ p.1 ∧ p.1 ≤ nookX a b ge + 3) ∧
    ∀ lo hi : ℚ, lo < nookX a b ge → nookX a b ge + 3 < hi →
      CeilFeature ((2 * H : ℚ) : ℝ) (lo : ℝ) (hi : ℝ) ((copyNook a b ge H).map ratPoint) := by
  set xN := nookX a b ge with hxN
  have hxN' : xN = 2 * a - b + copyE ge := rfl
  have he := copyE_bounds ge
  have hd1 : 0 < 2 * H - 1 := by linarith
  have hd2 : 0 < 2 * H - 2 := by linarith
  have hd3 : 0 < 2 * H - 3 := by linarith
  -- the openings relative to `x_N`
  have hPs1 : xN < (xN * (2 * H - 3) + 2 * a) / (2 * H - 1) := by
    rw [lt_div_iff₀ hd1]; nlinarith
  have hPt1 : xN < (xN * (2 * H - 3) + b) / (2 * H - 2) := by
    rw [lt_div_iff₀ hd2]; nlinarith
  have hPs3 : (xN * (2 * H - 3) + 2 * a) / (2 * H - 1) ≤ xN + 3 := by
    rw [div_le_iff₀ hd1]; nlinarith
  have hPt3 : (xN * (2 * H - 3) + b) / (2 * H - 2) ≤ xN + 3 := by
    rw [div_le_iff₀ hd2]; nlinarith
  have hD : (xN * (2 * H - 3) + b) * (2 * H - 1) - (xN * (2 * H - 3) + 2 * a) * (2 * H - 2) =
      2 * (b - a) + copyE ge * (2 * H - 3) := by rw [hxN']; ring
  have hy1 : 2 * H < 2 * H + 1 - 3 / (2 * H - 3) := by
    have : 3 / (2 * H - 3) < 1 := by rw [div_lt_iff₀ hd3]; linarith
    linarith
  have hy2 : 2 * H + 1 - 3 / (2 * H - 3) < 2 * H + 1 + 3 / (2 * H - 3) := by
    have : 0 < 3 / (2 * H - 3) := by positivity
    linarith
  refine ⟨?_, fun lo hi hlo hhi => ?_⟩
  · intro p hp
    cases ge <;> simp only [copyNook, nookPt, nookPs, nookTop, nookBot, Bool.false_eq_true,
      ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> constructor <;> linarith
  · cases ge
    · -- type LE: `R_m = P_σ`, `L_m = P_τ`
      have hc : copyE false = -16 := rfl
      have hord : (xN * (2 * H - 3) + b) / (2 * H - 2) < (xN * (2 * H - 3) + 2 * a) / (2 * H - 1) := by
        rw [div_lt_div_iff₀ hd2 hd1]; rw [hc] at hD; nlinarith
      simp only [copyNook, nookPt, nookPs, nookTop, nookBot, Bool.false_eq_true, ite_false]
      exact nook_ceil hPt1 hord hy1 hy2 hlo (by linarith)
    · -- type GE: `R_m = P_τ`, `L_m = P_σ`
      have hc : copyE true = 12 := rfl
      have hord : (xN * (2 * H - 3) + 2 * a) / (2 * H - 1) < (xN * (2 * H - 3) + b) / (2 * H - 2) := by
        rw [div_lt_div_iff₀ hd1 hd2]; rw [hc] at hD; nlinarith
      simp only [copyNook, nookPt, nookPs, nookTop, nookBot, ite_true]
      exact nook_ceil hPs1 hord hy1 hy2 hlo (by linarith)

theorem copyNook_len (ge : Bool) : 2 ≤ (copyNook a b ge H).length := by
  cases ge <;> simp [copyNook]

end Nooks

end

end ArtGallery.Stade
