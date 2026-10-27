module

public import ArtGallery.Membership.Sees
public import ArtGallery.Membership.WitnessAPI

/-!
# The formula GUARDS

`guardsF n g base` expresses that `g` guards, in the variables `base, …, base + 2g - 1`, guard the
polygon in the vertex variables.  With `m = n + g n` lines, its fresh variables are, in order:

* the guards `γ_a = (x_{base + 2a}, x_{base + 2a + 1})`, `a < g`;
* the parity variables of the guards (`n` each), for "`γ_a` is INSIDE";
* the intersection points `X^{ij}` (`i, j < m`, two variables each) of the lines `ℓ_i`, `ℓ_j`,
  where `ℓ_i` is edge line `i` for `i < n` and the line through guard `(i - n) / n` and vertex
  `(i - n) % n` otherwise (the order of `arrangementLines`); `INTERSECT(i, j)` says
  `D_{ij} ≠ 0 → D_{ij} X^{ij} = (numerators of lineInter)`;
* for every `λ < m⁶` (six line indices `i₁ j₁ i₂ j₂ i₃ j₃`, base-`m` digits of `λ`) a block of
  `lamSize n g` variables: the centroid `u_λ`, its parity variables, and one SEES block per guard;
  the formula: if the three pairs of lines are non-parallel, then `3 u_λ = X^{i₁j₁} + X^{i₂j₂} +
  X^{i₃j₃}`, the parity variables of `u_λ` are defined, and if `u_λ` is INSIDE, some guard SEES it.

Soundness (`guards_of_holds`) uses the witness lemma `ArtGallery.Membership.guards_of_witnesses`;
completeness (`exists_guards_holds`) uses a guard set of cardinality `g`.
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR Geometry

/-! ## Lines and their intersections (real numbers) -/

/-- The value of a pair of point terms. -/
def lineEval (x : ℕ → ℝ) (l : PTerm × PTerm) : Point × Point := (l.1.eval x, l.2.eval x)

/-- The denominator `d₁ × d₂` of `lineInter`. -/
def lineDenR (l₁ l₂ : Point × Point) : ℝ := crossR l₁.1 l₁.2 l₂.1 l₂.2

/-- The constant `c` of a line in `lineInter`. -/
def lineCR (l : Point × Point) : ℝ := l.1.1 * l.2.2 - l.1.2 * l.2.1

/-- The numerator of the abscissa in `lineInter`. -/
def lineNumXR (l₁ l₂ : Point × Point) : ℝ :=
  lineCR l₂ * (l₁.2.1 - l₁.1.1) - lineCR l₁ * (l₂.2.1 - l₂.1.1)

/-- The numerator of the ordinate in `lineInter`. -/
def lineNumYR (l₁ l₂ : Point × Point) : ℝ :=
  lineCR l₂ * (l₁.2.2 - l₁.1.2) - lineCR l₁ * (l₂.2.2 - l₂.1.2)

theorem lineInter_eq (l₁ l₂ : Point × Point) :
    lineInter l₁ l₂ = if lineDenR l₁ l₂ = 0 then none
      else some (lineNumXR l₁ l₂ / lineDenR l₁ l₂, lineNumYR l₁ l₂ / lineDenR l₁ l₂) := rfl

/-! ## Term versions -/

/-- The point term of guard `a`. -/
def guardT (gbase a : ℕ) : PTerm := pvar (gbase + 2 * a)

/-- Line `i`: edge line `i` for `i < n`, else the line through guard `(i - n) / n` and vertex
`(i - n) % n`. -/
def lineT (n gbase i : ℕ) : PTerm × PTerm :=
  if i < n then (vt i, vt ((i + 1) % n)) else (guardT gbase ((i - n) / n), vt ((i - n) % n))

/-- The term of the denominator. -/
def lineDenT (l₁ l₂ : PTerm × PTerm) : Term := crossT l₁.1 l₁.2 l₂.1 l₂.2

/-- The term of the constant of a line. -/
def lineCT (l : PTerm × PTerm) : Term := .sub (.mul l.1.1 l.2.2) (.mul l.1.2 l.2.1)

/-- The term of the numerator of the abscissa. -/
def lineNumXT (l₁ l₂ : PTerm × PTerm) : Term :=
  .sub (.mul (lineCT l₂) (.sub l₁.2.1 l₁.1.1)) (.mul (lineCT l₁) (.sub l₂.2.1 l₂.1.1))

/-- The term of the numerator of the ordinate. -/
def lineNumYT (l₁ l₂ : PTerm × PTerm) : Term :=
  .sub (.mul (lineCT l₂) (.sub l₁.2.2 l₁.1.2)) (.mul (lineCT l₁) (.sub l₂.2.2 l₂.1.2))

@[simp] theorem eval_lineDenT (x : ℕ → ℝ) (l₁ l₂ : PTerm × PTerm) :
    (lineDenT l₁ l₂).eval x = lineDenR (lineEval x l₁) (lineEval x l₂) := rfl

@[simp] theorem eval_lineNumXT (x : ℕ → ℝ) (l₁ l₂ : PTerm × PTerm) :
    (lineNumXT l₁ l₂).eval x = lineNumXR (lineEval x l₁) (lineEval x l₂) := rfl

@[simp] theorem eval_lineNumYT (x : ℕ → ℝ) (l₁ l₂ : PTerm × PTerm) :
    (lineNumYT l₁ l₂).eval x = lineNumYR (lineEval x l₁) (lineEval x l₂) := rfl

/-- **INTERSECT**: if the lines are not parallel, `X` is their intersection point. -/
def interF (l₁ l₂ : PTerm × PTerm) (X : PTerm) : Formula :=
  .or (.eq (lineDenT l₁ l₂) .zero)
    (.and (.eq (.mul (lineDenT l₁ l₂) X.1) (lineNumXT l₁ l₂))
      (.eq (.mul (lineDenT l₁ l₂) X.2) (lineNumYT l₁ l₂)))

/-- **CENTROID**: `3u = X₁ + X₂ + X₃`. -/
def cenF (u X₁ X₂ X₃ : PTerm) : Formula :=
  .and (.eq (.add (.add u.1 u.1) u.1) (.add (.add X₁.1 X₂.1) X₃.1))
    (.eq (.add (.add u.2 u.2) u.2) (.add (.add X₁.2 X₂.2) X₃.2))

/-- The number of lines. -/
def numLines (n g : ℕ) : ℕ := n + g * n

/-- The intersection variables of lines `i` and `j`. -/
def Xt (m xbase i j : ℕ) : PTerm := pvar (xbase + 2 * (i * m + j))

/-- The `k`-th base-`m` digit of `L`. -/
def lamC (m : ℕ) : ℕ → ℕ → ℕ
  | L, 0 => L % m
  | L, k + 1 => lamC m (L / m) k

/-- The number with base-`m` digits `l` (least significant first). -/
def lamEnc (m : ℕ) (l : List ℕ) : ℕ := l.foldr (fun a r => a + m * r) 0

/-- **CENTROID-DEFINED** for one pair: lines `i` and `j` are not parallel. -/
def cdF (n gbase i j : ℕ) : Formula := fNe (lineDenT (lineT n gbase i) (lineT n gbase j)) .zero

/-- Number of fresh variables of one centroid block. -/
def lamSize (n g : ℕ) : ℕ := 2 + n + g * seesSize n

/-- The condition for the centroid `λ` (block of variables starting at `b`). -/
def lamF (n g gbase xbase L b : ℕ) : Formula :=
  fImp (.and (cdF n gbase (lamC (numLines n g) L 0) (lamC (numLines n g) L 1))
      (.and (cdF n gbase (lamC (numLines n g) L 2) (lamC (numLines n g) L 3))
        (cdF n gbase (lamC (numLines n g) L 4) (lamC (numLines n g) L 5))))
    (.and (cenF (pvar b)
        (Xt (numLines n g) xbase (lamC (numLines n g) L 0) (lamC (numLines n g) L 1))
        (Xt (numLines n g) xbase (lamC (numLines n g) L 2) (lamC (numLines n g) L 3))
        (Xt (numLines n g) xbase (lamC (numLines n g) L 4) (lamC (numLines n g) L 5)))
      (.and (parDefF n (pvar b) (b + 2))
        (fImp (insideF n (pvar b) (b + 2))
          (bigOr ((List.range g).map fun a =>
            seesF n (guardT gbase a) (pvar b) (b + 2 + n + a * seesSize n))))))

/-- Guard `a` is INSIDE (parity variables at `gpbase + a n`). -/
def guardBlockF (n gbase gpbase a : ℕ) : Formula :=
  .and (parDefF n (guardT gbase a) (gpbase + a * n)) (insideF n (guardT gbase a) (gpbase + a * n))

/-- First parity variable of the guards. -/
def gpBase (g base : ℕ) : ℕ := base + 2 * g

/-- First intersection variable. -/
def xBase (n g base : ℕ) : ℕ := gpBase g base + g * n

/-- First centroid variable. -/
def lBase (n g base : ℕ) : ℕ := xBase n g base + 2 * (numLines n g * numLines n g)

/-- Number of fresh variables of `guardsF n g base`. -/
def guardsSize (n g : ℕ) : ℕ :=
  2 * g + g * n + 2 * (numLines n g * numLines n g) + numLines n g ^ 6 * lamSize n g

/-- **GUARDS**: the `g` guards in the variables `base, …` are in the region and see every
witness point. -/
def guardsF (n g base : ℕ) : Formula :=
  .and (bigAnd ((List.range g).map (guardBlockF n base (gpBase g base))))
    (.and (bigAnd ((List.range (numLines n g * numLines n g)).map fun q =>
        interF (lineT n base (q / numLines n g)) (lineT n base (q % numLines n g))
          (pvar (xBase n g base + 2 * q))))
      (bigAnd ((List.range (numLines n g ^ 6)).map fun L =>
        lamF n g base (xBase n g base) L (lBase n g base + L * lamSize n g))))

/-! ## Digits -/

theorem lamC_enc_cons {m a : ℕ} (ha : a < m) (l : List ℕ) (k : ℕ) :
    lamC m (lamEnc m (a :: l)) (k + 1) = lamC m (lamEnc m l) k := by
  simp only [lamEnc, List.foldr_cons, lamC]
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem lamC_enc_zero {m a : ℕ} (ha : a < m) (l : List ℕ) :
    lamC m (lamEnc m (a :: l)) 0 = a := by
  simp only [lamEnc, List.foldr_cons, lamC]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem lamEnc_lt {m : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a < m) : lamEnc m l < m ^ l.length := by
  induction l with
  | nil => simp [lamEnc]
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun b hb => hl b (by simp [hb]))
    simp only [lamEnc, List.foldr_cons, List.length_cons] at ih' ⊢
    have : m * (l.foldr (fun a r => a + m * r) 0 + 1) ≤ m * m ^ l.length :=
      Nat.mul_le_mul_left _ ih'
    rw [pow_succ]
    nlinarith

/-! ## Semantics of lines -/

/-- The guard points of an assignment. -/
def guardList (x : ℕ → ℝ) (g base : ℕ) : List Point :=
  (List.range g).map fun a => (guardT base a).eval x

theorem lineEval_lineT_lt {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {base i : ℕ}
    (hi : i < P.n) :
    lineEval x (lineT P.n base i) = (P.vtx i, P.vtx ((i + 1) % P.n)) := by
  simp [lineT, hi, lineEval, hx i hi, hx _ (succ_mod_lt hi)]

theorem lineEval_lineT_ge {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {base a k : ℕ}
    (hk : k < P.n) :
    lineEval x (lineT P.n base (P.n + a * P.n + k)) =
      ((guardT base a).eval x, P.vtx k) := by
  have h1 : ¬ (P.n + a * P.n + k < P.n) := by omega
  have h2 : P.n + a * P.n + k - P.n = a * P.n + k := by omega
  simp only [lineT, h1, ite_false, lineEval, h2, pair_div hk, pair_mod hk, hx k hk]

/-- Every line of the arrangement is one of the lines `ℓ_i`. -/
theorem mem_arrangementLines {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {g base : ℕ}
    {l : Point × Point} (hl : l ∈ arrangementLines P (guardList x g base)) :
    ∃ i < numLines P.n g, l = lineEval x (lineT P.n base i) := by
  unfold arrangementLines at hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hj
    exact ⟨j, by unfold numLines; omega, (lineEval_lineT_lt hx hj).symm⟩
  · obtain ⟨γ, hγ, hl⟩ := List.mem_flatMap.1 hl
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
    rw [List.mem_range] at ha
    refine ⟨P.n + a * P.n + k, ?_, (lineEval_lineT_ge hx hk).symm⟩
    have := pair_lt ha hk
    unfold numLines; omega

/-! ## Soundness -/

theorem holds_interF_eq {x : ℕ → ℝ} {l₁ l₂ : PTerm × PTerm} {X : PTerm}
    (h : (interF l₁ l₂ X).Holds x) {p : Point}
    (hp : lineInter (lineEval x l₁) (lineEval x l₂) = some p) : X.eval x = p := by
  rw [lineInter_eq] at hp
  split_ifs at hp with hD
  cases hp
  simp only [interF, holds_or, holds_and, holds_eq, eval_mul, eval_lineDenT, eval_lineNumXT,
    eval_lineNumYT, eval_zero] at h
  rcases h with h | ⟨h1, h2⟩
  · exact absurd h hD
  · ext
    · simp only [PTerm.eval_fst]; rw [← h1]; field_simp
    · simp only [PTerm.eval_snd]; rw [← h2]; field_simp

/-- **GUARDS is sound**: the guards of a satisfying assignment lie in the region and guard it
(via the witness lemma). -/
theorem guards_of_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x) {g base : ℕ}
    (h : (guardsF P.n g base).Holds x) :
    (∀ γ ∈ guardList x g base, γ ∈ P.filled) ∧
      ∀ p ∈ P.filled, ∃ γ ∈ guardList x g base, P.Sees γ p := by
  obtain ⟨hg, hint, hl⟩ := h
  rw [holds_bigAnd_range] at hg hint hl
  have hΓ : ∀ γ ∈ guardList x g base, γ ∈ P.filled := by
    intro γ hγ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
    rw [List.mem_range] at ha
    obtain ⟨hpd, hin⟩ := hg a ha
    exact (holds_insideF hP hx hpd).1 hin
  refine ⟨hΓ, guards_of_witnesses hP _ hΓ ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, m = numLines P.n g := ⟨_, rfl⟩
  rw [← hm] at hint hl
  -- each arrangement vertex is the intersection of two lines `ℓ_i`, `ℓ_j`
  have hvert : ∀ a ∈ arrangementVertices (arrangementLines P (guardList x g base)),
      ∃ i < m, ∃ j < m, lineInter (lineEval x (lineT P.n base i))
        (lineEval x (lineT P.n base j)) = some a := by
    rintro a ⟨l₁, hl₁, l₂, hl₂, ha⟩
    obtain ⟨i, hi, rfl⟩ := mem_arrangementLines hx hl₁
    obtain ⟨j, hj, rfl⟩ := mem_arrangementLines hx hl₂
    rw [← hm] at hi hj
    exact ⟨i, hi, j, hj, ha⟩
  have hX : ∀ i < m, ∀ j < m, ∀ a, lineInter (lineEval x (lineT P.n base i))
      (lineEval x (lineT P.n base j)) = some a → (Xt m (xBase P.n g base) i j).eval x = a := by
    intro i hi j hj a ha
    have := hint (i * m + j) (pair_lt hi hj)
    rw [pair_div hj, pair_mod hj] at this
    exact holds_interF_eq this ha
  have hD : ∀ i j a, lineInter (lineEval x (lineT P.n base i))
      (lineEval x (lineT P.n base j)) = some a →
      (cdF P.n base i j).Holds x := by
    intro i j a ha
    rw [lineInter_eq] at ha
    split_ifs at ha with hD
    simpa [cdF] using hD
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ hcen
  obtain ⟨i₁, hi₁, j₁, hj₁, e₁⟩ := hvert a₁ ha₁
  obtain ⟨i₂, hi₂, j₂, hj₂, e₂⟩ := hvert a₂ ha₂
  obtain ⟨i₃, hi₃, j₃, hj₃, e₃⟩ := hvert a₃ ha₃
  obtain ⟨L, hL⟩ : ∃ L, L = lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃] := ⟨_, rfl⟩
  have hLlt : L < m ^ 6 := by
    have := lamEnc_lt (m := m) [i₁, j₁, i₂, j₂, i₃, j₃] (by simp; omega)
    rw [hL]; simpa using this
  have hc0 : lamC m L 0 = i₁ := by rw [hL, lamC_enc_zero hi₁]
  have hc1 : lamC m L 1 = j₁ := by rw [hL, lamC_enc_cons hi₁, lamC_enc_zero hj₁]
  have hc2 : lamC m L 2 = i₂ := by
    rw [hL, lamC_enc_cons hi₁, lamC_enc_cons hj₁, lamC_enc_zero hi₂]
  have hc3 : lamC m L 3 = j₂ := by
    rw [hL, lamC_enc_cons hi₁, lamC_enc_cons hj₁, lamC_enc_cons hi₂, lamC_enc_zero hj₂]
  have hc4 : lamC m L 4 = i₃ := by
    rw [hL, lamC_enc_cons hi₁, lamC_enc_cons hj₁, lamC_enc_cons hi₂, lamC_enc_cons hj₂,
      lamC_enc_zero hi₃]
  have hc5 : lamC m L 5 = j₃ := by
    rw [hL, lamC_enc_cons hi₁, lamC_enc_cons hj₁, lamC_enc_cons hi₂, lamC_enc_cons hj₂,
      lamC_enc_cons hi₃, lamC_enc_zero hj₃]
  have hlam := hl L hLlt
  rw [lamF, holds_fImp, ← hm, hc0, hc1, hc2, hc3, hc4, hc5] at hlam
  obtain ⟨hcf, hpd, hsee⟩ := hlam ⟨hD _ _ _ e₁, hD _ _ _ e₂, hD _ _ _ e₃⟩
  have hu : (pvar (lBase P.n g base + L * lamSize P.n g)).eval x = centroid a₁ a₂ a₃ := by
    simp only [cenF, holds_and, holds_eq, eval_add] at hcf
    have f₁ := hX i₁ hi₁ j₁ hj₁ a₁ e₁
    have f₂ := hX i₂ hi₂ j₂ hj₂ a₂ e₂
    have f₃ := hX i₃ hi₃ j₃ hj₃ a₃ e₃
    rw [Prod.ext_iff] at f₁ f₂ f₃
    simp only [PTerm.eval_fst, PTerm.eval_snd] at f₁ f₂ f₃
    rw [f₁.1, f₂.1, f₃.1, f₁.2, f₂.2, f₃.2] at hcf
    obtain ⟨c1, c2⟩ := hcf
    simp only [pvar_fst, pvar_snd, eval_var] at c1 c2
    ext
    · simp only [pvar_eval, centroid]; linarith
    · simp only [pvar_eval, centroid]; linarith
  rw [holds_fImp, holds_insideF hP hx hpd, hu] at hsee
  obtain ⟨φ, hφ, hφh⟩ := (holds_bigOr x _).1 (hsee hcen)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
  rw [List.mem_range] at ha
  have hseg := sees_of_holds hP hx hφh
  rw [hu] at hseg
  exact ⟨(guardT base a).eval x, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩, hseg⟩

/-! ## Variables -/

theorem PVars_guardT {S : ℕ → Prop} {gbase a : ℕ} (h : S (gbase + 2 * a) ∧ S (gbase + 2 * a + 1)) :
    PVars S (guardT gbase a) := h

/-- The guard variables satisfy `S`. -/
def GuardVars (S : ℕ → Prop) (g gbase : ℕ) : Prop :=
  ∀ a < g, S (gbase + 2 * a) ∧ S (gbase + 2 * a + 1)

theorem PVars_lineT {S : ℕ → Prop} {n g gbase i : ℕ} (hv : VtxVars S n) (hg : GuardVars S g gbase)
    (hi : i < numLines n g) : PVars S (lineT n gbase i).1 ∧ PVars S (lineT n gbase i).2 := by
  unfold lineT
  split_ifs with h
  · exact ⟨hv.pv h, hv.pv (succ_mod_lt h)⟩
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [numLines] at hi
      · exact h0
    have ha : (i - n) / n < g := by
      apply Nat.div_lt_of_lt_mul; unfold numLines at hi
      rw [Nat.mul_comm]; omega
    exact ⟨PVars_guardT (hg _ ha), hv.pv (Nat.mod_lt _ hn)⟩

theorem TVars_lineDenT {S : ℕ → Prop} {l₁ l₂ : PTerm × PTerm}
    (h₁ : PVars S l₁.1 ∧ PVars S l₁.2) (h₂ : PVars S l₂.1 ∧ PVars S l₂.2) :
    TVars S (lineDenT l₁ l₂) := TVars_crossT h₁.1 h₁.2 h₂.1 h₂.2

theorem TVars_lineCT {S : ℕ → Prop} {l : PTerm × PTerm} (h : PVars S l.1 ∧ PVars S l.2) :
    TVars S (lineCT l) := ⟨⟨h.1.1, h.2.2⟩, ⟨h.1.2, h.2.1⟩⟩

theorem FVars_interF {S : ℕ → Prop} {l₁ l₂ : PTerm × PTerm} {X : PTerm}
    (h₁ : PVars S l₁.1 ∧ PVars S l₁.2) (h₂ : PVars S l₂.1 ∧ PVars S l₂.2) (hX : PVars S X) :
    FVars S (interF l₁ l₂ X) := by
  have hD := TVars_lineDenT h₁ h₂
  have hc₁ := TVars_lineCT h₁
  have hc₂ := TVars_lineCT h₂
  exact ⟨⟨hD, trivial⟩, ⟨⟨hD, hX.1⟩, ⟨hc₂, h₁.2.1, h₁.1.1⟩, ⟨hc₁, h₂.2.1, h₂.1.1⟩⟩,
    ⟨⟨hD, hX.2⟩, ⟨hc₂, h₁.2.2, h₁.1.2⟩, ⟨hc₁, h₂.2.2, h₂.1.2⟩⟩⟩

theorem FVars_cenF {S : ℕ → Prop} {u X₁ X₂ X₃ : PTerm} (hu : PVars S u) (h₁ : PVars S X₁)
    (h₂ : PVars S X₂) (h₃ : PVars S X₃) : FVars S (cenF u X₁ X₂ X₃) :=
  ⟨⟨⟨⟨hu.1, hu.1⟩, hu.1⟩, ⟨⟨h₁.1, h₂.1⟩, h₃.1⟩⟩, ⟨⟨⟨hu.2, hu.2⟩, hu.2⟩, ⟨⟨h₁.2, h₂.2⟩, h₃.2⟩⟩⟩

theorem lamC_lt {m : ℕ} (hm : 0 < m) (L k : ℕ) : lamC m L k < m := by
  induction k generalizing L with
  | zero => exact Nat.mod_lt _ hm
  | succ k ih => exact ih _

theorem FVars_lamF {S : ℕ → Prop} {n g gbase xbase L b : ℕ} (hv : VtxVars S n)
    (hg : GuardVars S g gbase)
    (hX : ∀ q < numLines n g * numLines n g, S (xbase + 2 * q) ∧ S (xbase + 2 * q + 1))
    (hb : ∀ v, b ≤ v → v < b + lamSize n g → S v) (hL : L < numLines n g ^ 6) :
    FVars S (lamF n g gbase xbase L b) := by
  have hm : 0 < numLines n g := by
    rcases Nat.eq_zero_or_pos (numLines n g) with h | h
    · rw [h] at hL; simp at hL
    · exact h
  have hl : ∀ k, PVars S (lineT n gbase (lamC (numLines n g) L k)).1 ∧
      PVars S (lineT n gbase (lamC (numLines n g) L k)).2 :=
    fun k => PVars_lineT hv hg (lamC_lt hm L k)
  have hcd : ∀ k k', FVars S (cdF n gbase (lamC (numLines n g) L k) (lamC (numLines n g) L k')) :=
    fun k k' => ⟨TVars_lineDenT (hl k) (hl k'), trivial⟩
  have hXt : ∀ k k', PVars S (Xt (numLines n g) xbase (lamC (numLines n g) L k)
      (lamC (numLines n g) L k')) :=
    fun k k' => hX _ (pair_lt (lamC_lt hm L k) (lamC_lt hm L k'))
  have hu : PVars S (pvar b) :=
    ⟨hb b le_rfl (by unfold lamSize; omega), hb (b + 1) (by omega) (by unfold lamSize; omega)⟩
  have hpar : ∀ e < n, S (b + 2 + e) := fun e he => hb _ (by omega) (by unfold lamSize; omega)
  have hsees : FVars S (bigOr ((List.range g).map fun a =>
      seesF n (guardT gbase a) (pvar b) (b + 2 + n + a * seesSize n))) := by
    rw [FVars_bigOr]
    intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨a, ha, rfl⟩ := hφ
    refine FVars_seesF (PVars_guardT (hg a ha)) hu hv (fun v h1 h2 => hb v (by omega) ?_)
    have : (a + 1) * seesSize n ≤ g * seesSize n := Nat.mul_le_mul_right _ ha
    unfold lamSize; rw [Nat.add_mul, Nat.one_mul] at this; omega
  exact ⟨⟨hcd 0 1, hcd 2 3, hcd 4 5⟩, FVars_cenF hu (hXt 0 1) (hXt 2 3) (hXt 4 5),
    FVars_parDefF hu hv hpar, FVars_insideF hu hv hpar, hsees⟩

theorem FVars_guardBlockF {S : ℕ → Prop} {n gbase gpbase a : ℕ} (hv : VtxVars S n)
    (hg : S (gbase + 2 * a) ∧ S (gbase + 2 * a + 1)) (hp : ∀ e < n, S (gpbase + a * n + e)) :
    FVars S (guardBlockF n gbase gpbase a) :=
  ⟨FVars_parDefF (PVars_guardT hg) hv hp, FVars_insideF (PVars_guardT hg) hv hp⟩

/-! ## Completeness -/

/-- Existence for one centroid block. -/
theorem exists_lam_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x)
    {g gbase xbase L b : ℕ} (hgv : GuardVars (· < b) g gbase)
    (hXv : ∀ q < numLines P.n g * numLines P.n g, xbase + 2 * q + 1 < b)
    (hb : 2 * P.n ≤ b) (hL : L < numLines P.n g ^ 6)
    (hguard : ∀ p ∈ P.filled, ∃ a < g, P.Sees ((guardT gbase a).eval x) p) :
    ∃ y : ℕ → ℝ, (∀ v < b, y v = x v) ∧ (lamF P.n g gbase xbase L b).Holds y := by
  have hm : 0 < numLines P.n g := by
    rcases Nat.eq_zero_or_pos (numLines P.n g) with h | h
    · rw [h] at hL; simp at hL
    · exact h
  have hV : VtxVars (· < b) P.n := vtxVars_lt hb
  have hl : ∀ k, PVars (· < b) (lineT P.n gbase (lamC (numLines P.n g) L k)).1 ∧
      PVars (· < b) (lineT P.n gbase (lamC (numLines P.n g) L k)).2 :=
    fun k => PVars_lineT hV hgv (lamC_lt hm L k)
  have hXt : ∀ k k', PVars (· < b) (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L k)
      (lamC (numLines P.n g) L k')) := fun k k' => by
    have := hXv _ (pair_lt (lamC_lt hm L k) (lamC_lt hm L k'))
    exact ⟨show _ < b by omega, show _ < b by omega⟩
  set A := Formula.and (cdF P.n gbase (lamC (numLines P.n g) L 0) (lamC (numLines P.n g) L 1))
      (.and (cdF P.n gbase (lamC (numLines P.n g) L 2) (lamC (numLines P.n g) L 3))
        (cdF P.n gbase (lamC (numLines P.n g) L 4) (lamC (numLines P.n g) L 5))) with hA_def
  by_cases hA : A.Holds x
  · set X₁ := (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 0)
      (lamC (numLines P.n g) L 1)).eval x
    set X₂ := (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 2)
      (lamC (numLines P.n g) L 3)).eval x
    set X₃ := (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 4)
      (lamC (numLines P.n g) L 5)).eval x
    set u : Point := ((X₁.1 + X₂.1 + X₃.1) / 3, (X₁.2 + X₂.2 + X₃.2) / 3) with hu_def
    let y1 := upd2 x b u.1 u.2
    have hy1 : ∀ v < b, y1 v = x v := fun v hv => upd2_of_lt hv
    have hx1 : VtxOK P y1 := hx.congr fun v hv => hy1 v (by omega)
    obtain ⟨y2, hy2, hpd⟩ := exists_parDef hx1
      (PVars_pvar (S := (· < b + 2)) (show b < b + 2 by omega) (show b + 1 < b + 2 by omega))
      (by omega)
    have hx2 : VtxOK P y2 := hx1.congr fun v hv => hy2 v (by omega)
    have hu2 : (pvar b).eval y2 = u := by
      rw [PTerm.eval_congr (S := (· < b + 2)) (p := pvar b) hy2
        (PVars_pvar (S := (· < b + 2)) (show b < b + 2 by omega) (show b + 1 < b + 2 by omega))]
      exact pvar_eval_upd2 x b u.1 u.2
    have hcen : ∀ y : ℕ → ℝ, (∀ v < b + 2, y v = y1 v) →
        (cenF (pvar b) (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 0)
          (lamC (numLines P.n g) L 1)) (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 2)
          (lamC (numLines P.n g) L 3)) (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 4)
          (lamC (numLines P.n g) L 5))).Holds y := by
      intro y hy
      have hS : FVars (· < b + 2) (cenF (pvar b)
          (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 0) (lamC (numLines P.n g) L 1))
          (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 2) (lamC (numLines P.n g) L 3))
          (Xt (numLines P.n g) xbase (lamC (numLines P.n g) L 4) (lamC (numLines P.n g) L 5))) :=
        FVars_cenF ⟨show b < b + 2 by omega, show b + 1 < b + 2 by omega⟩
          ((hXt 0 1).mono fun v hv => by omega) ((hXt 2 3).mono fun v hv => by omega)
          ((hXt 4 5).mono fun v hv => by omega)
      rw [holds_congr_lt hy hS]
      have e₁ := PTerm.eval_congr (S := (· < b)) hy1 (hXt 0 1)
      have e₂ := PTerm.eval_congr (S := (· < b)) hy1 (hXt 2 3)
      have e₃ := PTerm.eval_congr (S := (· < b)) hy1 (hXt 4 5)
      have f₁ := congrArg Prod.fst e₁
      have f₂ := congrArg Prod.fst e₂
      have f₃ := congrArg Prod.fst e₃
      have g₁ := congrArg Prod.snd e₁
      have g₂ := congrArg Prod.snd e₂
      have g₃ := congrArg Prod.snd e₃
      simp only [PTerm.eval_fst, PTerm.eval_snd] at f₁ f₂ f₃ g₁ g₂ g₃
      simp only [cenF, holds_and, holds_eq, eval_add, f₁, f₂, f₃, g₁, g₂, g₃]
      have hb0 : (pvar b).1.eval y1 = u.1 := by simp [pvar, y1]
      have hb1 : (pvar b).2.eval y1 = u.2 := by simp [pvar, y1]
      rw [hb0, hb1, hu_def]
      constructor
      · simp only [X₁, X₂, X₃, PTerm.eval_fst]; ring
      · simp only [X₁, X₂, X₃, PTerm.eval_snd]; ring
    by_cases hin : u ∈ P.filled
    · obtain ⟨a, ha, hsee⟩ := hguard u hin
      have hγ : PVars (· < b) (guardT gbase a) := PVars_guardT (hgv a ha)
      have hγ2 : (guardT gbase a).eval y2 = (guardT gbase a).eval x := by
        rw [PTerm.eval_congr (S := (· < b)) (fun v hv => hy2 v (by omega)) hγ]
        exact PTerm.eval_congr (S := (· < b)) hy1 hγ
      obtain ⟨y3, hy3, hS⟩ := exists_sees_holds hP hx2 (γ := guardT gbase a) (c := pvar b)
        (base := b + 2 + P.n + a * seesSize P.n) (hγ.mono fun v hv => by omega)
        ⟨show b < _ by omega, show b + 1 < _ by omega⟩ (by omega)
        (by rw [hγ2, hu2]; exact hsee)
      refine ⟨y3, fun v hv => by rw [hy3 v (by omega), hy2 v (by omega), hy1 v hv], ?_⟩
      rw [lamF, holds_fImp]
      intro _
      have hy31 : ∀ v < b + 2, y3 v = y1 v := fun v hv => by
        rw [hy3 v (by omega), hy2 v hv]
      have hpdS : FVars (· < b + 2 + P.n) (parDefF P.n (pvar b) (b + 2)) :=
        FVars_parDefF ⟨show b < _ by omega, show b + 1 < _ by omega⟩
          (vtxVars_lt (by omega)) (fun e he => by show _ < _; omega)
      refine ⟨hcen y3 hy31, (holds_congr_lt (fun v hv => hy3 v (by omega)) hpdS).2 hpd, ?_⟩
      rw [holds_fImp]
      intro _
      rw [holds_bigOr_range]
      exact ⟨a, ha, hS⟩
    · refine ⟨y2, fun v hv => by rw [hy2 v (by omega), hy1 v hv], ?_⟩
      rw [lamF, holds_fImp]
      intro _
      refine ⟨hcen y2 hy2, hpd, ?_⟩
      rw [holds_fImp, holds_insideF hP hx2 hpd, hu2]
      intro h
      exact absurd h hin
  · refine ⟨x, fun _ _ => rfl, ?_⟩
    rw [lamF, holds_fImp]
    intro h
    exact absurd h hA

/-- **GUARDS is complete**: from a guard set of cardinality `g`, all variables of GUARDS can be
chosen to satisfy it. -/
theorem exists_guards_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x)
    {g base : ℕ} (hb : 2 * P.n ≤ base) (hG : P.HasGuardSetOfCard g) :
    ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ (guardsF P.n g base).Holds y := by
  obtain ⟨G, hcard, hGsub, hGsees⟩ := hG
  have hlen : G.toList.length = g := by rw [Finset.length_toList, hcard]
  let γv : ℕ → Point := fun a => if h : a < G.toList.length then G.toList[a] else 0
  have hγG : ∀ a < g, γv a ∈ G := fun a ha => by
    have ha' : a < G.toList.length := by omega
    simp only [γv, dite_eq_left ha']
    exact Finset.mem_toList.1 (List.getElem_mem ha')
  have hguard : ∀ p ∈ P.filled, ∃ a < g, P.Sees (γv a) p := by
    intro p hp
    obtain ⟨γ, hγ, hs⟩ := hGsees p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hγ)
    refine ⟨a, by omega, ?_⟩
    simp only [γv, dite_eq_left ha]
    exact hs
  -- stage A: the guards
  let yA : ℕ → ℝ := fun v =>
    if base ≤ v ∧ v < base + 2 * g then
      (if (v - base) % 2 = 0 then (γv ((v - base) / 2)).1 else (γv ((v - base) / 2)).2)
    else x v
  have hyA : ∀ v < base, yA v = x v := fun v hv => by
    simp only [yA]
    rw [ite_eq_right (by omega)]
  have hyAg : ∀ a < g, (guardT base a).eval yA = γv a := fun a ha => by
    have e1 : base ≤ base + 2 * a ∧ base + 2 * a < base + 2 * g := by omega
    have e2 : base ≤ base + 2 * a + 1 ∧ base + 2 * a + 1 < base + 2 * g := by omega
    have e3 : (base + 2 * a - base) % 2 = 0 := by omega
    have e4 : ¬ (base + 2 * a + 1 - base) % 2 = 0 := by omega
    have e5 : (base + 2 * a - base) / 2 = a := by omega
    have e6 : (base + 2 * a + 1 - base) / 2 = a := by omega
    simp only [guardT, pvar_eval, yA, ite_eq_left e1, ite_eq_left e2, ite_eq_left e3, ite_eq_right e4, e5, e6]
  have hxA : VtxOK P yA := hx.congr fun v hv => hyA v (by omega)
  have hVb : VtxVars (· < base) P.n := vtxVars_lt hb
  -- stage B: the guards are inside
  obtain ⟨yB, hyB, hallB⟩ := exists_glue (x := yA) (base := gpBase g base) (K := P.n) (N := g)
    (φ := guardBlockF P.n base (gpBase g base))
    (fun a ha => FVars_guardBlockF (hVb.mono fun v hv => Or.inl (by unfold gpBase; omega))
      ⟨Or.inl (by unfold gpBase; omega), Or.inl (by unfold gpBase; omega)⟩
      (fun e he => Or.inr ⟨by omega, by omega⟩))
    (by
      intro a ha
      have hq : PVars (· < gpBase g base + a * P.n) (guardT base a) :=
        PVars_guardT ⟨by unfold gpBase; show _ < _; omega, by unfold gpBase; show _ < _; omega⟩
      obtain ⟨y, hy, hpd⟩ := exists_parDef hxA hq (by unfold gpBase; omega)
      refine ⟨y, fun v hv => hy v (by omega), hpd, ?_⟩
      have hxy : VtxOK P y := hxA.congr fun v hv => hy v (by unfold gpBase; omega)
      rw [holds_insideF hP hxy hpd, PTerm.eval_congr (S := (· < gpBase g base + a * P.n)) hy hq,
        hyAg a ha]
      exact hGsub (hγG a ha))
  have hxB : VtxOK P yB := hxA.congr fun v hv => hyB v (by unfold gpBase; omega)
  -- stage C: the intersection points
  have hgvx : GuardVars (· < xBase P.n g base) g base := fun a ha =>
    ⟨by unfold xBase gpBase; show _ < _; omega, by unfold xBase gpBase; show _ < _; omega⟩
  have hVx : VtxVars (· < xBase P.n g base) P.n :=
    hVb.mono fun v hv => by unfold xBase gpBase; omega
  obtain ⟨yC, hyC, hallC⟩ := exists_glue (x := yB) (base := xBase P.n g base) (K := 2)
    (N := numLines P.n g * numLines P.n g) (φ := fun q => interF (lineT P.n base (q / numLines P.n g)) (lineT P.n base (q % numLines P.n g))
      (pvar (xBase P.n g base + 2 * q)))
    (by
      intro q hq
      have hm0 : 0 < numLines P.n g := by
        rcases Nat.eq_zero_or_pos (numLines P.n g) with h | h
        · rw [h] at hq; simp at hq
        · exact h
      have h1 := PVars_lineT (S := InBlock (xBase P.n g base) 2 q)
        (hVx.mono fun v hv => Or.inl hv) (fun a ha => ⟨Or.inl (hgvx a ha).1, Or.inl (hgvx a ha).2⟩)
        (Nat.div_lt_of_lt_mul hq)
      have h2 := PVars_lineT (S := InBlock (xBase P.n g base) 2 q)
        (hVx.mono fun v hv => Or.inl hv) (fun a ha => ⟨Or.inl (hgvx a ha).1, Or.inl (hgvx a ha).2⟩)
        (Nat.mod_lt q hm0)
      exact FVars_interF h1 h2 ⟨Or.inr ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩)
    (by
      intro q hq
      set l₁ := lineEval yB (lineT P.n base (q / numLines P.n g))
      set l₂ := lineEval yB (lineT P.n base (q % numLines P.n g))
      let X : Point := if lineDenR l₁ l₂ = 0 then (0, 0)
        else (lineNumXR l₁ l₂ / lineDenR l₁ l₂, lineNumYR l₁ l₂ / lineDenR l₁ l₂)
      refine ⟨upd2 yB (xBase P.n g base + 2 * q) X.1 X.2, fun v hv => upd2_of_lt (by omega), ?_⟩
      have hm0 : 0 < numLines P.n g := by
        rcases Nat.eq_zero_or_pos (numLines P.n g) with h | h
        · rw [h] at hq; simp at hq
        · exact h
      have hagree : ∀ v < xBase P.n g base,
          upd2 yB (xBase P.n g base + 2 * q) X.1 X.2 v = yB v := fun v hv => upd2_of_lt (by omega)
      have hl₁ := PVars_lineT hVx hgvx (Nat.div_lt_of_lt_mul hq)
      have hl₂ := PVars_lineT hVx hgvx (Nat.mod_lt q hm0)
      have e₁ : lineEval (upd2 yB (xBase P.n g base + 2 * q) X.1 X.2) (lineT P.n base (q / numLines P.n g)) = l₁ := by
        simp only [lineEval, l₁, PTerm.eval_congr (S := (· < xBase P.n g base)) hagree hl₁.1,
          PTerm.eval_congr (S := (· < xBase P.n g base)) hagree hl₁.2]
      have e₂ : lineEval (upd2 yB (xBase P.n g base + 2 * q) X.1 X.2) (lineT P.n base (q % numLines P.n g)) = l₂ := by
        simp only [lineEval, l₂, PTerm.eval_congr (S := (· < xBase P.n g base)) hagree hl₂.1,
          PTerm.eval_congr (S := (· < xBase P.n g base)) hagree hl₂.2]
      simp only [interF, holds_or, holds_and, holds_eq, eval_mul, eval_lineDenT, eval_lineNumXT,
        eval_lineNumYT, eval_zero, e₁, e₂, pvar_fst, pvar_snd, eval_var, upd2_fst, upd2_snd]
      by_cases hD : lineDenR l₁ l₂ = 0
      · left; exact hD
      · right
        simp only [X, ite_eq_right hD]
        constructor <;> field_simp)
  have hxC : VtxOK P yC := hxB.congr fun v hv => hyC v (by unfold xBase gpBase; omega)
  -- stage D: the centroids
  have hgC : ∀ a < g, (guardT base a).eval yC = γv a := fun a ha => by
    have hq : PVars (· < gpBase g base) (guardT base a) :=
      PVars_guardT ⟨by unfold gpBase; show _ < _; omega, by unfold gpBase; show _ < _; omega⟩
    rw [PTerm.eval_congr (S := (· < gpBase g base))
      (fun v hv => by rw [hyC v (by unfold xBase; omega)]) hq,
      PTerm.eval_congr (S := (· < gpBase g base)) hyB hq, hyAg a ha]
  obtain ⟨yD, hyD, hallD⟩ := exists_glue (x := yC) (base := lBase P.n g base) (K := lamSize P.n g)
    (N := numLines P.n g ^ 6) (φ := fun L => lamF P.n g base (xBase P.n g base) L
      (lBase P.n g base + L * lamSize P.n g))
    (by
      intro L hL
      refine FVars_lamF (hVb.mono fun v hv => Or.inl (by unfold lBase xBase gpBase; omega))
        (fun a ha => ⟨Or.inl ?_, Or.inl ?_⟩) (fun q hq => ⟨Or.inl ?_, Or.inl ?_⟩)
        (fun v h1 h2 => Or.inr ⟨by omega, by omega⟩) hL
      · unfold lBase xBase gpBase; omega
      · unfold lBase xBase gpBase; omega
      · unfold lBase; omega
      · unfold lBase; omega)
    (by
      intro L hL
      obtain ⟨y, hy, hh⟩ := exists_lam_holds hP hxC (g := g) (gbase := base)
        (xbase := xBase P.n g base) (L := L) (b := lBase P.n g base + L * lamSize P.n g)
        (fun a ha => ⟨by show _ < _; unfold lBase xBase gpBase; omega,
          by show _ < _; unfold lBase xBase gpBase; omega⟩)
        (fun q hq => by unfold lBase; omega) (by unfold lBase xBase gpBase; omega) hL
        (fun p hp => by
          obtain ⟨a, ha, hs⟩ := hguard p hp
          exact ⟨a, ha, by rw [hgC a ha]; exact hs⟩)
      exact ⟨y, fun v hv => hy v (by omega), hh⟩)
  refine ⟨yD, fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [hyD v (by unfold lBase xBase gpBase; omega), hyC v (by unfold xBase gpBase; omega),
      hyB v (by unfold gpBase; omega), hyA v hv]
  · rw [holds_bigAnd_range]
    intro a ha
    have hS : FVars (· < xBase P.n g base) (guardBlockF P.n base (gpBase g base) a) := by
      refine FVars_guardBlockF hVx (hgvx a ha) (fun e he => ?_)
      have : (a + 1) * P.n ≤ g * P.n := Nat.mul_le_mul_right _ ha
      rw [Nat.add_mul, Nat.one_mul] at this
      show _ < _; unfold xBase; omega
    rw [holds_congr_lt (fun v hv => by rw [hyD v (by unfold lBase; omega), hyC v hv]) hS]
    exact hallB a ha
  · rw [holds_bigAnd_range]
    intro q hq
    have hm0 : 0 < numLines P.n g := by
      rcases Nat.eq_zero_or_pos (numLines P.n g) with h | h
      · rw [h] at hq; simp at hq
      · exact h
    have hS : FVars (· < lBase P.n g base) (interF (lineT P.n base (q / numLines P.n g))
        (lineT P.n base (q % numLines P.n g)) (pvar (xBase P.n g base + 2 * q))) := by
      have hV' : VtxVars (· < lBase P.n g base) P.n := hVx.mono fun v hv => by unfold lBase; omega
      have hg' : GuardVars (· < lBase P.n g base) g base := fun a ha =>
        ⟨by have := (hgvx a ha).1; show _ < _; unfold lBase; omega,
          by have := (hgvx a ha).2; show _ < _; unfold lBase; omega⟩
      exact FVars_interF (PVars_lineT hV' hg' (Nat.div_lt_of_lt_mul hq))
        (PVars_lineT hV' hg' (Nat.mod_lt q hm0))
        ⟨show _ < _ by unfold lBase; omega, show _ < _ by unfold lBase; omega⟩
    rw [holds_congr_lt hyD hS]
    exact hallC q hq
  · rw [holds_bigAnd_range]; exact hallD

end ArtGallery.Membership

end
