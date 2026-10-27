module

public import ArtGallery.FewVars.Sees
public import ArtGallery.Membership.Guards

/-!
# GUARDS without auxiliary variables

The only variables are the guard coordinates: guard `a` is the point `(x_{2a}, x_{2a+1})`
(`rguard a`).  With `m = n + g n` lines (`rline`: the edge lines, then the lines through a guard
and a corner, in the order of `arrangementLines`), the vertices of the arrangement are the
rational points `rinter` (intersection of two non-parallel lines, written with the explicit
numerators and denominator of `lineInter`), and the witness points are the centroids
`rcentroid` of three of them.

`rguardsF C g`: every guard is INSIDE, and for every `λ < m⁶` (six line indices, the base-`m`
digits of `λ`): if the three pairs of lines are non-parallel and the centroid is INSIDE, some
guard SEES it.  Main results: `guards_of_holds_rguardsF` and `holds_rguardsF_of_guards`.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

/-! ## Lines, intersection points, centroids -/

/-- Guard `a`: the point `(x_{2a}, x_{2a+1})`. -/
def rguard (a : ℕ) : RPt := rvarPt (2 * a)

/-- The guard points of an assignment. -/
def guardPt (x : ℕ → ℝ) (a : ℕ) : Point := (x (2 * a), x (2 * a + 1))

/-- Line `i`: edge line `i` for `i < n`, else the line through guard `(i - n) / n` and corner
`(i - n) % n`. -/
def rline (C : List RPt) (i : ℕ) : RPt × RPt :=
  if i < C.length then (cr C i, cr C ((i + 1) % C.length))
  else (rguard ((i - C.length) / C.length), cr C ((i - C.length) % C.length))

/-- The real line `i` (guards `Γ`). -/
def lineR (P : Polygon) (Γ : ℕ → Point) (i : ℕ) : Point × Point :=
  if i < P.n then (P.vtx i, P.vtx ((i + 1) % P.n))
  else (Γ ((i - P.n) / P.n), P.vtx ((i - P.n) % P.n))

/-- The denominator of the intersection point of two lines. -/
def rlineDen (l₁ l₂ : RPt × RPt) : RTerm := rcrossT l₁.1 l₁.2 l₂.1 l₂.2

/-- The constant of a line. -/
def rlineC (l : RPt × RPt) : RTerm := rsub (rmul l.1.1 l.2.2) (rmul l.1.2 l.2.1)

/-- The numerator of the abscissa of the intersection point. -/
def rlineNumX (l₁ l₂ : RPt × RPt) : RTerm :=
  rsub (rmul (rlineC l₂) (rsub l₁.2.1 l₁.1.1)) (rmul (rlineC l₁) (rsub l₂.2.1 l₂.1.1))

/-- The numerator of the ordinate of the intersection point. -/
def rlineNumY (l₁ l₂ : RPt × RPt) : RTerm :=
  rsub (rmul (rlineC l₂) (rsub l₁.2.2 l₁.1.2)) (rmul (rlineC l₁) (rsub l₂.2.2 l₂.1.2))

/-- The intersection point of two non-parallel lines. -/
def rinter (l₁ l₂ : RPt × RPt) : RPt :=
  (rdiv (rlineNumX l₁ l₂) (rlineDen l₁ l₂), rdiv (rlineNumY l₁ l₂) (rlineDen l₁ l₂))

/-- The centroid of three points. -/
def rcentroid (a b c : RPt) : RPt :=
  (rdiv (radd (radd a.1 b.1) c.1) rthree, rdiv (radd (radd a.2 b.2) c.2) rthree)

/-- Both points of a line are represented. -/
def LRep (x : ℕ → ℝ) (l : RPt × RPt) (l' : Point × Point) : Prop :=
  PRep x l.1 l'.1 ∧ PRep x l.2 l'.2

theorem PRep.guard (x : ℕ → ℝ) (a : ℕ) : PRep x (rguard a) (guardPt x a) := PRep.var x _

theorem lrep_rline (hC : CornersRep x P C) {g i : ℕ} (hi : i < numLines P.n g) :
    LRep x (rline C i) (lineR P (guardPt x) i) := by
  unfold rline lineR
  rw [hC.1]
  split_ifs with h
  · exact ⟨hC.vtx h, hC.next' h⟩
  · have hn : 0 < P.n := by
      rcases Nat.eq_zero_or_pos P.n with h0 | h0
      · rw [h0] at hi h; simp [numLines] at hi
      · exact h0
    exact ⟨PRep.guard x _, hC.vtx (Nat.mod_lt _ hn)⟩

theorem Rep.lineDen {l₁ l₂ : RPt × RPt} {l₁' l₂' : Point × Point} (h₁ : LRep x l₁ l₁')
    (h₂ : LRep x l₂ l₂') : Rep x (rlineDen l₁ l₂) (lineDenR l₁' l₂') :=
  Rep.cross h₁.1 h₁.2 h₂.1 h₂.2

theorem Rep.lineC {l : RPt × RPt} {l' : Point × Point} (h : LRep x l l') :
    Rep x (rlineC l) (lineCR l') :=
  (h.1.1.mul h.2.2).sub (h.1.2.mul h.2.1)

theorem PRep.inter {l₁ l₂ : RPt × RPt} {l₁' l₂' : Point × Point} (h₁ : LRep x l₁ l₁')
    (h₂ : LRep x l₂ l₂') (hD : lineDenR l₁' l₂' ≠ 0) :
    PRep x (rinter l₁ l₂) (lineNumXR l₁' l₂' / lineDenR l₁' l₂',
      lineNumYR l₁' l₂' / lineDenR l₁' l₂') :=
  ⟨Rep.div (((Rep.lineC h₂).mul (h₁.2.1.sub h₁.1.1)).sub ((Rep.lineC h₁).mul (h₂.2.1.sub h₂.1.1)))
      (Rep.lineDen h₁ h₂) hD,
    Rep.div (((Rep.lineC h₂).mul (h₁.2.2.sub h₁.1.2)).sub ((Rep.lineC h₁).mul (h₂.2.2.sub h₂.1.2)))
      (Rep.lineDen h₁ h₂) hD⟩

theorem PRep.centroid {a b c : RPt} {a' b' c' : Point} (ha : PRep x a a') (hb : PRep x b b')
    (hc : PRep x c c') : PRep x (rcentroid a b c) (Membership.centroid a' b' c') :=
  ⟨Rep.div ((ha.1.add hb.1).add hc.1) (Rep.three x) three_ne_zero,
    Rep.div ((ha.2.add hb.2).add hc.2) (Rep.three x) three_ne_zero⟩

/-! ## The formula -/

/-- Line number `k` of the witness `L` (`k`-th base-`m` digit). -/
def wLine (C : List RPt) (g L k : ℕ) : RPt × RPt := rline C (lamC (numLines C.length g) L k)

/-- The `k`-th denominator of the witness `L`. -/
def wDen (C : List RPt) (g L k : ℕ) : RTerm := rlineDen (wLine C g L (2 * k)) (wLine C g L (2 * k + 1))

/-- The `k`-th arrangement vertex of the witness `L`. -/
def wPt (C : List RPt) (g L k : ℕ) : RPt := rinter (wLine C g L (2 * k)) (wLine C g L (2 * k + 1))

/-- The witness point `L`: the centroid of three arrangement vertices. -/
def wCen (C : List RPt) (g L : ℕ) : RPt := rcentroid (wPt C g L 0) (wPt C g L 1) (wPt C g L 2)

/-- The condition for the witness `L`. -/
def rwitF (C : List RPt) (g L : ℕ) : Formula :=
  fImp (.and (rneF (wDen C g L 0)) (.and (rneF (wDen C g L 1)) (rneF (wDen C g L 2))))
    (fImp (rinsideF C (wCen C g L))
      (bigOr ((List.range g).map fun a => rseesF C (rguard a) (wCen C g L))))

/-- **GUARDS**: the `g` guards are in the region and see every witness point. -/
def rguardsF (C : List RPt) (g : ℕ) : Formula :=
  .and (bigAnd ((List.range g).map fun a => rinsideF C (rguard a)))
    (bigAnd ((List.range (numLines C.length g ^ 6)).map (rwitF C g)))

/-! ## Soundness -/

/-- The guard points as a list. -/
def guardPts (x : ℕ → ℝ) (g : ℕ) : List Point := (List.range g).map (guardPt x)

theorem mem_arrangementLines' {g : ℕ} {l : Point × Point}
    (hl : l ∈ arrangementLines P (guardPts x g)) :
    ∃ i < numLines P.n g, l = lineR P (guardPt x) i := by
  unfold arrangementLines at hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hj
    exact ⟨j, by unfold numLines; omega, by simp [lineR, hj]⟩
  · obtain ⟨γ, hγ, hl⟩ := List.mem_flatMap.1 hl
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
    rw [List.mem_range] at ha
    refine ⟨P.n + a * P.n + k, ?_, ?_⟩
    · have := pair_lt ha hk
      unfold numLines; omega
    · have h1 : ¬ (P.n + a * P.n + k < P.n) := by omega
      have h2 : P.n + a * P.n + k - P.n = a * P.n + k := by omega
      simp only [lineR, h1, ite_false, h2, pair_div hk, pair_mod hk]

theorem lamC_lamEnc_six {m : ℕ} {i₁ j₁ i₂ j₂ i₃ j₃ : ℕ} (h₁ : i₁ < m) (h₂ : j₁ < m) (h₃ : i₂ < m)
    (h₄ : j₂ < m) (h₅ : i₃ < m) (h₆ : j₃ < m) :
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 0 = i₁ ∧
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 1 = j₁ ∧
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 2 = i₂ ∧
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 3 = j₂ ∧
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 4 = i₃ ∧
    lamC m (lamEnc m [i₁, j₁, i₂, j₂, i₃, j₃]) 5 = j₃ ∧
    True := by
  refine ⟨lamC_enc_zero h₁ _, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [lamC_enc_cons h₁]; exact lamC_enc_zero h₂ _
  · rw [lamC_enc_cons h₁, lamC_enc_cons h₂]; exact lamC_enc_zero h₃ _
  · rw [lamC_enc_cons h₁, lamC_enc_cons h₂, lamC_enc_cons h₃]; exact lamC_enc_zero h₄ _
  · rw [lamC_enc_cons h₁, lamC_enc_cons h₂, lamC_enc_cons h₃, lamC_enc_cons h₄]
    exact lamC_enc_zero h₅ _
  · rw [lamC_enc_cons h₁, lamC_enc_cons h₂, lamC_enc_cons h₃, lamC_enc_cons h₄,
      lamC_enc_cons h₅]
    exact lamC_enc_zero h₆ _

/-- Semantics of the witness formula for given digits. -/
theorem holds_rwitF_of {hP : P.Simple} (hC : CornersRep x P C) {g L : ℕ} {i₁ j₁ i₂ j₂ i₃ j₃ : ℕ}
    (hm : ∀ i ∈ [i₁, j₁, i₂, j₂, i₃, j₃], i < numLines P.n g)
    (hL : L = lamEnc (numLines P.n g) [i₁, j₁, i₂, j₂, i₃, j₃])
    {a₁ a₂ a₃ : Point}
    (e₁ : lineInter (lineR P (guardPt x) i₁) (lineR P (guardPt x) j₁) = some a₁)
    (e₂ : lineInter (lineR P (guardPt x) i₂) (lineR P (guardPt x) j₂) = some a₂)
    (e₃ : lineInter (lineR P (guardPt x) i₃) (lineR P (guardPt x) j₃) = some a₃)
    (h : (rwitF C g L).Holds x) (hin : Membership.centroid a₁ a₂ a₃ ∈ P.filled) :
    ∃ a < g, P.Sees (guardPt x a) (Membership.centroid a₁ a₂ a₃) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hm
  obtain ⟨c0, c1, c2, c3, c4, c5, -⟩ := lamC_lamEnc_six hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1
    hm.2.2.2.2.1 hm.2.2.2.2.2
  rw [← hL] at c0 c1 c2 c3 c4 c5
  have hl : ∀ k, ∀ i, lamC (numLines P.n g) L k = i → i < numLines P.n g →
      LRep x (wLine C g L k) (lineR P (guardPt x) i) := by
    intro k i hk hi
    rw [wLine, hC.1, hk]
    exact lrep_rline hC hi
  have hpt : ∀ k i j a, lamC (numLines P.n g) L (2 * k) = i →
      lamC (numLines P.n g) L (2 * k + 1) = j → i < numLines P.n g → j < numLines P.n g →
      lineInter (lineR P (guardPt x) i) (lineR P (guardPt x) j) = some a →
      lineDenR (lineR P (guardPt x) i) (lineR P (guardPt x) j) ≠ 0 ∧
      Rep x (wDen C g L k) (lineDenR (lineR P (guardPt x) i) (lineR P (guardPt x) j)) ∧
      PRep x (wPt C g L k) a := by
    intro k i j a hi hj hi' hj' he
    have h1 := hl _ _ hi hi'
    have h2 := hl _ _ hj hj'
    rw [lineInter_eq] at he
    split_ifs at he with hD
    cases he
    exact ⟨hD, Rep.lineDen h1 h2, PRep.inter h1 h2 hD⟩
  obtain ⟨hD₁, hR₁, hP₁⟩ := hpt 0 i₁ j₁ a₁ c0 c1 hm.1 hm.2.1 e₁
  obtain ⟨hD₂, hR₂, hP₂⟩ := hpt 1 i₂ j₂ a₂ c2 c3 hm.2.2.1 hm.2.2.2.1 e₂
  obtain ⟨hD₃, hR₃, hP₃⟩ := hpt 2 i₃ j₃ a₃ c4 c5 hm.2.2.2.2.1 hm.2.2.2.2.2 e₃
  have hu : PRep x (wCen C g L) (Membership.centroid a₁ a₂ a₃) := PRep.centroid hP₁ hP₂ hP₃
  rw [rwitF, holds_fImp, holds_and, holds_and, holds_rneF hR₁, holds_rneF hR₂, holds_rneF hR₃,
    holds_fImp, holds_rinsideF hP hC hu, holds_bigOr_range] at h
  obtain ⟨a, ha, hs⟩ := h ⟨hD₁, hD₂, hD₃⟩ hin
  exact ⟨a, ha, (holds_rseesF hP hC (PRep.guard x a) hu).1 hs⟩

/-- **GUARDS is sound**: the guards of a satisfying assignment lie in the region and guard it. -/
theorem guards_of_holds_rguardsF (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (h : (rguardsF C g).Holds x) :
    (∀ γ ∈ guardPts x g, γ ∈ P.filled) ∧ ∀ p ∈ P.filled, ∃ γ ∈ guardPts x g, P.Sees γ p := by
  obtain ⟨hg, hw⟩ := h
  rw [holds_bigAnd_range] at hg hw
  have hΓ : ∀ γ ∈ guardPts x g, γ ∈ P.filled := by
    intro γ hγ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
    rw [List.mem_range] at ha
    exact (holds_rinsideF hP hC (PRep.guard x a)).1 (hg a ha)
  refine ⟨hΓ, guards_of_witnesses hP _ hΓ ?_⟩
  have hvert : ∀ a ∈ arrangementVertices (arrangementLines P (guardPts x g)),
      ∃ i < numLines P.n g, ∃ j < numLines P.n g,
        lineInter (lineR P (guardPt x) i) (lineR P (guardPt x) j) = some a := by
    rintro a ⟨l₁, hl₁, l₂, hl₂, ha⟩
    obtain ⟨i, hi, rfl⟩ := mem_arrangementLines' hl₁
    obtain ⟨j, hj, rfl⟩ := mem_arrangementLines' hl₂
    exact ⟨i, hi, j, hj, ha⟩
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ hcen
  obtain ⟨i₁, hi₁, j₁, hj₁, e₁⟩ := hvert a₁ ha₁
  obtain ⟨i₂, hi₂, j₂, hj₂, e₂⟩ := hvert a₂ ha₂
  obtain ⟨i₃, hi₃, j₃, hj₃, e₃⟩ := hvert a₃ ha₃
  have hm : ∀ i ∈ [i₁, j₁, i₂, j₂, i₃, j₃], i < numLines P.n g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  have hLlt : lamEnc (numLines P.n g) [i₁, j₁, i₂, j₂, i₃, j₃] < numLines C.length g ^ 6 := by
    rw [hC.1]; exact lamEnc_lt _ hm
  obtain ⟨a, ha, hs⟩ := holds_rwitF_of (hP := hP) hC hm rfl e₁ e₂ e₃ (hw _ hLlt) hcen
  exact ⟨guardPt x a, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩, hs⟩

/-! ## Completeness -/

/-- **GUARDS is complete**: if the guard points `guardPt x a` (`a < g`) lie in the region and
guard it, the formula holds. -/
theorem holds_rguardsF_of_guards (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (hin : ∀ a < g, guardPt x a ∈ P.filled)
    (hsees : ∀ p ∈ P.filled, ∃ a < g, P.Sees (guardPt x a) p) :
    (rguardsF C g).Holds x := by
  refine ⟨?_, ?_⟩
  · rw [holds_bigAnd_range]
    intro a ha
    exact (holds_rinsideF hP hC (PRep.guard x a)).2 (hin a ha)
  · rw [holds_bigAnd_range]
    intro L hL
    have hm0 : 0 < numLines C.length g := by
      rcases Nat.eq_zero_or_pos (numLines C.length g) with h | h
      · rw [h] at hL; simp at hL
      · exact h
    have hlt : ∀ k, lamC (numLines C.length g) L k < numLines P.n g := fun k => by
      rw [← hC.1]; exact lamC_lt hm0 L k
    have hl : ∀ k, LRep x (wLine C g L k) (lineR P (guardPt x) (lamC (numLines C.length g) L k)) :=
      fun k => lrep_rline hC (hlt k)
    rw [rwitF, holds_fImp]
    rintro ⟨h1, h2, h3⟩
    have hk : ∀ k, (rneF (wDen C g L k)).Holds x →
        ∃ a, lineDenR (lineR P (guardPt x) (lamC (numLines C.length g) L (2 * k)))
          (lineR P (guardPt x) (lamC (numLines C.length g) L (2 * k + 1))) ≠ 0 ∧
          PRep x (wPt C g L k) a := by
      intro k hk
      have hR := Rep.lineDen (hl (2 * k)) (hl (2 * k + 1))
      rw [wDen, holds_rneF hR] at hk
      exact ⟨_, hk, PRep.inter (hl (2 * k)) (hl (2 * k + 1)) hk⟩
    obtain ⟨b₁, -, hb₁⟩ := hk 0 h1
    obtain ⟨b₂, -, hb₂⟩ := hk 1 h2
    obtain ⟨b₃, -, hb₃⟩ := hk 2 h3
    have hu : PRep x (wCen C g L) _ := PRep.centroid hb₁ hb₂ hb₃
    rw [holds_fImp, holds_rinsideF hP hC hu, holds_bigOr_range]
    intro hu'
    obtain ⟨a, ha, hs⟩ := hsees _ hu'
    exact ⟨a, ha, (holds_rseesF hP hC (PRep.guard x a) hu).2 hs⟩

/-! ## Variables -/

theorem FVars_rguardsF {g : ℕ} (hC : CornersV (· < 2 * g) C) : FVars (· < 2 * g) (rguardsF C g) := by
  have hγ : ∀ a < g, PV (· < 2 * g) (rguard a) := fun a ha =>
    PV.var (show 2 * a < 2 * g by omega) (show 2 * a + 1 < 2 * g by omega)
  refine ⟨?_, ?_⟩
  · rw [FVars_bigAnd]
    intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
    exact FVars_rinsideF hC (hγ a (List.mem_range.1 ha))
  · rw [FVars_bigAnd]
    intro φ hφ
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hφ
    rw [List.mem_range] at hL
    have hm0 : 0 < numLines C.length g := by
      rcases Nat.eq_zero_or_pos (numLines C.length g) with h | h
      · rw [h] at hL; simp at hL
      · exact h
    have hl : ∀ k, PV (· < 2 * g) (wLine C g L k).1 ∧ PV (· < 2 * g) (wLine C g L k).2 := by
      intro k
      have hi := lamC_lt hm0 L k
      unfold wLine rline
      generalize lamC (numLines C.length g) L k = i at hi ⊢
      unfold numLines at hi
      split_ifs with h
      · exact ⟨hC _, hC _⟩
      · refine ⟨hγ _ ?_, hC _⟩
        have hn : 0 < C.length := by
          rcases Nat.eq_zero_or_pos C.length with h0 | h0
          · rw [h0] at hi h; simp at hi
          · exact h0
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_comm]; omega
    have hC' : ∀ l : RPt × RPt, PV (· < 2 * g) l.1 ∧ PV (· < 2 * g) l.2 →
        RVars (· < 2 * g) (rlineC l) := fun l h =>
      (h.1.1.mul h.2.2).sub (h.1.2.mul h.2.1)
    have hden : ∀ k, RVars (· < 2 * g) (wDen C g L k) := fun k =>
      RVars.cross (hl _).1 (hl _).2 (hl _).1 (hl _).2
    have hpt : ∀ k, PV (· < 2 * g) (wPt C g L k) := fun k =>
      ⟨RVars.div (((hC' _ (hl _)).mul ((hl _).2.1.sub (hl _).1.1)).sub
          ((hC' _ (hl _)).mul ((hl _).2.1.sub (hl _).1.1))) (hden k),
        RVars.div (((hC' _ (hl _)).mul ((hl _).2.2.sub (hl _).1.2)).sub
          ((hC' _ (hl _)).mul ((hl _).2.2.sub (hl _).1.2))) (hden k)⟩
    have hu : PV (· < 2 * g) (wCen C g L) :=
      ⟨RVars.div (((hpt 0).1.add (hpt 1).1).add (hpt 2).1) RVars.three,
        RVars.div (((hpt 0).2.add (hpt 1).2).add (hpt 2).2) RVars.three⟩
    refine ⟨⟨FVars_rneF (hden 0), FVars_rneF (hden 1), FVars_rneF (hden 2)⟩,
      FVars_rinsideF hC hu, ?_⟩
    rw [FVars_bigOr]
    intro ψ hψ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hψ
    exact FVars_rseesF hC (hγ a (List.mem_range.1 ha)) hu

end ArtGallery.FewVars

end
