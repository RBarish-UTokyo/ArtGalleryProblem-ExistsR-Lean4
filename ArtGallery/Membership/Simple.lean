module

public import ArtGallery.Membership.Combinators
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The formula SIMPLE

`simpleF n base` expresses that the polygon whose vertices are in the variables `0, …, 2n - 1`
is simple:

* `n ≥ 3` (a constant truth value);
* for every pair `(i, j)` of indices (encoded as `b = i n + j < n²`): if `i ≠ j`, vertices `i` and
  `j` are distinct, and edges `i` and `j` meet exactly in their common endpoints:
  - adjacent edges `[a, b]`, `[b, d]`: `¬(det a b d = 0 ∧ (a - b) · (d - b) > 0)`;
  - non-adjacent edges: a strictly separating line `α x + β y + c` (three fresh variables
    `base + 3b, base + 3b + 1, base + 3b + 2`), which exists exactly when the two (compact,
    convex) edges are disjoint (Hahn–Banach).

SIMPLE only occurs positively in the final formula, so the separating lines may be existentially
quantified.  Main results: `simple_of_holds` and `exists_simple_holds`.
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR Geometry

/-! ## Two adjacent edges -/

/-- Two segments `[a, b]`, `[b, d]` meet only in `b` iff they do not overlap collinearly. -/
theorem inter_adj_iff (a b d : Point) :
    ArtGallery.segment a b ∩ ArtGallery.segment b d = {b} ↔
      ¬ (det a b d = 0 ∧ 0 < dotR b a b d) := by
  have hdot' : dotR b a b d = (a.1 - b.1) * (d.1 - b.1) + (a.2 - b.2) * (d.2 - b.2) := rfl
  constructor
  · rintro h ⟨hdet, hdot⟩
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = dotR b a b d := ⟨_, rfl⟩
    rw [← hq] at hdot
    have hq' : q = (a.1 - b.1) * (d.1 - b.1) + (a.2 - b.2) * (d.2 - b.2) := hq.trans hdot'
    have hLpos : 0 < L := by
      by_contra hL0
      have hL0' : L = 0 := le_antisymm (not_lt.1 hL0) (by rw [hL]; positivity)
      rw [hL] at hL0'
      have h1 : a.1 - b.1 = 0 := by nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
      have h2 : a.2 - b.2 = 0 := by nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
      rw [hq', h1, h2] at hdot
      simp at hdot
    unfold det at hdet
    have hw1 : L * (d.1 - b.1) = q * (a.1 - b.1) := by
      rw [hq', hL]; linear_combination (a.2 - b.2) * hdet
    have hw2 : L * (d.2 - b.2) = q * (a.2 - b.2) := by
      rw [hq', hL]; linear_combination (-(a.1 - b.1)) * hdet
    have hpos : 0 < L + q := by linarith
    obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = L / (L + q) := ⟨_, rfl⟩
    have hτ : τ * (L + q) = L := by rw [hτdef]; exact div_mul_cancel₀ _ (ne_of_gt hpos)
    have hτ0 : 0 < τ := by rw [hτdef]; exact div_pos hLpos hpos
    have hτ1 : τ ≤ 1 := by rw [hτdef, div_le_one hpos]; linarith
    have hmem1 : ((b.1 + τ * (d.1 - b.1), b.2 + τ * (d.2 - b.2)) : Point) ∈
        ArtGallery.segment b d := ⟨τ, hτ0.le, hτ1, rfl⟩
    have hmem2 : ((b.1 + τ * (d.1 - b.1), b.2 + τ * (d.2 - b.2)) : Point) ∈
        ArtGallery.segment a b := by
      refine ⟨τ, hτ0.le, hτ1, ?_⟩
      have e1 : (L + q) * (b.1 + τ * (d.1 - b.1) - (a.1 + τ * (b.1 - a.1))) = 0 := by
        linear_combination (d.1 - b.1 - (b.1 - a.1)) * hτ + hw1
      have e2 : (L + q) * (b.2 + τ * (d.2 - b.2) - (a.2 + τ * (b.2 - a.2))) = 0 := by
        linear_combination (d.2 - b.2 - (b.2 - a.2)) * hτ + hw2
      rcases mul_eq_zero.1 e1 with h1 | h1
      · linarith
      rcases mul_eq_zero.1 e2 with h2 | h2
      · linarith
      ext
      · simp only; linarith
      · simp only; linarith
    have hin := h ▸ (Set.mem_inter hmem2 hmem1)
    rw [Set.mem_singleton_iff, Prod.ext_iff] at hin
    obtain ⟨h1, h2⟩ := hin
    simp only at h1 h2
    have hd1 : d.1 - b.1 = 0 := by
      rcases mul_eq_zero.1 (show τ * (d.1 - b.1) = 0 by linarith) with h | h
      · linarith
      · exact h
    have hd2 : d.2 - b.2 = 0 := by
      rcases mul_eq_zero.1 (show τ * (d.2 - b.2) = 0 by linarith) with h | h
      · linarith
      · exact h
    rw [hq', hd1, hd2] at hdot
    simp at hdot
  · intro hn
    ext p
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs0, hs1, hp1⟩, ⟨t, ht0, ht1, hp2⟩⟩
      by_contra hpb
      apply hn
      have f1 := congrArg Prod.fst hp1
      have f2 := congrArg Prod.snd hp1
      have g1 := congrArg Prod.fst hp2
      have g2 := congrArg Prod.snd hp2
      simp only at f1 f2 g1 g2
      have e1 : t * (d.1 - b.1) = (1 - s) * (a.1 - b.1) := by linarith
      have e2 : t * (d.2 - b.2) = (1 - s) * (a.2 - b.2) := by linarith
      have ht : 0 < t := by
        rcases lt_or_eq_of_le ht0 with h | h
        · exact h
        · exfalso; apply hpb; rw [hp2, ← h]; ext <;> simp
      have hs : 0 < 1 - s := by
        rcases lt_or_eq_of_le hs1 with h | h
        · linarith
        · exfalso; apply hpb; rw [hp1, h]; ext <;> simp
      have hab : 0 < (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
        by_contra hL0
        have hL0' : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 = 0 :=
          le_antisymm (not_lt.1 hL0) (by positivity)
        have h1 : a.1 - b.1 = 0 := by nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
        have h2 : a.2 - b.2 = 0 := by nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
        apply hpb
        ext
        · rw [f1]; nlinarith
        · rw [f2]; nlinarith
      constructor
      · have : t * det a b d = 0 := by
          unfold det; linear_combination (b.1 - a.1) * e2 - (b.2 - a.2) * e1
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      · have key : t * dotR b a b d = (1 - s) * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
          rw [hdot']; linear_combination (a.1 - b.1) * e1 + (a.2 - b.2) * e2
        have := mul_pos hs hab
        rw [← key] at this
        exact pos_of_mul_pos_right this ht.le
    · rintro rfl
      exact ⟨Geometry.right_mem_segment a p, Geometry.left_mem_segment p d⟩

/-! ## Separating lines -/

/-- The affine function `α x + β y + c`. -/
def linR (α β c : ℝ) (p : Point) : ℝ := α * p.1 + β * p.2 + c

theorem linR_lerp (α β c : ℝ) (p q : Point) (t : ℝ) :
    linR α β c (lerp p q t) = (1 - t) * linR α β c p + t * linR α β c q := by
  unfold linR lerp; ring

theorem linR_neg_of_mem {α β c : ℝ} {p q z : Point} (hp : linR α β c p < 0)
    (hq : linR α β c q < 0) (hz : z ∈ ArtGallery.segment p q) : linR α β c z < 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hz
  have h := linR_lerp α β c p q t
  simp only [lerp] at h
  rw [h]
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left (linR α β c p) (linR α β c q))
      (sub_nonneg.2 ht1),
    mul_le_mul_of_nonneg_left (le_max_right (linR α β c p) (linR α β c q)) ht0, max_lt hp hq]

/-- A strictly separating line makes two segments disjoint. -/
theorem disjoint_of_sep {α β c : ℝ} {p1 p2 p3 p4 : Point} (h1 : linR α β c p1 < 0)
    (h2 : linR α β c p2 < 0) (h3 : 0 < linR α β c p3) (h4 : 0 < linR α β c p4) :
    Disjoint (ArtGallery.segment p1 p2) (ArtGallery.segment p3 p4) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have A := linR_neg_of_mem h1 h2 hz
  have B := linR_neg_of_mem (α := -α) (β := -β) (c := -c) (p := p3) (q := p4)
    (by unfold linR at h3 ⊢; linarith) (by unfold linR at h4 ⊢; linarith) hz'
  unfold linR at A B
  linarith

/-- Two disjoint segments are strictly separated by a line (Hahn–Banach). -/
theorem exists_sep_of_disjoint {p1 p2 p3 p4 : Point}
    (h : Disjoint (ArtGallery.segment p1 p2) (ArtGallery.segment p3 p4)) :
    ∃ α β c : ℝ, linR α β c p1 < 0 ∧ linR α β c p2 < 0 ∧ 0 < linR α β c p3 ∧
      0 < linR α β c p4 := by
  obtain ⟨f, u, v, hu, huv, hv⟩ := geometric_hahn_banach_compact_closed
    (Geometry.segment_convex p1 p2) (Geometry.isCompact_segment p1 p2)
    (Geometry.segment_convex p3 p4) (Geometry.isClosed_segment p3 p4) h
  have hf : ∀ p : Point, f p = f ((1 : ℝ), (0 : ℝ)) * p.1 + f ((0 : ℝ), (1 : ℝ)) * p.2 := by
    intro p
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨f ((1 : ℝ), (0 : ℝ)), f ((0 : ℝ), (1 : ℝ)), -((u + v) / 2), ?_, ?_, ?_, ?_⟩
  · have := hu p1 (Geometry.left_mem_segment p1 p2); unfold linR; rw [hf] at this; linarith
  · have := hu p2 (Geometry.right_mem_segment p1 p2); unfold linR; rw [hf] at this; linarith
  · have := hv p3 (Geometry.left_mem_segment p3 p4); unfold linR; rw [hf] at this; linarith
  · have := hv p4 (Geometry.right_mem_segment p3 p4); unfold linR; rw [hf] at this; linarith

/-! ## Edges of a polygon with distinct vertices -/

section Edges

variable {P : Polygon}

/-- Vertices of `P` with distinct indices are distinct. -/
def DistinctVtx (P : Polygon) : Prop :=
  ∀ i j, i < P.n → j < P.n → P.vtx i = P.vtx j → i = j

/-- Adjacent edges `i`, `j = i + 1`. -/
theorem edge_inter_adj (hn : 3 ≤ P.n) (hd : DistinctVtx P) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) (hij : j = (i + 1) % P.n) :
    P.edge i ∩ P.edge j = P.commonEndpoints i j ↔
      ArtGallery.segment (P.vtx i) (P.vtx j) ∩
          ArtGallery.segment (P.vtx j) (P.vtx ((j + 1) % P.n)) = {P.vtx j} := by
  have hk : (j + 1) % P.n < P.n := succ_mod_lt hj
  have hne1 : i ≠ (j + 1) % P.n := by
    rcases succ_mod_cases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases succ_mod_cases hj with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  have hne2 : i ≠ j := by
    rcases succ_mod_cases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hv1 : P.vtx i ≠ P.vtx ((j + 1) % P.n) := fun h => hne1 (hd _ _ hi hk h)
  have hv2 : P.vtx i ≠ P.vtx j := fun h => hne2 (hd _ _ hi hj h)
  have hc : P.commonEndpoints i j = {P.vtx j} := by
    ext p
    simp only [Polygon.commonEndpoints, ← hij, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1 ▸ h2) hv2
      · exact absurd (h1 ▸ h2) hv1
      · exact h1
      · exact h1
    · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
  rw [hc, Polygon.edge, Polygon.edge, ← hij]

/-- Non-adjacent edges. -/
theorem edge_inter_nonadj (hd : DistinctVtx P) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (hij : i ≠ j) (h1 : j ≠ (i + 1) % P.n) (h2 : i ≠ (j + 1) % P.n) :
    P.edge i ∩ P.edge j = P.commonEndpoints i j ↔ Disjoint (P.edge i) (P.edge j) := by
  have hi' : (i + 1) % P.n < P.n := succ_mod_lt hi
  have hj' : (j + 1) % P.n < P.n := succ_mod_lt hj
  have h3 : (i + 1) % P.n ≠ (j + 1) % P.n := by
    rcases succ_mod_cases hi with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases succ_mod_cases hj with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> omega
  have hc : P.commonEndpoints i j = ∅ := by
    ext p
    simp only [Polygon.commonEndpoints, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro (e | e) (f | f) <;> subst e
    · exact hij (hd _ _ hi hj f)
    · exact h2 (hd _ _ hi hj' f)
    · exact h1 (hd _ _ hi' hj f).symm
    · exact h3 (hd _ _ hi' hj' f)
  rw [hc, Set.disjoint_iff_inter_eq_empty]

theorem commonEndpoints_comm (i j : ℕ) : P.commonEndpoints i j = P.commonEndpoints j i := by
  ext p; simp only [Polygon.commonEndpoints, Set.mem_ofPred_eq]; tauto

end Edges

/-! ## The formula -/

/-- The two point terms denote different points. -/
def ptNe (p q : PTerm) : Formula := .not (ptEq p q)

/-- Adjacent edges `[a, b]`, `[b, d]` meet only in `b`. -/
def adjF (a b d : PTerm) : Formula :=
  .not (.and (.eq (detT a b d) .zero) (.lt .zero (dotT b a b d)))

/-- The affine form `x_s · p.1 + x_{s+1} · p.2 + x_{s+2}`. -/
def linT (s : ℕ) (p : PTerm) : Term :=
  .add (.add (.mul (.var s) p.1) (.mul (.var (s + 1)) p.2)) (.var (s + 2))

/-- The line with coefficients `x_s, x_{s+1}, x_{s+2}` strictly separates `[p1, p2]` (negative
side) from `[p3, p4]` (positive side). -/
def sepF (s : ℕ) (p1 p2 p3 p4 : PTerm) : Formula :=
  .and (.lt (linT s p1) .zero)
    (.and (.lt (linT s p2) .zero) (.and (.lt .zero (linT s p3)) (.lt .zero (linT s p4))))

/-- Edges `i` and `j` meet exactly in their common endpoints (separating line in the variables
`s, s + 1, s + 2` for non-adjacent edges). -/
def edgePairF (n i j s : ℕ) : Formula :=
  if i = j then fTrue
  else if j = (i + 1) % n then adjF (vt i) (vt j) (vt ((j + 1) % n))
  else if i = (j + 1) % n then adjF (vt j) (vt i) (vt ((i + 1) % n))
  else sepF s (vt i) (vt ((i + 1) % n)) (vt j) (vt ((j + 1) % n))

/-- The conditions for the pair `(b / n, b % n)`. -/
def simplePairF (n s b : ℕ) : Formula :=
  .and (if b / n = b % n then fTrue else ptNe (vt (b / n)) (vt (b % n)))
    (edgePairF n (b / n) (b % n) s)

/-- **SIMPLE**: the polygon in the variables `0, …, 2n - 1` is simple; the separating lines use
the variables `base, …, base + 3n² - 1`. -/
def simpleF (n base : ℕ) : Formula :=
  .and (if 3 ≤ n then fTrue else fFalse)
    (bigAnd ((List.range (n * n)).map fun b => simplePairF n (base + 3 * b) b))

/-- Number of fresh variables of `simpleF n base`. -/
def simpleSize (n : ℕ) : ℕ := 3 * (n * n)

@[simp] theorem holds_ptNe (x : ℕ → ℝ) (p q : PTerm) :
    (ptNe p q).Holds x ↔ p.eval x ≠ q.eval x := by
  simp [ptNe]

theorem holds_adjF (x : ℕ → ℝ) (a b d : PTerm) :
    (adjF a b d).Holds x ↔ ¬ (det (a.eval x) (b.eval x) (d.eval x) = 0 ∧
      0 < dotR (b.eval x) (a.eval x) (b.eval x) (d.eval x)) := by
  simp [adjF]

theorem eval_linT (x : ℕ → ℝ) (s : ℕ) (p : PTerm) :
    (linT s p).eval x = linR (x s) (x (s + 1)) (x (s + 2)) (p.eval x) := by
  simp [linT, linR]

theorem holds_sepF (x : ℕ → ℝ) (s : ℕ) (p1 p2 p3 p4 : PTerm) :
    (sepF s p1 p2 p3 p4).Holds x ↔
      linR (x s) (x (s + 1)) (x (s + 2)) (p1.eval x) < 0 ∧
      linR (x s) (x (s + 1)) (x (s + 2)) (p2.eval x) < 0 ∧
      0 < linR (x s) (x (s + 1)) (x (s + 2)) (p3.eval x) ∧
      0 < linR (x s) (x (s + 1)) (x (s + 2)) (p4.eval x) := by
  simp only [sepF, holds_and, holds_lt, eval_linT, eval_zero]

/-! ## Soundness -/

theorem vtx_eval {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {k : ℕ} (hk : k < P.n) :
    (vt k).eval x = P.vtx k := hx k hk

/-- **SIMPLE is sound**: a satisfying assignment (with the vertices of `P` in the vertex
variables) witnesses that `P` is simple. -/
theorem simple_of_holds {P : Polygon} {x : ℕ → ℝ} {base : ℕ} (hx : VtxOK P x)
    (h : (simpleF P.n base).Holds x) : P.Simple := by
  obtain ⟨h3, hpairs⟩ := h
  have hn : 3 ≤ P.n := by
    by_contra hn; rw [ite_eq_right hn] at h3; exact not_holds_fFalse x h3
  rw [holds_bigAnd_range] at hpairs
  have hp : ∀ i < P.n, ∀ j < P.n, (simplePairF P.n (base + 3 * (i * P.n + j)) (i * P.n + j)).Holds x :=
    fun i hi j hj => hpairs _ (pair_lt hi hj)
  have hd : DistinctVtx P := by
    intro i j hi hj hij
    by_contra hne
    have := (hp i hi j hj).1
    rw [pair_div hj, pair_mod hj, ite_eq_right hne, holds_ptNe, hx i hi, hx j hj] at this
    exact this hij
  refine ⟨hn, hd, ?_⟩
  intro i j hi hj hij
  have he := (hp i hi j hj).2
  rw [pair_div hj, pair_mod hj] at he
  unfold edgePairF at he
  rw [ite_eq_right hij] at he
  by_cases h1 : j = (i + 1) % P.n
  · rw [ite_eq_left h1, holds_adjF, hx i hi, hx j hj, hx _ (succ_mod_lt hj)] at he
    rw [edge_inter_adj hn hd hi hj h1]
    exact (inter_adj_iff _ _ _).2 he
  rw [ite_eq_right h1] at he
  by_cases h2 : i = (j + 1) % P.n
  · rw [ite_eq_left h2, holds_adjF, hx i hi, hx j hj, hx _ (succ_mod_lt hi)] at he
    rw [Set.inter_comm, commonEndpoints_comm, edge_inter_adj hn hd hj hi h2]
    exact (inter_adj_iff _ _ _).2 he
  rw [ite_eq_right h2, holds_sepF, hx i hi, hx j hj, hx _ (succ_mod_lt hi),
    hx _ (succ_mod_lt hj)] at he
  rw [edge_inter_nonadj hd hi hj hij h1 h2]
  exact disjoint_of_sep he.1 he.2.1 he.2.2.1 he.2.2.2

/-! ## Completeness -/

theorem FVars_adjF {S : ℕ → Prop} {a b d : PTerm} (ha : PVars S a) (hb : PVars S b)
    (hd : PVars S d) : FVars S (adjF a b d) :=
  ⟨⟨TVars_detT ha hb hd, trivial⟩, ⟨trivial, TVars_dotT hb ha hb hd⟩⟩

theorem TVars_linT {S : ℕ → Prop} {s : ℕ} {p : PTerm} (hs : S s ∧ S (s + 1) ∧ S (s + 2))
    (hp : PVars S p) : TVars S (linT s p) := by
  simp only [linT, TVars_add, TVars_mul, TVars_var]
  exact ⟨⟨⟨hs.1, hp.1⟩, ⟨hs.2.1, hp.2⟩⟩, hs.2.2⟩

theorem FVars_sepF {S : ℕ → Prop} {s : ℕ} {p1 p2 p3 p4 : PTerm} (hs : S s ∧ S (s + 1) ∧ S (s + 2))
    (h1 : PVars S p1) (h2 : PVars S p2) (h3 : PVars S p3) (h4 : PVars S p4) :
    FVars S (sepF s p1 p2 p3 p4) := by
  simp only [sepF, FVars_and, FVars_lt, TVars_zero, and_true, true_and]
  exact ⟨TVars_linT hs h1, TVars_linT hs h2, TVars_linT hs h3, TVars_linT hs h4⟩

theorem FVars_simplePairF {S : ℕ → Prop} {n s b : ℕ} (hb : b < n * n) (hv : VtxVars S n)
    (hs : S s ∧ S (s + 1) ∧ S (s + 2)) : FVars S (simplePairF n s b) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hb
    · exact h
  have hi : b / n < n := Nat.div_lt_of_lt_mul hb
  have hj : b % n < n := Nat.mod_lt _ hn
  have hi' := succ_mod_lt hi
  have hj' := succ_mod_lt hj
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact FVars_fTrue S
    · exact FVars_ptEq (hv.pv hi) (hv.pv hj)
  · unfold edgePairF
    split_ifs
    · exact FVars_fTrue S
    · exact FVars_adjF (hv.pv hi) (hv.pv hj) (hv.pv hj')
    · exact FVars_adjF (hv.pv hj) (hv.pv hi) (hv.pv hi')
    · exact FVars_sepF hs (hv.pv hi) (hv.pv hi') (hv.pv hj) (hv.pv hj')

theorem FVars_simpleF {S : ℕ → Prop} {n base : ℕ} (hv : VtxVars S n)
    (hs : ∀ v, base ≤ v → v < base + simpleSize n → S v) : FVars S (simpleF n base) := by
  refine ⟨by split_ifs <;> simp, ?_⟩
  rw [FVars_bigAnd]
  intro φ hφ
  simp only [List.mem_map, List.mem_range] at hφ
  obtain ⟨b, hb, rfl⟩ := hφ
  have : 3 * b + 3 ≤ simpleSize n := by unfold simpleSize; omega
  exact FVars_simplePairF hb hv ⟨hs _ (by omega) (by omega), hs _ (by omega) (by omega),
    hs _ (by omega) (by omega)⟩

/-- An assignment updated on three consecutive variables. -/
noncomputable def upd3 (x : ℕ → ℝ) (i : ℕ) (a b c : ℝ) (v : ℕ) : ℝ :=
  if v = i then a else if v = i + 1 then b else if v = i + 2 then c else x v

/-- **SIMPLE is complete**: for a simple polygon whose vertices are in the vertex variables, the
separating-line variables can be chosen to satisfy SIMPLE. -/
theorem exists_simple_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x)
    {base : ℕ} (hbase : 2 * P.n ≤ base) :
    ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ (simpleF P.n base).Holds y := by
  obtain ⟨hn, hd, hedge⟩ := hP
  have hex : ∀ b < P.n * P.n, ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧
      (simplePairF P.n (base + 3 * b) b).Holds y := by
    intro b hb
    have hn0 : 0 < P.n := by omega
    set i := b / P.n with hi_def
    set j := b % P.n with hj_def
    have hi : i < P.n := Nat.div_lt_of_lt_mul hb
    have hj : j < P.n := Nat.mod_lt _ hn0
    have hi' := succ_mod_lt hi
    have hj' := succ_mod_lt hj
    -- the separating line, if needed
    obtain ⟨α, β, c, hsep⟩ : ∃ α β c : ℝ, (i ≠ j → j ≠ (i + 1) % P.n → i ≠ (j + 1) % P.n →
        linR α β c (P.vtx i) < 0 ∧ linR α β c (P.vtx ((i + 1) % P.n)) < 0 ∧
        0 < linR α β c (P.vtx j) ∧ 0 < linR α β c (P.vtx ((j + 1) % P.n))) := by
      by_cases hc : i ≠ j ∧ j ≠ (i + 1) % P.n ∧ i ≠ (j + 1) % P.n
      · have hdis := (edge_inter_nonadj hd hi hj hc.1 hc.2.1 hc.2.2).1 (hedge i j hi hj hc.1)
        obtain ⟨α, β, c, h⟩ := exists_sep_of_disjoint hdis
        exact ⟨α, β, c, fun _ _ _ => h⟩
      · exact ⟨0, 0, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
    let s := base + 3 * b
    refine ⟨upd3 x s α β c, fun v hv => ?_, ?_⟩
    · have : v ≠ s := by omega
      have : v ≠ s + 1 := by omega
      have : v ≠ s + 2 := by omega
      simp [upd3, *]
    have hy : VtxOK P (upd3 x s α β c) := by
      apply hx.congr
      intro v hv
      have : v ≠ s := by omega
      have : v ≠ s + 1 := by omega
      have : v ≠ s + 2 := by omega
      simp [upd3, *]
    refine ⟨?_, ?_⟩
    · show (if i = j then fTrue else ptNe (vt i) (vt j)).Holds _
      split_ifs with hij
      · exact holds_fTrue _
      · rw [holds_ptNe, hy i hi, hy j hj]
        exact fun h => hij (hd _ _ hi hj h)
    · show (edgePairF P.n i j s).Holds _
      unfold edgePairF
      split_ifs with h0 h1 h2
      · exact holds_fTrue _
      · rw [holds_adjF, hy i hi, hy j hj, hy _ hj']
        exact (inter_adj_iff _ _ _).1 ((edge_inter_adj hn hd hi hj h1).1 (hedge i j hi hj h0))
      · rw [holds_adjF, hy i hi, hy j hj, hy _ hi']
        have := hedge i j hi hj h0
        rw [Set.inter_comm, commonEndpoints_comm, edge_inter_adj hn hd hj hi h2] at this
        exact (inter_adj_iff _ _ _).1 this
      · rw [holds_sepF, hy i hi, hy j hj, hy _ hi', hy _ hj']
        have e0 : upd3 x s α β c s = α := by simp [upd3]
        have e1 : upd3 x s α β c (s + 1) = β := by simp [upd3]
        have e2 : upd3 x s α β c (s + 2) = c := by simp [upd3]
        rw [e0, e1, e2]
        exact hsep h0 h1 h2
  obtain ⟨y, hy, hall⟩ := exists_glue (x := x) (base := base) (K := 3) (N := P.n * P.n)
    (φ := fun b => simplePairF P.n (base + 3 * b) b)
    (fun b hb => FVars_simplePairF hb
      ((vtxVars_lt hbase).mono fun v hv => Or.inl hv)
      ⟨Or.inr ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩)
    hex
  refine ⟨y, hy, ?_, ?_⟩
  · rw [ite_eq_left hn]; exact holds_fTrue _
  · rw [holds_bigAnd_range]; exact hall

end ArtGallery.Membership

end
