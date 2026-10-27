module

public import ArtGallery.Membership.Combinators
public import ArtGallery.Jordan.Jordan

/-!
# The formula INSIDE

For a point given by terms `q`:

* `onSegF q a b`: `q` lies on the segment `[a, b]` (`det a b q = 0 ∧ (q - a) · (q - b) ≤ 0`);
* `onBoundaryF n q`: `q` lies on an edge of the polygon in the vertex variables;
* `crossesF q u v`: the edge `[u, v]` crosses the upward vertical ray from `q`
  (`ArtGallery.Jordan.crosses`, literally);
* `parDefF n q base`: the fresh variables `π_e = x_{base + e - 1}` (`π_0 = 1`) satisfy
  `π_{e+1} = -π_e` if edge `e` crosses the ray from `q`, and `π_{e+1} = π_e` otherwise, so that
  `π_n = (-1)^(number of crossings)`;
* `insideF n q base`: `q` is on the boundary or `π_n = -1`.

For a simple polygon and an assignment satisfying `parDefF`, `insideF` holds iff `q ∈ P.filled`
(`holds_insideF`, from the Jordan library: off the boundary, membership is odd crossing parity).
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR Geometry

/-! ## Points on a segment -/

/-- A point lies on the segment `[a, b]` iff it is collinear with `a, b` and the vectors to the
endpoints have non-positive scalar product. -/
theorem mem_segment_iff_det_dot {a b q : Point} :
    q ∈ ArtGallery.segment a b ↔ det a b q = 0 ∧ dotR a q b q ≤ 0 := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨by unfold det; ring, ?_⟩
    have : dotR a (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) b
        (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) =
        t * (t - 1) * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
      unfold dotR; ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith))
      (by positivity)
  · rintro ⟨hdet, hdot⟩
    unfold det at hdet
    unfold dotR at hdot
    by_cases hL : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 = 0
    · have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
      have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
      have hq : (q.1 - a.1) ^ 2 + (q.2 - a.2) ^ 2 ≤ 0 := by
        have e1 : q.1 - b.1 = q.1 - a.1 := by linarith
        have e2 : q.2 - b.2 = q.2 - a.2 := by linarith
        rw [e1, e2] at hdot; nlinarith
      have q1 : q.1 - a.1 = 0 := by nlinarith [sq_nonneg (q.1 - a.1), sq_nonneg (q.2 - a.2)]
      have q2 : q.2 - a.2 = 0 := by nlinarith [sq_nonneg (q.1 - a.1), sq_nonneg (q.2 - a.2)]
      refine ⟨0, le_rfl, zero_le_one, ?_⟩
      ext <;> simp <;> linarith
    · have hLpos : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hL)
      set L := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 with hLdef
      set r := (q.1 - a.1) * (b.1 - a.1) + (q.2 - a.2) * (b.2 - a.2) with hrdef
      set t := r / L with htdef
      have ht : t * L = r := div_mul_cancel₀ _ hL
      have hq1 : L * (q.1 - a.1) = r * (b.1 - a.1) := by
        rw [hLdef, hrdef]; linear_combination (-(b.2 - a.2)) * hdet
      have hq2 : L * (q.2 - a.2) = r * (b.2 - a.2) := by
        rw [hLdef, hrdef]; linear_combination (b.1 - a.1) * hdet
      have hq1' : q.1 = a.1 + t * (b.1 - a.1) := by
        have : L * (q.1 - a.1 - t * (b.1 - a.1)) = 0 := by
          linear_combination hq1 - (b.1 - a.1) * ht
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hL
        · linarith
      have hq2' : q.2 = a.2 + t * (b.2 - a.2) := by
        have : L * (q.2 - a.2 - t * (b.2 - a.2)) = 0 := by
          linear_combination hq2 - (b.2 - a.2) * ht
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hL
        · linarith
      have hd : t * (t - 1) * L ≤ 0 := by
        have : (q.1 - a.1) * (q.1 - b.1) + (q.2 - a.2) * (q.2 - b.2) = t * (t - 1) * L := by
          rw [hq1', hq2', hLdef]; ring
        linarith
      have htt : t * (t - 1) ≤ 0 := by
        by_contra h
        have := mul_pos (not_le.1 h) hLpos
        linarith
      refine ⟨t, by nlinarith, by nlinarith, ?_⟩
      ext
      · exact hq1'
      · exact hq2'

/-- A point collinear with `u, w` whose scalar product condition is an equality is an endpoint. -/
theorem eq_or_eq_of_det_dot_zero {u w q : Point} (h1 : det u w q = 0) (h2 : dotR u q w q = 0) :
    q = u ∨ q = w := by
  unfold det at h1
  unfold dotR at h2
  have hd : (q.1 - u.1) * (q.2 - w.2) - (q.2 - u.2) * (q.1 - w.1) = 0 := by
    linear_combination h1
  have key : ((q.1 - u.1) ^ 2 + (q.2 - u.2) ^ 2) * ((q.1 - w.1) ^ 2 + (q.2 - w.2) ^ 2) = 0 := by
    linear_combination ((q.1 - u.1) * (q.1 - w.1) + (q.2 - u.2) * (q.2 - w.2)) * h2 +
      ((q.1 - u.1) * (q.2 - w.2) - (q.2 - u.2) * (q.1 - w.1)) * hd
  rcases mul_eq_zero.1 key with h | h
  · left
    have a1 : q.1 - u.1 = 0 := by nlinarith [sq_nonneg (q.1 - u.1), sq_nonneg (q.2 - u.2)]
    have a2 : q.2 - u.2 = 0 := by nlinarith [sq_nonneg (q.1 - u.1), sq_nonneg (q.2 - u.2)]
    ext <;> linarith
  · right
    have a1 : q.1 - w.1 = 0 := by nlinarith [sq_nonneg (q.1 - w.1), sq_nonneg (q.2 - w.2)]
    have a2 : q.2 - w.2 = 0 := by nlinarith [sq_nonneg (q.1 - w.1), sq_nonneg (q.2 - w.2)]
    ext <;> linarith

/-! ## Formulas -/

/-- `q` lies on the segment `[a, b]`. -/
def onSegF (q a b : PTerm) : Formula :=
  .and (.eq (detT a b q) .zero) (.le (dotT a q b q) .zero)

theorem holds_onSegF (x : ℕ → ℝ) (q a b : PTerm) :
    (onSegF q a b).Holds x ↔ q.eval x ∈ ArtGallery.segment (a.eval x) (b.eval x) := by
  rw [mem_segment_iff_det_dot]
  simp [onSegF]

/-- `q` lies on the boundary of the polygon with `n` vertices in the vertex variables. -/
def onBoundaryF (n : ℕ) (q : PTerm) : Formula :=
  bigOr ((List.range n).map fun j => onSegF q (vt j) (vt ((j + 1) % n)))

theorem holds_onBoundaryF {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) (q : PTerm) :
    (onBoundaryF P.n q).Holds x ↔ q.eval x ∈ P.boundary := by
  rw [onBoundaryF, holds_bigOr_range]
  simp only [holds_onSegF]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [hx j hj, hx _ (succ_mod_lt hj)] at h
    exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨j, hj, ?_⟩
    rw [hx j hj, hx _ (succ_mod_lt hj)]
    exact h

/-- The edge `[u, v]` crosses the upward vertical ray from `z` (`ArtGallery.Jordan.crosses`). -/
def crossesF (z u v : PTerm) : Formula :=
  .or (.and (.le u.1 z.1) (.and (.lt z.1 v.1)
        (.lt (.mul (.sub z.2 u.2) (.sub v.1 u.1)) (.mul (.sub v.2 u.2) (.sub z.1 u.1)))))
    (.and (.le v.1 z.1) (.and (.lt z.1 u.1)
        (.lt (.mul (.sub z.2 v.2) (.sub u.1 v.1)) (.mul (.sub u.2 v.2) (.sub z.1 v.1)))))

theorem holds_crossesF (x : ℕ → ℝ) (z u v : PTerm) :
    (crossesF z u v).Holds x ↔ Jordan.crosses (z.eval x) (u.eval x) (v.eval x) := by
  simp only [crossesF, holds_or, holds_and, holds_le, holds_lt, eval_mul, eval_sub,
    Jordan.crosses, PTerm.eval_fst, PTerm.eval_snd]

/-- The parity products: `π_0 = 1` and `π_{e+1} = x_{base + e}`. -/
def piT (base : ℕ) : ℕ → Term
  | 0 => .one
  | e + 1 => .var (base + e)

/-- Step `e` of the parity computation. -/
def parStepF (n : ℕ) (q : PTerm) (base e : ℕ) : Formula :=
  .or (.and (crossesF q (vt e) (vt ((e + 1) % n)))
        (.eq (piT base (e + 1)) (.sub .zero (piT base e))))
    (.and (.not (crossesF q (vt e) (vt ((e + 1) % n)))) (.eq (piT base (e + 1)) (piT base e)))

/-- The parity variables `x_{base}, …, x_{base + n - 1}` of the point `q`. -/
def parDefF (n : ℕ) (q : PTerm) (base : ℕ) : Formula :=
  bigAnd ((List.range n).map (parStepF n q base))

/-- **INSIDE**: `q` is on the boundary, or has odd crossing parity (`π_n = -1`). -/
def insideF (n : ℕ) (q : PTerm) (base : ℕ) : Formula :=
  .or (onBoundaryF n q) (.eq (piT base n) (.sub .zero .one))

/-! ## The sign products -/

/-- `(-1)` to the number of edges among the first `k` crossing the upward ray from `z`. -/
noncomputable def signProd (P : Polygon) (z : Point) (k : ℕ) : ℝ :=
  ∏ e ∈ Finset.range k, (if Jordan.crosses z (P.vtx e) (P.vtx ((e + 1) % P.n)) then -1 else 1)

theorem signProd_succ (P : Polygon) (z : Point) (k : ℕ) :
    signProd P z (k + 1) =
      signProd P z k * (if Jordan.crosses z (P.vtx k) (P.vtx ((k + 1) % P.n)) then -1 else 1) :=
  Finset.prod_range_succ _ _

theorem signProd_zero (P : Polygon) (z : Point) : signProd P z 0 = 1 := by
  simp [signProd]

theorem zmod2_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

theorem signProd_eq (P : Polygon) (z : Point) (k : ℕ) :
    signProd P z k = if (∑ e ∈ Finset.range k,
      Jordan.crossInd z (P.vtx e) (P.vtx ((e + 1) % P.n))) = 1 then -1 else 1 := by
  have e0 : (0 : ZMod 2) ≠ 1 := by decide
  have e1 : (0 : ZMod 2) + 1 = 1 := by decide
  have e2 : (1 : ZMod 2) + 1 ≠ 1 := by decide
  induction k with
  | zero => simp [signProd_zero, e0]
  | succ k ih =>
    rw [signProd_succ, Finset.sum_range_succ, ih]
    generalize (∑ e ∈ Finset.range k, Jordan.crossInd z (P.vtx e) (P.vtx ((e + 1) % P.n))) = s
    by_cases hc : Jordan.crosses z (P.vtx k) (P.vtx ((k + 1) % P.n))
    · rw [Jordan.crossInd_of_crosses hc, ite_eq_left hc]
      rcases zmod2_cases s with rfl | rfl
      · simp [e0, e1]
      · simp [e2]
    · rw [Jordan.crossInd_of_not_crosses hc, ite_eq_right hc, add_zero, mul_one]

theorem signProd_eq_neg_one_iff (P : Polygon) (z : Point) :
    signProd P z P.n = -1 ↔ Jordan.parity P z = true := by
  rw [signProd_eq, Jordan.parity_eq_true_iff, Jordan.crossSum]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; norm_num

/-! ## Semantics -/

theorem piT_eval_of_parDef {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {q : PTerm} {base : ℕ}
    (h : (parDefF P.n q base).Holds x) :
    ∀ k ≤ P.n, (piT base k).eval x = signProd P (q.eval x) k := by
  rw [parDefF, holds_bigAnd_range] at h
  intro k hk
  induction k with
  | zero => simp [piT, signProd_zero]
  | succ k ih =>
    have hs := h k (by omega)
    have ih := ih (by omega)
    rw [signProd_succ, ← ih]
    simp only [parStepF, holds_or, holds_and, holds_not, holds_crossesF, holds_eq, eval_sub,
      eval_zero, hx k (by omega), hx _ (succ_mod_lt (show k < P.n by omega))] at hs
    rcases hs with ⟨hc, he⟩ | ⟨hc, he⟩
    · rw [ite_eq_left hc, he]; ring
    · rw [ite_eq_right hc, he]; ring

/-- **INSIDE is exact**: for a simple polygon, if the parity variables of `q` are defined,
`insideF` holds iff `q` lies in the closed region. -/
theorem holds_insideF {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x) {q : PTerm}
    {base : ℕ} (h : (parDefF P.n q base).Holds x) :
    (insideF P.n q base).Holds x ↔ q.eval x ∈ P.filled := by
  rw [insideF, holds_or, holds_onBoundaryF hx, holds_eq, piT_eval_of_parDef hx h _ le_rfl]
  simp only [eval_sub, eval_zero, eval_one, zero_sub]
  rw [signProd_eq_neg_one_iff]
  by_cases hb : q.eval x ∈ P.boundary
  · simp only [hb, true_or, true_iff]
    exact Jordan.boundary_subset_filled P hb
  · simp only [hb, false_or]
    exact (Jordan.mem_filled_iff hP hb).symm

/-- The parity variables can always be defined. -/
theorem exists_parDef {P : Polygon} {x : ℕ → ℝ} (hx : VtxOK P x) {q : PTerm} {base : ℕ}
    (hq : PVars (· < base) q) (hb : 2 * P.n ≤ base) :
    ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ (parDefF P.n q base).Holds y := by
  set z := q.eval x
  let y : ℕ → ℝ := fun v => if base ≤ v then signProd P z (v - base + 1) else x v
  have hy : ∀ v < base, y v = x v := fun v hv => by simp [y, not_le.2 hv]
  have hyq : q.eval y = z := PTerm.eval_congr (S := (· < base)) hy hq
  have hyx : VtxOK P y := hx.congr fun v hv => hy v (by omega)
  have hpi : ∀ e, (piT base e).eval y = signProd P z e := by
    intro e
    cases e with
    | zero => simp [piT, signProd_zero]
    | succ e => simp [piT, y]
  refine ⟨y, hy, ?_⟩
  rw [parDefF, holds_bigAnd_range]
  intro e he
  simp only [parStepF, holds_or, holds_and, holds_not, holds_crossesF, holds_eq, eval_sub,
    eval_zero, hyq, hyx e he, hyx _ (succ_mod_lt he), hpi, signProd_succ]
  by_cases hc : Jordan.crosses z (P.vtx e) (P.vtx ((e + 1) % P.n))
  · left; exact ⟨hc, by rw [ite_eq_left hc]; ring⟩
  · right; exact ⟨hc, by rw [ite_eq_right hc]; ring⟩

/-! ## Variables -/

theorem FVars_onSegF {S : ℕ → Prop} {q a b : PTerm} (hq : PVars S q) (ha : PVars S a)
    (hb : PVars S b) : FVars S (onSegF q a b) :=
  ⟨⟨TVars_detT ha hb hq, trivial⟩, ⟨TVars_dotT ha hq hb hq, trivial⟩⟩

theorem FVars_onBoundaryF {S : ℕ → Prop} {n : ℕ} {q : PTerm} (hq : PVars S q)
    (hv : VtxVars S n) : FVars S (onBoundaryF n q) := by
  rw [onBoundaryF, FVars_bigOr]
  intro φ hφ
  simp only [List.mem_map, List.mem_range] at hφ
  obtain ⟨j, hj, rfl⟩ := hφ
  exact FVars_onSegF hq (hv.pv hj) (hv.pv (succ_mod_lt hj))

theorem FVars_crossesF {S : ℕ → Prop} {z u v : PTerm} (hz : PVars S z) (hu : PVars S u)
    (hv : PVars S v) : FVars S (crossesF z u v) :=
  ⟨⟨⟨hu.1, hz.1⟩, ⟨hz.1, hv.1⟩, ⟨⟨hz.2, hu.2⟩, ⟨hv.1, hu.1⟩⟩, ⟨⟨hv.2, hu.2⟩, ⟨hz.1, hu.1⟩⟩⟩,
    ⟨⟨hv.1, hz.1⟩, ⟨hz.1, hu.1⟩, ⟨⟨hz.2, hv.2⟩, ⟨hu.1, hv.1⟩⟩, ⟨⟨hu.2, hv.2⟩, ⟨hz.1, hv.1⟩⟩⟩⟩

theorem TVars_piT {S : ℕ → Prop} {base k : ℕ} (h : ∀ e < k, S (base + e)) :
    TVars S (piT base k) := by
  cases k with
  | zero => trivial
  | succ k => exact h k (by omega)

theorem FVars_parDefF {S : ℕ → Prop} {n : ℕ} {q : PTerm} {base : ℕ} (hq : PVars S q)
    (hv : VtxVars S n) (hb : ∀ e < n, S (base + e)) : FVars S (parDefF n q base) := by
  rw [parDefF, FVars_bigAnd]
  intro φ hφ
  simp only [List.mem_map, List.mem_range] at hφ
  obtain ⟨e, he, rfl⟩ := hφ
  have hc := FVars_crossesF hq (hv.pv he) (hv.pv (succ_mod_lt he))
  have h1 : TVars S (piT base (e + 1)) := TVars_piT fun e' he' => hb e' (by omega)
  have h0 : TVars S (piT base e) := TVars_piT fun e' he' => hb e' (by omega)
  exact ⟨⟨hc, h1, trivial, h0⟩, ⟨hc, h1, h0⟩⟩

theorem FVars_insideF {S : ℕ → Prop} {n : ℕ} {q : PTerm} {base : ℕ} (hq : PVars S q)
    (hv : VtxVars S n) (hb : ∀ e < n, S (base + e)) : FVars S (insideF n q base) :=
  ⟨FVars_onBoundaryF hq hv, TVars_piT hb, trivial, trivial⟩

end ArtGallery.Membership

end
