module

public import ArtGallery.ETR.Gate
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Reduction to ETR^{1/8,+,·}_{[-1/8,1/8]} (paper §4, Theorem 16)

The systems of this step are lists of `Gate`s read with the semantics `Gate.Holds8`, in which
`one x` means `x = 1/8` (problem ETR^{1/8,+,·}).

Given a system `S` with variables `< N` and an exponent `k ≥ 2`, put `ε = 2^(-2^k)`.
`scaleSystem N k S` keeps each original variable `x` at its index (it now stands for `ε x`) and
uses the fresh variables

* `N` (`c₀ = 1/8`), `N + 1` (`z₀ = 0`, from `z₀ + z₀ = z₀`),
* `N + t` for `2 ≤ t ≤ k` (`u_t = 2^(-2^t)`: `u₂ + u₂ = c₀`, `u_{t+1} = u_t · u_t`),
* `N + k + 1 + j` for the `j`-th equation if it is a product (`w = ε² x y`).

Equations: `x = 1 ↦ x + z₀ = u_k`; `x + y = z` unchanged; `x · y = z ↦ x · y = w, u_k · z = w`.

* `scaleSystem_sound`: any solution `y` of the new system gives the solution `y / ε` of `S`
  (no range assumption).
* `scaleSystem_complete`: a solution `v` of `S` with `|v i| ≤ R` and `ε R ≤ 1/8` gives a
  solution of the new system with all values in `[-1/8, 1/8]`.
* `eps_mul_ball_le`: `ε · 2^(2^E) ≤ 1/8` for `k = E + 2`.

The general list combinator `Gate.blocks` (concatenating per-equation translations with
the equation's position as a parameter) is also used by `ArtGallery.ETR.ChainInv`.
-/

@[expose] public section

namespace ArtGallery.Gate

/-! ## Indexed concatenation -/

/-- `blocks f j [a₀, a₁, …] = f j a₀ ++ f (j + 1) a₁ ++ …`. -/
def blocks {α β : Type} (f : ℕ → α → List β) : ℕ → List α → List β
  | _, [] => []
  | j, a :: l => f j a ++ blocks f (j + 1) l

theorem mem_blocks {α β : Type} {f : ℕ → α → List β} {j : ℕ} {l : List α} {b : β}
    (h : b ∈ blocks f j l) : ∃ i a, l[i]? = some a ∧ b ∈ f (j + i) a := by
  induction l generalizing j with
  | nil => simp [blocks] at h
  | cons a l ih =>
    simp only [blocks, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, a, rfl, by simpa using h⟩
    · obtain ⟨i, a', hi, hb⟩ := ih h
      refine ⟨i + 1, a', by simpa using hi, ?_⟩
      rw [show j + (i + 1) = j + 1 + i by omega]
      exact hb

theorem subset_blocks {α β : Type} {f : ℕ → α → List β} {j : ℕ} {l : List α} {a : α}
    (h : a ∈ l) : ∃ i, ∀ b ∈ f i a, b ∈ blocks f j l := by
  induction l generalizing j with
  | nil => simp at h
  | cons a' l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨j, fun b hb => by simp only [blocks, List.mem_append]; exact Or.inl hb⟩
    · obtain ⟨i, hi⟩ := ih (j := j + 1) h
      exact ⟨i, fun b hb => by simp only [blocks, List.mem_append]; exact Or.inr (hi b hb)⟩

/-! ## The scaled system -/

/-- ETR^{1/8,+,·} semantics of an equation: `one x` means `x = 1/8`. -/
def Gate.Holds8 (v : ℕ → ℝ) : Gate → Prop
  | .one x => v x = 1 / 8
  | .add x y z => v x + v y = v z
  | .mul x y z => v x * v y = v z

/-- The translation of the `j`-th equation (`u_k` at `N + k`, `z₀` at `N + 1`, the fresh `w` at
`N + k + 1 + j`). -/
def scaleGate (N k j : ℕ) : Gate → List Gate
  | .one x => [.add x (N + 1) (N + k)]
  | .add x y z => [.add x y z]
  | .mul x y z => [.mul x y (N + k + 1 + j), .mul (N + k) z (N + k + 1 + j)]

/-- The constants: `c₀ = 1/8`, `z₀ = 0`, `u₂ + u₂ = c₀`, `u_{t+1} = u_t · u_t` (`2 ≤ t < k`). -/
def scaleHeader (N k : ℕ) : List Gate :=
  [.one N, .add (N + 1) (N + 1) (N + 1), .add (N + 2) (N + 2) N] ++
    (List.range (k - 2)).map (fun t => .mul (N + 2 + t) (N + 2 + t) (N + 3 + t))

/-- **The ETR^{1/8,+,·} system** obtained from `S` by scaling with `ε = 2^(-2^k)`. -/
def scaleSystem (N k : ℕ) (S : List Gate) : List Gate :=
  scaleHeader N k ++ blocks (scaleGate N k) 0 S

/-- The value of the fresh variable `w` of a product equation: `ε² · v x · v y`. -/
noncomputable def mulVal (ε : ℝ) (v : ℕ → ℝ) : Option Gate → ℝ
  | some (.mul x y _) => ε ^ 2 * (v x * v y)
  | _ => 0

theorem scaleHeader_sound {N k : ℕ} (hk : 2 ≤ k) {y : ℕ → ℝ}
    (h : ∀ g ∈ scaleHeader N k, g.Holds8 y) :
    y N = 1 / 8 ∧ y (N + 1) = 0 ∧ y (N + k) = (1 / 2) ^ 2 ^ k := by
  have h0 : y N = 1 / 8 := h (.one N) (by simp [scaleHeader])
  have h1 : y (N + 1) + y (N + 1) = y (N + 1) := h (.add (N + 1) (N + 1) (N + 1))
    (by simp [scaleHeader])
  have h2 : y (N + 2) + y (N + 2) = y N := h (.add (N + 2) (N + 2) N) (by simp [scaleHeader])
  have chain : ∀ t, t ≤ k - 2 → y (N + 2 + t) = (1 / 2) ^ 2 ^ (t + 2) := by
    intro t ht
    induction t with
    | zero =>
      simp only [Nat.add_zero, zero_add]
      norm_num
      linarith
    | succ t ih =>
      have hm : y (N + 2 + t) * y (N + 2 + t) = y (N + 3 + t) :=
        h (.mul (N + 2 + t) (N + 2 + t) (N + 3 + t))
          (List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩))
      rw [show N + 2 + (t + 1) = N + 3 + t by omega, ← hm, ih (by omega), ← pow_add]
      congr 1
      ring
  refine ⟨h0, by linarith, ?_⟩
  have := chain (k - 2) le_rfl
  rwa [show N + 2 + (k - 2) = N + k by omega, show k - 2 + 2 = k by omega] at this

/-- **Soundness of the scaling**: a solution `y` of the scaled system gives the solution
`y / ε` of the original system. -/
theorem scaleSystem_sound {N k : ℕ} (hk : 2 ≤ k) (S : List Gate) {y : ℕ → ℝ}
    (h : ∀ g ∈ scaleSystem N k S, g.Holds8 y) :
    Solves S (fun i => y i / (1 / 2) ^ 2 ^ k) := by
  obtain ⟨-, h1, hu⟩ := scaleHeader_sound hk (fun g hg => h g (List.mem_append_left _ hg))
  have hε : (0 : ℝ) < (1 / 2) ^ 2 ^ k := by positivity
  intro g hg
  obtain ⟨i, hi⟩ := subset_blocks (f := scaleGate N k) (j := 0) hg
  have hh : ∀ c ∈ scaleGate N k i g, c.Holds8 y :=
    fun c hc => h c (List.mem_append_right _ (hi c hc))
  cases g with
  | one x =>
    have e : y x + y (N + 1) = y (N + k) := hh (.add x (N + 1) (N + k)) (by simp [scaleGate])
    rw [h1, hu] at e
    show y x / (1 / 2) ^ 2 ^ k = 1
    rw [div_eq_one_iff_eq hε.ne']
    linarith
  | add x y' z =>
    have e : y x + y y' = y z := hh (.add x y' z) (by simp [scaleGate])
    show y x / (1 / 2) ^ 2 ^ k + y y' / (1 / 2) ^ 2 ^ k = y z / (1 / 2) ^ 2 ^ k
    rw [← add_div, e]
  | mul x y' z =>
    have e₁ : y x * y y' = y (N + k + 1 + i) := hh (.mul x y' (N + k + 1 + i)) (by simp [scaleGate])
    have e₂ : y (N + k) * y z = y (N + k + 1 + i) :=
      hh (.mul (N + k) z (N + k + 1 + i)) (by simp [scaleGate])
    rw [hu] at e₂
    show y x / (1 / 2) ^ 2 ^ k * (y y' / (1 / 2) ^ 2 ^ k) = y z / (1 / 2) ^ 2 ^ k
    rw [div_mul_div_comm, e₁, ← e₂]
    field_simp

/-- **Completeness of the scaling**: a solution of `S` in the box of radius `R`, with
`ε R ≤ 1/8`, gives a solution of the scaled system with all values in `[-1/8, 1/8]`. -/
theorem scaleSystem_complete {N k : ℕ} (hk : 2 ≤ k) {S : List Gate}
    (hS : ∀ g ∈ S, g.VarsLt N) {v : ℕ → ℝ} (hv : Solves S v) {R : ℝ} (hR : ∀ i, |v i| ≤ R)
    (hεR : (1 / 2 : ℝ) ^ 2 ^ k * R ≤ 1 / 8) :
    ∃ y : ℕ → ℝ, (∀ g ∈ scaleSystem N k S, g.Holds8 y) ∧ ∀ i, |y i| ≤ 1 / 8 := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 / 2) ^ 2 ^ k := ⟨_, rfl⟩
  rw [← hε] at hεR
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR 0)
  -- `|ε v i| ≤ 1/8`
  have hsmall : ∀ i, |ε * v i| ≤ 1 / 8 := by
    intro i
    rw [abs_mul, abs_of_pos hεpos]
    calc ε * |v i| ≤ ε * R := mul_le_mul_of_nonneg_left (hR i) hεpos.le
      _ ≤ 1 / 8 := hεR
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, y = fun i => if i < N then ε * v i else if i = N then 1 / 8
      else if i = N + 1 then 0 else if i ≤ N + k then (1 / 2) ^ 2 ^ (i - N)
      else mulVal ε v S[i - (N + k + 1)]? := ⟨_, rfl⟩
  have yx : ∀ i < N, y i = ε * v i := fun i hi => by simp only [hy, ite_eq_left hi]
  have yN : y N = 1 / 8 := by simp only [hy]; split_ifs <;> first | omega | rfl
  have y1 : y (N + 1) = 0 := by simp only [hy]; split_ifs <;> first | omega | rfl
  have yu : ∀ t, 2 ≤ t → t ≤ k → y (N + t) = (1 / 2) ^ 2 ^ t := by
    intro t ht₁ ht₂
    simp only [hy]
    split_ifs <;> first | omega | simp
  have yw : ∀ j, y (N + k + 1 + j) = mulVal ε v S[j]? := by
    intro j
    simp only [hy]
    split_ifs <;> first | omega | simp
  refine ⟨y, ?_, ?_⟩
  · intro g hg
    simp only [scaleSystem, scaleHeader, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false, List.mem_map, List.mem_range] at hg
    rcases hg with ((rfl | rfl | rfl) | ⟨t, ht, rfl⟩) | hg
    · exact yN
    · show y (N + 1) + y (N + 1) = y (N + 1)
      rw [y1]; norm_num
    · show y (N + 2) + y (N + 2) = y N
      rw [yu 2 le_rfl hk, yN]; norm_num
    · show y (N + 2 + t) * y (N + 2 + t) = y (N + 3 + t)
      rw [show N + 2 + t = N + (t + 2) by omega, show N + 3 + t = N + (t + 3) by omega,
        yu _ (by omega) (by omega), yu _ (by omega) (by omega), ← pow_add]
      congr 1
      ring
    · obtain ⟨i, g', hi, hg'⟩ := mem_blocks hg
      rw [zero_add] at hg'
      have hmem : g' ∈ S := List.mem_of_getElem? hi
      have hvg := hv g' hmem
      have hvars := hS g' hmem
      cases g' with
      | one x =>
        simp only [scaleGate, List.mem_singleton] at hg'
        subst hg'
        show y x + y (N + 1) = y (N + k)
        rw [yx x hvars, y1, yu k hk le_rfl, ← hε, show v x = 1 from hvg]
        ring
      | add x y' z =>
        simp only [scaleGate, List.mem_singleton] at hg'
        subst hg'
        obtain ⟨hx, hy', hz⟩ := hvars
        show y x + y y' = y z
        rw [yx x hx, yx y' hy', yx z hz, ← mul_add, show v x + v y' = v z from hvg]
      | mul x y' z =>
        obtain ⟨hx, hy', hz⟩ := hvars
        have hw : y (N + k + 1 + i) = ε ^ 2 * (v x * v y') := by rw [yw, hi]; rfl
        simp only [scaleGate, List.mem_cons, List.mem_nil_iff, or_false] at hg'
        rcases hg' with rfl | rfl
        · show y x * y y' = y (N + k + 1 + i)
          rw [yx x hx, yx y' hy', hw]
          ring
        · show y (N + k) * y z = y (N + k + 1 + i)
          rw [yu k hk le_rfl, ← hε, yx z hz, hw, ← show v x * v y' = v z from hvg]
          ring
  · intro i
    simp only [hy]
    split_ifs with h₁ h₂ h₃ h₄
    · exact hsmall i
    · norm_num
    · norm_num
    · have h2 : 2 ≤ i - N := by omega
      have hpos : (0 : ℝ) < (1 / 2) ^ 2 ^ (i - N) := by positivity
      rw [abs_of_pos hpos]
      calc (1 / 2 : ℝ) ^ 2 ^ (i - N) ≤ (1 / 2) ^ 2 ^ 2 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num)
              (Nat.pow_le_pow_right (by norm_num) h2)
        _ ≤ 1 / 8 := by norm_num
    · cases hS' : S[i - (N + k + 1)]? with
      | none => simp [mulVal]
      | some g =>
        cases g with
        | one x => simp [mulVal]
        | add x y' z => simp [mulVal]
        | mul x y' z =>
          simp only [mulVal]
          have e : ε ^ 2 * (v x * v y') = (ε * v x) * (ε * v y') := by ring
          rw [e, abs_mul]
          have hx := hsmall x
          have hy' := hsmall y'
          have := abs_nonneg (ε * v x)
          have := abs_nonneg (ε * v y')
          nlinarith

/-- The choice `k = E + 2` makes `ε · 2^(2^E) ≤ 1/8`. -/
theorem eps_mul_ball_le (E : ℕ) : (1 / 2 : ℝ) ^ 2 ^ (E + 2) * 2 ^ 2 ^ E ≤ 1 / 8 := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ E := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.one_le_two_pow
  have h4 : 2 ^ (E + 2) = M * 4 := by rw [hM, pow_add]; norm_num
  rw [h4, ← hM, pow_mul]
  set q : ℝ := (1 / 2) ^ M with hq
  have hq2 : q * 2 ^ M = 1 := by rw [hq, ← mul_pow]; norm_num
  have hqpos : 0 < q := by positivity
  have hqle : q ≤ 1 / 2 := by
    rw [hq]
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have e : q ^ 4 * 2 ^ M = q ^ 3 := by
    calc q ^ 4 * 2 ^ M = q ^ 3 * (q * 2 ^ M) := by ring
      _ = q ^ 3 := by rw [hq2, mul_one]
  rw [e]
  calc q ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hqpos.le hqle 3
    _ = 1 / 8 := by norm_num

/-- Variable bound of the scaled system. -/
theorem scaleSystem_vars {N k : ℕ} (hk : 2 ≤ k) {S : List Gate} (hS : ∀ g ∈ S, g.VarsLt N) :
    ∀ g ∈ scaleSystem N k S, g.VarsLt (N + k + 1 + S.length) := by
  intro g hg
  simp only [scaleSystem, scaleHeader, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false, List.mem_map, List.mem_range] at hg
  rcases hg with ((rfl | rfl | rfl) | ⟨t, ht, rfl⟩) | hg
  · show N < _; omega
  · show N + 1 < _ ∧ N + 1 < _ ∧ N + 1 < _; omega
  · show N + 2 < _ ∧ N + 2 < _ ∧ N < _; omega
  · show N + 2 + t < _ ∧ N + 2 + t < _ ∧ N + 3 + t < _; omega
  · obtain ⟨i, g', hi, hg'⟩ := mem_blocks hg
    rw [zero_add] at hg'
    have hil : i < S.length := (List.getElem?_eq_some_iff.mp hi).1
    have hvars := hS g' (List.mem_of_getElem? hi)
    cases g' with
    | one x =>
      simp only [scaleGate, List.mem_singleton] at hg'
      subst hg'
      have : x < N := hvars
      show x < _ ∧ N + 1 < _ ∧ N + k < _
      omega
    | add x y z =>
      simp only [scaleGate, List.mem_singleton] at hg'
      subst hg'
      obtain ⟨hx, hy, hz⟩ := hvars
      show x < _ ∧ y < _ ∧ z < _
      omega
    | mul x y z =>
      obtain ⟨hx, hy, hz⟩ := hvars
      simp only [scaleGate, List.mem_cons, List.mem_nil_iff, or_false] at hg'
      rcases hg' with rfl | rfl
      · show x < _ ∧ y < _ ∧ N + k + 1 + i < _
        omega
      · show N + k < _ ∧ z < _ ∧ N + k + 1 + i < _
        omega

end ArtGallery.Gate

end
