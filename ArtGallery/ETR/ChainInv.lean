module

public import ArtGallery.ETR.ChainGadget

/-!
# Reduction from ETR^{1/8,+,·}_{[-1/8,1/8]} to ETR-INV (paper §4, pp. 17–19)

`invSystem M T` translates a system `T` of ETR^{1/8,+,·} equations (read with `Gate.Holds8`)
on the variables `< M` into an ETR-INV instance.  The variable `x` keeps its index and now
stands for `X = x + 7/8`; the constants `1, 2, 1/2, 3/2, 3/4, 7/4, 7/8` sit at `M, …, M + 6`
(`constHeader`), and the `j`-th equation gets the 35 fresh variables starting at
`M + 7 + 35 j`:

* `x = 1/8 ↦ X = 1`;
* `x + y = z ↦ X + Y = W, Z + 7/8 = W` (`W = x + y + 7/4 ∈ [3/2, 2]`);
* `x · y = z ↦ prodGadget` (see `ArtGallery.ETR.ChainGadget`).

* `invSystem_sound`: every solution `Y` (no range assumption) gives the solution `Y − 7/8`.
* `invSystem_complete`: a solution with values in `[-1/8, 1/8]` gives a solution with all
  values (of all indices) in `[1/2, 2]`; moreover the second argument of every inversion
  `x · y = 1` then lies in `[1, 2]` (used for ETR-INV-REV).
* `invSystem_vars`: all indices are below `M + 7 + 35 · T.length`.
-/

@[expose] public section

namespace ArtGallery.Chain

open ArtGallery.ETRINV ArtGallery.Gate

/-- The base index of the fresh variables of the `j`-th equation. -/
def blockBase (M j : ℕ) : ℕ := M + 7 + 35 * j

/-- The ETR-INV translation of the `j`-th equation. -/
def invGate (M j : ℕ) : Gate → List Constraint
  | .one x => [.one x]
  | .add x y z => [.add x y (blockBase M j), .add z (M + 6) (blockBase M j)]
  | .mul x y z => prodGadget M x y z (blockBase M j)

/-- **The ETR-INV instance** of an ETR^{1/8,+,·} system on the variables `< M`. -/
def invSystem (M : ℕ) (T : List Gate) : List Constraint :=
  constHeader M ++ blocks (invGate M) 0 T

/-- **Soundness**: a solution `Y` of `invSystem M T` gives the solution `Y − 7/8` of `T`. -/
theorem invSystem_sound {M : ℕ} {T : List Gate} {Y : ℕ → ℝ}
    (h : ∀ c ∈ invSystem M T, c.Holds Y) : ∀ g ∈ T, g.Holds8 (fun i => Y i - 7 / 8) := by
  have hc := constHeader_sound (fun c hc => h c (List.mem_append_left _ hc))
  intro g hg
  obtain ⟨j, hj⟩ := subset_blocks (f := invGate M) (j := 0) hg
  have hh : ∀ c ∈ invGate M j g, c.Holds Y := fun c hc => h c (List.mem_append_right _ (hj c hc))
  cases g with
  | one x =>
    have e : Y x = 1 := hh (.one x) (by simp [invGate])
    show Y x - 7 / 8 = 1 / 8
    rw [e]; norm_num
  | add x y z =>
    have e₁ : Y x + Y y = Y (blockBase M j) := hh (.add x y (blockBase M j)) (by simp [invGate])
    have e₂ : Y z + Y (M + 6) = Y (blockBase M j) :=
      hh (.add z (M + 6) (blockBase M j)) (by simp [invGate])
    rw [hc.2.2.2.2.2.2] at e₂
    show Y x - 7 / 8 + (Y y - 7 / 8) = Y z - 7 / 8
    linarith
  | mul x y z => exact prodGadget_sound hc hh

/-- The value of the constant number `s`. -/
noncomputable def constVal (s : ℕ) : ℝ := [1, 2, 1 / 2, 3 / 2, 3 / 4, 7 / 4, 7 / 8].getD s 1

/-- The value of the fresh variable number `s` of the product gadget for `a · a'`. -/
noncomputable def prodVal (a a' : ℝ) (s : ℕ) : ℝ :=
  if s < 6 then (prodFirst a a').getD s 1
  else if s < 18 then (sqList (1 + (a + a') / 2)).getD (s - 6) 1
  else if s < 30 then (sqList (1 + (a - a') / 2)).getD (s - 18) 1
  else (prodLast a a').getD (s - 30) 1

/-- The value of the fresh variable number `s` of the block of an equation. -/
noncomputable def blockVal (y : ℕ → ℝ) : Option Gate → ℕ → ℝ
  | some (.add x y' _), s => if s = 0 then y x + y y' + 7 / 4 else 1
  | some (.mul x y' _), s => prodVal (y x) (y y') s
  | _, _ => 1

theorem prodVal_range {a a' : ℝ} (ha₁ : -1 / 8 ≤ a) (ha₂ : a ≤ 1 / 8) (ha'₁ : -1 / 8 ≤ a')
    (ha'₂ : a' ≤ 1 / 8) (s : ℕ) : 1 / 2 ≤ prodVal a a' s ∧ prodVal a a' s ≤ 2 := by
  unfold prodVal
  split_ifs
  · exact getD_range (prodFirst_range ha₁ ha₂ ha'₁ ha'₂) s
  · exact getD_range (sqList_range (by linarith) (by linarith)) _
  · exact getD_range (sqList_range (by linarith) (by linarith)) _
  · exact getD_range (prodLast_range ha₁ ha₂ ha'₁ ha'₂) _

/-- **Completeness**: a solution of `T` with values in `[-1/8, 1/8]` gives a solution of
`invSystem M T` with all values in `[1/2, 2]`, in which the second argument of every inversion
lies in `[1, 2]`. -/
theorem invSystem_complete {M : ℕ} {T : List Gate} (hT : ∀ g ∈ T, g.VarsLt M) {y : ℕ → ℝ}
    (hy : ∀ g ∈ T, g.Holds8 y) (hr : ∀ i, |y i| ≤ 1 / 8) :
    ∃ Y : ℕ → ℝ, (∀ i, 1 / 2 ≤ Y i ∧ Y i ≤ 2) ∧ (∀ c ∈ invSystem M T, c.Holds Y) ∧
      (∀ a b, Constraint.inv a b ∈ invSystem M T → 1 ≤ Y b ∧ Y b ≤ 2) ∧
      ∀ i < M, Y i = y i + 7 / 8 := by
  have hr' : ∀ i, -1 / 8 ≤ y i ∧ y i ≤ 1 / 8 := fun i => by
    have := abs_le.mp (hr i)
    constructor <;> linarith [this.1, this.2]
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, Y = fun i => if i < M then y i + 7 / 8
      else if i < M + 7 then constVal (i - M)
      else blockVal y T[(i - (M + 7)) / 35]? ((i - (M + 7)) % 35) := ⟨_, rfl⟩
  have Ylt : ∀ i < M, Y i = y i + 7 / 8 := fun i hi => by simp only [hY, ite_eq_left hi]
  have Yc : ∀ s < 7, Y (M + s) = constVal s := fun s hs => by
    simp only [hY]
    split_ifs <;> first | omega | simp
  have Yb : ∀ j s, s < 35 → Y (blockBase M j + s) = blockVal y T[j]? s := by
    intro j s hs
    have h₁ : (M + 7 + 35 * j + s - (M + 7)) / 35 = j := by omega
    have h₂ : (M + 7 + 35 * j + s - (M + 7)) % 35 = s := by omega
    simp only [hY, blockBase]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), h₁, h₂]
  have hc : ConstsOK Y M := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := Yc 0 (by norm_num); rw [Nat.add_zero] at this; rw [this]; rfl
    · rw [Yc 1 (by norm_num)]; rfl
    · rw [Yc 2 (by norm_num)]; rfl
    · rw [Yc 3 (by norm_num)]; rfl
    · rw [Yc 4 (by norm_num)]; rfl
    · rw [Yc 5 (by norm_num)]; rfl
    · rw [Yc 6 (by norm_num)]; rfl
  have hBm : ∀ j x y' z, T[j]? = some (Gate.mul x y' z) →
      ∀ s < 35, Y (blockBase M j + s) = prodVal (y x) (y y') s := by
    intro j x y' z hj s hs
    rw [Yb j s hs, hj]
    rfl
  have hSq₁ : ∀ j x y' z, T[j]? = some (Gate.mul x y' z) →
      ∀ i < 12, Y (blockBase M j + 6 + i) = (sqList (1 + (y x + y y') / 2)).getD i 1 := by
    intro j x y' z hj i hi
    rw [add_assoc, hBm j x y' z hj (6 + i) (by omega)]
    simp only [prodVal]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  have hSq₂ : ∀ j x y' z, T[j]? = some (Gate.mul x y' z) →
      ∀ i < 12, Y (blockBase M j + 18 + i) = (sqList (1 + (y x - y y') / 2)).getD i 1 := by
    intro j x y' z hj i hi
    rw [add_assoc, hBm j x y' z hj (18 + i) (by omega)]
    simp only [prodVal]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  refine ⟨Y, ?_, ?_, ?_, Ylt⟩
  · -- ranges
    intro i
    simp only [hY]
    split_ifs with h₁ h₂
    · constructor <;> linarith [(hr' i).1, (hr' i).2]
    · exact getD_range (by simp only [List.forall_mem_cons, forall_mem_nil_iff, and_true]; norm_num)
        _
    · cases hT' : T[(i - (M + 7)) / 35]? with
      | none => norm_num [blockVal]
      | some g =>
        cases g with
        | one x => norm_num [blockVal]
        | add x y' z =>
          simp only [blockVal]
          split_ifs
          · constructor <;> linarith [(hr' x).1, (hr' x).2, (hr' y').1, (hr' y').2]
          · norm_num
        | mul x y' z =>
          exact prodVal_range (hr' x).1 (hr' x).2 (hr' y').1 (hr' y').2 _
  · intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact constHeader_complete hc c hc'
    obtain ⟨j, g, hj, hcg⟩ := mem_blocks hc'
    rw [zero_add] at hcg
    have hmem : g ∈ T := List.mem_of_getElem? hj
    have hyg := hy g hmem
    have hvars := hT g hmem
    cases g with
    | one x =>
      simp only [invGate, List.mem_singleton] at hcg
      subst hcg
      have hx : x < M := hvars
      show Y x = 1
      rw [Ylt x hx, show y x = 1 / 8 from hyg]
      norm_num
    | add x y' z =>
      obtain ⟨hx, hy', hz⟩ := hvars
      have hW : Y (blockBase M j) = y x + y y' + 7 / 4 := by
        have := Yb j 0 (by norm_num)
        rw [Nat.add_zero, hj] at this
        rw [this]
        simp [blockVal]
      simp only [invGate, List.mem_cons, List.mem_nil_iff, or_false] at hcg
      rcases hcg with rfl | rfl
      · show Y x + Y y' = Y (blockBase M j)
        rw [Ylt x hx, Ylt y' hy', hW]
        ring
      · show Y z + Y (M + 6) = Y (blockBase M j)
        rw [Ylt z hz, hW, hc.2.2.2.2.2.2, ← show y x + y y' = y z from hyg]
        ring
    | mul x y' z =>
      obtain ⟨hx, hy', hz⟩ := hvars
      refine prodGadget_complete hc (hr' x).1 (hr' y').1 (hr' y').2 (Ylt x hx)
        (Ylt y' hy') ?_ ?_ (hSq₁ j x y' z hj) (hSq₂ j x y' z hj) ?_ c hcg
      · rw [Ylt z hz, ← show y x * y y' = y z from hyg]
      · intro i hi
        rw [hBm j x y' z hj i (by omega)]
        simp only [prodVal, ite_eq_left hi]
      · intro i hi
        rw [add_assoc, hBm j x y' z hj (30 + i) (by omega)]
        simp only [prodVal]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          Nat.add_sub_cancel_left]
  · -- the second argument of every inversion lies in `[1, 2]`
    intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · simp [constHeader] at hab
    obtain ⟨j, g, hj, hcg⟩ := mem_blocks hab
    rw [zero_add] at hcg
    cases g with
    | one x => simp [invGate] at hcg
    | add x y' z => simp [invGate] at hcg
    | mul x y' z =>
      exact prodGadget_invArg (hr' x).1 (hr' x).2 (hr' y').1 (hr' y').2 (hSq₁ j x y' z hj)
        (hSq₂ j x y' z hj) a b hcg

/-- All indices of `invSystem M T` are below `M + 7 + 35 · T.length`. -/
theorem invSystem_vars {M : ℕ} {T : List Gate} (hT : ∀ g ∈ T, g.VarsLt M) :
    ∀ c ∈ invSystem M T, c.VarsLt (M + 7 + 35 * T.length) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [constHeader, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Constraint.VarsLt] <;> omega
  obtain ⟨j, g, hj, hcg⟩ := mem_blocks hc
  rw [zero_add] at hcg
  have hjl : j < T.length := (List.getElem?_eq_some_iff.mp hj).1
  have hvars := hT g (List.mem_of_getElem? hj)
  have hb : blockBase M j + 35 ≤ M + 7 + 35 * T.length := by
    simp only [blockBase]
    omega
  cases g with
  | one x =>
    simp only [invGate, List.mem_singleton] at hcg
    subst hcg
    have hx : x < M := hvars
    show x < _
    omega
  | add x y z =>
    obtain ⟨hx, hy, hz⟩ := hvars
    simp only [invGate, List.mem_cons, List.mem_nil_iff, or_false] at hcg
    rcases hcg with rfl | rfl <;> simp only [Constraint.VarsLt] <;> omega
  | mul x y z =>
    obtain ⟨hx, hy, hz⟩ := hvars
    exact prodGadget_vars (by omega) (by omega) (by omega) hb (by omega) c hcg

end ArtGallery.Chain

end
