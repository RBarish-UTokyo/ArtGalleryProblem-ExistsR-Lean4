module

public import PT.Iterate

/-!
# Polynomial-time arithmetic on unary natural numbers

Natural numbers are coded in unary, so the value of a polynomial-time function into `Nat` is
polynomially bounded and addition, multiplication, division etc. are all polynomial-time.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β σ : Type} [Code α] [Code β] [Code σ]

theorem leadingOnes_enc_nat (n : Nat) : leadingOnes (enc n) = List.replicate n true := by
  rw [enc_nat_eq]
  exact leadingOnes_ones n []

/-- The value of a polynomial-time function into `Nat` is polynomially bounded. -/
protected theorem PT.nat_le {f : α → Nat} (hf : PT f) :
    ∃ c k, ∀ a, f a < powerBound c k (size a) := by
  obtain ⟨c, k, h⟩ := hf.size_le
  refine ⟨c, k, fun a => ?_⟩
  have := h a
  rw [size_nat] at this
  omega

/-! ### Successor, addition, truncated subtraction, minimum, maximum -/

@[fun_prop] protected theorem PT.succ {f : α → Nat} (hf : PT f) : PT (fun a => Nat.succ (f a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => true :: F x, polyTime_cons true hF, fun a => by simp only [hF']; rfl⟩

@[fun_prop] protected theorem PT.add {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a + g a) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  refine ⟨fun x => leadingOnes (F x) ++ G x,
    polyTime_append (polyTime_comp polyTime_leadingOnes hF) hG, fun a => ?_⟩
  simp only [hF', hG', leadingOnes_enc_nat]
  rw [enc_nat_eq, enc_nat_eq, ← List.append_assoc, List.replicate_append_replicate]

@[fun_prop] protected theorem PT.sub {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a - g a) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  refine ⟨fun x => (unpair (G x ++ leadingOnes (F x))).2 ++ [false],
    polyTime_append (polyTime_comp polyTime_pair_snd
      (polyTime_append hG (polyTime_comp polyTime_leadingOnes hF))) (polyTime_const _),
    fun a => ?_⟩
  simp only [hF', hG', leadingOnes_enc_nat]
  simp only [enc_nat_eq, List.append_assoc, List.singleton_append, unpair_ones,
    List.drop_replicate]

@[fun_prop] protected theorem PT.pred {f : α → Nat} (hf : PT f) : PT (fun a => Nat.pred (f a)) :=
  (PT.sub hf (PT.const 1)).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.min {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => min (f a) (g a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  obtain ⟨G, hG, hG'⟩ := hg
  refine ⟨fun x => (unpair (G x ++ leadingOnes (F x))).1 ++ [false],
    polyTime_append (polyTime_comp polyTime_pair_fst
      (polyTime_append hG (polyTime_comp polyTime_leadingOnes hF))) (polyTime_const _),
    fun a => ?_⟩
  simp only [hF', hG', leadingOnes_enc_nat]
  simp only [enc_nat_eq, List.append_assoc, List.singleton_append, unpair_ones,
    List.take_replicate, Nat.min_comm]

@[fun_prop] protected theorem PT.max {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => max (f a) (g a)) :=
  (PT.add hf (PT.sub hg hf)).of_eq fun a => by omega

/-! ### Comparisons -/

/-- Positivity test. -/
@[fun_prop] protected theorem PT.natPos {f : α → Nat} [inst : ∀ a, Decidable (0 < f a)]
    (hf : PT f) : PT (fun a => decide (0 < f a)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  refine ⟨fun x => (F x).take 1, polyTime_take_one hF, fun a => ?_⟩
  simp only [hF']
  rcases Nat.eq_zero_or_pos (f a) with h | h
  · simp [h]
  · obtain ⟨m, hm⟩ : ∃ m, f a = m + 1 := ⟨f a - 1, by omega⟩
    simp [hm]

@[fun_prop] protected theorem PT.natLt {f g : α → Nat} [inst : ∀ a, Decidable (f a < g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a < g a)) :=
  (PT.natPos (PT.sub hg hf)).decide_congr fun a => by omega

@[fun_prop] protected theorem PT.natLe {f g : α → Nat} [inst : ∀ a, Decidable (f a ≤ g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a ≤ g a)) :=
  (PT.decide_not (PT.natLt hg hf)).decide_congr fun a => by omega

@[fun_prop] protected theorem PT.natEq {f g : α → Nat} [inst : ∀ a, Decidable (f a = g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a = g a)) :=
  (PT.decide_and (PT.natLe hf hg) (PT.natLe hg hf)).decide_congr fun a => by omega

@[fun_prop] protected theorem PT.natNe {f g : α → Nat} [inst : ∀ a, Decidable (f a ≠ g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a ≠ g a)) :=
  (PT.decide_not (PT.natEq hf hg)).decide_congr fun _ => Iff.rfl

@[fun_prop] protected theorem PT.natBeq {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => Nat.beq (f a) (g a)) :=
  (PT.natEq hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

@[fun_prop] protected theorem PT.natBEq {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a == g a) :=
  (PT.natEq hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

@[fun_prop] protected theorem PT.natBNe {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a != g a) :=
  (PT.natNe hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp

@[fun_prop] protected theorem PT.natBle {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => Nat.ble (f a) (g a)) :=
  (PT.natLe hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp [Nat.ble_eq]

@[fun_prop] protected theorem PT.natBlt {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => Nat.blt (f a) (g a)) :=
  (PT.natLt hf hg).of_eq fun a => by
    rw [Bool.eq_iff_iff]
    simp [Nat.blt_eq]

/-! ### Multiplication and powers -/

theorem iterate_add_const (m i j : Nat) : (fun s => s + m)^[i] j = j + i * m := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, Nat.succ_mul]
    omega

@[fun_prop] protected theorem PT.mul {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a * g a) := by
  obtain ⟨cf, kf, hsf⟩ := hf.nat_le
  obtain ⟨cg, kg, hsg⟩ := hg.nat_le
  have h := PT.iterate (step := fun a s => s + g a) (init := fun _ => 0) (n := f)
    (PT.add PT.snd' (hg.comp PT.fst')) (PT.const 0) hf
    (fun N => powerBound cf kf N * powerBound cg kg N + 1)
    (((PolynomialBound.power cf kf).mul (PolynomialBound.power cg kg)).add
      (PolynomialBound.constant 1)) ?_
  · exact h.of_eq fun a => by simp [iterate_add_const]
  · intro a i hi
    have h1 := hsf a
    have h2 := hsg a
    simp only [iterate_add_const, size_nat, Nat.zero_add]
    have := Nat.mul_le_mul (show i ≤ powerBound cf kf (size a) by omega)
      (show g a ≤ powerBound cg kg (size a) by omega)
    omega

/-- Powers with a fixed exponent. -/
@[fun_prop] protected theorem PT.pow_const {f : α → Nat} (hf : PT f) (k : Nat) :
    PT (fun a => f a ^ k) := by
  induction k with
  | zero => simpa using PT.const (α := α) 1
  | succ k ih => simpa only [Nat.pow_succ] using PT.mul ih hf

/-! ### Division and remainder -/

/-- One step of division by repeated subtraction on the state `(quotient, remainder)`. -/
def divModStep (n : Nat) (s : Nat × Nat) : Nat × Nat :=
  if 0 < n ∧ n ≤ s.2 then (s.1 + 1, s.2 - n) else s

theorem divModStep_iterate (n m i : Nat) :
    (divModStep n)^[i] (0, m) = (min i (m / n), m - min i (m / n) * n) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [divModStep]
    · have hdm := Nat.div_add_mod' m n
      have hmod := Nat.mod_lt m hn
      rcases Nat.lt_or_ge i (m / n) with hlt | hge
      · have h1 : (i + 1) * n ≤ m / n * n := Nat.mul_le_mul_right n hlt
        rw [Nat.succ_mul] at h1
        rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.min_eq_left hlt, Nat.succ_mul]
        have hc : 0 < n ∧ n ≤ m - i * n := ⟨hn, by omega⟩
        simp only [divModStep, hc, and_self, ite_true]
        congr 1
        omega
      · rw [Nat.min_eq_right hge, Nat.min_eq_right (Nat.le_succ_of_le hge)]
        have hc : ¬ (0 < n ∧ n ≤ m - m / n * n) := by omega
        simp only [divModStep, hc, ite_false]

theorem divModStep_iterate_self (n m : Nat) : (divModStep n)^[m] (0, m) = (m / n, m % n) := by
  rw [divModStep_iterate, Nat.min_eq_right (Nat.div_le_self m n)]
  have hdm := Nat.div_add_mod' m n
  congr 1
  omega

/-- Quotient and remainder together. -/
protected theorem PT.divMod {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => (f a / g a, f a % g a)) := by
  obtain ⟨c, k, hs⟩ := hf.nat_le
  have hstep : PT (fun p : α × (Nat × Nat) => divModStep (g p.1) p.2) := by
    unfold divModStep
    fun_prop
  have h := PT.iterate (step := fun a => divModStep (g a)) (init := fun a => (0, f a)) (n := f)
    hstep (PT.pair (PT.const 0) hf) hf (fun N => 2 * powerBound c k N + 2)
    (((PolynomialBound.constant 2).mul (PolynomialBound.power c k)).add
      (PolynomialBound.constant 2)) ?_
  · exact h.of_eq fun a => divModStep_iterate_self (g a) (f a)
  · intro a i _
    have h1 := hs a
    have h2 : min i (f a / g a) ≤ f a := Nat.le_trans (Nat.min_le_right _ _) (Nat.div_le_self _ _)
    simp only [divModStep_iterate, size_prod, size_nat]
    omega

@[fun_prop] protected theorem PT.div {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a / g a) :=
  PT.fst (PT.divMod hf hg)

@[fun_prop] protected theorem PT.mod {f g : α → Nat} (hf : PT f) (hg : PT g) :
    PT (fun a => f a % g a) :=
  PT.snd (PT.divMod hf hg)

/-- Divisibility test. -/
@[fun_prop] protected theorem PT.natDvd {f g : α → Nat} [inst : ∀ a, Decidable (f a ∣ g a)]
    (hf : PT f) (hg : PT g) : PT (fun a => decide (f a ∣ g a)) :=
  (PT.natEq (PT.mod hg hf) (PT.const 0)).decide_congr fun _ =>
    (Nat.dvd_iff_mod_eq_zero ..).symm

/-! ### Bounded recursion on a natural number -/

/-- **Bounded primitive recursion.**  If `g a 0 = base a` and `g a (i + 1) = step a i (g a i)`
with `base`, `step` polynomial-time and the values `g a i`, `i ≤ n a`, polynomially bounded
in size, then `fun a => g a (n a)` is polynomial-time. -/
protected theorem PT.of_natRec {g : α → Nat → σ} {base : α → σ} {step : α → Nat → σ → σ}
    {n : α → Nat} (hbase : PT base)
    (hstep : PT (fun p : α × Nat × σ => step p.1 p.2.1 p.2.2)) (hn : PT n)
    (h0 : ∀ a, g a 0 = base a) (hs : ∀ a i, g a (i + 1) = step a i (g a i))
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a i, i ≤ n a → size (g a i) ≤ bound (size a)) :
    PT (fun a => g a (n a)) := by
  obtain ⟨c, k, hk⟩ := hn.nat_le
  have key : ∀ a i, (fun s : Nat × σ => (s.1 + 1, step a s.1 s.2))^[i] (0, base a) =
      (i, g a i) := by
    intro a i
    induction i with
    | zero => simp [h0]
    | succ i ih => rw [Function.iterate_succ_apply', ih, hs]
  have h := PT.iterate (step := fun a (s : Nat × σ) => (s.1 + 1, step a s.1 s.2))
    (init := fun a => (0, base a)) (n := n)
    (PT.pair (PT.succ (PT.fst PT.snd')) hstep) (PT.pair (PT.const 0) hbase) hn
    (fun N => powerBound c k N + 1 + bound N)
    (((PolynomialBound.power c k).add (PolynomialBound.constant 1)).add hbound) ?_
  · exact (PT.snd h).of_eq fun a => by simp only [key]
  · intro a i hi
    have h1 := hk a
    have h2 := hsize a i hi
    simp only [key, size_prod, size_nat]
    omega

/-- Bounded primitive recursion, stated with `Nat.rec`. -/
protected theorem PT.natRec {base : α → σ} {step : α → Nat → σ → σ} {n : α → Nat}
    (hbase : PT base) (hstep : PT (fun p : α × Nat × σ => step p.1 p.2.1 p.2.2)) (hn : PT n)
    (bound : Nat → Nat) (hbound : PolynomialBound bound)
    (hsize : ∀ a i, i ≤ n a →
      size (Nat.rec (motive := fun _ => σ) (base a) (step a) i) ≤ bound (size a)) :
    PT (fun a => Nat.rec (motive := fun _ => σ) (base a) (step a) (n a)) :=
  PT.of_natRec (g := fun a i => Nat.rec (motive := fun _ => σ) (base a) (step a) i)
    hbase hstep hn (fun _ => rfl) (fun _ _ => rfl) bound hbound hsize

/-- Case distinction on a natural number, in equational form. -/
protected theorem PT.of_natCases {n : α → Nat} {z : α → β} {s : α → Nat → β} {g : α → β}
    (hn : PT n) (hz : PT z) (hs : PT (fun p : α × Nat => s p.1 p.2))
    (hzero : ∀ a, n a = 0 → g a = z a) (hsucc : ∀ a k, n a = k + 1 → g a = s a k) : PT g :=
  (PT.ite_prop (PT.natEq hn (PT.const 0)) hz
    (hs.comp (PT.pair PT.id (PT.pred hn)))).of_eq fun a => by
      cases h : n a with
      | zero => simpa using (hzero a h).symm
      | succ k => simpa using (hsucc a k h).symm

/-- Case distinction on a natural number, in `match` form. -/
protected theorem PT.natCases {n : α → Nat} {z : α → β} {s : α → Nat → β}
    (hn : PT n) (hz : PT z) (hs : PT (fun p : α × Nat => s p.1 p.2)) :
    PT (fun a => match n a with
      | 0 => z a
      | k + 1 => s a k) :=
  PT.of_natCases hn hz hs (fun a h => by simp only [h]) (fun a k h => by simp only [h])

end Complexity.PT
