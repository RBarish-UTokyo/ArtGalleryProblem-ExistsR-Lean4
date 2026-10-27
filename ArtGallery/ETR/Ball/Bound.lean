module

public import ArtGallery.ETR.Gate
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The numerical bound of the ball theorem

The root bound produced by the characteristic-polynomial argument is `1 + ballH n S` with
`ballH n S = (5^n)! * (1 + S^(4n+1))^(5^n)` and `S = 18 m + 1`.  We show that it is at most
`2 ^ 2 ^ ballExp n m` with crude estimates.
-/

@[expose] public section

namespace ArtGallery.Ball

open ArtGallery.Gate

/-- The coefficient bound for the characteristic polynomials: `(5^n)! * (1 + S^(4n+1))^(5^n)`. -/
def ballH (n S : ℕ) : ℕ := (5 ^ n).factorial * (1 + S ^ (4 * n + 1)) ^ (5 ^ n)

theorem one_add_le_two_pow {a k : ℕ} (h : a ≤ 2 ^ k) : 1 + a ≤ 2 ^ (k + 1) := by
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem eighteen_le_two_pow (m : ℕ) : 18 * m + 1 ≤ 2 ^ (m + 5) := by
  have h := Nat.lt_two_pow_self (n := m)
  have : 2 ^ (m + 5) = 32 * 2 ^ m := by rw [pow_add]; ring
  rw [this]
  omega

theorem poly_le_two_pow (n m : ℕ) :
    3 * n + ((m + 5) * (4 * n + 1) + 1) + 1 ≤ 2 ^ (2 * (n + m + 5) + 3) := by
  set A := n + m + 5 with hA
  have hA2 : A * A ≤ 2 ^ (2 * A) := by
    have h := (Nat.lt_two_pow_self (n := A)).le
    calc A * A ≤ 2 ^ A * 2 ^ A := Nat.mul_le_mul h h
      _ = 2 ^ (2 * A) := by rw [← pow_add]; ring_nf
  have hpoly : 3 * n + ((m + 5) * (4 * n + 1) + 1) + 1 ≤ 8 * (A * A) := by
    rw [hA]
    nlinarith
  calc 3 * n + ((m + 5) * (4 * n + 1) + 1) + 1 ≤ 8 * (A * A) := hpoly
    _ ≤ 8 * 2 ^ (2 * A) := Nat.mul_le_mul_left _ hA2
    _ = 2 ^ (2 * A + 3) := by rw [pow_add]; ring

/-- The final numerical estimate. -/
theorem ballH_bound (n m : ℕ) : 1 + ballH n (18 * m + 1) ≤ 2 ^ 2 ^ ballExp n m := by
  set N := 5 ^ n with hN
  set e₁ := (m + 5) * (4 * n + 1) + 1 with he₁
  have hN8 : N ≤ 2 ^ (3 * n) := by
    rw [hN, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) n
  have hfac : N.factorial ≤ 2 ^ (3 * n * N) := by
    calc N.factorial ≤ N ^ N := Nat.factorial_le_pow N
      _ ≤ (2 ^ (3 * n)) ^ N := Nat.pow_le_pow_left hN8 N
      _ = 2 ^ (3 * n * N) := by rw [← pow_mul]
  have hE : 1 + (18 * m + 1) ^ (4 * n + 1) ≤ 2 ^ e₁ := by
    apply one_add_le_two_pow
    calc (18 * m + 1) ^ (4 * n + 1) ≤ (2 ^ (m + 5)) ^ (4 * n + 1) :=
          Nat.pow_le_pow_left (eighteen_le_two_pow m) _
      _ = 2 ^ ((m + 5) * (4 * n + 1)) := by rw [← pow_mul]
  have hH : ballH n (18 * m + 1) ≤ 2 ^ ((3 * n + e₁) * N) := by
    calc ballH n (18 * m + 1) = N.factorial * (1 + (18 * m + 1) ^ (4 * n + 1)) ^ N := rfl
      _ ≤ 2 ^ (3 * n * N) * (2 ^ e₁) ^ N :=
          Nat.mul_le_mul hfac (Nat.pow_le_pow_left hE N)
      _ = 2 ^ ((3 * n + e₁) * N) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hexp : (3 * n + e₁) * N + 1 ≤ 2 ^ ballExp n m := by
    have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by norm_num)
    have h1 : (3 * n + e₁) * N + 1 ≤ (3 * n + e₁ + 1) * N := by nlinarith
    have h2 : (3 * n + e₁ + 1) * N ≤ 2 ^ (2 * (n + m + 5) + 3) * 2 ^ (3 * n) :=
      Nat.mul_le_mul (poly_le_two_pow n m) hN8
    have h3 : 2 ^ (2 * (n + m + 5) + 3) * 2 ^ (3 * n) ≤ 2 ^ ballExp n m := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      simp only [ballExp]
      omega
    omega
  calc 1 + ballH n (18 * m + 1) ≤ 2 ^ ((3 * n + e₁) * N + 1) := one_add_le_two_pow hH
    _ ≤ 2 ^ 2 ^ ballExp n m := Nat.pow_le_pow_right (by norm_num) hexp

end ArtGallery.Ball

end
