module

public import Complexity.Reg
public import Mathlib.Logic.Function.Iterate

/-!
# Word-level primitives for the `PT` framework

A small stock of polynomial-time functions on raw binary words, from which all the
`enc`-level functions of the `PT` library are assembled with the closure theorems of
`Complexity.Reg`:

* `leadingOnes`, `afterOnes` — split off the unary prefix of a word (the only two new
  register programs);
* `polyTime_ones`, `polyTime_take`, `polyTime_drop`, `polyTime_tail`, `polyTime_cons`;
* `polyTime_replicate_powerBound` — a word of any prescribed polynomial length;
* `polyTime_iterate_on` — bounded iteration where the size bound is only required on a
  set `D` of "good" inputs (the iteration is clamped by a polynomial-length ruler, so the
  resulting function is polynomial-time on *all* inputs and correct on `D`).
-/

@[expose] public section

namespace Complexity.PT

open Complexity.Reg

/-- The library's `Complexity.iterate` is Mathlib's `Nat.iterate`. -/
theorem iterate_eq {α : Type} (f : α → α) (n : Nat) (x : α) :
    Complexity.iterate f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- The output of a polynomial-time function is polynomially bounded in length. -/
theorem polyTime_length_le {f : Word → Word} (hf : PolyTime f) :
    ∃ c k, ∀ x, (f x).length ≤ powerBound c k x.length := by
  obtain ⟨c, e, h⟩ := TimeBounded.of_polyTime hf
  obtain ⟨c', k', h'⟩ := PolynomialBound.identity.add
    ((PolynomialBound.constant 2).mul (PolynomialBound.power c e))
  exact ⟨c', k', fun x => Nat.le_trans (h.length_le x) (h' x.length)⟩

/-! ### The unary prefix of a word -/

/-- The leading block of `true`s of a word. -/
def leadingOnes (w : Word) : Word := List.replicate (stripOnes w 0).2 true

/-- What follows the leading block of `true`s and the `false` terminating it. -/
def afterOnes (w : Word) : Word := (stripOnes w 0).1

theorem stripOnes_ones (n : Nat) (z : Word) :
    stripOnes (List.replicate n true ++ false :: z) 0 = (z, n) := by
  simpa using stripOnes_replicate n 0 z

@[simp] theorem leadingOnes_ones (n : Nat) (z : Word) :
    leadingOnes (List.replicate n true ++ false :: z) = List.replicate n true := by
  simp [leadingOnes, stripOnes_ones]

@[simp] theorem afterOnes_ones (n : Nat) (z : Word) :
    afterOnes (List.replicate n true ++ false :: z) = z := by
  simp [afterOnes, stripOnes_ones]

theorem unpair_ones (n : Nat) (z : Word) :
    unpair (List.replicate n true ++ false :: z) = (z.take n, z.drop n) := by
  simp [unpair, stripOnes_ones]

theorem polyTime_afterOnes : PolyTime afterOnes := by
  refine polyTime_of_cmd_ofList stripCmd sound_stripCmd _ (fun n => 4 * n + 5)
    (((PolynomialBound.constant 4).mul PolynomialBound.identity).add
      (PolynomialBound.constant 5)) ?_
  intro w
  exact ⟨_, _, exec_stripCmd w, Nat.le_refl _, rfl⟩

/-- Registers: `0` input/output, `1` counter, `2` unused, `3` flag. -/
def leadingOnesCmd : Cmd 3 := .seq stripCmd (.seq (clear 0) (move 1 0))

theorem polyTime_leadingOnes : PolyTime leadingOnes := by
  refine polyTime_of_cmd_ofList leadingOnesCmd ⟨sound_stripCmd, sound_clear 0, sound_move 1 0⟩ _
    (fun n => 10 * n + 7)
    (((PolynomialBound.constant 10).mul PolynomialBound.identity).add
      (PolynomialBound.constant 7)) ?_
  intro w
  have hl := stripOnes_length_le w 0
  have h1 := exec_stripCmd w
  have h2 : Exec (clear 0)
      (ofList [(stripOnes w 0).1, List.replicate (stripOnes w 0).2 true, [], []] : Regs 3)
      (2 * w.length + 1) (ofList [[], List.replicate (stripOnes w 0).2 true, [], []]) :=
    (exec_clear 0 _).cast (by regs) (by regs_simp; omega)
  have h3 : Exec (move 1 0)
      (ofList [[], List.replicate (stripOnes w 0).2 true, [], []] : Regs 3)
      (4 * w.length + 1) (ofList [leadingOnes w, [], [], []]) :=
    (exec_move 1 0 (by decide) _).cast (by regs_simp; simp [leadingOnes])
      (by regs_simp; simp only [List.length_replicate]; omega)
  exact ⟨_, _, .seq h1 (.seq h2 h3), by omega, rfl⟩

/-! ### Derived word functions -/

/-- The all-ones word of the same length. -/
theorem polyTime_ones {G : Word → Word} (hG : PolyTime G) :
    PolyTime (fun x => List.replicate (G x).length true) :=
  polyTime_congr (fun x => by simp [pairWords])
    (polyTime_comp polyTime_leadingOnes (polyTime_pair hG (polyTime_const [])))

theorem polyTime_cons (b : Bool) {G : Word → Word} (hG : PolyTime G) :
    PolyTime (fun x => b :: G x) :=
  polyTime_congr (fun _ => rfl) (polyTime_append (polyTime_const [b]) hG)

/-- `(G x).take |L x|`. -/
theorem polyTime_take {L G : Word → Word} (hL : PolyTime L) (hG : PolyTime G) :
    PolyTime (fun x => (G x).take (L x).length) :=
  polyTime_congr (fun x => by simp [unpair_ones])
    (polyTime_comp polyTime_pair_fst (polyTime_append (polyTime_ones hL) (polyTime_cons false hG)))

/-- `(G x).drop |L x|`. -/
theorem polyTime_drop {L G : Word → Word} (hL : PolyTime L) (hG : PolyTime G) :
    PolyTime (fun x => (G x).drop (L x).length) :=
  polyTime_congr (fun x => by simp [unpair_ones])
    (polyTime_comp polyTime_pair_snd (polyTime_append (polyTime_ones hL) (polyTime_cons false hG)))

theorem polyTime_tail {G : Word → Word} (hG : PolyTime G) : PolyTime (fun x => (G x).tail) :=
  polyTime_congr (fun x => by simp) (polyTime_drop (polyTime_const [true]) hG)

/-- The first bit, as a word of length at most one. -/
theorem polyTime_take_one {G : Word → Word} (hG : PolyTime G) :
    PolyTime (fun x => (G x).take 1) :=
  polyTime_congr (fun x => by simp) (polyTime_take (polyTime_const [true]) hG)

/-! ### All-ones words of polynomial length -/

theorem polyTime_replicate_add {m n : Word → Nat}
    (hm : PolyTime (fun x => List.replicate (m x) true))
    (hn : PolyTime (fun x => List.replicate (n x) true)) :
    PolyTime (fun x => List.replicate (m x + n x) true) :=
  polyTime_congr (fun x => by simp) (polyTime_append hm hn)

/-- One step of the multiplication loop: `(u, acc) ↦ (u, u ++ acc)`. -/
def mulStep (w : Word) : Word := pairWords (unpair w).1 ((unpair w).1 ++ (unpair w).2)

theorem polyTime_mulStep : PolyTime mulStep :=
  polyTime_pair polyTime_pair_fst (polyTime_append polyTime_pair_fst polyTime_pair_snd)

theorem mulStep_iterate (n i j : Nat) :
    mulStep^[i] (pairWords (List.replicate n true) (List.replicate j true)) =
      pairWords (List.replicate n true) (List.replicate (i * n + j) true) := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    have h : mulStep (pairWords (List.replicate n true) (List.replicate j true)) =
        pairWords (List.replicate n true) (List.replicate (n + j) true) := by
      simp [mulStep]
    rw [Function.iterate_succ_apply, h, ih, Nat.succ_mul, Nat.add_assoc]

theorem polyTime_replicate_mul {m n : Word → Nat}
    (hm : PolyTime (fun x => List.replicate (m x) true))
    (hn : PolyTime (fun x => List.replicate (n x) true)) :
    PolyTime (fun x => List.replicate (m x * n x) true) := by
  obtain ⟨cm, km, hlm⟩ := polyTime_length_le hm
  obtain ⟨cn, kn, hln⟩ := polyTime_length_le hn
  simp only [List.length_replicate] at hlm hln
  have key : ∀ n i : Nat, mulStep^[i] (pairWords (List.replicate n true) []) =
      pairWords (List.replicate n true) (List.replicate (i * n) true) := fun n i => by
    simpa using mulStep_iterate n i 0
  have hit := polyTime_iterate polyTime_mulStep (polyTime_pair hn (polyTime_const [])) hm
    (fun l => 2 * powerBound cn kn l + 1 + powerBound cm km l * powerBound cn kn l)
    ((((PolynomialBound.constant 2).mul (PolynomialBound.power cn kn)).add
      (PolynomialBound.constant 1)).add
      ((PolynomialBound.power cm km).mul (PolynomialBound.power cn kn))) ?_
  · refine polyTime_congr (fun x => ?_) (polyTime_comp polyTime_pair_snd hit)
    simp only [iterate_eq, List.length_replicate, key, unpair_pairWords]
  · intro x i hi
    simp only [List.length_replicate] at hi
    simp only [iterate_eq, key, pairWords_length, List.length_replicate]
    have h1 := hln x
    have h2 := Nat.mul_le_mul (Nat.le_trans hi (hlm x)) h1
    omega

theorem polyTime_replicate_pow {m : Word → Nat}
    (hm : PolyTime (fun x => List.replicate (m x) true)) (k : Nat) :
    PolyTime (fun x => List.replicate (m x ^ k) true) := by
  induction k with
  | zero => simpa using polyTime_const [true]
  | succ k ih => simpa only [Nat.pow_succ] using polyTime_replicate_mul ih hm

/-- An all-ones word of any prescribed polynomial length. -/
theorem polyTime_replicate_powerBound (c k : Nat) :
    PolyTime (fun x : Word => List.replicate (powerBound c k x.length) true) := by
  have h1 : PolyTime (fun x : Word => List.replicate (x.length + 1) true) :=
    polyTime_replicate_add (polyTime_ones polyTime_id) (polyTime_const [true])
  exact polyTime_congr (fun x => by rw [powerBound_eq])
    (polyTime_replicate_mul (m := fun _ => c) (polyTime_const _) (polyTime_replicate_pow h1 k))

/-! ### Clamped iteration -/

/-- A step of the clamped iteration: the state `(u, s)` becomes `(u, (step s).take |u|)`. -/
def truncStep (step : Word → Word) (w : Word) : Word :=
  pairWords (unpair w).1 ((step (unpair w).2).take (unpair w).1.length)

theorem polyTime_truncStep {step : Word → Word} (hstep : PolyTime step) :
    PolyTime (truncStep step) :=
  polyTime_pair polyTime_pair_fst
    (polyTime_take polyTime_pair_fst (polyTime_comp hstep polyTime_pair_snd))

theorem truncStep_pairWords (step : Word → Word) (u s : Word) :
    truncStep step (pairWords u s) = pairWords u ((step s).take u.length) := by
  simp [truncStep]

theorem truncStep_iterate_bounded (step : Word → Word) (u : Word) (i : Nat) (s : Word)
    (hs : s.length ≤ u.length) :
    ∃ s', (truncStep step)^[i] (pairWords u s) = pairWords u s' ∧ s'.length ≤ u.length := by
  induction i generalizing s with
  | zero => exact ⟨s, rfl, hs⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply, truncStep_pairWords]
    exact ih _ (by rw [List.length_take]; omega)

theorem truncStep_iterate_eq (step : Word → Word) (u : Word) (i : Nat) (s : Word)
    (h : ∀ j, j ≤ i → (step^[j] s).length ≤ u.length) :
    (truncStep step)^[i] (pairWords u s) = pairWords u (step^[i] s) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    have h1 : (step s).length ≤ u.length := h 1 (by omega)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, truncStep_pairWords,
      List.take_of_length_le h1]
    exact ih _ (fun j hj => h (j + 1) (by omega))

/-- **Bounded iteration on a set of good inputs.**  If the intermediate values of the
iteration are polynomially bounded for every input in `D`, then some polynomial-time
function agrees with the iteration on `D`. -/
theorem polyTime_iterate_on (D : Word → Prop) {step init count : Word → Word}
    (hstep : PolyTime step) (hinit : PolyTime init) (hcount : PolyTime count)
    (size : Nat → Nat) (hsize : PolynomialBound size)
    (hbound : ∀ x, D x → ∀ i, i ≤ (count x).length →
      (step^[i] (init x)).length ≤ size x.length) :
    ∃ G : Word → Word, PolyTime G ∧ ∀ x, D x → G x = step^[(count x).length] (init x) := by
  obtain ⟨c, k, hck⟩ := hsize
  have hB := polyTime_replicate_powerBound c k
  have hit := polyTime_iterate (polyTime_truncStep hstep)
    (polyTime_pair hB (polyTime_take hB hinit)) hcount
    (fun n => 3 * powerBound c k n + 1)
    (((PolynomialBound.constant 3).mul (PolynomialBound.power c k)).add
      (PolynomialBound.constant 1)) ?_
  · refine ⟨_, polyTime_comp polyTime_pair_snd hit, fun x hx => ?_⟩
    have h0 : (init x).length ≤ powerBound c k x.length :=
      Nat.le_trans (hbound x hx 0 (Nat.zero_le _)) (hck _)
    simp only [iterate_eq, List.length_replicate]
    rw [List.take_of_length_le h0, truncStep_iterate_eq, unpair_pairWords]
    intro j hj
    rw [List.length_replicate]
    exact Nat.le_trans (hbound x hx j hj) (hck _)
  · intro x i _
    obtain ⟨s', hs', hlen⟩ := truncStep_iterate_bounded step
      (List.replicate (powerBound c k x.length) true) i
      ((init x).take (List.replicate (powerBound c k x.length) true).length)
      (by rw [List.length_take]; omega)
    simp only [iterate_eq]
    rw [hs', pairWords_length]
    simp only [List.length_replicate] at hlen ⊢
    omega

end Complexity.PT
