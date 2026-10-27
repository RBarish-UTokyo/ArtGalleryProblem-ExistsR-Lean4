module

public import ArtGallery.PTime.Scan

/-!
# Codes for ETR-INV instances

* `Code ETRINV.Constraint` through `ETRINV.Constraint.toSum` (into `ℕ ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ)`);
  `Code (List ETRINV.Constraint)` is then the list code;
* case analysis `ETRINV.Constraint.elim` with `PT.constraintElim`, constructors
  `PT.constraintOne`, `PT.constraintAdd`, `PT.constraintInv`;
* `PT.constraintEncode`, `PT.invEncode`: the raw codes of `ArtGallery.Spec` are polynomial-time;
* `ETRINV.decodeINV : Word → Option (List ETRINV.Constraint)`, with round trip
  `ETRINV.decodeINV_encode`, soundness `ETRINV.encode_of_decodeINV`, injectivity
  `ETRINV.encode_injective` and `PT.decodeINV`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETRINV

/-- An equation as a sum: `x = 1`, `x + y = z`, `x · y = 1`. -/
def Constraint.toSum : Constraint → ℕ ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ)
  | .one x => .inl x
  | .add x y z => .inr (.inl (x, y, z))
  | .inv x y => .inr (.inr (x, y))

/-- The inverse of `Constraint.toSum`. -/
def Constraint.ofSum : ℕ ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ) → Constraint
  | .inl x => .one x
  | .inr (.inl (x, y, z)) => .add x y z
  | .inr (.inr (x, y)) => .inv x y

theorem Constraint.ofSum_toSum (c : Constraint) : Constraint.ofSum c.toSum = c := by
  cases c <;> rfl

/-- Equations are coded as sums. -/
instance instCodeConstraint : Code Constraint :=
  Code.ofInj Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum

theorem size_constraint (c : Constraint) : size c = size c.toSum := rfl

@[simp] theorem size_one (x : ℕ) : size (Constraint.one x) = x + 2 := by
  simp [size_constraint, Constraint.toSum]

@[simp] theorem size_add (x y z : ℕ) : size (Constraint.add x y z) = x + y + z + 5 := by
  simp [size_constraint, Constraint.toSum]
  omega

@[simp] theorem size_inv (x y : ℕ) : size (Constraint.inv x y) = x + y + 4 := by
  simp [size_constraint, Constraint.toSum]
  omega

/-- Case analysis on an equation. -/
def Constraint.elim {β : Type} (f₁ : ℕ → β) (f₂ : ℕ → ℕ → ℕ → β) (f₃ : ℕ → ℕ → β) :
    Constraint → β
  | .one x => f₁ x
  | .add x y z => f₂ x y z
  | .inv x y => f₃ x y

theorem Constraint.elim_eq {β : Type} (f₁ : ℕ → β) (f₂ : ℕ → ℕ → ℕ → β) (f₃ : ℕ → ℕ → β)
    (c : Constraint) : c.elim f₁ f₂ f₃ =
      Sum.elim f₁ (Sum.elim (fun q => f₂ q.1 q.2.1 q.2.2) (fun q => f₃ q.1 q.2)) c.toSum := by
  cases c <;> rfl

/-- The raw code of an equation by cases. -/
theorem Constraint.encode_eq_elim (c : Constraint) : c.encode = c.elim
    (fun x => [false, false] ++ ArtGallery.unary x)
    (fun x y z => [false, true] ++ ArtGallery.unary x ++ ArtGallery.unary y ++ ArtGallery.unary z)
    (fun x y => [true, false] ++ ArtGallery.unary x ++ ArtGallery.unary y) := by
  cases c <;> rfl

/-- The raw code of an instance. -/
theorem encode_eq_flatMap (Φ : List Constraint) :
    encode Φ = Φ.flatMap (fun c => true :: c.encode) ++ [false] := by
  induction Φ with
  | nil => rfl
  | cons c Φ ih =>
    simp only [encode, encodeList] at ih ⊢
    rw [ih]
    simp

end ETRINV

open ETRINV

section PTLemmas

variable {α β : Type} [Code α] [Code β]

@[fun_prop] protected theorem PT.constraintToSum {c : α → Constraint} (hc : PT c) :
    PT (fun a => (c a).toSum) :=
  (PT.ofInj_to Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum).comp hc

theorem PT.constraint_of_toSum {c : α → Constraint} (h : PT (fun a => (c a).toSum)) : PT c :=
  PT.ofInj_mk Constraint.toSum Constraint.ofSum Constraint.ofSum_toSum h

@[fun_prop] protected theorem PT.constraintOne {x : α → ℕ} (hx : PT x) :
    PT (fun a => Constraint.one (x a)) :=
  PT.constraint_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.constraintAdd {x y z : α → ℕ} (hx : PT x) (hy : PT y)
    (hz : PT z) : PT (fun a => Constraint.add (x a) (y a) (z a)) :=
  PT.constraint_of_toSum (by simp only [Constraint.toSum]; fun_prop)

@[fun_prop] protected theorem PT.constraintInv {x y : α → ℕ} (hx : PT x) (hy : PT y) :
    PT (fun a => Constraint.inv (x a) (y a)) :=
  PT.constraint_of_toSum (by simp only [Constraint.toSum]; fun_prop)

/-- Case analysis on an equation (the branches in uncurried form). -/
@[fun_prop] protected theorem PT.constraintElim {c : α → Constraint} {f₁ : α → ℕ → β}
    {f₂ : α → ℕ → ℕ → ℕ → β} {f₃ : α → ℕ → ℕ → β}
    (h₁ : PT (fun p : α × ℕ => f₁ p.1 p.2))
    (h₂ : PT (fun p : α × ℕ × ℕ × ℕ => f₂ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h₃ : PT (fun p : α × ℕ × ℕ => f₃ p.1 p.2.1 p.2.2)) (hc : PT c) :
    PT (fun a => (c a).elim (f₁ a) (f₂ a) (f₃ a)) := by
  have h : PT (fun a => Sum.elim (f₁ a) (Sum.elim (fun q => f₂ a q.1 q.2.1 q.2.2)
      (fun q => f₃ a q.1 q.2)) (c a).toSum) :=
    PT.sumElim h₁ (PT.sumElim (h₂.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
      (h₃.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id))) PT.snd') (PT.constraintToSum hc)
  exact h.of_eq fun a => (Constraint.elim_eq _ _ _ (c a)).symm

/-- The raw code of an equation. -/
@[fun_prop] protected theorem PT.constraintEncode {c : α → Constraint} (hc : PT c) :
    PT (fun a => (c a).encode) := by
  have h : PT (fun a => (c a).elim
      (fun x => [false, false] ++ ArtGallery.unary x)
      (fun x y z => [false, true] ++ ArtGallery.unary x ++ ArtGallery.unary y ++ ArtGallery.unary z)
      (fun x y => [true, false] ++ ArtGallery.unary x ++ ArtGallery.unary y)) :=
    PT.constraintElim (f₁ := fun _ x => [false, false] ++ ArtGallery.unary x)
      (f₂ := fun _ x y z => [false, true] ++ ArtGallery.unary x ++ ArtGallery.unary y ++
        ArtGallery.unary z)
      (f₃ := fun _ x y => [true, false] ++ ArtGallery.unary x ++ ArtGallery.unary y)
      (by fun_prop) (by fun_prop) (by fun_prop) hc
  exact h.of_eq fun a => (Constraint.encode_eq_elim (c a)).symm

/-- The raw code of an ETR-INV instance (`ArtGallery.ETRINV.encode`). -/
@[fun_prop] protected theorem PT.invEncode {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => ETRINV.encode (Φ a)) := by
  have h : PT (fun a => (Φ a).flatMap (fun c => true :: c.encode) ++ [false]) := by fun_prop
  exact h.of_eq fun a => (encode_eq_flatMap (Φ a)).symm

end PTLemmas

/-! ### Decoding -/

namespace ETRINV

/-- One step of the decoding scan on the state `(rest, reversed equations)`: read `1`, a two-bit
tag and the unary indices. -/
def invStep (s : Word × List Constraint) : Word × List Constraint :=
  if s.1.head? = some true then
    if s.1.getD 1 false = false ∧ s.1.getD 2 false = false then
      ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1), .one (leadOnes (s.1.drop 3)) :: s.2)
    else if s.1.getD 1 false = false then
      ((((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)).drop
          (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)) + 1)).drop
          (leadOnes (((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)).drop
            (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)) + 1)) + 1),
        .add (leadOnes (s.1.drop 3)) (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)))
          (leadOnes (((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)).drop
            (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)) + 1))) :: s.2)
    else
      (((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)).drop
          (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)) + 1),
        .inv (leadOnes (s.1.drop 3)) (leadOnes ((s.1.drop 3).drop (leadOnes (s.1.drop 3) + 1)))
          :: s.2)
  else s

/-- The equations read from a word (correct on codes). -/
def guessINV (w : Word) : List Constraint := (invStep^[w.length] (w, [])).2.reverse

/-- Decode a raw word as an ETR-INV instance: scan, and check by re-encoding. -/
def decodeINV (w : Word) : Option (List Constraint) :=
  if encode (guessINV w) = w then some (guessINV w) else none

theorem invStep_code (c : Constraint) (r : Word) (acc : List Constraint) :
    invStep (true :: (c.encode ++ r), acc) = (r, c :: acc) := by
  cases c with
  | one x => simp [invStep, Constraint.encode]
  | add x y z => simp [invStep, Constraint.encode]
  | inv x y => simp [invStep, Constraint.encode]

theorem invStep_iterate (Φ : List Constraint) (r : Word) (acc : List Constraint) :
    invStep^[Φ.length] (Φ.flatMap (fun c => true :: c.encode) ++ r, acc) =
      (r, Φ.reverse ++ acc) := by
  induction Φ generalizing acc with
  | nil => simp
  | cons c Φ ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc]
    rw [invStep_code, ih]
    simp

theorem guessINV_encode (Φ : List Constraint) : guessINV (encode Φ) = Φ := by
  have hlen : Φ.length ≤ (Φ.flatMap (fun c => true :: c.encode)).length :=
    length_le_length_flatMap _ _ fun c _ => by simp
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hlen
  have hfix : invStep ([false], Φ.reverse) = ([false], Φ.reverse) := by simp [invStep]
  unfold guessINV
  rw [encode_eq_flatMap, List.length_append, he, List.length_singleton,
    show Φ.length + e + 1 = (e + 1) + Φ.length by omega, Function.iterate_add_apply,
    invStep_iterate, iterate_fixed _ _ (by simpa using hfix)]
  simp

/-- **Round trip.** -/
theorem decodeINV_encode (Φ : List Constraint) : decodeINV (encode Φ) = some Φ := by
  unfold decodeINV
  rw [guessINV_encode]
  simp

/-- **Soundness.** -/
theorem encode_of_decodeINV {w : Word} {Φ : List Constraint} (h : decodeINV w = some Φ) :
    encode Φ = w := by
  unfold decodeINV at h
  split_ifs at h with h'
  cases h
  exact h'

theorem encode_injective : Function.Injective ETRINV.encode := fun Φ Ψ h => by
  have h1 := decodeINV_encode Φ
  rw [h, decodeINV_encode Ψ] at h1
  exact (Option.some.inj h1).symm

/-- Membership of a code in `ETRINV`. -/
theorem ETRINV_encode_iff (Φ : List Constraint) : ETRINV (encode Φ) ↔ Satisfiable Φ :=
  ⟨fun ⟨_, h, hs⟩ => encode_injective h ▸ hs, fun h => ⟨Φ, rfl, h⟩⟩

/-- The size invariant of the decoding scan. -/
theorem invStep_inv (n i : ℕ) (s : Word × List Constraint)
    (h : s.1.length ≤ n ∧ size s.2 ≤ i * (3 * n + 10) + 1) :
    (invStep s).1.length ≤ n ∧ size (invStep s).2 ≤ (i + 1) * (3 * n + 10) + 1 := by
  obtain ⟨r, acc⟩ := s
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hm : (i + 1) * (3 * n + 10) = i * (3 * n + 10) + (3 * n + 10) := Nat.succ_mul _ _
  rw [hm]
  generalize i * (3 * n + 10) = M at h2 ⊢
  have hx := leadOnes_le (r.drop 3)
  have hy := leadOnes_le ((r.drop 3).drop (leadOnes (r.drop 3) + 1))
  have hz := leadOnes_le (((r.drop 3).drop (leadOnes (r.drop 3) + 1)).drop
    (leadOnes ((r.drop 3).drop (leadOnes (r.drop 3) + 1)) + 1))
  simp only [List.length_drop] at hx hy hz
  unfold invStep
  split_ifs <;> simp only [List.length_drop, size_cons, size_one, size_add, size_inv] <;>
    refine ⟨?_, ?_⟩ <;> omega

end ETRINV

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.invStep : PT invStep := by
  unfold invStep
  fun_prop

@[fun_prop] protected theorem PT.guessINV : PT guessINV := by
  have h := PT.iterate_const (step := invStep) (init := fun w : Word => (w, ([] : List Constraint)))
    (n := fun w : Word => w.length) PT.invStep (by fun_prop) (by fun_prop)
    (fun N => 2 * N + 2 + N * (3 * N + 10))
    ((((PolynomialBound.constant 2).mul PolynomialBound.identity).add
      (PolynomialBound.constant 2)).add (PolynomialBound.identity.mul
        (((PolynomialBound.constant 3).mul PolynomialBound.identity).add
          (PolynomialBound.constant 10)))) ?_
  · exact (PT.reverse (PT.snd h)).of_eq fun _ => rfl
  · intro w i hi
    have key := iterate_invariant invStep (fun i s => s.1.length ≤ w.length ∧
      size s.2 ≤ i * (3 * w.length + 10) + 1) (w, []) (by simp)
      (fun i s h => invStep_inv w.length i s h) i
    obtain ⟨h1, h2⟩ := key
    generalize invStep^[i] (w, []) = s at h1 h2
    obtain ⟨r, acc⟩ := s
    simp only at h1 h2
    have hw := size_word w
    have hm : i * (3 * w.length + 10) ≤ (2 * w.length + 1) * (3 * (2 * w.length + 1) + 10) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [size_prod, size_word]
    omega

/-- **The ETR-INV decoder is polynomial-time.** -/
@[fun_prop] protected theorem PT.decodeINV {w : α → Word} (hw : PT w) :
    PT (fun a => decodeINV (w a)) := by
  unfold decodeINV
  fun_prop

end ArtGallery

end
