module

public import ArtGallery.Spec

/-!
# Decoding art-gallery instances

The parser `decodeAGP : Word → Option (List FracPoint × ℕ)` inverts `encodeAGP`:

* `decodeAGP_encodeAGP : decodeAGP (encodeAGP V g) = some (V, g)`;
* `encodeAGP_of_decodeAGP : decodeAGP w = some (V, g) → encodeAGP V g = w`.

The parser reads the numbers (unary lengths, then binary digits), and finally checks that
re-encoding the result gives back the input word; this last check makes the second round-trip
lemma trivial and rejects non-canonical codes (leading zeros, negative zero).  All functions are
structurally recursive (the list parser uses the input length as fuel).
-/

@[expose] public section

namespace ArtGallery.Membership

open Complexity

/-- The natural number with binary digits `l`, least significant first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * ofBits l

/-- Reading back the binary digits of a number. -/
theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [ofBits, Nat.zero_bits]
    · have hd := Nat.bodd_add_div2 n
      have hb : Nat.div2 n = 0 → Nat.bodd n = true := by
        intro h0
        rw [h0] at hd
        cases hbo : Nat.bodd n
        · rw [hbo] at hd; simp at hd; exact absurd hd.symm hn
        · rfl
      have h2 := Nat.bits_append_bit (Nat.div2 n) (Nat.bodd n) hb
      rw [Nat.bit_bodd_div2] at h2
      rw [h2, ofBits, ih _ (Nat.binaryRec_decreasing hn)]
      exact hd

/-- Reads a number in unary (a block of ones closed by a zero). -/
def parseUnary : Word → Option (ℕ × Word)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => (parseUnary w).map fun r => (r.1 + 1, r.2)

theorem parseUnary_unary (k : ℕ) (w : Word) : parseUnary (unary k ++ w) = some (k, w) := by
  induction k with
  | zero => simp [unary, parseUnary]
  | succ k ih =>
    have h : unary (k + 1) ++ w = true :: (unary k ++ w) := by
      simp [unary, List.replicate_succ]
    rw [h, parseUnary, ih]
    rfl

/-- Reads a natural number in binary (`binaryNat`). -/
def parseNat (w : Word) : Option (ℕ × Word) :=
  (parseUnary w).bind fun r =>
    if r.1 ≤ r.2.length then some (ofBits (r.2.take r.1), r.2.drop r.1) else none

theorem parseNat_binaryNat (n : ℕ) (w : Word) : parseNat (binaryNat n ++ w) = some (n, w) := by
  have h : binaryNat n ++ w = unary n.bits.length ++ (n.bits ++ w) := by
    simp [binaryNat]
  rw [parseNat, h, parseUnary_unary]
  simp [ofBits_bits]

/-- Reads an integer in binary (`binaryInt`). -/
def parseInt : Word → Option (ℤ × Word)
  | [] => none
  | s :: w => (parseNat w).map fun r => (if s then -(r.1 : ℤ) else (r.1 : ℤ), r.2)

theorem parseInt_binaryInt (z : ℤ) (w : Word) : parseInt (binaryInt z ++ w) = some (z, w) := by
  simp only [binaryInt, List.cons_append, parseInt, parseNat_binaryNat, Option.map_some]
  by_cases h : z < 0
  · simp only [h, decide_true, ite_true, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Option.some.injEq,
      Prod.mk.injEq, and_true]
    exact Int.natAbs_of_nonneg (not_lt.1 h)

/-- Reads a vertex (`FracPoint.encode`). -/
def parseFrac (w : Word) : Option (FracPoint × Word) :=
  (parseInt w).bind fun r1 => (parseNat r1.2).bind fun r2 =>
    (parseInt r2.2).bind fun r3 => (parseNat r3.2).map fun r4 =>
      (⟨r1.1, r2.1, r3.1, r4.1⟩, r4.2)

theorem parseFrac_encode (p : FracPoint) (w : Word) :
    parseFrac (p.encode ++ w) = some (p, w) := by
  simp only [FracPoint.encode, List.append_assoc, parseFrac, parseInt_binaryInt,
    parseNat_binaryNat, Option.bind_some, Option.map_some]

/-- Reads a list of vertices (`encodeList FracPoint.encode`); the first argument is fuel. -/
def parseFracs : ℕ → Word → Option (List FracPoint × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: w => some ([], w)
  | k + 1, true :: w =>
    (parseFrac w).bind fun r => (parseFracs k r.2).map fun s => (r.1 :: s.1, s.2)

theorem parseFracs_encodeList (V : List FracPoint) (w : Word) (k : ℕ) (hk : V.length < k) :
    parseFracs k (encodeList FracPoint.encode V ++ w) = some (V, w) := by
  induction V generalizing k with
  | nil =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp [encodeList, parseFracs]
  | cons p V ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [List.length_cons] at hk
    simp only [encodeList, List.cons_append, List.append_assoc, parseFracs,
      parseFrac_encode, Option.bind_some, ih k (by omega), Option.map_some]

theorem length_encodeList_ge {α : Type} (e : α → Word) (V : List α) :
    V.length + 1 ≤ (encodeList e V).length := by
  induction V with
  | nil => simp [encodeList]
  | cons a V ih => simp [encodeList]; omega

/-- The raw parser of an instance, without the final canonicity check. -/
def parseAGP (w : Word) : Option (List FracPoint × ℕ) :=
  (parseFracs w.length w).bind fun r => (parseNat r.2).bind fun s =>
    if s.2 = [] then some (r.1, s.1) else none

theorem parseAGP_encodeAGP (V : List FracPoint) (g : ℕ) :
    parseAGP (encodeAGP V g) = some (V, g) := by
  have hlen : V.length < (encodeAGP V g).length := by
    have := length_encodeList_ge FracPoint.encode V
    simp only [encodeAGP, List.length_append]
    omega
  unfold parseAGP
  rw [show encodeAGP V g = encodeList FracPoint.encode V ++ binaryNat g from rfl] at hlen ⊢
  rw [parseFracs_encodeList V _ _ hlen]
  have h2 := parseNat_binaryNat g []
  rw [List.append_nil] at h2
  simp [h2]

/-- **Decoding** of an art-gallery instance: the vertex list and the number of guards, if the
word is the code of an instance. -/
def decodeAGP (w : Word) : Option (List FracPoint × ℕ) :=
  (parseAGP w).bind fun r => if encodeAGP r.1 r.2 = w then some r else none

theorem decodeAGP_encodeAGP (V : List FracPoint) (g : ℕ) :
    decodeAGP (encodeAGP V g) = some (V, g) := by
  simp [decodeAGP, parseAGP_encodeAGP]

theorem encodeAGP_of_decodeAGP {w : Word} {V : List FracPoint} {g : ℕ}
    (h : decodeAGP w = some (V, g)) : encodeAGP V g = w := by
  unfold decodeAGP at h
  cases hp : parseAGP w with
  | none => rw [hp] at h; simp at h
  | some r =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split_ifs at h with he
    · cases h; exact he

/-- Membership in `AGP` through the decoder. -/
theorem AGP_iff_decode (w : Word) :
    AGP w ↔ ∃ V g, decodeAGP w = some (V, g) ∧ (∀ p ∈ V, p.Valid) ∧
      (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
      (Polygon.mk (V.map FracPoint.toPoint)).HasGuardSetOfCard g := by
  constructor
  · rintro ⟨V, g, rfl, h⟩
    exact ⟨V, g, decodeAGP_encodeAGP V g, h⟩
  · rintro ⟨V, g, hd, h⟩
    exact ⟨V, g, encodeAGP_of_decodeAGP hd, h⟩

end ArtGallery.Membership

end
