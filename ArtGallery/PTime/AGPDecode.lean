module

public import ArtGallery.PTime.Binary

/-!
# Decoding art-gallery instances

The numbers of an art-gallery instance are written in binary, so they are returned as digit lists
(least significant first, `Nat.bits`); an integer is returned as its sign and the digits of its
absolute value (`intDigits`).

* `FracDigits`, `FracPoint.digits`, `FracPoint.ofDigits` (with `FracPoint.ofDigits_digits`);
* `decodeAGP : Word → Option (List FracDigits × Word)`:
  `decodeAGP_encodeAGP : decodeAGP (encodeAGP V g) = some (V.map FracPoint.digits, g.bits)` and
  `decodeAGP_sound : decodeAGP w = some (D, gd) → ∃ V g, encodeAGP V g = w ∧
    V.map FracPoint.digits = D ∧ g.bits = gd`, `PT.decodeAGP`;
* `decodeAGPInt : Word → Option (List ((Bool × Word) × (Bool × Word)) × Word)` with
  `decodeAGPInt_encodeAGPInt`, `decodeAGPInt_sound`, `PT.decodeAGPInt`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

/-- The digits of a vertex: signs and digits of `xNum`, digits of `xDen`, of `yNum`, of `yDen`. -/
abbrev FracDigits := (Bool × Word) × Word × (Bool × Word) × Word

/-- The digits of a vertex. -/
def FracPoint.digits (p : FracPoint) : FracDigits :=
  (intDigits p.xNum, p.xDen.bits, intDigits p.yNum, p.yDen.bits)

/-- The vertex with given digits. -/
def FracPoint.ofDigits (D : FracDigits) : FracPoint :=
  ⟨intOfDigits D.1, SAT.binaryValue D.2.1, intOfDigits D.2.2.1, SAT.binaryValue D.2.2.2⟩

theorem FracPoint.ofDigits_digits (p : FracPoint) : FracPoint.ofDigits p.digits = p := by
  simp [FracPoint.ofDigits, FracPoint.digits, intOfDigits_intDigits, binaryValue_bits]

theorem FracPoint.digits_injective : Function.Injective FracPoint.digits := fun p q h => by
  rw [← FracPoint.ofDigits_digits p, h, FracPoint.ofDigits_digits]

/-- Valid digits of a vertex. -/
def fracDigitsOk (D : FracDigits) : Bool :=
  intDigitsOk D.1 && natDigitsOk D.2.1 && intDigitsOk D.2.2.1 && natDigitsOk D.2.2.2

theorem FracPoint.digits_ofDigits {D : FracDigits} (h : fracDigitsOk D = true) :
    (FracPoint.ofDigits D).digits = D := by
  obtain ⟨a, b, c, d⟩ := D
  simp only [fracDigitsOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  simp [FracPoint.ofDigits, FracPoint.digits, intDigits_intOfDigits ha, bits_binaryValue hb,
    intDigits_intOfDigits hc, bits_binaryValue hd]

theorem fracDigitsOk_digits (p : FracPoint) : fracDigitsOk p.digits = true := by
  simp [fracDigitsOk, FracPoint.digits, intDigitsOk_intDigits, natDigitsOk_bits]

/-- The code of a vertex with given digits. -/
def fracWord (D : FracDigits) : Word :=
  binIntWord D.1 ++ binWord D.2.1 ++ binIntWord D.2.2.1 ++ binWord D.2.2.2

theorem FracPoint.encode_eq_fracWord (p : FracPoint) : p.encode = fracWord p.digits := rfl

/-- Read the digits of a vertex at the start of a word. -/
def readFrac (w : Word) : FracDigits × Word :=
  (((readBinInt w).1, (readBin (readBinInt w).2).1,
      (readBinInt (readBin (readBinInt w).2).2).1,
      (readBin (readBinInt (readBin (readBinInt w).2).2).2).1),
    (readBin (readBinInt (readBin (readBinInt w).2).2).2).2)

theorem readFrac_fracWord (D : FracDigits) (r : Word) : readFrac (fracWord D ++ r) = (D, r) := by
  obtain ⟨a, b, c, d⟩ := D
  simp [readFrac, fracWord, List.append_assoc]

theorem map_map_eq_self {β γ : Type} (f : β → γ) (g : γ → β) (l : List β)
    (h : ∀ b ∈ l, g (f b) = b) : (l.map f).map g = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, h b (by simp), ih fun b' hb' => h b' (by simp [hb'])]

theorem encodeList_map {β γ : Type} (e : γ → Word) (f : β → γ) (l : List β) :
    encodeList e (l.map f) = encodeList (fun b => e (f b)) l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [encodeList, ih]

/-! ### Rational instances -/

/-- The code of an instance with given digits. -/
def agpWord (D : List FracDigits) (gd : Word) : Word := encodeList fracWord D ++ binWord gd

theorem encodeAGP_eq_agpWord (V : List FracPoint) (g : ℕ) :
    encodeAGP V g = agpWord (V.map FracPoint.digits) g.bits := by
  simp only [encodeAGP, agpWord, encodeList_map]
  rfl

/-- The check of `decodeAGP`: the scanned digits are valid and re-encode to the input. -/
def checkAGP (w : Word) (s : List FracDigits × Word) : Option (List FracDigits × Word) :=
  if (s.1.all fracDigitsOk && natDigitsOk (readBin s.2).1) = true ∧
      agpWord s.1 (readBin s.2).1 = w then
    some (s.1, (readBin s.2).1)
  else none

/-- Decode an art-gallery instance, returning the digits of the vertex data and of the number of
guards: scan, and check by re-encoding. -/
def decodeAGP (w : Word) : Option (List FracDigits × Word) := checkAGP w (scanList readFrac w)

/-- **Round trip.** -/
theorem decodeAGP_encodeAGP (V : List FracPoint) (g : ℕ) :
    decodeAGP (encodeAGP V g) = some (V.map FracPoint.digits, g.bits) := by
  have h : scanList readFrac (encodeAGP V g) = (V.map FracPoint.digits, binWord g.bits) := by
    rw [encodeAGP_eq_agpWord, agpWord]
    exact scanList_encodeList (fun D r => readFrac_fracWord D r) _ _
  have h2 : readBin (binWord g.bits) = (g.bits, []) := by simp
  unfold decodeAGP checkAGP
  rw [h]
  simp only [h2]
  rw [ite_eq_left ⟨by simp [fracDigitsOk_digits, natDigitsOk_bits],
    (encodeAGP_eq_agpWord V g).symm⟩]

/-- **Soundness.** -/
theorem decodeAGP_sound {w : Word} {D : List FracDigits} {gd : Word}
    (h : decodeAGP w = some (D, gd)) :
    ∃ (V : List FracPoint) (g : ℕ), encodeAGP V g = w ∧ V.map FracPoint.digits = D ∧
      g.bits = gd := by
  unfold decodeAGP checkAGP at h
  split_ifs at h with h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hok, hw⟩ := h'
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  refine ⟨(scanList readFrac w).1.map FracPoint.ofDigits,
    SAT.binaryValue (readBin (scanList readFrac w).2).1, ?_, ?_, bits_binaryValue hok.2⟩
  · rw [encodeAGP_eq_agpWord, bits_binaryValue hok.2,
      map_map_eq_self _ _ _ (fun D hD => FracPoint.digits_ofDigits (hok.1 D hD))]
    exact hw
  · exact map_map_eq_self _ _ _ (fun D hD => FracPoint.digits_ofDigits (hok.1 D hD))

/-! ### Integer instances -/

/-- The code of an integer vertex with given digits. -/
def intPointWord (D : (Bool × Word) × (Bool × Word)) : Word := binIntWord D.1 ++ binIntWord D.2

/-- Read the digits of an integer vertex at the start of a word. -/
def readIntPoint (w : Word) : ((Bool × Word) × (Bool × Word)) × Word :=
  (((readBinInt w).1, (readBinInt (readBinInt w).2).1), (readBinInt (readBinInt w).2).2)

theorem readIntPoint_intPointWord (D : (Bool × Word) × (Bool × Word)) (r : Word) :
    readIntPoint (intPointWord D ++ r) = (D, r) := by
  simp [readIntPoint, intPointWord, List.append_assoc]

/-- The digits of an integer vertex. -/
def intPointDigits (p : ℤ × ℤ) : (Bool × Word) × (Bool × Word) := (intDigits p.1, intDigits p.2)

/-- The code of an integer instance with given digits. -/
def agpIntWord (D : List ((Bool × Word) × (Bool × Word))) (gd : Word) : Word :=
  encodeList intPointWord D ++ binWord gd

theorem encodeAGPInt_eq_agpIntWord (V : List (ℤ × ℤ)) (g : ℕ) :
    encodeAGPInt V g = agpIntWord (V.map intPointDigits) g.bits := by
  simp only [encodeAGPInt, agpIntWord, encodeList_map]
  rfl

/-- The check of `decodeAGPInt`: the scanned digits are valid and re-encode to the input. -/
def checkAGPInt (w : Word) (s : List ((Bool × Word) × (Bool × Word)) × Word) :
    Option (List ((Bool × Word) × (Bool × Word)) × Word) :=
  if (s.1.all (fun D => intDigitsOk D.1 && intDigitsOk D.2) && natDigitsOk (readBin s.2).1) = true ∧
      agpIntWord s.1 (readBin s.2).1 = w then
    some (s.1, (readBin s.2).1)
  else none

/-- Decode an integer art-gallery instance, returning the digits: scan, and check by
re-encoding. -/
def decodeAGPInt (w : Word) : Option (List ((Bool × Word) × (Bool × Word)) × Word) :=
  checkAGPInt w (scanList readIntPoint w)

/-- **Round trip.** -/
theorem decodeAGPInt_encodeAGPInt (V : List (ℤ × ℤ)) (g : ℕ) :
    decodeAGPInt (encodeAGPInt V g) = some (V.map intPointDigits, g.bits) := by
  have h : scanList readIntPoint (encodeAGPInt V g) = (V.map intPointDigits, binWord g.bits) := by
    rw [encodeAGPInt_eq_agpIntWord, agpIntWord]
    exact scanList_encodeList (fun D r => readIntPoint_intPointWord D r) _ _
  have h2 : readBin (binWord g.bits) = (g.bits, []) := by simp
  unfold decodeAGPInt checkAGPInt
  rw [h]
  simp only [h2]
  rw [ite_eq_left ⟨by simp [intPointDigits, intDigitsOk_intDigits, natDigitsOk_bits],
    (encodeAGPInt_eq_agpIntWord V g).symm⟩]

/-- **Soundness.** -/
theorem decodeAGPInt_sound {w : Word} {D : List ((Bool × Word) × (Bool × Word))} {gd : Word}
    (h : decodeAGPInt w = some (D, gd)) :
    ∃ (V : List (ℤ × ℤ)) (g : ℕ), encodeAGPInt V g = w ∧ V.map intPointDigits = D ∧
      g.bits = gd := by
  unfold decodeAGPInt checkAGPInt at h
  split_ifs at h with h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hok, hw⟩ := h'
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have hD : ∀ D ∈ (scanList readIntPoint w).1,
      intPointDigits (intOfDigits D.1, intOfDigits D.2) = D := fun D hD => by
    obtain ⟨h1, h2⟩ := hok.1 D hD
    simp [intPointDigits, intDigits_intOfDigits h1, intDigits_intOfDigits h2]
  refine ⟨(scanList readIntPoint w).1.map (fun D => (intOfDigits D.1, intOfDigits D.2)),
    SAT.binaryValue (readBin (scanList readIntPoint w).2).1, ?_, ?_, bits_binaryValue hok.2⟩
  · rw [encodeAGPInt_eq_agpIntWord, bits_binaryValue hok.2, map_map_eq_self _ _ _ hD]
    exact hw
  · exact map_map_eq_self _ _ _ hD

/-! ### Polynomial time -/

theorem readFrac_bound (x : Word) :
    (readFrac x).2.length ≤ x.length ∧ size (readFrac x).1 ≤ 8 * (x.length + 1) := by
  have h1 := length_readBinInt_snd x
  have s1 := size_readBinInt_fst x
  have h2 := length_readBin_snd (readBinInt x).2
  have s2 := length_readBin_fst (readBinInt x).2
  have h3 := length_readBinInt_snd (readBin (readBinInt x).2).2
  have s3 := size_readBinInt_fst (readBin (readBinInt x).2).2
  have h4 := length_readBin_snd (readBinInt (readBin (readBinInt x).2).2).2
  have s4 := length_readBin_fst (readBinInt (readBin (readBinInt x).2).2).2
  simp only [readFrac, size_prod, size_word, size_bool] at s1 s3 ⊢
  constructor <;> omega

theorem readIntPoint_bound (x : Word) :
    (readIntPoint x).2.length ≤ x.length ∧ size (readIntPoint x).1 ≤ 4 * (x.length + 1) := by
  have h1 := length_readBinInt_snd x
  have s1 := size_readBinInt_fst x
  have h2 := length_readBinInt_snd (readBinInt x).2
  have s2 := size_readBinInt_fst (readBinInt x).2
  simp only [readIntPoint, size_prod, size_word, size_bool] at s1 s2 ⊢
  constructor <;> omega

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.readFrac : PT readFrac := by
  unfold readFrac
  fun_prop

@[fun_prop] protected theorem PT.readIntPoint : PT readIntPoint := by
  unfold readIntPoint
  fun_prop

@[fun_prop] protected theorem PT.fracWord {D : α → FracDigits} (hD : PT D) :
    PT (fun a => fracWord (D a)) := by
  unfold fracWord
  fun_prop

@[fun_prop] protected theorem PT.fracDigitsOk {D : α → FracDigits} (hD : PT D) :
    PT (fun a => fracDigitsOk (D a)) := by
  unfold fracDigitsOk
  fun_prop

@[fun_prop] protected theorem PT.intPointWord {D : α → (Bool × Word) × (Bool × Word)}
    (hD : PT D) : PT (fun a => intPointWord (D a)) := by
  unfold intPointWord
  fun_prop

/-- `encodeList` of a polynomial-time element code. -/
@[fun_prop] protected theorem PT.encodeList {β : Type} [Code β] {e : β → Word} (he : PT e)
    {l : α → List β} (hl : PT l) : PT (fun a => encodeList e (l a)) := by
  have h : PT (fun a => (l a).flatMap (fun b => true :: e b) ++ [false]) := by fun_prop
  exact h.of_eq fun a => (encodeList_eq_flatMap e (l a)).symm

/-- **The decoder of art-gallery instances is polynomial-time.** -/
@[fun_prop] protected theorem PT.decodeAGP {w : α → Word} (hw : PT w) :
    PT (fun a => decodeAGP (w a)) := by
  have hs : PT (scanList readFrac) := PT.scanList PT.readFrac 8 readFrac_bound
  have hf : PT fracWord := PT.fracWord PT.id
  have hc : PT (fun p : Word × (List FracDigits × Word) => checkAGP p.1 p.2) := by
    unfold checkAGP agpWord
    fun_prop
  exact (hc.comp (PT.pair hw (hs.comp hw))).of_eq fun _ => rfl

/-- **The decoder of integer art-gallery instances is polynomial-time.** -/
@[fun_prop] protected theorem PT.decodeAGPInt {w : α → Word} (hw : PT w) :
    PT (fun a => decodeAGPInt (w a)) := by
  have hs : PT (scanList readIntPoint) := PT.scanList PT.readIntPoint 4 readIntPoint_bound
  have hf : PT intPointWord := PT.intPointWord PT.id
  have hc : PT (fun p : Word × (List ((Bool × Word) × (Bool × Word)) × Word) =>
      checkAGPInt p.1 p.2) := by
    unfold checkAGPInt agpIntWord
    fun_prop
  exact (hc.comp (PT.pair hw (hs.comp hw))).of_eq fun _ => rfl

end ArtGallery

end
