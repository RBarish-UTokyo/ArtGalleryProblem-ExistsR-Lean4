module

public import PT.Raw

/-!
# More of the interface between `PT` and raw `PolyTime` functions

A `PT` function of two arguments yields a polynomial-time word function on the pairing
`pairWords u v` of its arguments, where each argument is either the code of a value or a raw
word, and the result is either a code or (for word-valued functions) a raw word:

| lemma | input | output |
| --- | --- | --- |
| `PT.exists_polyTime` | `enc a` | `enc (f a)` |
| `PT.exists_polyTime_word` | `enc a` | `f a` |
| `PT.exists_polyTime_pairWords` | `pairWords (enc a) (enc b)` | `enc (h a b)` |
| `PT.exists_polyTime_pairWords_raw` | `pairWords (enc a) y` | `enc (h a y)` |
| `PT.exists_polyTime_pairWords_raw_left` | `pairWords x (enc b)` | `enc (h x b)` |
| `PT.exists_polyTime_pairWords_raw_raw` | `pairWords x y` | `enc (h x y)` |
| `PT.exists_polyTime_pairWords_word` etc. | as above | `h a b` |

For Boolean functions the code `enc b = [b]` is the usual `[true]`/`[false]` answer:
`PT.polyTime_bool`, `PT.polyTime_bool_pairWords`, `PT.exists_polyTime_pairWords_bool`, ….
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β γ : Type} [Code α] [Code β] [Code γ]

@[simp] theorem afterOnes_pairWords (x y : Word) : afterOnes (pairWords x y) = x ++ y := by
  rw [pairWords, afterOnes_ones]

theorem enc_bool_eq_ite (b : Bool) : (enc b : Word) = if b then [true] else [false] := by
  cases b <;> rfl

/-! ### Codes as outputs -/

/-- A `PT` function is computed on codes by a polynomial-time word function (this is the
definition of `PT`). -/
theorem PT.exists_polyTime {f : α → β} (hf : PT f) :
    ∃ F : Word → Word, PolyTime F ∧ ∀ a, F (Code.enc a) = Code.enc (f a) := hf

/-- A two-argument `PT` function yields a polynomial-time word function on `pairWords` of
codes. -/
theorem PT.exists_polyTime_pairWords {h : α → β → γ} (hh : PT (fun p : α × β => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧
      ∀ a b, G (pairWords (Code.enc a) (Code.enc b)) = Code.enc (h a b) := by
  obtain ⟨F, hF, hF'⟩ := hh
  refine ⟨fun z => F (afterOnes z), polyTime_comp hF polyTime_afterOnes, fun a b => ?_⟩
  show F (afterOnes (pairWords (enc a) (enc b))) = _
  rw [afterOnes_pairWords]
  exact hF' (a, b)

/-- Same when the second component is a raw word. -/
theorem PT.exists_polyTime_pairWords_raw {h : α → Word → γ}
    (hh : PT (fun p : α × Word => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧
      ∀ a (y : Word), G (pairWords (Code.enc a) y) = Code.enc (h a y) := by
  obtain ⟨F, hF, hF'⟩ := hh
  refine ⟨fun z => F ((unpair z).1 ++ enc (unpair z).2),
    polyTime_comp hF (polyTime_append polyTime_pair_fst (polyTime_wrap polyTime_pair_snd)),
    fun a y => ?_⟩
  simp only [unpair_pairWords]
  exact hF' (a, y)

/-- Same when the first component is a raw word. -/
theorem PT.exists_polyTime_pairWords_raw_left {h : Word → β → γ}
    (hh : PT (fun p : Word × β => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧
      ∀ (x : Word) b, G (pairWords x (Code.enc b)) = Code.enc (h x b) := by
  obtain ⟨F, hF, hF'⟩ := hh
  refine ⟨fun z => F (enc (unpair z).1 ++ (unpair z).2),
    polyTime_comp hF (polyTime_append (polyTime_wrap polyTime_pair_fst) polyTime_pair_snd),
    fun x b => ?_⟩
  simp only [unpair_pairWords]
  exact hF' (x, b)

/-- Same when both components are raw words (with an explicit word function). -/
theorem PT.polyTime_pairWords {h : Word → Word → γ} (hh : PT (fun p : Word × Word => h p.1 p.2)) :
    PolyTime (fun z => enc (h (unpair z).1 (unpair z).2)) :=
  PT.polyTime (hh.comp PT.unpair')

theorem PT.exists_polyTime_pairWords_raw_raw {h : Word → Word → γ}
    (hh : PT (fun p : Word × Word => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧ ∀ x y : Word, G (pairWords x y) = Code.enc (h x y) :=
  ⟨_, PT.polyTime_pairWords hh, fun x y => by simp only [unpair_pairWords]⟩

/-! ### Raw words as outputs -/

/-- A word-valued `PT` function, with its value (rather than the code of its value) as
output. -/
theorem PT.exists_polyTime_word {f : α → Word} (hf : PT f) :
    ∃ F : Word → Word, PolyTime F ∧ ∀ a, F (Code.enc a) = f a := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => afterOnes (F x), polyTime_comp polyTime_afterOnes hF,
    fun a => by simp only [hF', afterOnes_enc_word]⟩

theorem PT.exists_polyTime_pairWords_word {h : α → β → Word}
    (hh : PT (fun p : α × β => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧
      ∀ a b, G (pairWords (Code.enc a) (Code.enc b)) = h a b := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords hh
  exact ⟨fun z => afterOnes (G z), polyTime_comp polyTime_afterOnes hG,
    fun a b => by simp only [hG', afterOnes_enc_word]⟩

theorem PT.exists_polyTime_pairWords_raw_word {h : α → Word → Word}
    (hh : PT (fun p : α × Word => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧ ∀ a (y : Word), G (pairWords (Code.enc a) y) = h a y := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw hh
  exact ⟨fun z => afterOnes (G z), polyTime_comp polyTime_afterOnes hG,
    fun a y => by simp only [hG', afterOnes_enc_word]⟩

theorem PT.exists_polyTime_pairWords_raw_left_word {h : Word → β → Word}
    (hh : PT (fun p : Word × β => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧ ∀ (x : Word) b, G (pairWords x (Code.enc b)) = h x b := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw_left hh
  exact ⟨fun z => afterOnes (G z), polyTime_comp polyTime_afterOnes hG,
    fun x b => by simp only [hG', afterOnes_enc_word]⟩

/-- A two-argument `PT` function on raw words, as a polynomial-time function of
`pairWords x y`. -/
theorem PT.polyTime_pairWords_word {h : Word → Word → Word}
    (hh : PT (fun p : Word × Word => h p.1 p.2)) :
    PolyTime (fun z => h (unpair z).1 (unpair z).2) :=
  PT.polyTime_word (hh.comp PT.unpair')

theorem PT.exists_polyTime_pairWords_raw_raw_word {h : Word → Word → Word}
    (hh : PT (fun p : Word × Word => h p.1 p.2)) :
    ∃ G : Word → Word, PolyTime G ∧ ∀ x y : Word, G (pairWords x y) = h x y :=
  ⟨_, PT.polyTime_pairWords_word hh, fun x y => by simp only [unpair_pairWords]⟩

/-! ### Boolean functions as `[true]`/`[false]`-valued word functions -/

/-- A `PT` Boolean function of a raw word, as a polynomial-time characteristic function. -/
theorem PT.polyTime_bool {f : Word → Bool} (hf : PT f) :
    PolyTime (fun x => if f x then [true] else [false]) :=
  polyTime_congr (fun x => enc_bool_eq_ite (f x)) hf.polyTime

/-- A `PT` Boolean function on codes, as a polynomial-time characteristic function. -/
theorem PT.exists_polyTime_bool {f : α → Bool} (hf : PT f) :
    ∃ F : Word → Word, PolyTime F ∧ ∀ a, F (Code.enc a) = if f a then [true] else [false] := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨F, hF, fun a => by rw [hF', enc_bool_eq_ite]⟩

/-- A two-argument `PT` checker on raw words, as a polynomial-time characteristic function of
`pairWords x w` (compare `PT.inNP`). -/
theorem PT.polyTime_bool_pairWords {f : Word → Word → Bool}
    (hf : PT (fun p : Word × Word => f p.1 p.2)) :
    PolyTime (fun z => if f (unpair z).1 (unpair z).2 then [true] else [false]) :=
  PT.polyTime_bool (hf.comp PT.unpair')

theorem PT.exists_polyTime_pairWords_raw_raw_bool {f : Word → Word → Bool}
    (hf : PT (fun p : Word × Word => f p.1 p.2)) :
    ∃ χ : Word → Word, PolyTime χ ∧
      ∀ x w : Word, χ (pairWords x w) = if f x w then [true] else [false] :=
  ⟨_, PT.polyTime_bool_pairWords hf, fun x w => by simp only [unpair_pairWords]⟩

theorem PT.exists_polyTime_pairWords_bool {f : α → β → Bool}
    (hf : PT (fun p : α × β => f p.1 p.2)) :
    ∃ χ : Word → Word, PolyTime χ ∧
      ∀ a b, χ (pairWords (Code.enc a) (Code.enc b)) = if f a b then [true] else [false] := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords hf
  exact ⟨G, hG, fun a b => by rw [hG', enc_bool_eq_ite]⟩

theorem PT.exists_polyTime_pairWords_raw_bool {f : α → Word → Bool}
    (hf : PT (fun p : α × Word => f p.1 p.2)) :
    ∃ χ : Word → Word, PolyTime χ ∧
      ∀ a (w : Word), χ (pairWords (Code.enc a) w) = if f a w then [true] else [false] := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw hf
  exact ⟨G, hG, fun a w => by rw [hG', enc_bool_eq_ite]⟩

theorem PT.exists_polyTime_pairWords_raw_left_bool {f : Word → β → Bool}
    (hf : PT (fun p : Word × β => f p.1 p.2)) :
    ∃ χ : Word → Word, PolyTime χ ∧
      ∀ (x : Word) b, χ (pairWords x (Code.enc b)) = if f x b then [true] else [false] := by
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw_left hf
  exact ⟨G, hG, fun x b => by rw [hG', enc_bool_eq_ite]⟩

end Complexity.PT
