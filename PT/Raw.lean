module

public import PT.Basic

/-!
# Interface between `PT` and raw `PolyTime` functions on words

A word `w : Word = List Bool` is a list of bits, so its code is `writeNat w.length ++ w`.
The functions `x ↦ enc x` ("wrap") and its inverse ("unwrap") are polynomial-time, which
gives the translations `PT.of_polyTime`, `PT.polyTime`, `PT.polyTime_word`,
`PT.comp_polyTime`, and deciders/verifiers/reductions from `PT` functions on raw words.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β : Type} [Code α] [Code β]

theorem enc_word_eq (w : Word) : enc w = List.replicate w.length true ++ false :: w := by
  rw [enc_word, writeNat_append]

@[simp] theorem afterOnes_enc_word (w : Word) : afterOnes (enc w) = w := by
  rw [enc_word_eq, afterOnes_ones]

/-- Wrapping: `x ↦ enc (G x)` is polynomial-time for polynomial-time `G`. -/
theorem polyTime_wrap {G : Word → Word} (hG : PolyTime G) : PolyTime (fun x => enc (G x)) :=
  polyTime_congr (fun x => (enc_word_eq (G x)).symm)
    (polyTime_append (polyTime_ones hG) (polyTime_cons false hG))

/-- Unwrapping: `afterOnes (enc w) = w`. -/
theorem polyTime_unwrap : PolyTime afterOnes := polyTime_afterOnes

/-- A polynomial-time word function is `PT` as a function on `List Bool`. -/
protected theorem PT.of_polyTime {F : Word → Word} (hF : PolyTime F) : PT F :=
  ⟨fun x => enc (F (afterOnes x)), polyTime_wrap (polyTime_comp hF polyTime_afterOnes),
    fun w => by simp only [afterOnes_enc_word]⟩

/-- A `PT` function of a raw input word is polynomial-time after encoding its value. -/
protected theorem PT.polyTime {f : Word → β} (hf : PT f) : PolyTime (fun x => enc (f x)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact polyTime_congr (fun x => hF' x) (polyTime_comp hF (polyTime_wrap polyTime_id))

/-- A `PT` function from words to words is polynomial-time. -/
protected theorem PT.polyTime_word {f : Word → Word} (hf : PT f) : PolyTime f :=
  polyTime_congr (fun x => afterOnes_enc_word (f x))
    (polyTime_comp polyTime_afterOnes hf.polyTime)

theorem PT.word_iff {f : Word → Word} : PT f ↔ PolyTime f :=
  ⟨PT.polyTime_word, PT.of_polyTime⟩

/-- Compose a `PT` function with a polynomial-time parser producing codes. -/
protected theorem PT.comp_polyTime {f : α → β} (hf : PT f) {g : Word → α}
    (hg : PolyTime (fun x => enc (g x))) : PolyTime (fun x => enc (f (g x))) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact polyTime_congr (fun x => hF' (g x)) (polyTime_comp hF hg)

/-- A polynomial-time producer of codes, as a `PT` function of the raw input word. -/
protected theorem PT.of_polyTime_enc {g : Word → α} (hg : PolyTime (fun x => enc (g x))) :
    PT g :=
  ⟨fun x => enc (g (afterOnes x)), polyTime_comp hg polyTime_afterOnes,
    fun w => by simp only [afterOnes_enc_word]⟩

theorem PT.word_dom_iff {g : Word → α} : PT g ↔ PolyTime (fun x => enc (g x)) :=
  ⟨PT.polyTime, PT.of_polyTime_enc⟩

/-- The coding function itself, as a function into words. -/
@[fun_prop] protected theorem PT.enc {f : α → β} (hf : PT f) :
    PT (fun a => (Code.enc (f a) : Word)) := by
  obtain ⟨F, hF, hF'⟩ := hf
  exact ⟨fun x => enc (F x), polyTime_wrap hF, fun a => by simp only [hF']⟩

/-- `pairWords` as a function `Word × Word → Word` (compositional form). -/
@[fun_prop] protected theorem PT.pairWords {u v : α → Word} (hu : PT u) (hv : PT v) :
    PT (fun a => pairWords (u a) (v a)) := by
  obtain ⟨U, hU, hU'⟩ := hu
  obtain ⟨V, hV, hV'⟩ := hv
  exact ⟨fun x => enc (pairWords (afterOnes (U x)) (afterOnes (V x))),
    polyTime_wrap (polyTime_pair (polyTime_comp polyTime_afterOnes hU)
      (polyTime_comp polyTime_afterOnes hV)),
    fun a => by simp only [hU', hV', afterOnes_enc_word]⟩

/-- `Reg.unpair` as a function `Word → Word × Word` (compositional form). -/
@[fun_prop] protected theorem PT.unpair {w : α → Word} (hw : PT w) :
    PT (fun a => unpair (w a)) := by
  obtain ⟨W, hW, hW'⟩ := hw
  exact ⟨fun x => enc (unpair (afterOnes (W x))).1 ++ enc (unpair (afterOnes (W x))).2,
    polyTime_append
      (polyTime_wrap (polyTime_comp polyTime_pair_fst (polyTime_comp polyTime_afterOnes hW)))
      (polyTime_wrap (polyTime_comp polyTime_pair_snd (polyTime_comp polyTime_afterOnes hW))),
    fun a => by simp only [hW', afterOnes_enc_word, enc_prod]⟩

theorem PT.pairWords' : PT (fun p : Word × Word => pairWords p.1 p.2) :=
  PT.pairWords PT.fst' PT.snd'

theorem PT.unpair' : PT (unpair : Word → Word × Word) := PT.unpair PT.id

/-! ### Deciders, verifiers and reductions from `PT` functions on raw words -/

/-- A `PT` Boolean test on raw words decides a language in P. -/
protected theorem PT.inP {L : Language} {f : Word → Bool} (hf : PT f)
    (h : ∀ x, L x ↔ f x = true) : InP L :=
  inP_of_polyTime hf.polyTime fun x => by simp [h x]

/-- A `PT` Boolean verifier on raw words, with polynomially bounded certificates, puts a
language in NP. -/
protected theorem PT.inNP {L : Language} {f : Word → Word → Bool}
    (hf : PT (fun p : Word × Word => f p.1 p.2)) (c e : Nat)
    (h : ∀ x, L x ↔ ∃ w : Word, w.length ≤ powerBound c e x.length ∧ f x w = true) :
    InNP L :=
  inNP_of_polyTime (χ := fun z => enc (f (unpair z).1 (unpair z).2))
    (PT.polyTime (hf.comp PT.unpair')) c e fun x => by simp [h x]

/-- A `PT` function on raw words is a Karp reduction once it preserves membership. -/
protected theorem PT.polyRed {A B : Language} {f : Word → Word} (hf : PT f)
    (h : ∀ x, A x ↔ B (f x)) : PolyRed A B :=
  ⟨f, hf.polyTime_word, h⟩

end Complexity.PT
