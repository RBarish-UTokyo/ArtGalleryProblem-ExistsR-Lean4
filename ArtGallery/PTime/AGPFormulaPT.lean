module

public import ArtGallery.Membership.Correct
public import ArtGallery.PTime.INVinER

/-!
# The formula combinators of the reduction AGP → ETR are polynomial-time

`PT` lemmas (all `@[fun_prop]`, in compositional form) for the combinators of
`ArtGallery/Membership`: the logical combinators (`bigAnd`, `bigOr`, `fImp`, `fNe`), the
constants (`bitsTerm`), the point terms (`pvar`, `vt`, `detT`, `dotT`, `crossT`, `lerpT`, `ptEq`),
and the formulas SIMPLE (`simpleF`), INSIDE (`insideF`), SEES (`seesF`) and GUARDS (`guardsF`).

All parameters are natural numbers (coded in unary), so the lemmas say that these formulas are
computed in time polynomial in the values of the parameters.  The big conjunctions and
disjunctions are handled through their token lists (`bigAnd_toks`, `bigOr_toks`), which are
`flatMap`s and hence polynomial-time without any size side condition.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Membership

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETR

/-! ### Token lists of the big connectives -/

theorem bigAnd_toks (l : List Formula) :
    (bigAnd l).toks = l.flatMap (fun φ => 4 :: φ.toks) ++ fTrue.toks := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp [bigAnd, Formula.toks] at ih ⊢; exact ih

theorem bigOr_toks (l : List Formula) :
    (bigOr l).toks = l.flatMap (fun φ => 5 :: φ.toks) ++ fFalse.toks := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp [bigOr, Formula.toks] at ih ⊢; exact ih

/-- The token list of the Horner term of a digit list. -/
theorem bitsTerm_toks (l : List Bool) :
    (bitsTerm l).toks = l.flatMap (fun b => [8, if b then 7 else 6, 10, 8, 7, 7]) ++ [6] := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bitsTerm, Term.toks, ih]

/-- `piT` without pattern matching. -/
theorem piT_eq (base e : ℕ) : piT base e = if e = 0 then .one else .var (base + (e - 1)) := by
  cases e <;> simp [piT]

/-- `lamC` as a closed formula. -/
theorem lamC_succ (m L k : ℕ) : lamC m L (k + 1) = lamC m (L / m) k := rfl

end ArtGallery.Membership

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETR ArtGallery.Membership

variable {α : Type} [Code α]

/-! ### Logical combinators -/

@[fun_prop] protected theorem PT.bigAnd {l : α → List Formula} (hl : PT l) :
    PT (fun a => bigAnd (l a)) := by
  refine PT.formula_of_toks ?_
  have h : PT (fun a => (l a).flatMap (fun φ => 4 :: φ.toks) ++ fTrue.toks) := by fun_prop
  exact h.of_eq fun a => (bigAnd_toks (l a)).symm

@[fun_prop] protected theorem PT.bigOr {l : α → List Formula} (hl : PT l) :
    PT (fun a => bigOr (l a)) := by
  refine PT.formula_of_toks ?_
  have h : PT (fun a => (l a).flatMap (fun φ => 5 :: φ.toks) ++ fFalse.toks) := by fun_prop
  exact h.of_eq fun a => (bigOr_toks (l a)).symm

@[fun_prop] protected theorem PT.fTrue : PT (fun _ : α => fTrue) := PT.const _

@[fun_prop] protected theorem PT.fFalse : PT (fun _ : α => fFalse) := PT.const _

@[fun_prop] protected theorem PT.fImp {φ ψ : α → Formula} (hφ : PT φ) (hψ : PT ψ) :
    PT (fun a => fImp (φ a) (ψ a)) := by
  unfold fImp; fun_prop

@[fun_prop] protected theorem PT.fNe {s t : α → Term} (hs : PT s) (ht : PT t) :
    PT (fun a => fNe (s a) (t a)) := by
  unfold fNe; fun_prop

/-! ### Constants -/

@[fun_prop] protected theorem PT.bitsTerm {l : α → List Bool} (hl : PT l) :
    PT (fun a => bitsTerm (l a)) := by
  refine PT.term_of_toks ?_
  have h : PT (fun a => (l a).flatMap (fun b => [8, if b then 7 else 6, 10, 8, 7, 7]) ++ [6]) := by
    fun_prop
  exact h.of_eq fun a => (bitsTerm_toks (l a)).symm

/-! ### Point terms -/

@[fun_prop] protected theorem PT.pvar {i : α → ℕ} (hi : PT i) : PT (fun a => pvar (i a)) := by
  unfold pvar; fun_prop

@[fun_prop] protected theorem PT.vt {k : α → ℕ} (hk : PT k) : PT (fun a => vt (k a)) := by
  unfold vt; fun_prop

@[fun_prop] protected theorem PT.detT {p q r : α → PTerm} (hp : PT p) (hq : PT q) (hr : PT r) :
    PT (fun a => detT (p a) (q a) (r a)) := by
  unfold detT; fun_prop

@[fun_prop] protected theorem PT.dotT {p q r s : α → PTerm} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => dotT (p a) (q a) (r a) (s a)) := by
  unfold dotT; fun_prop

@[fun_prop] protected theorem PT.crossT {p q r s : α → PTerm} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => crossT (p a) (q a) (r a) (s a)) := by
  unfold crossT; fun_prop

@[fun_prop] protected theorem PT.lerpT {p q : α → PTerm} {h : α → Term} (hp : PT p) (hq : PT q)
    (hh : PT h) : PT (fun a => lerpT (p a) (q a) (h a)) := by
  unfold lerpT; fun_prop

@[fun_prop] protected theorem PT.ptEq {p q : α → PTerm} (hp : PT p) (hq : PT q) :
    PT (fun a => ptEq (p a) (q a)) := by
  unfold ptEq; fun_prop

/-! ### SIMPLE -/

@[fun_prop] protected theorem PT.ptNe {p q : α → PTerm} (hp : PT p) (hq : PT q) :
    PT (fun a => ptNe (p a) (q a)) := by
  unfold ptNe; fun_prop

@[fun_prop] protected theorem PT.adjF {p q r : α → PTerm} (hp : PT p) (hq : PT q) (hr : PT r) :
    PT (fun a => adjF (p a) (q a) (r a)) := by
  unfold adjF; fun_prop

@[fun_prop] protected theorem PT.linT {s : α → ℕ} {p : α → PTerm} (hs : PT s) (hp : PT p) :
    PT (fun a => linT (s a) (p a)) := by
  unfold linT; fun_prop

@[fun_prop] protected theorem PT.sepF {s : α → ℕ} {p q r t : α → PTerm} (hs : PT s) (hp : PT p)
    (hq : PT q) (hr : PT r) (ht : PT t) : PT (fun a => sepF (s a) (p a) (q a) (r a) (t a)) := by
  unfold sepF; fun_prop

@[fun_prop] protected theorem PT.edgePairF {n i j s : α → ℕ} (hn : PT n) (hi : PT i) (hj : PT j)
    (hs : PT s) : PT (fun a => edgePairF (n a) (i a) (j a) (s a)) := by
  unfold edgePairF; fun_prop

@[fun_prop] protected theorem PT.simplePairF {n s b : α → ℕ} (hn : PT n) (hs : PT s) (hb : PT b) :
    PT (fun a => simplePairF (n a) (s a) (b a)) := by
  unfold simplePairF; fun_prop

@[fun_prop] protected theorem PT.simpleF {n base : α → ℕ} (hn : PT n) (hb : PT base) :
    PT (fun a => simpleF (n a) (base a)) := by
  unfold simpleF; fun_prop

@[fun_prop] protected theorem PT.simpleSize {n : α → ℕ} (hn : PT n) :
    PT (fun a => simpleSize (n a)) := by
  unfold simpleSize; fun_prop

/-! ### INSIDE -/

@[fun_prop] protected theorem PT.onSegF {q p r : α → PTerm} (hq : PT q) (hp : PT p) (hr : PT r) :
    PT (fun a => onSegF (q a) (p a) (r a)) := by
  unfold onSegF; fun_prop

@[fun_prop] protected theorem PT.onBoundaryF {n : α → ℕ} {q : α → PTerm} (hn : PT n) (hq : PT q) :
    PT (fun a => onBoundaryF (n a) (q a)) := by
  unfold onBoundaryF; fun_prop

@[fun_prop] protected theorem PT.crossesF {z u v : α → PTerm} (hz : PT z) (hu : PT u)
    (hv : PT v) : PT (fun a => crossesF (z a) (u a) (v a)) := by
  unfold crossesF; fun_prop

@[fun_prop] protected theorem PT.piT {base e : α → ℕ} (hb : PT base) (he : PT e) :
    PT (fun a => piT (base a) (e a)) := by
  simp only [piT_eq]; fun_prop

@[fun_prop] protected theorem PT.parStepF {n : α → ℕ} {q : α → PTerm} {base e : α → ℕ} (hn : PT n)
    (hq : PT q) (hb : PT base) (he : PT e) : PT (fun a => parStepF (n a) (q a) (base a) (e a)) := by
  unfold parStepF; fun_prop

@[fun_prop] protected theorem PT.parDefF {n : α → ℕ} {q : α → PTerm} {base : α → ℕ} (hn : PT n)
    (hq : PT q) (hb : PT base) : PT (fun a => parDefF (n a) (q a) (base a)) := by
  unfold parDefF; fun_prop

@[fun_prop] protected theorem PT.insideF {n : α → ℕ} {q : α → PTerm} {base : α → ℕ} (hn : PT n)
    (hq : PT q) (hb : PT base) : PT (fun a => insideF (n a) (q a) (base a)) := by
  unfold insideF; fun_prop

/-! ### SEES -/

@[fun_prop] protected theorem PT.seesSize {n : α → ℕ} (hn : PT n) :
    PT (fun a => seesSize (n a)) := by
  unfold seesSize; fun_prop

@[fun_prop] protected theorem PT.tDefF {n : α → ℕ} {γ c : α → PTerm} {base j : α → ℕ} (hn : PT n)
    (hγ : PT γ) (hc : PT c) (hb : PT base) (hj : PT j) :
    PT (fun a => tDefF (n a) (γ a) (c a) (base a) (j a)) := by
  unfold tDefF; fun_prop

@[fun_prop] protected theorem PT.vDefF {n : α → ℕ} {γ c : α → PTerm} {base k : α → ℕ} (hn : PT n)
    (hγ : PT γ) (hc : PT c) (hb : PT base) (hk : PT k) :
    PT (fun a => vDefF (n a) (γ a) (c a) (base a) (k a)) := by
  unfold vDefF; fun_prop

@[fun_prop] protected theorem PT.tTerm {base i : α → ℕ} (hb : PT base) (hi : PT i) :
    PT (fun a => tTerm (base a) (i a)) := by
  unfold tTerm; fun_prop

@[fun_prop] protected theorem PT.unitF {t : α → Term} (ht : PT t) : PT (fun a => unitF (t a)) := by
  unfold unitF; fun_prop

@[fun_prop] protected theorem PT.pairBase {n base p : α → ℕ} (hn : PT n) (hb : PT base)
    (hp : PT p) : PT (fun a => pairBase (n a) (base a) (p a)) := by
  unfold pairBase; fun_prop

@[fun_prop] protected theorem PT.pairF {n : α → ℕ} {γ c : α → PTerm} {base p : α → ℕ} (hn : PT n)
    (hγ : PT γ) (hc : PT c) (hb : PT base) (hp : PT p) :
    PT (fun a => pairF (n a) (γ a) (c a) (base a) (p a)) := by
  unfold pairF; fun_prop

@[fun_prop] protected theorem PT.seesF {n : α → ℕ} {γ c : α → PTerm} {base : α → ℕ} (hn : PT n)
    (hγ : PT γ) (hc : PT c) (hb : PT base) :
    PT (fun a => seesF (n a) (γ a) (c a) (base a)) := by
  unfold seesF; fun_prop

/-! ### GUARDS -/

@[fun_prop] protected theorem PT.guardT {gbase i : α → ℕ} (hg : PT gbase) (hi : PT i) :
    PT (fun a => guardT (gbase a) (i a)) := by
  unfold guardT; fun_prop

@[fun_prop] protected theorem PT.lineT {n gbase i : α → ℕ} (hn : PT n) (hg : PT gbase)
    (hi : PT i) : PT (fun a => lineT (n a) (gbase a) (i a)) := by
  unfold lineT; fun_prop

@[fun_prop] protected theorem PT.lineDenT {l₁ l₂ : α → PTerm × PTerm} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => lineDenT (l₁ a) (l₂ a)) := by
  unfold lineDenT; fun_prop

@[fun_prop] protected theorem PT.lineCT {l : α → PTerm × PTerm} (hl : PT l) :
    PT (fun a => lineCT (l a)) := by
  unfold lineCT; fun_prop

@[fun_prop] protected theorem PT.lineNumXT {l₁ l₂ : α → PTerm × PTerm} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => lineNumXT (l₁ a) (l₂ a)) := by
  unfold lineNumXT; fun_prop

@[fun_prop] protected theorem PT.lineNumYT {l₁ l₂ : α → PTerm × PTerm} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => lineNumYT (l₁ a) (l₂ a)) := by
  unfold lineNumYT; fun_prop

@[fun_prop] protected theorem PT.interF {l₁ l₂ : α → PTerm × PTerm} {X : α → PTerm} (h₁ : PT l₁)
    (h₂ : PT l₂) (hX : PT X) : PT (fun a => interF (l₁ a) (l₂ a) (X a)) := by
  unfold interF; fun_prop

@[fun_prop] protected theorem PT.cenF {u X₁ X₂ X₃ : α → PTerm} (hu : PT u) (h₁ : PT X₁)
    (h₂ : PT X₂) (h₃ : PT X₃) : PT (fun a => cenF (u a) (X₁ a) (X₂ a) (X₃ a)) := by
  unfold cenF; fun_prop

@[fun_prop] protected theorem PT.numLines {n g : α → ℕ} (hn : PT n) (hg : PT g) :
    PT (fun a => numLines (n a) (g a)) := by
  unfold numLines; fun_prop

@[fun_prop] protected theorem PT.Xt {m xbase i j : α → ℕ} (hm : PT m) (hx : PT xbase) (hi : PT i)
    (hj : PT j) : PT (fun a => Xt (m a) (xbase a) (i a) (j a)) := by
  unfold Xt; fun_prop

/-- The `k`-th base-`m` digit, for a fixed `k`. -/
@[fun_prop] protected theorem PT.lamC {m L : α → ℕ} (hm : PT m) (hL : PT L) (k : ℕ) :
    PT (fun a => lamC (m a) (L a) k) := by
  induction k generalizing L with
  | zero => simp only [lamC]; fun_prop
  | succ k ih => simp only [lamC_succ]; exact ih (by fun_prop)

@[fun_prop] protected theorem PT.cdF {n gbase i j : α → ℕ} (hn : PT n) (hg : PT gbase) (hi : PT i)
    (hj : PT j) : PT (fun a => cdF (n a) (gbase a) (i a) (j a)) := by
  unfold cdF; fun_prop

@[fun_prop] protected theorem PT.lamSize {n g : α → ℕ} (hn : PT n) (hg : PT g) :
    PT (fun a => lamSize (n a) (g a)) := by
  unfold lamSize; fun_prop

@[fun_prop] protected theorem PT.lamF {n g gbase xbase L b : α → ℕ} (hn : PT n) (hg : PT g)
    (hgb : PT gbase) (hx : PT xbase) (hL : PT L) (hb : PT b) :
    PT (fun a => lamF (n a) (g a) (gbase a) (xbase a) (L a) (b a)) := by
  unfold lamF; fun_prop

@[fun_prop] protected theorem PT.guardBlockF {n gbase gpbase i : α → ℕ} (hn : PT n)
    (hg : PT gbase) (hgp : PT gpbase) (hi : PT i) :
    PT (fun a => guardBlockF (n a) (gbase a) (gpbase a) (i a)) := by
  unfold guardBlockF; fun_prop

@[fun_prop] protected theorem PT.gpBase {g base : α → ℕ} (hg : PT g) (hb : PT base) :
    PT (fun a => gpBase (g a) (base a)) := by
  unfold gpBase; fun_prop

@[fun_prop] protected theorem PT.xBase {n g base : α → ℕ} (hn : PT n) (hg : PT g) (hb : PT base) :
    PT (fun a => xBase (n a) (g a) (base a)) := by
  unfold xBase; fun_prop

@[fun_prop] protected theorem PT.lBase {n g base : α → ℕ} (hn : PT n) (hg : PT g) (hb : PT base) :
    PT (fun a => lBase (n a) (g a) (base a)) := by
  unfold lBase; fun_prop

/-- **GUARDS is polynomial-time** (in the unary parameters `n`, `g`, `base`). -/
@[fun_prop] protected theorem PT.guardsF {n g base : α → ℕ} (hn : PT n) (hg : PT g)
    (hb : PT base) : PT (fun a => guardsF (n a) (g a) (base a)) := by
  unfold guardsF; fun_prop

end ArtGallery

end
