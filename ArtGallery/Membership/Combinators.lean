module

public import ArtGallery.Membership.Decode
public import ArtGallery.Geometry.Basic

/-!
# Formula combinators for the reduction from AGP to ETR

A small library for writing ETR formulas:

* constants `fTrue`, `fFalse`, big conjunctions/disjunctions over lists (`bigAnd`, `bigOr`),
  implication `fImp φ ψ := ¬φ ∨ ψ`, disequality `fNe s t := ¬(s = t)`;
* integer constants from binary digits by Horner's rule (`bitsTerm`, `natTerm`, `intTerm`);
* point terms (`PTerm`, pairs of terms) and the polynomial terms `detT`, `dotT`, `crossT`;
* variable bookkeeping: `TVars S t` / `FVars S φ` (every variable satisfies `S`), the
  congruence lemmas `eval_congr`, `holds_congr`, and the *gluing* lemma `holds_glue`, which
  assembles satisfying assignments of formulas using disjoint blocks of fresh variables.
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR

/-! ## Semantics of the constructors -/

@[simp] theorem eval_var (x : ℕ → ℝ) (i : ℕ) : (Term.var i).eval x = x i := rfl
@[simp] theorem eval_zero (x : ℕ → ℝ) : Term.zero.eval x = 0 := rfl
@[simp] theorem eval_one (x : ℕ → ℝ) : Term.one.eval x = 1 := rfl
@[simp] theorem eval_add (x : ℕ → ℝ) (s t : Term) :
    (Term.add s t).eval x = s.eval x + t.eval x := rfl
@[simp] theorem eval_sub (x : ℕ → ℝ) (s t : Term) :
    (Term.sub s t).eval x = s.eval x - t.eval x := rfl
@[simp] theorem eval_mul (x : ℕ → ℝ) (s t : Term) :
    (Term.mul s t).eval x = s.eval x * t.eval x := rfl

@[simp] theorem holds_eq (x : ℕ → ℝ) (s t : Term) :
    (Formula.eq s t).Holds x ↔ s.eval x = t.eval x := Iff.rfl
@[simp] theorem holds_lt (x : ℕ → ℝ) (s t : Term) :
    (Formula.lt s t).Holds x ↔ s.eval x < t.eval x := Iff.rfl
@[simp] theorem holds_le (x : ℕ → ℝ) (s t : Term) :
    (Formula.le s t).Holds x ↔ s.eval x ≤ t.eval x := Iff.rfl
@[simp] theorem holds_not (x : ℕ → ℝ) (φ : Formula) :
    (Formula.not φ).Holds x ↔ ¬ φ.Holds x := Iff.rfl
@[simp] theorem holds_and (x : ℕ → ℝ) (φ ψ : Formula) :
    (Formula.and φ ψ).Holds x ↔ φ.Holds x ∧ ψ.Holds x := Iff.rfl
@[simp] theorem holds_or (x : ℕ → ℝ) (φ ψ : Formula) :
    (Formula.or φ ψ).Holds x ↔ φ.Holds x ∨ ψ.Holds x := Iff.rfl

/-! ## Logical combinators -/

/-- The true formula `0 ≤ 0`. -/
def fTrue : Formula := .le .zero .zero

/-- The false formula `1 < 0`. -/
def fFalse : Formula := .lt .one .zero

/-- Conjunction of a list of formulas. -/
def bigAnd (l : List Formula) : Formula := l.foldr .and fTrue

/-- Disjunction of a list of formulas. -/
def bigOr (l : List Formula) : Formula := l.foldr .or fFalse

/-- Implication `φ → ψ`, written `¬φ ∨ ψ`. -/
def fImp (φ ψ : Formula) : Formula := .or (.not φ) ψ

/-- Disequality `s ≠ t`, written `¬(s = t)`. -/
def fNe (s t : Term) : Formula := .not (.eq s t)

@[simp] theorem holds_fTrue (x : ℕ → ℝ) : fTrue.Holds x := le_refl (0 : ℝ)

@[simp] theorem not_holds_fFalse (x : ℕ → ℝ) : ¬ fFalse.Holds x := by
  simp [fFalse]

@[simp] theorem holds_bigAnd (x : ℕ → ℝ) (l : List Formula) :
    (bigAnd l).Holds x ↔ ∀ φ ∈ l, φ.Holds x := by
  induction l with
  | nil => simp [bigAnd]
  | cons φ l ih => simp only [bigAnd, List.foldr_cons] at ih ⊢; simp [ih]

@[simp] theorem holds_bigOr (x : ℕ → ℝ) (l : List Formula) :
    (bigOr l).Holds x ↔ ∃ φ ∈ l, φ.Holds x := by
  induction l with
  | nil => simp [bigOr]
  | cons φ l ih => simp only [bigOr, List.foldr_cons] at ih ⊢; simp [ih]

@[simp] theorem holds_fImp (x : ℕ → ℝ) (φ ψ : Formula) :
    (fImp φ ψ).Holds x ↔ (φ.Holds x → ψ.Holds x) := by
  simp only [fImp, holds_or, holds_not]; tauto

@[simp] theorem holds_fNe (x : ℕ → ℝ) (s t : Term) :
    (fNe s t).Holds x ↔ s.eval x ≠ t.eval x := Iff.rfl

theorem holds_bigAnd_range (x : ℕ → ℝ) (N : ℕ) (φ : ℕ → Formula) :
    (bigAnd ((List.range N).map φ)).Holds x ↔ ∀ i < N, (φ i).Holds x := by
  simp

theorem holds_bigOr_range (x : ℕ → ℝ) (N : ℕ) (φ : ℕ → Formula) :
    (bigOr ((List.range N).map φ)).Holds x ↔ ∃ i < N, (φ i).Holds x := by
  simp

/-! ## Integer constants -/

/-- The term of the number with binary digits `l` (least significant first), by Horner's
rule: `b₀ + (1 + 1) · (b₁ + (1 + 1) · (⋯))`. -/
def bitsTerm : List Bool → Term
  | [] => .zero
  | b :: l => .add (if b then .one else .zero) (.mul (.add .one .one) (bitsTerm l))

@[simp] theorem eval_bitsTerm (x : ℕ → ℝ) (l : List Bool) :
    (bitsTerm l).eval x = (ofBits l : ℝ) := by
  induction l with
  | nil => simp [bitsTerm, ofBits]
  | cons b l ih =>
    cases b
    · simp only [bitsTerm, ofBits, Bool.false_eq_true, ↓reduceIte, eval_add, eval_mul, eval_zero,
        eval_one, ih, Bool.toNat_false]
      push_cast; ring
    · simp only [bitsTerm, ofBits, ↓reduceIte, eval_add, eval_mul, eval_one, ih, Bool.toNat_true]
      push_cast; ring

/-- The term of a natural number, from its binary digits. -/
def natTerm (n : ℕ) : Term := bitsTerm n.bits

@[simp] theorem eval_natTerm (x : ℕ → ℝ) (n : ℕ) : (natTerm n).eval x = (n : ℝ) := by
  simp [natTerm, ofBits_bits]

/-- The term of an integer: its absolute value in binary, subtracted from `0` if negative. -/
def intTerm (z : ℤ) : Term :=
  if z < 0 then .sub .zero (natTerm z.natAbs) else natTerm z.natAbs

@[simp] theorem eval_intTerm (x : ℕ → ℝ) (z : ℤ) : (intTerm z).eval x = (z : ℝ) := by
  unfold intTerm
  split_ifs with h
  · simp only [eval_sub, eval_zero, eval_natTerm, zero_sub]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h), neg_neg]
  · simp only [eval_natTerm]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast not_lt.1 h)]

/-! ## Point terms -/

/-- A point given by two terms. -/
abbrev PTerm : Type := Term × Term

/-- The value of a point term. -/
def PTerm.eval (x : ℕ → ℝ) (p : PTerm) : Point := (p.1.eval x, p.2.eval x)

@[simp] theorem PTerm.eval_fst (x : ℕ → ℝ) (p : PTerm) : (p.eval x).1 = p.1.eval x := rfl
@[simp] theorem PTerm.eval_snd (x : ℕ → ℝ) (p : PTerm) : (p.eval x).2 = p.2.eval x := rfl

/-- The point whose coordinates are the variables `i` and `i + 1`. -/
def pvar (i : ℕ) : PTerm := (.var i, .var (i + 1))

@[simp] theorem pvar_eval (x : ℕ → ℝ) (i : ℕ) : (pvar i).eval x = (x i, x (i + 1)) := rfl

@[simp] theorem pvar_fst (i : ℕ) : (pvar i).1 = .var i := rfl
@[simp] theorem pvar_snd (i : ℕ) : (pvar i).2 = .var (i + 1) := rfl

/-- The `k`-th vertex of the polygon: variables `2k` and `2k + 1`. -/
def vt (k : ℕ) : PTerm := pvar (2 * k)

/-- The term `det a b c` (twice the signed area). -/
def detT (a b c : PTerm) : Term :=
  .sub (.mul (.sub b.1 a.1) (.sub c.2 a.2)) (.mul (.sub c.1 a.1) (.sub b.2 a.2))

@[simp] theorem eval_detT (x : ℕ → ℝ) (a b c : PTerm) :
    (detT a b c).eval x = det (a.eval x) (b.eval x) (c.eval x) := rfl

/-- The scalar product `(q - p) · (s - r)` (real version). -/
def dotR (p q r s : Point) : ℝ := (q.1 - p.1) * (s.1 - r.1) + (q.2 - p.2) * (s.2 - r.2)

/-- The cross product `(q - p) × (s - r)` (real version). -/
def crossR (p q r s : Point) : ℝ := (q.1 - p.1) * (s.2 - r.2) - (q.2 - p.2) * (s.1 - r.1)

/-- The term of the scalar product `(q - p) · (s - r)`. -/
def dotT (p q r s : PTerm) : Term :=
  .add (.mul (.sub q.1 p.1) (.sub s.1 r.1)) (.mul (.sub q.2 p.2) (.sub s.2 r.2))

/-- The term of the cross product `(q - p) × (s - r)`. -/
def crossT (p q r s : PTerm) : Term :=
  .sub (.mul (.sub q.1 p.1) (.sub s.2 r.2)) (.mul (.sub q.2 p.2) (.sub s.1 r.1))

@[simp] theorem eval_dotT (x : ℕ → ℝ) (p q r s : PTerm) :
    (dotT p q r s).eval x = dotR (p.eval x) (q.eval x) (r.eval x) (s.eval x) := rfl

@[simp] theorem eval_crossT (x : ℕ → ℝ) (p q r s : PTerm) :
    (crossT p q r s).eval x = crossR (p.eval x) (q.eval x) (r.eval x) (s.eval x) := rfl

/-- Two point terms denote the same point. -/
def ptEq (p q : PTerm) : Formula := .and (.eq p.1 q.1) (.eq p.2 q.2)

@[simp] theorem holds_ptEq (x : ℕ → ℝ) (p q : PTerm) :
    (ptEq p q).Holds x ↔ p.eval x = q.eval x := by
  simp [ptEq, Prod.ext_iff]

/-- The point term `a + h (b - a)` (`lerp a b h`). -/
def lerpT (a b : PTerm) (h : Term) : PTerm :=
  (.add a.1 (.mul h (.sub b.1 a.1)), .add a.2 (.mul h (.sub b.2 a.2)))

@[simp] theorem eval_lerpT (x : ℕ → ℝ) (a b : PTerm) (h : Term) :
    (lerpT a b h).eval x = Geometry.lerp (a.eval x) (b.eval x) (h.eval x) := rfl

/-! ## Variables -/

/-- Every variable of the term satisfies `S`. -/
def TVars (S : ℕ → Prop) : Term → Prop
  | .var i => S i
  | .zero => True
  | .one => True
  | .add s t => TVars S s ∧ TVars S t
  | .sub s t => TVars S s ∧ TVars S t
  | .mul s t => TVars S s ∧ TVars S t

/-- Every variable of the formula satisfies `S`. -/
def FVars (S : ℕ → Prop) : Formula → Prop
  | .eq s t => TVars S s ∧ TVars S t
  | .lt s t => TVars S s ∧ TVars S t
  | .le s t => TVars S s ∧ TVars S t
  | .not φ => FVars S φ
  | .and φ ψ => FVars S φ ∧ FVars S ψ
  | .or φ ψ => FVars S φ ∧ FVars S ψ

/-- Every variable of the point term satisfies `S`. -/
def PVars (S : ℕ → Prop) (p : PTerm) : Prop := TVars S p.1 ∧ TVars S p.2

theorem TVars.mono {S S' : ℕ → Prop} (h : ∀ v, S v → S' v) {t : Term} (ht : TVars S t) :
    TVars S' t := by
  induction t with
  | var i => exact h i ht
  | zero => trivial
  | one => trivial
  | add s t ihs iht => exact ⟨ihs ht.1, iht ht.2⟩
  | sub s t ihs iht => exact ⟨ihs ht.1, iht ht.2⟩
  | mul s t ihs iht => exact ⟨ihs ht.1, iht ht.2⟩

theorem FVars.mono {S S' : ℕ → Prop} (h : ∀ v, S v → S' v) {φ : Formula} (hφ : FVars S φ) :
    FVars S' φ := by
  induction φ with
  | eq s t => exact ⟨hφ.1.mono h, hφ.2.mono h⟩
  | lt s t => exact ⟨hφ.1.mono h, hφ.2.mono h⟩
  | le s t => exact ⟨hφ.1.mono h, hφ.2.mono h⟩
  | not φ ih => exact ih hφ
  | and φ ψ ihφ ihψ => exact ⟨ihφ hφ.1, ihψ hφ.2⟩
  | or φ ψ ihφ ihψ => exact ⟨ihφ hφ.1, ihψ hφ.2⟩

theorem PVars.mono {S S' : ℕ → Prop} (h : ∀ v, S v → S' v) {p : PTerm} (hp : PVars S p) :
    PVars S' p := ⟨hp.1.mono h, hp.2.mono h⟩

theorem eval_congr {S : ℕ → Prop} {x y : ℕ → ℝ} (hxy : ∀ v, S v → x v = y v) {t : Term}
    (ht : TVars S t) : t.eval x = t.eval y := by
  induction t with
  | var i => exact hxy i ht
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp [ihs ht.1, iht ht.2]
  | sub s t ihs iht => simp [ihs ht.1, iht ht.2]
  | mul s t ihs iht => simp [ihs ht.1, iht ht.2]

theorem PTerm.eval_congr {S : ℕ → Prop} {x y : ℕ → ℝ} (hxy : ∀ v, S v → x v = y v) {p : PTerm}
    (hp : PVars S p) : p.eval x = p.eval y := by
  simp only [PTerm.eval, Membership.eval_congr hxy hp.1, Membership.eval_congr hxy hp.2]

theorem holds_congr {S : ℕ → Prop} {x y : ℕ → ℝ} (hxy : ∀ v, S v → x v = y v) {φ : Formula}
    (hφ : FVars S φ) : φ.Holds x ↔ φ.Holds y := by
  induction φ with
  | eq s t => simp [eval_congr hxy hφ.1, eval_congr hxy hφ.2]
  | lt s t => simp [eval_congr hxy hφ.1, eval_congr hxy hφ.2]
  | le s t => simp [eval_congr hxy hφ.1, eval_congr hxy hφ.2]
  | not φ ih => simp [ih hφ]
  | and φ ψ ihφ ihψ => simp [ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ => simp [ihφ hφ.1, ihψ hφ.2]

/-- Congruence for assignments agreeing below a bound. -/
theorem holds_congr_lt {N : ℕ} {x y : ℕ → ℝ} (hxy : ∀ v < N, y v = x v) {φ : Formula}
    (hφ : FVars (· < N) φ) : φ.Holds y ↔ φ.Holds x :=
  holds_congr (S := (· < N)) hxy hφ

/-! ### Variable lemmas for the combinators -/

@[simp] theorem TVars_var (S : ℕ → Prop) (i : ℕ) : TVars S (.var i) ↔ S i := Iff.rfl
@[simp] theorem TVars_zero (S : ℕ → Prop) : TVars S .zero := trivial
@[simp] theorem TVars_one (S : ℕ → Prop) : TVars S .one := trivial
@[simp] theorem TVars_add (S : ℕ → Prop) (s t : Term) :
    TVars S (.add s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem TVars_sub (S : ℕ → Prop) (s t : Term) :
    TVars S (.sub s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem TVars_mul (S : ℕ → Prop) (s t : Term) :
    TVars S (.mul s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem FVars_eq (S : ℕ → Prop) (s t : Term) :
    FVars S (.eq s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem FVars_lt (S : ℕ → Prop) (s t : Term) :
    FVars S (.lt s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem FVars_le (S : ℕ → Prop) (s t : Term) :
    FVars S (.le s t) ↔ TVars S s ∧ TVars S t := Iff.rfl
@[simp] theorem FVars_not (S : ℕ → Prop) (φ : Formula) : FVars S (.not φ) ↔ FVars S φ := Iff.rfl
@[simp] theorem FVars_and (S : ℕ → Prop) (φ ψ : Formula) :
    FVars S (.and φ ψ) ↔ FVars S φ ∧ FVars S ψ := Iff.rfl
@[simp] theorem FVars_or (S : ℕ → Prop) (φ ψ : Formula) :
    FVars S (.or φ ψ) ↔ FVars S φ ∧ FVars S ψ := Iff.rfl

@[simp] theorem FVars_fTrue (S : ℕ → Prop) : FVars S fTrue := ⟨trivial, trivial⟩
@[simp] theorem FVars_fFalse (S : ℕ → Prop) : FVars S fFalse := ⟨trivial, trivial⟩

@[simp] theorem FVars_bigAnd (S : ℕ → Prop) (l : List Formula) :
    FVars S (bigAnd l) ↔ ∀ φ ∈ l, FVars S φ := by
  induction l with
  | nil => simp [bigAnd]
  | cons φ l ih => simp only [bigAnd, List.foldr_cons] at ih ⊢; simp [ih]

@[simp] theorem FVars_bigOr (S : ℕ → Prop) (l : List Formula) :
    FVars S (bigOr l) ↔ ∀ φ ∈ l, FVars S φ := by
  induction l with
  | nil => simp [bigOr]
  | cons φ l ih => simp only [bigOr, List.foldr_cons] at ih ⊢; simp [ih]

@[simp] theorem FVars_fImp (S : ℕ → Prop) (φ ψ : Formula) :
    FVars S (fImp φ ψ) ↔ FVars S φ ∧ FVars S ψ := Iff.rfl

@[simp] theorem FVars_fNe (S : ℕ → Prop) (s t : Term) :
    FVars S (fNe s t) ↔ TVars S s ∧ TVars S t := Iff.rfl

@[simp] theorem TVars_bitsTerm (S : ℕ → Prop) (l : List Bool) : TVars S (bitsTerm l) := by
  induction l with
  | nil => trivial
  | cons b l ih => cases b <;> exact ⟨trivial, ⟨trivial, trivial⟩, ih⟩

@[simp] theorem TVars_natTerm (S : ℕ → Prop) (n : ℕ) : TVars S (natTerm n) :=
  TVars_bitsTerm S _

@[simp] theorem TVars_intTerm (S : ℕ → Prop) (z : ℤ) : TVars S (intTerm z) := by
  unfold intTerm; split_ifs
  · exact ⟨trivial, TVars_natTerm S _⟩
  · exact TVars_natTerm S _

theorem PVars_pvar {S : ℕ → Prop} {i : ℕ} (h0 : S i) (h1 : S (i + 1)) : PVars S (pvar i) :=
  ⟨h0, h1⟩

theorem PVars_vt {S : ℕ → Prop} {k : ℕ} (h0 : S (2 * k)) (h1 : S (2 * k + 1)) : PVars S (vt k) :=
  ⟨h0, h1⟩

theorem TVars_detT {S : ℕ → Prop} {a b c : PTerm} (ha : PVars S a) (hb : PVars S b)
    (hc : PVars S c) : TVars S (detT a b c) :=
  ⟨⟨⟨hb.1, ha.1⟩, ⟨hc.2, ha.2⟩⟩, ⟨⟨hc.1, ha.1⟩, ⟨hb.2, ha.2⟩⟩⟩

theorem TVars_dotT {S : ℕ → Prop} {p q r s : PTerm} (hp : PVars S p) (hq : PVars S q)
    (hr : PVars S r) (hs : PVars S s) : TVars S (dotT p q r s) :=
  ⟨⟨⟨hq.1, hp.1⟩, ⟨hs.1, hr.1⟩⟩, ⟨⟨hq.2, hp.2⟩, ⟨hs.2, hr.2⟩⟩⟩

theorem TVars_crossT {S : ℕ → Prop} {p q r s : PTerm} (hp : PVars S p) (hq : PVars S q)
    (hr : PVars S r) (hs : PVars S s) : TVars S (crossT p q r s) :=
  ⟨⟨⟨hq.1, hp.1⟩, ⟨hs.2, hr.2⟩⟩, ⟨⟨hq.2, hp.2⟩, ⟨hs.1, hr.1⟩⟩⟩

theorem FVars_ptEq {S : ℕ → Prop} {p q : PTerm} (hp : PVars S p) (hq : PVars S q) :
    FVars S (ptEq p q) :=
  ⟨⟨hp.1, hq.1⟩, ⟨hp.2, hq.2⟩⟩

theorem PVars_lerpT {S : ℕ → Prop} {a b : PTerm} {h : Term} (ha : PVars S a) (hb : PVars S b)
    (hh : TVars S h) : PVars S (lerpT a b h) :=
  ⟨⟨ha.1, hh, hb.1, ha.1⟩, ⟨ha.2, hh, hb.2, ha.2⟩⟩

/-! ## Gluing assignments on blocks of fresh variables -/

/-- The assignment equal to `x` below `base` and to `Y i` on the `i`-th block
`[base + i K, base + i K + K)`. -/
noncomputable def glue (x : ℕ → ℝ) (base K : ℕ) (Y : ℕ → ℕ → ℝ) (v : ℕ) : ℝ :=
  if v < base then x v else Y ((v - base) / K) v

theorem glue_of_lt {x : ℕ → ℝ} {base K : ℕ} {Y : ℕ → ℕ → ℝ} {v : ℕ} (h : v < base) :
    glue x base K Y v = x v := by
  simp [glue, h]

theorem glue_of_block {x : ℕ → ℝ} {base K : ℕ} {Y : ℕ → ℕ → ℝ} {i v : ℕ}
    (h1 : base + i * K ≤ v) (h2 : v < base + i * K + K) : glue x base K Y v = Y i v := by
  have hb : ¬ v < base := by omega
  have hK : 0 < K := by omega
  have hdiv : (v - base) / K = i := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]; omega
  simp [glue, hb, hdiv]

/-- The block predicate: below `base`, or in the `i`-th block. -/
def InBlock (base K i v : ℕ) : Prop := v < base ∨ (base + i * K ≤ v ∧ v < base + i * K + K)

/-- **Gluing.** If every formula `φ i` only uses variables below `base` or in its own block,
and `Y i` agrees with `x` below `base` and satisfies `φ i`, then the glued assignment agrees with
`x` below `base` and satisfies every `φ i`. -/
theorem holds_glue {x : ℕ → ℝ} {base K N : ℕ} {Y : ℕ → ℕ → ℝ} {φ : ℕ → Formula}
    (hvars : ∀ i < N, FVars (InBlock base K i) (φ i))
    (hY : ∀ i < N, (∀ v < base, Y i v = x v) ∧ (φ i).Holds (Y i)) :
    ∀ i < N, (φ i).Holds (glue x base K Y) := by
  intro i hi
  refine (holds_congr (S := InBlock base K i) ?_ (hvars i hi)).1 (hY i hi).2
  intro v hv
  rcases hv with hv | ⟨h1, h2⟩
  · rw [glue_of_lt hv, (hY i hi).1 v hv]
  · rw [glue_of_block h1 h2]

theorem glue_agree {x : ℕ → ℝ} {base K : ℕ} {Y : ℕ → ℕ → ℝ} :
    ∀ v < base, glue x base K Y v = x v := fun _ h => glue_of_lt h

/-- Gluing, in the form used to build satisfying assignments: if every block formula can be
satisfied by an assignment agreeing with `x` below `base`, then all of them can be satisfied
simultaneously. -/
theorem exists_glue {x : ℕ → ℝ} {base K N : ℕ} {φ : ℕ → Formula}
    (hvars : ∀ i < N, FVars (InBlock base K i) (φ i))
    (hex : ∀ i < N, ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ (φ i).Holds y) :
    ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ ∀ i < N, (φ i).Holds y := by
  have hex' : ∀ i, ∃ y : ℕ → ℝ, i < N → (∀ v < base, y v = x v) ∧ (φ i).Holds y := by
    intro i
    by_cases hi : i < N
    · obtain ⟨y, hy⟩ := hex i hi
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hi⟩
  choose Y hY using hex'
  exact ⟨glue x base K Y, glue_agree, holds_glue hvars fun i hi => hY i hi⟩

/-- An assignment updated on two consecutive variables. -/
noncomputable def upd2 (x : ℕ → ℝ) (i : ℕ) (a b : ℝ) (v : ℕ) : ℝ :=
  if v = i then a else if v = i + 1 then b else x v

@[simp] theorem upd2_fst (x : ℕ → ℝ) (i : ℕ) (a b : ℝ) : upd2 x i a b i = a := by
  simp [upd2]

@[simp] theorem upd2_snd (x : ℕ → ℝ) (i : ℕ) (a b : ℝ) : upd2 x i a b (i + 1) = b := by
  simp [upd2]

theorem upd2_of_lt {x : ℕ → ℝ} {i : ℕ} {a b : ℝ} {v : ℕ} (h : v < i) : upd2 x i a b v = x v := by
  have h1 : v ≠ i := by omega
  have h2 : v ≠ i + 1 := by omega
  simp [upd2, h1, h2]

theorem pvar_eval_upd2 (x : ℕ → ℝ) (i : ℕ) (a b : ℝ) : (pvar i).eval (upd2 x i a b) = (a, b) := by
  simp

/-! ## Index arithmetic -/

/-- `(i + 1) % n` is `i + 1` or (at the end) `0`. -/
theorem succ_mod_cases {i n : ℕ} (hi : i < n) :
    ((i + 1) % n = i + 1 ∧ i + 1 < n) ∨ ((i + 1) % n = 0 ∧ i + 1 = n) := by
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have : i + 1 = n := by omega
    exact Or.inr ⟨by rw [this, Nat.mod_self], this⟩

theorem succ_mod_lt {i n : ℕ} (hi : i < n) : (i + 1) % n < n := Nat.mod_lt _ (by omega)

theorem pair_div {m i j : ℕ} (hj : j < m) : (i * m + j) / m = i := by
  have hm : 0 < m := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem pair_mod {m i j : ℕ} (hj : j < m) : (i * m + j) % m = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem pair_lt {m M i j : ℕ} (hi : i < M) (hj : j < m) : i * m + j < M * m := by
  have : (i + 1) * m ≤ M * m := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-! ## Vertex variables -/

/-- The vertex variables hold the vertices of `P`: variables `2k`, `2k + 1` are the coordinates
of vertex `k`. -/
def VtxOK (P : Polygon) (x : ℕ → ℝ) : Prop := ∀ k < P.n, (vt k).eval x = P.vtx k

/-- The vertex variables of the first `n` vertices satisfy `S`. -/
def VtxVars (S : ℕ → Prop) (n : ℕ) : Prop := ∀ k < n, S (2 * k) ∧ S (2 * k + 1)

theorem VtxVars.pv {S : ℕ → Prop} {n k : ℕ} (h : VtxVars S n) (hk : k < n) : PVars S (vt k) :=
  ⟨(h k hk).1, (h k hk).2⟩

theorem VtxVars.mono {S S' : ℕ → Prop} {n : ℕ} (h : VtxVars S n) (hS : ∀ v, S v → S' v) :
    VtxVars S' n := fun k hk => ⟨hS _ (h k hk).1, hS _ (h k hk).2⟩

theorem vtxVars_lt {n N : ℕ} (h : 2 * n ≤ N) : VtxVars (· < N) n :=
  fun k hk => ⟨by omega, by omega⟩

theorem VtxOK.congr {P : Polygon} {x y : ℕ → ℝ} (hx : VtxOK P x)
    (hxy : ∀ v < 2 * P.n, y v = x v) : VtxOK P y := by
  intro k hk
  rw [← hx k hk]
  exact PTerm.eval_congr (S := (· < 2 * P.n)) (fun v hv => hxy v hv) ⟨by simp [vt, pvar]; omega,
    by simp [vt, pvar]; omega⟩

end ArtGallery.Membership

end
