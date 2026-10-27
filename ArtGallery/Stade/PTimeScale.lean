module

public import ArtGallery.Stade.PTimePoly
public import ArtGallery.Stade.Simple
public import ArtGallery.Vis.CertCheckerTransfer

/-!
# Stade's polygon with integer coordinates

All vertices of `poly n Φ` are rationals with the common denominator
`Δ = denom n Φ = 9600 · (2H − 3)(2H − 1)(2H − 2)` (the template data have denominators dividing
`9600`, checked by `decide`; the wedges and the copy nooks have denominators dividing
`2(2H − 3)`, `4(2H − 1)`, `2H − 1`, `2H − 2`).  Hence

* `polyInt n Φ`: the vertices multiplied by `Δ`, as integers (`PT.polyInt`);
* `ratScale_polyInt : Vis.Cert.ratScale (denom n Φ) (polyInt n Φ) = poly n Φ`;
* the integer polygon is the image of the rational one under the scaling by `Δ`, so it is
  simple (`simple_polyInt`) and has a guard set (a boundary guard set) of cardinality `k` iff the
  rational polygon has (`hasGuardSetOfCard_polyInt_iff`, `hasBoundaryGuardSetOfCard_polyInt_iff`);
  these follow from the invariance of guard sets under invertible affine maps
  (`hasGuardSetOfCard_mapPoly_iff`, `hasBoundaryGuardSetOfCard_mapPoly_iff`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Stade

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV ArtGallery.Stade.Chain
open ArtGallery.Hardening.Invariance ArtGallery.Vis.Cert

/-! ### Integrality -/

/-- `q` is an integer. -/
structure IsInt (q : ℚ) : Prop where
  /-- The integer. -/
  out : ∃ z : ℤ, q = z

/-- `q` has a denominator dividing `9600` (the template denominators). -/
structure IsT (q : ℚ) : Prop where
  /-- `9600 q` is an integer. -/
  out : IsInt (9600 * q)

/-- The common denominator `Δ = 9600 (2H − 3)(2H − 1)(2H − 2)` of the vertices. -/
def denom (n : ℕ) (Φ : List Constraint) : ℕ :=
  9600 * ((2 * paramH n Φ - 3) * (2 * paramH n Φ - 1) * (2 * paramH n Φ - 2))

/-- `q` has a denominator dividing `Δ`. -/
structure IsD (n : ℕ) (Φ : List Constraint) (q : ℚ) : Prop where
  /-- `Δ q` is an integer. -/
  out : IsInt ((denom n Φ : ℚ) * q)

variable {n : ℕ} {Φ : List Constraint}

theorem isInt_add {a b : ℚ} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  obtain ⟨x, rfl⟩ := ha.out; obtain ⟨y, rfl⟩ := hb.out; exact ⟨x + y, by push_cast; ring⟩

theorem isInt_sub {a b : ℚ} (ha : IsInt a) (hb : IsInt b) : IsInt (a - b) := by
  obtain ⟨x, rfl⟩ := ha.out; obtain ⟨y, rfl⟩ := hb.out; exact ⟨x - y, by push_cast; ring⟩

theorem isInt_mul {a b : ℚ} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  obtain ⟨x, rfl⟩ := ha.out; obtain ⟨y, rfl⟩ := hb.out; exact ⟨x * y, by push_cast; ring⟩

theorem isInt_neg {a : ℚ} (ha : IsInt a) : IsInt (-a) := by
  obtain ⟨x, rfl⟩ := ha.out; exact ⟨-x, by push_cast; ring⟩

theorem isInt_natCast (m : ℕ) : IsInt (m : ℚ) := ⟨m, by push_cast; rfl⟩

theorem isInt_of_den {q : ℚ} (h : q.den = 1) : IsInt q :=
  ⟨q.num, (Rat.coe_int_num_of_den_eq_one h).symm⟩

theorem isT_of_isInt {a : ℚ} (ha : IsInt a) : IsT a := ⟨isInt_mul ⟨9600, by norm_num⟩ ha⟩

theorem isT_add {a b : ℚ} (ha : IsT a) (hb : IsT b) : IsT (a + b) :=
  ⟨by rw [mul_add]; exact isInt_add ha.out hb.out⟩

theorem isT_sub {a b : ℚ} (ha : IsT a) (hb : IsT b) : IsT (a - b) :=
  ⟨by rw [mul_sub]; exact isInt_sub ha.out hb.out⟩

theorem isT_neg {a : ℚ} (ha : IsT a) : IsT (-a) := ⟨by rw [mul_neg]; exact isInt_neg ha.out⟩

theorem isT_mul {a b : ℚ} (ha : IsInt a) (hb : IsT b) : IsT (a * b) :=
  ⟨by rw [mul_left_comm]; exact isInt_mul ha hb.out⟩

theorem isT_mul_right {a b : ℚ} (ha : IsT a) (hb : IsInt b) : IsT (a * b) := by
  rw [mul_comm]; exact isT_mul hb ha

theorem isT_of_den {q : ℚ} (h : (9600 * q).den = 1) : IsT q := ⟨isInt_of_den h⟩

theorem paramH_cast_sub (n : ℕ) (Φ : List Constraint) :
    ((2 * paramH n Φ - 3 : ℕ) : ℚ) = 2 * (paramH n Φ : ℚ) - 3 ∧
    ((2 * paramH n Φ - 1 : ℕ) : ℚ) = 2 * (paramH n Φ : ℚ) - 1 ∧
    ((2 * paramH n Φ - 2 : ℕ) : ℚ) = 2 * (paramH n Φ : ℚ) - 2 := by
  have := paramH_ge n Φ
  refine ⟨?_, ?_, ?_⟩ <;> rw [Nat.cast_sub (by omega)] <;> push_cast <;> ring

theorem denom_cast (n : ℕ) (Φ : List Constraint) : (denom n Φ : ℚ) =
    9600 * ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 1) *
      (2 * (paramH n Φ : ℚ) - 2)) := by
  obtain ⟨h1, h2, h3⟩ := paramH_cast_sub n Φ
  unfold denom
  push_cast [h1, h2, h3]
  ring

theorem denom_pos (n : ℕ) (Φ : List Constraint) : 0 < denom n Φ := by
  have := paramH_ge n Φ
  unfold denom
  apply Nat.mul_pos (by norm_num)
  apply Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

theorem two_H_sub_ne (n : ℕ) (Φ : List Constraint) :
    2 * (paramH n Φ : ℚ) - 3 ≠ 0 ∧ 2 * (paramH n Φ : ℚ) - 1 ≠ 0 ∧ 2 * (paramH n Φ : ℚ) - 2 ≠ 0 := by
  have := paramH_ge_q n Φ
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith

theorem isInt_two_H (n : ℕ) (Φ : List Constraint) (k : ℕ) :
    IsInt (2 * (paramH n Φ : ℚ) - k) :=
  isInt_sub (isInt_mul ⟨2, by norm_num⟩ (isInt_natCast _)) (isInt_natCast k)

theorem isD_of_isT {q : ℚ} (h : IsT q) : IsD n Φ q := by
  refine ⟨?_⟩
  rw [denom_cast, show ∀ K : ℚ, 9600 * K * q = K * (9600 * q) from fun K => by ring]
  refine isInt_mul ?_ h.out
  exact isInt_mul (isInt_mul (by exact_mod_cast isInt_two_H n Φ 3)
    (by exact_mod_cast isInt_two_H n Φ 1)) (by exact_mod_cast isInt_two_H n Φ 2)

theorem isD_add {a b : ℚ} (ha : IsD n Φ a) (hb : IsD n Φ b) : IsD n Φ (a + b) :=
  ⟨by rw [mul_add]; exact isInt_add ha.out hb.out⟩

theorem isD_sub {a b : ℚ} (ha : IsD n Φ a) (hb : IsD n Φ b) : IsD n Φ (a - b) :=
  ⟨by rw [mul_sub]; exact isInt_sub ha.out hb.out⟩

theorem isD_neg {a : ℚ} (ha : IsD n Φ a) : IsD n Φ (-a) :=
  ⟨by rw [mul_neg]; exact isInt_neg ha.out⟩

theorem isD_div3 {c : ℚ} (hc : IsT c) : IsD n Φ (c / (2 * (paramH n Φ : ℚ) - 3)) := by
  obtain ⟨h3, -, -⟩ := two_H_sub_ne n Φ
  refine ⟨?_⟩
  rw [denom_cast, show 9600 * ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 1) *
      (2 * (paramH n Φ : ℚ) - 2)) * (c / (2 * (paramH n Φ : ℚ) - 3)) =
      ((2 * (paramH n Φ : ℚ) - 1) * (2 * (paramH n Φ : ℚ) - 2)) * (9600 * c) by
    rw [mul_div_assoc', div_eq_iff (by assumption)]; ring]
  exact isInt_mul (isInt_mul (by exact_mod_cast isInt_two_H n Φ 1)
    (by exact_mod_cast isInt_two_H n Φ 2)) hc.out

theorem isD_div1 {c : ℚ} (hc : IsT c) : IsD n Φ (c / (2 * (paramH n Φ : ℚ) - 1)) := by
  obtain ⟨-, h1, -⟩ := two_H_sub_ne n Φ
  refine ⟨?_⟩
  rw [denom_cast, show 9600 * ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 1) *
      (2 * (paramH n Φ : ℚ) - 2)) * (c / (2 * (paramH n Φ : ℚ) - 1)) =
      ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 2)) * (9600 * c) by
    rw [mul_div_assoc', div_eq_iff (by assumption)]; ring]
  exact isInt_mul (isInt_mul (by exact_mod_cast isInt_two_H n Φ 3)
    (by exact_mod_cast isInt_two_H n Φ 2)) hc.out

theorem isD_div2 {c : ℚ} (hc : IsT c) : IsD n Φ (c / (2 * (paramH n Φ : ℚ) - 2)) := by
  obtain ⟨-, -, h2⟩ := two_H_sub_ne n Φ
  refine ⟨?_⟩
  rw [denom_cast, show 9600 * ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 1) *
      (2 * (paramH n Φ : ℚ) - 2)) * (c / (2 * (paramH n Φ : ℚ) - 2)) =
      ((2 * (paramH n Φ : ℚ) - 3) * (2 * (paramH n Φ : ℚ) - 1)) * (9600 * c) by
    rw [mul_div_assoc', div_eq_iff (by assumption)]; ring]
  exact isInt_mul (isInt_mul (by exact_mod_cast isInt_two_H n Φ 3)
    (by exact_mod_cast isInt_two_H n Φ 1)) hc.out

theorem isD_w3 : IsD n Φ (((paramH n Φ : ℚ) - 3) / (2 * (2 * (paramH n Φ : ℚ) - 3))) := by
  rw [← div_div]
  apply isD_div3
  refine ⟨?_⟩
  rw [show 9600 * (((paramH n Φ : ℚ) - 3) / 2) = 4800 * ((paramH n Φ : ℚ) - 3) by ring]
  exact isInt_mul ⟨4800, by norm_num⟩ (isInt_sub (isInt_natCast _) ⟨3, by norm_num⟩)

theorem isD_w4 : IsD n Φ (3 * ((paramH n Φ : ℚ) - 1) / (4 * (2 * (paramH n Φ : ℚ) - 1))) := by
  rw [← div_div]
  apply isD_div1
  refine ⟨?_⟩
  rw [show 9600 * (3 * ((paramH n Φ : ℚ) - 1) / 4) = 7200 * ((paramH n Φ : ℚ) - 1) by ring]
  exact isInt_mul ⟨7200, by norm_num⟩ (isInt_sub (isInt_natCast _) ⟨1, by norm_num⟩)

/-- Closure tactic for `IsD`, `IsT`, `IsInt` goals (complete: every branch must close its
goal). -/
syntax "isd_tac" : tactic

macro_rules
  | `(tactic| isd_tac) => `(tactic| first
    | assumption
    | exact isD_w3
    | exact isD_w4
    | (apply isD_div3 <;> isd_tac)
    | (apply isD_div1 <;> isd_tac)
    | (apply isD_div2 <;> isd_tac)
    | (apply isD_add <;> isd_tac)
    | (apply isD_sub <;> isd_tac)
    | (apply isD_neg <;> isd_tac)
    | (apply isD_of_isT <;> isd_tac)
    | (apply isT_add <;> isd_tac)
    | (apply isT_sub <;> isd_tac)
    | (apply isT_neg <;> isd_tac)
    | (apply isT_mul_right <;> isd_tac)
    | (apply isT_mul <;> isd_tac)
    | (apply isT_of_isInt <;> isd_tac)
    | (apply isT_of_den; norm_num; done)
    | (apply isInt_add <;> isd_tac)
    | (apply isInt_sub <;> isd_tac)
    | (apply isInt_mul <;> isd_tac)
    | (apply isInt_neg <;> isd_tac)
    | exact isInt_natCast _
    | (apply isInt_of_den; norm_num; done))

/-- Both coordinates have a denominator dividing `Δ`. -/
def GoodPt (n : ℕ) (Φ : List Constraint) (p : ℚ × ℚ) : Prop := IsD n Φ p.1 ∧ IsD n Φ p.2

/-! ### Template data -/

/-- The denominator of `q` divides `9600` (Boolean test). -/
def isTB (q : ℚ) : Bool := (9600 * q).den == 1

/-- The three components of a template vertex pass `isTB`. -/
def rptTB (p : RPt) : Bool := isTB p.1 && isTB p.2.1 && isTB p.2.2

theorem isT_of_isTB {q : ℚ} (h : isTB q = true) : IsT q :=
  isT_of_den (by simpa [isTB] using h)

theorem tmplFloor_tb :
    allKinds.all (fun k => (tmplFloor k).all (fun f => f.all rptTB)) = true := by
  decide +kernel

theorem needleDownL_tb : needleDownL.all rptTB = true := by decide +kernel

theorem tmplInputs_tb : allKinds.all (fun k => (tmplInputs k).all (fun i => isTB i.lx)) = true := by
  decide +kernel

theorem rpt_isT {p : RPt} (h : rptTB p = true) : IsT p.1 ∧ IsT p.2.1 ∧ IsT p.2.2 := by
  simp only [rptTB, Bool.and_eq_true] at h
  exact ⟨isT_of_isTB h.1.1, isT_of_isTB h.1.2, isT_of_isTB h.2⟩

theorem good_inst {ox : ℕ} {p : RPt} (h : rptTB p = true) :
    GoodPt n Φ (RPt.inst (paramH n Φ : ℚ) (ox : ℚ) p) := by
  obtain ⟨h1, h2, h3⟩ := rpt_isT h
  unfold RPt.inst GoodPt
  constructor <;> isd_tac

theorem tmplFloor_rpt {k : TKind} {f : List RPt} (hf : f ∈ tmplFloor k) {p : RPt} (hp : p ∈ f) :
    rptTB p = true := by
  have h := tmplFloor_tb
  simp only [List.all_eq_true] at h
  exact h k (mem_allKinds k) f hf p hp

theorem inputs_isT {i : InputSeg} (hi : i ∈ inputs n Φ) : IsT i.b := by
  simp only [inputs, slotInputs, List.mem_flatMap, List.mem_range, List.mem_map] at hi
  obtain ⟨c, -, t, ht, rfl⟩ := hi
  have h := tmplInputs_tb
  simp only [List.all_eq_true] at h
  have ht' := isT_of_isTB (h _ (mem_allKinds _) t ht)
  show IsT ((slotG n Φ c : ℚ) + t.lx)
  isd_tac

/-! ### Floor and ceiling -/

theorem good_floor {p : ℚ × ℚ} {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) (hp : p ∈ f) :
    GoodPt n Φ p := by
  simp only [floorFeats, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at hf
  rcases hf with ⟨k, -, rfl⟩ | ⟨c, -, ch, hch, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have h := needleDownL_tb
    simp only [List.all_eq_true] at h
    exact good_inst (h q hq)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact good_inst (tmplFloor_rpt hch hq)

theorem good_wedgeW1 {s : ℚ} (hs : IsT s) (pos : Bool) :
    ∀ p ∈ wedgeW1 s pos (paramH n Φ : ℚ), GoodPt n Φ p := by
  intro p hp
  cases pos <;>
  · simp only [wedgeW1, List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true,
      ↓reduceIte] at hp
    rcases hp with rfl | rfl | rfl <;> (unfold GoodPt; constructor <;> isd_tac)

theorem good_wedgeW3 {s T : ℚ} (hs : IsT s) (hT : IsT T) (pos : Bool) :
    ∀ p ∈ wedgeW3 s pos T (paramH n Φ : ℚ), GoodPt n Φ p := by
  intro p hp
  cases pos <;>
  · simp only [wedgeW3, List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true,
      ↓reduceIte] at hp
    rcases hp with rfl | rfl | rfl <;> (unfold GoodPt; constructor <;> isd_tac)

theorem good_wedgeW4 {s : ℚ} (hs : IsT s) : ∀ p ∈ wedgeW4 s (paramH n Φ : ℚ), GoodPt n Φ p := by
  intro p hp
  simp only [wedgeW4, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> (unfold GoodPt; constructor <;> isd_tac)

theorem good_wedgeW5 {s : ℚ} (hs : IsT s) : ∀ p ∈ wedgeW5 s (paramH n Φ : ℚ), GoodPt n Φ p := by
  intro p hp
  simp only [wedgeW5, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> (unfold GoodPt; constructor <;> isd_tac)

theorem isT_H3 : IsT (3 * (paramH n Φ : ℚ)) := by isd_tac
theorem isT_H4 : IsT (4 * (paramH n Φ : ℚ)) := by isd_tac

theorem good_inputCeil {b : ℚ} (hb : IsT b) (pos : Bool) :
    ∀ f ∈ inputCeil b pos (paramH n Φ : ℚ), ∀ p ∈ f, GoodPt n Φ p := by
  intro f hf p hp
  cases pos <;>
  · simp only [inputCeil, List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true,
      ↓reduceIte] at hf
    rcases hf with rfl | rfl
    · first | exact good_wedgeW1 hb _ p hp | exact good_wedgeW3 hb isT_H4 _ p hp
    · first | exact good_wedgeW1 hb _ p hp | exact good_wedgeW3 hb isT_H4 _ p hp

theorem good_varCeil {s : ℚ} (hs : IsT s) (one : Bool) :
    ∀ f ∈ varCeil s one (paramH n Φ : ℚ), ∀ p ∈ f, GoodPt n Φ p := by
  intro f hf p hp
  simp only [varCeil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with (rfl | rfl) | hf
  · exact good_wedgeW1 hs _ p hp
  · exact good_wedgeW3 hs isT_H3 _ p hp
  · cases one
    · simp at hf
    · simp only [↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact good_wedgeW4 hs p hp
      · exact good_wedgeW5 hs p hp

theorem isT_nookX {a b : ℚ} (ha : IsT a) (hb : IsT b) (ge : Bool) : IsT (nookX a b ge) := by
  unfold nookX copyE
  cases ge <;> (simp only [Bool.false_eq_true, ↓reduceIte]; isd_tac)

theorem good_copyNook {a b : ℚ} (ha : IsT a) (hb : IsT b) (ge : Bool) :
    ∀ p ∈ copyNook a b ge (paramH n Φ : ℚ), GoodPt n Φ p := by
  have hx := isT_nookX ha hb ge
  intro p hp
  cases ge <;>
  · simp only [copyNook, List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true,
      ↓reduceIte] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      (simp only [GoodPt, nookPs, nookPt, nookTop, nookBot]; constructor <;> isd_tac)

theorem good_ceil {p : ℚ × ℚ} {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) (hp : p ∈ f) :
    GoodPt n Φ p := by
  rcases mem_ceilFeats hf with ⟨i, hi, hfi⟩ | ⟨k, -, hfk⟩ | ⟨k, -, i, hi, -, rfl⟩
  · exact good_inputCeil (inputs_isT hi) i.pos f hfi p hp
  · exact good_varCeil (isT_of_isInt (isInt_natCast _)) _ f hfk p hp
  · exact good_copyNook (isT_of_isInt (isInt_natCast _)) (inputs_isT hi) _ p hp

/-- **Every vertex of the polygon has coordinates with denominator dividing `Δ`.** -/
theorem good_poly : ∀ p ∈ poly n Φ, GoodPt n Φ p := by
  intro p hp
  simp only [poly, List.mem_append, List.mem_flatten, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with (((rfl | ⟨f, hf, hp⟩) | (rfl | rfl)) | ⟨f, hf, hp⟩) | rfl
  · unfold GoodPt xL; constructor <;> isd_tac
  · exact good_floor hf hp
  · unfold GoodPt xR; constructor <;> isd_tac
  · unfold GoodPt xR; constructor <;> isd_tac
  · exact good_ceil hf hp
  · unfold GoodPt xL; constructor <;> isd_tac

/-! ### The integer polygon -/

/-- The integer `D · q` (correct when `D · q` is an integer). -/
def scaleQ (D : ℕ) (q : ℚ) : ℤ := ((D : ℚ) * q).num

/-- **The integer polygon**: the vertices of `poly n Φ` multiplied by `Δ = denom n Φ`. -/
def polyInt (n : ℕ) (Φ : List Constraint) : List (ℤ × ℤ) :=
  (poly n Φ).map fun p => (scaleQ (denom n Φ) p.1, scaleQ (denom n Φ) p.2)

theorem scaleQ_div {D : ℕ} (hD : 0 < D) {q : ℚ} (h : IsInt ((D : ℚ) * q)) :
    (scaleQ D q : ℚ) / D = q := by
  obtain ⟨z, hz⟩ := h.out
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold scaleQ
  rw [hz, Rat.num_intCast, ← hz]
  field_simp

/-- The integer polygon scaled down by `Δ` is the rational polygon. -/
theorem ratScale_polyInt (n : ℕ) (Φ : List Constraint) :
    ratScale (denom n Φ) (polyInt n Φ) = poly n Φ := by
  unfold ratScale polyInt
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (poly n Φ)]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨h1, h2⟩ := good_poly p hp
  simp only [Function.comp_apply, ratScalePt, id]
  rw [scaleQ_div (denom_pos n Φ) h1.out, scaleQ_div (denom_pos n Φ) h2.out]

/-- The rational polygon is the image of the integer polygon under the scaling by `1 / Δ`. -/
theorem mk_poly_eq_mapPoly (n : ℕ) (Φ : List Constraint) :
    Polygon.mk ((poly n Φ).map ratPoint) =
      mapPoly (scaleDown (denom n Φ) (denom_pos n Φ)) (Polygon.mk ((polyInt n Φ).map intPoint)) := by
  rw [← mk_ratScale_eq, ratScale_polyInt]

/-! ### Guard sets under invertible affine maps -/

section Affine

variable (A : Point ≃ᵃ[ℝ] Point) (P : Polygon)

theorem isGuardSet_mapPoly {G : Set Point} (h : P.IsGuardSet G) : (mapPoly A P).IsGuardSet (A '' G) := by
  refine ⟨?_, ?_⟩
  · rw [filled_mapPoly]; exact Set.image_mono h.1
  · intro p hp
    rw [filled_mapPoly] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨g, hg, hgx⟩ := h.2 x hx
    exact ⟨A g, Set.mem_image_of_mem _ hg, (sees_mapPoly_iff A P g x).2 hgx⟩

theorem isBoundaryGuardSet_mapPoly {G : Set Point} (h : P.IsBoundaryGuardSet G) :
    (mapPoly A P).IsBoundaryGuardSet (A '' G) := by
  refine ⟨?_, ?_⟩
  · rw [filled_mapPoly]; exact Set.image_mono h.1
  · intro p hp
    rw [boundary_mapPoly] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨g, hg, hgx⟩ := h.2 x hx
    exact ⟨A g, Set.mem_image_of_mem _ hg, (sees_mapPoly_iff A P g x).2 hgx⟩

theorem hasGuardSetOfCard_mapPoly {k : ℕ} (h : P.HasGuardSetOfCard k) :
    (mapPoly A P).HasGuardSetOfCard k := by
  obtain ⟨G, hG, hGS⟩ := h
  refine ⟨G.map A.toEquiv.toEmbedding, by rw [Finset.card_map, hG], ?_⟩
  rw [Finset.coe_map]
  exact isGuardSet_mapPoly A P hGS

theorem hasBoundaryGuardSetOfCard_mapPoly {k : ℕ} (h : P.HasBoundaryGuardSetOfCard k) :
    (mapPoly A P).HasBoundaryGuardSetOfCard k := by
  obtain ⟨G, hG, hGS⟩ := h
  refine ⟨G.map A.toEquiv.toEmbedding, by rw [Finset.card_map, hG], ?_⟩
  rw [Finset.coe_map]
  exact isBoundaryGuardSet_mapPoly A P hGS

/-- **Guard numbers are invariant under invertible affine maps.** -/
theorem hasGuardSetOfCard_mapPoly_iff {k : ℕ} :
    (mapPoly A P).HasGuardSetOfCard k ↔ P.HasGuardSetOfCard k := by
  refine ⟨fun h => ?_, hasGuardSetOfCard_mapPoly A P⟩
  have := hasGuardSetOfCard_mapPoly A.symm _ h
  rwa [mapPoly_symm_mapPoly] at this

/-- **Boundary guard numbers are invariant under invertible affine maps.** -/
theorem hasBoundaryGuardSetOfCard_mapPoly_iff {k : ℕ} :
    (mapPoly A P).HasBoundaryGuardSetOfCard k ↔ P.HasBoundaryGuardSetOfCard k := by
  refine ⟨fun h => ?_, hasBoundaryGuardSetOfCard_mapPoly A P⟩
  have := hasBoundaryGuardSetOfCard_mapPoly A.symm _ h
  rwa [mapPoly_symm_mapPoly] at this

end Affine

/-- The integer polygon is simple. -/
theorem simple_polyInt (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((polyInt n Φ).map intPoint)).Simple := by
  have h := simple n Φ
  rw [mk_poly_eq_mapPoly, simple_mapPoly_iff] at h
  exact h

/-- The integer polygon has a guard set of cardinality `k` iff the rational polygon has. -/
theorem hasGuardSetOfCard_polyInt_iff (n : ℕ) (Φ : List Constraint) (k : ℕ) :
    (Polygon.mk ((polyInt n Φ).map intPoint)).HasGuardSetOfCard k ↔
      (Polygon.mk ((poly n Φ).map ratPoint)).HasGuardSetOfCard k := by
  rw [mk_poly_eq_mapPoly, hasGuardSetOfCard_mapPoly_iff]

/-- The integer polygon has a boundary guard set of cardinality `k` iff the rational polygon
has. -/
theorem hasBoundaryGuardSetOfCard_polyInt_iff (n : ℕ) (Φ : List Constraint) (k : ℕ) :
    (Polygon.mk ((polyInt n Φ).map intPoint)).HasBoundaryGuardSetOfCard k ↔
      (Polygon.mk ((poly n Φ).map ratPoint)).HasBoundaryGuardSetOfCard k := by
  rw [mk_poly_eq_mapPoly, hasBoundaryGuardSetOfCard_mapPoly_iff]

/-! ### Polynomial time -/

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.denom {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => denom (n a) (Φ a)) := by
  unfold denom
  fun_prop

/-- **The integer polygon is polynomial-time.** -/
@[fun_prop] protected theorem PT.polyInt {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => polyInt (n a) (Φ a)) := by
  unfold polyInt scaleQ
  fun_prop

end ArtGallery.Stade

end
