module

public import ArtGallery.Irrational.Checker

/-!
# Kernel-checkable certificates: arithmetic primitives

Boolean primitives for the certificate checkers of `ArtGallery/Vis/CertChecker*.lean`, designed
for evaluation by `decide +kernel` (no `native_decide`), together with their soundness lemmas.

* **Natural points** `NPt = ℕ × ℕ` and `natPoint`.  The orientation determinant of natural
  points is the difference `detP − detN` of two natural numbers (`det_natPoint`); its sign is
  decided by one `Nat.blt` on kernel-accelerated (GMP) natural-number arithmetic (`dpos`,
  `dneg`).  The simplicity checker works on natural points (integer polygons are translated
  first, see `ArtGallery/Vis/CertCheckerSimple.lean`).
* **Boxes** (`Box`, `InBox`, `segBox`, `Box.union`, `boxSep`): axis-parallel bounding boxes and
  their strict separation.
* **Separation of two segments by a line** (`sepD`) and the **adjacent-edge test** (`tripleOK`).
* **Integer points**: the determinant `idet` of integer points and the constructor-matching sign
  tests `ilt`, `ile`, `ipos`, `ineg`, `inonneg`, `inonpos` (faster in the kernel than the
  `Decidable` instances of `ℤ`).
-/

@[expose] public section

namespace ArtGallery.Vis.Cert

open ArtGallery.Geometry Set

/-! ### Segments: coordinate bounds -/

/-- A lower bound for both endpoints is a lower bound on the segment (first coordinate). -/
theorem seg_fst_lb {a b p : Point} (h : p ∈ ArtGallery.segment a b) {L : ℝ} (ha : L ≤ a.1)
    (hb : L ≤ b.1) : L ≤ p.1 := by
  obtain ⟨t, h0, h1, hx, -⟩ := Irrational.mem_segment_coords h
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha), mul_nonneg h0 (sub_nonneg.2 hb)]

/-- An upper bound for both endpoints is an upper bound on the segment (first coordinate). -/
theorem seg_fst_ub {a b p : Point} (h : p ∈ ArtGallery.segment a b) {U : ℝ} (ha : a.1 ≤ U)
    (hb : b.1 ≤ U) : p.1 ≤ U := by
  obtain ⟨t, h0, h1, hx, -⟩ := Irrational.mem_segment_coords h
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha), mul_nonneg h0 (sub_nonneg.2 hb)]

/-- A lower bound for both endpoints is a lower bound on the segment (second coordinate). -/
theorem seg_snd_lb {a b p : Point} (h : p ∈ ArtGallery.segment a b) {L : ℝ} (ha : L ≤ a.2)
    (hb : L ≤ b.2) : L ≤ p.2 := by
  obtain ⟨t, h0, h1, -, hy⟩ := Irrational.mem_segment_coords h
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha), mul_nonneg h0 (sub_nonneg.2 hb)]

/-- An upper bound for both endpoints is an upper bound on the segment (second coordinate). -/
theorem seg_snd_ub {a b p : Point} (h : p ∈ ArtGallery.segment a b) {U : ℝ} (ha : a.2 ≤ U)
    (hb : b.2 ≤ U) : p.2 ≤ U := by
  obtain ⟨t, h0, h1, -, hy⟩ := Irrational.mem_segment_coords h
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha), mul_nonneg h0 (sub_nonneg.2 hb)]

/-! ### Natural points -/

/-- Points with natural coordinates (the data of the simplicity checker). -/
abbrev NPt : Type := ℕ × ℕ

/-- The real point with natural coordinates `p`. -/
def natPoint (p : NPt) : Point := ((p.1 : ℝ), (p.2 : ℝ))

@[simp] theorem natPoint_fst (p : NPt) : (natPoint p).1 = (p.1 : ℝ) := rfl

@[simp] theorem natPoint_snd (p : NPt) : (natPoint p).2 = (p.2 : ℝ) := rfl

@[simp] theorem natPoint_zero : natPoint (0, 0) = (0, 0) := by simp [natPoint]

/-- `natPoint` is injective. -/
theorem natPoint_injective : Function.Injective natPoint := by
  intro a b h
  simp only [natPoint, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- The positive part of the determinant of natural points. -/
def detP (a b c : NPt) : ℕ := b.1 * c.2 + c.1 * a.2 + a.1 * b.2

/-- The negative part of the determinant of natural points. -/
def detN (a b c : NPt) : ℕ := b.1 * a.2 + a.1 * c.2 + c.1 * b.2

/-- The determinant of natural points is `detP − detN`. -/
theorem det_natPoint (a b c : NPt) :
    det (natPoint a) (natPoint b) (natPoint c) = (detP a b c : ℝ) - (detN a b c : ℝ) := by
  simp only [det, natPoint, detP, detN]; push_cast; ring

/-- `c` is strictly left of the directed line `a → b`. -/
def dpos (a b c : NPt) : Bool := Nat.blt (detN a b c) (detP a b c)

/-- `c` is strictly right of the directed line `a → b`. -/
def dneg (a b c : NPt) : Bool := Nat.blt (detP a b c) (detN a b c)

theorem det_pos_of_dpos {a b c : NPt} (h : dpos a b c = true) :
    0 < det (natPoint a) (natPoint b) (natPoint c) := by
  rw [det_natPoint, sub_pos]
  have : detN a b c < detP a b c := by simpa [dpos, Nat.blt_eq] using h
  exact_mod_cast this

theorem det_neg_of_dneg {a b c : NPt} (h : dneg a b c = true) :
    det (natPoint a) (natPoint b) (natPoint c) < 0 := by
  rw [det_natPoint, sub_neg]
  have : detP a b c < detN a b c := by simpa [dneg, Nat.blt_eq] using h
  exact_mod_cast this

/-! ### Boxes -/

/-- A closed axis-parallel box `[x0, x1] × [y0, y1]` with natural bounds. -/
structure Box where
  /-- Left bound. -/
  x0 : ℕ
  /-- Right bound. -/
  x1 : ℕ
  /-- Lower bound. -/
  y0 : ℕ
  /-- Upper bound. -/
  y1 : ℕ

/-- The real point `p` lies in the box. -/
def InBox (bx : Box) (p : Point) : Prop :=
  (bx.x0 : ℝ) ≤ p.1 ∧ p.1 ≤ bx.x1 ∧ (bx.y0 : ℝ) ≤ p.2 ∧ p.2 ≤ bx.y1

/-- Minimum of two naturals (kernel-friendly). -/
def nmin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- Maximum of two naturals (kernel-friendly). -/
def nmax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

theorem ble_eq_false_of_not_le {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.ble_eq.mp hb) h

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  by_cases h : a ≤ b
  · simp [Nat.ble_eq.mpr h, h]
  · simp [ble_eq_false_of_not_le h]; omega

theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax
  by_cases h : a ≤ b
  · simp [Nat.ble_eq.mpr h, h]
  · simp [ble_eq_false_of_not_le h]; omega

theorem nmin_le_left (a b : ℕ) : nmin a b ≤ a := by rw [nmin_eq]; exact min_le_left _ _

theorem nmin_le_right (a b : ℕ) : nmin a b ≤ b := by rw [nmin_eq]; exact min_le_right _ _

theorem le_nmax_left (a b : ℕ) : a ≤ nmax a b := by rw [nmax_eq]; exact le_max_left _ _

theorem le_nmax_right (a b : ℕ) : b ≤ nmax a b := by rw [nmax_eq]; exact le_max_right _ _

/-- The bounding box of the segment `a b`. -/
def segBox (a b : NPt) : Box := ⟨nmin a.1 b.1, nmax a.1 b.1, nmin a.2 b.2, nmax a.2 b.2⟩

/-- A segment lies in its bounding box. -/
theorem inBox_segBox {a b : NPt} {p : Point}
    (h : p ∈ ArtGallery.segment (natPoint a) (natPoint b)) : InBox (segBox a b) p := by
  refine ⟨seg_fst_lb h ?_ ?_, seg_fst_ub h ?_ ?_, seg_snd_lb h ?_ ?_, seg_snd_ub h ?_ ?_⟩ <;>
    simp only [segBox, natPoint_fst, natPoint_snd, Nat.cast_le]
  exacts [nmin_le_left _ _, nmin_le_right _ _, le_nmax_left _ _, le_nmax_right _ _,
    nmin_le_left _ _, nmin_le_right _ _, le_nmax_left _ _, le_nmax_right _ _]

/-- The smallest box containing two boxes. -/
def Box.union (p q : Box) : Box :=
  ⟨nmin p.x0 q.x0, nmax p.x1 q.x1, nmin p.y0 q.y0, nmax p.y1 q.y1⟩

/-- The box `p` is contained in the box `q`. -/
def Box.Sub (p q : Box) : Prop := q.x0 ≤ p.x0 ∧ p.x1 ≤ q.x1 ∧ q.y0 ≤ p.y0 ∧ p.y1 ≤ q.y1

theorem Box.inBox_of_sub {p q : Box} (h : p.Sub q) {x : Point} (hx : InBox p x) : InBox q x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := hx
  refine ⟨le_trans (by exact_mod_cast h1) e1, le_trans e2 (by exact_mod_cast h2),
    le_trans (by exact_mod_cast h3) e3, le_trans e4 (by exact_mod_cast h4)⟩

theorem Box.sub_union_left (p q : Box) : p.Sub (p.union q) :=
  ⟨nmin_le_left _ _, le_nmax_left _ _, nmin_le_left _ _, le_nmax_left _ _⟩

theorem Box.sub_union_right (p q : Box) : q.Sub (p.union q) :=
  ⟨nmin_le_right _ _, le_nmax_right _ _, nmin_le_right _ _, le_nmax_right _ _⟩

/-- The boxes are strictly separated by a vertical or a horizontal line. -/
def boxSep (p q : Box) : Bool :=
  Nat.blt p.x1 q.x0 || Nat.blt q.x1 p.x0 || Nat.blt p.y1 q.y0 || Nat.blt q.y1 p.y0

/-- Strictly separated boxes have no common point. -/
theorem not_inBox_of_boxSep {p q : Box} (h : boxSep p q = true) {x : Point} (hp : InBox p x)
    (hq : InBox q x) : False := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  simp only [boxSep, Bool.or_eq_true, Nat.blt_eq] at h
  rcases h with ((h | h) | h) | h
  · have : (p.x1 : ℝ) < q.x0 := by exact_mod_cast h
    linarith
  · have : (q.x1 : ℝ) < p.x0 := by exact_mod_cast h
    linarith
  · have : (p.y1 : ℝ) < q.y0 := by exact_mod_cast h
    linarith
  · have : (q.y1 : ℝ) < p.y0 := by exact_mod_cast h
    linarith

/-! ### Separation of two segments by the line of one of them -/

/-- The segment `c d` lies strictly on one side of the line `a b`, or `a b` strictly on one side
of the line `c d`. -/
def sepD (a b c d : NPt) : Bool :=
  (dpos a b c && dpos a b d) || (dneg a b c && dneg a b d) ||
  (dpos c d a && dpos c d b) || (dneg c d a && dneg c d b)

/-- **Soundness of `sepD`**: the two closed segments are disjoint. -/
theorem disjoint_of_sepD {a b c d : NPt} (h : sepD a b c d = true) :
    Disjoint (ArtGallery.segment (natPoint a) (natPoint b))
      (ArtGallery.segment (natPoint c) (natPoint d)) := by
  rw [Set.disjoint_left]
  intro p h1 h2
  have z1 := det_eq_zero_of_mem_segment h1
  have z2 := det_eq_zero_of_mem_segment h2
  simp only [sepD, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((⟨h, h'⟩ | ⟨h, h'⟩) | ⟨h, h'⟩) | ⟨h, h'⟩
  · have := Irrational.det_pos_of_mem_segment (det_pos_of_dpos h) (det_pos_of_dpos h') h2
    linarith
  · have := Irrational.det_neg_of_mem_segment (det_neg_of_dneg h) (det_neg_of_dneg h') h2
    linarith
  · have := Irrational.det_pos_of_mem_segment (det_pos_of_dpos h) (det_pos_of_dpos h') h1
    linarith
  · have := Irrational.det_neg_of_mem_segment (det_neg_of_dneg h) (det_neg_of_dneg h') h1
    linarith

/-! ### Two consecutive edges -/

/-- Positive part of the scalar product `(a − b) · (c − b)`. -/
def dotP (a b c : NPt) : ℕ := a.1 * c.1 + b.1 * b.1 + a.2 * c.2 + b.2 * b.2

/-- Negative part of the scalar product `(a − b) · (c − b)`. -/
def dotN (a b c : NPt) : ℕ := a.1 * b.1 + b.1 * c.1 + a.2 * b.2 + b.2 * c.2

/-- The consecutive edges `a b` and `b c` meet only in `b`: the corner is not straight
(`det a b c ≠ 0`) or it is a straight corner with `b` strictly between `a` and `c`
(`(a − b) · (c − b) < 0`). -/
def tripleOK (a b c : NPt) : Bool :=
  !(Nat.beq (detP a b c) (detN a b c)) || Nat.blt (dotP a b c) (dotN a b c)

/-- The scalar product of natural points. -/
theorem dot_natPoint (a b c : NPt) :
    ((natPoint a).1 - (natPoint b).1) * ((natPoint c).1 - (natPoint b).1) +
      ((natPoint a).2 - (natPoint b).2) * ((natPoint c).2 - (natPoint b).2) =
      (dotP a b c : ℝ) - (dotN a b c : ℝ) := by
  simp only [natPoint, dotP, dotN]; push_cast; ring

/-- Two segments `a b` and `b c` with `(a − b) · (c − b) < 0` meet only in `b`. -/
theorem eq_of_mem_segment_dot {a b c p : Point}
    (hdot : (a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2) < 0)
    (h1 : p ∈ ArtGallery.segment a b) (h2 : p ∈ ArtGallery.segment b c) : p = b := by
  obtain ⟨s, hs0, hs1, hp1, hp2⟩ := Irrational.mem_segment_coords h1
  obtain ⟨t, ht0, ht1, hq1, hq2⟩ := Irrational.mem_segment_coords h2
  -- `p − b = (1 − s) (a − b) = t (c − b)`
  have e1 : (1 - s) * (a.1 - b.1) = t * (c.1 - b.1) := by linarith
  have e2 : (1 - s) * (a.2 - b.2) = t * (c.2 - b.2) := by linarith
  have key : (1 - s) * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) =
      t * ((a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2)) := by
    linear_combination (a.1 - b.1) * e1 + (a.2 - b.2) * e2
  have l1 : 0 ≤ (1 - s) * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have l2 : t * ((a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht0 hdot.le
  have ht : t = 0 := by
    have h0 : t * ((a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2)) = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd h hdot.ne
  subst ht
  exact point_ext (by linarith) (by linarith)

/-- **Soundness of `tripleOK`**: the consecutive segments meet only in `b`. -/
theorem eq_of_tripleOK {a b c : NPt} (h : tripleOK a b c = true) {p : Point}
    (h1 : p ∈ ArtGallery.segment (natPoint a) (natPoint b))
    (h2 : p ∈ ArtGallery.segment (natPoint b) (natPoint c)) : p = natPoint b := by
  simp only [tripleOK, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
  rcases h with h | h
  · have hne : detP a b c ≠ detN a b c := by
      intro he; simp [he] at h
    have hdet : det (natPoint a) (natPoint b) (natPoint c) ≠ 0 := by
      rw [det_natPoint, sub_ne_zero]; exact_mod_cast hne
    exact Irrational.eq_of_mem_segment_adjacent hdet h1 h2
  · refine eq_of_mem_segment_dot ?_ h1 h2
    rw [dot_natPoint, sub_neg]; exact_mod_cast h

/-- `tripleOK a b c` forces `a ≠ b`. -/
theorem ne_of_tripleOK {a b c : NPt} (h : tripleOK a b c = true) : a ≠ b := by
  rintro rfl
  simp only [tripleOK, detP, detN, dotP, dotN, Bool.or_eq_true, Bool.not_eq_true',
    Nat.blt_eq] at h
  rcases h with h | h
  · have : Nat.beq (a.1 * c.2 + c.1 * a.2 + a.1 * a.2) (a.1 * a.2 + a.1 * c.2 + c.1 * a.2) =
        true := by rw [Nat.beq_eq]; ring
    rw [this] at h; exact absurd h (by decide)
  · nlinarith

/-! ### Integer points -/

/-- Points with integer coordinates. -/
abbrev IPt : Type := ℤ × ℤ

@[simp] theorem intPoint_fst (p : IPt) : (intPoint p).1 = (p.1 : ℝ) := rfl

@[simp] theorem intPoint_snd (p : IPt) : (intPoint p).2 = (p.2 : ℝ) := rfl

@[simp] theorem intPoint_zero : intPoint (0, 0) = (0, 0) := by simp [intPoint]

/-- `intPoint` is injective. -/
theorem intPoint_injective : Function.Injective intPoint := by
  intro a b h
  simp only [intPoint, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- The set of real points of a list of integer points. -/
def intSet (l : List IPt) : Set Point := {x | ∃ z ∈ l, intPoint z = x}

theorem mem_intSet {l : List IPt} {x : Point} : x ∈ intSet l ↔ ∃ z ∈ l, intPoint z = x := Iff.rfl

theorem intPoint_mem_intSet {l : List IPt} {z : IPt} (h : z ∈ l) : intPoint z ∈ intSet l :=
  ⟨z, h, rfl⟩

@[simp] theorem intSet_nil : intSet [] = ∅ := by ext; simp [intSet]

@[simp] theorem intSet_cons (z : IPt) (l : List IPt) :
    intSet (z :: l) = insert (intPoint z) (intSet l) := by
  ext x; simp only [intSet, List.mem_cons, exists_eq_or_imp, mem_insert_iff, mem_ofPred_eq]
  exact or_congr ⟨fun h => h.symm, fun h => h.symm⟩ Iff.rfl

theorem finite_intSet (l : List IPt) : (intSet l).Finite := by
  have : intSet l = intPoint '' {z | z ∈ l} := by ext x; simp [intSet]
  rw [this]; exact (List.finite_toSet l).image _

/-- Vertices of the polygon of an integer list. -/
theorem vtx_map_intPoint (V : List IPt) (i : ℕ) :
    (Polygon.mk (V.map intPoint)).vtx i = intPoint (V.getD i (0, 0)) := by
  unfold Polygon.vtx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases V[i]? with
  | none => simp
  | some a => simp

theorem n_map_intPoint (V : List IPt) : (Polygon.mk (V.map intPoint)).n = V.length := by
  simp [Polygon.n]

/-- Edge `i` of the polygon of an integer list. -/
theorem edge_map_intPoint (V : List IPt) (i : ℕ) :
    (Polygon.mk (V.map intPoint)).edge i =
      ArtGallery.segment (intPoint (V.getD i (0, 0)))
        (intPoint (V.getD ((i + 1) % V.length) (0, 0))) := by
  simp only [Polygon.edge, vtx_map_intPoint, n_map_intPoint]

/-- The orientation determinant of integer points. -/
def idet (a b c : IPt) : ℤ := (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/-- The real determinant of integer points is the integer one. -/
theorem det_intPoint (a b c : IPt) :
    det (intPoint a) (intPoint b) (intPoint c) = (idet a b c : ℝ) := by
  simp only [det, idet, intPoint]; push_cast; ring

/-- `a < b` on integers, by matching constructors. -/
def ilt : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.blt m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.blt n m

/-- `a ≤ b` on integers, by matching constructors. -/
def ile : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m

/-- `0 < a`. -/
def ipos : ℤ → Bool
  | .ofNat (_ + 1) => true
  | _ => false

/-- `a < 0`. -/
def ineg : ℤ → Bool
  | .negSucc _ => true
  | _ => false

/-- `0 ≤ a`. -/
def inonneg : ℤ → Bool
  | .ofNat _ => true
  | _ => false

/-- `a ≤ 0`. -/
def inonpos : ℤ → Bool
  | .ofNat (_ + 1) => false
  | _ => true

theorem ilt_iff {a b : ℤ} : ilt a b = true ↔ a < b := by
  cases a <;> cases b <;> simp [ilt, Nat.blt_eq, Int.negSucc_eq] <;> omega

theorem ile_iff {a b : ℤ} : ile a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp [ile, Nat.ble_eq, Int.negSucc_eq] <;> omega

theorem ipos_iff {a : ℤ} : ipos a = true ↔ 0 < a := by
  rcases a with (_ | n) | n <;> simp [ipos, Int.negSucc_eq]

theorem ineg_iff {a : ℤ} : ineg a = true ↔ a < 0 := by
  rcases a with n | n <;> simp [ineg, Int.negSucc_eq]
  omega

theorem inonneg_iff {a : ℤ} : inonneg a = true ↔ 0 ≤ a := by
  rcases a with n | n <;> simp [inonneg, Int.negSucc_eq]
  omega

theorem inonpos_iff {a : ℤ} : inonpos a = true ↔ a ≤ 0 := by
  rcases a with (_ | n) | n <;> simp [inonpos, Int.negSucc_eq]

end ArtGallery.Vis.Cert

end
