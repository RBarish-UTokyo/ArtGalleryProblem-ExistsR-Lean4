module

public import ArtGallery.Geometry.Det
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Convex.Topology

/-!
# Verified Boolean checks for polygons with rational vertices

For a polygon given by a list `vs` of rational points we provide Boolean checks, evaluated by
kernel computation, together with their soundness proofs:

* `simpleCheck vs = true → (Polygon.mk (vs.map ratPoint)).Simple` (`simple_of_simpleCheck`):
  consecutive edges are not collinear, any two non-adjacent edges are strictly separated (by an
  axis-parallel line or by the line of one of them);
* half-plane descriptions of convex pieces with integer coefficients (`hp`, closed, and `hpo`,
  open), and the checks `edgesInPieces` (every edge lies in one of the given closed pieces,
  `boundary_subset_of_edgesInPieces`) and `openAvoids` (an open piece meets no edge,
  `not_mem_boundary_of_openAvoids`).
-/

namespace ArtGallery.Irrational

@[expose] public section

open ArtGallery.Geometry Set

/-! ### Rational points -/

/-- Points with rational coordinates (the data of the checks). -/
abbrev QPt : Type := ℚ × ℚ

/-- The orientation determinant over `ℚ`. -/
def qdet (a b c : QPt) : ℚ := (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

theorem ratPoint_fst (a : QPt) : (ratPoint a).1 = (a.1 : ℝ) := rfl

theorem ratPoint_snd (a : QPt) : (ratPoint a).2 = (a.2 : ℝ) := rfl

/-- The real determinant of rational points is the rational one. -/
theorem det_ratPoint (a b c : QPt) :
    det (ratPoint a) (ratPoint b) (ratPoint c) = (qdet a b c : ℝ) := by
  simp only [det, qdet, ratPoint]; push_cast; ring

/-- `ratPoint` is injective. -/
theorem ratPoint_injective : Function.Injective ratPoint := by
  intro a b h
  simp only [ratPoint, Prod.mk.injEq, Rat.cast_inj] at h
  exact Prod.ext h.1 h.2

/-! ### Segments -/

/-- Points of a segment are convex combinations of the endpoints. -/
theorem mem_segment_coords {a b p : Point} (h : p ∈ ArtGallery.segment a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p.1 = (1 - t) * a.1 + t * b.1 ∧ p.2 = (1 - t) * a.2 + t * b.2 := by
  obtain ⟨t, h0, h1, rfl⟩ := h
  exact ⟨t, h0, h1, by ring, by ring⟩

theorem seg_fst_le {a b p : Point} (h : p ∈ ArtGallery.segment a b) : p.1 ≤ max a.1 b.1 := by
  obtain ⟨t, h0, h1, hx, -⟩ := mem_segment_coords h
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left a.1 b.1))
  have e2 := mul_nonneg h0 (sub_nonneg.2 (le_max_right a.1 b.1))
  nlinarith

theorem seg_fst_ge {a b p : Point} (h : p ∈ ArtGallery.segment a b) : min a.1 b.1 ≤ p.1 := by
  obtain ⟨t, h0, h1, hx, -⟩ := mem_segment_coords h
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left a.1 b.1))
  have e2 := mul_nonneg h0 (sub_nonneg.2 (min_le_right a.1 b.1))
  nlinarith

theorem seg_snd_le {a b p : Point} (h : p ∈ ArtGallery.segment a b) : p.2 ≤ max a.2 b.2 := by
  obtain ⟨t, h0, h1, -, hy⟩ := mem_segment_coords h
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left a.2 b.2))
  have e2 := mul_nonneg h0 (sub_nonneg.2 (le_max_right a.2 b.2))
  nlinarith

theorem seg_snd_ge {a b p : Point} (h : p ∈ ArtGallery.segment a b) : min a.2 b.2 ≤ p.2 := by
  obtain ⟨t, h0, h1, -, hy⟩ := mem_segment_coords h
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left a.2 b.2))
  have e2 := mul_nonneg h0 (sub_nonneg.2 (min_le_right a.2 b.2))
  nlinarith

/-- If both endpoints are strictly left of the line `a b`, so is the whole segment. -/
theorem det_pos_of_mem_segment {a b c d p : Point} (hc : 0 < det a b c) (hd : 0 < det a b d)
    (hp : p ∈ ArtGallery.segment c d) : 0 < det a b p := by
  obtain ⟨t, h0, h1, rfl⟩ := mem_segment_iff_lerp.1 hp
  rw [det_lerp]
  rcases eq_or_lt_of_le h0 with rfl | ht
  · simpa using hc
  · nlinarith

/-- If both endpoints are strictly right of the line `a b`, so is the whole segment. -/
theorem det_neg_of_mem_segment {a b c d p : Point} (hc : det a b c < 0) (hd : det a b d < 0)
    (hp : p ∈ ArtGallery.segment c d) : det a b p < 0 := by
  obtain ⟨t, h0, h1, rfl⟩ := mem_segment_iff_lerp.1 hp
  rw [det_lerp]
  rcases eq_or_lt_of_le h0 with rfl | ht
  · simpa using hc
  · nlinarith

/-- Two segments sharing the endpoint `b`, with `a b c` not collinear, meet only in `b`. -/
theorem eq_of_mem_segment_adjacent {a b c p : Point} (h : det a b c ≠ 0)
    (h1 : p ∈ ArtGallery.segment a b) (h2 : p ∈ ArtGallery.segment b c) : p = b := by
  have hp := det_eq_zero_of_mem_segment h1
  obtain ⟨s, -, -, rfl⟩ := mem_segment_iff_lerp.1 h2
  rw [det_lerp] at hp
  have hbb : det a b b = 0 := by unfold det; ring
  rw [hbb] at hp
  have hs : s = 0 := by
    rcases mul_eq_zero.1 (show s * det a b c = 0 by linarith) with hs | hs
    · exact hs
    · exact absurd hs h
  subst hs; simp

/-! ### Separation of two segments -/

/-- A sufficient Boolean condition for two closed segments to be disjoint: a strict separation
by an axis-parallel line or by the line through one of the segments. -/
def sepB (a b c d : QPt) : Bool :=
  decide (max a.1 b.1 < min c.1 d.1) || decide (max c.1 d.1 < min a.1 b.1) ||
  decide (max a.2 b.2 < min c.2 d.2) || decide (max c.2 d.2 < min a.2 b.2) ||
  decide (0 < qdet a b c ∧ 0 < qdet a b d) || decide (qdet a b c < 0 ∧ qdet a b d < 0) ||
  decide (0 < qdet c d a ∧ 0 < qdet c d b) || decide (qdet c d a < 0 ∧ qdet c d b < 0)

theorem disjoint_of_sepB {a b c d : QPt} (h : sepB a b c d = true) {p : Point}
    (h1 : p ∈ ArtGallery.segment (ratPoint a) (ratPoint b))
    (h2 : p ∈ ArtGallery.segment (ratPoint c) (ratPoint d)) : False := by
  simp only [sepB, Bool.or_eq_true, decide_eq_true_eq] at h
  have x1 := seg_fst_le h1; have x2 := seg_fst_ge h1
  have x3 := seg_fst_le h2; have x4 := seg_fst_ge h2
  have y1 := seg_snd_le h1; have y2 := seg_snd_ge h1
  have y3 := seg_snd_le h2; have y4 := seg_snd_ge h2
  simp only [ratPoint_fst, ratPoint_snd] at x1 x2 x3 x4 y1 y2 y3 y4
  have z1 := det_eq_zero_of_mem_segment h1
  have z2 := det_eq_zero_of_mem_segment h2
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · have : ((max a.1 b.1 : ℚ) : ℝ) < ((min c.1 d.1 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((max c.1 d.1 : ℚ) : ℝ) < ((min a.1 b.1 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((max a.2 b.2 : ℚ) : ℝ) < ((min c.2 d.2 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((max c.2 d.2 : ℚ) : ℝ) < ((min a.2 b.2 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have := det_pos_of_mem_segment (a := ratPoint a) (b := ratPoint b)
      (by rw [det_ratPoint]; exact_mod_cast h.1) (by rw [det_ratPoint]; exact_mod_cast h.2) h2
    linarith
  · have := det_neg_of_mem_segment (a := ratPoint a) (b := ratPoint b)
      (by rw [det_ratPoint]; exact_mod_cast h.1) (by rw [det_ratPoint]; exact_mod_cast h.2) h2
    linarith
  · have := det_pos_of_mem_segment (a := ratPoint c) (b := ratPoint d)
      (by rw [det_ratPoint]; exact_mod_cast h.1) (by rw [det_ratPoint]; exact_mod_cast h.2) h1
    linarith
  · have := det_neg_of_mem_segment (a := ratPoint c) (b := ratPoint d)
      (by rw [det_ratPoint]; exact_mod_cast h.1) (by rw [det_ratPoint]; exact_mod_cast h.2) h1
    linarith

/-! ### Simplicity -/

/-- The condition on the pair of edges `i < j` of the polygon `vs`. -/
def pairOK (vs : List QPt) (i j : ℕ) : Bool :=
  let n := vs.length
  let v := fun k => vs.getD k 0
  if j = i + 1 then decide (qdet (v i) (v j) (v ((j + 1) % n)) ≠ 0)
  else if i = 0 ∧ j + 1 = n then decide (qdet (v j) (v 0) (v 1) ≠ 0)
  else sepB (v i) (v ((i + 1) % n)) (v j) (v ((j + 1) % n))

/-- A sufficient Boolean condition for simplicity. -/
def simpleCheck (vs : List QPt) : Bool :=
  decide (3 ≤ vs.length) &&
  ((List.range vs.length).all fun i => (List.range vs.length).all fun j =>
    i == j || vs.getD i 0 != vs.getD j 0) &&
  ((List.range vs.length).all fun j => (List.range j).all fun i => pairOK vs i j)

/-- Vertices of the polygon of a rational list. -/
theorem vtx_map_ratPoint (vs : List QPt) (i : ℕ) :
    (Polygon.mk (vs.map ratPoint)).vtx i = ratPoint (vs.getD i 0) := by
  unfold Polygon.vtx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[i]? with
  | none => simp [ratPoint]
  | some a => simp

theorem n_map_ratPoint (vs : List QPt) : (Polygon.mk (vs.map ratPoint)).n = vs.length := by
  simp [Polygon.n]

/-- One half of the edge condition, for `i < j`. -/
theorem edge_inter_subset_of_pairOK {vs : List QPt} (h3 : 3 ≤ vs.length) {i j : ℕ} (hij : i < j)
    (hj : j < vs.length) (h : pairOK vs i j = true) :
    (Polygon.mk (vs.map ratPoint)).edge i ∩ (Polygon.mk (vs.map ratPoint)).edge j ⊆
      (Polygon.mk (vs.map ratPoint)).commonEndpoints i j := by
  rintro p ⟨h1, h2⟩
  simp only [Polygon.edge, Polygon.commonEndpoints, n_map_ratPoint, vtx_map_ratPoint] at h1 h2 ⊢
  unfold pairOK at h
  simp only at h
  split_ifs at h with hA hB
  · -- adjacent edges `i, i+1`
    subst hA
    have hi1 : (i + 1) % vs.length = i + 1 := Nat.mod_eq_of_lt hj
    rw [hi1] at h1 ⊢
    have hdet : det (ratPoint (vs.getD i 0)) (ratPoint (vs.getD (i + 1) 0))
        (ratPoint (vs.getD ((i + 1 + 1) % vs.length) 0)) ≠ 0 := by
      rw [det_ratPoint]; exact_mod_cast (of_decide_eq_true h)
    have := eq_of_mem_segment_adjacent hdet h1 h2
    exact ⟨Or.inr this, Or.inl this⟩
  · -- edges `n-1` and `0`
    obtain ⟨rfl, hB⟩ := hB
    have hj1 : (j + 1) % vs.length = 0 := by rw [hB, Nat.mod_self]
    have h01 : (0 + 1) % vs.length = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hj1] at h2 ⊢
    rw [h01] at h1 ⊢
    have hdet : det (ratPoint (vs.getD j 0)) (ratPoint (vs.getD 0 0))
        (ratPoint (vs.getD 1 0)) ≠ 0 := by
      rw [det_ratPoint]; exact_mod_cast (of_decide_eq_true h)
    have := eq_of_mem_segment_adjacent hdet h2 h1
    exact ⟨Or.inl this, Or.inr this⟩
  · exact (disjoint_of_sepB h h1 h2).elim

/-- **Soundness of the simplicity check.** -/
theorem simple_of_simpleCheck {vs : List QPt} (h : simpleCheck vs = true) :
    (Polygon.mk (vs.map ratPoint)).Simple := by
  simp only [simpleCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h3, hd⟩, he⟩ := h
  refine ⟨by rw [n_map_ratPoint]; exact h3, ?_, ?_⟩
  · intro i j hi hj hv
    rw [n_map_ratPoint] at hi hj
    rw [vtx_map_ratPoint, vtx_map_ratPoint] at hv
    rcases hd i hi j hj with h' | h'
    · exact h'
    · exact absurd (ratPoint_injective hv) h'
  · intro i j hi hj hij
    rw [n_map_ratPoint] at hi hj
    apply Subset.antisymm
    · rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact edge_inter_subset_of_pairOK h3 hlt hj (he j hj i hlt)
      · rw [inter_comm]
        intro p hp
        have := edge_inter_subset_of_pairOK h3 hlt hi (he i hi j hlt) hp
        simp only [Polygon.commonEndpoints, mem_ofPred_eq] at this ⊢
        exact ⟨this.2, this.1⟩
    · rintro p ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with rfl | rfl
        · exact Geometry.left_mem_segment _ _
        · exact Geometry.right_mem_segment _ _
      · rcases h2 with rfl | rfl
        · exact Geometry.left_mem_segment _ _
        · exact Geometry.right_mem_segment _ _

/-! ### Half-plane pieces -/

/-- A half-plane constraint `a * x + b * y + c ≥ 0` with integer coefficients `(a, b, c)`. -/
abbrev HP : Type := ℤ × ℤ × ℤ

/-- The value of the constraint at a real point. -/
def HP.val (c : HP) (p : Point) : ℝ := (c.1 : ℝ) * p.1 + (c.2.1 : ℝ) * p.2 + (c.2.2 : ℝ)

/-- The value of the constraint at a rational point. -/
def HP.qval (c : HP) (p : QPt) : ℚ := (c.1 : ℚ) * p.1 + (c.2.1 : ℚ) * p.2 + (c.2.2 : ℚ)

theorem HP.val_ratPoint (c : HP) (p : QPt) : c.val (ratPoint p) = (c.qval p : ℝ) := by
  simp only [HP.val, HP.qval, ratPoint]; push_cast; ring

theorem HP.val_lerp (c : HP) (a b : Point) (t : ℝ) :
    c.val (lerp a b t) = (1 - t) * c.val a + t * c.val b := by
  simp only [HP.val, lerp_fst, lerp_snd]; ring

theorem HP.continuous_val (c : HP) : Continuous c.val := by
  unfold HP.val; fun_prop

/-- The closed convex piece cut out by a list of constraints. -/
def hp (l : List HP) : Set Point := {p | ∀ c ∈ l, 0 ≤ c.val p}

/-- The open convex piece cut out by a list of constraints (strict inequalities). -/
def hpo (l : List HP) : Set Point := {p | ∀ c ∈ l, 0 < c.val p}

@[simp] theorem mem_hp_nil (p : Point) : p ∈ hp [] := by simp [hp]

@[simp] theorem mem_hp_cons (c : HP) (l : List HP) (p : Point) :
    p ∈ hp (c :: l) ↔ 0 ≤ (c.1 : ℝ) * p.1 + (c.2.1 : ℝ) * p.2 + (c.2.2 : ℝ) ∧ p ∈ hp l := by
  simp [hp, HP.val]

@[simp] theorem mem_hpo_nil (p : Point) : p ∈ hpo [] := by simp [hpo]

@[simp] theorem mem_hpo_cons (c : HP) (l : List HP) (p : Point) :
    p ∈ hpo (c :: l) ↔ 0 < (c.1 : ℝ) * p.1 + (c.2.1 : ℝ) * p.2 + (c.2.2 : ℝ) ∧ p ∈ hpo l := by
  simp [hpo, HP.val]

theorem convex_hp (l : List HP) : Convex ℝ (hp l) := by
  intro a ha b hb s t hs ht hst c hc
  have h1 := ha c hc; have h2 := hb c hc
  have : c.val (s • a + t • b) = s * c.val a + t * c.val b := by
    simp only [HP.val, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : s = 1 - t := by linarith
    subst this; ring
  rw [this]; positivity

theorem convex_hpo (l : List HP) : Convex ℝ (hpo l) := by
  intro a ha b hb s t hs ht hst c hc
  have h1 := ha c hc; have h2 := hb c hc
  have : c.val (s • a + t • b) = s * c.val a + t * c.val b := by
    simp only [HP.val, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : s = 1 - t := by linarith
    subst this; ring
  rw [this]
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst; subst hst; simpa using h2
  · nlinarith [mul_pos hs' h1, mul_nonneg ht h2.le]

theorem isClosed_hp (l : List HP) : IsClosed (hp l) := by
  have : hp l = ⋂ c ∈ l, {p | 0 ≤ c.val p} := by ext p; simp [hp]
  rw [this]
  exact isClosed_biInter fun c _ => isClosed_le continuous_const c.continuous_val

theorem isOpen_hpo (l : List HP) : IsOpen (hpo l) := by
  have : hpo l = ⋂ c ∈ l, {p | 0 < c.val p} := by ext p; simp [hpo]
  rw [this]
  exact (l.finite_toSet).isOpen_biInter fun c _ => isOpen_lt continuous_const c.continuous_val

theorem hpo_subset_hp (l : List HP) : hpo l ⊆ hp l := fun _ h c hc => (h c hc).le

/-- A closed piece with an interior point is the closure of its open part. -/
theorem hp_subset_closure_hpo {l : List HP} {z : Point} (hz : z ∈ hpo l) :
    hp l ⊆ closure (hpo l) := by
  intro q hq
  have hcont : Continuous fun t : ℝ => lerp q z t := continuous_lerp q z
  have hlim : Filter.Tendsto (fun t : ℝ => lerp q z t) (nhdsWithin 0 (Ioi 0)) (nhds q) := by
    have := hcont.tendsto 0
    simp only [lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  intro c hc
  rw [HP.val_lerp]
  have h1 := hq c hc; have h2 := hz c hc
  have := ht.1; have := ht.2
  nlinarith [mul_pos ht.1 h2, mul_nonneg (sub_nonneg.2 ht.2.le) h1]

/-- Membership of a rational point in a closed piece, as a Boolean. -/
def inHPB (l : List HP) (p : QPt) : Bool := l.all fun c => decide (0 ≤ c.qval p)

theorem mem_hp_of_inHPB {l : List HP} {p : QPt} (h : inHPB l p = true) : ratPoint p ∈ hp l := by
  intro c hc
  simp only [inHPB, List.all_eq_true, decide_eq_true_eq] at h
  rw [HP.val_ratPoint]; exact_mod_cast h c hc

/-- Every edge has both endpoints in one of the closed pieces. -/
def edgesInPieces (vs : List QPt) (pcs : List (List HP)) : Bool :=
  (List.range vs.length).all fun i => pcs.any fun pc =>
    inHPB pc (vs.getD i 0) && inHPB pc (vs.getD ((i + 1) % vs.length) 0)

/-- The union of a list of closed pieces. -/
def unionHP (pcs : List (List HP)) : Set Point := {p | ∃ pc ∈ pcs, p ∈ hp pc}

theorem boundary_subset_of_edgesInPieces {vs : List QPt} {pcs : List (List HP)}
    (h : edgesInPieces vs pcs = true) :
    (Polygon.mk (vs.map ratPoint)).boundary ⊆ unionHP pcs := by
  rintro p ⟨i, hi, hp⟩
  rw [n_map_ratPoint] at hi
  simp only [edgesInPieces, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨pc, hpc, h1, h2⟩ := h i hi
  refine ⟨pc, hpc, ?_⟩
  simp only [Polygon.edge, n_map_ratPoint, vtx_map_ratPoint] at hp
  exact segment_subset_of_convex (convex_hp pc) (mem_hp_of_inHPB h1) (mem_hp_of_inHPB h2) hp

/-- The open piece meets no edge: for every edge some constraint is `≤ 0` at both endpoints. -/
def openAvoids (vs : List QPt) (l : List HP) : Bool :=
  (List.range vs.length).all fun i => l.any fun c =>
    decide (c.qval (vs.getD i 0) ≤ 0) && decide (c.qval (vs.getD ((i + 1) % vs.length) 0) ≤ 0)

theorem not_mem_boundary_of_openAvoids {vs : List QPt} {l : List HP}
    (h : openAvoids vs l = true) {p : Point} (hp : p ∈ hpo l) :
    p ∉ (Polygon.mk (vs.map ratPoint)).boundary := by
  rintro ⟨i, hi, hpe⟩
  rw [n_map_ratPoint] at hi
  simp only [openAvoids, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨c, hc, h1, h2⟩ := h i hi
  simp only [Polygon.edge, n_map_ratPoint, vtx_map_ratPoint] at hpe
  obtain ⟨t, h0, h1', rfl⟩ := mem_segment_iff_lerp.1 hpe
  have := hp c hc
  rw [HP.val_lerp, HP.val_ratPoint, HP.val_ratPoint] at this
  have e1 : ((c.qval (vs.getD i 0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h1
  have e2 : ((c.qval (vs.getD ((i + 1) % vs.length) 0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h2
  nlinarith [mul_nonneg (sub_nonneg.2 h1') (neg_nonneg.2 e1), mul_nonneg h0 (neg_nonneg.2 e2)]

end

end ArtGallery.Irrational
