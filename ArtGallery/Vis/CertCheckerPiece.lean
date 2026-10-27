module

public import ArtGallery.Vis.CertCheckerCross
public import ArtGallery.Geometry.Triangle

/-!
# Kernel-checkable certificates: convex pieces

A *convex piece* is the convex hull of a finite list `Q` of integer points (or, in the
half-plane form, an intersection `Irrational.hp l` of closed half-planes with integer
coefficients).  The check `pieceCheck V Q` certifies that the interior of the piece meets no
edge of the integer polygon `V`:

  `disjoint_interior_of_pieceCheck : pieceCheck V Q = true →
    ∀ i < n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i)`,

which is the hypothesis of `Polygon.closure_subset_filled_of_convex`; the packaged consequence is
`hull_subset_filled_of_pieceCheck` (the whole piece lies in the region once one interior point
does).  For every edge `a b` of the polygon the check looks for an affine functional `g`
(integer coefficients, not constant) that is `≥ 0` on all vertices of `Q` and `≤ 0` at `a` and
`b`; the candidates are tried in the order

1. the four sides of the bounding box of `Q` (box prefilter),
2. the lines of the edges of `Q`,
3. the line of the edge `a b` itself (both orientations).

The candidates of 1–2 are validated once for the piece (`pieceSeps`).  Interior points of a piece
are provided by `centroid_mem_interior_hull` and `mem_interior_hull_of_dets` /
`interiorCheck`.  Rational forms: `disjoint_interior_ratScale_of_pieceCheck`.
-/

@[expose] public section

namespace ArtGallery.Vis.Cert

open ArtGallery.Geometry ArtGallery.Hardening.Invariance ArtGallery.Irrational Set

/-! ### Affine functionals -/

/-- The value of the functional at an integer point. -/
def ivalHP (g : HP) (p : IPt) : ℤ := g.1 * p.1 + g.2.1 * p.2 + g.2.2

theorem val_intPoint_HP (g : HP) (p : IPt) : g.val (intPoint p) = (ivalHP g p : ℝ) := by
  simp only [HP.val, ivalHP, intPoint]; push_cast; ring

/-- The functional is not constant. -/
def nondegHP (g : HP) : Bool := !(g.1 == 0 && g.2.1 == 0)

theorem nondegHP_iff {g : HP} : nondegHP g = true ↔ ¬ (g.1 = 0 ∧ g.2.1 = 0) := by
  simp only [nondegHP, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    not_and_or]

/-- A non-constant affine functional that is `≥ 0` on `T` is `> 0` on the interior of `T`. -/
theorem pos_of_mem_interior_HP {g : HP} (hg : nondegHP g = true) {T : Set Point}
    (hT : ∀ x ∈ T, 0 ≤ g.val x) {x : Point} (hx : x ∈ interior T) : 0 < g.val x := by
  have hx0 := hT x (interior_subset hx)
  rcases lt_or_eq_of_le hx0 with h | h
  · exact h
  · exfalso
    set N : ℝ := (g.1 : ℝ) ^ 2 + (g.2.1 : ℝ) ^ 2 with hN
    have hNpos : 0 < N := by
      have := nondegHP_iff.1 hg
      rcases not_and_or.1 this with h1 | h1
      · have : (0 : ℝ) < (g.1 : ℝ) ^ 2 := by positivity
        positivity
      · have : (0 : ℝ) < (g.2.1 : ℝ) ^ 2 := by positivity
        positivity
    let v : Point := (x.1 + g.1, x.2 + g.2.1)
    have hv : g.val v = N := by
      have : g.val v = g.val x + N := by simp only [HP.val, v, hN]; ring
      rw [this, ← h, zero_add]
    refine not_mem_interior_of_affine_zero (v := v) (f := fun y => g.val y / N)
      (fun y hy => div_nonneg (hT y hy) hNpos.le) (fun s => ?_) ?_ ?_ hx
    · rw [HP.val_lerp]; field_simp
    · rw [hv, div_self hNpos.ne']
    · rw [← h, zero_div]

/-- A functional that is `≤ 0` at both endpoints is `≤ 0` on the segment. -/
theorem nonpos_of_mem_segment_HP {g : HP} {a b p : Point} (ha : g.val a ≤ 0) (hb : g.val b ≤ 0)
    (hp : p ∈ ArtGallery.segment a b) : g.val p ≤ 0 := by
  obtain ⟨t, h0, h1, rfl⟩ := mem_segment_iff_lerp.1 hp
  rw [HP.val_lerp]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 ha), mul_nonneg h0 (neg_nonneg.2 hb)]

/-- **Separation by a functional**: if a non-constant functional is `≥ 0` on `T` and `≤ 0` at the
endpoints of a segment, the interior of `T` misses the segment. -/
theorem disjoint_interior_segment_HP {g : HP} (hg : nondegHP g = true) {T : Set Point}
    (hT : ∀ x ∈ T, 0 ≤ g.val x) {a b : Point} (ha : g.val a ≤ 0) (hb : g.val b ≤ 0) :
    Disjoint (interior T) (ArtGallery.segment a b) :=
  Set.disjoint_left.2 fun _ hx hs =>
    absurd (nonpos_of_mem_segment_HP ha hb hs) (not_le.2 (pos_of_mem_interior_HP hg hT hx))

/-- The functional `x ↦ det a b x`. -/
def lineHP (a b : IPt) : HP := (-(b.2 - a.2), b.1 - a.1, (b.2 - a.2) * a.1 - (b.1 - a.1) * a.2)

/-- The opposite functional. -/
def negHP (g : HP) : HP := (-g.1, -g.2.1, -g.2.2)

theorem lineHP_val (a b : IPt) (x : Point) :
    (lineHP a b).val x = det (intPoint a) (intPoint b) x := by
  simp only [lineHP, HP.val, det, intPoint]; push_cast; ring

theorem negHP_val (g : HP) (x : Point) : (negHP g).val x = - g.val x := by
  simp only [negHP, HP.val]; push_cast; ring

/-! ### Convex pieces given by vertices -/

/-- `g` is a valid separator for the piece `Q`: not constant and `≥ 0` at every vertex. -/
def validHP (Q : List IPt) (g : HP) : Bool := nondegHP g && Q.all fun q => inonneg (ivalHP g q)

theorem nonneg_hull_of_validHP {Q : List IPt} {g : HP} (h : validHP Q g = true) :
    nondegHP g = true ∧ ∀ x ∈ convexHull ℝ (intSet Q), 0 ≤ g.val x := by
  simp only [validHP, Bool.and_eq_true, List.all_eq_true, inonneg_iff] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have hsub : intSet Q ⊆ hp [g] := by
    rintro _ ⟨z, hz, rfl⟩ c hc
    simp only [List.mem_singleton] at hc; subst hc
    rw [val_intPoint_HP]; exact_mod_cast h.2 z hz
  exact convexHull_min hsub (convex_hp [g]) hx g (List.mem_singleton_self g)

/-- The edges `(qₖ, qₖ₊₁)` of a closed chain whose first vertex is `a₀`. -/
def cycGo {α : Type} (a₀ : α) : List α → List (α × α)
  | a :: b :: rest => (a, b) :: cycGo a₀ (b :: rest)
  | [a] => [(a, a₀)]
  | [] => []

/-- The edges `(vᵢ, v_{(i+1) mod n})` of a closed chain. -/
def cycEdges {α : Type} : List α → List (α × α)
  | [] => []
  | a :: rest => cycGo a (a :: rest)

theorem length_cycGo {α : Type} (a₀ : α) (l : List α) : (cycGo a₀ l).length = l.length := by
  induction l with
  | nil => simp [cycGo]
  | cons a l ih =>
    match l, ih with
    | [], _ => simp [cycGo]
    | b :: rest, ih => simp only [cycGo, List.length_cons] at ih ⊢; rw [ih]

theorem getElem_cycGo {α : Type} (a₀ d : α) (l : List α) (k : ℕ) (hk : k < (cycGo a₀ l).length) :
    (cycGo a₀ l)[k] = (l.getD k d, (l ++ [a₀]).getD (k + 1) d) := by
  induction l generalizing k with
  | nil => simp [cycGo] at hk
  | cons a l ih =>
    match l, ih with
    | [], _ =>
      simp only [cycGo, List.length_singleton, Nat.lt_one_iff] at hk
      subst hk; simp [cycGo]
    | b :: rest, ih =>
      cases k with
      | zero => simp [cycGo]
      | succ k =>
        simp only [cycGo, List.length_cons] at hk
        simp only [cycGo, List.getElem_cons_succ]
        rw [ih k (by simpa [length_cycGo] using hk)]
        simp

/-- The edges of the closed chain, by index. -/
theorem mem_cycEdges {α : Type} (d : α) (V : List α) {i : ℕ} (hi : i < V.length) :
    (V.getD i d, V.getD ((i + 1) % V.length) d) ∈ cycEdges V := by
  match V, hi with
  | a :: rest, hi =>
    have hlen := length_cycGo a (a :: rest)
    have := getElem_cycGo a d (a :: rest) i (by omega)
    have e : ((a :: rest) ++ [a]).getD (i + 1) d =
        (a :: rest).getD ((i + 1) % (a :: rest).length) d := by
      by_cases h1 : i + 1 < (a :: rest).length
      · rw [getD_append_left' h1, Nat.mod_eq_of_lt h1]
      · have : i + 1 = (a :: rest).length := by omega
        rw [getD_append_right' (by omega), this, Nat.mod_self, Nat.sub_self]; rfl
    rw [e] at this
    rw [← this]
    exact List.getElem_mem _

/-- The sides of the bounding box of `Q` (`m` and `M` are the componentwise minimum and maximum
of `Q` and the origin; the validity of every candidate is checked anyway). -/
def boxHPs (Q : List IPt) : List HP :=
  let m := iminPt Q (0, 0)
  let M := iminPt (Q.map fun q => (-q.1, -q.2)) (0, 0)
  [(1, 0, -m.1), (-1, 0, -M.1), (0, 1, -m.2), (0, -1, -M.2)]

/-- The candidate separators of the piece `Q` that are valid. -/
def pieceSeps (Q : List IPt) : List HP :=
  (boxHPs Q ++ (cycEdges Q).map fun e => lineHP e.1 e.2).filter (validHP Q)

/-- The edge `a b` avoids the interior of the piece: some valid separator is `≤ 0` at `a` and
`b`; `seps` are separators validated beforehand. -/
def edgeAvoids (Q : List IPt) (seps : List HP) (a b : IPt) : Bool :=
  (seps.any fun g => inonpos (ivalHP g a) && inonpos (ivalHP g b)) ||
    validHP Q (lineHP a b) || validHP Q (negHP (lineHP a b))

theorem disjoint_of_edgeAvoids {Q : List IPt} {seps : List HP}
    (hseps : ∀ g ∈ seps, validHP Q g = true) {a b : IPt} (h : edgeAvoids Q seps a b = true) :
    Disjoint (interior (convexHull ℝ (intSet Q))) (ArtGallery.segment (intPoint a) (intPoint b)) := by
  simp only [edgeAvoids, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, inonpos_iff] at h
  rcases h with (⟨g, hg, ha, hb⟩ | h) | h
  · obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP (hseps g hg)
    refine disjoint_interior_segment_HP hnd hT ?_ ?_
    · rw [val_intPoint_HP]; exact_mod_cast ha
    · rw [val_intPoint_HP]; exact_mod_cast hb
  · obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP h
    refine disjoint_interior_segment_HP hnd hT ?_ ?_
    · rw [lineHP_val]; simp
    · rw [lineHP_val]; simp
  · obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP h
    refine disjoint_interior_segment_HP hnd hT ?_ ?_
    · rw [negHP_val, lineHP_val]; simp
    · rw [negHP_val, lineHP_val]; simp

/-- **The convex-piece check**: the interior of `conv Q` meets no edge of the polygon `V`. -/
def pieceCheck (V Q : List IPt) : Bool :=
  let seps := pieceSeps Q
  (cycEdges V).all fun e => edgeAvoids Q seps e.1 e.2

/-- Unfolding of `pieceCheck`. -/
theorem pieceCheck_eq (V Q : List IPt) :
    pieceCheck V Q = (cycEdges V).all fun e => edgeAvoids Q (pieceSeps Q) e.1 e.2 := rfl

/-- **Soundness of the convex-piece check.** -/
theorem disjoint_interior_of_pieceCheck {V Q : List IPt} (h : pieceCheck V Q = true) :
    ∀ i < (Polygon.mk (V.map intPoint)).n,
      Disjoint (interior (convexHull ℝ (intSet Q))) ((Polygon.mk (V.map intPoint)).edge i) := by
  intro i hi
  rw [n_map_intPoint] at hi
  rw [edge_map_intPoint]
  rw [pieceCheck_eq, List.all_eq_true] at h
  have hseps : ∀ g ∈ pieceSeps Q, validHP Q g = true := by
    intro g hg; simp only [pieceSeps, List.mem_filter] at hg; exact hg.2
  have hm := mem_cycEdges ((0 : ℤ), (0 : ℤ)) V hi
  have h' := h _ hm
  exact disjoint_of_edgeAvoids hseps h'

/-- A convex piece is compact, hence closed. -/
theorem isClosed_hull_intSet (Q : List IPt) : IsClosed (convexHull ℝ (intSet Q)) :=
  (isCompact_convexHull_of_finite (finite_intSet Q)).isClosed

/-- **Convex piece in the region**: a certified piece with one interior point in the region of
a simple polygon lies in the region. -/
theorem hull_subset_filled_of_pieceCheck {V Q : List IPt}
    (hP : (Polygon.mk (V.map intPoint)).Simple) (h : pieceCheck V Q = true) {z : Point}
    (hz : z ∈ interior (convexHull ℝ (intSet Q))) (hzP : z ∈ (Polygon.mk (V.map intPoint)).filled) :
    convexHull ℝ (intSet Q) ⊆ (Polygon.mk (V.map intPoint)).filled := by
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _)
    (disjoint_interior_of_pieceCheck h) hz hzP
  rwa [(isClosed_hull_intSet Q).closure_eq] at this

/-! ### Interior points of pieces -/

/-- The centroid of three non-collinear vertices is an interior point of the piece. -/
theorem centroid_mem_interior_hull {Q : List IPt} {a b c : IPt} (ha : a ∈ Q) (hb : b ∈ Q)
    (hc : c ∈ Q) (h : idet a b c ≠ 0) :
    centroid (intPoint a) (intPoint b) (intPoint c) ∈ interior (convexHull ℝ (intSet Q)) := by
  have hdet : det (intPoint a) (intPoint b) (intPoint c) ≠ 0 := by
    rw [det_intPoint]; exact_mod_cast h
  refine interior_mono (convexHull_mono ?_) (centroid_mem_interior hdet)
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [intPoint_mem_intSet ha, intPoint_mem_intSet hb, intPoint_mem_intSet hc]

/-- A point strictly inside a triangle of points of `S` (positively oriented) is an interior
point of the hull of `S`. -/
theorem mem_interior_hull_of_dets {S : Set Point} {a b c z : Point} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (habc : 0 < det a b c) (h₁ : 0 < det a b z) (h₂ : 0 < det b c z)
    (h₃ : 0 < det c a z) : z ∈ interior (convexHull ℝ S) := by
  have hne : det a b c ≠ 0 := habc.ne'
  refine interior_mono (convexHull_mono ?_) ((mem_interior_triangle_iff hne).2 ⟨?_, ?_, ?_⟩)
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · unfold bary₁; rw [← det_cyclic]; exact div_pos h₂ habc
  · unfold bary₂; rw [← det_cyclic_right]; exact div_pos h₃ habc
  · unfold bary₃; exact div_pos h₁ habc

/-- `z` is strictly inside the positively oriented triangle `a b c` of vertices of `Q`. -/
def interiorCheck (Q : List IPt) (a b c z : IPt) : Bool :=
  Q.elem a && Q.elem b && Q.elem c && ipos (idet a b c) && ipos (idet a b z) &&
    ipos (idet b c z) && ipos (idet c a z)

theorem mem_interior_of_interiorCheck {Q : List IPt} {a b c z : IPt}
    (h : interiorCheck Q a b c z = true) : intPoint z ∈ interior (convexHull ℝ (intSet Q)) := by
  simp only [interiorCheck, Bool.and_eq_true, List.elem_iff, ipos_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  refine mem_interior_hull_of_dets (intPoint_mem_intSet ha) (intPoint_mem_intSet hb)
    (intPoint_mem_intSet hc) ?_ ?_ ?_ ?_ <;> rw [det_intPoint] <;> exact_mod_cast ‹_›

/-! ### Convex pieces given by half-planes -/

/-- Every constraint is non-constant and every edge of `V` has a constraint `≤ 0` at both
endpoints. -/
def pieceCheckHP (V : List IPt) (l : List HP) : Bool :=
  (l.all nondegHP) &&
    (cycEdges V).all fun e => l.any fun g => inonpos (ivalHP g e.1) && inonpos (ivalHP g e.2)

/-- The interior of a closed piece with non-constant constraints lies in the open piece. -/
theorem interior_hp_subset_hpo {l : List HP} (hl : ∀ g ∈ l, nondegHP g = true) :
    interior (hp l) ⊆ hpo l := by
  intro x hx g hg
  exact pos_of_mem_interior_HP (hl g hg) (fun y hy => (show ∀ c ∈ l, 0 ≤ c.val y from hy) g hg) hx

/-- **Soundness of the half-plane piece check.** -/
theorem disjoint_interior_of_pieceCheckHP {V : List IPt} {l : List HP}
    (h : pieceCheckHP V l = true) :
    ∀ i < (Polygon.mk (V.map intPoint)).n,
      Disjoint (interior (hp l)) ((Polygon.mk (V.map intPoint)).edge i) := by
  intro i hi
  rw [n_map_intPoint] at hi
  rw [edge_map_intPoint]
  simp only [pieceCheckHP, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    inonpos_iff] at h
  obtain ⟨hnd, he⟩ := h
  obtain ⟨g, hg, ha, hb⟩ := he _ (mem_cycEdges (0, 0) V hi)
  refine disjoint_interior_segment_HP (hnd g hg) (fun y hy => (show ∀ c ∈ l, 0 ≤ c.val y from hy) g hg) ?_ ?_
  · rw [val_intPoint_HP]; exact_mod_cast ha
  · rw [val_intPoint_HP]; exact_mod_cast hb

/-- **Half-plane piece in the region.** -/
theorem hp_subset_filled_of_pieceCheckHP {V : List IPt} {l : List HP}
    (hP : (Polygon.mk (V.map intPoint)).Simple) (h : pieceCheckHP V l = true) {z : Point}
    (hz : z ∈ hpo l) (hzP : z ∈ (Polygon.mk (V.map intPoint)).filled) :
    hp l ⊆ (Polygon.mk (V.map intPoint)).filled := by
  have := Polygon.closure_subset_filled_of_convex hP (convex_hp l)
    (disjoint_interior_of_pieceCheckHP h) ((isOpen_hpo l).subset_interior_iff.2
      (hpo_subset_hp l) hz) hzP
  rwa [(isClosed_hp l).closure_eq] at this

/-! ### Rational forms -/

/-- **Convex-piece certificate, rational form.** -/
theorem disjoint_interior_ratScale_of_pieceCheck {D : ℕ} (hD : 0 < D) {V Q : List IPt}
    (h : pieceCheck V Q = true) :
    ∀ i < (Polygon.mk ((ratScale D V).map ratPoint)).n,
      Disjoint (interior (convexHull ℝ (ratSet (ratScale D Q))))
        ((Polygon.mk ((ratScale D V).map ratPoint)).edge i) := by
  intro i hi
  rw [mk_ratScale_eq D hD] at hi ⊢
  rw [n_mapPoly] at hi
  rw [ratSet_ratScale D hD, ← image_convexHull_affine, ← image_interior_affine,
    edge_mapPoly _ _ hi, Set.disjoint_image_iff (scaleDown D hD).injective]
  exact disjoint_interior_of_pieceCheck h i hi

/-- **Convex piece in the region, rational form.** -/
theorem hull_subset_filled_ratScale_of_pieceCheck {D : ℕ} (hD : 0 < D) {V Q : List IPt}
    (hP : (Polygon.mk ((ratScale D V).map ratPoint)).Simple) (h : pieceCheck V Q = true)
    {z : Point} (hz : z ∈ interior (convexHull ℝ (ratSet (ratScale D Q))))
    (hzP : z ∈ (Polygon.mk ((ratScale D V).map ratPoint)).filled) :
    convexHull ℝ (ratSet (ratScale D Q)) ⊆ (Polygon.mk ((ratScale D V).map ratPoint)).filled := by
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _)
    (disjoint_interior_ratScale_of_pieceCheck hD h) hz hzP
  rwa [(isCompact_convexHull_of_finite (finite_ratSet _)).isClosed.closure_eq] at this

end ArtGallery.Vis.Cert

end
