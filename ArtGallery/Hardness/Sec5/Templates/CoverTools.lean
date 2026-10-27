module

public import ArtGallery.Hardness.Sec5.Templates.Tools

/-!
# Section 5 templates: tools for the coverage certificates (T-cover)

`docs/section5/08_proof_plan.md` §7 (T-cover), §9.  A template's region is covered by finitely
many convex integer pieces `conv Q` (`Q` a counter-clockwise convex vertex list), each seen by one
canonical guard (or a zone treated by the mechanism lemmas).  This file provides:

* **visibility of a piece** (`hull_subset_filled_of_auto`, `sees_of_hull_subset`): the hull of the
  piece together with the extreme positions of its guard lies in the region (`pieceAutoB`: the
  separators of every chain edge are searched automatically among the edge lines and the
  bounding box of the hull and the chain edge line);
* **membership in a piece from its edges** (`mem_hull_of_edges`): a point on the nonnegative side
  of every edge of a convex polygon (fan data `fanB`) is in its hull;
* **Farkas certificates** (`implB`): an affine function is `≥ 0` on a cell `{cs ≥ 0}`;
* **completeness** (`filled_subset_cover`): the filled region of a fixed integer polygon `K`
  (the closed template chain) lies in the union of the pieces.  Certificate: a BSP tree on a box
  containing `K` whose leaves are either inside a piece (Farkas certificates for its edges), or
  have a free ray (`ray`), or are joined by segments to an *anchor* with a free ray (`link`) --
  such points are not in `K.filled` unless they lie on its boundary; the boundary is covered
  edge by edge (`bdCoverB`).  This uses only the definition of `filled` (bounded components of
  the complement of the boundary).
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)

/-! ### Farkas certificates -/

/-- The sparse nonnegative combination `Σ l • cs[i]` (pairs `(i, l)`). -/
def combS (cs : List HP) : List (ℕ × ℕ) → HP
  | [] => (0, 0, 0)
  | (i, l) :: rest =>
    ((l : ℤ) * (cs.getD i (0, 0, 0)).1 + (combS cs rest).1,
      (l : ℤ) * (cs.getD i (0, 0, 0)).2.1 + (combS cs rest).2.1,
      (l : ℤ) * (cs.getD i (0, 0, 0)).2.2 + (combS cs rest).2.2)

theorem getD_val_nonneg {cs : List HP} {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) (i : ℕ) :
    0 ≤ (cs.getD i (0, 0, 0)).val z := by
  rw [List.getD_eq_getElem?_getD]
  cases h : cs[i]? with
  | none => simp [Irrational.HP.val]
  | some c => exact hz c (List.mem_of_getElem? h)

theorem combS_val_nonneg (cs : List HP) {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) :
    ∀ lam : List (ℕ × ℕ), 0 ≤ (combS cs lam).val z
  | [] => by simp [combS, Irrational.HP.val]
  | (i, l) :: rest => by
    have ih := combS_val_nonneg cs hz rest
    have hi := getD_val_nonneg hz i
    simp only [combS, Irrational.HP.val] at ih hi ⊢
    push_cast
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith [mul_nonneg this hi]

/-- `c • e = Σ λᵢ csᵢ + μ` with `c > 0`, `μ ≥ 0`: `e ≥ 0` follows from `cs ≥ 0`. -/
def implB (cs : List HP) (e : HP) (c : ℕ) (lam : List (ℕ × ℕ)) : Bool :=
  Nat.blt 0 c && ((c : ℤ) * e.1 == (combS cs lam).1) && ((c : ℤ) * e.2.1 == (combS cs lam).2.1) &&
    ile (combS cs lam).2.2 ((c : ℤ) * e.2.2)

theorem implB_sound {cs : List HP} {e : HP} {c : ℕ} {lam : List (ℕ × ℕ)}
    (h : implB cs e c lam = true) {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) : 0 ≤ e.val z := by
  simp only [implB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, ile_iff] at h
  obtain ⟨⟨⟨hc, h1⟩, h2⟩, h3⟩ := h
  have hs := combS_val_nonneg cs hz lam
  set s := combS cs lam
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have key : (c : ℝ) * e.val z = s.val z + ((c : ℝ) * e.2.2 - s.2.2) := by
    simp only [Irrational.HP.val]
    have e1 : ((c : ℤ) * e.1 : ℤ) = s.1 := h1
    have e2 : ((c : ℤ) * e.2.1 : ℤ) = s.2.1 := h2
    have e1' : (c : ℝ) * (e.1 : ℝ) = (s.1 : ℝ) := by exact_mod_cast e1
    have e2' : (c : ℝ) * (e.2.1 : ℝ) = (s.2.1 : ℝ) := by exact_mod_cast e2
    linear_combination z.1 * e1' + z.2 * e2'
  have h3' : (s.2.2 : ℝ) ≤ (c : ℝ) * e.2.2 := by exact_mod_cast h3
  have : 0 ≤ (c : ℝ) * e.val z := by rw [key]; linarith
  exact (mul_nonneg_iff_of_pos_left hcr).1 this

/-! ### Convex polygons: membership from the edges -/

/-- The edge functionals `x ↦ det(Qₖ, Qₖ₊₁, x)` of a closed vertex list. -/
def edgesHP (Q : List IPt) : List HP := (cycEdges Q).map fun e => lineHP e.1 e.2

/-- Fan data of a convex counter-clockwise polygon: at least three vertices and
`det(Q₀, Qₖ, Qₖ₊₁) > 0` for `1 ≤ k ≤ n − 2`. -/
def fanB (Q : List IPt) : Bool :=
  Nat.blt 2 Q.length && (List.range (Q.length - 2)).all fun k =>
    ipos (idet (Q.getD 0 (0, 0)) (Q.getD (k + 1) (0, 0)) (Q.getD (k + 2) (0, 0)))

/-- The integer point `p` is on the nonnegative side of every edge of `Q`. -/
def inHullB (Q : List IPt) (p : IPt) : Bool := (edgesHP Q).all fun g => inonneg (ivalHP g p)

/-- An integer point in the hull of a vertex list. -/
theorem mem_intSet_hull {Q : List IPt} {q : IPt} (h : q ∈ Q) :
    intPoint q ∈ convexHull ℝ (intSet Q) :=
  subset_convexHull ℝ _ (intPoint_mem_intSet h)

/-- **Membership from the edges.** -/
theorem mem_hull_of_edges {Q : List IPt} (hQ : fanB Q = true) {z : Point}
    (h : ∀ g ∈ edgesHP Q, 0 ≤ g.val z) : z ∈ convexHull ℝ (intSet Q) := by
  simp only [fanB, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range, ipos_iff] at hQ
  obtain ⟨hn, hfan⟩ := hQ
  set n := Q.length with hn_def
  set q : ℕ → Point := fun k => intPoint (Q.getD k (0, 0)) with hq
  have hmem : ∀ k < n, Q.getD k (0, 0) ∈ Q := fun k hk => getD_mem' hk
  -- the edge conditions
  have hedge : ∀ k < n, 0 ≤ det (q k) (q ((k + 1) % n)) z := by
    intro k hk
    have hm := mem_cycEdges ((0 : ℤ), (0 : ℤ)) Q hk
    have := h _ (List.mem_map.2 ⟨_, hm, rfl⟩)
    rwa [lineHP_val] at this
  have hfan' : ∀ k, k + 2 < n → 0 < det (q 0) (q (k + 1)) (q (k + 2)) := by
    intro k hk
    rw [det_intPoint]; exact_mod_cast hfan k (by omega)
  -- the sign change of `f k = det(q 0, q k, z)`
  set f : ℕ → ℝ := fun k => det (q 0) (q k) z with hf
  have hf1 : 0 ≤ f 1 := by
    have := hedge 0 (by omega)
    rwa [show (0 + 1) % n = 1 from Nat.mod_eq_of_lt (by omega)] at this
  have hflast : f (n - 1) ≤ 0 := by
    have := hedge (n - 1) (by omega)
    rw [show (n - 1 + 1) % n = 0 by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]] at this
    have e : det (q (n - 1)) (q 0) z = - f (n - 1) := by
      simp only [hf]; exact Geometry.det_swap12 _ _ _
    linarith
  have hex : ∃ k, 1 ≤ k ∧ k + 2 ≤ n ∧ f (k + 1) ≤ 0 :=
    ⟨n - 2, by omega, by omega, by rw [show n - 2 + 1 = n - 1 by omega]; exact hflast⟩
  classical
  set k := Nat.find hex with hk
  obtain ⟨hk1, hk2, hk3⟩ := Nat.find_spec hex
  have hfk : 0 ≤ f k := by
    rcases Nat.lt_or_ge 1 k with h1 | h1
    · have hmin := Nat.find_min hex (show k - 1 < k by omega)
      simp only [not_and, not_le] at hmin
      have := hmin (by omega) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      exact this.le
    · rw [show k = 1 by omega]; exact hf1
  have hD := hfan' (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at hD
  have hek := hedge k (by omega)
  rw [show (k + 1) % n = k + 1 from Nat.mod_eq_of_lt (by omega)] at hek
  have htri : z ∈ convexHull ℝ ({q 0, q k, q (k + 1)} : Set Point) := by
    refine (Geometry.mem_triangle_iff_bary hD.ne').2 ⟨?_, ?_, ?_⟩
    · unfold Geometry.bary₁; rw [← Geometry.det_cyclic]; exact div_nonneg hek hD.le
    · unfold Geometry.bary₂
      refine div_nonneg ?_ hD.le
      rw [Geometry.det_swap23]; linarith
    · unfold Geometry.bary₃; exact div_nonneg hfk hD.le
  refine convexHull_min ?_ (convex_convexHull ℝ _) htri
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mem_intSet_hull (hmem 0 (by omega))
  · exact mem_intSet_hull (hmem k (by omega))
  · exact mem_intSet_hull (hmem (k + 1) (by omega))

/-- An integer point passing `inHullB` is in the hull. -/
theorem mem_hull_of_inHullB {Q : List IPt} (hQ : fanB Q = true) {p : IPt}
    (h : inHullB Q p = true) : intPoint p ∈ convexHull ℝ (intSet Q) := by
  refine mem_hull_of_edges hQ fun g hg => ?_
  simp only [inHullB, List.all_eq_true, inonneg_iff] at h
  rw [val_intPoint_HP]; exact_mod_cast h g hg

/-- Conversely, the points of the hull are on the nonnegative side of every edge (checked on the
vertices). -/
theorem edges_nonneg_of_mem_hull {Q : List IPt}
    (h : ((edgesHP Q).all fun g => Q.all fun q => inonneg (ivalHP g q)) = true) {z : Point}
    (hz : z ∈ convexHull ℝ (intSet Q)) : ∀ g ∈ edgesHP Q, 0 ≤ g.val z := by
  intro g hg
  simp only [List.all_eq_true] at h
  exact nonneg_on_hull (by simpa [List.all_eq_true] using h g hg) z hz

/-! ### Visibility of a piece -/

/-- The bounding box of `Q` (true minimum / maximum) as four half-planes. -/
def bboxT (Q : List IPt) : List HP :=
  let m := iminPt Q (Q.headD (0, 0))
  let M := iminPt (Q.map fun q => (-q.1, -q.2)) ((Q.headD (0, 0)).1 * -1, (Q.headD (0, 0)).2 * -1)
  [(1, 0, -m.1), (-1, 0, -M.1), (0, 1, -m.2), (0, -1, -M.2)]

/-- The valid candidate separators of `Q`: the bounding box and the lines through any two points
of `Q`. -/
def sepsT (Q : List IPt) : List HP :=
  (bboxT Q ++ Q.flatMap fun x => Q.map fun y => lineHP x y).filter (validHP Q)

/-- **Automatic piece check for a chain**: every edge of the open chain `V` avoids the interior
of `conv Q`. -/
def pieceAutoB (V Q : List IPt) : Bool :=
  (List.range (V.length - 1)).all fun j => edgeAvoids Q (sepsT Q) (cv V j) (cv V (j + 1))

theorem disjoint_of_pieceAutoB {V Q : List IPt} (h : pieceAutoB V Q = true) {j : ℕ}
    (hj : j + 1 < V.length) :
    Disjoint (interior (convexHull ℝ (intSet Q)))
      (ArtGallery.segment (intPoint (cv V j)) (intPoint (cv V (j + 1)))) := by
  simp only [pieceAutoB, List.all_eq_true, List.mem_range] at h
  have hseps : ∀ g ∈ sepsT Q, validHP Q g = true := by
    intro g hg; simp only [sepsT, List.mem_filter] at hg; exact hg.2
  exact disjoint_of_edgeAvoids hseps (h j (by omega))

variable {P : Polygon} {V : List IPt} {a : ℕ}

/-- **Convex piece in the region** (automatic separators, Farkas region check). -/
theorem hull_subset_filled_of_auto {R : Region} (hP : P.Simple) (hC : ChainAt P V a)
    (hS : SepAt P V a R) {Q : List IPt} {cert : List (List ℕ × ℕ)}
    (hpc : pieceAutoB V Q = true) (hR : R.checkF Q cert = true) {z : Point}
    (hz : z ∈ interior (convexHull ℝ (intSet Q))) (hzP : z ∈ P.filled) :
    convexHull ℝ (intSet Q) ⊆ P.filled := by
  have hedge : ∀ i < P.n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i) := by
    intro i hi
    by_cases hc : ∃ j, j + 1 < V.length ∧ (a + j) % P.n = i
    · obtain ⟨j, hj, rfl⟩ := hc
      rw [hC.edge_eq hj]
      exact disjoint_of_pieceAutoB hpc hj
    · push Not at hc
      rw [Set.disjoint_left]
      intro x hx hxe
      exact hS i hi (fun j hj h => hc j hj h) x hxe (Region.interior_hull_subset_F hR hx)
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _) hedge hz hzP
  rwa [(isClosed_hull_intSet Q).closure_eq] at this

/-- **Visibility from a certified hull**: if `conv Qc ⊆ filled` and the guard points `G` and the
piece `Q` are listed in `Qc`, every point of `conv G` sees every point of `conv Q`. -/
theorem sees_of_hull_subset {Qc G Q : List IPt} (hsub : convexHull ℝ (intSet Qc) ⊆ P.filled)
    (hG : (G.all fun x => Qc.elem x) = true) (hQ : (Q.all fun x => Qc.elem x) = true) :
    ∀ g ∈ convexHull ℝ (intSet G), ∀ z ∈ convexHull ℝ (intSet Q), P.Sees g z := fun _ hg _ hz =>
  sees_of_convex (convex_convexHull ℝ _) hsub (hull_subset_hull_of_all hG hg)
    (hull_subset_hull_of_all hQ hz)

/-- A guard position on a sub-segment `[M, N]` of a guard segment, given by the values `lo < hi`
of its ends (stated for any point function affine in the value). -/
theorem mem_hull_pair_of_affine (f : ℝ → Point) (hf : ∀ s t r : ℝ, f (s + r * (t - s)) =
      Geometry.lerp (f s) (f t) r) {M N : IPt} {lo hi u : ℝ} (hlh : lo < hi)
    (hM : intPoint M = f lo) (hN : intPoint N = f hi) (h0 : lo ≤ u) (h1 : u ≤ hi) :
    f u ∈ convexHull ℝ (intSet [M, N]) := by
  have hd : 0 < hi - lo := by linarith
  have e : u = lo + (u - lo) / (hi - lo) * (hi - lo) := by field_simp; ring
  rw [e, hf, ← hM, ← hN]
  exact mem_hull_pair (div_nonneg (by linarith) hd.le) ((div_le_one hd).2 (by linarith))

/-! ### Completeness: BSP certificates -/

theorem getD_mem_gen {α : Type} {L : List α} {j : ℕ} {d : α} (h : j < L.length) : L.getD j d ∈ L := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- Leaf certificates of the BSP. -/
inductive CLeaf where
  /-- The cell lies in piece `j`: a Farkas certificate for every edge of the piece. -/
  | inside (j : ℕ) (certs : List (ℕ × List (ℕ × ℕ)))
  /-- Every ray from the cell in direction `d` misses the boundary (separators with Farkas
  certificates). -/
  | ray (d : IPt) (seps : List (HP × ℕ × List (ℕ × ℕ)))
  /-- Every segment from the cell to the anchor `k` misses the boundary. -/
  | link (k : ℕ) (seps : List (HP × ℕ × List (ℕ × ℕ)))

/-- A BSP tree: an inner node splits the cell by `h ≥ 0` / `h ≤ 0`. -/
inductive CBSP where
  /-- A leaf. -/
  | leaf (l : CLeaf)
  /-- A split by the line `h = 0`. -/
  | node (h : HP) (pos neg : CBSP)

/-- Farkas certificates for a list of functionals. -/
def certsB (cs : List HP) : List HP → List (ℕ × List (ℕ × ℕ)) → Bool
  | [], [] => true
  | e :: es, (c, lam) :: rest => implB cs e c lam && certsB cs es rest
  | _, _ => false

theorem certsB_sound {cs : List HP} {z : Point} (hz : ∀ h ∈ cs, 0 ≤ h.val z) :
    ∀ (es : List HP) (L : List (ℕ × List (ℕ × ℕ))), certsB cs es L = true → ∀ e ∈ es, 0 ≤ e.val z
  | [], _, _ => by simp
  | e :: es, (c, lam) :: rest, h => by
    simp only [certsB, Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact implB_sound h.1 hz
    · exact certsB_sound hz es rest h.2 e' he'
  | _ :: _, [], h => by simp [certsB] at h

/-- `h` separates the edge `[a, b]` from the ray in direction `d` (given `h ≥ 0` at the start). -/
def rayOK (h : HP) (d a b : IPt) : Bool :=
  inonpos (ivalHP h a) && inonpos (ivalHP h b) &&
    (ipos (h.1 * d.1 + h.2.1 * d.2) ||
      (ineg (ivalHP h a) && ineg (ivalHP h b) && inonneg (h.1 * d.1 + h.2.1 * d.2)))

/-- `h` separates the edge `[a, b]` from the segment to `w` (given `h ≥ 0` at the start). -/
def segOK (h : HP) (w a b : IPt) : Bool :=
  inonpos (ivalHP h a) && inonpos (ivalHP h b) &&
    (ipos (ivalHP h w) || (ineg (ivalHP h a) && ineg (ivalHP h b) && inonneg (ivalHP h w)))

/-- An anchor `(w, d, seps)`: the ray from `w` in direction `d` misses every edge of `Kl`. -/
def anchorB (Kl : List IPt) (an : IPt × IPt × List HP) : Bool :=
  !(an.2.1.1 == 0 && an.2.1.2 == 0) && (cycEdges Kl).all fun e => an.2.2.any fun h =>
    inonpos (ivalHP h e.1) && inonpos (ivalHP h e.2) && ipos (ivalHP h an.1) &&
      inonneg (h.1 * an.2.1.1 + h.2.1 * an.2.1.2)

/-- The leaf check. -/
def leafB (Kl : List IPt) (pieces : List (List IPt)) (anchors : List (IPt × IPt × List HP))
    (cs : List HP) : CLeaf → Bool
  | .inside j certs => Nat.blt j pieces.length && certsB cs (edgesHP (pieces.getD j [])) certs
  | .ray d seps => !(d.1 == 0 && d.2 == 0) && (seps.all fun s => implB cs s.1 s.2.1 s.2.2) &&
      (cycEdges Kl).all fun e => seps.any fun s => rayOK s.1 d e.1 e.2
  | .link k seps => Nat.blt k anchors.length && (seps.all fun s => implB cs s.1 s.2.1 s.2.2) &&
      (cycEdges Kl).all fun e => seps.any fun s => segOK s.1 (anchors.getD k ((0, 0), (0, 0), [])).1 e.1 e.2

/-- The BSP check (path constraints `cs`). -/
def bspB (Kl : List IPt) (pieces : List (List IPt)) (anchors : List (IPt × IPt × List HP)) :
    List HP → CBSP → Bool
  | cs, .leaf l => leafB Kl pieces anchors cs l
  | cs, .node h t u => bspB Kl pieces anchors (h :: cs) t && bspB Kl pieces anchors (negHP h :: cs) u

/-- The point `a + (n / N) (b − a)` is on the nonnegative side of every edge of `Q`. -/
def inHullT (Q : List IPt) (a b : IPt) (N n : ℕ) : Bool :=
  (edgesHP Q).all fun g => inonneg (((N : ℤ) - n) * ivalHP g a + (n : ℤ) * ivalHP g b)

/-- The parameter interval `[lo/N, 1]` of the segment `[a, b]` is covered by the parts
`(hi, j)`: piece `j` contains the sub-segment `[lo/N, hi/N]`, then the next part starts at `hi`. -/
def partsB (pieces : List (List IPt)) (a b : IPt) (N : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | lo, [] => lo == N
  | lo, (hi, j) :: rest => Nat.blt j pieces.length && Nat.ble lo hi && Nat.ble hi N &&
      inHullT (pieces.getD j []) a b N lo && inHullT (pieces.getD j []) a b N hi &&
      partsB pieces a b N hi rest

/-- Every edge of the closed polygon `Kl` is covered by pieces (certificate: `(N, parts)` per
edge). -/
def bdCoverB (Kl : List IPt) (pieces : List (List IPt)) (cert : List (ℕ × List (ℕ × ℕ))) : Bool :=
  ((cycEdges Kl).length == cert.length) &&
    ((cycEdges Kl).zip cert).all fun ec => Nat.blt 0 ec.2.1 && partsB pieces ec.1.1 ec.1.2 ec.2.1 0 ec.2.2

/-- The union of the pieces. -/
def unionHull (pieces : List (List IPt)) : Set Point :=
  {z | ∃ Q ∈ pieces, z ∈ convexHull ℝ (intSet Q)}

section Complete

variable {Kl : List IPt}

/-- The boundary of the integer polygon `Kl` is the union of the segments of `cycEdges Kl`. -/
theorem mem_boundary_intPoly {z : Point} (hz : z ∈ (Polygon.mk (Kl.map intPoint)).boundary) :
    ∃ e ∈ cycEdges Kl, z ∈ ArtGallery.segment (intPoint e.1) (intPoint e.2) := by
  obtain ⟨i, hi, hz⟩ := hz
  rw [n_map_intPoint] at hi
  rw [edge_map_intPoint] at hz
  exact ⟨_, mem_cycEdges ((0 : ℤ), (0 : ℤ)) Kl hi, hz⟩

/-- The elements of `cycGo`. -/
theorem mem_cycGo {α : Type} (d a₀ : α) :
    ∀ (l : List α) (e : α × α), e ∈ cycGo a₀ l →
      ∃ i < l.length, e = (l.getD i d, (l ++ [a₀]).getD (i + 1) d)
  | [], e, h => by simp [cycGo] at h
  | [a], e, h => by
    simp only [cycGo, List.mem_singleton] at h
    exact ⟨0, by simp, by simp [h]⟩
  | a :: b :: rest, e, h => by
    simp only [cycGo, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := mem_cycGo d a₀ (b :: rest) e (by simpa [cycGo] using h)
      exact ⟨i + 1, by simp at hi ⊢; omega, by simp⟩

theorem boundary_of_mem_edge {e : IPt × IPt} (he : e ∈ cycEdges Kl) {z : Point}
    (hz : z ∈ ArtGallery.segment (intPoint e.1) (intPoint e.2)) :
    z ∈ (Polygon.mk (Kl.map intPoint)).boundary := by
  match Kl, he with
  | a :: rest, he =>
    obtain ⟨i, hi, rfl⟩ := mem_cycGo ((0 : ℤ), (0 : ℤ)) a (a :: rest) e he
    have e' : ((a :: rest) ++ [a]).getD (i + 1) (0, 0) =
        (a :: rest).getD ((i + 1) % (a :: rest).length) (0, 0) := by
      by_cases h1 : i + 1 < (a :: rest).length
      · rw [getD_append_left' h1, Nat.mod_eq_of_lt h1]
      · have : i + 1 = (a :: rest).length := by omega
        rw [getD_append_right' (by omega), this, Nat.mod_self, Nat.sub_self]; rfl
    refine ⟨i, by rw [n_map_intPoint]; exact hi, ?_⟩
    rw [edge_map_intPoint, ← e']
    exact hz

/-- **Soundness of the edge parts.** -/
theorem partsB_sound {pieces : List (List IPt)} (hfan : (pieces.all fanB) = true) {a b : IPt}
    {N : ℕ} (hN : 0 < N) :
    ∀ (L : List (ℕ × ℕ)) (lo : ℕ), partsB pieces a b N lo L = true → ∀ τ : ℝ, (lo : ℝ) / N ≤ τ →
      (L = [] → (lo : ℝ) / N < τ) → τ ≤ 1 →
        Geometry.lerp (intPoint a) (intPoint b) τ ∈ unionHull pieces
  | [], lo, h, τ, _, hs, h1 => by
    simp only [partsB, beq_iff_eq] at h
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have := hs rfl
    rw [h, div_self hNr.ne'] at this
    exact absurd h1 (not_le.2 this)
  | (hi, j) :: rest, lo, h, τ, h0, _, h1 => by
    simp only [partsB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨hj, hlh⟩, hhN⟩, hlo⟩, hhi⟩, hrest⟩ := h
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases hτ : τ ≤ (hi : ℝ) / N
    · simp only [List.all_eq_true] at hfan
      have hjm : pieces.getD j [] ∈ pieces := getD_mem_gen hj
      refine ⟨_, hjm, mem_hull_of_edges (hfan _ hjm) fun g hg => ?_⟩
      simp only [inHullT, List.all_eq_true, inonneg_iff] at hlo hhi
      have e1 := hlo g hg
      have e2 := hhi g hg
      rw [Irrational.HP.val_lerp, val_intPoint_HP, val_intPoint_HP]
      set A := (ivalHP g a : ℝ)
      set B := (ivalHP g b : ℝ)
      have f1 : 0 ≤ ((N : ℝ) - lo) * A + lo * B := by
        have : (0 : ℝ) ≤ (((N : ℤ) - (lo : ℤ)) * ivalHP g a + (lo : ℤ) * ivalHP g b : ℤ) := by
          exact_mod_cast e1
        push_cast at this; linarith
      have f2 : 0 ≤ ((N : ℝ) - hi) * A + hi * B := by
        have : (0 : ℝ) ≤ (((N : ℤ) - (hi : ℤ)) * ivalHP g a + (hi : ℤ) * ivalHP g b : ℤ) := by
          exact_mod_cast e2
        push_cast at this; linarith
      have hτN0 : (lo : ℝ) ≤ τ * N := by rwa [div_le_iff₀ hNr] at h0
      have hτN1 : τ * N ≤ (hi : ℝ) := by rwa [le_div_iff₀ hNr] at hτ
      have key : (N : ℝ) * ((1 - τ) * A + τ * B) = (N - τ * N) * A + τ * N * B := by ring
      have hlohi : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
      rcases eq_or_lt_of_le hlohi with heq | hlt
      · have hτe : τ * N = lo := le_antisymm (heq ▸ hτN1) hτN0
        have : 0 ≤ (N : ℝ) * ((1 - τ) * A + τ * B) := by
          rw [key, hτe]; linarith
        exact (mul_nonneg_iff_of_pos_left hNr).1 this
      · set s := (τ * N - lo) / (hi - lo) with hs
        have hd : (0 : ℝ) < hi - lo := by linarith
        have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
        have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
        have hsd : s * (hi - lo) = τ * N - lo := div_mul_cancel₀ _ hd.ne'
        have hcomb : (N - τ * N) * A + τ * N * B =
            (1 - s) * (((N : ℝ) - lo) * A + lo * B) + s * (((N : ℝ) - hi) * A + hi * B) := by
          have : τ * N = lo + s * (hi - lo) := by linarith
          rw [this]; ring
        have : 0 ≤ (N : ℝ) * ((1 - τ) * A + τ * B) := by
          rw [key, hcomb]
          have := mul_nonneg (sub_nonneg.2 hs1) f1
          have := mul_nonneg hs0 f2
          linarith
        exact (mul_nonneg_iff_of_pos_left hNr).1 this
    · push Not at hτ
      exact partsB_sound hfan hN rest hi hrest τ hτ.le (fun _ => hτ) h1

/-- A point on the nonnegative side of `h` with `rayOK` is not on the edge for `t > 0` along the
ray, nor at `t = 0` unless it is on the edge itself. -/
theorem ray_misses {h : HP} {d a b : IPt} (hok : rayOK h d a b = true) {z : Point}
    (hz : 0 ≤ h.val z) (hz' : z ∉ ArtGallery.segment (intPoint a) (intPoint b)) {s : ℝ}
    (hs : 0 ≤ s) :
    z + s • intPoint d ∉ ArtGallery.segment (intPoint a) (intPoint b) := by
  simp only [rayOK, Bool.and_eq_true, Bool.or_eq_true, inonpos_iff, ipos_iff, ineg_iff,
    inonneg_iff] at hok
  obtain ⟨⟨ha, hb⟩, hd⟩ := hok
  intro hm
  have hval : h.val (z + s • intPoint d) = h.val z + s * ((h.1 * d.1 + h.2.1 * d.2 : ℤ) : ℝ) := by
    simp only [Irrational.HP.val, intPoint, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    push_cast; ring
  have hle := nonpos_of_mem_segment_HP (g := h) (by rw [val_intPoint_HP]; exact_mod_cast ha)
    (by rw [val_intPoint_HP]; exact_mod_cast hb) hm
  rcases hd with hd | ⟨⟨ha', hb'⟩, hd⟩
  · rcases eq_or_lt_of_le hs with rfl | hs'
    · apply hz'; simpa using hm
    · have : (0 : ℝ) < ((h.1 * d.1 + h.2.1 * d.2 : ℤ) : ℝ) := by exact_mod_cast hd
      have := mul_pos hs' this
      linarith
  · have hlt : h.val (z + s • intPoint d) < 0 := by
      obtain ⟨t, h0, h1, he⟩ := Geometry.mem_segment_iff_lerp.1 hm
      rw [he, Irrational.HP.val_lerp, val_intPoint_HP, val_intPoint_HP]
      have ha2 : (ivalHP h a : ℝ) < 0 := by exact_mod_cast ha'
      have hb2 : (ivalHP h b : ℝ) < 0 := by exact_mod_cast hb'
      nlinarith [mul_le_mul_of_nonneg_left (le_max_left (ivalHP h a : ℝ) (ivalHP h b))
        (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left (le_max_right (ivalHP h a : ℝ) (ivalHP h b)) h0,
        max_lt ha2 hb2]
    have : (0 : ℝ) ≤ ((h.1 * d.1 + h.2.1 * d.2 : ℤ) : ℝ) := by exact_mod_cast hd
    have := mul_nonneg hs this
    linarith

/-- The same for segments to an anchor `w`. -/
theorem seg_misses {h : HP} {w a b : IPt} (hok : segOK h w a b = true) {z : Point}
    (hz : 0 ≤ h.val z) (hz' : z ∉ ArtGallery.segment (intPoint a) (intPoint b)) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Geometry.lerp z (intPoint w) s ∉ ArtGallery.segment (intPoint a) (intPoint b) := by
  simp only [segOK, Bool.and_eq_true, Bool.or_eq_true, inonpos_iff, ipos_iff, ineg_iff,
    inonneg_iff] at hok
  obtain ⟨⟨ha, hb⟩, hd⟩ := hok
  intro hm
  have hval : h.val (Geometry.lerp z (intPoint w) s) = (1 - s) * h.val z + s * (ivalHP h w : ℝ) := by
    rw [Irrational.HP.val_lerp, val_intPoint_HP]
  have hle := nonpos_of_mem_segment_HP (g := h) (by rw [val_intPoint_HP]; exact_mod_cast ha)
    (by rw [val_intPoint_HP]; exact_mod_cast hb) hm
  rcases hd with hd | ⟨⟨ha', hb'⟩, hd⟩
  · rcases eq_or_lt_of_le hs0 with rfl | hs'
    · apply hz'; simpa [Geometry.lerp] using hm
    · have : (0 : ℝ) < (ivalHP h w : ℝ) := by exact_mod_cast hd
      have h1 := mul_pos hs' this
      have h2 : 0 ≤ (1 - s) * h.val z := mul_nonneg (by linarith) hz
      linarith
  · have hlt : h.val (Geometry.lerp z (intPoint w) s) < 0 := by
      obtain ⟨t, h0, h1, he⟩ := Geometry.mem_segment_iff_lerp.1 hm
      rw [he, Irrational.HP.val_lerp, val_intPoint_HP, val_intPoint_HP]
      have ha2 : (ivalHP h a : ℝ) < 0 := by exact_mod_cast ha'
      have hb2 : (ivalHP h b : ℝ) < 0 := by exact_mod_cast hb'
      nlinarith [mul_le_mul_of_nonneg_left (le_max_left (ivalHP h a : ℝ) (ivalHP h b))
        (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left (le_max_right (ivalHP h a : ℝ) (ivalHP h b)) h0,
        max_lt ha2 hb2]
    have : (0 : ℝ) ≤ (ivalHP h w : ℝ) := by exact_mod_cast hd
    have h1 := mul_nonneg hs0 this
    have h2 : 0 ≤ (1 - s) * h.val z := mul_nonneg (by linarith) hz
    linarith

/-- An anchor is not in the filled region (its ray misses the boundary). -/
theorem anchor_not_filled {an : IPt × IPt × List HP} (h : anchorB Kl an = true) :
    intPoint an.1 ∉ (Polygon.mk (Kl.map intPoint)).filled := by
  simp only [anchorB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
    inonpos_iff, ipos_iff, inonneg_iff] at h
  obtain ⟨hd0, hall⟩ := h
  set K := Polygon.mk (Kl.map intPoint)
  have hd : intPoint an.2.1 ≠ 0 := by
    intro h0
    have h1 : (an.2.1.1 : ℝ) = 0 := congrArg Prod.fst h0
    have h2 : (an.2.1.2 : ℝ) = 0 := congrArg Prod.snd h0
    have : an.2.1.1 = 0 ∧ an.2.1.2 = 0 := ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    simp [this] at hd0
  have hray : Jordan.ray (intPoint an.1) (intPoint an.2.1) ⊆ K.boundaryᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hb
    obtain ⟨e, he, hm⟩ := mem_boundary_intPoly hb
    obtain ⟨g, -, ⟨⟨⟨ha, hb'⟩, hw⟩, hgd⟩⟩ := hall e he
    have hle := nonpos_of_mem_segment_HP (g := g) (by rw [val_intPoint_HP]; exact_mod_cast ha)
      (by rw [val_intPoint_HP]; exact_mod_cast hb') hm
    have hval : g.val (intPoint an.1 + s • intPoint an.2.1) =
        (ivalHP g an.1 : ℝ) + s * ((g.1 * an.2.1.1 + g.2.1 * an.2.1.2 : ℤ) : ℝ) := by
      rw [← val_intPoint_HP]
      simp only [Irrational.HP.val, intPoint, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      push_cast; ring
    have h1 : (0 : ℝ) < (ivalHP g an.1 : ℝ) := by exact_mod_cast hw
    have h2 : (0 : ℝ) ≤ ((g.1 * an.2.1.1 + g.2.1 * an.2.1.2 : ℤ) : ℝ) := by exact_mod_cast hgd
    have := mul_nonneg (mem_Ici.1 hs) h2
    linarith
  rintro (hb | hb)
  · exact hray (Jordan.mem_ray_self _ _) hb
  · exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray K hd hray hb

/-- **Soundness of the BSP certificate.** -/
theorem bspB_sound {pieces : List (List IPt)} {anchors : List (IPt × IPt × List HP)}
    (hfan : (pieces.all fanB) = true) (hanc : (anchors.all (anchorB Kl)) = true) :
    ∀ (t : CBSP) (cs : List HP), bspB Kl pieces anchors cs t = true → ∀ z : Point,
      (∀ c ∈ cs, 0 ≤ c.val z) →
        z ∈ unionHull pieces ∨ (z ∉ (Polygon.mk (Kl.map intPoint)).boundary →
          z ∉ (Polygon.mk (Kl.map intPoint)).filled)
  | .node h t u, cs, hb, z, hz => by
    simp only [bspB, Bool.and_eq_true] at hb
    by_cases hh : 0 ≤ h.val z
    · exact bspB_sound hfan hanc t (h :: cs) hb.1 z (fun c hc => by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hh
        · exact hz c hc)
    · exact bspB_sound hfan hanc u (negHP h :: cs) hb.2 z (fun c hc => by
        rcases List.mem_cons.1 hc with rfl | hc
        · rw [negHP_val]; linarith
        · exact hz c hc)
  | .leaf (.inside j certs), cs, hb, z, hz => by
    simp only [bspB, leafB, Bool.and_eq_true, Nat.blt_eq] at hb
    left
    have hjm : pieces.getD j [] ∈ pieces := getD_mem_gen hb.1
    refine ⟨_, hjm, mem_hull_of_edges ?_ (certsB_sound hz _ _ hb.2)⟩
    simp only [List.all_eq_true] at hfan
    exact hfan _ hjm
  | .leaf (.ray d seps), cs, hb, z, hz => by
    simp only [bspB, leafB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      List.any_eq_true] at hb
    obtain ⟨⟨hd0, hseps⟩, hall⟩ := hb
    right
    intro hzb
    set K := Polygon.mk (Kl.map intPoint)
    have hd : intPoint d ≠ 0 := by
      intro h0
      have h1 : (d.1 : ℝ) = 0 := congrArg Prod.fst h0
      have h2 : (d.2 : ℝ) = 0 := congrArg Prod.snd h0
      have : d.1 = 0 ∧ d.2 = 0 := ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      simp [this] at hd0
    have hray : Jordan.ray z (intPoint d) ⊆ K.boundaryᶜ := by
      rintro _ ⟨s, hs, rfl⟩ hb
      obtain ⟨e, he, hm⟩ := mem_boundary_intPoly hb
      obtain ⟨sp, hsp, hok⟩ := hall e he
      have hpos := implB_sound (hseps sp hsp) hz
      exact ray_misses hok hpos (fun hz' => hzb (boundary_of_mem_edge he hz')) (mem_Ici.1 hs) hm
    rintro (hb | hb)
    · exact hzb hb
    · exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray K hd hray hb
  | .leaf (.link k seps), cs, hb, z, hz => by
    simp only [bspB, leafB, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true,
      List.any_eq_true] at hb
    obtain ⟨⟨hk, hseps⟩, hall⟩ := hb
    right
    intro hzb
    set K := Polygon.mk (Kl.map intPoint)
    set an := anchors.getD k ((0, 0), (0, 0), [])
    have hanm : an ∈ anchors := getD_mem_gen hk
    simp only [List.all_eq_true] at hanc
    have hw := anchor_not_filled (hanc an hanm)
    have hseg : ArtGallery.segment z (intPoint an.1) ⊆ K.boundaryᶜ := by
      intro x hx hb
      obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
      obtain ⟨e, he, hm⟩ := mem_boundary_intPoly hb
      obtain ⟨sp, hsp, hok⟩ := hall e he
      have hpos := implB_sound (hseps sp hsp) hz
      exact seg_misses hok hpos (fun hz' => hzb (boundary_of_mem_edge he hz')) hs0 hs1 hm
    have hwb : intPoint an.1 ∉ K.boundary := fun h => hw (Or.inl h)
    have hconn : IsPreconnected (ArtGallery.segment z (intPoint an.1)) := by
      rw [Geometry.segment_eq]; exact (convex_segment _ _).isPreconnected
    have hsub := hconn.subset_connectedComponentIn (Geometry.left_mem_segment _ _) hseg
    have hwmem : intPoint an.1 ∈ connectedComponentIn K.boundaryᶜ z := by
      apply hsub
      rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _
    rintro (hb | hb)
    · exact hzb hb
    · apply hw
      right
      show IsBoundedSet (connectedComponentIn K.boundaryᶜ (intPoint an.1))
      rw [← connectedComponentIn_eq hwmem]; exact hb

/-- **Completeness of the cover**: the filled region of the polygon `Kl` lies in the union of the
pieces. -/
theorem filled_subset_cover {pieces : List (List IPt)} {anchors : List (IPt × IPt × List HP)}
    {box : List HP} {t : CBSP} (hfan : (pieces.all fanB) = true)
    (hanc : (anchors.all (anchorB Kl)) = true) (hbsp : bspB Kl pieces anchors box t = true)
    (hbox : (box.all fun c => nondegHP c && Kl.all fun v => inonneg (ivalHP c v)) = true)
    {bdc : List (ℕ × List (ℕ × ℕ))} (hbd : bdCoverB Kl pieces bdc = true) :
    (Polygon.mk (Kl.map intPoint)).filled ⊆ unionHull pieces := by
  intro z hz
  have hzbox : ∀ c ∈ box, 0 ≤ c.val z := by
    intro c hc
    simp only [List.all_eq_true, Bool.and_eq_true] at hbox
    obtain ⟨h1, h2⟩ := hbox c hc
    exact filled_subset_hp Kl h1 (by simpa [List.all_eq_true] using h2) hz
  rcases bspB_sound hfan hanc t box hbsp z hzbox with h | h
  · exact h
  · by_cases hzb : z ∈ (Polygon.mk (Kl.map intPoint)).boundary
    · obtain ⟨e, he, hm⟩ := mem_boundary_intPoly hzb
      simp only [bdCoverB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hbd
      obtain ⟨hlen, hall⟩ := hbd
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      have hk' : k < bdc.length := by rw [← hlen]; exact hk
      have hz' := hall ((cycEdges Kl)[k], bdc[k]) (by
        rw [List.mem_iff_getElem]
        exact ⟨k, by rw [List.length_zip, hlen, Nat.min_self]; exact hk', by simp⟩)
      simp only [Nat.blt_eq] at hz'
      obtain ⟨hN, hp⟩ := hz'
      obtain ⟨τ, h0, h1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hm
      refine partsB_sound hfan hN _ 0 hp τ (by simpa using h0) (fun hnil => ?_) h1
      rw [hnil] at hp
      simp [partsB] at hp
      omega
    · exact absurd hz (h hzb)

end Complete

end ArtGallery.Sec5.Tmpl

end
