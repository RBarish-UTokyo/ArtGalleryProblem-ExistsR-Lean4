module

public import ArtGallery.FewVars.RTerm
public import ArtGallery.FewVars.Xor
public import ArtGallery.Membership.Inside

/-!
# INSIDE without auxiliary variables

The corners of the polygon are given by a list `C` of rational points (`cr C k` is corner `k`;
`CornersRep x P C` says that they represent the vertices of `P`).  For a rational point `q`:

* `ronSegF q a b`: `q` lies on the segment `[a, b]`;
* `rcrossesF z u v`: the edge `[u, v]` crosses the upward vertical ray from `z`
  (`ArtGallery.Jordan.crosses`);
* `rinsideF C q`: `q` lies on the boundary, or the crossing parity of `q` is odd; the parity is
  the exclusive or `xorList` of the crossing tests, so no parity variables are needed.

Main result: `holds_rinsideF` (for a simple polygon, `rinsideF` holds iff `q ∈ P.filled`).
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry

/-! ## Corners -/

/-- Corner `k` of the corner list `C` (the origin if `k` is out of range). -/
def cr (C : List RPt) (k : ℕ) : RPt := C.getD k r0

/-- The corner list `C` represents the vertices of `P` under `x`. -/
def CornersRep (x : ℕ → ℝ) (P : Polygon) (C : List RPt) : Prop :=
  C.length = P.n ∧ ∀ k < P.n, PRep x (cr C k) (P.vtx k)

/-- All variables of the corners satisfy `S`. -/
def CornersV (S : ℕ → Prop) (C : List RPt) : Prop := ∀ k, PV S (cr C k)

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

theorem CornersRep.vtx (hC : CornersRep x P C) {k : ℕ} (hk : k < P.n) :
    PRep x (cr C k) (P.vtx k) := hC.2 k hk

theorem CornersRep.next (hC : CornersRep x P C) {k : ℕ} (hk : k < P.n) :
    PRep x (cr C ((k + 1) % C.length)) (P.vtx ((k + 1) % P.n)) := by
  rw [hC.1]; exact hC.2 _ (succ_mod_lt hk)

theorem CornersRep.next' (hC : CornersRep x P C) {k : ℕ} (hk : k < P.n) :
    PRep x (cr C ((k + 1) % P.n)) (P.vtx ((k + 1) % P.n)) := hC.2 _ (succ_mod_lt hk)

/-! ## Points on segments -/

/-- `q` lies on the segment `[a, b]`. -/
def ronSegF (q a b : RPt) : Formula := .and (rzeroF (rdetT a b q)) (rnonposF (rdotT a q b q))

variable {q a b : RPt} {q' a' b' : Point}

theorem holds_ronSegF (hq : PRep x q q') (ha : PRep x a a') (hb : PRep x b b') :
    (ronSegF q a b).Holds x ↔ q' ∈ ArtGallery.segment a' b' := by
  rw [mem_segment_iff_det_dot, ronSegF, holds_and, holds_rzeroF (Rep.det ha hb hq),
    holds_rnonposF (Rep.dot ha hq hb hq)]

theorem FVars_ronSegF {S : ℕ → Prop} (hq : PV S q) (ha : PV S a) (hb : PV S b) :
    FVars S (ronSegF q a b) :=
  ⟨FVars_rzeroF (RVars.det ha hb hq), FVars_rnonposF (RVars.dot ha hq hb hq)⟩

/-! ## Crossings -/

/-- The edge `[u, v]` crosses the upward vertical ray from `z`. -/
def rcrossesF (z u v : RPt) : Formula :=
  .or (.and (rleF u.1 z.1) (.and (rltF z.1 v.1)
        (rltF (rmul (rsub z.2 u.2) (rsub v.1 u.1)) (rmul (rsub v.2 u.2) (rsub z.1 u.1)))))
    (.and (rleF v.1 z.1) (.and (rltF z.1 u.1)
        (rltF (rmul (rsub z.2 v.2) (rsub u.1 v.1)) (rmul (rsub u.2 v.2) (rsub z.1 v.1)))))

theorem holds_rcrossesF {z u v : RPt} {z' u' v' : Point} (hz : PRep x z z') (hu : PRep x u u')
    (hv : PRep x v v') : (rcrossesF z u v).Holds x ↔ Jordan.crosses z' u' v' := by
  rw [rcrossesF, Jordan.crosses, holds_or, holds_and, holds_and, holds_and, holds_and,
    holds_rleF hu.1 hz.1, holds_rltF hz.1 hv.1,
    holds_rltF ((hz.2.sub hu.2).mul (hv.1.sub hu.1)) ((hv.2.sub hu.2).mul (hz.1.sub hu.1)),
    holds_rleF hv.1 hz.1, holds_rltF hz.1 hu.1,
    holds_rltF ((hz.2.sub hv.2).mul (hu.1.sub hv.1)) ((hu.2.sub hv.2).mul (hz.1.sub hv.1))]

theorem FVars_rcrossesF {S : ℕ → Prop} {z u v : RPt} (hz : PV S z) (hu : PV S u)
    (hv : PV S v) : FVars S (rcrossesF z u v) :=
  ⟨⟨FVars_rleF hu.1 hz.1, FVars_rltF hz.1 hv.1,
      FVars_rltF ((hz.2.sub hu.2).mul (hv.1.sub hu.1)) ((hv.2.sub hu.2).mul (hz.1.sub hu.1))⟩,
    ⟨FVars_rleF hv.1 hz.1, FVars_rltF hz.1 hu.1,
      FVars_rltF ((hz.2.sub hv.2).mul (hu.1.sub hv.1)) ((hu.2.sub hv.2).mul (hz.1.sub hv.1))⟩⟩

/-! ## INSIDE -/

/-- `q` lies on the boundary of the polygon with corners `C`. -/
def rboundaryF (C : List RPt) (q : RPt) : Formula :=
  bigOr ((List.range C.length).map fun j => ronSegF q (cr C j) (cr C ((j + 1) % C.length)))

/-- The crossing tests of `q` with the edges. -/
def crossList (C : List RPt) (q : RPt) : List Formula :=
  (List.range C.length).map fun e => rcrossesF q (cr C e) (cr C ((e + 1) % C.length))

/-- **INSIDE**: `q` lies on the boundary or has odd crossing parity. -/
def rinsideF (C : List RPt) (q : RPt) : Formula :=
  .or (rboundaryF C q) (xorList (crossList C q))

theorem holds_rboundaryF (hC : CornersRep x P C) (hq : PRep x q q') :
    (rboundaryF C q).Holds x ↔ q' ∈ P.boundary := by
  rw [rboundaryF, holds_bigOr_range, hC.1]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [← hC.1, holds_ronSegF hq (hC.vtx hj) (hC.next hj)] at h
    exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨j, hj, ?_⟩
    rw [← hC.1, holds_ronSegF hq (hC.vtx hj) (hC.next hj)]
    exact h

open Classical in
theorem list_sum_map_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ e ∈ Finset.range n, f e := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem parityOf_crossList (hC : CornersRep x P C) (hq : PRep x q q') :
    parityOf x (crossList C q) = Jordan.crossSum P q' := by
  classical
  rw [parityOf, crossList, List.map_map, list_sum_map_range, Jordan.crossSum, hC.1]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e < P.n := Finset.mem_range.1 he
  simp only [Function.comp_apply]
  rw [← hC.1, holds_rcrossesF hq (hC.vtx he') (hC.next he'), Jordan.crossInd, hC.1]
  by_cases h : Jordan.crosses q' (P.vtx e) (P.vtx ((e + 1) % P.n)) <;> simp [h]

/-- **INSIDE is exact**: for a simple polygon, `rinsideF C q` holds iff `q` lies in the closed
region. -/
theorem holds_rinsideF (hP : P.Simple) (hC : CornersRep x P C) (hq : PRep x q q') :
    (rinsideF C q).Holds x ↔ q' ∈ P.filled := by
  rw [rinsideF, holds_or, holds_rboundaryF hC hq, holds_xorList, parityOf_crossList hC hq,
    ← Jordan.parity_eq_true_iff]
  by_cases hb : q' ∈ P.boundary
  · simp only [hb, true_or, true_iff]
    exact Jordan.boundary_subset_filled P hb
  · simp only [hb, false_or]
    exact (Jordan.mem_filled_iff hP hb).symm

theorem FVars_rinsideF {S : ℕ → Prop} (hC : CornersV S C) (hq : PV S q) :
    FVars S (rinsideF C q) := by
  refine ⟨?_, FVars_xorList ?_⟩
  · rw [rboundaryF, FVars_bigOr]
    intro φ hφ
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hφ
    exact FVars_ronSegF hq (hC _) (hC _)
  · intro φ hφ
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hφ
    exact FVars_rcrossesF hq (hC _) (hC _)

end ArtGallery.FewVars

end
