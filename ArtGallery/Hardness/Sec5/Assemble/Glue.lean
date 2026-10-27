module

public import ArtGallery.Stade.Chains
public import ArtGallery.Hardness.Sec5.Corridor.Chain
public import ArtGallery.Vis.CertCheckerTransfer

/-!
# Section 5: gluing simple chains (generic tools)

Tools for the simplicity proof of the global polygon (08 §4, Lemmas S1/S2), on top of the open
polylines of `ArtGallery/Stade/Chains.lean` (`chainSet`, `ChainSimple`, `ChainSimple.join`,
`simple_of_chain`, the comb lemma `comb_floor`):

* `mem_chainSet_iff`: a point of a chain lies on one of its edges `edgeSeg l i`;
* `chainSimple_of_corridor`: the corridor's notion `Corridor.ChainSimple` implies the Stade one;
* `chainSimple_of_edges`: the indexed characterisation; consequences: a prefix of the vertex list
  of a simple polygon is a simple chain (`chainSimple_of_simple`), simple chains stay simple when
  reversed (`chainSimple_reverse`) and under invertible affine maps (`chainSimple_map`), with
  `chainSet_reverse`, `chainSet_map`;
* half-plane bounds: `chainSet_subset_halfplane` (all vertices in a half-plane), `PairsIn` /
  `chainSet_subset_union` (every edge in one of two convex sets), and `chainSet_lt_or_ends`
  (inner vertices strictly inside a half-plane: only the two end points can reach its boundary).
-/

@[expose] public section

namespace ArtGallery.Sec5.Glue

open ArtGallery Set
open ArtGallery.Stade.Chain

/-! ### Points of a chain -/

theorem mem_chainSet_iff : ∀ {l : List Point} {x : Point},
    x ∈ chainSet l ↔ ∃ i, i + 1 < l.length ∧ x ∈ edgeSeg l i
  | [], x => by simp
  | [a], x => by simp
  | a :: b :: l, x => by
    rw [chainSet_cons_cons, mem_union, mem_chainSet_iff]
    constructor
    · rintro (h | ⟨i, hi, hx⟩)
      · exact ⟨0, by simp, by rwa [edgeSeg_cons_cons_zero]⟩
      · exact ⟨i + 1, by simp at hi ⊢; omega, by rwa [edgeSeg_cons_succ]⟩
    · rintro ⟨i, hi, hx⟩
      cases i with
      | zero => left; rwa [edgeSeg_cons_cons_zero] at hx
      | succ i => right; exact ⟨i, by simp at hi ⊢; omega, by rwa [edgeSeg_cons_succ] at hx⟩

theorem mem_chainSet_iff_edges : ∀ {l : List Point} {x : Point},
    x ∈ chainSet l ↔ ∃ e ∈ Corridor.edgesOf l, x ∈ Corridor.segOf e
  | [], x => by simp
  | [a], x => by simp
  | a :: b :: l, x => by
    rw [chainSet_cons_cons, mem_union, mem_chainSet_iff_edges, Corridor.edgesOf_cons_cons]
    simp [Corridor.segOf]

/-- The corridor's simple polylines are simple chains. -/
theorem chainSimple_of_corridor : ∀ {l : List Point}, Corridor.ChainSimple l → ChainSimple l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨fun hab => h1 (hab ▸ List.mem_cons_self), ?_, chainSimple_of_corridor h4⟩
    rintro x ⟨hx1, hx2⟩
    cases l with
    | nil => simp at hx2
    | cons c l =>
      rw [chainSet_cons_cons] at hx2
      rcases hx2 with hx2 | hx2
      · exact h2 c (by simp) ⟨hx1, hx2⟩
      · obtain ⟨e, he, hxe⟩ := mem_chainSet_iff_edges.1 hx2
        exact absurd hxe (Set.disjoint_left.1 (h3 e he) hx1)

/-! ### The indexed characterisation -/

/-- **Indexed characterisation** of simple chains. -/
theorem chainSimple_of_edges : ∀ {l : List Point},
    (∀ i, i + 1 < l.length → l.getD i (0, 0) ≠ l.getD (i + 1) (0, 0)) →
    (∀ i j, i < j → j + 1 < l.length →
      edgeSeg l i ∩ edgeSeg l j ⊆ (if j = i + 1 then {l.getD j (0, 0)} else ∅)) →
    ChainSimple l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: l, hne, h => by
    refine ⟨hne 0 (by simp), ?_, chainSimple_of_edges (fun i hi => ?_) (fun i j hij hj => ?_)⟩
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨j, hj, hxj⟩ := mem_chainSet_iff.1 hx2
      have := h 0 (j + 1) (by omega) (by simp at hj ⊢; omega)
        ⟨by rwa [edgeSeg_cons_cons_zero], by rwa [edgeSeg_cons_succ]⟩
      split_ifs at this with hj0
      · have hj0' : j = 0 := by omega
        subst hj0'
        simpa using this
      · exact this.elim
    · have := hne (i + 1) (by simp at hi ⊢; omega)
      simpa using this
    · have := h (i + 1) (j + 1) (by omega) (by simp at hj ⊢; omega)
      simp only [edgeSeg_cons_succ, List.getD_cons_succ] at this
      by_cases hji : j = i + 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at this
        rw [ite_eq_left_of_eq_true _ _ (eq_true hji)]
        exact this
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at this
        rw [ite_eq_right_of_eq_false _ _ (eq_false hji)]
        exact this

/-- The indexed conditions of a simple chain. -/
theorem chainSimple_edges {l : List Point} (h : ChainSimple l) {i j : ℕ} (hij : i < j)
    (hj : j + 1 < l.length) :
    edgeSeg l i ∩ edgeSeg l j ⊆ (if j = i + 1 then {l.getD j (0, 0)} else ∅) := by
  obtain ⟨h1, h2⟩ := h.edge_inter hij hj
  split_ifs with hji
  · subst hji; exact h1 rfl
  · rw [h2 (by omega)]

theorem getD_append_left' {L M : List Point} {i : ℕ} (hi : i < L.length) :
    (L ++ M).getD i (0, 0) = L.getD i (0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- **A prefix of the vertex list of a simple polygon is a simple chain.** -/
theorem chainSimple_of_simple {L M : List Point} (h : (Polygon.mk (L ++ M)).Simple) :
    ChainSimple L := by
  obtain ⟨h3, hinj, hedge⟩ := h
  set P := Polygon.mk (L ++ M) with hP
  have hn : P.n = L.length + M.length := by simp [P, Polygon.n]
  have hv : ∀ i < L.length, P.vtx i = L.getD i (0, 0) := fun i hi => getD_append_left' hi
  have he : ∀ i, i + 1 < L.length → P.edge i = edgeSeg L i := by
    intro i hi
    simp only [Polygon.edge, edgeSeg]
    rw [Nat.mod_eq_of_lt (by omega), hv i (by omega), hv (i + 1) hi]
  apply chainSimple_of_edges
  · intro i hi heq
    have := hinj i (i + 1) (by omega) (by omega) (by rw [hv i (by omega), hv (i + 1) hi]; exact heq)
    omega
  · intro i j hij hj x hx
    rw [← he i (by omega), ← he j hj, hedge i j (by omega) (by omega) (by omega)] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [Nat.mod_eq_of_lt (by omega)] at h1 h2
    have key : ∀ a b, a < P.n → b < P.n → x = P.vtx a → x = P.vtx b → a = b :=
      fun a b ha hb e1 e2 => hinj a b ha hb (e1 ▸ e2)
    split_ifs with hji
    · subst hji
      rw [mem_singleton_iff, ← hv (i + 1) (by omega)]
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact absurd (key _ _ (by omega) (by omega) h1 h2) (by omega)
        · exact absurd (key _ _ (by omega) (by omega) h1 h2) (by omega)
      · exact h1
    · exfalso
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        · have := key _ _ (by omega) (by omega) h1 h2; omega

/-! ### Reversal -/

theorem getD_reverse' {l : List Point} {i : ℕ} (hi : i < l.length) :
    l.reverse.getD i (0, 0) = l.getD (l.length - 1 - i) (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), List.getD_eq_getElem?_getD]

theorem edgeSeg_reverse {l : List Point} {i : ℕ} (hi : i + 1 < l.length) :
    edgeSeg l.reverse i = edgeSeg l (l.length - 2 - i) := by
  have hi' : i + 1 < l.length := by simpa using hi
  simp only [edgeSeg]
  rw [getD_reverse' (by omega), getD_reverse' hi',
    show l.length - 1 - (i + 1) = l.length - 2 - i by omega,
    show l.length - 1 - i = l.length - 2 - i + 1 by omega, Geometry.segment_comm]

theorem chainSet_reverse (l : List Point) : chainSet l.reverse = chainSet l := by
  ext x
  rw [mem_chainSet_iff, mem_chainSet_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [List.length_reverse] at hi
    rw [edgeSeg_reverse (by simpa using hi)] at hx
    exact ⟨l.length - 2 - i, by omega, hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨l.length - 2 - i, by simp only [List.length_reverse]; omega, ?_⟩
    rw [edgeSeg_reverse (by omega)]
    convert hx using 2
    omega

/-- **Reversed simple chains are simple.** -/
theorem chainSimple_reverse {l : List Point} (h : ChainSimple l) : ChainSimple l.reverse := by
  have hnd := List.nodup_reverse.2 h.nodup
  apply chainSimple_of_edges
  · intro i hi heq
    have := getD_inj_of_nodup hnd (by omega) hi heq
    omega
  · intro i j hij hj
    rw [List.length_reverse] at hj
    rw [edgeSeg_reverse (by omega), edgeSeg_reverse (by omega), inter_comm]
    have := chainSimple_edges h (i := l.length - 2 - j) (j := l.length - 2 - i) (by omega)
      (by omega)
    by_cases hji : j = i + 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_true hji), getD_reverse' (by omega)]
      convert this using 3
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at this
      rw [ite_eq_right_of_eq_false _ _ (eq_false hji)]
      exact this

/-! ### Invertible affine maps -/

theorem chainSet_map (A : Point ≃ᵃ[ℝ] Point) :
    ∀ l : List Point, chainSet (l.map A) = A '' chainSet l
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    rw [List.map_cons, List.map_cons, chainSet_cons_cons, ← List.map_cons, chainSet_map A (b :: l),
      chainSet_cons_cons, image_union, Hardening.Invariance.image_segment']

/-- **Simple chains stay simple under invertible affine maps.** -/
theorem chainSimple_map (A : Point ≃ᵃ[ℝ] Point) :
    ∀ {l : List Point}, ChainSimple l → ChainSimple (l.map A)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [List.map_cons, List.map_cons]
    refine ⟨fun e => h1 (A.injective e), ?_, ?_⟩
    · rw [← List.map_cons, chainSet_map A (b :: l), ← Hardening.Invariance.image_segment',
        ← image_inter A.injective]
      rintro _ ⟨x, hx, rfl⟩
      rw [h2 hx]; rfl
    · rw [← List.map_cons]; exact chainSimple_map A h3

theorem fstPt_map (f : Point → Point) {l : List Point} (hl : l ≠ []) :
    fstPt (l.map f) = f (fstPt l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => rfl

theorem lstPt_map (f : Point → Point) {l : List Point} (hl : l ≠ []) :
    lstPt (l.map f) = f (lstPt l) := by
  unfold lstPt
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map,
    List.getLast?_eq_some_getLast hl]
  rfl

theorem fstPt_reverse {l : List Point} : fstPt l.reverse = lstPt l := by
  unfold fstPt lstPt
  rw [List.headD_eq_head?_getD, List.head?_reverse, List.getLastD_eq_getLast?]

theorem lstPt_reverse {l : List Point} : lstPt l.reverse = fstPt l := by
  have := fstPt_reverse (l := l.reverse)
  rw [List.reverse_reverse] at this
  exact this.symm

theorem fstPt_cons (a : Point) (l : List Point) : fstPt (a :: l) = a := rfl

theorem lstPt_append_single (l : List Point) (z : Point) : lstPt (l ++ [z]) = z := by
  unfold lstPt
  rw [List.getLastD_eq_getLast?]; simp

/-! ### Half-planes -/

/-- The affine functional `p ↦ α p.1 + β p.2` along a segment. -/
theorem lin_lerp (α β : ℝ) (a b : Point) (t : ℝ) :
    α * (a.1 + t * (b.1 - a.1)) + β * (a.2 + t * (b.2 - a.2)) =
      (1 - t) * (α * a.1 + β * a.2) + t * (α * b.1 + β * b.2) := by ring

theorem convex_halfplane (α β c : ℝ) : Convex ℝ {p : Point | α * p.1 + β * p.2 ≤ c} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  have e : α * (s * x.1 + t * y.1) + β * (s * x.2 + t * y.2) =
      s * (α * x.1 + β * x.2) + t * (α * y.1 + β * y.2) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hx hs
  have := mul_le_mul_of_nonneg_left hy ht
  have : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
  linarith

/-- A chain whose vertices lie in a half-plane lies in it. -/
theorem chainSet_subset_halfplane {α β c : ℝ} {l : List Point}
    (h : ∀ p ∈ l, α * p.1 + β * p.2 ≤ c) : ∀ p ∈ chainSet l, α * p.1 + β * p.2 ≤ c :=
  fun _ hp => chainSet_subset_of_convex (convex_halfplane α β c) h hp

/-- Every edge of the chain lies in `K₁` or in `K₂`. -/
def PairsIn (K₁ K₂ : Set Point) : List Point → Prop
  | a :: b :: l => ((a ∈ K₁ ∧ b ∈ K₁) ∨ (a ∈ K₂ ∧ b ∈ K₂)) ∧ PairsIn K₁ K₂ (b :: l)
  | _ => True

theorem chainSet_subset_union {K₁ K₂ : Set Point} (h₁ : Convex ℝ K₁) (h₂ : Convex ℝ K₂) :
    ∀ {l : List Point}, PairsIn K₁ K₂ l → chainSet l ⊆ K₁ ∪ K₂
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [chainSet_cons_cons]
    refine union_subset ?_ (chainSet_subset_union h₁ h₂ h.2)
    rcases h.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact (Geometry.segment_subset_of_convex h₁ ha hb).trans subset_union_left
    · exact (Geometry.segment_subset_of_convex h₂ ha hb).trans subset_union_right

/-- On a segment from a point strictly inside a half-plane to a point of the closed half-plane,
only the end point can lie on the boundary line. -/
theorem seg_lt_or_right {α β c : ℝ} {a b p : Point} (ha : α * a.1 + β * a.2 < c)
    (hb : α * b.1 + β * b.2 ≤ c) (hp : p ∈ ArtGallery.segment a b) :
    α * p.1 + β * p.2 < c ∨ p = b := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  rw [lin_lerp]
  rcases lt_or_eq_of_le ht1 with ht | rfl
  · left
    have h1 : 0 < 1 - t := by linarith
    nlinarith [mul_lt_mul_of_pos_left ha h1, mul_le_mul_of_nonneg_left hb ht0]
  · right; ext <;> simp

theorem seg_lt_or_left {α β c : ℝ} {a b p : Point} (ha : α * a.1 + β * a.2 ≤ c)
    (hb : α * b.1 + β * b.2 < c) (hp : p ∈ ArtGallery.segment a b) :
    α * p.1 + β * p.2 < c ∨ p = a := by
  rw [Geometry.segment_comm] at hp
  exact seg_lt_or_right hb ha hp

/-- Inner vertices strictly inside: points of `m ++ [z]` other than `z` are strictly inside. -/
theorem chainSet_lt_or_last {α β c : ℝ} {z : Point} (hz : α * z.1 + β * z.2 ≤ c) :
    ∀ {m : List Point}, (∀ v ∈ m, α * v.1 + β * v.2 < c) →
      ∀ p ∈ chainSet (m ++ [z]), α * p.1 + β * p.2 < c ∨ p = z
  | [], _, p, hp => by simp at hp
  | [b], hm, p, hp => by
    simp only [List.cons_append, List.nil_append, chainSet_cons_cons, chainSet_single,
      union_empty] at hp
    exact seg_lt_or_right (hm b (by simp)) hz hp
  | b :: b' :: m, hm, p, hp => by
    rw [List.cons_append, List.cons_append, chainSet_cons_cons, ← List.cons_append] at hp
    rcases hp with hp | hp
    · left
      rcases seg_lt_or_right (hm b (by simp)) (hm b' (by simp)).le hp with h | rfl
      · exact h
      · exact hm _ (by simp)
    · exact chainSet_lt_or_last hz (fun v hv => hm v (List.mem_cons_of_mem _ hv)) p hp

/-- **Only the end points reach the boundary line.** If the inner vertices of `a, m…, z`
(`m ≠ []`) lie strictly inside a half-plane and the end points in its closure, every point of
the chain other than `a`, `z` is strictly inside. -/
theorem chainSet_lt_or_ends {α β c : ℝ} {a z : Point} {m : List Point} (hm0 : m ≠ [])
    (ha : α * a.1 + β * a.2 ≤ c) (hz : α * z.1 + β * z.2 ≤ c)
    (hm : ∀ v ∈ m, α * v.1 + β * v.2 < c) :
    ∀ p ∈ chainSet (a :: m ++ [z]), α * p.1 + β * p.2 < c ∨ p = a ∨ p = z := by
  intro p hp
  obtain ⟨b, m', rfl⟩ := List.exists_cons_of_ne_nil hm0
  rw [List.cons_append, List.cons_append, chainSet_cons_cons, ← List.cons_append] at hp
  rcases hp with hp | hp
  · rcases seg_lt_or_left ha (hm b (by simp)) hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases chainSet_lt_or_last hz hm p hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- Vertices of a chain with at least two vertices are points of the chain. -/
theorem mem_chainSet_of_mem' {l : List Point} {p : Point} (hp : p ∈ l) (hl : 2 ≤ l.length) :
    p ∈ chainSet l := mem_chainSet_of_mem hp hl

/-- The boundary of the polygon with vertex list `V`: the chain `V` and the closing edge. -/
theorem boundary_subset_chainSet {V : List Point} (hV : 2 ≤ V.length) :
    (Polygon.mk V).boundary ⊆ chainSet V ∪ ArtGallery.segment (lstPt V) (fstPt V) := by
  rintro p ⟨i, hi, hp⟩
  have hn : (Polygon.mk V).n = V.length := rfl
  by_cases h : i + 1 < V.length
  · left
    rw [mem_chainSet_iff]
    refine ⟨i, h, ?_⟩
    simp only [Polygon.edge, hn, Nat.mod_eq_of_lt h] at hp
    exact hp
  · right
    have hi' : i = V.length - 1 := by rw [hn] at hi; omega
    simp only [Polygon.edge, hn, show i + 1 = V.length by omega, Nat.mod_self] at hp
    have e1 : (Polygon.mk V).vtx i = lstPt V := by
      obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil (show V ≠ [] by rintro rfl; simp at hV)
      simp only [Polygon.vtx, lstPt, hi']
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [List.getD_eq_getElem?_getD]
    have e2 : (Polygon.mk V).vtx 0 = fstPt V := by
      obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil (show V ≠ [] by rintro rfl; simp at hV)
      rfl
    rw [e1, e2] at hp
    exact hp

end ArtGallery.Sec5.Glue

end
