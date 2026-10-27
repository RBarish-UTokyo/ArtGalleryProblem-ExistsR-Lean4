module

public import ArtGallery.Irrational.Checker

/-!
# Simplicity of polygons assembled from chains

Generic tools for proving that a polygon (in the sense of `ArtGallery.Spec`) is simple when its
boundary is assembled from *open polylines* (chains):

* `chainSet l`: the union of the edges of the open polyline `l`;
* `ChainSimple l`: `l` is a simple open polyline (each edge meets the rest of the polyline
  only in its end point); it implies `l.Nodup` (`ChainSimple.nodup`) and the pairwise edge
  conditions (`ChainSimple.edge_inter`, `ChainSimple.vertex_mem_edge`);
* `ChainSimple.join`: two simple chains sharing exactly their common end point form a simple
  chain;
* `simple_of_chain`: a simple chain closed by an edge meeting it only in the two end points
  is a simple polygon;
* `comb_floor` / `comb_ceiling`: a horizontal line from which finitely many pairwise disjoint
  *features* (simple chains starting and ending on the line, otherwise strictly on one side)
  hang, ordered along the line, is a simple chain;
* `simple_of_combs`: a rectangle `[x_lo, x_hi] × [y_lo, y_hi]` with features hanging below its
  floor and above its ceiling is a simple polygon (proof plan L2.2a).
-/

namespace ArtGallery.Stade.Chain

@[expose] public section

open ArtGallery.Geometry Set

/-! ### Chains -/

/-- The union of the edges of the open polyline `l`. -/
def chainSet : List Point → Set Point
  | a :: b :: l => ArtGallery.segment a b ∪ chainSet (b :: l)
  | _ => ∅

/-- The open polyline `l` is simple: consecutive vertices are distinct and every edge meets the
rest of the polyline only in its end point. -/
def ChainSimple : List Point → Prop
  | a :: b :: l => a ≠ b ∧ ArtGallery.segment a b ∩ chainSet (b :: l) ⊆ {b} ∧ ChainSimple (b :: l)
  | _ => True

@[simp] theorem chainSet_nil : chainSet [] = ∅ := rfl

@[simp] theorem chainSet_single (a : Point) : chainSet [a] = ∅ := rfl

@[simp] theorem chainSet_cons_cons (a b : Point) (l : List Point) :
    chainSet (a :: b :: l) = ArtGallery.segment a b ∪ chainSet (b :: l) := rfl

@[simp] theorem chainSimple_nil : ChainSimple [] := trivial

@[simp] theorem chainSimple_single (a : Point) : ChainSimple [a] := trivial

theorem chainSimple_cons_cons {a b : Point} {l : List Point} :
    ChainSimple (a :: b :: l) ↔
      a ≠ b ∧ ArtGallery.segment a b ∩ chainSet (b :: l) ⊆ {b} ∧ ChainSimple (b :: l) :=
  Iff.rfl

theorem ChainSimple.tail {a : Point} {l : List Point} (h : ChainSimple (a :: l)) :
    ChainSimple l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2.2

/-- The edges of a concatenation at a common vertex. -/
theorem chainSet_append_cons (l₁ : List Point) (p : Point) (l₂ : List Point) :
    chainSet (l₁ ++ p :: l₂) = chainSet (l₁ ++ [p]) ∪ chainSet (p :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have e1 : (a :: b :: l) ++ p :: l₂ = a :: ((b :: l) ++ p :: l₂) := rfl
      have e2 : (a :: b :: l) ++ [p] = a :: ((b :: l) ++ [p]) := rfl
      rw [e1, e2]
      simp only [List.cons_append, chainSet_cons_cons] at ih ⊢
      rw [ih, union_assoc]

/-- Vertices of a chain with at least two vertices lie on the chain. -/
theorem mem_chainSet_of_mem {l : List Point} {p : Point} (hp : p ∈ l) (hl : 2 ≤ l.length) :
    p ∈ chainSet l := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      rw [chainSet_cons_cons]
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inl (left_mem_segment _ _)
      · cases l with
        | nil =>
          simp only [List.mem_singleton] at hp
          subst hp; exact Or.inl (right_mem_segment _ _)
        | cons c l => exact Or.inr (ih hp (by simp))

/-- A chain whose vertices lie in a convex set lies in it. -/
theorem chainSet_subset_of_convex {K : Set Point} (hK : Convex ℝ K) :
    ∀ {l : List Point}, (∀ p ∈ l, p ∈ K) → chainSet l ⊆ K
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [chainSet_cons_cons]
    refine union_subset (segment_subset_of_convex hK (h a (by simp)) (h b (by simp))) ?_
    exact chainSet_subset_of_convex hK (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The first vertex of a simple chain is not on the later edges. -/
theorem ChainSimple.head_not_mem {a b : Point} {l : List Point}
    (h : ChainSimple (a :: b :: l)) : a ∉ chainSet (b :: l) := by
  intro ha
  have := h.2.1 ⟨left_mem_segment a b, ha⟩
  exact h.1 this

/-- A simple chain has no repeated vertex. -/
theorem ChainSimple.nodup : ∀ {l : List Point}, ChainSimple l → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | a :: b :: l, h => by
    refine List.nodup_cons.2 ⟨?_, ChainSimple.nodup h.2.2⟩
    intro ha
    rcases List.mem_cons.1 ha with hab | hl
    · exact h.1 hab
    · exact h.head_not_mem (mem_chainSet_of_mem (List.mem_cons_of_mem _ hl) (by
        cases l with
        | nil => simp at hl
        | cons c l => simp))

/-- **Join.**  Two simple chains sharing the end point `p`, and meeting only there, form a
simple chain. -/
theorem ChainSimple.join {l₁ l₂ : List Point} {p : Point} (h₁ : ChainSimple (l₁ ++ [p]))
    (h₂ : ChainSimple (p :: l₂)) (h : chainSet (l₁ ++ [p]) ∩ chainSet (p :: l₂) ⊆ {p}) :
    ChainSimple (l₁ ++ p :: l₂) := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.cons_append, List.nil_append, chainSet_cons_cons, chainSet_single,
        union_empty] at h h₁ ⊢
      exact ⟨h₁.1, h, h₂⟩
    | cons b l =>
      have e1 : (a :: b :: l) ++ p :: l₂ = a :: b :: (l ++ p :: l₂) := rfl
      have e2 : (a :: b :: l) ++ [p] = a :: b :: (l ++ [p]) := rfl
      rw [e2] at h₁ h
      rw [e1]
      obtain ⟨hab, hseg, hrest⟩ := h₁
      refine ⟨hab, ?_, ?_⟩
      · have e3 : b :: (l ++ p :: l₂) = (b :: l) ++ p :: l₂ := rfl
        rw [e3, chainSet_append_cons]
        rintro x ⟨hx1, hx2 | hx2⟩
        · exact hseg ⟨hx1, hx2⟩
        · have hxp : x = p := h ⟨Or.inl hx1, hx2⟩
          subst hxp
          have : x ∈ chainSet (b :: (l ++ [x])) :=
            mem_chainSet_of_mem (by simp) (by simp)
          exact hseg ⟨hx1, this⟩
      · have h' : chainSet ((b :: l) ++ [p]) ∩ chainSet (p :: l₂) ⊆ {p} := by
          rintro x ⟨hx1, hx2⟩
          exact h ⟨Or.inr hx1, hx2⟩
        exact ih hrest h'

/-! ### Edges by index -/

/-- Edge `i` of the open polyline `l`: from vertex `i` to vertex `i + 1`. -/
def edgeSeg (l : List Point) (i : ℕ) : Set Point :=
  ArtGallery.segment (l.getD i (0, 0)) (l.getD (i + 1) (0, 0))

@[simp] theorem edgeSeg_cons_succ (a : Point) (l : List Point) (i : ℕ) :
    edgeSeg (a :: l) (i + 1) = edgeSeg l i := by
  simp [edgeSeg]

theorem edgeSeg_cons_cons_zero (a b : Point) (l : List Point) :
    edgeSeg (a :: b :: l) 0 = ArtGallery.segment a b := by
  simp [edgeSeg]

theorem edgeSeg_subset : ∀ {l : List Point} {i : ℕ}, i + 1 < l.length → edgeSeg l i ⊆ chainSet l
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: l, 0, _ => by
    rw [edgeSeg_cons_cons_zero, chainSet_cons_cons]; exact subset_union_left
  | a :: b :: l, i + 1, h => by
    rw [edgeSeg_cons_succ, chainSet_cons_cons]
    exact (edgeSeg_subset (l := b :: l) (by simp at h ⊢; omega)).trans subset_union_right

/-- Pairwise edge conditions of a simple chain. -/
theorem ChainSimple.edge_inter : ∀ {l : List Point}, ChainSimple l → ∀ {i j : ℕ}, i < j →
    j + 1 < l.length →
      (j = i + 1 → edgeSeg l i ∩ edgeSeg l j ⊆ {l.getD (i + 1) (0, 0)}) ∧
      (i + 1 < j → edgeSeg l i ∩ edgeSeg l j = ∅)
  | [], _, _, _, _, hj => by simp at hj
  | [_], _, _, _, _, hj => by simp at hj
  | a :: b :: l, h, 0, j + 1, _, hj => by
    have hsub : edgeSeg (a :: b :: l) (j + 1) ⊆ chainSet (b :: l) := by
      rw [edgeSeg_cons_succ]; exact edgeSeg_subset (by simp at hj ⊢; omega)
    have key : edgeSeg (a :: b :: l) 0 ∩ edgeSeg (a :: b :: l) (j + 1) ⊆ {b} := by
      rw [edgeSeg_cons_cons_zero]
      rintro x ⟨hx1, hx2⟩
      exact h.2.1 ⟨hx1, hsub hx2⟩
    refine ⟨fun _ => by simpa using key, fun hlt => ?_⟩
    apply eq_empty_of_forall_notMem
    intro x hx
    have hxb : x = b := key hx
    subst hxb
    cases l with
    | nil => simp at hj
    | cons c l =>
      have hx2 := hx.2
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [edgeSeg_cons_succ, edgeSeg_cons_succ] at hx2
      have : x ∈ chainSet (c :: l) := edgeSeg_subset (by simp at hj ⊢; omega) hx2
      exact h.2.2.head_not_mem this
  | a :: b :: l, h, i + 1, j + 1, hij, hj => by
    have := ChainSimple.edge_inter (l := b :: l) h.2.2 (i := i) (j := j) (by omega)
      (by simp at hj ⊢; omega)
    simp only [edgeSeg_cons_succ, List.getD_cons_succ]
    refine ⟨fun hji => this.1 (by omega), fun hlt => this.2 (by omega)⟩

theorem getD_eq_getElem' {l : List Point} {i : ℕ} (hi : i < l.length) :
    l.getD i (0, 0) = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- `getD` is injective on the indices of a list without repetitions. -/
theorem getD_inj_of_nodup {l : List Point} (hl : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i (0, 0) = l.getD j (0, 0)) : i = j := by
  rw [getD_eq_getElem' hi, getD_eq_getElem' hj] at h
  exact (hl.getElem_inj_iff).1 h

/-- In a simple chain, vertex `k` lies only on the edges `k − 1` and `k`. -/
theorem ChainSimple.vertex_mem_edge {l : List Point} (h : ChainSimple l) {k i : ℕ}
    (hk : k < l.length) (hi : i + 1 < l.length) (hm : l.getD k (0, 0) ∈ edgeSeg l i) :
    i = k ∨ i + 1 = k := by
  have hnd := h.nodup
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  by_cases hk1 : k + 1 < l.length
  · have hmk : l.getD k (0, 0) ∈ edgeSeg l k := left_mem_segment _ _
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have := (h.edge_inter hlt hk1).2 (by omega)
      have hmem : l.getD k (0, 0) ∈ edgeSeg l i ∩ edgeSeg l k := ⟨hm, hmk⟩
      rw [this] at hmem; exact hmem
    · by_cases hik : i = k + 1
      · subst hik
        have := (h.edge_inter (i := k) (j := k + 1) (by omega) hi).1 rfl ⟨hmk, hm⟩
        exact absurd (getD_inj_of_nodup hnd hk (by omega) this) (by omega)
      · have := (h.edge_inter (i := k) (j := i) hgt hi).2 (by omega)
        have hmem : l.getD k (0, 0) ∈ edgeSeg l k ∩ edgeSeg l i := ⟨hmk, hm⟩
        rw [this] at hmem; exact hmem
  · have hk' : k = l.length - 1 := by omega
    have hk0 : 1 ≤ k := by omega
    have hmk : l.getD k (0, 0) ∈ edgeSeg l (k - 1) := by
      unfold edgeSeg
      rw [show k - 1 + 1 = k by omega]
      exact right_mem_segment _ _
    have hik : i < k - 1 := by omega
    by_cases hik1 : i + 1 = k - 1
    · have := (h.edge_inter (i := i) (j := k - 1) hik (by omega)).1 (by omega) ⟨hm, hmk⟩
      exact absurd (getD_inj_of_nodup hnd hk (by omega) this) (by omega)
    · have := (h.edge_inter (i := i) (j := k - 1) hik (by omega)).2 (by omega)
      have hmem : l.getD k (0, 0) ∈ edgeSeg l i ∩ edgeSeg l (k - 1) := ⟨hm, hmk⟩
      rw [this] at hmem; exact hmem

/-! ### Closing a chain -/

theorem getD_append_singleton_last (l : List Point) (z : Point) :
    (l ++ [z]).getD l.length (0, 0) = z := by
  rw [getD_eq_getElem' (by simp)]
  simp

/-- **Closing.**  A simple chain `a, …, z` with at least three vertices, closed by the edge
`[z, a]` that meets the chain only in `a` and `z`, is a simple polygon. -/
theorem simple_of_chain {a z : Point} {m : List Point} (hm : m ≠ [])
    (hc : ChainSimple (a :: m ++ [z]))
    (hclose : ArtGallery.segment z a ∩ chainSet (a :: m ++ [z]) ⊆ {a, z}) :
    (Polygon.mk (a :: m ++ [z])).Simple := by
  set vs := a :: m ++ [z] with hvs
  have hlen : vs.length = m.length + 2 := by simp [vs]
  have hm1 : 1 ≤ m.length := List.length_pos_iff.2 hm
  have hn : (Polygon.mk vs).n = vs.length := rfl
  have hvtx : ∀ i, (Polygon.mk vs).vtx i = vs.getD i (0, 0) := fun _ => rfl
  have h0 : vs.getD 0 (0, 0) = a := by simp [vs]
  have hlast : vs.getD (vs.length - 1) (0, 0) = z := by
    rw [hlen, show m.length + 2 - 1 = (a :: m).length by simp]
    exact getD_append_singleton_last (a :: m) z
  have hnd := hc.nodup
  -- the pairwise edge condition for `i < j`
  have key : ∀ i j, i < j → j < vs.length →
      (Polygon.mk vs).edge i ∩ (Polygon.mk vs).edge j ⊆ (Polygon.mk vs).commonEndpoints i j := by
    intro i j hij hj
    simp only [Polygon.edge, Polygon.commonEndpoints, hn, hvtx]
    have hi1 : (i + 1) % vs.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hi1]
    by_cases hj1 : j + 1 < vs.length
    · rw [Nat.mod_eq_of_lt hj1]
      rintro x ⟨hx1, hx2⟩
      by_cases hji : j = i + 1
      · have := (hc.edge_inter hij hj1).1 hji ⟨hx1, hx2⟩
        rw [Set.mem_singleton_iff] at this
        subst this
        exact ⟨Or.inr rfl, Or.inl (by rw [hji])⟩
      · have := (hc.edge_inter hij hj1).2 (by omega)
        have hmem : x ∈ edgeSeg vs i ∩ edgeSeg vs j := ⟨hx1, hx2⟩
        rw [this] at hmem; exact hmem.elim
    · have hjl : j = vs.length - 1 := by omega
      have hj0 : (j + 1) % vs.length = 0 := by rw [show j + 1 = vs.length by omega, Nat.mod_self]
      rw [hj0]
      rintro x ⟨hx1, hx2⟩
      have hxS : x ∈ chainSet vs := edgeSeg_subset (by omega) hx1
      rw [hjl, hlast, h0] at hx2
      have hcl := hclose ⟨hx2, hxS⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcl
      rcases hcl with hxa | hxz
      · subst hxa
        have hm0 : vs.getD 0 (0, 0) ∈ edgeSeg vs i := by rw [h0]; exact hx1
        rcases hc.vertex_mem_edge (k := 0) (by omega) (by omega) hm0 with h' | h'
        · subst h'
          exact ⟨Or.inl h0.symm, Or.inr h0.symm⟩
        · omega
      · subst hxz
        have hmz : vs.getD (vs.length - 1) (0, 0) ∈ edgeSeg vs i := by rw [hlast]; exact hx1
        rcases hc.vertex_mem_edge (k := vs.length - 1) (by omega) (by omega) hmz with h' | h'
        · omega
        · refine ⟨Or.inr ?_, Or.inl ?_⟩
          · rw [h', hlast]
          · rw [hjl, hlast]
  refine ⟨by rw [hn]; omega, ?_, ?_⟩
  · intro i j hi hj hv
    rw [hn] at hi hj
    exact getD_inj_of_nodup hnd hi hj hv
  · intro i j hi hj hij
    rw [hn] at hi hj
    apply Subset.antisymm
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact key i j hlt hj
      · rw [inter_comm]
        intro p hp
        have := key j i hgt hi hp
        exact ⟨this.2, this.1⟩
    · rintro p ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with rfl | rfl
        · exact left_mem_segment _ _
        · exact right_mem_segment _ _
      · rcases h2 with rfl | rfl
        · exact left_mem_segment _ _
        · exact right_mem_segment _ _

/-! ### Features hanging from a horizontal line -/

/-- First vertex of a chain. -/
def fstPt (f : List Point) : Point := f.headD (0, 0)

/-- Last vertex of a chain. -/
def lstPt (f : List Point) : Point := f.getLastD (0, 0)

/-- A *floor feature* for the line `y = y₀` inside the strip `x_lo < x < x_hi`: a simple chain
with at least two vertices, starting and ending on the line (from left to right), all of whose
other points lie strictly below the line, and lying strictly inside the strip. -/
def FloorFeature (y₀ xlo xhi : ℝ) (f : List Point) : Prop :=
  2 ≤ f.length ∧ ChainSimple f ∧ (fstPt f).2 = y₀ ∧ (lstPt f).2 = y₀ ∧
    (fstPt f).1 < (lstPt f).1 ∧ (∀ p ∈ chainSet f, p.2 < y₀ ∨ p = fstPt f ∨ p = lstPt f) ∧
    (∀ p ∈ chainSet f, xlo < p.1 ∧ p.1 < xhi)

theorem decomp_of_two_le {f : List Point} (hf : 2 ≤ f.length) :
    f = fstPt f :: (f.tail.dropLast ++ [lstPt f]) := by
  match f, hf with
  | a :: b :: l, _ =>
    have hne : (b :: l) ≠ [] := by simp
    simp only [fstPt, lstPt, List.headD_cons, List.tail_cons, List.cons.injEq, true_and]
    rw [List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    exact (List.dropLast_append_getLast hne).symm

theorem fstPt_mem_list {f : List Point} (hf : 2 ≤ f.length) : fstPt f ∈ f := by
  match f, hf with
  | a :: b :: l, _ => simp [fstPt]

theorem lstPt_mem_list {f : List Point} (hf : 2 ≤ f.length) : lstPt f ∈ f := by
  match f, hf with
  | a :: l, _ =>
    unfold lstPt
    rw [List.getLastD_cons]
    exact List.getLastD_mem_cons

theorem fstPt_mem {f : List Point} (hf : 2 ≤ f.length) : fstPt f ∈ chainSet f :=
  mem_chainSet_of_mem (fstPt_mem_list hf) hf

theorem lstPt_mem {f : List Point} (hf : 2 ≤ f.length) : lstPt f ∈ chainSet f :=
  mem_chainSet_of_mem (lstPt_mem_list hf) hf

/-- The horizontal part of a comb: the points of the line `y = y₀` with `s ≤ x ≤ t`. -/
def hline (y₀ s t : ℝ) : Set Point := {p | p.2 = y₀ ∧ s ≤ p.1 ∧ p.1 ≤ t}

theorem segment_subset_hline {y₀ s t : ℝ} (hst : s ≤ t) :
    ArtGallery.segment (s, y₀) (t, y₀) ⊆ hline y₀ s t := by
  rintro p ⟨τ, h0, h1, rfl⟩
  refine ⟨by simp, ?_, ?_⟩ <;> simp only <;> nlinarith

theorem segment_subset_hline' {y₀ : ℝ} {a b : Point} (ha : a.2 = y₀) (hb : b.2 = y₀)
    (hab : a.1 ≤ b.1) : ArtGallery.segment a b ⊆ hline y₀ a.1 b.1 := by
  rintro p ⟨τ, h0, h1, rfl⟩
  refine ⟨by simp [ha, hb], ?_, ?_⟩ <;> simp only <;> nlinarith

/-- **Comb (floor).**  The polyline from `(s, y₀)` through the features `fs` to `(x_hi, y₀)`
is simple, and lies on the line `y = y₀` between `s` and `x_hi` or on the features. -/
theorem comb_floor {y₀ xlo xhi : ℝ} : ∀ (fs : List (List Point)) (s : ℝ), s < xhi →
    (∀ f ∈ fs, FloorFeature y₀ xlo xhi f) → (∀ f ∈ fs, s < (fstPt f).1) →
    fs.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1) →
    ChainSimple ((s, y₀) :: fs.flatten ++ [(xhi, y₀)]) ∧
      chainSet ((s, y₀) :: fs.flatten ++ [(xhi, y₀)]) ⊆
        hline y₀ s xhi ∪ {p | ∃ f ∈ fs, p ∈ chainSet f}
  | [], s, hs, _, _, _ => by
    simp only [List.flatten_nil, List.nil_append, List.cons_append, chainSet_cons_cons,
      chainSet_single, union_empty]
    refine ⟨⟨fun h => by simp at h; linarith, by simp, trivial⟩, ?_⟩
    exact (segment_subset_hline hs.le).trans subset_union_left
  | f :: fs, s, hs, hF, hfst, hpw => by
    obtain ⟨hlen, hcs, hfy, hly, hfl, hbel, hx⟩ := hF f (by simp)
    set a := fstPt f
    set q := lstPt f
    have hqmem := lstPt_mem hlen
    have hq : q = (q.1, y₀) := Prod.ext rfl hly
    have hpw' := List.pairwise_cons.1 hpw
    have ih := comb_floor fs q.1 (hx q hqmem).2 (fun g hg => hF g (by simp [hg]))
      (fun g hg => (hpw'.1 g hg).2) hpw'.2
    -- the first part: `(s, y₀)` followed by `f`
    set f' := f.tail.dropLast
    have hfdec : f = a :: (f' ++ [q]) := decomp_of_two_le hlen
    have hsa : s < a.1 := hfst f (by simp)
    have hP1 : ChainSimple ((s, y₀) :: (a :: f') ++ [q]) := by
      have e : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: f := by rw [hfdec]; rfl
      rw [e, hfdec, chainSimple_cons_cons, ← hfdec]
      refine ⟨fun h => by rw [← h] at hsa; simp at hsa, ?_, hcs⟩
      rintro x ⟨hx1, hx2⟩
      have hxl := segment_subset_hline' (y₀ := y₀) (a := (s, y₀)) rfl hfy hsa.le hx1
      rcases hbel x hx2 with h | h | h
      · exact absurd hxl.1 (by linarith)
      · exact h
      · exfalso; rw [h] at hxl; linarith [hxl.2.2]
    have hS1 : chainSet ((s, y₀) :: (a :: f') ++ [q]) =
        ArtGallery.segment (s, y₀) a ∪ chainSet f := by
      have e : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: a :: (f' ++ [q]) := rfl
      rw [e, chainSet_cons_cons, ← hfdec]
    have hseg : ArtGallery.segment (s, y₀) a ⊆ hline y₀ s a.1 :=
      segment_subset_hline' (a := (s, y₀)) rfl hfy hsa.le
    have hjoin : chainSet ((s, y₀) :: (a :: f') ++ [q]) ∩ chainSet (q :: (fs.flatten ++ [(xhi, y₀)]))
        ⊆ {q} := by
      rw [hS1]
      rintro x ⟨hx1, hx2⟩
      have hx2' := ih.2 (by rw [hq] at hx2 ⊢; simpa using hx2)
      rcases hx1 with hx1 | hx1
      · have h1 := hseg hx1
        exfalso
        rcases hx2' with h2 | ⟨g, hg, hxg⟩
        · linarith [h1.2.2, h2.2.1]
        · obtain ⟨hglen, -, hgfy, hgly, hgfl, hgbel, -⟩ := hF g (by simp [hg])
          have hqg := (hpw'.1 g hg).2
          rcases hgbel x hxg with h | h | h
          · linarith [h1.1]
          · rw [h] at h1; linarith [h1.2.2]
          · rw [h] at h1; linarith [h1.2.2]
      · rcases hx2' with h2 | ⟨g, hg, hxg⟩
        · rcases hbel x hx1 with h | h | h
          · linarith [h2.1]
          · exfalso; rw [h] at h2; linarith [h2.2.1]
          · exact h
        · exact absurd hxg (Set.disjoint_left.1 (hpw'.1 g hg).1 hx1)
    have hcomb := ChainSimple.join hP1 (by rw [hq] at ih ⊢; simpa using ih.1) hjoin
    have e : (s, y₀) :: (f :: fs).flatten ++ [(xhi, y₀)] =
        ((s, y₀) :: (a :: f')) ++ q :: (fs.flatten ++ [(xhi, y₀)]) := by
      conv_lhs => rw [List.flatten_cons, hfdec]
      simp
    rw [e]
    refine ⟨hcomb, ?_⟩
    rw [chainSet_append_cons, hS1]
    refine union_subset (union_subset ?_ ?_) ?_
    · intro x hxs
      have := hseg hxs
      exact Or.inl ⟨this.1, this.2.1, by linarith [this.2.2, hfl, (hx q hqmem).2]⟩
    · intro x hx; exact Or.inr ⟨f, by simp, hx⟩
    · intro x hx
      rcases ih.2 (by rw [hq] at hx ⊢; simpa using hx) with h | ⟨g, hg, hxg⟩
      · exact Or.inl ⟨h.1, by linarith [h.2.1], h.2.2⟩
      · exact Or.inr ⟨g, by simp [hg], hxg⟩

/-! ### Reflection through the origin -/

theorem mem_segment_neg {a b p : Point} :
    p ∈ ArtGallery.segment (-a) (-b) ↔ -p ∈ ArtGallery.segment a b := by
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, by ext <;> simp <;> ring⟩
  · rintro ⟨t, h0, h1, h⟩
    refine ⟨t, h0, h1, ?_⟩
    have : p = -(-p) := (neg_neg p).symm
    rw [this, h]; ext <;> simp <;> ring

theorem chainSet_map_neg : ∀ (l : List Point) (p : Point),
    p ∈ chainSet (l.map (fun q => -q)) ↔ -p ∈ chainSet l
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, p => by
    simp only [List.map_cons, chainSet_cons_cons, mem_union, mem_segment_neg]
    rw [← List.map_cons, chainSet_map_neg (b :: l) p]

theorem chainSimple_map_neg : ∀ {l : List Point}, ChainSimple l →
    ChainSimple (l.map (fun q => -q))
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    simp only [List.map_cons]
    refine ⟨fun e => h.1 (neg_inj.1 e), ?_, ?_⟩
    · rintro x ⟨hx1, hx2⟩
      rw [← List.map_cons, chainSet_map_neg] at hx2
      have := h.2.1 ⟨mem_segment_neg.1 hx1, hx2⟩
      rw [Set.mem_singleton_iff] at this ⊢
      rw [← this, neg_neg]
    · rw [← List.map_cons]; exact chainSimple_map_neg h.2.2

/-- A *ceiling feature* for the line `y = Y` inside the strip `x_lo < x < x_hi`: a simple chain
with at least two vertices, starting and ending on the line (from right to left), all of whose
other points lie strictly above the line, and lying strictly inside the strip. -/
def CeilFeature (Y xlo xhi : ℝ) (f : List Point) : Prop :=
  2 ≤ f.length ∧ ChainSimple f ∧ (fstPt f).2 = Y ∧ (lstPt f).2 = Y ∧
    (lstPt f).1 < (fstPt f).1 ∧ (∀ p ∈ chainSet f, Y < p.2 ∨ p = fstPt f ∨ p = lstPt f) ∧
    (∀ p ∈ chainSet f, xlo < p.1 ∧ p.1 < xhi)

theorem fstPt_map_neg {f : List Point} (hf : 2 ≤ f.length) :
    fstPt (f.map (fun q => -q)) = -fstPt f := by
  match f, hf with
  | a :: b :: l, _ => rfl

theorem lstPt_map_neg (f : List Point) : lstPt (f.map (fun q => -q)) = -lstPt f := by
  unfold lstPt
  have := List.getLastD_map (f := fun q : Point => -q) (l := f) (a := ((0 : ℝ), (0 : ℝ)))
  simp only [Prod.neg_mk, neg_zero] at this
  exact this

theorem CeilFeature.neg {Y xlo xhi : ℝ} {f : List Point} (h : CeilFeature Y xlo xhi f) :
    FloorFeature (-Y) (-xhi) (-xlo) (f.map (fun q => -q)) := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hab, hx⟩ := h
  rw [FloorFeature, fstPt_map_neg hlen, lstPt_map_neg]
  refine ⟨by simpa using hlen, chainSimple_map_neg hcs, by simp [hfy], by simp [hly],
    by simp; linarith, ?_, ?_⟩
  · intro p hp
    rw [chainSet_map_neg] at hp
    rcases hab _ hp with h | h | h
    · left; simp at h; linarith
    · right; left; rw [← h, neg_neg]
    · right; right; rw [← h, neg_neg]
  · intro p hp
    rw [chainSet_map_neg] at hp
    have := hx _ hp
    simp at this
    constructor <;> linarith [this.1, this.2]

/-- **Comb (ceiling).**  The polyline from `(x_hi, Y)` through the ceiling features `fs`
(ordered from right to left) to `(x_lo, Y)` is simple, and lies on the line `y = Y` between
`x_lo` and `x_hi` or on the features. -/
theorem comb_ceiling {Y xlo xhi : ℝ} (hlt : xlo < xhi) (fs : List (List Point))
    (hF : ∀ f ∈ fs, CeilFeature Y xlo xhi f)
    (hpw : fs.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (fstPt g).1 < (lstPt f).1)) :
    ChainSimple ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]) ∧
      chainSet ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]) ⊆
        hline Y xlo xhi ∪ {p | ∃ f ∈ fs, p ∈ chainSet f} := by
  have hF' : ∀ f ∈ fs.map (List.map (fun q => -q)), FloorFeature (-Y) (-xhi) (-xlo) f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (hF g hg).neg
  have hfst : ∀ f ∈ fs.map (List.map (fun q => -q)), -xhi < (fstPt f).1 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hlen, -, -, -, -, -, hx⟩ := hF g hg
    rw [fstPt_map_neg hlen]
    have := (hx _ (fstPt_mem hlen)).2
    simp; linarith
  have hpw' : (fs.map (List.map (fun q => -q))).Pairwise
      (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1) := by
    rw [List.pairwise_map]
    refine hpw.imp_of_mem (fun {f g} hf hg hfg => ⟨?_, ?_⟩)
    · rw [Set.disjoint_iff]
      rintro x ⟨h1, h2⟩
      rw [chainSet_map_neg] at h1 h2
      exact Set.disjoint_left.1 hfg.1 h1 h2
    · rw [lstPt_map_neg, fstPt_map_neg (hF g hg).1]
      simp; linarith [hfg.2]
  obtain ⟨h1, h2⟩ := comb_floor (xlo := -xhi) _ (-xhi) (by linarith) hF' hfst hpw'
  have e : (-xhi, -Y) :: (fs.map (List.map (fun q => -q))).flatten ++ [(-xlo, -Y)] =
      ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]).map (fun q => -q) := by
    simp [List.map_flatten]
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · have := chainSimple_map_neg h1
    simpa [List.map_map] using this
  · intro p hp
    have hp' : -p ∈ chainSet (((xhi, Y) :: fs.flatten ++ [(xlo, Y)]).map (fun q => -q)) := by
      rw [chainSet_map_neg, neg_neg]; exact hp
    rcases h2 hp' with h | ⟨f, hf, hpf⟩
    · left
      obtain ⟨hy, hx1, hx2⟩ := h
      simp at hy hx1 hx2
      exact ⟨by linarith, by linarith, by linarith⟩
    · right
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      rw [chainSet_map_neg, neg_neg] at hpf
      exact ⟨g, hg, hpf⟩

/-! ### Rectangle with combs -/

theorem FloorFeature.below {y₀ xlo xhi : ℝ} {f : List Point} (h : FloorFeature y₀ xlo xhi f)
    {p : Point} (hp : p ∈ chainSet f) : p.2 ≤ y₀ := by
  obtain ⟨-, -, hfy, hly, -, hbel, -⟩ := h
  rcases hbel p hp with h | rfl | rfl
  · exact h.le
  · exact hfy.le
  · exact hly.le

theorem CeilFeature.above {Y xlo xhi : ℝ} {f : List Point} (h : CeilFeature Y xlo xhi f)
    {p : Point} (hp : p ∈ chainSet f) : Y ≤ p.2 := by
  obtain ⟨-, -, hfy, hly, -, hab, -⟩ := h
  rcases hab p hp with h | rfl | rfl
  · exact h.le
  · exact hfy.ge
  · exact hly.ge

theorem vseg_fst {x y y' : ℝ} {p : Point} (hp : p ∈ ArtGallery.segment (x, y) (x, y')) :
    p.1 = x := by
  obtain ⟨t, -, -, rfl⟩ := hp; simp

theorem vseg_snd {x y y' : ℝ} (hyy : y ≤ y') {p : Point}
    (hp : p ∈ ArtGallery.segment (x, y) (x, y')) : y ≤ p.2 ∧ p.2 ≤ y' := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  simp only
  constructor <;> nlinarith

/-- **Rectangle with combs** (proof plan L2.2a).  The polygon
`(x_lo, y_lo), floor features, (x_hi, y_lo), (x_hi, y_hi), ceiling features, (x_lo, y_hi)` is
simple when the floor features hang below `y = y_lo` (ordered from left to right), the ceiling
features stand above `y = y_hi` (ordered from right to left), both inside `x_lo < x < x_hi`, and
the features of each side are pairwise disjoint. -/
theorem simple_of_combs {xlo xhi ylo yhi : ℝ} (hx : xlo < xhi) (hy : ylo < yhi)
    (F C : List (List Point)) (hF : ∀ f ∈ F, FloorFeature ylo xlo xhi f)
    (hFpw : F.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1))
    (hC : ∀ f ∈ C, CeilFeature yhi xlo xhi f)
    (hCpw : C.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (fstPt g).1 < (lstPt f).1)) :
    (Polygon.mk ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
      [(xlo, yhi)])).Simple := by
  have hfst : ∀ f ∈ F, xlo < (fstPt f).1 := fun f hf =>
    ((hF f hf).2.2.2.2.2.2 _ (fstPt_mem (hF f hf).1)).1
  obtain ⟨hF1, hF2⟩ := comb_floor F xlo hx hF hfst hFpw
  obtain ⟨hC1, hC2⟩ := comb_ceiling hx C hC hCpw
  -- the floor chain followed by the right wall
  have hW : ChainSimple ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)] =
        ((xlo, ylo) :: F.flatten) ++ (xhi, ylo) :: [(xhi, yhi)] := by simp
    rw [e]
    refine ChainSimple.join (by simpa using hF1) ⟨fun h => by simp at h; linarith, by simp, trivial⟩
      ?_
    rintro p ⟨h1, h2⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at h2
    have hp1 := vseg_fst h2
    have h1' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) := by simpa using h1
    rcases hF2 h1' with ⟨hpy, -, -⟩ | ⟨f, hf, hpf⟩
    · exact Prod.ext hp1 hpy
    · exact absurd hp1 (ne_of_lt ((hF f hf).2.2.2.2.2.2 p hpf).2)
  have hWset : chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) =
      chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ∪
        ArtGallery.segment (xhi, ylo) (xhi, yhi) := by
    have e : (xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)] =
        ((xlo, ylo) :: F.flatten) ++ (xhi, ylo) :: [(xhi, yhi)] := by simp
    rw [e, chainSet_append_cons]
    simp
  -- floor bounds
  have hFbd : ∀ p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]),
      p.2 ≤ ylo ∧ xlo ≤ p.1 ∧ p.1 ≤ xhi ∧ (p.1 = xlo → p = (xlo, ylo)) := by
    intro p hp
    rcases hF2 hp with ⟨hpy, h1, h2⟩ | ⟨f, hf, hpf⟩
    · exact ⟨hpy.le, h1, h2, fun h => Prod.ext h hpy⟩
    · have := (hF f hf).2.2.2.2.2.2 p hpf
      exact ⟨(hF f hf).below hpf, this.1.le, this.2.le, fun h => absurd h (ne_of_gt this.1)⟩
  have hCbd : ∀ p ∈ chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]),
      yhi ≤ p.2 ∧ (p.1 = xlo → p = (xlo, yhi)) ∧ (p.1 = xhi → p = (xhi, yhi)) := by
    intro p hp
    rcases hC2 hp with ⟨hpy, -, -⟩ | ⟨f, hf, hpf⟩
    · exact ⟨hpy.ge, fun h => Prod.ext h hpy, fun h => Prod.ext h hpy⟩
    · have := (hC f hf).2.2.2.2.2.2 p hpf
      exact ⟨(hC f hf).above hpf, fun h => absurd h (ne_of_gt this.1),
        fun h => absurd h (ne_of_lt this.2)⟩
  -- join with the ceiling chain
  have hAll : ChainSimple ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++ [(xlo, yhi)] =
        ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ++ (xhi, yhi) :: (C.flatten ++ [(xlo, yhi)]) := by
      simp
    rw [e]
    refine ChainSimple.join (by simpa using hW) (by simpa using hC1) ?_
    rintro p ⟨h1, h2⟩
    have h1' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) := by
      simpa using h1
    have h2' : p ∈ chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]) := by simpa using h2
    have hc := hCbd p h2'
    rw [hWset] at h1'
    rcases h1' with h1' | h1'
    · exact absurd (hFbd p h1').1 (by linarith [hc.1])
    · exact hc.2.2 (vseg_fst h1')
  have hAllset : chainSet ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) = chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) ∪
        chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++ [(xlo, yhi)] =
        ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ++ (xhi, yhi) :: (C.flatten ++ [(xlo, yhi)]) := by
      simp
    rw [e, chainSet_append_cons]
    simp
  have e : [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++ [(xlo, yhi)] =
      (xlo, ylo) :: (F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten) ++ [(xlo, yhi)] := by
    simp
  rw [e]
  refine simple_of_chain (by simp) (by simpa using hAll) ?_
  rintro p ⟨h1, h2⟩
  have hp1 := vseg_fst h1
  have h2' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) := by simpa using h2
  rw [hAllset, hWset] at h2'
  rcases h2' with (h | h) | h
  · exact Or.inl ((hFbd p h).2.2.2 hp1)
  · exact absurd (vseg_fst h) (by rw [hp1]; exact ne_of_lt hx)
  · exact Or.inr ((hCbd p h).2.1 hp1)

end

end ArtGallery.Stade.Chain
