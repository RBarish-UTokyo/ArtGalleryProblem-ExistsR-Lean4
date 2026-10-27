module

public import ArtGallery.Vis.CertCheckerBasic

/-!
# Simple polylines

Tools for proving that parametric vertex lists form simple polygons (used for the corridor chains
of Section 5, docs/section5/08_proof_plan.md §4).

* `edgesOf L`: the edges `(L₀, L₁), (L₁, L₂), …` of the polyline `L`.
* `ChainSimple L` (recursive): the vertices are pairwise distinct, consecutive edges meet only in
  their common vertex and non-consecutive edges are disjoint.  Indexed form: `ChainSimple.inter`.
* **Gluing** (`ChainSimple.append`): two simple polylines sharing an end vertex `m`, whose edges
  meet only in `m`, form a simple polyline.
* **Closing** (`simple_of_chainSimple`): a simple polyline whose closing edge meets the first and
  last edges only in the end vertices and misses all other edges is a simple polygon.
* **Monotone chains** (`chainSimple_of_xMono`): a chain whose abscissae decrease weakly, with
  vertical edges never consecutive, is simple.
* **Dented lines** (`chainSimple_dents`): a horizontal line with dents (thin triangles below it,
  each inside its own region meeting the line only in its mouth, the regions pairwise disjoint and
  the mouths ordered) is simple.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

/-! ### Segment facts -/

section Seg

theorem seg_fst_mem {a b p : Point} (h : p ∈ ArtGallery.segment a b) :
    min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 :=
  ⟨Vis.Cert.seg_fst_lb h (min_le_left _ _) (min_le_right _ _),
    Vis.Cert.seg_fst_ub h (le_max_left _ _) (le_max_right _ _)⟩

/-- A point of the segment `ab` with the abscissa of `b`, where `a.1 ≠ b.1`, is `b`. -/
theorem seg_eq_right_of_fst {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.1 ≠ b.1)
    (hp : p.1 = b.1) : p = b := by
  obtain ⟨t, -, -, rfl⟩ := h
  simp only at hp
  have ht : t = 1 := by
    have : (t - 1) * (b.1 - a.1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd (by linarith) hab
  subst ht
  ext <;> simp

/-- A point of the segment `ab` with the abscissa of `a`, where `a.1 ≠ b.1`, is `a`. -/
theorem seg_eq_left_of_fst {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.1 ≠ b.1)
    (hp : p.1 = a.1) : p = a := by
  rw [Geometry.segment_comm] at h
  exact seg_eq_right_of_fst h (Ne.symm hab) hp

/-- A point of the segment `ab` with the ordinate of `b`, where `a.2 ≠ b.2`, is `b`. -/
theorem seg_eq_right_of_snd {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.2 ≠ b.2)
    (hp : p.2 = b.2) : p = b := by
  obtain ⟨t, -, -, rfl⟩ := h
  simp only at hp
  have ht : t = 1 := by
    have : (t - 1) * (b.2 - a.2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd (by linarith) hab
  subst ht
  ext <;> simp

/-- A point of the segment `ab` with the ordinate of `a`, where `a.2 ≠ b.2`, is `a`. -/
theorem seg_eq_left_of_snd {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.2 ≠ b.2)
    (hp : p.2 = a.2) : p = a := by
  rw [Geometry.segment_comm] at h
  exact seg_eq_right_of_snd h (Ne.symm hab) hp

/-- Points of a vertical segment have its abscissa. -/
theorem seg_fst_of_vertical {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.1 = b.1) :
    p.1 = a.1 := by
  obtain ⟨t, -, -, rfl⟩ := h
  simp [hab]

/-- Points of a horizontal segment have its ordinate. -/
theorem seg_snd_of_horizontal {a b p : Point} (h : p ∈ ArtGallery.segment a b) (hab : a.2 = b.2) :
    p.2 = a.2 := by
  obtain ⟨t, -, -, rfl⟩ := h
  simp [hab]

end Seg

/-! ### Polylines -/

/-- The edges of a polyline: `(L₀, L₁), (L₁, L₂), …`. -/
def edgesOf : List Point → List (Point × Point)
  | a :: b :: l => (a, b) :: edgesOf (b :: l)
  | _ => []

/-- The closed segment of an edge. -/
def segOf (e : Point × Point) : Set Point := ArtGallery.segment e.1 e.2

@[simp] theorem edgesOf_nil : edgesOf [] = [] := rfl

@[simp] theorem edgesOf_single (a : Point) : edgesOf [a] = [] := rfl

@[simp] theorem edgesOf_cons_cons (a b : Point) (l : List Point) :
    edgesOf (a :: b :: l) = (a, b) :: edgesOf (b :: l) := rfl

/-- Edges of a concatenation sharing the vertex `m`. -/
theorem edgesOf_append (L M : List Point) (m : Point) :
    edgesOf (L ++ m :: M) = edgesOf (L ++ [m]) ++ edgesOf (m :: M) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases L with
    | nil => simp
    | cons b L =>
      simp only [List.cons_append, edgesOf_cons_cons, List.cons_append] at ih ⊢
      rw [ih]

/-- Both endpoints of an edge are vertices. -/
theorem mem_of_mem_edgesOf {L : List Point} {e : Point × Point} (he : e ∈ edgesOf L) :
    e.1 ∈ L ∧ e.2 ∈ L := by
  induction L with
  | nil => simp at he
  | cons a L ih =>
    cases L with
    | nil => simp at he
    | cons b L =>
      simp only [edgesOf_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · simp
      · have := ih he
        exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-- Every vertex of a polyline with at least two vertices lies on an edge. -/
theorem exists_edge_of_mem {L : List Point} (hL : 2 ≤ L.length) {x : Point} (hx : x ∈ L) :
    ∃ e ∈ edgesOf L, x ∈ segOf e := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    cases L with
    | nil => simp at hL
    | cons b L =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨(x, b), by simp, Geometry.left_mem_segment _ _⟩
      · rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨(a, x), by simp, Geometry.right_mem_segment _ _⟩
        · cases L with
          | nil => simp at hx'
          | cons c L =>
            obtain ⟨e, he, hxe⟩ := ih (by simp) hx
            exact ⟨e, by simp only [edgesOf_cons_cons, List.mem_cons] at he ⊢; exact Or.inr he,
              hxe⟩

/-- The `k`-th edge. -/
theorem mem_edgesOf_getD {L : List Point} {k : ℕ} (hk : k + 1 < L.length) :
    (L.getD k 0, L.getD (k + 1) 0) ∈ edgesOf L := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a L ih =>
    cases L with
    | nil => simp at hk
    | cons b L =>
      cases k with
      | zero => simp
      | succ k =>
        simp only [edgesOf_cons_cons, List.mem_cons]
        right
        have := ih (k := k) (by simpa using hk)
        simpa using this

/-- **Simple polylines** (recursive): for `a :: b :: l`, the vertex `a` is not repeated, the
first two edges meet only in `b`, the first edge misses all later edges, and the rest is a
simple polyline. -/
def ChainSimple : List Point → Prop
  | a :: b :: l => a ∉ b :: l ∧
      (∀ c ∈ l.head?, ArtGallery.segment a b ∩ ArtGallery.segment b c ⊆ {b}) ∧
      (∀ e ∈ edgesOf l, Disjoint (ArtGallery.segment a b) (segOf e)) ∧
      ChainSimple (b :: l)
  | _ => True

@[simp] theorem chainSimple_nil : ChainSimple [] := trivial

@[simp] theorem chainSimple_single (a : Point) : ChainSimple [a] := trivial

theorem chainSimple_cons_cons {a b : Point} {l : List Point} :
    ChainSimple (a :: b :: l) ↔ a ∉ b :: l ∧
      (∀ c ∈ l.head?, ArtGallery.segment a b ∩ ArtGallery.segment b c ⊆ {b}) ∧
      (∀ e ∈ edgesOf l, Disjoint (ArtGallery.segment a b) (segOf e)) ∧
      ChainSimple (b :: l) := Iff.rfl

/-- A two-vertex polyline is simple iff its vertices differ. -/
theorem chainSimple_pair {a b : Point} (h : a ≠ b) : ChainSimple [a, b] := by
  refine ⟨by simpa using h, by simp, by simp, trivial⟩

theorem ChainSimple.tail {a : Point} {l : List Point} (h : ChainSimple (a :: l)) :
    ChainSimple l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2.2.2

/-- Simple polylines have distinct vertices. -/
theorem ChainSimple.nodup {L : List Point} (h : ChainSimple L) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    cases L with
    | nil => exact List.nodup_singleton a
    | cons b L => exact List.nodup_cons.2 ⟨h.1, ih h.2.2.2⟩

/-- A vertex after the first edge does not lie on the first edge. -/
theorem ChainSimple.not_mem_first {a b : Point} {l : List Point} (h : ChainSimple (a :: b :: l))
    {x : Point} (hx : x ∈ l) : x ∉ ArtGallery.segment a b := by
  intro hxs
  cases l with
  | nil => simp at hx
  | cons c l =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · have := h.2.1 x (by simp) ⟨hxs, Geometry.right_mem_segment _ _⟩
      rw [mem_singleton_iff] at this
      subst this
      exact h.2.2.2.1 (List.mem_cons_self)
    · obtain ⟨e, he, hxe⟩ := exists_edge_of_mem (L := c :: l)
        (by cases l with | nil => simp at hx' | cons _ _ => simp) (List.mem_cons_of_mem _ hx')
      exact Set.disjoint_left.1 (h.2.2.1 e he) hxs hxe

/-- The first vertex does not lie on any edge after the first. -/
theorem ChainSimple.head_not_mem {m c : Point} {M : List Point} (h : ChainSimple (m :: c :: M))
    {e : Point × Point} (he : e ∈ edgesOf (c :: M)) : m ∉ segOf e := by
  intro hm
  cases M with
  | nil => simp at he
  | cons d M =>
    simp only [edgesOf_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have := h.2.1 d (by simp) ⟨Geometry.left_mem_segment _ _, hm⟩
      rw [mem_singleton_iff] at this
      exact h.1 (this ▸ List.mem_cons_self)
    · exact Set.disjoint_left.1 (h.2.2.1 e he) (Geometry.left_mem_segment _ _) hm

/-- The first vertex lies on no edge except the first. -/
theorem ChainSimple.head_not_mem' {m : Point} {M : List Point} (h : ChainSimple (m :: M))
    {e : Point × Point} (he : e ∈ edgesOf M) : m ∉ segOf e := by
  cases M with
  | nil => simp at he
  | cons c M => exact h.head_not_mem he

/-- **Indexed form.** In a simple polyline, edges `i < j` meet only in the common vertex if
`j = i + 1`, and not at all otherwise. -/
theorem ChainSimple.inter {L : List Point} (h : ChainSimple L) {i j : ℕ} (hij : i < j)
    (hj : j + 1 < L.length) :
    ArtGallery.segment (L.getD i 0) (L.getD (i + 1) 0) ∩
        ArtGallery.segment (L.getD j 0) (L.getD (j + 1) 0) ⊆
      if j = i + 1 then {L.getD j 0} else ∅ := by
  induction L generalizing i j with
  | nil => simp at hj
  | cons a L ih =>
    cases L with
    | nil => simp at hj
    | cons b L =>
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j =>
          cases j with
          | zero =>
            cases L with
            | nil => simp at hj
            | cons c L =>
              simp only [List.getD_cons_zero, List.getD_cons_succ, zero_add, ite_true]
              exact h.2.1 c (by simp)
          | succ j =>
            rw [ite_eq_right (by omega)]
            have hjl : j + 1 < L.length := by simp at hj; omega
            have he := mem_edgesOf_getD hjl
            intro x ⟨hx1, hx2⟩
            simp only [List.getD_cons_zero, List.getD_cons_succ, zero_add] at hx1 hx2
            exact (Set.disjoint_left.1 (h.2.2.1 _ he) hx1 hx2).elim
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          have := ih h.2.2.2 (i := i) (j := j) (by omega) (by simpa using hj)
          simp only [List.getD_cons_succ] at this ⊢
          simpa using this

/-- Distinct indices give distinct vertices. -/
theorem ChainSimple.getD_inj {L : List Point} (h : ChainSimple L) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) (hv : L.getD i 0 = L.getD j 0) : i = j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj] at hv
  exact (h.nodup.getElem_inj_iff).1 (by simpa using hv)

/-! ### Gluing -/

/-- A vertex of a polyline lies on one of its edges, or the polyline is a single point. -/
theorem ChainSimple.append_aux {a a' m : Point} {L : List Point}
    (h : ChainSimple (a :: a' :: (L ++ [m]))) : m ∉ ArtGallery.segment a a' :=
  h.not_mem_first (by simp)

/-- **Gluing.** Two simple polylines `L ++ [m]` and `m :: M` whose vertices (other than `m`) are
distinct and whose edges meet only in `m` form a simple polyline. -/
theorem ChainSimple.append {L M : List Point} {m : Point} (hL : ChainSimple (L ++ [m]))
    (hM : ChainSimple (m :: M)) (hdisj : ∀ x ∈ L, x ∉ m :: M)
    (hcross : ∀ e ∈ edgesOf (L ++ [m]), ∀ f ∈ edgesOf (m :: M), segOf e ∩ segOf f ⊆ {m}) :
    ChainSimple (L ++ m :: M) := by
  induction L with
  | nil => simpa using hM
  | cons a L ih =>
    cases L with
    | nil =>
      -- the polyline `a :: m :: M`
      simp only [List.cons_append, List.nil_append] at hL ⊢
      refine ⟨hdisj a (by simp), ?_, ?_, hM⟩
      · intro c hc
        cases M with
        | nil => simp at hc
        | cons c' M =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
          subst hc
          exact hcross (a, m) (by simp) (m, c') (by simp)
      · intro e he
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have := hcross (a, m) (by simp) e (by
          cases M with
          | nil => simp at he
          | cons c M => simp only [edgesOf_cons_cons, List.mem_cons]; exact Or.inr he) ⟨hx1, hx2⟩
        rw [mem_singleton_iff] at this
        subst this
        exact hM.head_not_mem' he hx2
    | cons a' L =>
      simp only [List.cons_append] at hL ⊢
      have hL' : ChainSimple (a' :: (L ++ [m])) := hL.2.2.2
      have ih' := ih (by simpa using hL')
        (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
        (fun e he f hf => hcross e (by
          simp only [List.cons_append, edgesOf_cons_cons, List.mem_cons]
          exact Or.inr (by simpa using he)) f hf)
      refine ⟨?_, ?_, ?_, by simpa using ih'⟩
      · intro hmem
        rcases List.mem_cons.1 hmem with h1 | h1
        · exact hL.1 (h1 ▸ List.mem_cons_self)
        · rcases List.mem_append.1 h1 with h2 | h2
          · exact hL.1 (List.mem_cons_of_mem _ (List.mem_append_left _ h2))
          · exact hdisj a (by simp) h2
      · intro c hc
        apply hL.2.1 c
        cases L with
        | nil => simpa using hc
        | cons l0 L => simpa using hc
      · intro e he
        have he' := he
        rw [edgesOf_append] at he'
        rcases List.mem_append.1 he' with he1 | he2
        · exact hL.2.2.1 e he1
        · rw [Set.disjoint_left]
          intro x hx1 hx2
          have := hcross (a, a') (by simp) e he2 ⟨hx1, hx2⟩
          rw [mem_singleton_iff] at this
          subst this
          exact hL.append_aux hx1

/-! ### Closing a polyline -/

theorem vtx_mk (V : List Point) (i : ℕ) : (Polygon.mk V).vtx i = V.getD i 0 := rfl

theorem n_mk (V : List Point) : (Polygon.mk V).n = V.length := rfl

/-- **Closing.** A simple polyline `V` with at least three vertices whose closing edge
`V_{n−1} V_0` meets the first edge only in `V_0`, the last edge only in `V_{n−1}`, and misses all
other edges, is a simple polygon. -/
theorem simple_of_chainSimple {V : List Point} (hV : ChainSimple V) (h3 : 3 ≤ V.length)
    (hfirst : ArtGallery.segment (V.getD (V.length - 1) 0) (V.getD 0 0) ∩
      ArtGallery.segment (V.getD 0 0) (V.getD 1 0) ⊆ {V.getD 0 0})
    (hlast : ArtGallery.segment (V.getD (V.length - 1) 0) (V.getD 0 0) ∩
      ArtGallery.segment (V.getD (V.length - 2) 0) (V.getD (V.length - 1) 0) ⊆
        {V.getD (V.length - 1) 0})
    (hmid : ∀ k, 1 ≤ k → k + 2 < V.length →
      Disjoint (ArtGallery.segment (V.getD (V.length - 1) 0) (V.getD 0 0))
        (ArtGallery.segment (V.getD k 0) (V.getD (k + 1) 0))) :
    (Polygon.mk V).Simple := by
  set n := V.length with hn
  refine ⟨h3, fun i j hi hj hv => hV.getD_inj hi hj hv, ?_⟩
  -- the edge segments
  have hedge : ∀ i < n, (Polygon.mk V).edge i =
      ArtGallery.segment (V.getD i 0) (V.getD (if i + 1 = n then 0 else i + 1) 0) := by
    intro i hi
    simp only [Polygon.edge, vtx_mk, n_mk]
    congr 2
    split_ifs with h
    · rw [← hn, h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  -- the inclusion `⊆` for `i < j`
  have key : ∀ i j, i < j → j < n → (Polygon.mk V).edge i ∩ (Polygon.mk V).edge j ⊆
      (Polygon.mk V).commonEndpoints i j := by
    intro i j hij hj
    have hsucc : ∀ k < n, (k + 1) % n = if k + 1 = n then 0 else k + 1 := by
      intro k hk
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [hedge i (by omega), hedge j hj]
    simp only [Polygon.commonEndpoints, vtx_mk, n_mk, ← hn, hsucc i (by omega), hsucc j hj]
    rw [ite_eq_right (by omega)]
    by_cases hjn : j + 1 = n
    · -- `j` is the closing edge
      rw [ite_eq_left hjn]
      have hjv : j = n - 1 := by omega
      subst hjv
      by_cases hi0 : i = 0
      · subst hi0
        intro x hx
        have := hfirst ⟨hx.2, hx.1⟩
        rw [mem_singleton_iff] at this
        exact ⟨Or.inl this, Or.inr this⟩
      by_cases hil : i = n - 2
      · subst hil
        rw [show n - 2 + 1 = n - 1 by omega]
        intro x hx
        have := hlast ⟨hx.2, hx.1⟩
        rw [mem_singleton_iff] at this
        exact ⟨Or.inr this, Or.inl this⟩
      · intro x hx
        exact (Set.disjoint_left.1 (hmid i (by omega) (by omega)) hx.2 hx.1).elim
    · rw [ite_eq_right hjn]
      intro x hx
      have := hV.inter hij (by omega) hx
      split_ifs at this with h
      · rw [mem_singleton_iff] at this
        exact ⟨Or.inr (h ▸ this), Or.inl this⟩
      · exact this.elim
  intro i j hi hj hij
  apply Subset.antisymm
  · rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h hj
    · rw [inter_comm]
      intro x hx
      have := key j i h hi hx
      exact ⟨this.2, this.1⟩
  · rintro x ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with rfl | rfl
      · exact Geometry.left_mem_segment _ _
      · exact Geometry.right_mem_segment _ _
    · rcases h2 with rfl | rfl
      · exact Geometry.left_mem_segment _ _
      · exact Geometry.right_mem_segment _ _

/-! ### Monotone chains -/

/-- A chain with weakly decreasing abscissae: each edge either goes strictly west, or is a
nondegenerate vertical edge followed by an edge going strictly west. -/
def XMono : List Point → Prop
  | a :: b :: l => (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 ≠ a.2 ∧ ∀ c ∈ l.head?, c.1 < b.1)) ∧
      XMono (b :: l)
  | _ => True

theorem xMono_cons_cons {a b : Point} {l : List Point} :
    XMono (a :: b :: l) ↔ (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 ≠ a.2 ∧ ∀ c ∈ l.head?, c.1 < b.1)) ∧
      XMono (b :: l) := Iff.rfl

/-- In a monotone chain all vertices are weakly west of the first. -/
theorem XMono.le_head {b : Point} {l : List Point} (h : XMono (b :: l)) :
    ∀ x ∈ b :: l, x.1 ≤ b.1 := by
  induction l generalizing b with
  | nil => intro x hx; simp at hx; rw [hx]
  | cons c l ih =>
    intro x hx
    have hbc : c.1 ≤ b.1 := by
      rcases h.1 with h1 | h1
      · exact h1.le
      · exact h1.1.le
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact (ih h.2 x hx).trans hbc

/-- In a monotone chain all edge points are weakly west of the first vertex. -/
theorem XMono.seg_le_head {b : Point} {l : List Point} (h : XMono (b :: l)) {e : Point × Point}
    (he : e ∈ edgesOf (b :: l)) {z : Point} (hz : z ∈ segOf e) : z.1 ≤ b.1 := by
  have hm := mem_of_mem_edgesOf he
  exact Vis.Cert.seg_fst_ub hz (h.le_head _ hm.1) (h.le_head _ hm.2)

/-- **Monotone chains are simple.** -/
theorem chainSimple_of_xMono {L : List Point} (h : XMono L) : ChainSimple L := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    cases L with
    | nil => trivial
    | cons b l =>
      have hb := h.2
      refine ⟨?_, ?_, ?_, ih hb⟩
      · -- `a` is not repeated
        intro ha
        rcases List.mem_cons.1 ha with hab | hal
        · rcases h.1 with h1 | h1
          · rw [← hab] at h1; exact lt_irrefl _ h1
          · rw [← hab] at h1; exact h1.2.1 rfl
        · cases l with
          | nil => simp at hal
          | cons c l =>
            have hc := hb.2.le_head a hal
            rcases h.1 with h1 | h1
            · have : c.1 ≤ b.1 := hb.le_head c (by simp)
              linarith
            · have := h1.2.2 c (by simp)
              linarith
      · -- consecutive edges meet only at `b`
        intro c hc
        cases l with
        | nil => simp at hc
        | cons c' l =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
          subst hc
          rintro z ⟨hz1, hz2⟩
          rw [mem_singleton_iff]
          have hcb : c'.1 ≤ b.1 := hb.le_head c' (by simp)
          rcases h.1 with h1 | h1
          · -- `ab` goes west: `z.1 ≥ b.1`, and `z.1 ≤ b.1` on `bc`
            have e1 := Vis.Cert.seg_fst_lb hz1 h1.le le_rfl
            have e2 := Vis.Cert.seg_fst_ub hz2 le_rfl hcb
            exact seg_eq_right_of_fst hz1 (ne_of_gt h1) (by linarith)
          · have hc' := h1.2.2 c' (by simp)
            have e1 := seg_fst_of_vertical hz1 h1.1.symm
            exact seg_eq_left_of_fst hz2 (ne_of_gt hc') (by rw [e1, h1.1])
      · -- the first edge misses later edges
        intro e he
        cases l with
        | nil => simp at he
        | cons c l =>
          rw [Set.disjoint_left]
          intro z hz1 hz2
          have hcb : c.1 ≤ b.1 := hb.le_head c (by simp)
          have hzc : z.1 ≤ c.1 := hb.2.seg_le_head he hz2
          rcases h.1 with h1 | h1
          · have e1 := Vis.Cert.seg_fst_lb hz1 h1.le le_rfl
            rcases hb.1 with h2 | h2
            · linarith
            · -- `bc` vertical: the next edge goes strictly west
              cases l with
              | nil => simp at he
              | cons d l =>
                have hdc : d.1 < c.1 := h2.2.2 d (by simp)
                simp only [edgesOf_cons_cons, List.mem_cons] at he
                rcases he with rfl | he
                · have hzb : z = b := seg_eq_right_of_fst hz1 (ne_of_gt h1) (by linarith)
                  have hzc' : z = c := seg_eq_left_of_fst hz2 (ne_of_gt hdc) (by linarith)
                  exact h2.2.1 (by rw [← hzb, hzc'])
                · have := hb.2.2.seg_le_head he hz2
                  linarith
          · have hc := h1.2.2 c (by simp)
            have e1 := seg_fst_of_vertical hz1 h1.1.symm
            rw [h1.1] at hc
            linarith

/-! ### Dented lines -/

/-- A dent of a horizontal line: the mouth corners `A`, `B` on the line, the tip `T` below it,
and a region `R` containing the two dent edges `A T`, `T B`. -/
structure Dent where
  /-- Left mouth corner. -/
  A : Point
  /-- Tip. -/
  T : Point
  /-- Right mouth corner. -/
  B : Point
  /-- A region containing the dent. -/
  R : Set Point

/-- The conditions on one dent of the line `y = y₀`. -/
structure Dent.OK (d : Dent) (y₀ : ℝ) : Prop where
  hA : d.A.2 = y₀
  hB : d.B.2 = y₀
  hT : d.T.2 < y₀
  hAB : d.A.1 < d.B.1
  hAT : ArtGallery.segment d.A d.T ⊆ d.R
  hTB : ArtGallery.segment d.T d.B ⊆ d.R
  hRy : ∀ z ∈ d.R, z.2 ≤ y₀
  hRline : ∀ z ∈ d.R, z.2 = y₀ → d.A.1 ≤ z.1 ∧ z.1 ≤ d.B.1
  hcorner : ArtGallery.segment d.A d.T ∩ ArtGallery.segment d.T d.B ⊆ {d.T}

/-- The chain of the dents followed by the end point `e`. -/
def dentChain (e : Point) : List Dent → List Point
  | [] => [e]
  | d :: ds => d.A :: d.T :: d.B :: dentChain e ds

/-- The abscissa where the remaining chain starts. -/
def firstX (e : Point) : List Dent → ℝ
  | [] => e.1
  | d :: _ => d.A.1

/-- The region swept by the remaining chain. -/
def dentRight (y₀ : ℝ) (e : Point) (ds : List Dent) : Set Point :=
  {z | (z.2 = y₀ ∧ firstX e ds ≤ z.1 ∧ z.1 ≤ e.1) ∨ ∃ d ∈ ds, z ∈ d.R}

/-- The hypotheses on the dents: each dent is fine, the regions are pairwise disjoint, the mouths
are ordered and end before `e`. -/
structure DentsOK (y₀ : ℝ) (e : Point) (ds : List Dent) : Prop where
  ok : ∀ d ∈ ds, d.OK y₀
  disj : ds.Pairwise (fun d d' => Disjoint d.R d'.R)
  sorted : ds.IsChain (fun d d' => d.B.1 < d'.A.1)
  last : ∀ d ∈ ds.getLast?, d.B.1 < e.1
  he : e.2 = y₀

theorem DentsOK.tail {y₀ : ℝ} {e : Point} {d : Dent} {ds : List Dent}
    (h : DentsOK y₀ e (d :: ds)) : DentsOK y₀ e ds :=
  ⟨fun d' hd' => h.ok d' (List.mem_cons_of_mem _ hd'), (List.pairwise_cons.1 h.disj).2,
    h.sorted.tail, fun d' hd' => h.last d' (by
      cases ds with
      | nil => simp at hd'
      | cons _ _ => simpa [List.getLast?_cons_cons] using hd'), h.he⟩

/-- The start of the remaining chain is left of its end. -/
theorem DentsOK.firstX_lt {y₀ : ℝ} {e : Point} {ds : List Dent} (h : DentsOK y₀ e ds) :
    firstX e ds ≤ e.1 := by
  induction ds with
  | nil => exact le_rfl
  | cons d ds ih =>
    have ih' := ih h.tail
    simp only [firstX]
    cases ds with
    | nil =>
      have := h.last d (by simp)
      have := (h.ok d (by simp)).hAB
      linarith
    | cons d' ds =>
      have h1 : d.B.1 < d'.A.1 := (List.isChain_cons_cons.1 h.sorted).1
      have := (h.ok d (by simp)).hAB
      simp only [firstX] at ih'
      linarith

/-- The edges of the remaining chain lie in its region. -/
theorem dentChain_edges {y₀ : ℝ} {e : Point} {ds : List Dent} (h : DentsOK y₀ e ds) :
    ∀ f ∈ edgesOf (dentChain e ds), segOf f ⊆ dentRight y₀ e ds := by
  induction ds with
  | nil => simp [dentChain]
  | cons d ds ih =>
    have hd := h.ok d (by simp)
    have ih' := ih h.tail
    have hfx := h.tail.firstX_lt
    intro f hf
    simp only [dentChain, edgesOf_cons_cons, List.mem_cons] at hf
    have hR : d.R ⊆ dentRight y₀ e (d :: ds) := fun z hz => Or.inr ⟨d, by simp, hz⟩
    rcases hf with rfl | rfl | hf
    · exact hd.hAT.trans hR
    · exact hd.hTB.trans hR
    · -- edges from `B`
      cases ds with
      | nil =>
        simp only [dentChain, edgesOf_cons_cons, edgesOf_single, List.mem_cons,
          List.not_mem_nil, or_false] at hf
        subst hf
        intro z hz
        left
        refine ⟨?_, ?_, ?_⟩
        · rw [seg_snd_of_horizontal hz (by rw [hd.hB, h.he]), hd.hB]
        · simp only [firstX]
          exact Vis.Cert.seg_fst_lb hz hd.hAB.le (by have := h.last d (by simp); linarith [hd.hAB])
        · exact Vis.Cert.seg_fst_ub hz (h.last d (by simp)).le le_rfl
      | cons d' ds =>
        simp only [dentChain, edgesOf_cons_cons, List.mem_cons] at hf
        have h1 : d.B.1 < d'.A.1 := (List.isChain_cons_cons.1 h.sorted).1
        rcases hf with rfl | hf
        · intro z hz
          left
          have hd' := h.ok d' (by simp)
          refine ⟨?_, ?_, ?_⟩
          · rw [seg_snd_of_horizontal hz (by rw [hd.hB, hd'.hA]), hd.hB]
          · simp only [firstX]
            exact Vis.Cert.seg_fst_lb hz hd.hAB.le (by linarith [hd.hAB])
          · simp only [firstX] at hfx
            exact Vis.Cert.seg_fst_ub hz (by linarith) hfx
        · intro z hz
          have := ih' f (by simp only [dentChain, edgesOf_cons_cons, List.mem_cons]; exact hf) hz
          rcases this with ⟨h2, h3, h4⟩ | ⟨d'', hd'', hz''⟩
          · left
            simp only [firstX] at h3 ⊢
            exact ⟨h2, by linarith [hd.hAB], h4⟩
          · exact Or.inr ⟨d'', List.mem_cons_of_mem _ hd'', hz''⟩

/-- The vertices of the remaining chain lie in its region. -/
theorem dentChain_mem {y₀ : ℝ} {e : Point} {ds : List Dent} (h : DentsOK y₀ e ds) :
    ∀ x ∈ dentChain e ds, x ∈ dentRight y₀ e ds := by
  cases ds with
  | nil =>
    intro x hx
    simp only [dentChain, List.mem_singleton] at hx
    subst hx
    exact Or.inl ⟨h.he, le_rfl, le_rfl⟩
  | cons d ds =>
    intro x hx
    obtain ⟨f, hf, hxf⟩ := exists_edge_of_mem (by simp [dentChain]) hx
    exact dentChain_edges h f hf hxf

/-- **Dented lines are simple.** For a start point `s` on the line `y = y₀`, left of the first
mouth (or of `e` if there are no dents), the chain `s, A₁, T₁, B₁, …, e` is simple. -/
theorem chainSimple_dents {y₀ : ℝ} {e s : Point} {ds : List Dent} (h : DentsOK y₀ e ds)
    (hs : s.2 = y₀) (hsx : s.1 < firstX e ds) : ChainSimple (s :: dentChain e ds) := by
  induction ds generalizing s with
  | nil =>
    simp only [dentChain]
    refine chainSimple_pair ?_
    intro hse
    simp only [firstX] at hsx
    rw [hse] at hsx
    exact lt_irrefl _ hsx
  | cons d ds ih =>
    have hd := h.ok d (by simp)
    have hfx := h.tail.firstX_lt
    have hBx : d.B.1 < firstX e ds := by
      cases ds with
      | nil => exact h.last d (by simp)
      | cons d' ds => exact (List.isChain_cons_cons.1 h.sorted).1
    have ihB := ih h.tail hd.hB hBx
    simp only [firstX] at hsx
    -- points of the later regions
    have hlate : ∀ z ∈ dentRight y₀ e ds, z ∉ d.R ∧ (z.2 = y₀ → d.B.1 ≤ z.1) := by
      intro z hz
      rcases hz with ⟨h2, h3, -⟩ | ⟨d', hd', hz'⟩
      · refine ⟨fun hzR => ?_, fun _ => by linarith⟩
        have := (hd.hRline z hzR h2).2
        linarith
      · have hd'ok := h.ok d' (List.mem_cons_of_mem _ hd')
        refine ⟨fun hzR => Set.disjoint_left.1 ((List.pairwise_cons.1 h.disj).1 d' hd') hzR hz',
          fun h2 => ?_⟩
        have := (hd'ok.hRline z hz' h2).1
        have hle : d.B.1 < d'.A.1 := by
          -- the mouths are sorted
          have hs := h.sorted
          have key : ∀ (l : List Dent) (d0 : Dent), (d0 :: l).IsChain
              (fun d d' => d.B.1 < d'.A.1) → (∀ x ∈ d0 :: l, (x.OK y₀)) →
              ∀ x ∈ l, d0.B.1 < x.A.1 := by
            intro l
            induction l with
            | nil => simp
            | cons x l ihl =>
              intro d0 hc hok y hy
              have h01 : d0.B.1 < x.A.1 := (List.isChain_cons_cons.1 hc).1
              rcases List.mem_cons.1 hy with rfl | hy
              · exact h01
              · have := ihl x (List.isChain_cons_cons.1 hc).2
                  (fun z hz => hok z (List.mem_cons_of_mem _ hz)) y hy
                have := (hok x (by simp)).hAB
                linarith
          exact key ds d hs h.ok d' hd'
        linarith
    have hTR : d.T ∈ d.R := hd.hAT (Geometry.right_mem_segment _ _)
    have hAR : d.A ∈ d.R := hd.hAT (Geometry.left_mem_segment _ _)
    have hBR : d.B ∈ d.R := hd.hTB (Geometry.right_mem_segment _ _)
    have hBmem : ∀ x ∈ d.B :: dentChain e ds, x = d.B ∨ x ∈ dentRight y₀ e ds := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (dentChain_mem h.tail x hx)
    -- the head part `s, A, T, B`
    have hsA : ∀ z ∈ ArtGallery.segment s d.A, z.2 = y₀ ∧ z.1 ≤ d.A.1 := by
      intro z hz
      exact ⟨by rw [seg_snd_of_horizontal hz (by rw [hs, hd.hA]), hs],
        Vis.Cert.seg_fst_ub hz hsx.le le_rfl⟩
    have hhead : ChainSimple ([s, d.A, d.T] ++ [d.B]) := by
      simp only [List.cons_append, List.nil_append]
      have hTne : ∀ x : Point, x.2 = y₀ → x ≠ d.T := fun x hx hxT => by
        rw [hxT] at hx; linarith [hd.hT]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
      · intro hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h1 | h1 | h1
        · rw [h1] at hsx; exact lt_irrefl _ hsx
        · exact hTne s hs h1
        · rw [h1] at hsx; linarith [hd.hAB]
      · intro c hc
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
        subst hc
        rintro z ⟨hz1, hz2⟩
        obtain ⟨hzy, hzx⟩ := hsA z hz1
        have := (hd.hRline z (hd.hAT hz2) hzy).1
        exact seg_eq_right_of_fst hz1 (ne_of_lt hsx) (by linarith)
      · intro f hf
        simp only [edgesOf_cons_cons, edgesOf_single, List.mem_singleton] at hf
        subst hf
        rw [Set.disjoint_left]
        intro z hz1 hz2
        obtain ⟨hzy, hzx⟩ := hsA z hz1
        have := (hd.hRline z (hd.hTB hz2) hzy).1
        have hzA : z = d.A := seg_eq_right_of_fst hz1 (ne_of_lt hsx) (by linarith)
        subst hzA
        have := seg_eq_right_of_snd hz2 (by rw [hd.hB]; exact ne_of_lt hd.hT) (by rw [hd.hA, hd.hB])
        have h2 := hd.hAB
        rw [this] at h2
        exact lt_irrefl _ h2
      · intro hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h1 | h1
        · exact hTne _ hd.hA h1
        · have h2 := hd.hAB; rw [h1] at h2; exact lt_irrefl _ h2
      · intro c hc
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
        subst hc
        exact hd.hcorner
      · intro f hf; simp at hf
      · simpa using (hTne _ hd.hB).symm
    refine ChainSimple.append (L := [s, d.A, d.T]) hhead ihB ?_ ?_
    · -- vertices of the head part are not repeated later
      intro x hx hxl
      rcases hBmem x hxl with hxB | hxR
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [hxB] at hsx; linarith [hd.hAB]
        · have h2 := hd.hAB; rw [hxB] at h2; exact lt_irrefl _ h2
        · have h2 := hd.hT; rw [hxB] at h2; linarith [hd.hB]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨hnR, hline⟩ := hlate x hxR
        rcases hx with rfl | rfl | rfl
        · have := hline hs; linarith [hd.hAB]
        · have := hline hd.hA; linarith [hd.hAB]
        · exact hnR hTR
    · -- edges meet only at `B`
      intro f hf g hg
      simp only [List.cons_append, List.nil_append, edgesOf_cons_cons, edgesOf_single,
        List.mem_cons, List.not_mem_nil, or_false] at hf
      -- the edges of the tail part
      have hgsplit : g = (d.B, (dentChain e ds).headI) ∨
          segOf g ⊆ dentRight y₀ e ds := by
        cases ds with
        | nil =>
          simp only [dentChain, edgesOf_cons_cons, edgesOf_single, List.mem_singleton] at hg
          left; simpa [dentChain] using hg
        | cons d' ds =>
          change g ∈ (d.B, d'.A) :: edgesOf (dentChain e (d' :: ds)) at hg
          rcases List.mem_cons.1 hg with rfl | hg
          · left; rfl
          · right
            exact dentChain_edges h.tail g hg
      -- the first tail edge lies on the line, right of `B`
      have hfirstedge : ∀ z ∈ segOf (d.B, (dentChain e ds).headI), z.2 = y₀ ∧ d.B.1 ≤ z.1 := by
        intro z hz
        have hy : ((dentChain e ds).headI).2 = y₀ := by
          cases ds with
          | nil => simpa [dentChain] using h.he
          | cons d' ds => simpa [dentChain] using (h.ok d' (by simp)).hA
        have hx : d.B.1 ≤ ((dentChain e ds).headI).1 := by
          cases ds with
          | nil => simpa [dentChain, firstX] using hBx.le
          | cons d' ds => simpa [dentChain, firstX] using hBx.le
        exact ⟨by rw [seg_snd_of_horizontal hz (by rw [hd.hB, hy]), hd.hB],
          Vis.Cert.seg_fst_lb hz le_rfl hx⟩
      rintro z ⟨hzf, hzg⟩
      rw [mem_singleton_iff]
      rcases hf with rfl | rfl | rfl
      · -- edge `s A` (on the line, left of `A`)
        obtain ⟨hzy, hzx⟩ := hsA z hzf
        rcases hgsplit with rfl | hgR
        · have := (hfirstedge z hzg).2; linarith [hd.hAB]
        · have := (hlate z (hgR hzg)).2 hzy; linarith [hd.hAB]
      · -- edge `A T`
        have hzR := hd.hAT hzf
        rcases hgsplit with rfl | hgR
        · obtain ⟨hzy, hzx⟩ := hfirstedge z hzg
          have := (hd.hRline z hzR hzy).2
          exact seg_eq_left_of_fst hzg (by
            intro hEq
            have hy : ((dentChain e ds).headI).1 = d.B.1 := hEq.symm
            -- the next vertex is strictly right of `B`
            cases ds with
            | nil => simp [dentChain] at hy; linarith
            | cons d' ds => simp [dentChain, firstX] at hy hBx; linarith) (by linarith)
        · exact ((hlate z (hgR hzg)).1 hzR).elim
      · -- edge `T B`
        have hzR := hd.hTB hzf
        rcases hgsplit with rfl | hgR
        · obtain ⟨hzy, hzx⟩ := hfirstedge z hzg
          have := (hd.hRline z hzR hzy).2
          exact seg_eq_left_of_fst hzg (by
            intro hEq
            have hy : ((dentChain e ds).headI).1 = d.B.1 := hEq.symm
            cases ds with
            | nil => simp [dentChain] at hy; linarith
            | cons d' ds => simp [dentChain, firstX] at hy hBx; linarith) (by linarith)
        · exact ((hlate z (hgR hzg)).1 hzR).elim

end ArtGallery.Sec5.Corridor

end
