module

public import ArtGallery.Vis.CertCheckerBasic

/-!
# Kernel-checkable certificates: simplicity of a polygon with natural vertices

`simpleCheckN V = true → (Polygon.mk (V.map natPoint)).Simple` (`simple_of_simpleCheckN`).

**Algorithm.**  The `n` edges `(i, vᵢ, vᵢ₊₁)` (indices mod `n`) are the leaves of a balanced
binary tree (`ETree`) built bottom-up by pairing neighbours (`pairUp`, `build`); every node
stores the bounding box of its leaves.  `selfT` checks every pair of edges by a dual-tree
traversal (`crossT`, `crossLeaf`): a pair of subtrees with strictly separated boxes is accepted
at once, so only edges whose boxes overlap are compared individually.  A pair of edges is
accepted if their boxes are strictly separated, if they are consecutive (`adj`; these are
handled by `tripleOK` on every corner), or if one segment lies strictly on one side of the line
of the other (`sepD`).  For the polygons met in practice this examines `O(n log n)` pairs instead
of `n²/2`.

All functions are structurally recursive on lists or trees, use only kernel-accelerated natural
number arithmetic and are meant to be evaluated by `decide +kernel`.
-/

@[expose] public section

namespace ArtGallery.Vis.Cert

open ArtGallery.Geometry Set

/-! ### List lemmas -/

theorem getD_append_left' {α : Type*} {l l' : List α} {k : ℕ} {d : α} (h : k < l.length) :
    (l ++ l').getD k d = l.getD k d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type*} {l l' : List α} {k : ℕ} {d : α} (h : l.length ≤ k) :
    (l ++ l').getD k d = l'.getD (k - l.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-! ### Edge trees -/

/-- A binary tree whose leaves are the edges `(i, a, b)` of the polygon (index, endpoints) with
their bounding boxes; inner nodes store a box containing the boxes of their children. -/
inductive ETree where
  /-- The edge with index `i` from `a` to `b`, with its bounding box `bx`. -/
  | leaf (i : ℕ) (a b : NPt) (bx : Box)
  /-- Two subtrees, with a common bounding box. -/
  | node (bx : Box) (l r : ETree)

namespace ETree

/-- The box stored at the root. -/
def box : ETree → Box
  | .leaf _ _ _ bx => bx
  | .node bx _ _ => bx

/-- The edges of the tree, from left to right. -/
def leaves : ETree → List (ℕ × NPt × NPt)
  | .leaf i a b _ => [(i, a, b)]
  | .node _ l r => l.leaves ++ r.leaves

/-- The stored boxes are correct: leaf boxes are the bounding boxes of the edges, node boxes
contain the boxes of the children. -/
def WF : ETree → Prop
  | .leaf _ a b bx => bx = segBox a b
  | .node bx l r => l.box.Sub bx ∧ r.box.Sub bx ∧ l.WF ∧ r.WF

end ETree

/-- The closed segment of an edge `(i, a, b)`. -/
def segOf (x : ℕ × NPt × NPt) : Set Point := ArtGallery.segment (natPoint x.2.1) (natPoint x.2.2)

/-- Every edge of a well-formed tree lies in the root box. -/
theorem ETree.inBox_of_mem_leaves {t : ETree} (ht : t.WF) {x : ℕ × NPt × NPt}
    (hx : x ∈ t.leaves) {p : Point} (hp : p ∈ segOf x) : InBox t.box p := by
  induction t with
  | leaf i a b bx =>
    simp only [ETree.leaves, List.mem_singleton] at hx
    subst hx
    simp only [ETree.WF] at ht
    subst ht
    exact inBox_segBox hp
  | node bx l r ihl ihr =>
    obtain ⟨hl, hr, wl, wr⟩ := ht
    simp only [ETree.leaves, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Box.inBox_of_sub hl (ihl wl hx)
    · exact Box.inBox_of_sub hr (ihr wr hx)

/-! ### The pair checks -/

/-- Edges `i < j` of an `n`-gon are consecutive: `j = i + 1`, or `i = 0` and `j = n − 1`. -/
def adj (n i j : ℕ) : Bool := Nat.beq j (i + 1) || (Nat.beq i 0 && Nat.beq (j + 1) n)

theorem adj_iff {n i j : ℕ} : adj n i j = true ↔ j = i + 1 ∨ (i = 0 ∧ j + 1 = n) := by
  simp [adj, Nat.beq_eq]

/-- The condition verified for a pair of edges: consecutive, or disjoint. -/
def Good (n : ℕ) (x y : ℕ × NPt × NPt) : Prop :=
  adj n x.1 y.1 = true ∨ Disjoint (segOf x) (segOf y)

/-- One edge `(i, a, b)` with box `bx` against all edges of a tree. -/
def crossLeaf (n i : ℕ) (a b : NPt) (bx : Box) : ETree → Bool
  | .leaf j c d bx' => boxSep bx bx' || adj n i j || sepD a b c d
  | .node bx' l r => boxSep bx bx' || (crossLeaf n i a b bx l && crossLeaf n i a b bx r)

/-- All edges of the first tree against all edges of the second tree. -/
def crossT (n : ℕ) : ETree → ETree → Bool
  | .leaf i a b bx, t₂ => crossLeaf n i a b bx t₂
  | .node bx l r, t₂ => boxSep bx t₂.box || (crossT n l t₂ && crossT n r t₂)

/-- All pairs of edges of a tree. -/
def selfT (n : ℕ) : ETree → Bool
  | .leaf .. => true
  | .node _ l r => selfT n l && selfT n r && crossT n l r

/-- Points of two strictly separated boxes give disjoint edges. -/
theorem disjoint_of_boxSep {p q : Box} (h : boxSep p q = true) {x y : ℕ × NPt × NPt}
    (hx : ∀ z ∈ segOf x, InBox p z) (hy : ∀ z ∈ segOf y, InBox q z) :
    Disjoint (segOf x) (segOf y) :=
  Set.disjoint_left.2 fun z h1 h2 => not_inBox_of_boxSep h (hx z h1) (hy z h2)

theorem crossLeaf_sound {n i : ℕ} {a b : NPt} {bx : Box}
    (hbx : ∀ z ∈ segOf (i, a, b), InBox bx z) {t : ETree} (ht : t.WF)
    (h : crossLeaf n i a b bx t = true) : ∀ y ∈ t.leaves, Good n (i, a, b) y := by
  induction t with
  | leaf j c d bx' =>
    intro y hy
    simp only [ETree.leaves, List.mem_singleton] at hy
    subst hy
    simp only [crossLeaf, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · refine Or.inr (disjoint_of_boxSep h hbx fun z hz => ?_)
      have := ETree.inBox_of_mem_leaves (t := .leaf j c d bx') ht (by simp [ETree.leaves]) hz
      exact this
    · exact Or.inl h
    · exact Or.inr (disjoint_of_sepD h)
  | node bx' l r ihl ihr =>
    intro y hy
    obtain ⟨hl, hr, wl, wr⟩ := ht
    simp only [crossLeaf, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · refine Or.inr (disjoint_of_boxSep h hbx fun z hz => ?_)
      exact ETree.inBox_of_mem_leaves (t := .node bx' l r) ⟨hl, hr, wl, wr⟩ hy hz
    · simp only [ETree.leaves, List.mem_append] at hy
      rcases hy with hy | hy
      · exact ihl wl h1 y hy
      · exact ihr wr h2 y hy

theorem crossT_sound {n : ℕ} {t₁ t₂ : ETree} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : crossT n t₁ t₂ = true) : ∀ x ∈ t₁.leaves, ∀ y ∈ t₂.leaves, Good n x y := by
  induction t₁ with
  | leaf i a b bx =>
    intro x hx
    simp only [ETree.leaves, List.mem_singleton] at hx
    subst hx
    refine crossLeaf_sound (fun z hz => ?_) h₂ h
    exact ETree.inBox_of_mem_leaves (t := .leaf i a b bx) h₁ (by simp [ETree.leaves]) hz
  | node bx l r ihl ihr =>
    intro x hx y hy
    obtain ⟨hl, hr, wl, wr⟩ := h₁
    simp only [crossT, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨e1, e2⟩
    · refine Or.inr (disjoint_of_boxSep h (fun z hz => ?_) fun z hz =>
        ETree.inBox_of_mem_leaves h₂ hy hz)
      exact ETree.inBox_of_mem_leaves (t := .node bx l r) ⟨hl, hr, wl, wr⟩ hx hz
    · simp only [ETree.leaves, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihl wl e1 x hx y hy
      · exact ihr wr e2 x hx y hy

theorem selfT_sound {n : ℕ} {t : ETree} (ht : t.WF) (h : selfT n t = true) :
    t.leaves.Pairwise (Good n) := by
  induction t with
  | leaf => simp [ETree.leaves]
  | node bx l r ihl ihr =>
    obtain ⟨-, -, wl, wr⟩ := ht
    simp only [selfT, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [ETree.leaves]
    exact List.pairwise_append.2 ⟨ihl wl h1, ihr wr h2, crossT_sound wl wr h3⟩

/-! ### Building the tree -/

/-- Pair neighbouring trees. -/
def pairUp : List ETree → List ETree
  | a :: b :: rest => .node (a.box.union b.box) a b :: pairUp rest
  | l => l

/-- Pair repeatedly until one tree is left (the first argument is fuel). -/
def build {α : Type} : List α → List ETree → ETree
  | _, [] => .leaf 0 (0, 0) (0, 0) ⟨0, 0, 0, 0⟩
  | _, [t] => t
  | [], t :: _ :: _ => t
  | _ :: f, ts@(_ :: _ :: _) => build f (pairUp ts)

/-- The edges of a closed chain: the open chain `l` from index `i` on, closed back to `a₀`. -/
def edgesGo (a₀ : NPt) : ℕ → List NPt → List ETree
  | i, a :: b :: rest => .leaf i a b (segBox a b) :: edgesGo a₀ (i + 1) (b :: rest)
  | i, [a] => [.leaf i a a₀ (segBox a a₀)]
  | _, [] => []

/-- The edges of a list of trees, from left to right. -/
def flat (ts : List ETree) : List (ℕ × NPt × NPt) := ts.flatMap ETree.leaves

theorem flat_pairUp : ∀ ts : List ETree, flat (pairUp ts) = flat ts
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have ih := flat_pairUp rest
    simp only [pairUp, flat, List.flatMap_cons, ETree.leaves, List.append_assoc] at ih ⊢
    rw [ih]

theorem wf_pairUp : ∀ ts : List ETree, (∀ t ∈ ts, t.WF) → ∀ t ∈ pairUp ts, t.WF
  | [], h => h
  | [_], h => h
  | a :: b :: rest, h => by
    simp only [pairUp, List.mem_cons, forall_eq_or_imp] at h ⊢
    obtain ⟨ha, hb, hr⟩ := h
    exact ⟨⟨Box.sub_union_left _ _, Box.sub_union_right _ _, ha, hb⟩, wf_pairUp rest hr⟩

theorem length_pairUp : ∀ ts : List ETree, 2 * (pairUp ts).length ≤ ts.length + 1
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | a :: b :: rest => by
    have := length_pairUp rest
    simp only [pairUp, List.length_cons]; omega

theorem build_spec {α : Type} (f : List α) (ts : List ETree) (hne : ts ≠ [])
    (hlen : ts.length ≤ f.length + 1) (hwf : ∀ t ∈ ts, t.WF) :
    (build f ts).WF ∧ (build f ts).leaves = flat ts := by
  induction f generalizing ts with
  | nil =>
    match ts, hne, hlen with
    | [t], _, _ => exact ⟨hwf t (by simp), by simp [build, flat]⟩
  | cons x f ih =>
    match ts, hne, hlen with
    | [t], _, _ => exact ⟨hwf t (by simp), by simp [build, flat]⟩
    | a :: b :: rest, _, hlen =>
      have hl := length_pairUp (a :: b :: rest)
      have hne' : pairUp (a :: b :: rest) ≠ [] := by simp [pairUp]
      have := ih (pairUp (a :: b :: rest)) hne'
        (by simp only [List.length_cons] at hl hlen ⊢; omega)
        (wf_pairUp _ hwf)
      simp only [build]
      rw [flat_pairUp] at this
      exact this

theorem length_edgesGo (a₀ : NPt) (i : ℕ) (l : List NPt) :
    (edgesGo a₀ i l).length = l.length := by
  induction l generalizing i with
  | nil => simp [edgesGo]
  | cons a l ih =>
    match l, ih with
    | [], _ => simp [edgesGo]
    | b :: rest, ih => simp only [edgesGo, List.length_cons] at ih ⊢; rw [ih]

/-- The edge list as a plain list of triples. -/
def edgeTriples (a₀ : NPt) : ℕ → List NPt → List (ℕ × NPt × NPt)
  | i, a :: b :: rest => (i, a, b) :: edgeTriples a₀ (i + 1) (b :: rest)
  | i, [a] => [(i, a, a₀)]
  | _, [] => []

theorem flat_edgesGo (a₀ : NPt) (i : ℕ) (l : List NPt) :
    flat (edgesGo a₀ i l) = edgeTriples a₀ i l ∧ ∀ t ∈ edgesGo a₀ i l, t.WF := by
  induction l generalizing i with
  | nil => simp [edgesGo, edgeTriples, flat]
  | cons a l ih =>
    match l, ih with
    | [], _ => simp [edgesGo, edgeTriples, flat, ETree.leaves, ETree.WF]
    | b :: rest, ih =>
      obtain ⟨h1, h2⟩ := ih (i + 1)
      simp only [flat] at h1
      simp only [edgesGo, edgeTriples, flat, List.flatMap_cons, ETree.leaves, h1,
        List.singleton_append, List.mem_cons, forall_eq_or_imp, ETree.WF, true_and]
      exact h2

theorem length_edgeTriples (a₀ : NPt) (i : ℕ) (l : List NPt) :
    (edgeTriples a₀ i l).length = l.length := by
  induction l generalizing i with
  | nil => simp [edgeTriples]
  | cons a l ih =>
    match l, ih with
    | [], _ => simp [edgeTriples]
    | b :: rest, ih => simp only [edgeTriples, List.length_cons] at ih ⊢; rw [ih]

theorem getElem_edgeTriples (a₀ : NPt) (i : ℕ) (l : List NPt) (k : ℕ)
    (hk : k < (edgeTriples a₀ i l).length) :
    (edgeTriples a₀ i l)[k] = (i + k, (l ++ [a₀]).getD k (0, 0), (l ++ [a₀]).getD (k + 1) (0, 0)) := by
  induction l generalizing i k with
  | nil => simp [edgeTriples] at hk
  | cons a l ih =>
    match l, ih with
    | [], _ =>
      simp only [edgeTriples, List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      simp [edgeTriples]
    | b :: rest, ih =>
      cases k with
      | zero => simp [edgeTriples]
      | succ k =>
        simp only [edgeTriples, List.length_cons] at hk
        simp only [edgeTriples, List.getElem_cons_succ]
        rw [ih (i + 1) k (by simpa [length_edgeTriples] using hk)]
        simp only [List.cons_append, List.getD_cons_succ]
        refine Prod.ext ?_ rfl
        simp only; omega

/-! ### Corners -/

/-- All corners `(vₖ, vₖ₊₁, vₖ₊₂)` of a closed chain whose two first vertices are `a₀ a₁`. -/
def triplesGo (a₀ a₁ : NPt) : List NPt → Bool
  | a :: b :: c :: rest => tripleOK a b c && triplesGo a₀ a₁ (b :: c :: rest)
  | [a, b] => tripleOK a b a₀ && tripleOK b a₀ a₁
  | _ => true

theorem triplesGo_sound (a₀ a₁ : NPt) (l : List NPt) (hl : 2 ≤ l.length)
    (h : triplesGo a₀ a₁ l = true) : ∀ k < l.length,
      tripleOK ((l ++ [a₀, a₁]).getD k (0, 0)) ((l ++ [a₀, a₁]).getD (k + 1) (0, 0))
        ((l ++ [a₀, a₁]).getD (k + 2) (0, 0)) = true := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    match l, ih, hl, h with
    | [b], _, _, h =>
      simp only [triplesGo, Bool.and_eq_true] at h
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using h.1
      · simpa using h.2
    | b :: c :: rest, ih, _, h =>
      simp only [triplesGo, Bool.and_eq_true] at h
      intro k hk
      cases k with
      | zero => simpa using h.1
      | succ k =>
        have := ih (by simp) h.2 k (by simp only [List.length_cons] at hk ⊢; omega)
        simpa [List.getD_cons_succ] using this

/-! ### The simplicity check -/

/-- **The simplicity check** for a polygon with natural vertex coordinates: at least three
vertices, every corner passes `tripleOK`, and every pair of non-consecutive edges is separated
(dual-tree traversal of the edge tree). -/
def simpleCheckN (V : List NPt) : Bool :=
  match V with
  | a₀ :: a₁ :: _ :: _ =>
    triplesGo a₀ a₁ V && selfT V.length (build V (edgesGo a₀ 0 V))
  | _ => false

/-- Vertices of the polygon of a natural list. -/
theorem vtx_map_natPoint (V : List NPt) (i : ℕ) :
    (Polygon.mk (V.map natPoint)).vtx i = natPoint (V.getD i (0, 0)) := by
  unfold Polygon.vtx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases V[i]? with
  | none => simp
  | some a => simp

theorem n_map_natPoint (V : List NPt) : (Polygon.mk (V.map natPoint)).n = V.length := by
  simp [Polygon.n]

/-- The polygon's edge `i` as the segment of the edge triple. -/
theorem edge_map_natPoint (V : List NPt) (i : ℕ) :
    (Polygon.mk (V.map natPoint)).edge i =
      ArtGallery.segment (natPoint (V.getD i (0, 0)))
        (natPoint (V.getD ((i + 1) % V.length) (0, 0))) := by
  simp only [Polygon.edge, vtx_map_natPoint, n_map_natPoint]

/-- The facts extracted from a successful check, in index form. -/
theorem simpleCheckN_spec {V : List NPt} (h : simpleCheckN V = true) :
    3 ≤ V.length ∧
    (∀ i < V.length, tripleOK (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0))
      (V.getD ((i + 2) % V.length) (0, 0)) = true) ∧
    (∀ i j, i < j → j < V.length → ¬ (j = i + 1 ∨ (i = 0 ∧ j + 1 = V.length)) →
      Disjoint
        (ArtGallery.segment (natPoint (V.getD i (0, 0)))
          (natPoint (V.getD ((i + 1) % V.length) (0, 0))))
        (ArtGallery.segment (natPoint (V.getD j (0, 0)))
          (natPoint (V.getD ((j + 1) % V.length) (0, 0))))) := by
  match V, h with
  | a₀ :: a₁ :: a₂ :: rest, h =>
    have h' : triplesGo a₀ a₁ (a₀ :: a₁ :: a₂ :: rest) = true ∧
        selfT (a₀ :: a₁ :: a₂ :: rest).length
          (build (a₀ :: a₁ :: a₂ :: rest) (edgesGo a₀ 0 (a₀ :: a₁ :: a₂ :: rest))) = true := by
      simpa only [simpleCheckN, Bool.and_eq_true] using h
    obtain ⟨ht, hs⟩ := h'
    generalize hV : a₀ :: a₁ :: a₂ :: rest = V at ht hs
    have hn : 3 ≤ V.length := by simp [← hV]
    have h0 : V.getD 0 (0, 0) = a₀ := by simp [← hV]
    have h1 : V.getD 1 (0, 0) = a₁ := by simp [← hV]
    refine ⟨hn, ?_, ?_⟩
    · intro i hi
      have := triplesGo_sound a₀ a₁ V (by omega) ht i hi
      -- the extended list agrees with `V` read cyclically
      have key : ∀ k, k < V.length + 2 →
          (V ++ [a₀, a₁]).getD k (0, 0) = V.getD (k % V.length) (0, 0) := by
        intro k hk
        by_cases hkn : k < V.length
        · rw [getD_append_left' hkn, Nat.mod_eq_of_lt hkn]
        · rw [getD_append_right' (by omega)]
          rcases (show k = V.length ∨ k = V.length + 1 by omega) with rfl | rfl
          · rw [Nat.sub_self, Nat.mod_self, h0]; rfl
          · rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < V.length),
              show V.length + 1 - V.length = 1 by omega, h1]; rfl
      rw [key i (by omega), key (i + 1) (by omega), key (i + 2) (by omega),
        Nat.mod_eq_of_lt hi] at this
      exact this
    · intro i j hij hj hna
      have hne : edgesGo a₀ 0 V ≠ [] := by
        intro he; have := length_edgesGo a₀ 0 V; rw [he] at this; simp at this; omega
      obtain ⟨hwf, hleaves⟩ := build_spec V (edgesGo a₀ 0 V) hne
        (by rw [length_edgesGo]; omega) (flat_edgesGo a₀ 0 V).2
      have hp := selfT_sound hwf hs
      rw [hleaves, (flat_edgesGo a₀ 0 V).1, List.pairwise_iff_getElem] at hp
      have hlen := length_edgeTriples a₀ 0 V
      have := hp i j (by omega) (by omega) hij
      rw [getElem_edgeTriples, getElem_edgeTriples] at this
      rcases this with ha | hd
      · simp only [zero_add] at ha
        exact absurd (adj_iff.1 ha) hna
      · simp only [segOf] at hd
        have e : ∀ k < V.length, (V ++ [a₀]).getD (k + 1) (0, 0) =
            V.getD ((k + 1) % V.length) (0, 0) := by
          intro k hk
          by_cases hk1 : k + 1 < V.length
          · rw [getD_append_left' hk1, Nat.mod_eq_of_lt hk1]
          · have : k + 1 = V.length := by omega
            rw [getD_append_right' (by omega), this, Nat.mod_self, Nat.sub_self, h0]; rfl
        rw [getD_append_left' (by omega), getD_append_left' hj, e i (by omega), e j hj] at hd
        exact hd

/-- **Soundness of the simplicity check.** -/
theorem simple_of_simpleCheckN {V : List NPt} (h : simpleCheckN V = true) :
    (Polygon.mk (V.map natPoint)).Simple := by
  obtain ⟨h3, htri, hsep⟩ := simpleCheckN_spec h
  have hvtx : ∀ k, (Polygon.mk (V.map natPoint)).vtx k = natPoint (V.getD k (0, 0)) :=
    vtx_map_natPoint V
  have hN : (Polygon.mk (V.map natPoint)).n = V.length := n_map_natPoint V
  -- consecutive edges
  have hadj1 : ∀ i, i + 1 < V.length → ∀ p, p ∈ (Polygon.mk (V.map natPoint)).edge i →
      p ∈ (Polygon.mk (V.map natPoint)).edge (i + 1) → p = natPoint (V.getD (i + 1) (0, 0)) := by
    intro i hi p h1 h2
    have ht := htri i (by omega)
    rw [Nat.mod_eq_of_lt hi] at ht
    rw [edge_map_natPoint, Nat.mod_eq_of_lt hi] at h1
    rw [edge_map_natPoint] at h2
    exact eq_of_tripleOK ht h1 h2
  have hadj2 : ∀ p, p ∈ (Polygon.mk (V.map natPoint)).edge (V.length - 1) →
      p ∈ (Polygon.mk (V.map natPoint)).edge 0 → p = natPoint (V.getD 0 (0, 0)) := by
    intro p h1 h2
    have ht := htri (V.length - 1) (by omega)
    have e1 : (V.length - 1 + 1) % V.length = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    have e2 : (V.length - 1 + 2) % V.length = 1 := by
      rw [show V.length - 1 + 2 = 1 + V.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2] at ht
    rw [edge_map_natPoint, e1] at h1
    rw [edge_map_natPoint, Nat.mod_eq_of_lt (by omega : 0 + 1 < V.length)] at h2
    exact eq_of_tripleOK ht h1 h2
  -- non-consecutive edges
  have hfar : ∀ i j, i < j → j < V.length → ¬ (j = i + 1 ∨ (i = 0 ∧ j + 1 = V.length)) →
      Disjoint ((Polygon.mk (V.map natPoint)).edge i) ((Polygon.mk (V.map natPoint)).edge j) := by
    intro i j hij hj hna
    rw [edge_map_natPoint, edge_map_natPoint]
    exact hsep i j hij hj hna
  refine ⟨by rw [hN]; exact h3, ?_, ?_⟩
  · -- distinct vertices
    have key : ∀ i j, i < j → j < V.length → V.getD i (0, 0) ≠ V.getD j (0, 0) := by
      intro i j hij hj he
      by_cases h1 : j = i + 1
      · subst h1
        have := ne_of_tripleOK (htri i (by omega))
        rw [Nat.mod_eq_of_lt hj] at this
        exact this he
      · by_cases h2 : i = 0 ∧ j + 1 = V.length
        · obtain ⟨rfl, hj'⟩ := h2
          have := ne_of_tripleOK (htri j hj)
          rw [hj', Nat.mod_self] at this
          exact this he.symm
        · have hd := hfar i j hij hj (by tauto)
          have m1 : natPoint (V.getD i (0, 0)) ∈ (Polygon.mk (V.map natPoint)).edge i := by
            rw [edge_map_natPoint]; exact left_mem_segment _ _
          have m2 : natPoint (V.getD i (0, 0)) ∈ (Polygon.mk (V.map natPoint)).edge j := by
            rw [edge_map_natPoint, he]; exact left_mem_segment _ _
          exact Set.disjoint_left.1 hd m1 m2
    intro i j hi hj he
    rw [hN] at hi hj
    rw [hvtx, hvtx] at he
    have he' := natPoint_injective he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i j hlt hj he'
    · exact key j i hlt hi he'.symm
  · -- edges meet exactly in common endpoints
    have half : ∀ i j, i < j → j < V.length →
        (Polygon.mk (V.map natPoint)).edge i ∩ (Polygon.mk (V.map natPoint)).edge j ⊆
          (Polygon.mk (V.map natPoint)).commonEndpoints i j := by
      intro i j hij hj p ⟨h1, h2⟩
      simp only [Polygon.commonEndpoints, hN, mem_ofPred_eq]
      by_cases ha : j = i + 1
      · subst ha
        have := hadj1 i hj p h1 h2
        rw [hvtx, hvtx, hvtx, Nat.mod_eq_of_lt hj]
        exact ⟨Or.inr this, Or.inl this⟩
      · by_cases hb : i = 0 ∧ j + 1 = V.length
        · obtain ⟨rfl, hj'⟩ := hb
          have hj1 : j = V.length - 1 := by omega
          subst hj1
          have := hadj2 p h2 h1
          rw [hvtx, hvtx, hvtx, hvtx, Nat.sub_add_cancel (by omega), Nat.mod_self]
          exact ⟨Or.inl this, Or.inr this⟩
        · exact absurd h2 (Set.disjoint_left.1 (hfar i j hij hj (by tauto)) h1)
    intro i j hi hj hij
    rw [hN] at hi hj
    apply Subset.antisymm
    · rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact half i j hlt hj
      · rw [inter_comm]
        intro p hp
        have := half j i hlt hi hp
        simp only [Polygon.commonEndpoints, mem_ofPred_eq] at this ⊢
        exact ⟨this.2, this.1⟩
    · rintro p ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with rfl | rfl
        · exact left_mem_segment _ _
        · exact right_mem_segment _ _
      · rcases h2 with rfl | rfl
        · exact left_mem_segment _ _
        · exact right_mem_segment _ _

end ArtGallery.Vis.Cert

end
