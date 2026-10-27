module

public import ArtGallery.Stade.RegionGen

/-!
# The convex pieces of the gadget templates (proof plan L2.3)

For every gadget kind `k`, `fineP k` lists the convex pieces of a slot below the floor as
template polygons (vertices `(x, y₀, d) : RPt` standing for `(G + x, y₀ − d·H)`), with every point
where another piece or a wall of the polygon meets a side inserted as a vertex (so that pieces are
glued exactly along whole sides).  `coarseP k` lists the same pieces without the inserted
vertices; they are the pieces `slotPieces k G H` of `ArtGallery/Stade/GuardSlots.lean`.

The following facts are checked by `decide +kernel` on the fixed template data, robustly for all
`H ≥ 1000` (determinants are affine in `H`):
* `tmplP_piece`: every fine and coarse piece is a convex piece;
* `tmplP_same`: corresponding fine and coarse pieces have the same vertices up to inserted points
  (each lies in the other);
* `tmplP_sep`: every edge of every floor feature of the slot misses the interior of every piece
  (it lies weakly outside one of its sides);
* `tmplP_cover`: every edge of a floor feature lies in some piece;
* `tmplP_sides`: every side of every piece is an edge of a floor feature (a wall), or glued
  to a side of another piece, or the mouth `(last, first)` of a floor feature;
* `tmplP_wall`, `tmplP_vtx`, `tmplP_mouth`: every piece has a wall, every vertex is a vertex of a
  floor feature, and every floor feature has its mouth as a side of a piece.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set ArtGallery.Stade.Chain ArtGallery.Irrational

/-! ### Realizing template points -/

/-- A template point realized with slot origin `G` and needle depth `H`. -/
def realize (G H : ℝ) (p : RPt) : Point := (G + p.1, p.2.1 - p.2.2 * H)

/-- A template polygon realized with slot origin `G` and needle depth `H`. -/
def rpoly (G H : ℝ) (l : List RPt) : Polygon := ⟨l.map (realize G H)⟩

theorem det_realize (G H : ℝ) (a b c : RPt) :
    det (realize G H a) (realize G H b) (realize G H c) =
      ((rdetA a b c : ℚ) : ℝ) + ((rdetB a b c : ℚ) : ℝ) * H := by
  simp only [det, realize, rdetA, rdetB]; push_cast; ring

/-- The rational vertex of `poly` is the realized template point. -/
theorem ratPoint_inst (H g : ℚ) (p : RPt) : ratPoint (p.inst H g) = realize (g : ℝ) (H : ℝ) p := by
  simp only [ratPoint, RPt.inst, realize]; push_cast; ring_nf

/-- Robust nonnegativity of `α + β H` for all `H ≥ H₀`. -/
def rnnB (H₀ α β : ℚ) : Bool := decide (0 ≤ α + β * H₀) && decide (0 ≤ β)

theorem rnn_sound {H₀ α β : ℚ} {H : ℝ} (h : rnnB H₀ α β = true) (hH : (H₀ : ℝ) ≤ H) :
    0 ≤ (α : ℝ) + (β : ℝ) * H := by
  simp only [rnnB, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : (0 : ℝ) ≤ α + β * H₀ := by exact_mod_cast h.1
  have h2 : (0 : ℝ) ≤ β := by exact_mod_cast h.2
  nlinarith [mul_nonneg h2 (sub_nonneg.2 hH)]

theorem rpos_sound' {H₀ α β : ℚ} {H : ℝ} (h : rposB H₀ α β = true) (hH : (H₀ : ℝ) ≤ H) :
    0 < (α : ℝ) + (β : ℝ) * H := by
  simp only [rposB, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : (0 : ℝ) < α + β * H₀ := by exact_mod_cast h.1
  have h2 : (0 : ℝ) ≤ β := by exact_mod_cast h.2
  nlinarith [mul_nonneg h2 (sub_nonneg.2 hH)]

/-- Vertex `j` of a template polygon. -/
def cur (l : List RPt) (j : ℕ) : RPt := l.getD j 0

/-- The successor of vertex `j` of a template polygon. -/
def nxt (l : List RPt) (j : ℕ) : RPt := l.getD ((j + 1) % l.length) 0

theorem rpoly_n (G H : ℝ) (l : List RPt) : (rpoly G H l).n = l.length := by
  simp [rpoly, Polygon.n]

theorem rpoly_vtx (G H : ℝ) (l : List RPt) {j : ℕ} (hj : j < l.length) :
    (rpoly G H l).vtx j = realize G H (cur l j) := by
  simp only [rpoly, Polygon.vtx, cur]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem rpoly_vtx_succ (G H : ℝ) (l : List RPt) {j : ℕ} (hj : j < l.length) :
    (rpoly G H l).vtx ((j + 1) % (rpoly G H l).n) = realize G H (nxt l j) := by
  rw [rpoly_n, rpoly_vtx G H l (Nat.mod_lt _ (by omega))]
  rfl

/-- `p` lies robustly weakly left of every side of `l`. -/
def inB (l : List RPt) (p : RPt) : Bool :=
  (List.range l.length).all fun j => rnnB 1000 (rdetA (cur l j) (nxt l j) p) (rdetB (cur l j) (nxt l j) p)

/-- The average of the vertices (a candidate center). -/
def avgR (l : List RPt) : RPt :=
  ((l.map (·.1)).sum / l.length, (l.map (·.2.1)).sum / l.length, (l.map (·.2.2)).sum / l.length)

/-- `l` is robustly a convex piece. -/
def pieceB (l : List RPt) : Bool :=
  decide (3 ≤ l.length) && l.all (inB l) &&
    (List.range l.length).all fun j =>
      rposB 1000 (rdetA (cur l j) (nxt l j) (avgR l)) (rdetB (cur l j) (nxt l j) (avgR l))

/-- The segment `a b` lies robustly weakly right of some side of `l`. -/
def sepB (l : List RPt) (a b : RPt) : Bool :=
  (List.range l.length).any fun j =>
    rnnB 1000 (-rdetA (cur l j) (nxt l j) a) (-rdetB (cur l j) (nxt l j) a) &&
      rnnB 1000 (-rdetA (cur l j) (nxt l j) b) (-rdetB (cur l j) (nxt l j) b)

variable {G H : ℝ}

theorem inB_sound (hH : 1000 ≤ H) {l : List RPt} {p : RPt} (h : inB l p = true) :
    realize G H p ∈ piece (rpoly G H l) := by
  intro j hj
  rw [rpoly_n] at hj
  rw [rpoly_vtx G H l hj, rpoly_vtx_succ G H l hj, det_realize]
  simp only [inB, List.all_eq_true, List.mem_range] at h
  exact rnn_sound (h j hj) (by norm_num; linarith)

theorem pieceB_sound (hH : 1000 ≤ H) {l : List RPt} (h : pieceB l = true) :
    IsPiece (rpoly G H l) ∧ 3 ≤ (rpoly G H l).n := by
  simp only [pieceB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h3, hin⟩, hc⟩ := h
  refine ⟨⟨fun j hj k hk => ?_, ⟨realize G H (avgR l), fun j hj => ?_⟩⟩, by rw [rpoly_n]; exact h3⟩
  · rw [rpoly_n] at hj hk
    have := inB_sound (G := G) hH (hin _ (List.getElem_mem hk))
    rw [rpoly_vtx G H l hk]
    have e : cur l k = l[k] := by simp [cur, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rw [e]
    exact this j (by rw [rpoly_n]; exact hj)
  · rw [rpoly_n] at hj
    rw [rpoly_vtx G H l hj, rpoly_vtx_succ G H l hj, det_realize]
    exact rpos_sound' (hc j hj) (by norm_num; linarith)

theorem sepB_sound (hH : 1000 ≤ H) {l : List RPt} (hl : pieceB l = true) {a b : RPt}
    (h : sepB l a b = true) :
    Disjoint (interior (piece (rpoly G H l))) (segment (realize G H a) (realize G H b)) := by
  simp only [sepB, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨j, hj, h1, h2⟩ := h
  have hK := (pieceB_sound (G := G) hH hl).1
  have hj' : j < (rpoly G H l).n := by rw [rpoly_n]; exact hj
  refine disjoint_interior_of_side hK hj' ?_ ?_
  · rw [rpoly_vtx G H l hj, rpoly_vtx_succ G H l hj, det_realize]
    have := rnn_sound h1 (H := H) (by norm_num; linarith)
    push_cast at this; linarith
  · rw [rpoly_vtx G H l hj, rpoly_vtx_succ G H l hj, det_realize]
    have := rnn_sound h2 (H := H) (by norm_num; linarith)
    push_cast at this; linarith

/-- Two robust pieces with each vertex of one in the other have the same points. -/
theorem piece_eq_of_inB (hH : 1000 ≤ H) {l l' : List RPt} (hl : pieceB l = true)
    (hl' : pieceB l' = true) (h1 : l.all (inB l') = true) (h2 : l'.all (inB l) = true) :
    piece (rpoly G H l) = piece (rpoly G H l') := by
  have sub : ∀ {l l' : List RPt}, pieceB l = true → l.all (inB l') = true →
      piece (rpoly G H l) ⊆ piece (rpoly G H l') := by
    intro l l' hl h y hy j hj
    obtain ⟨hK, hn⟩ := pieceB_sound (G := G) hH hl
    have hv : ∀ k < (rpoly G H l).n,
        0 ≤ det ((rpoly G H l').vtx j) ((rpoly G H l').vtx ((j + 1) % (rpoly G H l').n))
          ((rpoly G H l).vtx k) := by
      intro k hk
      rw [rpoly_n] at hk
      simp only [List.all_eq_true] at h
      have := inB_sound (G := G) hH (h _ (List.getElem_mem hk)) j hj
      rw [rpoly_vtx G H l hk]
      have e : cur l k = l[k] := by
        simp [cur, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rw [e]; exact this
    set a := (rpoly G H l').vtx j
    set b := (rpoly G H l').vtx ((j + 1) % (rpoly G H l').n)
    have := piece_aff_nonneg hK (by omega) (α := -(b.2 - a.2)) (β := b.1 - a.1)
      (γ := (b.2 - a.2) * a.1 - (b.1 - a.1) * a.2)
      (fun k hk => by have := hv k hk; simp only [det] at this; linarith) hy
    show 0 ≤ det a b y
    simp only [det]; linarith
  exact Set.Subset.antisymm (sub hl h1) (sub hl' h2)

/-! ### Pairs of consecutive entries -/

/-- The consecutive pairs of a list. -/
def pairs {α : Type} (l : List α) : List (α × α) := l.zip l.tail

theorem infix_of_mem_pairs {α : Type} : ∀ {l : List α} {a b : α}, (a, b) ∈ pairs l → [a, b] <:+: l
  | x :: y :: l, a, b, h => by
    simp only [pairs, List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨[], l, rfl⟩
    · exact (infix_of_mem_pairs (l := y :: l) (by simpa [pairs] using h)).trans
        (List.infix_cons (List.infix_refl _))
  | [], _, _, h => by simp [pairs] at h
  | [_], _, _, h => by simp [pairs] at h

theorem mem_pairs_of_lt {α : Type} : ∀ (l : List α) (j : ℕ) (hj : j + 1 < l.length),
    (l[j], l[j + 1]) ∈ pairs l
  | x :: y :: l, 0, _ => by simp [pairs]
  | x :: y :: l, j + 1, hj => by
    have := mem_pairs_of_lt (y :: l) j (by simp at hj ⊢; omega)
    simp only [pairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at this ⊢
    exact Or.inr (by simpa using this)

/-- The chain of a list of points is the union of the segments of its consecutive pairs. -/
theorem chainSet_subset_pairs {S : Set Point} :
    ∀ (l : List Point), (∀ a b, (a, b) ∈ pairs l → segment a b ⊆ S) → chainSet l ⊆ S
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [chainSet_cons_cons]
    refine union_subset (h a b (by simp [pairs])) (chainSet_subset_pairs (b :: l) fun x y hxy =>
      h x y ?_)
    simp only [pairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hxy ⊢
    exact Or.inr (by simpa using hxy)

theorem pairs_map {α β : Type} (f : α → β) :
    ∀ l : List α, pairs (l.map f) = (pairs l).map (fun p => (f p.1, f p.2))
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have := pairs_map f (b :: l)
    simp only [pairs, List.map_cons, List.tail_cons, List.zip_cons_cons] at this ⊢
    rw [this]

/-! ### The template pieces -/

/-- The fine pieces of a slot (with all junction points as vertices). -/
def fineP : TKind → List (List RPt)
  | .invGe =>
    [[(159 / 4, -1, 0), (40, -1, 1), (40, -1, 0)],
     [(81 / 2, -1, 0), (43, -6, 0), (97, -6, 0), (199 / 2, -1, 0)],
     [(79, -78, 0), (97, -6, 0), (43, -6, 0), (61, -78, 0)],
     [(100, -1, 0), (100, -1, 1), (401 / 4, -1, 0)]]
  | .invRevLe =>
    [[(59, -1, 0), (80, -8, 0), (101, -1, 0)],
     [(56, -22, 0), (60, -59 / 3, 0), (241 / 4, -937 / 48, 0), (80, -8, 0), (59, -1, 0),
       (38, -22, 0)],
     [(60, -59 / 3, 0), (60, -59 / 3, 1), (241 / 4, -937 / 48, 0)],
     [(104, -1, 0), (104, -1, 1), (417 / 4, -1, 0)]]
  | .addLe =>
    [[(200, -1, 0), (50, -445 / 4, 0), (50, -113, 0), (50, -118, 0), (50, -2994 / 25, 0),
       (50, -491 / 4, 0), (50, -128, 0), (439 / 4, -128, 0), (441 / 4, -128, 0), (210, -128, 0),
       (841 / 4, -128, 0), (370, -128, 0), (1481 / 4, -128, 0), (527, -128, 0), (527, -1, 0)],
     [(30, -7589 / 64, 0), (50, -113, 0), (50, -445 / 4, 0), (30, -7561 / 64, 0)],
     [(30, -4443 / 32, 0), (50, -128, 0), (50, -491 / 4, 0), (30, -4417 / 32, 0)],
     [(30, -2001 / 16, 0), (50, -2994 / 25, 0), (50, -118, 0), (30, -499 / 4, 0)],
     [(439 / 4, -128, 0), (110, -519 / 4, 0), (441 / 4, -128, 0)],
     [(210, -128, 0), (210, -128, 1), (841 / 4, -128, 0)],
     [(370, -128, 0), (370, -128, 1), (1481 / 4, -128, 0)],
     [(530, -1, 0), (530, -1, 1), (2121 / 4, -1, 0)]]
  | .addGe =>
    [[(85, -1, 0), (50, -37, 0), (50, -153 / 4, 0), (50, -151 / 3, 0), (50, -77, 0),
       (50, -94, 0), (327 / 4, -94, 0), (329 / 4, -94, 0), (185 / 2, -94, 0), (371 / 4, -94, 0),
       (210, -94, 0), (841 / 4, -94, 0), (363, -94, 0), (363, -1, 0)],
     [(50, -153 / 4, 0), (65 / 2, -5977 / 100, 0), (50, -151 / 3, 0)],
     [(30, -2649 / 64, 0), (50, -153 / 4, 0), (50, -37, 0), (30, -2601 / 64, 0)],
     [(30, -855 / 8, 0), (50, -94, 0), (50, -77, 0), (30, -423 / 4, 0)],
     [(30, -6001 / 96, 0), (50, -151 / 3, 0), (65 / 2, -5977 / 100, 0), (30, -5941 / 96, 0)],
     [(327 / 4, -94, 0), (82, -113, 0), (329 / 4, -94, 0)],
     [(185 / 2, -94, 0), (185 / 2, -94, 1), (371 / 4, -94, 0)],
     [(210, -94, 0), (210, -94, 1), (841 / 4, -94, 0)],
     [(370, -1, 0), (370, -1, 1), (1481 / 4, -1, 0)]]

/-- The coarse pieces of a slot (the pieces `slotPieces`). -/
def coarseP : TKind → List (List RPt)
  | .invGe => fineP .invGe
  | .invRevLe =>
    [[(59, -1, 0), (80, -8, 0), (101, -1, 0)],
     [(56, -22, 0), (80, -8, 0), (59, -1, 0), (38, -22, 0)],
     [(60, -59 / 3, 0), (60, -59 / 3, 1), (241 / 4, -937 / 48, 0)],
     [(104, -1, 0), (104, -1, 1), (417 / 4, -1, 0)]]
  | .addLe =>
    [[(200, -1, 0), (50, -445 / 4, 0), (50, -128, 0), (527, -128, 0), (527, -1, 0)],
     [(30, -7589 / 64, 0), (50, -113, 0), (50, -445 / 4, 0), (30, -7561 / 64, 0)],
     [(30, -4443 / 32, 0), (50, -128, 0), (50, -491 / 4, 0), (30, -4417 / 32, 0)],
     [(30, -2001 / 16, 0), (50, -2994 / 25, 0), (50, -118, 0), (30, -499 / 4, 0)],
     [(439 / 4, -128, 0), (110, -519 / 4, 0), (441 / 4, -128, 0)],
     [(210, -128, 0), (210, -128, 1), (841 / 4, -128, 0)],
     [(370, -128, 0), (370, -128, 1), (1481 / 4, -128, 0)],
     [(530, -1, 0), (530, -1, 1), (2121 / 4, -1, 0)]]
  | .addGe =>
    [[(85, -1, 0), (50, -37, 0), (50, -94, 0), (363, -94, 0), (363, -1, 0)],
     [(50, -153 / 4, 0), (65 / 2, -5977 / 100, 0), (50, -151 / 3, 0)],
     [(30, -2649 / 64, 0), (50, -153 / 4, 0), (50, -37, 0), (30, -2601 / 64, 0)],
     [(30, -855 / 8, 0), (50, -94, 0), (50, -77, 0), (30, -423 / 4, 0)],
     [(30, -6001 / 96, 0), (50, -151 / 3, 0), (65 / 2, -5977 / 100, 0), (30, -5941 / 96, 0)],
     [(327 / 4, -94, 0), (82, -113, 0), (329 / 4, -94, 0)],
     [(185 / 2, -94, 0), (185 / 2, -94, 1), (371 / 4, -94, 0)],
     [(210, -94, 0), (210, -94, 1), (841 / 4, -94, 0)],
     [(370, -1, 0), (370, -1, 1), (1481 / 4, -1, 0)]]

/-- Side `(a, b)` is an edge of a floor feature of the template. -/
def wallB (k : TKind) (a b : RPt) : Bool := (tmplFloor k).any fun ch => decide ((a, b) ∈ pairs ch)

/-- Side `(a, b)` is glued to a side `(b, a)` of a fine piece. -/
def glueB (k : TKind) (a b : RPt) : Bool :=
  (fineP k).any fun K' => (List.range K'.length).any fun j' =>
    decide (cur K' j' = b) && decide (nxt K' j' = a)

/-- Side `(a, b)` is the mouth `(last, first)` of a floor feature. -/
def mouthB (k : TKind) (a b : RPt) : Bool :=
  (tmplFloor k).any fun ch => decide (a = ch.getLastD 0) && decide (b = ch.headD 0)

/-- **The template checks.** -/
def tmplOK (k : TKind) : Bool :=
  (fineP k).all pieceB && (coarseP k).all pieceB &&
  decide ((fineP k).length = (coarseP k).length) &&
  ((fineP k).zip (coarseP k)).all (fun q => q.1.all (inB q.2) && q.2.all (inB q.1)) &&
  (fineP k).all (fun K => (tmplFloor k).all fun ch => (pairs ch).all fun e => sepB K e.1 e.2) &&
  (tmplFloor k).all (fun ch => (pairs ch).all fun e =>
    (fineP k).any fun K => inB K e.1 && inB K e.2) &&
  (fineP k).all (fun K => (List.range K.length).all fun j =>
    wallB k (cur K j) (nxt K j) || glueB k (cur K j) (nxt K j) || mouthB k (cur K j) (nxt K j)) &&
  (fineP k).all (fun K => (List.range K.length).any fun j => wallB k (cur K j) (nxt K j)) &&
  (fineP k).all (fun K => K.all fun v => (tmplFloor k).any fun ch => decide (v ∈ ch)) &&
  (tmplFloor k).all (fun ch => (fineP k).any fun K => (List.range K.length).any fun j =>
    decide (cur K j = ch.getLastD 0) && decide (nxt K j = ch.headD 0))

theorem tmplOK_all : allKinds.all tmplOK = true := by decide +kernel

/-! ### The checks, unpacked -/

section Unpack

variable (k : TKind)

theorem tmplOK_k : tmplOK k = true := List.all_eq_true.1 tmplOK_all k (mem_allKinds k)

theorem tmplOK_parts :
    (fineP k).all pieceB = true ∧ (coarseP k).all pieceB = true ∧
    (fineP k).length = (coarseP k).length ∧
    ((fineP k).zip (coarseP k)).all (fun q => q.1.all (inB q.2) && q.2.all (inB q.1)) = true ∧
    (fineP k).all (fun K => (tmplFloor k).all fun ch => (pairs ch).all fun e =>
      sepB K e.1 e.2) = true ∧
    (tmplFloor k).all (fun ch => (pairs ch).all fun e =>
      (fineP k).any fun K => inB K e.1 && inB K e.2) = true ∧
    (fineP k).all (fun K => (List.range K.length).all fun j =>
      wallB k (cur K j) (nxt K j) || glueB k (cur K j) (nxt K j) ||
        mouthB k (cur K j) (nxt K j)) = true ∧
    (fineP k).all (fun K => (List.range K.length).any fun j =>
      wallB k (cur K j) (nxt K j)) = true ∧
    (fineP k).all (fun K => K.all fun v => (tmplFloor k).any fun ch => decide (v ∈ ch)) = true ∧
    (tmplFloor k).all (fun ch => (fineP k).any fun K => (List.range K.length).any fun j =>
      decide (cur K j = ch.getLastD 0) && decide (nxt K j = ch.headD 0)) = true := by
  have h := tmplOK_k k
  simp only [tmplOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

variable {k}

theorem tP_piece {K : List RPt} (hK : K ∈ fineP k) : pieceB K = true :=
  List.all_eq_true.1 (tmplOK_parts k).1 K hK

theorem tP_cpiece {K : List RPt} (hK : K ∈ coarseP k) : pieceB K = true :=
  List.all_eq_true.1 (tmplOK_parts k).2.1 K hK

theorem tP_len : (fineP k).length = (coarseP k).length := (tmplOK_parts k).2.2.1

theorem tP_same {i : ℕ} (hi : i < (fineP k).length) :
    ((fineP k)[i]).all (inB ((coarseP k)[i]'(by rw [← tP_len]; exact hi))) = true ∧
      ((coarseP k)[i]'(by rw [← tP_len]; exact hi)).all (inB (fineP k)[i]) = true := by
  have h := List.all_eq_true.1 (tmplOK_parts k).2.2.2.1
    ((fineP k)[i], (coarseP k)[i]'(by rw [← tP_len]; exact hi))
    (List.mem_iff_getElem.2 ⟨i, by simp [hi, ← tP_len], by simp⟩)
  simpa only [Bool.and_eq_true] using h

theorem tP_sep {K : List RPt} (hK : K ∈ fineP k) {ch : List RPt} (hch : ch ∈ tmplFloor k)
    {e : RPt × RPt} (he : e ∈ pairs ch) : sepB K e.1 e.2 = true := by
  have h := (tmplOK_parts k).2.2.2.2.1
  simp only [List.all_eq_true] at h
  exact h K hK ch hch e he

theorem tP_cover {ch : List RPt} (hch : ch ∈ tmplFloor k) {e : RPt × RPt} (he : e ∈ pairs ch) :
    ∃ K ∈ fineP k, inB K e.1 = true ∧ inB K e.2 = true := by
  have h := (tmplOK_parts k).2.2.2.2.2.1
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  exact h ch hch e he

theorem tP_sides {K : List RPt} (hK : K ∈ fineP k) {j : ℕ} (hj : j < K.length) :
    wallB k (cur K j) (nxt K j) = true ∨ glueB k (cur K j) (nxt K j) = true ∨
      mouthB k (cur K j) (nxt K j) = true := by
  have h := (tmplOK_parts k).2.2.2.2.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  rcases h K hK j hj with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem tP_wall {K : List RPt} (hK : K ∈ fineP k) :
    ∃ j < K.length, wallB k (cur K j) (nxt K j) = true := by
  have h := (tmplOK_parts k).2.2.2.2.2.2.2.1
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range] at h
  exact h K hK

theorem tP_vtx {K : List RPt} (hK : K ∈ fineP k) {v : RPt} (hv : v ∈ K) :
    ∃ ch ∈ tmplFloor k, v ∈ ch := by
  have h := (tmplOK_parts k).2.2.2.2.2.2.2.2.1
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h K hK v hv

theorem tP_mouth {ch : List RPt} (hch : ch ∈ tmplFloor k) :
    ∃ K ∈ fineP k, ∃ j < K.length, cur K j = ch.getLastD 0 ∧ nxt K j = ch.headD 0 := by
  have h := (tmplOK_parts k).2.2.2.2.2.2.2.2.2
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h ch hch

theorem wallB_spec {a b : RPt} (h : wallB k a b = true) : ∃ ch ∈ tmplFloor k, [a, b] <:+: ch := by
  simp only [wallB, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨ch, hch, hab⟩ := h
  exact ⟨ch, hch, infix_of_mem_pairs hab⟩

theorem glueB_spec {a b : RPt} (h : glueB k a b = true) :
    ∃ K' ∈ fineP k, ∃ j' < K'.length, cur K' j' = b ∧ nxt K' j' = a := by
  simp only [glueB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem mouthB_spec {a b : RPt} (h : mouthB k a b = true) :
    ∃ ch ∈ tmplFloor k, a = ch.getLastD 0 ∧ b = ch.headD 0 := by
  simp only [mouthB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end Unpack

end ArtGallery.Stade

end
