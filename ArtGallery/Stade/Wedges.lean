module

public import ArtGallery.Stade.SimpleOrient
public import ArtGallery.Stade.Exit

/-!
# Stade's construction: wedge cones and guard regions (proof plan L4.1, L4.2, L4.4)

Notation: `SP n Φ` is the polygon `Polygon.mk ((poly n Φ).map ratPoint)`, `H = paramH n Φ`.

* **Vertices and edges of `SP n Φ`** (`chain_of_infix`, `edge_of_infix`, `corner_of_infix`,
  `list_mem_boundary`): consecutive entries of the vertex list are consecutive vertices; every
  feature of `floorFeats` / `ceilFeats` is a contiguous part of `poly n Φ` (`floor_infix`,
  `ceil_infix`).
* **Strip** (`poly_snd_ge`, `poly_snd_le`, `filled_strip`): the region lies in
  `−H − 140 ≤ y ≤ 4H`.
* **Wedge cones (L4.1)**: a point seeing the tip of a wedge lies in its cone (`sees_corner`); the
  cone of every wedge of a segment region at abscissa `s` meets the strip inside the slab
  `|x − s| ≤ 4` (`slab s`); the viewers of the aux tip of an addition gadget lie in the explicit
  triangle `auxRegion k G` (cone of the aux wedge below the upper-left room wall; the proof uses
  the blocking lemma T1 for that wall).
* **Disjointness (L4.2)**: slabs of distinct segment regions and aux regions are pairwise
  disjoint (`Disjoint` lemmas at the end of the file).
* **Guard positions (L4.4)**: a point seeing the tips of `W1, W2, W3` of a variable lies on the
  segment `{a_k} × [H, H+3]` (`var_position`), at `(a_k, H + 1)` if the variable carries a
  constraint `x = 1` (`var_position_one`); for an input, on `{b} × [0, 6]` (`input_position`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-- Stade's polygon as a `Polygon`. -/
abbrev SP (n : ℕ) (Φ : List Constraint) : Polygon := Polygon.mk ((poly n Φ).map ratPoint)

variable {n : ℕ} {Φ : List Constraint}

/-! ### Vertices, edges and corners of a polygon given by a rational list -/

/-- Vertex `i < length` of the polygon of a rational list. -/
theorem vtx_mk_map (l : List (ℚ × ℚ)) {i : ℕ} (hi : i < l.length) :
    (Polygon.mk (l.map ratPoint)).vtx i = ratPoint l[i] := by
  rw [vtx_map_ratPoint, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- A contiguous part of the vertex list is a run of consecutive vertices (no wrap-around). -/
theorem chain_of_infix {m l : List (ℚ × ℚ)} (h : m <:+: l) :
    ∃ a, a + m.length ≤ l.length ∧ ∀ j (hj : j < m.length),
      (Polygon.mk (l.map ratPoint)).vtx (a + j) = ratPoint m[j] := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨s.length, by simp, fun j hj => ?_⟩
  rw [vtx_mk_map _ (by simp; omega)]
  congr 1
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-- Two consecutive entries of the vertex list form an edge. -/
theorem edge_of_infix {l : List (ℚ × ℚ)} {u v : ℚ × ℚ} (h : [u, v] <:+: l) :
    ∃ i < (Polygon.mk (l.map ratPoint)).n, (Polygon.mk (l.map ratPoint)).vtx i = ratPoint u ∧
      (Polygon.mk (l.map ratPoint)).vtx ((i + 1) % (Polygon.mk (l.map ratPoint)).n) =
        ratPoint v := by
  obtain ⟨a, ha, hv⟩ := chain_of_infix h
  simp only [List.length_cons, List.length_nil] at ha
  have hn : (Polygon.mk (l.map ratPoint)).n = l.length := n_map_ratPoint l
  refine ⟨a, by omega, ?_, ?_⟩
  · simpa using hv 0 (by simp)
  · rw [hn, Nat.mod_eq_of_lt (by omega)]
    simpa using hv 1 (by simp)

/-- Three consecutive entries of the vertex list form a corner (vertex with predecessor and
successor). -/
theorem corner_of_infix {l : List (ℚ × ℚ)} {u v w : ℚ × ℚ} (h : [u, v, w] <:+: l) :
    ∃ i < (Polygon.mk (l.map ratPoint)).n,
      (Polygon.mk (l.map ratPoint)).vtx ((i + (Polygon.mk (l.map ratPoint)).n - 1) %
        (Polygon.mk (l.map ratPoint)).n) = ratPoint u ∧
      (Polygon.mk (l.map ratPoint)).vtx i = ratPoint v ∧
      (Polygon.mk (l.map ratPoint)).vtx ((i + 1) % (Polygon.mk (l.map ratPoint)).n) =
        ratPoint w := by
  obtain ⟨a, ha, hv⟩ := chain_of_infix h
  simp only [List.length_cons, List.length_nil] at ha
  have hn : (Polygon.mk (l.map ratPoint)).n = l.length := n_map_ratPoint l
  refine ⟨a + 1, by omega, ?_, ?_, ?_⟩
  · rw [hn, show a + 1 + l.length - 1 = a + l.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    simpa using hv 0 (by simp)
  · simpa using hv 1 (by simp)
  · rw [hn, Nat.mod_eq_of_lt (by omega)]
    simpa using hv 2 (by simp)

/-- Every entry of the vertex list lies on the boundary. -/
theorem list_mem_boundary {l : List (ℚ × ℚ)} {u : ℚ × ℚ} (h : u ∈ l) :
    ratPoint u ∈ (Polygon.mk (l.map ratPoint)).boundary := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  refine ⟨i, by rw [n_map_ratPoint]; exact hi, 0, le_rfl, zero_le_one, ?_⟩
  rw [vtx_mk_map _ hi]
  simp

/-! ### Features are contiguous parts of `poly n Φ` -/

/-- Every floor feature is a contiguous part of the vertex list. -/
theorem floor_infix {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) : f <:+: poly n Φ := by
  refine (List.infix_of_mem_flatten hf).trans ?_
  unfold poly
  exact ⟨[(xL n Φ, -1)], [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++
    (ceilFeats n Φ).flatten ++ [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩

/-- Every ceiling feature is a contiguous part of the vertex list. -/
theorem ceil_infix {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) : f <:+: poly n Φ := by
  refine (List.infix_of_mem_flatten hf).trans ?_
  unfold poly
  exact ⟨[(xL n Φ, -1)] ++ (floorFeats n Φ).flatten ++
    [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))], [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩

/-- The ceiling wedges of variable `k < n` are ceiling features. -/
theorem varCeil_mem {k : ℕ} (hk : k < n) {f : List (ℚ × ℚ)}
    (hf : f ∈ varCeil (varA Φ k) (hasOne Φ k) (paramH n Φ)) : f ∈ ceilFeats n Φ := by
  simp only [ceilFeats, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, hf⟩)

/-- The ceiling wedges of an input are ceiling features. -/
theorem inputCeil_mem {i : InputSeg} (hi : i ∈ inputs n Φ) {f : List (ℚ × ℚ)}
    (hf : f ∈ inputCeil i.b i.pos (paramH n Φ)) : f ∈ ceilFeats n Φ := by
  simp only [ceilFeats, List.mem_append, List.mem_flatMap, List.mem_reverse]
  exact Or.inl (Or.inl ⟨i, hi, hf⟩)

/-- The copy nook of an input copying variable `k < n` is a ceiling feature. -/
theorem copyNook_mem {i : InputSeg} (hi : i ∈ inputs n Φ) (hk : i.var < n) :
    copyNook (varA Φ i.var) i.b i.ge (paramH n Φ) ∈ ceilFeats n Φ := by
  simp only [ceilFeats, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq]
  exact Or.inr ⟨i.var, hk, i, ⟨hi, rfl⟩, rfl⟩

/-- The floor needle of variable `k < n` is a floor feature. -/
theorem varFloor_mem {k : ℕ} (hk : k < n) :
    needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k)) ∈ floorFeats n Φ := by
  simp only [floorFeats, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl ⟨k, hk, rfl⟩

/-- The floor features of slot `c < C` are floor features. -/
theorem slotFloor_mem {c : ℕ} (hc : c < paramC Φ) {ch : List RPt}
    (hch : ch ∈ tmplFloor (cKind (gadAt Φ c))) :
    ch.map (RPt.inst (paramH n Φ) (slotG n Φ c)) ∈ floorFeats n Φ := by
  simp only [floorFeats, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]
  exact Or.inr ⟨c, hc, ch, hch, rfl⟩

/-! ### The strip `−H − 140 ≤ y ≤ 4H` -/

/-- Ordinates of the template vertices: `y₀ ∈ [−140, −1]`, depth `d ∈ [0, 1]`. -/
theorem tmplFloor_y_ok : allKinds.all (fun k => (tmplFloor k).all (fun ch => ch.all (fun q =>
    decide (-140 ≤ q.2.1 ∧ q.2.1 ≤ -1 ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ 1)))) = true := by
  decide +kernel

theorem tmplFloor_y {k : TKind} {ch : List RPt} (hch : ch ∈ tmplFloor k) {q : RPt}
    (hq : q ∈ ch) : -140 ≤ q.2.1 ∧ q.2.1 ≤ -1 ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ 1 := by
  have := tmplFloor_y_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this k (mem_allKinds k) ch hch q hq

/-- Bounds of `3/(2H−3)`. -/
theorem frac_nook_le {H : ℚ} (hH : 1000 ≤ H) : 0 < 3 / (2 * H - 3) ∧ 3 / (2 * H - 3) ≤ 1 := by
  have h : 0 < 2 * H - 3 := by linarith
  exact ⟨div_pos (by norm_num) h, (div_le_one h).2 (by linarith)⟩

/-- Ordinates of the floor features. -/
theorem floor_snd {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) {p : ℚ × ℚ} (hp : p ∈ f) :
    -(paramH n Φ : ℚ) - 140 ≤ p.2 ∧ p.2 ≤ -1 := by
  have hH := paramH_ge_q n Φ
  rcases mem_floorFeats hf with ⟨k, -, rfl⟩ | ⟨c, -, ch, hch, rfl⟩
  · simp only [needleDownL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, RPt.inst] at hp
    rcases hp with rfl | rfl | rfl <;> constructor <;> norm_num <;> linarith
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3, h4⟩ := tmplFloor_y hch hq
    simp only [RPt.inst]
    constructor <;> nlinarith

/-- Ordinates of the ceiling features. -/
theorem ceil_snd {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) {p : ℚ × ℚ} (hp : p ∈ f) :
    2 * (paramH n Φ : ℚ) ≤ p.2 ∧ p.2 ≤ 4 * (paramH n Φ : ℚ) := by
  have hH := paramH_ge_q n Φ
  set H := (paramH n Φ : ℚ)
  have hW1 : ∀ s pos, ∀ p ∈ wedgeW1 s pos H, 2 * H ≤ p.2 ∧ p.2 ≤ 4 * H := by
    intro s pos p hp
    cases pos <;> simp only [wedgeW1, ↓reduceIte, Bool.false_eq_true, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;> constructor <;> simp <;> linarith
  have hW3 : ∀ s pos T, 2 * H ≤ T → T ≤ 4 * H → ∀ p ∈ wedgeW3 s pos T H,
      2 * H ≤ p.2 ∧ p.2 ≤ 4 * H := by
    intro s pos T h1 h2 p hp
    cases pos <;> simp only [wedgeW3, ↓reduceIte, Bool.false_eq_true, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;> constructor <;> simp <;> linarith
  rcases mem_ceilFeats hf with ⟨i, -, hfi⟩ | ⟨k, -, hfk⟩ | ⟨k, -, i, -, -, rfl⟩
  · cases hpos : i.pos <;> rw [hpos] at hfi <;>
      simp only [inputCeil, ↓reduceIte, Bool.false_eq_true, List.mem_cons,
        List.not_mem_nil, or_false] at hfi
    · rcases hfi with rfl | rfl
      · exact hW3 _ _ _ (by linarith) le_rfl p hp
      · exact hW1 _ _ p hp
    · rcases hfi with rfl | rfl
      · exact hW1 _ _ p hp
      · exact hW3 _ _ _ (by linarith) le_rfl p hp
  · simp only [varCeil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hfk
    rcases hfk with (rfl | rfl) | hfk
    · exact hW1 _ _ p hp
    · exact hW3 _ _ _ (by linarith) (by linarith) p hp
    · split_ifs at hfk
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl <;>
          simp only [wedgeW4, wedgeW5, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
          rcases hp with rfl | rfl | rfl <;> constructor <;> simp <;> linarith
      · simp at hfk
  · have hb := frac_nook_le hH
    cases hge : i.ge <;>
      simp only [copyNook, hge, ↓reduceIte, Bool.false_eq_true, List.mem_cons,
        List.not_mem_nil, or_false, nookPt, nookPs, nookTop, nookBot] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> linarith

/-- Every vertex has ordinate `≥ −H − 140`. -/
theorem poly_snd_ge : ∀ p ∈ poly n Φ, -(paramH n Φ : ℚ) - 140 ≤ p.2 := by
  intro p hp
  have hH := paramH_ge_q n Φ
  simp only [poly, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten] at hp
  rcases hp with (((rfl | ⟨f, hf, hpf⟩) | (rfl | rfl)) | ⟨f, hf, hpf⟩) | rfl
  · simp only; linarith
  · exact (floor_snd hf hpf).1
  · simp only; linarith
  · simp only; linarith
  · linarith [(ceil_snd hf hpf).1]
  · simp only; linarith

/-- Every vertex has ordinate `≤ 4H`. -/
theorem poly_snd_le : ∀ p ∈ poly n Φ, p.2 ≤ 4 * (paramH n Φ : ℚ) := by
  intro p hp
  have hH := paramH_ge_q n Φ
  simp only [poly, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten] at hp
  rcases hp with (((rfl | ⟨f, hf, hpf⟩) | (rfl | rfl)) | ⟨f, hf, hpf⟩) | rfl
  · simp only; linarith
  · linarith [(floor_snd hf hpf).2]
  · simp only; linarith
  · simp only; linarith
  · exact (ceil_snd hf hpf).2
  · simp only; linarith

/-- **The strip (L4.2).** Every point of the region satisfies `−H − 140 ≤ y ≤ 4H`. -/
theorem filled_strip {p : Point} (hp : p ∈ (SP n Φ).filled) :
    -(paramH n Φ : ℝ) - 140 ≤ p.2 ∧ p.2 ≤ 4 * (paramH n Φ : ℝ) := by
  have hmem : ∀ j < (SP n Φ).n, (poly n Φ).getD j 0 ∈ poly n Φ := by
    intro j hj
    rw [n_map_ratPoint] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  constructor
  · refine filled_snd_ge (SP n Φ) (fun j hj => ?_) p hp
    rw [vtx_map_ratPoint, ratPoint_snd]
    have := poly_snd_ge _ (hmem j hj)
    exact_mod_cast this
  · refine filled_snd_le (SP n Φ) (fun j hj => ?_) p hp
    rw [vtx_map_ratPoint, ratPoint_snd]
    have := poly_snd_le _ (hmem j hj)
    exact_mod_cast this

/-! ### Wedge cones -/

/-- **Wedge cone (L4.1).** A point seeing the tip `v` of a convex corner `u, v, w` of the vertex
list lies in the cone: `0 ≤ det u v p` and `0 ≤ det v w p`. -/
theorem sees_corner {u v w : ℚ × ℚ} (h : [u, v, w] <:+: poly n Φ) (hconv : 0 < qdet u v w)
    {p : Point} (hp : (SP n Φ).Sees p (ratPoint v)) :
    0 ≤ det (ratPoint u) (ratPoint v) p ∧ 0 ≤ det (ratPoint v) (ratPoint w) p := by
  obtain ⟨i, hi, hu, hv, hw⟩ := corner_of_infix h
  exact Polygon.sees_subset_cone' (simple n Φ) (interiorLeft n Φ) hi hu hv hw
    (by rw [det_ratPoint]; exact_mod_cast hconv) hp

section WedgeAlg

variable {H s : ℝ} {p : Point}

/-- `W1`, mouth on the right: `s ≤ x ≤ s + 2`. -/
theorem w1pos_facts (hH : 1000 ≤ H) (hy : -H - 140 ≤ p.2)
    (h1 : 0 ≤ det (s + 1 / 4, 2 * H) (s, 3 * H) p) (h2 : 0 ≤ det (s, 3 * H) (s, 2 * H) p) :
    s ≤ p.1 ∧ p.1 ≤ s + 2 := by
  simp only [det] at h1 h2
  constructor
  · nlinarith
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 2) (by linarith : (0:ℝ) < H)]

/-- `W1`, mouth on the left: `s − 2 ≤ x ≤ s`. -/
theorem w1neg_facts (hH : 1000 ≤ H) (hy : -H - 140 ≤ p.2)
    (h1 : 0 ≤ det (s, 2 * H) (s, 3 * H) p) (h2 : 0 ≤ det (s, 3 * H) (s - 1 / 4, 2 * H) p) :
    s - 2 ≤ p.1 ∧ p.1 ≤ s := by
  simp only [det] at h1 h2
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 2 - p.1) (by linarith : (0:ℝ) < H)]
  · nlinarith

/-- `W3`, mouth on the left of the segment (side `+`): slab, and at `x = s` the ordinate lies in
`[4H − T, …]` with `H (2H − y) ≥ (H − 3)(T − 2H)`. -/
theorem w3pos_facts {T e : ℝ} (hH : 1000 ≤ H) (he : e * (2 * (2 * H - 3)) = H - 3)
    (hT : 3 * H ≤ T) (hT' : T ≤ 4 * H) (hy : -H - 140 ≤ p.2) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s - e, 2 * H) (s - 1 / 2, T) p)
    (h2 : 0 ≤ det (s - 1 / 2, T) (s - 1 / 4, 2 * H) p) :
    s - 4 ≤ p.1 ∧ p.1 ≤ s + 4 ∧
      (p.1 = s → 4 * H - T ≤ p.2 ∧ (H - 3) * (T - 2 * H) ≤ H * (2 * H - p.2)) := by
  have hD : 0 < 2 * (2 * H - 3) := by linarith
  have he1 : 0 < e := by
    by_contra hc; push Not at hc; nlinarith
  have he2 : e < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  simp only [det] at h1 h2
  refine ⟨?_, ?_, fun hx => ?_⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 4 - p.1) (by linarith : (0:ℝ) < T - 2 * H)]
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 4) (by linarith : (0:ℝ) < T - 2 * H),
      mul_pos (by linarith : (0:ℝ) < 1 / 2 - e) (by linarith : (0:ℝ) < 3 * H + 140 - (2 * H - p.2) + 1)]
  · rw [hx] at h1 h2
    constructor
    · nlinarith
    · have key : 2 * (2 * H - 3) * ((s - 1 / 2 - (s - e)) * (p.2 - 2 * H) -
          (s - (s - e)) * (T - 2 * H)) = -H * (p.2 - 2 * H) - (H - 3) * (T - 2 * H) := by
        linear_combination (p.2 - 2 * H - (T - 2 * H)) * he
      nlinarith [mul_nonneg hD.le h1]

/-- `W3`, side `−`. -/
theorem w3neg_facts {T e : ℝ} (hH : 1000 ≤ H) (he : e * (2 * (2 * H - 3)) = H - 3)
    (hT : 3 * H ≤ T) (hT' : T ≤ 4 * H) (hy : -H - 140 ≤ p.2) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s + 1 / 4, 2 * H) (s + 1 / 2, T) p)
    (h2 : 0 ≤ det (s + 1 / 2, T) (s + e, 2 * H) p) :
    s - 4 ≤ p.1 ∧ p.1 ≤ s + 4 ∧
      (p.1 = s → 4 * H - T ≤ p.2 ∧ (2 * H - 3) * (T - 2 * H) ≤ H * (T - p.2)) := by
  have hD : 0 < 2 * (2 * H - 3) := by linarith
  have he1 : 0 < e := by
    by_contra hc; push Not at hc; nlinarith
  have he2 : e < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  simp only [det] at h1 h2
  refine ⟨?_, ?_, fun hx => ?_⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 4 - p.1) (by linarith : (0:ℝ) < T - 2 * H),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - e) (by linarith : (0:ℝ) ≤ p.2 + H + 140),
      mul_pos he1 (by linarith : (0:ℝ) < T)]
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 4) (by linarith : (0:ℝ) < T - 2 * H)]
  · rw [hx] at h1 h2
    constructor
    · nlinarith
    · have key : 2 * (2 * H - 3) * ((s + e - (s + 1 / 2)) * (p.2 - T) -
          (s - (s + 1 / 2)) * (2 * H - T)) = -H * (p.2 - T) - (2 * H - 3) * (T - 2 * H) := by
        linear_combination (p.2 - T) * he
      nlinarith [mul_nonneg hD.le h2]

/-- `W4` (variables with `x = 1`): slab, and at `x = s` the ordinate lies in `[H, H + 1]`. -/
theorem w4_facts {f : ℝ} (hH : 1000 ≤ H) (hf : f * (4 * (2 * H - 1)) = 3 * (H - 1))
    (hy : -H - 140 ≤ p.2) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s - f, 2 * H) (s - 3 / 4, 3 * H) p)
    (h2 : 0 ≤ det (s - 3 / 4, 3 * H) (s - 3 / 8, 2 * H) p) :
    s - 4 ≤ p.1 ∧ p.1 ≤ s + 4 ∧ (p.1 = s → H ≤ p.2 ∧ p.2 ≤ H + 1) := by
  have hD : 0 < 4 * (2 * H - 1) := by linarith
  have hf1 : 0 < f := by
    by_contra hc; push Not at hc; nlinarith
  have hf2 : f < 3 / 4 := by
    by_contra hc; push Not at hc; nlinarith
  simp only [det] at h1 h2
  refine ⟨?_, ?_, fun hx => ?_⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 4 - p.1) (by linarith : (0:ℝ) < H)]
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 4) (by linarith : (0:ℝ) < H),
      mul_pos (by linarith : (0:ℝ) < 3 / 4 - f) (by linarith : (0:ℝ) < 3 * H + 141 - (2 * H - p.2))]
  · rw [hx] at h1 h2
    constructor
    · nlinarith
    · have key : 4 * (2 * H - 1) * ((s - 3 / 4 - (s - f)) * (p.2 - 2 * H) -
          (s - (s - f)) * (3 * H - 2 * H)) = -3 * H * (p.2 - 2 * H) - 3 * (H - 1) * H := by
        linear_combination (p.2 - 2 * H - H) * hf
      nlinarith [mul_nonneg hD.le h1]

/-- `W5` (variables with `x = 1`): slab, and at `x = s` the ordinate lies in `[H + 1, H + 3]`. -/
theorem w5_facts {g h : ℝ} (hH : 1000 ≤ H) (hg : g * (2 * H - 3) = H - 3)
    (hh : h * (2 * H - 1) = H - 1) (hy : -H - 140 ≤ p.2) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s - g, 2 * H) (s - 1, 3 * H) p)
    (h2 : 0 ≤ det (s - 1, 3 * H) (s - h, 2 * H) p) :
    s - 4 ≤ p.1 ∧ p.1 ≤ s + 4 ∧ (p.1 = s → H + 1 ≤ p.2 ∧ p.2 ≤ H + 3) := by
  have hD1 : 0 < 2 * H - 3 := by linarith
  have hD2 : 0 < 2 * H - 1 := by linarith
  have hg1 : 0 < g := by
    by_contra hc; push Not at hc; nlinarith
  have hg2 : g < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  have hh1 : 0 < h := by
    by_contra hc; push Not at hc; nlinarith
  have hh2 : h < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  simp only [det] at h1 h2
  refine ⟨?_, ?_, fun hx => ?_⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 4 - p.1) (by linarith : (0:ℝ) < H)]
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 4) (by linarith : (0:ℝ) < H),
      mul_pos (by linarith : (0:ℝ) < 1 - g) (by linarith : (0:ℝ) < 3 * H + 141 - (2 * H - p.2))]
  · rw [hx] at h1 h2
    constructor
    · have key : (2 * H - 1) * ((s - h - (s - 1)) * (p.2 - 3 * H) -
          (s - (s - 1)) * (2 * H - 3 * H)) = H * (p.2 - 3 * H) + H * (2 * H - 1) := by
        linear_combination (-(p.2 - 3 * H)) * hh
      nlinarith [mul_nonneg hD2.le h2]
    · have key : (2 * H - 3) * ((s - 1 - (s - g)) * (p.2 - 2 * H) -
          (s - (s - g)) * (3 * H - 2 * H)) = -H * (p.2 - 2 * H) - (H - 3) * H := by
        linear_combination (p.2 - 2 * H - H) * hg
      nlinarith [mul_nonneg hD1.le h1]

/-- A floor needle (`W2`) with tip `(s, vy)`, mouth on the left (`u = (s − 1/4, uy)`,
`w = (s, wy)`): slab and `x ≤ s`. -/
theorem w2pos_facts {vy uy wy : ℝ} (hH : 1000 ≤ H) (hu : H ≤ uy - vy) (hu' : uy - vy ≤ H + 1)
    (hw : H ≤ wy - vy) (hv : -H - 140 ≤ vy) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s - 1 / 4, uy) (s, vy) p) (h2 : 0 ≤ det (s, vy) (s, wy) p) :
    s - 4 ≤ p.1 ∧ p.1 ≤ s := by
  simp only [det] at h1 h2
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < s - 4 - p.1) (by linarith : (0:ℝ) < H)]
  · nlinarith

/-- A floor needle (`W2`) with tip `(s, vy)`, mouth on the right (`u = (s, uy)`,
`w = (s + 1/4, wy)`): slab and `s ≤ x`. -/
theorem w2neg_facts {vy uy wy : ℝ} (hH : 1000 ≤ H) (hu : H ≤ uy - vy)
    (hw : H ≤ wy - vy) (hw' : wy - vy ≤ H + 1) (hv : -H - 140 ≤ vy) (hy' : p.2 ≤ 4 * H)
    (h1 : 0 ≤ det (s, uy) (s, vy) p) (h2 : 0 ≤ det (s, vy) (s + 1 / 4, wy) p) :
    s ≤ p.1 ∧ p.1 ≤ s + 4 := by
  simp only [det] at h1 h2
  constructor
  · nlinarith
  · by_contra hc; push Not at hc
    nlinarith [mul_pos (by linarith : (0:ℝ) < p.1 - s - 4) (by linarith : (0:ℝ) < H)]

end WedgeAlg

/-! ### Consecutive triples of a list -/

/-- The consecutive triples of a list. -/
def triples {α : Type} : List α → List (α × α × α)
  | a :: b :: c :: l => (a, b, c) :: triples (b :: c :: l)
  | _ => []

/-- A consecutive triple is a contiguous part. -/
theorem infix_of_mem_triples {α : Type} :
    ∀ {l : List α} {a b c : α}, (a, b, c) ∈ triples l → [a, b, c] <:+: l
  | x :: y :: z :: l, a, b, c, h => by
    simp only [triples, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], l, rfl⟩
    · exact (infix_of_mem_triples h).trans (List.infix_cons (List.infix_refl _))
  | [], _, _, _, h => by simp [triples] at h
  | [_], _, _, _, h => by simp [triples] at h
  | [_, _], _, _, _, h => by simp [triples] at h

/-! ### The bottom wedges `W2` of the inputs (template check) -/

/-- The triple `u, v, w` of a floor feature is the bottom wedge `W2` of the template input `t`:
tip `v = (t.lx, y₀ − H)`, mouth ends at depth `0` and at most `1/4` above `y₀`, on the side
opposite to the top wedge. -/
def w2OK (t : TInput) : RPt × RPt × RPt → Bool
  | (u, v, w) => decide (v.1 = t.lx ∧ v.2.2 = 1 ∧ u.2.2 = 0 ∧ w.2.2 = 0 ∧ -140 ≤ v.2.1 ∧
      v.2.1 ≤ -1 ∧ v.2.1 ≤ u.2.1 ∧ u.2.1 ≤ v.2.1 + 1 / 4 ∧ v.2.1 ≤ w.2.1 ∧
      w.2.1 ≤ v.2.1 + 1 / 4) &&
    ((t.pos && decide (u.1 = t.lx - 1 / 4 ∧ w.1 = t.lx)) ||
      (!t.pos && decide (u.1 = t.lx ∧ w.1 = t.lx + 1 / 4)))

/-- Every template input has a bottom wedge in the floor features of its template. -/
theorem tmplW2_ok : allKinds.all (fun k => (tmplInputs k).all (fun t =>
    (tmplFloor k).any (fun ch => (triples ch).any (w2OK t)))) = true := by decide +kernel

/-- The bottom wedge of a template input. -/
theorem tmplW2 {k : TKind} {t : TInput} (ht : t ∈ tmplInputs k) :
    ∃ ch ∈ tmplFloor k, ∃ u v w : RPt, [u, v, w] <:+: ch ∧ v.1 = t.lx ∧ v.2.2 = 1 ∧
      u.2.2 = 0 ∧ w.2.2 = 0 ∧ -140 ≤ v.2.1 ∧ v.2.1 ≤ -1 ∧ v.2.1 ≤ u.2.1 ∧
      u.2.1 ≤ v.2.1 + 1 / 4 ∧ v.2.1 ≤ w.2.1 ∧ w.2.1 ≤ v.2.1 + 1 / 4 ∧
      ((t.pos = true ∧ u.1 = t.lx - 1 / 4 ∧ w.1 = t.lx) ∨
        (t.pos = false ∧ u.1 = t.lx ∧ w.1 = t.lx + 1 / 4)) := by
  have := tmplW2_ok
  simp only [List.all_eq_true, List.any_eq_true] at this
  obtain ⟨ch, hch, ⟨u, v, w⟩, hq, hok⟩ := this k (mem_allKinds k) t ht
  refine ⟨ch, hch, u, v, w, infix_of_mem_triples hq, ?_⟩
  simp only [w2OK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11⟩ := hok
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  rcases h11 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩

/-! ### Segment regions: slabs and positions -/

/-- The slab `|x − s| ≤ 4` of a segment region at abscissa `s`. -/
def slab (s : ℝ) : Set Point := {p | s - 4 ≤ p.1 ∧ p.1 ≤ s + 4}

/-- The tip of the cutter `W3` of a segment region at `s` (side `pos`, height `T`). -/
def w3tip (s : ℚ) (pos : Bool) (T : ℚ) : ℚ × ℚ := if pos then (s - 1 / 2, T) else (s + 1 / 2, T)

/-- A point seeing some point lies in the region. -/
theorem mem_filled_of_sees {P : Polygon} {p q : Point} (h : P.Sees p q) : p ∈ P.filled :=
  h (Geometry.left_mem_segment p q)

theorem paramH_ge_r (n : ℕ) (Φ : List Constraint) : (1000 : ℝ) ≤ (paramH n Φ : ℝ) := by
  exact_mod_cast paramH_ge n Φ

/-- Strip bounds for a viewer. -/
theorem strip_of_sees {p q : Point} (h : (SP n Φ).Sees p q) :
    -(paramH n Φ : ℝ) - 140 ≤ p.2 ∧ p.2 ≤ 4 * (paramH n Φ : ℝ) :=
  filled_strip (mem_filled_of_sees h)

/-- The top wedge `W1` of a segment region at `s` with side `pos`: its viewers lie in
`[s, s + 2]` (`pos`) resp. `[s − 2, s]`. -/
theorem w1_viewer {s : ℚ} {pos : Bool} (hW : wedgeW1 s pos (paramH n Φ) <:+: poly n Φ) {p : Point}
    (hp : (SP n Φ).Sees p (ratPoint (s, 3 * (paramH n Φ : ℚ)))) :
    (pos = true → (s : ℝ) ≤ p.1 ∧ p.1 ≤ s + 2) ∧ (pos = false → (s : ℝ) - 2 ≤ p.1 ∧ p.1 ≤ s) := by
  have hH := paramH_ge_r n Φ
  have hy := (strip_of_sees hp).1
  have hHq := paramH_ge_q n Φ
  cases pos
  · refine ⟨fun h => by simp at h, fun _ => ?_⟩
    have h := sees_corner (u := (s, 2 * (paramH n Φ : ℚ))) (w := (s - 1 / 4, 2 * (paramH n Φ : ℚ)))
      hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h
    exact w1neg_facts hH hy h.1 h.2
  · refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have h := sees_corner (u := (s + 1 / 4, 2 * (paramH n Φ : ℚ))) (w := (s, 2 * (paramH n Φ : ℚ)))
      hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h
    exact w1pos_facts hH hy h.1 h.2

/-- The cutter `W3` of a segment region at `s` with tip height `T ∈ [3H, 4H]`: its viewers lie
in the slab, and a viewer on the line `x = s` satisfies the two ordinate bounds. -/
theorem w3_viewer {s T : ℚ} {pos : Bool} (hT : 3 * (paramH n Φ : ℚ) ≤ T)
    (hT' : T ≤ 4 * (paramH n Φ : ℚ)) (hW : wedgeW3 s pos T (paramH n Φ) <:+: poly n Φ)
    {p : Point} (hp : (SP n Φ).Sees p (ratPoint (w3tip s pos T))) :
    p ∈ slab s ∧ (p.1 = s → 4 * (paramH n Φ : ℝ) - T ≤ p.2 ∧
      (pos = true → ((paramH n Φ : ℝ) - 3) * (T - 2 * (paramH n Φ : ℝ)) ≤
        (paramH n Φ : ℝ) * (2 * (paramH n Φ : ℝ) - p.2)) ∧
      (pos = false → (2 * (paramH n Φ : ℝ) - 3) * (T - 2 * (paramH n Φ : ℝ)) ≤
        (paramH n Φ : ℝ) * (T - p.2))) := by
  have hH := paramH_ge_r n Φ
  have hy := strip_of_sees hp
  have hHq := paramH_ge_q n Φ
  have hT1 : 3 * (paramH n Φ : ℝ) ≤ T := by exact_mod_cast hT
  have hT2 : (T : ℝ) ≤ 4 * (paramH n Φ : ℝ) := by exact_mod_cast hT'
  have he : (((paramH n Φ : ℚ) - 3) / (2 * (2 * (paramH n Φ : ℚ) - 3)) : ℚ) *
      (2 * (2 * (paramH n Φ : ℚ) - 3)) = (paramH n Φ : ℚ) - 3 :=
    div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have he' : ((((paramH n Φ : ℚ) - 3) / (2 * (2 * (paramH n Φ : ℚ) - 3)) : ℚ) : ℝ) *
      (2 * (2 * (paramH n Φ : ℝ) - 3)) = (paramH n Φ : ℝ) - 3 := by
    have := congrArg (fun x : ℚ => (x : ℝ)) he
    push_cast at this ⊢
    linarith
  have hb := frac3_bounds hHq
  cases pos
  · have h := sees_corner (u := (s + 1 / 4, 2 * (paramH n Φ : ℚ)))
      (w := (s + ((paramH n Φ : ℚ) - 3) / (2 * (2 * (paramH n Φ : ℚ) - 3)), 2 * (paramH n Φ : ℚ)))
      hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h he'
    obtain ⟨h1, h2, h3⟩ := w3neg_facts hH he' hT1 hT2 hy.1 hy.2 h.1 h.2
    exact ⟨⟨h1, h2⟩, fun hx => ⟨(h3 hx).1, fun h => by simp at h, fun _ => (h3 hx).2⟩⟩
  · have h := sees_corner
      (u := (s - ((paramH n Φ : ℚ) - 3) / (2 * (2 * (paramH n Φ : ℚ) - 3)), 2 * (paramH n Φ : ℚ)))
      (w := (s - 1 / 4, 2 * (paramH n Φ : ℚ))) hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h he'
    obtain ⟨h1, h2, h3⟩ := w3pos_facts hH he' hT1 hT2 hy.1 hy.2 h.1 h.2
    exact ⟨⟨h1, h2⟩, fun hx => ⟨(h3 hx).1, fun _ => (h3 hx).2, fun h => by simp at h⟩⟩

/-- The wedges `W4`, `W5` of a variable at `s` with a constraint `x = 1`: viewers lie in the
slab; a viewer on `x = s` has ordinate in `[H, H + 1]` resp. `[H + 1, H + 3]`. -/
theorem w4_viewer {s : ℚ} (hW : wedgeW4 s (paramH n Φ) <:+: poly n Φ) {p : Point}
    (hp : (SP n Φ).Sees p (ratPoint (s - 3 / 4, 3 * (paramH n Φ : ℚ)))) :
    p ∈ slab s ∧ (p.1 = s → (paramH n Φ : ℝ) ≤ p.2 ∧ p.2 ≤ (paramH n Φ : ℝ) + 1) := by
  have hH := paramH_ge_r n Φ
  have hy := strip_of_sees hp
  have hHq := paramH_ge_q n Φ
  have hf : (3 * ((paramH n Φ : ℚ) - 1) / (4 * (2 * (paramH n Φ : ℚ) - 1)) : ℚ) *
      (4 * (2 * (paramH n Φ : ℚ) - 1)) = 3 * ((paramH n Φ : ℚ) - 1) :=
    div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hf' := congrArg (fun x : ℚ => (x : ℝ)) hf
  have hb := frac4_bounds hHq
  have h := sees_corner hW (by unfold qdet; simp only; nlinarith) hp
  simp only [ratPoint_mk] at h
  push_cast at h hf'
  obtain ⟨h1, h2, h3⟩ := w4_facts hH hf' hy.1 hy.2 h.1 h.2
  exact ⟨⟨h1, h2⟩, h3⟩

theorem w5_viewer {s : ℚ} (hW : wedgeW5 s (paramH n Φ) <:+: poly n Φ) {p : Point}
    (hp : (SP n Φ).Sees p (ratPoint (s - 1, 3 * (paramH n Φ : ℚ)))) :
    p ∈ slab s ∧ (p.1 = s → (paramH n Φ : ℝ) + 1 ≤ p.2 ∧ p.2 ≤ (paramH n Φ : ℝ) + 3) := by
  have hH := paramH_ge_r n Φ
  have hy := strip_of_sees hp
  have hHq := paramH_ge_q n Φ
  have hg : (((paramH n Φ : ℚ) - 3) / (2 * (paramH n Φ : ℚ) - 3) : ℚ) *
      (2 * (paramH n Φ : ℚ) - 3) = (paramH n Φ : ℚ) - 3 :=
    div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hh : (((paramH n Φ : ℚ) - 1) / (2 * (paramH n Φ : ℚ) - 1) : ℚ) *
      (2 * (paramH n Φ : ℚ) - 1) = (paramH n Φ : ℚ) - 1 :=
    div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hg' := congrArg (fun x : ℚ => (x : ℝ)) hg
  have hh' := congrArg (fun x : ℚ => (x : ℝ)) hh
  have hb := frac5_bounds hHq
  have h := sees_corner hW (by unfold qdet; simp only; nlinarith) hp
  simp only [ratPoint_mk] at h
  push_cast at h hg' hh'
  obtain ⟨h1, h2, h3⟩ := w5_facts hH hg' hh' hy.1 hy.2 h.1 h.2
  exact ⟨⟨h1, h2⟩, h3⟩

/-- A bottom wedge `W2` with tip `v = (s, ·)`: viewers lie in the slab, on the side `x ≤ s` if the
mouth is on the left, `x ≥ s` if it is on the right. -/
theorem w2_viewer {u v w : ℚ × ℚ} {s : ℚ} (hW : [u, v, w] <:+: poly n Φ) (hv1 : v.1 = s)
    (hu : (paramH n Φ : ℚ) ≤ u.2 - v.2) (hu' : u.2 - v.2 ≤ (paramH n Φ : ℚ) + 1)
    (hw : (paramH n Φ : ℚ) ≤ w.2 - v.2) (hw' : w.2 - v.2 ≤ (paramH n Φ : ℚ) + 1)
    (hvy : -(paramH n Φ : ℚ) - 140 ≤ v.2)
    (hside : (u.1 = s - 1 / 4 ∧ w.1 = s) ∨ (u.1 = s ∧ w.1 = s + 1 / 4)) {p : Point}
    (hp : (SP n Φ).Sees p (ratPoint v)) :
    p ∈ slab s ∧ (u.1 = s - 1 / 4 → p.1 ≤ s) ∧ (w.1 = s + 1 / 4 → s ≤ p.1) := by
  have hH := paramH_ge_r n Φ
  have hy := strip_of_sees hp
  have hHq := paramH_ge_q n Φ
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  simp only at hv1 hu hu' hw hw' hvy hside ⊢
  subst hv1
  have hu_r : (paramH n Φ : ℝ) ≤ (u2 : ℝ) - v2 := by exact_mod_cast hu
  have hu_r' : (u2 : ℝ) - v2 ≤ (paramH n Φ : ℝ) + 1 := by exact_mod_cast hu'
  have hw_r : (paramH n Φ : ℝ) ≤ (w2 : ℝ) - v2 := by exact_mod_cast hw
  have hw_r' : (w2 : ℝ) - v2 ≤ (paramH n Φ : ℝ) + 1 := by exact_mod_cast hw'
  have hv_r : -(paramH n Φ : ℝ) - 140 ≤ (v2 : ℝ) := by exact_mod_cast hvy
  rcases hside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := sees_corner hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h
    obtain ⟨h1, h2⟩ := w2pos_facts hH hu_r hu_r' hw_r hv_r hy.2 h.1 h.2
    refine ⟨⟨h1, by linarith⟩, fun _ => h2, fun h' => ?_⟩
    exfalso; linarith
  · have h := sees_corner hW (by unfold qdet; simp only; nlinarith) hp
    simp only [ratPoint_mk] at h
    push_cast at h
    obtain ⟨h1, h2⟩ := w2neg_facts hH hu_r hw_r hw_r' hv_r hy.2 h.1 h.2
    refine ⟨⟨by linarith, h2⟩, fun h' => ?_, fun _ => h1⟩
    exfalso; linarith

/-! ### Variables -/

/-- The floor needle of a variable, explicitly. -/
theorem needleDownL_inst (H a : ℚ) :
    needleDownL.map (RPt.inst H a) = [(a - 1 / 4, -1), (a, -1 - H), (a, -1)] := by
  simp only [needleDownL, List.map_cons, List.map_nil, RPt.inst, List.cons.injEq, Prod.mk.injEq,
    and_true]
  refine ⟨⟨by ring, by ring⟩, ⟨by ring, by ring⟩, by ring, by ring⟩

/-- Tip of the top wedge `W1` of a segment region at `s`. -/
def tipW1 (n : ℕ) (Φ : List Constraint) (s : ℚ) : Point := ratPoint (s, 3 * (paramH n Φ : ℚ))

/-- Tip of the floor needle `W2` of variable `k`. -/
def varTipW2 (n : ℕ) (Φ : List Constraint) (k : ℕ) : Point :=
  ratPoint ((varA Φ k : ℚ), -1 - (paramH n Φ : ℚ))

/-- Tip of the cutter `W3` of variable `k`. -/
def varTipW3 (n : ℕ) (Φ : List Constraint) (k : ℕ) : Point :=
  ratPoint (w3tip (varA Φ k : ℚ) true (3 * (paramH n Φ : ℚ)))

/-- Tip of the wedge `W4` of variable `k`. -/
def varTipW4 (n : ℕ) (Φ : List Constraint) (k : ℕ) : Point :=
  ratPoint ((varA Φ k : ℚ) - 3 / 4, 3 * (paramH n Φ : ℚ))

/-- Tip of the wedge `W5` of variable `k`. -/
def varTipW5 (n : ℕ) (Φ : List Constraint) (k : ℕ) : Point :=
  ratPoint ((varA Φ k : ℚ) - 1, 3 * (paramH n Φ : ℚ))

theorem varW1_infix {k : ℕ} (hk : k < n) :
    wedgeW1 (varA Φ k : ℚ) true (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (varCeil_mem hk (by simp [varCeil]))

theorem varW3_infix {k : ℕ} (hk : k < n) :
    wedgeW3 (varA Φ k : ℚ) true (3 * (paramH n Φ : ℚ)) (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (varCeil_mem hk (by simp [varCeil]))

theorem varW2_infix {k : ℕ} (hk : k < n) :
    [((varA Φ k : ℚ) - 1 / 4, -1), ((varA Φ k : ℚ), -1 - (paramH n Φ : ℚ)), ((varA Φ k : ℚ), -1)]
      <:+: poly n Φ := by
  rw [← needleDownL_inst]
  exact floor_infix (varFloor_mem hk)

theorem varW4_infix {k : ℕ} (hk : k < n) (h1 : hasOne Φ k = true) :
    wedgeW4 (varA Φ k : ℚ) (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (varCeil_mem hk (by simp [varCeil, h1]))

theorem varW5_infix {k : ℕ} (hk : k < n) (h1 : hasOne Φ k = true) :
    wedgeW5 (varA Φ k : ℚ) (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (varCeil_mem hk (by simp [varCeil, h1]))

/-- A point of an infix of the vertex list lies on the boundary. -/
theorem mem_boundary_of_infix {m : List (ℚ × ℚ)} (h : m <:+: poly n Φ) {u : ℚ × ℚ}
    (hu : u ∈ m) : ratPoint u ∈ (SP n Φ).boundary :=
  list_mem_boundary (h.subset hu)

/-- **Variable regions (L4.1, L4.4).** The tips of `W1, W2, W3` of variable `k` lie on the
boundary, their viewers lie in the slab of `a_k`, and a point seeing all three lies on the
variable segment `{a_k} × [H, H + 3]`. -/
theorem var_tips {k : ℕ} (hk : k < n) :
    tipW1 n Φ (varA Φ k) ∈ (SP n Φ).boundary ∧ varTipW2 n Φ k ∈ (SP n Φ).boundary ∧
      varTipW3 n Φ k ∈ (SP n Φ).boundary ∧
      (∀ p, (SP n Φ).Sees p (tipW1 n Φ (varA Φ k)) → p ∈ slab ((varA Φ k : ℚ) : ℝ)) ∧
      (∀ p, (SP n Φ).Sees p (varTipW2 n Φ k) → p ∈ slab ((varA Φ k : ℚ) : ℝ)) ∧
      (∀ p, (SP n Φ).Sees p (varTipW3 n Φ k) → p ∈ slab ((varA Φ k : ℚ) : ℝ)) ∧
      (∀ p, (SP n Φ).Sees p (tipW1 n Φ (varA Φ k)) → (SP n Φ).Sees p (varTipW2 n Φ k) →
        (SP n Φ).Sees p (varTipW3 n Φ k) →
        p.1 = ((varA Φ k : ℚ) : ℝ) ∧ (paramH n Φ : ℝ) ≤ p.2 ∧ p.2 ≤ (paramH n Φ : ℝ) + 3) := by
  have hHq := paramH_ge_q n Φ
  have hH := paramH_ge_r n Φ
  have hW1 := varW1_infix (Φ := Φ) hk
  have hW2 := varW2_infix (Φ := Φ) hk
  have hW3 := varW3_infix (Φ := Φ) hk
  have hW2v := fun {p : Point} (hp : (SP n Φ).Sees p (varTipW2 n Φ k)) =>
    w2_viewer (s := (varA Φ k : ℚ)) hW2 rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; linarith) (Or.inl ⟨rfl, rfl⟩) hp
  have hW3v := fun {p : Point} (hp : (SP n Φ).Sees p (varTipW3 n Φ k)) =>
    w3_viewer (by linarith) (by linarith) hW3 hp
  refine ⟨mem_boundary_of_infix hW1 (by simp [wedgeW1]), mem_boundary_of_infix hW2 (by simp),
    mem_boundary_of_infix hW3 (by simp [wedgeW3, w3tip]), fun p hp => ?_, fun p hp => (hW2v hp).1,
    fun p hp => (hW3v hp).1, fun p h1 h2 h3 => ?_⟩
  · obtain ⟨h1, h2⟩ := (w1_viewer hW1 hp).1 rfl
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h1a, -⟩ := (w1_viewer hW1 h1).1 rfl
    have h2a := (hW2v h2).2.1 rfl
    have hx : p.1 = ((varA Φ k : ℚ) : ℝ) := le_antisymm h2a h1a
    obtain ⟨-, h3b⟩ := hW3v h3
    obtain ⟨h3c, h3d, -⟩ := h3b hx
    have h3d := h3d rfl
    push_cast at h3c h3d
    refine ⟨hx, by linarith, ?_⟩
    nlinarith

/-- **Variables with `x = 1` (L4.4).** The tips of `W4, W5` lie on the boundary, their viewers
lie in the slab, and a point seeing the tips of `W1, W2, W4, W5` is `(a_k, H + 1)`. -/
theorem var_tips_one {k : ℕ} (hk : k < n) (hone : hasOne Φ k = true) :
    varTipW4 n Φ k ∈ (SP n Φ).boundary ∧ varTipW5 n Φ k ∈ (SP n Φ).boundary ∧
      (∀ p, (SP n Φ).Sees p (varTipW4 n Φ k) → p ∈ slab ((varA Φ k : ℚ) : ℝ)) ∧
      (∀ p, (SP n Φ).Sees p (varTipW5 n Φ k) → p ∈ slab ((varA Φ k : ℚ) : ℝ)) ∧
      (∀ p, (SP n Φ).Sees p (tipW1 n Φ (varA Φ k)) → (SP n Φ).Sees p (varTipW2 n Φ k) →
        (SP n Φ).Sees p (varTipW4 n Φ k) → (SP n Φ).Sees p (varTipW5 n Φ k) →
        p.1 = ((varA Φ k : ℚ) : ℝ) ∧ p.2 = (paramH n Φ : ℝ) + 1) := by
  have hHq := paramH_ge_q n Φ
  have hW1 := varW1_infix (Φ := Φ) hk
  have hW2 := varW2_infix (Φ := Φ) hk
  have hW4 := varW4_infix (Φ := Φ) hk hone
  have hW5 := varW5_infix (Φ := Φ) hk hone
  refine ⟨mem_boundary_of_infix hW4 (by simp [wedgeW4]),
    mem_boundary_of_infix hW5 (by simp [wedgeW5]), fun p hp => (w4_viewer hW4 hp).1,
    fun p hp => (w5_viewer hW5 hp).1, fun p h1 h2 h4 h5 => ?_⟩
  obtain ⟨h1a, -⟩ := (w1_viewer hW1 h1).1 rfl
  have h2a := (w2_viewer (s := (varA Φ k : ℚ)) hW2 rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; linarith) (Or.inl ⟨rfl, rfl⟩) h2).2.1 rfl
  have hx : p.1 = ((varA Φ k : ℚ) : ℝ) := le_antisymm h2a h1a
  obtain ⟨h4a, h4b⟩ := (w4_viewer hW4 h4).2 hx
  obtain ⟨h5a, h5b⟩ := (w5_viewer hW5 h5).2 hx
  exact ⟨hx, le_antisymm h4b h5a⟩

/-! ### Inputs -/

/-- Tip of the cutter `W3` of an input. -/
def inTipW3 (n : ℕ) (Φ : List Constraint) (i : InputSeg) : Point :=
  ratPoint (w3tip i.b i.pos (4 * (paramH n Φ : ℚ)))

theorem inW1_infix {i : InputSeg} (hi : i ∈ inputs n Φ) :
    wedgeW1 i.b i.pos (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (inputCeil_mem hi (by cases i.pos <;> simp [inputCeil]))

theorem inW3_infix {i : InputSeg} (hi : i ∈ inputs n Φ) :
    wedgeW3 i.b i.pos (4 * (paramH n Φ : ℚ)) (paramH n Φ) <:+: poly n Φ :=
  ceil_infix (inputCeil_mem hi (by cases i.pos <;> simp [inputCeil]))

/-- **Input regions (L4.1, L4.4).** The tips of `W1, W2, W3` of an input lie on the boundary,
their viewers lie in the slab of `b`, and a point seeing all three lies on the input segment
`{b} × [0, 6]`. -/
theorem input_tips {i : InputSeg} (hi : i ∈ inputs n Φ) :
    ∃ w2 : Point, w2 ∈ (SP n Φ).boundary ∧ tipW1 n Φ i.b ∈ (SP n Φ).boundary ∧
      inTipW3 n Φ i ∈ (SP n Φ).boundary ∧
      (∀ p, (SP n Φ).Sees p (tipW1 n Φ i.b) → p ∈ slab i.b) ∧
      (∀ p, (SP n Φ).Sees p w2 → p ∈ slab i.b) ∧
      (∀ p, (SP n Φ).Sees p (inTipW3 n Φ i) → p ∈ slab i.b) ∧
      (∀ p, (SP n Φ).Sees p (tipW1 n Φ i.b) → (SP n Φ).Sees p w2 →
        (SP n Φ).Sees p (inTipW3 n Φ i) → p.1 = i.b ∧ 0 ≤ p.2 ∧ p.2 ≤ 6) := by
  have hHq := paramH_ge_q n Φ
  have hH := paramH_ge_r n Φ
  obtain ⟨c, hc, t, ht, hb, hpos, -⟩ := mem_inputs hi
  obtain ⟨ch, hch, u, v, w, hinf, hv1, hv22, hu22, hw22, hv21a, hv21b, hu1, hu2, hw1, hw2,
    hside⟩ := tmplW2 ht
  set g : ℚ := (slotG n Φ c : ℚ)
  set Hq : ℚ := (paramH n Φ : ℚ)
  have hW2 : [u.inst Hq g, v.inst Hq g, w.inst Hq g] <:+: poly n Φ :=
    (hinf.map (RPt.inst Hq g)).trans (floor_infix (slotFloor_mem hc hch))
  have hW1 := inW1_infix hi
  have hW3 := inW3_infix hi
  have hv1' : (v.inst Hq g).1 = i.b := by simp only [RPt.inst]; rw [hv1, hb]
  have hside' : ((u.inst Hq g).1 = i.b - 1 / 4 ∧ (w.inst Hq g).1 = i.b) ∨
      ((u.inst Hq g).1 = i.b ∧ (w.inst Hq g).1 = i.b + 1 / 4) := by
    simp only [RPt.inst, hb]
    rcases hside with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  have hW2v := fun {p : Point} (hp : (SP n Φ).Sees p (ratPoint (v.inst Hq g))) =>
    w2_viewer (s := i.b) hW2 hv1' (by simp only [RPt.inst, hu22, hv22]; linarith)
      (by simp only [RPt.inst, hu22, hv22]; linarith) (by simp only [RPt.inst, hw22, hv22]; linarith)
      (by simp only [RPt.inst, hw22, hv22]; linarith) (by simp only [RPt.inst, hv22]; linarith)
      hside' hp
  have hW3v := fun {p : Point} (hp : (SP n Φ).Sees p (inTipW3 n Φ i)) =>
    w3_viewer (by linarith) (by linarith) hW3 hp
  refine ⟨ratPoint (v.inst Hq g), mem_boundary_of_infix hW2 (by simp),
    mem_boundary_of_infix hW1 (by cases i.pos <;> simp [wedgeW1]),
    mem_boundary_of_infix hW3 (by cases i.pos <;> simp [wedgeW3, w3tip]), fun p hp => ?_,
    fun p hp => (hW2v hp).1, fun p hp => (hW3v hp).1, fun p h1 h2 h3 => ?_⟩
  · have := w1_viewer hW1 hp
    cases hp' : i.pos
    · obtain ⟨h1, h2⟩ := this.2 hp'
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨h1, h2⟩ := this.1 hp'
      exact ⟨by linarith, by linarith⟩
  · have hw1 := w1_viewer hW1 h1
    have hw2 := hW2v h2
    have hx : p.1 = i.b := by
      rcases hside' with ⟨h, -⟩ | ⟨-, h⟩
      · have hp' : i.pos = true := by
          rcases hside with ⟨hp, -⟩ | ⟨-, h', -⟩
          · rw [hpos, hp]
          · simp only [RPt.inst, hb] at h; linarith
        exact le_antisymm (hw2.2.1 h) (hw1.1 hp').1
      · have hp' : i.pos = false := by
          rcases hside with ⟨-, -, h'⟩ | ⟨hp, -⟩
          · simp only [RPt.inst, hb] at h; linarith
          · rw [hpos, hp]
        exact le_antisymm (hw1.2 hp').2 (hw2.2.2 h)
    obtain ⟨h3a, h3b, h3c⟩ := (hW3v h3).2 hx
    push_cast at h3a h3b h3c
    refine ⟨hx, by linarith, ?_⟩
    cases hp' : i.pos
    · have := h3c hp'
      nlinarith
    · have := h3b hp'
      nlinarith

/-! ### Aux regions of the addition gadgets -/

/-- Tip of the aux wedge of an addition template (local coordinates). -/
def auxTip : TKind → ℚ × ℚ
  | .addGe => (82, -113)
  | _ => (110, -519 / 4)

/-- First mouth end (in boundary order) of the aux wedge. -/
def auxM1 : TKind → ℚ × ℚ
  | .addGe => (327 / 4, -94)
  | _ => (439 / 4, -128)

/-- Second mouth end of the aux wedge. -/
def auxM2 : TKind → ℚ × ℚ
  | .addGe => (329 / 4, -94)
  | _ => (441 / 4, -128)

/-- The window end `WL` of the room (start of the upper-left room wall). -/
def auxWL : TKind → ℚ × ℚ
  | .addGe => (85, -1)
  | _ => (200, -1)

/-- The top `T0` of the left room wall (end of the upper-left room wall). -/
def auxT0 : TKind → ℚ × ℚ
  | .addGe => (50, -37)
  | _ => (50, -445 / 4)

/-- A local template point translated by the slot origin `G`. -/
def trP (G : ℝ) (q : ℚ × ℚ) : Point := (G + q.1, q.2)

/-- **The aux region** of an addition gadget with slot origin `G`: the cone of the aux wedge
(between the rays from the tip through the two mouth ends) on the room side of the upper-left
room wall `WL → T0`.  Every point seeing the aux tip lies in it (`aux_viewer`). -/
def auxRegion (k : TKind) (G : ℝ) : Set Point :=
  {p | 0 ≤ det (trP G (auxM1 k)) (trP G (auxTip k)) p ∧
    0 ≤ det (trP G (auxTip k)) (trP G (auxM2 k)) p ∧
    0 ≤ det (trP G (auxWL k)) (trP G (auxT0 k)) p}

/-- The aux wedge and the upper-left room wall are consecutive vertices of the gadget chain. -/
theorem aux_chain_ok : [TKind.addLe, .addGe].all (fun k =>
    decide ([fixR (auxM1 k), fixR (auxTip k), fixR (auxM2 k)] <:+: tmplChain k) &&
      decide ([fixR (auxWL k), fixR (auxT0 k)] <:+: tmplChain k)) = true := by
  decide +kernel

/-- An addition kind. -/
def IsAdd (k : TKind) : Prop := k = .addLe ∨ k = .addGe

theorem tmplChain_mem {k : TKind} (hk : IsAdd k) : tmplChain k ∈ tmplFloor k := by
  rcases hk with rfl | rfl <;> simp [tmplChain, tmplFloor]

theorem aux_infix {k : TKind} (hk : IsAdd k) :
    [fixR (auxM1 k), fixR (auxTip k), fixR (auxM2 k)] <:+: tmplChain k ∧
      [fixR (auxWL k), fixR (auxT0 k)] <:+: tmplChain k := by
  have := aux_chain_ok
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at this
  rcases hk with rfl | rfl
  · exact this.1
  · exact this.2

/-- The instantiated template point. -/
theorem ratPoint_fixR (H G : ℚ) (q : ℚ × ℚ) :
    ratPoint ((fixR q).inst H G) = trP (G : ℝ) q := by
  simp [fixR, RPt.inst, ratPoint, trP]

/-- The geometric facts of the aux wedges: the tip is strictly on the room side of the wall, and
a point of the cone strictly beyond the wall gives a proper crossing of the wall. -/
theorem aux_geom {k : TKind} (hk : IsAdd k) (G : ℝ) :
    0 < det (trP G (auxWL k)) (trP G (auxT0 k)) (trP G (auxTip k)) ∧
    0 < det (trP G (auxM1 k)) (trP G (auxTip k)) (trP G (auxM2 k)) ∧
    ∀ p : Point, 0 ≤ det (trP G (auxM1 k)) (trP G (auxTip k)) p →
      0 ≤ det (trP G (auxTip k)) (trP G (auxM2 k)) p →
      det (trP G (auxWL k)) (trP G (auxT0 k)) p < 0 →
      0 < det p (trP G (auxTip k)) (trP G (auxWL k)) ∧
        det p (trP G (auxTip k)) (trP G (auxT0 k)) < 0 := by
  rcases hk with rfl | rfl <;> refine ⟨?_, ?_, fun p h1 h2 h3 => ⟨?_, ?_⟩⟩ <;>
    simp only [auxWL, auxT0, auxTip, auxM1, auxM2, trP, det] at * <;> norm_num at * <;> linarith

/-- The aux tip of slot `c`. -/
def auxTipPt (n : ℕ) (Φ : List Constraint) (c : ℕ) : Point :=
  trP (slotG n Φ c : ℝ) (auxTip (cKind (gadAt Φ c)))

/-- **Viewers of the aux tip (L4.1').** The aux tip of an addition slot lies on the boundary, and
every point seeing it lies in the aux region. -/
theorem aux_viewer {c : ℕ} (hc : c < paramC Φ) (hk : IsAdd (cKind (gadAt Φ c))) :
    auxTipPt n Φ c ∈ (SP n Φ).boundary ∧
      ∀ p, (SP n Φ).Sees p (auxTipPt n Φ c) →
        p ∈ auxRegion (cKind (gadAt Φ c)) (slotG n Φ c) := by
  set k := cKind (gadAt Φ c) with hkdef
  set g : ℚ := (slotG n Φ c : ℚ)
  set Hq : ℚ := (paramH n Φ : ℚ)
  obtain ⟨hi1, hi2⟩ := aux_infix hk
  have hfl : (tmplChain k).map (RPt.inst Hq g) <:+: poly n Φ :=
    floor_infix (slotFloor_mem hc (tmplChain_mem hk))
  have hc1 := (hi1.map (RPt.inst Hq g)).trans hfl
  have hc2 := (hi2.map (RPt.inst Hq g)).trans hfl
  simp only [List.map_cons, List.map_nil] at hc1 hc2
  have htip : auxTipPt n Φ c = ratPoint ((fixR (auxTip k)).inst Hq g) := by
    rw [ratPoint_fixR]; rfl
  obtain ⟨hA, hB, hC⟩ := aux_geom hk (g : ℝ)
  refine ⟨by rw [htip]; exact mem_boundary_of_infix hc1 (by simp), fun p hp => ?_⟩
  have hq : 0 < qdet ((fixR (auxM1 k)).inst Hq g) ((fixR (auxTip k)).inst Hq g)
      ((fixR (auxM2 k)).inst Hq g) := by
    have e := det_ratPoint ((fixR (auxM1 k)).inst Hq g) ((fixR (auxTip k)).inst Hq g)
      ((fixR (auxM2 k)).inst Hq g)
    rw [ratPoint_fixR, ratPoint_fixR, ratPoint_fixR] at e
    have : (0 : ℝ) < (qdet ((fixR (auxM1 k)).inst Hq g) ((fixR (auxTip k)).inst Hq g)
      ((fixR (auxM2 k)).inst Hq g) : ℝ) := e ▸ hB
    exact_mod_cast this
  have hp' : (SP n Φ).Sees p (ratPoint ((fixR (auxTip k)).inst Hq g)) := htip ▸ hp
  have hcone := sees_corner hc1 hq hp'
  rw [ratPoint_fixR, ratPoint_fixR, ratPoint_fixR] at hcone
  refine ⟨hcone.1, hcone.2, ?_⟩
  by_contra hneg
  push Not at hneg
  obtain ⟨i, hi, hv0, hv1⟩ := edge_of_infix hc2
  rw [ratPoint_fixR] at hv0 hv1
  obtain ⟨h1, h2⟩ := hC p hcone.1 hcone.2 hneg
  refine Polygon.not_sees_of_proper_cross (simple n Φ) hi (p := p) (q := auxTipPt n Φ c) ?_ ?_ hp
  · rw [hv0, hv1]
    exact mul_neg_of_neg_of_pos hneg hA
  · rw [hv0, hv1]
    exact mul_neg_of_pos_of_neg h1 h2

/-- Bounds of the aux regions: `addLe`: `x ∈ [G + 100, G + 121]`, `y ∈ [−130, −59]`;
`addGe`: `x ∈ [G + 80, G + 84]`, `y ∈ [−113, −2]`. -/
theorem auxRegion_bounds {k : TKind} (hk : IsAdd k) {G : ℝ} {p : Point}
    (hp : p ∈ auxRegion k G) :
    G + 80 ≤ p.1 ∧ p.1 ≤ G + 121 ∧ -130 ≤ p.2 ∧ p.2 ≤ -2 ∧
      (k = .addLe → G + 100 ≤ p.1 ∧ p.2 ≤ -59) ∧ (k = .addGe → p.1 ≤ G + 84) := by
  obtain ⟨h1, h2, h3⟩ := hp
  rcases hk with rfl | rfl <;>
    simp only [auxWL, auxT0, auxTip, auxM1, auxM2, trP, det] at h1 h2 h3 <;> norm_num at h1 h2 h3
  · refine ⟨by linarith, by linarith, by linarith, by linarith,
      fun _ => ⟨by linarith, by linarith⟩, fun h => ?_⟩
    cases h
  · refine ⟨by linarith, by linarith, by linarith, by linarith, fun h => ?_,
      fun _ => by linarith⟩
    cases h

/-! ### Disjointness of the viewer sets (L4.2) -/

/-- Template inputs of the addition gadgets lie well to the right of the aux regions. -/
theorem tmplInputs_add_ok :
    (tmplInputs .addLe).all (fun t => decide (200 ≤ t.lx)) &&
      (tmplInputs .addGe).all (fun t => decide (90 ≤ t.lx)) = true := by
  decide +kernel

theorem slab_disjoint {s s' : ℝ} (h : s + 8 < s' ∨ s' + 8 < s) : Disjoint (slab s) (slab s') := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases h with h | h <;> linarith

/-- Slabs of distinct variables are disjoint. -/
theorem slab_var_var {k k' : ℕ} (h : k ≠ k') :
    Disjoint (slab ((varA Φ k : ℚ) : ℝ)) (slab ((varA Φ k' : ℚ) : ℝ)) := by
  apply slab_disjoint
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := s2_var (Φ := Φ) h
    have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
    left; push_cast; exact_mod_cast (by linarith : (varA Φ k : ℚ) + 8 < varA Φ k')
  · have := s2_var (Φ := Φ) h
    have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
    right; push_cast; exact_mod_cast (by linarith : (varA Φ k' : ℚ) + 8 < varA Φ k)

/-- The slab of a variable and the slab of an input are disjoint. -/
theorem slab_var_input {k : ℕ} (hk : k < n) {i : InputSeg} (hi : i ∈ inputs n Φ) :
    Disjoint (slab ((varA Φ k : ℚ) : ℝ)) (slab (i.b : ℝ)) := by
  apply slab_disjoint
  have := (input_delta hi hk).1
  have hH := paramH_ge_q n Φ
  left; exact_mod_cast (by linarith : (varA Φ k : ℚ) + 8 < i.b)

/-- Slabs of distinct inputs are disjoint. -/
theorem slab_input_input {i j : InputSeg} (hi : i ∈ inputs n Φ) (hj : j ∈ inputs n Φ)
    (h : i ≠ j) : Disjoint (slab (i.b : ℝ)) (slab (j.b : ℝ)) := by
  apply slab_disjoint
  have hpw : (inputs n Φ).Pairwise (fun i j => i.b + 44 ≤ j.b ∨ j.b + 44 ≤ i.b) :=
    inputs_pw.imp (fun h => Or.inl h)
  have : Std.Symm (fun i j : InputSeg => i.b + 44 ≤ j.b ∨ j.b + 44 ≤ i.b) :=
    ⟨fun _ _ h => h.symm⟩
  rcases hpw.forall hi hj h with h | h
  · left; exact_mod_cast (by linarith : i.b + 8 < j.b)
  · right; exact_mod_cast (by linarith : j.b + 8 < i.b)

/-- Two inputs at distance `< 44` are equal. -/
theorem input_eq_of_near {i j : InputSeg} (hi : i ∈ inputs n Φ) (hj : j ∈ inputs n Φ)
    (h : |(i.b : ℝ) - j.b| < 44) : i = j := by
  by_contra hne
  have hpw : (inputs n Φ).Pairwise (fun i j => i.b + 44 ≤ j.b ∨ j.b + 44 ≤ i.b) :=
    inputs_pw.imp (fun h => Or.inl h)
  have : Std.Symm (fun i j : InputSeg => i.b + 44 ≤ j.b ∨ j.b + 44 ≤ i.b) :=
    ⟨fun _ _ h => h.symm⟩
  rw [abs_lt] at h
  rcases hpw.forall hi hj hne with h' | h'
  · have : ((i.b + 44 : ℚ) : ℝ) ≤ j.b := by exact_mod_cast h'
    push_cast at this; linarith
  · have : ((j.b + 44 : ℚ) : ℝ) ≤ i.b := by exact_mod_cast h'
    push_cast at this; linarith

/-- The slab of a variable and an aux region are disjoint. -/
theorem slab_var_aux {k : ℕ} (hk : k < n) {c : ℕ} {kd : TKind} (hkd : IsAdd kd) :
    Disjoint (slab ((varA Φ k : ℚ) : ℝ)) (auxRegion kd (slotG n Φ c)) := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ hp
  have hb := auxRegion_bounds hkd hp
  have := s2_var_slot (Φ := Φ) (c := c) hk
  have hH := paramH_ge_q n Φ
  have : ((varA Φ k : ℚ) : ℝ) + 1000 ≤ (slotG n Φ c : ℝ) := by
    have : (varA Φ k : ℚ) + 1000 ≤ (slotG n Φ c : ℚ) := by linarith
    exact_mod_cast this
  linarith [hb.1]

/-- The slab of an input and an aux region are disjoint. -/
theorem slab_input_aux {i : InputSeg} (hi : i ∈ inputs n Φ) {c : ℕ} (hc : c < paramC Φ)
    (hkd : IsAdd (cKind (gadAt Φ c))) :
    Disjoint (slab (i.b : ℝ)) (auxRegion (cKind (gadAt Φ c)) (slotG n Φ c)) := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ hp
  have hb := auxRegion_bounds hkd hp
  obtain ⟨c', hc', t, ht, hbt, -, -⟩ := mem_inputs hi
  have htx := tmplInputs_x ht
  rcases lt_trichotomy c' c with hlt | rfl | hgt
  · have := s2_slot (n := n) (Φ := Φ) hlt
    have : (i.b : ℝ) + 500 ≤ (slotG n Φ c : ℝ) := by
      have : i.b + 500 ≤ (slotG n Φ c : ℚ) := by rw [hbt]; linarith [htx.2]
      exact_mod_cast this
    linarith [hb.1]
  · have hok := tmplInputs_add_ok
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    have hb' : (i.b : ℝ) = (slotG n Φ c' : ℝ) + (t.lx : ℝ) := by rw [hbt]; push_cast; ring
    rcases hkd with hkd | hkd
    · rw [hkd] at ht hb
      have : (200 : ℝ) ≤ t.lx := by exact_mod_cast hok.1 t ht
      linarith [hb.2.1]
    · rw [hkd] at ht hb
      have : (90 : ℝ) ≤ t.lx := by exact_mod_cast hok.2 t ht
      linarith [hb.2.2.2.2.2 rfl]
  · have := s2_slot (n := n) (Φ := Φ) hgt
    have : (slotG n Φ c : ℝ) + 1000 ≤ (i.b : ℝ) := by
      have : (slotG n Φ c : ℚ) + 1000 ≤ i.b := by rw [hbt]; linarith [htx.1]
      exact_mod_cast this
    linarith [hb.2.1]

/-- Aux regions of distinct slots are disjoint. -/
theorem aux_aux {c c' : ℕ} (h : c ≠ c') {kd kd' : TKind} (hkd : IsAdd kd) (hkd' : IsAdd kd') :
    Disjoint (auxRegion kd (slotG n Φ c)) (auxRegion kd' (slotG n Φ c')) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hb := auxRegion_bounds hkd hp
  have hb' := auxRegion_bounds hkd' hp'
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := s2_slot (n := n) (Φ := Φ) h
    have : (slotG n Φ c : ℝ) + 1200 ≤ (slotG n Φ c' : ℝ) := by exact_mod_cast this
    linarith [hb.2.1, hb'.1]
  · have := s2_slot (n := n) (Φ := Φ) h
    have : (slotG n Φ c' : ℝ) + 1200 ≤ (slotG n Φ c : ℝ) := by exact_mod_cast this
    linarith [hb.1, hb'.2.1]

end ArtGallery.Stade

end
