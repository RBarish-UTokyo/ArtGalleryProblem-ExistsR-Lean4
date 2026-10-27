module

public import ArtGallery.Stade.RegionSP

/-!
# The region of Stade's polygon as a union of convex pieces (proof plan L2.3)

`regionFine n Φ`: the hall, the ceiling features, the floor needles of the variables and the fine
template pieces of the slots.  **`filled_eq_regionFine`**: the region of `SP n Φ` is the union
of these pieces (`filled_eq_of_sides`, `RegionGen.lean`):
* every piece is a convex piece lying in the region (`RegionSP.lean`);
* the pieces cover the boundary (`boundary_subset_regionFine`);
* every point of every side of every piece is a boundary point or an interior point of the union
  (`side_regionFine`): sides are walls (edges of the polygon), glued exactly to a side of another
  piece, or mouths of floor / ceiling features lying on the floor / ceiling side of the hall (two
  half-discs); the floor and ceiling sides of the hall are covered by the comb chains and the
  mouths (`comb_floor_cover`, `comb_ceil_cover`).

**Bridge to `GuardRegion.lean`**: the coarse pieces `regionPieces n Φ` have the same point sets
(`filled_subset_regionPieces'`, `regionPieces_subset_filled'`).
-/

@[expose] public section

namespace ArtGallery.Stade

open Set ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational
open ArtGallery.Geometry (lerp)

variable {n : ℕ} {Φ : List Constraint}

/-! ### Comb cover for the ceiling -/

/-- **Comb cover (ceiling).** A point of the ceiling line between `x_lo` and `s` lies on the comb
chain (from `s` leftwards) or in the open mouth of one of its features. -/
theorem comb_ceil_cover {Y xlo xhi : ℝ} : ∀ (fs : List (List Point)) (s : ℝ), xlo ≤ s →
    (∀ f ∈ fs, CeilFeature Y xlo xhi f) → (∀ f ∈ fs, (fstPt f).1 < s) →
    fs.Pairwise (fun f g => (fstPt g).1 < (lstPt f).1) → ∀ x, xlo ≤ x → x ≤ s →
    ((x, Y) : Point) ∈ chainSet ((s, Y) :: fs.flatten ++ [(xlo, Y)]) ∨
      ∃ f ∈ fs, (lstPt f).1 < x ∧ x < (fstPt f).1
  | [], s, hs, _, _, _, x, hx1, hx2 => by
    left
    simp only [List.flatten_nil, List.nil_append, List.cons_append, chainSet_cons_cons,
      chainSet_single, union_empty]
    rcases eq_or_lt_of_le hs with h | h
    · subst h
      have : x = xlo := le_antisymm hx2 hx1
      subst this; exact Geometry.left_mem_segment _ _
    · have hne : s - xlo ≠ 0 := ne_of_gt (by linarith)
      refine ⟨(s - x) / (s - xlo), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only; field_simp; ring
      · simp
  | f :: fs, s, hs, hF, hfst, hpw, x, hx1, hx2 => by
    obtain ⟨hlen, -, hfy, hly, hfl, -, hxs⟩ := hF f (by simp)
    set a := fstPt f
    set q := lstPt f
    have hqx := (hxs q (lstPt_mem hlen)).1
    have hsa : a.1 < s := hfst f (by simp)
    have hpw' := List.pairwise_cons.1 hpw
    set f' := f.tail.dropLast
    have hfdec : f = a :: (f' ++ [q]) := decomp_of_two_le hlen
    have e : (s, Y) :: (f :: fs).flatten ++ [(xlo, Y)] =
        ((s, Y) :: (a :: f')) ++ q :: (fs.flatten ++ [(xlo, Y)]) := by
      conv_lhs => rw [List.flatten_cons, hfdec]
      simp
    rw [e, chainSet_append_cons]
    by_cases hxa : a.1 ≤ x
    · left; left
      have e2 : (s, Y) :: (a :: f') ++ [q] = (s, Y) :: a :: (f' ++ [q]) := rfl
      rw [e2, chainSet_cons_cons]
      left
      have ha : a = (a.1, Y) := Prod.ext rfl hfy
      rw [ha]
      have hne : s - a.1 ≠ 0 := ne_of_gt (by linarith)
      refine ⟨(s - x) / (s - a.1), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only; field_simp; ring
      · simp
    · push Not at hxa
      by_cases hxq : q.1 < x
      · exact Or.inr ⟨f, by simp, hxq, hxa⟩
      · push Not at hxq
        have ih := comb_ceil_cover fs q.1 (by linarith) (fun g hg => hF g (by simp [hg]))
          (fun g hg => hpw'.1 g hg) hpw'.2 x hx1 hxq
        rcases ih with h | ⟨g, hg, hg1, hg2⟩
        · left; right
          have hq : q = (q.1, Y) := Prod.ext rfl hly
          rw [hq]; simpa using h
        · exact Or.inr ⟨g, by simp [hg], hg1, hg2⟩

/-! ### The pieces -/

/-- **The fine pieces of the region**: the hall, the ceiling features, the floor needles of the
variables and the fine template pieces of the slots. -/
noncomputable def regionFine (n : ℕ) (Φ : List Constraint) : List Polygon :=
  [hallPoly n Φ] ++ (ceilFeats n Φ).map (fun f => Polygon.mk (f.map ratPoint)) ++
    (List.range n).map (fun k => needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ++
    (List.range (paramC Φ)).flatMap (slotFine n Φ)

theorem mem_regionFine {K : Polygon} :
    K ∈ regionFine n Φ ↔ K = hallPoly n Φ ∨
      (∃ f ∈ ceilFeats n Φ, K = Polygon.mk (f.map ratPoint)) ∨
      (∃ k < n, K = needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ∨
      (∃ c < paramC Φ, ∃ l ∈ fineP (cKind (gadAt Φ c)),
        K = rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l) := by
  simp only [regionFine, slotFine, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    List.mem_map, List.mem_range, List.mem_flatMap]
  constructor
  · rintro (((h | ⟨f, hf, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨c, hc, l, hl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨f, hf, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, hc, l, hl, rfl⟩))
  · rintro (h | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨f, hf, rfl⟩))
    · exact Or.inl (Or.inr ⟨k, hk, rfl⟩)
    · exact Or.inr ⟨c, hc, l, hl, rfl⟩

theorem regionFine_isPiece {K : Polygon} (hK : K ∈ regionFine n Φ) : IsPiece K := by
  rcases mem_regionFine.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩
  · exact hallPoly_isPiece n Φ
  · exact ceil_isPiece hf
  · exact needle_isPiece _ (by have := paramH_ge_r n Φ; show (0 : ℝ) < (paramH n Φ : ℝ); linarith)
  · exact (fine_isPiece hl).1

theorem regionFine_sub {K : Polygon} (hK : K ∈ regionFine n Φ) : piece K ⊆ (SP n Φ).filled := by
  rcases mem_regionFine.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩
  · exact hall_sub
  · exact ceil_sub hf
  · exact needle_sub hk
  · exact fine_sub hc hl

/-- The union of the fine pieces. -/
noncomputable abbrev UF (n : ℕ) (Φ : List Constraint) : Set Point :=
  pieceUnion {K | K ∈ regionFine n Φ}

theorem piece_sub_UF {K : Polygon} (hK : K ∈ regionFine n Φ) : piece K ⊆ UF n Φ :=
  piece_subset_pieceUnion (S := {K | K ∈ regionFine n Φ}) hK

theorem hall_mem : hallPoly n Φ ∈ regionFine n Φ := mem_regionFine.2 (Or.inl rfl)

theorem mem_hall' {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ (xR n Φ : ℝ)) (h3 : -1 ≤ p.2)
    (h4 : p.2 ≤ 2 * (paramH n Φ : ℝ)) : p ∈ UF n Φ :=
  piece_sub_UF hall_mem (mem_hall.2 ⟨h1, h2, h3, h4⟩)

/-! ### The boundary is covered -/

theorem lstPt_map {l : List RPt} (hl : l ≠ []) (g : RPt → Point) :
    lstPt (l.map g) = g (l.getLastD 0) := by
  unfold lstPt
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map]
  cases h : l.getLast? with
  | none => simp [List.getLast?_eq_none_iff] at h; exact absurd h hl
  | some a => rfl

theorem fstPt_map {l : List RPt} (hl : l ≠ []) (g : RPt → Point) :
    fstPt (l.map g) = g (l.headD 0) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => rfl

/-- **The pieces cover the boundary.** -/
theorem boundary_subset_regionFine : (SP n Φ).boundary ⊆ UF n Φ := by
  intro p hp
  have hHr := paramH_ge_r n Φ
  have hxr := xL_lt_xR_r n Φ
  rcases boundary_decomp hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨f, hf, hpf⟩ | ⟨f, hf, hpf⟩
  · exact mem_hall' h2 h3 (by linarith) (by linarith)
  · exact mem_hall' h2 h3 (by linarith) (by linarith)
  · rcases h3 with h | h
    · exact mem_hall' (le_of_eq h.symm) (by rw [h]; linarith) h1 h2
    · exact mem_hall' (by rw [h]; linarith) (le_of_eq h) h1 h2
  · rcases mem_floorFeats hf with ⟨k, hk, rfl⟩ | ⟨c, hc, ch, hch, rfl⟩
    · have hK : needleL (varA Φ k : ℝ) (-1) (hH n Φ) ∈ regionFine n Φ :=
        mem_regionFine.2 (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
      refine piece_sub_UF hK ?_
      rw [needle_real] at hpf
      have hKp := regionFine_isPiece hK
      refine chainSet_subset_of_convex (convex_piece _) (fun q hq => ?_) hpf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact vtx_mem_piece hKp (k := 0) (by simp [needleL, tri, Polygon.n])
      · have := vtx_mem_piece hKp (k := 1) (by simp [needleL, tri, Polygon.n])
        simpa [needleL, tri, Polygon.vtx, hH] using this
      · exact vtx_mem_piece hKp (k := 2) (by simp [needleL, tri, Polygon.n])
    · rw [slot_map] at hpf
      refine chainSet_subset_idx _ (fun j hj => ?_) hpf
      simp only [List.length_map] at hj
      obtain ⟨l, hl, h1, h2⟩ := tP_cover hch (mem_pairs_of_lt ch j hj)
      have hK : rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l ∈ regionFine n Φ :=
        mem_regionFine.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, l, hl, rfl⟩)))
      refine (Geometry.segment_subset_of_convex (convex_piece _) ?_ ?_).trans (piece_sub_UF hK)
      · simpa using inB_sound (G := (slotG n Φ c : ℝ)) hHr h1
      · simpa using inB_sound (G := (slotG n Φ c : ℝ)) hHr h2
  · have hK : Polygon.mk (f.map ratPoint) ∈ regionFine n Φ :=
      mem_regionFine.2 (Or.inr (Or.inl ⟨f, hf, rfl⟩))
    refine piece_sub_UF hK (chainSet_subset_of_convex (convex_piece _) (fun q hq => ?_) hpf)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have := vtx_mem_piece (regionFine_isPiece hK) (k := j) hj
    rwa [mk_vtx _ hj] at this

/-! ### Sides -/

theorem side_cases {K : Polygon} {j : ℕ} {y : Point} (hy : y ∈ K.edge j) :
    y = K.vtx j ∨ y = K.vtx ((j + 1) % K.n) ∨
      ∃ t, 0 < t ∧ t < 1 ∧ y = lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) t := by
  obtain ⟨t, h0, h1, rfl⟩ := hy
  rcases h0.lt_or_eq with h0 | rfl
  · rcases h1.lt_or_eq with h1 | rfl
    · exact Or.inr (Or.inr ⟨t, h0, h1, rfl⟩)
    · right; left; ext <;> simp
  · left; ext <;> simp

theorem edge_sub_of_wall {K : Polygon} {j : ℕ} (hw : IsWall (SP n Φ) K j) :
    K.edge j ⊆ (SP n Φ).boundary := by
  obtain ⟨i, hi, h1, h2⟩ := hw
  intro y hy
  refine ⟨i, hi, ?_⟩
  unfold Polygon.edge at hy ⊢
  rw [h1, h2]; exact hy

/-- The vertices of the pieces lie on the boundary. -/
theorem regionFine_vtx {K : Polygon} (hK : K ∈ regionFine n Φ) {j : ℕ} (hj : j < K.n) :
    K.vtx j ∈ (SP n Φ).boundary := by
  rcases mem_regionFine.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩
  · have hmem : ∀ q ∈ ([(xL n Φ, (-1 : ℚ)), (xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ)),
        (xL n Φ, 2 * (paramH n Φ : ℚ))] : List (ℚ × ℚ)), ratPoint q ∈ (SP n Φ).boundary := by
      intro q hq
      refine list_mem_boundary ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      simp only [poly, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases hq with rfl | rfl | rfl | rfl <;> simp
    rw [hall_n] at hj
    interval_cases j
    · simpa [ratPoint, hallPoly, quad, Polygon.vtx] using hmem (xL n Φ, -1) (by simp)
    · simpa [ratPoint, hallPoly, quad, Polygon.vtx] using hmem (xR n Φ, -1) (by simp)
    · simpa [ratPoint, hallPoly, quad, Polygon.vtx] using
        hmem (xR n Φ, 2 * (paramH n Φ : ℚ)) (by simp)
    · simpa [ratPoint, hallPoly, quad, Polygon.vtx] using
        hmem (xL n Φ, 2 * (paramH n Φ : ℚ)) (by simp)
  · rw [n_map_ratPoint] at hj
    rw [vtx_map_ratPoint]
    refine list_mem_boundary ((ceil_infix hf).subset ?_)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  · have h := varW2_infix (Φ := Φ) hk
    simp only [needleL, tri, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simpa [ratPoint, needleL, tri, Polygon.vtx] using
        mem_boundary_of_infix h (u := ((varA Φ k : ℚ) - 1 / 4, -1)) (by simp)
    · simpa [ratPoint, needleL, tri, Polygon.vtx, hH] using
        mem_boundary_of_infix h (u := ((varA Φ k : ℚ), -1 - (paramH n Φ : ℚ))) (by simp)
    · simpa [ratPoint, needleL, tri, Polygon.vtx] using
        mem_boundary_of_infix h (u := ((varA Φ k : ℚ), -1)) (by simp)
  · exact (fine_vtx hc hl (by rw [rpoly_n] at hj; exact hj)).2.2.2

/-- **Floor mouths.** A point in the open mouth of a floor feature whose mouth is a side of a
piece is an interior point of the union. -/
theorem floor_mouth {K : Polygon} (hKS : K ∈ regionFine n Φ) {j : ℕ} (hj : j < K.n)
    {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) (h1 : K.vtx j = lstPt (f.map ratPoint))
    (h2 : K.vtx ((j + 1) % K.n) = fstPt (f.map ratPoint)) {x : ℝ}
    (hx1 : (fstPt (f.map ratPoint)).1 < x) (hx2 : x < (lstPt (f.map ratPoint)).1) :
    ((x, -1) : Point) ∈ interior (UF n Φ) := by
  obtain ⟨hlen, -, hfy, hly, hfl, -, hxs⟩ := floor_feature f hf
  have hfx := (hxs _ (fstPt_mem hlen)).1
  have hlx := (hxs _ (lstPt_mem hlen)).2
  norm_num at hfy hly
  have e1 : K.vtx j = ((lstPt (f.map ratPoint)).1, -1) := by rw [h1]; exact Prod.ext rfl hly
  have e2 : K.vtx ((j + 1) % K.n) = ((fstPt (f.map ratPoint)).1, -1) := by
    rw [h2]; exact Prod.ext rfl hfy
  have h := mem_interior_union_horiz (hallPoly_isPiece n Φ) (regionFine_isPiece hKS) (j := 0)
    (j' := j) (by rw [hall_n]; norm_num) hj (hall_vtx.1) (by rw [hall_n]; exact hall_vtx.2.1)
    e1 e2 (by linarith) (by linarith) hx1 hx2
  exact interior_mono (union_subset (piece_sub_UF hall_mem) (piece_sub_UF hKS)) h

/-- **Ceiling mouths.** -/
theorem ceil_mouth {K : Polygon} (hKS : K ∈ regionFine n Φ) {j : ℕ} (hj : j < K.n)
    {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) (h1 : K.vtx j = lstPt (f.map ratPoint))
    (h2 : K.vtx ((j + 1) % K.n) = fstPt (f.map ratPoint)) {x : ℝ}
    (hx1 : (lstPt (f.map ratPoint)).1 < x) (hx2 : x < (fstPt (f.map ratPoint)).1) :
    ((x, 2 * (paramH n Φ : ℝ)) : Point) ∈ interior (UF n Φ) := by
  obtain ⟨hlen, -, hfy, hly, hfl, -, hxs⟩ := ceil_feature f hf
  have hfx := (hxs _ (fstPt_mem hlen)).2
  have hlx := (hxs _ (lstPt_mem hlen)).1
  push_cast at hfy hly
  have e1 : K.vtx j = ((lstPt (f.map ratPoint)).1, 2 * (paramH n Φ : ℝ)) := by
    rw [h1]; exact Prod.ext rfl hly
  have e2 : K.vtx ((j + 1) % K.n) = ((fstPt (f.map ratPoint)).1, 2 * (paramH n Φ : ℝ)) := by
    rw [h2]; exact Prod.ext rfl hfy
  have h := mem_interior_union_horiz (regionFine_isPiece hKS) (hallPoly_isPiece n Φ) (j := j)
    (j' := 2) hj (by rw [hall_n]; norm_num) e1 e2 (hall_vtx.2.2.1)
    (by rw [hall_n]; exact hall_vtx.2.2.2) hx1 hx2 (by linarith) (by linarith)
  exact interior_mono (union_subset (piece_sub_UF hKS) (piece_sub_UF hall_mem)) h

/-- A point of an open horizontal side. -/
theorem lerp_horiz {a b : Point} (ha : a.2 = b.2) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    lerp a b t = ((lerp a b t).1, b.2) ∧ min a.1 b.1 ≤ (lerp a b t).1 ∧
      (lerp a b t).1 ≤ max a.1 b.1 ∧ (a.1 < b.1 → a.1 < (lerp a b t).1 ∧ (lerp a b t).1 < b.1) ∧
      (b.1 < a.1 → b.1 < (lerp a b t).1 ∧ (lerp a b t).1 < a.1) := by
  simp only [lerp]
  refine ⟨Prod.ext rfl (by simp only; rw [ha]; ring), ?_, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · rcases le_total a.1 b.1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total a.1 b.1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  all_goals nlinarith

/-- The top piece of a floor feature: a piece one of whose sides is its mouth. -/
theorem floor_top {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) :
    ∃ K ∈ regionFine n Φ, ∃ j < K.n, K.vtx j = lstPt (f.map ratPoint) ∧
      K.vtx ((j + 1) % K.n) = fstPt (f.map ratPoint) := by
  rcases mem_floorFeats hf with ⟨k, hk, rfl⟩ | ⟨c, hc, ch, hch, rfl⟩
  · refine ⟨needleL (varA Φ k : ℝ) (-1) (hH n Φ),
      mem_regionFine.2 (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))), 2,
      by simp [needleL, tri, Polygon.n], ?_, ?_⟩ <;> rw [needle_real] <;>
      simp [needleL, tri, Polygon.vtx, Polygon.n, lstPt, fstPt]
  · obtain ⟨l, hl, j, hj, h1, h2⟩ := tP_mouth hch
    have hne : ch ≠ [] := by
      have := floor_len hf
      simp only [List.length_map] at this
      exact List.ne_nil_of_length_pos (by omega)
    refine ⟨rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l,
      mem_regionFine.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, l, hl, rfl⟩))), j,
      by rw [rpoly_n]; exact hj, ?_, ?_⟩
    · rw [rpoly_vtx _ _ l hj, slot_map, lstPt_map hne, h1]
    · rw [rpoly_vtx_succ _ _ l hj, slot_map, fstPt_map hne, h2]

/-- Points of a side with a classified interior. -/
theorem side_of_open {K : Polygon} (hKS : K ∈ regionFine n Φ) {j : ℕ} (hj : j < K.n)
    (hopen : ∀ t, 0 < t → t < 1 → lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) t ∈ interior (UF n Φ))
    {y : Point} (hy : y ∈ K.edge j) : y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  rcases side_cases hy with rfl | rfl | ⟨t, h0, h1, rfl⟩
  · exact Or.inl (regionFine_vtx hKS hj)
  · exact Or.inl (regionFine_vtx hKS (Nat.mod_lt _ (by omega)))
  · exact Or.inr (hopen t h0 h1)

/-- Sides of the hall. -/
theorem hall_sides {j : ℕ} (hj : j < (hallPoly n Φ).n) {y : Point} (hy : y ∈ (hallPoly n Φ).edge j) :
    y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  rw [hall_n] at hj
  have hHr := paramH_ge_r n Φ
  have hxr := xL_lt_xR_r n Φ
  set F := (floorFeats n Φ).map (List.map ratPoint) with hF
  set C := (ceilFeats n Φ).map (List.map ratPoint) with hC
  have hFF : ∀ f ∈ F, FloorFeature (((-1 : ℚ)) : ℝ) (xL n Φ : ℝ) (xR n Φ : ℝ) f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact floor_feature g hg
  have hCC : ∀ f ∈ C, CeilFeature (((2 * (paramH n Φ : ℚ) : ℚ)) : ℝ) (xL n Φ : ℝ) (xR n Φ : ℝ)
      f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact ceil_feature g hg
  interval_cases j
  · -- the floor side
    obtain ⟨t, h0, h1, rfl⟩ := hy
    simp only [hall_vtx.1, show (0 + 1) % (hallPoly n Φ).n = 1 from rfl, hall_vtx.2.1] at *
    set x := (xL n Φ : ℝ) + t * ((xR n Φ : ℝ) - (xL n Φ : ℝ))
    have hx1 : (xL n Φ : ℝ) ≤ x := by nlinarith
    have hx2 : x ≤ (xR n Φ : ℝ) := by nlinarith
    have hpt : (((xL n Φ : ℝ) + t * ((xR n Φ : ℝ) - (xL n Φ : ℝ)), -1 + t * (-1 - -1)) : Point) =
        (x, (((-1 : ℚ)) : ℝ)) := by ext <;> simp [x]
    show (((xL n Φ : ℝ) + t * ((xR n Φ : ℝ) - (xL n Φ : ℝ)), -1 + t * (-1 - -1)) : Point) ∈ _ ∨ _
    rw [hpt]
    rcases comb_floor_cover F (xL n Φ : ℝ) hxr.le hFF
      (fun f hf => ((hFF f hf).2.2.2.2.2.2 _ (fstPt_mem (hFF f hf).1)).1)
      (by rw [hF, List.pairwise_map]; exact floor_pw.imp (fun h => h.2)) x hx1 hx2 with h | ⟨f, hf, h1, h2⟩
    · left
      refine chainSet_subset_boundary ?_ h
      rw [poly_map]
      exact ⟨[], (ceilFeats n Φ |>.map (List.map ratPoint)).flatten.cons
        ((xR n Φ : ℝ), (((2 * (paramH n Φ : ℚ) : ℚ)) : ℝ)) ++
        [((xL n Φ : ℝ), (((2 * (paramH n Φ : ℚ) : ℚ)) : ℝ))], by simp [hF]⟩
    · right
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      obtain ⟨K, hK, j, hj, e1, e2⟩ := floor_top hg
      have := floor_mouth hK hj hg e1 e2 h1 h2
      simpa using this
  · exact Or.inl (edge_sub_of_wall hall_wall hy)
  · -- the ceiling side
    obtain ⟨t, h0, h1, rfl⟩ := hy
    simp only [hall_vtx.2.2.1, show (2 + 1) % (hallPoly n Φ).n = 3 from rfl, hall_vtx.2.2.2] at *
    set x := (xR n Φ : ℝ) + t * ((xL n Φ : ℝ) - (xR n Φ : ℝ))
    have hx1 : (xL n Φ : ℝ) ≤ x := by nlinarith
    have hx2 : x ≤ (xR n Φ : ℝ) := by nlinarith
    have hpt : (((xR n Φ : ℝ) + t * ((xL n Φ : ℝ) - (xR n Φ : ℝ)),
        2 * hH n Φ + t * (2 * hH n Φ - 2 * hH n Φ)) : Point) =
        (x, (((2 * (paramH n Φ : ℚ) : ℚ)) : ℝ)) := by ext <;> simp [x, hH]
    show (((xR n Φ : ℝ) + t * ((xL n Φ : ℝ) - (xR n Φ : ℝ)),
        2 * hH n Φ + t * (2 * hH n Φ - 2 * hH n Φ)) : Point) ∈ _ ∨ _
    rw [hpt]
    rcases comb_ceil_cover C (xR n Φ : ℝ) hxr.le hCC
      (fun f hf => ((hCC f hf).2.2.2.2.2.2 _ (fstPt_mem (hCC f hf).1)).2)
      (by rw [hC, List.pairwise_map]; exact ceil_pw.imp (fun h => h.2)) x hx1 hx2 with h | ⟨f, hf, h1, h2⟩
    · left
      refine chainSet_subset_boundary ?_ h
      rw [poly_map]
      exact ⟨[((xL n Φ : ℝ), (((-1 : ℚ)) : ℝ))] ++ (floorFeats n Φ |>.map (List.map ratPoint)).flatten ++
        [((xR n Φ : ℝ), (((-1 : ℚ)) : ℝ))], [], by simp [hC]⟩
    · right
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      have hglen := ceil_len hg
      have hK : Polygon.mk (g.map ratPoint) ∈ regionFine n Φ :=
        mem_regionFine.2 (Or.inr (Or.inl ⟨g, hg, rfl⟩))
      set M := g.map ratPoint
      have hM : 2 ≤ M.length := by
        show 2 ≤ (g.map ratPoint).length; rw [List.length_map]; omega
      have hn : (Polygon.mk M).n = M.length := rfl
      have := ceil_mouth hK (j := M.length - 1) (show M.length - 1 < M.length by omega) hg
        (by rw [mk_vtx M (j := M.length - 1) (by omega), lstPt_eq (M := M) (by omega)])
        (by rw [hn, show M.length - 1 + 1 = M.length by omega, Nat.mod_self,
          mk_vtx M (j := 0) (by omega), fstPt_eq (M := M) (by omega)]) h1 h2
      simpa using this
  · -- the left wall: the closing edge of the polygon
    left
    have hlen := poly_length_ge n Φ
    refine edge_sub_of_wall ⟨(poly n Φ).length - 1, by rw [n_map_ratPoint]; omega, ?_, ?_⟩ hy
    · rw [vtx_map_ratPoint]
      have := poly_last n Φ
      simp only [Prod.zero_eq_mk] at this ⊢
      rw [this]; simp [ratPoint, hallPoly, quad, Polygon.vtx, hH]
    · rw [n_map_ratPoint, show (poly n Φ).length - 1 + 1 = (poly n Φ).length by omega,
        Nat.mod_self, vtx_map_ratPoint]
      have := poly_head n Φ
      simp only [Prod.zero_eq_mk] at this ⊢
      rw [this]; simp [ratPoint, hallPoly, quad, Polygon.vtx, Polygon.n]

/-- Sides of the ceiling features. -/
theorem ceil_sides {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) {j : ℕ}
    (hj : j < (Polygon.mk (f.map ratPoint)).n) {y : Point}
    (hy : y ∈ (Polygon.mk (f.map ratPoint)).edge j) :
    y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  have hK : Polygon.mk (f.map ratPoint) ∈ regionFine n Φ :=
    mem_regionFine.2 (Or.inr (Or.inl ⟨f, hf, rfl⟩))
  have hn : (Polygon.mk (f.map ratPoint)).n = f.length := n_map_ratPoint f
  have hlen := ceil_len hf
  rw [hn] at hj
  rcases Nat.lt_or_ge (j + 1) f.length with hj1 | hj1
  · left
    refine edge_sub_of_wall ?_ hy
    obtain ⟨i, hi, h1, h2⟩ :=
      edge_of_infix ((infix_of_mem_pairs (mem_pairs_of_lt f j hj1)).trans (ceil_infix hf))
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1, vtx_map_ratPoint, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    · rw [h2, hn, Nat.mod_eq_of_lt hj1, vtx_map_ratPoint, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj1]; rfl
  · obtain rfl : j = f.length - 1 := by omega
    have hne : f ≠ [] := List.ne_nil_of_length_pos (by omega)
    have e1 : (Polygon.mk (f.map ratPoint)).vtx (f.length - 1) = lstPt (f.map ratPoint) := by
      rw [vtx_map_ratPoint]
      cases f using List.reverseRecOn with
      | nil => exact absurd rfl hne
      | append_singleton l a _ =>
        simp [lstPt, List.getD_eq_getElem?_getD]
    have e2 : (Polygon.mk (f.map ratPoint)).vtx ((f.length - 1 + 1) %
        (Polygon.mk (f.map ratPoint)).n) = fstPt (f.map ratPoint) := by
      rw [hn, show f.length - 1 + 1 = f.length by omega, Nat.mod_self, vtx_map_ratPoint]
      cases f with
      | nil => exact absurd rfl hne
      | cons a l => rfl
    obtain ⟨-, -, hfy, hly, hfl, -, -⟩ := ceil_feature f hf
    refine side_of_open hK (by rw [hn]; omega) (fun t ht0 ht1 => ?_) hy
    rw [e1, e2]
    obtain ⟨hpt, -, -, hb, -⟩ := lerp_horiz (a := lstPt (f.map ratPoint))
      (b := fstPt (f.map ratPoint)) (by rw [hfy, hly]) ht0 ht1
    obtain ⟨hx1, hx2⟩ := hb hfl
    rw [hpt, hfy]
    have := ceil_mouth hK (j := f.length - 1) (by rw [hn]; omega) hf e1 e2 hx1 hx2
    push_cast; exact this

/-- Sides of the floor needles of the variables. -/
theorem needle_sides {k : ℕ} (hk : k < n) {j : ℕ}
    (hj : j < (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).n) {y : Point}
    (hy : y ∈ (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).edge j) :
    y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  have hK : needleL (varA Φ k : ℝ) (-1) (hH n Φ) ∈ regionFine n Φ :=
    mem_regionFine.2 (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  have h := varW2_infix (Φ := Φ) hk
  simp only [needleL, tri, Polygon.n, List.length_cons, List.length_nil] at hj
  interval_cases j
  · left
    refine edge_sub_of_wall ?_ hy
    obtain ⟨i, hi, h1, h2⟩ := edge_of_infix ((List.infix_append [] _ [((varA Φ k : ℚ), -1)]).trans h)
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1]; simp [ratPoint, needleL, tri, Polygon.vtx]
    · rw [h2]; simp [ratPoint, needleL, tri, Polygon.vtx, Polygon.n, hH]
  · left
    refine edge_sub_of_wall ?_ hy
    obtain ⟨i, hi, h1, h2⟩ := edge_of_infix ((List.infix_append [((varA Φ k : ℚ) - 1 / 4, -1)] _
      []).trans h)
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1]; simp [ratPoint, needleL, tri, Polygon.vtx, hH]
    · rw [h2]; simp [ratPoint, needleL, tri, Polygon.vtx, Polygon.n]
  · have hf := varFloor_mem (n := n) (Φ := Φ) hk
    have e1 : (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).vtx 2 =
        lstPt ((needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k))).map ratPoint) := by
      rw [needle_real]; simp [needleL, tri, Polygon.vtx, lstPt]
    have e2 : (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).vtx
        ((2 + 1) % (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).n) =
        fstPt ((needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k))).map ratPoint) := by
      rw [needle_real]; simp [needleL, tri, Polygon.vtx, Polygon.n, fstPt]
    refine side_of_open hK (by simp [needleL, tri, Polygon.n]) (fun t ht0 ht1 => ?_) hy
    rw [e1, e2]
    rw [needle_real] at e1 e2 ⊢
    simp only [lstPt, fstPt, List.getLastD_cons, List.getLastD_nil, List.headD_cons] at e1 e2 ⊢
    obtain ⟨hpt, -, -, -, hb⟩ := lerp_horiz (a := ((varA Φ k : ℝ), -1))
      (b := ((varA Φ k : ℝ) - 1 / 4, -1)) rfl ht0 ht1
    obtain ⟨hx1, hx2⟩ := hb (by simp only; linarith)
    rw [hpt]
    have := floor_mouth hK (j := 2) (by simp [needleL, tri, Polygon.n]) hf
      (by rw [needle_real]; simp [needleL, tri, Polygon.vtx, lstPt])
      (by rw [needle_real]; simp [needleL, tri, Polygon.vtx, Polygon.n, fstPt])
      (x := (lerp ((varA Φ k : ℝ), -1) ((varA Φ k : ℝ) - 1 / 4, -1) t).1)
      (by rw [needle_real]; simpa [fstPt] using hx1)
      (by rw [needle_real]; simpa [lstPt] using hx2)
    simpa using this

/-- Sides of the fine template pieces. -/
theorem fine_sides {c : ℕ} (hc : c < paramC Φ) {l : List RPt}
    (hl : l ∈ fineP (cKind (gadAt Φ c))) {j : ℕ}
    (hj : j < (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).n) {y : Point}
    (hy : y ∈ (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).edge j) :
    y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  have hK : rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l ∈ regionFine n Φ :=
    mem_regionFine.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, l, hl, rfl⟩)))
  have hH := paramH_ge_r n Φ
  have hj' : j < l.length := by rw [rpoly_n] at hj; exact hj
  rcases tP_sides hl hj' with hw | hg | hm
  · left
    refine edge_sub_of_wall ?_ hy
    obtain ⟨ch, hch, hab⟩ := wallB_spec hw
    obtain ⟨i, hi, h1, h2⟩ :=
      edge_of_infix ((hab.map (RPt.inst (paramH n Φ) (slotG n Φ c))).trans
        (floor_infix (slotFloor_mem hc hch)))
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1, slot_pt, rpoly_vtx _ _ l hj']
    · rw [h2, slot_pt, rpoly_vtx_succ _ _ l hj']
  · obtain ⟨l', hl', j', hj'', e1, e2⟩ := glueB_spec hg
    have hK' : rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l' ∈ regionFine n Φ :=
      mem_regionFine.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, l', hl', rfl⟩)))
    have hglue : Glued (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l)
        (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l') j j' := by
      refine ⟨by rw [rpoly_n]; exact hj'', ?_, ?_⟩
      · rw [rpoly_vtx _ _ l' hj'', rpoly_vtx_succ _ _ l hj', e1]
      · rw [rpoly_vtx_succ _ _ l' hj'', rpoly_vtx _ _ l hj', e2]
    refine side_of_open hK hj (fun t ht0 ht1 => ?_) hy
    exact interior_mono (union_subset (piece_sub_UF hK) (piece_sub_UF hK'))
      (mem_interior_union_of_glued (fine_isPiece hl).1 (fine_isPiece hl').1 hj hglue ht0 ht1)
  · obtain ⟨ch, hch, e1, e2⟩ := mouthB_spec hm
    have hf := slotFloor_mem (n := n) hc hch
    have hne : ch ≠ [] := by
      have := floor_len hf
      simp only [List.length_map] at this
      exact List.ne_nil_of_length_pos (by omega)
    have v1 : (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx j =
        lstPt ((ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))).map ratPoint) := by
      rw [rpoly_vtx _ _ l hj', slot_map, lstPt_map hne, e1]
    have v2 : (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx
        ((j + 1) % (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).n) =
        fstPt ((ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))).map ratPoint) := by
      rw [rpoly_vtx_succ _ _ l hj', slot_map, fstPt_map hne, e2]
    obtain ⟨hlen, -, hfy, hly, hfl, -, -⟩ := floor_feature _ hf
    refine side_of_open hK hj (fun t ht0 ht1 => ?_) hy
    rw [v1, v2]
    obtain ⟨hpt, -, -, -, hb⟩ := lerp_horiz
      (a := lstPt ((ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))).map ratPoint))
      (b := fstPt ((ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))).map ratPoint))
      (by rw [hfy, hly]) ht0 ht1
    obtain ⟨hx1, hx2⟩ := hb hfl
    rw [hpt, hfy]
    have := floor_mouth hK hj hf v1 v2 hx1 hx2
    simpa [lerp, List.map_map] using this

/-- **Sides.** Every point of every side of every piece is a boundary point or an interior point
of the union. -/
theorem side_regionFine {K : Polygon} (hK : K ∈ regionFine n Φ) {j : ℕ} (hj : j < K.n)
    {y : Point} (hy : y ∈ K.edge j) : y ∈ (SP n Φ).boundary ∨ y ∈ interior (UF n Φ) := by
  rcases mem_regionFine.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩
  · exact hall_sides hj hy
  · exact ceil_sides hf hj hy
  · exact needle_sides hk hj hy
  · exact fine_sides hc hl hj hy

/-! ### The region -/

/-- **L2.3: the region of Stade's polygon is the union of the fine pieces.** -/
theorem filled_eq_regionFine (n : ℕ) (Φ : List Constraint) : (SP n Φ).filled = UF n Φ :=
  filled_eq_of_sides (simple n Φ) _ (fun _ hK => regionFine_isPiece hK)
    (fun _ hK => regionFine_sub hK) boundary_subset_regionFine
    (fun _ hK _ hj _ hy => side_regionFine hK hj hy) (by simp [regionFine])

/-! ### The coarse pieces of `GuardRegion.lean` -/

theorem coarse_piece_eq {c : ℕ} {k : TKind} {i : ℕ} (hi : i < (fineP k).length) :
    piece (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) (fineP k)[i]) =
      piece (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ)
        ((coarseP k)[i]'(by rw [← tP_len]; exact hi))) :=
  piece_eq_of_inB (paramH_ge_r n Φ) (tP_piece (List.getElem_mem hi))
    (tP_cpiece (List.getElem_mem _)) (tP_same hi).1 (tP_same hi).2

/-- **L2.3 (⊆) for `regionPieces`.** -/
theorem filled_subset_regionPieces' (n : ℕ) (Φ : List Constraint) :
    (SP n Φ).filled ⊆ ⋃ K ∈ regionPieces n Φ, piece K := by
  rw [filled_eq_regionFine]
  intro x hx
  obtain ⟨K, hK, hxK⟩ := mem_pieceUnion.1 hx
  simp only [Set.mem_iUnion]
  rcases mem_regionFine.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, l, hl, rfl⟩
  · exact ⟨_, mem_regionPieces.2 (Or.inl rfl), hxK⟩
  · exact ⟨_, mem_regionPieces.2 (Or.inr (Or.inl ⟨f, hf, rfl⟩)), hxK⟩
  · exact ⟨_, mem_regionPieces.2 (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))), hxK⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    refine ⟨_, mem_regionPieces.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, ?_⟩))),
      (coarse_piece_eq (c := c) hi) ▸ hxK⟩
    rw [slotPieces_eq]
    exact List.mem_map.2 ⟨_, List.getElem_mem _, rfl⟩

/-- **L2.3 (⊇) for `regionPieces`.** -/
theorem regionPieces_subset_filled' (n : ℕ) (Φ : List Constraint) :
    ∀ K ∈ regionPieces n Φ, piece K ⊆ (SP n Φ).filled := by
  intro K hK
  rcases mem_regionPieces.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, hKc⟩
  · exact hall_sub
  · exact ceil_sub hf
  · exact needle_sub hk
  · rw [slotPieces_eq] at hKc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hKc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < (fineP (cKind (gadAt Φ c))).length := by rw [tP_len]; exact hi
    rw [← coarse_piece_eq (n := n) (c := c) hi']
    exact fine_sub hc (List.getElem_mem hi')

end ArtGallery.Stade

end
