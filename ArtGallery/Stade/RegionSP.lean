module

public import ArtGallery.Stade.RegionTmpl
public import ArtGallery.Stade.GuardRegion

/-!
# The region of Stade's polygon: the pieces lie in the region (proof plan L2.3, L1.7)

The pieces of the region are the hall `hallPoly n Φ`, the ceiling features (as polygons of their
vertex lists), the floor needles of the variables, and the fine template pieces of the slots
(`slotFine n Φ c`, `RegionTmpl.lean`).  Here:

* `boundary_decomp`: the boundary of `SP n Φ` lies on the floor line, the ceiling line, the two
  walls, the floor feature chains and the ceiling feature chains;
* `hall_isPiece'`, `needle_isPiece`, `ceil_isPiece`, `fine_isPiece`: the pieces are convex pieces;
* `hall_disj`, `needle_disj`, `ceil_disj`, `fine_disj`: the interior of every piece misses the
  boundary (by the hull lemma and separating lines, by the template checks for the edges of the
  same slot, and by a connectedness argument for the ceiling features, which may overlap in
  abscissa);
* `hall_sub`, `needle_sub`, `ceil_sub`, `fine_sub`: hence every piece lies in the region
  (`piece_subset_filled`, a wall side of every piece is an edge of the polygon).
-/

@[expose] public section

namespace ArtGallery.Stade

open Set ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational

variable {n : ℕ} {Φ : List Constraint}

/-! ### Preliminaries -/

/-- The pieces `slotPieces` are the coarse template pieces. -/
theorem slotPieces_eq (k : TKind) (G H : ℝ) : slotPieces k G H = (coarseP k).map (rpoly G H) := by
  cases k <;>
  simp only [slotPieces, alPieces, agPieces, coarseP, fineP, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, rpoly, realize, needleL, needleR, tri, quad, pent,
    igCorridor, igPocket, igC1, igC2, igP, igQ, igI, igJ, irCorridor, irPocket, irNeedle, irP,
    irQ, irQ', irI, irJ, alRoom, alPocketX, alPocketY, alPocketZ, alAuxTri, alHungY, alHungX,
    alWL, alN1, alR, alBR, alWR, alXlo, alP, alXhi, alYlo, alN3, alYhi, alZlo, alN2, alQ, alZhi,
    alM1, alTip, alM2, agRoom, agBay, agPocketX, agPocketY, agPocketZ, agAuxTri, agHungZ, agHungY,
    agWL, agP, agN3, agBR, agWR, agXlo, agN1, agXhi, agYlo, agR, agYhi, agZlo, agQ, agN2, agZhi,
    agM1, agTip, agM2] <;>
  norm_num <;> (repeat' constructor) <;> ring

/-- The fine pieces of slot `c`. -/
noncomputable def slotFine (n : ℕ) (Φ : List Constraint) (c : ℕ) : List Polygon :=
  (fineP (cKind (gadAt Φ c))).map (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ))

/-- The template points of slot `c` in `poly n Φ`. -/
theorem slot_pt (c : ℕ) (p : RPt) :
    ratPoint (p.inst (paramH n Φ) (slotG n Φ c)) = realize (slotG n Φ c : ℝ) (paramH n Φ : ℝ) p := by
  rw [ratPoint_inst]; push_cast; rfl

theorem slot_map (c : ℕ) (ch : List RPt) :
    (ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))).map ratPoint =
      ch.map (realize (slotG n Φ c : ℝ) (paramH n Φ : ℝ)) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p _ => slot_pt c p)

/-- A chain lies in a set containing the segments of its consecutive points. -/
theorem chainSet_subset_idx {S : Set Point} : ∀ (M : List Point),
    (∀ j (hj : j + 1 < M.length), segment M[j] M[j + 1] ⊆ S) → chainSet M ⊆ S
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [chainSet_cons_cons]
    refine union_subset (h 0 (by simp)) (chainSet_subset_idx (b :: l) fun j hj => ?_)
    have := h (j + 1) (by simp at hj ⊢; omega)
    simpa using this

/-- The affine function of a horizontal / vertical half-plane on the interior of a piece. -/
theorem int_pos {K : Polygon} (hK : IsPiece K) (hn : 0 < K.n) {α β γ : ℝ}
    (hαβ : 0 < α ^ 2 + β ^ 2) (hv : ∀ k < K.n, 0 ≤ α * (K.vtx k).1 + β * (K.vtx k).2 + γ)
    {x : Point} (hx : x ∈ interior (piece K)) : 0 < α * x.1 + β * x.2 + γ :=
  pos_of_mem_interior_aff hαβ (fun _ hy => piece_aff_nonneg hK hn hv hy) hx

theorem piece_aff {K : Polygon} (hK : IsPiece K) (hn : 0 < K.n) {α β γ : ℝ}
    (hv : ∀ k < K.n, 0 ≤ α * (K.vtx k).1 + β * (K.vtx k).2 + γ) {x : Point}
    (hx : x ∈ piece K) : 0 ≤ α * x.1 + β * x.2 + γ :=
  piece_aff_nonneg hK hn hv hx

theorem xL_lt_xR_r (n : ℕ) (Φ : List Constraint) : (xL n Φ : ℝ) < (xR n Φ : ℝ) := by
  exact_mod_cast xL_lt_xR n Φ

/-! ### The boundary -/

/-- **The boundary of `SP n Φ`** lies on the floor and ceiling lines, the two walls and the
feature chains. -/
theorem boundary_decomp {p : Point} (hp : p ∈ (SP n Φ).boundary) :
    (p.2 = -1 ∧ (xL n Φ : ℝ) ≤ p.1 ∧ p.1 ≤ (xR n Φ : ℝ)) ∨
    (p.2 = 2 * (paramH n Φ : ℝ) ∧ (xL n Φ : ℝ) ≤ p.1 ∧ p.1 ≤ (xR n Φ : ℝ)) ∨
    (-1 ≤ p.2 ∧ p.2 ≤ 2 * (paramH n Φ : ℝ) ∧ (p.1 = (xL n Φ : ℝ) ∨ p.1 = (xR n Φ : ℝ))) ∨
    (∃ f ∈ floorFeats n Φ, p ∈ chainSet (f.map ratPoint)) ∨
    (∃ f ∈ ceilFeats n Φ, p ∈ chainSet (f.map ratPoint)) := by
  have hne : (poly n Φ).map ratPoint ≠ [] := by simp [poly]
  have hb := boundary_subset_chainSet hne hp
  set F := (floorFeats n Φ).map (List.map ratPoint) with hF
  set C := (ceilFeats n Φ).map (List.map ratPoint) with hC
  set xl : ℝ := (xL n Φ : ℝ)
  set xr : ℝ := (xR n Φ : ℝ)
  set ylo : ℝ := (((-1 : ℚ)) : ℝ)
  set yhi : ℝ := (((2 * (paramH n Φ : ℚ) : ℚ)) : ℝ)
  have hylo : ylo = -1 := by simp [ylo]
  have hyhi : yhi = 2 * (paramH n Φ : ℝ) := by simp [yhi]
  have hH := paramH_ge_r n Φ
  have hx : xl < xr := xL_lt_xR_r n Φ
  have hhead : ((poly n Φ).map ratPoint).headD 0 = (xl, ylo) := by rw [poly_map]; rfl
  rw [hhead, poly_map] at hb
  have e : [(xl, ylo)] ++ F.flatten ++ [(xr, ylo), (xr, yhi)] ++ C.flatten ++ [(xl, yhi)] ++
      [(xl, ylo)] = ((xl, ylo) :: F.flatten) ++
        (xr, ylo) :: (xr, yhi) :: (C.flatten ++ [(xl, yhi), (xl, ylo)]) := by simp
  have e2 : (xr, yhi) :: (C.flatten ++ [(xl, yhi), (xl, ylo)]) =
      ((xr, yhi) :: C.flatten) ++ (xl, yhi) :: [(xl, ylo)] := by simp
  rw [e, chainSet_append_cons, chainSet_cons_cons, e2,
    chainSet_append_cons ((xr, yhi) :: C.flatten) (xl, yhi) [(xl, ylo)]] at hb
  have hFF : ∀ f ∈ F, FloorFeature ylo xl xr f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact floor_feature g hg
  have hCC : ∀ f ∈ C, CeilFeature yhi xl xr f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact ceil_feature g hg
  have hfst : ∀ f ∈ F, xl < (fstPt f).1 := fun f hf =>
    ((hFF f hf).2.2.2.2.2.2 _ (fstPt_mem (hFF f hf).1)).1
  obtain ⟨-, hF2⟩ := comb_floor F xl hx hFF hfst (by rw [hF, List.pairwise_map]; exact floor_pw)
  obtain ⟨-, hC2⟩ := comb_ceiling hx C hCC (by rw [hC, List.pairwise_map]; exact ceil_pw)
  rcases hb with h | h | h | h
  · rcases hF2 (by simpa using h) with ⟨h1, h2, h3⟩ | ⟨f, hf, hpf⟩
    · left; exact ⟨by rw [h1, hylo], h2, h3⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g, hg, hpf⟩)))
  · right; right; left
    have h1 := vseg_fst h
    have h2 := vseg_snd (by rw [hylo, hyhi]; linarith) h
    rw [hylo, hyhi] at h2
    exact ⟨h2.1, h2.2, Or.inr h1⟩
  · rcases hC2 (by simpa using h) with ⟨h1, h2, h3⟩ | ⟨f, hf, hpf⟩
    · right; left; exact ⟨by rw [h1, hyhi], h2, h3⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, hpf⟩)))
  · right; right; left
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at h
    rw [Geometry.segment_comm] at h
    have h1 := vseg_fst h
    have h2 := vseg_snd (by rw [hylo, hyhi]; linarith) h
    rw [hylo, hyhi] at h2
    exact ⟨h2.1, h2.2, Or.inl h1⟩

/-! ### Convexity of the pieces -/

theorem needle_isPiece (a : ℝ) {H : ℝ} (hH : 0 < H) : IsPiece (needleL a (-1) H) :=
  isPiece_tri (by simp only [det]; nlinarith)

theorem wedge_isPiece {u v w : ℚ × ℚ} (h : 0 < qdet u v w) :
    IsPiece (Polygon.mk ([u, v, w].map ratPoint)) :=
  isPiece_tri (a := ratPoint u) (b := ratPoint v) (c := ratPoint w)
    (by rw [det_ratPoint]; exact_mod_cast h)

/-- The ceiling features are convex pieces. -/
theorem ceil_isPiece {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) :
    IsPiece (Polygon.mk (f.map ratPoint)) := by
  have hH := paramH_ge_q n Φ
  set H := (paramH n Φ : ℚ)
  have h3 := frac3_bounds hH
  have h4 := frac4_bounds hH
  have h5 := frac5_bounds hH
  have w1 : ∀ s pos, IsPiece (Polygon.mk ((wedgeW1 s pos H).map ratPoint)) := by
    intro s pos
    cases pos
    · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
    · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
  have w3 : ∀ s pos T, 2 * H < T → IsPiece (Polygon.mk ((wedgeW3 s pos T H).map ratPoint)) := by
    intro s pos T hT
    cases pos
    · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
    · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
  rcases mem_ceilFeats hf with ⟨i, -, hfi⟩ | ⟨k, -, hfk⟩ | ⟨k, hk, i, hi, -, rfl⟩
  · cases hpos : i.pos <;> rw [hpos] at hfi <;>
      simp only [inputCeil, ↓reduceIte, Bool.false_eq_true, List.mem_cons, List.not_mem_nil,
        or_false] at hfi <;> rcases hfi with rfl | rfl
    · exact w3 _ _ _ (by linarith)
    · exact w1 _ _
    · exact w1 _ _
    · exact w3 _ _ _ (by linarith)
  · simp only [varCeil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hfk
    rcases hfk with (rfl | rfl) | hfk
    · exact w1 _ _
    · exact w3 _ _ _ (by linarith)
    · split_ifs at hfk
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
        · exact wedge_isPiece (by unfold qdet; simp only; nlinarith)
      · simp at hfk
  · obtain ⟨d1, d2⟩ := input_delta hi hk
    have hp := CopyParams.of_rat (H := H) (a := (varA Φ k : ℚ)) (b := i.b) hH (by linarith)
      (by linarith)
    obtain ⟨c1, c2, c3, c4⟩ := copy_pocket_ccw i.ge hp
    rw [copyNook_map]
    exact isPiece_quad c3 c4 c1 c2

/-! ### The hall -/

theorem hall_vtx :
    (hallPoly n Φ).vtx 0 = ((xL n Φ : ℝ), -1) ∧ (hallPoly n Φ).vtx 1 = ((xR n Φ : ℝ), -1) ∧
      (hallPoly n Φ).vtx 2 = ((xR n Φ : ℝ), 2 * hH n Φ) ∧
      (hallPoly n Φ).vtx 3 = ((xL n Φ : ℝ), 2 * hH n Φ) := ⟨rfl, rfl, rfl, rfl⟩

theorem hall_n : (hallPoly n Φ).n = 4 := rfl

/-- The interior of the hall misses the boundary. -/
theorem hall_disj : Disjoint (interior (piece (hallPoly n Φ))) (SP n Φ).boundary := by
  rw [Set.disjoint_left]
  intro x hx hxb
  have hK := hallPoly_isPiece n Φ
  have hHr := paramH_ge_r n Φ
  have hxr := xL_lt_xR_r n Φ
  have hv : ∀ k < (hallPoly n Φ).n, (xL n Φ : ℝ) ≤ ((hallPoly n Φ).vtx k).1 ∧
      ((hallPoly n Φ).vtx k).1 ≤ (xR n Φ : ℝ) ∧ -1 ≤ ((hallPoly n Φ).vtx k).2 ∧
      ((hallPoly n Φ).vtx k).2 ≤ 2 * (paramH n Φ : ℝ) := by
    intro k hk
    rw [hall_n] at hk
    have hxq := xL_lt_xR n Φ
    have hHq := paramH_ge_q n Φ
    interval_cases k <;> simp [hallPoly, quad, Polygon.vtx] <;> constructor <;>
      first | linarith | (show _ ≤ (paramH n Φ : ℝ) * 2 ∨ _; left; linarith) | skip
  have hn : 0 < (hallPoly n Φ).n := by rw [hall_n]; norm_num
  have i1 := int_pos hK hn (α := 1) (β := 0) (γ := -(xL n Φ : ℝ)) (by norm_num)
    (fun k hk => by have := hv k hk; linarith) hx
  have i2 := int_pos hK hn (α := -1) (β := 0) (γ := (xR n Φ : ℝ)) (by norm_num)
    (fun k hk => by have := hv k hk; linarith) hx
  have i3 := int_pos hK hn (α := 0) (β := 1) (γ := 1) (by norm_num)
    (fun k hk => by have := hv k hk; linarith) hx
  have i4 := int_pos hK hn (α := 0) (β := -1) (γ := 2 * (paramH n Φ : ℝ)) (by norm_num)
    (fun k hk => by have := hv k hk; linarith) hx
  rcases boundary_decomp hxb with h | h | h | ⟨f, hf, hxf⟩ | ⟨f, hf, hxf⟩
  · linarith [h.1]
  · linarith [h.1]
  · rcases h.2.2 with h' | h' <;> linarith
  · have := (floor_feature f hf).below hxf
    norm_num at this; linarith
  · have := (ceil_feature f hf).above hxf
    push_cast at this; linarith

/-! ### Floor needles of the variables -/

theorem needle_real {k : ℕ} :
    (needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k))).map ratPoint =
      [((varA Φ k : ℝ) - 1 / 4, -1), ((varA Φ k : ℝ), -1 - (paramH n Φ : ℝ)),
        ((varA Φ k : ℝ), -1)] := by
  rw [needleDownL_inst]
  simp [ratPoint]

/-- The interior of the floor needle of variable `k` misses the boundary. -/
theorem needle_disj {k : ℕ} (hk : k < n) :
    Disjoint (interior (piece (needleL (varA Φ k : ℝ) (-1) (hH n Φ)))) (SP n Φ).boundary := by
  rw [Set.disjoint_left]
  intro x hx hxb
  have hHr := paramH_ge_r n Φ
  have hK := needle_isPiece (varA Φ k : ℝ) (by show (0:ℝ) < (paramH n Φ : ℝ); linarith [hHr])
  have hn : 0 < (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).n := by simp [needleL, tri, Polygon.n]
  have hv : ∀ j < (needleL (varA Φ k : ℝ) (-1) (hH n Φ)).n,
      (varA Φ k : ℝ) - 1 / 4 ≤ ((needleL (varA Φ k : ℝ) (-1) (hH n Φ)).vtx j).1 ∧
      ((needleL (varA Φ k : ℝ) (-1) (hH n Φ)).vtx j).1 ≤ (varA Φ k : ℝ) ∧
      ((needleL (varA Φ k : ℝ) (-1) (hH n Φ)).vtx j).2 ≤ -1 := by
    intro j hj
    simp only [needleL, tri, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [needleL, tri, Polygon.vtx] <;> unfold hH <;> norm_num <;> linarith
  have i1 := int_pos hK hn (α := 0) (β := -1) (γ := -1) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  have i2 := int_pos hK hn (α := 1) (β := 0) (γ := -((varA Φ k : ℝ) - 1 / 4)) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  have i3 := int_pos hK hn (α := -1) (β := 0) (γ := (varA Φ k : ℝ)) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  rcases boundary_decomp hxb with h | h | h | ⟨f, hf, hxf⟩ | ⟨f, hf, hxf⟩
  · linarith [h.1]
  · linarith [h.1]
  · linarith [h.1]
  · rcases mem_floorFeats hf with ⟨k', hk', rfl⟩ | ⟨c, hc, ch, hch, rfl⟩
    · rcases lt_trichotomy k' k with hlt | rfl | hgt
      · have := s2_var (Φ := Φ) hlt
        have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
        have := chainSet_fst_le (fun p hp => (needle_bounds (Φ := Φ) (n := n) p hp).2) x hxf
        have : ((varA Φ k' : ℚ) : ℝ) + 50 ≤ ((varA Φ k : ℚ) : ℝ) := by
          exact_mod_cast (by linarith : (varA Φ k' : ℚ) + 50 ≤ varA Φ k)
        push_cast at *; linarith
      · rw [needle_real] at hxf
        simp only [chainSet_cons_cons, chainSet_single, union_empty] at hxf
        rcases hxf with h | h
        · exact Set.disjoint_left.1 (disjoint_interior_of_wall hK (j := 0) (by simp [needleL,
            tri, Polygon.n])) hx (by simpa [needleL, tri, Polygon.vtx, Polygon.n, hH] using h)
        · exact Set.disjoint_left.1 (disjoint_interior_of_wall hK (j := 1) (by simp [needleL,
            tri, Polygon.n])) hx (by simpa [needleL, tri, Polygon.vtx, Polygon.n, hH] using h)
      · have := s2_var (Φ := Φ) hgt
        have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
        have := chainSet_fst_ge (fun p hp => (needle_bounds (Φ := Φ) (n := n) p hp).1) x hxf
        have : ((varA Φ k : ℚ) : ℝ) + 50 ≤ ((varA Φ k' : ℚ) : ℝ) := by
          exact_mod_cast (by linarith : (varA Φ k : ℚ) + 50 ≤ varA Φ k')
        push_cast at *; linarith
    · have := chainSet_fst_ge (fun p hp => (slot_bounds (n := n) hch p hp).1) x hxf
      have h2 := s2_var_slot (Φ := Φ) (c := c) hk
      have : ((varA Φ k : ℚ) : ℝ) + 1000 ≤ ((slotG n Φ c : ℚ) : ℝ) := by
        exact_mod_cast (by linarith [paramH_ge_q n Φ] : (varA Φ k : ℚ) + 1000 ≤ slotG n Φ c)
      push_cast at *; linarith
  · have := (ceil_feature f hf).above hxf
    push_cast at this; linarith

/-! ### The fine template pieces -/

theorem fine_isPiece {c : ℕ} {l : List RPt} (hl : l ∈ fineP (cKind (gadAt Φ c))) :
    IsPiece (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l) ∧
      3 ≤ (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).n :=
  pieceB_sound (paramH_ge_r n Φ) (tP_piece hl)

theorem cur_mem {l : List RPt} {j : ℕ} (hj : j < l.length) : cur l j ∈ l := by
  unfold cur
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

/-- Vertices of the fine pieces: in the slot, below the floor, on the boundary. -/
theorem fine_vtx {c : ℕ} (hc : c < paramC Φ) {l : List RPt}
    (hl : l ∈ fineP (cKind (gadAt Φ c))) {j : ℕ} (hj : j < l.length) :
    (slotG n Φ c : ℝ) + 30 ≤ ((rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx j).1 ∧
      ((rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx j).1 ≤ (slotG n Φ c : ℝ) + 600 ∧
      ((rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx j).2 ≤ -1 ∧
      (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).vtx j ∈ (SP n Φ).boundary := by
  rw [rpoly_vtx _ _ l hj]
  obtain ⟨ch, hch, hv⟩ := tP_vtx hl (cur_mem hj)
  have hx := tmplFloor_x hch _ hv
  obtain ⟨y1, y2, d1, d2⟩ := tmplFloor_y hch hv
  have hH := paramH_ge_r n Φ
  have hx1 : (30 : ℝ) ≤ (cur l j).1 := by exact_mod_cast hx.1
  have hx2 : ((cur l j).1 : ℝ) ≤ 600 := by exact_mod_cast hx.2
  have hy2 : ((cur l j).2.1 : ℝ) ≤ -1 := by exact_mod_cast y2
  have hd1 : (0 : ℝ) ≤ (cur l j).2.2 := by exact_mod_cast d1
  refine ⟨by simp only [realize]; linarith, by simp only [realize]; linarith,
    by simp only [realize]; nlinarith, ?_⟩
  rw [← slot_pt]
  exact mem_boundary_of_infix (floor_infix (slotFloor_mem hc hch)) (List.mem_map_of_mem hv)

/-- The interior of a fine piece misses the boundary. -/
theorem fine_disj {c : ℕ} (hc : c < paramC Φ) {l : List RPt}
    (hl : l ∈ fineP (cKind (gadAt Φ c))) :
    Disjoint (interior (piece (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l))) (SP n Φ).boundary := by
  rw [Set.disjoint_left]
  intro x hx hxb
  obtain ⟨hK, hn3⟩ := fine_isPiece (n := n) hl
  have hn : 0 < (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).n := by omega
  have hv := fun j (hj : j < (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l).n) =>
    fine_vtx (n := n) hc hl (j := j) (by rw [rpoly_n] at hj; exact hj)
  have hH := paramH_ge_r n Φ
  have i1 := int_pos hK hn (α := 0) (β := -1) (γ := -1) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  have i2 := int_pos hK hn (α := 1) (β := 0) (γ := -((slotG n Φ c : ℝ) + 30)) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  have i3 := int_pos hK hn (α := -1) (β := 0) (γ := (slotG n Φ c : ℝ) + 600) (by norm_num)
    (fun j hj => by have := hv j hj; linarith) hx
  rcases boundary_decomp hxb with h | h | h | ⟨f, hf, hxf⟩ | ⟨f, hf, hxf⟩
  · linarith [h.1]
  · linarith [h.1]
  · linarith [h.1]
  · rcases mem_floorFeats hf with ⟨k', hk', rfl⟩ | ⟨c', hc', ch, hch, rfl⟩
    · have := chainSet_fst_le (fun p hp => (needle_bounds (Φ := Φ) (n := n) p hp).2) x hxf
      have h2 := s2_var_slot (Φ := Φ) (c := c) hk'
      have : ((varA Φ k' : ℚ) : ℝ) + 1000 ≤ ((slotG n Φ c : ℚ) : ℝ) := by
        exact_mod_cast (by linarith [paramH_ge_q n Φ] : (varA Φ k' : ℚ) + 1000 ≤ slotG n Φ c)
      push_cast at *; linarith
    · rcases lt_trichotomy c' c with hlt | rfl | hgt
      · have := chainSet_fst_le (fun p hp => (slot_bounds (n := n) hch p hp).2.1) x hxf
        have h2 := slot_lt_real (n := n) (Φ := Φ) hlt
        push_cast at *; linarith
      · rw [slot_map] at hxf
        refine Set.disjoint_left.1 ?_ hx (chainSet_subset_idx (S := ⋃ e ∈ pairs ch,
          segment (realize (slotG n Φ c' : ℝ) (paramH n Φ : ℝ) e.1)
            (realize (slotG n Φ c' : ℝ) (paramH n Φ : ℝ) e.2)) _ (fun j hj => ?_) hxf)
        · rw [Set.disjoint_iUnion₂_right]
          intro e he
          exact sepB_sound (paramH_ge_r n Φ) (tP_piece hl) (tP_sep hl hch he)
        · simp only [List.length_map] at hj
          intro y hy
          refine Set.mem_iUnion₂.2 ⟨(ch[j], ch[j + 1]), mem_pairs_of_lt ch j hj, ?_⟩
          simpa using hy
      · have := chainSet_fst_ge (fun p hp => (slot_bounds (n := n) hch p hp).1) x hxf
        have h2 := slot_lt_real (n := n) (Φ := Φ) hgt
        push_cast at *; linarith
  · have := (ceil_feature f hf).above hxf
    push_cast at this; linarith

/-! ### The ceiling features -/

theorem isPreconnected_chainSet : ∀ l : List Point, IsPreconnected (chainSet l)
  | [] => by simp [isPreconnected_empty]
  | [_] => by simp [isPreconnected_empty]
  | [a, b] => by
    simp only [chainSet_cons_cons, chainSet_single, union_empty]
    rw [Geometry.segment_eq]; exact (convex_segment a b).isPreconnected
  | a :: b :: c :: l => by
    rw [chainSet_cons_cons]
    refine IsPreconnected.union b (Geometry.right_mem_segment a b) ?_ ?_
      (isPreconnected_chainSet (b :: c :: l))
    · rw [chainSet_cons_cons]; exact Or.inl (Geometry.left_mem_segment b c)
    · rw [Geometry.segment_eq]; exact (convex_segment a b).isPreconnected

/-- **Connectedness argument.** A preconnected set that meets no side of a piece and has a point
outside its interior misses its interior. -/
theorem disj_of_preconnected {K : Polygon} (hK : IsPiece K) {S : Set Point}
    (hS : IsPreconnected S) (hfr : ∀ k < K.n, Disjoint (K.edge k) S)
    (hout : ∃ p ∈ S, p ∉ interior (piece K)) : Disjoint (interior (piece K)) S := by
  rw [Set.disjoint_left]
  intro x hx hxS
  have hsub : S ⊆ interior (piece K) ∪ (piece K)ᶜ := by
    intro s hs
    by_cases h1 : s ∈ interior (piece K)
    · exact Or.inl h1
    by_cases h2 : s ∈ piece K
    · exfalso
      obtain ⟨k, hk, hsk⟩ := mem_edge_of_mem_frontier hK ⟨subset_closure h2, h1⟩
      exact Set.disjoint_left.1 (hfr k hk) hsk hs
    · exact Or.inr h2
  rcases hS.subset_or_subset isOpen_interior (isClosed_piece K).isOpen_compl
    (Set.disjoint_left.2 fun y hy hy' => hy' (interior_subset hy)) hsub with h | h
  · obtain ⟨p, hp, hpo⟩ := hout
    exact hpo (h hp)
  · exact h hxS (interior_subset hx)

theorem fstPt_eq {M : List Point} (hM : 0 < M.length) : fstPt M = M[0] := by
  cases M with
  | nil => simp at hM
  | cons a l => rfl

theorem lstPt_eq {M : List Point} (hM : 0 < M.length) : lstPt M = M[M.length - 1] := by
  unfold lstPt
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

/-- Vertices of the polygon of a list. -/
theorem mk_vtx (M : List Point) {j : ℕ} (hj : j < M.length) : (Polygon.mk M).vtx j = M[j] := by
  unfold Polygon.vtx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The interior of a ceiling feature misses the boundary. -/
theorem ceil_disj {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) :
    Disjoint (interior (piece (Polygon.mk (f.map ratPoint)))) (SP n Φ).boundary := by
  rw [Set.disjoint_left]
  intro x hx hxb
  have hK := ceil_isPiece hf
  have hH := paramH_ge_r n Φ
  have hv : ∀ j < (Polygon.mk (f.map ratPoint)).n,
      2 * (paramH n Φ : ℝ) ≤ ((Polygon.mk (f.map ratPoint)).vtx j).2 := by
    intro j hj
    rw [n_map_ratPoint] at hj
    rw [vtx_map_ratPoint, ratPoint_snd]
    have hm : f.getD j 0 ∈ f := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    have := (ceil_snd hf hm).1
    exact_mod_cast this
  obtain ⟨hflen, -, hffy, hfly, hffl, -, -⟩ := ceil_feature f hf
  obtain ⟨M, hM⟩ : ∃ M, M = f.map ratPoint := ⟨_, rfl⟩
  rw [← hM] at hx hK hv hflen hffy hfly hffl
  have hn : (Polygon.mk M).n = M.length := rfl
  have hn0 : 0 < (Polygon.mk M).n := by rw [hn]; omega
  have i1 := int_pos hK hn0 (α := 0) (β := 1) (γ := -(2 * (paramH n Φ : ℝ)))
    (by norm_num) (fun j hj => by have := hv j hj; linarith) hx
  have hwall : ∀ j (hj : j + 1 < M.length), Disjoint (interior (piece (Polygon.mk M)))
      (segment M[j] M[j + 1]) := by
    intro j hj
    have := disjoint_interior_of_wall hK (j := j) (by rw [hn]; omega)
    rwa [hn, Nat.mod_eq_of_lt hj, mk_vtx M (by omega), mk_vtx M hj] at this
  rcases boundary_decomp hxb with h | h | h | ⟨g, hg, hxg⟩ | ⟨g, hg, hxg⟩
  · linarith [h.1]
  · linarith [h.1]
  · linarith [h.2.1]
  · have := (floor_feature g hg).below hxg
    norm_num at this; linarith
  · by_cases hfg : g = f
    · rw [hfg, ← hM] at hxg
      exact (chainSet_subset_idx (S := (interior (piece (Polygon.mk M)))ᶜ) M
        (fun j hj y hy hyi => Set.disjoint_left.1 (hwall j hj) hyi hy) hxg) hx
    · -- another ceiling feature: the connectedness argument
      have hpw : (ceilFeats n Φ).Pairwise (fun f g => CeilRel f g ∨ CeilRel g f) :=
        ceil_pw.imp Or.inl
      have : Std.Symm (fun f g : List (ℚ × ℚ) => CeilRel f g ∨ CeilRel g f) :=
        ⟨fun _ _ h => h.symm⟩
      have hrel := hpw.forall hf hg (Ne.symm hfg)
      simp only [CeilRel] at hrel
      rw [← hM] at hrel
      obtain ⟨hglen, -, hgfy, hgly, hgfl, hgab, -⟩ := ceil_feature g hg
      have hM0 : 0 < M.length := by omega
      refine Set.disjoint_left.1 (disj_of_preconnected hK (isPreconnected_chainSet _)
        (fun k hk => ?_) ⟨fstPt (g.map ratPoint), fstPt_mem hglen, fun h => ?_⟩) hx hxg
      · rw [hn] at hk
        rcases Nat.lt_or_ge (k + 1) M.length with hk1 | hk1
        · have hseg : (Polygon.mk M).edge k ⊆ chainSet M := by
            unfold Polygon.edge
            rw [hn, Nat.mod_eq_of_lt hk1, mk_vtx M hk, mk_vtx M hk1]
            exact segment_subset_chainSet M k hk1
          refine Set.disjoint_of_subset_left hseg ?_
          rcases hrel with h | h
          · exact h.1
          · exact h.1.symm
        · obtain rfl : k = M.length - 1 := by omega
          have hseg : (Polygon.mk M).edge (M.length - 1) = segment (lstPt M) (fstPt M) := by
            unfold Polygon.edge
            rw [hn, show M.length - 1 + 1 = M.length by omega, Nat.mod_self, mk_vtx M hk,
              mk_vtx M hM0, lstPt_eq hM0, fstPt_eq hM0]
          rw [hseg, Set.disjoint_left]
          intro z hz hzN
          have hz2 : z.2 = 2 * (paramH n Φ : ℝ) := by
            obtain ⟨t, -, -, rfl⟩ := hz
            simp only [hfly, hffy]; push_cast; ring
          have hz1 : (lstPt M).1 ≤ z.1 ∧ z.1 ≤ (fstPt M).1 := by
            obtain ⟨t, h0, h1, rfl⟩ := hz
            simp only; constructor <;> nlinarith
          rcases hgab z hzN with h | h | h
          · push_cast at h; linarith
          · rcases hrel with hr | hr
            · have := hr.2; rw [← h] at this; linarith [hz1.1]
            · have := hr.2; rw [h] at hz1; linarith [hz1.2, hgfl]
          · rcases hrel with hr | hr
            · have := hr.2; rw [h] at hz1; linarith [hz1.1, hgfl]
            · have := hr.2; rw [← h] at this; linarith [hz1.2]
      · have := int_pos hK hn0 (α := 0) (β := 1) (γ := -(2 * (paramH n Φ : ℝ)))
          (by norm_num) (fun j hj => by have := hv j hj; linarith) h
        rw [hgfy] at this; push_cast at this; linarith

/-! ### Walls and inclusion in the region -/

/-- A piece with a wall whose interior misses the boundary lies in the region. -/
theorem sub_of_disj {K : Polygon} (hK : IsPiece K)
    (hd : Disjoint (interior (piece K)) (SP n Φ).boundary) {j : ℕ} (hj : j < K.n)
    (hw : IsWall (SP n Φ) K j) : piece K ⊆ (SP n Φ).filled :=
  piece_subset_filled (simple n Φ) (interiorLeft n Φ) hK
    (fun i hi => Set.disjoint_of_subset_right
      (fun y (hy : y ∈ (SP n Φ).edge i) => (⟨i, hi, hy⟩ : y ∈ (SP n Φ).boundary)) hd) hj hw

theorem hall_wall : IsWall (SP n Φ) (hallPoly n Φ) 1 := by
  have h : [(xR n Φ, (-1 : ℚ)), (xR n Φ, 2 * (paramH n Φ : ℚ))] <:+: poly n Φ := by
    unfold poly
    exact ⟨[(xL n Φ, -1)] ++ (floorFeats n Φ).flatten, (ceilFeats n Φ).flatten ++
      [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩
  obtain ⟨i, hi, h1, h2⟩ := edge_of_infix h
  refine ⟨i, hi, ?_, ?_⟩
  · rw [h1]; simp [ratPoint, hallPoly, quad, Polygon.vtx]
  · rw [h2]; simp [ratPoint, hallPoly, quad, Polygon.vtx, Polygon.n]

/-- **The hall lies in the region.** -/
theorem hall_sub : piece (hallPoly n Φ) ⊆ (SP n Φ).filled :=
  sub_of_disj (hallPoly_isPiece n Φ) hall_disj (by rw [hall_n]; norm_num) hall_wall

/-- **The floor needles of the variables lie in the region.** -/
theorem needle_sub {k : ℕ} (hk : k < n) :
    piece (needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ⊆ (SP n Φ).filled := by
  have hHr := paramH_ge_r n Φ
  refine sub_of_disj (needle_isPiece _ (by show (0 : ℝ) < (paramH n Φ : ℝ); linarith))
    (needle_disj hk) (j := 0) (by simp [needleL, tri, Polygon.n]) ?_
  have h := varW2_infix (Φ := Φ) hk
  have h' : [((varA Φ k : ℚ) - 1 / 4, (-1 : ℚ)), ((varA Φ k : ℚ), -1 - (paramH n Φ : ℚ))] <:+:
      poly n Φ := (List.infix_append [] _ [((varA Φ k : ℚ), -1)]).trans h
  obtain ⟨i, hi, h1, h2⟩ := edge_of_infix h'
  refine ⟨i, hi, ?_, ?_⟩
  · rw [h1]; simp [ratPoint, needleL, tri, Polygon.vtx]
  · rw [h2]; simp [ratPoint, needleL, tri, Polygon.vtx, Polygon.n, hH]

/-- **The ceiling features lie in the region.** -/
theorem ceil_sub {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ) :
    piece (Polygon.mk (f.map ratPoint)) ⊆ (SP n Φ).filled := by
  have hlen := ceil_len hf
  refine sub_of_disj (ceil_isPiece hf) (ceil_disj hf) (j := 0)
    (by rw [n_map_ratPoint]; omega) ?_
  have h01 : [f[0], f[1]] <:+: f := by
    obtain ⟨a, b, l, rfl⟩ : ∃ a b l, f = a :: b :: l := by
      match f, hlen with
      | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
    exact ⟨[], l, rfl⟩
  obtain ⟨i, hi, h1, h2⟩ := edge_of_infix (h01.trans (ceil_infix hf))
  refine ⟨i, hi, ?_, ?_⟩
  · rw [h1, vtx_map_ratPoint, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [h2, n_map_ratPoint, Nat.mod_eq_of_lt (by omega), vtx_map_ratPoint,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

/-- **The fine pieces of the slots lie in the region.** -/
theorem fine_sub {c : ℕ} (hc : c < paramC Φ) {l : List RPt}
    (hl : l ∈ fineP (cKind (gadAt Φ c))) :
    piece (rpoly (slotG n Φ c : ℝ) (paramH n Φ : ℝ) l) ⊆ (SP n Φ).filled := by
  obtain ⟨j, hj, hw⟩ := tP_wall hl
  obtain ⟨ch, hch, hab⟩ := wallB_spec hw
  refine sub_of_disj (fine_isPiece hl).1 (fine_disj hc hl) (j := j) (by rw [rpoly_n]; exact hj) ?_
  obtain ⟨i, hi, h1, h2⟩ :=
    edge_of_infix ((hab.map (RPt.inst (paramH n Φ) (slotG n Φ c))).trans
      (floor_infix (slotFloor_mem hc hch)))
  refine ⟨i, hi, ?_, ?_⟩
  · rw [h1, slot_pt, rpoly_vtx _ _ l hj]
  · rw [h2, slot_pt, rpoly_vtx_succ _ _ l hj]

end ArtGallery.Stade

end
