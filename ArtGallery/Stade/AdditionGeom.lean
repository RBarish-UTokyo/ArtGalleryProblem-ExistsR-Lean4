module

public import ArtGallery.Stade.AdditionAlg
public import ArtGallery.Stade.Exit
public import ArtGallery.Stade.Templates

/-!
# Stade construction, §7: geometry of the addition gadgets (generic part and `addLe`)

Visibility facts for the addition gadgets of `docs/stade/construction.md` §7 (notation of
`ArtGallery/Stade/AdditionAlg.lean`, slot origin `G`); `addGe` is in
`ArtGallery/Stade/AdditionGeomGe.lean`.  The statements are relative to an arbitrary simple
polygon `P` with its interior on the left whose edges include the walls of the gadget
(`PEdge`, collected in `AlWalls`, `AlAuxWalls`).

Generic tools:
* `add_nook_bounds`: a guard right of both mouth corners of a pocket with vertical nook line
  sees only nook points between its two shadows (from `pocket_projection`);
* `add_nook_viewer`: every viewer of a nook point is in the pocket or in its partial-visibility
  region `pocketPV` (from `pocket_pv`);
* `add_sees_wedge_room` (**aux region**, L4.1'): a point seeing the tip of a wedge hanging from
  a side of a convex room, whose cone meets the door of the room only in that side, lies in the
  wedge triangle or in `cone ∩ room`;
* `add_exists_cross_hline`, `add_mem_segment_of_le`, `add_sees_chain3`, `add_sees_chain4`:
  crossing points and sight lines through chains of convex parts of the region.

`addLe` (`v_x + v_y ≤ v_z`):
* `al_rel_of_cover` (L7.3, L7.4): if the aux guard `a` (any point right of `x = G + 50`) and
  the inputs cover the three nook segments, then `v_x + v_y ≤ v_z`;
* `al_sees_auxTip`: the viewers of the aux tip lie in `piece (alAuxTri G) ∪ alAuxRegion G`
  (`alAuxRegion G = cone ∩ room`), which lies in `G + 91 ≤ x ≤ G + 129`, `y ≤ −1`
  (`al_aux_bounds`); the canonical aux point lies in `alAuxRegion G` (`alI_mem_auxRegion`);
* `al_viewer_x`, `al_viewer_y`, `al_viewer_z` (L7.6, PV exclusion): a viewer of a nook point
  outside the pocket satisfies `x ≥ G + 50`, and in the input band `0 ≤ y ≤ 6` it lies in
  `[G + 353, G + 513]`, `[G + 202, G + 318]`, `[G + 384, G + 555]` respectively; the foreign
  inputs of the slot (at `G + 210, G + 370, G + 530`) are excluded with margins `17, 52, 14`;
* `al_cover_of_rel` (L7.8 for the nooks) and `al_cover_iff`: with the aux guard at the canonical
  point `alI G v_x v_y`, the three nooks are covered iff `v_x + v_y ≤ v_z`.
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon}

/-- `a → b` is an edge of `P` (traversed in this direction). -/
def PEdge (P : Polygon) (a b : Point) : Prop :=
  ∃ i < P.n, P.vtx i = a ∧ P.vtx ((i + 1) % P.n) = b

/-! ## Generic tools -/

/-- A sub-segment of a sight line is a sight line. -/
theorem add_sees_of_mem {s p q : Point} (hq : q ∈ segment s p) (h : P.Sees s p) :
    P.Sees q p :=
  (segment_subset_of_convex (segment_convex s p) hq (right_mem_segment s p)).trans h

/-- **Order along a segment.** If `f` is affine along `[g, s]` and decreases from `g` to `s`,
a point `q₂` of the segment with `f q₂ ≤ f q₁` lies on `[q₁, s]`. -/
theorem add_mem_segment_of_le {g s q₁ q₂ : Point} (f : Point → ℝ)
    (hf : ∀ t : ℝ, f (lerp g s t) = (1 - t) * f g + t * f s) (hq₁ : q₁ ∈ segment g s)
    (hq₂ : q₂ ∈ segment g s) (hgs : f s < f g) (h : f q₂ ≤ f q₁) : q₂ ∈ segment q₁ s := by
  obtain ⟨t₁, ht₁0, ht₁1, rfl⟩ := mem_segment_iff_lerp.1 hq₁
  obtain ⟨t₂, ht₂0, ht₂1, rfl⟩ := mem_segment_iff_lerp.1 hq₂
  rw [hf, hf] at h
  have ht : t₁ ≤ t₂ := by nlinarith
  rcases eq_or_lt_of_le ht₁1 with h1 | h1
  · have : t₂ = 1 := by linarith
    subst h1; subst this
    simp only [lerp_one]
    exact left_mem_segment s s
  · refine mem_segment_iff_lerp.2 ⟨(t₂ - t₁) / (1 - t₁), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    rw [lerp_lerp_right]
    congr 1
    field_simp
    ring

/-- Order along a segment going down. -/
theorem add_mem_segment_of_snd_le {g s q₁ q₂ : Point} (hq₁ : q₁ ∈ segment g s)
    (hq₂ : q₂ ∈ segment g s) (hgs : s.2 < g.2) (h : q₂.2 ≤ q₁.2) : q₂ ∈ segment q₁ s :=
  add_mem_segment_of_le (fun p => p.2) (fun t => by simp only [lerp_snd]; ring) hq₁ hq₂ hgs h

/-- Order along a segment going left. -/
theorem add_mem_segment_of_fst_le {g s q₁ q₂ : Point} (hq₁ : q₁ ∈ segment g s)
    (hq₂ : q₂ ∈ segment g s) (hgs : s.1 < g.1) (h : q₂.1 ≤ q₁.1) : q₂ ∈ segment q₁ s :=
  add_mem_segment_of_le (fun p => p.1) (fun t => by simp only [lerp_fst]; ring) hq₁ hq₂ hgs h

/-- **Crossing a horizontal line.**  A segment from `g` (at or above `y = y₀`) to `s` (strictly
below) meets `[(x₁, y₀), (x₂, y₀)]` if its crossing abscissa `g.1 + t (s.1 − g.1)`,
`t = (g.2 − y₀)/(g.2 − s.2)`, lies in `[x₁, x₂]` (stated after multiplication by
`g.2 − s.2 > 0`). -/
theorem add_exists_cross_hline {g s : Point} {y₀ x₁ x₂ : ℝ} (hg : y₀ ≤ g.2) (hs : s.2 < y₀)
    (hx : x₁ ≤ x₂) (h1 : (x₁ - g.1) * (g.2 - s.2) ≤ (g.2 - y₀) * (s.1 - g.1))
    (h2 : (g.2 - y₀) * (s.1 - g.1) ≤ (x₂ - g.1) * (g.2 - s.2)) :
    ∃ q ∈ segment (x₁, y₀) (x₂, y₀), q ∈ segment g s := by
  have hd : 0 < g.2 - s.2 := by linarith
  set t := (g.2 - y₀) / (g.2 - s.2) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨lerp g s t, ?_, lerp_mem_segment _ _ ht0 ht1⟩
  rw [mem_segment_horiz_iff hx]
  simp only [lerp_fst, lerp_snd]
  have key : t * (s.1 - g.1) = (g.2 - y₀) * (s.1 - g.1) / (g.2 - s.2) := by rw [ht]; ring
  have e : t * (s.2 - g.2) = -(g.2 - y₀) := by rw [ht]; field_simp; ring
  refine ⟨by linarith, ?_, ?_⟩
  · have : x₁ - g.1 ≤ t * (s.1 - g.1) := by rw [key, le_div_iff₀ hd]; linarith
    linarith
  · have : t * (s.1 - g.1) ≤ x₂ - g.1 := by rw [key, div_le_iff₀ hd]; linarith
    linarith

/-- **Sight lines through three convex parts** `A ∋ g`, `B`, `C ∋ s` of the region, the segment
`[g, s]` passing through `q₁ ∈ A ∩ B` and then `q₂ ∈ B ∩ C`. -/
theorem add_sees_chain3 {A B C : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    {g s q₁ q₂ : Point} (hg : g ∈ A) (hq₁A : q₁ ∈ A) (hq₁B : q₁ ∈ B) (hq₂B : q₂ ∈ B)
    (hq₂C : q₂ ∈ C) (hs : s ∈ C) (hq₁ : q₁ ∈ segment g s) (hq₂ : q₂ ∈ segment q₁ s) :
    P.Sees g s :=
  sees_of_mem_segment hq₁ (sees_of_convex hA hAP hg hq₁A)
    (sees_of_two_convex hB hC hBP hCP hq₁B hs hq₂B hq₂C hq₂)

/-- **Sight lines through four convex parts** `A ∋ g`, `B`, `C`, `D ∋ s`, crossing
`q₁ ∈ A ∩ B`, `q₂ ∈ B ∩ C`, `q₃ ∈ C ∩ D` in this order. -/
theorem add_sees_chain4 {A B C D : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hD : Convex ℝ D) (hDP : D ⊆ P.filled) {g s q₁ q₂ q₃ : Point} (hg : g ∈ A) (hq₁A : q₁ ∈ A)
    (hq₁B : q₁ ∈ B) (hq₂B : q₂ ∈ B) (hq₂C : q₂ ∈ C) (hq₃C : q₃ ∈ C) (hq₃D : q₃ ∈ D) (hs : s ∈ D)
    (hq₁ : q₁ ∈ segment g s) (hq₂ : q₂ ∈ segment q₁ s) (hq₃ : q₃ ∈ segment q₂ s) :
    P.Sees g s :=
  sees_of_mem_segment hq₁ (sees_of_convex hA hAP hg hq₁A)
    (add_sees_chain3 hB hBP hC hCP hD hDP hq₁B hq₂B hq₂C hq₃C hq₃D hs hq₂ hq₃)

section Pocket

variable {lo dn up hi : Point}

/-- **What a guard sees of a nook (L7.3).** Let `lo, dn, up, hi` be a strictly convex
counter-clockwise pocket whose walls `lo → dn`, `up → hi`, `hi → lo` are edges of `P`, with the
nook segment `[lo, hi]` on a vertical line `x = c`.  A guard `g` outside the pocket and strictly
right of both mouth corners sees only nook points `(c, h)` between its shadows:
`π_dn(g) ≤ h ≤ π_up(g)`. -/
theorem add_nook_bounds (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : PEdge P lo dn) (hw2 : PEdge P up hi) (hw3 : PEdge P hi lo) {g : Point}
    (hg : g ∉ piece (quad lo dn up hi)) (hdn : dn.1 < g.1) (hup : up.1 < g.1) {c h : ℝ}
    (hs : (c, h) ∈ segment lo hi) (hsees : P.Sees g (c, h)) :
    vproj g dn c ≤ h ∧ h ≤ vproj g up c := by
  have hs' : (c, h) ∈ segment hi lo := by rw [segment_comm]; exact hs
  have := pocket_projection hP hL h1 h2 h3 h4 hw0 hw2 hw3 hs' hg (Polygon.sees_comm.1 hsees)
  exact ⟨vproj_le_of_det_nonpos hdn this.1, le_vproj_of_det_nonneg hup this.2⟩

/-- The partial-visibility region of the pocket `lo, dn, up, hi`: beyond the mouth line and
between the two diagonals (proof plan L1.4). -/
def pocketPV (lo dn up hi : Point) : Set Point :=
  {p | det dn up p ≤ 0 ∧ 0 ≤ det hi dn p ∧ det lo up p ≤ 0}

/-- **Viewers of a nook (L1.4).**  Under the hypotheses of `add_nook_bounds`, every point seeing
a point of the nook segment lies in the pocket or in its partial-visibility region. -/
theorem add_nook_viewer (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hw0 : PEdge P lo dn) (hw2 : PEdge P up hi) (hw3 : PEdge P hi lo) {s p : Point}
    (hs : s ∈ segment lo hi) (hsees : P.Sees p s) :
    p ∈ piece (quad lo dn up hi) ∨ p ∈ pocketPV lo dn up hi := by
  have hs' : s ∈ segment hi lo := by rw [segment_comm]; exact hs
  exact pocket_pv hP hL h1 h2 h3 h4 hw0 hw2 hw3 hs' (Polygon.sees_comm.1 hsees)

/-- The mouth `[dn, up]` of a pocket lies in the pocket piece. -/
theorem add_mouth_subset (h1 : 0 < det lo dn up) (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo)
    (h4 : 0 < det hi lo dn) : segment dn up ⊆ piece (quad lo dn up hi) := by
  intro q hq
  refine edge_subset_piece (isPiece_quad h1 h2 h3 h4) (j := 1) (by simp [quad, Polygon.n]) ?_
  simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n] using hq

/-- The nook segment `[lo, hi]` of a pocket lies in the pocket piece. -/
theorem add_nook_subset (h1 : 0 < det lo dn up) (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo)
    (h4 : 0 < det hi lo dn) : segment lo hi ⊆ piece (quad lo dn up hi) := by
  intro q hq
  rw [segment_comm] at hq
  refine edge_subset_piece (isPiece_quad h1 h2 h3 h4) (j := 3) (by simp [quad, Polygon.n]) ?_
  simpa [Polygon.edge, quad, Polygon.vtx, Polygon.n] using hq

/-- A point strictly right of a vertical mouth `dn.1 = up.1` (with `dn` below `up`) is not in
the pocket. -/
theorem add_not_mem_pocket {g : Point} (hd : dn.1 = up.1) (hdu : dn.2 < up.2)
    (hg : dn.1 < g.1) : g ∉ piece (quad lo dn up hi) := by
  intro h
  have h1 := (mem_piece_quad.1 h).2.1
  unfold det at h1
  rw [← hd] at h1
  nlinarith

end Pocket

/-! ### Wedges hanging from a room (aux regions) -/

/-- The door of the triangle `m₁, tip, m₂` with opening side `2` is its mouth `[m₂, m₁]`. -/
theorem door_tri_two {m₁ tip m₂ : Point} :
    door (tri m₁ tip m₂) (· = 2) = segment m₂ m₁ := by
  ext y
  constructor
  · rintro ⟨j, -, rfl, hy⟩
    simpa [Polygon.edge, tri, Polygon.vtx, Polygon.n] using hy
  · intro hy
    exact ⟨2, by simp [tri, Polygon.n], rfl, by simpa [Polygon.edge, tri, Polygon.vtx, Polygon.n]⟩

/-- **Viewers of a wedge tip hanging from a room (L4.1').**  Let `m₁, tip, m₂` be a
counter-clockwise wedge whose sides `m₁ → tip`, `tip → m₂` are edges of `P`, hanging from side
`j` of a convex room `K` (walls and openings `O`): the mouth `[m₂, m₁]` lies in the relative
interior of side `j` and the tip strictly outside it.  If the cone of the wedge meets the door
of `K` only on the line of side `j`, then every point seeing the tip lies in the wedge triangle,
or in the cone and in `K`. -/
theorem add_sees_wedge_room (hP : P.Simple) (hL : P.InteriorLeft) {m₁ tip m₂ : Point}
    (htri : 0 < det m₁ tip m₂) (hw₁ : PEdge P m₁ tip) (hw₂ : PEdge P tip m₂)
    {K : Polygon} (hK : IsPiece K) {O : ℕ → Prop} (hWO : ∀ j < K.n, O j ∨ IsWall P K j)
    {j : ℕ} (hj : j < K.n)
    (hm : ∀ q ∈ segment m₂ m₁, ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      q = lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) τ)
    (htip : det (K.vtx j) (K.vtx ((j + 1) % K.n)) tip < 0)
    (hdoor : ∀ y ∈ door K O, 0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) y →
      0 ≤ det m₁ tip y → 0 ≤ det tip m₂ y → False)
    {p : Point} (h : P.Sees p tip) :
    p ∈ piece (tri m₁ tip m₂) ∨ (0 ≤ det m₁ tip p ∧ 0 ≤ det tip m₂ p ∧ p ∈ piece K) := by
  by_cases hpT : p ∈ piece (tri m₁ tip m₂)
  · exact Or.inl hpT
  right
  have hT := isPiece_tri htri
  have hWOT : ∀ i < (tri m₁ tip m₂).n, i = 2 ∨ IsWall P (tri m₁ tip m₂) i := by
    intro i hi
    simp only [tri, Polygon.n, List.length_cons, List.length_nil] at hi
    interval_cases i
    · right; simpa [IsWall, PEdge, tri, Polygon.vtx, Polygon.n] using hw₁
    · right; simpa [IsWall, PEdge, tri, Polygon.vtx, Polygon.n] using hw₂
    · left; rfl
  have htipT : tip ∈ piece (tri m₁ tip m₂) := vtx_mem_piece hT (k := 1) (by simp [tri, Polygon.n])
  have htipD : tip ∉ door (tri m₁ tip m₂) (· = 2) := by
    rw [door_tri_two]
    intro hm'
    have h0 := det_eq_zero_of_mem_segment hm'
    rw [det_cyclic_right] at h0
    linarith
  obtain ⟨i, -, rfl, q, hq, -, t, ht, hpt⟩ :=
    exists_exit_ray hP hL hT hWOT htipT htipD hpT (Polygon.sees_comm.1 h)
  have hq' : q ∈ segment m₂ m₁ := by simpa [Polygon.edge, tri, Polygon.vtx, Polygon.n] using hq
  -- the cone conditions at `q` and `p`
  have hqc : 0 ≤ det m₁ tip q ∧ 0 ≤ det tip m₂ q := by
    obtain ⟨μ, hμ0, hμ1, hqe⟩ := mem_segment_iff_lerp.1 hq'
    rw [hqe, det_lerp, det_lerp]
    have e1 : det m₁ tip m₁ = 0 := by unfold det; ring
    have e2 : det tip m₂ m₂ = 0 := by unfold det; ring
    have e3 : det tip m₂ m₁ = det m₁ tip m₂ := det_cyclic m₁ tip m₂
    rw [e1, e2, e3]
    constructor <;> nlinarith
  have hself1 : det m₁ tip tip = 0 := by unfold det; ring
  have hself2 : det tip m₂ tip = 0 := by unfold det; ring
  have hpc : 0 ≤ det m₁ tip p ∧ 0 ≤ det tip m₂ p := by
    rw [hpt, det_lerp, det_lerp, hself1, hself2]
    constructor <;> nlinarith
  refine ⟨hpc.1, hpc.2, ?_⟩
  by_contra hpK
  -- the sight line continues from the mouth into `K` and must leave `K` through its door
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [lerp_one] at hpt
    exact hpT (hpt ▸ edge_subset_piece hT (j := 2) (by simp [tri, Polygon.n]) hq)
  have ht1' : 1 < t := lt_of_le_of_ne ht (Ne.symm ht1)
  obtain ⟨τ, hτ0, hτ1, hqτ⟩ := hm q hq'
  have hq0 : det (K.vtx j) (K.vtx ((j + 1) % K.n)) q = 0 := by
    rw [hqτ]; exact det_lerp_self _ _ _
  have hpj : 0 < det (K.vtx j) (K.vtx ((j + 1) % K.n)) p := by
    rw [hpt, det_lerp, hq0]; nlinarith
  have htne : t ≠ 0 := by linarith
  have hqseg : q ∈ segment tip p := by
    have e : lerp tip p (1 / t) = q := by rw [hpt]; exact lerp_lerp_inv tip q htne
    rw [← e]
    exact lerp_mem_segment _ _ (by positivity) ((div_le_one (by linarith)).2 ht)
  have hqp : P.Sees q p := add_sees_of_mem hqseg (Polygon.sees_comm.1 h)
  obtain ⟨μ, hμ0, hμ1, hyD, hyj, -⟩ :=
    exit_after_crossing hP hL hK hWO hj hτ0 hτ1 hqτ hpj hpK hqp
  refine hdoor _ hyD hyj ?_ ?_
  · rw [det_lerp]; nlinarith [hqc.1, hpc.1]
  · rw [det_lerp]; nlinarith [hqc.2, hpc.2]

/-- The pentagon with vertices `a, b, c, d, e`. -/
def pent (a b c d e : Point) : Polygon := ⟨[a, b, c, d, e]⟩

/-- Membership in a pentagon piece. -/
theorem mem_piece_pent {a b c d e x : Point} :
    x ∈ piece (pent a b c d e) ↔
      0 ≤ det a b x ∧ 0 ≤ det b c x ∧ 0 ≤ det c d x ∧ 0 ≤ det d e x ∧ 0 ≤ det e a x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [pent, Polygon.vtx, Polygon.n] using h 0 (by simp [pent, Polygon.n])
    · simpa [pent, Polygon.vtx, Polygon.n] using h 1 (by simp [pent, Polygon.n])
    · simpa [pent, Polygon.vtx, Polygon.n] using h 2 (by simp [pent, Polygon.n])
    · simpa [pent, Polygon.vtx, Polygon.n] using h 3 (by simp [pent, Polygon.n])
    · simpa [pent, Polygon.vtx, Polygon.n] using h 4 (by simp [pent, Polygon.n])
  · rintro ⟨h0, h1, h2, h3, h4⟩ j hj
    simp only [pent, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simpa [pent, Polygon.vtx, Polygon.n]

/-- The sides of a pentagon. -/
theorem pent_edge (a b c d e : Point) :
    (pent a b c d e).edge 0 = segment a b ∧ (pent a b c d e).edge 1 = segment b c ∧
      (pent a b c d e).edge 2 = segment c d ∧ (pent a b c d e).edge 3 = segment d e ∧
      (pent a b c d e).edge 4 = segment e a :=
  ⟨rfl, rfl, rfl, rfl, by simp [Polygon.edge, pent, Polygon.vtx, Polygon.n]⟩

/-- A pentagon all of whose vertices lie weakly left of all sides, with a point strictly left
of all sides, is a piece. -/
theorem isPiece_pent {a b c d e : Point}
    (hv : ∀ x ∈ ({a, b, c, d, e} : Set Point), x ∈ piece (pent a b c d e))
    (o : Point) (ho : 0 < det a b o ∧ 0 < det b c o ∧ 0 < det c d o ∧ 0 < det d e o ∧
      0 < det e a o) : IsPiece (pent a b c d e) := by
  refine ⟨fun j hj k hk => ?_, ⟨o, fun j hj => ?_⟩⟩
  · have hk' : (pent a b c d e).vtx k ∈ ({a, b, c, d, e} : Set Point) := by
      simp only [pent, Polygon.n, List.length_cons, List.length_nil] at hk
      interval_cases k <;> simp [pent, Polygon.vtx]
    exact hv _ hk' j hj
  · simp only [pent, Polygon.n, List.length_cons, List.length_nil] at hj
    obtain ⟨h0, h1, h2, h3, h4⟩ := ho
    interval_cases j <;> simpa [pent, Polygon.vtx, Polygon.n]

/-! ## `addLe` -/

section addLe

variable {G : ℝ}

/-- `addLe`: the x-pocket `Xlo, P, N1, Xhi` (mouth `[P, N1]`). -/
noncomputable def alPocketX (G : ℝ) : Polygon := quad (alXlo G) (alP G) (alN1 G) (alXhi G)
/-- `addLe`: the y-pocket `Ylo, R, N3, Yhi` (mouth `[R, N3]`). -/
noncomputable def alPocketY (G : ℝ) : Polygon := quad (alYlo G) (alR G) (alN3 G) (alYhi G)
/-- `addLe`: the z-pocket `Zlo, N2, Q, Zhi` (mouth `[N2, Q]`). -/
noncomputable def alPocketZ (G : ℝ) : Polygon := quad (alZlo G) (alN2 G) (alQ G) (alZhi G)

/-- The x-pocket of `addLe` is strictly convex and counter-clockwise. -/
theorem alPocketX_ccw :
    0 < det (alXlo G) (alP G) (alN1 G) ∧ 0 < det (alP G) (alN1 G) (alXhi G) ∧
      0 < det (alN1 G) (alXhi G) (alXlo G) ∧ 0 < det (alXhi G) (alXlo G) (alP G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, alXlo, alP, alN1, alXhi] <;> linarith

/-- The y-pocket of `addLe` is strictly convex and counter-clockwise. -/
theorem alPocketY_ccw :
    0 < det (alYlo G) (alR G) (alN3 G) ∧ 0 < det (alR G) (alN3 G) (alYhi G) ∧
      0 < det (alN3 G) (alYhi G) (alYlo G) ∧ 0 < det (alYhi G) (alYlo G) (alR G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, alYlo, alR, alN3, alYhi] <;> linarith

/-- The z-pocket of `addLe` is strictly convex and counter-clockwise. -/
theorem alPocketZ_ccw :
    0 < det (alZlo G) (alN2 G) (alQ G) ∧ 0 < det (alN2 G) (alQ G) (alZhi G) ∧
      0 < det (alQ G) (alZhi G) (alZlo G) ∧ 0 < det (alZhi G) (alZlo G) (alN2 G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, alZlo, alN2, alQ, alZhi] <;> linarith

/-- The walls of the three pockets of `addLe` (`lo → dn`, `up → hi`, `hi → lo`) are edges of
`P`. -/
structure AlWalls (P : Polygon) (G : ℝ) : Prop where
  /-- x-pocket: `Xlo → P`. -/
  x0 : PEdge P (alXlo G) (alP G)
  /-- x-pocket: `N1 → Xhi`. -/
  x2 : PEdge P (alN1 G) (alXhi G)
  /-- x-pocket: `Xhi → Xlo`. -/
  x3 : PEdge P (alXhi G) (alXlo G)
  /-- y-pocket: `Ylo → R`. -/
  y0 : PEdge P (alYlo G) (alR G)
  /-- y-pocket: `N3 → Yhi`. -/
  y2 : PEdge P (alN3 G) (alYhi G)
  /-- y-pocket: `Yhi → Ylo`. -/
  y3 : PEdge P (alYhi G) (alYlo G)
  /-- z-pocket: `Zlo → N2`. -/
  z0 : PEdge P (alZlo G) (alN2 G)
  /-- z-pocket: `Q → Zhi`. -/
  z2 : PEdge P (alQ G) (alZhi G)
  /-- z-pocket: `Zhi → Zlo`. -/
  z3 : PEdge P (alZhi G) (alZlo G)

/-- The x-nook segment of `addLe`, explicitly. -/
theorem al_nookX_iff {s : Point} :
    s ∈ segment (alXlo G) (alXhi G) ↔ s.1 = G + 30 ∧ -7589 / 64 ≤ s.2 ∧ s.2 ≤ -7561 / 64 :=
  mem_segment_vert_iff (by norm_num)

/-- The y-nook segment of `addLe`, explicitly. -/
theorem al_nookY_iff {s : Point} :
    s ∈ segment (alYlo G) (alYhi G) ↔ s.1 = G + 30 ∧ -4443 / 32 ≤ s.2 ∧ s.2 ≤ -4417 / 32 :=
  mem_segment_vert_iff (by norm_num)

/-- The z-nook segment of `addLe`, explicitly. -/
theorem al_nookZ_iff {s : Point} :
    s ∈ segment (alZlo G) (alZhi G) ↔ s.1 = G + 30 ∧ -2001 / 16 ≤ s.2 ∧ s.2 ≤ -499 / 4 :=
  mem_segment_vert_iff (by norm_num)

/-! ### What each guard sees (L7.3) -/

section Sees

variable (hP : P.Simple) (hL : P.InteriorLeft) (hW : AlWalls P G)
include hP hL hW

/-- `addLe`, x-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_P(g)` and
`≤ π_{N1}(g)`. -/
theorem al_sees_x {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (alXlo G) (alXhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (alP G) (G + 30) ≤ h ∧ h ≤ vproj g (alN1 G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketX_ccw (G := G)
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3
    (add_not_mem_pocket rfl (by simp only [alP, alN1]; norm_num) hg) hg hg hh hs

/-- `addLe`, y-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_R(g)` and
`≤ π_{N3}(g)`. -/
theorem al_sees_y {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (alYlo G) (alYhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (alR G) (G + 30) ≤ h ∧ h ≤ vproj g (alN3 G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketY_ccw (G := G)
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3
    (add_not_mem_pocket rfl (by simp only [alR, alN3]; norm_num) hg) hg hg hh hs

/-- `addLe`, z-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_{N2}(g)` and
`≤ π_Q(g)`. -/
theorem al_sees_z {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (alZlo G) (alZhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (alN2 G) (G + 30) ≤ h ∧ h ≤ vproj g (alQ G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketZ_ccw (G := G)
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3
    (add_not_mem_pocket rfl (by simp only [alN2, alQ]; norm_num) hg) hg hg hh hs

end Sees

/-- The three nooks of `addLe` are covered by the aux guard `a` and the inputs of values
`v_x, v_y, v_z`. -/
def AlCover (P : Polygon) (G : ℝ) (a : Point) (vx vy vz : ℝ) : Prop :=
  (∀ s ∈ segment (alXlo G) (alXhi G), P.Sees a s ∨ P.Sees (inPt (G + 370) vx) s) ∧
    (∀ s ∈ segment (alYlo G) (alYhi G), P.Sees a s ∨ P.Sees (inPt (G + 210) vy) s) ∧
    (∀ s ∈ segment (alZlo G) (alZhi G), P.Sees a s ∨ P.Sees (inPt (G + 530) vz) s)

/-- **`addLe`: coverage ⇒ `v_x + v_y ≤ v_z` (L7.4).**  If the walls of the three pockets are
edges of `P` and the aux guard `a` (any point right of `x = G + 50`) and the three inputs cover
the three nook segments, then `v_x + v_y ≤ v_z`. -/
theorem al_rel_of_cover (hP : P.Simple) (hL : P.InteriorLeft) (hW : AlWalls P G) {a : Point}
    (ha : G + 50 < a.1) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2) (hcov : AlCover P G a vx vy vz) :
    vx + vy ≤ vz := by
  obtain ⟨hcx, hcy, hcz⟩ := hcov
  refine al_rel_of_cover_alg (G := G) a hx1 hx2 hy1 hy2 hz1 hz2 ?_ ?_ ?_
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (alXlo G) (alXhi G) := al_nookX_iff.2 ⟨rfl, h1, h2⟩
    rcases hcx _ hs with hh | hh
    · exact Or.inl (al_sees_x hP hL hW ha hs hh).1
    · right
      have := (al_sees_x hP hL hW (by simp only [inPt_fst]; linarith) hs hh).2
      rwa [al_shadow_x] at this
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (alYlo G) (alYhi G) := al_nookY_iff.2 ⟨rfl, h1, h2⟩
    rcases hcy _ hs with hh | hh
    · exact Or.inl (al_sees_y hP hL hW ha hs hh).1
    · right
      have := (al_sees_y hP hL hW (by simp only [inPt_fst]; linarith) hs hh).2
      rwa [al_shadow_y] at this
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (alZlo G) (alZhi G) := al_nookZ_iff.2 ⟨rfl, h1, h2⟩
    rcases hcz _ hs with hh | hh
    · exact Or.inl (al_sees_z hP hL hW ha hs hh).2
    · right
      have := (al_sees_z hP hL hW (by simp only [inPt_fst]; linarith) hs hh).1
      rwa [al_shadow_z] at this

/-! ### Partial visibility (L7.6) -/

section PV

variable (hP : P.Simple) (hL : P.InteriorLeft) (hW : AlWalls P G)
include hP hL hW

/-- **`addLe`, viewers of the x-nook.**  A point seeing a point of the x-nook is in the
x-pocket, or right of `x = G + 50`, and in the input band `0 ≤ y ≤ 6` in `[G + 353, G + 513]`
(so it is not on the inputs at `G + 210` and `G + 530`). -/
theorem al_viewer_x {s p : Point} (hs : s ∈ segment (alXlo G) (alXhi G)) (hsees : P.Sees p s) :
    p ∈ piece (alPocketX G) ∨
      (G + 50 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 513) ∧ (0 ≤ p.2 → G + 353 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketX_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, alXlo, alP, alN1, alXhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

/-- **`addLe`, viewers of the y-nook.**  A point seeing a point of the y-nook is in the
y-pocket, or right of `x = G + 50`, and in the input band in `[G + 202, G + 318]` (not on the
inputs at `G + 370`, `G + 530`). -/
theorem al_viewer_y {s p : Point} (hs : s ∈ segment (alYlo G) (alYhi G)) (hsees : P.Sees p s) :
    p ∈ piece (alPocketY G) ∨
      (G + 50 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 318) ∧ (0 ≤ p.2 → G + 202 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketY_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, alYlo, alR, alN3, alYhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

/-- **`addLe`, viewers of the z-nook.**  A point seeing a point of the z-nook is in the
z-pocket, or right of `x = G + 50`, and in the input band in `[G + 384, G + 555]` (not on the
inputs at `G + 210`, `G + 370`). -/
theorem al_viewer_z {s p : Point} (hs : s ∈ segment (alZlo G) (alZhi G)) (hsees : P.Sees p s) :
    p ∈ piece (alPocketZ G) ∨
      (G + 50 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 555) ∧ (0 ≤ p.2 → G + 384 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := alPocketZ_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, alZlo, alN2, alQ, alZhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

end PV

/-- The pockets of `addLe` lie in the strip `G + 30 ≤ x ≤ G + 50`, below the floor. -/
theorem al_pocket_bounds {p : Point}
    (hp : p ∈ piece (alPocketX G) ∨ p ∈ piece (alPocketY G) ∨ p ∈ piece (alPocketZ G)) :
    G + 30 ≤ p.1 ∧ p.1 ≤ G + 50 ∧ p.2 ≤ -111 := by
  rcases hp with hp | hp | hp <;>
  · obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 hp
    simp only [det, alXlo, alP, alN1, alXhi, alYlo, alR, alN3, alYhi, alZlo, alN2, alQ,
      alZhi] at h0 h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩

/-! ### The room and the aux region -/

/-- `addLe`: tip of the aux wedge. -/
noncomputable def alTip (G : ℝ) : Point := (G + 110, -519 / 4)
/-- `addLe`: first mouth end of the aux wedge. -/
noncomputable def alM1 (G : ℝ) : Point := (G + 439 / 4, -128)
/-- `addLe`: second mouth end of the aux wedge. -/
noncomputable def alM2 (G : ℝ) : Point := (G + 441 / 4, -128)
/-- `addLe`: left end `WL` of the window. -/
noncomputable def alWL (G : ℝ) : Point := (G + 200, -1)
/-- `addLe`: right end `WR` of the window. -/
noncomputable def alWR (G : ℝ) : Point := (G + 527, -1)
/-- `addLe`: bottom right corner of the room. -/
noncomputable def alBR (G : ℝ) : Point := (G + 527, -128)

/-- `addLe`: the convex room `WL, T0 = N1, B0 = R, BR, WR` (walls `WL → T0`, `BR → WR`;
openings: the left side `x = G + 50`, the bottom `y = −128`, the window `y = −1`). -/
noncomputable def alRoom (G : ℝ) : Polygon := pent (alWL G) (alN1 G) (alR G) (alBR G) (alWR G)

/-- `addLe`: the aux wedge `M1, tip, M2`. -/
noncomputable def alAuxTri (G : ℝ) : Polygon := tri (alM1 G) (alTip G) (alM2 G)

/-- `addLe`: the cone of the aux wedge. -/
def alCone (G : ℝ) : Set Point := {p | 0 ≤ det (alM1 G) (alTip G) p ∧ 0 ≤ det (alTip G) (alM2 G) p}

/-- `addLe`: the **aux region** `cone ∩ room`. -/
def alAuxRegion (G : ℝ) : Set Point := alCone G ∩ piece (alRoom G)

/-- Membership in the room of `addLe`, in coordinates. -/
theorem mem_alRoom {p : Point} :
    p ∈ piece (alRoom G) ↔ 0 ≤ 441 / 4 * (p.1 - G - 50) - 150 * p.2 - 33375 / 2 ∧
      G + 50 ≤ p.1 ∧ -128 ≤ p.2 ∧ p.1 ≤ G + 527 ∧ p.2 ≤ -1 := by
  rw [alRoom, mem_piece_pent]
  simp only [det, alWL, alN1, alR, alBR, alWR]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The room of `addLe` is a convex piece. -/
theorem alRoom_isPiece : IsPiece (alRoom G) := by
  refine isPiece_pent ?_ (G + 300, -50) ?_
  · intro x hx
    rw [← alRoom, mem_alRoom]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp only [alWL, alN1, alR, alBR, alWR] <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · simp only [det, alWL, alN1, alR, alBR, alWR]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Points of the left side `x = G + 50`, `−128 ≤ y ≤ −445/4` lie in the room. -/
theorem alRoom_left {q : Point} (h1 : q.1 = G + 50) (h2 : -128 ≤ q.2) (h3 : q.2 ≤ -445 / 4) :
    q ∈ piece (alRoom G) :=
  mem_alRoom.2 ⟨by rw [h1]; linarith, by linarith, h2, by linarith, by linarith⟩

/-- The window lies in the room. -/
theorem alRoom_window {q : Point} (hq : q ∈ segment (alWL G) (alWR G)) : q ∈ piece (alRoom G) := by
  obtain ⟨h1, h2, h3⟩ :=
    (mem_segment_horiz_iff (c := -1) (x₁ := G + 200) (x₂ := G + 527) (by linarith)).1 hq
  exact mem_alRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, h3, by linarith⟩

/-- The walls of the aux wedge and of the room of `addLe` are edges of `P`. -/
structure AlAuxWalls (P : Polygon) (G : ℝ) : Prop where
  /-- Aux wedge: `M1 → tip`. -/
  w1 : PEdge P (alM1 G) (alTip G)
  /-- Aux wedge: `tip → M2`. -/
  w2 : PEdge P (alTip G) (alM2 G)
  /-- Room: `WL → T0`. -/
  r0 : PEdge P (alWL G) (alN1 G)
  /-- Room: `BR → WR`. -/
  r3 : PEdge P (alBR G) (alWR G)

/-- **`addLe`: viewers of the aux tip (L4.1').**  Every point seeing the tip of the aux wedge
lies in the aux wedge or in the aux region `cone ∩ room`. -/
theorem al_sees_auxTip (hP : P.Simple) (hL : P.InteriorLeft) (hA : AlAuxWalls P G) {p : Point}
    (h : P.Sees p (alTip G)) : p ∈ piece (alAuxTri G) ∪ alAuxRegion G := by
  have htri : 0 < det (alM1 G) (alTip G) (alM2 G) := by
    simp only [det, alM1, alTip, alM2]; linarith
  have hWO : ∀ j < (alRoom G).n, (j = 1 ∨ j = 2 ∨ j = 4) ∨ IsWall P (alRoom G) j := by
    intro j hj
    simp only [alRoom, pent, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j
    · right; simpa [IsWall, PEdge, alRoom, pent, Polygon.vtx, Polygon.n] using hA.r0
    · left; left; rfl
    · left; right; left; rfl
    · right; simpa [IsWall, PEdge, alRoom, pent, Polygon.vtx, Polygon.n] using hA.r3
    · left; right; right; rfl
  have v2 : (alRoom G).vtx 2 = alR G := rfl
  have v3 : (alRoom G).vtx ((2 + 1) % (alRoom G).n) = alBR G := rfl
  have hj : 2 < (alRoom G).n := by simp [alRoom, pent, Polygon.n]
  have hm : ∀ q ∈ segment (alM2 G) (alM1 G), ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      q = lerp ((alRoom G).vtx 2) ((alRoom G).vtx ((2 + 1) % (alRoom G).n)) τ := by
    intro q hq
    obtain ⟨μ, hμ0, hμ1, rfl⟩ := mem_segment_iff_lerp.1 hq
    refine ⟨(241 / 4 - μ / 2) / 477, by linarith, by linarith, ?_⟩
    rw [v2, v3]
    ext
    · simp only [lerp_fst, alM1, alM2, alR, alBR]; ring
    · simp only [lerp_snd, alM1, alM2, alR, alBR]; ring
  have htip : det ((alRoom G).vtx 2) ((alRoom G).vtx ((2 + 1) % (alRoom G).n)) (alTip G) < 0 := by
    rw [v2, v3]; simp only [det, alR, alBR, alTip]; linarith
  have hdoor : ∀ y ∈ door (alRoom G) (fun j => j = 1 ∨ j = 2 ∨ j = 4),
      0 < det ((alRoom G).vtx 2) ((alRoom G).vtx ((2 + 1) % (alRoom G).n)) y →
      0 ≤ det (alM1 G) (alTip G) y → 0 ≤ det (alTip G) (alM2 G) y → False := by
    rw [v2, v3]
    rintro y ⟨j, -, hO, hy⟩ hpos hc1 hc2
    simp only [det, alR, alBR, alM1, alTip, alM2] at hpos hc1 hc2
    rcases hO with rfl | rfl | rfl
    · change y ∈ segment (alN1 G) (alR G) at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [alN1, alR] at hc1
      nlinarith
    · change y ∈ segment (alR G) (alBR G) at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [alR, alBR] at hpos
      nlinarith
    · rw [show (alRoom G).edge 4 = segment (alWR G) (alWL G) from
        (pent_edge _ _ _ _ _).2.2.2.2] at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [alWR, alWL] at hc2
      nlinarith
  rcases add_sees_wedge_room hP hL htri hA.w1 hA.w2 alRoom_isPiece hWO hj hm htip hdoor h with
    h' | ⟨h1, h2, h3⟩
  · exact Or.inl h'
  · exact Or.inr ⟨⟨h1, h2⟩, h3⟩

/-- **`addLe`: position of the aux viewers.**  The aux wedge and the aux region lie in
`G + 91 ≤ x ≤ G + 129`, `y ≤ −1` (in particular right of `x = G + 50`, and away from the
slabs `|x − b| ≤ 3` of the inputs at `b = G + 210, G + 370, G + 530`). -/
theorem al_aux_bounds {p : Point} (hp : p ∈ piece (alAuxTri G) ∪ alAuxRegion G) :
    G + 91 ≤ p.1 ∧ p.1 ≤ G + 129 ∧ p.2 ≤ -1 := by
  have key : ∀ q : Point, 0 ≤ det (alM1 G) (alTip G) q → 0 ≤ det (alTip G) (alM2 G) q →
      q.2 ≤ -1 → G + 91 ≤ q.1 ∧ q.1 ≤ G + 129 ∧ q.2 ≤ -1 := by
    intro q h1 h2 h3
    simp only [det, alM1, alTip, alM2] at h1 h2
    exact ⟨by linarith, by linarith, h3⟩
  rcases hp with hp | ⟨⟨h1, h2⟩, hR⟩
  · obtain ⟨h1, h2, h3⟩ := mem_piece_tri.1 hp
    refine key p h1 h2 ?_
    simp only [det, alM2, alM1] at h3
    linarith
  · exact key p h1 h2 (mem_alRoom.1 hR).2.2.2.2

/-- **`addLe`: the canonical aux point lies in the aux region** (for `v_x, v_y ≥ 1/2`,
`v_x + v_y ≤ 2`). -/
theorem alI_mem_auxRegion {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy)
    (hxy : vx + vy ≤ 2) : alI G vx vy ∈ alAuxRegion G := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := alI_pos (G := G) hx1 hy1 hxy
  have hf := alI_fst (G := G) (vx := vx) (vy := vy) (by linarith) (by linarith)
  refine ⟨⟨?_, ?_⟩, mem_alRoom.2 ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith⟩⟩
  · simp only [det, alM1, alTip]; linarith
  · simp only [det, alTip, alM2]; linarith

/-! ### Positive visibility (L7.8 for the nooks) -/

section Positive

variable {A : Set Point}

/-- `addLe`, x-nook: with the aux guard at `I(v_x, v_y)`, the aux guard and the x-input cover
the x-nook. -/
theorem al_cover_x (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled) (hXP : piece (alPocketX G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2) (hxA : inPt (G + 370) vx ∈ A) :
    ∀ s ∈ segment (alXlo G) (alXhi G), P.Sees (alI G vx vy) s ∨
      P.Sees (inPt (G + 370) vx) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := al_nookX_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := alPocketX_ccw (G := G)
  have hsX : s ∈ piece (alPocketX G) := add_nook_subset c1 c2 c3 c4 hs
  have hmX : segment (alP G) (alN1 G) ⊆ piece (alPocketX G) := add_mouth_subset c1 c2 c3 c4
  have hx2 : vx ≤ 2 := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hmR : ∀ q ∈ segment (alP G) (alN1 G), q ∈ piece (alRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -113) (y₂ := -445 / 4) (by norm_num)).1 hq
    exact alRoom_left h1 (by linarith) h3
  have hd : ∀ p : Point, det (alP G) (alN1 G) p = -(7 / 4) * (p.1 - G - 50) := fun p => by
    simp only [det, alP, alN1]; ring
  rw [e]
  by_cases hh : alSx vx ≤ s.2
  · left
    have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
    have hIf := alI_fst (G := G) hx2 hy0
    obtain ⟨q, hq, hqs⟩ : ∃ q ∈ segment (alP G) (alN1 G),
        q ∈ segment (alI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hd, hd]; simp only; nlinarith
      · rw [alI_P hx2 hy0]
        have := alI_N1 (G := G) hx1 hx2 hy1
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact sees_of_two_convex (convex_piece _) (convex_piece _) hRP hXP hI.2 (e ▸ hsX) (hmR q hq)
      (hmX hq) hqs
  · right
    push Not at hh
    have hg1 : (alP G).1 < (inPt (G + 370) vx).1 := by simp only [alP, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (alP G) (alN1 G),
        q ∈ segment (inPt (G + 370) vx) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hd, hd]; simp only [inPt_fst]; nlinarith
      · rw [al_shadow_x]
        have := al_input_x_P (G := G) (v := vx) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 200, -1) : Point) (G + 527, -1),
        q ∈ segment (inPt (G + 370) vx) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -445 / 4 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -113) (y₂ := -445 / 4) (by norm_num)).1 hq₂).2.2
    refine add_sees_chain3 hA hAP (convex_piece _) hRP (convex_piece _) hXP hxA (hWA hq₁)
      (alRoom_window hq₁) (hmR q₂ hq₂) (hmX hq₂) (e ▸ hsX) hq₁s ?_
    exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
      (by rw [hq₁2]; linarith)

/-- `addLe`, y-nook: with the aux guard at `I(v_x, v_y)`, the aux guard and the y-input cover
the y-nook. -/
theorem al_cover_y (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hYP : piece (alPocketY G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2) (hyA : inPt (G + 210) vy ∈ A) :
    ∀ s ∈ segment (alYlo G) (alYhi G), P.Sees (alI G vx vy) s ∨
      P.Sees (inPt (G + 210) vy) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := al_nookY_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := alPocketY_ccw (G := G)
  have hsY : s ∈ piece (alPocketY G) := add_nook_subset c1 c2 c3 c4 hs
  have hmY : segment (alR G) (alN3 G) ⊆ piece (alPocketY G) := add_mouth_subset c1 c2 c3 c4
  have hx2 : vx ≤ 2 := by linarith
  have hy2 : vy ≤ 2 := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hmR : ∀ q ∈ segment (alR G) (alN3 G), q ∈ piece (alRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -128) (y₂ := -491 / 4) (by norm_num)).1 hq
    exact alRoom_left h1 h2 (by linarith)
  have hd : ∀ p : Point, det (alR G) (alN3 G) p = -(21 / 4) * (p.1 - G - 50) := fun p => by
    simp only [det, alR, alN3]; ring
  rw [e]
  by_cases hh : alSy vy ≤ s.2
  · left
    have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
    have hIf := alI_fst (G := G) hx2 hy0
    obtain ⟨q, hq, hqs⟩ : ∃ q ∈ segment (alR G) (alN3 G),
        q ∈ segment (alI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hd, hd]; simp only; nlinarith
      · rw [alI_R hx2 hy0]
        have := alI_N3 (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact sees_of_two_convex (convex_piece _) (convex_piece _) hRP hYP hI.2 (e ▸ hsY) (hmR q hq)
      (hmY hq) hqs
  · right
    push Not at hh
    have hg1 : (alR G).1 < (inPt (G + 210) vy).1 := by simp only [alR, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (alR G) (alN3 G),
        q ∈ segment (inPt (G + 210) vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hd, hd]; simp only [inPt_fst]; nlinarith
      · rw [al_shadow_y]
        have := al_input_y_R (G := G) (v := vy) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 200, -1) : Point) (G + 527, -1),
        q ∈ segment (inPt (G + 210) vy) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -491 / 4 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -128) (y₂ := -491 / 4) (by norm_num)).1 hq₂).2.2
    refine add_sees_chain3 hA hAP (convex_piece _) hRP (convex_piece _) hYP hyA (hWA hq₁)
      (alRoom_window hq₁) (hmR q₂ hq₂) (hmY hq₂) (e ▸ hsY) hq₁s ?_
    exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
      (by rw [hq₁2]; linarith)

/-- `addLe`, z-nook: with the aux guard at `I(v_x, v_y)` and `v_x + v_y ≤ v_z`, the aux guard
and the z-input cover the z-nook. -/
theorem al_cover_z (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hZP : piece (alPocketZ G) ⊆ P.filled) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hy1 : 1 / 2 ≤ vy) (hz2 : vz ≤ 2) (hzA : inPt (G + 530) vz ∈ A) (hrel : vx + vy ≤ vz) :
    ∀ s ∈ segment (alZlo G) (alZhi G), P.Sees (alI G vx vy) s ∨
      P.Sees (inPt (G + 530) vz) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := al_nookZ_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := alPocketZ_ccw (G := G)
  have hsZ : s ∈ piece (alPocketZ G) := add_nook_subset c1 c2 c3 c4 hs
  have hmZ : segment (alN2 G) (alQ G) ⊆ piece (alPocketZ G) := add_mouth_subset c1 c2 c3 c4
  have hxy : vx + vy ≤ 2 := by linarith
  have hx2 : vx ≤ 2 := by linarith
  have hy2 : vy ≤ 2 := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hmR : ∀ q ∈ segment (alN2 G) (alQ G), q ∈ piece (alRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -2994 / 25) (y₂ := -118) (by norm_num)).1 hq
    exact alRoom_left h1 (by linarith) (by linarith)
  have hd : ∀ p : Point, det (alN2 G) (alQ G) p = -(44 / 25) * (p.1 - G - 50) := fun p => by
    simp only [det, alN2, alQ]; ring
  rw [e]
  by_cases hh : s.2 ≤ vproj (alI G vx vy) (alQ G) (G + 30)
  · left
    have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
    have hIf := alI_fst (G := G) hx2 hy0
    obtain ⟨q, hq, hqs⟩ : ∃ q ∈ segment (alN2 G) (alQ G),
        q ∈ segment (alI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hd, hd]; simp only; nlinarith
      · have := alI_N2 (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact sees_of_two_convex (convex_piece _) (convex_piece _) hRP hZP hI.2 (e ▸ hsZ) (hmR q hq)
      (hmZ hq) hqs
  · right
    push Not at hh
    have hzs : alSz vz ≤ s.2 := le_trans ((alI_Q_ge_iff hx2 hy0).2 hrel) hh.le
    have hg1 : (alN2 G).1 < (inPt (G + 530) vz).1 := by simp only [alN2, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (alN2 G) (alQ G),
        q ∈ segment (inPt (G + 530) vz) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hd, hd]; simp only [inPt_fst]; nlinarith
      · rw [al_shadow_z]
        have := al_input_z_Q (G := G) (v := vz) hz2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hz1 : 1 / 2 ≤ vz := by linarith
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 200, -1) : Point) (G + 527, -1),
        q ∈ segment (inPt (G + 530) vz) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -118 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -2994 / 25) (y₂ := -118)
        (by norm_num)).1 hq₂).2.2
    refine add_sees_chain3 hA hAP (convex_piece _) hRP (convex_piece _) hZP hzA (hWA hq₁)
      (alRoom_window hq₁) (hmR q₂ hq₂) (hmZ hq₂) (e ▸ hsZ) hq₁s ?_
    exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
      (by rw [hq₁2]; linarith)

/-- **`addLe`: `v_x + v_y ≤ v_z` ⇒ coverage (L7.8 for the nooks).**  Let `A` (the hall) be a
convex part of the region containing the window and the three inputs, and let the room and the
three pockets lie in the region.  With the aux guard at the canonical point `I(v_x, v_y)`, the
three nooks are covered. -/
theorem al_cover_of_rel (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hXP : piece (alPocketX G) ⊆ P.filled) (hYP : piece (alPocketY G) ⊆ P.filled)
    (hZP : piece (alPocketZ G) ⊆ P.filled) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hy1 : 1 / 2 ≤ vy) (hz2 : vz ≤ 2) (hxA : inPt (G + 370) vx ∈ A)
    (hyA : inPt (G + 210) vy ∈ A) (hzA : inPt (G + 530) vz ∈ A) (hrel : vx + vy ≤ vz) :
    AlCover P G (alI G vx vy) vx vy vz :=
  ⟨al_cover_x hA hAP hWA hRP hXP hx1 hy1 (by linarith) hxA,
    al_cover_y hA hAP hWA hRP hYP hx1 hy1 (by linarith) hyA,
    al_cover_z hA hAP hWA hRP hZP hx1 hy1 hz2 hzA hrel⟩

/-- **`addLe`: the three nooks are covered iff `v_x + v_y ≤ v_z`** (aux guard at the canonical
point `I(v_x, v_y)`, `v_x, v_y ≥ 1/2`, `v_x + v_y ≤ 2`, `v_z ∈ [1/2, 2]`). -/
theorem al_cover_iff (hP : P.Simple) (hL : P.InteriorLeft) (hW : AlWalls P G)
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hXP : piece (alPocketX G) ⊆ P.filled) (hYP : piece (alPocketY G) ⊆ P.filled)
    (hZP : piece (alPocketZ G) ⊆ P.filled) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2)
    (hxA : inPt (G + 370) vx ∈ A) (hyA : inPt (G + 210) vy ∈ A)
    (hzA : inPt (G + 530) vz ∈ A) :
    AlCover P G (alI G vx vy) vx vy vz ↔ vx + vy ≤ vz :=
  ⟨al_rel_of_cover hP hL hW (alI_fst (by linarith) (by linarith)) hx1 (by linarith) hy1
      (by linarith) hz1 hz2,
    al_cover_of_rel hA hAP hWA hRP hXP hYP hZP hx1 hy1 hz2 hxA hyA hzA⟩

end Positive

/-! ### The template chain -/

/-- The `addLe` gadget chain of `Templates.lean`, translated by `ox` (needle tips at depth `H`),
is `WL, N1, Xhi, Xlo, P, Q, Zhi, Zlo, N2, N3, Yhi, Ylo, R, M1, tip, M2`, the needles of the
y- and x-inputs hanging from the bottom, `BR, WR`. -/
theorem chainAddLe_inst (H ox : ℚ) :
    chainAddLe.map (fun p => ratPoint (p.inst H ox)) =
      [alWL (ox : ℝ), alN1 (ox : ℝ), alXhi (ox : ℝ), alXlo (ox : ℝ), alP (ox : ℝ), alQ (ox : ℝ),
        alZhi (ox : ℝ), alZlo (ox : ℝ), alN2 (ox : ℝ), alN3 (ox : ℝ), alYhi (ox : ℝ),
        alYlo (ox : ℝ), alR (ox : ℝ), alM1 (ox : ℝ), alTip (ox : ℝ), alM2 (ox : ℝ),
        ((ox : ℝ) + 210, -128), ((ox : ℝ) + 210, -128 - (H : ℝ)), ((ox : ℝ) + 841 / 4, -128),
        ((ox : ℝ) + 370, -128), ((ox : ℝ) + 370, -128 - (H : ℝ)), ((ox : ℝ) + 1481 / 4, -128),
        alBR (ox : ℝ), alWR (ox : ℝ)] := by
  simp only [chainAddLe, List.map_cons, List.map_nil, Chain.RPt.inst, ratPoint, alWL, alN1,
    alXhi, alXlo, alP, alQ, alZhi, alZlo, alN2, alN3, alYhi, alYlo, alR, alM1, alTip, alM2, alBR,
    alWR]
  push_cast
  norm_num

end addLe

end Stade

end ArtGallery

end
