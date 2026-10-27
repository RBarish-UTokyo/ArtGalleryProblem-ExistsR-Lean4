module

public import ArtGallery.Vis.CertChecker
public import ArtGallery.Vis.Rooms
public import ArtGallery.Vis.StationaryGuard

/-!
# Section 5 templates: certificate tools for template chains

The gadget templates (`docs/section5/05_gadgets.md`, `07_template_vertices.md`) are fixed
integer vertex chains `V` (template coordinates multiplied by a common denominator).  All
template lemmas are stated for an **arbitrary** simple polygon `P` that contains the chain as a
contiguous chain of vertices (`ChainAt P V a`) and whose other edges avoid an explicit open
region `R` around the template (`SepAt P V a R`); the template polygon `P_T` (chain closed by a
fixed stub) is one such polygon, the units of the construction (after the similarity
`z ↦ m + z/(S·D)`) are the others.

Tools (soundness of Boolean certificates evaluated by `decide +kernel`):

* `not_sees_of_chainCross`: every segment between two convex hulls properly crosses a chain
  edge (`crossB`), hence is not in the region;
* `not_sees_of_chainHalf` (*half crossing*): the same for all segments `p q` with
  `det p q b > 0`, where `b` is an endpoint of a chain edge `a b` (the *shadow corner*): the
  remaining three sign conditions are checked on the vertices (`halfB`);
* `sees_of_gate`: two convex pieces of the region sharing a *gate* segment `[g₀, g₁]`; every
  segment from the first to the second piece with `det p q g₀ ≤ 0` passes through the gate
  (`gateB`), hence lies in the region;
* `hull_subset_filled_of_piece`: a convex hull of integer points whose interior misses every
  chain edge (explicit separators, `pieceB`) and whose interior lies in `R` (`Region.check`) is in the
  region once one interior point is; interior points from an edge of the chain
  (`seed_of_chain_edge`, via `InteriorLeft`) or from a previous piece;
* `chain_cone`, `not_sees_of_outCone`: the vertex cone lemma at a convex vertex of the chain.
-/

@[expose] public section

namespace ArtGallery.Sec5.Tmpl

open ArtGallery Set Polygon Vis.Cert
open ArtGallery.Irrational (HP)
open ArtGallery.Geometry (lerp)

/-! ### Template chains and separation -/

/-- Vertex `j` of an integer chain (total). -/
abbrev cv (V : List IPt) (j : ℕ) : IPt := V.getD j (0, 0)

/-- The integer chain `V` is the contiguous chain of vertices `P.vtx ((a + j) % P.n)` of `P`. -/
def ChainAt (P : Polygon) (V : List IPt) (a : ℕ) : Prop :=
  ∀ j < V.length, P.vtx ((a + j) % P.n) = intPoint (cv V j)

/-- An open convex polygon (`box`: all constraints `> 0`) minus finitely many closed convex
*zones* (each the set where all constraints of a list of half-planes are `≥ 0`). -/
structure Region where
  /-- The open box (strict constraints). -/
  box : List HP
  /-- The excluded zones. -/
  zones : List (List HP)

/-- Membership in the region: strictly inside the box and strictly outside one constraint of
every zone. -/
def Region.Mem (R : Region) (x : Point) : Prop :=
  (∀ c ∈ R.box, 0 < c.val x) ∧ ∀ W ∈ R.zones, ∃ c ∈ W, c.val x < 0

/-- No edge of `P` other than the chain edges meets the region `R`. -/
def SepAt (P : Polygon) (V : List IPt) (a : ℕ) (R : Region) : Prop :=
  ∀ i < P.n, (∀ j, j + 1 < V.length → (a + j) % P.n ≠ i) → ∀ x ∈ P.edge i, ¬ R.Mem x

variable {P : Polygon} {V : List IPt} {a : ℕ}

theorem n_pos_of_simple (hP : P.Simple) : 0 < P.n := by have := hP.1; omega

/-- The two endpoints of chain edge `j`. -/
theorem ChainAt.edge_vtx (hC : ChainAt P V a) {j : ℕ} (hj : j + 1 < V.length) :
    P.vtx ((a + j) % P.n) = intPoint (cv V j) ∧
      P.vtx (((a + j) % P.n + 1) % P.n) = intPoint (cv V (j + 1)) :=
  ⟨hC j (by omega), by rw [Polygon.chain_succ]; exact hC (j + 1) hj⟩

/-- Chain edge `j` is the segment between consecutive chain vertices. -/
theorem ChainAt.edge_eq (hC : ChainAt P V a) {j : ℕ} (hj : j + 1 < V.length) :
    P.edge ((a + j) % P.n) = ArtGallery.segment (intPoint (cv V j)) (intPoint (cv V (j + 1))) := by
  obtain ⟨e1, e2⟩ := hC.edge_vtx hj
  rw [Polygon.edge, e1, e2]

/-- Chain vertices lie in the region. -/
theorem ChainAt.vtx_mem_filled (hC : ChainAt P V a) (hP : P.Simple) {j : ℕ} (hj : j < V.length) :
    intPoint (cv V j) ∈ P.filled := by
  rw [← hC j hj]
  exact Or.inl ⟨_, Nat.mod_lt _ (n_pos_of_simple hP), Geometry.left_mem_segment _ _⟩

/-! ### Sees: elementary facts -/

theorem sees_of_convex {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled) {p q : Point}
    (hp : p ∈ A) (hq : q ∈ A) : P.Sees p q :=
  (Geometry.segment_subset_of_convex hA hp hq).trans hAP

/-- Concatenation of sight lines through a point of the segment. -/
theorem sees_of_mem_segment {p q x : Point} (hx : x ∈ ArtGallery.segment p q)
    (hpx : P.Sees p x) (hxq : P.Sees x q) : P.Sees p q := by
  intro y hy
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hy
  by_cases hsτ : s ≤ τ
  · apply hpx
    rcases eq_or_lt_of_le hτ0 with hτ | hτ
    · subst hτ
      have : s = 0 := by linarith
      subst this
      exact Geometry.mem_segment_iff_lerp.2 ⟨0, le_rfl, zero_le_one, by
        simp [lerp]⟩
    · refine Geometry.mem_segment_iff_lerp.2 ⟨s / τ, div_nonneg hs0 hτ.le, (div_le_one hτ).2 hsτ, ?_⟩
      ext <;> simp only [lerp] <;> field_simp <;> ring
  · apply hxq
    push Not at hsτ
    have hτ1' : τ < 1 := lt_of_lt_of_le hsτ hs1
    refine Geometry.mem_segment_iff_lerp.2 ⟨(s - τ) / (1 - τ), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    have h1 : (1 - τ) ≠ 0 := by linarith
    ext <;> simp only [lerp] <;> field_simp <;> ring

/-- Visibility through two convex subsets of the region meeting on the segment. -/
theorem sees_of_two_convex {A B : Set Point} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAP : A ⊆ P.filled) (hBP : B ⊆ P.filled) {p q x : Point} (hp : p ∈ A) (hq : q ∈ B)
    (hxA : x ∈ A) (hxB : x ∈ B) (hx : x ∈ ArtGallery.segment p q) : P.Sees p q :=
  sees_of_mem_segment hx (sees_of_convex hA hAP hp hxA) (sees_of_convex hB hBP hxB hq)

/-! ### Crossing certificates on chain edges -/

/-- A crossing certificate on chain edge `j`. -/
def chainCross (V : List IPt) (j : ℕ) (P₁ Q₁ : List IPt) : Bool :=
  Nat.blt (j + 1) V.length && crossB (cv V j) (cv V (j + 1)) P₁ Q₁

/-- **Crossing a chain edge**: no point of `conv P₁` sees a point of `conv Q₁`. -/
theorem not_sees_of_chainCross (hP : P.Simple) (hC : ChainAt P V a) {j : ℕ} {P₁ Q₁ : List IPt}
    (h : chainCross V j P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁), ¬ P.Sees p q := by
  simp only [chainCross, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hj, h⟩ := h
  obtain ⟨e1, e2⟩ := hC.edge_vtx hj
  intro p hp q hq
  obtain ⟨h1, h2⟩ := crossB_sound h p hp q hq
  exact Polygon.not_sees_of_proper_cross hP (Nat.mod_lt _ (n_pos_of_simple hP))
    (by rw [e1, e2]; exact h1) (by rw [e1, e2]; exact h2)

/-- Half-crossing data: `P₁` and `Q₁` strictly on opposite sides of the line `a b`, and `a`
strictly to the right of every line `p q` (`p ∈ P₁`, `q ∈ Q₁`). -/
def halfB (a b : IPt) (P₁ Q₁ : List IPt) : Bool :=
  ((P₁.all fun p => ipos (idet a b p)) && (Q₁.all fun q => ineg (idet a b q)) ||
    (P₁.all fun p => ineg (idet a b p)) && (Q₁.all fun q => ipos (idet a b q))) &&
  (P₁.all fun p => Q₁.all fun q => ineg (idet p q a))

/-- The relation `det p q c < 0` is convex in `p` and in `q`. -/
theorem convex_det_neg_left (q c : Point) : Convex ℝ {p | det p q c < 0} := by
  have e : {p | det p q c < 0} = {p | det q c p < 0} := by
    ext p; simp only [mem_ofPred_eq, Geometry.det_cyclic p q c]
  rw [e]; exact convex_det_neg q c

theorem convex_det_neg_right (p c : Point) : Convex ℝ {q | det p q c < 0} := by
  have e : {q | det p q c < 0} = {q | det c p q < 0} := by
    ext q; simp only [mem_ofPred_eq, Geometry.det_cyclic_right p q c]
  rw [e]; exact convex_det_neg c p

theorem convex_det_nonneg_left (q c : Point) : Convex ℝ {p | 0 ≤ det p q c} := by
  have e : {p | 0 ≤ det p q c} = {p | 0 ≤ det q c p} := by
    ext p; simp only [mem_ofPred_eq, Geometry.det_cyclic p q c]
  rw [e]; exact convex_det_nonneg q c

theorem convex_det_nonneg_right (p c : Point) : Convex ℝ {q | 0 ≤ det p q c} := by
  have e : {q | 0 ≤ det p q c} = {q | 0 ≤ det c p q} := by
    ext q; simp only [mem_ofPred_eq, Geometry.det_cyclic_right p q c]
  rw [e]; exact convex_det_nonneg c p

/-- Strict opposite sides of a line, checked on the vertices, hold on the hulls. -/
theorem sides_sound {a b : IPt} {P₁ Q₁ : List IPt}
    (h : ((P₁.all fun p => ipos (idet a b p)) && (Q₁.all fun q => ineg (idet a b q)) ||
      (P₁.all fun p => ineg (idet a b p)) && (Q₁.all fun q => ipos (idet a b q))) = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      det (intPoint a) (intPoint b) p * det (intPoint a) (intPoint b) q < 0 := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, ipos_iff, ineg_iff] at h
  intro p hp q hq
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := det_pos_on_hull (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := hx; rw [det_intPoint]; exact_mod_cast h1 z hz) p hp
    have e2 := det_neg_on_hull (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := hx; rw [det_intPoint]; exact_mod_cast h2 z hz) q hq
    exact mul_neg_of_pos_of_neg e1 e2
  · have e1 := det_neg_on_hull (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := hx; rw [det_intPoint]; exact_mod_cast h1 z hz) p hp
    have e2 := det_pos_on_hull (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := hx; rw [det_intPoint]; exact_mod_cast h2 z hz) q hq
    exact mul_neg_of_neg_of_pos e1 e2

/-- **Soundness of `halfB`**: for all `p ∈ conv P₁`, `q ∈ conv Q₁` with `det p q b > 0` the
segment `p q` properly crosses the segment `a b`. -/
theorem halfB_sound {a b : IPt} {P₁ Q₁ : List IPt} (h : halfB a b P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁), 0 < det p q (intPoint b) →
      det (intPoint a) (intPoint b) p * det (intPoint a) (intPoint b) q < 0 ∧
        det p q (intPoint a) * det p q (intPoint b) < 0 := by
  simp only [halfB, Bool.and_eq_true] at h
  obtain ⟨hs, hpair⟩ := h
  simp only [List.all_eq_true, ineg_iff] at hpair
  intro p hp q hq hb
  refine ⟨sides_sound hs p hp q hq, ?_⟩
  have := forall_hull_hull (R := fun p q => det p q (intPoint a) < 0)
    (fun q => convex_det_neg_left q _) (fun p => convex_det_neg_right p _) (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [det_intPoint]; exact_mod_cast hpair z hz w hw) p hp q hq
  exact mul_neg_of_neg_of_pos this hb

/-- A half-crossing certificate on chain edge `j`; `rev = false`: the free (shadow) endpoint is
`V[j+1]`, `rev = true`: it is `V[j]`. -/
def chainHalf (V : List IPt) (j : ℕ) (rev : Bool) (P₁ Q₁ : List IPt) : Bool :=
  Nat.blt (j + 1) V.length &&
    (if rev then halfB (cv V (j + 1)) (cv V j) P₁ Q₁ else halfB (cv V j) (cv V (j + 1)) P₁ Q₁)

/-- The shadow corner of a half-crossing certificate. -/
def halfCorner (V : List IPt) (j : ℕ) (rev : Bool) : IPt := if rev then cv V j else cv V (j + 1)

/-- **Half crossing of a chain edge**: no `p ∈ conv P₁` sees a `q ∈ conv Q₁` with
`det p q b > 0`, `b` the shadow corner. -/
theorem not_sees_of_chainHalf (hP : P.Simple) (hC : ChainAt P V a) {j : ℕ} {rev : Bool}
    {P₁ Q₁ : List IPt} (h : chainHalf V j rev P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      0 < det p q (intPoint (halfCorner V j rev)) → ¬ P.Sees p q := by
  simp only [chainHalf, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hj, h⟩ := h
  obtain ⟨e1, e2⟩ := hC.edge_vtx hj
  have hi := Nat.mod_lt (a + j) (n_pos_of_simple hP)
  intro p hp q hq hb
  cases rev
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := halfB_sound h p hp q hq hb
    exact Polygon.not_sees_of_proper_cross hP hi (by rw [e1, e2]; exact h1)
      (by rw [e1, e2]; exact h2)
  · simp only [↓reduceIte] at h
    obtain ⟨h1, h2⟩ := halfB_sound h p hp q hq hb
    have h1' : det (intPoint (cv V j)) (intPoint (cv V (j + 1))) p *
        det (intPoint (cv V j)) (intPoint (cv V (j + 1))) q < 0 := by
      rw [Geometry.det_swap12 _ _ p, Geometry.det_swap12 _ _ q] at h1; linarith
    have h2' : det p q (intPoint (cv V j)) * det p q (intPoint (cv V (j + 1))) < 0 := by linarith
    exact Polygon.not_sees_of_proper_cross hP hi (by rw [e1, e2]; exact h1')
      (by rw [e1, e2]; exact h2')

/-! ### Gates -/

/-- Two segments meet: `p`, `q` strictly on opposite sides of the line `g₀ g₁`, and
`det p q g₀ ≤ 0 ≤ det p q g₁`. -/
theorem exists_mem_segment_inter {p q g₀ g₁ : Point}
    (hs : det g₀ g₁ p * det g₀ g₁ q < 0) (h₀ : det p q g₀ ≤ 0) (h₁ : 0 ≤ det p q g₁) :
    ∃ m ∈ ArtGallery.segment g₀ g₁, m ∈ ArtGallery.segment p q := by
  have hst : det g₀ g₁ p - det g₀ g₁ q ≠ 0 := by
    intro h
    have : det g₀ g₁ p = det g₀ g₁ q := by linarith
    rw [this] at hs; nlinarith [sq_nonneg (det g₀ g₁ q)]
  have hcross : (g₁.1 - g₀.1) * (q.2 - p.2) - (g₁.2 - g₀.2) * (q.1 - p.1) ≠ 0 := by
    intro h; apply hst; unfold det; linear_combination -h
  -- the gate endpoints are not both on the line `p q`
  have hd : det p q g₀ < det p q g₁ := by
    rcases lt_or_eq_of_le (le_trans h₀ h₁) with h | h
    · exact h
    · exfalso
      have e0 : det p q g₀ = 0 := le_antisymm h₀ (h ▸ h₁)
      have e1 : det p q g₁ = 0 := by rw [← h, e0]
      apply hcross
      unfold det at e0 e1
      linear_combination e0 - e1
  set d₀ := det p q g₀ with hd₀
  set d₁ := det p q g₁ with hd₁
  set μ := d₀ / (d₀ - d₁) with hμ
  have hden : d₀ - d₁ < 0 := by linarith
  have hμ0 : 0 ≤ μ := div_nonneg_of_nonpos h₀ hden.le
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one_of_neg hden]; linarith
  refine ⟨lerp g₀ g₁ μ, Geometry.lerp_mem_segment _ _ hμ0 hμ1, ?_⟩
  set s := det g₀ g₁ p with hs'
  set t := det g₀ g₁ q with ht'
  set lam := s / (s - t) with hlam'
  have hlam : 0 ≤ lam ∧ lam ≤ 1 := by
    rcases mul_neg_iff.1 hs with ⟨hs0, ht0⟩ | ⟨hs0, ht0⟩
    · have h' : 0 < s - t := by linarith
      exact ⟨div_nonneg hs0.le h'.le, by rw [hlam', div_le_one h']; linarith⟩
    · have h' : s - t < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos hs0.le h'.le, by rw [hlam', div_le_one_of_neg h']; linarith⟩
  refine Geometry.mem_segment_iff_lerp.2 ⟨lam, hlam.1, hlam.2, ?_⟩
  have hden' : d₀ - d₁ ≠ 0 := hden.ne
  have hm1 : det p q (lerp g₀ g₁ μ) = 0 := by
    rw [Geometry.det_lerp, ← hd₀, ← hd₁, hμ]
    field_simp
    ring
  have hm2 : det g₀ g₁ (lerp g₀ g₁ μ) = 0 := Geometry.det_lerp_self _ _ _
  have hl1 : det p q (lerp p q lam) = 0 := Geometry.det_lerp_self _ _ _
  have hl2 : det g₀ g₁ (lerp p q lam) = 0 := by
    rw [Geometry.det_lerp, ← hs', ← ht', hlam']
    field_simp
    ring
  have key : ∀ m m' : Point, det p q m = 0 → det g₀ g₁ m = 0 → det p q m' = 0 →
      det g₀ g₁ m' = 0 → m = m' := by
    intro m m' a1 a2 a3 a4
    unfold det at a1 a2 a3 a4
    have ea : (q.1 - p.1) * (m.2 - m'.2) - (q.2 - p.2) * (m.1 - m'.1) = 0 := by
      linear_combination a1 - a3
    have eb : (g₁.1 - g₀.1) * (m.2 - m'.2) - (g₁.2 - g₀.2) * (m.1 - m'.1) = 0 := by
      linear_combination a2 - a4
    have hw1 : (m.1 - m'.1) * ((g₁.1 - g₀.1) * (q.2 - p.2) - (g₁.2 - g₀.2) * (q.1 - p.1)) = 0 := by
      linear_combination (q.1 - p.1) * eb - (g₁.1 - g₀.1) * ea
    have hw2 : (m.2 - m'.2) * ((g₁.1 - g₀.1) * (q.2 - p.2) - (g₁.2 - g₀.2) * (q.1 - p.1)) = 0 := by
      linear_combination (q.2 - p.2) * eb - (g₁.2 - g₀.2) * ea
    have h1 := (mul_eq_zero.1 hw1).resolve_right hcross
    have h2 := (mul_eq_zero.1 hw2).resolve_right hcross
    ext <;> linarith
  exact key _ _ hm1 hm2 hl1 hl2

/-- Gate data: `P₁`, `Q₁` strictly on opposite sides of the line `g₀ g₁` and
`0 ≤ det p q g₁` for all vertex pairs. -/
def gateB (g₀ g₁ : IPt) (P₁ Q₁ : List IPt) : Bool :=
  ((P₁.all fun p => ipos (idet g₀ g₁ p)) && (Q₁.all fun q => ineg (idet g₀ g₁ q)) ||
    (P₁.all fun p => ineg (idet g₀ g₁ p)) && (Q₁.all fun q => ipos (idet g₀ g₁ q))) &&
  (P₁.all fun p => Q₁.all fun q => inonneg (idet p q g₁))

/-- **Soundness of `gateB`**: every segment from `conv P₁` to `conv Q₁` with `det p q g₀ ≤ 0`
meets the gate `[g₀, g₁]`. -/
theorem gateB_sound {g₀ g₁ : IPt} {P₁ Q₁ : List IPt} (h : gateB g₀ g₁ P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      det p q (intPoint g₀) ≤ 0 →
        ∃ m ∈ ArtGallery.segment (intPoint g₀) (intPoint g₁), m ∈ ArtGallery.segment p q := by
  simp only [gateB, Bool.and_eq_true] at h
  obtain ⟨hs, hpair⟩ := h
  simp only [List.all_eq_true, inonneg_iff] at hpair
  intro p hp q hq h0
  have h1 := forall_hull_hull (R := fun p q => 0 ≤ det p q (intPoint g₁))
    (fun q => convex_det_nonneg_left q _) (fun p => convex_det_nonneg_right p _) (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [det_intPoint]; exact_mod_cast hpair z hz w hw) p hp q hq
  exact exists_mem_segment_inter (sides_sound hs p hp q hq) h0 h1

/-- **Visibility through a gate.**  `A ⊇ conv P₁`, `B ⊇ conv Q₁` convex subsets of the region,
both containing the gate `[g₀, g₁]`: every `p ∈ conv P₁` sees every `q ∈ conv Q₁` with
`det p q g₀ ≤ 0`. -/
theorem sees_of_gate {A B : Set Point} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAP : A ⊆ P.filled) (hBP : B ⊆ P.filled) {g₀ g₁ : IPt} {P₁ Q₁ : List IPt}
    (hPA : convexHull ℝ (intSet P₁) ⊆ A) (hQB : convexHull ℝ (intSet Q₁) ⊆ B)
    (hgA : ArtGallery.segment (intPoint g₀) (intPoint g₁) ⊆ A)
    (hgB : ArtGallery.segment (intPoint g₀) (intPoint g₁) ⊆ B) (h : gateB g₀ g₁ P₁ Q₁ = true) :
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁),
      det p q (intPoint g₀) ≤ 0 → P.Sees p q := by
  intro p hp q hq h0
  obtain ⟨m, hm, hmpq⟩ := gateB_sound h p hp q hq h0
  exact sees_of_two_convex hA hB hAP hBP (hPA hp) (hQB hq) (hgA hm) (hgB hm) hmpq

/-! ### Convex pieces -/

/-- List inclusion gives inclusion of the hulls. -/
theorem hull_subset_hull_of_all {P₁ Q : List IPt} (h : (P₁.all fun x => Q.elem x) = true) :
    convexHull ℝ (intSet P₁) ⊆ convexHull ℝ (intSet Q) := by
  refine convexHull_mono ?_
  rintro _ ⟨z, hz, rfl⟩
  simp only [List.all_eq_true, List.elem_iff] at h
  exact intPoint_mem_intSet (h z hz)

/-- A segment between two points of the list lies in the hull. -/
theorem segment_subset_hull {Q : List IPt} {a b : IPt} (ha : Q.elem a = true)
    (hb : Q.elem b = true) :
    ArtGallery.segment (intPoint a) (intPoint b) ⊆ convexHull ℝ (intSet Q) := by
  simp only [List.elem_iff] at ha hb
  exact Geometry.segment_subset_convexHull (intPoint_mem_intSet ha) (intPoint_mem_intSet hb)


/-- Every interior point of `conv Q` is in the region `R`: every box constraint is non-constant
and `≥ 0` on `Q`, and every zone has a non-constant constraint `≤ 0` on `Q`. -/
def Region.check (R : Region) (Q : List IPt) : Bool :=
  (R.box.all fun c => validHP Q c) &&
    R.zones.all fun W => W.any fun c => validHP Q (negHP c)

theorem Region.interior_hull_subset {R : Region} {Q : List IPt} (h : R.check Q = true) :
    interior (convexHull ℝ (intSet Q)) ⊆ {x | R.Mem x} := by
  simp only [Region.check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨hb, hz⟩ := h
  intro x hx
  refine ⟨fun c hc => ?_, fun W hW => ?_⟩
  · obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP (hb c hc)
    exact pos_of_mem_interior_HP hnd hT hx
  · obtain ⟨c, hc, hv⟩ := hz W hW
    obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP hv
    refine ⟨c, hc, ?_⟩
    have := pos_of_mem_interior_HP hnd hT hx
    rw [negHP_val] at this; linarith

/-- A nonnegative integer combination `Σ λᵢ cᵢ` of half-plane functions. -/
def combHP : List HP → List ℕ → HP
  | c :: W, l :: L =>
    ((l : ℤ) * c.1 + (combHP W L).1, (l : ℤ) * c.2.1 + (combHP W L).2.1,
      (l : ℤ) * c.2.2 + (combHP W L).2.2)
  | _, _ => (0, 0, 0)

theorem combHP_nonneg : ∀ (W : List HP) (L : List ℕ) (x : Point), (∀ c ∈ W, 0 ≤ c.val x) →
    0 ≤ (combHP W L).val x
  | [], _, x, _ => by simp [combHP, Irrational.HP.val]
  | _ :: _, [], x, _ => by simp [combHP, Irrational.HP.val]
  | c :: W, l :: L, x, h => by
    have ih := combHP_nonneg W L x (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have hc := h c List.mem_cons_self
    simp only [combHP, Irrational.HP.val] at ih hc ⊢
    push_cast
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith [mul_nonneg this hc]

/-- Region check with Farkas certificates: for zone `k` the combination
`Σ λᵢ cᵢ + μ` (`cert.getD k`) is `≤ 0` on `Q` (so every interior point of the piece violates some
constraint of the zone). -/
def Region.checkF (R : Region) (Q : List IPt) (cert : List (List ℕ × ℕ)) : Bool :=
  (R.box.all fun c => validHP Q c) &&
    (List.range R.zones.length).all fun k =>
      validHP Q (negHP (let h := combHP (R.zones.getD k []) (cert.getD k ([], 0)).1
        (h.1, h.2.1, h.2.2 + ((cert.getD k ([], 0)).2 : ℤ))))

theorem Region.interior_hull_subset_F {R : Region} {Q : List IPt} {cert : List (List ℕ × ℕ)}
    (h : R.checkF Q cert = true) : interior (convexHull ℝ (intSet Q)) ⊆ {x | R.Mem x} := by
  simp only [Region.checkF, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hb, hz⟩ := h
  intro x hx
  refine ⟨fun c hc => ?_, fun W hW => ?_⟩
  · obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP (hb c hc)
    exact pos_of_mem_interior_HP hnd hT hx
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hW
    have hv := hz k hk
    obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP hv
    have hpos := pos_of_mem_interior_HP hnd hT hx
    rw [negHP_val] at hpos
    by_contra hall
    push Not at hall
    have h0 := combHP_nonneg (R.zones.getD k []) (cert.getD k ([], 0)).1 x (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hall)
    simp only [Irrational.HP.val] at h0 hpos
    push_cast at h0 hpos
    have : (0 : ℝ) ≤ ((cert.getD k ([], 0)).2 : ℝ) := Nat.cast_nonneg _
    linarith

/-- Piece certificate: `seps.getD j` separates chain edge `j` from the piece `Q` (it is a valid
separator of `Q` and `≤ 0` at both endpoints of the edge). -/
def pieceB (V Q : List IPt) (seps : List HP) : Bool :=
  (List.range (V.length - 1)).all fun j =>
    validHP Q (seps.getD j (0, 0, 0)) && inonpos (ivalHP (seps.getD j (0, 0, 0)) (cv V j)) &&
      inonpos (ivalHP (seps.getD j (0, 0, 0)) (cv V (j + 1)))

theorem disjoint_of_pieceB {Q : List IPt} {seps : List HP} (h : pieceB V Q seps = true) {j : ℕ}
    (hj : j + 1 < V.length) :
    Disjoint (interior (convexHull ℝ (intSet Q)))
      (ArtGallery.segment (intPoint (cv V j)) (intPoint (cv V (j + 1)))) := by
  simp only [pieceB, List.all_eq_true, List.mem_range, Bool.and_eq_true, inonpos_iff] at h
  obtain ⟨⟨hv, ha⟩, hb⟩ := h j (by omega)
  obtain ⟨hnd, hT⟩ := nonneg_hull_of_validHP hv
  exact disjoint_interior_segment_HP hnd hT (by rw [val_intPoint_HP]; exact_mod_cast ha)
    (by rw [val_intPoint_HP]; exact_mod_cast hb)

/-- **Convex piece in the region.** -/
theorem hull_subset_filled_of_piece {R : Region} (hP : P.Simple) (hC : ChainAt P V a)
    (hS : SepAt P V a R) {Q : List IPt} {seps : List HP} (hpc : pieceB V Q seps = true)
    (hR : R.check Q = true) {z : Point} (hz : z ∈ interior (convexHull ℝ (intSet Q)))
    (hzP : z ∈ P.filled) : convexHull ℝ (intSet Q) ⊆ P.filled := by
  have hedge : ∀ i < P.n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i) := by
    intro i hi
    by_cases hc : ∃ j, j + 1 < V.length ∧ (a + j) % P.n = i
    · obtain ⟨j, hj, rfl⟩ := hc
      rw [hC.edge_eq hj]
      exact disjoint_of_pieceB hpc hj
    · push Not at hc
      rw [Set.disjoint_left]
      intro x hx hxe
      exact hS i hi (fun j hj h => hc j hj h) x hxe (Region.interior_hull_subset hR hx)
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _) hedge hz hzP
  rwa [(isClosed_hull_intSet Q).closure_eq] at this

/-- **Convex piece in the region** (Farkas form of the region check). -/
theorem hull_subset_filled_of_pieceF {R : Region} (hP : P.Simple) (hC : ChainAt P V a)
    (hS : SepAt P V a R) {Q : List IPt} {seps : List HP} {cert : List (List ℕ × ℕ)}
    (hpc : pieceB V Q seps = true) (hR : R.checkF Q cert = true) {z : Point}
    (hz : z ∈ interior (convexHull ℝ (intSet Q))) (hzP : z ∈ P.filled) :
    convexHull ℝ (intSet Q) ⊆ P.filled := by
  have hedge : ∀ i < P.n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i) := by
    intro i hi
    by_cases hc : ∃ j, j + 1 < V.length ∧ (a + j) % P.n = i
    · obtain ⟨j, hj, rfl⟩ := hc
      rw [hC.edge_eq hj]
      exact disjoint_of_pieceB hpc hj
    · push Not at hc
      rw [Set.disjoint_left]
      intro x hx hxe
      exact hS i hi (fun j hj h => hc j hj h) x hxe (Region.interior_hull_subset_F hR hx)
  have := Polygon.closure_subset_filled_of_convex hP (convex_convexHull ℝ _) hedge hz hzP
  rwa [(isClosed_hull_intSet Q).closure_eq] at this

/-- An interior point of a piece next to a chain edge: if the chain edge `V[j] → V[j+1]` and a
point `c` strictly to its left are vertices of the piece, some interior point of the piece lies
in the region. -/
theorem seed_of_chain_edge (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ}
    (hj : j + 1 < V.length) {Q : List IPt} {c : IPt} (ha : cv V j ∈ Q) (hb : cv V (j + 1) ∈ Q)
    (hc : c ∈ Q) (habc : 0 < idet (cv V j) (cv V (j + 1)) c) :
    ∃ z ∈ interior (convexHull ℝ (intSet Q)), z ∈ P.filled := by
  obtain ⟨e1, e2⟩ := hC.edge_vtx hj
  have hi := Nat.mod_lt (a + j) (n_pos_of_simple hP)
  obtain ⟨δ₀, hδ₀, hδ⟩ := hL _ hi (1 / 2) (by norm_num) (by norm_num)
  rw [e1, e2] at hδ
  set A := intPoint (cv V j)
  set B := intPoint (cv V (j + 1))
  set C := intPoint c
  have hK : 0 < det A B C := by rw [det_intPoint]; exact_mod_cast habc
  set nrm := leftNormal A B
  set M := A + (1 / 2 : ℝ) • (B - A)
  -- the three determinants along `M + δ • nrm`
  have dAB : ∀ δ : ℝ, det A B (M + δ • nrm) = δ * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
    intro δ
    simp only [M, nrm, leftNormal, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  set k₁ := (C.1 - B.1) * nrm.2 - (C.2 - B.2) * nrm.1
  set k₂ := (A.1 - C.1) * nrm.2 - (A.2 - C.2) * nrm.1
  have dBC : ∀ δ : ℝ, det B C (M + δ • nrm) = det A B C / 2 + δ * k₁ := by
    intro δ
    simp only [M, nrm, k₁, leftNormal, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have dCA : ∀ δ : ℝ, det C A (M + δ • nrm) = det A B C / 2 + δ * k₂ := by
    intro δ
    simp only [M, nrm, k₂, leftNormal, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have hAB : A ≠ B := by
    intro h; rw [h] at hK; simp [det] at hK
  have hlen : 0 < (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 := by
    rcases (ne_or_eq A.1 B.1) with h | h
    · have : 0 < (B.1 - A.1) ^ 2 := by
        have : B.1 - A.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
        positivity
      nlinarith [sq_nonneg (B.2 - A.2)]
    · have h2 : A.2 ≠ B.2 := fun h2 => hAB (Prod.ext h h2)
      have : 0 < (B.2 - A.2) ^ 2 := by
        have : B.2 - A.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
        positivity
      nlinarith [sq_nonneg (B.1 - A.1)]
  set K := det A B C
  set δ := min (δ₀ / 2) (K / (4 * (|k₁| + |k₂| + 1)))
  have hden : 0 < 4 * (|k₁| + |k₂| + 1) := by positivity
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos hK hden)
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδK : δ * (4 * (|k₁| + |k₂| + 1)) ≤ K := by
    have := min_le_right (δ₀ / 2) (K / (4 * (|k₁| + |k₂| + 1)))
    rwa [le_div_iff₀ hden] at this
  have hk1 : -(δ * k₁) ≤ δ * |k₁| := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs k₁) hδpos.le
  have hk2 : -(δ * k₂) ≤ δ * |k₂| := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs k₂) hδpos.le
  refine ⟨M + δ • nrm, ?_, (hδ δ hδpos hδlt).1.1⟩
  refine mem_interior_hull_of_dets (intPoint_mem_intSet ha) (intPoint_mem_intSet hb)
    (intPoint_mem_intSet hc) hK ?_ ?_ ?_
  · rw [dAB]; positivity
  · rw [dBC]; nlinarith [abs_nonneg k₁, abs_nonneg k₂]
  · rw [dCA]; nlinarith [abs_nonneg k₁, abs_nonneg k₂]

/-! ### Affine functions on hulls, quadrilaterals, bilinear interpolation -/

/-- A half-plane function positive at all points of `Q` is positive on the hull. -/
theorem pos_on_hull {Q : List IPt} {g : HP} (h : (Q.all fun q => ipos (ivalHP g q)) = true) :
    ∀ x ∈ convexHull ℝ (intSet Q), 0 < g.val x := by
  simp only [List.all_eq_true, ipos_iff] at h
  have hconv : Convex ℝ {x : Point | 0 < g.val x} := by
    have e : {x : Point | 0 < g.val x} = Irrational.hpo [g] := by
      ext x; simp [Irrational.hpo]
    rw [e]; exact Irrational.convex_hpo _
  intro x hx
  exact convexHull_min (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [mem_ofPred_eq, val_intPoint_HP]; exact_mod_cast h z hz) hconv hx

/-- A half-plane function vanishing at all points of `Q` vanishes on the hull. -/
theorem zero_on_hull {Q : List IPt} {g : HP} (h : (Q.all fun q => ivalHP g q == 0) = true) :
    ∀ x ∈ convexHull ℝ (intSet Q), g.val x = 0 := by
  simp only [List.all_eq_true, beq_iff_eq] at h
  have hconv : Convex ℝ {x : Point | g.val x = 0} := by
    intro u hu v hv s t hs ht hst
    simp only [mem_ofPred_eq, Irrational.HP.val, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hu hv ⊢
    have : s = 1 - t := by linarith
    subst this
    linear_combination (1 - t) * hu + t * hv
  intro x hx
  exact convexHull_min (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [mem_ofPred_eq, val_intPoint_HP]; exact_mod_cast h z hz) hconv hx

/-- Membership in the hull of a convex quadrilateral `A B C D` (counter-clockwise) from the four
edge conditions. -/
theorem mem_hull_quad {Q : List IPt} {A B C D : IPt} (hA : A ∈ Q) (hB : B ∈ Q) (hC : C ∈ Q)
    (hD : D ∈ Q) (hABC : 0 < idet A B C) (hACD : 0 < idet A C D) {z : Point}
    (h₁ : 0 ≤ det (intPoint A) (intPoint B) z) (h₂ : 0 ≤ det (intPoint B) (intPoint C) z)
    (h₃ : 0 ≤ det (intPoint C) (intPoint D) z) (h₄ : 0 ≤ det (intPoint D) (intPoint A) z) :
    z ∈ convexHull ℝ (intSet Q) := by
  have kABC : 0 < det (intPoint A) (intPoint B) (intPoint C) := by
    rw [det_intPoint]; exact_mod_cast hABC
  have kACD : 0 < det (intPoint A) (intPoint C) (intPoint D) := by
    rw [det_intPoint]; exact_mod_cast hACD
  have sub3 : ∀ {a b c : IPt}, a ∈ Q → b ∈ Q → c ∈ Q →
      convexHull ℝ ({intPoint a, intPoint b, intPoint c} : Set Point) ⊆ convexHull ℝ (intSet Q) := by
    intro a b c ha hb hc
    refine convexHull_mono ?_
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [intPoint_mem_intSet ha, intPoint_mem_intSet hb, intPoint_mem_intSet hc]
  by_cases hz : 0 ≤ det (intPoint A) (intPoint C) z
  · refine sub3 hA hC hD ((Geometry.mem_triangle_iff_bary kACD.ne').2 ⟨?_, ?_, ?_⟩)
    · unfold Geometry.bary₁; rw [← Geometry.det_cyclic]; exact div_nonneg h₃ kACD.le
    · unfold Geometry.bary₂; rw [← Geometry.det_cyclic_right]; exact div_nonneg h₄ kACD.le
    · unfold Geometry.bary₃; exact div_nonneg hz kACD.le
  · push Not at hz
    refine sub3 hA hB hC ((Geometry.mem_triangle_iff_bary kABC.ne').2 ⟨?_, ?_, ?_⟩)
    · unfold Geometry.bary₁; rw [← Geometry.det_cyclic]; exact div_nonneg h₂ kABC.le
    · unfold Geometry.bary₂; rw [← Geometry.det_cyclic_right]
      refine div_nonneg ?_ kABC.le
      rw [Geometry.det_swap12]; linarith
    · unfold Geometry.bary₃; exact div_nonneg h₁ kABC.le

/-- Points of the segment between the two points of a two-element list are in its hull. -/
theorem mem_hull_pair {A B : IPt} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Geometry.lerp (intPoint A) (intPoint B) t ∈ convexHull ℝ (intSet [A, B]) := by
  refine Geometry.segment_subset_convexHull (s := intSet [A, B]) (intPoint_mem_intSet (by simp))
    (intPoint_mem_intSet (by simp)) (Geometry.lerp_mem_segment _ _ h0 h1)

/-- **Bilinear interpolation on `[1/2, 2]²`**: a function satisfying the bilinear interpolation
identity is nonnegative on the square if it is nonnegative at the four corners. -/
theorem bilin_nonneg (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, 9 / 4 * f x y = (2 - x) * (2 - y) * f (1 / 2) (1 / 2) +
      (x - 1 / 2) * (2 - y) * f 2 (1 / 2) + (2 - x) * (y - 1 / 2) * f (1 / 2) 2 +
      (x - 1 / 2) * (y - 1 / 2) * f 2 2)
    (h00 : 0 ≤ f (1 / 2) (1 / 2)) (h10 : 0 ≤ f 2 (1 / 2)) (h01 : 0 ≤ f (1 / 2) 2)
    (h11 : 0 ≤ f 2 2) {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    0 ≤ f x y := by
  have := hf x y
  have a1 : 0 ≤ (2 - x) * (2 - y) := mul_nonneg (by linarith) (by linarith)
  have a2 : 0 ≤ (x - 1 / 2) * (2 - y) := mul_nonneg (by linarith) (by linarith)
  have a3 : 0 ≤ (2 - x) * (y - 1 / 2) := mul_nonneg (by linarith) (by linarith)
  have a4 : 0 ≤ (x - 1 / 2) * (y - 1 / 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg a1 h00, mul_nonneg a2 h10, mul_nonneg a3 h01, mul_nonneg a4 h11]

/-- Strict version of `bilin_nonneg`. -/
theorem bilin_pos (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, 9 / 4 * f x y = (2 - x) * (2 - y) * f (1 / 2) (1 / 2) +
      (x - 1 / 2) * (2 - y) * f 2 (1 / 2) + (2 - x) * (y - 1 / 2) * f (1 / 2) 2 +
      (x - 1 / 2) * (y - 1 / 2) * f 2 2)
    (h00 : 0 < f (1 / 2) (1 / 2)) (h10 : 0 < f 2 (1 / 2)) (h01 : 0 < f (1 / 2) 2)
    (h11 : 0 < f 2 2) {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2) :
    0 < f x y := by
  set m := min (min (f (1 / 2) (1 / 2)) (f 2 (1 / 2))) (min (f (1 / 2) 2) (f 2 2))
  have hm : 0 < m := lt_min (lt_min h00 h10) (lt_min h01 h11)
  have g : ∀ x y, 9 / 4 * (f x y - m) = (2 - x) * (2 - y) * (f (1 / 2) (1 / 2) - m) +
      (x - 1 / 2) * (2 - y) * (f 2 (1 / 2) - m) + (2 - x) * (y - 1 / 2) * (f (1 / 2) 2 - m) +
      (x - 1 / 2) * (y - 1 / 2) * (f 2 2 - m) := by
    intro x y; have := hf x y; linear_combination this
  have := bilin_nonneg (fun x y => f x y - m) g
    (by have := min_le_left (min (f (1 / 2) (1 / 2)) (f 2 (1 / 2))) (min (f (1 / 2) 2) (f 2 2))
        have := min_le_left (f (1 / 2) (1 / 2)) (f 2 (1 / 2)); linarith)
    (by have := min_le_left (min (f (1 / 2) (1 / 2)) (f 2 (1 / 2))) (min (f (1 / 2) 2) (f 2 2))
        have := min_le_right (f (1 / 2) (1 / 2)) (f 2 (1 / 2)); linarith)
    (by have := min_le_right (min (f (1 / 2) (1 / 2)) (f 2 (1 / 2))) (min (f (1 / 2) 2) (f 2 2))
        have := min_le_left (f (1 / 2) 2) (f 2 2); linarith)
    (by have := min_le_right (min (f (1 / 2) (1 / 2)) (f 2 (1 / 2))) (min (f (1 / 2) 2) (f 2 2))
        have := min_le_right (f (1 / 2) 2) (f 2 2); linarith) hx0 hx1 hy0 hy1
  linarith

/-! ### Cones at chain vertices -/

/-- The predecessor of chain vertex `j ≥ 1`. -/
theorem ChainAt.prev_vtx (hC : ChainAt P V a) (hP : P.Simple) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < V.length) :
    P.vtx (((a + j) % P.n + P.n - 1) % P.n) = intPoint (cv V (j - 1)) := by
  have := Polygon.chain_prev (n_pos_of_simple hP) a hj1
  unfold Jordan.prevIdx at this
  rw [this]; exact hC (j - 1) (by omega)

/-- **Vertex cone lemma at a convex chain vertex.** -/
theorem chain_cone (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < V.length)
    (hconv : 0 < idet (cv V (j - 1)) (cv V j) (cv V (j + 1))) {x : Point}
    (h : P.Sees (intPoint (cv V j)) x) :
    0 ≤ det (intPoint (cv V (j - 1))) (intPoint (cv V j)) x ∧
      0 ≤ det (intPoint (cv V j)) (intPoint (cv V (j + 1))) x := by
  refine Polygon.sees_subset_cone hP hL (Nat.mod_lt (a + j) (n_pos_of_simple hP))
    (hC.prev_vtx hP hj1 (by omega)) (hC j (by omega)) (hC.edge_vtx hj).2 ?_ h
  rw [det_intPoint]; exact_mod_cast hconv

/-- All points of `S` lie strictly outside one of the two closed half-planes of the cone at chain
vertex `j`. -/
def outConeB (V : List IPt) (j : ℕ) (S : List IPt) : Bool :=
  (S.all fun p => ineg (idet (cv V (j - 1)) (cv V j) p)) ||
    (S.all fun p => ineg (idet (cv V j) (cv V (j + 1)) p))

/-- **Outside the cone**: the convex vertex `j` of the chain sees no point of `conv S`. -/
theorem not_sees_of_outCone (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < V.length)
    (hconv : 0 < idet (cv V (j - 1)) (cv V j) (cv V (j + 1))) {S : List IPt}
    (h : outConeB V j S = true) :
    ∀ x ∈ convexHull ℝ (intSet S), ¬ P.Sees (intPoint (cv V j)) x := by
  intro x hx hs
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC hj1 hj hconv hs
  simp only [outConeB, Bool.or_eq_true, List.all_eq_true, ineg_iff] at h
  rcases h with h | h
  · have := det_neg_on_hull (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast h z hz) x hx
    linarith
  · have := det_neg_on_hull (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy; rw [det_intPoint]; exact_mod_cast h z hz) x hx
    linarith

/-- **A convex chain vertex on the segment.**  If the convex chain vertex `v = V[j]` lies on the
segment `p q` and `q` is strictly outside one of the two half-planes of its cone, `p` does not
see `q` (the sub-segment `v q` would be seen from `v`). -/
theorem not_sees_of_vertex_on_segment {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple)
    (hL : P.InteriorLeft) (hC : ChainAt P V a) {j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 < V.length)
    (hconv : 0 < idet (cv V (j - 1)) (cv V j) (cv V (j + 1))) {p q : Point}
    (hv : intPoint (cv V j) ∈ ArtGallery.segment p q)
    (hq : det (intPoint (cv V (j - 1))) (intPoint (cv V j)) q < 0 ∨
      det (intPoint (cv V j)) (intPoint (cv V (j + 1))) q < 0) : ¬ P.Sees p q := by
  intro hs
  have hsub : P.Sees (intPoint (cv V j)) q := fun y hy => hs
    (Geometry.segment_subset_of_convex (Geometry.segment_convex p q) hv
      (Geometry.right_mem_segment p q) hy)
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC hj1 hj hconv hsub
  rcases hq with h | h <;> linarith

/-- A point on a horizontal segment between the two ends. -/
theorem mem_segment_horiz {p q v : Point} {c : ℝ} (h1 : p.2 = c) (h2 : q.2 = c) (h3 : v.2 = c)
    (hpv : p.1 ≤ v.1) (hvq : v.1 ≤ q.1) : v ∈ ArtGallery.segment p q := by
  rcases eq_or_lt_of_le (le_trans hpv hvq) with h | h
  · have e1 : p.1 = v.1 := le_antisymm hpv (h ▸ hvq)
    refine Geometry.mem_segment_iff_lerp.2 ⟨0, le_rfl, zero_le_one, ?_⟩
    ext <;> simp only [Geometry.lerp] <;> linarith
  · refine Geometry.mem_segment_iff_lerp.2 ⟨(v.1 - p.1) / (q.1 - p.1),
      div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith), ?_⟩
    have hne : q.1 - p.1 ≠ 0 := by linarith
    ext
    · simp only [Geometry.lerp]; rw [div_mul_cancel₀ _ hne]; ring
    · simp only [Geometry.lerp]; rw [h1, h2, h3]; ring

/-- Nonnegativity of a half-plane function on a hull, from the points. -/
theorem nonneg_on_hull {Q : List IPt} {g : HP} (h : (Q.all fun q => inonneg (ivalHP g q)) = true) :
    ∀ x ∈ convexHull ℝ (intSet Q), 0 ≤ g.val x := by
  simp only [List.all_eq_true, inonneg_iff] at h
  have hconv : Convex ℝ {x : Point | 0 ≤ g.val x} := by
    have e : {x : Point | 0 ≤ g.val x} = Irrational.hp [g] := by
      ext x; simp [Irrational.hp]
    rw [e]; exact Irrational.convex_hp _
  intro x hx
  exact convexHull_min (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [mem_ofPred_eq, val_intPoint_HP]; exact_mod_cast h z hz) hconv hx

/-- Horizontal collinearity data: all points of `L`, `v` and `w` on the line `y = c`, and `v`
between `L` and `w`. -/
def horizBetweenB (L : List IPt) (v w : IPt) (c : ℤ) : Bool :=
  (L.all fun q => q.2 == c) && (v.2 == c) && (w.2 == c) &&
    ((L.all fun q => ile q.1 v.1) && ile v.1 w.1 || (L.all fun q => ile v.1 q.1) && ile w.1 v.1)

theorem vertex_on_segment_horiz {L : List IPt} {v w : IPt} {c : ℤ}
    (h : horizBetweenB L v w c = true) :
    ∀ x ∈ convexHull ℝ (intSet L), intPoint v ∈ ArtGallery.segment x (intPoint w) := by
  simp only [horizBetweenB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq,
    ile_iff] at h
  obtain ⟨⟨⟨hy, hv⟩, hw⟩, hord⟩ := h
  intro x hx
  have hxy : x.2 = c := by
    have := zero_on_hull (Q := L) (g := (0, 1, -c)) (by
      simp only [List.all_eq_true, beq_iff_eq]
      intro q hq; simp only [ivalHP]; rw [hy q hq]; ring) x hx
    simp only [Irrational.HP.val] at this; push_cast at this; linarith
  rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hb := nonneg_on_hull (Q := L) (g := (-1, 0, v.1)) (by
      simp only [List.all_eq_true, inonneg_iff]
      intro q hq; simp only [ivalHP]; have := h1 q hq; linarith) x hx
    simp only [Irrational.HP.val] at hb; push_cast at hb
    exact mem_segment_horiz (c := c) hxy (by simp [hw]) (by simp [hv]) (by simp; linarith)
      (by simp; exact_mod_cast h2)
  · have hb := nonneg_on_hull (Q := L) (g := (1, 0, -v.1)) (by
      simp only [List.all_eq_true, inonneg_iff]
      intro q hq; simp only [ivalHP]; have := h1 q hq; linarith) x hx
    simp only [Irrational.HP.val] at hb; push_cast at hb
    rw [Geometry.segment_comm]
    exact mem_segment_horiz (c := c) (by simp [hw]) hxy (by simp [hv]) (by simp; exact_mod_cast h2)
      (by simp; linarith)

/-- A point of a horizontal segment `[A, B]` of integer points lies in the hull of `[A, B]`. -/
theorem mem_segment_horiz_hull {A B : IPt} (hb : A.2 = B.2) (hab : (A.1 : ℝ) < B.1) {x : Point}
    (h2 : x.2 = A.2) (h0 : (A.1 : ℝ) ≤ x.1) (h1 : x.1 ≤ B.1) :
    x ∈ convexHull ℝ (intSet [A, B]) := by
  have e : x = Geometry.lerp (intPoint A) (intPoint B) ((x.1 - A.1) / (B.1 - A.1)) := by
    have hne : (B.1 : ℝ) - A.1 ≠ 0 := by linarith
    ext
    · simp only [Geometry.lerp, intPoint_fst]; rw [div_mul_cancel₀ _ hne]; ring
    · simp only [Geometry.lerp, intPoint_snd, h2, hb]; ring
  rw [e]
  exact mem_hull_pair (div_nonneg (by linarith) (by linarith))
    ((div_le_one (by linarith)).2 (by linarith))

/-! ### Pinning a guard segment by four half-planes; stationary guards -/

/-- Data for `spot_of_four`: `A B` horizontal on `y = c`; the line `L1` horizontal on `y = c`
heading left (`det ≥ 0` means `y ≤ c`), `L2` horizontal heading right (`y ≥ c`), `L3` through
`A` with `B` strictly on its left, `L4` through `B` with `A` strictly on its left. -/
def spotB (L1 L2 L3 L4 : IPt × IPt) (A B : IPt) : Bool :=
  (A.2 == B.2) && ilt A.1 B.1 && (L1.1.2 == A.2) && (L1.2.2 == A.2) && ilt L1.2.1 L1.1.1 &&
    (L2.1.2 == A.2) && (L2.2.2 == A.2) && ilt L2.1.1 L2.2.1 &&
    (idet L3.1 L3.2 A == 0) && ipos (idet L3.1 L3.2 B) &&
    (idet L4.1 L4.2 B == 0) && ipos (idet L4.1 L4.2 A)

/-- **A guard segment pinned by four half-planes** (W1 from four witness cones). -/
theorem spot_of_four {L1 L2 L3 L4 : IPt × IPt} {A B : IPt} (h : spotB L1 L2 L3 L4 A B = true)
    {x : Point} (h1 : 0 ≤ det (intPoint L1.1) (intPoint L1.2) x)
    (h2 : 0 ≤ det (intPoint L2.1) (intPoint L2.2) x) (h3 : 0 ≤ det (intPoint L3.1) (intPoint L3.2) x)
    (h4 : 0 ≤ det (intPoint L4.1) (intPoint L4.2) x) : x ∈ convexHull ℝ (intSet [A, B]) := by
  simp only [spotB, Bool.and_eq_true, beq_iff_eq, ilt_iff, ipos_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAB, hAB1⟩, e1⟩, e2⟩, o1⟩, e3⟩, e4⟩, o2⟩, z3⟩, p3⟩, z4⟩, p4⟩ := h
  have hAB1' : (A.1 : ℝ) < B.1 := by exact_mod_cast hAB1
  simp only [det, intPoint_fst, intPoint_snd] at h1 h2 h3 h4
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  have o1' : (L1.2.1 : ℝ) < L1.1.1 := by exact_mod_cast o1
  have o2' : (L2.1.1 : ℝ) < L2.2.1 := by exact_mod_cast o2
  have hy : x.2 = A.2 := by
    have a1 : x.2 - A.2 ≤ 0 := by nlinarith
    have a2 : 0 ≤ x.2 - A.2 := by nlinarith
    linarith
  have z3' := congrArg (fun t : ℤ => (t : ℝ)) z3
  have p3' : (0 : ℝ) < (idet L3.1 L3.2 B : ℝ) := by exact_mod_cast p3
  have z4' := congrArg (fun t : ℤ => (t : ℝ)) z4
  have p4' : (0 : ℝ) < (idet L4.1 L4.2 A : ℝ) := by exact_mod_cast p4
  simp only [idet] at z3' p3' z4' p4'
  push_cast at z3' p3' z4' p4'
  rw [hy] at h3 h4
  rw [← hAB] at p3' z4'
  have k3 : 0 < -((L3.2.2 : ℝ) - L3.1.2) := by nlinarith
  have k4 : 0 < (L4.2.2 : ℝ) - L4.1.2 := by nlinarith
  have hx1 : (A.1 : ℝ) ≤ x.1 := by nlinarith
  have hx2 : x.1 ≤ (B.1 : ℝ) := by nlinarith
  refine mem_segment_horiz_hull hAB hAB1' hy hx1 hx2

/-- Sign data of the stationary-guard lemma (`Polygon.sg_unique_of_vertices`) for the chain
vertex `jp` (the guard) and the slot tips `ja`, `jb`. -/
def sgB (V : List IPt) (jp ja jb : ℕ) : Bool :=
  Nat.ble 1 jp && Nat.blt (jp + 1) V.length && Nat.ble 1 ja && Nat.blt (ja + 1) V.length &&
    Nat.ble 1 jb && Nat.blt (jb + 1) V.length &&
    (let u := cv V (jp - 1); let p := cv V jp; let w := cv V (jp + 1)
     let qa := cv V ja; let ua := cv V (ja - 1); let wa := cv V (ja + 1)
     let qb := cv V jb; let ub := cv V (jb - 1); let wb := cv V (jb + 1)
     ipos (idet ua qa wa) && ipos (idet ub qb wb) && ipos (idet p w qa) && ipos (idet p w qb) &&
       ipos (idet u p qa) && ipos (idet u p qb) && ipos (idet p qa qb) &&
       inonneg (idet qa p ua) && inonneg (idet qa p wa) && inonneg (idet p qb ub) &&
       inonneg (idet p qb wb) && ineg (idet qa w ua) && ineg (idet qa w wa) &&
       ipos (idet qb u ub) && ipos (idet qb u wb))

/-- **Stationary guard pinned by its two slots** (W1 for a stationary guard of the chain). -/
theorem chain_sg_unique {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P V a) {jp ja jb : ℕ} (h : sgB V jp ja jb = true) {x : Point}
    (ha : P.Sees x (intPoint (cv V ja))) (hb : P.Sees x (intPoint (cv V jb))) :
    x = intPoint (cv V jp) := by
  simp only [sgB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, ipos_iff, inonneg_iff, ineg_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hp1, hp2⟩, ha1⟩, ha2⟩, hb1⟩, hb2⟩, hs⟩ := h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩ := hs
  have hn := n_pos_of_simple hP
  have d : ∀ {u v w : IPt}, 0 < idet u v w → 0 < det (intPoint u) (intPoint v) (intPoint w) := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have d' : ∀ {u v w : IPt}, 0 ≤ idet u v w → 0 ≤ det (intPoint u) (intPoint v) (intPoint w) := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have dn : ∀ {u v w : IPt}, idet u v w < 0 → det (intPoint u) (intPoint v) (intPoint w) < 0 := by
    intro u v w h; rw [det_intPoint]; exact_mod_cast h
  have e0 := hC.edge_vtx (j := jp - 1) (by omega)
  rw [show jp - 1 + 1 = jp by omega] at e0
  have e1 := hC.edge_vtx (j := jp) (by omega)
  exact Polygon.sg_unique_of_vertices hP hL (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
    (Nat.mod_lt _ hn) e0.1 e0.2 e1.1 e1.2 (hC.prev_vtx hP ha1 (by omega)) (hC ja (by omega))
    (hC.edge_vtx (by omega)).2 (d c1) (hC.prev_vtx hP hb1 (by omega)) (hC jb (by omega))
    (hC.edge_vtx (by omega)).2 (d c2) (d c3) (d c4) (d c5) (d c6) (d c7) (d' c8) (d' c9) (d' c10)
    (d' c11) (dn c12) (dn c13) (d c14) (d c15) ha hb

/-- Convexity data for the cones at the witness vertices `js`. -/
def conesB (V : List IPt) (js : List ℕ) : Bool :=
  js.all fun j => Nat.ble 1 j && Nat.blt (j + 1) V.length &&
    ipos (idet (cv V (j - 1)) (cv V j) (cv V (j + 1)))

/-- **Witness cones** for a list of convex chain vertices. -/
theorem chain_cone_of_list {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple)
    (hL : P.InteriorLeft) (hC : ChainAt P V a) {js : List ℕ} (h : conesB V js = true) {j : ℕ}
    (hj : j ∈ js) {x : Point} (hs : P.Sees x (intPoint (cv V j))) :
    0 ≤ det (intPoint (cv V (j - 1))) (intPoint (cv V j)) x ∧
      0 ≤ det (intPoint (cv V j)) (intPoint (cv V (j + 1))) x := by
  simp only [conesB, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, ipos_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j hj
  exact chain_cone hP hL hC h1 h2 h3 (Polygon.sees_comm.1 hs)

/-! ### Visibility of a witness stopped by a vertical chain edge -/

/-- Ray data for `crossVertB`: the ray from `v` with direction `g − v` reaches the vertical line
`x = T.x` and hits it strictly beyond `B` (towards `T`) and at most at `T`. -/
def rayOKB (v g T B : IPt) : Bool :=
  let d1 := g.1 - v.1
  let d2 := g.2 - v.2
  let num := v.2 * d1 + (T.1 - v.1) * d2
  ipos ((T.1 - v.1) * d1) && ipos ((num - B.2 * d1) * (T.2 - B.2) * d1) &&
    inonneg ((T.2 * d1 - num) * (T.2 - B.2) * d1)

/-- The cone of the convex chain vertex `jw` meets the vertical line of the chain edge
`je → je + 1` only in points of that edge other than `V[je + 1]`, and `V[je]` is a convex chain
vertex; the witness is strictly on the inner side of the edge. -/
def crossVertB (V : List IPt) (jw je : ℕ) : Bool :=
  Nat.ble 1 jw && Nat.blt (jw + 1) V.length && Nat.ble 1 je && Nat.blt (je + 1) V.length &&
    ipos (idet (cv V (jw - 1)) (cv V jw) (cv V (jw + 1))) &&
    ipos (idet (cv V (je - 1)) (cv V je) (cv V (je + 1))) &&
    ((cv V je).1 == (cv V (je + 1)).1) && ipos (idet (cv V je) (cv V (je + 1)) (cv V jw)) &&
    rayOKB (cv V jw) (cv V (jw - 1)) (cv V je) (cv V (je + 1)) &&
    rayOKB (cv V jw) (cv V (jw + 1)) (cv V je) (cv V (je + 1))

theorem rayOKB_sound {v g T B : IPt} (h : rayOKB v g T B = true) :
    0 < ((T.1 : ℝ) - v.1) * ((g.1 : ℝ) - v.1) ∧
      0 < ((T.1 : ℝ) - v.1) * (((v.2 : ℝ) * (g.1 - v.1) + (T.1 - v.1) * (g.2 - v.2)) -
        B.2 * (g.1 - v.1)) * (T.2 - B.2) ∧
      0 ≤ ((T.1 : ℝ) - v.1) * ((T.2 : ℝ) * (g.1 - v.1) -
        ((v.2 : ℝ) * (g.1 - v.1) + (T.1 - v.1) * (g.2 - v.2))) * (T.2 - B.2) := by
  simp only [rayOKB, Bool.and_eq_true, ipos_iff, inonneg_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' : (0 : ℝ) < ((T.1 - v.1) * (g.1 - v.1) : ℤ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (((v.2 * (g.1 - v.1) + (T.1 - v.1) * (g.2 - v.2)) - B.2 * (g.1 - v.1)) *
      (T.2 - B.2) * (g.1 - v.1) : ℤ) := by exact_mod_cast h2
  have h3' : (0 : ℝ) ≤ ((T.2 * (g.1 - v.1) - (v.2 * (g.1 - v.1) + (T.1 - v.1) * (g.2 - v.2))) *
      (T.2 - B.2) * (g.1 - v.1) : ℤ) := by exact_mod_cast h3
  push_cast at h1' h2' h3'
  set d := (g.1 : ℝ) - v.1
  set e := (T.1 : ℝ) - v.1
  refine ⟨h1', ?_, ?_⟩
  · have : 0 < (e * d) * ((((v.2 : ℝ) * d + e * (g.2 - v.2)) - B.2 * d) * (T.2 - B.2) * d) :=
      mul_pos h1' h2'
    have hd2 : 0 < d ^ 2 := by
      have : d ≠ 0 := by intro h0; rw [h0] at h1'; simp at h1'
      positivity
    have : 0 < (e * ((((v.2 : ℝ) * d + e * (g.2 - v.2)) - B.2 * d)) * (T.2 - B.2)) * d ^ 2 := by
      nlinarith
    exact pos_of_mul_pos_left this hd2.le
  · have : 0 ≤ (e * d) * ((((T.2 : ℝ) * d - ((v.2 : ℝ) * d + e * (g.2 - v.2)))) * (T.2 - B.2) * d) :=
      mul_nonneg h1'.le h3'
    have hd2 : 0 < d ^ 2 := by
      have : d ≠ 0 := by intro h0; rw [h0] at h1'; simp at h1'
      positivity
    have : 0 ≤ (e * (((T.2 : ℝ) * d - ((v.2 : ℝ) * d + e * (g.2 - v.2)))) * (T.2 - B.2)) * d ^ 2 := by
      nlinarith
    exact nonneg_of_mul_nonneg_left this hd2

/-- **A witness stopped by a vertical edge.**  Every point seen from the chain vertex `V[jw]`
lies weakly on the inner side of the vertical chain edge `V[je] → V[je + 1]`. -/
theorem sees_side_of_crossVert {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple)
    (hL : P.InteriorLeft) (hC : ChainAt P V a) {jw je : ℕ} (h : crossVertB V jw je = true)
    {x : Point} (hs : P.Sees (intPoint (cv V jw)) x) :
    0 ≤ det (intPoint (cv V je)) (intPoint (cv V (je + 1))) x := by
  simp only [crossVertB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, ipos_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw1, hw2⟩, he1⟩, he2⟩, hcw⟩, hcT⟩, hvert⟩, hside⟩, hr1⟩, hr2⟩ := h
  set v := cv V jw
  set u := cv V (jw - 1)
  set w' := cv V (jw + 1)
  set T := cv V je
  set B := cv V (je + 1)
  obtain ⟨r1a, r1b, r1c⟩ := rayOKB_sound hr1
  obtain ⟨r2a, r2b, r2c⟩ := rayOKB_sound hr2
  by_contra hneg
  push Not at hneg
  have hcone := chain_cone hP hL hC hw1 hw2 hcw hs
  have hK : 0 < det (intPoint u) (intPoint v) (intPoint w') := by
    rw [det_intPoint]; exact_mod_cast hcw
  have hlv : 0 < det (intPoint T) (intPoint B) (intPoint v) := by
    rw [det_intPoint]; exact_mod_cast hside
  set lx := det (intPoint T) (intPoint B) x
  set lv := det (intPoint T) (intPoint B) (intPoint v)
  set t := lv / (lv - lx)
  have ht0 : 0 ≤ t := div_nonneg hlv.le (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  set m := Geometry.lerp (intPoint v) x t
  have hmseg : m ∈ ArtGallery.segment (intPoint v) x := Geometry.lerp_mem_segment _ _ ht0 ht1
  have hmcone := Polygon.segment_subset_cone hcone hmseg
  have hlm : det (intPoint T) (intPoint B) m = 0 := by
    simp only [m, Geometry.det_lerp]
    have : lv - lx ≠ 0 := by linarith
    simp only [t]; field_simp; ring
  have hTB : (T.1 : ℝ) = B.1 := by exact_mod_cast hvert
  -- the edge is not degenerate
  have hs0 : (T.2 : ℝ) - B.2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at r1b; exact lt_irrefl _ r1b
  have hm1 : m.1 = T.1 := by
    have := hlm
    simp only [det, intPoint_fst, intPoint_snd] at this
    rw [← hTB] at this
    have : (m.1 - T.1) * ((B.2 : ℝ) - T.2) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd (by linarith) hs0
  -- decomposition of `m` in the cone
  obtain ⟨dc1, dc2⟩ := cone_decomp_coord (intPoint u) (intPoint v) (intPoint w') m
  set A := det (intPoint u) (intPoint v) m
  set Bc := det (intPoint v) (intPoint w') m
  have hA : 0 ≤ A := hmcone.1
  have hB : 0 ≤ Bc := hmcone.2
  set K := det (intPoint u) (intPoint v) (intPoint w')
  simp only [intPoint_fst, intPoint_snd] at dc1 dc2 r1a r1b r1c r2a r2b r2c
  rw [hm1] at dc1
  set e := (T.1 : ℝ) - v.1
  set s := (T.2 : ℝ) - B.2
  -- the key identity
  have key : K * e * e * (m.2 - B.2) * s =
      A * (e * (((v.2 : ℝ) * (w'.1 - v.1) + e * (w'.2 - v.2)) - B.2 * (w'.1 - v.1)) * s) +
        Bc * (e * (((v.2 : ℝ) * (u.1 - v.1) + e * (u.2 - v.2)) - B.2 * (u.1 - v.1)) * s) := by
    have e1 : K * e = A * (w'.1 - v.1) + Bc * (u.1 - v.1) := by simp only [e]; linarith
    have e2 : K * (m.2 - v.2) = A * (w'.2 - v.2) + Bc * (u.2 - v.2) := dc2
    linear_combination (e * s * (v.2 - B.2)) * e1 + (e * e * s) * e2
  have key2 : K * e * e * (T.2 - m.2) * s =
      A * (e * ((T.2 : ℝ) * (w'.1 - v.1) - ((v.2 : ℝ) * (w'.1 - v.1) + e * (w'.2 - v.2))) * s) +
        Bc * (e * ((T.2 : ℝ) * (u.1 - v.1) - ((v.2 : ℝ) * (u.1 - v.1) + e * (u.2 - v.2))) * s) := by
    have e1 : K * e = A * (w'.1 - v.1) + Bc * (u.1 - v.1) := by simp only [e]; linarith
    have e2 : K * (m.2 - v.2) = A * (w'.2 - v.2) + Bc * (u.2 - v.2) := dc2
    linear_combination (e * s * (T.2 - v.2)) * e1 - (e * e * s) * e2
  have he : e ≠ 0 := by intro h0; rw [h0, zero_mul] at r1a; exact lt_irrefl _ r1a
  have hAB : 0 < A ∨ 0 < Bc := by
    by_contra hc
    push Not at hc
    have : A = 0 := le_antisymm hc.1 hA
    have : Bc = 0 := le_antisymm hc.2 hB
    have : K * e = 0 := by simp only [e]; rw [dc1]; simp [*]
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact he h0
  have hKee : 0 < K * e * e := by
    have : 0 < e * e := mul_self_pos.2 he
    rw [mul_assoc]; exact mul_pos hK this
  have hpos : 0 < (m.2 - B.2) * s := by
    have : 0 < K * e * e * (m.2 - B.2) * s := by
      rw [key]
      rcases hAB with h0 | h0
      · linarith [mul_pos h0 r2b, mul_nonneg hB r1b.le]
      · linarith [mul_pos h0 r1b, mul_nonneg hA r2b.le]
    have : 0 < (K * e * e) * ((m.2 - B.2) * s) := by linarith
    exact pos_of_mul_pos_right this hKee.le
  have hnn : 0 ≤ (T.2 - m.2) * s := by
    have : 0 ≤ K * e * e * (T.2 - m.2) * s := by
      rw [key2]; linarith [mul_nonneg hA r2c, mul_nonneg hB r1c]
    have : 0 ≤ (K * e * e) * ((T.2 - m.2) * s) := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hKee
  rcases eq_or_lt_of_le hnn with h0 | h0
  · -- `m = T`: the vertex `T` lies on the segment
    have hm2 : m.2 = T.2 := by
      rcases mul_eq_zero.1 h0.symm with h1 | h1
      · linarith
      · exact absurd h1 hs0
    have hmT : m = intPoint T := Prod.ext (by rw [hm1]; rfl) (by rw [hm2]; rfl)
    refine not_sees_of_vertex_on_segment hP hL hC he1 he2 hcT (p := intPoint v) (q := x)
      (by rw [← hmT]; exact hmseg) (Or.inr ?_) hs
    rw [show je + 1 = je + 1 from rfl]; exact hneg
  · -- `m` strictly inside the edge: proper crossing
    obtain ⟨e1, e2⟩ := hC.edge_vtx he2
    refine Polygon.not_sees_of_proper_cross hP (i := (a + je) % P.n)
      (Nat.mod_lt _ (n_pos_of_simple hP)) ?_ ?_ hs
    · rw [e1, e2]; exact mul_neg_of_pos_of_neg hlv hneg
    · rw [e1, e2]
      -- `det(v, x, ·)` vanishes at `m`
      have hz : det (intPoint v) x m = 0 := by
        simp only [m]; exact Geometry.det_lerp_self _ _ _
      have hxv : x.1 ≠ v.1 := by
        intro hx
        have : lx = lv := by
          simp only [lx, lv, det, intPoint_fst, intPoint_snd]; rw [hx, ← hTB]; ring
        linarith
      have d1 : det (intPoint v) x (intPoint T) = (T.2 - m.2) * (x.1 - v.1) := by
        have := hz; simp only [det, intPoint_fst, intPoint_snd] at this ⊢
        rw [← hm1]; linear_combination this
      have d2 : det (intPoint v) x (intPoint B) = (B.2 - m.2) * (x.1 - v.1) := by
        have := hz; simp only [det, intPoint_fst, intPoint_snd] at this ⊢
        rw [← hTB, ← hm1]; linear_combination this
      rw [d1, d2]
      have hsq : 0 < (x.1 - v.1) ^ 2 := by
        have : x.1 - v.1 ≠ 0 := sub_ne_zero.2 hxv
        positivity
      have : (T.2 - m.2) * (B.2 - m.2) < 0 := by
        have h3 : 0 < ((T.2 : ℝ) - m.2) * s * ((m.2 - B.2) * s) := mul_pos h0 hpos
        have h4 : 0 < s ^ 2 := by positivity
        have e5 : ((T.2 : ℝ) - m.2) * s * ((m.2 - B.2) * s) = -((T.2 - m.2) * (B.2 - m.2)) * s ^ 2 := by
          ring
        rw [e5] at h3
        have := pos_of_mul_pos_left h3 h4.le
        linarith
      have e6 : (T.2 - m.2) * (x.1 - v.1) * ((B.2 - m.2) * (x.1 - v.1)) =
          ((T.2 - m.2) * (B.2 - m.2)) * (x.1 - v.1) ^ 2 := by ring
      rw [e6]
      exact mul_neg_of_neg_of_pos this hsq

/-- The cone at the convex chain vertex `j` lies in the half-plane `g ≥ 0`: `g ≥ 0` at the apex
and `g` does not decrease along the two generators. -/
def coneHPB (V : List IPt) (j : ℕ) (g : HP) : Bool :=
  Nat.ble 1 j && Nat.blt (j + 1) V.length && ipos (idet (cv V (j - 1)) (cv V j) (cv V (j + 1))) &&
    inonneg (ivalHP g (cv V j)) &&
    inonneg (g.1 * ((cv V (j - 1)).1 - (cv V j).1) + g.2.1 * ((cv V (j - 1)).2 - (cv V j).2)) &&
    inonneg (g.1 * ((cv V (j + 1)).1 - (cv V j).1) + g.2.1 * ((cv V (j + 1)).2 - (cv V j).2))

/-- **The visibility set of a convex chain vertex lies in a half-plane containing its cone.** -/
theorem sees_hp_of_cone {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P V a) {j : ℕ} {g : HP} (h : coneHPB V j g = true) {x : Point}
    (hs : P.Sees (intPoint (cv V j)) x) : 0 ≤ g.val x := by
  simp only [coneHPB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, ipos_iff, inonneg_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  obtain ⟨c1, c2⟩ := chain_cone hP hL hC h1 h2 h3 hs
  obtain ⟨d1, d2⟩ := cone_decomp_coord (intPoint (cv V (j - 1))) (intPoint (cv V j))
    (intPoint (cv V (j + 1))) x
  have hK : 0 < det (intPoint (cv V (j - 1))) (intPoint (cv V j)) (intPoint (cv V (j + 1))) := by
    rw [det_intPoint]; exact_mod_cast h3
  set K := det (intPoint (cv V (j - 1))) (intPoint (cv V j)) (intPoint (cv V (j + 1)))
  set A := det (intPoint (cv V (j - 1))) (intPoint (cv V j)) x
  set B := det (intPoint (cv V j)) (intPoint (cv V (j + 1))) x
  have h4' : (0 : ℝ) ≤ (ivalHP g (cv V j) : ℝ) := by exact_mod_cast h4
  have h5' : (0 : ℝ) ≤ ((g.1 * ((cv V (j - 1)).1 - (cv V j).1) +
      g.2.1 * ((cv V (j - 1)).2 - (cv V j).2) : ℤ) : ℝ) := by exact_mod_cast h5
  have h6' : (0 : ℝ) ≤ ((g.1 * ((cv V (j + 1)).1 - (cv V j).1) +
      g.2.1 * ((cv V (j + 1)).2 - (cv V j).2) : ℤ) : ℝ) := by exact_mod_cast h6
  simp only [ivalHP] at h4'
  push_cast at h4' h5' h6'
  simp only [intPoint_fst, intPoint_snd] at d1 d2
  have key : K * (g.val x - ivalHP g (cv V j)) =
      A * ((g.1 : ℝ) * ((cv V (j + 1)).1 - (cv V j).1) + g.2.1 * ((cv V (j + 1)).2 - (cv V j).2)) +
        B * ((g.1 : ℝ) * ((cv V (j - 1)).1 - (cv V j).1) + g.2.1 * ((cv V (j - 1)).2 - (cv V j).2)) := by
    simp only [Irrational.HP.val, ivalHP]; push_cast
    linear_combination (g.1 : ℝ) * d1 + (g.2.1 : ℝ) * d2
  have h7 : 0 ≤ K * (g.val x - ivalHP g (cv V j)) := by
    rw [key]; exact add_nonneg (mul_nonneg c1 h6') (mul_nonneg c2 h5')
  have h8 : 0 ≤ g.val x - ivalHP g (cv V j) := nonneg_of_mul_nonneg_right h7 hK
  have h9 : ((ivalHP g (cv V j) : ℤ) : ℝ) = (g.1 : ℝ) * (cv V j).1 + g.2.1 * (cv V j).2 + g.2.2 := by
    simp only [ivalHP]; push_cast; ring
  linarith

/-! ### Template polygons (chain + stub) -/

theorem getD_mem' {L : List IPt} {j : ℕ} (hj : j < L.length) : L.getD j (0, 0) ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _

/-- The chain `V` is the beginning of the polygon with vertex list `V ++ W`. -/
theorem chainAt_append (V W : List IPt) : ChainAt (Polygon.mk ((V ++ W).map intPoint)) V 0 := by
  intro j hj
  have hn : (Polygon.mk ((V ++ W).map intPoint)).n = (V ++ W).length := n_map_intPoint _
  rw [vtx_map_intPoint, hn, zero_add, Nat.mod_eq_of_lt (by rw [List.length_append]; omega),
    getD_append_left' hj]

/-- Every edge of `V ++ W` from index `V.length − 1` on (the stub edges, including the closing
edge) lies outside `R`: both endpoints are weakly outside one box constraint, or weakly inside
all constraints of one zone. -/
def stubOutB (R : Region) (V W : List IPt) : Bool :=
  (List.range (W.length + 1)).all fun k =>
    let L := V ++ W
    let a := L.getD (V.length - 1 + k) (0, 0)
    let b := L.getD ((V.length - 1 + k + 1) % L.length) (0, 0)
    (R.box.any fun c => inonpos (ivalHP c a) && inonpos (ivalHP c b)) ||
      (R.zones.any fun Z => Z.all fun c => inonneg (ivalHP c a) && inonneg (ivalHP c b))

theorem not_mem_of_segment_out {R : Region} {a b : IPt}
    (h : ((R.box.any fun c => inonpos (ivalHP c a) && inonpos (ivalHP c b)) ||
      (R.zones.any fun Z => Z.all fun c => inonneg (ivalHP c a) && inonneg (ivalHP c b))) = true) :
    ∀ x ∈ ArtGallery.segment (intPoint a) (intPoint b), ¬ R.Mem x := by
  intro x hx hm
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  simp only [Bool.or_eq_true, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, inonpos_iff,
    inonneg_iff] at h
  rcases h with ⟨c, hc, ha, hb⟩ | ⟨Z, hZ, hall⟩
  · have := hm.1 c hc
    rw [Irrational.HP.val_lerp, val_intPoint_HP, val_intPoint_HP] at this
    have e1 : ((ivalHP c a : ℤ) : ℝ) ≤ 0 := by exact_mod_cast ha
    have e2 : ((ivalHP c b : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hb
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 e1), mul_nonneg ht0 (neg_nonneg.2 e2)]
  · obtain ⟨c, hc, hneg⟩ := hm.2 Z hZ
    obtain ⟨ha, hb⟩ := hall c hc
    rw [Irrational.HP.val_lerp, val_intPoint_HP, val_intPoint_HP] at hneg
    have e1 : (0 : ℝ) ≤ ((ivalHP c a : ℤ) : ℝ) := by exact_mod_cast ha
    have e2 : (0 : ℝ) ≤ ((ivalHP c b : ℤ) : ℝ) := by exact_mod_cast hb
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) e1, mul_nonneg ht0 e2]

/-- **The template polygon satisfies the separation hypothesis.** -/
theorem sepAt_append {R : Region} {V W : List IPt} (hV : 0 < V.length) (h : stubOutB R V W = true) :
    SepAt (Polygon.mk ((V ++ W).map intPoint)) V 0 R := by
  intro i hi hnc x hx
  have hn : (Polygon.mk ((V ++ W).map intPoint)).n = (V ++ W).length := n_map_intPoint _
  rw [hn, List.length_append] at hi
  have hge : V.length - 1 ≤ i := by
    by_contra hlt
    push Not at hlt
    exact hnc i (by omega) (by rw [hn, zero_add, Nat.mod_eq_of_lt (by rw [List.length_append]; omega)])
  simp only [stubOutB, List.all_eq_true, List.mem_range] at h
  have hk := h (i - (V.length - 1)) (by omega)
  have e : V.length - 1 + (i - (V.length - 1)) = i := by omega
  rw [e] at hk
  rw [Polygon.edge, vtx_map_intPoint, vtx_map_intPoint, hn] at hx
  exact not_mem_of_segment_out hk x hx

/-- Orientation from a lowest horizontal edge (integer data). -/
theorem interiorLeft_of_lowB {L : List IPt} (hP : (Polygon.mk (L.map intPoint)).Simple) {i : ℕ}
    (h : (Nat.blt (i + 1) L.length && (L.all fun v => ile (L.getD i (0, 0)).2 v.2) &&
      ((L.getD (i + 1) (0, 0)).2 == (L.getD i (0, 0)).2) &&
      ilt (L.getD i (0, 0)).1 (L.getD (i + 1) (0, 0)).1) = true) :
    (Polygon.mk (L.map intPoint)).InteriorLeft := by
  simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, ile_iff, beq_iff_eq, ilt_iff] at h
  obtain ⟨⟨⟨hi, hlow⟩, hy⟩, hx⟩ := h
  have hn : (Polygon.mk (L.map intPoint)).n = L.length := n_map_intPoint _
  have hs : ((i + 1) % (Polygon.mk (L.map intPoint)).n) = i + 1 := by
    rw [hn]; exact Nat.mod_eq_of_lt hi
  refine Polygon.interiorLeft_of_bottom_edge hP (i := i) (y₀ := ((L.getD i (0, 0)).2 : ℝ))
    (by rw [hn]; omega) (fun j hj => ?_) ?_ ?_ ?_
  · rw [vtx_map_intPoint, intPoint_snd]
    rw [hn] at hj
    exact_mod_cast hlow _ (getD_mem' hj)
  · rw [vtx_map_intPoint, intPoint_snd]
  · rw [hs, vtx_map_intPoint, intPoint_snd, hy]
  · rw [hs, vtx_map_intPoint, vtx_map_intPoint, intPoint_fst, intPoint_fst]; exact_mod_cast hx

/-! ### Rooms cut off by a chord between chain vertices -/

/-- The sub-polygon of the `m + 1` chain vertices `V[k], …, V[k + m]` (closed by the chord
`V[k + m] → V[k]`). -/
def subList (V : List IPt) (k m : ℕ) : List IPt := (V.drop k).take (m + 1)

theorem subList_getD {V : List IPt} {k m j : ℕ} (hj : j ≤ m) :
    (subList V k m).getD j (0, 0) = cv V (k + j) := by
  simp only [subList, cv, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ite_eq_left (by omega)]

theorem subList_length {V : List IPt} {k m : ℕ} (hkm : k + m < V.length) :
    (subList V k m).length = m + 1 := by
  simp only [subList, List.length_take, List.length_drop]; omega

/-- **Sub-chain rooms.** -/
theorem subList_isRoom {P : Polygon} {V : List IPt} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P V a) {k m : ℕ} (hkm : k + m < V.length)
    (hK : (Polygon.mk ((subList V k m).map intPoint)).Simple)
    (hKL : (Polygon.mk ((subList V k m).map intPoint)).InteriorLeft) :
    P.IsRoom (Polygon.mk ((subList V k m).map intPoint)).filled
      (ArtGallery.segment (intPoint (cv V (k + m))) (intPoint (cv V k))) := by
  have hKn : (Polygon.mk ((subList V k m).map intPoint)).n = m + 1 := by
    rw [n_map_intPoint, subList_length hkm]
  have hchain : ∀ j ≤ m, (Polygon.mk ((subList V k m).map intPoint)).vtx j =
      P.vtx ((a + k + j) % P.n) := by
    intro j hj
    rw [vtx_map_intPoint, subList_getD hj, Nat.add_assoc, hC (k + j) (by omega)]
  have h := Polygon.isRoom_of_chain hP hL hK hKL hKn hchain
  rwa [vtx_map_intPoint, vtx_map_intPoint, subList_getD le_rfl, subList_getD (Nat.zero_le _),
    Nat.add_zero] at h

/-- Orientation of a polygon from a supporting edge (integer data). -/
theorem interiorLeft_of_supportB {L : List IPt} (hP : (Polygon.mk (L.map intPoint)).Simple) {i : ℕ}
    (h : (Nat.blt i L.length && L.all fun v =>
      inonneg (idet (L.getD i (0, 0)) (L.getD ((i + 1) % L.length) (0, 0)) v)) = true) :
    (Polygon.mk (L.map intPoint)).InteriorLeft := by
  simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, inonneg_iff] at h
  have hn : (Polygon.mk (L.map intPoint)).n = L.length := n_map_intPoint _
  refine Polygon.interiorLeft_of_supporting_edge hP (i := i) (by rw [hn]; exact h.1) fun j hj => ?_
  rw [hn] at hj ⊢
  rw [vtx_map_intPoint, vtx_map_intPoint, vtx_map_intPoint, det_intPoint]
  exact_mod_cast h.2 _ (getD_mem' hj)

/-- **The region lies in every half-plane containing all vertices.** -/
theorem filled_subset_hp (L : List IPt) {c : HP} (hc : nondegHP c = true)
    (h : (L.all fun v => inonneg (ivalHP c v)) = true) :
    (Polygon.mk (L.map intPoint)).filled ⊆ {x | 0 ≤ c.val x} := by
  simp only [List.all_eq_true, inonneg_iff] at h
  set K := Polygon.mk (L.map intPoint)
  have hv : ∀ j < K.n, 0 ≤ c.val (K.vtx j) := by
    intro j hj
    rw [vtx_map_intPoint, val_intPoint_HP]
    rw [n_map_intPoint] at hj
    exact_mod_cast h _ (getD_mem' hj)
  have hbd : ∀ x ∈ K.boundary, 0 ≤ c.val x := by
    rintro x ⟨i, hi, hx⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    rw [Irrational.HP.val_lerp]
    have h1 := hv i hi
    have h2 := hv ((i + 1) % K.n) (Nat.mod_lt _ (by omega))
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) h1, mul_nonneg ht0 h2]
  intro x hx
  by_contra hneg
  simp only [mem_ofPred_eq, not_le] at hneg
  have hnd := nondegHP_iff.1 hc
  set d : Point := (-(c.1 : ℝ), -(c.2.1 : ℝ))
  have hN : 0 < (c.1 : ℝ) ^ 2 + (c.2.1 : ℝ) ^ 2 := by
    by_cases h1 : c.1 = 0
    · have h2 : c.2.1 ≠ 0 := fun h2 => hnd ⟨h1, h2⟩
      have : (0 : ℝ) < (c.2.1 : ℝ) ^ 2 := by
        have : (c.2.1 : ℝ) ≠ 0 := by exact_mod_cast h2
        positivity
      nlinarith [sq_nonneg (c.1 : ℝ)]
    · have : (0 : ℝ) < (c.1 : ℝ) ^ 2 := by
        have : (c.1 : ℝ) ≠ 0 := by exact_mod_cast h1
        positivity
      nlinarith [sq_nonneg (c.2.1 : ℝ)]
  have hd : d ≠ 0 := by
    intro h0
    have h1 : (c.1 : ℝ) = 0 := by
      have := congrArg Prod.fst h0; simp only [d, Prod.fst_zero] at this; linarith
    have h2 : (c.2.1 : ℝ) = 0 := by
      have := congrArg Prod.snd h0; simp only [d, Prod.snd_zero] at this; linarith
    rw [h1, h2] at hN; norm_num at hN
  have hray : Jordan.ray x d ⊆ K.boundaryᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hb
    have := hbd _ hb
    simp only [Irrational.HP.val, d, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at this
    simp only [Irrational.HP.val] at hneg
    have hs0 : (0 : ℝ) ≤ s := hs
    nlinarith [mul_nonneg hs0 hN.le]
  rcases hx with hx | hx
  · exact (hray (Jordan.mem_ray_self x d)) hx
  · exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray K hd hray hx

end ArtGallery.Sec5.Tmpl

end
