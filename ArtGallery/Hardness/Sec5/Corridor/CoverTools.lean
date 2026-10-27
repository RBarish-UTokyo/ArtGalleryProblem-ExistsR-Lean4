module

public import ArtGallery.Vis.API

/-!
# Section 5: corridors — generic tools for the coverage proof

Generic facts about a simple polygon `K` used to show that the canonical guards see the whole
corridor (docs/section5/08_proof_plan.md §9):

* **Affine constraints** (`Aff`): `ev f z = a z.x + b z.y + c`; `hpSet fs` is the closed convex set
  where all constraints of the list `fs` are nonnegative.
* **Convex containment by constraints** (`hpSet_subset_filled`): if every boundary point of `K`
  violates (weakly) some constraint, some point satisfies all constraints strictly, and one point
  of `hpSet fs` is an interior point of `K`, then `hpSet fs ⊆ K.filled`.  The anchor is the target
  point itself, so no point of the region has to be exhibited separately.
* **Rays** (`exists_boundary_on_ray`): every ray from an interior point meets the boundary.
* **Composition of sight segments** (`sees_of_segment_split`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-! ## Affine constraints -/

/-- An affine function `z ↦ a z.x + b z.y + c` on the plane. -/
structure Aff where
  /-- Coefficient of `z.x`. -/
  a : ℝ
  /-- Coefficient of `z.y`. -/
  b : ℝ
  /-- Constant term. -/
  c : ℝ

namespace Aff

/-- Evaluation of an affine function. -/
def ev (f : Aff) (z : Point) : ℝ := f.a * z.1 + f.b * z.2 + f.c

/-- The affine function `det p q ·` (positive strictly left of the directed line `p → q`). -/
def det (p q : Point) : Aff :=
  ⟨-(q.2 - p.2), q.1 - p.1, (q.2 - p.2) * p.1 - (q.1 - p.1) * p.2⟩

@[simp] theorem ev_det (p q z : Point) : (Aff.det p q).ev z = ArtGallery.det p q z := by
  simp only [ev, Aff.det, ArtGallery.det]; ring

/-- `ev` along a segment parameter. -/
theorem ev_lerp (f : Aff) (p q : Point) (t : ℝ) :
    f.ev (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) = f.ev p + t * (f.ev q - f.ev p) := by
  simp only [ev]; ring

theorem ev_comb (f : Aff) (p q : Point) (s : ℝ) :
    f.ev ((1 - s) • p + s • q) = (1 - s) * f.ev p + s * f.ev q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [ev, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring

theorem continuous_ev (f : Aff) : Continuous f.ev := by
  unfold ev; fun_prop

/-- An affine inequality valid at both ends of a segment holds on the segment. -/
theorem ev_le_of_segment (f : Aff) {p q z : Point} (hz : z ∈ ArtGallery.segment p q) {c : ℝ}
    (hp : f.ev p ≤ c) (hq : f.ev q ≤ c) : f.ev z ≤ c := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hz
  rw [ev_lerp]
  nlinarith [mul_le_mul_of_nonneg_left hq ht0, mul_le_mul_of_nonneg_left hp (sub_nonneg.2 ht1)]

/-- Same for lower bounds. -/
theorem ge_ev_of_segment (f : Aff) {p q z : Point} (hz : z ∈ ArtGallery.segment p q) {c : ℝ}
    (hp : c ≤ f.ev p) (hq : c ≤ f.ev q) : c ≤ f.ev z := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hz
  rw [ev_lerp]
  nlinarith [mul_le_mul_of_nonneg_left hq ht0, mul_le_mul_of_nonneg_left hp (sub_nonneg.2 ht1)]

end Aff

/-- The closed convex set where all constraints are nonnegative. -/
def hpSet (fs : List Aff) : Set Point := {z | ∀ f ∈ fs, 0 ≤ f.ev z}

/-- The open convex set where all constraints are positive. -/
def hpOpen (fs : List Aff) : Set Point := {z | ∀ f ∈ fs, 0 < f.ev z}

theorem convex_hpSet (fs : List Aff) : Convex ℝ (hpSet fs) := by
  intro x hx y hy a b ha hb hab f hf
  have e : a • x + b • y = (1 - b) • x + b • y := by rw [← hab]; congr 1; ring_nf
  rw [e, Aff.ev_comb, show 1 - b = a by linarith]
  have := hx f hf; have := hy f hf
  positivity

theorem convex_hpOpen (fs : List Aff) : Convex ℝ (hpOpen fs) := by
  intro x hx y hy a b ha hb hab f hf
  have e : a • x + b • y = (1 - b) • x + b • y := by rw [← hab]; congr 1; ring_nf
  rw [e, Aff.ev_comb, show 1 - b = a by linarith]
  have h1 := hx f hf; have h2 := hy f hf
  rcases ha.lt_or_eq with ha' | ha'
  · have := mul_pos ha' h1; nlinarith [mul_nonneg hb h2.le]
  · subst ha'; have hb1 : b = 1 := by linarith
    subst hb1; simpa using h2

theorem isOpen_hpOpen (fs : List Aff) : IsOpen (hpOpen fs) := by
  induction fs with
  | nil => simp [hpOpen]
  | cons f fs ih =>
    have e : hpOpen (f :: fs) = {z | 0 < f.ev z} ∩ hpOpen fs := by
      ext z; simp [hpOpen]
    rw [e]
    exact (isOpen_lt continuous_const f.continuous_ev).inter ih

theorem hpOpen_subset_hpSet (fs : List Aff) : hpOpen fs ⊆ hpSet fs :=
  fun _ hz f hf => (hz f hf).le

/-- The segment segment from a point of `hpSet` towards a strict point is strict except at its
start. -/
theorem comb_mem_hpOpen {fs : List Aff} {z c : Point} (hz : z ∈ hpSet fs) (hc : c ∈ hpOpen fs)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : (1 - s) • z + s • c ∈ hpOpen fs := by
  intro f hf
  rw [Aff.ev_comb]
  have := hz f hf; have := hc f hf
  have := mul_nonneg (sub_nonneg.2 hs1) (hz f hf)
  have := mul_pos hs0 (hc f hf)
  linarith

theorem tendsto_comb (z c : Point) :
    Filter.Tendsto (fun s : ℝ => (1 - s) • z + s • c) (nhdsWithin 0 (Ioi 0)) (nhds z) := by
  have hc : Continuous (fun s : ℝ => (1 - s) • z + s • c) := by fun_prop
  have := hc.tendsto 0
  simp only [sub_zero, one_smul, zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `hpSet` lies in the closure of `hpOpen` when the latter is nonempty. -/
theorem hpSet_subset_closure {fs : List Aff} {c : Point} (hc : c ∈ hpOpen fs) :
    hpSet fs ⊆ closure (hpOpen fs) := by
  intro z hz
  apply mem_closure_of_tendsto (tendsto_comb z c)
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact comb_mem_hpOpen hz hc hs.1 hs.2

/-! ## Convex containment by constraints -/

/-- **Convex containment by constraints.**  If every boundary point of the simple polygon `K`
violates weakly one of the constraints, some point satisfies all of them strictly and one point of
`hpSet fs` is an interior point of `K`, then `hpSet fs` lies in the region of `K`. -/
theorem hpSet_subset_filled {K : Polygon} (hK : K.Simple) {fs : List Aff}
    (hbd : ∀ w ∈ K.boundary, ∃ f ∈ fs, f.ev w ≤ 0) {c : Point} (hc : c ∈ hpOpen fs)
    {z : Point} (hz : z ∈ hpSet fs) (hzK : z ∈ K.filled) (hzb : z ∉ K.boundary) :
    hpSet fs ⊆ K.filled := by
  have hopen := Jordan.isOpen_filled_sdiff_boundary hK
  have hmem : z ∈ K.filled \ K.boundary := ⟨hzK, hzb⟩
  -- a strict point in the open region
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), (1 - s) • z + s • c ∈ K.filled \ K.boundary :=
    (tendsto_comb z c) (hopen.mem_nhds hmem)
  have hev2 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), s ∈ Ioc (0 : ℝ) 1 :=
    Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨s, hs1, hs2⟩ := (hev.and hev2).exists
  have hcs : (1 - s) • z + s • c ∈ hpOpen fs := comb_mem_hpOpen hz hc hs2.1 hs2.2
  have hedge : ∀ i < K.n, Disjoint (interior (hpOpen fs)) (K.edge i) := by
    intro i hi
    rw [(isOpen_hpOpen fs).interior_eq, Set.disjoint_left]
    intro w hw hwe
    obtain ⟨f, hf, hle⟩ := hbd w ⟨i, hi, hwe⟩
    exact absurd (hw f hf) (not_lt.2 hle)
  have hcl := Polygon.closure_subset_filled_of_convex hK (convex_hpOpen fs) hedge
    (by rw [(isOpen_hpOpen fs).interior_eq]; exact hcs) hs1.1
  exact (hpSet_subset_closure hc).trans hcl

/-- **Sight through a convex constraint set**: if the segment's ends lie in `hpSet fs ⊆ P.filled`,
the ends see each other. -/
theorem sees_of_hpSet {P : Polygon} {fs : List Aff} (hsub : hpSet fs ⊆ P.filled) {g z : Point}
    (hg : g ∈ hpSet fs) (hz : z ∈ hpSet fs) : P.Sees g z :=
  (Geometry.segment_subset_of_convex (convex_hpSet fs) hg hz).trans hsub

/-! ## Rays -/

/-- **Every ray from an interior point meets the boundary.** -/
theorem exists_boundary_on_ray {K : Polygon} {z d : Point} (hd : d ≠ 0) (hz : z ∈ K.filled)
    (hzb : z ∉ K.boundary) : ∃ s : ℝ, 0 < s ∧ z + s • d ∈ K.boundary := by
  by_contra hcon
  push Not at hcon
  have hray : Jordan.ray z d ⊆ K.boundaryᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hb
    rcases (mem_Ici.1 hs).lt_or_eq with hs' | hs'
    · exact hcon s hs' hb
    · subst hs'; simp at hb; exact hzb hb
  exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray K hd hray
    ((Jordan.mem_filled_iff_bounded K hzb).1 hz)

/-! ## Composition of sight segments -/

/-- A segment through an intermediate point is the union of the two sub-segments. -/
theorem segment_subset_union {g w z : Point} (hw : w ∈ ArtGallery.segment g z) :
    ArtGallery.segment g z ⊆ ArtGallery.segment g w ∪ ArtGallery.segment w z := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hw
  rintro _ ⟨s, hs0, hs1, rfl⟩
  by_cases hst : s ≤ t
  · left
    rcases ht0.lt_or_eq with ht | ht
    · refine ⟨s / t, div_nonneg hs0 ht.le, (div_le_one ht).2 hst, ?_⟩
      ext <;> simp only <;> field_simp <;> ring
    · subst ht
      have : s = 0 := le_antisymm hst hs0
      subst this
      exact ⟨0, le_rfl, zero_le_one, by ext <;> simp⟩
  · right
    push Not at hst
    have h1t : 0 < 1 - t := by linarith
    refine ⟨(s - t) / (1 - t), div_nonneg (by linarith) h1t.le,
      (div_le_one h1t).2 (by linarith), ?_⟩
    ext <;> simp only <;> field_simp <;> ring

/-- **Composition**: if `g` sees a point `w` of the segment `g z` and the rest of the segment lies
in the region, then `g` sees `z`. -/
theorem sees_of_segment_split {P : Polygon} {g w z : Point} (hw : w ∈ ArtGallery.segment g z)
    (h₁ : P.Sees g w) (h₂ : ArtGallery.segment w z ⊆ P.filled) : P.Sees g z := by
  intro x hx
  rcases segment_subset_union hw hx with h | h
  · exact h₁ h
  · exact h₂ h

/-- The point of the segment `g z` with a prescribed value of an affine function that changes
sign weakly between the ends. -/
theorem exists_mem_segment_ev_eq (f : Aff) {g z : Point} {c : ℝ} (hg : f.ev g ≤ c)
    (hz : c ≤ f.ev z) : ∃ w ∈ ArtGallery.segment g z, f.ev w = c := by
  by_cases h : f.ev z = f.ev g
  · exact ⟨z, Geometry.right_mem_segment g z, by linarith⟩
  · have hlt : f.ev g < f.ev z := lt_of_le_of_ne (hg.trans hz) (Ne.symm h)
    refine ⟨(g.1 + (c - f.ev g) / (f.ev z - f.ev g) * (z.1 - g.1),
      g.2 + (c - f.ev g) / (f.ev z - f.ev g) * (z.2 - g.2)),
      ⟨(c - f.ev g) / (f.ev z - f.ev g), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), rfl⟩, ?_⟩
    rw [Aff.ev_lerp]
    field_simp
    ring

end ArtGallery.Sec5.Corridor

end
