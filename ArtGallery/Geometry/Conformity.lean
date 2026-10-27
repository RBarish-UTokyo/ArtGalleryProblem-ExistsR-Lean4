module

public import ArtGallery.Geometry.Triangle
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The conformity criterion

Two nondegenerate triangles with disjoint interiors such that no vertex of either lies in
the other triangle except at a common vertex meet exactly in the convex hull of their
common vertices (`conforming_of_disjoint_interiors`), and the same for the specification's
`Polygon.triSet` (`triSet_inter_triSet_of_disjoint_interiors`).

Proof route.  The two open convex interiors are separated by a line `{φ = u}`
(`geometric_hahn_banach_open_open`); by density of the interior in the triangle, `φ ≤ u` on
the first closed triangle and `φ ≥ u` on the second, so the intersection lies on the line.
A triangle contained in a half-plane meets the boundary line in the convex hull of its
vertices on the line (`convexHull_inter_level_le`, a general fact about finite sets).
Finally the intersection of two convex hulls of finite subsets of a line, such that no point
of either set lies in the other hull unless it belongs to both, is the hull of the common
points (`convexHull_inter_convexHull_real` on `ℝ`, transported to the line by a linear
functional injective on it, `convexHull_inter_convexHull_of_injOn`).

Provenance: adapted from `Chazelle/Geometry/Conformity.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery

namespace Geometry

open Topology

@[expose] public section

/-! ### Linear functionals on the plane -/

/-- The linear functional `p ↦ α * p.1 + β * p.2`. -/
def lin (α β : ℝ) : Point →ₗ[ℝ] ℝ where
  toFun p := α * p.1 + β * p.2
  map_add' := by intro p q; simp only [add_fst, add_snd]; ring
  map_smul' := by intro t p; simp only [smul_fst, smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem lin_apply (α β : ℝ) (p : Point) : lin α β p = α * p.1 + β * p.2 := rfl

/-- Every linear functional on the plane is `lin α β` with `α = φ (1,0)`, `β = φ (0,1)`. -/
theorem linearMap_apply_eq (φ : Point →ₗ[ℝ] ℝ) (p : Point) :
    φ p = φ (1, 0) * p.1 + φ (0, 1) * p.2 := by
  have hp : p = p.1 • ((1, 0) : Point) + p.2 • ((0, 1) : Point) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- A level set `{φ = u}` of a linear functional is convex. -/
theorem convex_level (φ : Point →ₗ[ℝ] ℝ) (u : ℝ) : Convex ℝ {x : Point | φ x = u} :=
  (convex_singleton u).linear_preimage φ

/-- For a nonzero linear functional `φ` there is a linear functional injective on every level
set of `φ`. -/
theorem exists_injOn_level {φ : Point →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ∃ ψ : Point →ₗ[ℝ] ℝ, Set.InjOn ψ {x : Point | φ x = u} := by
  set α := φ (1, 0) with hα
  set β := φ (0, 1) with hβ
  have hne : ¬ (α = 0 ∧ β = 0) := by
    rintro ⟨h1, h2⟩
    apply hφ
    apply LinearMap.ext
    intro p
    rw [linearMap_apply_eq φ p, ← hα, ← hβ, h1, h2]
    simp
  have hαβ : α ^ 2 + β ^ 2 ≠ 0 := by
    intro h0
    apply hne
    constructor <;> nlinarith [sq_nonneg α, sq_nonneg β]
  refine ⟨lin (-β) α, ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  rw [linearMap_apply_eq φ x, ← hα, ← hβ] at hx
  rw [linearMap_apply_eq φ y, ← hα, ← hβ] at hy
  simp only [lin_apply] at hxy
  have e1 : α * x.1 + β * x.2 = α * y.1 + β * y.2 := by rw [hx, hy]
  have h1 : (α ^ 2 + β ^ 2) * (x.1 - y.1) = 0 := by linear_combination α * e1 - β * hxy
  have h2 : (α ^ 2 + β ^ 2) * (x.2 - y.2) = 0 := by linear_combination β * e1 + α * hxy
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h hαβ
  rcases mul_eq_zero.1 h2 with h' | h'
  · exact absurd h' hαβ
  apply point_ext <;> linarith

/-! ### Faces: a hull in a half-plane meets the boundary line in a face -/

/-- If a finite set `s` lies in the half-plane `{φ ≤ u}`, then the part of its convex hull
on the line `{φ = u}` is the convex hull of the points of `s` on that line. -/
theorem convexHull_inter_level_le (s : Finset Point) (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (hs : ∀ y ∈ s, φ y ≤ u) :
    convexHull ℝ (s : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ((s : Set Point) ∩ {x | φ x = u}) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxu⟩
    simp only [Set.mem_ofPred_eq] at hxu
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
    -- all weight sits on vertices with `φ y = u`
    have hsum : ∑ y ∈ s, w y * (u - φ y) = 0 := by
      have hφx : φ x = ∑ y ∈ s, w y * φ y := by
        rw [← hwx, map_sum]
        simp only [map_smul, smul_eq_mul]
      have : ∑ y ∈ s, w y * (u - φ y) = u * ∑ y ∈ s, w y - ∑ y ∈ s, w y * φ y := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _; ring
      rw [this, hw1, ← hφx, hxu]; ring
    have hzero : ∀ y ∈ s, w y * (u - φ y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y hy => mul_nonneg (hw0 y hy) (sub_nonneg.2 (hs y hy)))).1 hsum
    have hw' : ∀ y ∈ s, w y ≠ 0 → φ y = u := by
      intro y hy hwy
      rcases mul_eq_zero.1 (hzero y hy) with h | h
      · exact absurd h hwy
      · linarith
    have hcoe : ((s.filter (fun y => φ y = u) : Finset Point) : Set Point) =
        (s : Set Point) ∩ {x | φ x = u} := by
      rw [Finset.coe_filter]; rfl
    rw [← hcoe, Finset.mem_convexHull']
    refine ⟨w, fun y hy => hw0 y (Finset.mem_filter.1 hy).1, ?_, ?_⟩
    · rw [Finset.sum_filter_of_ne (fun y hy hne => hw' y hy hne), hw1]
    · rw [Finset.sum_filter_of_ne, hwx]
      intro y hy hne
      apply hw' y hy
      intro h0
      apply hne
      rw [h0, zero_smul]
  · apply Set.subset_inter
    · exact convexHull_mono Set.inter_subset_left
    · exact convexHull_min Set.inter_subset_right (convex_level φ u)

/-- The half-plane `{φ ≥ u}` version of `convexHull_inter_level_le`. -/
theorem convexHull_inter_level_ge (s : Finset Point) (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (hs : ∀ y ∈ s, u ≤ φ y) :
    convexHull ℝ (s : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ((s : Set Point) ∩ {x | φ x = u}) := by
  have hL : {x : Point | (-φ) x = -u} = {x | φ x = u} := by
    ext x; simp only [Set.mem_ofPred_eq, LinearMap.neg_apply, neg_inj]
  rw [← hL]
  exact convexHull_inter_level_le s (-φ) (-u)
    (fun y hy => by rw [LinearMap.neg_apply]; linarith [hs y hy])

/-- The triangle version of `convexHull_inter_level_le`. -/
theorem triangle_inter_level_le (a b c : Point) (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (ha : φ a ≤ u) (hb : φ b ≤ u) (hc : φ c ≤ u) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ (({a, b, c} : Set Point) ∩ {x | φ x = u}) := by
  classical
  have h := convexHull_inter_level_le ({a, b, c} : Finset Point) φ u (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption)
  simpa only [Finset.coe_insert, Finset.coe_singleton] using h

/-- The triangle version of `convexHull_inter_level_ge`. -/
theorem triangle_inter_level_ge (a b c : Point) (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (ha : u ≤ φ a) (hb : u ≤ φ b) (hc : u ≤ φ c) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ (({a, b, c} : Set Point) ∩ {x | φ x = u}) := by
  classical
  have h := convexHull_inter_level_ge ({a, b, c} : Finset Point) φ u (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption)
  simpa only [Finset.coe_insert, Finset.coe_singleton] using h

/-! ### Intersections of convex hulls on a line -/

/-- A point of the convex hull of `A ⊆ ℝ` is bracketed by two points of `A`. -/
theorem exists_le_le_of_mem_convexHull_real {A : Set ℝ} {x : ℝ} (hx : x ∈ convexHull ℝ A) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≤ x ∧ x ≤ a₂ := by
  suffices hS : convexHull ℝ A ⊆ {y : ℝ | ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≤ y ∧ y ≤ a₂} from hS hx
  refine convexHull_min ?_ ?_
  · intro y hy; exact ⟨y, hy, y, hy, le_rfl, le_rfl⟩
  · rw [convex_iff_ordConnected]
    refine ⟨?_⟩
    rintro y ⟨a₁, ha₁, -, -, hy₁, -⟩ z ⟨-, -, a₂, ha₂, -, hz₂⟩ w ⟨hw₁, hw₂⟩
    exact ⟨a₁, ha₁, a₂, ha₂, hy₁.trans hw₁, hw₂.trans hz₂⟩

/-- A real number between two points of `A` lies in the convex hull of `A`. -/
theorem mem_convexHull_real_of_between {A : Set ℝ} {a₁ a₂ y : ℝ} (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A)
    (hy₁ : a₁ ≤ y) (hy₂ : y ≤ a₂) : y ∈ convexHull ℝ A := by
  have : y ∈ _root_.segment ℝ a₁ a₂ := by
    rw [segment_eq_Icc (hy₁.trans hy₂)]; exact ⟨hy₁, hy₂⟩
  exact _root_.segment_subset_convexHull h₁ h₂ this

/-- On the real line: if no point of `B` lies in the hull of `A` unless it belongs to `A`,
and symmetrically, then the two hulls meet exactly in the hull of `A ∩ B`. -/
theorem convexHull_inter_convexHull_real {A B : Set ℝ}
    (hAB : ∀ y ∈ B, y ∈ convexHull ℝ A → y ∈ A)
    (hBA : ∀ y ∈ A, y ∈ convexHull ℝ B → y ∈ B) :
    convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa₁, hxa₂⟩ := exists_le_le_of_mem_convexHull_real hxA
    obtain ⟨b₁, hb₁, b₂, hb₂, hxb₁, hxb₂⟩ := exists_le_le_of_mem_convexHull_real hxB
    have hlo : max a₁ b₁ ∈ A ∩ B := by
      rcases le_total a₁ b₁ with h | h
      · rw [max_eq_right h]
        exact ⟨hAB b₁ hb₁ (mem_convexHull_real_of_between ha₁ ha₂ h (hxb₁.trans hxa₂)), hb₁⟩
      · rw [max_eq_left h]
        exact ⟨ha₁, hBA a₁ ha₁ (mem_convexHull_real_of_between hb₁ hb₂ h (hxa₁.trans hxb₂))⟩
    have hhi : min a₂ b₂ ∈ A ∩ B := by
      rcases le_total a₂ b₂ with h | h
      · rw [min_eq_left h]
        exact ⟨ha₂, hBA a₂ ha₂ (mem_convexHull_real_of_between hb₁ hb₂ (hxb₁.trans hxa₂) h)⟩
      · rw [min_eq_right h]
        exact ⟨hAB b₂ hb₂ (mem_convexHull_real_of_between ha₁ ha₂ (hxa₁.trans hxb₂) h), hb₂⟩
    exact mem_convexHull_real_of_between hlo hhi (max_le hxa₁ hxb₁) (le_min hxa₂ hxb₂)
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

/-- Transport of `convexHull_inter_convexHull_real` to a convex set `L` of the plane on which
some linear functional `ψ` is injective (e.g. a line). -/
theorem convexHull_inter_convexHull_of_injOn {L : Set Point} (hL : Convex ℝ L)
    (ψ : Point →ₗ[ℝ] ℝ) (hψ : Set.InjOn ψ L) {A B : Set Point} (hA : A ⊆ L) (hB : B ⊆ L)
    (hAB : ∀ y ∈ B, y ∈ convexHull ℝ A → y ∈ A)
    (hBA : ∀ y ∈ A, y ∈ convexHull ℝ B → y ∈ B) :
    convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  have hAL : convexHull ℝ A ⊆ L := convexHull_min hA hL
  have hBL : convexHull ℝ B ⊆ L := convexHull_min hB hL
  have hABL : convexHull ℝ (A ∩ B) ⊆ L := convexHull_min (Set.inter_subset_left.trans hA) hL
  apply Set.Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    -- the images under `ψ`
    have hAB' : ∀ y ∈ ψ '' B, y ∈ convexHull ℝ (ψ '' A) → y ∈ ψ '' A := by
      rintro _ ⟨y, hy, rfl⟩ hmem
      rw [← LinearMap.image_convexHull] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      have : z = y := hψ (hAL hz) (hB hy) hzy
      subst this
      exact ⟨z, hAB z hy hz, rfl⟩
    have hBA' : ∀ y ∈ ψ '' A, y ∈ convexHull ℝ (ψ '' B) → y ∈ ψ '' B := by
      rintro _ ⟨y, hy, rfl⟩ hmem
      rw [← LinearMap.image_convexHull] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      have : z = y := hψ (hBL hz) (hA hy) hzy
      subst this
      exact ⟨z, hBA z hy hz, rfl⟩
    have hx' : ψ x ∈ convexHull ℝ (ψ '' A) ∩ convexHull ℝ (ψ '' B) := by
      rw [← LinearMap.image_convexHull, ← LinearMap.image_convexHull]
      exact ⟨Set.mem_image_of_mem ψ hxA, Set.mem_image_of_mem ψ hxB⟩
    rw [convexHull_inter_convexHull_real hAB' hBA', ← hψ.image_inter hA hB,
      ← LinearMap.image_convexHull] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    have : z = x := hψ (hABL hz) (hAL hxA) hzx
    subst this
    exact hz
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

/-! ### The conformity criterion -/

/-- **Conformity criterion.**  Two nondegenerate triangles with disjoint interiors, such that
every vertex of either lying in the other triangle is a vertex of it, meet exactly in the
convex hull of their common vertices. -/
theorem conforming_of_disjoint_interiors {a b c d e f : Point}
    (habc : det a b c ≠ 0) (hdef : det d e f ≠ 0)
    (hdisj : Disjoint (interior (convexHull ℝ ({a, b, c} : Set Point)))
      (interior (convexHull ℝ ({d, e, f} : Set Point))))
    (hv₁ : ∀ v ∈ ({d, e, f} : Set Point),
      v ∈ convexHull ℝ ({a, b, c} : Set Point) → v ∈ ({a, b, c} : Set Point))
    (hv₂ : ∀ v ∈ ({a, b, c} : Set Point),
      v ∈ convexHull ℝ ({d, e, f} : Set Point) → v ∈ ({d, e, f} : Set Point)) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) =
      convexHull ℝ (({a, b, c} : Set Point) ∩ {d, e, f}) := by
  -- separate the interiors by a line
  obtain ⟨φ, u, h₁, h₂⟩ := geometric_hahn_banach_open_open
    (convex_triangle a b c).interior isOpen_interior
    (convex_triangle d e f).interior isOpen_interior hdisj
  set φl : Point →ₗ[ℝ] ℝ := (φ : Point →ₗ[ℝ] ℝ) with hφl
  have hφl_apply : ∀ x, φl x = φ x := fun _ => rfl
  -- `φ ≤ u` on the first closed triangle, `φ ≥ u` on the second
  have hT₁ : ∀ x ∈ convexHull ℝ ({a, b, c} : Set Point), φl x ≤ u := by
    intro x hx
    rw [← closure_interior_triangle habc] at hx
    exact closure_minimal (fun y hy => (h₁ y hy).le)
      (isClosed_le φ.continuous continuous_const) hx
  have hT₂ : ∀ x ∈ convexHull ℝ ({d, e, f} : Set Point), u ≤ φl x := by
    intro x hx
    rw [← closure_interior_triangle hdef] at hx
    exact closure_minimal (fun y hy => (h₂ y hy).le)
      (isClosed_le continuous_const φ.continuous) hx
  -- `φ` is not zero
  have hφ0 : φl ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := interior_triangle_nonempty habc
    obtain ⟨q, hq⟩ := interior_triangle_nonempty hdef
    have h1 := h₁ p hp
    have h2 := h₂ q hq
    rw [← hφl_apply, h0] at h1 h2
    simp at h1 h2
    linarith
  set L : Set Point := {x | φl x = u} with hLdef
  have hL : Convex ℝ L := convex_level φl u
  obtain ⟨ψ, hψ⟩ := exists_injOn_level hφ0 u
  -- the intersection lies on the line
  have hsub : convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) ⊆ L :=
    fun x ⟨hx₁, hx₂⟩ => le_antisymm (hT₁ x hx₁) (hT₂ x hx₂)
  have hV : ({a, b, c} : Set Point) ∩ {d, e, f} ⊆ L :=
    fun x ⟨hx₁, hx₂⟩ => hsub ⟨subset_convexHull ℝ _ hx₁, subset_convexHull ℝ _ hx₂⟩
  -- rewrite the intersection through the line
  have hface₁ := triangle_inter_level_le a b c φl u
    (hT₁ a (vertex_mem_triangle_left a b c)) (hT₁ b (vertex_mem_triangle_mid a b c))
    (hT₁ c (vertex_mem_triangle_right a b c))
  have hface₂ := triangle_inter_level_ge d e f φl u
    (hT₂ d (vertex_mem_triangle_left d e f)) (hT₂ e (vertex_mem_triangle_mid d e f))
    (hT₂ f (vertex_mem_triangle_right d e f))
  have hinter : convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) =
      (convexHull ℝ ({a, b, c} : Set Point) ∩ L) ∩ (convexHull ℝ ({d, e, f} : Set Point) ∩ L) := by
    ext x
    constructor
    · intro hx; exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
    · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; exact ⟨h1, h2⟩
  rw [hinter, hface₁, hface₂]
  -- the two faces on the line
  have hAB : ∀ y ∈ ({d, e, f} : Set Point) ∩ L,
      y ∈ convexHull ℝ (({a, b, c} : Set Point) ∩ L) → y ∈ ({a, b, c} : Set Point) ∩ L := by
    rintro y ⟨hy, hyL⟩ hmem
    exact ⟨hv₁ y hy (convexHull_mono Set.inter_subset_left hmem), hyL⟩
  have hBA : ∀ y ∈ ({a, b, c} : Set Point) ∩ L,
      y ∈ convexHull ℝ (({d, e, f} : Set Point) ∩ L) → y ∈ ({d, e, f} : Set Point) ∩ L := by
    rintro y ⟨hy, hyL⟩ hmem
    exact ⟨hv₂ y hy (convexHull_mono Set.inter_subset_left hmem), hyL⟩
  rw [convexHull_inter_convexHull_of_injOn hL ψ hψ Set.inter_subset_right Set.inter_subset_right
    hAB hBA]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hV ⟨h1, h2⟩⟩, ⟨h2, hV ⟨h1, h2⟩⟩⟩

/-- The conformity criterion for the specification's triangles: two valid triangles of `P`
with disjoint interiors, such that every vertex of either lying in the other triangle is one
of its vertices, meet exactly in the convex hull of their common vertices. -/
theorem triSet_inter_triSet_of_disjoint_interiors {P : Polygon} {s t : Polygon.Triangle}
    (hs : P.validTriangle s) (ht : P.validTriangle t)
    (hdisj : Disjoint (interior (P.triSet s)) (interior (P.triSet t)))
    (hv₁ : ∀ v ∈ P.triVertices t, v ∈ P.triSet s → v ∈ P.triVertices s)
    (hv₂ : ∀ v ∈ P.triVertices s, v ∈ P.triSet t → v ∈ P.triVertices t) :
    P.triSet s ∩ P.triSet t = convexHull ℝ (P.triVertices s ∩ P.triVertices t) :=
  conforming_of_disjoint_interiors (det_ne_zero_of_validTriangle hs)
    (det_ne_zero_of_validTriangle ht) hdisj hv₁ hv₂

end

end Geometry

end ArtGallery
