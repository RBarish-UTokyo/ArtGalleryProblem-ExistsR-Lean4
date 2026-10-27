module

public import ArtGallery.Irrational.Edges
public import ArtGallery.Invariance.Affine

/-!
# Theorem 4: irrational guards are sometimes needed

`ArtGallery.irrational_guards_needed`: the polygon `𝒫` of §2.1, scaled by `9376500` (the least
common multiple of the denominators of its coordinates) to integer coordinates
(`irrPolygonInt`), is simple and x-monotone, can be guarded by three guards, can be guarded by
four guards at rational points, and every guard set consisting of rational points has at least
four guards.

On `𝒫` itself:

* three guards: `(2, 2 - √2)`, `(3.5 + 5√2, 1.5√2)`, `(19, 1 + √2/2)` (`paper_three`, by
  `cover`; the conditions (A)–(D) hold with equality);
* four rational guards: `(2, 0.586)`, `(10.57, 2.121)`, `(10.572, 2.1216)`, `(19, 1.707)`
  (`paper_four`, by `cover`);
* the lower bound `four_le_card_of_rational` (Lemmas 5–12).

The scaling `A p = 9376500 • p` is an invertible affine map; the image polygon has the image
region (`Hardening.Invariance.filled_mapPoly`), and seeing, guard sets, cardinalities,
rationality of points and monotonicity are transported along `A`.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set ArtGallery.Hardening.Invariance

/-! ### Three guards and four rational guards on `𝒫` -/

/-- A set of points of `U` containing the four guards of `cover` is a guard set. -/
theorem isGuardSet_of_cover {h x₁ x₂ k : ℝ} (hh : 1 / 2 ≤ h ∧ h ≤ 3 / 5)
    (hk : 17 / 10 ≤ k ∧ k ≤ 9 / 5) (hx₁ : 21 / 2 ≤ x₁ ∧ x₁ ≤ 53 / 5)
    (hx₂ : 21 / 2 ≤ x₂ ∧ x₂ ≤ 53 / 5)
    (hA : x₁ * (50 - 14 * h) ≤ 535 - 159 * h) (hB : 2 * x₁ * (1 - h) ≤ 3 * h + 7)
    (hC : 490 * k - 243 ≤ x₂ * (20 * k + 22)) (hD : 34 * k - 7 ≤ x₂ * (4 * k - 2))
    {G : Set Point} (hGU : G ⊆ U) (hL : gL h ∈ G) (hM₁ : gM x₁ ∈ G) (hM₂ : gM x₂ ∈ G)
    (hR : gR k ∈ G) : P.IsGuardSet G := by
  refine ⟨fun g hg => filled_eq_U ▸ hGU hg, fun p hp => ?_⟩
  rcases cover hh hk hx₁ hx₂ hA hB hC hD hp with s | s | s | s
  · exact ⟨_, hL, s⟩
  · exact ⟨_, hM₁, s⟩
  · exact ⟨_, hM₂, s⟩
  · exact ⟨_, hR, s⟩

theorem gL_mem_U {h : ℝ} (hh : 0 ≤ h ∧ h ≤ 4) : gL h ∈ U := B_subset_U (gL_mem_B hh)
theorem gM_mem_U {x : ℝ} (hx : 7 / 2 ≤ x ∧ x ≤ 101 / 6) : gM x ∈ U := B_subset_U (gM_mem_B hx)
theorem gR_mem_U {k : ℝ} (hk : 0 ≤ k ∧ k ≤ 4) : gR k ∈ U := B_subset_U (gR_mem_B hk)

theorem gL_ne_gM {h x : ℝ} (hx : x ≠ 2) : gL h ≠ gM x := by
  intro e; have := congrArg Prod.fst e; simp only [gL, gM] at this; exact hx this.symm

theorem gL_ne_gR {h k : ℝ} : gL h ≠ gR k := by
  intro e; have := congrArg Prod.fst e; simp only [gL, gR] at this; norm_num at this

theorem gM_ne_gR {x k : ℝ} (hx : x ≠ 19) : gM x ≠ gR k := by
  intro e; have := congrArg Prod.fst e; simp only [gM, gR] at this; exact hx this

theorem gM_ne_gM {x x' : ℝ} (hx : x ≠ x') : gM x ≠ gM x' := by
  intro e; have := congrArg Prod.fst e; simp only [gM] at this; exact hx this

/-- **Part (1) on `𝒫`**: three guards, at `(2, 2 - √2)`, `(3.5 + 5√2, 1.5√2)`, `(19, 1 + √2/2)`. -/
theorem paper_three : P.HasGuardSetOfCard 3 := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hlo : 1.414 < √2 := by nlinarith
  have hhi : √2 < 1.415 := by nlinarith
  refine ⟨{gL (2 - √2), gM (7 / 2 + 5 * √2), gR (1 + √2 / 2)}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact gM_ne_gR (by intro e; linarith)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨gL_ne_gM (by intro e; linarith), gL_ne_gR⟩
  · refine isGuardSet_of_cover (h := 2 - √2) (x₁ := 7 / 2 + 5 * √2) (x₂ := 7 / 2 + 5 * √2)
      (k := 1 + √2 / 2) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by nlinarith) (by nlinarith)
      (by nlinarith) (by nlinarith) ?_ (by simp) (by simp) (by simp) (by simp)
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact gL_mem_U ⟨by linarith, by linarith⟩
    · exact gM_mem_U ⟨by linarith, by linarith⟩
    · exact gR_mem_U ⟨by linarith, by linarith⟩

/-- **Part (2) on `𝒫`**: four guards at rational points. -/
theorem paper_four : ∃ G : Finset Point, G.card = 4 ∧ P.IsGuardSet (G : Set Point) ∧
    ∀ p ∈ G, IsRationalPoint p := by
  refine ⟨{gL (293 / 500), gM (1057 / 100), gM (2643 / 250), gR (1707 / 1000)}, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact gM_ne_gR (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨gM_ne_gM (by norm_num), gM_ne_gR (by norm_num)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨gL_ne_gM (by norm_num), gL_ne_gM (by norm_num), gL_ne_gR⟩
  · refine isGuardSet_of_cover (h := 293 / 500) (x₁ := 1057 / 100) (x₂ := 2643 / 250)
      (k := 1707 / 1000) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ (by simp) (by simp) (by simp) (by simp)
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact gL_mem_U ⟨by norm_num, by norm_num⟩
    · exact gM_mem_U ⟨by norm_num, by norm_num⟩
    · exact gM_mem_U ⟨by norm_num, by norm_num⟩
    · exact gR_mem_U ⟨by norm_num, by norm_num⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨2, 293 / 500, by simp only [gL, Prod.mk.injEq]; constructor <;> norm_num⟩
    · exact ⟨1057 / 100, 2121 / 1000, by simp only [gM, Prod.mk.injEq]; constructor <;> norm_num⟩
    · exact ⟨2643 / 250, 1326 / 625, by simp only [gM, Prod.mk.injEq]; constructor <;> norm_num⟩
    · exact ⟨19, 1707 / 1000, by simp only [gR, Prod.mk.injEq]; constructor <;> norm_num⟩

/-! ### Scaling to integer coordinates -/

/-- The polygon `𝒫` scaled by `9376500`, with integer vertex coordinates. -/
def irrPolygonInt : List (ℤ × ℤ) :=
  [(0, 0), (17815350, 0), (18753000, -4688250), (18753000, 0), (28129500, 0),
   (28129500, -1406475), (32817750, 0), (37506000, 0), (37506000, -5922000),
   (75012000, -8883000), (75012000, 0), (112518000, 0), (112518000, -15181000),
   (150024000, -16074000), (150024000, 0), (177215850, 0), (178153500, -4688250),
   (178153500, 0), (187530000, 0), (187530000, 4688250), (281295000, 4688250),
   (281295000, 5625900), (187530000, 5625900), (187530000, 37506000), (179091150, 37506000),
   (178153500, 42194250), (178153500, 37506000), (162526000, 37506000),
   (162526000, 38912475), (157837750, 37506000), (150024000, 37506000),
   (150024000, 44407104), (112518000, 62159944), (112518000, 37506000), (99390900, 37506000),
   (99390900, 75012000), (98453250, 75012000), (98453250, 37506000), (75012000, 37506000),
   (75012000, 58653000), (37506000, 55860000), (37506000, 37506000), (19690650, 37506000),
   (18753000, 42194250), (18753000, 37506000), (0, 37506000), (0, 16877700),
   (-93765000, 16877700), (-93765000, 15940050), (0, 15940050)]

theorem irrPolygonInt_eq : irrPolygonInt.map (fun z : ℤ × ℤ => ((z.1 : ℚ), (z.2 : ℚ))) =
    paperVerts.map (fun p : QPt => (9376500 * p.1, 9376500 * p.2)) := by decide +kernel

/-- The scaling `p ↦ 9376500 • p`. -/
noncomputable def scaleA : Point ≃ᵃ[ℝ] Point :=
  (LinearEquiv.smulOfNeZero ℝ Point (9376500 : ℝ) (by norm_num)).toAffineEquiv

theorem scaleA_apply (p : Point) : scaleA p = (9376500 : ℝ) • p := rfl

theorem scaleA_symm_apply (p : Point) : scaleA.symm p = (9376500 : ℝ)⁻¹ • p := by
  rw [AffineEquiv.symm_apply_eq, scaleA_apply, smul_smul]; norm_num

/-- The integer polygon is the image of `𝒫` under the scaling. -/
theorem intPolygon_eq : Polygon.mk (irrPolygonInt.map intPoint) = mapPoly scaleA P := by
  unfold mapPoly P
  congr 1
  have h1 : irrPolygonInt.map intPoint =
      (irrPolygonInt.map (fun z : ℤ × ℤ => ((z.1 : ℚ), (z.2 : ℚ)))).map ratPoint := by
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    simp [intPoint, ratPoint]
  rw [h1, irrPolygonInt_eq, List.map_map, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, scaleA_apply, ratPoint, Prod.smul_mk, smul_eq_mul]
  push_cast; rfl

theorem sees_scaleA {p q : Point} :
    (mapPoly scaleA P).Sees (scaleA p) (scaleA q) ↔ P.Sees p q := by
  unfold Polygon.Sees
  rw [filled_mapPoly, ← image_segment', image_subset_image_iff scaleA.injective]

theorem isGuardSet_scaleA {G : Finset Point} (hG : P.IsGuardSet (G : Set Point)) :
    (mapPoly scaleA P).IsGuardSet ((G.image scaleA : Finset Point) : Set Point) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [filled_mapPoly]; exact mem_image_of_mem _ (hG.1 hg')
  · intro p hp
    rw [filled_mapPoly] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨g, hg, hs⟩ := hG.2 p' hp'
    exact ⟨scaleA g, by simp only [Finset.coe_image]; exact mem_image_of_mem _ hg,
      sees_scaleA.2 hs⟩

theorem isGuardSet_of_scaleA {G : Finset Point}
    (hG : (mapPoly scaleA P).IsGuardSet (G : Set Point)) :
    P.IsGuardSet ((G.image scaleA.symm : Finset Point) : Set Point) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hG.1 hg'
    rw [filled_mapPoly] at this
    obtain ⟨x, hx, hxg⟩ := this
    rw [← hxg, AffineEquiv.symm_apply_apply]; exact hx
  · intro p hp
    have hp' : scaleA p ∈ (mapPoly scaleA P).filled := by
      rw [filled_mapPoly]; exact mem_image_of_mem _ hp
    obtain ⟨g, hg, hs⟩ := hG.2 _ hp'
    refine ⟨scaleA.symm g, by simp only [Finset.coe_image]; exact mem_image_of_mem _ hg, ?_⟩
    rw [← sees_scaleA, AffineEquiv.apply_symm_apply]; exact hs

theorem isRationalPoint_scaleA {p : Point} (hp : IsRationalPoint p) :
    IsRationalPoint (scaleA p) := by
  obtain ⟨a, b, rfl⟩ := hp
  exact ⟨9376500 * a, 9376500 * b, by
    rw [scaleA_apply]; simp only [Prod.smul_mk, smul_eq_mul]; push_cast; rfl⟩

theorem isRationalPoint_scaleA_symm {p : Point} (hp : IsRationalPoint p) :
    IsRationalPoint (scaleA.symm p) := by
  obtain ⟨a, b, rfl⟩ := hp
  exact ⟨(9376500)⁻¹ * a, (9376500)⁻¹ * b, by
    rw [scaleA_symm_apply]; simp only [Prod.smul_mk, smul_eq_mul]; push_cast; rfl⟩

theorem xMonotone_scaleA : (mapPoly scaleA P).XMonotone := by
  intro a
  have hS : {p ∈ (mapPoly scaleA P).filled | p.1 = a} =
      scaleA '' {p ∈ P.filled | p.1 = a / 9376500} := by
    ext p
    simp only [filled_mapPoly, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h1⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      rw [scaleA_apply] at h1
      simp only [Prod.smul_fst, smul_eq_mul] at h1
      rw [← h1]; ring
    · rintro ⟨x, ⟨hx, h1⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rw [scaleA_apply]; simp only [Prod.smul_fst, smul_eq_mul]; rw [h1]; ring
  rw [hS]
  exact (xMonotone_P _).image _ (AffineEquiv.continuous_of_finiteDimensional scaleA).continuousOn

end

end ArtGallery.Irrational

namespace ArtGallery

@[expose] public section

open ArtGallery.Irrational ArtGallery.Hardening.Invariance

/-- **Theorem 4** (Abrahamsen–Adamaszek–Miltzow, §2). There is a simple monotone polygon with
integer vertex coordinates that can be guarded by three guards, while the optimal guard sets with
guards at rational points have four guards. -/
theorem irrational_guards_needed :
    ∃ V : List (ℤ × ℤ),
      (Polygon.mk (V.map intPoint)).Simple ∧
      (Polygon.mk (V.map intPoint)).XMonotone ∧
      (Polygon.mk (V.map intPoint)).HasGuardSetOfCard 3 ∧
      (∃ G : Finset Point, G.card = 4 ∧
        (Polygon.mk (V.map intPoint)).IsGuardSet (G : Set Point) ∧
        ∀ p ∈ G, IsRationalPoint p) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map intPoint)).IsGuardSet (G : Set Point) →
        (∀ p ∈ G, IsRationalPoint p) → 4 ≤ G.card := by
  refine ⟨irrPolygonInt, ?_⟩
  rw [intPolygon_eq]
  refine ⟨(simple_mapPoly_iff scaleA P).2 simple_P, xMonotone_scaleA, ?_, ?_, ?_⟩
  · obtain ⟨G, hc, hG⟩ := paper_three
    exact ⟨G.image scaleA, by rw [Finset.card_image_of_injective _ scaleA.injective, hc],
      isGuardSet_scaleA hG⟩
  · obtain ⟨G, hc, hG, hr⟩ := paper_four
    refine ⟨G.image scaleA, by rw [Finset.card_image_of_injective _ scaleA.injective, hc],
      isGuardSet_scaleA hG, ?_⟩
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact isRationalPoint_scaleA (hr q hq)
  · intro G hG hr
    have h4 := four_le_card_of_rational (isGuardSet_of_scaleA hG) (by
      intro p hp
      simp only [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact isRationalPoint_scaleA_symm (hr q hq))
    rwa [Finset.card_image_of_injective _ scaleA.symm.injective] at h4

end

end ArtGallery
