module

public import ArtGallery.Hardness.BP.Assemble.Sides
public import ArtGallery.Hardness.BP.Templates.InvData
public import ArtGallery.Hardness.BP.Templates.AddGEData
public import ArtGallery.Hardness.BP.Templates.AddLEData
public import ArtGallery.Hardness.BP.Templates.OrientData
public import ArtGallery.Hardness.Sec5.Assemble.Sep

/-!
# Boundary-point variant: the template hypotheses `ChainAt` / `SepAt` for the units

As `Sec5/Assemble/Sep.lean`, for the boundary-point templates:

* **Bridge** to the certificate data: `tmplVBP k` and `tmplDBP k` are literally the lists and
  denominators of `BP/Templates/*Data.lean` (`tmplVBP_ge : tmplVBP .ge = Tmpl.bpGEV`, …), and
  `tmplRBP k` is the separation region of the kind (`Tmpl.bpGER`, …).
* In template coordinates the channel walls are `[V₀, (−D S, D S)]` and
  `[V_l, (−D S, D S + 3D/2)]` (`tmplMapBP_symm_c1`, `tmplMapBP_symm_d1`); the **lower wall lies in
  the first zone** of the region (`lowerWallBP_zone`) and the **upper wall in the second zone**
  (`upperWallBP_zone`), for all four kinds and `S ≥ 10⁴`.
* `SideAtBP.sepAt`: every unit of a side (`rightSideBP` in `polyCBP`, `leftSideBP` in the
  mirrored `polyMBP`) has `Tmpl.SepAt` in its template coordinates; `SideAtBP.tmpl_simple`,
  `SideAtBP.tmpl_ccw`: the polygon in template coordinates is simple and counter-clockwise.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue
open ArtGallery.Irrational (HP hp convex_hp)

/-! ### Bridge to the certificate data -/

theorem tmplVBP_ge : tmplVBP .ge = Tmpl.bpGEV := by decide +kernel
theorem tmplVBP_le : tmplVBP .le = Tmpl.bpLEV := by decide +kernel
theorem tmplVBP_orient : tmplVBP .orient = Tmpl.bpORV := by decide +kernel
theorem tmplVBP_inv : tmplVBP .inv = Tmpl.bpInvV := by decide +kernel
theorem tmplDBP_ge : tmplDBP .ge = Tmpl.bpGED := rfl
theorem tmplDBP_le : tmplDBP .le = Tmpl.bpLED := rfl
theorem tmplDBP_orient : tmplDBP .orient = Tmpl.bpORD := rfl
theorem tmplDBP_inv : tmplDBP .inv = Tmpl.bpInvD := rfl
theorem tmplVTBP_ge : tmplVTBP .ge = Tmpl.bpGEVT := by decide +kernel
theorem tmplVTBP_le : tmplVTBP .le = Tmpl.bpLEVT := by decide +kernel
theorem tmplVTBP_orient : tmplVTBP .orient = Tmpl.bpORVT := by decide +kernel
theorem tmplVTBP_inv : tmplVTBP .inv = Tmpl.bpInvVT := by decide +kernel

/-- The separation region of the certificates of a kind. -/
def tmplRBP : Kind → Tmpl.Region
  | .ge => Tmpl.bpGER
  | .le => Tmpl.bpLER
  | .orient => Tmpl.bpORR
  | .inv => Tmpl.bpInvR

/-- The box of the regions: `|x|, |y| < 60 D`. -/
theorem tmplRBP_box (k : Kind) : ∀ x, (tmplRBP k).Mem x →
    |x.1| < 60 * (tmplDBP k : ℝ) ∧ |x.2| < 60 * (tmplDBP k : ℝ) := by
  intro x hx
  have h := hx.1
  cases k <;>
  · simp only [tmplRBP, Tmpl.bpGER, Tmpl.bpLER, Tmpl.bpORR, Tmpl.bpInvR, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Irrational.HP.val] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    push_cast at h1 h2 h3 h4
    simp only [tmplDBP]
    push_cast
    rw [abs_lt, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-! ### The walls in template coordinates -/

theorem tmplMapBP_symm_c1 (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    (tmplMapBP k S H (S_ne_of hS)).symm (S + 2, H) = (-((tmplDBP k : ℝ) * S), (tmplDBP k : ℝ) * S) := by
  apply (tmplMapBP k S H (S_ne_of hS)).injective
  rw [AffineEquiv.apply_symm_apply, tmplMapBP_apply]
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : S ≠ 0 := S_ne_of hS
  ext <;> simp only <;> field_simp <;> ring

theorem tmplMapBP_symm_d1 (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    (tmplMapBP k S H (S_ne_of hS)).symm (S + 2, H + 3 / (2 * S)) =
      (-((tmplDBP k : ℝ) * S), (tmplDBP k : ℝ) * S + 3 / 2 * (tmplDBP k : ℝ)) := by
  apply (tmplMapBP k S H (S_ne_of hS)).injective
  rw [AffineEquiv.apply_symm_apply, tmplMapBP_apply]
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : S ≠ 0 := S_ne_of hS
  ext <;> simp only <;> field_simp <;> ring

/-- **The lower channel wall lies in the first zone** (all kinds, `S ≥ 10⁴`). -/
theorem lowerWallBP_zone (k : Kind) {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplFstBP k)) (-((tmplDBP k : ℝ) * S), (tmplDBP k : ℝ) * S),
      ¬ (tmplRBP k).Mem x := by
  cases k
  · refine not_mem_of_zone (R := tmplRBP .orient) (W := [((-1 : ℤ), 0, -11275200), (1, 1, 11240400), (-101, -100, -1135315200)]) (by simp [tmplRBP, Tmpl.bpORR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFstBP, tmplVBP, tmplVORBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · refine not_mem_of_zone (R := tmplRBP .ge) (W := [((-1 : ℤ), 0, -11275200), (1, 1, 11240400), (-101, -100, -1135315200)]) (by simp [tmplRBP, Tmpl.bpGER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFstBP, tmplVBP, tmplVGEBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · refine not_mem_of_zone (R := tmplRBP .le) (W := [((-1 : ℤ), 0, -13497600), (1, 1, 13453200), (-101, -100, -1358817600)]) (by simp [tmplRBP, Tmpl.bpLER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFstBP, tmplVBP, tmplVLEBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · refine not_mem_of_zone (R := tmplRBP .inv) (W := [((-1 : ℤ), 0, -1504487371200), (1, 1, 1128365528400), (-101, -100, -114341040211200)]) (by simp [tmplRBP, Tmpl.bpInvR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFstBP, tmplVBP, tmplVInvBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith

/-- **The upper channel wall of an inversion unit lies in the second zone.** -/
theorem upperWallBP_zone_inv {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplLstBP .inv))
      (-((tmplDBP .inv : ℝ) * S), (tmplDBP .inv : ℝ) * S + 3 / 2 * (tmplDBP .inv : ℝ)),
      ¬ (tmplRBP .inv).Mem x := by
  refine not_mem_of_zone (R := tmplRBP .inv)
    (W := [((-1 : ℤ), 0, 21062823196800), (-1, -1, 56534314009800), (99, 100, -5632368577783200)])
    (by simp [tmplRBP, Tmpl.bpInvR]) ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp [Irrational.HP.val, intPoint, tmplLstBP, tmplVBP, tmplVInvBP] <;> norm_num
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith

/-- **The upper channel wall lies in the second zone** (all kinds, `S ≥ 10⁴`).  For the three
addition kinds the zone is `{x ≤ V_l.x, x + y ≥ V_l.x + V_l.y, 101 x + 100 y ≤ 101 V_l.x + 100 V_l.y}`
with `V_l = (−10, 21/2)·D`: along the wall (direction `(−S + 10, S − 9)·D`) the three constraints
grow by `S − 10`, `1` and `S − 110` (times `D` and the parameter). -/
theorem upperWallBP_zone (k : Kind) {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplLstBP k))
      (-((tmplDBP k : ℝ) * S), (tmplDBP k : ℝ) * S + 3 / 2 * (tmplDBP k : ℝ)),
      ¬ (tmplRBP k).Mem x := by
  cases k
  · refine not_mem_of_zone (R := tmplRBP .orient) (W := [((-1 : ℤ), 0, -4176000), (1, 1, 1252800), (-101, -100, -129456000)]) (by simp [tmplRBP, Tmpl.bpORR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLstBP, tmplVBP, tmplVORBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · refine not_mem_of_zone (R := tmplRBP .ge) (W := [((-1 : ℤ), 0, -4176000), (1, 1, 1252800), (-101, -100, -129456000)]) (by simp [tmplRBP, Tmpl.bpGER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLstBP, tmplVBP, tmplVGEBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · refine not_mem_of_zone (R := tmplRBP .le) (W := [((-1 : ℤ), 0, -5328000), (1, 1, 1598400), (-101, -100, -165168000)]) (by simp [tmplRBP, Tmpl.bpLER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLstBP, tmplVBP, tmplVLEBP] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplDBP] <;> nlinarith
  · exact upperWallBP_zone_inv hS

/-! ### `SepAt` for the units of a side -/

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- **`Tmpl.SepAt` for unit `m`** (either side, every kind): in the template coordinates of the
unit, the edges of `Q` other than the template chain avoid the separation region `tmplRBP`. -/
theorem SideAtBP.sepAt :
    Tmpl.SepAt (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind
      (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k)).symm Q) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm)
      (tmplRBP (us[m]'hm).kind) := by
  have hg := hQ.good hm
  have hS8 := hg.S_ge_real
  refine sepAt_of_walls (hQ.sep_walls hm) (tmplRBP_box _) ?_ ?_
  · rw [ratPoint_c1', tmplMapBP_symm_c1 _ hg.S_ge_k]
    exact lowerWallBP_zone _ (by linarith)
  · rw [ratPoint_d1', rhoR_eq, tmplMapBP_symm_d1 _ hg.S_ge_k]
    exact upperWallBP_zone _ (by linarith)

end Side

/-! ### The polygon in template coordinates -/

/-- The inverse placement preserves orientation. -/
theorem orientFactor_tmplMapBP_symm (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    0 < Stade.orientFactor (tmplMapBP k S H (S_ne_of hS)).symm := by
  set A := tmplMapBP k S H (S_ne_of hS)
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  have h := Stade.det_map A.symm (A 0) (A (1, 0)) (A (0, 1))
  simp only [AffineEquiv.symm_apply_apply] at h
  have h1 : det (0 : Point) (1, 0) (0, 1) = 1 := by
    simp only [det, Prod.fst_zero, Prod.snd_zero]; norm_num
  have h2 : det (A 0) (A (1, 0)) (A (0, 1)) = 1 / ((tmplDBP k : ℝ) * S) ^ 2 := by
    simp only [A, tmplMapBP_apply, det, Prod.fst_zero, Prod.snd_zero]
    field_simp
    ring
  rw [h1, h2] at h
  have hpos : (0 : ℝ) < 1 / ((tmplDBP k : ℝ) * S) ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

section Side2

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- The polygon in the template coordinates of unit `m` is simple. -/
theorem SideAtBP.tmpl_simple : (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind
    (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
    (S_ne_of (hQ.good hm).S_ge_k)).symm Q).Simple :=
  Hardening.Invariance.simple_mapPoly _ _ hQ.simple

/-- The polygon in the template coordinates of unit `m` is counter-clockwise. -/
theorem SideAtBP.tmpl_ccw : (Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind
    (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
    (S_ne_of (hQ.good hm).S_ge_k)).symm Q).InteriorLeft :=
  Stade.interiorLeft_mapPoly _ (orientFactor_tmplMapBP_symm _ (hQ.good hm).S_ge_k) hQ.simple hQ.ccw

end Side2

end ArtGallery.BP

end
