module

public import ArtGallery.Hardness.Sec5.Assemble.Sides
public import ArtGallery.Hardness.Sec5.Templates.InvData
public import ArtGallery.Hardness.Sec5.Templates.AddGEData
public import ArtGallery.Hardness.Sec5.Templates.AddLEData
public import ArtGallery.Hardness.Sec5.Templates.OrientData
public import ArtGallery.Stade.Generic.AffineOrient

/-!
# Section 5: the template hypotheses `ChainAt` / `SepAt` for the units

* **Bridge** to the certificate data: `tmplV k` and `tmplD k` are literally the lists and
  denominators of `Templates/*Data.lean` (`tmplV_ge : tmplV .ge = Tmpl.addGEV`, …), and `tmplR k`
  is the separation region of the kind.
* `sepAt_of_walls`: the wall separation `SideAt.sep_walls` gives `Tmpl.SepAt` for a region inside
  the box `|x|, |y| < 60 D` whose zones contain the two channel walls.
* In template coordinates the channel walls are `[V₀, (−D S, D S)]` and `[V_l, (−D S, D S + 3D/2)]`
  (`tmplMap_symm_c1`, `tmplMap_symm_d1`).  The **lower wall lies in the first zone**
  (`lowerWall_zone`) and the **upper wall in the second zone** (`upperWall_zone`), for all four
  kinds.  (For the addition kinds the upper wall leaves `V_l = (−10, 21/2)·D` with `x + y`
  increasing, so their second zone is `{x ≤ V_l.x, x + y ≥ V_l.x + V_l.y, 101x + 100y ≤ …}`,
  of the same shape as the first zone; for `Inv` it is the wedge on the other side of
  `x + y = V_l.x + V_l.y`.)
* `SideAt.sepAt`: every unit of a side (`rightSide` in `polyC`, `leftSide` in the mirrored
  `polyM`) has `Tmpl.SepAt` in its template coordinates.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input CorridorAt c0 c1 d0 d1)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue
open ArtGallery.Irrational (HP hp convex_hp)

/-! ### Bridge to the certificate data -/

theorem tmplV_ge : tmplV .ge = Tmpl.addGEV := by decide +kernel
theorem tmplV_le : tmplV .le = Tmpl.addLEV := by decide +kernel
theorem tmplV_orient : tmplV .orient = Tmpl.addORV := by decide +kernel
theorem tmplV_inv : tmplV .inv = Tmpl.invV := by decide +kernel
theorem tmplD_ge : tmplD .ge = Tmpl.addGED := rfl
theorem tmplD_le : tmplD .le = Tmpl.addLED := rfl
theorem tmplD_orient : tmplD .orient = Tmpl.addORD := rfl
theorem tmplD_inv : tmplD .inv = Tmpl.invD := rfl

/-- The separation region of the certificates of a kind. -/
def tmplR : Kind → Tmpl.Region
  | .ge => Tmpl.addGER
  | .le => Tmpl.addLER
  | .orient => Tmpl.addORR
  | .inv => Tmpl.invR

/-! ### From walls to `SepAt` -/

/-- **`SepAt` from the wall separation.** -/
theorem sepAt_of_walls {P : Polygon} {V : List (ℤ × ℤ)} {a : ℕ} {R : Tmpl.Region} {B : ℝ}
    {wL wU : Set Point}
    (hsep : ∀ i < P.n, (∀ j, j + 1 < V.length → (a + j) % P.n ≠ i) → ∀ x ∈ P.edge i,
      |x.1| < B → |x.2| < B → x ∈ wL ∨ x ∈ wU)
    (hbox : ∀ x, R.Mem x → |x.1| < B ∧ |x.2| < B)
    (hwL : ∀ x ∈ wL, ¬ R.Mem x) (hwU : ∀ x ∈ wU, ¬ R.Mem x) : Tmpl.SepAt P V a R := by
  intro i hi hnc x hx hR
  obtain ⟨b1, b2⟩ := hbox x hR
  rcases hsep i hi hnc x hx b1 b2 with h | h
  · exact hwL x h hR
  · exact hwU x h hR

/-- A segment whose end points lie in a zone of the region misses the region. -/
theorem not_mem_of_zone {R : Tmpl.Region} {W : List HP} (hW : W ∈ R.zones) {p q : Point}
    (hp' : p ∈ hp W) (hq : q ∈ hp W) : ∀ x ∈ ArtGallery.segment p q, ¬ R.Mem x := by
  intro x hx hR
  have hx' : x ∈ hp W := Geometry.segment_subset_of_convex (convex_hp W) hp' hq hx
  obtain ⟨c, hc, hneg⟩ := hR.2 W hW
  have := hx' c hc
  linarith

/-- The box of the regions: `|x|, |y| < 60 D`. -/
theorem tmplR_box (k : Kind) : ∀ x, (tmplR k).Mem x →
    |x.1| < 60 * (tmplD k : ℝ) ∧ |x.2| < 60 * (tmplD k : ℝ) := by
  intro x hx
  have h := hx.1
  cases k <;>
  · simp only [tmplR, Tmpl.addGER, Tmpl.addLER, Tmpl.addORR, Tmpl.invR, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Irrational.HP.val] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    push_cast at h1 h2 h3 h4
    simp only [tmplD]
    push_cast
    rw [abs_lt, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-! ### The walls in template coordinates -/

theorem tmplMap_symm_c1 (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    (tmplMap k S H (S_ne_of hS)).symm (S + 2, H) = (-((tmplD k : ℝ) * S), (tmplD k : ℝ) * S) := by
  apply (tmplMap k S H (S_ne_of hS)).injective
  rw [AffineEquiv.apply_symm_apply, tmplMap_apply]
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : S ≠ 0 := S_ne_of hS
  ext <;> simp only <;> field_simp <;> ring

theorem tmplMap_symm_d1 (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    (tmplMap k S H (S_ne_of hS)).symm (S + 2, H + 3 / (2 * S)) =
      (-((tmplD k : ℝ) * S), (tmplD k : ℝ) * S + 3 / 2 * (tmplD k : ℝ)) := by
  apply (tmplMap k S H (S_ne_of hS)).injective
  rw [AffineEquiv.apply_symm_apply, tmplMap_apply]
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : S ≠ 0 := S_ne_of hS
  ext <;> simp only <;> field_simp <;> ring

/-- **The lower channel wall lies in the first zone** (all kinds, `S ≥ 10⁴`). -/
theorem lowerWall_zone (k : Kind) {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplFst k)) (-((tmplD k : ℝ) * S), (tmplD k : ℝ) * S),
      ¬ (tmplR k).Mem x := by
  cases k
  · refine not_mem_of_zone (R := tmplR .orient) (W := [((-1 : ℤ), 0, -6044495520), (1, 1, 6029607600), (-101, -100, -609005255520)]) (by simp [tmplR, Tmpl.addORR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFst, tmplV, tmplVOR] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · refine not_mem_of_zone (R := tmplR .ge) (W := [((-1 : ℤ), 0, -3377806320), (1, 1, 3369486600), (-101, -100, -340326466320)]) (by simp [tmplR, Tmpl.addGER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFst, tmplV, tmplVGE] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · refine not_mem_of_zone (R := tmplR .le) (W := [((-1 : ℤ), 0, -942517800), (1, 1, 940044000), (-101, -100, -94946917800)]) (by simp [tmplR, Tmpl.addLER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFst, tmplV, tmplVLE] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · refine not_mem_of_zone (R := tmplR .inv) (W := [((-1 : ℤ), 0, -752243685600), (1, 1, 250747895200), (-101, -100, -25827033205600)]) (by simp [tmplR, Tmpl.invR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplFst, tmplV, tmplVInv] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith

/-- **The upper channel wall of an inversion unit lies in the second zone.** -/
theorem upperWall_zone_inv {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplLst .inv))
      (-((tmplD .inv : ℝ) * S), (tmplD .inv : ℝ) * S + 3 / 2 * (tmplD .inv : ℝ)),
      ¬ (tmplR .inv).Mem x := by
  refine not_mem_of_zone (R := tmplR .inv)
    (W := [((-1 : ℤ), 0, 3510470532800), (-1, -1, 9422385668300), (99, 100, -938728096297200)])
    (by simp [tmplR, Tmpl.invR]) ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp [Irrational.HP.val, intPoint, tmplLst, tmplV, tmplVInv] <;> norm_num
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith

/-- **The upper channel wall lies in the second zone** (all kinds, `S ≥ 10⁴`).  For the three
addition kinds the zone is `{x ≤ V_l.x, x + y ≥ V_l.x + V_l.y, 101 x + 100 y ≤ 101 V_l.x + 100 V_l.y}`
with `V_l = (−10, 21/2)·D`: along the wall (direction `(−S + 10, S − 9)·D`) the three constraints
grow by `S − 10`, `1` and `S − 110` (times `D` and the parameter). -/
theorem upperWall_zone (k : Kind) {S : ℝ} (hS : 10000 ≤ S) :
    ∀ x ∈ ArtGallery.segment (intPoint (tmplLst k))
      (-((tmplD k : ℝ) * S), (tmplD k : ℝ) * S + 3 / 2 * (tmplD k : ℝ)),
      ¬ (tmplR k).Mem x := by
  cases k
  · refine not_mem_of_zone (R := tmplR .orient) (W := [((-1 : ℤ), 0, -1488792000), (1, 1, -74439600), (-101, -100, 5955168000)]) (by simp [tmplR, Tmpl.addORR]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLst, tmplV, tmplVOR] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · refine not_mem_of_zone (R := tmplR .ge) (W := [((-1 : ℤ), 0, -831972000), (1, 1, -41598600), (-101, -100, 3327888000)]) (by simp [tmplR, Tmpl.addGER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLst, tmplV, tmplVGE] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · refine not_mem_of_zone (R := tmplR .le) (W := [((-1 : ℤ), 0, -247380000), (1, 1, -12369000), (-101, -100, 989520000)]) (by simp [tmplR, Tmpl.addLER]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp [Irrational.HP.val, intPoint, tmplLst, tmplV, tmplVLE] <;> norm_num
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Irrational.HP.val, tmplD] <;> nlinarith
  · exact upperWall_zone_inv hS

/-! ### `SepAt` for the units of a side -/

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- **`Tmpl.SepAt` for unit `m`** (either side, every kind): in the template coordinates of the
unit, the edges of `Q` other than the template chain avoid the separation region `tmplR`. -/
theorem SideAt.sepAt :
    Tmpl.SepAt (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind
      (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k)).symm Q) (tmplV (us[m]'hm).kind) (hQ.tStart hm)
      (tmplR (us[m]'hm).kind) := by
  have hg := hQ.good hm
  have hS8 := hg.S_ge_real
  refine sepAt_of_walls (hQ.sep_walls hm) (tmplR_box _) ?_ ?_
  · rw [ratPoint_c1', tmplMap_symm_c1 _ hg.S_ge_k]
    exact lowerWall_zone _ (by linarith)
  · rw [ratPoint_d1', rhoR_eq, tmplMap_symm_d1 _ hg.S_ge_k]
    exact upperWall_zone _ (by linarith)

/-- **`Tmpl.SepAt` for an inversion unit** (a special case of `SideAt.sepAt`). -/
theorem SideAt.sepAt_inv (_hk : (us[m]'hm).kind = .inv) :
    Tmpl.SepAt (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind
      (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k)).symm Q) (tmplV (us[m]'hm).kind) (hQ.tStart hm)
      (tmplR (us[m]'hm).kind) := by
  exact hQ.sepAt hm

end Side

/-! ### The polygon in template coordinates -/

/-- The inverse placement preserves orientation. -/
theorem orientFactor_tmplMap_symm (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    0 < Stade.orientFactor (tmplMap k S H (S_ne_of hS)).symm := by
  set A := tmplMap k S H (S_ne_of hS)
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  have h := Stade.det_map A.symm (A 0) (A (1, 0)) (A (0, 1))
  simp only [AffineEquiv.symm_apply_apply] at h
  have h1 : det (0 : Point) (1, 0) (0, 1) = 1 := by
    simp only [det, Prod.fst_zero, Prod.snd_zero]; norm_num
  have h2 : det (A 0) (A (1, 0)) (A (0, 1)) = 1 / ((tmplD k : ℝ) * S) ^ 2 := by
    simp only [A, tmplMap_apply, det, Prod.fst_zero, Prod.snd_zero]
    field_simp
    ring
  rw [h1, h2] at h
  have hpos : (0 : ℝ) < 1 / ((tmplD k : ℝ) * S) ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

section Side2

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- The polygon in the template coordinates of unit `m` is simple. -/
theorem SideAt.tmpl_simple : (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind
    (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
    (S_ne_of (hQ.good hm).S_ge_k)).symm Q).Simple :=
  Hardening.Invariance.simple_mapPoly _ _ hQ.simple

/-- The polygon in the template coordinates of unit `m` is counter-clockwise. -/
theorem SideAt.tmpl_ccw : (Hardening.Invariance.mapPoly (tmplMap (us[m]'hm).kind
    (unitInput n k m (us[m]'hm)).S (unitInput n k m (us[m]'hm)).H
    (S_ne_of (hQ.good hm).S_ge_k)).symm Q).InteriorLeft :=
  Stade.interiorLeft_mapPoly _ (orientFactor_tmplMap_symm _ (hQ.good hm).S_ge_k) hQ.simple hQ.ccw

end Side2

end ArtGallery.Sec5

end
