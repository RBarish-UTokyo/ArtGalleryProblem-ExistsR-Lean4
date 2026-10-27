module

public import ArtGallery.Hardness.Sec5.ConstraintTmpl

/-!
# Section 5, constraints (iv)+(v) for one unit

For a unit `m` of a side (`SideAt Q n k us st`) and guards `UnitG` seen from it (working frame,
base offsets `off σ`), the constraint enforced by the unit, in terms of the offsets of its working
slots `σ_j = (unitInput n k m u).sigma j`:

* `UnitG.ge_rel`: `off σ_2 ≤ off σ_0 + off σ_1 + 1/2` (`x_c ≤ x_a + x_b` for `≥`-add units);
* `UnitG.le_rel`: `(1/2 + off σ_2) + 5/2 ≤ (1/2 + off σ_0) + (1/2 + off σ_1)` (right readings of
  a mirrored `≤`-add unit);
* `UnitG.orient_rel`: `5/2 ≤ (1/2 + off σ_0) + (1/2 + off σ_1)`;
* `UnitG.inv_rel`: `(1/2 + off σ_0) (2 − off σ_1) = 1`.

Proof: the receiver guards are the copies of the base guards (`UnitG.recv_eq`), every point of the
critical zones is seen by a template position of the unit (`UnitG.zone_seen`), and the template
mechanism (`ge_mech`, …) applies in the template frame of the unit.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon Tmpl Vis.Cert
open Corridor (Input place)
open Corridor.Input
open ArtGallery.Sec5.Count (tsysOf uφ)

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {m : ℕ} (hm : m < us.length) {κ : Kind} {G : Set Point} {off : ℕ → ℝ}
  {tg : Fin (tsysOf κ).r → Point}
include hQ

/-- The template frame of the unit. -/
theorem tframe : (tP Q n k m (us[m]'hm)).Simple ∧ (tP Q n k m (us[m]'hm)).InteriorLeft ∧
    ChainAt (tP Q n k m (us[m]'hm)) (tmplV (us[m]'hm).kind) (hQ.tStart hm) ∧
    SepAt (tP Q n k m (us[m]'hm)) (tmplV (us[m]'hm).kind) (hQ.tStart hm)
      (tmplR (us[m]'hm).kind) :=
  ⟨hQ.tmpl_simple hm, hQ.tmpl_ccw hm, hQ.chainAt hm, hQ.sepAt hm⟩

/-- **The receiver guard in the template frame** is the segment guard with the value of the copied
base guard. -/
theorem UnitG.recv_tmpl (hU : UnitG Q n k us m hm κ G off tg) {j : ℕ}
    (hj : j < (unitInput n k m (us[m]'hm)).np) {A B : IPt}
    (hA1 : (A.1 : ℝ) = (tmplD κ : ℝ) *
      (((unitInput n k m (us[m]'hm)).Tt ((unitInput n k m (us[m]'hm)).tau j)).1 : ℝ))
    (hA2 : (A.2 : ℝ) = (tmplD κ : ℝ) *
      (((unitInput n k m (us[m]'hm)).Tt ((unitInput n k m (us[m]'hm)).tau j)).2 : ℝ))
    (hB1 : (B.1 : ℝ) = A.1 + 3 / 2 * (tmplD κ : ℝ)) (hB2 : (B.2 : ℝ) = A.2) :
    (uφ n k m (us[m]'hm)).symm (tg (recvIdx κ ((unitInput n k m (us[m]'hm)).tau j))) =
      segGuard A B (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma j)) := by
  have e := hU.recv_eq hQ hm hj
  obtain hκ := hU.kind
  subst hκ
  rw [e, AffineEquiv.symm_apply_eq, uφ_eq_place]
  have hD : (0 : ℝ) < tmplD (us[m]'hm).kind := by exact_mod_cast tmplD_pos _
  congr 1
  simp only [segGuard, Geometry.lerp, intPoint]
  ext
  · simp only
    rw [hB1, hA1]; field_simp; ring
  · simp only
    rw [hB2, hA2]; field_simp; ring

omit hQ in
/-- **A two-point position** carries a segment guard with a value in `[1/2, 2]`. -/
theorem UnitG.seg_val (hU : UnitG Q n k us m hm κ G off tg) {X : Fin (tsysOf κ).r} {A B : IPt}
    (hX : (tsysOf κ).spot X = [A, B]) :
    ∃ u : ℝ, 1 / 2 ≤ u ∧ u ≤ 2 ∧ (uφ n k m (us[m]'hm)).symm (tg X) = segGuard A B u := by
  obtain ⟨x, hx, e⟩ := hU.tg_mem X
  rw [hX] at hx
  obtain ⟨r, hr0, hr1, rfl⟩ := mem_hull_two hx
  refine ⟨1 / 2 + 3 / 2 * r, by linarith, by linarith, ?_⟩
  rw [← e, AffineEquiv.symm_apply_apply, segGuard]
  congr 1; ring

omit hQ in
/-- A template position: the guard lies on it in the template frame. -/
theorem UnitG.tg_hull (hU : UnitG Q n k us m hm κ G off tg) (X : Fin (tsysOf κ).r) :
    (uφ n k m (us[m]'hm)).symm (tg X) ∈ convexHull ℝ (intSet ((tsysOf κ).spot X)) := by
  obtain ⟨x, hx, e⟩ := hU.tg_mem X
  rw [← e, AffineEquiv.symm_apply_apply]; exact hx

omit hQ in
/-- The zones are in the template box. -/
theorem zone_box {L : List IPt} {D : ℕ}
    (h : ∀ q ∈ L, -(60 * (D : ℤ)) ≤ q.1 ∧ q.1 ≤ 60 * D ∧ -(60 * (D : ℤ)) ≤ q.2 ∧ q.2 ≤ 60 * D) :
    ∀ z ∈ convexHull ℝ (intSet L), |z.1| ≤ 60 * (D : ℝ) ∧ |z.2| ≤ 60 * (D : ℝ) := by
  intro z hz
  obtain ⟨b1, b2, b3, b4⟩ := Count.hull_box h z hz
  push_cast at b1 b2 b3 b4
  exact ⟨abs_le.2 ⟨b1, b2⟩, abs_le.2 ⟨b3, b4⟩⟩

/-- The working data of a unit: number of pairs, receiver indices, receiver data. -/
theorem unit_data (hκ : (us[m]'hm).kind = κ) :
    (unitInput n k m (us[m]'hm)).np = (tmplT κ).length ∧
      (∀ j, (unitInput n k m (us[m]'hm)).tau j = (tmplT κ).length - 1 - j) ∧
      (∀ τ, (unitInput n k m (us[m]'hm)).Tt τ = (tmplT κ).getD τ (0, 0)) ∧
      (∀ j < (tmplT κ).length, (unitInput n k m (us[m]'hm)).sigma j < 4 * n) := by
  have hok := hQ.ok _ (List.getElem_mem hm)
  have hnp : (unitInput n k m (us[m]'hm)).np = (tmplT κ).length := by
    show (us[m]'hm).work.length = _; rw [hok.len, hκ]
  refine ⟨hnp, fun j => by simp only [Input.tau, hnp], fun τ => ?_, fun j hj => ?_⟩
  · show (tmplT (us[m]'hm).kind).getD τ (0, 0) = _; rw [hκ]
  · apply hok.lt
    have hj' : j < (us[m]'hm).work.length := by rw [← hnp] at hj; exact hj
    show (us[m]'hm).work.getD j 0 ∈ (us[m]'hm).work
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact List.getElem_mem _

/-- **A `≥`-add unit** enforces `x_c ≤ x_a + x_b` on its working slots. -/
theorem UnitG.ge_rel {tg : Fin 5 → Point} (hU : UnitG Q n k us m hm .ge G off tg) :
    1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 2) ≤
      (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_data hQ hm hκ
  have hlen : (tmplT .ge).length = 3 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframe hQ hm
  rw [hκ, tmplV_ge] at hC'
  rw [hκ, tmplV_ge] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have o2 := hU.off_mem _ (hσ 2 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-1830338400), (-1455951000)))
    (B := ((-1705542600), (-1455951000))) (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-2163127200), 0))
    (B := ((-2038331400), 0)) (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e2 := hU.recv_tmpl hQ hm (j := 2) (by omega) (A := ((-166394400), (-873570600)))
    (B := ((-41598600), (-873570600))) (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTGE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  rw [htau] at e0 e1 e2
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (2038331400, 0)) (B := (2163127200, 0))
    rfl
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addGEZg))
    (zone_box (by decide +kernel)) (jv := 48) (by decide)
    (by rw [tmplV_ge]; exact ge_zone_sees_g hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addGEZn))
    (zone_box (by decide +kernel)) (jv := 67) (by decide)
    (by rw [tmplV_ge]; exact ge_zone_sees_n hP' hL' hC' hS')
  exact ge_mech hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (by linarith) (by linarith) (fun X => (uφ n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e1 e0 e2 e4 hZg hZn

/-- **A `≤`-add unit** enforces `x_a + x_b ≤ x_c` (right readings: `u_c + 5/2 ≤ u_a + u_b`) on its working slots. -/
theorem UnitG.le_rel {tg : Fin 5 → Point} (hU : UnitG Q n k us m hm (.le) G off tg) :
    1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 2) + 5 / 2 ≤
      (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_data hQ hm hκ
  have hlen : (tmplT .le).length = 3 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframe hQ hm
  rw [hκ, tmplV_le] at hC'
  rw [hκ, tmplV_le] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have o2 := hU.off_mem _ (hσ 2 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-544236000), (-371070000)))
    (B := ((-507129000), (-371070000))) (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-581343000), 0))
    (B := ((-544236000), 0)) (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e2 := hU.recv_tmpl hQ hm (j := 2) (by omega) (A := (12369000, (-259749000)))
    (B := (49476000, (-259749000))) (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTLE, tmplD]) (by norm_num [tmplD]) (by norm_num)
  rw [htau] at e0 e1 e2
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (544236000, 0)) (B := (581343000, 0))
    rfl
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addLEZg))
    (zone_box (by decide +kernel)) (jv := 48) (by decide)
    (by rw [tmplV_le]; exact le_zone_sees_g hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addLEZn))
    (zone_box (by decide +kernel)) (jv := 67) (by decide)
    (by rw [tmplV_le]; exact le_zone_sees_n hP' hL' hC' hS')
  exact le_mech hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (by linarith) (by linarith) (fun X => (uφ n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e1 e0 e2 e4 hZg hZn

/-- **An orientation unit** enforces `5/2 ≤ u_0 + u_1` (right readings of its two slots). -/
theorem UnitG.orient_rel {tg : Fin 5 → Point} (hU : UnitG Q n k us m hm .orient G off tg) :
    5 / 2 ≤ (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_data hQ hm hκ
  have hlen : (tmplT .orient).length = 2 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframe hQ hm
  rw [hκ, tmplV_orient] at hC'
  rw [hκ, tmplV_orient] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-3275342400), (-2605386000)))
    (B := ((-3052023600), (-2605386000))) (by rw [hTt, htau]; norm_num [tmplT, tmplTOR, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTOR, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-3870859200), 0))
    (B := ((-3647540400), 0)) (by rw [hTt, htau]; norm_num [tmplT, tmplTOR, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTOR, tmplD]) (by norm_num [tmplD]) (by norm_num)
  rw [htau] at e0 e1
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (3647540400, 0))
    (B := (3870859200, 0)) rfl
  have e3 : (uφ n k m (us[m]'hm)).symm (tg 1) = addORC := mem_hull_single (hU.tg_hull hm (1 : Fin 5))
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addORZg))
    (zone_box (by decide +kernel)) (jv := 42) (by decide)
    (by rw [tmplV_orient]; exact orient_zone_sees_g hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet addORZn))
    (zone_box (by decide +kernel)) (jv := 61) (by decide)
    (by rw [tmplV_orient]; exact orient_zone_sees_n hP' hL' hC' hS')
  exact orient_mech hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (fun X => (uφ n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e3 e1 e0 e4 hZg hZn

/-- **An inversion unit** enforces `x · y = 1` for the right reading `x = 1/2 + t_0` of its first
slot and the left reading `y = 2 − t_1` of its second slot. -/
theorem UnitG.inv_rel {tg : Fin 3 → Point} (hU : UnitG Q n k us m hm .inv G off tg) :
    (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 0)) *
        (2 - off ((unitInput n k m (us[m]'hm)).sigma 1)) = 1 := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_data hQ hm hκ
  have hlen : (tmplT .inv).length = 2 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframe hQ hm
  rw [hκ, tmplV_inv] at hC'
  rw [hκ, tmplV_inv] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := (250747895200, 0))
    (B := (1002991580800, 0)) (by rw [hTt, htau]; norm_num [tmplT, tmplTInv, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTInv, tmplD]) (by norm_num [tmplD]) (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := (6970791486560, 50149579040))
    (B := (7723035172160, 50149579040)) (by rw [hTt, htau]; norm_num [tmplT, tmplTInv, tmplD])
    (by rw [hTt, htau]; norm_num [tmplT, tmplTInv, tmplD]) (by norm_num [tmplD]) (by norm_num)
  rw [htau] at e0 e1
  set x := 1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 0) with hx
  set y := 2 - off ((unitInput n k m (us[m]'hm)).sigma 1) with hy
  have f0 : segGuard (250747895200, 0) (1002991580800, 0) x = invGp x := by
    simp only [segGuard, Geometry.lerp, intPoint, invGp, invD]; push_cast
    ext <;> simp only <;> ring
  have f1 : segGuard (6970791486560, 50149579040) (7723035172160, 50149579040)
      (1 / 2 + off ((unitInput n k m (us[m]'hm)).sigma 1)) = invGq y := by
    simp only [segGuard, Geometry.lerp, intPoint, invGq, invD, hy]; push_cast
    ext <;> simp only <;> ring
  rw [f0] at e0
  rw [f1] at e1
  have hZu := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet invZu))
    (zone_box (by decide +kernel)) (jv := 14) (by decide)
    (by rw [tmplV_inv]; exact inv_zone_sees_u hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet invZn))
    (zone_box (by decide +kernel)) (jv := 41) (by decide)
    (by rw [tmplV_inv]; exact inv_zone_sees_n hP' hL' hC' hS')
  exact inv_mech hP' hL' hC' hS' (by linarith) (by linarith) (by linarith) (by linarith)
    (fun X => (uφ n k m (us[m]'hm)).symm (tg X)) (hU.tg_hull hm (0 : Fin 3)) e0 e1
    (fun z hz _ => hZu z hz) hZn

end Unit

end ArtGallery.Sec5.Constraint

end
