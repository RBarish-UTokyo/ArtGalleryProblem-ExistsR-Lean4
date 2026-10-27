module

public import ArtGallery.Hardness.BP.ConstraintUnit

/-!
# Boundary-point variant, constraints (v): the relation enforced by one unit

**The mechanism of the four templates** in template coordinates (for an arbitrary simple
counter-clockwise polygon `P` containing the template chain with its other edges avoiding the
region), with the guards of the template positions given by a function `pt` on the positions
(order of `Count.tsysOfBP`: `ge`, `le`: `g, B, W, C, A`; `orient`: `g, p, B, W, A`;
`inv`: `g, r_i, r_j`).  If every point of the critical zones is seen by one of them, the
constraint holds (`ge_mechBP`: `w ≤ u + v`, `le_mechBP`: `w + 5/2 ≤ u + v`, `orient_mechBP`:
`5/2 ≤ u + v` with `u` on `W`, `v` on `B`, `w` on `C`; `inv_mechBP`: `x y = 1`).  Proof: the other
positions do not see the zones (`bp*_excl_*`, `bpInv_g_not_sees_*`), and the weak copy
`u_A ≤ u_W` together with `Γ` gives the relation (`bp*_relation`, `bpInv_umbra_iff`,
`bpInv_nook_iff`).

**The relation of a unit** (as `Sec5/ConstraintKinds.lean`): for a unit `m` of a side and guards
`UnitGBP` seen from it, in terms of the offsets of its working slots `σ_j`:

* `UnitGBP.ge_rel`: `(1/2 + off σ_2) ≤ (1/2 + off σ_0) + (1/2 + off σ_1)`;
* `UnitGBP.le_rel`: `(1/2 + off σ_2) + 5/2 ≤ (1/2 + off σ_0) + (1/2 + off σ_1)`;
* `UnitGBP.orient_rel`: `5/2 ≤ (1/2 + off σ_0) + (1/2 + off σ_1)`;
* `UnitGBP.inv_rel`: `(1/2 + off σ_0) (2 − off σ_1) = 1`.

The receivers of pair `j` are `τ = np − 1 − j`: for `ge`, `le` pair `0` is `B`, pair `1` is `W`,
pair `2` is `C`; for `orient` pair `0` is `B`, pair `1` is `W`; for `inv` pair `0` is `r_i`, pair
`1` is `r_j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.Constraint

open ArtGallery Set Polygon Sec5.Tmpl Vis.Cert BP.Tmpl
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input place)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Sec5.Constraint (sees_of_piece mem_hull_single mem_hull_two zone_box)
open ArtGallery.BP.Count (tsysOfBP uφBP tmplTBP_length)

/-! ### The template mechanisms -/

section GE

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpGEV a)
  (hS : SepAt P bpGEV a bpGER)
include hP hL hC hS

/-- **The `ge` template enforces `w ≤ u + v`** (`u` on `W`, `v` on `B`, `w` on `C`). -/
theorem ge_mechBP {u u' v w : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2) (hw0 : 1 / 2 ≤ w) (hw1 : w ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet bpGEGs)) (h1 : pt 1 = bpGEB v)
    (h2 : pt 2 = bpGEW u) (h3 : pt 3 = bpGEC w) (h4 : pt 4 = bpGEA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet bpGEZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet bpGEZn), ∃ X, P.Sees (pt X) z) : w ≤ u + v := by
  refine bpGE_relation hP hL hC hS hu0 hu1 hu0' hu1' hv0 hv1 hw0 hw1 (fun z hz => ?_)
    (fun z hz => ?_)
  · obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpGE_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees (bpGEB v) z := by rw [← h1]; exact hX
      exact absurd hX' (bpGE_excl_Zn_B hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨2, _⟩, hX => exact Or.inl (by rw [← h2]; exact hX)
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (bpGEC w) z := by rw [← h3]; exact hX
      exact absurd hX' (bpGE_excl_Zn_C hP hC _ (segGuard_mem hw0 hw1) z hz)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  · obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpGE_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inl (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (bpGEW u) z := by rw [← h2]; exact hX
      exact absurd hX' (bpGE_excl_Zg_W hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨3, _⟩, hX => exact Or.inr (Or.inr (by rw [← h3]; exact hX))
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 45). -/
theorem ge_zone_sees_gBP : ∀ z ∈ convexHull ℝ (intSet bpGEZg), P.Sees (tpt bpGEV 45) z :=
  fun _ hz => sees_of_piece (bpGEGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 62). -/
theorem ge_zone_sees_nBP : ∀ z ∈ convexHull ℝ (intSet bpGEZn), P.Sees (tpt bpGEV 62) z :=
  fun _ hz => sees_of_piece (bpGEN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end GE

section LE

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpLEV a)
  (hS : SepAt P bpLEV a bpLER)
include hP hL hC hS

/-- **The `le` template enforces `w + 5/2 ≤ u + v`** (`u` on `W`, `v` on `B`, `w` on `C`). -/
theorem le_mechBP {u u' v w : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2) (hw0 : 1 / 2 ≤ w) (hw1 : w ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet bpLEGs)) (h1 : pt 1 = bpLEB v)
    (h2 : pt 2 = bpLEW u) (h3 : pt 3 = bpLEC w) (h4 : pt 4 = bpLEA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet bpLEZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet bpLEZn), ∃ X, P.Sees (pt X) z) : w + 5 / 2 ≤ u + v := by
  refine bpLE_relation hP hL hC hS hu0 hu1 hu0' hu1' hv0 hv1 hw0 hw1 (fun z hz => ?_)
    (fun z hz => ?_)
  · obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpLE_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees (bpLEB v) z := by rw [← h1]; exact hX
      exact absurd hX' (bpLE_excl_Zn_B hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨2, _⟩, hX => exact Or.inl (by rw [← h2]; exact hX)
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (bpLEC w) z := by rw [← h3]; exact hX
      exact absurd hX' (bpLE_excl_Zn_C hP hC _ (segGuard_mem hw0 hw1) z hz)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  · obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpLE_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inl (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (bpLEW u) z := by rw [← h2]; exact hX
      exact absurd hX' (bpLE_excl_Zg_W hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨3, _⟩, hX => exact Or.inr (Or.inr (by rw [← h3]; exact hX))
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 45). -/
theorem le_zone_sees_gBP : ∀ z ∈ convexHull ℝ (intSet bpLEZg), P.Sees (tpt bpLEV 45) z :=
  fun _ hz => sees_of_piece (bpLEGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 62). -/
theorem le_zone_sees_nBP : ∀ z ∈ convexHull ℝ (intSet bpLEZn), P.Sees (tpt bpLEV 62) z :=
  fun _ hz => sees_of_piece (bpLEN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end LE

section OR

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpORV a)
  (hS : SepAt P bpORV a bpORR)
include hP hL hC hS

/-- **The `orient` template enforces `5/2 ≤ u + v`** (`u` on `W`, `v` on `B`). -/
theorem orient_mechBP {u u' v : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet bpORGs)) (h1 : pt 1 = bpORC)
    (h2 : pt 2 = bpORB v) (h3 : pt 3 = bpORW u) (h4 : pt 4 = bpORA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet bpORZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet bpORZn), ∃ X, P.Sees (pt X) z) : 5 / 2 ≤ u + v := by
  have hCp : bpORC ∈ convexHull ℝ (intSet bpORPs) :=
    subset_convexHull ℝ _ (intPoint_mem_intSet (by simp [bpORPs]))
  refine bpOR_relation hP hL hC hS hu0 hu1 hu0' hu1' hv0 hv1 (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpOR_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees bpORC z := by rw [← h1]; exact hX
      exact absurd hX' (bpOR_excl_Zn_p hP hL hC _ hCp z hz)
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (bpORB v) z := by rw [← h2]; exact hX
      exact absurd hX' (bpOR_excl_Zn_B hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨3, _⟩, hX => exact Or.inl (by rw [← h3]; exact hX)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  · obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (bpOR_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inr (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX => exact Or.inr (Or.inl (by rw [← h2]; exact hX))
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (bpORW u) z := by rw [← h3]; exact hX
      exact absurd hX' (bpOR_excl_Zg_W hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 41). -/
theorem orient_zone_sees_gBP : ∀ z ∈ convexHull ℝ (intSet bpORZg), P.Sees (tpt bpORV 41) z :=
  fun _ hz => sees_of_piece (bpORGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 58). -/
theorem orient_zone_sees_nBP : ∀ z ∈ convexHull ℝ (intSet bpORZn), P.Sees (tpt bpORV 58) z :=
  fun _ hz => sees_of_piece (bpORN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end OR

section Inv

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a)
  (hS : SepAt P bpInvV a bpInvR)
include hP hL hC hS

/-- **The `inv` template enforces `x y = 1`** (`x` on `r_i`, `y` on `r_j`). -/
theorem inv_mechBP {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (pt : Fin 3 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet bpInvGs)) (h1 : pt 1 = bpInvGp x)
    (h2 : pt 2 = bpInvGq y)
    (hU : ∀ z ∈ convexHull ℝ (intSet bpInvZu), 0 < bpInvLu.val z → ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet bpInvZn), ∃ X, P.Sees (pt X) z) : x * y = 1 := by
  have h0' : pt 0 = intPoint (cv bpInvV 32) := by
    rw [bpInvGs_eq] at h0
    exact mem_hull_single h0
  have hu : x * y ≤ 1 := by
    refine (bpInv_umbra_iff hP hL hC hS hx0 hx1 hy0 hy1).1 fun z hz hLz => ?_
    obtain ⟨X, hX⟩ := hU z hz hLz
    match X, hX with
    | ⟨0, _⟩, hX =>
      have hX' : P.Sees (intPoint (cv bpInvV 32)) z := by rw [← h0']; exact hX
      exact absurd hX' (bpInv_g_not_sees_umbra hP hL hC hLz)
    | ⟨1, _⟩, hX => exact Or.inl (by rw [← h1]; exact hX)
    | ⟨2, _⟩, hX => exact Or.inr (by rw [← h2]; exact hX)
  have hn : 1 ≤ x * y := by
    refine (bpInv_nook_iff hP hL hC hS hx0 hx1 hy0 hy1).1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX =>
      have hX' : P.Sees (intPoint (cv bpInvV 32)) z := by rw [← h0']; exact hX
      exact absurd hX' (bpInv_g_not_sees_nook hP hL hC z hz)
    | ⟨1, _⟩, hX => exact Or.inl (by rw [← h1]; exact hX)
    | ⟨2, _⟩, hX => exact Or.inr (by rw [← h2]; exact hX)
  linarith

/-- The umbra zone lies in a convex piece with the shadow corner `ξ0` (chain vertex 12). -/
theorem inv_zone_sees_uBP : ∀ z ∈ convexHull ℝ (intSet bpInvZu), P.Sees (tpt bpInvV 12) z :=
  fun _ hz => sees_of_piece (bpInvBp_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `ξ2` (chain vertex 37). -/
theorem inv_zone_sees_nBP : ∀ z ∈ convexHull ℝ (intSet bpInvZn), P.Sees (tpt bpInvV 37) z :=
  fun _ hz => sees_of_piece (bpInvBn_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end Inv

/-! ### The relation of one unit -/

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length) {κ : Kind} {G : Set Point} {off : ℕ → ℝ}
  {tg : Fin (tsysOfBP κ).r → Point}
include hQ

/-- The template frame of the unit. -/
theorem tframeBP : (tPBP Q n k m (us[m]'hm)).Simple ∧ (tPBP Q n k m (us[m]'hm)).InteriorLeft ∧
    ChainAt (tPBP Q n k m (us[m]'hm)) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm) ∧
    SepAt (tPBP Q n k m (us[m]'hm)) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm)
      (tmplRBP (us[m]'hm).kind) :=
  ⟨hQ.tmpl_simple hm, hQ.tmpl_ccw hm, hQ.chainAt hm, hQ.sepAt hm⟩

/-- **The receiver guard in the template frame** is the segment guard with the value of the copied
base guard. -/
theorem UnitGBP.recv_tmpl (hU : UnitGBP Q n k us m hm κ G off tg) {j : ℕ}
    (hj : j < (unitInputBP n k m (us[m]'hm)).np) {A B : IPt}
    (hA1 : (A.1 : ℝ) = (tmplDBP κ : ℝ) *
      (((unitInputBP n k m (us[m]'hm)).Tt ((unitInputBP n k m (us[m]'hm)).tau j)).1 : ℝ))
    (hA2 : (A.2 : ℝ) = (tmplDBP κ : ℝ) *
      (((unitInputBP n k m (us[m]'hm)).Tt ((unitInputBP n k m (us[m]'hm)).tau j)).2 : ℝ))
    (hB1 : (B.1 : ℝ) = A.1 + 3 / 2 * (tmplDBP κ : ℝ)) (hB2 : (B.2 : ℝ) = A.2) :
    (uφBP n k m (us[m]'hm)).symm (tg (recvIdxBP κ ((unitInputBP n k m (us[m]'hm)).tau j))) =
      segGuard A B (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma j)) := by
  have e := hU.recv_eq hQ hm hj
  obtain hκ := hU.kind
  subst hκ
  rw [e, AffineEquiv.symm_apply_eq, uφBP_eq_place]
  have hD : (0 : ℝ) < tmplDBP (us[m]'hm).kind := by exact_mod_cast tmplDBP_pos _
  congr 1
  simp only [segGuard, Geometry.lerp, intPoint]
  ext
  · simp only
    rw [hB1, hA1]; field_simp; ring
  · simp only
    rw [hB2, hA2]; field_simp; ring

omit hQ in
/-- **A two-point position** carries a segment guard with a value in `[1/2, 2]`. -/
theorem UnitGBP.seg_val (hU : UnitGBP Q n k us m hm κ G off tg) {X : Fin (tsysOfBP κ).r}
    {A B : IPt} (hX : (tsysOfBP κ).spot X = [A, B]) :
    ∃ u : ℝ, 1 / 2 ≤ u ∧ u ≤ 2 ∧ (uφBP n k m (us[m]'hm)).symm (tg X) = segGuard A B u := by
  obtain ⟨x, hx, e⟩ := hU.tg_mem X
  rw [hX] at hx
  obtain ⟨r, hr0, hr1, rfl⟩ := mem_hull_two hx
  refine ⟨1 / 2 + 3 / 2 * r, by linarith, by linarith, ?_⟩
  rw [← e, AffineEquiv.symm_apply_apply, segGuard]
  congr 1; ring

omit hQ in
/-- A template position: the guard lies on it in the template frame. -/
theorem UnitGBP.tg_hull (hU : UnitGBP Q n k us m hm κ G off tg) (X : Fin (tsysOfBP κ).r) :
    (uφBP n k m (us[m]'hm)).symm (tg X) ∈ convexHull ℝ (intSet ((tsysOfBP κ).spot X)) := by
  obtain ⟨x, hx, e⟩ := hU.tg_mem X
  rw [← e, AffineEquiv.symm_apply_apply]; exact hx

/-- The working data of a unit: number of pairs, receiver indices, receiver data. -/
theorem unit_dataBP (hκ : (us[m]'hm).kind = κ) :
    (unitInputBP n k m (us[m]'hm)).np = (tmplTBP κ).length ∧
      (∀ j, (unitInputBP n k m (us[m]'hm)).tau j = (tmplTBP κ).length - 1 - j) ∧
      (∀ τ, (unitInputBP n k m (us[m]'hm)).Tt τ = (tmplTBP κ).getD τ (0, 0)) ∧
      (∀ j < (tmplTBP κ).length, (unitInputBP n k m (us[m]'hm)).sigma j < 4 * n) := by
  have hok := hQ.ok _ (List.getElem_mem hm)
  have hnp : (unitInputBP n k m (us[m]'hm)).np = (tmplTBP κ).length := by
    show (us[m]'hm).work.length = _; rw [hok.len, ← hκ, tmplTBP_length]
  refine ⟨hnp, fun j => by simp only [Input.tau, hnp], fun τ => ?_, fun j hj => ?_⟩
  · show (tmplTBP (us[m]'hm).kind).getD τ (0, 0) = _; rw [hκ]
  · apply hok.lt
    have hj' : j < (us[m]'hm).work.length := by rw [← hnp] at hj; exact hj
    show (us[m]'hm).work.getD j 0 ∈ (us[m]'hm).work
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact List.getElem_mem _

/-- **A `≥`-add unit** enforces `x_c ≤ x_a + x_b` on its working slots. -/
theorem UnitGBP.ge_rel {tg : Fin 5 → Point} (hU : UnitGBP Q n k us m hm .ge G off tg) :
    1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 2) ≤
      (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_dataBP hQ hm hκ
  have hlen : (tmplTBP .ge).length = 3 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframeBP hQ hm
  rw [hκ, tmplVBP_ge] at hC'
  rw [hκ, tmplVBP_ge] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have o2 := hU.off_mem _ (hσ 2 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-10996800), 0))
    (B := ((-10579200), 0)) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-6124800), (-1113600)))
    (B := ((-5707200), (-1113600))) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e2 := hU.recv_tmpl hQ hm (j := 2) (by omega) (A := ((-556800), (-2923200)))
    (B := ((-139200), (-2923200))) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTGEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  rw [htau] at e0 e1 e2
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (10579200, 0))
    (B := (10996800, 0)) rfl
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpGEZg))
    (zone_box (by decide +kernel)) (jv := 45) (by decide)
    (by rw [tmplVBP_ge]; exact ge_zone_sees_gBP hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpGEZn))
    (zone_box (by decide +kernel)) (jv := 62) (by decide)
    (by rw [tmplVBP_ge]; exact ge_zone_sees_nBP hP' hL' hC' hS')
  have := ge_mechBP hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (by linarith) (by linarith) (fun X => (uφBP n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e0 e1 e2 e4 hZg hZn
  linarith

/-- **A `≤`-add unit** enforces `x_a + x_b ≤ x_c` (right readings: `u_c + 5/2 ≤ u_a + u_b`) on
its working slots. -/
theorem UnitGBP.le_rel {tg : Fin 5 → Point} (hU : UnitGBP Q n k us m hm .le G off tg) :
    1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 2) + 5 / 2 ≤
      (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_dataBP hQ hm hκ
  have hlen : (tmplTBP .le).length = 3 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframeBP hQ hm
  rw [hκ, tmplVBP_le] at hC'
  rw [hκ, tmplVBP_le] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have o2 := hU.off_mem _ (hσ 2 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-13142400), 0))
    (B := ((-12609600), 0)) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-7814400), (-532800)))
    (B := ((-7281600), (-532800))) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e2 := hU.recv_tmpl hQ hm (j := 2) (by omega) (A := (177600, (-3729600)))
    (B := (710400, (-3729600))) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTLEBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  rw [htau] at e0 e1 e2
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (12609600, 0))
    (B := (13142400, 0)) rfl
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpLEZg))
    (zone_box (by decide +kernel)) (jv := 45) (by decide)
    (by rw [tmplVBP_le]; exact le_zone_sees_gBP hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpLEZn))
    (zone_box (by decide +kernel)) (jv := 62) (by decide)
    (by rw [tmplVBP_le]; exact le_zone_sees_nBP hP' hL' hC' hS')
  have := le_mechBP hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (by linarith) (by linarith) (fun X => (uφBP n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e0 e1 e2 e4 hZg hZn
  linarith

/-- **An orientation unit** enforces `5/2 ≤ u_0 + u_1` (right readings of its two slots). -/
theorem UnitGBP.orient_rel {tg : Fin 5 → Point} (hU : UnitGBP Q n k us m hm .orient G off tg) :
    5 / 2 ≤ (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 0)) +
        (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 1)) := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_dataBP hQ hm hκ
  have hlen : (tmplTBP .orient).length = 2 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframeBP hQ hm
  rw [hκ, tmplVBP_orient] at hC'
  rw [hκ, tmplVBP_orient] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := ((-10996800), 0))
    (B := ((-10579200), 0)) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTORBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTORBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := ((-6124800), (-1113600)))
    (B := ((-5707200), (-1113600))) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTORBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTORBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  rw [htau] at e0 e1
  obtain ⟨u', hu0', hu1', e4⟩ := hU.seg_val hm (X := (4 : Fin 5)) (A := (10579200, 0))
    (B := (10996800, 0)) rfl
  have e3 : (uφBP n k m (us[m]'hm)).symm (tg 1) = bpORC :=
    mem_hull_single (hU.tg_hull hm (1 : Fin 5))
  have hZg := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpORZg))
    (zone_box (by decide +kernel)) (jv := 41) (by decide)
    (by rw [tmplVBP_orient]; exact orient_zone_sees_gBP hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpORZn))
    (zone_box (by decide +kernel)) (jv := 58) (by decide)
    (by rw [tmplVBP_orient]; exact orient_zone_sees_nBP hP' hL' hC' hS')
  have := orient_mechBP hP' hL' hC' hS' (by linarith) (by linarith) hu0' hu1' (by linarith)
    (by linarith) (fun X => (uφBP n k m (us[m]'hm)).symm (tg X))
    (hU.tg_hull hm (0 : Fin 5)) e3 e0 e1 e4 hZg hZn
  linarith

/-- **An inversion unit** enforces `x · y = 1` for the right reading `x = 1/2 + t_0` of its first
slot and the left reading `y = 2 − t_1` of its second slot. -/
theorem UnitGBP.inv_rel {tg : Fin 3 → Point} (hU : UnitGBP Q n k us m hm .inv G off tg) :
    (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 0)) *
        (2 - off ((unitInputBP n k m (us[m]'hm)).sigma 1)) = 1 := by
  have hκ := hU.kind
  obtain ⟨hnp, htau, hTt, hσ⟩ := unit_dataBP hQ hm hκ
  have hlen : (tmplTBP .inv).length = 2 := rfl
  rw [hlen] at hnp htau hσ
  obtain ⟨hP', hL', hC', hS'⟩ := tframeBP hQ hm
  rw [hκ, tmplVBP_inv] at hC'
  rw [hκ, tmplVBP_inv] at hS'
  have o0 := hU.off_mem _ (hσ 0 (by norm_num))
  have o1 := hU.off_mem _ (hσ 1 (by norm_num))
  have e0 := hU.recv_tmpl hQ hm (j := 0) (by omega) (A := (1504487371200, 0))
    (B := (6017949484800, 0)) (by rw [hTt, htau]; norm_num [tmplTBP, tmplTInvBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTInvBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  have e1 := hU.recv_tmpl hQ hm (j := 1) (by omega) (A := (41824748919360, 300897474240))
    (B := (46338211032960, 300897474240))
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTInvBP, tmplDBP])
    (by rw [hTt, htau]; norm_num [tmplTBP, tmplTInvBP, tmplDBP]) (by norm_num [tmplDBP])
    (by norm_num)
  rw [htau] at e0 e1
  set x := 1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 0) with hx
  set y := 2 - off ((unitInputBP n k m (us[m]'hm)).sigma 1) with hy
  have f0 : segGuard (1504487371200, 0) (6017949484800, 0) x = bpInvGp x := by
    simp only [segGuard, Geometry.lerp, intPoint, bpInvGp, bpInvD]; push_cast
    ext <;> simp only <;> ring
  have f1 : segGuard (41824748919360, 300897474240) (46338211032960, 300897474240)
      (1 / 2 + off ((unitInputBP n k m (us[m]'hm)).sigma 1)) = bpInvGq y := by
    simp only [segGuard, Geometry.lerp, intPoint, bpInvGq, bpInvD, hy]; push_cast
    ext <;> simp only <;> ring
  rw [f0] at e0
  rw [f1] at e1
  have hZu := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpInvZu))
    (zone_box (by decide +kernel)) (jv := 12) (by decide)
    (by rw [tmplVBP_inv]; exact inv_zone_sees_uBP hP' hL' hC' hS')
  have hZn := hU.zone_seen hQ hm (Z := convexHull ℝ (intSet bpInvZn))
    (zone_box (by decide +kernel)) (jv := 37) (by decide)
    (by rw [tmplVBP_inv]; exact inv_zone_sees_nBP hP' hL' hC' hS')
  exact inv_mechBP hP' hL' hC' hS' (by linarith) (by linarith) (by linarith) (by linarith)
    (fun X => (uφBP n k m (us[m]'hm)).symm (tg X)) (hU.tg_hull hm (0 : Fin 3)) e0 e1
    (fun z hz _ => hZu z hz) hZn

end Unit

end ArtGallery.BP.Constraint

end
