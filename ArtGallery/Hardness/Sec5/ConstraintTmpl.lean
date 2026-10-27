module

public import ArtGallery.Hardness.Sec5.ConstraintUnit

/-!
# Section 5, constraints (v): the mechanism of the four templates

Statements in template coordinates, for an arbitrary simple counter-clockwise polygon `P`
containing the template chain (`ChainAt`) whose other edges avoid the region (`SepAt`).  The guards
of the template positions are given by a function `pt` on the positions (in the order of the
position systems `addGETS`, `addLETS`, `addORTS`, `invTS`); if every point of the critical zones
is seen by one of them, the constraint holds:

* `ge_mech`: `w ≤ u + v` (`u` the value on `r_i`, `v` on `r_j`, `w` on `r_l`);
* `le_mech`: `w + 5/2 ≤ u + v`;
* `orient_mech`: `5/2 ≤ u + v`;
* `inv_mech`: `x y = 1` (`x` on `r_i`, `y` on `r_j`).

Proof: the weak-copy nook gives `u' ≤ u` for the value `u'` on `r'_i` (`add*_nook_iff`), the zone
`Γ` gives the inequality for `u'` (`add*_gamma_iff`); the other positions do not see the zones
(`add*_excl_*`, `inv_g_not_sees_*`).  For each zone we also record a convex piece containing it and
a chain vertex (`*_zone_sees`), which puts the zone into the unit room (`UnitG.zone_seen`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon Tmpl Vis.Cert

/-- A chain vertex in a convex piece of the region sees every point of the piece. -/
theorem sees_of_piece {P : Polygon} {L : List IPt} (hL : convexHull ℝ (intSet L) ⊆ P.filled)
    {x z : Point} (hx : x ∈ convexHull ℝ (intSet L)) (hz : z ∈ convexHull ℝ (intSet L)) :
    P.Sees x z := fun _ hw =>
  hL (Geometry.segment_subset_of_convex (convex_convexHull ℝ _) hx hz hw)

/-- A point of the hull of a single integer point is that point. -/
theorem mem_hull_single {A : IPt} {x : Point} (hx : x ∈ convexHull ℝ (intSet [A])) :
    x = intPoint A := by
  have e : intSet [A] = {intPoint A} := by simp
  rw [e, convexHull_singleton] at hx
  exact hx

/-! ### `ge` -/

section GE

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P addGEV a)
  (hS : SepAt P addGEV a addGER)
include hP hL hC hS

/-- **The `ge` template enforces `w ≤ u + v`.** -/
theorem ge_mech {u u' v w : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2) (hw0 : 1 / 2 ≤ w) (hw1 : w ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet addGEGs)) (h1 : pt 1 = addGEB v)
    (h2 : pt 2 = addGEI u) (h3 : pt 3 = addGEC w) (h4 : pt 4 = addGEA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet addGEZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet addGEZn), ∃ X, P.Sees (pt X) z) : w ≤ u + v := by
  have hcopy : u' ≤ u := by
    refine (addGE_nook_iff hP hL hC hS hu0 hu1 hu0' hu1').1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addGE_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees (addGEB v) z := by rw [← h1]; exact hX
      exact absurd hX' (addGE_excl_Zn_rj hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨2, _⟩, hX => exact Or.inl (by rw [← h2]; exact hX)
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (addGEC w) z := by rw [← h3]; exact hX
      exact absurd hX' (addGE_excl_Zn_rl hP hC _ (segGuard_mem hw0 hw1) z hz)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  have hg : w ≤ u' + v := by
    refine (addGE_gamma_iff hP hL hC hS hu0' hu1' hv0 hv1 hw0 hw1).1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addGE_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inl (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (addGEI u) z := by rw [← h2]; exact hX
      exact absurd hX' (addGE_excl_Zg_ri hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨3, _⟩, hX => exact Or.inr (Or.inr (by rw [← h3]; exact hX))
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)
  linarith

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 48). -/
theorem ge_zone_sees_g : ∀ z ∈ convexHull ℝ (intSet addGEZg), P.Sees (tpt addGEV 48) z :=
  fun _ hz => sees_of_piece (addGEGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 67). -/
theorem ge_zone_sees_n : ∀ z ∈ convexHull ℝ (intSet addGEZn), P.Sees (tpt addGEV 67) z :=
  fun _ hz => sees_of_piece (addGEN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end GE

/-! ### `le` -/

section LE

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P addLEV a)
  (hS : SepAt P addLEV a addLER)
include hP hL hC hS

/-- **The `le` template enforces `w + 5 / 2 ≤ u + v`.** -/
theorem le_mech {u u' v w : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2) (hw0 : 1 / 2 ≤ w) (hw1 : w ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet addLEGs)) (h1 : pt 1 = addLEB v)
    (h2 : pt 2 = addLEI u) (h3 : pt 3 = addLEC w) (h4 : pt 4 = addLEA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet addLEZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet addLEZn), ∃ X, P.Sees (pt X) z) : w + 5 / 2 ≤ u + v := by
  have hcopy : u' ≤ u := by
    refine (addLE_nook_iff hP hL hC hS hu0 hu1 hu0' hu1').1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addLE_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees (addLEB v) z := by rw [← h1]; exact hX
      exact absurd hX' (addLE_excl_Zn_rj hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨2, _⟩, hX => exact Or.inl (by rw [← h2]; exact hX)
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (addLEC w) z := by rw [← h3]; exact hX
      exact absurd hX' (addLE_excl_Zn_rl hP hC _ (segGuard_mem hw0 hw1) z hz)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  have hg : w + 5 / 2 ≤ u' + v := by
    refine (addLE_gamma_iff hP hL hC hS hu0' hu1' hv0 hv1 hw0 hw1).1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addLE_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inl (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (addLEI u) z := by rw [← h2]; exact hX
      exact absurd hX' (addLE_excl_Zg_ri hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨3, _⟩, hX => exact Or.inr (Or.inr (by rw [← h3]; exact hX))
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)
  linarith

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 48). -/
theorem le_zone_sees_g : ∀ z ∈ convexHull ℝ (intSet addLEZg), P.Sees (tpt addLEV 48) z :=
  fun _ hz => sees_of_piece (addLEGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 67). -/
theorem le_zone_sees_n : ∀ z ∈ convexHull ℝ (intSet addLEZn), P.Sees (tpt addLEV 67) z :=
  fun _ hz => sees_of_piece (addLEN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end LE

/-! ### `orient` -/

section OR

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P addORV a)
  (hS : SepAt P addORV a addORR)
include hP hL hC hS

/-- **The `orient` template enforces `5/2 ≤ u + v`.** -/
theorem orient_mech {u u' v : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 2) (hu0' : 1 / 2 ≤ u')
    (hu1' : u' ≤ 2) (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 2)
    (pt : Fin 5 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet addORGs)) (h1 : pt 1 = addORC)
    (h2 : pt 2 = addORB v) (h3 : pt 3 = addORI u) (h4 : pt 4 = addORA u')
    (hΓ : ∀ z ∈ convexHull ℝ (intSet addORZg), ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet addORZn), ∃ X, P.Sees (pt X) z) : 5 / 2 ≤ u + v := by
  have hCp : addORC ∈ convexHull ℝ (intSet addORPs) :=
    subset_convexHull ℝ _ (intPoint_mem_intSet (by simp [addORPs]))
  have hcopy : u' ≤ u := by
    refine (addOR_nook_iff hP hL hC hS hu0 hu1 hu0' hu1').1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addOR_excl_Zn_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX =>
      have hX' : P.Sees addORC z := by rw [← h1]; exact hX
      exact absurd hX' (addOR_excl_Zn_p hP hL hC _ hCp z hz)
    | ⟨2, _⟩, hX =>
      have hX' : P.Sees (addORB v) z := by rw [← h2]; exact hX
      exact absurd hX' (addOR_excl_Zn_rj hP hC _ (segGuard_mem hv0 hv1) z hz)
    | ⟨3, _⟩, hX => exact Or.inl (by rw [← h3]; exact hX)
    | ⟨4, _⟩, hX => exact Or.inr (by rw [← h4]; exact hX)
  have hg : 5 / 2 ≤ u' + v := by
    refine (addOR_gamma_iff hP hL hC hS hu0' hu1' hv0 hv1).1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hΓ z hz
    match X, hX with
    | ⟨0, _⟩, hX => exact absurd hX (addOR_excl_Zg_g hP hL hC _ h0 z hz)
    | ⟨1, _⟩, hX => exact Or.inr (Or.inr (by rw [← h1]; exact hX))
    | ⟨2, _⟩, hX => exact Or.inr (Or.inl (by rw [← h2]; exact hX))
    | ⟨3, _⟩, hX =>
      have hX' : P.Sees (addORI u) z := by rw [← h3]; exact hX
      exact absurd hX' (addOR_excl_Zg_ri hP hC _ (segGuard_mem hu0 hu1) z hz)
    | ⟨4, _⟩, hX => exact Or.inl (by rw [← h4]; exact hX)
  linarith

/-- The zone `Γ` lies in a convex piece with the corner `e_i` (chain vertex 42). -/
theorem orient_zone_sees_g : ∀ z ∈ convexHull ℝ (intSet addORZg), P.Sees (tpt addORV 42) z :=
  fun _ hz => sees_of_piece (addORGA2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `k0` (chain vertex 61). -/
theorem orient_zone_sees_n : ∀ z ∈ convexHull ℝ (intSet addORZn), P.Sees (tpt addORV 61) z :=
  fun _ hz => sees_of_piece (addORN2_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end OR

/-! ### `inv` -/

section Inv

variable {P : Polygon} {a : ℕ} (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P invV a)
  (hS : SepAt P invV a Tmpl.invR)
include hP hL hC hS

/-- **The `inv` template enforces `x y = 1`.** -/
theorem inv_mech {x y : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 2)
    (pt : Fin 3 → Point) (h0 : pt 0 ∈ convexHull ℝ (intSet invGs)) (h1 : pt 1 = invGp x)
    (h2 : pt 2 = invGq y)
    (hU : ∀ z ∈ convexHull ℝ (intSet invZu), 0 < invLu.val z → ∃ X, P.Sees (pt X) z)
    (hN : ∀ z ∈ convexHull ℝ (intSet invZn), ∃ X, P.Sees (pt X) z) : x * y = 1 := by
  have h0' : pt 0 = intPoint (cv invV 36) := by
    have e : cv invV 36 = (8023932646400, 3396868759800) := by decide +kernel
    rw [mem_hull_single h0, e]
  have hu : x * y ≤ 1 := by
    refine (inv_umbra_iff hP hL hC hS hx0 hx1 hy0 hy1).1 fun z hz hLz => ?_
    obtain ⟨X, hX⟩ := hU z hz hLz
    match X, hX with
    | ⟨0, _⟩, hX =>
      have hX' : P.Sees (intPoint (cv invV 36)) z := by rw [← h0']; exact hX
      exact absurd hX' (inv_g_not_sees_umbra hP hL hC hLz)
    | ⟨1, _⟩, hX => exact Or.inl (by rw [← h1]; exact hX)
    | ⟨2, _⟩, hX => exact Or.inr (by rw [← h2]; exact hX)
  have hn : 1 ≤ x * y := by
    refine (inv_nook_iff hP hL hC hS hx0 hx1 hy0 hy1).1 fun z hz => ?_
    obtain ⟨X, hX⟩ := hN z hz
    match X, hX with
    | ⟨0, _⟩, hX =>
      have hX' : P.Sees (intPoint (cv invV 36)) z := by rw [← h0']; exact hX
      exact absurd hX' (inv_g_not_sees_nook hP hL hC z hz)
    | ⟨1, _⟩, hX => exact Or.inl (by rw [← h1]; exact hX)
    | ⟨2, _⟩, hX => exact Or.inr (by rw [← h2]; exact hX)
  linarith

/-- The umbra zone lies in a convex piece with the shadow corner `ξ0` (chain vertex 14). -/
theorem inv_zone_sees_u : ∀ z ∈ convexHull ℝ (intSet invZu), P.Sees (tpt invV 14) z :=
  fun _ hz => sees_of_piece (invBp_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

/-- The nook zone lies in a convex piece with the shadow corner `ξ2` (chain vertex 41). -/
theorem inv_zone_sees_n : ∀ z ∈ convexHull ℝ (intSet invZn), P.Sees (tpt invV 41) z :=
  fun _ hz => sees_of_piece (invBn_sub hP hL hC hS)
    (subset_convexHull ℝ _ (intPoint_mem_intSet (by decide +kernel)))
    (hull_subset_hull_of_all (by decide +kernel) hz)

end Inv

end ArtGallery.Sec5.Constraint

end
