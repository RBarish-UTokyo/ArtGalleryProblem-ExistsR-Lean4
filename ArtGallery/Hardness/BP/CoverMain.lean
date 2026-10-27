module

public import ArtGallery.Hardness.BP.CoverRegion
public import ArtGallery.Hardness.BP.CoverCanon
public import ArtGallery.Hardness.Sec5.Cover

/-!
# Boundary-point variant: the canonical guards see the whole polygon

As `Sec5/Cover.lean`.  **`canonGuardsBP_sees`**: for `n ≥ 1`, variables `x_i ∈ [1/2, 2]`
satisfying `Φ`, every point of the region of `polyCBP Φ n` is seen by a canonical guard; with
`canonGuardsBP_boundary` the canonical guard set is a guard set on the boundary
(**`canonGuardsBP_guard`**).

The region is the union of its pieces (`CoverM.filled_eq_globU`), and each piece is seen:

* the main hexagon by the base guards (`HexHypBP.hex_coveredBP`);
* the pocket room with bay of slot `σ` by the base guard of `σ` (`sees_pocketRoomBP`; with `one`
  spikes the base guard is the value-`1` point);
* the region of a right unit by its base guards, corridor stationary guards and canonical template
  guards (`CoverU.unit_cover`): the receiver values of the unit are the values of the copied slots
  (`recvVal`), they satisfy the template constraint (`Sec5.Sec5.CoverT.right_cons`), and the base guards
  see the entrance on `x = S` (`HexHypBP.base_sees_rightBP`);
* the region of a left unit likewise in the mirrored polygon (`Sec5.Sec5.CoverT.left_cons`,
  `HexHypBP.base_sees_leftBP`); the mirror image of the base guard of working slot `w` is the base
  guard of slot `4n − 1 − w`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

/-- The number of template positions of a kind. -/
theorem ArtGallery.BP.tsysOfBP_r_eq (k : ArtGallery.Sec5.Kind) :
    (ArtGallery.BP.Count.tsysOfBP k).r = ArtGallery.BP.CoverK.tNumBP k := by
  cases k <;> rfl

namespace ArtGallery.BP.CoverM

open ArtGallery Set Polygon ArtGallery.Sec5 CoverK
open ArtGallery.Sec5.CoverM (sS sTop sXL sS_big umbra_p slotX_real work_mem base_mem hone
  mem_mirror_image)
open ArtGallery.Sec5.Count (mirrorEquiv mirrorEquiv_apply mirrorEquiv_mirrorEquiv)
open ArtGallery.BP.Count (GPosBP UPosBP tsysOfBP sees_polyCBP_mirror)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

variable {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ}

/-! ### The base guards of a corridor -/

theorem recv_tau (left : Bool) (k m : ℕ) (u : UnitSpec) {j : ℕ} (hj : j < u.work.length) :
    recvVal n x left u ((unitInputBP n k m u).tau j) = workVal n x left (u.work.getD j 0) := by
  have : u.work.length - 1 - (unitInputBP n k m u).tau j = j := by
    simp only [Corridor.Input.tau, Corridor.Input.np, unitInputBP]; omega
  simp only [recvVal, this]

theorem sigma_eq (k m : ℕ) (u : UnitSpec) (j : ℕ) :
    (unitInputBP n k m u).sigma j = u.work.getD j 0 := rfl

/-! ### Canonical guards -/

theorem canon_base (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) : basePt n x σ ∈ canonGuardsBP Φ n x := by
  classical
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuardsBP, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨.inl (), (⟨σ, hσ⟩ : Fin (4 * n))⟩, rfl⟩

theorem canon_mem (hn : 0 < n) (X : GPosBP Φ n) : canonPtBP Φ n x X ∈ canonGuardsBP Φ n x := by
  classical
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuardsBP, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨X, rfl⟩

section Main

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (hx : ValsOK n x) (hΦx : ∀ c ∈ Φ, c.Holds x)
include hΦ hn hx hΦx

/-! ### Coverage of the pieces -/

theorem pocket_covered {σ : ℕ} (hσ : σ < 4 * n) {z : Point} (hz : z ∈ pkU Φ n σ) :
    ∃ g ∈ canonGuardsBP Φ n x, (polyCBP Φ n).Sees g z := by
  have hM := mainHypBP hΦ hn
  obtain ⟨b2, b1, b1'⟩ := base_mem hn hx σ
  refine ⟨_, canon_base hn hσ, sees_pocketRoomBP hM.simple hM.ccw (hM.pocket σ hσ)
    (boxSepBP hΦ hn hσ (T := 1) (by have := sS_big (Φ := Φ) (n := n); linarith)) b2 b1 b1'
    (fun h => hone hΦ hn hx hΦx h) hz⟩

theorem right_covered (m : Fin (unitSpecs n Φ).1.length) {z : Point} (hz : z ∈ rU Φ n m) :
    ∃ g ∈ canonGuardsBP Φ n x, (polyCBP Φ n).Sees g z := by
  have hQ := rightSideBP hΦ hn
  have hok : UnitOK n ((unitSpecs n Φ).1[m.1]'m.2) :=
    unitSpecs_ok hΦ _ (List.mem_append_left _ (List.getElem_mem _))
  have hv := fun τ => recvVal_mem hn hx false ((unitSpecs n Φ).1[m.1]'m.2) τ
  have hc := Sec5.CoverT.right_cons hΦ hΦx _ (List.getElem_mem m.2)
  -- the base guard of pair `j` is the canonical base guard of its slot
  have hbase : ∀ j < (unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).np,
      ((unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).umbraR j).p
        (recvVal n x false ((unitSpecs n Φ).1[m.1]'m.2)
          ((unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).tau j) - 1 / 2) =
        basePt n x (((unitSpecs n Φ).1[m.1]'m.2).work.getD j 0) := by
    intro j hj
    rw [umbra_p, recv_tau false _ _ _ hj, sigma_eq, Sec5.CoverT.workVal_right, basePt, slotX_real]
  have hent : ∀ j < (unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).np,
      ∀ w ∈ (unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).entrance,
      (polyCBP Φ n).Sees (((unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).umbraR j).p
        (recvVal n x false ((unitSpecs n Φ).1[m.1]'m.2)
          ((unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).tau j) - 1 / 2)) w := by
    intro j hj w hw
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 hw
    rw [hbase j hj, show w = (sS Φ n, w.2) from Prod.ext e1 rfl]
    obtain ⟨b2, b1, b1'⟩ := base_mem hn hx (((unitSpecs n Φ).1[m.1]'m.2).work.getD j 0)
    exact (hexHypBP hΦ hn).base_sees_rightBP hn (hok.lt _ (work_mem hj)) b2 b1 b1' (by linarith) e3.le
  rcases CoverU.unit_cover hQ m.2 hv hc hent z hz with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | ⟨X, hX, h⟩
  · rw [hbase j hj] at h
    exact ⟨_, canon_base hn (hok.lt _ (work_mem hj)), h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inl m), (.inl ⟨j, hj⟩ : UPosBP n (numC Φ) (unitSpecs n Φ).1 m)⟩,
      h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inl m), (.inr ⟨X, by rw [tsysOfBP_r_eq]; exact hX⟩ :
      UPosBP n (numC Φ) (unitSpecs n Φ).1 m)⟩, h⟩

theorem left_covered (m : Fin (unitSpecs n Φ).2.length) {z : Point} (hz : z ∈ lU Φ n m) :
    ∃ g ∈ canonGuardsBP Φ n x, (polyCBP Φ n).Sees g z := by
  have hQ := leftSideBP hΦ hn
  have hok : UnitOK n ((unitSpecs n Φ).2[m.1]'m.2) :=
    unitSpecs_ok hΦ _ (List.mem_append_right _ (List.getElem_mem _))
  have hv := fun τ => recvVal_mem hn hx true ((unitSpecs n Φ).2[m.1]'m.2) τ
  have hc := Sec5.CoverT.left_cons hΦ hΦx _ (List.getElem_mem m.2)
  rw [lU, mem_mirror_image] at hz
  -- the mirror image of the base guard of pair `j` is the canonical base guard of the slot
  -- `4n − 1 − w`
  have hbase : ∀ j < (unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).np,
      mirrorEquiv n (((unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).umbraR j).p
        (recvVal n x true ((unitSpecs n Φ).2[m.1]'m.2)
          ((unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).tau j) - 1 / 2)) =
        basePt n x (4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0) := by
    intro j hj
    have hw := hok.lt _ (work_mem hj)
    have hc : ((4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0 : ℕ) : ℝ) =
        4 * n - 1 - (((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0 : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [umbra_p, recv_tau true _ _ _ hj, sigma_eq, workVal, mirrorEquiv_apply, basePt,
      slotX_real, hc]
    simp only [ite_true]
    ext <;> simp only
    ring
  have hent : ∀ j < (unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).np,
      ∀ w ∈ (unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).entrance,
      (polyMBP Φ n).Sees (((unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).umbraR j).p
        (recvVal n x true ((unitSpecs n Φ).2[m.1]'m.2)
          ((unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).tau j) - 1 / 2)) w := by
    intro j hj w hw
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 hw
    rw [← sees_polyCBP_mirror, hbase j hj,
      show mirrorEquiv n w = (sXL Φ n, w.2) by rw [mirrorEquiv_apply, e1]; rfl]
    obtain ⟨b2, b1, b1'⟩ := base_mem hn hx (4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0)
    exact (hexHypBP hΦ hn).base_sees_leftBP hn (by omega) b2 b1 b1' (by linarith) e3.le
  have hmir : ∀ g : Point, (polyMBP Φ n).Sees g (mirrorEquiv n z) →
      (polyCBP Φ n).Sees (mirrorEquiv n g) z := fun g h => by
    rw [← sees_polyCBP_mirror, mirrorEquiv_mirrorEquiv] at h; exact h
  rcases CoverU.unit_cover hQ m.2 hv hc hent _ hz with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | ⟨X, hX, h⟩
  · have h' := hmir _ h
    rw [hbase j hj] at h'
    exact ⟨_, canon_base hn (by omega), h'⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inr m), (.inl ⟨j, hj⟩ : UPosBP n (numC Φ) (unitSpecs n Φ).2 m)⟩,
      hmir _ h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inr m), (.inr ⟨X, by rw [tsysOfBP_r_eq]; exact hX⟩ :
      UPosBP n (numC Φ) (unitSpecs n Φ).2 m)⟩,
      hmir _ h⟩

end Main

end ArtGallery.BP.CoverM

namespace ArtGallery.BP

open ArtGallery CoverM
open ArtGallery.Sec5 (ValsOK basePt)
open ArtGallery.Sec5.CoverM (base_mem)

/-- **The canonical guards see the whole polygon**: for `n ≥ 1` and values `x_i ∈ [1/2, 2]`
satisfying `Φ`, every point of the region of `polyCBP Φ n` is seen by a point of
`canonGuardsBP Φ n x`. -/
theorem canonGuardsBP_sees {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2)
    (hΦx : ∀ c ∈ Φ, c.Holds x) :
    ∀ q ∈ (polyCBP Φ n).filled, ∃ g ∈ canonGuardsBP Φ n x, (polyCBP Φ n).Sees g q := by
  intro z hz
  rw [filled_eq_globU hΦ hn] at hz
  rcases hz with (((h | h) | h) | h)
  · obtain ⟨σ, hσ, hs⟩ := (hexHypBP hΦ hn).hex_coveredBP hn (basePt n x)
      (base_mem hn (show ValsOK n x from hx)) z h
    exact ⟨_, canon_base hn hσ, hs⟩
  · obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 h
    exact pocket_covered hΦ hn hx hΦx σ.2 hσ
  · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
    exact right_covered hΦ hn hx hΦx m hm
  · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
    exact left_covered hΦ hn hx hΦx m hm

/-- **The canonical guards form a guard set on the boundary** (`IsGuardSetOnBoundary`). -/
theorem canonGuardsBP_guard {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2)
    (hΦx : ∀ c ∈ Φ, c.Holds x) :
    (polyCBP Φ n).IsGuardSetOnBoundary (canonGuardsBP Φ n x : Set Point) :=
  ⟨canonGuardsBP_boundary hΦ hx hΦx, canonGuardsBP_sees hΦ hn hx hΦx⟩

end ArtGallery.BP

end
