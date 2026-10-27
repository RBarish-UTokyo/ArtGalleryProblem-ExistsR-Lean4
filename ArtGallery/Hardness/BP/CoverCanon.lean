module

public import ArtGallery.Hardness.BP.CoverKind
public import ArtGallery.Hardness.BP.Count
public import ArtGallery.Hardness.Sec5.CoverCanon

/-!
# Boundary-point variant: the canonical guards of an assignment

As `Sec5/CoverCanon.lean` (`docs/boundary_point/design.md` §3.4).  For an assignment `x : ℕ → ℝ`
(values in `[1/2, 2]`) every guard position `X` of the global polygon (`Count.GPosBP`) receives a
canonical point `canonPtBP Φ n x X`:

* base slot `σ`: the Section 5 point `basePt n x σ = (27σ/2 + slotVal σ − 1/2, 0)` on the floor of
  the bay of `σ` (with `one` spikes: the value-`1` point);
* a corridor stationary guard: the point `p_k` itself;
* a template position of a unit: the canonical template guard `CoverK.tGuardBP` for the receiver
  values `recvVal` (the values of the copied slots, as in Section 5), placed by `Count.uφBP`; the
  weak copy `A` gets the value of `W`; left units are mirrored.

Main results:

* `canonPtBP_mem_spot`: the canonical point of `X` lies on the position `X`
  (`Count.gPosSpotBP X`), hence on the boundary;
* **`canonGuardsBP_card`**: the canonical guard set has `numGuardsBP Φ n` points (distinct
  positions are disjoint, `Count.gPosSpotBP_disjoint`);
* **`canonGuardsBP_boundary`**: it lies on the boundary of `polyCBP Φ n`;
* **`canonGuardsBP_mem`**: it contains `(x_i + d_i, 0)`, `d_i = shift i = 27i/2 − 1/2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl CoverK
open ArtGallery.Sec5 (Kind UnitSpec numC unitSpecs slotOne slotX slotVal basePt recvVal ValsOK
  slotVal_mem recvVal_mem basePt_mem holds_one shift triangle0)
open ArtGallery.Sec5.Count (mirrorEquiv baseSeg)
open ArtGallery.BP.Count (GPosBP UPosBP uφBP tsysOfBP gPosSpotBP gPosSpotBP_main_eq
  gPosSpotBP_disjoint gPosSpotBP_subset_boundary card_posBP)

/-! ### The canonical template guards lie on their positions -/

/-- The canonical template guards lie on their template positions. -/
theorem tGuardBP_mem (k : Kind) {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2)
    (X : Fin (tsysOfBP k).r) :
    tGuardBP k v X ∈ convexHull ℝ (intSet ((tsysOfBP k).spot X)) := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  cases k
  · change Fin 5 at X
    fin_cases X
    · exact Tmpl.bpOR_g_mem
    · exact Tmpl.bpOR_p_mem
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h0.1 h0.2
  · change Fin 5 at X
    fin_cases X
    · exact Tmpl.bpGE_g_mem
    · exact segGuard_mem h2.1 h2.2
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h1.1 h1.2
  · change Fin 5 at X
    fin_cases X
    · exact Tmpl.bpLE_g_mem
    · exact segGuard_mem h2.1 h2.2
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h1.1 h1.2
  · change Fin 3 at X
    fin_cases X
    · exact Tmpl.bpInv_g_mem
    · exact Tmpl.bpInvGp_mem h1.1 h1.2
    · exact Tmpl.bpInvGq_mem (by linarith) (by linarith)

/-! ### The canonical points of the positions -/

/-- The canonical point of a position of a unit (working frame): the corridor stationary guard
`p_k`, or the placed canonical template guard. -/
noncomputable def unitPtBP (n : ℕ) (x : ℕ → ℝ) (left : Bool) (k m : ℕ) (u : UnitSpec) :
    Fin (unitInputBP n k m u).np ⊕ Fin (tsysOfBP u.kind).r → Point :=
  Sum.elim (fun j => ratPoint ((unitInputBP n k m u).sgPt j))
    (fun X => uφBP n k m u (tGuardBP u.kind (recvVal n x left u) X))

/-- **The canonical point of a position** of the global polygon. -/
noncomputable def canonPtBP (Φ : List ETRINV.Constraint) (n : ℕ) (x : ℕ → ℝ) : GPosBP Φ n → Point
  | ⟨.inl _, σ⟩ => basePt n x (show Fin (4 * n) from σ)
  | ⟨.inr (.inl i), X⟩ => unitPtBP n x false (numC Φ) i (unitSpecs n Φ).1[i] X
  | ⟨.inr (.inr i), X⟩ => mirrorEquiv n (unitPtBP n x true (numC Φ) i (unitSpecs n Φ).2[i] X)

/-- **The canonical guard set** of an assignment `x` (for `n = 0`: the vertex `(0, 0)` of the
triangle). -/
noncomputable def canonGuardsBP (Φ : List ETRINV.Constraint) (n : ℕ) (x : ℕ → ℝ) : Finset Point :=
  by classical exact if n = 0 then {(0, 0)} else Finset.univ.image (canonPtBP Φ n x)

/-! ### The canonical points lie on their positions -/

section Spot

variable {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ}

theorem unitPtBP_mem (hn : 0 < n) (hx : ValsOK n x) (left : Bool) (k m : ℕ) (u : UnitSpec)
    (X : Fin (unitInputBP n k m u).np ⊕ Fin (tsysOfBP u.kind).r) :
    unitPtBP n x left k m u X ∈ (Count.uSysBP n k m u).Spot X := by
  rcases X with j | X
  · exact rfl
  · exact ⟨_, tGuardBP_mem u.kind (fun τ => recvVal_mem hn hx left u τ) X, rfl⟩

/-- **The canonical point of `X` lies on the position `X`.** -/
theorem canonPtBP_mem_spot (hn : 0 < n) (hx : ValsOK n x) (hΦx : ∀ c ∈ Φ, c.Holds x)
    (X : GPosBP Φ n) : canonPtBP Φ n x X ∈ gPosSpotBP X := by
  rcases X with ⟨_ | i | i, X⟩
  · change Fin (4 * n) at X
    rw [gPosSpotBP_main_eq]
    split_ifs with h
    · have hσ : (X : ℕ) < n := by
        simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
      have h1 := holds_one hΦx h
      have hlt : (X : ℕ) < 3 * n := by omega
      show basePt n x X ∈ _
      simp only [basePt, slotVal, hlt, ite_true, Nat.mod_eq_of_lt hσ, h1, mem_singleton_iff]
      ext <;> norm_num
    · exact basePt_mem hn hx X
  · exact unitPtBP_mem hn hx false _ _ _ X
  · exact ⟨_, unitPtBP_mem hn hx true _ _ _ X, rfl⟩

theorem canonPtBP_injective (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (hx : ValsOK n x)
    (hΦx : ∀ c ∈ Φ, c.Holds x) : Function.Injective (canonPtBP Φ n x) := by
  intro X Y h
  by_contra hXY
  exact Set.disjoint_left.1 (gPosSpotBP_disjoint hΦ hn hXY) (canonPtBP_mem_spot hn hx hΦx X)
    (h ▸ canonPtBP_mem_spot hn hx hΦx Y)

end Spot

/-! ### Cardinality, boundary and the representative guards -/

/-- **The canonical guard set has `numGuardsBP Φ n` points.** -/
theorem canonGuardsBP_card {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) (hΦx : ∀ c ∈ Φ, c.Holds x) :
    (canonGuardsBP Φ n x).card = numGuardsBP Φ n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [canonGuardsBP, numGuardsBP, Sec5.numGuards]
  · have hn0 : n ≠ 0 := by omega
    simp only [canonGuardsBP, hn0, ite_false]
    rw [Finset.card_image_of_injective _ (canonPtBP_injective hΦ hn hx hΦx), Finset.card_univ,
      card_posBP hΦ hn]

/-- **The canonical guards lie on the boundary.** -/
theorem canonGuardsBP_boundary {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) (hΦx : ∀ c ∈ Φ, c.Holds x) :
    (canonGuardsBP Φ n x : Set Point) ⊆ (polyCBP Φ n).boundary := by
  classical
  intro g hg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [canonGuardsBP, ite_true, Finset.coe_singleton, mem_singleton_iff] at hg
    subst hg
    refine ⟨0, by simp [polyCBP, constructBP_zero, triangle0, Polygon.n], ?_⟩
    rw [Polygon.edge]
    have : (polyCBP Φ 0).vtx 0 = (0, 0) := by
      simp [polyCBP, constructBP_zero, triangle0, Polygon.vtx, ratPoint]
    rw [this]; exact Geometry.left_mem_segment _ _
  · have hn0 : n ≠ 0 := by omega
    simp only [canonGuardsBP, hn0, ite_false, Finset.coe_image, Finset.coe_univ, image_univ,
      mem_range] at hg
    obtain ⟨X, rfl⟩ := hg
    exact gPosSpotBP_subset_boundary hΦ hn X (canonPtBP_mem_spot hn hx hΦx X)

/-- **The canonical guard set contains `(x_i + d_i, 0)`**, `d_i = 27i/2 − 1/2`. -/
theorem canonGuardsBP_mem {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ} :
    ∀ i < n, (x i + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ canonGuardsBP Φ n x := by
  classical
  intro i hi
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuardsBP, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨.inl (), (⟨i, by omega⟩ : Fin (4 * n))⟩, ?_⟩
  have hlt : i < 3 * n := by omega
  simp only [canonPtBP, basePt, slotVal, hlt, ite_true, Nat.mod_eq_of_lt hi, slotX, shift]
  ext <;> push_cast <;> ring

end ArtGallery.BP

end
