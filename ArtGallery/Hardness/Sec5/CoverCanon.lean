module

public import ArtGallery.Hardness.Sec5.CountGlobal
public import ArtGallery.Hardness.Sec5.Templates.InvCover
public import ArtGallery.Hardness.Sec5.Templates.AddGECover
public import ArtGallery.Hardness.Sec5.Templates.AddLECover
public import ArtGallery.Hardness.Sec5.Templates.OrientCover

/-!
# Section 5, sufficiency (vi)/(vii): the canonical guards of an assignment

For an assignment `x : ℕ → ℝ` (values in `[1/2, 2]`, `docs/section5/06_assembly.md`,
"Canonical guards") every guard position `X` of the global polygon (`Count.GPos`) receives a
canonical point `canonPt Φ n x X`:

* base slot `σ = g n + i` (`i < n`): the point `(27σ/2 + t_σ, 0)` with offset
  `t_σ = slotVal σ − 1/2`, where `slotVal σ = x_i` for the groups `g = 0, 1, 2` and
  `slotVal σ = 5/2 − x_i` for the group `g = 3` (`basePt`);
* a corridor stationary guard: the point `p_k` itself;
* a template position of a unit: the template guard with the copied value (`tGuard`), placed by
  `uφ`; the *working value* of a working slot `w` of a unit is `slotVal w` (right units) resp.
  `5/2 − slotVal (4n − 1 − w)` (left units, mirror principle); the receiver `τ` reads the slot of
  pair `k = np − 1 − τ`; the weak copy `r'_i` gets the value of `r_i`; left units are mirrored.

Main results:

* `canonPt_mem_spot`: the canonical point of `X` lies on the position `X` (`gPosSpot X`);
* **`canonGuards_card`**: the canonical guard set has `numGuards Φ n` points (distinct positions
  are disjoint);
* **`canonGuards_mem`**: it contains `(x_i + d_i, 0)`, `d_i = shift i = 27i/2 − 1/2`;
* `tGuard_recv`: the canonical receiver guards are the corridor receiver guards at the copied
  offset (`Corridor.place S H (T_τ + (t, 0))`), as required by the corridor coverage.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5

open ArtGallery Set Polygon Tmpl ArtGallery.Sec5.Count
open Vis.Cert

/-! ### Values of slots -/

/-- The value specified by the canonical guard of slot `σ`: `x_i` for `σ = g n + i`, `g < 3`, and
`5/2 − x_i` for `σ = 3n + i` (group 3 is left-oriented). -/
noncomputable def slotVal (n : ℕ) (x : ℕ → ℝ) (σ : ℕ) : ℝ :=
  if σ < 3 * n then x (σ % n) else 5 / 2 - x (σ % n)

/-- The canonical guard of slot `σ`: offset `slotVal σ − 1/2` from the left end `a_σ`. -/
noncomputable def basePt (n : ℕ) (x : ℕ → ℝ) (σ : ℕ) : Point :=
  ((slotX σ : ℝ) + (slotVal n x σ - 1 / 2), 0)

/-- The value read by a working slot `w` of a unit: `slotVal w` (right units), resp.
`5/2 − slotVal (4n − 1 − w)` (left units: the mirror reverses the guard segment). -/
noncomputable def workVal (n : ℕ) (x : ℕ → ℝ) (left : Bool) (w : ℕ) : ℝ :=
  if left then 5 / 2 - slotVal n x (4 * n - 1 - w) else slotVal n x w

/-- The value of receiver `τ` of the unit `u` (pair `k = np − 1 − τ`). -/
noncomputable def recvVal (n : ℕ) (x : ℕ → ℝ) (left : Bool) (u : UnitSpec) (τ : ℕ) : ℝ :=
  workVal n x left (u.work.getD (u.work.length - 1 - τ) 0)

/-- Values in `[1/2, 2]` on the variables. -/
def ValsOK (n : ℕ) (x : ℕ → ℝ) : Prop := ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2

theorem slotVal_mem {n : ℕ} {x : ℕ → ℝ} (hn : 0 < n) (hx : ValsOK n x) (σ : ℕ) :
    1 / 2 ≤ slotVal n x σ ∧ slotVal n x σ ≤ 2 := by
  obtain ⟨h0, h1⟩ := hx (σ % n) (Nat.mod_lt _ hn)
  unfold slotVal
  split_ifs <;> constructor <;> linarith

theorem workVal_mem {n : ℕ} {x : ℕ → ℝ} (hn : 0 < n) (hx : ValsOK n x) (left : Bool) (w : ℕ) :
    1 / 2 ≤ workVal n x left w ∧ workVal n x left w ≤ 2 := by
  unfold workVal
  split_ifs
  · obtain ⟨h0, h1⟩ := slotVal_mem hn hx (4 * n - 1 - w)
    constructor <;> linarith
  · exact slotVal_mem hn hx w

theorem recvVal_mem {n : ℕ} {x : ℕ → ℝ} (hn : 0 < n) (hx : ValsOK n x) (left : Bool)
    (u : UnitSpec) (τ : ℕ) : 1 / 2 ≤ recvVal n x left u τ ∧ recvVal n x left u τ ≤ 2 :=
  workVal_mem hn hx left _

/-! ### The canonical template guards -/

/-- The canonical guards of a template, in template (integer) coordinates, for the receiver
values `v τ` (`τ = 0` belongs to the largest working slot):
* `inv` (positions `g, r_i, r_j`): `g = V₃₆`, `invGp (v 1)`, `invGq (5/2 − v 0)` (the guard
  segment `r_j` is read from the right);
* `ge`, `le` (positions `g, r_j, r_i, r_l, r'_i`): `g = V₇₀`, `B (v 1)`, `I (v 2)`, `C (v 0)`,
  `A (v 2)` (exact weak copy);
* `orient` (positions `g, p, r_j, r_i, r'_i`): `g = V₆₄`, `p`, `B (v 0)`, `I (v 1)`, `A (v 1)`. -/
noncomputable def tGuard : (k : Kind) → (ℕ → ℝ) → Fin (tsysOf k).r → Point
  | .inv, v => ![intPoint (cv invV 36), invGp (v 1), invGq (5 / 2 - v 0)]
  | .ge, v => ![intPoint (cv addGEV 70), addGEB (v 1), addGEI (v 2), addGEC (v 0), addGEA (v 2)]
  | .le, v => ![intPoint (cv addLEV 70), addLEB (v 1), addLEI (v 2), addLEC (v 0), addLEA (v 2)]
  | .orient, v => ![intPoint (cv addORV 64), addORC, addORB (v 0), addORI (v 1), addORA (v 1)]

/-- The canonical template guards lie on their positions. -/
theorem tGuard_mem (k : Kind) {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2)
    (X : Fin (tsysOf k).r) : tGuard k v X ∈ convexHull ℝ (intSet ((tsysOf k).spot X)) := by
  cases k
  · -- orient
    have h0 := hv 0
    have h1 := hv 1
    change Fin 5 at X
    fin_cases X
    · exact addOR_g_mem
    · exact addOR_p_mem
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h1.1 h1.2
  · -- ge
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    change Fin 5 at X
    fin_cases X
    · exact addGE_g_mem
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h2.1 h2.2
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h2.1 h2.2
  · -- le
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    change Fin 5 at X
    fin_cases X
    · exact addLE_g_mem
    · exact segGuard_mem h1.1 h1.2
    · exact segGuard_mem h2.1 h2.2
    · exact segGuard_mem h0.1 h0.2
    · exact segGuard_mem h2.1 h2.2
  · -- inv
    have h0 := hv 0
    have h1 := hv 1
    change Fin 3 at X
    fin_cases X
    · exact inv_g_mem
    · exact invGp_mem h1.1 h1.2
    · exact invGq_mem (by linarith) (by linarith)

/-! ### The canonical points of the positions -/

/-- The canonical point of a position of a unit (working frame): the corridor stationary guard
`p_k`, or the placed canonical template guard. -/
noncomputable def unitPt (n : ℕ) (x : ℕ → ℝ) (left : Bool) (k m : ℕ) (u : UnitSpec) :
    Fin (unitInput n k m u).np ⊕ Fin (tsysOf u.kind).r → Point :=
  Sum.elim (fun j => ratPoint ((unitInput n k m u).sgPt j))
    (fun X => uφ n k m u (tGuard u.kind (recvVal n x left u) X))

/-- **The canonical point of a position** of the global polygon. -/
noncomputable def canonPt (Φ : List ETRINV.Constraint) (n : ℕ) (x : ℕ → ℝ) : GPos Φ n → Point
  | ⟨.inl _, σ⟩ => basePt n x (show Fin (4 * n) from σ)
  | ⟨.inr (.inl i), X⟩ => unitPt n x false (numC Φ) i (unitSpecs n Φ).1[i] X
  | ⟨.inr (.inr i), X⟩ => mirrorEquiv n (unitPt n x true (numC Φ) i (unitSpecs n Φ).2[i] X)

/-- **The canonical guard set** of an assignment `x` (for `n = 0`: the vertex `(0, 0)` of the
triangle). -/
noncomputable def canonGuards (Φ : List ETRINV.Constraint) (n : ℕ) (x : ℕ → ℝ) : Finset Point :=
  by classical exact if n = 0 then {(0, 0)} else Finset.univ.image (canonPt Φ n x)

/-! ### The canonical points lie on their positions -/

section Spot

variable {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ}

theorem basePt_eq_g1 (σ : ℕ) (hσ : σ < n) (h1 : x σ = 1) : basePt n x σ = g1Pt σ := by
  have hlt : σ < 3 * n := by omega
  simp only [basePt, slotVal, hlt, ite_true, Nat.mod_eq_of_lt hσ, h1, g1Pt, absPt_eq, g1Rel]
  ext <;> norm_num

theorem basePt_mem (hn : 0 < n) (hx : ValsOK n x) (σ : ℕ) : basePt n x σ ∈ baseSeg σ := by
  obtain ⟨h0, h1⟩ := slotVal_mem hn hx σ
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [basePt] <;> linarith

theorem holds_one {σ : ℕ} (hΦx : ∀ c ∈ Φ, c.Holds x) (h : slotOne n Φ σ = true) : x σ = 1 := by
  simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨-, c, hc, hc1⟩ := h
  have := hΦx c hc
  cases c <;> simp_all [isOneOf, ETRINV.Constraint.Holds]

theorem unitPt_mem (hn : 0 < n) (hx : ValsOK n x) (left : Bool) (k m : ℕ) (u : UnitSpec)
    (X : Fin (unitInput n k m u).np ⊕ Fin (tsysOf u.kind).r) :
    unitPt n x left k m u X ∈ (uSys n k m u).Spot X := by
  rcases X with j | X
  · exact rfl
  · exact ⟨_, tGuard_mem u.kind (fun τ => recvVal_mem hn hx left u τ) X, rfl⟩

/-- **The canonical point of `X` lies on the position `X`.** -/
theorem canonPt_mem_spot (hn : 0 < n) (hx : ValsOK n x) (hΦx : ∀ c ∈ Φ, c.Holds x)
    (X : GPos Φ n) : canonPt Φ n x X ∈ gPosSpot X := by
  rcases X with ⟨_ | i | i, X⟩
  · change Fin (4 * n) at X
    rw [gPosSpot_main]
    split_ifs with h
    · have hσ : (X : ℕ) < n := by
        simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
      exact basePt_eq_g1 X hσ (holds_one hΦx h)
    · exact basePt_mem hn hx X
  · exact unitPt_mem hn hx false _ _ _ X
  · exact ⟨_, unitPt_mem hn hx true _ _ _ X, rfl⟩

/-- **Distinct positions are disjoint.** -/
theorem gPosSpot_disjoint (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {X Y : GPos Φ n}
    (hXY : X ≠ Y) : Disjoint (gPosSpot X) (gPosSpot Y) := by
  have hOK := gZ_ok hΦ hn
  obtain ⟨z, X⟩ := X
  obtain ⟨z', Y⟩ := Y
  by_cases hz : z = z'
  · subst hz
    have hne : X ≠ Y := fun h => hXY (by rw [h])
    exact (hOK z).spot_disj X Y hne
  · exact Set.disjoint_of_subset ((hOK z).spot_reg X) ((hOK z').spot_reg Y) (gReg_disjoint z z' hz)

theorem canonPt_injective (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (hx : ValsOK n x)
    (hΦx : ∀ c ∈ Φ, c.Holds x) : Function.Injective (canonPt Φ n x) := by
  intro X Y h
  by_contra hXY
  exact Set.disjoint_left.1 (gPosSpot_disjoint hΦ hn hXY) (canonPt_mem_spot hn hx hΦx X)
    (h ▸ canonPt_mem_spot hn hx hΦx Y)

end Spot

/-! ### Cardinality and the representative guards -/

/-- **The canonical guard set has `numGuards Φ n` points.** -/
theorem canonGuards_card {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) (hΦx : ∀ c ∈ Φ, c.Holds x) :
    (canonGuards Φ n x).card = numGuards Φ n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [canonGuards, numGuards]
  · have hn0 : n ≠ 0 := by omega
    simp only [canonGuards, hn0, ite_false]
    rw [Finset.card_image_of_injective _ (canonPt_injective hΦ hn hx hΦx), Finset.card_univ,
      card_pos hΦ hn]

/-- **The canonical guard set contains `(x_i + d_i, 0)`**, `d_i = 27i/2 − 1/2`. -/
theorem canonGuards_mem {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ} :
    ∀ i < n, (x i + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ canonGuards Φ n x := by
  classical
  intro i hi
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuards, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨.inl (), (⟨i, by omega⟩ : Fin (4 * n))⟩, ?_⟩
  have hlt : i < 3 * n := by omega
  simp only [canonPt, basePt, slotVal, hlt, ite_true, Nat.mod_eq_of_lt hi, slotX, shift]
  ext <;> push_cast <;> ring

end ArtGallery.Sec5

end
