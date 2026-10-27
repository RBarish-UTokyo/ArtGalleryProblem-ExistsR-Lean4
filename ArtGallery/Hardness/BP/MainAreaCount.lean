module

public import ArtGallery.Hardness.BP.MainArea
public import ArtGallery.Hardness.Sec5.CountMain

/-!
# Boundary-point variant, counting: the base positions (main area)

The `4n` base positions of the main area with bays (`docs/boundary_point/design.md` §3.5), in a
polygon `P` that contains the closed pocket chains of all slots (`MainHypBP`), with guards
restricted to the boundary (allowed set `Ω = P.boundary`):

* main witness: the tip `T1` of the bay of slot `σ`; witnesses: `T1`, `T2` (and `O1`, `O2` for a
  slot with `one` spikes); position: the floor segment `s_σ` (resp. the value-`1` point);
* all ranks are `0`: the visibility sets of the witnesses of slot `σ` lie in the box
  `[a_σ.x − 5/6, a_σ.x + 7/3] × [0, 1/16]` (`vis_box`), and the boxes of different slots are
  disjoint, so (W2) and (W3) hold for all points of the plane; only the pinning (W1) uses that the
  guards lie on the boundary (`spot_bayWit`);
* the region of the zone is the strip `X_L < x < S` (`Count.mainReg`), as in Section 5.

`MainHypBP.okOn`: the position system satisfies `PosSys.OKOn P P.boundary`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Sec5 (slotX slotX_sep_real)
open ArtGallery.Sec5.Count (PosSys mainReg)

/-- The slot abscissae: `0 ≤ 27σ/2` and `27σ/2 + 15/2 ≤ 54n − 6` for `σ < 4n`. -/
theorem slotX_real_bounds {n σ : ℕ} (hσ : σ < 4 * n) :
    (0 : ℝ) ≤ slotX σ ∧ (slotX σ : ℝ) + 15 / 2 ≤ 54 * (n : ℝ) - 6 := by
  have : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ
  simp only [slotX]; push_cast
  exact ⟨by positivity, by linarith⟩

/-- **The base positions** (boundary-point variant). -/
noncomputable def mainSysBP (n : ℕ) (one : ℕ → Bool) : PosSys (Fin (4 * n)) where
  m σ := (slotFrame σ).pt w1Rel
  W σ := bayWit (one σ) (slotFrame σ)
  Spot σ := baySpot (one σ) (slotFrame σ)
  rank _ := 0

/-- The hypotheses on the main area: every slot `σ < 4n` carries its closed pocket chain, and no
other edge meets the box `(a_σ.x − 6, a_σ.x + 15/2) × (0, 1/8)`. -/
structure MainHypBP (P : Polygon) (n : ℕ) (one : ℕ → Bool) (start : ℕ → ℕ) : Prop where
  simple : P.Simple
  ccw : P.InteriorLeft
  pocket : ∀ σ < 4 * n, PocketAtBP P (one σ) σ (start σ)
  sep : ∀ σ < 4 * n, BoxSepBP P (one σ) σ (start σ) (1/8)

namespace MainHypBP

variable {P : Polygon} {n k : ℕ} {one : ℕ → Bool} {start : ℕ → ℕ}
  (h : MainHypBP P n one start)
include h

theorem bayAt {σ : ℕ} (hσ : σ < 4 * n) : BayAt P (one σ) (slotFrame σ) (start σ + 1) :=
  (h.pocket σ hσ).bayAt

theorem baySep {σ : ℕ} (hσ : σ < 4 * n) : BaySep P (one σ) (slotFrame σ) (start σ + 1) :=
  (h.sep σ hσ).baySep (h.pocket σ hσ) h.simple le_rfl

/-- The visibility sets of the witnesses of slot `σ` lie in `[a_σ.x − 5/6, a_σ.x + 7/3]`. -/
theorem vis_x {σ : ℕ} (hσ : σ < 4 * n) {w : Point} (hw : w ∈ bayWit (one σ) (slotFrame σ))
    {p : Point} (hs : P.Sees p w) :
    (slotX σ : ℝ) - 5/6 ≤ p.1 ∧ p.1 ≤ (slotX σ : ℝ) + 7/3 := by
  obtain ⟨b1, b2, -, -⟩ := vis_box (h.bayAt hσ) h.simple h.ccw hw (sees_comm.1 hs)
  rw [slotFrame_rel] at b1 b2
  simp only at b1 b2
  exact ⟨by linarith, by linarith⟩

/-- No point sees witnesses of two different slots. -/
theorem vis_disj {σ σ' : ℕ} (hσ : σ < 4 * n) (hσ' : σ' < 4 * n) (hne : σ ≠ σ') {w w' : Point}
    (hw : w ∈ bayWit (one σ) (slotFrame σ)) (hw' : w' ∈ bayWit (one σ') (slotFrame σ'))
    {p : Point} (hs : P.Sees p w) (hs' : P.Sees p w') : False := by
  obtain ⟨a1, a2⟩ := h.vis_x hσ hw hs
  obtain ⟨b1, b2⟩ := h.vis_x hσ' hw' hs'
  rcases slotX_sep_real hne with e | e <;> linarith

/-- **The base positions satisfy the counting conditions for guards on the boundary.** -/
theorem okOn : (mainSysBP n one).OKOn P P.boundary (mainReg n k) := by
  have hP := h.simple
  have hL := h.ccw
  refine ⟨fun σ => w1_mem_bayWit, fun σ w hw => bayWit_mem_filled (h.bayAt σ.2) hP hw,
    fun σ w hw p _ hs => ?_,
    fun σ p hp hall => spot_bayWit (h.bayAt σ.2) hP hL (h.baySep σ.2) hp hall, ?_, ?_, ?_, ?_, ?_⟩
  · -- reg
    obtain ⟨a1, a2⟩ := h.vis_x σ.2 hw hs
    have hS := Sec5.slots_lt_S (n := n) (k := k)
    have hS' : 54 * (n : ℝ) + 100000 ≤ (Sec5.S n k : ℝ) := by exact_mod_cast hS
    obtain ⟨h0, hX'⟩ := slotX_real_bounds σ.2
    exact ⟨by linarith, by linarith⟩
  · -- spot_reg
    rintro ⟨σ, hσ⟩ p hp
    obtain ⟨b1, b2, b3⟩ := baySpot_rel (h.bayAt hσ).ne hp
    rw [slotFrame_rel] at b1 b2 b3
    simp only at b2 b3
    have hS := Sec5.slots_lt_S (n := n) (k := k)
    have hS' : 54 * (n : ℝ) + 100000 ≤ (Sec5.S n k : ℝ) := by exact_mod_cast hS
    obtain ⟨h0, hX'⟩ := slotX_real_bounds hσ
    exact ⟨by linarith, by linarith⟩
  · -- spot_disj
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne
    have hss : σ ≠ σ' := fun e => hne (by subst e; rfl)
    rw [Set.disjoint_left]
    intro p hp hp'
    obtain ⟨-, a2, a3⟩ := baySpot_rel (h.bayAt hσ).ne hp
    obtain ⟨-, b2, b3⟩ := baySpot_rel (h.bayAt hσ').ne hp'
    rw [slotFrame_rel] at a2 a3 b2 b3
    simp only at a2 a3 b2 b3
    rcases slotX_sep_real hss with e | e <;> linarith
  · -- disj
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne p _ h1 h2
    have hss : σ ≠ σ' := fun e => hne (by subst e; rfl)
    exact h.vis_disj hσ hσ' hss w1_mem_bayWit w1_mem_bayWit h1 h2
  · -- early (all ranks are `0`)
    intro X Y _ hr
    exact absurd hr (lt_irrefl 0)
  · -- late
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne - w hw p _ h1 h2
    have hss : σ' ≠ σ := fun e => hne (by subst e; rfl)
    exact h.vis_disj hσ' hσ hss w1_mem_bayWit hw h1 h2

end MainHypBP

end ArtGallery.BP

end
