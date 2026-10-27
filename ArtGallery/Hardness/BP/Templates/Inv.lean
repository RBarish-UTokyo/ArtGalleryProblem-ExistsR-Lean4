module

public import ArtGallery.Hardness.BP.Templates.InvMech

/-!
# Boundary-point templates: the inversion template `x_a · x_b = 1` — template facts

The inversion template of Section 5 (`Sec5/Templates/Inv.lean`) with the receivers `r_i`
(right-oriented, value `x`: guard `bpInvGp x = (D x, 0)`) and `r_j` (left-oriented, value `y`:
guard `bpInvGq y = (D (159/10 − y), D/10)`) on the floors of bays
(`docs/boundary_point/design.md`, §3.3).  Integer template coordinates (`InvData.lean`).

All statements are about an arbitrary simple counter-clockwise polygon `P` containing the
template chain (`ChainAt P bpInvV a`), where needed with its other edges avoiding the region
`bpInvR` (`SepAt P bpInvV a bpInvR`); `bpInvPT` (the chain closed by the fixed stub) is such a
polygon.

* (T-simple) `bpInvPT_simple`, `bpInvPT_ccw`, `bpInvPT_chain`, `bpInvPT_sep`;
* (T-mech) `bpInv_umbra_iff`, `bpInv_nook_iff` (`InvMech.lean`); the critical sets are not seen
  by the stationary guard `g` (`bpInv_g_not_sees_umbra`, `bpInv_g_not_sees_nook`);
* the counting facts for guards on the boundary are in `CountInv.lean`.
-/

@[expose] public section

namespace ArtGallery.BP.Tmpl

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl
open ArtGallery.Irrational (HP)

/-! ### The template polygon -/

/-- The template polygon `P_T`: the chain closed by the stub. -/
def bpInvPT : Polygon := ⟨bpInvVT.map intPoint⟩

theorem bpInvPT_simple : bpInvPT.Simple := simple_of_simpleCheck (by decide +kernel)

theorem bpInvPT_ccw : bpInvPT.InteriorLeft :=
  interiorLeft_of_lowB bpInvPT_simple (i := 5) (by decide +kernel)

theorem bpInvPT_chain : ChainAt bpInvPT bpInvV 0 := chainAt_append _ _

theorem bpInvPT_sep : SepAt bpInvPT bpInvV 0 bpInvR := sepAt_append (by decide) (by decide +kernel)

/-! ### The critical sets are not seen by `g` -/

section General

variable {P : Polygon} {a : ℕ}

/-- The stationary guard `g` is the chain vertex `32`. -/
theorem bpInvGs_eq : bpInvGs = [cv bpInvV 32] := by decide +kernel

theorem bpInv_g_det_axis (z : Point) :
    det (intPoint (cv bpInvV 32)) (intPoint (cv bpInvV 33)) z = -242012400 * bpInvLu.val z := by
  have e32 : cv bpInvV 32 = (48143595878400, 20381212558800) := by decide +kernel
  have e33 : cv bpInvV 33 = (37612184280000, 15904709196000) := by decide +kernel
  rw [e32, e33]
  simp only [det, intPoint, bpInvLu, Irrational.HP.val]; push_cast; ring

/-- `g` sees no point strictly above the umbra axis. -/
theorem bpInv_g_not_sees_umbra (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a)
    {z : Point} (hz : 0 < bpInvLu.val z) : ¬ P.Sees (intPoint (cv bpInvV 32)) z := by
  intro hs
  have := (chain_cone hP hL hC (j := 32) (by norm_num) (by decide) (by decide +kernel) hs).2
  rw [show (32 : ℕ) + 1 = 33 from rfl, bpInv_g_det_axis] at this
  linarith

/-- `g` sees no point of the nook zone. -/
theorem bpInv_g_not_sees_nook (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P bpInvV a) :
    ∀ w ∈ convexHull ℝ (intSet bpInvZn), ¬ P.Sees (intPoint (cv bpInvV 32)) w :=
  not_sees_of_outCone hP hL hC (j := 32) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end General

end ArtGallery.BP.Tmpl

end
