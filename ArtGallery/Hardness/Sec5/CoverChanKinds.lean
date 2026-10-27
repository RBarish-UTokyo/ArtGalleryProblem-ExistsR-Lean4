module

public import ArtGallery.Hardness.Sec5.CoverChanData

/-!
# Section 5, sufficiency (vi): the channel certificates of the four templates

The data of `ChanD` for the templates `orient`, `ge`, `le`, `inv` (receivers in the order `τ`
of `tmplT`), computed by a script from the template data: for every receiver the mouth
sub-segment `[M₂, M₁]` (the whole mouth where possible, otherwise a sub-segment containing the
crossings of all sight lines to the window), an interior point of `A_τ` inside a cover piece, and
the distinguished receiver (`r_j` for the addition kinds, `r_i` for `inv`).  The checks are
verified by `decide +kernel` (`chan_ok`).
-/

@[expose] public section

namespace ArtGallery.Sec5.CoverT

open ArtGallery Vis.Cert Tmpl

/-- The channel certificate of `orient`. -/
def chanOR : ChanD := ⟨148879200, tmplV .orient, [(0, 1, -14887920)], [
    ⟨((-3870859200), 0), ((-3647540400), 0), ((-6044495520), 14887920), ((-1488792000), 1563231600), ((-3870859200), 0), ((-3647540400), 0), ((-1488792000), 1563231600), ((-3002397200), 521077200), 27⟩,
    ⟨((-3275342400), (-2605386000)), ((-3052023600), (-2605386000)), ((-6044495520), 14887920), ((-1488792000), 1563231600), ((-3275342400), (-2605386000)), ((-3052023600), (-2605386000)), ((-1488792000), 1563231600), ((-1962433996), 384278893), 27⟩], 0⟩

/-- The channel certificate of `ge`. -/
def chanGE : ChanD := ⟨83197200, tmplV .ge, [(0, 1, -8319720)], [
    ⟨((-166394400), (-873570600)), ((-41598600), (-873570600)), ((-1680583440), 585153640), ((-1468430580), 657257880), ((-166394400), (-873570600)), ((-41598600), (-873570600)), ((-1468430580), 657257880), ((-1018943968), 152866637), 31⟩,
    ⟨((-2163127200), 0), ((-2038331400), 0), ((-3377806320), 8319720), ((-831972000), 873570600), ((-2163127200), 0), ((-2038331400), 0), ((-831972000), 873570600), ((-1677810200), 291190200), 31⟩,
    ⟨((-1830338400), (-1455951000)), ((-1705542600), (-1455951000)), ((-3377806320), 8319720), ((-831972000), 873570600), ((-1830338400), (-1455951000)), ((-1705542600), (-1455951000)), ((-831972000), 873570600), ((-1096654292), 214744087), 31⟩], 1⟩

/-- The channel certificate of `le`. -/
def chanLE : ChanD := ⟨24738000, tmplV .le, [(0, 1, -2473800)], [
    ⟨(12369000, (-259749000)), (49476000, (-259749000)), ((-455921340), 182566440), ((-386407560), 208293960), (12369000, (-259749000)), (49476000, (-259749000)), ((-386407560), 208293960), ((-258225882), 64530996), 48⟩,
    ⟨((-581343000), 0), ((-544236000), 0), ((-942517800), 2473800), ((-247380000), 259749000), ((-581343000), 0), ((-544236000), 0), ((-247380000), 259749000), ((-457653000), 86583000), 48⟩,
    ⟨((-544236000), (-371070000)), ((-507129000), (-371070000)), ((-942517800), 2473800), ((-247380000), 259749000), ((-544236000), (-371070000)), ((-507129000), (-371070000)), ((-247380000), 259749000), ((-326475574), 80460113), 48⟩], 1⟩

/-- The channel certificate of `inv`. -/
def chanInv : ChanD := ⟨501495790400, tmplV .inv, [(-1, 0, 3510470532800)], [
    ⟨(6970791486560, 50149579040), (7723035172160, 50149579040), (2316910551648, 4396997718872), (2871063400040, 5100352233735), (6970791486560, 50149579040), (7723035172160, 50149579040), (2871063400040, 5100352233735), (3297334821880, 4615959944403), 0⟩,
    ⟨(250747895200, 0), (1002991580800, 0), ((-752243685600), 501495790400), (3510470532800, 5911915135500), (250747895200, 0), (1002991580800, 0), (3510470532800, 5911915135500), (1591225433571, 1977656188322), 0⟩], 1⟩

theorem chanOR_ok : chanOR.chanB addORR addORCvPieces = true := by decide +kernel

theorem chanGE_ok : chanGE.chanB addGER addGECvPieces = true := by decide +kernel

theorem chanLE_ok : chanLE.chanB addLER addLECvPieces = true := by decide +kernel

theorem chanInv_ok : chanInv.chanB Tmpl.invR invCvPieces = true := by decide +kernel

end ArtGallery.Sec5.CoverT

end
