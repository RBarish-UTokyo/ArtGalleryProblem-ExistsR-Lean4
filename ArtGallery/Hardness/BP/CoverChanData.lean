module

public import ArtGallery.Hardness.Sec5.CoverChanData
public import ArtGallery.Hardness.BP.Assemble.Sep
public import ArtGallery.Hardness.BP.Templates.InvCover
public import ArtGallery.Hardness.BP.Templates.AddGECover
public import ArtGallery.Hardness.BP.Templates.AddLECover
public import ArtGallery.Hardness.BP.Templates.OrientCover

/-!
# Boundary-point variant: the channel certificates of the four templates

The data of the Section 5 channel certificate `Sec5.CoverT.ChanD` (`Sec5/CoverChanData.lean`) for
the boundary-point templates `orient`, `ge`, `le`, `inv` (chains `tmplVBP k`, scales `tmplDBP k`,
receivers in the order `τ` of `tmplTBP k`, guard segments on the bay floors).  For every receiver
`[R₀, R₁]` the certificate lists a sub-segment `[M₂, M₁]` of the mouth `V_l V₀` crossed by all
sight lines from the receiver to the window of the corridor, an interior point of the piece
`conv {R₀, R₁, M₂, M₁}` inside a cover piece of the template region, and the distinguished
receiver `B` (`τ = 2` for `ge`, `le`; `τ = 1` for `orient`; `r_i` for `inv`) whose sub-segment is
the whole mouth.  For `inv` the chain edge `V₃₄ V₃₅` next to the upper end of the mouth is
separated from the channel by the extra line `x = 29/4` (template units).

The data was computed by a script from the template data; the checks (`ChanD.chanB`) are
verified by `decide +kernel` (`chan*BP_ok`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Vis.Cert
open ArtGallery.Sec5.CoverT (ChanD RecvD)

/-- The channel certificate of `orient`. -/
def chanORBP : ChanD := ⟨278400, tmplVBP .orient, [], [
    ⟨((-6124800), (-1113600)), ((-5707200), (-1113600)), ((-8431032), 1191986), ((-8133192), 1313166), ((-6124800), (-1113600)), ((-5707200), (-1113600)), ((-8133192), 1313166), ((-7099056), 69488), 50⟩,
    ⟨((-10996800), 0), ((-10579200), 0), ((-11275200), 34800), ((-4176000), 2923200), ((-10996800), 0), ((-10579200), 0), ((-4176000), 2923200), ((-9256800), 739500), 52⟩], 1⟩

/-- The channel certificate of `ge`. -/
def chanGEBP : ChanD := ⟨278400, tmplVBP .ge, [], [
    ⟨((-556800), (-2923200)), ((-139200), (-2923200)), ((-5759652), 2278871), ((-5461608), 2400134), ((-556800), (-2923200)), ((-139200), (-2923200)), ((-5461608), 2400134), ((-2979315), (-291849)), 50⟩,
    ⟨((-6124800), (-1113600)), ((-5707200), (-1113600)), ((-8431032), 1191986), ((-8133192), 1313166), ((-6124800), (-1113600)), ((-5707200), (-1113600)), ((-8133192), 1313166), ((-7099056), 69488), 52⟩,
    ⟨((-10996800), 0), ((-10579200), 0), ((-11275200), 34800), ((-4176000), 2923200), ((-10996800), 0), ((-10579200), 0), ((-4176000), 2923200), ((-9256800), 739500), 54⟩], 2⟩

/-- The channel certificate of `le`. -/
def chanLEBP : ChanD := ⟨355200, tmplVBP .le, [], [
    ⟨(177600, (-3729600)), (710400, (-3729600)), ((-6674696), 3122123), ((-6306696), 3288123), (177600, (-3729600)), (710400, (-3729600)), ((-6306696), 3288123), ((-3023348), (-262239)), 32⟩,
    ⟨((-7814400), (-532800)), ((-7281600), (-532800)), ((-9979336), 1631443), ((-9611152), 1797526), ((-7814400), (-532800)), ((-7281600), (-532800)), ((-9611152), 1797526), ((-8671622), 590842), 34⟩,
    ⟨((-13142400), 0), ((-12609600), 0), ((-13497600), 44400), ((-5328000), 3729600), ((-13142400), 0), ((-12609600), 0), ((-5328000), 3729600), ((-11144400), 943500), 36⟩], 2⟩

/-- The channel certificate of `inv`. -/
def chanInvBP : ChanD := ⟨3008974742400, tmplVBP .inv, [((-1), 0, 21815066882400)], [
    ⟨(41824748919360, 300897474240), (46338211032960, 300897474240), (15423555184200, 26701629157235), (17190159338880, 29448949199912), (41824748919360, 300897474240), (46338211032960, 300897474240), (17190159338880, 29448949199912), (30194168618850, 14188093326406), 11⟩,
    ⟨(1504487371200, 0), (6017949484800, 0), ((-1504487371200), 376121842800), (21062823196800, 35471490813000), (1504487371200, 0), (6017949484800, 0), (21062823196800, 35471490813000), (6770193170400, 8961903163950), 3⟩], 1⟩

theorem chanORBP_ok : chanORBP.chanB Tmpl.bpORR Tmpl.bpORCvPieces = true := by decide +kernel

theorem chanGEBP_ok : chanGEBP.chanB Tmpl.bpGER Tmpl.bpGECvPieces = true := by decide +kernel

theorem chanLEBP_ok : chanLEBP.chanB Tmpl.bpLER Tmpl.bpLECvPieces = true := by decide +kernel

theorem chanInvBP_ok : chanInvBP.chanB Tmpl.bpInvR Tmpl.bpInvCvPieces = true := by decide +kernel

end ArtGallery.BP

end
