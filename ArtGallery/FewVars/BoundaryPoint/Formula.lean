module

public import ArtGallery.FewVars.PT

/-!
# The formula for the boundary-point art gallery problem

In the boundary-point variant the guards must lie on the boundary and see the whole region.
The formula is the point-point formula with "the guard lies in the region" strengthened to
"the guard lies on the boundary":

* `ronBoundaryF C g`: every guard `rguard a` (`a < g`) lies on some edge (`rboundaryF`: the
  determinant with the edge's endpoints vanishes and the guard lies between them);
* `rbpguardsF C g` is `ronBoundaryF C g ∧ rguardsF C g` (GUARDS of the point-point formula: the
  guards are in the region and see every witness point, hence the whole region).

`fvbpFormulaD D g` is SIMPLE (if `n ≤ g + 2`: the `n - 2` corners picked from a triangulation
form a guard set on the boundary, `hasGuardSetOnBoundaryOfCard_n_sub_two`) or
SIMPLE ∧ `rbpguardsF`; `fvbpToETR` decodes the instance.  Main results:
`fvbpToETR_correct : AGPBoundaryPoint w ↔ (fvbpToETR w).Satisfiable`,
`fvbpToETR_encodeAGP_varsLt` and `PT.fvbpToETR`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.FewVars.BoundaryPoint

open ArtGallery.ETR ArtGallery.Membership ArtGallery.FewVars Complexity Complexity.PT
  Complexity.PT.Code

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

/-! ## Guard sets on the boundary -/

/-- The boundary of a simple polygon is infinite (it contains a nondegenerate edge). -/
theorem boundary_infinite (hP : P.Simple) : P.boundary.Infinite := by
  have h3 : 3 ≤ P.n := hP.1
  have h0 : 0 < P.n := by omega
  have huv := Jordan.simple_vtx_succ_ne hP h0
  refine Set.infinite_of_injOn_mapsTo (Geometry.lerp_injective huv).injOn ?_
    (Set.Icc_infinite (zero_lt_one' ℝ))
  intro τ hτ
  exact ⟨0, h0, Geometry.lerp_mem_segment _ _ hτ.1 hτ.2⟩

/-- A guard set on the boundary can be enlarged by one point. -/
theorem hasGuardSetOnBoundaryOfCard_succ (hP : P.Simple) {k : ℕ}
    (h : P.HasGuardSetOnBoundaryOfCard k) : P.HasGuardSetOnBoundaryOfCard (k + 1) := by
  classical
  obtain ⟨G, hG, hsub, hsee⟩ := h
  obtain ⟨y, hyb, hyG⟩ := (boundary_infinite hP).exists_notMem_finset G
  refine ⟨insert y G, by rw [Finset.card_insert_of_notMem hyG, hG], ?_, ?_⟩
  · intro z hz
    rw [Finset.coe_insert] at hz
    rcases hz with rfl | hz
    · exact hyb
    · exact hsub hz
  · intro p hp
    obtain ⟨γ, hγ, hγp⟩ := hsee p hp
    refine ⟨γ, ?_, hγp⟩
    rw [Finset.coe_insert]
    exact Or.inr hγ

/-- **Padding** for guard sets on the boundary. -/
theorem HasGuardSetOnBoundaryOfCard.mono (hP : P.Simple) {k k' : ℕ}
    (h : P.HasGuardSetOnBoundaryOfCard k) (hk : k ≤ k') : P.HasGuardSetOnBoundaryOfCard k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact h
  | succ d ih => exact hasGuardSetOnBoundaryOfCard_succ hP ih

/-- **A simple polygon with `n` vertices has a guard set of `n − 2` points of its boundary**:
one corner of each triangle of a triangulation sees the whole (convex) triangle. -/
theorem hasGuardSetOnBoundaryOfCard_n_sub_two (hP : P.Simple) :
    P.HasGuardSetOnBoundaryOfCard (P.n - 2) := by
  classical
  obtain ⟨T, hT⟩ := Existence.exists_triangulation hP
  have hlen := Existence.triangulates_length hT
  obtain ⟨hval, -, hunion, -, -⟩ := hT
  have htri : ∀ t ∈ T, P.triSet t ⊆ P.filled := by
    intro t ht y hy
    rw [← hunion]
    exact ⟨t, ht, hy⟩
  have hcorner : ∀ t : Polygon.Triangle, P.vtx t.1 ∈ P.triSet t := fun t =>
    Geometry.triVertices_subset_triSet P t (Set.mem_insert _ _)
  refine HasGuardSetOnBoundaryOfCard.mono hP
    ⟨(T.map fun t => P.vtx t.1).toFinset, rfl, ?_, ?_⟩ ?_
  · intro γ hγ
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hγ
    obtain ⟨t, ht, rfl⟩ := hγ
    exact Existence.vtx_mem_boundary P (hval t ht).1
  · intro p hp
    rw [← hunion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    refine ⟨P.vtx t.1, ?_, ?_⟩
    · rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨t, ht, rfl⟩
    · exact (Geometry.segment_subset_of_convex (Geometry.convex_triSet P t) (hcorner t) hpt).trans
        (htri t ht)
  · calc (T.map fun t => P.vtx t.1).toFinset.card ≤ (T.map fun t => P.vtx t.1).length :=
          List.toFinset_card_le _
      _ = T.length := List.length_map _
      _ = P.n - 2 := hlen

/-! ## The formula -/

/-- **ON-BOUNDARY**: every guard `rguard a` (`a < g`) lies on an edge. -/
def ronBoundaryF (C : List RPt) (g : ℕ) : Formula :=
  bigAnd ((List.range g).map fun a => rboundaryF C (rguard a))

/-- **Boundary-point GUARDS**: the guards lie on the boundary, and GUARDS of the point-point
formula (they see every witness point). -/
def rbpguardsF (C : List RPt) (g : ℕ) : Formula := .and (ronBoundaryF C g) (rguardsF C g)

/-- **Boundary-point GUARDS is sound.** -/
theorem bpguards_of_holds (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (h : (rbpguardsF C g).Holds x) :
    (∀ γ ∈ guardPts x g, γ ∈ P.boundary) ∧ ∀ p ∈ P.filled, ∃ γ ∈ guardPts x g, P.Sees γ p := by
  obtain ⟨hb, hg⟩ := h
  rw [ronBoundaryF, holds_bigAnd_range] at hb
  refine ⟨fun γ hγ => ?_, (guards_of_holds_rguardsF hP hC hg).2⟩
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
  exact (holds_rboundaryF hC (PRep.guard x a)).1 (hb a (List.mem_range.1 ha))

/-- **Boundary-point GUARDS is complete.** -/
theorem holds_rbpguardsF_of_guards (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (hon : ∀ a < g, guardPt x a ∈ P.boundary)
    (hsees : ∀ p ∈ P.filled, ∃ a < g, P.Sees (guardPt x a) p) :
    (rbpguardsF C g).Holds x := by
  refine ⟨?_, holds_rguardsF_of_guards hP hC
    (fun a ha => Jordan.boundary_subset_filled P (hon a ha)) hsees⟩
  rw [ronBoundaryF, holds_bigAnd_range]
  intro a ha
  exact (holds_rboundaryF hC (PRep.guard x a)).2 (hon a ha)

theorem FVars_rbpguardsF {g : ℕ} (hC : CornersV (· < 2 * g) C) :
    FVars (· < 2 * g) (rbpguardsF C g) := by
  refine ⟨?_, FVars_rguardsF hC⟩
  rw [ronBoundaryF, FVars_bigAnd]
  intro φ hφ
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
  have ha' := List.mem_range.1 ha
  rw [rboundaryF, FVars_bigOr]
  intro ψ hψ
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hψ
  exact FVars_ronSegF (PV.var (show 2 * a < 2 * g by omega) (show 2 * a + 1 < 2 * g by omega))
    (hC _) (hC _)

/-! ## The reduction -/

/-- **The formula of a boundary-point instance** with vertex digits `D` and `g` guards. -/
def fvbpFormulaD (D : List FracDigits) (g : ℕ) : Formula :=
  if validBD D then
    if D.length ≤ g + 2 then rsimpleF (cornersD D)
    else .and (rsimpleF (cornersD D)) (rbpguardsF (cornersD D) g)
  else fFalse

/-- **The reduction from the boundary-point AGP to ETR with only guard variables.** -/
def fvbpToETR (w : Word) : Formula :=
  match ArtGallery.decodeAGP w with
  | none => fFalse
  | some (D, gd) => fvbpFormulaD D (min (SAT.binaryValue gd) (D.length + 3))

theorem fvbpFormulaD_complete {V : List FracPoint} {g : ℕ} (hV : ∀ p ∈ V, p.Valid)
    (hS : (polyOf V).Simple) (hG : (polyOf V).HasGuardSetOnBoundaryOfCard g) :
    (fvbpFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable := by
  unfold fvbpFormulaD
  rw [ite_eq_left (by rw [← validB_eq_validBD]; exact (validB_iff V).2 hV), List.length_map]
  split_ifs with hng
  · exact ⟨fun _ => 0, (holds_rsimpleF (cornersRep_of_valid _ hV)).2 hS⟩
  · have hg : min g (V.length + 3) = g := by omega
    rw [hg]
    obtain ⟨G, hcard, hGsub, hGsees⟩ := hG
    have hlen : G.toList.length = g := by rw [Finset.length_toList, hcard]
    let γv : ℕ → Point := fun a => if h : a < G.toList.length then G.toList[a] else 0
    have hγG : ∀ a < g, γv a ∈ G := fun a ha => by
      have ha' : a < G.toList.length := by omega
      simp only [γv, dite_eq_left ha']
      exact Finset.mem_toList.1 (List.getElem_mem ha')
    let y : ℕ → ℝ := fun v => if v % 2 = 0 then (γv (v / 2)).1 else (γv (v / 2)).2
    have hy : ∀ a, guardPt y a = γv a := fun a => by
      have e1 : 2 * a % 2 = 0 := by omega
      have e2 : ¬ (2 * a + 1) % 2 = 0 := by omega
      have e3 : 2 * a / 2 = a := by omega
      have e4 : (2 * a + 1) / 2 = a := by omega
      simp only [guardPt, y, e1, e2, e3, e4, ite_true, ite_false]
    have hC := cornersRep_of_valid y hV
    refine ⟨y, (holds_rsimpleF hC).2 hS, holds_rbpguardsF_of_guards hS hC ?_ ?_⟩
    · intro a ha
      rw [hy]; exact hGsub (hγG a ha)
    · intro p hp
      obtain ⟨γ, hγ, hs⟩ := hGsees p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hγ)
      refine ⟨a, by omega, ?_⟩
      rw [hy]
      simp only [γv, dite_eq_left ha]
      exact hs

theorem fvbpFormulaD_sound {V : List FracPoint} {g : ℕ}
    (h : (fvbpFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable) :
    (∀ p ∈ V, p.Valid) ∧ (polyOf V).Simple ∧ (polyOf V).HasGuardSetOnBoundaryOfCard g := by
  obtain ⟨y, hy⟩ := h
  unfold fvbpFormulaD at hy
  by_cases hv : validBD (V.map FracPoint.digits) = true
  · rw [ite_eq_left hv, List.length_map] at hy
    have hV : ∀ p ∈ V, p.Valid := (validB_iff V).1 (by rw [validB_eq_validBD]; exact hv)
    have hn : (polyOf V).n = V.length := polyOf_n V
    have hC := cornersRep_of_valid y hV
    split_ifs at hy with hng
    · have hS := (holds_rsimpleF hC).1 hy
      exact ⟨hV, hS, HasGuardSetOnBoundaryOfCard.mono hS
        (hasGuardSetOnBoundaryOfCard_n_sub_two hS) (by omega)⟩
    · obtain ⟨hs, hgd⟩ := hy
      have hS := (holds_rsimpleF hC).1 hs
      have hg : min g (V.length + 3) = g := by omega
      rw [hg] at hgd
      refine ⟨hV, hS, ?_⟩
      obtain ⟨hΓ, hsees⟩ := bpguards_of_holds hS hC hgd
      set Γ := guardPts y g
      have hcard : Γ.toFinset.card ≤ g := by
        have := List.toFinset_card_le Γ
        simpa [Γ, guardPts] using this
      have hGS : (polyOf V).IsGuardSetOnBoundary (Γ.toFinset : Set Point) := by
        refine ⟨fun γ hγ => hΓ γ (List.mem_toFinset.1 hγ), fun p hp => ?_⟩
        obtain ⟨γ, hγ, hs⟩ := hsees p hp
        exact ⟨γ, List.mem_toFinset.2 hγ, hs⟩
      exact HasGuardSetOnBoundaryOfCard.mono hS ⟨Γ.toFinset, rfl, hGS⟩ hcard
  · rw [ite_eq_right hv] at hy
    exact absurd hy (not_holds_fFalse y)

theorem fvbpToETR_encodeAGP (V : List FracPoint) (g : ℕ) :
    fvbpToETR (encodeAGP V g) = fvbpFormulaD (V.map FracPoint.digits) (min g (V.length + 3)) := by
  simp [fvbpToETR, ArtGallery.decodeAGP_encodeAGP, binaryValue_bits]

/-- **Correctness of the reduction.** -/
theorem fvbpToETR_correct (w : Word) : AGPBoundaryPoint w ↔ (fvbpToETR w).Satisfiable := by
  cases h : ArtGallery.decodeAGP w with
  | none =>
    have hfalse : fvbpToETR w = fFalse := by simp [fvbpToETR, h]
    rw [hfalse]
    constructor
    · rintro ⟨V, g, rfl, -⟩
      rw [ArtGallery.decodeAGP_encodeAGP] at h
      exact absurd h (by simp)
    · rintro ⟨y, hy⟩
      exact absurd hy (not_holds_fFalse y)
  | some r =>
    obtain ⟨D, gd⟩ := r
    obtain ⟨V, g, rfl, rfl, rfl⟩ := ArtGallery.decodeAGP_sound h
    rw [fvbpToETR_encodeAGP]
    constructor
    · rintro ⟨V', g', h', hval, hS, hG⟩
      obtain ⟨rfl, rfl⟩ := encodeAGP_inj h'
      exact fvbpFormulaD_complete hval hS hG
    · intro hs
      obtain ⟨hval, hS, hG⟩ := fvbpFormulaD_sound hs
      exact ⟨V, g, rfl, hval, hS, hG⟩

/-- **Only the guard coordinates are variables.** -/
theorem fvbpToETR_encodeAGP_varsLt (V : List FracPoint) (g : ℕ) :
    (fvbpToETR (encodeAGP V g)).VarsLt (2 * g) := by
  rw [fvbpToETR_encodeAGP]
  have hF : ∀ D h, FVars (· < 2 * h) (fvbpFormulaD D h) := by
    intro D h
    unfold fvbpFormulaD
    split_ifs
    · exact FVars_rsimpleF (cornersV_cornersD _ D)
    · exact ⟨FVars_rsimpleF (cornersV_cornersD _ D), FVars_rbpguardsF (cornersV_cornersD _ D)⟩
    · exact FVars_fFalse _
  refine fvars_varsLt ((hF _ _).mono fun v hv => ?_)
  have : min g (V.length + 3) ≤ g := min_le_left _ _
  show v < 2 * g
  have : v < 2 * min g (V.length + 3) := hv
  omega

/-! ## Polynomial time -/

section PTLemmas

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.ronBoundaryF {C : α → List RPt} {g : α → ℕ} (hC : PT C)
    (hg : PT g) : PT (fun a => ronBoundaryF (C a) (g a)) := by
  unfold ronBoundaryF; fun_prop

@[fun_prop] protected theorem PT.rbpguardsF {C : α → List RPt} {g : α → ℕ} (hC : PT C)
    (hg : PT g) : PT (fun a => rbpguardsF (C a) (g a)) := by
  unfold rbpguardsF; fun_prop

@[fun_prop] protected theorem PT.fvbpFormulaD {D : α → List FracDigits} {g : α → ℕ} (hD : PT D)
    (hg : PT g) : PT (fun a => fvbpFormulaD (D a) (g a)) := by
  unfold fvbpFormulaD; fun_prop

end PTLemmas

/-- **The boundary-point reduction is polynomial-time.** -/
protected theorem PT.fvbpToETR : PT fvbpToETR := by
  refine PT.of_optionCases (o := ArtGallery.decodeAGP) (d := fun _ => fFalse)
    (f := fun _ r => fvbpFormulaD r.1 (min (SAT.binaryValue r.2) (r.1.length + 3)))
    (PT.decodeAGP PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [fvbpToETR, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [fvbpToETR, h]

end ArtGallery.FewVars.BoundaryPoint

end
