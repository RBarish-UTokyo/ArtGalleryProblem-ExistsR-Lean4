module

public import ArtGallery.FewVars.Boundary.Cover
public import ArtGallery.FewVars.PT

/-!
# The formula for the point-boundary art gallery problem

`rbguardsF C g`: the `g` guards `rguard a` are INSIDE, and for every edge `e` and every pair of
breakpoints of `e` (`rebT`, with divisors `rebD`, the rational-term versions of `ebT`, `ebD`)
with nonzero divisors and values in `[0, 1]`, some guard SEES the point of the edge at their
midpoint.  By the boundary witness lemma (`boundary_seen_of_witnesses`) this holds iff the
guards lie in the region and see its boundary.

`fvbFormulaD D g` is SIMPLE (if `n ≤ g + 2`; `n - 2` guards guard the whole region) or
SIMPLE ∧ boundary GUARDS; `fvbToETR` decodes the instance.  Main results:
`fvbToETR_correct : AGPPointBoundary w ↔ (fvbToETR w).Satisfiable`,
`fvbToETR_encodeAGP_varsLt` and `PT.fvbToETR`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.FewVars.Boundary

open ArtGallery.ETR ArtGallery.Membership ArtGallery.FewVars Complexity Complexity.PT
  Complexity.PT.Code
open ArtGallery.Geometry (lerp lerp_mem_segment)

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

/-! ## Padding boundary guard sets -/

/-- A boundary guard set can be enlarged by one point. -/
theorem hasBoundaryGuardSetOfCard_succ (hP : P.Simple) {k : ℕ}
    (h : P.HasBoundaryGuardSetOfCard k) : P.HasBoundaryGuardSetOfCard (k + 1) := by
  classical
  obtain ⟨G, hG, hsub, hsee⟩ := h
  obtain ⟨y, hyf, hyG⟩ := (Vis.filled_infinite hP).exists_notMem_finset G
  refine ⟨insert y G, by rw [Finset.card_insert_of_notMem hyG, hG], ?_, ?_⟩
  · intro z hz
    rw [Finset.coe_insert] at hz
    rcases hz with rfl | hz
    · exact hyf
    · exact hsub hz
  · intro p hp
    obtain ⟨γ, hγ, hγp⟩ := hsee p hp
    refine ⟨γ, ?_, hγp⟩
    rw [Finset.coe_insert]
    exact Or.inr hγ

/-- **Padding** for boundary guard sets. -/
theorem HasBoundaryGuardSetOfCard.mono (hP : P.Simple) {k k' : ℕ}
    (h : P.HasBoundaryGuardSetOfCard k) (hk : k ≤ k') : P.HasBoundaryGuardSetOfCard k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact h
  | succ d ih => exact hasBoundaryGuardSetOfCard_succ hP ih

/-- A guard set guards the boundary. -/
theorem HasGuardSetOfCard.boundary {k : ℕ} (h : P.HasGuardSetOfCard k) :
    P.HasBoundaryGuardSetOfCard k := by
  obtain ⟨G, hG, hsub, hsee⟩ := h
  exact ⟨G, hG, hsub, fun p hp => hsee p (Jordan.boundary_subset_filled P hp)⟩

/-! ## Breakpoints as rational terms -/

/-- The divisor of breakpoint `α` of edge `e`. -/
def rebD (C : List RPt) (e α : ℕ) : RTerm :=
  if α < 2 then rone
  else rsub (rdetT (rline C (α - 2)).1 (rline C (α - 2)).2 (cr C ((e + 1) % C.length)))
    (rdetT (rline C (α - 2)).1 (rline C (α - 2)).2 (cr C e))

/-- Breakpoint `α` of edge `e`. -/
def rebT (C : List RPt) (e α : ℕ) : RTerm :=
  if α = 0 then rzero else if α = 1 then rone
  else rdiv (rneg (rdetT (rline C (α - 2)).1 (rline C (α - 2)).2 (cr C e))) (rebD C e α)

theorem rep_rebD (hC : CornersRep x P C) {g e α : ℕ} (he : e < P.n)
    (hα : α < numLines P.n g + 2) : Rep x (rebD C e α) (ebD P (guardPt x) e α) := by
  unfold rebD ebD
  split_ifs with h
  · exact Rep.one x
  · have hl := lrep_rline hC (g := g) (i := α - 2) (by omega)
    rw [hC.1]
    exact Rep.sub (Rep.det hl.1 hl.2 (hC.next' he)) (Rep.det hl.1 hl.2 (hC.vtx he))

theorem rep_rebT (hC : CornersRep x P C) {g e α : ℕ} (he : e < P.n)
    (hα : α < numLines P.n g + 2) (hD : ebD P (guardPt x) e α ≠ 0) :
    Rep x (rebT C e α) (ebT P (guardPt x) e α) := by
  have hDr := rep_rebD hC he hα
  unfold rebT ebT
  split_ifs with h0 h1
  · exact Rep.zero x
  · exact Rep.one x
  · have hl := lrep_rline hC (g := g) (i := α - 2) (by omega)
    exact Rep.div (Rep.neg (Rep.det hl.1 hl.2 (hC.vtx he))) hDr hD

/-! ## The formula -/

/-- The witness test for edge `e` and the pair `p = α M + β` of breakpoints (`M = m + 2`). -/
def rbwitF (C : List RPt) (g e p : ℕ) : Formula :=
  fImp (.and (rneF (rebD C e (p / (numLines C.length g + 2))))
      (.and (rneF (rebD C e (p % (numLines C.length g + 2))))
        (.and (runitF (rebT C e (p / (numLines C.length g + 2))))
          (runitF (rebT C e (p % (numLines C.length g + 2)))))))
    (bigOr ((List.range g).map fun a => rseesF C (rguard a)
      (rlerpT (cr C e) (cr C ((e + 1) % C.length))
        (rdiv (radd (rebT C e (p / (numLines C.length g + 2)))
          (rebT C e (p % (numLines C.length g + 2)))) rtwo))))

/-- The witness tests of edge `e`. -/
def rbedgeF (C : List RPt) (g e : ℕ) : Formula :=
  bigAnd ((List.range ((numLines C.length g + 2) * (numLines C.length g + 2))).map
    (rbwitF C g e))

/-- **Boundary GUARDS**: the guards are in the region and see every boundary witness point. -/
def rbguardsF (C : List RPt) (g : ℕ) : Formula :=
  .and (bigAnd ((List.range g).map fun a => rinsideF C (rguard a)))
    (bigAnd ((List.range C.length).map (rbedgeF C g)))

theorem holds_rbwitF (hP : P.Simple) (hC : CornersRep x P C) {g e α β : ℕ} (he : e < P.n)
    (hα : α < numLines P.n g + 2) (hβ : β < numLines P.n g + 2) :
    (rbwitF C g e (α * (numLines P.n g + 2) + β)).Holds x ↔
      (ebD P (guardPt x) e α ≠ 0 → ebD P (guardPt x) e β ≠ 0 →
        0 ≤ ebT P (guardPt x) e α → ebT P (guardPt x) e α ≤ 1 →
        0 ≤ ebT P (guardPt x) e β → ebT P (guardPt x) e β ≤ 1 →
        ∃ a < g, P.Sees (guardPt x a) (lerp (P.vtx e) (P.vtx ((e + 1) % P.n))
          ((ebT P (guardPt x) e α + ebT P (guardPt x) e β) / 2))) := by
  rw [rbwitF, hC.1, pair_div hβ, pair_mod hβ, holds_fImp, holds_and, holds_and, holds_and,
    holds_rneF (rep_rebD hC he hα), holds_rneF (rep_rebD hC he hβ)]
  have hpt : ∀ hDa : ebD P (guardPt x) e α ≠ 0, ∀ hDb : ebD P (guardPt x) e β ≠ 0,
      (bigOr ((List.range g).map fun a => rseesF C (rguard a)
        (rlerpT (cr C e) (cr C ((e + 1) % P.n))
          (rdiv (radd (rebT C e α) (rebT C e β)) rtwo)))).Holds x ↔
      ∃ a < g, P.Sees (guardPt x a) (lerp (P.vtx e) (P.vtx ((e + 1) % P.n))
          ((ebT P (guardPt x) e α + ebT P (guardPt x) e β) / 2)) := by
    intro hDa hDb
    have hq := PRep.lerp (hC.vtx he) (hC.next' he)
      (Rep.div (Rep.add (rep_rebT hC he hα hDa) (rep_rebT hC he hβ hDb)) (Rep.two x)
        two_ne_zero)
    rw [holds_bigOr_range]
    constructor
    · rintro ⟨a, ha, hs⟩
      exact ⟨a, ha, (holds_rseesF hP hC (PRep.guard x a) hq).1 hs⟩
    · rintro ⟨a, ha, hs⟩
      exact ⟨a, ha, (holds_rseesF hP hC (PRep.guard x a) hq).2 hs⟩
  constructor
  · intro h hDa hDb ha0 ha1 hb0 hb1
    rw [holds_runitF (rep_rebT hC he hα hDa), holds_runitF (rep_rebT hC he hβ hDb)] at h
    exact (hpt hDa hDb).1 (h ⟨hDa, hDb, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩)
  · rintro h ⟨hDa, hDb, hua, hub⟩
    rw [holds_runitF (rep_rebT hC he hα hDa)] at hua
    rw [holds_runitF (rep_rebT hC he hβ hDb)] at hub
    exact (hpt hDa hDb).2 (h hDa hDb hua.1 hua.2 hub.1 hub.2)

/-- **Boundary GUARDS is sound.** -/
theorem bguards_of_holds (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (h : (rbguardsF C g).Holds x) :
    (∀ γ ∈ guardPts x g, γ ∈ P.filled) ∧ ∀ p ∈ P.boundary, ∃ γ ∈ guardPts x g, P.Sees γ p := by
  obtain ⟨hg, hw⟩ := h
  rw [holds_bigAnd_range] at hg hw
  have hin : ∀ a < g, guardPt x a ∈ P.filled := fun a ha =>
    (holds_rinsideF hP hC (PRep.guard x a)).1 (hg a ha)
  refine ⟨fun γ hγ => ?_, fun p hp => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hγ
    exact hin a (List.mem_range.1 ha)
  · obtain ⟨a, ha, hs⟩ := boundary_seen_of_witnesses hP (guardPt x) g hin (by
      intro e he α hα β hβ
      have he' : e < C.length := by rw [hC.1]; exact he
      have := hw e he'
      rw [rbedgeF, holds_bigAnd_range, hC.1] at this
      exact (holds_rbwitF hP hC he hα hβ).1 (this _ (pair_lt hα hβ))) p hp
    exact ⟨guardPt x a, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩, hs⟩

/-- **Boundary GUARDS is complete.** -/
theorem holds_rbguardsF_of_guards (hP : P.Simple) (hC : CornersRep x P C) {g : ℕ}
    (hin : ∀ a < g, guardPt x a ∈ P.filled)
    (hsees : ∀ p ∈ P.boundary, ∃ a < g, P.Sees (guardPt x a) p) :
    (rbguardsF C g).Holds x := by
  refine ⟨?_, ?_⟩
  · rw [holds_bigAnd_range]
    intro a ha
    exact (holds_rinsideF hP hC (PRep.guard x a)).2 (hin a ha)
  · rw [holds_bigAnd_range]
    intro e he
    rw [hC.1] at he
    rw [rbedgeF, holds_bigAnd_range, hC.1]
    intro p hp
    have hN : 0 < numLines P.n g + 2 := by omega
    have hα : p / (numLines P.n g + 2) < numLines P.n g + 2 := Nat.div_lt_of_lt_mul hp
    have hβ : p % (numLines P.n g + 2) < numLines P.n g + 2 := Nat.mod_lt _ hN
    have := (holds_rbwitF hP hC he hα hβ (g := g)).2 (fun _ _ ha0 ha1 hb0 hb1 =>
      hsees _ ⟨e, he, lerp_mem_segment _ _ (by linarith) (by linarith)⟩)
    rwa [Nat.div_add_mod'] at this

/-! ## Variables -/

theorem FVars_rbguardsF {g : ℕ} (hC : CornersV (· < 2 * g) C) :
    FVars (· < 2 * g) (rbguardsF C g) := by
  have hγ : ∀ a < g, PV (· < 2 * g) (rguard a) := fun a ha =>
    PV.var (show 2 * a < 2 * g by omega) (show 2 * a + 1 < 2 * g by omega)
  have hl : ∀ i < numLines C.length g, PV (· < 2 * g) (rline C i).1 ∧
      PV (· < 2 * g) (rline C i).2 := by
    intro i hi
    unfold rline
    split_ifs with h
    · exact ⟨hC _, hC _⟩
    · refine ⟨hγ _ ?_, hC _⟩
      have hn : 0 < C.length := by
        rcases Nat.eq_zero_or_pos C.length with h0 | h0
        · rw [h0] at hi h; simp [numLines] at hi
        · exact h0
      apply Nat.div_lt_of_lt_mul
      unfold numLines at hi
      rw [Nat.mul_comm]; omega
  have hD : ∀ e, ∀ α < numLines C.length g + 2, RVars (· < 2 * g) (rebD C e α) := by
    intro e α hα
    unfold rebD
    split_ifs
    · exact RVars.one
    · have := hl (α - 2) (by omega)
      exact (RVars.det this.1 this.2 (hC _)).sub (RVars.det this.1 this.2 (hC _))
  have hT : ∀ e, ∀ α < numLines C.length g + 2, RVars (· < 2 * g) (rebT C e α) := by
    intro e α hα
    unfold rebT
    split_ifs
    · exact RVars.zero
    · exact RVars.one
    · have := hl (α - 2) (by omega)
      exact (RVars.det this.1 this.2 (hC _)).neg.div (hD e α hα)
  refine ⟨?_, ?_⟩
  · rw [FVars_bigAnd]
    intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
    exact FVars_rinsideF hC (hγ a (List.mem_range.1 ha))
  · rw [FVars_bigAnd]
    intro φ hφ
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hφ
    rw [rbedgeF, FVars_bigAnd]
    intro ψ hψ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hψ
    rw [List.mem_range] at hp
    have hN : 0 < numLines C.length g + 2 := by omega
    have hα : p / (numLines C.length g + 2) < numLines C.length g + 2 :=
      Nat.div_lt_of_lt_mul hp
    have hβ : p % (numLines C.length g + 2) < numLines C.length g + 2 := Nat.mod_lt _ hN
    refine ⟨⟨FVars_rneF (hD e _ hα), FVars_rneF (hD e _ hβ), FVars_runitF (hT e _ hα),
      FVars_runitF (hT e _ hβ)⟩, ?_⟩
    rw [FVars_bigOr]
    intro χ hχ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hχ
    exact FVars_rseesF hC (hγ a (List.mem_range.1 ha))
      (PV.lerp (hC _) (hC _) (((hT e _ hα).add (hT e _ hβ)).div RVars.two))

/-! ## The reduction -/

/-- **The formula of a point-boundary instance** with vertex digits `D` and `g` guards. -/
def fvbFormulaD (D : List FracDigits) (g : ℕ) : Formula :=
  if validBD D then
    if D.length ≤ g + 2 then rsimpleF (cornersD D)
    else .and (rsimpleF (cornersD D)) (rbguardsF (cornersD D) g)
  else fFalse

/-- **The reduction from the point-boundary AGP to ETR with only guard variables.** -/
def fvbToETR (w : Word) : Formula :=
  match ArtGallery.decodeAGP w with
  | none => fFalse
  | some (D, gd) => fvbFormulaD D (min (SAT.binaryValue gd) (D.length + 3))

theorem fvbFormulaD_complete {V : List FracPoint} {g : ℕ} (hV : ∀ p ∈ V, p.Valid)
    (hS : (polyOf V).Simple) (hG : (polyOf V).HasBoundaryGuardSetOfCard g) :
    (fvbFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable := by
  unfold fvbFormulaD
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
    refine ⟨y, (holds_rsimpleF hC).2 hS, holds_rbguardsF_of_guards hS hC ?_ ?_⟩
    · intro a ha
      rw [hy]; exact hGsub (hγG a ha)
    · intro p hp
      obtain ⟨γ, hγ, hs⟩ := hGsees p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hγ)
      refine ⟨a, by omega, ?_⟩
      rw [hy]
      simp only [γv, dite_eq_left ha]
      exact hs

theorem fvbFormulaD_sound {V : List FracPoint} {g : ℕ}
    (h : (fvbFormulaD (V.map FracPoint.digits) (min g (V.length + 3))).Satisfiable) :
    (∀ p ∈ V, p.Valid) ∧ (polyOf V).Simple ∧ (polyOf V).HasBoundaryGuardSetOfCard g := by
  obtain ⟨y, hy⟩ := h
  unfold fvbFormulaD at hy
  by_cases hv : validBD (V.map FracPoint.digits) = true
  · rw [ite_eq_left hv, List.length_map] at hy
    have hV : ∀ p ∈ V, p.Valid := (validB_iff V).1 (by rw [validB_eq_validBD]; exact hv)
    have hn : (polyOf V).n = V.length := polyOf_n V
    have hC := cornersRep_of_valid y hV
    split_ifs at hy with hng
    · have hS := (holds_rsimpleF hC).1 hy
      exact ⟨hV, hS, HasBoundaryGuardSetOfCard.mono hS
        (HasGuardSetOfCard.boundary (Polygon.hasGuardSetOfCard_n_sub_two hS)) (by omega)⟩
    · obtain ⟨hs, hgd⟩ := hy
      have hS := (holds_rsimpleF hC).1 hs
      have hg : min g (V.length + 3) = g := by omega
      rw [hg] at hgd
      refine ⟨hV, hS, ?_⟩
      obtain ⟨hΓ, hsees⟩ := bguards_of_holds hS hC hgd
      set Γ := guardPts y g
      have hcard : Γ.toFinset.card ≤ g := by
        have := List.toFinset_card_le Γ
        simpa [Γ, guardPts] using this
      have hGS : (polyOf V).IsBoundaryGuardSet (Γ.toFinset : Set Point) := by
        refine ⟨fun γ hγ => hΓ γ (List.mem_toFinset.1 hγ), fun p hp => ?_⟩
        obtain ⟨γ, hγ, hs⟩ := hsees p hp
        exact ⟨γ, List.mem_toFinset.2 hγ, hs⟩
      exact HasBoundaryGuardSetOfCard.mono hS ⟨Γ.toFinset, rfl, hGS⟩ hcard
  · rw [ite_eq_right hv] at hy
    exact absurd hy (not_holds_fFalse y)

theorem fvbToETR_encodeAGP (V : List FracPoint) (g : ℕ) :
    fvbToETR (encodeAGP V g) = fvbFormulaD (V.map FracPoint.digits) (min g (V.length + 3)) := by
  simp [fvbToETR, ArtGallery.decodeAGP_encodeAGP, binaryValue_bits]

/-- **Correctness of the reduction.** -/
theorem fvbToETR_correct (w : Word) : AGPPointBoundary w ↔ (fvbToETR w).Satisfiable := by
  cases h : ArtGallery.decodeAGP w with
  | none =>
    have hfalse : fvbToETR w = fFalse := by simp [fvbToETR, h]
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
    rw [fvbToETR_encodeAGP]
    constructor
    · rintro ⟨V', g', h', hval, hS, hG⟩
      obtain ⟨rfl, rfl⟩ := encodeAGP_inj h'
      exact fvbFormulaD_complete hval hS hG
    · intro hs
      obtain ⟨hval, hS, hG⟩ := fvbFormulaD_sound hs
      exact ⟨V, g, rfl, hval, hS, hG⟩

/-- **Only the guard coordinates are variables.** -/
theorem fvbToETR_encodeAGP_varsLt (V : List FracPoint) (g : ℕ) :
    (fvbToETR (encodeAGP V g)).VarsLt (2 * g) := by
  rw [fvbToETR_encodeAGP]
  have hF : ∀ D h, FVars (· < 2 * h) (fvbFormulaD D h) := by
    intro D h
    unfold fvbFormulaD
    split_ifs
    · exact FVars_rsimpleF (cornersV_cornersD _ D)
    · exact ⟨FVars_rsimpleF (cornersV_cornersD _ D), FVars_rbguardsF (cornersV_cornersD _ D)⟩
    · exact FVars_fFalse _
  refine fvars_varsLt ((hF _ _).mono fun v hv => ?_)
  have : min g (V.length + 3) ≤ g := min_le_left _ _
  show v < 2 * g
  have : v < 2 * min g (V.length + 3) := hv
  omega

/-! ## Polynomial time -/

section PTLemmas

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.rebD {C : α → List RPt} {e i : α → ℕ} (hC : PT C) (he : PT e)
    (hi : PT i) : PT (fun a => rebD (C a) (e a) (i a)) := by
  unfold rebD; fun_prop

@[fun_prop] protected theorem PT.rebT {C : α → List RPt} {e i : α → ℕ} (hC : PT C) (he : PT e)
    (hi : PT i) : PT (fun a => rebT (C a) (e a) (i a)) := by
  unfold rebT; fun_prop

@[fun_prop] protected theorem PT.rbwitF {C : α → List RPt} {g e p : α → ℕ} (hC : PT C)
    (hg : PT g) (he : PT e) (hp : PT p) : PT (fun a => rbwitF (C a) (g a) (e a) (p a)) := by
  unfold rbwitF; fun_prop

@[fun_prop] protected theorem PT.rbedgeF {C : α → List RPt} {g e : α → ℕ} (hC : PT C)
    (hg : PT g) (he : PT e) : PT (fun a => rbedgeF (C a) (g a) (e a)) := by
  unfold rbedgeF; fun_prop

@[fun_prop] protected theorem PT.rbguardsF {C : α → List RPt} {g : α → ℕ} (hC : PT C)
    (hg : PT g) : PT (fun a => rbguardsF (C a) (g a)) := by
  unfold rbguardsF; fun_prop

@[fun_prop] protected theorem PT.fvbFormulaD {D : α → List FracDigits} {g : α → ℕ} (hD : PT D)
    (hg : PT g) : PT (fun a => fvbFormulaD (D a) (g a)) := by
  unfold fvbFormulaD; fun_prop

end PTLemmas

/-- **The boundary reduction is polynomial-time.** -/
protected theorem PT.fvbToETR : PT fvbToETR := by
  refine PT.of_optionCases (o := ArtGallery.decodeAGP) (d := fun _ => fFalse)
    (f := fun _ r => fvbFormulaD r.1 (min (SAT.binaryValue r.2) (r.1.length + 3)))
    (PT.decodeAGP PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [fvbToETR, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [fvbToETR, h]

end ArtGallery.FewVars.Boundary

end
