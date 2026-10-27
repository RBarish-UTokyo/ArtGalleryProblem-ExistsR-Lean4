module

public import ArtGallery.FewVars.Inside
public import ArtGallery.Membership.Sees

/-!
# SEES without auxiliary variables

`rseesF C γ c` expresses that the segment `[γ, c]` lies in the closed region of the polygon with
corner list `C`.  The breakpoints (`bpT`) are explicit rational terms, each with its divisor:

* `0` and `1`;
* for every edge `j`: the parameter `-det(v_j, v_{j+1}, γ) / ((v_{j+1} - v_j) × (c - γ))` of the
  intersection of the line `γc` with the line of the edge (divisor: the cross product);
* for every corner `k`: the parameter `((v_k - γ) · (c - γ)) / |c - γ|²` of the projection of the
  corner onto the line `γc` (divisor: `|c - γ|²`).

For every pair of breakpoints with nonzero divisors and values in `[0, 1]`, the point of the
segment at their midpoint must be INSIDE.  Extra breakpoints are harmless, so no case
distinctions beyond the divisors are needed.  Main result: `holds_rseesF`.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

/-- The divisor of breakpoint `α`. -/
def bpD (C : List RPt) (γ c : RPt) (α : ℕ) : RTerm :=
  if α < 2 then rone
  else if α < C.length + 2 then
    rcrossT (cr C (α - 2)) (cr C ((α - 2 + 1) % C.length)) γ c
  else rdotT γ c γ c

/-- The value of breakpoint `α`. -/
def bpT (C : List RPt) (γ c : RPt) (α : ℕ) : RTerm :=
  if α = 0 then rzero
  else if α = 1 then rone
  else if α < C.length + 2 then
    rdiv (rneg (rdetT (cr C (α - 2)) (cr C ((α - 2 + 1) % C.length)) γ)) (bpD C γ c α)
  else rdiv (rdotT γ (cr C (α - 2 - C.length)) γ c) (bpD C γ c α)

/-- The real divisor of breakpoint `α`. -/
noncomputable def bpDR (P : Polygon) (γ c : Point) (α : ℕ) : ℝ :=
  if α < 2 then 1
  else if α < P.n + 2 then crossR (P.vtx (α - 2)) (P.vtx ((α - 2 + 1) % P.n)) γ c
  else dotR γ c γ c

/-- The real value of breakpoint `α`. -/
noncomputable def bpR (P : Polygon) (γ c : Point) (α : ℕ) : ℝ :=
  if α = 0 then 0
  else if α = 1 then 1
  else if α < P.n + 2 then
    -det (P.vtx (α - 2)) (P.vtx ((α - 2 + 1) % P.n)) γ / bpDR P γ c α
  else dotR γ (P.vtx (α - 2 - P.n)) γ c / bpDR P γ c α

variable {γ c : RPt} {γ' c' : Point}

theorem rep_bpD (hC : CornersRep x P C) (hγ : PRep x γ γ') (hc : PRep x c c') {α : ℕ}
    (_hα : α < 2 * P.n + 2) : Rep x (bpD C γ c α) (bpDR P γ' c' α) := by
  unfold bpD bpDR
  rw [hC.1]
  split_ifs with h1 h2
  · exact Rep.one x
  · exact Rep.cross (hC.vtx (by omega)) (hC.next' (by omega)) hγ hc
  · exact Rep.dot hγ hc hγ hc

theorem rep_bpT (hC : CornersRep x P C) (hγ : PRep x γ γ') (hc : PRep x c c') {α : ℕ}
    (hα : α < 2 * P.n + 2) (hD : bpDR P γ' c' α ≠ 0) : Rep x (bpT C γ c α) (bpR P γ' c' α) := by
  have hDr := rep_bpD hC hγ hc hα
  unfold bpT bpR
  rw [hC.1]
  split_ifs with h0 h1 h2
  · exact Rep.zero x
  · exact Rep.one x
  · exact Rep.div (Rep.neg (Rep.det (hC.vtx (by omega)) (hC.next' (by omega)) hγ)) hDr hD
  · exact Rep.div (Rep.dot hγ (hC.vtx (by omega)) hγ hc) hDr hD

/-- The midpoint test for the pair `p = α (2n + 2) + β` of breakpoints. -/
def rpairF (C : List RPt) (γ c : RPt) (p : ℕ) : Formula :=
  fImp (.and (rneF (bpD C γ c (p / (2 * C.length + 2))))
      (.and (rneF (bpD C γ c (p % (2 * C.length + 2))))
        (.and (runitF (bpT C γ c (p / (2 * C.length + 2))))
          (runitF (bpT C γ c (p % (2 * C.length + 2)))))))
    (rinsideF C (rlerpT γ c (rdiv (radd (bpT C γ c (p / (2 * C.length + 2)))
      (bpT C γ c (p % (2 * C.length + 2)))) rtwo)))

/-- **SEES**: the segment `[γ, c]` lies in the closed region. -/
def rseesF (C : List RPt) (γ c : RPt) : Formula :=
  bigAnd ((List.range ((2 * C.length + 2) * (2 * C.length + 2))).map (rpairF C γ c))

/-- The pair test, semantically. -/
theorem holds_rpairF (hP : P.Simple) (hC : CornersRep x P C) (hγ : PRep x γ γ')
    (hc : PRep x c c') {α β : ℕ} (hα : α < 2 * P.n + 2) (hβ : β < 2 * P.n + 2) :
    (rpairF C γ c (α * (2 * P.n + 2) + β)).Holds x ↔
      (bpDR P γ' c' α ≠ 0 → bpDR P γ' c' β ≠ 0 → 0 ≤ bpR P γ' c' α → bpR P γ' c' α ≤ 1 →
        0 ≤ bpR P γ' c' β → bpR P γ' c' β ≤ 1 →
        lerp γ' c' ((bpR P γ' c' α + bpR P γ' c' β) / 2) ∈ P.filled) := by
  rw [rpairF, hC.1, pair_div hβ, pair_mod hβ, holds_fImp, holds_and, holds_and, holds_and,
    holds_rneF (rep_bpD hC hγ hc hα), holds_rneF (rep_bpD hC hγ hc hβ)]
  constructor
  · intro h hDa hDb ha0 ha1 hb0 hb1
    have hTa := rep_bpT hC hγ hc hα hDa
    have hTb := rep_bpT hC hγ hc hβ hDb
    rw [holds_runitF hTa, holds_runitF hTb] at h
    have := h ⟨hDa, hDb, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
    rwa [holds_rinsideF hP hC
      (PRep.lerp hγ hc (Rep.div (Rep.add hTa hTb) (Rep.two x) two_ne_zero))] at this
  · rintro h ⟨hDa, hDb, hua, hub⟩
    have hTa := rep_bpT hC hγ hc hα hDa
    have hTb := rep_bpT hC hγ hc hβ hDb
    rw [holds_runitF hTa] at hua
    rw [holds_runitF hTb] at hub
    rw [holds_rinsideF hP hC
      (PRep.lerp hγ hc (Rep.div (Rep.add hTa hTb) (Rep.two x) two_ne_zero))]
    exact h hDa hDb hua.1 hua.2 hub.1 hub.2

/-- **SEES is exact.** -/
theorem holds_rseesF (hP : P.Simple) (hC : CornersRep x P C) (hγ : PRep x γ γ')
    (hc : PRep x c c') : (rseesF C γ c).Holds x ↔ ArtGallery.segment γ' c' ⊆ P.filled := by
  rw [rseesF, holds_bigAnd_range, hC.1]
  constructor
  · intro h
    have hp : ∀ α < 2 * P.n + 2, ∀ β < 2 * P.n + 2, _ := fun α hα β hβ =>
      (holds_rpairF hP hC hγ hc hα hβ).1 (h _ (pair_lt hα hβ))
    classical
    let T : Finset ℝ := ((Finset.range (2 * P.n + 2)).filter
      (fun α => bpDR P γ' c' α ≠ 0)).image (bpR P γ' c')
    have hmemT : ∀ α < 2 * P.n + 2, bpDR P γ' c' α ≠ 0 → bpR P γ' c' α ∈ T := fun α hα hD =>
      Finset.mem_image.2 ⟨α, Finset.mem_filter.2 ⟨Finset.mem_range.2 hα, hD⟩, rfl⟩
    have h0 : (0 : ℝ) ∈ T := by
      have := hmemT 0 (by omega) (by simp [bpDR]); simpa [bpR] using this
    have h1 : (1 : ℝ) ∈ T := by
      have := hmemT 1 (by omega) (by simp [bpDR]); simpa [bpR] using this
    refine segment_subset_filled_of_breakpoints hP T h0 h1 ?_ ?_ ?_
    · intro j hj s hD hs
      have e1 : bpDR P γ' c' (j + 2) = crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ' c' := by
        simp [bpDR, show ¬ j + 2 < 2 by omega, show j + 2 < P.n + 2 by omega]
      have hm := hmemT (j + 2) (by omega) (by rw [e1]; exact hD)
      have e2 : bpR P γ' c' (j + 2) = s := by
        simp only [bpR, show j + 2 ≠ 0 by omega, show j + 2 ≠ 1 by omega,
          show j + 2 < P.n + 2 by omega, ite_false, ite_true, show j + 2 - 2 = j by omega, e1]
        field_simp
        linarith
      rwa [e2] at hm
    · intro hγc k hk s hs0 hs1 hs
      have hL : dotR γ' c' γ' c' ≠ 0 := by
        intro h0
        apply hγc
        unfold dotR at h0
        have a1 : c'.1 - γ'.1 = 0 := by nlinarith [sq_nonneg (c'.1 - γ'.1), sq_nonneg (c'.2 - γ'.2)]
        have a2 : c'.2 - γ'.2 = 0 := by nlinarith [sq_nonneg (c'.1 - γ'.1), sq_nonneg (c'.2 - γ'.2)]
        ext <;> linarith
      have e1 : bpDR P γ' c' (P.n + 2 + k) = dotR γ' c' γ' c' := by
        simp [bpDR, show ¬ P.n + 2 + k < 2 by omega, show ¬ P.n + 2 + k < P.n + 2 by omega]
      have hm := hmemT (P.n + 2 + k) (by omega) (by rw [e1]; exact hL)
      have e2 : bpR P γ' c' (P.n + 2 + k) = s := by
        simp only [bpR, show P.n + 2 + k ≠ 0 by omega, show P.n + 2 + k ≠ 1 by omega,
          show ¬ P.n + 2 + k < P.n + 2 by omega, ite_false, show P.n + 2 + k - 2 - P.n = k by omega,
          e1]
        rw [div_eq_iff hL, ← hs]
        unfold dotR lerp
        ring
      rwa [e2] at hm
    · intro a ha b hb ha0 ha1 hb0 hb1
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hb
      rw [Finset.mem_filter, Finset.mem_range] at hα hβ
      exact hp α hα.1 β hβ.1 hα.2 hβ.2 ha0 ha1 hb0 hb1
  · intro hseg p hp
    have hN : 0 < 2 * P.n + 2 := by omega
    have hα : p / (2 * P.n + 2) < 2 * P.n + 2 := Nat.div_lt_of_lt_mul hp
    have hβ : p % (2 * P.n + 2) < 2 * P.n + 2 := Nat.mod_lt _ hN
    have := (holds_rpairF hP hC hγ hc hα hβ).2 (fun _ _ ha0 ha1 hb0 hb1 =>
      hseg (lerp_mem_segment _ _ (by linarith) (by linarith)))
    rwa [Nat.div_add_mod'] at this

/-! ## Variables -/

variable {S : ℕ → Prop}

theorem RVars_bpD (hC : CornersV S C) (hγ : PV S γ) (hc : PV S c) (α : ℕ) :
    RVars S (bpD C γ c α) := by
  unfold bpD
  split_ifs
  · exact RVars.one
  · exact RVars.cross (hC _) (hC _) hγ hc
  · exact RVars.dot hγ hc hγ hc

theorem RVars_bpT (hC : CornersV S C) (hγ : PV S γ) (hc : PV S c) (α : ℕ) :
    RVars S (bpT C γ c α) := by
  unfold bpT
  split_ifs
  · exact RVars.zero
  · exact RVars.one
  · exact (RVars.det (hC _) (hC _) hγ).neg.div (RVars_bpD hC hγ hc α)
  · exact (RVars.dot hγ (hC _) hγ hc).div (RVars_bpD hC hγ hc α)

theorem FVars_rseesF (hC : CornersV S C) (hγ : PV S γ) (hc : PV S c) :
    FVars S (rseesF C γ c) := by
  rw [rseesF, FVars_bigAnd]
  intro φ hφ
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hφ
  exact ⟨⟨FVars_rneF (RVars_bpD hC hγ hc _), FVars_rneF (RVars_bpD hC hγ hc _),
      FVars_runitF (RVars_bpT hC hγ hc _), FVars_runitF (RVars_bpT hC hγ hc _)⟩,
    FVars_rinsideF hC (PV.lerp hγ hc
      ((RVars_bpT hC hγ hc _).add (RVars_bpT hC hγ hc _) |>.div RVars.two))⟩

end ArtGallery.FewVars

end
