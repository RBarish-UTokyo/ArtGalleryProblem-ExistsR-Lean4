module

public import ArtGallery.Hardness.BP.Assemble.Sides
public import ArtGallery.Hardness.BP.MainAreaCount
public import ArtGallery.Hardness.BP.MainAreaHex

/-!
# Boundary-point variant: the main area of the global polygon

The boundary of `polyCBP Φ n` (`n ≥ 1`) decomposes (`polyCBP_bdry`, as `Sec5/CoverMain.lean`)
into the closed pocket chains with bays (`pocketBPClosed σ`, `σ < 4n`, below `y = 1`), the
diagonal edges `w_r v_r`, `v_l w_l`, the top edge `t_r t_l`, the comb segments on `x = S` and
`x = X_L`, the right unit chains and the mirror images of the left unit chains.  Consequences:

* `pocketsBP`: every slot carries its closed pocket chain (`PocketAtBP`, at `startBP n Φ σ`);
* `boxSepBP`: box separation of every slot up to any height `T ≤ S` (`BoxSepBP`);
* `mainHypBP`: the hypotheses `MainHypBP` of the counting of the base positions
  (`BP/MainAreaCount.lean`), for `one = slotOne n Φ`;
* `hex_subsetBP`, `hexHypBP`: the main hexagon lies in the region, and the hypotheses
  `HexHypBP` of its coverage by the base guards (`BP/MainAreaHex.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Sec5
open ArtGallery.Sec5.CoverM (comb_cases sS sTop sXL pwR pvR ptR ptL pvL pwL sS_big rho_pos'
  rho_small' sTop_eq sS_lt_sTop slotX_lt_real slotX_add_le_real seg_bounds hexSet
  interior_hexSet)
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### The pockets of the bottom wall -/

/-- Every point of the bottom wall lies on the closed chain of one pocket (with its bay). -/
theorem bottomBP_pockets (one : ℕ → Bool) : ∀ j : ℕ, ∀ p ∈ chainSet
    (((List.range (j + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++ [ratPoint (mR j)]),
    ∃ σ ≤ j, p ∈ chainSet ((pocketBPClosed (one σ) σ).map ratPoint)
  | 0 => by
    intro p hp
    refine ⟨0, le_rfl, ?_⟩
    have e : ((List.range (0 + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR 0)] = (pocketBPClosed (one 0) 0).map ratPoint := by
      rw [pocketBPClosed_eq]; simp
    rwa [e] at hp
  | j + 1 => by
    intro p hp
    have hmL : ratPoint (mL (j + 1)) = ratPoint (mR j) := by rw [mL_succ]
    have e : ((List.range (j + 1 + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR (j + 1))] =
        ((List.range (j + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
          ratPoint (mR j) :: (innerRBP (one (j + 1)) (j + 1) ++ [ratPoint (mR (j + 1))]) := by
      rw [List.range_succ, List.flatMap_append, List.map_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [pocketBP_eq, ← hmL]
      simp [innerRBP]
    rw [e, chainSet_append_cons] at hp
    rcases hp with hp | hp
    · obtain ⟨σ, hσ, h⟩ := bottomBP_pockets one j p hp
      exact ⟨σ, by omega, h⟩
    · refine ⟨j + 1, le_rfl, ?_⟩
      rw [pocketBPClosed_map, hmL]
      simpa using hp

/-! ### The boundary of the global polygon -/

section Global

variable {Φ : List ETRINV.Constraint} {n : ℕ}


/-- The unit features of a side. -/
theorem side_featuresBP {us : List UnitSpec} (hus : ∀ u ∈ us, UnitOK n u)
    (hlen : us.length ≤ bigN n (numC Φ)) :
    ∀ j (hj : j < (sideChainsRBP n (numC Φ) us).length),
      UnitFeature (sS Φ n) (sS Φ n + 3 * j + 1)
        (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) (sideChainsRBP n (numC Φ) us)[j] := by
  have hNn := four_n_le_bigN (n := n) (k := numC Φ)
  intro j hj
  have hj' : j < us.length := by simpa [sideChainsRBP, length_unitChainsBP] using hj
  simp only [sideChainsRBP, List.getElem_map]
  rw [getElem_unitChainsBP, Nat.zero_add]
  exact unitChainBP_feature (hus _ (List.getElem_mem _)) (by omega) hNn

theorem len_topBP {us : List UnitSpec} (hlen : us.length ≤ bigN n (numC Φ)) :
    sS Φ n + 3 * ((sideChainsRBP n (numC Φ) us).length : ℝ) ≤ sTop Φ n := by
  have : ((sideChainsRBP n (numC Φ) us).length : ℝ) ≤ bigN n (numC Φ) := by
    simp only [sideChainsRBP, List.length_map, length_unitChainsBP]; exact_mod_cast hlen
  rw [sTop_eq]; linarith

/-- The left side of the polygon is the mirror image of a comb. -/
theorem left_comb_eqBP : ptL Φ n :: (leftPartBP n Φ).map ratPoint ++ [pvL Φ n] =
    (((sS Φ n, sS Φ n) :: (sideChainsRBP n (numC Φ) (unitSpecs n Φ).2).flatten ++
      [(sS Φ n, sTop Φ n)]).map (mirrorR n)).reverse := by
  have hm : ∀ p : Point, mirrorR n p = (54 * (n : ℝ) - 12 - p.1, p.2) := fun p => by
    simp [mirrorR]
  simp only [leftPartBP, sideChainsRBP, List.map_flatten, List.map_reverse,
    List.map_map, List.map_cons, List.map_append, List.reverse_append, List.reverse_cons,
    List.reverse_flatten, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append]
  have hf : (List.map ratPoint ∘ leftChain n) =
      (List.reverse ∘ List.map ⇑(mirrorR n) ∘ List.map ratPoint) := by
    funext c
    simp [leftChain, Function.comp_def, List.map_reverse, List.map_map, ratPoint_mirror]
  rw [hm, hm]
  simp only [ptL, pvL, sXL, hf]

/-- The vertex list of the global polygon. -/
theorem constructPosBP_map : (constructPosBP Φ n).map ratPoint =
    (((((bottomWallBP n Φ).map ratPoint ++ [pwR n]) ++
      pvR Φ n :: (sideChainsRBP n (numC Φ) (unitSpecs n Φ).1).flatten) ++ [ptR Φ n]) ++
        ptL Φ n :: ((leftPartBP n Φ).map ratPoint ++ [pvL Φ n])) := by
  have ewR : ratPoint (wR n) = pwR n := by simp [ratPoint, wR, pwR]
  have evR : ratPoint (vR n (numC Φ)) = pvR Φ n := by simp [ratPoint, vR, pvR, sS]
  have etR : ratPoint (tR n (numC Φ)) = ptR Φ n := by simp [ratPoint, tR, ptR, sTop, sS]
  have etL : ratPoint (tL n (numC Φ)) = ptL Φ n := by
    simp [ratPoint, tL, ptL, sTop, sS, XL, xMirror, sXL]
  have evL : ratPoint (vL n (numC Φ)) = pvL Φ n := by
    simp [ratPoint, vL, pvL, sS, XL, xMirror, sXL]
  simp only [constructPosBP, List.map_append, List.map_cons, List.map_nil, ewR, evR, etR, etL,
    evL, rightPartBP, List.map_flatten, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- **The boundary of the global polygon.** -/
theorem polyCBP_bdry (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {p : Point}
    (hp : p ∈ (polyCBP Φ n).boundary) :
    (∃ σ < 4 * n, p ∈ chainSet ((pocketBPClosed (slotOne n Φ σ) σ).map ratPoint)) ∨
      p ∈ ArtGallery.segment (pwR n) (pvR Φ n) ∨
      (p.1 = sS Φ n ∧ sS Φ n ≤ p.2 ∧ p.2 ≤ sTop Φ n) ∨
      (∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).1, p ∈ chainSet f) ∨
      p ∈ ArtGallery.segment (ptR Φ n) (ptL Φ n) ∨
      (p.1 = sXL Φ n ∧ sS Φ n ≤ p.2 ∧ p.2 ≤ sTop Φ n) ∨
      (∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f) ∨
      p ∈ ArtGallery.segment (pvL Φ n) pwL := by
  have hok := unitSpecs_ok hΦ
  have hR := side_featuresBP (Φ := Φ) (fun u hu => hok u (List.mem_append_left _ hu))
    (length_unitSpecs_fst n Φ)
  have hL := side_featuresBP (Φ := Φ) (fun u hu => hok u (List.mem_append_right _ hu))
    (length_unitSpecs_snd n Φ)
  have hC2 := comb_cases _ rho_pos' rho_small' hR (len_topBP (length_unitSpecs_fst n Φ))
    sS_lt_sTop
  have hC3 := comb_cases _ rho_pos' rho_small' hL (len_topBP (length_unitSpecs_snd n Φ))
    sS_lt_sTop
  rw [polyCBP, constructBP_pos (by omega), constructPosBP_map] at hp
  set B := (bottomWallBP n Φ).map ratPoint with hB
  set RF := (sideChainsRBP n (numC Φ) (unitSpecs n Φ).1).flatten
  set LF := (leftPartBP n Φ).map ratPoint
  have hBne : 2 ≤ (B ++ [pwR n]).length := by
    have : B ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [B, List.length_map, List.length_nil] at this
      rw [length_bottomWallBP] at this
      have h1 := startBP_succ (n := n) (Φ := Φ) 0
      have h2 := startBP_mono (n := n) (Φ := Φ) (show 0 + 1 ≤ 4 * n by omega)
      have h3 := length_pocketBPRel (slotOne n Φ 0)
      omega
    simp only [List.length_append, List.length_singleton]
    have := List.length_pos_iff.2 this; omega
  have hfst : fstPt ((((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++
      ptL Φ n :: (LF ++ [pvL Φ n])) = pwL := by
    have := bottomBP_fst hn Φ
    rw [List.map_append, List.map_singleton] at this
    have ewR : ratPoint (wR n) = pwR n := by simp [ratPoint, wR, pwR]
    rw [ewR] at this
    obtain ⟨b, B', hB'⟩ := List.exists_cons_of_ne_nil (show B ++ [pwR n] ≠ [] by simp)
    have hb : b = pwL := by rw [hB'] at this; exact this
    rw [show (((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++ ptL Φ n :: (LF ++ [pvL Φ n]) =
      (B ++ [pwR n]) ++ (pvR Φ n :: RF ++ [ptR Φ n] ++ ptL Φ n :: (LF ++ [pvL Φ n])) by simp,
      hB', hb]
    rfl
  have hlst : lstPt ((((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++
      ptL Φ n :: (LF ++ [pvL Φ n])) = pvL Φ n := by
    rw [show (((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++ ptL Φ n :: (LF ++ [pvL Φ n]) =
      ((((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++ ptL Φ n :: LF) ++ [pvL Φ n] by simp]
    exact lstPt_append_single _ _
  have hbd := boundary_subset_chainSet (V := (((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++
    ptL Φ n :: (LF ++ [pvL Φ n])) (by simp; omega) hp
  rw [hfst, hlst] at hbd
  rcases hbd with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  have hV : (((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++ ptL Φ n :: (LF ++ [pvL Φ n]) =
      (B ++ [pwR n]) ++ pvR Φ n :: (RF ++ ptR Φ n :: ptL Φ n :: (LF ++ [pvL Φ n])) := by simp
  rw [hV, chainSet_append_cons] at h
  rcases h with h | h
  · have e1 : (B ++ [pwR n]) ++ [pvR Φ n] = B ++ pwR n :: [pvR Φ n] := by simp
    rw [e1, chainSet_append_cons] at h
    rcases h with h | h
    · -- the bottom wall
      left
      have e : B ++ [pwR n] = ((List.range (4 * n - 1 + 1)).flatMap fun σ =>
          pocketBP (slotOne n Φ σ) σ).map ratPoint ++ [ratPoint (mR (4 * n - 1))] := by
        rw [hB, bottomWallBP, mR_last hn, show 4 * n - 1 + 1 = 4 * n by omega]
        simp [ratPoint, wR, pwR]
      rw [e] at h
      obtain ⟨σ, hσ, h⟩ := bottomBP_pockets (slotOne n Φ) (4 * n - 1) p h
      exact ⟨σ, by omega, h⟩
    · right; left
      simpa using h
  · have e2 : pvR Φ n :: (RF ++ ptR Φ n :: ptL Φ n :: (LF ++ [pvL Φ n])) =
        (pvR Φ n :: RF) ++ ptR Φ n :: (ptL Φ n :: (LF ++ [pvL Φ n])) := by simp
    rw [e2, chainSet_append_cons] at h
    rcases h with h | h
    · -- the right comb
      have h' : p ∈ chainSet ((sS Φ n, sS Φ n) :: RF ++ [(sS Φ n, sTop Φ n)]) := by
        simpa [pvR, ptR] using h
      rcases hC2 p h' with h'' | h''
      · right; right; left; exact h''
      · right; right; right; left; exact h''
    · rw [chainSet_cons_cons] at h
      rcases h with h | h
      · right; right; right; right; left; exact h
      · -- the left comb
        have h' : p ∈ chainSet (ptL Φ n :: LF ++ [pvL Φ n]) := by simpa using h
        rw [left_comb_eqBP, chainSet_reverse, chainSet_map] at h'
        obtain ⟨q, hq, rfl⟩ := h'
        have hmir : ∀ p : Point, mirrorR n (mirrorR n p) = p := fun p => by
          simp only [mirrorR, Vis.Cert.reflX_apply]; ext <;> simp
        rcases hC3 q hq with ⟨h1, h2, h3⟩ | ⟨f, hf, hqf⟩
        · right; right; right; right; right; left
          simp only [mirrorR, Vis.Cert.reflX_apply, sXL]
          exact ⟨by rw [h1], h2, h3⟩
        · right; right; right; right; right; right; left
          exact ⟨f, hf, by rw [hmir]; exact hqf⟩

/-! ### Bounds for the pieces of the boundary -/

theorem pocketBP_chain_bounds (one : Bool) (σ : ℕ) :
    ∀ p ∈ chainSet ((pocketBPClosed one σ).map ratPoint), (slotX σ : ℝ) - 6 ≤ p.1 ∧
      p.1 ≤ (slotX σ : ℝ) + 15 / 2 ∧ p.2 ≤ 1 ∧ (p.1 ≤ (slotX σ : ℝ) - 6 → p = ratPoint (mL σ)) ∧
      ((slotX σ : ℝ) + 15 / 2 ≤ p.1 → p = ratPoint (mR σ)) := by
  rw [pocketBPClosed_map]
  have hb := innerRBP_bounds one σ
  intro p hp
  have hall : ∀ v ∈ ratPoint (mL σ) :: innerRBP one σ ++ [ratPoint (mR σ)],
      (slotX σ : ℝ) - 6 ≤ v.1 ∧ v.1 ≤ (slotX σ : ℝ) + 15 / 2 ∧ v.2 ≤ 1 := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · rw [ratPoint_mL]; simp only; refine ⟨le_rfl, by linarith, le_rfl⟩
    · obtain ⟨a, b, c⟩ := hb v hv; exact ⟨a.le, b.le, c⟩
    · rw [ratPoint_mR]; simp only; refine ⟨by linarith, le_rfl, le_rfl⟩
  refine ⟨?_, ?_, ?_, fun hx => ?_, fun hx => ?_⟩
  · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := -((slotX σ : ℝ) - 6))
      (fun v hv => by have := (hall v hv).1; linarith) p hp
    linarith
  · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := (slotX σ : ℝ) + 15 / 2)
      (fun v hv => by have := (hall v hv).2.1; linarith) p hp
    linarith
  · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := 1)
      (fun v hv => by have := (hall v hv).2.2; linarith) p hp
    linarith
  · rcases chainSet_lt_or_ends (α := -1) (β := 0) (c := -((slotX σ : ℝ) - 6))
      (innerRBP_ne_nil _ _) (by rw [ratPoint_mL]; simp) (by rw [ratPoint_mR]; simp; linarith)
      (fun v hv => by have := (hb v hv).1; linarith) p hp with h | h | h
    · linarith
    · exact h
    · rw [h, ratPoint_mR] at hx; simp at hx; linarith
  · rcases chainSet_lt_or_ends (α := 1) (β := 0) (c := (slotX σ : ℝ) + 15 / 2)
      (innerRBP_ne_nil _ _) (by rw [ratPoint_mL]; simp; linarith) (by rw [ratPoint_mR]; simp)
      (fun v hv => by have := (hb v hv).2.1; linarith) p hp with h | h | h
    · linarith
    · rw [h, ratPoint_mL] at hx; simp at hx; linarith
    · exact h

theorem unit_chain_rightBP {us : List UnitSpec} (hus : ∀ u ∈ us, UnitOK n u)
    (hlen : us.length ≤ bigN n (numC Φ)) {f : List Point}
    (hf : f ∈ sideChainsRBP n (numC Φ) us) {p : Point} (hp : p ∈ chainSet f) :
    sS Φ n ≤ p.1 ∧ p.1 ≤ sS Φ n + 4 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  obtain ⟨b1, b2, -, -⟩ := (side_featuresBP (Φ := Φ) hus hlen j hj).box p hp
  exact ⟨b1, b2⟩

/-- **Boundary points near the pockets**: a boundary point in the open box of slot `σ` (height
`T ≤ S`) lies on the closed pocket chain (with bay) of `σ`. -/
theorem bdry_openBoxBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) {T : ℝ}
    (hT : T ≤ sS Φ n) {p : Point} (hp : p ∈ (polyCBP Φ n).boundary) (hb : p ∈ openBoxBP σ T) :
    p ∈ chainSet ((pocketBPClosed (slotOne n Φ σ) σ).map ratPoint) := by
  have hok := unitSpecs_ok hΦ
  have hS := sS_big (Φ := Φ) (n := n)
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have ha' := slotX_add_le_real (n := n) hσ
  have ha0 : (0 : ℝ) ≤ slotX σ := by exact_mod_cast slotX_nonneg σ
  have hXL : sXL Φ n ≤ -6 - 99994 := by simp only [sXL]; linarith
  rcases polyCBP_bdry hΦ hn hp with ⟨σ', hσ', h⟩ | h | h | ⟨f, hf, h⟩ | h | h | ⟨f, hf, h⟩ | h
  · rcases lt_trichotomy σ' σ with hlt | rfl | hgt
    · exfalso
      have := (pocketBP_chain_bounds _ σ' p h).2.1
      have := slotX_lt_real hlt
      linarith
    · exact h
    · exfalso
      have := (pocketBP_chain_bounds _ σ' p h).1
      have := slotX_lt_real hgt
      linarith
  · exfalso
    have := (seg_bounds h).1
    simp only [pwR, pvR] at this
    have : 54 * (n : ℝ) - 6 ≤ p.1 := le_trans (le_min le_rfl (by linarith)) this
    linarith
  · exfalso; linarith [h.1]
  · exfalso
    have := (unit_chain_rightBP (fun u hu => hok u (List.mem_append_left _ hu))
      (length_unitSpecs_fst n Φ) hf h).1
    linarith
  · exfalso
    have := (seg_bounds h).2.2.1
    simp only [ptR, ptL, min_self] at this
    have := sS_lt_sTop (Φ := Φ) (n := n)
    linarith
  · exfalso; linarith [h.1]
  · exfalso
    have := (unit_chain_rightBP (fun u hu => hok u (List.mem_append_right _ hu))
      (length_unitSpecs_snd n Φ) hf h).1
    simp only [mirrorR, Vis.Cert.reflX_apply] at this
    simp only [sXL] at hXL
    linarith
  · exfalso
    have := (seg_bounds h).2.1
    simp only [pvL, pwL] at this
    have : p.1 ≤ -6 := le_trans this (max_le (by linarith) le_rfl)
    linarith


/-! ### The pockets with bays and the box separation -/

theorem polyCBP_bottom (hn : 0 < n) : polyCBP Φ n = Polygon.mk ((bottomWallBP n Φ ++
    ([wR n, vR n (numC Φ)] ++ rightPartBP n Φ ++ [tR n (numC Φ), tL n (numC Φ)] ++ leftPartBP n Φ ++
      [vL n (numC Φ)])).map ratPoint) := by
  rw [polyCBP, constructBP_pos (by omega)]
  simp [constructPosBP, List.append_assoc]

/-- **The closed pocket chains with bays are chains of the global polygon.** -/
theorem pocketsBP (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) :
    PocketAtBP (polyCBP Φ n) (slotOne n Φ σ) σ (startBP n Φ σ) := by
  rw [polyCBP_bottom hn]
  exact pocketAtBP_of_bottomWall (by simp) hσ

/-- **Box separation for the pockets of the global polygon.** -/
theorem boxSepBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) {T : ℝ}
    (hT : T ≤ sS Φ n) :
    BoxSepBP (polyCBP Φ n) (slotOne n Φ σ) σ (startBP n Φ σ) T := by
  have hK := pocketsBP (Φ := Φ) hn hσ
  have hP : (polyCBP Φ n).Simple := (constructBP_global hΦ hn).1
  have hn0 : 0 < (polyCBP Φ n).n := by have := hP.1; omega
  intro i hi hnot p hp hpb
  have hpc := bdry_openBoxBP hΦ hn hσ hT ⟨i, hi, hp⟩ hpb
  obtain ⟨b1, b2, -, -⟩ := hpb
  set one := slotOne n Φ σ
  set a := startBP n Φ σ
  set P := polyCBP Φ n
  set L := (pocketBPRel one).length with hLdef
  have hL1 : L = (bayRel one).length + 1 := length_pocketBPRel one
  have hlen : ((pocketBPClosed one σ).map ratPoint).length = L + 1 := by
    simp [pocketBPClosed, hL1, length_pocketBPClosedRel]
  obtain ⟨j, hj, hpj⟩ := mem_chainSet_iff.1 hpc
  rw [hlen] at hj
  have hv : ∀ j' ≤ L, P.vtx ((a + j') % P.n) = ratPoint ((pocketBPClosed one σ).getD j' 0) :=
    fun j' hj' => hK j' (by omega)
  have hget : ∀ j', ((pocketBPClosed one σ).map ratPoint).getD j' (0, 0) =
      ratPoint ((pocketBPClosed one σ).getD j' 0) := fun j' => Count.getD_map_ratPoint _ _
  simp only [edgeSeg, hget] at hpj
  rw [← hv j (by omega), ← hv (j + 1) (by omega), ← Polygon.chain_succ] at hpj
  have hne : (a + j) % P.n ≠ i := hnot j (by omega)
  -- a vertex of the chain on edge `i`
  have hvert : ∀ j' ≤ L, p = P.vtx ((a + j') % P.n) → False := by
    intro j' hj' hpv
    by_cases h0 : j' = 0
    · subst h0
      rw [hv 0 (Nat.zero_le _), pocketBPClosed_getD_zero, ratPoint_mL] at hpv
      rw [hpv] at b1; simp at b1
    by_cases hL : j' = L
    · subst hL
      rw [hv _ le_rfl, hL1, pocketBPClosed_getD_last, ratPoint_mR] at hpv
      rw [hpv] at b2; simp at b2
    have hmem : P.vtx ((a + j') % P.n) ∈ P.edge i := hpv ▸ hp
    rcases (Jordan.simple_vtx_mem_edge_iff hP (Nat.mod_lt _ hn0) hi).1 hmem with h | h
    · exact hnot j' (by omega) h.symm
    · rw [Polygon.chain_prev hn0 a (by omega)] at h
      exact hnot (j' - 1) (by omega) h.symm
  rcases Jordan.simple_endpoint_of_mem_two hP (Nat.mod_lt _ hn0) hi hne hpj hp with h | h
  · exact hvert j (by omega) h
  · rw [Polygon.chain_succ] at h
    exact hvert (j + 1) (by omega) h


/-! ### The hypotheses of the main area -/

/-- **The counting hypotheses of the base positions** for the global polygon. -/
theorem mainHypBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    MainHypBP (polyCBP Φ n) n (slotOne n Φ) (startBP n Φ) := by
  obtain ⟨h1, h2, -⟩ := constructBP_global hΦ hn
  have hS := sS_big (Φ := Φ) (n := n)
  exact ⟨h1, h2, fun σ hσ => pocketsBP hn hσ,
    fun σ hσ => boxSepBP hΦ hn hσ (T := 1 / 8) (by linarith)⟩

/-- A point satisfying the hexagon inequalities strictly is not on the boundary. -/
theorem strict_not_bdryBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {x : Point}
    (k1 : 0 < det (pwR n) (pvR Φ n) x) (k2 : 0 < det (pvL Φ n) pwL x) (k3 : 1 < x.2)
    (k4 : x.2 < sTop Φ n) (k5 : sXL Φ n < x.1) (k6 : x.1 < sS Φ n) :
    x ∉ (polyCBP Φ n).boundary := by
  intro hxe
  have hok := unitSpecs_ok hΦ
  have hS := sS_big (Φ := Φ) (n := n)
  rcases polyCBP_bdry hΦ hn hxe with ⟨σ, -, h⟩ | h | h | ⟨f, hf, h⟩ | h | h | ⟨f, hf, h⟩ | h
  · have := (pocketBP_chain_bounds _ σ x h).2.2.1; linarith
  · rw [CoverU.det_eq_zero_of_mem h] at k1; exact lt_irrefl _ k1
  · linarith [h.1]
  · have := (unit_chain_rightBP (fun u hu => hok u (List.mem_append_left _ hu))
      (length_unitSpecs_fst n Φ) hf h).1
    linarith
  · have := (seg_bounds h).2.2.1
    simp only [ptR, ptL, min_self] at this
    linarith
  · linarith [h.1]
  · have := (unit_chain_rightBP (fun u hu => hok u (List.mem_append_right _ hu))
      (length_unitSpecs_snd n Φ) hf h).1
    simp only [mirrorR, Vis.Cert.reflX_apply] at this
    simp only [sXL] at k5
    linarith
  · rw [CoverU.det_eq_zero_of_mem h] at k2; exact lt_irrefl _ k2

/-- **The main hexagon lies in the region.** -/
theorem hex_subsetBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    hexSet Φ n ⊆ (polyCBP Φ n).filled := by
  obtain ⟨h1, h2, -⟩ := constructBP_global hΦ hn
  have hS := sS_big (Φ := Φ) (n := n)
  have h0 : 0 < 4 * n := by omega
  refine hex_subset_of (one := slotOne n Φ) (start := startBP n Φ) h1 h2 hn (pocketsBP hn h0)
    (boxSepBP hΦ hn h0 (T := 2) (by linarith)) (fun x hx => ?_)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := interior_hexSet hx
  exact strict_not_bdryBP hΦ hn k1 k2 k3 k4 k5 k6

/-- **The coverage hypotheses of the main hexagon** for the global polygon. -/
theorem hexHypBP (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) :
    HexHypBP (polyCBP Φ n) Φ n (slotOne n Φ) (startBP n Φ) := by
  obtain ⟨h1, h2, -⟩ := constructBP_global hΦ hn
  have hS := sS_big (Φ := Φ) (n := n)
  exact ⟨h1, h2, fun σ hσ => pocketsBP hn hσ,
    fun σ hσ => boxSepBP hΦ hn hσ (T := 2) (by linarith), hex_subsetBP hΦ hn⟩

end Global

end ArtGallery.BP

end
