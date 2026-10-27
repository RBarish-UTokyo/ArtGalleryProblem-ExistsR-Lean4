module

public import ArtGallery.Hardness.Sec5.CoverUnitLocal
public import ArtGallery.Hardness.Sec5.MainArea.Cover

/-!
# Section 5, sufficiency (vi): the boundary of the global polygon

The boundary of `polyC Φ n` (`n ≥ 1`) decomposes (`polyC_bdry`) into

* the pocket chains (`pocketClosed σ`, `σ < 4n`), below `y = 1`;
* the diagonal edges `w_r v_r`, `v_l w_l` and the top edge `t_r t_l` of the main hexagon;
* the comb segments on `x = S` and `x = X_L` (`S ≤ y ≤ S + 3N`);
* the right unit chains and the mirror images of the left unit chains.

This is the decomposition of the proof of `global_simple` (`Assemble/Global.lean`), kept with the
information needed for the coverage.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.CoverM

open ArtGallery Set Polygon
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### The pockets of the bottom wall -/

/-- Every point of the bottom wall lies on the closed chain of one pocket. -/
theorem bottom_pockets (one : ℕ → Bool) : ∀ j : ℕ, ∀ p ∈ chainSet
    (((List.range (j + 1)).flatMap fun σ => pocket (one σ) σ).map ratPoint ++ [ratPoint (mR j)]),
    ∃ σ ≤ j, p ∈ chainSet ((pocketClosed (one σ) σ).map ratPoint)
  | 0 => by
    intro p hp
    refine ⟨0, le_rfl, ?_⟩
    have e : ((List.range (0 + 1)).flatMap fun σ => pocket (one σ) σ).map ratPoint ++
        [ratPoint (mR 0)] = (pocketClosed (one 0) 0).map ratPoint := by
      rw [pocketClosed_eq]; simp
    rwa [e] at hp
  | j + 1 => by
    intro p hp
    have hmL : ratPoint (mL (j + 1)) = ratPoint (mR j) := by rw [mL_succ]
    have e : ((List.range (j + 1 + 1)).flatMap fun σ => pocket (one σ) σ).map ratPoint ++
        [ratPoint (mR (j + 1))] =
        ((List.range (j + 1)).flatMap fun σ => pocket (one σ) σ).map ratPoint ++
          ratPoint (mR j) :: (innerR (one (j + 1)) (j + 1) ++ [ratPoint (mR (j + 1))]) := by
      rw [List.range_succ, List.flatMap_append, List.map_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [pocket_eq, ← hmL]
      simp [innerR]
    rw [e, chainSet_append_cons] at hp
    rcases hp with hp | hp
    · obtain ⟨σ, hσ, h⟩ := bottom_pockets one j p hp
      exact ⟨σ, by omega, h⟩
    · refine ⟨j + 1, le_rfl, ?_⟩
      rw [pocketClosed_map, hmL]
      simpa using hp

/-! ### The comb of a side -/

/-- **The comb of the units of one side**, with the exact range of its vertical segments. -/
theorem comb_cases {S ρ top : ℝ} (fs : List (List Point)) (hρ : 0 < ρ) (hρ1 : ρ < 1 / 100)
    (hF : ∀ j (hj : j < fs.length), UnitFeature S (S + 3 * j + 1) ρ fs[j])
    (htop : S + 3 * fs.length ≤ top) (hst : S < top) :
    ∀ p ∈ chainSet ((S, S) :: fs.flatten ++ [(S, top)]),
      (p.1 = S ∧ S ≤ p.2 ∧ p.2 ≤ top) ∨ ∃ f ∈ fs, p ∈ chainSet f := by
  have hV : ∀ f ∈ fs, VFeature S (S - 1) top f ∧ ∃ j : ℕ, j < fs.length ∧
      UnitFeature S (S + 3 * j + 1) ρ f := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have u := hF j hj
    have hjl : (j : ℝ) + 1 ≤ fs.length := by exact_mod_cast hj
    refine ⟨⟨u.len, u.simple, by rw [u.fst], by rw [u.lst], by rw [u.fst, u.lst]; simp; linarith,
      u.right, fun p hp => ?_⟩, j, hj, u⟩
    obtain ⟨-, -, b3, b4⟩ := u.box p hp
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor <;> linarith
  have hlen : (0 : ℝ) ≤ fs.length := Nat.cast_nonneg _
  obtain ⟨-, h2⟩ := comb_vertical (X₀ := S) (lo := S - 1) (hi := top) (s := S) fs
    hst
    (fun f hf => (hV f hf).1)
    (fun f hf => by
      obtain ⟨-, j, -, u⟩ := hV f hf
      rw [u.fst]; simp; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    (by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have ui := hF i hi
      have uj := hF j hj
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      refine ⟨Set.disjoint_left.2 fun p hp1 hp2 => ?_, ?_⟩
      · have a := (ui.box p hp1).2.2.2
        have b := (uj.box p hp2).2.2.1
        linarith
      · rw [ui.lst, uj.fst]; simp; linarith)
  intro p hp
  rcases h2 hp with ⟨hx, hy1, hy2⟩ | ⟨f, hf, hpf⟩
  · exact Or.inl ⟨hx, hy1, hy2⟩
  · exact Or.inr ⟨f, hf, hpf⟩

/-! ### The boundary of the global polygon -/

section Global

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-- `S` as a real number. -/
noncomputable def sS (Φ : List ETRINV.Constraint) (n : ℕ) : ℝ := (S n (numC Φ) : ℝ)

/-- The top `S + 3N`. -/
noncomputable def sTop (Φ : List ETRINV.Constraint) (n : ℕ) : ℝ :=
  sS Φ n + 3 * (bigN n (numC Φ) : ℝ)

/-- The left line `X_L = 54n − 12 − S`. -/
noncomputable def sXL (Φ : List ETRINV.Constraint) (n : ℕ) : ℝ := 54 * (n : ℝ) - 12 - sS Φ n

/-- The hexagon corner `w_r`. -/
noncomputable def pwR (n : ℕ) : Point := (54 * (n : ℝ) - 6, 1)
/-- The hexagon corner `v_r`. -/
noncomputable def pvR (Φ : List ETRINV.Constraint) (n : ℕ) : Point := (sS Φ n, sS Φ n)
/-- The hexagon corner `t_r`. -/
noncomputable def ptR (Φ : List ETRINV.Constraint) (n : ℕ) : Point := (sS Φ n, sTop Φ n)
/-- The hexagon corner `t_l`. -/
noncomputable def ptL (Φ : List ETRINV.Constraint) (n : ℕ) : Point := (sXL Φ n, sTop Φ n)
/-- The hexagon corner `v_l`. -/
noncomputable def pvL (Φ : List ETRINV.Constraint) (n : ℕ) : Point := (sXL Φ n, sS Φ n)
/-- The hexagon corner `w_l`. -/
def pwL : Point := (-6, 1)

theorem sS_big : 54 * (n : ℝ) + 100000 ≤ sS Φ n := Count.S_big

/-- The unit features of a side. -/
theorem side_features {us : List UnitSpec} (hus : ∀ u ∈ us, UnitOK n u)
    (hlen : us.length ≤ bigN n (numC Φ)) :
    ∀ j (hj : j < (sideChainsR n (numC Φ) us).length),
      UnitFeature (sS Φ n) (sS Φ n + 3 * j + 1)
        (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) (sideChainsR n (numC Φ) us)[j] := by
  have hNn := four_n_le_bigN (n := n) (k := numC Φ)
  intro j hj
  have hj' : j < us.length := by simpa [sideChainsR, length_unitChains] using hj
  simp only [sideChainsR, List.getElem_map]
  rw [getElem_unitChains, Nat.zero_add]
  exact unitChain_feature (hus _ (List.getElem_mem _)) (by omega) hNn

theorem rho_pos' : (0 : ℝ) < (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) := by
  have := S_pos_q (n := n) (k := numC Φ)
  have : (0 : ℚ) < Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) := by
    simp only [Corridor.rho]; positivity
  exact_mod_cast this

theorem rho_small' : (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) < 1 / 100 := by
  have := S_ge (n := n) (k := numC Φ)
  have h8 : (800000 : ℚ) ≤ ((S n (numC Φ) : ℕ) : ℚ) := by exact_mod_cast this
  have : Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) < 1 / 100 := by
    simp only [Corridor.rho]; rw [div_lt_iff₀ (by positivity)]; linarith
  calc _ < ((1 / 100 : ℚ) : ℝ) := Rat.cast_lt.2 this
    _ = 1 / 100 := by norm_num

theorem sTop_eq : sTop Φ n = sS Φ n + 3 * (bigN n (numC Φ) : ℝ) := rfl

theorem sS_lt_sTop : sS Φ n < sTop Φ n := by
  have hN2 : (2 : ℝ) ≤ bigN n (numC Φ) := by exact_mod_cast two_le_bigN
  rw [sTop_eq]; linarith

theorem len_top {us : List UnitSpec} (hlen : us.length ≤ bigN n (numC Φ)) :
    sS Φ n + 3 * ((sideChainsR n (numC Φ) us).length : ℝ) ≤ sTop Φ n := by
  have : ((sideChainsR n (numC Φ) us).length : ℝ) ≤ bigN n (numC Φ) := by
    simp only [sideChainsR, List.length_map, length_unitChains]; exact_mod_cast hlen
  rw [sTop_eq]; linarith

/-- The left side of the polygon is the mirror image of a comb. -/
theorem left_comb_eq : ptL Φ n :: (leftPart n Φ).map ratPoint ++ [pvL Φ n] =
    (((sS Φ n, sS Φ n) :: (sideChainsR n (numC Φ) (unitSpecs n Φ).2).flatten ++
      [(sS Φ n, sTop Φ n)]).map (mirrorR n)).reverse := by
  have hm : ∀ p : Point, mirrorR n p = (54 * (n : ℝ) - 12 - p.1, p.2) := fun p => by
    simp [mirrorR]
  simp only [leftPart, sideChainsR, List.map_flatten, List.map_reverse,
    List.map_map, List.map_cons, List.map_append, List.reverse_append, List.reverse_cons,
    List.reverse_flatten, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append]
  have hf : (List.map ratPoint ∘ leftChain n) =
      (List.reverse ∘ List.map ⇑(mirrorR n) ∘ List.map ratPoint) := by
    funext c
    simp [leftChain, Function.comp_def, List.map_reverse, List.map_map, ratPoint_mirror]
  rw [hm, hm]
  simp only [ptL, pvL, sXL, hf]

/-- The vertex list of the global polygon. -/
theorem constructPos_map : (constructPos Φ n).map ratPoint =
    (((((bottomWall n Φ).map ratPoint ++ [pwR n]) ++
      pvR Φ n :: (sideChainsR n (numC Φ) (unitSpecs n Φ).1).flatten) ++ [ptR Φ n]) ++
        ptL Φ n :: ((leftPart n Φ).map ratPoint ++ [pvL Φ n])) := by
  have ewR : ratPoint (wR n) = pwR n := by simp [ratPoint, wR, pwR]
  have evR : ratPoint (vR n (numC Φ)) = pvR Φ n := by simp [ratPoint, vR, pvR, sS]
  have etR : ratPoint (tR n (numC Φ)) = ptR Φ n := by simp [ratPoint, tR, ptR, sTop, sS]
  have etL : ratPoint (tL n (numC Φ)) = ptL Φ n := by
    simp [ratPoint, tL, ptL, sTop, sS, XL, xMirror, sXL]
  have evL : ratPoint (vL n (numC Φ)) = pvL Φ n := by
    simp [ratPoint, vL, pvL, sS, XL, xMirror, sXL]
  simp only [constructPos, List.map_append, List.map_cons, List.map_nil, ewR, evR, etR, etL,
    evL, rightPart, List.map_flatten, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- **The boundary of the global polygon.** -/
theorem polyC_bdry (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {p : Point}
    (hp : p ∈ (polyC Φ n).boundary) :
    (∃ σ < 4 * n, p ∈ chainSet ((pocketClosed (slotOne n Φ σ) σ).map ratPoint)) ∨
      p ∈ ArtGallery.segment (pwR n) (pvR Φ n) ∨
      (p.1 = sS Φ n ∧ sS Φ n ≤ p.2 ∧ p.2 ≤ sTop Φ n) ∨
      (∃ f ∈ sideChainsR n (numC Φ) (unitSpecs n Φ).1, p ∈ chainSet f) ∨
      p ∈ ArtGallery.segment (ptR Φ n) (ptL Φ n) ∨
      (p.1 = sXL Φ n ∧ sS Φ n ≤ p.2 ∧ p.2 ≤ sTop Φ n) ∨
      (∃ f ∈ sideChainsR n (numC Φ) (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f) ∨
      p ∈ ArtGallery.segment (pvL Φ n) pwL := by
  have hok := unitSpecs_ok hΦ
  have hR := side_features (Φ := Φ) (fun u hu => hok u (List.mem_append_left _ hu))
    (length_unitSpecs_fst n Φ)
  have hL := side_features (Φ := Φ) (fun u hu => hok u (List.mem_append_right _ hu))
    (length_unitSpecs_snd n Φ)
  have hC2 := comb_cases _ rho_pos' rho_small' hR (len_top (length_unitSpecs_fst n Φ))
    sS_lt_sTop
  have hC3 := comb_cases _ rho_pos' rho_small' hL (len_top (length_unitSpecs_snd n Φ))
    sS_lt_sTop
  rw [polyC, construct_pos (by omega), constructPos_map] at hp
  set B := (bottomWall n Φ).map ratPoint with hB
  set RF := (sideChainsR n (numC Φ) (unitSpecs n Φ).1).flatten
  set LF := (leftPart n Φ).map ratPoint
  have hBne : 2 ≤ (B ++ [pwR n]).length := by
    have : B ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [B, List.length_map, List.length_nil] at this
      rw [length_bottomWall] at this
      have h1 := pocketStart_succ (n := n) (Φ := Φ) 0
      have h2 := pocketStart_mono (n := n) (Φ := Φ) (show 0 + 1 ≤ 4 * n by omega)
      have h3 := length_pocketRel_pos (slotOne n Φ 0)
      omega
    simp only [List.length_append, List.length_singleton]
    have := List.length_pos_iff.2 this; omega
  have hfst : fstPt ((((B ++ [pwR n]) ++ pvR Φ n :: RF) ++ [ptR Φ n]) ++
      ptL Φ n :: (LF ++ [pvL Φ n])) = pwL := by
    have := bottom_fst hn Φ
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
          pocket (slotOne n Φ σ) σ).map ratPoint ++ [ratPoint (mR (4 * n - 1))] := by
        rw [hB, bottomWall, mR_last hn, show 4 * n - 1 + 1 = 4 * n by omega]
        simp [ratPoint, wR, pwR]
      rw [e] at h
      obtain ⟨σ, hσ, h⟩ := bottom_pockets (slotOne n Φ) (4 * n - 1) p h
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
        rw [left_comb_eq, chainSet_reverse, chainSet_map] at h'
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

theorem pocket_chain_bounds (one : Bool) (σ : ℕ) :
    ∀ p ∈ chainSet ((pocketClosed one σ).map ratPoint), (slotX σ : ℝ) - 6 ≤ p.1 ∧
      p.1 ≤ (slotX σ : ℝ) + 15 / 2 ∧ p.2 ≤ 1 ∧ (p.1 ≤ (slotX σ : ℝ) - 6 → p = ratPoint (mL σ)) ∧
      ((slotX σ : ℝ) + 15 / 2 ≤ p.1 → p = ratPoint (mR σ)) := by
  rw [pocketClosed_map]
  have hb := innerR_bounds one σ
  intro p hp
  have hall : ∀ v ∈ ratPoint (mL σ) :: innerR one σ ++ [ratPoint (mR σ)],
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
      (innerR_ne_nil _ _) (by rw [ratPoint_mL]; simp) (by rw [ratPoint_mR]; simp; linarith)
      (fun v hv => by have := (hb v hv).1; linarith) p hp with h | h | h
    · linarith
    · exact h
    · rw [h, ratPoint_mR] at hx; simp at hx; linarith
  · rcases chainSet_lt_or_ends (α := 1) (β := 0) (c := (slotX σ : ℝ) + 15 / 2)
      (innerR_ne_nil _ _) (by rw [ratPoint_mL]; simp; linarith) (by rw [ratPoint_mR]; simp)
      (fun v hv => by have := (hb v hv).2.1; linarith) p hp with h | h | h
    · linarith
    · rw [h, ratPoint_mL] at hx; simp at hx; linarith
    · exact h

theorem slotX_lt_real {σ σ' : ℕ} (h : σ < σ') : (slotX σ : ℝ) + 27 / 2 ≤ slotX σ' := by
  have := slotX_lt h
  have h' : ((slotX σ + 27 / 2 : ℚ) : ℝ) ≤ ((slotX σ' : ℚ) : ℝ) := Rat.cast_le.2 this
  push_cast at h'; exact h'

theorem slotX_add_le_real {σ : ℕ} (h : σ < 4 * n) : (slotX σ : ℝ) + 15 / 2 ≤ 54 * (n : ℝ) - 6 := by
  have := slotX_add_le (n := n) h
  have h' : ((slotX σ + 15 / 2 : ℚ) : ℝ) ≤ ((54 * (n : ℚ) - 6 : ℚ) : ℝ) := Rat.cast_le.2 this
  push_cast at h'; exact h'

theorem seg_bounds {a b p : Point} (hp : p ∈ ArtGallery.segment a b) :
    min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧ min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
  simp only [Geometry.lerp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_total a.1 b.1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total a.1 b.1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  · rcases le_total a.2 b.2 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total a.2 b.2 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

theorem unit_chain_right {us : List UnitSpec} (hus : ∀ u ∈ us, UnitOK n u)
    (hlen : us.length ≤ bigN n (numC Φ)) {f : List Point}
    (hf : f ∈ sideChainsR n (numC Φ) us) {p : Point} (hp : p ∈ chainSet f) :
    sS Φ n ≤ p.1 ∧ p.1 ≤ sS Φ n + 4 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  obtain ⟨b1, b2, -, -⟩ := (side_features (Φ := Φ) hus hlen j hj).box p hp
  exact ⟨b1, b2⟩

/-- **Boundary points near the pockets**: a boundary point in the open box of slot `σ` (height
`T ≤ S`) lies on the pocket chain of `σ`. -/
theorem bdry_openBox (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) {T : ℝ}
    (hT : T ≤ sS Φ n) {p : Point} (hp : p ∈ (polyC Φ n).boundary) (hb : p ∈ Sec5.openBox σ T) :
    p ∈ chainSet ((pocketClosed (slotOne n Φ σ) σ).map ratPoint) := by
  have hok := unitSpecs_ok hΦ
  have hS := sS_big (Φ := Φ) (n := n)
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have ha' := slotX_add_le_real (n := n) hσ
  have ha0 : (0 : ℝ) ≤ slotX σ := by exact_mod_cast slotX_nonneg σ
  have hXL : sXL Φ n ≤ -6 - 99994 := by simp only [sXL]; linarith
  rcases polyC_bdry hΦ hn hp with ⟨σ', hσ', h⟩ | h | h | ⟨f, hf, h⟩ | h | h | ⟨f, hf, h⟩ | h
  · rcases lt_trichotomy σ' σ with hlt | rfl | hgt
    · exfalso
      have := (pocket_chain_bounds _ σ' p h).2.1
      have := slotX_lt_real hlt
      linarith
    · exact h
    · exfalso
      have := (pocket_chain_bounds _ σ' p h).1
      have := slotX_lt_real hgt
      linarith
  · exfalso
    have := (seg_bounds h).1
    simp only [pwR, pvR] at this
    have : 54 * (n : ℝ) - 6 ≤ p.1 := le_trans (le_min le_rfl (by linarith)) this
    linarith
  · exfalso; linarith [h.1]
  · exfalso
    have := (unit_chain_right (fun u hu => hok u (List.mem_append_left _ hu))
      (length_unitSpecs_fst n Φ) hf h).1
    linarith
  · exfalso
    have := (seg_bounds h).2.2.1
    simp only [ptR, ptL, min_self] at this
    have := sS_lt_sTop (Φ := Φ) (n := n)
    linarith
  · exfalso; linarith [h.1]
  · exfalso
    have := (unit_chain_right (fun u hu => hok u (List.mem_append_right _ hu))
      (length_unitSpecs_snd n Φ) hf h).1
    simp only [mirrorR, Vis.Cert.reflX_apply] at this
    simp only [sXL] at hXL
    linarith
  · exfalso
    have := (seg_bounds h).2.1
    simp only [pvL, pwL] at this
    have : p.1 ≤ -6 := le_trans this (max_le (by linarith) le_rfl)
    linarith

theorem pocketClosed_getD_zero (one : Bool) (σ : ℕ) :
    ratPoint ((pocketClosed one σ).getD 0 0) = ratPoint (mL σ) := by
  have h0 : 0 < (pocket one σ).length := by rw [length_pocket]; exact length_pocketRel_pos one
  rw [pocketClosed_eq, List.getD_append _ _ _ _ h0, pocket_getD_zero]

theorem pocketClosed_getD_last (one : Bool) (σ : ℕ) :
    ratPoint ((pocketClosed one σ).getD (pocketRel one).length 0) = ratPoint (mR σ) := by
  rw [pocketClosed_eq, List.getD_append_right _ _ _ _ (by rw [length_pocket]),
    length_pocket, Nat.sub_self]
  rfl

/-- **Box separation for the pockets of the global polygon.** -/
theorem boxSep (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) {T : ℝ}
    (hT : T ≤ sS Φ n) :
    BoxSep (polyC Φ n) (slotOne n Φ σ) σ (pocketStart n Φ σ) T := by
  have hK := (Count.mainHyp hΦ hn).pocket σ hσ
  have hP := (Count.mainHyp hΦ hn).simple
  have hn0 : 0 < (polyC Φ n).n := by have := hP.1; omega
  intro i hi hnot p hp hpb
  have hpc := bdry_openBox hΦ hn hσ hT ⟨i, hi, hp⟩ hpb
  obtain ⟨b1, b2, -, -⟩ := hpb
  set one := slotOne n Φ σ
  set a := pocketStart n Φ σ
  set P := polyC Φ n
  set L := (pocketRel one).length
  have hlen : ((pocketClosed one σ).map ratPoint).length = L + 1 := by
    simp [pocketClosed, L, length_pocketClosedRel]
  obtain ⟨j, hj, hpj⟩ := mem_chainSet_iff.1 hpc
  rw [hlen] at hj
  have hv : ∀ j' ≤ L, P.vtx ((a + j') % P.n) = ratPoint ((pocketClosed one σ).getD j' 0) := hK
  have hget : ∀ j', ((pocketClosed one σ).map ratPoint).getD j' (0, 0) =
      ratPoint ((pocketClosed one σ).getD j' 0) := fun j' => Count.getD_map_ratPoint _ _
  simp only [edgeSeg, hget] at hpj
  rw [← hv j (by omega), ← hv (j + 1) (by omega), ← Polygon.chain_succ] at hpj
  have hne : (a + j) % P.n ≠ i := hnot j (by omega)
  -- a vertex of the chain on edge `i`
  have hvert : ∀ j' ≤ L, p = P.vtx ((a + j') % P.n) → False := by
    intro j' hj' hpv
    by_cases h0 : j' = 0
    · subst h0
      rw [hv 0 (Nat.zero_le _), pocketClosed_getD_zero, ratPoint_mL] at hpv
      rw [hpv] at b1; simp at b1
    by_cases hL : j' = L
    · subst hL
      rw [hv _ le_rfl, pocketClosed_getD_last, ratPoint_mR] at hpv
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

end Global

end ArtGallery.Sec5.CoverM

end
