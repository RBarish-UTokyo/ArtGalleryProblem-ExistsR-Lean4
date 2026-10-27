module

public import ArtGallery.Hardness.BP.Assemble.Construct
public import ArtGallery.Hardness.BP.MainAreaBottom
public import ArtGallery.Hardness.Sec5.Assemble.Global

/-!
# Boundary-point variant: the global polygon is simple, given simple units

`global_simpleBP`: if every unit chain (working frame, real coordinates) is a `UnitFeature` at its
height `S + 3m + 1`, the polygon `constructPosBP Φ n` is simple and counter-clockwise.  The proof
is that of `Sec5/Assemble/Global.lean` (`global_simple`), with the bottom wall with bays
(`bottomBP_chain`: a simple chain from `w_l` to `w_r` in `[−6, 54n − 6] × (−∞, 1]`, as the
Section 5 bottom wall):
```
C1 = w_l, bays…, w_r             [w_r, v_r]           C2 = v_r, right units…, t_r
[t_r, t_l]                        C3 = t_l, left units…, v_l
```
closed by the edge `v_l → w_l`.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The unit chains of one side (working frame) in real coordinates. -/
noncomputable def sideChainsRBP (n k : ℕ) (us : List UnitSpec) : List (List Point) :=
  (unitChainsBP n k 0 us).map (List.map ratPoint)

section Global

variable {n : ℕ} {Φ : List ETRINV.Constraint}

/-- **Global simplicity and orientation from the units**. -/
theorem global_simpleBP (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1 / 100)
    (hR : ∀ j (hj : j < (sideChainsRBP n (numC Φ) (unitSpecs n Φ).1).length),
      UnitFeature (S n (numC Φ) : ℝ) ((S n (numC Φ) : ℝ) + 3 * j + 1) ρ
        (sideChainsRBP n (numC Φ) (unitSpecs n Φ).1)[j])
    (hL : ∀ j (hj : j < (sideChainsRBP n (numC Φ) (unitSpecs n Φ).2).length),
      UnitFeature (S n (numC Φ) : ℝ) ((S n (numC Φ) : ℝ) + 3 * j + 1) ρ
        (sideChainsRBP n (numC Φ) (unitSpecs n Φ).2)[j])
    (hRl : (unitSpecs n Φ).1.length ≤ bigN n (numC Φ))
    (hLl : (unitSpecs n Φ).2.length ≤ bigN n (numC Φ)) :
    (Polygon.mk ((constructPosBP Φ n).map ratPoint)).Simple ∧
      (Polygon.mk ((constructPosBP Φ n).map ratPoint)).InteriorLeft ∧
      (∀ p ∈ (Polygon.mk ((constructPosBP Φ n).map ratPoint)).boundary,
        p.1 ≤ (S n (numC Φ) : ℝ) ∨
          ∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).1, p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((constructPosBP Φ n).map ratPoint)).boundary,
        54 * (n : ℝ) - 12 - (S n (numC Φ) : ℝ) ≤ p.1 ∨
          ∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((constructPosBP Φ n).map ratPoint)).boundary,
        p.2 ≤ (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
  set k := numC Φ
  set Sr : ℝ := (S n k : ℝ) with hSr
  set top : ℝ := Sr + 3 * (bigN n k : ℝ) with htop
  set XLr : ℝ := 54 * (n : ℝ) - 12 - Sr with hXLr
  have hS1 : 54 * (n : ℝ) + 100000 ≤ Sr := by
    have := slots_lt_S (n := n) (k := k)
    have : ((54 * (n : ℚ) + 100000 : ℚ) : ℝ) ≤ ((S n k : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this; exact this
  have hN2 : (2 : ℝ) ≤ bigN n k := by exact_mod_cast two_le_bigN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the hexagon corners
  set wLr : Point := ((-6 : ℝ), 1)
  set wRr : Point := (54 * (n : ℝ) - 6, 1)
  set vRr : Point := (Sr, Sr)
  set tRr : Point := (Sr, top)
  set tLr : Point := (XLr, top)
  set vLr : Point := (XLr, Sr)
  have ewR : ratPoint (wR n) = wRr := by simp [ratPoint, wR, wRr]
  have evR : ratPoint (vR n k) = vRr := by simp [ratPoint, vR, vRr, Sr]
  have etR : ratPoint (tR n k) = tRr := by simp [ratPoint, tR, tRr, top, Sr]
  have etL : ratPoint (tL n k) = tLr := by
    simp [ratPoint, tL, tLr, top, Sr, XL, xMirror, XLr]
  have evL : ratPoint (vL n k) = vLr := by simp [ratPoint, vL, vLr, Sr, XL, xMirror, XLr]
  -- the pieces
  set B := (bottomWallBP n Φ).map ratPoint
  set RF := (sideChainsRBP n k (unitSpecs n Φ).1).flatten
  set LC := sideChainsRBP n k (unitSpecs n Φ).2
  set LF := ((leftPartBP n Φ).map ratPoint)
  have hC1 := bottomBP_chain hn Φ
  rw [List.map_append, List.map_singleton, ewR] at hC1
  obtain ⟨hC1s, hC1b⟩ := hC1
  have hRlen : Sr + 3 * ((sideChainsRBP n k (unitSpecs n Φ).1).length : ℝ) ≤ top := by
    have : ((sideChainsRBP n k (unitSpecs n Φ).1).length : ℝ) ≤ bigN n k := by
      simp only [sideChainsRBP, List.length_map, length_unitChainsBP]; exact_mod_cast hRl
    linarith
  have hLlen : Sr + 3 * (LC.length : ℝ) ≤ top := by
    have : (LC.length : ℝ) ≤ bigN n k := by
      simp only [LC, sideChainsRBP, List.length_map, length_unitChainsBP]; exact_mod_cast hLl
    linarith
  obtain ⟨hC2s, hC2b, hC2m⟩ := comb_units _ hρ hρ1 hR hRlen (by linarith)
  obtain ⟨hWLs, hWLb, hWLm⟩ := comb_units _ hρ hρ1 hL hLlen (by linarith)
  -- the left side is the mirror image of a comb
  have hC3eq : tLr :: LF ++ [vLr] = (((Sr, Sr) :: LC.flatten ++ [(Sr, top)]).map (mirrorR n)).reverse := by
    have hm : ∀ p : Point, mirrorR n p = (54 * (n : ℝ) - 12 - p.1, p.2) := fun p => by
      simp [mirrorR]
    simp only [LF, leftPartBP, LC, sideChainsRBP, List.map_flatten, List.map_reverse,
      List.map_map, List.map_cons, List.map_append, List.reverse_append, List.reverse_cons,
      List.reverse_flatten, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append]
    have hf : (List.map ratPoint ∘ leftChain n) =
        (List.reverse ∘ List.map ⇑(mirrorR n) ∘ List.map ratPoint) := by
      funext c
      simp [leftChain, Function.comp_def, List.map_reverse, List.map_map, ratPoint_mirror]
    rw [hm, hm]
    simp only [tLr, vLr, XLr, List.cons.injEq, true_and, hf]
    rfl
  have hC3s : ChainSimple (tLr :: LF ++ [vLr]) := by
    rw [hC3eq]; exact chainSimple_reverse (chainSimple_map _ hWLs)
  have hC3b : ∀ p ∈ chainSet (tLr :: LF ++ [vLr]),
      p.1 ≤ XLr ∧ p.2 ≤ top ∧ (top ≤ p.2 → p = tLr) := by
    intro p hp
    rw [hC3eq, chainSet_reverse, chainSet_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨a, b, c⟩ := hWLb q hq
    simp only [mirrorR, Vis.Cert.reflX_apply]
    refine ⟨by simp only [XLr]; linarith, b, fun h => ?_⟩
    simp [c h, tLr, XLr]
  -- the diagonal and the top edge
  have hD : ∀ p ∈ ArtGallery.segment wRr vRr, 54 * (n : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ Sr ∧ 1 ≤ p.2 ∧
      p.2 ≤ Sr ∧ (Sr ≤ p.1 → p = vRr) ∧ (p.2 ≤ 1 → p = wRr) := by
    intro p hp
    have hsub := fun α β c (h1 : α * wRr.1 + β * wRr.2 ≤ c) (h2 : α * vRr.1 + β * vRr.2 ≤ c) =>
      Geometry.segment_subset_of_convex (convex_halfplane α β c) h1 h2 hp
    refine ⟨?_, ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
    · have := hsub (-1) 0 (-(54 * (n : ℝ) - 6)) (by simp [wRr]) (by simp [vRr]; linarith)
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 1 0 Sr (by simp [wRr]; linarith) (by simp [vRr])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 (-1) (-1) (by simp [wRr]) (by simp [vRr]; linarith)
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 1 Sr (by simp [wRr]; linarith) (by simp [vRr])
      simp only [mem_ofPred_eq] at this; linarith
    · rcases seg_lt_or_right (α := 1) (β := 0) (c := Sr) (by simp [wRr]; linarith)
        (by simp [vRr]) hp with h' | h'
      · linarith
      · exact h'
    · rcases seg_lt_or_left (α := 0) (β := -1) (c := -1) (by simp [wRr])
        (by simp [vRr]; linarith) hp with h' | h'
      · linarith
      · exact h'
  have hTop : ∀ p ∈ ArtGallery.segment tRr tLr, p.2 = top ∧ XLr ≤ p.1 ∧ p.1 ≤ Sr := by
    intro p hp
    obtain ⟨t, ht0, ht1, rfl⟩ := hp
    simp only [tRr, tLr]
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  -- J1
  have j1 : ChainSimple (B ++ wRr :: [vRr]) := by
    refine ChainSimple.join hC1s ⟨fun h => ?_, by simp, trivial⟩ ?_
    · have := congrArg Prod.snd h; simp [wRr, vRr] at this; linarith
    · rintro x ⟨hx1, hx2⟩
      simp only [chainSet_cons_cons, chainSet_single, union_empty] at hx2
      exact (hD x hx2).2.2.2.2.2 (hC1b x hx1).2.2
  have cs1 : chainSet (B ++ wRr :: [vRr]) = chainSet (B ++ [wRr]) ∪ ArtGallery.segment wRr vRr := by
    rw [chainSet_append_cons]; simp
  -- J2
  have j2 : ChainSimple ((B ++ [wRr]) ++ vRr :: (RF ++ [tRr])) := by
    refine ChainSimple.join (by simpa using j1) (by simpa using hC2s) ?_
    rintro x ⟨hx1, hx2⟩
    have hx1' : x ∈ chainSet (B ++ wRr :: [vRr]) := by simpa using hx1
    have hx2' : x ∈ chainSet ((Sr, Sr) :: RF ++ [(Sr, top)]) := by simpa using hx2
    rw [cs1] at hx1'
    have := (hC2b x hx2').1
    rcases hx1' with h | h
    · exfalso; have := (hC1b x h).2.1; linarith
    · exact (hD x h).2.2.2.2.1 this
  have cs2 : chainSet ((B ++ [wRr]) ++ vRr :: (RF ++ [tRr])) =
      (chainSet (B ++ [wRr]) ∪ ArtGallery.segment wRr vRr) ∪
        chainSet ((Sr, Sr) :: RF ++ [(Sr, top)]) := by
    rw [chainSet_append_cons, ← cs1]; simp [vRr, tRr]
  -- J3
  have j3 : ChainSimple (((B ++ [wRr]) ++ vRr :: RF) ++ tRr :: [tLr]) := by
    refine ChainSimple.join (by simpa using j2) ⟨fun h => ?_, by simp, trivial⟩ ?_
    · have := congrArg Prod.fst h; simp [tRr, tLr, XLr] at this; linarith
    · rintro x ⟨hx1, hx2⟩
      simp only [chainSet_cons_cons, chainSet_single, union_empty] at hx2
      obtain ⟨e1, -, -⟩ := hTop x hx2
      have hx1' : x ∈ chainSet ((B ++ [wRr]) ++ vRr :: (RF ++ [tRr])) := by simpa using hx1
      rw [cs2] at hx1'
      rcases hx1' with (h | h) | h
      · exfalso; have := (hC1b x h).2.2; linarith
      · exfalso; have := (hD x h).2.2.2.1; linarith
      · exact (hC2b x h).2.2 e1.ge
  have cs3 : chainSet (((B ++ [wRr]) ++ vRr :: RF) ++ tRr :: [tLr]) =
      ((chainSet (B ++ [wRr]) ∪ ArtGallery.segment wRr vRr) ∪
        chainSet ((Sr, Sr) :: RF ++ [(Sr, top)])) ∪ ArtGallery.segment tRr tLr := by
    rw [chainSet_append_cons, ← cs2]; simp
  -- J4
  have j4 : ChainSimple ((((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: (LF ++ [vLr])) := by
    refine ChainSimple.join (by simpa using j3) (by simpa using hC3s) ?_
    rintro x ⟨hx1, hx2⟩
    have hx1' : x ∈ chainSet (((B ++ [wRr]) ++ vRr :: RF) ++ tRr :: [tLr]) := by simpa using hx1
    have hx2' : x ∈ chainSet (tLr :: LF ++ [vLr]) := by simpa using hx2
    obtain ⟨l1, l2, l3⟩ := hC3b x hx2'
    rw [cs3] at hx1'
    rcases hx1' with ((h | h) | h) | h
    · exfalso; have := (hC1b x h).1; linarith
    · exfalso; have := (hD x h).1; linarith
    · exfalso; have := (hC2b x h).1; linarith
    · exact l3 (hTop x h).1.ge
  have cs4 : chainSet ((((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: (LF ++ [vLr])) =
      (((chainSet (B ++ [wRr]) ∪ ArtGallery.segment wRr vRr) ∪
        chainSet ((Sr, Sr) :: RF ++ [(Sr, top)])) ∪ ArtGallery.segment tRr tLr) ∪
          chainSet (tLr :: LF ++ [vLr]) := by
    rw [chainSet_append_cons, ← cs3]; simp
  -- the full list
  set V := (((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: (LF ++ [vLr]) with hVdef
  have hV : (constructPosBP Φ n).map ratPoint = V := by
    have evR' : ratPoint (vR n (numC Φ)) = vRr := evR
    have etR' : ratPoint (tR n (numC Φ)) = tRr := etR
    have etL' : ratPoint (tL n (numC Φ)) = tLr := etL
    have evL' : ratPoint (vL n (numC Φ)) = vLr := evL
    rw [hVdef]
    simp only [constructPosBP, List.map_append, List.map_cons, List.map_nil, ewR, evR', etR', etL',
      evL', rightPartBP, List.map_flatten, List.append_assoc, List.cons_append,
      List.nil_append]
    rfl
  have hVb : ∀ p ∈ chainSet V, p.2 ≤ top := by
    intro p hp
    rw [cs4] at hp
    rcases hp with (((h | h) | h) | h) | h
    · have := (hC1b p h).2.2; linarith
    · have := (hD p h).2.2.2.1; linarith
    · exact (hC2b p h).2.1
    · exact (hTop p h).1.le
    · exact (hC3b p h).2.1
  have hBne : 2 ≤ (B ++ [wRr]).length := by
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
  have hVlen : 3 ≤ V.length := by simp [hVdef]; omega
  have hfst : fstPt V = wLr := by
    have := bottomBP_fst hn Φ
    rw [List.map_append, List.map_singleton, ewR] at this
    obtain ⟨b, B', hB⟩ := List.exists_cons_of_ne_nil (show B ++ [wRr] ≠ [] by simp)
    have hb : b = wLr := by rw [hB] at this; exact this
    rw [hVdef, show (((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: (LF ++ [vLr]) =
      (B ++ [wRr]) ++ (vRr :: RF ++ [tRr] ++ tLr :: (LF ++ [vLr])) by simp, hB, hb]
    rfl
  have hlst : lstPt V = vLr := by
    rw [hVdef, show (((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: (LF ++ [vLr]) =
      ((((B ++ [wRr]) ++ vRr :: RF) ++ [tRr]) ++ tLr :: LF) ++ [vLr] by simp]
    exact lstPt_append_single _ _
  have hdec := decomp_of_two_le (f := V) (by omega)
  rw [hfst, hlst] at hdec
  have hm : V.tail.dropLast ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this; omega
  have hVs : ChainSimple V := j4
  rw [hdec] at hVs
  have hsimple : (Polygon.mk V).Simple := by
    rw [hdec]
    refine simple_of_chain hm (by simpa using hVs) ?_
    rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ chainSet V := by rw [hdec]; simpa using hx2
    -- the closing edge `v_l → w_l`
    have hcl : XLr ≤ x.1 ∧ x.1 ≤ -6 ∧ 1 ≤ x.2 ∧ x.2 ≤ Sr ∧ (x.1 ≤ XLr → x = vLr) ∧
        (x.2 ≤ 1 → x = wLr) := by
      have hsub := fun α β c (h1 : α * vLr.1 + β * vLr.2 ≤ c) (h2 : α * wLr.1 + β * wLr.2 ≤ c) =>
        Geometry.segment_subset_of_convex (convex_halfplane α β c) h1 h2 hx1
      refine ⟨?_, ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
      · have := hsub (-1) 0 (-XLr) (by simp [vLr]) (by simp [wLr, XLr]; linarith)
        simp only [mem_ofPred_eq] at this; linarith
      · have := hsub 1 0 (-6) (by simp [vLr, XLr]; linarith) (by simp [wLr])
        simp only [mem_ofPred_eq] at this; linarith
      · have := hsub 0 (-1) (-1) (by simp [vLr]; linarith) (by simp [wLr])
        simp only [mem_ofPred_eq] at this; linarith
      · have := hsub 0 1 Sr (by simp [vLr]) (by simp [wLr]; linarith)
        simp only [mem_ofPred_eq] at this; linarith
      · rcases seg_lt_or_left (α := -1) (β := 0) (c := -XLr) (by simp [vLr])
          (by simp [wLr, XLr]; linarith) hx1 with h' | h'
        · linarith
        · exact h'
      · rcases seg_lt_or_right (α := 0) (β := -1) (c := -1) (by simp [vLr]; linarith)
          (by simp [wLr]) hx1 with h' | h'
        · linarith
        · exact h'
    rw [cs4] at hx2'
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hx2' with (((h | h) | h) | h) | h
    · exact Or.inl (hcl.2.2.2.2.2 (hC1b x h).2.2)
    · exfalso; have := (hD x h).1; linarith [hcl.2.1]
    · exfalso; have := (hC2b x h).1; linarith [hcl.2.1]
    · exfalso; have := (hTop x h).1; linarith [hcl.2.2.2.1]
    · exact Or.inr (hcl.2.2.2.2.1 (hC3b x h).1)
  -- the boundary: right of `x = S` only the right units, left of `x = X_L` only the left units
  have hmir : ∀ p : Point, mirrorR n (mirrorR n p) = p := fun p => by
    simp only [mirrorR, Vis.Cert.reflX_apply]; ext <;> simp
  have hbd : (Polygon.mk V).boundary ⊆ chainSet V ∪ ArtGallery.segment vLr wLr := by
    have := boundary_subset_chainSet (V := V) (by omega)
    rwa [hfst, hlst] at this
  have hcl0 : ∀ x ∈ ArtGallery.segment vLr wLr, XLr ≤ x.1 ∧ x.1 ≤ -6 := by
    intro x hx
    have hsub := fun α β c (h1 : α * vLr.1 + β * vLr.2 ≤ c) (h2 : α * wLr.1 + β * wLr.2 ≤ c) =>
      Geometry.segment_subset_of_convex (convex_halfplane α β c) h1 h2 hx
    constructor
    · have := hsub (-1) 0 (-XLr) (by simp [vLr]) (by simp [wLr, XLr]; linarith)
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 1 0 (-6) (by simp [vLr, XLr]; linarith) (by simp [wLr])
      simp only [mem_ofPred_eq] at this; linarith
  have hB1 : ∀ p ∈ (Polygon.mk V).boundary, p.1 ≤ Sr ∨
      ∃ f ∈ sideChainsRBP n k (unitSpecs n Φ).1, p ∈ chainSet f := by
    intro p hp
    rcases hbd hp with h | h
    · rw [cs4] at h
      rcases h with (((h | h) | h) | h) | h
      · left; have := (hC1b p h).2.1; linarith
      · left; exact (hD p h).2.1
      · rcases hC2m p h with h' | h'
        · left; exact h'.le
        · right; exact h'
      · left; exact (hTop p h).2.2
      · left; have := (hC3b p h).1; linarith
    · left; have := (hcl0 p h).2; linarith
  have hB2 : ∀ p ∈ (Polygon.mk V).boundary, XLr ≤ p.1 ∨
      ∃ f ∈ sideChainsRBP n k (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f := by
    intro p hp
    rcases hbd hp with h | h
    · rw [cs4] at h
      rcases h with (((h | h) | h) | h) | h
      · left; have := (hC1b p h).1; linarith
      · left; have := (hD p h).1; linarith
      · left; have := (hC2b p h).1; linarith
      · left; exact (hTop p h).2.1
      · rw [hC3eq, chainSet_reverse, chainSet_map] at h
        obtain ⟨q, hq, rfl⟩ := h
        rcases hWLm q hq with h' | h'
        · left; simp only [mirrorR, Vis.Cert.reflX_apply, h', XLr]; linarith
        · right; rw [hmir]; exact h'
    · left; exact (hcl0 p h).1
  have hB3 : ∀ p ∈ (Polygon.mk V).boundary, p.2 ≤ top := by
    intro p hp
    rcases hbd hp with h | h
    · exact hVb p h
    · have hsub := Geometry.segment_subset_of_convex (convex_halfplane 0 1 Sr)
        (by simp [vLr] : 0 * vLr.1 + 1 * vLr.2 ≤ Sr) (by simp [wLr]; linarith) h
      simp only [mem_ofPred_eq] at hsub; linarith
  rw [hV]
  refine ⟨hsimple, ?_, hB1, hB2, hB3⟩
  -- orientation: the top edge `t_r → t_l` supports the polygon
  set A := ((B ++ [wRr]) ++ vRr :: RF)
  have hVA : V = A ++ tRr :: tLr :: (LF ++ [vLr]) := by simp [hVdef, A]
  obtain ⟨g1, g2⟩ := getD_mid (A := A) (x := tRr) (y := tLr) (C := LF ++ [vLr])
  have hAl : A.length + 1 < V.length := by rw [hVA]; simp
  apply Polygon.interiorLeft_of_supporting_edge hsimple (i := A.length)
    (show A.length < V.length by omega)
  intro j hj
  have hvj : (Polygon.mk V).vtx j ∈ V := by
    have hj' : j < V.length := hj
    show V.getD j (0, 0) ∈ V
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; exact List.getElem_mem _
  have hy := hVb _ (mem_chainSet_of_mem hvj (by omega))
  have e1 : (Polygon.mk V).vtx A.length = tRr := by
    simp only [Polygon.vtx]; rw [hVA]; exact g1
  have e2 : (Polygon.mk V).vtx ((A.length + 1) % (Polygon.mk V).n) = tLr := by
    rw [Nat.mod_eq_of_lt (by simpa [Polygon.n] using hAl)]
    simp only [Polygon.vtx]; rw [hVA]; exact g2
  rw [e1, e2]
  simp only [det, tRr, tLr, XLr]
  nlinarith

end Global

end ArtGallery.BP

end