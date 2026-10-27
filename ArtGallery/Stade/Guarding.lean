module

public import ArtGallery.Stade.GuardCanon

/-!
# Stade's construction, fact (b): a solution gives a guard set (proof plan §9)

**Main result** `guardSet_of_sat_of_region`: for an instance `Φ` on the variables `< n`
(`0 < n`) and a solution `v` with values in `[1/2, 2]`, if the region of `SP n Φ` is the union
of the convex pieces `regionPieces n Φ` (`RegionDecomp n Φ`, proof plan L2.3), then the
canonical guard set `canonGuards n Φ v` has `guards n Φ` elements, is a guard set of the
polygon, and contains the guard `(varX i, varY0 + 2 v_i)` of every variable `i < n`.

Proof: every piece is seen by the canonical guards —
* the hall (convex) by the guard of variable `0`;
* the ceiling wedges and the floor needles of the variables and inputs by the guard of their
  segment region (`GuardCeil.lean`, `GuardWedges.lean`);
* the copy pockets by the variable guard and the input guard (`copy_feat_cover`);
* the pieces of the gadget slots by the guards of the slot (`slot_cover`), using that the
  constraint of the slot holds;
and the canonical guards are pairwise distinct (`canonGuards_card`) and lie in the hall or in a
room of an addition gadget.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

variable {n : ℕ} {Φ : List Constraint} {v : ℕ → ℝ}

/-! ### Constraints -/

/-- The relation of a slot holds when its constraint holds. -/
theorem kRel_of_holds {c : ℕ} (hc : c < paramC Φ) (hsol : ∀ c ∈ Φ, c.Holds v) :
    kRel (cKind (gadAt Φ c)) (v (gadVar Φ c 0)) (v (gadVar Φ c 1)) (v (gadVar Φ c 2)) := by
  have h := hsol _ (gadAt_mem hc)
  unfold gadVar
  cases hg : gadAt Φ c with
  | one x => have := gadAt_isGad hc; rw [hg] at this; simp [isGad] at this
  | invGe x y => rw [hg] at h; simpa [kRel, cKind, cVars, Constraint.Holds] using h
  | invRevLe x y => rw [hg] at h; simpa [kRel, cKind, cVars, Constraint.Holds] using h
  | addLe x y z => rw [hg] at h; simpa [kRel, cKind, cVars, Constraint.Holds] using h
  | addGe x y z => rw [hg] at h; simpa [kRel, cKind, cVars, Constraint.Holds] using h

/-- A variable with a constraint `x = 1` has value `1`. -/
theorem val_one_of_hasOne (hsol : ∀ c ∈ Φ, c.Holds v) {k : ℕ} (h : hasOne Φ k = true) :
    v k = 1 := by
  obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 h
  cases c with
  | one x =>
    simp only [isOneOf, beq_iff_eq] at hck
    subst hck
    exact hsol _ hc
  | _ => simp [isOneOf] at hck

/-! ### Positions -/

/-- Every variable abscissa is at least `H + 100` left of the right wall. -/
theorem varA_le_xR {k : ℕ} (hk : k < n) : (varA Φ k : ℝ) + hH n Φ + 100 ≤ (xR n Φ : ℝ) := by
  have hva := var_lt_xR (Φ := Φ) hk
  have h' : (((varA Φ k : ℚ) + (paramH n Φ : ℚ) + 100 : ℚ) : ℝ) ≤ (xR n Φ : ℝ) := by
    exact_mod_cast hva
  push_cast at h'
  unfold hH; linarith

/-- The left wall is at `x ≤ −3000`, over `ℝ`. -/
theorem xL_le_neg (n : ℕ) (Φ : List Constraint) : (xL n Φ : ℝ) ≤ -3000 := by
  exact_mod_cast xL_neg n Φ

/-- The variable guards lie in the hall. -/
theorem varGuard_hall (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) {k : ℕ} (hk : k < n) :
    varGuard n Φ v k ∈ piece (hallPoly n Φ) := by
  have h1 := varA_le_xR (Φ := Φ) hk
  have h2 := xL_le_neg n Φ
  have h3 : (0 : ℝ) ≤ (varA Φ k : ℝ) := by positivity
  have hH0 := hH_ge n Φ
  have := hv k
  exact mem_hall.2 ⟨by simp only [varGuard]; linarith, by simp only [varGuard]; linarith,
    by simp only [varGuard]; linarith, by simp only [varGuard, hH] at *; linarith⟩

/-- Every input abscissa is far from the walls, over `ℝ`. -/
theorem input_b_real {i : InputSeg} (hi : i ∈ inputs n Φ) :
    (xL n Φ : ℝ) + 3000 ≤ (i.b : ℝ) ∧ (i.b : ℝ) + 700 ≤ (xR n Φ : ℝ) := by
  have hb := input_b_bounds hi
  have hX0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
  have h2 := xL_neg n Φ
  constructor
  · have : xL n Φ + 3000 ≤ i.b := by linarith [hb.1]
    exact_mod_cast this
  · exact_mod_cast hb.2

/-- The input guards lie in the hall. -/
theorem inGuard_hall (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) {i : InputSeg} (hi : i ∈ inputs n Φ) :
    inGuard v i ∈ piece (hallPoly n Φ) := by
  obtain ⟨h1, h2⟩ := input_b_real hi
  have hH0 := hH_ge n Φ
  have := hv i.var
  exact mem_hall.2 ⟨by simp only [inGuard]; linarith, by simp only [inGuard]; linarith,
    by simp only [inGuard]; linarith, by simp only [inGuard]; linarith⟩

/-- The aux guard of an addition slot lies in a piece of the slot. -/
theorem auxGuard_piece (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) {c : ℕ}
    (hc : c < paramC Φ) (ha : isAdd (gadAt Φ c) = true) :
    ∃ K ∈ slotPieces (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (hH n Φ),
      auxGuard n Φ v c ∈ piece K := by
  have hrel := hsol _ (gadAt_mem hc)
  unfold auxGuard
  cases h : gadAt Φ c with
  | one x => rw [h] at ha; simp [isAdd] at ha
  | invGe x y => rw [h] at ha; simp [isAdd] at ha
  | invRevLe x y => rw [h] at ha; simp [isAdd] at ha
  | addLe x y z =>
    rw [h] at hrel
    simp only [Constraint.Holds] at hrel
    simp only [cKind, auxPt, gadVar, h, cVars, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨alRoom _, by simp [slotPieces, alPieces], (alI_mem_auxRegion (hv x).1 (hv y).1
      (by linarith [(hv z).2])).2⟩
  | addGe x y z =>
    simp only [cKind, auxPt, gadVar, h, cVars, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨agRoom _, by simp [slotPieces, agPieces],
      (agI_mem_auxRegion (hv x).1 (hv x).2 (hv y).1 (hv y).2).2⟩

/-! ### Coverage of the ceiling features -/

/-- Cast of `H` from `ℚ` to `ℝ`. -/
theorem guard_cast_paramH : ((paramH n Φ : ℚ) : ℝ) = hH n Φ := by simp [hH]

/-- Cast of a variable abscissa from `ℚ` to `ℝ`. -/
theorem guard_cast_varA (k : ℕ) : (((varA Φ k : ℕ) : ℚ) : ℝ) = (varA Φ k : ℝ) := by simp

/-- **The ceiling features are seen by the canonical guards.** -/
theorem ceil_feature_cover (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (hHP : piece (hallPoly n Φ) ⊆ (SP n Φ).filled) {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeats n Φ)
    (hTP : piece (Polygon.mk (f.map ratPoint)) ⊆ (SP n Φ).filled) :
    ∀ z ∈ piece (Polygon.mk (f.map ratPoint)), ∃ g ∈ canonList n Φ v, (SP n Φ).Sees g z := by
  have hH0 := hH_ge n Φ
  have hxL := xL_le_neg n Φ
  intro z hz
  rcases mem_ceilFeats hf with ⟨i, hi, hfi⟩ | ⟨k, hk, hfk⟩ | ⟨k, hk, i, hi, hik, rfl⟩
  · -- input wedges
    obtain ⟨b1, b2⟩ := input_b_real hi
    have hw := hv i.var
    have hf' : f = wedgeW1 i.b i.pos (paramH n Φ) ∨
        f = wedgeW3 i.b i.pos (4 * (paramH n Φ : ℚ)) (paramH n Φ) := by
      unfold inputCeil at hfi
      cases hp : i.pos <;> rw [hp] at hfi <;>
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true,
          ↓reduceIte] at hfi <;>
        tauto
    have hT : (((4 * (paramH n Φ : ℚ)) : ℚ) : ℝ) = 4 * hH n Φ := by push_cast; simp [hH]
    refine ⟨inGuard v i, inGuard_mem hi, seg_wedge_cover hHP (s := i.b) (by linarith)
      (by linarith) (T := 4 * (paramH n Φ : ℚ)) (y := 4 * v i.var - 2) (by linarith)
      (by linarith) (by linarith) (by rw [hT]; linarith) (by rw [hT]; nlinarith) hf' hTP z hz⟩
  · -- variable wedges
    have hw := hv k
    have hva := varA_le_xR (Φ := Φ) hk
    have h0 : (0 : ℝ) ≤ (varA Φ k : ℝ) := by positivity
    have hgk : varGuard n Φ v k ∈ canonList n Φ v := varGuard_mem hk
    have hPH : (paramH n Φ : ℝ) = hH n Φ := rfl
    unfold varCeil at hfk
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hfk
    rcases hfk with (hf1 | hf3) | hf45
    · refine ⟨_, hgk, ?_⟩
      have := seg_wedge_cover hHP (s := (varA Φ k : ℚ)) (by rw [guard_cast_varA]; linarith)
        (by rw [guard_cast_varA]; linarith) (T := 3 * (paramH n Φ : ℚ)) (y := hH n Φ + 2 * v k - 1)
        le_rfl (by linarith) (by linarith) (by push_cast; rw [hPH]; linarith)
        (by push_cast; rw [hPH]; nlinarith) (Or.inl hf1) hTP z hz
      rwa [guard_cast_varA] at this
    · refine ⟨_, hgk, ?_⟩
      have := seg_wedge_cover hHP (s := (varA Φ k : ℚ)) (by rw [guard_cast_varA]; linarith)
        (by rw [guard_cast_varA]; linarith) (T := 3 * (paramH n Φ : ℚ)) (y := hH n Φ + 2 * v k - 1)
        le_rfl (by linarith) (by linarith) (by push_cast; rw [hPH]; linarith)
        (by push_cast; rw [hPH]; nlinarith) (Or.inr hf3) hTP z hz
      rwa [guard_cast_varA] at this
    · cases hone : hasOne Φ k
      · rw [hone] at hf45; simp at hf45
      · rw [hone] at hf45
        simp only [↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hf45
        have h1 := val_one_of_hasOne hsol hone
        refine ⟨_, hgk, ?_⟩
        have := one_wedge_cover hHP (s := (varA Φ k : ℚ)) (by rw [guard_cast_varA]; linarith)
          (by rw [guard_cast_varA]; linarith) hf45 hTP z hz
        rw [guard_cast_varA] at this
        have e : varGuard n Φ v k = ((varA Φ k : ℝ), hH n Φ + 1) := by
          simp only [varGuard, h1, hH]; ring_nf
        rw [e]; exact this
  · -- copy nooks
    have hw := hv i.var
    rcases copy_feat_cover hHP hi (by rw [hik]; exact hk) (by rw [hik]; exact hTP) hw.1 hw.2 z
      (by rw [hik]; exact hz) with h | h
    · refine ⟨varGuard n Φ v i.var, varGuard_mem (by rw [hik]; exact hk), ?_⟩
      simpa [varGuard, hH] using h
    · exact ⟨inGuard v i, inGuard_mem hi, h⟩

/-! ### The main theorem -/

/-- **Fact (b) of Stade's construction**, assuming the region decomposition (proof plan L2.3):
a solution `v` with values in `[1/2, 2]` gives a guard set of cardinality `guards n Φ`
containing the guard `(varX i, varY0 + 2 v_i)` of every variable `i < n`. -/
theorem guardSet_of_sat_of_region (hn : 0 < n) (hreg : RegionDecomp n Φ)
    (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    ∃ G : Finset Point, G.card = guards n Φ ∧
      (Polygon.mk ((poly n Φ).map ratPoint)).IsGuardSet (G : Set Point) ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G := by
  have hP := simple n Φ
  have hL := interiorLeft n Φ
  have hH0 := hH_ge n Φ
  have hxL := xL_le_neg n Φ
  have hKP : ∀ K ∈ regionPieces n Φ, piece K ⊆ (SP n Φ).filled := hreg.2
  have hHP : piece (hallPoly n Φ) ⊆ (SP n Φ).filled := hKP _ (mem_regionPieces.2 (Or.inl rfl))
  refine ⟨canonGuards n Φ v, canonGuards_card hv hsol, ⟨?_, ?_⟩, ?_⟩
  · -- the guards lie in the region
    intro g hg
    have hg' : g ∈ canonList n Φ v := List.mem_toFinset.1 hg
    unfold canonList at hg'
    simp only [List.mem_append, List.mem_map, List.mem_range] at hg'
    rcases hg' with (⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨c, hc, rfl⟩
    · exact hHP (varGuard_hall hv hk)
    · exact hHP (inGuard_hall hv hi)
    · obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
      have hc1 := List.mem_range.1 hc1
      obtain ⟨K, hK, hgK⟩ := auxGuard_piece hv hsol hc1 hc2
      exact hKP K (mem_regionPieces.2 (Or.inr (Or.inr (Or.inr ⟨c, hc1, hK⟩)))) hgK
  · -- every point of the region is seen
    intro z hz
    obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.1 (hreg.1 hz)
    have hKP' := hKP K hK
    suffices h : ∃ g ∈ canonList n Φ v, (SP n Φ).Sees g z by
      obtain ⟨g, hg, hgz⟩ := h
      exact ⟨g, List.mem_toFinset.2 hg, hgz⟩
    rcases mem_regionPieces.1 hK with rfl | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, hKc⟩
    · -- the hall
      exact ⟨_, varGuard_mem hn, sees_of_convex (convex_piece _) hHP (varGuard_hall hv hn) hzK⟩
    · exact ceil_feature_cover hv hsol hHP hf hKP' z hzK
    · -- the floor needle of a variable
      have hw := hv k
      refine ⟨_, varGuard_mem hk, var_needle_cover hHP hk (y := hH n Φ + 2 * v k - 1)
        (by linarith) (by linarith) hKP' z hzK⟩
    · -- a gadget slot
      have hG0 : (0 : ℝ) ≤ (slotG n Φ c : ℝ) := by positivity
      have hGR : (slotG n Φ c : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by
        have := slot_lt_xR (n := n) hc
        exact_mod_cast this
      have hFA : ∀ x, (slotG n Φ c : ℝ) + 30 ≤ x → x ≤ (slotG n Φ c : ℝ) + 600 →
          ((x, -1) : Point) ∈ piece (hallPoly n Φ) := fun x h1 h2 =>
        mem_hall.2 ⟨by linarith, by linarith, le_rfl, by linarith⟩
      have hBA : ∀ x y, (slotG n Φ c : ℝ) + 30 ≤ x → x ≤ (slotG n Φ c : ℝ) + 600 → 0 ≤ y →
          y ≤ 6 → ((x, y) : Point) ∈ piece (hallPoly n Φ) := fun x y h1 h2 h3 h4 =>
        mem_hall.2 ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hSP : ∀ K' ∈ slotPieces (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (hH n Φ),
          piece K' ⊆ (SP n Φ).filled := fun K' hK' =>
        hKP K' (mem_regionPieces.2 (Or.inr (Or.inr (Or.inr ⟨c, hc, hK'⟩))))
      obtain ⟨g, hg, hgz⟩ := slot_cover hP hL (cKind (gadAt Φ c)) hH0 (convex_piece _) hHP hFA
        hBA hSP (slot_walls hc) (hv _).1 (hv _).2 (hv _).1 (hv _).2 (hv _).1 (hv _).2
        (kRel_of_holds hc hsol) K hKc z hzK
      exact ⟨g, slotGuards_mem hc hg, hgz⟩
  · -- the variable guards
    intro i hi
    have e : ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) = varGuard n Φ v i := by
      simp only [varX, varY0, varGuard]
      push_cast
      ring_nf
    rw [e]
    exact List.mem_toFinset.2 (varGuard_mem hi)

end ArtGallery.Stade

end
