module

public import ArtGallery.Stade.LowerAssign
public import ArtGallery.Stade.Copy

/-!
# Stade's construction, (c): the copy nooks (proof plan §8.3, L5.4, L5.5)

For a boundary guard set `G` with `|G| = guards n Φ` and its guard assignment `A`
(`LowerAssign.lean`), and an input segment `j` copying the variable `k`:

* `copy_excl` (**exclusion**, L5.5): a guard seeing a point of the copy nook of `j` is the guard of
  `k` or of `j` (the partial-visibility region `copyPV` meets no other guard region: other
  variables are `≥ 650` away at the variable band, other inputs `≥ 44` away at the input band, and
  the aux regions are below the floor where `copyPV` stays within `[b − 14, b + 400]`);
* `copy_rel` (**coverage ⇒ copy inequality**, L5.4): with `v_k = (y(γ_k) − H + 1)/2` and
  `w_j = (y(γ_j) + 2)/4`, `w_j ≤ v_k` for type GE and `v_k ≤ w_j` for type LE.

Also the generic facts `chain_of_infix_gen`, `pedge_of_infix_gen` (consecutive points of a real
vertex list are consecutive vertices).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Consecutive vertices of a real vertex list -/

/-- A contiguous part of a vertex list is a run of consecutive vertices. -/
theorem chain_of_infix_gen {L M : List Point} (h : M <:+: L) :
    ∃ a, a + M.length ≤ L.length ∧ ∀ j (hj : j < M.length), (Polygon.mk L).vtx (a + j) = M[j] := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨s.length, by simp, fun j hj => ?_⟩
  unfold Polygon.vtx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  simp only [Option.getD_some]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-- Two consecutive points of a contiguous part of a vertex list form an edge. -/
theorem pedge_of_infix_gen {L M : List Point} (h : M <:+: L) {j : ℕ} (hj : j + 1 < M.length) :
    ∃ i < (Polygon.mk L).n, (Polygon.mk L).vtx i = M[j] ∧
      (Polygon.mk L).vtx ((i + 1) % (Polygon.mk L).n) = M[j + 1] := by
  obtain ⟨a, ha, hv⟩ := chain_of_infix_gen h
  have hn : (Polygon.mk L).n = L.length := rfl
  refine ⟨a + j, by omega, hv j (by omega), ?_⟩
  rw [hn, Nat.mod_eq_of_lt (by omega), show a + j + 1 = a + (j + 1) by omega]
  exact hv (j + 1) hj

/-- A segment between consecutive points of a contiguous part lies on the boundary. -/
theorem seg_subset_boundary {L M : List Point} (h : M <:+: L) {j : ℕ} (hj : j + 1 < M.length) :
    segment M[j] M[j + 1] ⊆ (Polygon.mk L).boundary := by
  obtain ⟨i, hi, h1, h2⟩ := pedge_of_infix_gen h hj
  intro x hx
  refine ⟨i, hi, ?_⟩
  unfold Polygon.edge
  rw [h1, h2]
  exact hx

/-! ### Positions of the assigned guards -/

section Assign

variable {G : Finset Point} (A : Assign n Φ G)

theorem cast_paramH (n : ℕ) (Φ : List Constraint) :
    (((paramH n Φ : ℚ)) : ℝ) = (paramH n Φ : ℝ) := Rat.cast_natCast _

/-- Every assigned guard lies strictly below the ceiling. -/
theorem Assign.snd_lt (X : Idx n Φ) : (A.γ X).2 < 2 * (paramH n Φ : ℝ) := by
  have hH := paramH_ge_r n Φ
  rcases X with k | j | j
  · have := A.var k; linarith
  · have := A.inp j; linarith
  · have := auxRegion_bounds (addSlot_isAdd j) (A.aux j); linarith

/-- The slot structure of an input: `b = g_c + δ`, `δ ∈ [30, 600]`. -/
theorem input_slot {i : InputSeg} (hi : i ∈ inputs n Φ) :
    ∃ c < paramC Φ, ∃ t ∈ tmplInputs (cKind (gadAt Φ c)),
      (i.b : ℝ) = (slotG n Φ c : ℝ) + (t.lx : ℝ) ∧ i.ge = t.ge ∧ 30 ≤ (t.lx : ℝ) ∧
        (t.lx : ℝ) ≤ 600 := by
  obtain ⟨c, hc, t, ht, hb, -, hge⟩ := mem_inputs hi
  have := tmplInputs_x ht
  refine ⟨c, hc, t, ht, by rw [hb]; push_cast; ring, hge, by exact_mod_cast this.1,
    by exact_mod_cast this.2⟩

theorem slot_lt_real {c c' : ℕ} (h : c < c') :
    (slotG n Φ c : ℝ) + 1200 ≤ (slotG n Φ c' : ℝ) := by
  exact_mod_cast s2_slot (n := n) (Φ := Φ) h

end Assign

/-! ### The copy nooks -/

/-- Template inputs of the addition gadgets of type GE lie at local abscissa `≥ 200`. -/
theorem tmplInputs_add_ge_ok :
    (tmplInputs .addLe).all (fun t => !t.ge || decide (200 ≤ t.lx)) &&
      (tmplInputs .addGe).all (fun t => !t.ge || decide (200 ≤ t.lx)) = true := by
  decide +kernel

/-- Below the input band, the partial-visibility region of a copy nook stays left of
`b + 400`. -/
theorem copyPV_low_upper {H a b : ℝ} {ge : Bool} (hp : CopyParams H a b) {p : Point}
    (hpv : p ∈ copyPV ge H a b) (hy1 : -130 ≤ p.2) (hy2 : p.2 ≤ 0) : p.1 ≤ b + 400 := by
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  by_contra hc; push Not at hc
  cases ge
  · obtain ⟨-, h2⟩ := copyLE_PV_poly hp hpv
    have hQ : 0 ≤ (2 * H - 3) * (b - a + 16) := by nlinarith
    have h3 : -p.2 * ((2 * H - 3) * (b - a + 16)) ≤ 130 * ((2 * H - 3) * (b - a + 16)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    have h4 : 0 < (2 * H - 1) * (H - 3) := by nlinarith
    have h5 : 400 * ((2 * H - 1) * (H - 3)) < (p.1 - b) * ((2 * H - 1) * (H - 3)) :=
      mul_lt_mul_of_pos_right (by linarith) h4
    nlinarith
  · obtain ⟨-, h2⟩ := copyGE_PV_poly hp hpv
    have hQ : 0 ≤ (2 * H - 3) * (b - a - 6) := by nlinarith
    have h3 : (6 - p.2) * ((2 * H - 3) * (b - a - 6)) ≤ 136 * ((2 * H - 3) * (b - a - 6)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    have h4 : 0 < (H - 1) * (H - 3) := by nlinarith
    have h5 : 400 * ((H - 1) * (H - 3)) < (p.1 - b) * ((H - 1) * (H - 3)) :=
      mul_lt_mul_of_pos_right (by linarith) h4
    nlinarith

section Copy

variable {G : Finset Point} (A : Assign n Φ G)

/-- Real parameters of the copy nook of input `j`. -/
theorem copyParams_j (j : Fin (inputs n Φ).length) (hk : (inputs n Φ)[j].var < n) :
    CopyParams (((paramH n Φ : ℚ)) : ℝ) (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ)
      (((inputs n Φ)[j].b : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := input_delta (input_mem j) hk
  exact CopyParams.of_rat (paramH_ge_q n Φ) (by linarith) (by linarith)

/-- The vertices `R_m, N_top, N_bot, L_m` of the copy nook of input `j` are consecutive in
`SP n Φ`. -/
theorem copy_chain (j : Fin (inputs n Φ).length) (hk : (inputs n Φ)[j].var < n) :
    [copyRm (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ)
        (((inputs n Φ)[j].b : ℚ) : ℝ),
      copyNtop (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ)
        (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ),
      copyNbot (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ)
        (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ),
      copyLm (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ) (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ)
        (((inputs n Φ)[j].b : ℚ) : ℝ)] <:+: (poly n Φ).map ratPoint := by
  rw [← copyNook_map]
  exact (ceil_infix (copyNook_mem (input_mem j) hk)).map _

/-- **Exclusion for copy nooks (L5.5).** A guard seeing a point of the copy nook of input `j` is
the guard of its variable or of `j`. -/
theorem copy_excl (j : Fin (inputs n Φ).length) (hk : (inputs n Φ)[j].var < n) {s : Point}
    (hs : s ∈ segment (copyNbot (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ))
      (copyNtop (inputs n Φ)[j].ge (((paramH n Φ : ℚ)) : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ)))
    (X : Idx n Φ) (hX : (SP n Φ).Sees (A.γ X) s) :
    X = .inl ⟨(inputs n Φ)[j].var, hk⟩ ∨ X = .inr (.inl j) := by
  have hp := copyParams_j j hk
  have hch := copy_chain j hk
  have hHq := paramH_ge_q n Φ
  have hHr := paramH_ge_r n Φ
  rw [cast_paramH] at hp hch hs
  have hpv := copy_viewer_mem_PV_of_walls (simple n Φ) (interiorLeft n Φ) _ hp
    (pedge_of_infix_gen hch (j := 2) (by simp)) (pedge_of_infix_gen hch (j := 0) (by simp))
    (pedge_of_infix_gen hch (j := 1) (by simp)) hs (A.snd_lt X) hX
  set i := (inputs n Φ)[j] with hi_def
  rcases X with k' | j' | j'
  · -- another variable: excluded at the variable band
    left
    obtain ⟨hx, hy1, hy2⟩ := A.var k'
    have hb := copyPV_var_band _ hp hpv hy1 hy2
    rw [hx] at hb
    congr 1
    refine Fin.ext ?_
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := s2_var (Φ := Φ) h
      have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
      have : ((varA Φ k' : ℚ) : ℝ) + 50 ≤ ((varA Φ i.var : ℚ) : ℝ) := by
        exact_mod_cast (by linarith : (varA Φ k' : ℚ) + 50 ≤ varA Φ i.var)
      linarith [hb.1]
    · have := s2_var (Φ := Φ) h
      have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
      have : ((varA Φ i.var : ℚ) : ℝ) + 50 ≤ ((varA Φ k' : ℚ) : ℝ) := by
        exact_mod_cast (by linarith : (varA Φ i.var : ℚ) + 50 ≤ varA Φ k')
      linarith [hb.2]
  · -- another input: excluded at the input band
    right
    obtain ⟨hx, hy1, hy2⟩ := A.inp j'
    have hb := copyPV_in_band _ hp hpv hy1 hy2
    rw [hx] at hb
    have heq := input_eq_of_near (input_mem j') (input_mem j) (by rw [abs_lt]; constructor <;>
      linarith [hb.1, hb.2])
    rw [input_inj heq]
  · -- an aux region: excluded below the floor
    exfalso
    have hab := auxRegion_bounds (addSlot_isAdd j') (A.aux j')
    obtain ⟨hax1, hax2, hay1, hay2, hle, hge⟩ := hab
    set p := A.γ (.inr (.inr j'))
    have hlow := copyPV_low _ hp hpv (by linarith)
    have hup := copyPV_low_upper hp hpv hay1 (by linarith)
    obtain ⟨c, hc, t, ht, hb, hge', ht1, ht2⟩ := input_slot (input_mem j)
    set c' := addSlot Φ j'
    rcases lt_trichotomy c c' with hlt | heq | hgt
    · have := slot_lt_real (n := n) (Φ := Φ) hlt
      linarith
    · -- the same slot: an addition gadget; the copy region passes right of the aux region
      have hkd : IsAdd (cKind (gadAt Φ c)) := by rw [heq]; exact addSlot_isAdd j'
      rw [← heq] at hax1 hax2 hle hge
      have hok := tmplInputs_add_ok
      have hok' := tmplInputs_add_ge_ok
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
        Bool.not_eq_true'] at hok hok'
      cases hig : i.ge
      · have hlowLE := copyPV_low_LE hp (hig ▸ hpv) (by linarith)
        rcases hkd with hkd | hkd
        · rw [hkd] at ht
          have : (200 : ℝ) ≤ t.lx := by exact_mod_cast hok.1 t ht
          linarith
        · rw [hkd] at ht
          have : (90 : ℝ) ≤ t.lx := by exact_mod_cast hok.2 t ht
          linarith [hge hkd]
      · have htge : t.ge = true := by rw [← hge', hig]
        rcases hkd with hkd | hkd
        · rw [hkd] at ht
          have : (200 : ℝ) ≤ t.lx := by
            have := (hok'.1 t ht).resolve_left (by rw [htge]; simp)
            exact_mod_cast this
          linarith [(hle hkd).2]
        · rw [hkd] at ht
          have : (200 : ℝ) ≤ t.lx := by
            have := (hok'.2 t ht).resolve_left (by rw [htge]; simp)
            exact_mod_cast this
          linarith [hge hkd]
    · have := slot_lt_real (n := n) (Φ := Φ) hgt
      linarith

/-- The value of the guard of variable `k`: `(y − H + 1)/2`. -/
noncomputable def Assign.val (k : Fin n) : ℝ := ((A.γ (.inl k)).2 - (paramH n Φ : ℝ) + 1) / 2

/-- The value of the guard of input `j`: `(y + 2)/4`. -/
noncomputable def Assign.ival (j : Fin (inputs n Φ).length) : ℝ := ((A.γ (.inr (.inl j))).2 + 2) / 4

theorem Assign.val_mem (k : Fin n) : 1 / 2 ≤ A.val k ∧ A.val k ≤ 2 := by
  have := A.var k; unfold Assign.val; constructor <;> linarith

theorem Assign.ival_mem (j : Fin (inputs n Φ).length) : 1 / 2 ≤ A.ival j ∧ A.ival j ≤ 2 := by
  have := A.inp j; unfold Assign.ival; constructor <;> linarith

theorem Assign.γ_var (k : Fin n) :
    A.γ (.inl k) = varPt (paramH n Φ : ℝ) ((varA Φ k : ℚ) : ℝ) (A.val k) := by
  have := A.var k
  refine Prod.ext this.1 ?_
  simp only [varPt_snd, Assign.val]; ring

theorem Assign.γ_inp (j : Fin (inputs n Φ).length) :
    A.γ (.inr (.inl j)) = inPt ((inputs n Φ)[j].b : ℝ) (A.ival j) := by
  have := A.inp j
  refine Prod.ext this.1 ?_
  simp only [inPt_snd, Assign.ival]; ring

/-- **Copy nooks: coverage ⇒ copy inequality (L5.4, §8.3).** For an input `j` copying the
variable `k`: `w_j ≤ v_k` (type GE), `v_k ≤ w_j` (type LE). -/
theorem copy_rel (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point))
    (j : Fin (inputs n Φ).length) (hk : (inputs n Φ)[j].var < n) :
    ((inputs n Φ)[j].ge = true → A.ival j ≤ A.val ⟨(inputs n Φ)[j].var, hk⟩) ∧
      ((inputs n Φ)[j].ge = false → A.val ⟨(inputs n Φ)[j].var, hk⟩ ≤ A.ival j) := by
  have hp := copyParams_j j hk
  have hch := copy_chain j hk
  rw [cast_paramH] at hp hch
  have hw0 := pedge_of_infix_gen hch (j := 2) (by simp)
  have hw2 := pedge_of_infix_gen hch (j := 0) (by simp)
  have hw3 := pedge_of_infix_gen hch (j := 1) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hw0 hw2 hw3
  have hbd : segment (copyNbot (inputs n Φ)[j].ge (paramH n Φ : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ))
      (copyNtop (inputs n Φ)[j].ge (paramH n Φ : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ)) ⊆
      (SP n Φ).boundary := by
    rw [Geometry.segment_comm]
    exact seg_subset_boundary hch (j := 1) (by simp)
  have hcov : ∀ s ∈ segment (copyNbot (inputs n Φ)[j].ge (paramH n Φ : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ))
      (copyNtop (inputs n Φ)[j].ge (paramH n Φ : ℝ)
      (((varA Φ (inputs n Φ)[j].var : ℚ)) : ℝ) (((inputs n Φ)[j].b : ℚ) : ℝ)),
      (SP n Φ).Sees (varPt (paramH n Φ : ℝ) ((varA Φ (inputs n Φ)[j].var : ℚ) : ℝ)
          (A.val ⟨(inputs n Φ)[j].var, hk⟩)) s ∨
        (SP n Φ).Sees (inPt ((inputs n Φ)[j].b : ℝ) (A.ival j)) s := by
    intro s hs
    obtain ⟨X, hX⟩ := A.cover hG (hbd hs)
    have hs' := hs
    rw [← cast_paramH] at hs'
    rcases copy_excl A j hk hs' X hX with rfl | rfl
    · left
      have e1 := A.γ_var ⟨_, hk⟩
      simp only at e1
      rw [e1] at hX; exact hX
    · right; rw [← A.γ_inp]; exact hX
  have hv := A.val_mem ⟨(inputs n Φ)[j].var, hk⟩
  have hw := A.ival_mem j
  constructor
  · intro hge
    rw [hge] at hw0 hw2 hw3 hcov
    exact copyGE_rel_of_walls (simple n Φ) (interiorLeft n Φ) hp hw0 hw2 hw3 hv.1 hv.2
      hw.1 hw.2 hcov
  · intro hge
    rw [hge] at hw0 hw2 hw3 hcov
    exact copyLE_rel_of_walls (simple n Φ) (interiorLeft n Φ) hp hw0 hw2 hw3 hv.1 hv.2
      hw.1 hw.2 hcov

end Copy

end ArtGallery.Stade

end
