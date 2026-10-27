module

public import ArtGallery.Stade.LowerCopy
public import ArtGallery.Stade.Inversion
public import ArtGallery.Stade.AdditionGeomGe

/-!
# Stade's construction, (c): the constraint gadgets (proof plan §8.3, L6.3, L6.4, L7.4, L7.6)

For a boundary guard set `G` with `|G| = guards n Φ` and its guard assignment `A`, and a slot `c`
whose gadget constraint is

* `invGe x y`: the input values satisfy `1 ≤ w_x w_y` (`invGe_rel`);
* `invRevLe x y`: `w_x (5/2 − w_y) ≤ 1` (`invRevLe_rel`);
* `addLe x y z`: `w_x + w_y ≤ w_z` (`addLe_rel`);
* `addGe x y z`: `w_z ≤ w_x + w_y` (`addGe_rel`).

In each case the nook segments consist of boundary points; a guard seeing a nook point lies in
the partial-visibility region of the nook (gadget files), which meets no guard region except
those of the designated guards (exclusion, proved here from the positions of `Assign`); hence the
designated guards cover the nooks and the coverage lemmas of the gadget files apply.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Slots and their inputs -/

theorem cast_slotG (n : ℕ) (Φ : List Constraint) (c : ℕ) :
    (((slotG n Φ c : ℚ)) : ℝ) = (slotG n Φ c : ℝ) := Rat.cast_natCast _

/-- The inputs of a slot are inputs. -/
theorem slotInputs_sub {c : ℕ} (hc : c < paramC Φ) {i : InputSeg} (hi : i ∈ slotInputs n Φ c) :
    i ∈ inputs n Φ := by
  simp only [inputs, List.mem_flatMap, List.mem_range]
  exact ⟨c, hc, hi⟩

/-- An input of a slot has an index. -/
theorem slotInput_idx {c : ℕ} (hc : c < paramC Φ) {i : InputSeg} (hi : i ∈ slotInputs n Φ c) :
    ∃ j : Fin (inputs n Φ).length, (inputs n Φ)[j] = i := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem (slotInputs_sub hc hi)
  exact ⟨⟨j, hj⟩, e⟩

/-- An input whose abscissa is near slot `c` belongs to slot `c`: `b = g_c + δ` for a template
input of the gadget of `c`. -/
theorem input_near_slot {c : ℕ} (hc : c < paramC Φ) {i : InputSeg} (hi : i ∈ inputs n Φ)
    (h1 : (slotG n Φ c : ℝ) - 400 ≤ i.b) (h2 : (i.b : ℝ) ≤ (slotG n Φ c : ℝ) + 1000) :
    ∃ t ∈ tmplInputs (cKind (gadAt Φ c)), (i.b : ℝ) = (slotG n Φ c : ℝ) + (t.lx : ℝ) := by
  obtain ⟨c', hc', t, ht, hb, -, ht1, ht2⟩ := input_slot hi
  rcases lt_trichotomy c' c with hlt | rfl | hgt
  · have := slot_lt_real (n := n) (Φ := Φ) hlt; linarith
  · exact ⟨t, ht, hb⟩
  · have := slot_lt_real (n := n) (Φ := Φ) hgt; linarith

/-- The index of the aux guard of an addition slot. -/
theorem addSlot_idx {c : ℕ} (hc : c < paramC Φ) (hadd : isAdd (gadAt Φ c) = true) :
    ∃ ja : Fin (addSlotList Φ).length, addSlot Φ ja = c := by
  have : c ∈ addSlotList Φ := by
    simp only [addSlotList, List.mem_filter, List.mem_range]; exact ⟨hc, hadd⟩
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem this
  exact ⟨⟨j, hj⟩, e⟩

/-- Two inputs with the same abscissa are the same index. -/
theorem idx_eq_of_b {j j' : Fin (inputs n Φ).length}
    (h : |((inputs n Φ)[j].b : ℝ) - (inputs n Φ)[j'].b| < 44) : j = j' :=
  input_inj (input_eq_of_near (input_mem j) (input_mem j') h)

section Gadgets

variable {G : Finset Point} (A : Assign n Φ G)

/-- The position of an aux guard: in its slot, below the floor. -/
theorem Assign.aux_pos (j : Fin (addSlotList Φ).length) :
    (slotG n Φ (addSlot Φ j) : ℝ) + 80 ≤ (A.γ (.inr (.inr j))).1 ∧
      (A.γ (.inr (.inr j))).1 ≤ (slotG n Φ (addSlot Φ j) : ℝ) + 121 ∧
      -130 ≤ (A.γ (.inr (.inr j))).2 ∧ (A.γ (.inr (.inr j))).2 ≤ -2 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := auxRegion_bounds (addSlot_isAdd j) (A.aux j)
  exact ⟨h1, h2, h3, h4⟩

/-- A variable guard lies left of every slot by `H`. -/
theorem Assign.var_left (k : Fin n) (c : ℕ) :
    (A.γ (.inl k)).1 + (paramH n Φ : ℝ) ≤ (slotG n Φ c : ℝ) := by
  rw [(A.var k).1]
  have := s2_var_slot (Φ := Φ) (c := c) k.isLt
  push_cast at this ⊢
  exact_mod_cast this

/-- Aux guards of other slots are far away. -/
theorem Assign.aux_far (j : Fin (addSlotList Φ).length) {c : ℕ} (hc : addSlot Φ j ≠ c) :
    (A.γ (.inr (.inr j))).1 + 1000 ≤ (slotG n Φ c : ℝ) ∨
      (slotG n Φ c : ℝ) + 1000 ≤ (A.γ (.inr (.inr j))).1 := by
  have h := A.aux_pos j
  rcases Nat.lt_or_gt_of_ne hc with hlt | hgt
  · left; have := slot_lt_real (n := n) (Φ := Φ) hlt; linarith
  · right; have := slot_lt_real (n := n) (Φ := Φ) hgt; linarith

/-! ### `invGe` -/

/-- The `invGe` pocket lies in `G + 43 ≤ x ≤ G + 97`. -/
theorem igPocket_x {Gr : ℝ} {p : Point} (hp : p ∈ piece (igPocket Gr)) :
    Gr + 43 ≤ p.1 ∧ p.1 ≤ Gr + 97 := by
  obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 hp
  simp only [det, igI, igQ, igP, igJ] at h0 h1 h2 h3
  constructor <;> nlinarith

/-- **`invGe` (L6.3, L6.4).** The input values of an `invGe` slot satisfy `1 ≤ w_x w_y`. -/
theorem invGe_rel (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {c : ℕ}
    (hc : c < paramC Φ) {jx jy : Fin (inputs n Φ).length}
    (hjx : (inputs n Φ)[jx].b = (slotG n Φ c : ℚ) + 40)
    (hjy : (inputs n Φ)[jy].b = (slotG n Φ c : ℚ) + 100)
    (hkind : cKind (gadAt Φ c) = .invGe) (hnadd : isAdd (gadAt Φ c) = false) :
    1 ≤ A.ival jx * A.ival jy := by
  set Gr : ℝ := (slotG n Φ c : ℝ)
  have hch0 : chainInvGe ∈ tmplFloor (cKind (gadAt Φ c)) := by rw [hkind]; simp [tmplFloor]
  have hinf := (floor_infix (slotFloor_mem (n := n) hc hch0)).map ratPoint
  rw [List.map_map] at hinf
  have e : (ratPoint ∘ RPt.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ)) =
      (fun p => ratPoint (p.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ))) := rfl
  rw [e, chainInvGe_inst, cast_slotG] at hinf
  have hw0 := pedge_of_infix_gen hinf (j := 3) (by simp)
  have hw2 := pedge_of_infix_gen hinf (j := 1) (by simp)
  have hw3 := pedge_of_infix_gen hinf (j := 2) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hw0 hw2 hw3
  have hbd : segment (igJ Gr) (igI Gr) ⊆ (SP n Φ).boundary := by
    have := seg_subset_boundary hinf (j := 2) (by simp)
    simpa using this
  have hR := ig_isRoom (simple n Φ) (interiorLeft n Φ) hw0 hw2 hw3
  have hHr := paramH_ge_r n Φ
  have hbx : ((inputs n Φ)[jx].b : ℝ) = Gr + 40 := by rw [hjx]; push_cast; ring
  have hby : ((inputs n Φ)[jy].b : ℝ) = Gr + 100 := by rw [hjy]; push_cast; ring
  have hcov : ∀ s ∈ segment (igJ Gr) (igI Gr),
      (SP n Φ).Sees (inPt (Gr + 40) (A.ival jx)) s ∨
        (SP n Φ).Sees (inPt (Gr + 100) (A.ival jy)) s := by
    intro s hs
    obtain ⟨X, hX⟩ := A.cover hG (hbd hs)
    rcases X with k | j' | j'
    · exfalso
      have hpv := ig_viewer_mem_PV hR ig_nook_subset_pocket hs
        (not_mem_igPocket (by linarith [(A.var k).2.1])) hX
      obtain ⟨-, h2, -⟩ := hpv
      have := A.var_left k c
      linarith [(A.var k).2.2]
    · obtain ⟨hx, hy1, hy2⟩ := A.inp j'
      have hpv := ig_viewer_mem_PV hR ig_nook_subset_pocket hs (not_mem_igPocket (by linarith)) hX
      have hb := igPV_in_band hpv hy2
      rw [hx] at hb
      by_cases hle : ((inputs n Φ)[j'].b : ℝ) ≤ Gr + 70
      · left
        rw [idx_eq_of_b (j := j') (j' := jx) (by rw [abs_lt]; constructor <;> linarith),
          A.γ_inp, hbx] at hX
        exact hX
      · right
        rw [idx_eq_of_b (j := j') (j' := jy) (by rw [abs_lt]; constructor <;> linarith),
          A.γ_inp, hby] at hX
        exact hX
    · exfalso
      have hne : addSlot Φ j' ≠ c := fun h => by
        have := (addSlot_spec j').2; rw [h, hnadd] at this; exact absurd this (by simp)
      have hfar := A.aux_far j' hne
      have hpos := A.aux_pos j'
      have hnp : A.γ (.inr (.inr j')) ∉ piece (igPocket Gr) := fun h => by
        have := igPocket_x h; rcases hfar with hf | hf <;> linarith
      obtain ⟨h1, h2, h3⟩ := ig_viewer_mem_PV hR ig_nook_subset_pocket hs hnp hX
      rcases hfar with hf | hf <;> linarith
  have hv := A.ival_mem jx
  have hw := A.ival_mem jy
  exact ig_rel_of_walls (simple n Φ) (interiorLeft n Φ) hw0 hw2 hw3 hv.1 hv.2 hw.1 hw.2 hcov

/-! ### `invRevLe` -/

/-- The vertices of the `invRevLe` pocket polygon lie below the floor and right of `ox + 38`. -/
theorem irK_vtx_bounds {H ox : ℚ} (hH : 0 ≤ H) :
    ∀ j < (irK H ox).n, ((irK H ox).vtx j).2 ≤ -1 ∧ (ox : ℝ) + 38 ≤ ((irK H ox).vtx j).1 := by
  have hH' : (0 : ℝ) ≤ H := by exact_mod_cast hH
  intro j hj
  rw [irK_n] at hj
  interval_cases j <;>
    simp [irK, rpts, irPocketChain, Polygon.vtx, RPt.inst, ratPoint] <;> norm_num <;> linarith

/-- Points above the floor are not in the `invRevLe` pocket region. -/
theorem not_mem_irK_above {H ox : ℚ} (hH : 0 ≤ H) {p : Point} (hp : -1 < p.2) :
    p ∉ (irK H ox).filled := by
  refine not_mem_filled_of_right (e₀ := (0, -1)) (e₁ := (-1, -1)) (by simp)
    (fun j hj => ?_) ?_
  · have := (irK_vtx_bounds hH j hj).1
    simp only [det]; linarith
  · simp only [det]; linarith

/-- Points left of `ox + 38` are not in the `invRevLe` pocket region. -/
theorem not_mem_irK_left {H ox : ℚ} (hH : 0 ≤ H) {p : Point} (hp : p.1 < (ox : ℝ) + 38) :
    p ∉ (irK H ox).filled := by
  refine not_mem_filled_of_right (e₀ := ((ox : ℝ) + 38, 0)) (e₁ := ((ox : ℝ) + 38, -1))
    (by simp) (fun j hj => ?_) ?_
  · have := (irK_vtx_bounds hH j hj).2
    simp only [det]; linarith
  · simp only [det]; linarith

/-- **`invRevLe` (L6.3, L6.4).** The input values of an `invRevLe` slot satisfy
`w_x (5/2 − w_y) ≤ 1`. -/
theorem invRevLe_rel (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {c : ℕ}
    (hc : c < paramC Φ) {jx jy : Fin (inputs n Φ).length}
    (hjx : (inputs n Φ)[jx].b = (slotG n Φ c : ℚ) + 60)
    (hjy : (inputs n Φ)[jy].b = (slotG n Φ c : ℚ) + 104)
    (hkind : cKind (gadAt Φ c) = .invRevLe) (hnadd : isAdd (gadAt Φ c) = false) :
    A.ival jx * (5 / 2 - A.ival jy) ≤ 1 := by
  set Gr : ℝ := (slotG n Φ c : ℝ)
  set Hq : ℚ := (paramH n Φ : ℚ)
  set g : ℚ := (slotG n Φ c : ℚ)
  have hHq := paramH_ge_q n Φ
  have hHr := paramH_ge_r n Φ
  have hch0 : chainInvRevLe ∈ tmplFloor (cKind (gadAt Φ c)) := by rw [hkind]; simp [tmplFloor]
  have hinf := (floor_infix (slotFloor_mem (n := n) hc hch0)).map ratPoint
  have hsub : rpts Hq g irPocketChain <:+:
      (chainInvRevLe.map (RPt.inst Hq g)).map ratPoint := by
    rw [chainInvRevLe_eq, List.map_append, List.map_append, rpts_eq]
    exact List.prefix_append _ _ |>.isInfix
  obtain ⟨a, ha, hv⟩ := chain_of_infix_gen (hsub.trans hinf)
  have hlen : (rpts Hq g irPocketChain).length = 7 := by simp [rpts, irPocketChain]
  have hchain : ∀ j ≤ 6, (irK Hq g).vtx j = (SP n Φ).vtx ((a + j) % (SP n Φ).n) := by
    intro j hj
    have hn : (SP n Φ).n = ((poly n Φ).map ratPoint).length := rfl
    rw [hn, Nat.mod_eq_of_lt (by rw [hlen] at ha; omega), hv j (by rw [hlen]; omega)]
    unfold Polygon.vtx irK
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    rfl
  have hR := ir_isRoom (simple n Φ) (interiorLeft n Φ) hHq hchain
  have hNR := ir_nook_subset_irK Hq g
  have hinf' := hinf
  rw [List.map_map] at hinf'
  have e : (ratPoint ∘ RPt.inst Hq g) = (fun p => ratPoint (p.inst Hq g)) := rfl
  rw [e, chainInvRevLe_inst] at hinf'
  have hbd : segment (irJ (g : ℝ)) (irI (g : ℝ)) ⊆ (SP n Φ).boundary := by
    have := seg_subset_boundary hinf' (j := 1) (by simp)
    simpa using this
  have hg : ((g : ℚ) : ℝ) = Gr := cast_slotG n Φ c
  have hbx : ((inputs n Φ)[jx].b : ℝ) = (g : ℝ) + 60 := by rw [hjx]; push_cast; ring
  have hby : ((inputs n Φ)[jy].b : ℝ) = (g : ℝ) + 104 := by rw [hjy]; push_cast; ring
  have hcov : ∀ s ∈ segment (irJ (g : ℝ)) (irI (g : ℝ)),
      (SP n Φ).Sees (inPt ((g : ℝ) + 60) (A.ival jx)) s ∨
        (SP n Φ).Sees (inPt ((g : ℝ) + 104) (A.ival jy)) s := by
    intro s hs
    obtain ⟨X, hX⟩ := A.cover hG (hbd hs)
    rcases X with k | j' | j'
    · exfalso
      have hpv := ir_viewer_mem_PV hR hNR hs
        (not_mem_irK_above (by linarith) (by linarith [(A.var k).2.1])) hX
      have := irPV_bounds hpv
      have := A.var_left k c
      rw [hg] at *
      linarith
    · obtain ⟨hx, hy1, hy2⟩ := A.inp j'
      have hpv := ir_viewer_mem_PV hR hNR hs (not_mem_irK_above (by linarith) (by linarith)) hX
      have hb := irPV_in_band hpv hy1 hy2
      rw [hx] at hb
      by_cases hle : ((inputs n Φ)[j'].b : ℝ) ≤ (g : ℝ) + 82
      · left
        rw [idx_eq_of_b (j := j') (j' := jx) (by rw [abs_lt]; constructor <;> linarith),
          A.γ_inp, hbx] at hX
        exact hX
      · right
        rw [idx_eq_of_b (j := j') (j' := jy) (by rw [abs_lt]; constructor <;> linarith),
          A.γ_inp, hby] at hX
        exact hX
    · exfalso
      have hne : addSlot Φ j' ≠ c := fun h => by
        have := (addSlot_spec j').2; rw [h, hnadd] at this; exact absurd this (by simp)
      have hfar := A.aux_far j' hne
      have hpos := A.aux_pos j'
      have hfar' : (A.γ (.inr (.inr j'))).1 + 1000 ≤ ((g : ℚ) : ℝ) ∨
          ((g : ℚ) : ℝ) + 1000 ≤ (A.γ (.inr (.inr j'))).1 := by rw [hg]; exact hfar
      clear hfar
      have hfar := hfar'
      have hnp : A.γ (.inr (.inr j')) ∉ (irK Hq g).filled := by
        rcases hfar with hf | hf
        · exact not_mem_irK_left (by linarith) (by linarith)
        · exact not_mem_irK hHq (by linarith)
      have hpv := ir_viewer_mem_PV hR hNR hs hnp hX
      obtain ⟨h1, h2, h3⟩ := hpv
      rcases hfar with hf | hf <;> linarith
  have hv := A.ival_mem jx
  have hw := A.ival_mem jy
  exact ir_rel_of_chain (simple n Φ) (interiorLeft n Φ) hHq hchain hv.1 hv.2 hw.1 hw.2 hcov

/-! ### Addition gadgets -/

/-- **Exclusion for the nooks of an addition gadget (L7.6).** A guard satisfying the conclusion of
the viewer lemmas of the gadget files (in the pocket, or right of the nook line and, in the input
band, in the window `[G + L, G + U]` that contains only the designated input) is the designated
input guard or the aux guard of the slot. -/
theorem add_excl {c : ℕ} (hc : c < paramC Φ) {ja : Fin (addSlotList Φ).length}
    (hja : addSlot Φ ja = c) {jr : Fin (inputs n Φ).length} {lx L U lo : ℝ}
    (hjr : ((inputs n Φ)[jr].b : ℝ) = (slotG n Φ c : ℝ) + lx)
    (htmpl : ∀ t ∈ tmplInputs (cKind (gadAt Φ c)), L ≤ (t.lx : ℝ) → (t.lx : ℝ) ≤ U →
      (t.lx : ℝ) = lx)
    (hU : U < 1000) (hlo : 31 ≤ lo) {pk : Set Point}
    (hpk : ∀ p ∈ pk, (slotG n Φ c : ℝ) + 30 ≤ p.1 ∧ p.1 ≤ (slotG n Φ c : ℝ) + 50 ∧ p.2 ≤ -37)
    (X : Idx n Φ)
    (hview : A.γ X ∈ pk ∨ ((slotG n Φ c : ℝ) + lo ≤ (A.γ X).1 ∧
      ((A.γ X).2 ≤ 6 → (A.γ X).1 ≤ (slotG n Φ c : ℝ) + U) ∧
      (0 ≤ (A.γ X).2 → (slotG n Φ c : ℝ) + L ≤ (A.γ X).1))) :
    X = .inr (.inl jr) ∨ X = .inr (.inr ja) := by
  have hHr := paramH_ge_r n Φ
  rcases X with k | j' | j'
  · exfalso
    have hv := A.var k
    have := A.var_left k c
    rcases hview with h | ⟨h1, -, -⟩
    · have := hpk _ h; linarith
    · linarith
  · obtain ⟨hx, hy1, hy2⟩ := A.inp j'
    rcases hview with h | ⟨h1, h2, h3⟩
    · exfalso; have := hpk _ h; linarith
    · left
      have hb2 := h2 hy2
      have hb3 := h3 hy1
      rw [hx] at h1 hb2 hb3
      obtain ⟨t, ht, htb⟩ := input_near_slot hc (input_mem j') (by linarith) (by linarith)
      have := htmpl t ht (by linarith) (by linarith)
      rw [idx_eq_of_b (j := j') (j' := jr) (by rw [htb, hjr, this]; simp)]
  · by_cases hjc : addSlot Φ j' = c
    · right; rw [addSlot_inj (hjc.trans hja.symm)]
    · exfalso
      have hfar := A.aux_far j' hjc
      have hpos := A.aux_pos j'
      rcases hview with h | ⟨h1, h2, -⟩
      · have := hpk _ h; rcases hfar with hf | hf <;> linarith
      · have := h2 (by linarith); rcases hfar with hf | hf <;> linarith

/-- The aux guard of an addition slot lies right of the room's left side. -/
theorem Assign.aux_right {c : ℕ} {ja : Fin (addSlotList Φ).length} (hja : addSlot Φ ja = c) :
    (slotG n Φ c : ℝ) + 50 < (A.γ (.inr (.inr ja))).1 := by
  have := (A.aux_pos ja).1
  rw [hja] at this
  linarith

/-- **`addLe` (L7.4, L7.6).** The input values of an `addLe` slot satisfy `w_x + w_y ≤ w_z`. -/
theorem addLe_rel (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {c : ℕ}
    (hc : c < paramC Φ) {jx jy jz : Fin (inputs n Φ).length}
    (hjx : (inputs n Φ)[jx].b = (slotG n Φ c : ℚ) + 370)
    (hjy : (inputs n Φ)[jy].b = (slotG n Φ c : ℚ) + 210)
    (hjz : (inputs n Φ)[jz].b = (slotG n Φ c : ℚ) + 530)
    (hkind : cKind (gadAt Φ c) = .addLe) (hadd : isAdd (gadAt Φ c) = true) :
    A.ival jx + A.ival jy ≤ A.ival jz := by
  set Gr : ℝ := (slotG n Φ c : ℝ)
  have hch0 : chainAddLe ∈ tmplFloor (cKind (gadAt Φ c)) := by rw [hkind]; simp [tmplFloor]
  have hinf := (floor_infix (slotFloor_mem (n := n) hc hch0)).map ratPoint
  rw [List.map_map] at hinf
  have e : (ratPoint ∘ RPt.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ)) =
      (fun p => ratPoint (p.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ))) := rfl
  rw [e, chainAddLe_inst, cast_slotG] at hinf
  have pe := fun (j : ℕ) (hj : j + 1 < 24) => pedge_of_infix_gen hinf (j := j) (by simpa using hj)
  have hW : AlWalls (SP n Φ) Gr :=
    ⟨by simpa [PEdge] using pe 3 (by norm_num), by simpa [PEdge] using pe 1 (by norm_num),
      by simpa [PEdge] using pe 2 (by norm_num), by simpa [PEdge] using pe 11 (by norm_num),
      by simpa [PEdge] using pe 9 (by norm_num), by simpa [PEdge] using pe 10 (by norm_num),
      by simpa [PEdge] using pe 7 (by norm_num), by simpa [PEdge] using pe 5 (by norm_num),
      by simpa [PEdge] using pe 6 (by norm_num)⟩
  have sb := fun (j : ℕ) (hj : j + 1 < 24) => seg_subset_boundary hinf (j := j) (by simpa using hj)
  obtain ⟨ja, hja⟩ := addSlot_idx hc hadd
  have hq := A.aux_right hja
  have hbx : ((inputs n Φ)[jx].b : ℝ) = Gr + 370 := by rw [hjx]; push_cast; ring
  have hby : ((inputs n Φ)[jy].b : ℝ) = Gr + 210 := by rw [hjy]; push_cast; ring
  have hbz : ((inputs n Φ)[jz].b : ℝ) = Gr + 530 := by rw [hjz]; push_cast; ring
  have htm : ∀ t ∈ tmplInputs (cKind (gadAt Φ c)), (t.lx : ℝ) = 210 ∨ (t.lx : ℝ) = 370 ∨
      (t.lx : ℝ) = 530 := by
    intro t ht
    rw [hkind] at ht
    simp only [tmplInputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> norm_num
  have hpk : ∀ (K : Polygon), (K = alPocketX Gr ∨ K = alPocketY Gr ∨ K = alPocketZ Gr) →
      ∀ p ∈ piece K, Gr + 30 ≤ p.1 ∧ p.1 ≤ Gr + 50 ∧ p.2 ≤ -37 := by
    rintro K hK p hp
    have := al_pocket_bounds (G := Gr) (p := p) (by rcases hK with rfl | rfl | rfl <;> simp [hp])
    exact ⟨this.1, this.2.1, by linarith [this.2.2]⟩
  refine al_rel_of_cover (simple n Φ) (interiorLeft n Φ) hW hq (A.ival_mem jx).1
    (A.ival_mem jx).2 (A.ival_mem jy).1 (A.ival_mem jy).2 (A.ival_mem jz).1 (A.ival_mem jz).2
    ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 2 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hbx (L := 353) (U := 513) (lo := 50)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inl rfl)) X
      (al_viewer_x (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hbx] at hX; exact hX
    · left; exact hX
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 10 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hby (L := 202) (U := 318) (lo := 50)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inr (Or.inl rfl))) X
      (al_viewer_y (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hby] at hX; exact hX
    · left; exact hX
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 6 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hbz (L := 384) (U := 555) (lo := 50)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inr (Or.inr rfl))) X
      (al_viewer_z (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hbz] at hX; exact hX
    · left; exact hX

/-- **`addGe` (L7.4, L7.6).** The input values of an `addGe` slot satisfy `w_z ≤ w_x + w_y`. -/
theorem addGe_rel (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {c : ℕ}
    (hc : c < paramC Φ) {jx jy jz : Fin (inputs n Φ).length}
    (hjx : (inputs n Φ)[jx].b = (slotG n Φ c : ℚ) + 370)
    (hjy : (inputs n Φ)[jy].b = (slotG n Φ c : ℚ) + 210)
    (hjz : (inputs n Φ)[jz].b = (slotG n Φ c : ℚ) + 185 / 2)
    (hkind : cKind (gadAt Φ c) = .addGe) (hadd : isAdd (gadAt Φ c) = true) :
    A.ival jz ≤ A.ival jx + A.ival jy := by
  set Gr : ℝ := (slotG n Φ c : ℝ)
  have hch0 : chainAddGe ∈ tmplFloor (cKind (gadAt Φ c)) := by rw [hkind]; simp [tmplFloor]
  have hinf := (floor_infix (slotFloor_mem (n := n) hc hch0)).map ratPoint
  rw [List.map_map] at hinf
  have e : (ratPoint ∘ RPt.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ)) =
      (fun p => ratPoint (p.inst (paramH n Φ : ℚ) (slotG n Φ c : ℚ))) := rfl
  rw [e, chainAddGe_inst, cast_slotG] at hinf
  have pe := fun (j : ℕ) (hj : j + 1 < 24) => pedge_of_infix_gen hinf (j := j) (by simpa using hj)
  have hW : AgWalls (SP n Φ) Gr :=
    ⟨by simpa [PEdge] using pe 3 (by norm_num), by simpa [PEdge] using pe 1 (by norm_num),
      by simpa [PEdge] using pe 2 (by norm_num), by simpa [PEdge] using pe 11 (by norm_num),
      by simpa [PEdge] using pe 9 (by norm_num), by simpa [PEdge] using pe 10 (by norm_num),
      by simpa [PEdge] using pe 7 (by norm_num), by simpa [PEdge] using pe 5 (by norm_num),
      by simpa [PEdge] using pe 6 (by norm_num)⟩
  have sb := fun (j : ℕ) (hj : j + 1 < 24) => seg_subset_boundary hinf (j := j) (by simpa using hj)
  obtain ⟨ja, hja⟩ := addSlot_idx hc hadd
  have hq := A.aux_right hja
  have hbx : ((inputs n Φ)[jx].b : ℝ) = Gr + 370 := by rw [hjx]; push_cast; ring
  have hby : ((inputs n Φ)[jy].b : ℝ) = Gr + 210 := by rw [hjy]; push_cast; ring
  have hbz : ((inputs n Φ)[jz].b : ℝ) = Gr + 185 / 2 := by rw [hjz]; push_cast; ring
  have htm : ∀ t ∈ tmplInputs (cKind (gadAt Φ c)), (t.lx : ℝ) = 185 / 2 ∨ (t.lx : ℝ) = 210 ∨
      (t.lx : ℝ) = 370 := by
    intro t ht
    rw [hkind] at ht
    simp only [tmplInputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> norm_num
  have hpk : ∀ (K : Polygon), (K = agPocketX Gr ∨ K = agPocketY Gr ∨ K = agPocketZ Gr) →
      ∀ p ∈ piece K, Gr + 30 ≤ p.1 ∧ p.1 ≤ Gr + 50 ∧ p.2 ≤ -37 := by
    rintro K hK p hp
    exact ag_pocket_bounds (G := Gr) (p := p) (by rcases hK with rfl | rfl | rfl <;> simp [hp])
  refine ag_rel_of_cover (simple n Φ) (interiorLeft n Φ) hW hq (A.ival_mem jx).1
    (A.ival_mem jx).2 (A.ival_mem jy).1 (A.ival_mem jy).2 (A.ival_mem jz).1 (A.ival_mem jz).2
    ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 2 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hbx (L := 218) (U := 421) (lo := 50)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inl rfl)) X
      (ag_viewer_x (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hbx] at hX; exact hX
    · left; exact hX
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 10 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hby (L := 101) (U := 221) (lo := 50)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inr (Or.inl rfl))) X
      (ag_viewer_y (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hby] at hX; exact hX
    · left; exact hX
  · have hsb : s ∈ (SP n Φ).boundary := by
      rw [Geometry.segment_comm] at hs; simpa using sb 6 (by norm_num) hs
    obtain ⟨X, hX⟩ := A.cover hG hsb
    rcases add_excl A hc hja hbz (L := 87) (U := 148) (lo := 31)
      (fun t ht h1 h2 => by rcases htm t ht with h | h | h <;> rw [h] at h1 h2 ⊢ <;> norm_num at *)
      (by norm_num) (by norm_num) (hpk _ (Or.inr (Or.inr rfl))) X
      (ag_viewer_z (simple n Φ) (interiorLeft n Φ) hW hs hX) with rfl | rfl
    · right; rw [A.γ_inp, hbz] at hX; exact hX
    · left; exact hX

end Gadgets

end ArtGallery.Stade

end
