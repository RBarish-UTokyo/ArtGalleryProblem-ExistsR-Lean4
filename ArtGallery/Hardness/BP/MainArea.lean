module

public import ArtGallery.Hardness.BP.BayCover

/-!
# Boundary-point variant: the bottom wall with bays (definitions, placement)

The main area of the Section 5 construction (`Sec5/MainArea.lean`) with the pockets of the base
segments replaced by bays (`docs/boundary_point/design.md` §3.1): per slot `σ < 4n` the left mouth corner `a_σ + (-6, 1)` followed by
the bay chain of the segment `s_σ = [a_σ, a_σ + (3/2, 0)]` (with the two `one` spikes for a slot
`σ < n` with `one σ ∈ Φ`).  The right mouth corner `a_σ + (15/2, 1)` is the next slot's left
corner (pitch `27/2`), the last one is `w_r`.

* `pocketBPRel one = m_L :: bayRel one` (relative to `a_σ`), `pocketBP one σ` (absolute),
  `pocketBPClosed one σ` (followed by `m_R`), `bottomWallBP n Φ` and the index `startBP n Φ σ` of
  the first vertex of slot `σ` (`bottomWallBP_getD`, `bottomWallBP_append_getD`).
* `PocketAtBP P one σ a`: the closed pocket chain of slot `σ` is a chain of consecutive vertices
  of `P`; `pocketAtBP_of_bottomWall` (the polygon whose vertex list starts with the bottom wall
  followed by `w_r`).
* `PocketAtBP.bayAt`: the bay of slot `σ` is placed by the frame `slotFrame σ` (origin `a_σ`,
  scale `1`).
* `BoxSepBP P one σ a T`: no other edge of `P` meets the open box
  `(a_σ.x − 6, a_σ.x + 15/2) × (0, T)`; for `T ≥ 1/8` it gives the separation hypothesis of
  the bay (`BoxSepBP.baySep`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Irrational (HP hp hpo qdet mem_hp_cons mem_hp_nil mem_hpo_cons mem_hpo_nil)
open ArtGallery.Sec5 (Q2 slotX slotA slotOne mouthL mouthR mL mR wR slotX_succ)

/-! ### The pockets with bays -/

/-- The pocket of a slot (relative to `a_σ`): the left mouth corner `(-6, 1)` and the bay. -/
def pocketBPRel (one : Bool) : List Q2 := mouthL :: bayRel one

/-- The pocket followed by the right mouth corner `(15/2, 1)` (relative). -/
def pocketBPClosedRel (one : Bool) : List Q2 := pocketBPRel one ++ [mouthR]

/-- The pocket of slot `σ` (absolute coordinates). -/
def pocketBP (one : Bool) (σ : ℕ) : List Q2 := (pocketBPRel one).map (· + slotA σ)

/-- The pocket of slot `σ` followed by its right mouth corner. -/
def pocketBPClosed (one : Bool) (σ : ℕ) : List Q2 := (pocketBPClosedRel one).map (· + slotA σ)

/-- **The bottom wall with bays**: the pockets of slots `0, …, 4n − 1`, left to right. -/
def bottomWallBP (n : ℕ) (Φ : List ETRINV.Constraint) : List Q2 :=
  (List.range (4 * n)).flatMap fun σ => pocketBP (slotOne n Φ σ) σ

/-- The index of the first vertex (`m_L`) of slot `σ` in the bottom wall. -/
def startBP (n : ℕ) (Φ : List ETRINV.Constraint) (σ : ℕ) : ℕ :=
  ((List.range σ).map fun s => (pocketBPRel (slotOne n Φ s)).length).sum

/-- The frame of the bay of slot `σ`: origin `a_σ = (27σ/2, 0)`, scale `1`. -/
def slotFrame (σ : ℕ) : Frame := ⟨(slotX σ : ℝ), 0, 1⟩

theorem length_pocketBPRel (one : Bool) : (pocketBPRel one).length = (bayRel one).length + 1 := by
  simp [pocketBPRel]

theorem length_pocketBPClosedRel (one : Bool) :
    (pocketBPClosedRel one).length = (bayRel one).length + 2 := by
  simp [pocketBPClosedRel, pocketBPRel]

theorem length_pocketBP (one : Bool) (σ : ℕ) :
    (pocketBP one σ).length = (pocketBPRel one).length := by
  simp [pocketBP]

theorem pocketBPClosed_eq (one : Bool) (σ : ℕ) :
    pocketBPClosed one σ = pocketBP one σ ++ [mR σ] := by
  simp [pocketBPClosed, pocketBP, pocketBPClosedRel, mR]

theorem pocketBP_getD_zero (one : Bool) (σ : ℕ) : (pocketBP one σ).getD 0 0 = mL σ := by
  simp [pocketBP, pocketBPRel, mL]

/-- Vertices of the closed pocket chain. -/
theorem pocketBPClosed_getD (one : Bool) (σ : ℕ) {j : ℕ}
    (hj : j < (pocketBPClosedRel one).length) :
    (pocketBPClosed one σ).getD j 0 = (pocketBPClosedRel one).getD j 0 + slotA σ := by
  rw [List.getD_eq_getElem _ _ (by simpa [pocketBPClosed] using hj), List.getD_eq_getElem _ _ hj]
  simp [pocketBPClosed]

/-- The bay vertices inside the closed pocket chain. -/
theorem pocketBPClosedRel_getD_succ (one : Bool) {j : ℕ} (hj : j < (bayRel one).length) :
    (pocketBPClosedRel one).getD (j + 1) 0 = (bayRel one).getD j 0 := by
  rw [pocketBPClosedRel, pocketBPRel, List.cons_append, List.getD_cons_succ,
    List.getD_append _ _ _ _ hj]

theorem pocketBPClosedRel_getD_zero (one : Bool) : (pocketBPClosedRel one).getD 0 0 = mouthL := by
  simp [pocketBPClosedRel, pocketBPRel]

theorem pocketBPClosedRel_getD_last (one : Bool) :
    (pocketBPClosedRel one).getD ((bayRel one).length + 1) 0 = mouthR := by
  rw [pocketBPClosedRel, List.getD_append_right _ _ _ _ (by simp [length_pocketBPRel])]
  simp [length_pocketBPRel]

/-- Absolute coordinates in the slot frame. -/
theorem slotFrame_pt (σ : ℕ) (q : Q2) : (slotFrame σ).pt q = ratPoint (q + slotA σ) := by
  simp only [Frame.pt, Frame.abs, slotFrame, ratPoint, slotA, Prod.fst_add, Prod.snd_add,
    add_zero, one_mul, zero_add]
  push_cast; ext <;> simp; ring

theorem slotFrame_rel (σ : ℕ) (p : Point) : (slotFrame σ).rel p = (p.1 - slotX σ, p.2) := by
  simp [Frame.rel, slotFrame]

/-! ### Placement in the bottom wall -/

variable {n : ℕ} {Φ : List ETRINV.Constraint}

theorem length_bottomWallBP : (bottomWallBP n Φ).length = startBP n Φ (4 * n) := by
  unfold bottomWallBP startBP
  rw [Sec5.length_flatMap_range]
  simp [length_pocketBP]

theorem startBP_succ (σ : ℕ) :
    startBP n Φ (σ + 1) = startBP n Φ σ + (pocketBPRel (slotOne n Φ σ)).length := by
  simp [startBP, List.range_succ]

theorem startBP_mono {σ σ' : ℕ} (h : σ ≤ σ') : startBP n Φ σ ≤ startBP n Φ σ' := by
  induction σ' with
  | zero => rw [Nat.le_zero.1 h]
  | succ r ih =>
    rcases Nat.lt_or_ge σ (r + 1) with h' | h'
    · have := ih (by omega); rw [startBP_succ]; omega
    · rw [show σ = r + 1 by omega]

/-- **Placement.** Vertex `j` of pocket `σ` is vertex `startBP σ + j` of the bottom wall. -/
theorem bottomWallBP_getD {σ j : ℕ} (hσ : σ < 4 * n)
    (hj : j < (pocketBPRel (slotOne n Φ σ)).length) :
    (bottomWallBP n Φ).getD (startBP n Φ σ + j) 0 = (pocketBP (slotOne n Φ σ) σ).getD j 0 := by
  have := Sec5.getD_flatMap_range (fun σ => pocketBP (slotOne n Φ σ) σ) (0 : Q2) hσ
    (by rw [length_pocketBP]; exact hj)
  simpa [bottomWallBP, startBP, length_pocketBP] using this

/-- **Placement of the closed pocket chain.** If the bottom wall is followed by a list starting
with `w_r`, the vertices `startBP σ + j` (`j ≤ |pocket σ|`) of the concatenation are the vertices
of `pocketBPClosed σ`. -/
theorem bottomWallBP_append_getD {rest : List Q2} (hrest : rest.getD 0 0 = wR n) {σ j : ℕ}
    (hσ : σ < 4 * n) (hj : j ≤ (pocketBPRel (slotOne n Φ σ)).length) :
    (bottomWallBP n Φ ++ rest).getD (startBP n Φ σ + j) 0 =
      (pocketBPClosed (slotOne n Φ σ) σ).getD j 0 := by
  have hs1 := startBP_succ (n := n) (Φ := Φ) σ
  have hmono := startBP_mono (n := n) (Φ := Φ) (show σ + 1 ≤ 4 * n by omega)
  rw [pocketBPClosed_eq]
  rcases Nat.lt_or_ge j (pocketBPRel (slotOne n Φ σ)).length with hj' | hj'
  · rw [List.getD_append _ _ _ _ (by rw [length_bottomWallBP]; omega), bottomWallBP_getD hσ hj',
      List.getD_append _ _ _ _ (by rw [length_pocketBP]; exact hj')]
  · have hjeq : j = (pocketBPRel (slotOne n Φ σ)).length := le_antisymm hj hj'
    subst hjeq
    rw [List.getD_append_right (pocketBP (slotOne n Φ σ) σ) [mR σ] 0 _ (by rw [length_pocketBP]),
      length_pocketBP, Nat.sub_self, List.getD_cons_zero, ← hs1]
    rcases Nat.lt_or_ge (σ + 1) (4 * n) with hσ' | hσ'
    · have hs2 := startBP_succ (n := n) (Φ := Φ) (σ + 1)
      have hmono2 := startBP_mono (n := n) (Φ := Φ) (show σ + 1 + 1 ≤ 4 * n by omega)
      have hpos : 0 < (pocketBPRel (slotOne n Φ (σ + 1))).length := by
        rw [length_pocketBPRel]; omega
      have h0 := bottomWallBP_getD (n := n) (Φ := Φ) hσ' hpos
      rw [Nat.add_zero, pocketBP_getD_zero, Sec5.mL_succ] at h0
      rw [List.getD_append _ _ _ _ (by rw [length_bottomWallBP]; omega), h0]
    · have hσl : σ = 4 * n - 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [length_bottomWallBP, show σ + 1 = 4 * n by omega]),
        length_bottomWallBP, show σ + 1 = 4 * n by omega, Nat.sub_self, hrest, hσl,
        Sec5.mR_last (by omega)]

/-! ### The pocket inside a polygon -/

/-- The closed pocket chain of slot `σ` is the chain of consecutive vertices `P.vtx (a + j)`,
`j ≤ |bay| + 1`, of `P` (indices mod `P.n`). -/
def PocketAtBP (P : Polygon) (one : Bool) (σ a : ℕ) : Prop :=
  ∀ j ≤ (bayRel one).length + 1, P.vtx ((a + j) % P.n) = ratPoint ((pocketBPClosed one σ).getD j 0)

/-- **The pockets of the bottom wall are chains of the polygon.** -/
theorem pocketAtBP_of_bottomWall {rest : List Q2} (hrest : rest.getD 0 0 = wR n) {σ : ℕ}
    (hσ : σ < 4 * n) :
    PocketAtBP ⟨(bottomWallBP n Φ ++ rest).map ratPoint⟩ (slotOne n Φ σ) σ (startBP n Φ σ) := by
  intro j hj
  have hne : rest ≠ [] := by
    rintro rfl
    have := congrArg Prod.snd hrest
    simp [wR] at this
  have hlen : startBP n Φ σ + j < (bottomWallBP n Φ ++ rest).length := by
    have h1 := startBP_succ (n := n) (Φ := Φ) σ
    have h2 := startBP_mono (n := n) (Φ := Φ) (show σ + 1 ≤ 4 * n by omega)
    have h3 := length_bottomWallBP (n := n) (Φ := Φ)
    have h4 : 0 < rest.length := List.length_pos_iff.2 hne
    have h5 := length_pocketBPRel (slotOne n Φ σ)
    rw [List.length_append]; omega
  have hn : (Polygon.mk ((bottomWallBP n Φ ++ rest).map ratPoint)).n =
      (bottomWallBP n Φ ++ rest).length := by simp [Polygon.n]
  rw [Irrational.vtx_map_ratPoint, hn, Nat.mod_eq_of_lt hlen,
    bottomWallBP_append_getD hrest hσ (by rw [length_pocketBPRel]; exact hj)]

section PocketAt

variable {P : Polygon} {one : Bool} {σ a : ℕ}

theorem PocketAtBP.vtx (hK : PocketAtBP P one σ a) {j : ℕ} (hj : j ≤ (bayRel one).length + 1) :
    P.vtx ((a + j) % P.n) = ratPoint ((pocketBPClosedRel one).getD j 0 + slotA σ) := by
  rw [hK j hj, pocketBPClosed_getD one σ (by rw [length_pocketBPClosedRel]; omega)]

/-- **The bay of slot `σ`** is placed by the slot frame. -/
theorem PocketAtBP.bayAt (hK : PocketAtBP P one σ a) : BayAt P one (slotFrame σ) (a + 1) := by
  refine ⟨by simp [slotFrame], fun j hj => ?_⟩
  rw [show a + 1 + j = a + (j + 1) by omega, hK.vtx (by omega),
    pocketBPClosedRel_getD_succ one hj, slotFrame_pt]

/-- Chain edge `j` of the closed pocket chain. -/
theorem PocketAtBP.edge_eq (hK : PocketAtBP P one σ a) {j : ℕ} (hj : j ≤ (bayRel one).length) :
    P.edge ((a + j) % P.n) = ArtGallery.segment
      (ratPoint ((pocketBPClosedRel one).getD j 0 + slotA σ))
      (ratPoint ((pocketBPClosedRel one).getD (j + 1) 0 + slotA σ)) := by
  rw [Polygon.edge, chain_succ, hK.vtx (by omega), hK.vtx (by omega)]

end PocketAt

/-! ### Box separation -/

/-- The open box `(a_σ.x − 6, a_σ.x + 15/2) × (0, T)` above the pocket of slot `σ`. -/
def openBoxBP (σ : ℕ) (T : ℝ) : Set Point :=
  {p | (slotX σ : ℝ) - 6 < p.1 ∧ p.1 < slotX σ + 15/2 ∧ 0 < p.2 ∧ p.2 < T}

/-- **Box separation**: no edge of `P` other than the edges of the closed pocket chain meets the
open box `(a_σ.x − 6, a_σ.x + 15/2) × (0, T)`. -/
def BoxSepBP (P : Polygon) (one : Bool) (σ a : ℕ) (T : ℝ) : Prop :=
  ∀ i < P.n, (∀ j ≤ (bayRel one).length, (a + j) % P.n ≠ i) → ∀ p ∈ P.edge i, p ∉ openBoxBP σ T

section Sep

variable {P : Polygon} {one : Bool} {σ a : ℕ} {T : ℝ}

theorem BoxSepBP.mono {T' : ℝ} (h : BoxSepBP P one σ a T) (hT : T' ≤ T) : BoxSepBP P one σ a T' :=
  fun i hi hch p hp hpb => h i hi hch p hp ⟨hpb.1, hpb.2.1, hpb.2.2.1, by linarith [hpb.2.2.2]⟩

/-- **The bay of slot `σ` is separated** (for `T ≥ 1/8`): the two mouth edges `m_L → LS` and
`RS → m_R` stay outside the bay box, all other edges outside the open box of the slot. -/
theorem BoxSepBP.baySep (hsep : BoxSepBP P one σ a T) (hK : PocketAtBP P one σ a)
    (hP : P.Simple) (hT : 1/8 ≤ T) : BaySep P one (slotFrame σ) (a + 1) := by
  have hn : 0 < P.n := by have := hP.1; omega
  intro i hi hch p hp hbox
  rw [slotFrame_rel] at hbox
  obtain ⟨b1, b2, b3, b4⟩ := hbox
  simp only at b1 b2 b3 b4
  by_cases h0 : (a + 0) % P.n = i
  · -- the edge `m_L → LS`
    subst h0
    rw [hK.edge_eq (by omega)] at hp
    have e0 : (pocketBPClosedRel one).getD 0 0 = (-6, 1) := pocketBPClosedRel_getD_zero one
    have e1 : (pocketBPClosedRel one).getD 1 0 = (-1, 1/8) := by
      rw [pocketBPClosedRel_getD_succ one (by cases one <;> decide)]; cases one <;> rfl
    rw [e0, e1] at hp
    have := Irrational.seg_fst_le hp
    simp only [ratPoint, slotA, Prod.fst_add] at this
    push_cast at this
    have : p.1 ≤ slotX σ - 1 :=
      this.trans (max_le (by norm_num; linarith) (by norm_num))
    linarith
  by_cases hl : (a + (bayRel one).length) % P.n = i
  · -- the edge `RS → m_R`
    subst hl
    rw [hK.edge_eq le_rfl] at hp
    have e0 : (pocketBPClosedRel one).getD (bayRel one).length 0 = (5/2, 1/8) := by
      rw [show (bayRel one).length = ((bayRel one).length - 1) + 1 by cases one <;> decide,
        pocketBPClosedRel_getD_succ one (by cases one <;> decide)]
      cases one <;> rfl
    have e1 := pocketBPClosedRel_getD_last one
    rw [e0, e1] at hp
    have := Irrational.seg_fst_ge hp
    simp only [ratPoint, slotA, Prod.fst_add, mouthR] at this
    push_cast at this
    have : slotX σ + 5/2 ≤ p.1 := by
      refine le_trans (le_min ?_ ?_) this <;> norm_num <;> linarith
    linarith
  · refine hsep i hi (fun j hj h => ?_) p hp ⟨by linarith, by linarith, b3, by linarith⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h0 h
    rcases Nat.lt_or_ge j (bayRel one).length with hj' | hj'
    · exact hch (j - 1) (by omega) (by rw [show a + 1 + (j - 1) = a + j by omega]; exact h)
    · exact hl (by rw [show (bayRel one).length = j by omega]; exact h)

end Sep

end ArtGallery.BP

end
