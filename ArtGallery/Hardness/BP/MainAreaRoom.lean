module

public import ArtGallery.Hardness.BP.MainArea

/-!
# Boundary-point variant: the room of a base bay and its coverage

The room of slot `σ` is the polygon `pocketPolyBP one σ` whose vertices are the closed pocket
chain `pocketBPClosed one σ` (left mouth corner, bay, right mouth corner); its last edge is the
door `m_R → m_L` on `y = 1`.  It is the translate by `a_σ` of the fixed polygon `K0BP one`.

* `K0BP` is simple (kernel-checked) and counter-clockwise; `pocketBP_isRoom`: the region of
  `pocketPolyBP one σ` is a room of every polygon containing the closed pocket chain.
* **Pieces** (relative coordinates): the mouth `pcMth = conv{m_L, LS, LT, RT, RS, m_R}`, the
  closed column `colC = [-1/2, 2] × [0, 1/8]` and the spikes `spW1`, `spW2` (`spO1`, `spO2`);
  their union is `UBP one`.  `filled_K0BP_subset`: the region of `K0BP` lies in `UBP`.  The
  horizontal sections of `UBP` are not intervals (between a spike and its wall); every point
  outside `UBP` has a ray avoiding `UBP` (`ray_UBP`): vertical, horizontal, or of slope `±1/16`
  next to the spikes.
* **Coverage** (for `P` containing the closed pocket chain with no other edge meeting the open
  box `(a_σ.x − 6, a_σ.x + 15/2) × (0, T)`, `T ≥ 1`): the mouth with walls up to height `T`
  (`mouthCol σ T`) lies in the region (`mouthCol_subset_filled`), every point of the floor
  segment sees it through the top of the bay column (`sees_mouthCol`), hence
  **the guard of slot `σ` sees the whole room** (`sees_pocketRoomBP`) and its column
  `[a_σ.x − 6, a_σ.x + 15/2] × [1, T]` of the main hexagon (`sees_columnBP`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set Polygon Filter Topology
open ArtGallery.Irrational (HP hp hpo qdet unionHP simpleCheck simple_of_simpleCheck
  edgesInPieces boundary_subset_of_edgesInPieces mem_hp_cons mem_hp_nil mem_hpo_cons mem_hpo_nil)
open ArtGallery.Geometry (lerp)
open ArtGallery.Sec5 (Q2 slotX slotA mouthL mouthR mL mR slotShift)

/-! ### The fixed room polygon -/

/-- The room polygon in relative coordinates (slot `0`). -/
def K0BP (one : Bool) : Polygon := ⟨(pocketBPClosedRel one).map ratPoint⟩

/-- The room of slot `σ`: the polygon with vertices `pocketBPClosed one σ`. -/
def pocketPolyBP (one : Bool) (σ : ℕ) : Polygon := ⟨(pocketBPClosed one σ).map ratPoint⟩

theorem simpleCheck_K0BP_false : simpleCheck (pocketBPClosedRel false) = true := by decide +kernel

theorem simpleCheck_K0BP_true : simpleCheck (pocketBPClosedRel true) = true := by decide +kernel

/-- The fixed room polygon is simple. -/
theorem simple_K0BP (one : Bool) : (K0BP one).Simple := by
  cases one
  · exact simple_of_simpleCheck simpleCheck_K0BP_false
  · exact simple_of_simpleCheck simpleCheck_K0BP_true

/-- The room of slot `σ` is the translate of `K0BP`. -/
theorem pocketPolyBP_eq_mapPoly (one : Bool) (σ : ℕ) :
    pocketPolyBP one σ = Hardening.Invariance.mapPoly (slotShift σ) (K0BP one) := by
  simp only [pocketPolyBP, K0BP, Hardening.Invariance.mapPoly, pocketBPClosed, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact Sec5.ratPoint_add_slotA q σ

/-- **The room is a simple polygon.** -/
theorem simple_pocketPolyBP (one : Bool) (σ : ℕ) : (pocketPolyBP one σ).Simple := by
  rw [pocketPolyBP_eq_mapPoly]
  exact Hardening.Invariance.simple_mapPoly _ _ (simple_K0BP one)

theorem n_pocketPolyBP (one : Bool) (σ : ℕ) :
    (pocketPolyBP one σ).n = (bayRel one).length + 2 := by
  simp [pocketPolyBP, Polygon.n, pocketBPClosed, length_pocketBPClosedRel]

theorem vtx_pocketPolyBP (one : Bool) (σ j : ℕ) :
    (pocketPolyBP one σ).vtx j = ratPoint ((pocketBPClosed one σ).getD j 0) :=
  Irrational.vtx_map_ratPoint _ j

/-- All room vertices lie weakly below the door line `y = 1`. -/
theorem pocketBPClosedRel_snd_le (one : Bool) :
    ∀ j < (pocketBPClosedRel one).length, ((pocketBPClosedRel one).getD j 0).2 ≤ 1 := by
  cases one <;> decide +kernel

theorem pocketBPClosed_getD_last (one : Bool) (σ : ℕ) :
    (pocketBPClosed one σ).getD ((bayRel one).length + 1) 0 = mR σ := by
  rw [pocketBPClosed_getD one σ (by rw [length_pocketBPClosedRel]; omega),
    pocketBPClosedRel_getD_last]; rfl

theorem pocketBPClosed_getD_zero (one : Bool) (σ : ℕ) :
    (pocketBPClosed one σ).getD 0 0 = mL σ := by
  rw [pocketBPClosed_getD one σ (by rw [length_pocketBPClosedRel]; omega),
    pocketBPClosedRel_getD_zero]; rfl

/-- **The room is counter-clockwise** (the door `m_R → m_L` is a supporting edge). -/
theorem interiorLeft_pocketPolyBP (one : Bool) (σ : ℕ) : (pocketPolyBP one σ).InteriorLeft := by
  have hn := n_pocketPolyBP one σ
  refine Polygon.interiorLeft_of_supporting_edge (simple_pocketPolyBP one σ)
    (i := (bayRel one).length + 1) (by omega) fun j hj => ?_
  rw [hn, show (bayRel one).length + 1 + 1 = (bayRel one).length + 2 by omega, Nat.mod_self,
    vtx_pocketPolyBP, vtx_pocketPolyBP, vtx_pocketPolyBP, pocketBPClosed_getD_last,
    pocketBPClosed_getD_zero]
  have hlen : j < (pocketBPClosedRel one).length := by rw [length_pocketBPClosedRel]; omega
  have hy := pocketBPClosedRel_snd_le one j hlen
  have ej : ((pocketBPClosed one σ).getD j 0).2 = ((pocketBPClosedRel one).getD j 0).2 := by
    rw [pocketBPClosed_getD one σ hlen]; simp [slotA]
  simp only [det, ratPoint, mR, mL, mouthR, mouthL, slotA, Prod.fst_add, Prod.snd_add]
  have : ((((pocketBPClosed one σ).getD j 0).2 : ℚ) : ℝ) ≤ 1 := by rw [ej]; exact_mod_cast hy
  push_cast
  nlinarith

/-- **The room of slot `σ` is a room** of `P`; its door is the mouth `m_R m_L` on `y = 1`. -/
theorem pocketBP_isRoom {P : Polygon} {one : Bool} {σ a : ℕ} (hP : P.Simple)
    (hL : P.InteriorLeft) (hK : PocketAtBP P one σ a) :
    P.IsRoom (pocketPolyBP one σ).filled
      (ArtGallery.segment (ratPoint (mR σ)) (ratPoint (mL σ))) := by
  have h := isRoom_of_chain hP hL (simple_pocketPolyBP one σ) (interiorLeft_pocketPolyBP one σ)
    (m := (bayRel one).length + 1) (n_pocketPolyBP one σ)
    (fun j hj => by rw [vtx_pocketPolyBP, hK j hj])
  rwa [vtx_pocketPolyBP, vtx_pocketPolyBP, pocketBPClosed_getD_last, pocketBPClosed_getD_zero] at h

/-! ### Pieces and the region of the fixed room -/

/-- The mouth `conv{m_L, LS, LT, RT, RS, m_R}` (relative coordinates). -/
def pcMth : List HP := [(7, 40, 2), (1, 8, 0), (0, 16, -1), (-2, 16, 3), (-14, 80, 25), (0, -1, 1)]

/-- The pieces of the room. -/
def piecesBP (one : Bool) : List (List HP) :=
  [pcMth, colC, spW1, spW2] ++ (if one then [spO1, spO2] else [])

/-- The union of the pieces (relative coordinates). -/
def UBP (one : Bool) : Set Point := unionHP (piecesBP one)

theorem edgesInPieces_K0BP_false :
    edgesInPieces (pocketBPClosedRel false) (piecesBP false) = true := by decide +kernel

theorem edgesInPieces_K0BP_true :
    edgesInPieces (pocketBPClosedRel true) (piecesBP true) = true := by decide +kernel

/-- The boundary of the fixed room lies in `UBP`. -/
theorem boundary_K0BP_subset (one : Bool) : (K0BP one).boundary ⊆ UBP one := by
  cases one
  · exact boundary_subset_of_edgesInPieces edgesInPieces_K0BP_false
  · exact boundary_subset_of_edgesInPieces edgesInPieces_K0BP_true

theorem mem_UBP {one : Bool} {p : Point} : p ∈ UBP one ↔
    p ∈ hp pcMth ∨ p ∈ hp colC ∨ p ∈ hp spW1 ∨ p ∈ hp spW2 ∨
      (one = true ∧ (p ∈ hp spO1 ∨ p ∈ hp spO2)) := by
  cases one <;> simp [UBP, unionHP, piecesBP]

/-- Unfold membership in a room piece. -/
macro "rpc" " at " h:ident : tactic =>
  `(tactic| (simp only [pcMth, colC, spW1, spW2, spO1, spO2, mem_hp_cons, mem_hp_nil,
                mem_hpo_cons, mem_hpo_nil, and_true, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
                Prod.smul_snd, smul_eq_mul] at $h:ident
             norm_num at $h:ident))

/-- **Rays avoiding the pieces.**  From every point outside `UBP` some ray avoids `UBP`. -/
theorem ray_UBP (one : Bool) {q : Point} (hq : q ∉ UBP one) :
    ∃ d : Point, d ≠ 0 ∧ ∀ s : ℝ, 0 ≤ s → q + s • d ∉ UBP one := by
  obtain ⟨x, y⟩ := q
  -- the pieces at `q`
  have nM : (x, y) ∉ hp pcMth := fun h => hq (mem_UBP.2 (Or.inl h))
  have nC : (x, y) ∉ hp colC := fun h => hq (mem_UBP.2 (Or.inr (Or.inl h)))
  have nW1 : (x, y) ∉ hp spW1 := fun h => hq (mem_UBP.2 (Or.inr (Or.inr (Or.inl h))))
  have nW2 : (x, y) ∉ hp spW2 := fun h => hq (mem_UBP.2 (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have nO : one = true → (x, y) ∉ hp spO1 ∧ (x, y) ∉ hp spO2 := fun h1 =>
    ⟨fun h => hq (mem_UBP.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, Or.inl h⟩))))),
      fun h => hq (mem_UBP.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, Or.inr h⟩)))))⟩
  simp only [pcMth, colC, mem_hp_cons, mem_hp_nil, and_true] at nM nC
  simp only [spW1, spW2, spO1, spO2, mem_hp_cons, mem_hp_nil, and_true] at nW1 nW2 nO
  push_cast at nM nC nW1 nW2 nO
  -- a ray works if every piece fails along it
  have key : ∀ d : Point, d ≠ 0 → (∀ s : ℝ, 0 ≤ s → (x + s * d.1, y + s * d.2) ∉ hp pcMth ∧
      (x + s * d.1, y + s * d.2) ∉ hp colC ∧ (x + s * d.1, y + s * d.2) ∉ hp spW1 ∧
      (x + s * d.1, y + s * d.2) ∉ hp spW2 ∧ (one = true →
        (x + s * d.1, y + s * d.2) ∉ hp spO1 ∧ (x + s * d.1, y + s * d.2) ∉ hp spO2)) →
      ∃ d : Point, d ≠ 0 ∧ ∀ s : ℝ, 0 ≤ s → (x, y) + s • d ∉ UBP one := by
    intro d hd h
    refine ⟨d, hd, fun s hs hm => ?_⟩
    have e : (x, y) + s • d = (x + s * d.1, y + s * d.2) := by ext <;> simp
    rw [e, mem_UBP] at hm
    obtain ⟨a1, a2, a3, a4, a5⟩ := h s hs
    rcases hm with hm | hm | hm | hm | ⟨h1, hm | hm⟩
    exacts [a1 hm, a2 hm, a3 hm, a4 hm, (a5 h1).1 hm, (a5 h1).2 hm]
  -- the generic failure of a piece along a ray
  simp only [pcMth, colC, spW1, spW2, spO1, spO2, mem_hp_cons, mem_hp_nil, and_true] at key
  push_cast at key
  rcases lt_or_ge y 0 with hy0 | hy0
  · -- below the floor line: downwards
    refine key (0, -1) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
      intro h <;> simp only at h <;> linarith
  rcases lt_or_ge 1 y with hy1 | hy1
  · -- above the door line: upwards
    refine key (0, 1) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
      intro h <;> simp only at h <;> linarith
  rcases le_or_gt (1/16) y with hy2 | hy2
  · -- the mouth: horizontal rays
    have hM : 7 * x + 40 * y + 2 < 0 ∨ x + 8 * y < 0 ∨ -2 * x + 16 * y + 3 < 0 ∨
        -14 * x + 80 * y + 25 < 0 := by
      by_contra hc
      push Not at hc
      exact nM ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    rcases hM with hM | hM | hM | hM
    · refine key (-1, 0) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
    · refine key (-1, 0) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
    · refine key (1, 0) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
    · refine key (1, 0) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
  rcases lt_or_ge x (-1/2) with hx | hx
  · -- left of the bay column
    rcases lt_or_ge (4 * x + 128 * y + 1) 0 with hc | hc
    · refine key (0, -1) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
    · have h1 : -2 * x - 256 * y + 3 < 0 := by
        by_contra h; push Not at h; exact nW1 ⟨by linarith, hc, by linarith⟩
      refine key (-1, 1/16) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun ho => ⟨?_, ?_⟩⟩
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · have h2 : -6 * x - 128 * y + 3 < 0 ∨ 20 * x + 128 * y + 5 < 0 := by
          by_contra h; push Not at h; exact (nO ho).1 ⟨by linarith, by linarith, by linarith⟩
        intro h; simp only at h
        rcases h2 with h2 | h2 <;> linarith
      · intro h; simp only at h; linarith
  rcases le_or_gt x 2 with hx2 | hx2
  · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ nC
  · -- right of the bay column
    rcases lt_or_ge (-4 * x + 128 * y + 7) 0 with hc | hc
    · refine key (0, -1) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        intro h <;> simp only at h <;> linarith
    · have h1 : 2 * x - 256 * y < 0 := by
        by_contra h; push Not at h; exact nW2 ⟨by linarith, hc, by linarith⟩
      refine key (1, 1/16) (by simp) fun s hs => ⟨?_, ?_, ?_, ?_, fun ho => ⟨?_, ?_⟩⟩
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · intro h; simp only at h; linarith
      · have h2 : 2 * x - 64 * y - 1 < 0 ∨ -20 * x + 128 * y + 35 < 0 := by
          by_contra h; push Not at h; exact (nO ho).2 ⟨by linarith, by linarith, by linarith⟩
        intro h; simp only at h
        rcases h2 with h2 | h2 <;> linarith

/-- **The region of the fixed room lies in `UBP`.** -/
theorem filled_K0BP_subset (one : Bool) : (K0BP one).filled ⊆ UBP one := by
  intro q hq
  by_contra hqU
  obtain ⟨d, hd, hray⟩ := ray_UBP one hqU
  have hb : q ∉ (K0BP one).boundary := fun h => hqU (boundary_K0BP_subset one h)
  have hunb : ¬ IsBoundedSet (connectedComponentIn (K0BP one).boundaryᶜ q) := by
    refine Jordan.not_isBoundedSet_connectedComponentIn_of_ray (K0BP one) hd ?_
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hray s hs (boundary_K0BP_subset one hmem)
  rcases hq with h | h
  · exact hb h
  · exact hunb h

/-- **The region of the room of slot `σ` lies in the translated pieces.** -/
theorem filled_pocketPolyBP_subset (one : Bool) (σ : ℕ) {p : Point}
    (hp : p ∈ (pocketPolyBP one σ).filled) : (slotFrame σ).rel p ∈ UBP one := by
  rw [pocketPolyBP_eq_mapPoly] at hp
  have e : p = slotShift σ ((slotFrame σ).rel p) := by
    rw [Sec5.slotShift_apply, slotFrame_rel]; ext <;> simp
  rw [e] at hp
  exact filled_K0BP_subset one ((Hardening.Invariance.mem_filled_mapPoly_iff _ _).1 hp)

/-- **Bounds of the room**: `[a_σ.x − 6, a_σ.x + 15/2] × [0, 1]`. -/
theorem pocketPolyBP_bounds (one : Bool) (σ : ℕ) {p : Point}
    (hp : p ∈ (pocketPolyBP one σ).filled) :
    (slotX σ : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ (slotX σ : ℝ) + 15/2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  have h := filled_pocketPolyBP_subset one σ hp
  rw [slotFrame_rel, mem_UBP] at h
  rcases h with h | h | h | h | ⟨-, h | h⟩ <;> rpc at h <;>
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Coverage of the room and of the column above it -/

/-- The mouth without its top (relative coordinates). -/
def pcMw : List HP := [(7, 40, 2), (1, 8, 0), (0, 16, -1), (-2, 16, 3), (-14, 80, 25)]

/-- The closed box `[a_σ.x − 6, a_σ.x + 15/2] × [0, T]`. -/
def closedBoxBP (σ : ℕ) (T : ℝ) : Set Point :=
  {p | (slotX σ : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ slotX σ + 15/2 ∧ 0 ≤ p.2 ∧ p.2 ≤ T}

/-- **The mouth of slot `σ` with its walls, up to height `T`.** -/
def mouthCol (σ : ℕ) (T : ℝ) : Set Point := (slotFrame σ).pc pcMw ∩ closedBoxBP σ T

theorem chainAvoids_Mw (one : Bool) : Sec5.chainAvoids (pocketBPClosedRel one) pcMw = true := by
  cases one <;> decide +kernel

theorem convex_openBoxBP (σ : ℕ) (T : ℝ) : Convex ℝ (openBoxBP σ T) := by
  have : openBoxBP σ T = Ioo ((slotX σ : ℝ) - 6) (slotX σ + 15/2) ×ˢ Ioo 0 T := by
    ext p; simp [openBoxBP, and_assoc]
  rw [this]; exact (convex_Ioo _ _).prod (convex_Ioo _ _)

theorem convex_closedBoxBP (σ : ℕ) (T : ℝ) : Convex ℝ (closedBoxBP σ T) := by
  have : closedBoxBP σ T = Icc ((slotX σ : ℝ) - 6) (slotX σ + 15/2) ×ˢ Icc 0 T := by
    ext p; simp only [closedBoxBP, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]; tauto
  rw [this]; exact (convex_Icc _ _).prod (convex_Icc _ _)

theorem convex_mouthCol (σ : ℕ) (T : ℝ) : Convex ℝ (mouthCol σ T) :=
  (Frame.convex_pc pcMw).inter (convex_closedBoxBP σ T)

section Cover

variable {P : Polygon} {one : Bool} {σ a : ℕ} {T : ℝ}

/-- Points of the closed pocket chain edges, in relative coordinates. -/
theorem rel_mem_chain_edge {j : ℕ} {p : Point}
    (hp : p ∈ ArtGallery.segment (ratPoint ((pocketBPClosedRel one).getD j 0 + slotA σ))
      (ratPoint ((pocketBPClosedRel one).getD (j + 1) 0 + slotA σ))) :
    (slotFrame σ).rel p ∈ ArtGallery.segment (ratPoint ((pocketBPClosedRel one).getD j 0))
      (ratPoint ((pocketBPClosedRel one).getD (j + 1) 0)) := by
  rw [← slotFrame_pt, ← slotFrame_pt] at hp
  exact Frame.rel_mem_segment_pt (by simp [slotFrame]) hp

/-- **The mouth with its walls lies in the region** (`T ≥ 1`). -/
theorem mouthCol_subset_filled (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAtBP P one σ a)
    (hsep : BoxSepBP P one σ a T) (hT : 1 ≤ T) : mouthCol σ T ⊆ P.filled := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hB := hK.bayAt
  have hS := hsep.baySep hK hP (by linarith)
  set F := slotFrame σ with hF
  have hs : F.s ≠ 0 := by simp [hF, slotFrame]
  set O := F.pco pcMw ∩ openBoxBP σ T with hO
  -- the open part avoids the boundary
  have hav : ∀ p ∈ O, p ∉ P.boundary := by
    rintro p ⟨hpw, hpb⟩ ⟨i, hi, hpi⟩
    by_cases hc : ∃ j ≤ (bayRel one).length, (a + j) % P.n = i
    · obtain ⟨j, hj, rfl⟩ := hc
      rw [hK.edge_eq hj] at hpi
      exact Sec5.not_mem_hpo_of_chainAvoids (chainAvoids_Mw one)
        (by rw [length_pocketBPClosedRel]; omega) (rel_mem_chain_edge hpi) hpw
    · push Not at hc
      exact hsep i hi (fun j hj h => hc j hj h) p hpi hpb
  -- an interior point
  have hzc : ((3/4 : ℝ), (3/32 : ℝ)) ∈ hpo colO := by
    simp only [colO, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  have hz : F.abs (3/4, 3/32) ∈ O := by
    refine ⟨Frame.mem_pco_of hs
      (by simp only [pcMw, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num), ?_⟩
    simp only [hF, slotFrame, Frame.abs, openBoxBP, Set.mem_ofPred_eq]
    refine ⟨by linarith, by linarith, by norm_num, by linarith⟩
  have hzI := colO_subset_interior hB hP hL hS (Frame.mem_pco_of hs hzc)
  have hOC : O ⊆ P.filled \ P.boundary :=
    Sec5.subset_interior_of_meets hP ((Frame.convex_pco pcMw).inter (convex_openBoxBP σ T)) hav
      hz hzI
  -- the closed part is in the closure of the open part
  have hClO : mouthCol σ T ⊆ closure O := by
    refine Sec5.subset_closure_of_lerp (z := F.abs (3/4, 3/32)) fun p hp t ht0 ht1 => ⟨?_, ?_⟩
    · show F.rel (lerp p _ t) ∈ hpo pcMw
      rw [Frame.rel_lerp]
      intro c hc
      rw [Irrational.HP.val_lerp]
      have h1 := hp.1 c hc; have h2 := hz.1 c hc
      nlinarith [mul_pos ht0 h2, mul_nonneg (sub_nonneg.2 ht1.le) h1]
    · obtain ⟨b1, b2, b3, b4⟩ := hp.2
      obtain ⟨c1, c2, c3, c4⟩ := hz.2
      simp only [openBoxBP, Set.mem_ofPred_eq, lerp]
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  exact hClO.trans ((closure_mono (hOC.trans sdiff_subset)).trans
    (isClosed_filled P).closure_eq.le)

/-- **The floor sees the mouth through the top of the bay column.**  Every point of the floor
segment `[0, 3/2] × {0}` of slot `σ` sees every point of `mouthCol σ T` (`T ≥ 1`). -/
theorem sees_mouthCol (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAtBP P one σ a)
    (hsep : BoxSepBP P one σ a T) (hT : 1 ≤ T) {g : Point} (hg2 : g.2 = 0)
    (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3/2) {q : Point}
    (hq : q ∈ mouthCol σ T) : P.Sees g q := by
  have hB := hK.bayAt
  have hS := hsep.baySep hK hP (by linarith)
  set F := slotFrame σ with hF
  have hrel : ∀ p : Point, F.rel p = (p.1 - slotX σ, p.2) := slotFrame_rel σ
  obtain ⟨hqw, hqb⟩ := hq
  have hqw' := hqw
  change F.rel q ∈ hp pcMw at hqw'
  rw [hrel] at hqw'
  simp only [pcMw, mem_hp_cons, mem_hp_nil, and_true] at hqw'
  push_cast at hqw'
  obtain ⟨c1, c2, c3, c4, c5⟩ := hqw'
  have hqy : 1/16 ≤ q.2 := by linarith
  set t := 1 / (16 * q.2) with ht
  have hq0 : 0 < q.2 := by linarith
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
  have htq : t * (16 * q.2) = 1 := by rw [ht]; field_simp
  set m := lerp g q t with hm
  have hm1 : m.1 = g.1 + t * (q.1 - g.1) := rfl
  have hm2 : m.2 = 1/16 := by
    show g.2 + t * (q.2 - g.2) = 1/16
    rw [hg2]; linear_combination htq / 16
  -- the crossing point lies in `[-1/2, 2]` (relative)
  have hgx := sub_nonneg.2 hg1
  have hgx' : 0 ≤ (slotX σ : ℝ) + 3/2 - g.1 := by linarith
  have hlo : (slotX σ : ℝ) - 1/2 ≤ m.1 := by
    rw [hm1]
    -- `q.1 + 8 q.2 ≥ slotX`, `t (16 q.2) = 1`
    have : 0 ≤ t * ((q.1 - slotX σ) + 8 * q.2) := mul_nonneg ht0.le (by linarith)
    have h2 : 0 ≤ (1 - t) * (g.1 - slotX σ) := mul_nonneg (by linarith) hgx
    nlinarith
  have hhi : m.1 ≤ (slotX σ : ℝ) + 2 := by
    rw [hm1]
    have : 0 ≤ t * (8 * q.2 + 3/2 - (q.1 - slotX σ)) := mul_nonneg ht0.le (by linarith)
    have h2 : 0 ≤ (1 - t) * ((slotX σ : ℝ) + 3/2 - g.1) := mul_nonneg (by linarith) hgx'
    nlinarith
  have hmc : m ∈ F.pc colC := by
    show F.rel m ∈ hp colC
    rw [hrel]; simp only [colC, mem_hp_cons, mem_hp_nil, and_true]; push_cast
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hmM : m ∈ mouthCol σ T := by
    refine ⟨?_, ?_⟩
    · show F.rel m ∈ hp pcMw
      rw [hrel]; simp only [pcMw, mem_hp_cons, mem_hp_nil, and_true]; push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨b1, b2, b3, b4⟩ := hqb
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hgc : g ∈ F.pc colC := by
    show F.rel g ∈ hp colC
    rw [hrel]; simp only [colC, mem_hp_cons, mem_hp_nil, and_true]; push_cast
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  exact sees_via_column hB hP hL hS (convex_mouthCol σ T)
    (mouthCol_subset_filled hP hL hK hsep hT) hgc ⟨hqw, hqb⟩ hmM hmc
    (Geometry.lerp_mem_segment _ _ ht0.le ht1)

/-- **The guard of slot `σ` sees the whole room.**  Any point `g` of the guard segment
`s_σ = [a_σ, a_σ + (3/2, 0)]` (with `one` spikes: the value-`1` point `a_σ + (1/2, 0)`) sees every
point of the room `pocketPolyBP one σ`. -/
theorem sees_pocketRoomBP (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAtBP P one σ a)
    (hsep : BoxSepBP P one σ a 1) {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1)
    (hg1' : g.1 ≤ slotX σ + 3/2) (hone : one = true → g.1 = slotX σ + 1/2) {q : Point}
    (hq : q ∈ (pocketPolyBP one σ).filled) : P.Sees g q := by
  have hB := hK.bayAt
  have hS := hsep.baySep hK hP (by norm_num)
  have hU := filled_pocketPolyBP_subset one σ hq
  have hrel := slotFrame_rel σ
  have hbay : q ∈ bayRegion one (slotFrame σ) → P.Sees g q := fun h =>
    sees_bayRegion hB hP hL hS (by rw [hrel]; exact hg2) (by rw [hrel]; simp only; linarith)
      (by rw [hrel]; simp only; linarith) (fun h1 => by rw [hrel]; simp only; rw [hone h1]; ring) h
  rw [mem_UBP] at hU
  rcases hU with h | h | h | h | ⟨h1, h | h⟩
  · refine sees_mouthCol hP hL hK hsep le_rfl hg2 hg1 hg1' ⟨?_, ?_⟩
    · show (slotFrame σ).rel q ∈ hp pcMw
      rw [hrel] at h ⊢; rpc at h; simp only [pcMw, mem_hp_cons, mem_hp_nil, and_true]
      push_cast
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [hrel] at h; rpc at h
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exact hbay (Or.inl (Or.inl (Or.inl h)))
  · exact hbay (Or.inl (Or.inl (Or.inr h)))
  · exact hbay (Or.inl (Or.inr h))
  · exact hbay (Or.inr ⟨h1, Or.inl h⟩)
  · exact hbay (Or.inr ⟨h1, Or.inr h⟩)

/-- **The guard of slot `σ` sees its column of the main hexagon**: every point of the guard
segment sees every point of `[a_σ.x − 6, a_σ.x + 15/2] × [1, T]` (`T ≥ 1`). -/
theorem sees_columnBP (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAtBP P one σ a)
    (hsep : BoxSepBP P one σ a T) (hT : 1 ≤ T) {g : Point} (hg2 : g.2 = 0)
    (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3/2) {q : Point}
    (hq1 : (slotX σ : ℝ) - 6 ≤ q.1) (hq1' : q.1 ≤ slotX σ + 15/2) (hq2 : 1 ≤ q.2)
    (hq2' : q.2 ≤ T) : P.Sees g q := by
  refine sees_mouthCol hP hL hK hsep hT hg2 hg1 hg1' ⟨?_, ⟨hq1, hq1', by linarith, hq2'⟩⟩
  show (slotFrame σ).rel q ∈ hp pcMw
  rw [slotFrame_rel]; simp only [pcMw, mem_hp_cons, mem_hp_nil, and_true]; push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The guard segment of slot `σ` lies on the boundary** (it is a piece of the bay floor). -/
theorem base_mem_boundary (hP : P.Simple) (hK : PocketAtBP P one σ a) {g : Point}
    (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3/2) :
    g ∈ P.boundary := by
  have hrel := slotFrame_rel σ
  refine hK.bayAt.floor_mem_boundary hP ?_ ?_ ?_ <;> rw [hrel] <;> simp only
  · exact hg2
  · linarith
  · linarith

end Cover

theorem ratPoint_mL_BP (σ : ℕ) : ratPoint (mL σ) = ((slotX σ : ℝ) - 6, 1) := by
  simp only [ratPoint, mL, mouthL, slotA, Prod.fst_add, Prod.snd_add, add_zero]
  push_cast; ext <;> simp; ring

theorem ratPoint_mR_BP (σ : ℕ) : ratPoint (mR σ) = ((slotX σ : ℝ) + 15 / 2, 1) := by
  simp only [ratPoint, mR, mouthR, slotA, Prod.fst_add, Prod.snd_add, add_zero]
  push_cast; ext <;> simp; ring

/-- **Near an open pocket mouth, the half-plane `y ≤ 1` lies in the room.** -/
theorem pocketBP_below (one : Bool) (σ : ℕ) {y : Point} (h1 : y.2 = 1)
    (h2 : (slotX σ : ℝ) - 6 < y.1) (h3 : y.1 < slotX σ + 15 / 2) :
    ∀ᶠ z in 𝓝 y, z.2 ≤ 1 → z ∈ (pocketPolyBP one σ).filled := by
  have hn := n_pocketPolyBP one σ
  have hi : (bayRel one).length + 1 < (pocketPolyBP one σ).n := by omega
  have e1 : (pocketPolyBP one σ).vtx ((bayRel one).length + 1) =
      ((slotX σ : ℝ) + 15 / 2, 1) := by
    rw [vtx_pocketPolyBP, pocketBPClosed_getD_last, ratPoint_mR_BP]
  have e2 : (pocketPolyBP one σ).vtx (((bayRel one).length + 1 + 1) % (pocketPolyBP one σ).n) =
      ((slotX σ : ℝ) - 6, 1) := by
    rw [hn, show (bayRel one).length + 1 + 1 = (bayRel one).length + 2 by omega, Nat.mod_self,
      vtx_pocketPolyBP, pocketBPClosed_getD_zero, ratPoint_mL_BP]
  set t : ℝ := ((slotX σ : ℝ) + 15 / 2 - y.1) / (27 / 2) with ht
  have ht0 : 0 < t := by rw [ht]; apply div_pos <;> linarith
  have ht1 : t < 1 := by rw [ht, div_lt_one (by norm_num)]; linarith
  obtain ⟨r, hr, h⟩ := Polygon.local_halfplane (simple_pocketPolyBP one σ)
    (interiorLeft_pocketPolyBP one σ) hi ht0 ht1
  rw [e1, e2] at h
  have hy : ((slotX σ : ℝ) + 15 / 2, (1 : ℝ)) + t • (((slotX σ : ℝ) - 6, (1 : ℝ)) -
      ((slotX σ : ℝ) + 15 / 2, (1 : ℝ))) = y := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, ht]; field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, h1]; ring
  rw [hy] at h
  refine Metric.eventually_nhds_iff.2 ⟨r, hr, fun z hz hz2 => (h z hz).2 ?_⟩
  simp only [det]; nlinarith

end ArtGallery.BP

end
