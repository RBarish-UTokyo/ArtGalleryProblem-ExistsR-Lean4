module

public import ArtGallery.Hardness.Sec5.MainArea.Witness

/-!
# Section 5: coverage of the pocket room and of its column of the main hexagon

For a simple counter-clockwise polygon `P` containing the closed pocket chain of slot `σ`
(`PocketAt P one σ a`) and no other edge meeting the open box
`(a_σ.x − 6, a_σ.x + 15/2) × (−6, T)` (`BoxSep P one σ a T`):

* every convex piece of the pocket room (`Pocket.lean`), translated to slot `σ`, lies in
  `P.filled` (`hpS_subset_filled_*`): its interior meets no edge of `P` (chain edges by a
  kernel-checked separation certificate `chainAvoids`, other edges by `BoxSep`), and it is
  connected to an interior point of `P` next to the chamber floor `C → D` (`InteriorLeft`)
  through a chain of overlapping open pieces;
* **the guard of slot `σ` sees the whole pocket room** (`sees_pocket_room`): any point of the
  guard segment `s_σ` (without `one` spikes), resp. the value-`1` point `g1` (with spikes), sees
  every point of `pocketPoly one σ`; in particular every witness of the slot;
* **the guard sees its column of the main hexagon** (`sees_column`): for `T ≥ 2`, every point
  `q` with `q.1 ∈ [a_σ.x − 6, a_σ.x + 15/2]` and `q.2 ∈ [1, T]` (the segment passes the door
  inside the mouth `conv{m_L, H', H, K, m_R}`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set Polygon Filter Topology
open ArtGallery.Irrational (HP hp hpo QPt mem_hp_cons mem_hp_nil mem_hpo_cons mem_hpo_nil)
open ArtGallery.Geometry (lerp)

/-! ### Separation certificates for open chains -/

/-- Every edge `v_i v_{i+1}` (`i + 1 < |vs|`) of the open chain `vs` has both endpoints weakly
outside one constraint of the open piece `l`. -/
def chainAvoids (vs : List QPt) (l : List HP) : Bool :=
  (List.range (vs.length - 1)).all fun i => l.any fun c =>
    decide (c.qval (vs.getD i 0) ≤ 0) && decide (c.qval (vs.getD (i + 1) 0) ≤ 0)

theorem not_mem_hpo_of_chainAvoids {vs : List QPt} {l : List HP} (h : chainAvoids vs l = true)
    {i : ℕ} (hi : i + 1 < vs.length) {p : Point}
    (hp : p ∈ ArtGallery.segment (ratPoint (vs.getD i 0)) (ratPoint (vs.getD (i + 1) 0))) :
    p ∉ hpo l := by
  intro hpl
  simp only [chainAvoids, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨c, hc, h1, h2⟩ := h i (by omega)
  obtain ⟨t, h0, h1', rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
  have := hpl c hc
  rw [Irrational.HP.val_lerp, Irrational.HP.val_ratPoint, Irrational.HP.val_ratPoint] at this
  have e1 : ((c.qval (vs.getD i 0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h1
  have e2 : ((c.qval (vs.getD (i + 1) 0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h2
  nlinarith [mul_nonneg (sub_nonneg.2 h1') (neg_nonneg.2 e1), mul_nonneg h0 (neg_nonneg.2 e2)]

/-! ### Pieces translated to slot `σ` -/

/-- The bridge `(0,1) × (−1/2,1/2)` across the base line (relative coordinates). -/
def pcBr : List HP := [(1, 0, 0), (-1, 0, 1), (0, 2, 1), (0, -2, 1)]

/-- The mouth with its top moved to `y = 2` and side walls `x = −6`, `x = 15/2`. -/
def pcM2 : List HP := [(2, 11, 1), (0, 1, 0), (-1, 10, 2), (-38, 200, 85), (0, -1, 2), (1, 0, 6),
  (-2, 0, 15)]

/-- A closed piece translated to slot `σ`. -/
def hpS (σ : ℕ) (l : List HP) : Set Point := {p | rel σ p ∈ hp l}

/-- An open piece translated to slot `σ`. -/
def hpoS (σ : ℕ) (l : List HP) : Set Point := {p | rel σ p ∈ hpo l}

theorem rel_lerp (σ : ℕ) (p q : Point) (t : ℝ) :
    rel σ (lerp p q t) = lerp (rel σ p) (rel σ q) t := by
  ext <;> simp only [rel, lerp]
  ring

theorem convex_hpS (σ : ℕ) (l : List HP) : Convex ℝ (hpS σ l) := by
  intro p hp' q hq s t hs ht hst
  have e : s • p + t • q = lerp p q t := by
    have : s = 1 - t := by linarith
    subst this; ext <;> simp [lerp] <;> ring
  show rel σ (s • p + t • q) ∈ hp l
  have e2 : (1 - t) • rel σ p + t • rel σ q = lerp (rel σ p) (rel σ q) t := by
    ext <;> simp [lerp] <;> ring
  rw [e, rel_lerp, ← e2]
  exact Irrational.convex_hp l hp' hq (by linarith) ht (by ring)

theorem convex_hpoS (σ : ℕ) (l : List HP) : Convex ℝ (hpoS σ l) := by
  intro p hp q hq s t hs ht hst
  have e : s • p + t • q = lerp p q t := by
    have : s = 1 - t := by linarith
    subst this; ext <;> simp [lerp] <;> ring
  show rel σ (s • p + t • q) ∈ hpo l
  have e2 : (1 - t) • rel σ p + t • rel σ q = lerp (rel σ p) (rel σ q) t := by
    ext <;> simp [lerp] <;> ring
  rw [e, rel_lerp, ← e2]
  exact Irrational.convex_hpo l hp hq (by linarith) ht (by ring)

/-- A closed set whose points are approached by the segments towards a point `z` of the open
set `O` lies in the closure of `O`. -/
theorem subset_closure_of_lerp {S O : Set Point} {z : Point}
    (h : ∀ q ∈ S, ∀ t : ℝ, 0 < t → t < 1 → lerp q z t ∈ O) : S ⊆ closure O := by
  intro q hq
  have hcont : Continuous fun t : ℝ => lerp q z t := Geometry.continuous_lerp q z
  have hlim : Tendsto (fun t : ℝ => lerp q z t) (𝓝[>] 0) (𝓝 q) := by
    have := hcont.tendsto 0
    simp only [Geometry.lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact h q hq t ht.1 ht.2

theorem hpS_subset_closure {σ : ℕ} {l : List HP} {z : Point} (hz : z ∈ hpoS σ l) :
    hpS σ l ⊆ closure (hpoS σ l) := by
  refine subset_closure_of_lerp (z := z) fun q hq t ht0 ht1 => ?_
  show rel σ (lerp q z t) ∈ hpo l
  rw [rel_lerp]
  intro c hc
  rw [Irrational.HP.val_lerp]
  have h1 := hq c hc; have h2 := hz c hc
  nlinarith [mul_pos ht0 h2, mul_nonneg (sub_nonneg.2 ht1.le) h1]

/-- A segment between translated vertices, in relative coordinates. -/
theorem rel_mem_segment {σ : ℕ} {A B : Q2} {p : Point}
    (hp : p ∈ ArtGallery.segment (absPt σ A) (absPt σ B)) :
    rel σ p ∈ ArtGallery.segment (ratPoint A) (ratPoint B) := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  refine ⟨t, h0, h1, ?_⟩
  rw [absPt_eq, absPt_eq]
  simp only [rel, ratPoint]
  ext <;> simp only
  ring

/-! ### The polygon around the pocket -/

/-- The open box `(a_σ.x − 6, a_σ.x + 15/2) × (−6, T)` around the pocket of slot `σ`. -/
def openBox (σ : ℕ) (T : ℝ) : Set Point :=
  {p | (slotX σ : ℝ) - 6 < p.1 ∧ p.1 < slotX σ + 15/2 ∧ -6 < p.2 ∧ p.2 < T}

/-- **Box separation**: no edge of `P` other than the pocket chain edges meets the open box
`(a_σ.x − 6, a_σ.x + 15/2) × (−6, T)`. -/
def BoxSep (P : Polygon) (one : Bool) (σ a : ℕ) (T : ℝ) : Prop :=
  ∀ i < P.n, (∀ j < (pocketRel one).length, (a + j) % P.n ≠ i) →
    ∀ p ∈ P.edge i, p ∉ openBox σ T

section Polygon

variable {P : Polygon} {one : Bool} {σ a : ℕ} {T : ℝ}

theorem BoxSep.mono {T' : ℝ} (h : BoxSep P one σ a T) (hT : T' ≤ T) : BoxSep P one σ a T' :=
  fun i hi hch p hp hpb => h i hi hch p hp ⟨hpb.1, hpb.2.1, hpb.2.2.1, by linarith [hpb.2.2.2]⟩

/-- Points of an open set lying in the relative open box and avoiding every chain edge avoid the
boundary of `P`. -/
theorem not_mem_boundary_of_chain (hP : P.Simple) (hK : PocketAt P one σ a)
    (hsep : BoxSep P one σ a T) {p : Point} (hbox : p ∈ openBox σ T)
    (hch : ∀ j < (pocketRel one).length, p ∉ ArtGallery.segment
      (absPt σ ((pocketClosedRel one).getD j 0)) (absPt σ ((pocketClosedRel one).getD (j + 1) 0))) :
    p ∉ P.boundary := by
  have hn : 0 < P.n := by have := hP.1; omega
  rintro ⟨i, hi, hpi⟩
  by_cases hc : ∃ j < (pocketRel one).length, (a + j) % P.n = i
  · obtain ⟨j, hj, rfl⟩ := hc
    have e : P.edge ((a + j) % P.n) = ArtGallery.segment
        (absPt σ ((pocketClosedRel one).getD j 0))
        (absPt σ ((pocketClosedRel one).getD (j + 1) 0)) := by
      rw [Polygon.edge, chain_succ, hK.vtx hj.le, hK.vtx (by omega)]
    rw [e] at hpi
    exact hch j hj hpi
  · push Not at hc
    exact hsep i hi (fun j hj h => hc j hj h) p hpi hbox

/-- An open piece passing the separation certificate and lying in the box avoids the boundary. -/
theorem hpoS_not_mem_boundary (hP : P.Simple) (hK : PocketAt P one σ a)
    (hsep : BoxSep P one σ a T) {l : List HP} (hc : chainAvoids (pocketClosedRel one) l = true)
    (hb : ∀ p ∈ hpo l, -6 < p.1 ∧ p.1 < 15/2 ∧ -6 < p.2 ∧ p.2 < T) :
    ∀ p ∈ hpoS σ l, p ∉ P.boundary := by
  intro p hp
  obtain ⟨b1, b2, b3, b4⟩ := hb _ hp
  refine not_mem_boundary_of_chain hP hK hsep ⟨?_, ?_, b3, b4⟩ fun j hj hpj => ?_
  · simp only [rel] at b1; linarith
  · simp only [rel] at b2; linarith
  · exact not_mem_hpo_of_chainAvoids hc (by rw [length_pocketClosedRel]; omega)
      (rel_mem_segment hpj) hp

/-- Convex open sets avoiding the boundary and meeting the interior lie in the interior. -/
theorem subset_interior_of_meets (hP : P.Simple) {O : Set Point} (hO : Convex ℝ O)
    (hav : ∀ p ∈ O, p ∉ P.boundary) {z : Point} (hz : z ∈ O) (hzC : z ∈ P.filled \ P.boundary) :
    O ⊆ P.filled \ P.boundary := by
  rw [Jordan.filled_sdiff_boundary_eq_component hP hzC]
  exact hO.isPreconnected.subset_connectedComponentIn hz (fun p hp => hav p hp)

/-- An interior point of `P` above the chamber floor `C → D`. -/
theorem exists_chamber_point (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a) :
    ∃ z, z ∈ hpoS σ pcC ∧ z ∈ P.filled \ P.boundary := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hC : P.vtx ((a + 4) % P.n) = absPt σ (-1, -1) := by
    rw [hK.vtx (by rw [length_pocketRel]; split <;> omega)]; cases one <;> rfl
  have hD : P.vtx (((a + 4) % P.n + 1) % P.n) = absPt σ (0, -1) := by
    rw [chain_succ, hK.vtx (by rw [length_pocketRel]; split <;> omega)]; cases one <;> rfl
  obtain ⟨δ₀, hδ₀, hδ⟩ := hL _ (Nat.mod_lt (a + 4) hn) (1/2) (by norm_num) (by norm_num)
  set δ := min (δ₀ / 2) (1/2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1/2 := min_le_right _ _
  obtain ⟨hin, -⟩ := hδ δ hδpos hδlt
  rw [hC, hD] at hin
  have e : absPt σ (-1, -1) + (1 / 2 : ℝ) • (absPt σ (0, -1) - absPt σ (-1, -1)) +
      δ • leftNormal (absPt σ (-1, -1)) (absPt σ (0, -1)) = ((slotX σ : ℝ) - 1/2, -1 + δ) := by
    rw [absPt_eq, absPt_eq]
    ext <;> simp only [leftNormal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring
  rw [e] at hin
  refine ⟨_, ?_, hin⟩
  simp only [hpoS, rel, pcC, mem_hpo_cons, mem_hpo_nil, and_true, Set.mem_ofPred_eq]
  norm_num
  constructor <;> linarith

/-- Unfold membership in a translated piece into linear inequalities. -/
macro "pcS_simp" " at " h:ident : tactic =>
  `(tactic| (simp only [hpS, hpoS, rel, pcM, pcF, pcR, pcC, pcSh, pcQ1, pcQ2, pcBr, pcM2,
                mem_hp_cons, mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true,
                Set.mem_ofPred_eq] at $h:ident
             push_cast at $h:ident))

/-- Reduce membership in a translated piece to linear goals. -/
macro "pcS_goal" : tactic =>
  `(tactic| (simp only [hpS, hpoS, rel, pcM, pcF, pcR, pcC, pcSh, pcQ1, pcQ2, pcBr, pcM2,
                mem_hp_cons, mem_hp_nil, mem_hpo_cons, mem_hpo_nil, and_true,
                Set.mem_ofPred_eq]
             push_cast
             repeat' apply And.intro))

/-- The relative-box bounds of an open piece. -/
macro "pc_box" : tactic =>
  `(tactic| (intro p hp
             simp only [pcM, pcF, pcR, pcC, pcSh, pcQ1, pcQ2, pcBr, pcM2, mem_hpo_cons,
                mem_hpo_nil, and_true] at hp
             push_cast at hp
             refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith))

/-- Membership of an explicit relative point in a translated open piece. -/
theorem mem_hpoS_of {l : List HP} {q : Point} (h : q ∈ hpo l) :
    ((slotX σ : ℝ) + q.1, q.2) ∈ hpoS σ l := by
  simpa [hpoS, rel] using h

theorem chainAvoids_C : chainAvoids (pocketClosedRel one) pcC = true := by
  cases one <;> decide +kernel
theorem chainAvoids_Br : chainAvoids (pocketClosedRel one) pcBr = true := by
  cases one <;> decide +kernel
theorem chainAvoids_M : chainAvoids (pocketClosedRel one) pcM = true := by
  cases one <;> decide +kernel
theorem chainAvoids_F : chainAvoids (pocketClosedRel one) pcF = true := by
  cases one <;> decide +kernel
theorem chainAvoids_R : chainAvoids (pocketClosedRel one) pcR = true := by
  cases one <;> decide +kernel
theorem chainAvoids_Sh : chainAvoids (pocketClosedRel one) pcSh = true := by
  cases one <;> decide +kernel
theorem chainAvoids_M2 : chainAvoids (pocketClosedRel one) pcM2 = true := by
  cases one <;> decide +kernel
theorem chainAvoids_Q1 : chainAvoids (pocketClosedRel true) pcQ1 = true := by decide +kernel
theorem chainAvoids_Q2 : chainAvoids (pocketClosedRel true) pcQ2 = true := by decide +kernel

variable (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
  (hsep : BoxSep P one σ a 1)
include hP hL hK hsep

/-- The open chamber lies in the interior of `P`. -/
theorem hpoS_C_subset : hpoS σ pcC ⊆ P.filled \ P.boundary := by
  obtain ⟨z, hz, hzC⟩ := exists_chamber_point hP hL hK
  exact subset_interior_of_meets hP (convex_hpoS σ pcC)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_C (by pc_box)) hz hzC

theorem hpoS_Br_subset : hpoS σ pcBr ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcBr)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_Br (by pc_box))
    (z := ((slotX σ : ℝ) + 1/2, -1/4)) (mem_hpoS_of (q := (1/2, -1/4)) ?_)
    (hpoS_C_subset hP hL hK hsep (mem_hpoS_of (q := (1/2, -1/4)) ?_))
  · simp only [pcBr, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcC, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

theorem hpoS_M_subset : hpoS σ pcM ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcM)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_M (by pc_box))
    (mem_hpoS_of (q := (1/2, 1/4)) ?_)
    (hpoS_Br_subset hP hL hK hsep (mem_hpoS_of (q := (1/2, 1/4)) ?_))
  · simp only [pcM, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcBr, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

theorem hpoS_F_subset : hpoS σ pcF ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcF)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_F (by pc_box))
    (mem_hpoS_of (q := (1, 1/100)) ?_)
    (hpoS_M_subset hP hL hK hsep (mem_hpoS_of (q := (1, 1/100)) ?_))
  · simp only [pcF, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcM, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

theorem hpoS_R_subset : hpoS σ pcR ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcR)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_R (by pc_box))
    (mem_hpoS_of (q := (0, -1/100)) ?_)
    (hpoS_C_subset hP hL hK hsep (mem_hpoS_of (q := (0, -1/100)) ?_))
  · simp only [pcR, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcC, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

theorem hpoS_Sh_subset : hpoS σ pcSh ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcSh)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_Sh (by pc_box))
    (mem_hpoS_of (q := (1, -1/2)) ?_)
    (hpoS_C_subset hP hL hK hsep (mem_hpoS_of (q := (1, -1/2)) ?_))
  · simp only [pcSh, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcC, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

omit hP hL hK hsep in
/-- A closed piece whose open part lies in the interior lies in the region. -/
theorem hpS_subset_filled_of {l : List HP} (hO : hpoS σ l ⊆ P.filled \ P.boundary)
    {z : Point} (hz : z ∈ hpoS σ l) : hpS σ l ⊆ P.filled :=
  calc hpS σ l ⊆ closure (hpoS σ l) := hpS_subset_closure hz
    _ ⊆ closure P.filled := closure_mono (hO.trans sdiff_subset)
    _ = P.filled := (isClosed_filled P).closure_eq

end Polygon

section Spikes

variable {P : Polygon} {σ a : ℕ}
variable (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
  (hsep : BoxSep P true σ a 1)
include hP hL hK hsep

theorem hpoS_Q1_subset : hpoS σ pcQ1 ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcQ1)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_Q1 (by pc_box))
    (mem_hpoS_of (q := (2/5, -1/2)) ?_)
    (hpoS_C_subset hP hL hK hsep (mem_hpoS_of (q := (2/5, -1/2)) ?_))
  · simp only [pcQ1, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcC, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

theorem hpoS_Q2_subset : hpoS σ pcQ2 ⊆ P.filled \ P.boundary := by
  refine subset_interior_of_meets hP (convex_hpoS σ pcQ2)
    (hpoS_not_mem_boundary hP hK hsep chainAvoids_Q2 (by pc_box))
    (mem_hpoS_of (q := (9/20, -2)) ?_)
    (hpoS_Sh_subset hP hL hK hsep (mem_hpoS_of (q := (9/20, -2)) ?_))
  · simp only [pcQ2, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num
  · simp only [pcSh, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num

end Spikes

/-! ### Coverage of the pocket room -/

section Coverage

variable {P : Polygon} {one : Bool} {σ a : ℕ}

/-- Two points of a closed piece contained in the region see each other. -/
theorem sees_of_mem_hpS {l : List HP} (hl : hpS σ l ⊆ P.filled) {g q : Point}
    (hg : g ∈ hpS σ l) (hq : q ∈ hpS σ l) : P.Sees g q :=
  (Geometry.segment_subset_of_convex (convex_hpS σ l) hg hq).trans hl

variable (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
  (hsep : BoxSep P one σ a 1)
include hP hL hK hsep

theorem hpS_M_subset_filled : hpS σ pcM ⊆ P.filled :=
  hpS_subset_filled_of (hpoS_M_subset hP hL hK hsep) (mem_hpoS_of (q := (1/2, 1/4))
    (by simp only [pcM, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num))

theorem hpS_F_subset_filled : hpS σ pcF ⊆ P.filled :=
  hpS_subset_filled_of (hpoS_F_subset hP hL hK hsep) (mem_hpoS_of (q := (1, 1/100))
    (by simp only [pcF, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num))

theorem hpS_R_subset_filled : hpS σ pcR ⊆ P.filled :=
  hpS_subset_filled_of (hpoS_R_subset hP hL hK hsep) (mem_hpoS_of (q := (0, -1/100))
    (by simp only [pcR, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num))

theorem hpS_C_subset_filled : hpS σ pcC ⊆ P.filled :=
  hpS_subset_filled_of (hpoS_C_subset hP hL hK hsep) (mem_hpoS_of (q := (1, -1/2))
    (by simp only [pcC, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num))

theorem hpS_Sh_subset_filled : hpS σ pcSh ⊆ P.filled :=
  hpS_subset_filled_of (hpoS_Sh_subset hP hL hK hsep) (mem_hpoS_of (q := (1, -1/2))
    (by simp only [pcSh, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num))

/-- **The guard of slot `σ` sees the whole pocket room.**  Without `one` spikes any point `g` of
the guard segment `s_σ` works; with spikes `g` must be the value-`1` point `g1`. -/
theorem sees_pocket_room {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1)
    (hg1' : g.1 ≤ slotX σ + 3/2) (hone : one = true → g.1 = slotX σ + 1/2) {q : Point}
    (hq : q ∈ (pocketPoly one σ).filled) : P.Sees g q := by
  have hU := filled_pocketPoly_subset one σ hq
  cases one
  · rcases mem_U0_false.1 hU with h | h | h | h | h
    · exact sees_of_mem_hpS (hpS_M_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_F_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_R_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_C_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_Sh_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
  · have hg := hone rfl
    rcases mem_U0_true.1 hU with h | h | h | h | h | h | h
    · exact sees_of_mem_hpS (hpS_M_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_F_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_R_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_C_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_Sh_subset_filled hP hL hK hsep) (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_subset_filled_of (hpoS_Q1_subset hP hL hK hsep)
        (mem_hpoS_of (q := (2/5, -1/2))
          (by simp only [pcQ1, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num)))
        (by pcS_goal <;> linarith) h
    · exact sees_of_mem_hpS (hpS_subset_filled_of (hpoS_Q2_subset hP hL hK hsep)
        (mem_hpoS_of (q := (9/20, -2))
          (by simp only [pcQ2, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num)))
        (by pcS_goal <;> linarith) h

/-- The guard sees the witnesses `t0, t1, u0, u1` of its slot. -/
theorem sees_witnesses {g : Point} (hg2 : g.2 = 0) (hg1 : (slotX σ : ℝ) ≤ g.1)
    (hg1' : g.1 ≤ slotX σ + 3/2) (hone : one = true → g.1 = slotX σ + 1/2) :
    P.Sees g (t0Pt σ) ∧ P.Sees g (t1Pt σ) ∧ P.Sees g (u0Pt σ) ∧ P.Sees g (u1Pt σ) := by
  have hs := fun {q : Point} (hq : q ∈ (pocketPoly one σ).filled) =>
    sees_pocket_room hP hL hK hsep hg2 hg1 hg1' hone hq
  refine ⟨hs t0Pt_mem_room, hs t1Pt_mem_room, ?_, ?_⟩
  · cases one
    · exact hs (pocket_vtx_mem_room (one := false) (σ := σ) (j := 6) (by decide))
    · exact hs (pocket_vtx_mem_room (one := true) (σ := σ) (j := 9) (by decide))
  · cases one
    · exact hs (pocket_vtx_mem_room (one := false) (σ := σ) (j := 7) (by decide))
    · exact hs (pocket_vtx_mem_room (one := true) (σ := σ) (j := 12) (by decide))

omit hL hK hsep in
/-- The value-`1` point sees the spike witnesses `q1, q2` (with `one` spikes). -/
theorem sees_witnesses_one (hL : P.InteriorLeft) (hK : PocketAt P true σ a)
    (hsep : BoxSep P true σ a 1) : P.Sees (g1Pt σ) (q1Pt σ) ∧ P.Sees (g1Pt σ) (q2Pt σ) := by
  have e : g1Pt σ = ((slotX σ : ℝ) + 1/2, 0) := by
    rw [g1Pt, absPt_eq]; simp [g1Rel]
  have hs := fun {q : Point} (hq : q ∈ (pocketPoly true σ).filled) =>
    sees_pocket_room hP hL hK hsep (g := g1Pt σ) (by rw [e]) (by rw [e]; simp)
      (by rw [e]; simp only; linarith) (fun _ => by rw [e]) hq
  exact ⟨hs (pocket_vtx_mem_room (one := true) (σ := σ) (j := 7) (by decide)),
    hs (pocket_vtx_mem_room (one := true) (σ := σ) (j := 10) (by decide))⟩

end Coverage

/-! ### The column of the main hexagon above the pocket -/

/-- The walls of the mouth (`pcM` without its top). -/
def pcMw : List HP := [(2, 11, 1), (0, 1, 0), (-1, 10, 2), (-38, 200, 85)]

/-- The closed box `[a_σ.x − 6, a_σ.x + 15/2] × [−6, T]`. -/
def closedBox (σ : ℕ) (T : ℝ) : Set Point :=
  {p | (slotX σ : ℝ) - 6 ≤ p.1 ∧ p.1 ≤ slotX σ + 15/2 ∧ -6 ≤ p.2 ∧ p.2 ≤ T}

theorem convex_openBox (σ : ℕ) (T : ℝ) : Convex ℝ (openBox σ T) := by
  have : openBox σ T = Ioo ((slotX σ : ℝ) - 6) (slotX σ + 15/2) ×ˢ Ioo (-6) T := by
    ext p; simp [openBox, and_assoc]
  rw [this]; exact (convex_Ioo _ _).prod (convex_Ioo _ _)

theorem convex_closedBox (σ : ℕ) (T : ℝ) : Convex ℝ (closedBox σ T) := by
  have : closedBox σ T = Icc ((slotX σ : ℝ) - 6) (slotX σ + 15/2) ×ˢ Icc (-6) T := by
    ext p; simp only [closedBox, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]; tauto
  rw [this]; exact (convex_Icc _ _).prod (convex_Icc _ _)

section Column

variable {P : Polygon} {one : Bool} {σ a : ℕ} {T : ℝ}

/-- Points of the pocket chain edges lie weakly below the door line. -/
theorem chain_edge_snd_le {j : ℕ} (hj : j < (pocketRel one).length) {p : Point}
    (hp : p ∈ ArtGallery.segment (absPt σ ((pocketClosedRel one).getD j 0))
      (absPt σ ((pocketClosedRel one).getD (j + 1) 0))) : p.2 ≤ 1 := by
  have h1 := pocketClosedRel_snd_le one j (by rw [length_pocketClosedRel]; omega)
  have h2 := pocketClosedRel_snd_le one (j + 1) (by rw [length_pocketClosedRel]; omega)
  have := Irrational.seg_snd_le hp
  rw [absPt_eq, absPt_eq] at this
  have e1 : (((pocketClosedRel one).getD j 0).2 : ℝ) ≤ 1 := by exact_mod_cast h1
  have e2 : (((pocketClosedRel one).getD (j + 1) 0).2 : ℝ) ≤ 1 := by exact_mod_cast h2
  simp only at this
  exact this.trans (max_le e1 e2)

/-- **The guard of slot `σ` sees its column of the main hexagon**: if no other edge of `P` meets
the open box `(a_σ.x − 6, a_σ.x + 15/2) × (−6, T)` (`T ≥ 2`), every point of the guard segment
sees every point of `[a_σ.x − 6, a_σ.x + 15/2] × [1, T]`. -/
theorem sees_column (hP : P.Simple) (hL : P.InteriorLeft) (hK : PocketAt P one σ a)
    (hsep : BoxSep P one σ a T) (hT : 2 ≤ T) {g : Point} (hg2 : g.2 = 0)
    (hg1 : (slotX σ : ℝ) ≤ g.1) (hg1' : g.1 ≤ slotX σ + 3/2) {q : Point}
    (hq1 : (slotX σ : ℝ) - 6 ≤ q.1) (hq1' : q.1 ≤ slotX σ + 15/2) (hq2 : 1 ≤ q.2)
    (hq2' : q.2 ≤ T) : P.Sees g q := by
  set O := hpoS σ pcMw ∩ openBox σ T with hO
  set Cl := hpS σ pcMw ∩ closedBox σ T with hCl
  have hsep1 := hsep.mono (show (1 : ℝ) ≤ T by linarith)
  -- the open column avoids the boundary
  have hav : ∀ p ∈ O, p ∉ P.boundary := by
    rintro p ⟨hpw, hpb⟩
    refine not_mem_boundary_of_chain hP hK hsep hpb fun j hj hpj => ?_
    have hy := chain_edge_snd_le hj hpj
    refine not_mem_hpo_of_chainAvoids chainAvoids_M2 (by rw [length_pocketClosedRel]; omega)
      (rel_mem_segment hpj) ?_
    obtain ⟨b1, b2, -, -⟩ := hpb
    simp only [hpoS, rel, pcMw, mem_hpo_cons, mem_hpo_nil, and_true, Set.mem_ofPred_eq] at hpw
    simp only [rel, pcM2, mem_hpo_cons, mem_hpo_nil, and_true]
    push_cast at hpw ⊢
    refine ⟨hpw.1, hpw.2.1, hpw.2.2.1, hpw.2.2.2, by linarith, by linarith, by linarith⟩
  -- an interior point
  set z : Point := ((slotX σ : ℝ) + 1/2, 1/4) with hz
  have hzM : z ∈ hpoS σ pcM := mem_hpoS_of (q := (1/2, 1/4))
    (by simp only [pcM, mem_hpo_cons, mem_hpo_nil, and_true]; norm_num)
  have hzO : z ∈ O := by
    refine ⟨?_, ?_⟩
    · simp only [hz, hpoS, rel, pcMw, mem_hpo_cons, mem_hpo_nil, and_true, Set.mem_ofPred_eq]
      norm_num
    · simp only [hz, openBox, Set.mem_ofPred_eq]
      refine ⟨by linarith, by linarith, by norm_num, by linarith⟩
  have hOC : O ⊆ P.filled \ P.boundary :=
    subset_interior_of_meets hP ((convex_hpoS σ pcMw).inter (convex_openBox σ T)) hav hzO
      (hpoS_M_subset hP hL hK hsep1 hzM)
  -- the closed column is in the closure of the open one
  have hClO : Cl ⊆ closure O := by
    refine subset_closure_of_lerp (z := z) fun p hp t ht0 ht1 => ⟨?_, ?_⟩
    · show rel σ (lerp p z t) ∈ hpo pcMw
      rw [rel_lerp]
      intro c hc
      rw [Irrational.HP.val_lerp]
      have h1 := hp.1 c hc; have h2 := hzO.1 c hc
      nlinarith [mul_pos ht0 h2, mul_nonneg (sub_nonneg.2 ht1.le) h1]
    · obtain ⟨b1, b2, b3, b4⟩ := hp.2
      obtain ⟨c1, c2, c3, c4⟩ := hzO.2
      simp only [openBox, Set.mem_ofPred_eq, lerp]
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  have hClP : Cl ⊆ P.filled :=
    hClO.trans ((closure_mono (hOC.trans sdiff_subset)).trans (isClosed_filled P).closure_eq.le)
  have hgCl : g ∈ Cl := by
    refine ⟨?_, ?_⟩
    · simp only [hpS, rel, pcMw, mem_hp_cons, mem_hp_nil, and_true, Set.mem_ofPred_eq]
      push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simp only [closedBox, Set.mem_ofPred_eq]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hqCl : q ∈ Cl := by
    refine ⟨?_, ?_⟩
    · simp only [hpS, rel, pcMw, mem_hp_cons, mem_hp_nil, and_true, Set.mem_ofPred_eq]
      push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simp only [closedBox, Set.mem_ofPred_eq]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  exact (Geometry.segment_subset_of_convex ((convex_hpS σ pcMw).inter (convex_closedBox σ T))
    hgCl hqCl).trans hClP

end Column

end ArtGallery.Sec5

end
