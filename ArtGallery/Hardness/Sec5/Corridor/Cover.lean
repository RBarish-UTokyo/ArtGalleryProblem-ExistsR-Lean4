module

public import ArtGallery.Hardness.Sec5.Corridor.CoverSlotD
public import ArtGallery.Hardness.Sec5.Corridor.Member
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Section 5: corridors — the canonical guards cover the corridor

**Main theorem** (`Good.corridor_covered`; docs/section5/08_proof_plan.md §9): let `I` be a good
corridor input sitting in a polygon `P` (`I.poly.filled ⊆ P.filled`, which follows from
`CorridorAt P I a b`, `CorridorClear P I`, `P.Simple`, `P.InteriorLeft` by `Good.poly_subset`).
For every copied pair `k < I.np` place the base guard `p_k(t_k) = (27 σ_k / 2 + t_k, 0)` and the
receiver guard `q_k(t_k)` at the **same** offset `t_k ∈ [0, 3/2]`, and assume that the base guard
sees the entrance `d0 c0` and the receiver sees the window `c1 d1` within `P`.  Together with the
stationary guards `p_k = sgPt k`, these guards see every point of the corridor region.

Proof: interior points off the finitely many lines `y = H`, `x = (sgPt j).x` are classified
(`Good.classify_lower`, `Good.classify_upper`):

* slot pieces (below the floor line) and strips: the stationary guard of the pair;
* umbra pieces: `w > 0`, `L ≥ 0` there, so the umbra copy statement (`CopyPair.umbra_covered`,
  equal offsets) puts the point on the visible side of `p c0` or of `q c1`
  (`Good.base_sees_umbra`, `Good.recv_sees_umbra`);
* nook pieces (above the mouth `z0 z1`): `w > 0`, `L ≤ 0` (below the nook axis through `n0`,
  `n1`), so the nook copy statement (`CopyPair.nook_covered`) puts the point on the visible side of
  `p z0` or of `q z1`, seen through the mouth (`Good.base_sees_nook`, `Good.recv_sees_nook`).

The remaining points are limits of such points, and the seen sets are closed.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-- Two points on the line through `f₀, f₁` give the same orientation test up to a factor. -/
theorem det_onLine_onLine (f₀ f₁ z : Point) (x₀ x₁ : ℝ) (h : f₁.1 - f₀.1 ≠ 0) :
    ArtGallery.det (onLine f₀ f₁ x₁) (onLine f₀ f₁ x₀) z * (f₁.1 - f₀.1) =
      (x₀ - x₁) * ArtGallery.det f₀ f₁ z := by
  simp only [ArtGallery.det, onLine]
  field_simp
  ring

/-- The set of points seen from `g` is closed. -/
theorem isClosed_setOf_sees (P : Polygon) (g : Point) : IsClosed {z | P.Sees g z} := by
  have : {z | P.Sees g z} = ⋂ t ∈ Icc (0 : ℝ) 1, (fun z => Geometry.lerp g z t) ⁻¹' P.filled := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, Polygon.Sees,
      Geometry.segment_eq_image_lerp, image_subset_iff]
    rfl
  rw [this]
  refine isClosed_biInter fun t _ => (Jordan.isClosed_filled P).preimage ?_
  unfold Geometry.lerp; fun_prop

namespace Input

variable {I : Input} {N : ℚ}

section Cover

variable (hg : I.Good N) {P : Polygon} (hsub : I.poly.filled ⊆ P.filled) {t : ℕ → ℝ}
  (ht : ∀ k < I.np, 0 ≤ t k ∧ t k ≤ 3 / 2)
  (hent : ∀ k < I.np, ∀ w ∈ I.entrance, P.Sees ((I.umbraR k).p (t k)) w)
  (hwin : ∀ k < I.np, ∀ w ∈ I.window, P.Sees ((I.umbraR k).q (t k)) w)
include hg hsub ht hent hwin

/-- A point is seen by one of the guards of the corridor. -/
def SeenBy (P : Polygon) (I : Input) (t : ℕ → ℝ) (z : Point) : Prop :=
  ∃ k < I.np, P.Sees ((I.umbraR k).p (t k)) z ∨ P.Sees ((I.umbraR k).q (t k)) z ∨
    P.Sees (ratPoint (I.sgPt k)) z

omit hg hsub ht hent hwin in
theorem isClosed_seenBy (P : Polygon) (I : Input) (t : ℕ → ℝ) : IsClosed {z | SeenBy P I t z} := by
  have : {z | SeenBy P I t z} = ⋃ k ∈ Finset.range I.np,
      ({z | P.Sees ((I.umbraR k).p (t k)) z} ∪ {z | P.Sees ((I.umbraR k).q (t k)) z} ∪
        {z | P.Sees (ratPoint (I.sgPt k)) z}) := by
    ext z
    simp only [SeenBy, mem_ofPred_eq, mem_iUnion, Finset.mem_range, mem_union, exists_prop,
      or_assoc]
  rw [this]
  exact isClosed_biUnion_finset fun k _ =>
    ((isClosed_setOf_sees P _).union (isClosed_setOf_sees P _)).union (isClosed_setOf_sees P _)

omit hsub ht hent hwin in
/-- The nook piece is below the nook axis: `L ≤ 0`. -/
theorem Good.nook_L_nonpos {k : ℕ} (hk : k < I.np) {z : Point} (hz : z ∈ hpSet (I.nookFs k)) :
    (I.nookR k).L z ≤ 0 := by
  have hd := hz (Aff.det (ratPoint (I.n1 k)) (ratPoint (I.n0 k))) (by simp [nookFs])
  rw [Aff.ev_det] at hd
  have hF := F0_fst_lt hg.toValid hk
  have hF' : ((I.F0 k).1 : ℝ) < ((I.F1 k).1 : ℝ) := by exact_mod_cast hF
  have hx : ((I.z0 k).1 : ℝ) < ((I.z1 k).1 : ℝ) := by
    have h0 := (hg.rl_z0 hk).1
    have h1 := (hg.rl_z1 hk).1
    have : I.lXR (ratPoint (I.z0 k)) < I.lXR (ratPoint (I.z1 k)) := by rw [h0, h1]; linarith
    rwa [lXR_lt_iff' hg] at this
  have e := det_onLine_onLine (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) z ((I.z0 k).1 : ℝ)
    ((I.z1 k).1 : ℝ) (by simp only [ratPoint_fst]; linarith)
  simp only [n1, n0, ratPoint_onLine] at hd
  simp only [ratPoint_fst] at e
  have hdet : ArtGallery.det (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) z ≤ 0 := by
    by_contra hc
    push Not at hc
    have h1 : 0 ≤ ArtGallery.det (onLine (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) ((I.z1 k).1 : ℝ))
        (onLine (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) ((I.z0 k).1 : ℝ)) z *
        (((I.F1 k).1 : ℝ) - (I.F0 k).1) := mul_nonneg hd (by linarith)
    have h2 : (((I.z0 k).1 : ℝ) - (I.z1 k).1) *
        ArtGallery.det (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) z < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hc
    linarith
  by_contra hc
  push Not at hc
  exact absurd ((nookR_L_pos_iff hg.toValid hk z).1 hc) (not_lt.2 hdet)

/-- **Coverage of the generic points** (off the lines `y = H` and `x = (sgPt j).x`). -/
theorem Good.seen_generic {z : Point} (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hzH : z.2 ≠ I.H) (hzx : ∀ j < I.np, z.1 ≠ ((ratPoint (I.sgPt j)).1)) :
    SeenBy P I t z := by
  rcases lt_or_gt_of_ne hzH with hlo | hhi
  · obtain ⟨k, hk, h | h⟩ := hg.classify_lower hzK hzb hlo
    · exact ⟨k, hk, Or.inr (Or.inr (hg.sg_sees_slot2 hk hsub h hzK hzb))⟩
    · exact ⟨k, hk, Or.inr (Or.inr (hg.sg_sees_slot4 hk hsub h hzK hzb))⟩
  have hzx' : ∀ j < I.np, I.lXR z ≠ I.lXR (ratPoint (I.sgPt j)) := fun j hj h =>
    hzx j hj ((lXR_eq_iff' hg).1 h)
  obtain ⟨k, hk, hcl⟩ := hg.classify_upper hzK hzb hhi.le hzx'
  obtain ⟨ht0, ht1⟩ := ht k hk
  have hS2 : (0 : ℝ) < 8 * (I.S : ℝ) ^ 2 := by have := hg.S_pos; positivity
  rcases hcl with h | h | ⟨h, hy⟩
  · exact ⟨k, hk, Or.inr (Or.inr (hg.sees_strip hk hsub h))⟩
  · -- the umbra
    have hw : 0 < (I.umbraR k).w z := by
      show 0 < z.2 - (I.umbraR k).k0.2
      rw [umbraR_k0, ratPoint_c0']; simp only; linarith
    have hL : 0 ≤ (I.umbraR k).L z := by
      have h1 := (mem_umbra_iff.1 h).1
      rw [← hg.umbraR_L_AR k z] at h1
      exact nonneg_of_mul_nonneg_c hS2 h1
    rcases CopyPair.umbra_covered (umbraR_hyp hg.toValid k) (le_refl (t k)) hw hL with h' | h'
    · rw [umbraR_k0, ← det_eq_det2] at h'
      exact ⟨k, hk, Or.inl (hg.base_sees_umbra hk hsub ht0 ht1 (hent k hk) h h')⟩
    · rw [umbraR_k1, ← det_eq_det2] at h'
      exact ⟨k, hk, Or.inr (Or.inl (hg.recv_sees_umbra hk hsub ht0 ht1 (hwin k hk) h h'))⟩
  · -- the nook
    have hw : 0 < (I.nookR k).w z := by
      show 0 < z.2 - (I.nookR k).k0.2
      rw [nookR_k0]
      have h0 : I.lYR (ratPoint (I.z0 k)) < I.lYR z := by
        rw [(hg.rl_z0 hk).2, ← (hg.rl_z1 hk).2]; exact hy
      have : ¬ z.2 ≤ (ratPoint (I.z0 k)).2 := fun hc => absurd ((lYR_le_iff' hg).2 hc) (not_le.2 h0)
      linarith [not_le.1 this]
    have hL := hg.nook_L_nonpos hk h
    have ep : (I.nookR k).p (t k) = (I.umbraR k).p (t k) := by rw [nookR_p, umbraR_p]
    have eq : (I.nookR k).q (t k) = (I.umbraR k).q (t k) := by rw [nookR_q, umbraR_q]
    have hzK' := hzK
    rcases CopyPair.nook_covered (nookR_hyp hg.toValid k) (le_refl (t k)) hw hL with h' | h'
    · rw [nookR_k0, ← det_eq_det2, ep] at h'
      exact ⟨k, hk, Or.inl (hg.base_sees_nook hk hsub ht0 ht1 (hent k hk) h hzK hzb h')⟩
    · rw [nookR_k1, ← det_eq_det2, eq] at h'
      exact ⟨k, hk, Or.inr (Or.inl (hg.recv_sees_nook hk hsub ht0 ht1 (hwin k hk) h hzK hzb h'))⟩

/-- **The canonical guards cover the corridor.**  Every point of the corridor region is seen
(within `P`) by the base guard `p_k(t_k)`, the receiver guard `q_k(t_k)` or the stationary guard
`p_k` of some pair `k < I.np`. -/
theorem Good.corridor_covered {z : Point} (hz : z ∈ I.poly.filled) : SeenBy P I t z := by
  set D : Set Point := ⋂ i : Option (Fin I.np), Option.elim i {w : Point | w.2 ≠ I.H}
    (fun j => {w : Point | w.1 ≠ (ratPoint (I.sgPt j)).1}) with hD
  have hDo : ∀ i : Option (Fin I.np), IsOpen (Option.elim i {w : Point | w.2 ≠ I.H}
      (fun j => {w : Point | w.1 ≠ (ratPoint (I.sgPt j)).1})) := by
    rintro (_ | j)
    · exact isOpen_ne_fun continuous_snd continuous_const
    · exact isOpen_ne_fun continuous_fst continuous_const
  have hDd : ∀ i : Option (Fin I.np), Dense (Option.elim i {w : Point | w.2 ≠ I.H}
      (fun j => {w : Point | w.1 ≠ (ratPoint (I.sgPt j)).1})) := by
    rintro (_ | j)
    · exact (dense_compl_singleton (I.H : ℝ)).preimage isOpenMap_snd
    · exact (dense_compl_singleton ((ratPoint (I.sgPt j)).1)).preimage isOpenMap_fst
  have hDense : Dense D := dense_iInter_of_isOpen hDo hDd
  have hK := hg.poly_simple
  have hO := Jordan.isOpen_filled_sdiff_boundary hK
  have hgen : (I.poly.filled \ I.poly.boundary) ∩ D ⊆ {z | SeenBy P I t z} := by
    rintro w ⟨⟨hwK, hwb⟩, hwD⟩
    simp only [hD, mem_iInter] at hwD
    exact hg.seen_generic hsub ht hent hwin hwK hwb (hwD none) fun j hj => hwD (some ⟨j, hj⟩)
  have h1 := Polygon.filled_subset_closure_interior hK hz
  have h2 : closure (I.poly.filled \ I.poly.boundary) ⊆
      closure ((I.poly.filled \ I.poly.boundary) ∩ D) :=
    closure_minimal (hDense.open_subset_closure_inter hO) isClosed_closure
  exact closure_minimal hgen (isClosed_seenBy P I t) (h2 h1)

end Cover

/-- **Coverage of a corridor in a global polygon** (the corridor hypotheses of the reduction). -/
theorem Good.corridor_covered_in {P : Polygon} {a b : ℕ} (hg : I.Good N) (hP : P.Simple)
    (hL : P.InteriorLeft) (hC : CorridorAt P I a b) (hcl : CorridorClear P I) {t : ℕ → ℝ}
    (ht : ∀ k < I.np, 0 ≤ t k ∧ t k ≤ 3 / 2)
    (hent : ∀ k < I.np, ∀ w ∈ I.entrance, P.Sees ((I.umbraR k).p (t k)) w)
    (hwin : ∀ k < I.np, ∀ w ∈ I.window, P.Sees ((I.umbraR k).q (t k)) w)
    {z : Point} (hz : z ∈ I.poly.filled) : SeenBy P I t z :=
  hg.corridor_covered (hg.poly_subset hP hL hC hcl) ht hent hwin hz

end Input

end ArtGallery.Sec5.Corridor

end
