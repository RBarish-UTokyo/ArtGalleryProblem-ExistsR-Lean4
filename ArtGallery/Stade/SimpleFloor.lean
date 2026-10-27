module

public import ArtGallery.Stade.Polygon
public import ArtGallery.Stade.SimpleTools

/-!
# Simplicity of Stade's polygon: inputs and floor

Facts about the input segments (`inputs_pw`: increasing abscissae with gaps `≥ 44`;
`inputs_b`: every input lies in its slot) and the floor features of `poly n Φ`
(`floor_feature`: each one is a `FloorFeature` of the line `y = −1` inside `x_L < x < x_R`;
`floor_pw`: they are pairwise disjoint and ordered from left to right).
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Unpacking the template checks -/

theorem tmplFloor_feat {k : TKind} {ch : List RPt} (h : ch ∈ tmplFloor k) :
    rFloorFeatB 1000 (-1) ch = true := by
  have := tmplFloor_ok
  simp only [List.all_eq_true] at this
  exact this k (mem_allKinds k) ch h

theorem tmplFloor_x {k : TKind} {ch : List RPt} (h : ch ∈ tmplFloor k) :
    ∀ p ∈ ch, 30 ≤ p.1 ∧ p.1 ≤ 600 := by
  have := tmplFloor_range
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this k (mem_allKinds k) ch h

theorem tmplFloor_pw (k : TKind) : (tmplFloor k).Pairwise (fun f g => xmaxR f < xminR g) := by
  have := tmplFloor_sep
  simp only [List.all_eq_true] at this
  exact (pairwiseB_sound (this k (mem_allKinds k))).imp (fun h => of_decide_eq_true h)

theorem tmplInputs_x {k : TKind} {t : TInput} (h : t ∈ tmplInputs k) : 30 ≤ t.lx ∧ t.lx ≤ 600 := by
  have := tmplInputs_ok
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (this k (mem_allKinds k)).1 t h

theorem tmplInputs_pw (k : TKind) : (tmplInputs k).Pairwise (fun i j => i.lx + 44 ≤ j.lx) := by
  have := tmplInputs_ok
  simp only [List.all_eq_true, Bool.and_eq_true] at this
  exact (pairwiseB_sound (this k (mem_allKinds k)).2).imp (fun h => of_decide_eq_true h)

theorem needleDownL_feat : rFloorFeatB 1000 (-1) needleDownL = true := by decide +kernel

theorem needleDownL_x : ∀ p ∈ needleDownL, -1 / 4 ≤ p.1 ∧ p.1 ≤ 0 := by
  intro p hp
  simp only [needleDownL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem rpts_eq (H ox : ℚ) (ch : List RPt) :
    (ch.map (RPt.inst H ox)).map ratPoint = rpts H ox ch := by
  simp only [rpts, List.map_map]; rfl

theorem inst_fst (H ox : ℚ) (p : RPt) : (p.inst H ox).1 = ox + p.1 := rfl

theorem varA_nonneg (Φ : List Constraint) (k : ℕ) : (0 : ℚ) ≤ varA Φ k := by positivity

theorem slotG_nonneg (n : ℕ) (Φ : List Constraint) (c : ℕ) : (0 : ℚ) ≤ slotG n Φ c := by
  positivity

/-! ### Inputs -/

theorem mem_inputs {i : InputSeg} (h : i ∈ inputs n Φ) :
    ∃ c < paramC Φ, ∃ t ∈ tmplInputs (cKind (gadAt Φ c)),
      i.b = (slotG n Φ c : ℚ) + t.lx ∧ i.pos = t.pos ∧ i.ge = t.ge := by
  simp only [inputs, slotInputs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨c, hc, t, ht, rfl⟩ := h
  exact ⟨c, hc, t, ht, rfl, rfl, rfl⟩

theorem inputs_b {i : InputSeg} (h : i ∈ inputs n Φ) :
    ∃ c < paramC Φ, ∃ δ : ℚ, 30 ≤ δ ∧ δ ≤ 600 ∧ i.b = (slotG n Φ c : ℚ) + δ := by
  obtain ⟨c, hc, t, ht, hb, -, -⟩ := mem_inputs h
  exact ⟨c, hc, t.lx, (tmplInputs_x ht).1, (tmplInputs_x ht).2, hb⟩

/-- The input abscissae increase with gaps `≥ 44`. -/
theorem inputs_pw : (inputs n Φ).Pairwise (fun i j => i.b + 44 ≤ j.b) := by
  unfold inputs
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · unfold slotInputs
    rw [List.pairwise_map]
    exact (tmplInputs_pw _).imp (fun h => by simp only; linarith)
  · refine List.pairwise_lt_range.imp (fun {c c'} hcc => ?_)
    intro x hx y hy
    simp only [slotInputs, List.mem_map] at hx hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    have := s2_slot (n := n) (Φ := Φ) hcc
    have h1 := tmplInputs_x ht
    have h2 := tmplInputs_x ht'
    simp only
    linarith [h1.2, h2.1]

/-! ### Floor features -/

theorem mem_floorFeats {f : List (ℚ × ℚ)} (h : f ∈ floorFeats n Φ) :
    (∃ k < n, f = needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k))) ∨
    (∃ c < paramC Φ, ∃ ch ∈ tmplFloor (cKind (gadAt Φ c)),
      f = ch.map (RPt.inst (paramH n Φ) (slotG n Φ c))) := by
  simp only [floorFeats, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at h
  rcases h with ⟨k, hk, rfl⟩ | ⟨c, hc, ch, hch, rfl⟩
  · exact Or.inl ⟨k, hk, rfl⟩
  · exact Or.inr ⟨c, hc, ch, hch, rfl⟩

/-- Every floor feature is a floor feature of the line `y = −1` strictly between the walls. -/
theorem floor_feature : ∀ f ∈ floorFeats n Φ,
    FloorFeature (((-1 : ℚ)) : ℝ) (xL n Φ : ℝ) (xR n Φ : ℝ) (f.map ratPoint) := by
  intro f hf
  have hH := paramH_ge_q n Φ
  rcases mem_floorFeats hf with ⟨k, hk, rfl⟩ | ⟨c, hc, ch, hch, rfl⟩
  · rw [rpts_eq]
    refine rFloorFeatB_sound needleDownL_feat hH (fun p hp => ?_)
    have h1 := needleDownL_x p hp
    have h2 := var_lt_xR (Φ := Φ) hk
    have h3 := varA_nonneg Φ k
    constructor
    · have : xL n Φ < varA Φ k + p.1 := by unfold xL; linarith [h1.1]
      exact_mod_cast this
    · have : varA Φ k + p.1 < xR n Φ := by linarith [h1.2]
      exact_mod_cast this
  · rw [rpts_eq]
    refine rFloorFeatB_sound (tmplFloor_feat hch) hH (fun p hp => ?_)
    have h1 := tmplFloor_x hch p hp
    have h2 := slot_lt_xR (n := n) hc
    have h3 := slotG_nonneg n Φ c
    constructor
    · have : xL n Φ < slotG n Φ c + p.1 := by unfold xL; linarith [h1.1]
      exact_mod_cast this
    · have : slotG n Φ c + p.1 < xR n Φ := by linarith [h1.2]
      exact_mod_cast this

theorem floor_len {f : List (ℚ × ℚ)} (hf : f ∈ floorFeats n Φ) : 2 ≤ f.length := by
  have := (floor_feature f hf).1
  simpa using this

/-- The pairwise relation of floor features. -/
def FloorRel (f g : List (ℚ × ℚ)) : Prop :=
  Disjoint (chainSet (f.map ratPoint)) (chainSet (g.map ratPoint)) ∧
    (lstPt (f.map ratPoint)).1 < (fstPt (g.map ratPoint)).1

theorem floorRel_of_bounds {f g : List (ℚ × ℚ)} (hf2 : f ∈ floorFeats n Φ)
    (hg2 : g ∈ floorFeats n Φ) {U L : ℚ} (hf : ∀ p ∈ f, p.1 ≤ U) (hg : ∀ q ∈ g, L ≤ q.1)
    (hUL : U < L) : FloorRel f g :=
  sep_floor hf hg hUL (floor_len hf2) (floor_len hg2)

theorem needle_bounds {k : ℕ} : ∀ p ∈ needleDownL.map (RPt.inst (paramH n Φ) (varA Φ k)),
    (varA Φ k : ℚ) - 1 / 4 ≤ p.1 ∧ p.1 ≤ varA Φ k := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have := needleDownL_x q hq
  rw [inst_fst]; constructor <;> linarith [this.1, this.2]

theorem slot_bounds {c : ℕ} {ch : List RPt} (hch : ch ∈ tmplFloor (cKind (gadAt Φ c))) :
    ∀ p ∈ ch.map (RPt.inst (paramH n Φ) (slotG n Φ c)),
      (slotG n Φ c : ℚ) + 30 ≤ p.1 ∧ p.1 ≤ slotG n Φ c + 600 ∧
      (slotG n Φ c : ℚ) + xminR ch ≤ p.1 ∧ p.1 ≤ slotG n Φ c + xmaxR ch := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have := tmplFloor_x hch q hq
  rw [inst_fst]
  exact ⟨by linarith [this.1], by linarith [this.2], by linarith [xminR_le hq],
    by linarith [le_xmaxR hq]⟩

/-- The floor features are pairwise disjoint and ordered from left to right. -/
theorem floor_pw : (floorFeats n Φ).Pairwise FloorRel := by
  have hmem : ∀ f, f ∈ floorFeats n Φ → f ∈ floorFeats n Φ := fun _ h => h
  refine List.Pairwise.imp_of_mem (R := fun f g => f ∈ floorFeats n Φ → g ∈ floorFeats n Φ →
    FloorRel f g) (fun ha hb h => h ha hb) ?_
  unfold floorFeats
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp (fun {k k'} hkk hf hg => ?_)
    have h := s2_var (Φ := Φ) hkk
    have hC : (0 : ℚ) ≤ paramC Φ := by positivity
    refine floorRel_of_bounds hf hg (fun p hp => (needle_bounds p hp).2)
      (fun q hq => (needle_bounds q hq).1) (by linarith)
  · rw [List.pairwise_flatMap]
    refine ⟨fun c _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (tmplFloor_pw _).imp_of_mem (fun {f g} hfm hgm hfg hf hg => ?_)
      exact floorRel_of_bounds hf hg (fun p hp => (slot_bounds hfm p hp).2.2.2)
        (fun q hq => (slot_bounds hgm q hq).2.2.1) (by linarith)
    · refine List.pairwise_lt_range.imp (fun {c c'} hcc => ?_)
      intro f hf g hg hf' hg'
      simp only [List.mem_map] at hf hg
      obtain ⟨ch, hch, rfl⟩ := hf
      obtain ⟨ch', hch', rfl⟩ := hg
      have := s2_slot (n := n) (Φ := Φ) hcc
      exact floorRel_of_bounds hf' hg' (fun p hp => (slot_bounds hch p hp).2.1)
        (fun q hq => (slot_bounds hch' q hq).1) (by linarith)
  · intro f hf g hg hf' hg'
    simp only [List.mem_map, List.mem_range, List.mem_flatMap] at hf hg
    obtain ⟨k, hk, rfl⟩ := hf
    obtain ⟨c, hc, ch, hch, rfl⟩ := hg
    have := s2_var_slot (Φ := Φ) (c := c) hk
    have hH := paramH_ge_q n Φ
    exact floorRel_of_bounds hf' hg' (fun p hp => (needle_bounds p hp).2)
      (fun q hq => (slot_bounds hch q hq).1) (by linarith)

end

end ArtGallery.Stade
