module

public import ArtGallery.Stade.GuardRegion

/-!
# The canonical guards: membership and distinctness

* `inGuard_mem`, `varGuard_mem`, `auxGuard_mem`: membership in `canonList`;
* `slotGuards_mem`: the guards of a slot (`GuardSlots.lean`) are canonical guards;
* `auxGuard_room`: the aux guard of an addition slot `c` lies in the room of the slot, hence in
  `g_c + [50, 527] × (−∞, −1]`;
* `canonList_nodup`: the canonical guards are pairwise distinct (variable guards at height
  `≥ H`, input guards at height in `[0, 6]`, aux guards below the floor; abscissae distinct
  within each kind).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

variable {n : ℕ} {Φ : List Constraint} {v : ℕ → ℝ}

/-- The guard of a variable `k < n` is a canonical guard. -/
theorem varGuard_mem {k : ℕ} (hk : k < n) : varGuard n Φ v k ∈ canonList n Φ v := by
  unfold canonList
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk,
    rfl⟩))

/-- The guard of an input segment is a canonical guard. -/
theorem inGuard_mem {i : InputSeg} (hi : i ∈ inputs n Φ) : inGuard v i ∈ canonList n Φ v := by
  unfold canonList
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, hi, rfl⟩))

/-- The aux guard of an addition slot is a canonical guard. -/
theorem auxGuard_mem {c : ℕ} (hc : c < paramC Φ) (ha : isAdd (gadAt Φ c) = true) :
    auxGuard n Φ v c ∈ canonList n Φ v := by
  unfold canonList
  refine List.mem_append_right _ (List.mem_map.2 ⟨c, ?_, rfl⟩)
  exact List.mem_filter.2 ⟨List.mem_range.2 hc, ha⟩

/-- The input guards of the template inputs of slot `c` are canonical guards. -/
theorem slot_inGuard_mem {c : ℕ} (hc : c < paramC Φ) {t : TInput}
    (ht : t ∈ tmplInputs (cKind (gadAt Φ c))) :
    inPt ((slotG n Φ c : ℝ) + (t.lx : ℝ)) (v (gadVar Φ c t.role)) ∈ canonList n Φ v := by
  have hi : (⟨(slotG n Φ c : ℚ) + t.lx, t.pos, gadVar Φ c t.role, t.ge, c, t.role⟩ : InputSeg) ∈
      inputs n Φ := by
    simp only [inputs, slotInputs, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨c, hc, t, ht, rfl⟩
  have := inGuard_mem (v := v) hi
  simpa [inGuard, inPt] using this

/-- **The guards of a slot are canonical guards** (inputs at the values of the variables of the
constraint, and the aux guard). -/
theorem slotGuards_mem {c : ℕ} (hc : c < paramC Φ) {g : Point}
    (hg : g ∈ slotGuards (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (v (gadVar Φ c 0))
      (v (gadVar Φ c 1)) (v (gadVar Φ c 2))) : g ∈ canonList n Φ v := by
  have hI := fun t (ht : t ∈ tmplInputs (cKind (gadAt Φ c))) =>
    slot_inGuard_mem (n := n) (v := v) hc ht
  have hA := auxGuard_mem (n := n) (v := v) hc
  have hgad := gadAt_isGad hc
  unfold auxGuard at hA
  cases h : gadAt Φ c with
  | one x => rw [h] at hgad; simp [isGad] at hgad
  | invGe x y =>
    rw [h] at hg hI
    simp only [cKind, slotGuards, tmplInputs, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at hg hI
    rcases hg with rfl | rfl
    · simpa using hI.1
    · simpa using hI.2
  | invRevLe x y =>
    rw [h] at hg hI
    simp only [cKind, slotGuards, tmplInputs, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at hg hI
    rcases hg with rfl | rfl
    · simpa using hI.1
    · simpa using hI.2
  | addLe x y z =>
    rw [h] at hg hI hA
    simp only [cKind, slotGuards, tmplInputs, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at hg hI
    rcases hg with rfl | rfl | rfl | rfl
    · simpa [isAdd, auxPt, cKind] using hA
    · simpa using hI.2.1
    · simpa using hI.1
    · simpa using hI.2.2
  | addGe x y z =>
    rw [h] at hg hI hA
    simp only [cKind, slotGuards, tmplInputs, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at hg hI
    rcases hg with rfl | rfl | rfl | rfl
    · simpa [isAdd, auxPt, cKind] using hA
    · simpa using hI.2.2
    · simpa using hI.2.1
    · simpa using hI.1

/-! ### Position of the aux guards -/

/-- The aux guard of an addition slot lies in `g_c + [50, 527] × (−∞, −1]`. -/
theorem auxGuard_pos (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) {c : ℕ}
    (hc : c < paramC Φ) (ha : isAdd (gadAt Φ c) = true) :
    (slotG n Φ c : ℝ) + 50 ≤ (auxGuard n Φ v c).1 ∧
      (auxGuard n Φ v c).1 ≤ (slotG n Φ c : ℝ) + 527 ∧ (auxGuard n Φ v c).2 ≤ -1 := by
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
    have hR := (alI_mem_auxRegion (G := (slotG n Φ c : ℝ)) (hv x).1 (hv y).1
      (by linarith [(hv z).2])).2
    obtain ⟨-, h1, -, h3, h4⟩ := mem_alRoom.1 hR
    exact ⟨h1, h3, h4⟩
  | addGe x y z =>
    simp only [cKind, auxPt, gadVar, h, cVars, List.getD_cons_zero, List.getD_cons_succ]
    have hR := (agI_mem_auxRegion (G := (slotG n Φ c : ℝ)) (hv x).1 (hv x).2 (hv y).1
      (hv y).2).2
    obtain ⟨-, h1, -, h3, h4⟩ := mem_agRoom.1 hR
    exact ⟨h1, by linarith, h4⟩

/-! ### Distinctness -/

/-- **The canonical guards are pairwise distinct.** -/
theorem canonList_nodup (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    (canonList n Φ v).Nodup := by
  have hH0 := hH_ge n Φ
  unfold canonList
  rw [List.nodup_append, List.nodup_append]
  have hDV : 0 < paramDV Φ := by unfold paramDV; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- variable guards
    refine List.Nodup.map_on (fun k _ k' _ hkk => ?_) List.nodup_range
    have h1 := congrArg Prod.fst hkk
    simp only [varGuard, Nat.cast_inj] at h1
    exact Nat.eq_of_mul_eq_mul_right hDV h1
  · -- input guards
    refine List.pairwise_map.2 (inputs_pw.imp fun {i j} hij hg => ?_)
    have h1 := congrArg Prod.fst hg
    simp only [inGuard, Rat.cast_inj] at h1
    linarith
  · -- variables vs inputs
    intro a ha b hb hab
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    have h2 := congrArg Prod.snd hab
    simp only [varGuard, inGuard] at h2
    linarith [(hv k).1, (hv i.var).2]
  · -- aux guards
    refine List.pairwise_map.2 ?_
    have hpw : (addSlots Φ).Pairwise (· < ·) := List.pairwise_lt_range.filter _
    refine List.Pairwise.imp_of_mem (fun {c c'} hc hc' hcc hg => ?_) hpw
    obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
    obtain ⟨hc1', hc2'⟩ := List.mem_filter.1 hc'
    have p1 := auxGuard_pos (n := n) hv hsol (List.mem_range.1 hc1) hc2
    have p2 := auxGuard_pos (n := n) hv hsol (List.mem_range.1 hc1') hc2'
    have hs := s2_slot (n := n) (Φ := Φ) hcc
    have hs' : (slotG n Φ c : ℝ) + 1200 ≤ (slotG n Φ c' : ℝ) := by exact_mod_cast hs
    have h1 := congrArg Prod.fst hg
    linarith [p1.1, p1.2.1, p2.1, p2.2.1]
  · -- variables and inputs vs aux guards
    intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
    have p := auxGuard_pos (n := n) hv hsol (List.mem_range.1 hc1) hc2
    have h2 := congrArg Prod.snd hab
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
      simp only [varGuard] at h2
      linarith [(hv k).1, p.2.2]
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      simp only [inGuard] at h2
      linarith [(hv i.var).1, p.2.2]

/-- **The canonical guard set has `guards n Φ` elements.** -/
theorem canonGuards_card (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    (canonGuards n Φ v).card = guards n Φ := by
  unfold canonGuards
  rw [List.toFinset_card_of_nodup (canonList_nodup hv hsol), canonList_length]

end ArtGallery.Stade

end
