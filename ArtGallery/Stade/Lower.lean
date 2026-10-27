module

public import ArtGallery.Stade.LowerGadgets

/-!
# Stade's construction: the correctness statements (a) and (c) (proof plan §8)

* **(a)** `card_le_of_boundaryGuard'` (`LowerAssign.lean`): every boundary guard set of
  `poly n Φ` has at least `guards n Φ` points.
* **(c)** `sat_of_boundaryGuard'`: a boundary guard set `G` of cardinality `guards n Φ` encodes a
  solution `v` with `v_i ∈ [1/2, 2]`, the guard of variable `i` being `(varX i, varY0 + 2 v_i)`.

Proof of (c) (§8): the guard assignment (`exists_assign`) places one guard on every variable
segment, input segment and aux region; `v_k := (y(γ_k) − H + 1)/2`, `w_j := (y(γ_j) + 2)/4`.
* `x = 1`: the wedges `W4, W5` pin the guard at height `H + 1` (`Assign.one`);
* copy nooks: `w_j ≤ v_k` (GE) resp. `v_k ≤ w_j` (LE) (`copy_rel`);
* gadgets: `invGe_rel`, `invRevLe_rel`, `addLe_rel`, `addGe_rel`;
* composition with the copy inequalities by monotonicity (table of construction.md §8).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-- A gadget constraint of `Φ` is the gadget of some slot. -/
theorem exists_slot {c : Constraint} (hc : c ∈ Φ) (hg : isGad c = true) :
    ∃ s < paramC Φ, gadAt Φ s = c := by
  have : c ∈ gad Φ := List.mem_filter.2 ⟨hc, hg⟩
  obtain ⟨s, hs, e⟩ := List.getElem_of_mem this
  refine ⟨s, hs, ?_⟩
  unfold gadAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some, e]

/-- The input of slot `c` for the template input `t`. -/
theorem slot_input {c : ℕ} (hc : c < paramC Φ) {t : TInput}
    (ht : t ∈ tmplInputs (cKind (gadAt Φ c))) :
    ∃ j : Fin (inputs n Φ).length, (inputs n Φ)[j].b = (slotG n Φ c : ℚ) + t.lx ∧
      (inputs n Φ)[j].var = (cVars (gadAt Φ c)).getD t.role 0 ∧ (inputs n Φ)[j].ge = t.ge := by
  have hmem : (⟨(slotG n Φ c : ℚ) + t.lx, t.pos, (cVars (gadAt Φ c)).getD t.role 0, t.ge, c,
      t.role⟩ : InputSeg) ∈ slotInputs n Φ c := List.mem_map.2 ⟨t, ht, rfl⟩
  obtain ⟨j, hj⟩ := slotInput_idx hc hmem
  exact ⟨j, by rw [hj], by rw [hj], by rw [hj]⟩

section Sat

variable {G : Finset Point} (A : Assign n Φ G)

/-- The candidate solution: the values of the variable guards. -/
noncomputable def Assign.sol (i : ℕ) : ℝ := if h : i < n then A.val ⟨i, h⟩ else 1

theorem Assign.sol_eq {i : ℕ} (h : i < n) : A.sol i = A.val ⟨i, h⟩ := dif_pos h

/-- Copy inequalities in terms of the candidate solution. -/
theorem Assign.copy (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point))
    (j : Fin (inputs n Φ).length) {x : ℕ} (hx : x < n) (hvar : (inputs n Φ)[j].var = x) :
    ((inputs n Φ)[j].ge = true → A.ival j ≤ A.sol x) ∧
      ((inputs n Φ)[j].ge = false → A.sol x ≤ A.ival j) := by
  have hk : (inputs n Φ)[j].var < n := hvar ▸ hx
  have e : A.sol x = A.val ⟨(inputs n Φ)[j].var, hk⟩ := by
    rw [A.sol_eq hx]; congr 1; exact Fin.ext hvar.symm
  rw [e]
  exact copy_rel A hG j hk

theorem Assign.sol_mem {i : ℕ} (h : i < n) : 1 / 2 ≤ A.sol i ∧ A.sol i ≤ 2 := by
  rw [A.sol_eq h]; exact A.val_mem _

/-- Every constraint holds for the candidate solution. -/
theorem Assign.holds (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {c : Constraint} (hcΦ : c ∈ Φ) :
    c.Holds A.sol := by
  have hvl := hΦ c hcΦ
  cases c with
  | one x =>
    have hx : x < n := hvl
    have hone : hasOne Φ x = true := List.any_eq_true.2 ⟨_, hcΦ, by simp [isOneOf]⟩
    show A.sol x = 1
    rw [A.sol_eq hx]
    have := A.one ⟨x, hx⟩ hone
    unfold Assign.val; rw [this]; ring
  | invGe x y =>
    obtain ⟨hx, hy⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    have hkind : cKind (gadAt Φ s) = .invGe := by rw [hgad]; rfl
    have hvars : cVars (gadAt Φ s) = [x, y] := by rw [hgad]; rfl
    obtain ⟨jx, hbx, hvx, hgx⟩ := slot_input (n := n) hs (t := ⟨40, true, 0, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jy, hby, hvy, hgy⟩ := slot_input (n := n) hs (t := ⟨100, false, 1, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    rw [hvars] at hvx hvy
    have h1 := (A.copy hG jx hx hvx).1 hgx
    have h2 := (A.copy hG jy hy hvy).1 hgy
    have hr := invGe_rel A hG hs hbx hby hkind (by rw [hgad]; rfl)
    have := A.ival_mem jx
    have := A.ival_mem jy
    show 1 ≤ A.sol x * A.sol y
    nlinarith
  | invRevLe x y =>
    obtain ⟨hx, hy⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    have hkind : cKind (gadAt Φ s) = .invRevLe := by rw [hgad]; rfl
    have hvars : cVars (gadAt Φ s) = [x, y] := by rw [hgad]; rfl
    obtain ⟨jx, hbx, hvx, hgx⟩ := slot_input (n := n) hs (t := ⟨60, false, 0, false⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jy, hby, hvy, hgy⟩ := slot_input (n := n) hs (t := ⟨104, false, 1, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    rw [hvars] at hvx hvy
    have h1 := (A.copy hG jx hx hvx).2 hgx
    have h2 := (A.copy hG jy hy hvy).1 hgy
    have hr := invRevLe_rel A hG hs hbx hby hkind (by rw [hgad]; rfl)
    have := A.ival_mem jx
    have := A.ival_mem jy
    have := A.sol_mem hx
    have := A.sol_mem hy
    show A.sol x * (5 / 2 - A.sol y) ≤ 1
    nlinarith [mul_le_mul h1 (by linarith : 5 / 2 - A.sol y ≤ 5 / 2 - A.ival jy)
      (by linarith) (by linarith)]
  | addLe x y z =>
    obtain ⟨hx, hy, hz⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    have hkind : cKind (gadAt Φ s) = .addLe := by rw [hgad]; rfl
    have hvars : cVars (gadAt Φ s) = [x, y, z] := by rw [hgad]; rfl
    obtain ⟨jx, hbx, hvx, hgx⟩ := slot_input (n := n) hs (t := ⟨370, false, 0, false⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jy, hby, hvy, hgy⟩ := slot_input (n := n) hs (t := ⟨210, false, 1, false⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jz, hbz, hvz, hgz⟩ := slot_input (n := n) hs (t := ⟨530, false, 2, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    rw [hvars] at hvx hvy hvz
    have h1 := (A.copy hG jx hx hvx).2 hgx
    have h2 := (A.copy hG jy hy hvy).2 hgy
    have h3 := (A.copy hG jz hz hvz).1 hgz
    have hr := addLe_rel A hG hs hbx hby hbz hkind (by rw [hgad]; rfl)
    show A.sol x + A.sol y ≤ A.sol z
    linarith
  | addGe x y z =>
    obtain ⟨hx, hy, hz⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    have hkind : cKind (gadAt Φ s) = .addGe := by rw [hgad]; rfl
    have hvars : cVars (gadAt Φ s) = [x, y, z] := by rw [hgad]; rfl
    obtain ⟨jx, hbx, hvx, hgx⟩ := slot_input (n := n) hs (t := ⟨370, false, 0, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jy, hby, hvy, hgy⟩ := slot_input (n := n) hs (t := ⟨210, false, 1, true⟩)
      (by rw [hkind]; simp [tmplInputs])
    obtain ⟨jz, hbz, hvz, hgz⟩ := slot_input (n := n) hs (t := ⟨185 / 2, false, 2, false⟩)
      (by rw [hkind]; simp [tmplInputs])
    rw [hvars] at hvx hvy hvz
    have h1 := (A.copy hG jx hx hvx).1 hgx
    have h2 := (A.copy hG jy hy hvy).1 hgy
    have h3 := (A.copy hG jz hz hvz).2 hgz
    have hr := addGe_rel A hG hs hbx hby hbz hkind (by rw [hgad]; rfl)
    show A.sol z ≤ A.sol x + A.sol y
    linarith

/-- The guard of variable `i` is `(varX i, varY0 + 2 v_i)`. -/
theorem Assign.var_mem {i : ℕ} (hi : i < n) :
    ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * A.sol i) ∈ G := by
  have e : ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * A.sol i) = A.γ (.inl ⟨i, hi⟩) := by
    refine Prod.ext ?_ ?_
    · simp only [varX]; exact (A.var ⟨i, hi⟩).1.symm
    · simp only [varY0, A.sol_eq hi, Assign.val]; push_cast; ring
  rw [e]
  exact A.mem _

end Sat

/-- **(c) A boundary guard set of cardinality `guards n Φ` encodes a solution.** -/
theorem sat_of_boundaryGuard' (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guards n Φ) :
    ∃ v : ℕ → ℝ, (∀ i < n, 1 / 2 ≤ v i ∧ v i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds v) ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G := by
  obtain ⟨A⟩ := exists_assign G hG hcard
  exact ⟨A.sol, fun i hi => A.sol_mem hi, fun c hc => A.holds hΦ hG hc,
    fun i hi => A.var_mem hi⟩

end ArtGallery.Stade

end
