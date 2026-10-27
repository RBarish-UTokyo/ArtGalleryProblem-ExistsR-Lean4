module

public import ArtGallery.Hardness.Sec5.Assemble.UnitChain
public import ArtGallery.Hardness.Sec5.Assemble.Global

/-!
# Section 5: the polygon `construct Φ n` is simple (08 §4)

**Main theorem** `construct_simple`: for every instance with all variable indices `< n`, the
polygon `construct Φ n` is simple and counter-clockwise.

* Every unit of `unitSpecs n Φ` is admissible (`UnitOK`: increasing working slots `< 4n`, as many
  as its template has receivers; `unitSpecs_ok`), and there are at most `N` units per side
  (`length_unitSpecs_fst/snd`); hence its corridor input is good (`unitInput_good`), with
  `S + 1 ≤ H_m = S + 3m + 1 ≤ S + 3N`.
* The unit chains are `UnitFeature`s (`unit_feature`, `UnitChain.lean`), and `global_simple`
  (`Global.lean`) assembles the polygon.
* `n = 0`: the triangle `(0,0), (1,0), (0,1)`.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input)
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### Admissible units -/

/-- An admissible unit: its working slots are increasing, below `4n`, and as many as the
receivers of its template. -/
structure UnitOK (n : ℕ) (u : UnitSpec) : Prop where
  /-- One working slot per receiver. -/
  len : u.work.length = (tmplT u.kind).length
  /-- Working slots are slots. -/
  lt : ∀ σ ∈ u.work, σ < 4 * n
  /-- Strictly increasing. -/
  mono : u.work.Pairwise (· < ·)

theorem length_tmplT (k : Kind) : (tmplT k).length = 2 ∨ (tmplT k).length = 3 := by
  cases k <;> simp [tmplT, tmplTGE, tmplTLE, tmplTOR, tmplTInv]

theorem unitSpecs_ok {n : ℕ} {Φ : List ETRINV.Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∀ u ∈ (unitSpecs n Φ).1 ++ (unitSpecs n Φ).2, UnitOK n u := by
  intro u hu
  simp only [unitSpecs, List.mem_append, orientR, orientL, List.mem_flatMap, List.mem_map,
    List.mem_range] at hu
  rcases hu with ((⟨i, hi, g, hg, rfl⟩ | ⟨c, hc, hu⟩) | ⟨c, hc, hu⟩) | (⟨i, hi, g, hg, rfl⟩ | ⟨c, hc, hu⟩)
  · refine ⟨rfl, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro σ (rfl | rfl) <;> nlinarith
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
      nlinarith
  · cases c with
    | add a b c =>
      have h := hΦ _ hc
      simp only [ETRINV.Constraint.VarsLt] at h
      simp only [addR, List.mem_singleton] at hu; subst hu
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro σ (rfl | rfl | rfl) <;> omega
      · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
        omega
    | one a => simp [addR] at hu
    | inv a b => simp [addR] at hu
  · cases c with
    | inv a b =>
      have h := hΦ _ hc
      simp only [ETRINV.Constraint.VarsLt] at h
      simp only [invR, List.mem_singleton] at hu; subst hu
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro σ (rfl | rfl) <;> omega
      · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
          List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
        omega
    | one a => simp [invR] at hu
    | add a b c => simp [invR] at hu
  · refine ⟨rfl, ?_, ?_⟩
    · simp only [workSlot, List.mem_cons, List.not_mem_nil, or_false]
      rintro σ (rfl | rfl) <;> omega
    · simp only [workSlot, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
      have : g * n < 3 * n := Nat.mul_lt_mul_of_pos_right hg (by omega)
      omega
  · cases c with
    | add a b c =>
      have h := hΦ _ hc
      simp only [ETRINV.Constraint.VarsLt] at h
      simp only [addL, List.mem_singleton] at hu; subst hu
      refine ⟨rfl, ?_, ?_⟩
      · simp only [workSlot, List.mem_cons, List.not_mem_nil, or_false]
        rintro σ (rfl | rfl | rfl) <;> omega
      · simp only [workSlot, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
          implies_true]
        omega
    | one a => simp [addL] at hu
    | inv a b => simp [addL] at hu

theorem length_flatMap_le (f : ETRINV.Constraint → List UnitSpec) (hf : ∀ c, (f c).length ≤ 1) :
    ∀ Φ : List ETRINV.Constraint, (Φ.flatMap f).length ≤ Φ.length
  | [] => by simp
  | c :: Φ => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := length_flatMap_le f hf Φ; have := hf c; omega

theorem length_add_inv_le (n : ℕ) : ∀ Φ : List ETRINV.Constraint,
    (Φ.flatMap (addR n)).length + (Φ.flatMap (invR n)).length ≤ Φ.length
  | [] => by simp
  | c :: Φ => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := length_add_inv_le n Φ
    cases c <;> simp only [addR, invR, List.length_cons, List.length_nil] <;> omega

theorem length_orientR (n : ℕ) : (orientR n).length = 3 * n := by
  simp [orientR, List.length_flatMap, List.sum_replicate]; ring

theorem length_orientL (n : ℕ) : (orientL n).length = 3 * n := by
  simp [orientL, List.length_flatMap, List.sum_replicate]; ring

theorem length_unitSpecs_fst (n : ℕ) (Φ : List ETRINV.Constraint) :
    (unitSpecs n Φ).1.length ≤ bigN n (numC Φ) := by
  have := length_add_inv_le n Φ
  have : numC Φ = Φ.length := rfl
  have := four_n_add_k_le_bigN (n := n) (k := numC Φ)
  simp only [unitSpecs, List.length_append, length_orientR]
  omega

theorem length_unitSpecs_snd (n : ℕ) (Φ : List ETRINV.Constraint) :
    (unitSpecs n Φ).2.length ≤ bigN n (numC Φ) := by
  have := length_flatMap_le (addL n) (fun c => by cases c <;> simp [addL]) Φ
  have : numC Φ = Φ.length := rfl
  have := four_n_add_k_le_bigN (n := n) (k := numC Φ)
  simp only [unitSpecs, List.length_append, length_orientL]
  omega

/-! ### Good corridor inputs -/

theorem tmplT_ok (k : Kind) : ∀ τ < (tmplT k).length,
    (-50 ≤ ((tmplT k).getD τ (0, 0)).1 ∧ ((tmplT k).getD τ (0, 0)).1 ≤ 50 ∧
      -50 ≤ ((tmplT k).getD τ (0, 0)).2 ∧ ((tmplT k).getD τ (0, 0)).2 ≤ 50) ∧
    ((tmplT k).getD τ (0, 0)).1 + ((tmplT k).getD τ (0, 0)).2 =
      ((tmplT k).getD 0 (0, 0)).1 + ((tmplT k).getD 0 (0, 0)).2 - 27 * τ / 2 := by
  intro τ hτ
  cases k <;> simp only [tmplT, tmplTGE, tmplTLE, tmplTOR, tmplTInv, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;> norm_num [tmplT, tmplTGE, tmplTLE, tmplTOR, tmplTInv]

/-- **The corridor input of an admissible unit is good.** -/
theorem unitInput_good {n k m : ℕ} {u : UnitSpec} (hu : UnitOK n u) (hm : m < bigN n k)
    (hn : 4 * n ≤ bigN n k) : (unitInput n k m u).Good (bigN n k : ℚ) := by
  have hN2 : (2 : ℚ) ≤ bigN n k := by exact_mod_cast two_le_bigN
  have hm' : (m : ℚ) + 1 ≤ bigN n k := by exact_mod_cast hm
  have hn' : (4 * n : ℚ) ≤ bigN n k := by exact_mod_cast hn
  have hlen := length_tmplT u.kind
  have hnp : (unitInput n k m u).np = (tmplT u.kind).length := hu.len
  refine ⟨⟨⟨hN2, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [unitInput, S_cast]
  · simp only [unitInput, unitH]; have : (0 : ℚ) ≤ m := Nat.cast_nonneg m; linarith
  · simp only [unitInput, unitH]; linarith
  · rw [hnp]; omega
  · intro j hj
    have hj0 : j < u.work.length := by simpa [Input.np, unitInput] using hj
    have hσ := hu.lt _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0]
                           exact List.getElem_mem _ : u.work.getD j 0 ∈ u.work)
    have : ((Input.sigma (unitInput n k m u) j : ℕ) : ℚ) + 1 ≤ 4 * n := by
      have : Input.sigma (unitInput n k m u) j + 1 ≤ 4 * n := by
        simp only [Input.sigma, unitInput]; omega
      exact_mod_cast this
    nlinarith
  · intro τ hτ
    exact (tmplT_ok u.kind τ (by rwa [hnp] at hτ)).1
  · intro τ hτ
    exact (tmplT_ok u.kind τ (by rwa [hnp] at hτ)).2
  · rw [hnp]; omega
  · intro j hj
    have hm := hu.mono
    rw [List.pairwise_iff_getElem] at hm
    have hj' : j + 1 < u.work.length := by simpa [Input.np, unitInput] using hj
    have := hm j (j + 1) (by omega) hj' (by omega)
    simp only [Input.sigma, unitInput, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
      List.getElem?_eq_getElem (show j < u.work.length by omega), Option.getD_some]
    exact this

/-! ### The main theorem -/

theorem unitChain_feature {n k m : ℕ} {u : UnitSpec} (hu : UnitOK n u) (hm : m < bigN n k)
    (hn : 4 * n ≤ bigN n k) :
    UnitFeature (S n k : ℝ) ((S n k : ℝ) + 3 * m + 1)
      (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ) ((unitChain n k m u).map ratPoint) := by
  have h := unit_feature (unitInput_good hu hm hn) u.kind
  have e1 : (((unitInput n k m u).S : ℚ) : ℝ) = (S n k : ℝ) := by simp [unitInput]
  have e2 : (((unitInput n k m u).H : ℚ) : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
    simp [unitInput, unitH]
  rw [e1, e2] at h
  exact h

theorem ratPoint_triangle_ccw :
    (Polygon.mk (triangle0.map ratPoint)).Simple ∧
      (Polygon.mk (triangle0.map ratPoint)).InteriorLeft := by
  have hs : (Polygon.mk (triangle0.map ratPoint)).Simple :=
    Irrational.simple_of_simpleCheck (by decide +kernel)
  refine ⟨hs, Polygon.interiorLeft_of_supporting_edge hs (i := 0) (by decide) ?_⟩
  intro j hj
  have hj' : j < 3 := hj
  interval_cases j <;> simp [triangle0, Polygon.vtx, Polygon.n, ratPoint, det]

/-- **The global facts** for `n ≥ 1`: the polygon is simple and counter-clockwise; right of
`x = S` its boundary consists of the right unit chains, left of `x = X_L` of the (mirrored) left
unit chains; it lies below `y = S + 3N`. -/
theorem construct_global {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) :
    (Polygon.mk ((construct Φ n).map ratPoint)).Simple ∧
      (Polygon.mk ((construct Φ n).map ratPoint)).InteriorLeft ∧
      (∀ p ∈ (Polygon.mk ((construct Φ n).map ratPoint)).boundary,
        p.1 ≤ (S n (numC Φ) : ℝ) ∨
          ∃ f ∈ sideChainsR n (numC Φ) (unitSpecs n Φ).1, p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((construct Φ n).map ratPoint)).boundary,
        54 * (n : ℝ) - 12 - (S n (numC Φ) : ℝ) ≤ p.1 ∨
          ∃ f ∈ sideChainsR n (numC Φ) (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((construct Φ n).map ratPoint)).boundary,
        p.2 ≤ (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
  rw [construct_pos (by omega)]
  have hok := unitSpecs_ok hΦ
  have hNn := four_n_le_bigN (n := n) (k := numC Φ)
  have hρ : (0 : ℝ) < (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) := by
    have := S_pos_q (n := n) (k := numC Φ)
    have : (0 : ℚ) < Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) := by
      simp only [Corridor.rho]; positivity
    exact_mod_cast this
  have hρ1 : (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) < 1 / 100 := by
    have := S_ge (n := n) (k := numC Φ)
    have h8 : (800000 : ℚ) ≤ ((S n (numC Φ) : ℕ) : ℚ) := by exact_mod_cast this
    have : Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) < 1 / 100 := by
      simp only [Corridor.rho]; rw [div_lt_iff₀ (by positivity)]; linarith
    calc _ < ((1 / 100 : ℚ) : ℝ) := Rat.cast_lt.2 this
      _ = 1 / 100 := by norm_num
  have side : ∀ (us : List UnitSpec), (∀ u ∈ us, UnitOK n u) → us.length ≤ bigN n (numC Φ) →
      ∀ j (hj : j < (sideChainsR n (numC Φ) us).length),
        UnitFeature (S n (numC Φ) : ℝ) ((S n (numC Φ) : ℝ) + 3 * j + 1)
          (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) (sideChainsR n (numC Φ) us)[j] := by
    intro us hus hlen j hj
    have hj' : j < us.length := by simpa [sideChainsR, length_unitChains] using hj
    simp only [sideChainsR, List.getElem_map]
    rw [getElem_unitChains, Nat.zero_add]
    exact unitChain_feature (hus _ (List.getElem_mem _)) (by omega) hNn
  exact global_simple hn hρ hρ1
    (side _ (fun u hu => hok u (List.mem_append_left _ hu)) (length_unitSpecs_fst n Φ))
    (side _ (fun u hu => hok u (List.mem_append_right _ hu)) (length_unitSpecs_snd n Φ))
    (length_unitSpecs_fst n Φ) (length_unitSpecs_snd n Φ)

/-- **The polygon of the reduction is simple and counter-clockwise** (08 §4). -/
theorem construct_simple {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    (Polygon.mk ((construct Φ n).map ratPoint)).Simple ∧
      (Polygon.mk ((construct Φ n).map ratPoint)).InteriorLeft := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [construct_zero]; exact ratPoint_triangle_ccw
  obtain ⟨h1, h2, -⟩ := construct_global hΦ hn
  exact ⟨h1, h2⟩

end ArtGallery.Sec5

end
