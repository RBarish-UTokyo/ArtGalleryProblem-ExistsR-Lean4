module

public import ArtGallery.Hardness.Sec5.Assemble.TmplData
public import ArtGallery.Hardness.Sec5.Assemble.Glue

/-!
# Section 5: the placed template chains (simplicity and position)

Kernel-checked facts about the fixed template chains `tmplV k` (integer template coordinates,
`TmplData.lean`) and their consequences for the placed chain `φ(tmplV k)`, where
`φ(V) = (S + 3, H − 1) + V/(D S)` (`tmplMap`, a similarity) is the placement `m + T/S` of the
template point `T = V/D`:

* (T-simple) the template chain closed by the stub `tmplStub` (the stub of `Templates/*Data.lean`)
  passes the integer simplicity checker, hence the placed chain is a simple chain
  (`tmplPlaced_simple`);
* (box) all template coordinates are at most `50` in absolute value, so the placed chain lies in
  the box `[S + 3 − 50/S, S + 3 + 50/S] × [H − 1 − 50/S, H − 1 + 50/S]` (`tmplPlaced_box`);
* (walls) every template edge lies right of the first vertex `V₀` or below it, and right of the
  last vertex `V_l` or below it (`quadOK`): the channel walls `c1 → φ(V₀)` and `φ(V_l) → d1`, which
  leave `φ(V₀)`, `φ(V_l)` towards the upper left, meet the placed chain only there
  (`tmplPlaced_quadFst`, `tmplPlaced_quadLst`);
* (window) `V₀.x + V₀.y ≤ 0 < V_l.x + V_l.y`: the two walls are separated by the lines of slope
  `−1` (`tmplPlaced_sumFst`, `tmplPlaced_sumLst`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### Integer checks -/

/-- The stub closing the template chain to a polygon (as in `Templates/*Data.lean`). -/
def tmplStub : Kind → List (ℤ × ℤ)
  | .ge => [((-8319720000), 8361318600), ((-8319720000), 4950233400)]
  | .le => [((-2473800000), 2486169000), ((-2473800000), 1533756000)]
  | .orient => [((-14887920000), 14962359600), ((-14887920000), 8858312400)]
  | .inv => [((-50149579040000), 59571964708300), ((-50149579040000), 49898831144800)]

/-- The template polygon: the chain closed by the stub. -/
def tmplVT (k : Kind) : List (ℤ × ℤ) := tmplV k ++ tmplStub k

/-- The first template vertex `V₀`. -/
def tmplFst (k : Kind) : ℤ × ℤ := (tmplV k).headD (0, 0)

/-- The last template vertex `V_l`. -/
def tmplLst (k : Kind) : ℤ × ℤ := (tmplV k).getLastD (0, 0)

/-- All points lie in the square `[−B, B]²`. -/
def boxOK (B : ℤ) : List (ℤ × ℤ) → Bool
  | [] => true
  | p :: l => decide (-B ≤ p.1 ∧ p.1 ≤ B ∧ -B ≤ p.2 ∧ p.2 ≤ B) && boxOK B l

/-- Every edge has both ends weakly right of `P` or both ends weakly below `P`. -/
def quadOK (P : ℤ × ℤ) : List (ℤ × ℤ) → Bool
  | a :: b :: l => ((decide (P.1 ≤ a.1) && decide (P.1 ≤ b.1)) ||
      (decide (a.2 ≤ P.2) && decide (b.2 ≤ P.2))) && quadOK P (b :: l)
  | _ => true

/-- (T-simple) The template polygon passes the integer simplicity checker. -/
theorem tmpl_simpleCheck (k : Kind) : Vis.Cert.simpleCheck (tmplVT k) = true := by
  cases k <;> decide +kernel

/-- (box) All template coordinates are at most `50 D` in absolute value. -/
theorem tmpl_boxOK (k : Kind) : boxOK (50 * (tmplD k : ℤ)) (tmplV k) = true := by
  cases k <;> decide +kernel

/-- (walls) Every template edge is right of or below the first vertex. -/
theorem tmpl_quadFst (k : Kind) : quadOK (tmplFst k) (tmplV k) = true := by
  cases k <;> decide +kernel

/-- (walls) Every template edge is right of or below the last vertex. -/
theorem tmpl_quadLst (k : Kind) : quadOK (tmplLst k) (tmplV k) = true := by
  cases k <;> decide +kernel

/-- (window) `V₀.x + V₀.y ≤ 0`. -/
theorem tmpl_sumFst (k : Kind) : (tmplFst k).1 + (tmplFst k).2 ≤ 0 := by
  cases k <;> decide +kernel

/-- (window) `V_l.x + V_l.y > 0`. -/
theorem tmpl_sumLst (k : Kind) : 0 < (tmplLst k).1 + (tmplLst k).2 := by
  cases k <;> decide +kernel

theorem tmpl_length (k : Kind) : 3 ≤ (tmplV k).length := by
  cases k <;> decide +kernel

theorem tmplD_pos (k : Kind) : 0 < tmplD k := by cases k <;> decide

/-! ### From the checks to real statements -/

theorem boxOK_mem {B : ℤ} : ∀ {l : List (ℤ × ℤ)}, boxOK B l = true → ∀ p ∈ l,
    -B ≤ p.1 ∧ p.1 ≤ B ∧ -B ≤ p.2 ∧ p.2 ≤ B
  | [], _, p, hp => by simp at hp
  | q :: l, h, p, hp => by
    simp only [boxOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact boxOK_mem h.2 p hp

theorem pairsIn_of_quadOK {P : ℤ × ℤ} : ∀ {l : List (ℤ × ℤ)}, quadOK P l = true →
    PairsIn {q : Point | (-1) * q.1 + 0 * q.2 ≤ -(P.1 : ℝ)} {q : Point | 0 * q.1 + 1 * q.2 ≤ (P.2 : ℝ)}
      (l.map intPoint)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    simp only [quadOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, pairsIn_of_quadOK h.2⟩
    simp only [intPoint, mem_ofPred_eq]
    rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h1' : (P.1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast h1
      have h2' : (P.1 : ℝ) ≤ (b.1 : ℝ) := by exact_mod_cast h2
      exact ⟨by linarith, by linarith⟩
    · right
      have h1' : (a.2 : ℝ) ≤ (P.2 : ℝ) := by exact_mod_cast h1
      have h2' : (b.2 : ℝ) ≤ (P.2 : ℝ) := by exact_mod_cast h2
      exact ⟨by linarith, by linarith⟩

/-- The scale factor `1/(D S)` of the placement is nonzero. -/
theorem tmplScale_ne {k : Kind} {S : ℝ} (hS : S ≠ 0) : 1 / ((tmplD k : ℝ) * S) ≠ 0 := by
  have : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  exact one_div_ne_zero (mul_ne_zero this.ne' hS)

/-- The placement `V ↦ (S + 3, H − 1) + V/(D S)` of integer template points. -/
noncomputable def tmplMap (k : Kind) (S H : ℝ) (hS : S ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  Vis.Cert.simil (1 / ((tmplD k : ℝ) * S)) (tmplScale_ne hS) (S + 3, H - 1)

theorem tmplMap_apply (k : Kind) {S H : ℝ} (hS : S ≠ 0) (p : Point) :
    tmplMap k S H hS p = (S + 3 + p.1 / ((tmplD k : ℝ) * S), H - 1 + p.2 / ((tmplD k : ℝ) * S)) := by
  simp only [tmplMap, Vis.Cert.simil_apply]
  ext <;> simp <;> ring

/-- The placed template chain (real points). -/
noncomputable def tmplPlaced (k : Kind) (S H : ℝ) (hS : S ≠ 0) : List Point :=
  (tmplV k).map fun V => tmplMap k S H hS (intPoint V)

section Placed

variable (k : Kind) {S H : ℝ} (hS : 1000 ≤ S)

theorem S_ne_of (hS : 1000 ≤ S) : S ≠ 0 := by intro h; rw [h] at hS; norm_num at hS

include hS

theorem tmplPlaced_eq : tmplPlaced k S H (S_ne_of hS) =
    ((tmplV k).map intPoint).map (tmplMap k S H (S_ne_of hS)) := by
  simp [tmplPlaced, List.map_map, Function.comp_def]

theorem tmplPlaced_length : 3 ≤ (tmplPlaced k S H (S_ne_of hS)).length := by
  simpa [tmplPlaced] using tmpl_length k

/-- **The placed template chain is simple.** -/
theorem tmplPlaced_simple : ChainSimple (tmplPlaced k S H (S_ne_of hS)) := by
  have hP := Vis.Cert.simple_of_simpleCheck (tmpl_simpleCheck k)
  have hP' := Hardening.Invariance.simple_mapPoly (tmplMap k S H (S_ne_of hS)) _ hP
  simp only [Hardening.Invariance.mapPoly, tmplVT, List.map_append] at hP'
  rw [tmplPlaced_eq k hS]
  exact chainSimple_of_simple hP'

theorem tmplPlaced_mem {p : Point} (hp : p ∈ chainSet (tmplPlaced k S H (S_ne_of hS))) :
    ∃ q ∈ chainSet ((tmplV k).map intPoint), p = tmplMap k S H (S_ne_of hS) q := by
  rw [tmplPlaced_eq k hS, chainSet_map] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  exact ⟨q, hq, hqp.symm⟩

omit hS in
theorem tmpl_box_int {q : Point} (hq : q ∈ chainSet ((tmplV k).map intPoint)) :
    -(50 * (tmplD k : ℝ)) ≤ q.1 ∧ q.1 ≤ 50 * (tmplD k : ℝ) ∧
      -(50 * (tmplD k : ℝ)) ≤ q.2 ∧ q.2 ≤ 50 * (tmplD k : ℝ) := by
  have hb := boxOK_mem (tmpl_boxOK k)
  have hv : ∀ p ∈ (tmplV k).map intPoint, -(50 * (tmplD k : ℝ)) ≤ p.1 ∧ p.1 ≤ 50 * (tmplD k : ℝ) ∧
      -(50 * (tmplD k : ℝ)) ≤ p.2 ∧ p.2 ≤ 50 * (tmplD k : ℝ) := by
    intro p hp
    obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hp
    obtain ⟨a1, a2, a3, a4⟩ := hb V hV
    simp only [intPoint]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : ((-(50 * (tmplD k : ℤ)) : ℤ) : ℝ) ≤ (V.1 : ℝ) := by exact_mod_cast a1
      push_cast at this; linarith
    · have : ((V.1 : ℤ) : ℝ) ≤ ((50 * (tmplD k : ℤ) : ℤ) : ℝ) := by exact_mod_cast a2
      push_cast at this; linarith
    · have : ((-(50 * (tmplD k : ℤ)) : ℤ) : ℝ) ≤ (V.2 : ℝ) := by exact_mod_cast a3
      push_cast at this; linarith
    · have : ((V.2 : ℤ) : ℝ) ≤ ((50 * (tmplD k : ℤ) : ℤ) : ℝ) := by exact_mod_cast a4
      push_cast at this; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := 50 * (tmplD k : ℝ))
      (fun p hp => by have := (hv p hp).1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := 50 * (tmplD k : ℝ))
      (fun p hp => by have := (hv p hp).2.1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 0) (β := -1) (c := 50 * (tmplD k : ℝ))
      (fun p hp => by have := (hv p hp).2.2.1; linarith) q hq
    linarith
  · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := 50 * (tmplD k : ℝ))
      (fun p hp => by have := (hv p hp).2.2.2; linarith) q hq
    linarith

/-- **Position of the placed template.** -/
theorem tmplPlaced_box {p : Point} (hp : p ∈ chainSet (tmplPlaced k S H (S_ne_of hS))) :
    S + 3 - 50 / S ≤ p.1 ∧ p.1 ≤ S + 3 + 50 / S ∧ H - 1 - 50 / S ≤ p.2 ∧ p.2 ≤ H - 1 + 50 / S := by
  obtain ⟨q, hq, rfl⟩ := tmplPlaced_mem k hS hp
  obtain ⟨b1, b2, b3, b4⟩ := tmpl_box_int k hq
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  rw [tmplMap_apply]
  have e : ∀ x : ℝ, x / ((tmplD k : ℝ) * S) = (x / (tmplD k : ℝ)) / S := fun x => by
    field_simp
  have hb : ∀ x : ℝ, -(50 * (tmplD k : ℝ)) ≤ x → x ≤ 50 * (tmplD k : ℝ) →
      -(50 / S) ≤ x / ((tmplD k : ℝ) * S) ∧ x / ((tmplD k : ℝ) * S) ≤ 50 / S := by
    intro x h1 h2
    rw [e]
    have h1' : -50 ≤ x / (tmplD k : ℝ) := by rw [le_div_iff₀ hD]; linarith
    have h2' : x / (tmplD k : ℝ) ≤ 50 := by rw [div_le_iff₀ hD]; linarith
    constructor
    · rw [neg_div', div_le_div_iff_of_pos_right hS0]; linarith
    · exact div_le_div_of_nonneg_right h2' hS0.le
  obtain ⟨c1, c2⟩ := hb _ b1 b2
  obtain ⟨c3, c4⟩ := hb _ b3 b4
  simp only
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem tmplPlaced_fst : fstPt (tmplPlaced k S H (S_ne_of hS)) =
    tmplMap k S H (S_ne_of hS) (intPoint (tmplFst k)) := by
  have hne : tmplV k ≠ [] := by cases k <;> simp [tmplV, tmplVGE, tmplVLE, tmplVOR, tmplVInv]
  obtain ⟨a, l, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [tmplPlaced, tmplFst, he]
  rfl

theorem tmplPlaced_lst : lstPt (tmplPlaced k S H (S_ne_of hS)) =
    tmplMap k S H (S_ne_of hS) (intPoint (tmplLst k)) := by
  have hne : tmplV k ≠ [] := by cases k <;> simp [tmplV, tmplVGE, tmplVLE, tmplVOR, tmplVInv]
  unfold tmplPlaced tmplLst lstPt
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map,
    List.getLast?_eq_some_getLast hne]
  rfl

/-- The coordinate-wise monotone placement. -/
theorem tmplMap_le_iff {a b : ℝ} : a / ((tmplD k : ℝ) * S) ≤ b / ((tmplD k : ℝ) * S) ↔ a ≤ b := by
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  exact div_le_div_iff_of_pos_right (by positivity)

theorem tmplPlaced_quad {P : ℤ × ℤ} (hq : quadOK P (tmplV k) = true) {p : Point}
    (hp : p ∈ chainSet (tmplPlaced k S H (S_ne_of hS))) :
    (tmplMap k S H (S_ne_of hS) (intPoint P)).1 ≤ p.1 ∨
      p.2 ≤ (tmplMap k S H (S_ne_of hS) (intPoint P)).2 := by
  obtain ⟨q, hq', rfl⟩ := tmplPlaced_mem k hS hp
  have := chainSet_subset_union (convex_halfplane _ _ _) (convex_halfplane _ _ _)
    (pairsIn_of_quadOK hq) hq'
  rw [tmplMap_apply, tmplMap_apply]
  simp only [intPoint, mem_union, mem_ofPred_eq] at this ⊢
  rcases this with h | h
  · left
    have : (P.1 : ℝ) ≤ q.1 := by linarith
    have := (tmplMap_le_iff k hS).2 this
    linarith
  · right
    have : q.2 ≤ (P.2 : ℝ) := by linarith
    have := (tmplMap_le_iff k hS).2 this
    linarith

theorem tmplPlaced_fst_mem : tmplMap k S H (S_ne_of hS) (intPoint (tmplFst k)) ∈
    chainSet (tmplPlaced k S H (S_ne_of hS)) := by
  rw [← tmplPlaced_fst k hS]
  exact fstPt_mem (by have := tmplPlaced_length k hS (H := H); omega)

theorem tmplPlaced_lst_mem : tmplMap k S H (S_ne_of hS) (intPoint (tmplLst k)) ∈
    chainSet (tmplPlaced k S H (S_ne_of hS)) := by
  rw [← tmplPlaced_lst k hS]
  exact lstPt_mem (by have := tmplPlaced_length k hS (H := H); omega)

end Placed

end ArtGallery.Sec5

end
