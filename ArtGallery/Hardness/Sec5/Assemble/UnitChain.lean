module

public import ArtGallery.Hardness.Sec5.Assemble.Construct
public import ArtGallery.Hardness.Sec5.Assemble.TmplFacts
public import ArtGallery.Hardness.Sec5.Assemble.Comb
public import ArtGallery.Hardness.Sec5.Corridor.Poly

/-!
# Section 5: the chain of one unit is simple (08 §4, Lemma S4)

For a good corridor input `I` (`Corridor.Input.Good`) and a template kind `k`, the unit chain
```
F = c0, floor…, c1      LW = [c1, φ(V₀)]      T = φ(template)      UW = [φ(V_l), d1]
U = d1, upper wall…, d0
```
(`(I.chainBefore ++ placedTmpl I k ++ I.chainAfter).map ratPoint`) is a simple chain
(`unit_feature`).  The pieces are separated as follows (`S`, `H` of `I`, `ρ = 3/(2S)`):
* `F` lies in `[S, S + 2] × [H − 1/4, H]` and reaches `x = S + 2` only at `c1`, `x = S` only at
  `c0`; `U` lies in `[S, S + 2] × [H + ρ, H + 3/2]` and reaches `x = S` only at `d0`;
* `T` lies in the box of radius `50/S` around `m = (S + 3, H − 1)`;
* the walls leave `φ(V₀)`, `φ(V_l)` towards the upper left, where the template has no point
  (`tmplPlaced_quadFst/Lst`), and they are separated by the line `x + y = S + H + 2`.

The result is packaged as `UnitFeature S H ρ f`: a simple chain from `(S, H)` to `(S, H + 2ρ)`,
strictly right of `x = S` except at its two ends, inside `[S, S + 4] × [H − 1 − 1/100, H + 3/2]` —
exactly what the global comb argument needs.
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open Corridor (Input place)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

namespace Corridor.Input

variable {I : Input} {N : ℚ}

theorem Good.S_ge_real (hg : I.Good N) : (800000 : ℝ) ≤ I.S := by
  have : (800000 : ℚ) ≤ I.S := hg.scale.S_ge
  have : ((800000 : ℚ) : ℝ) ≤ (I.S : ℝ) := by exact_mod_cast this
  push_cast at this; linarith

theorem Good.floor_ne_nil (hg : I.Good N) : I.floor ≠ [] := by
  have h1 := hg.np_pos
  have h3 := hg.np_le
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with h | h | h
  · rw [floor_eq_one hg h]; simp [slot2]
  · rw [floor_eq_two hg h]; simp [slot2]
  · rw [floor_eq_three hg h]; simp [slot2]

theorem Good.upper_ne_nil (hg : I.Good N) : I.upper ≠ [] := by
  have h0 : 0 < I.np := by have := hg.np_pos; omega
  simp only [upper, ne_eq, List.flatMap_eq_nil_iff, List.mem_range, not_forall]
  exact ⟨0, h0, by simp [upperPair]⟩

end Corridor.Input

/-- The placed template in real coordinates. -/
theorem placedTmpl_map (I : Input) (k : Kind) (hS : (1000 : ℝ) ≤ I.S) :
    (placedTmpl I k).map ratPoint = tmplPlaced k (I.S : ℝ) (I.H : ℝ) (S_ne_of hS) := by
  simp only [placedTmpl, tmplPlaced, List.map_map]
  apply List.map_congr_left
  intro V _
  have hS0 : (I.S : ℝ) ≠ 0 := S_ne_of hS
  have hD : (tmplD k : ℝ) ≠ 0 := by exact_mod_cast (tmplD_pos k).ne'
  simp only [Function.comp, tmplMap_apply, ratPoint, place, tmplPt, intPoint]
  push_cast
  ext <;> simp only <;> field_simp

section Unit

variable {I : Input} {N : ℚ} (hg : I.Good N) (k : Kind)
include hg

/-- **The unit chain is a simple chain hanging right of `x = S`.** -/
theorem unit_feature :
    UnitFeature (I.S : ℝ) (I.H : ℝ) I.rhoR
      ((I.chainBefore ++ placedTmpl I k ++ I.chainAfter).map ratPoint) := by
  have hS8 := hg.S_ge_real
  have hS : (1000 : ℝ) ≤ I.S := by linarith
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  set S : ℝ := (I.S : ℝ) with hSdef
  set H : ℝ := (I.H : ℝ) with hHdef
  set ρ := I.rhoR
  have hS0 : (0 : ℝ) < S := by linarith
  have he : 50 / S ≤ 1 / 1000 := by rw [div_le_iff₀ hS0]; linarith
  have he0 : 0 < 50 / S := by positivity
  set c0R : Point := (S, H)
  set c1R : Point := (S + 2, H)
  set d1R : Point := (S + 2, H + ρ)
  set d0R : Point := (S, H + 2 * ρ)
  set Fl := I.floor.map ratPoint
  set Up := I.upper.map ratPoint
  set T := tmplPlaced k S H (S_ne_of hS)
  set a0 := tmplMap k S H (S_ne_of hS) (intPoint (tmplFst k))
  set al := tmplMap k S H (S_ne_of hS) (intPoint (tmplLst k))
  have hFl0 : Fl ≠ [] := by simpa [Fl] using hg.floor_ne_nil
  have hUp0 : Up ≠ [] := by simpa [Up] using hg.upper_ne_nil
  -- the three pieces
  have hCB : I.chainBefore.map ratPoint = c0R :: Fl ++ [c1R] := by
    simp [chainBefore, ratPoint_c0', ratPoint_c1', c0R, c1R, Fl]
    exact ⟨rfl, rfl⟩
  have hCA : I.chainAfter.map ratPoint = d1R :: Up ++ [d0R] := by
    simp [chainAfter, ratPoint_d1', ratPoint_d0', d1R, d0R, Up]
    exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  have hT : (placedTmpl I k).map ratPoint = T := placedTmpl_map I k hS
  have hTs : ChainSimple T := tmplPlaced_simple k hS
  have hTl : 3 ≤ T.length := tmplPlaced_length k hS
  have hTf : fstPt T = a0 := tmplPlaced_fst k hS
  have hTla : lstPt T = al := tmplPlaced_lst k hS
  obtain ⟨T', hT'⟩ : ∃ T', T = a0 :: T' ++ [al] := by
    have h2 : 2 ≤ T.length := by omega
    refine ⟨T.tail.dropLast, ?_⟩
    have := decomp_of_two_le h2
    rw [hTf, hTla] at this
    exact this
  have hFs : ChainSimple (c0R :: Fl ++ [c1R]) := by
    rw [← hCB]; exact chainSimple_of_corridor hg.chainSimple_chainBefore
  have hUs : ChainSimple (d1R :: Up ++ [d0R]) := by
    rw [← hCA]; exact chainSimple_of_corridor hg.chainSimple_chainAfter
  -- positions of the template ends
  have hD : (0 : ℝ) < tmplD k := by exact_mod_cast tmplD_pos k
  have hDS : (0 : ℝ) < (tmplD k : ℝ) * S := by positivity
  have hTbox : ∀ {p : Point}, p ∈ chainSet T → S + 3 - 50 / S ≤ p.1 ∧ p.1 ≤ S + 3 + 50 / S ∧
      H - 1 - 50 / S ≤ p.2 ∧ p.2 ≤ H - 1 + 50 / S := fun hp => tmplPlaced_box k hS hp
  have ha0mem : a0 ∈ chainSet T := by rw [← hTf]; exact fstPt_mem (by omega)
  have halmem : al ∈ chainSet T := by rw [← hTla]; exact lstPt_mem (by omega)
  have ha0b := hTbox ha0mem
  have halb := hTbox halmem
  have hsum0 : a0.1 + a0.2 ≤ S + H + 2 := by
    have h := tmpl_sumFst k
    have h' : ((tmplFst k).1 : ℝ) + ((tmplFst k).2 : ℝ) ≤ 0 := by exact_mod_cast h
    simp only [a0, tmplMap_apply, intPoint]
    have : ((tmplFst k).1 : ℝ) / ((tmplD k : ℝ) * S) + ((tmplFst k).2 : ℝ) / ((tmplD k : ℝ) * S) ≤ 0 := by
      rw [← add_div]; exact div_nonpos_of_nonpos_of_nonneg h' hDS.le
    linarith
  have hsuml : S + H + 2 < al.1 + al.2 := by
    have h := tmpl_sumLst k
    have h' : (0 : ℝ) < ((tmplLst k).1 : ℝ) + ((tmplLst k).2 : ℝ) := by exact_mod_cast h
    simp only [al, tmplMap_apply, intPoint]
    have : 0 < ((tmplLst k).1 : ℝ) / ((tmplD k : ℝ) * S) + ((tmplLst k).2 : ℝ) / ((tmplD k : ℝ) * S) := by
      rw [← add_div]; exact div_pos h' hDS
    linarith
  have hquad0 : ∀ p ∈ chainSet T, a0.1 ≤ p.1 ∨ p.2 ≤ a0.2 :=
    fun p hp => tmplPlaced_quad k hS (tmpl_quadFst k) hp
  have hquadl : ∀ p ∈ chainSet T, al.1 ≤ p.1 ∨ p.2 ≤ al.2 :=
    fun p hp => tmplPlaced_quad k hS (tmpl_quadLst k) hp
  -- the floor
  have hFv : ∀ v ∈ Fl, S + 1 / 4 ≤ v.1 ∧ v.1 ≤ S + 15 / 8 ∧ H - 1 / 4 ≤ v.2 ∧ v.2 ≤ H :=
    fun v hv => hg.floor_box v hv
  have hFall : ∀ v ∈ c0R :: Fl ++ [c1R], S ≤ v.1 ∧ v.1 ≤ S + 2 ∧ H - 1 / 4 ≤ v.2 ∧ v.2 ≤ H := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · simp [c0R]
    · obtain ⟨a, b, c, d⟩ := hFv v hv; exact ⟨by linarith, by linarith, c, d⟩
    · simp [c1R]
  have hF1 : ∀ p ∈ chainSet (c0R :: Fl ++ [c1R]),
      S ≤ p.1 ∧ p.1 ≤ S + 2 ∧ H - 1 / 4 ≤ p.2 ∧ p.2 ≤ H := by
    intro p hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := -S)
        (fun v hv => by have := (hFall v hv).1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := S + 2)
        (fun v hv => by have := (hFall v hv).2.1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 0) (β := -1) (c := -(H - 1 / 4))
        (fun v hv => by have := (hFall v hv).2.2.1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := H)
        (fun v hv => by have := (hFall v hv).2.2.2; linarith) p hp; linarith
  have hFr : ∀ p ∈ chainSet (c0R :: Fl ++ [c1R]), S + 2 ≤ p.1 → p = c1R := by
    intro p hp hx
    rcases chainSet_lt_or_ends (α := 1) (β := 0) (c := S + 2) hFl0 (by simp [c0R])
      (by norm_num [c1R]) (fun v hv => by have := (hFv v hv).2.1; linarith) p hp with h | h | h
    · linarith
    · exfalso; rw [h] at hx; simp only [c0R] at hx; linarith
    · exact h
  have hFlft : ∀ p ∈ chainSet (c0R :: Fl ++ [c1R]), p.1 ≤ S → p = c0R := by
    intro p hp hx
    rcases chainSet_lt_or_ends (α := -1) (β := 0) (c := -S) hFl0 (by simp [c0R])
      (by norm_num [c1R]) (fun v hv => by have := (hFv v hv).1; linarith) p hp with h | h | h
    · linarith
    · exact h
    · exfalso; rw [h] at hx; simp only [c1R] at hx; linarith
  -- the upper wall
  have hUv := hg.upper_box'
  have hUall : ∀ v ∈ d1R :: Up ++ [d0R], S ≤ v.1 ∧ v.1 ≤ S + 2 ∧ H + ρ ≤ v.2 ∧ v.2 ≤ H + 3 / 2 := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · simp [d1R]; linarith
    · obtain ⟨a, b, c, d, -⟩ := hUv v hv; exact ⟨a.le, b, c.le, d⟩
    · simp [d0R]; constructor <;> linarith
  have hU1 : ∀ p ∈ chainSet (d1R :: Up ++ [d0R]),
      S ≤ p.1 ∧ p.1 ≤ S + 2 ∧ H + ρ ≤ p.2 ∧ p.2 ≤ H + 3 / 2 := by
    intro p hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := -S)
        (fun v hv => by have := (hUall v hv).1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := S + 2)
        (fun v hv => by have := (hUall v hv).2.1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 0) (β := -1) (c := -(H + ρ))
        (fun v hv => by have := (hUall v hv).2.2.1; linarith) p hp; linarith
    · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := H + 3 / 2)
        (fun v hv => by have := (hUall v hv).2.2.2; linarith) p hp; linarith
  have hUlft : ∀ p ∈ chainSet (d1R :: Up ++ [d0R]), p.1 ≤ S → p = d0R := by
    intro p hp hx
    rcases chainSet_lt_or_ends (α := -1) (β := 0) (c := -S) hUp0 (by simp only [d1R]; linarith)
      (by simp [d0R]) (fun v hv => by have := (hUv v hv).1; linarith) p hp with h | h | h
    · linarith
    · rw [h] at hx; simp [d1R] at hx; linarith
    · exact h
  -- the lower wall `LW = [c1, a0]`
  have hLW : ∀ p ∈ ArtGallery.segment c1R a0, S + 2 ≤ p.1 ∧ p.2 ≤ H ∧
      H - 1 - 1 / 1000 ≤ p.2 ∧ p.1 ≤ S + 4 ∧ p.1 + p.2 ≤ S + H + 2 ∧
      (p.1 ≤ S + 2 → p = c1R) ∧ (p ≠ a0 → p.1 < a0.1 ∧ a0.2 < p.2) := by
    intro p hp
    have hsub := fun α β c (h1 : α * c1R.1 + β * c1R.2 ≤ c) (h2 : α * a0.1 + β * a0.2 ≤ c) =>
      Geometry.segment_subset_of_convex (convex_halfplane α β c) h1 h2 hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hsub (-1) 0 (-(S + 2)) (by norm_num [c1R]) (by simp; linarith [ha0b.1])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 1 H (by norm_num [c1R]) (by simp; linarith [ha0b.2.2.2])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 (-1) (-(H - 1 - 1 / 1000)) (by simp [c1R]; linarith)
        (by simp; linarith [ha0b.2.2.1])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 1 0 (S + 4) (by norm_num [c1R]) (by simp; linarith [ha0b.2.1])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 1 1 (S + H + 2) (by simp [c1R]; linarith) (by linarith)
      simp only [mem_ofPred_eq] at this; linarith
    · intro hx
      rcases seg_lt_or_left (α := -1) (β := 0) (c := -(S + 2)) (by norm_num [c1R])
        (by simp; linarith [ha0b.1]) hp with h | h
      · linarith
      · exact h
    · intro hne
      constructor
      · rcases seg_lt_or_right (α := 1) (β := 0) (c := a0.1) (by simp [c1R]; linarith [ha0b.1])
          (by simp) hp with h | h
        · linarith
        · exact absurd h hne
      · rcases seg_lt_or_right (α := 0) (β := -1) (c := -a0.2)
          (by simp [c1R]; linarith [ha0b.2.2.2]) (by simp) hp with h | h
        · linarith
        · exact absurd h hne
  -- the upper wall `UW = [al, d1]`
  have hUW : ∀ p ∈ ArtGallery.segment al d1R, S + 2 ≤ p.1 ∧ H - 1 - 1 / 1000 ≤ p.2 ∧
      p.2 ≤ H + ρ ∧ p.1 ≤ S + 4 ∧ S + H + 2 < p.1 + p.2 ∧
      (p.1 ≤ S + 2 → p = d1R) ∧ (p ≠ al → p.1 < al.1 ∧ al.2 < p.2) := by
    intro p hp
    have hsub := fun α β c (h1 : α * al.1 + β * al.2 ≤ c) (h2 : α * d1R.1 + β * d1R.2 ≤ c) =>
      Geometry.segment_subset_of_convex (convex_halfplane α β c) h1 h2 hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hsub (-1) 0 (-(S + 2)) (by simp; linarith [halb.1]) (by norm_num [d1R])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 (-1) (-(H - 1 - 1 / 1000)) (by simp; linarith [halb.2.2.1])
        (by simp [d1R]; linarith)
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 0 1 (H + ρ) (by simp; linarith [halb.2.2.2]) (by norm_num [d1R])
      simp only [mem_ofPred_eq] at this; linarith
    · have := hsub 1 0 (S + 4) (by simp; linarith [halb.2.1]) (by norm_num [d1R])
      simp only [mem_ofPred_eq] at this; linarith
    · rcases seg_lt_or_right (α := -1) (β := -1) (c := -(S + H + 2)) (by linarith)
        (by simp [d1R]; linarith) hp with h | h
      · linarith
      · rw [h]; simp [d1R]; linarith
    · intro hx
      rcases seg_lt_or_right (α := -1) (β := 0) (c := -(S + 2)) (by simp; linarith [halb.1])
        (by norm_num [d1R]) hp with h | h
      · linarith
      · exact h
    · intro hne
      constructor
      · rcases seg_lt_or_left (α := 1) (β := 0) (c := al.1) (by simp)
          (by simp [d1R]; linarith [halb.1]) hp with h | h
        · linarith
        · exact absurd h hne
      · rcases seg_lt_or_left (α := 0) (β := -1) (c := -al.2) (by simp)
          (by simp [d1R]; linarith [halb.2.2.2]) hp with h | h
        · linarith
        · exact absurd h hne
  -- gluing
  have hc1a0 : c1R ≠ a0 := by
    intro h; have := ha0b.1; rw [← h] at this; simp [c1R] at this; linarith
  have hald1 : al ≠ d1R := by
    intro h; have := halb.1; rw [h] at this; simp [d1R] at this; linarith
  -- step 1: F, LW
  have st1 : ChainSimple ((c0R :: Fl) ++ c1R :: [a0]) := by
    refine ChainSimple.join (by simpa using hFs) ⟨hc1a0, by simp, trivial⟩ ?_
    rintro x ⟨hx1, hx2⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at hx2
    have h1 : x ∈ chainSet (c0R :: Fl ++ [c1R]) := by simpa using hx1
    exact hFr x h1 (hLW x hx2).1
  have cs1 : chainSet ((c0R :: Fl) ++ c1R :: [a0]) =
      chainSet (c0R :: Fl ++ [c1R]) ∪ ArtGallery.segment c1R a0 := by
    rw [chainSet_append_cons]; simp
  -- step 2: T
  have st2 : ChainSimple ((c0R :: Fl ++ [c1R]) ++ a0 :: (T' ++ [al])) := by
    refine ChainSimple.join (by simpa using st1) (by rw [← List.cons_append, ← hT']; exact hTs) ?_
    rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ chainSet T := by rw [hT']; simpa using hx2
    have hx1' : x ∈ chainSet ((c0R :: Fl) ++ c1R :: [a0]) := by simpa using hx1
    rw [cs1] at hx1'
    rcases hx1' with h | h
    · exfalso
      have := (hF1 x h).2.1
      have := (hTbox hx2').1
      linarith
    · by_contra hne
      obtain ⟨hlt1, hlt2⟩ := (hLW x h).2.2.2.2.2.2 hne
      rcases hquad0 x hx2' with h' | h' <;> linarith
  have cs2 : chainSet ((c0R :: Fl ++ [c1R]) ++ a0 :: (T' ++ [al])) =
      (chainSet (c0R :: Fl ++ [c1R]) ∪ ArtGallery.segment c1R a0) ∪ chainSet T := by
    rw [chainSet_append_cons, ← cs1, hT']
    congr 1
    simp
  -- step 3: UW
  have st3 : ChainSimple (((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ al :: [d1R]) := by
    refine ChainSimple.join (by simpa using st2) ⟨hald1, by simp, trivial⟩ ?_
    rintro x ⟨hx1, hx2⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at hx2
    have hx1' : x ∈ chainSet ((c0R :: Fl ++ [c1R]) ++ a0 :: (T' ++ [al])) := by simpa using hx1
    rw [cs2] at hx1'
    obtain ⟨u1, -, -, -, u5, u6, u7⟩ := hUW x hx2
    rcases hx1' with (h | h) | h
    · exfalso
      have hx := (hF1 x h).2.1
      have := u6 hx
      have := hFr x h (by linarith)
      rw [this] at u6
      have := u6 (by norm_num [c1R])
      simp [c1R, d1R] at this; linarith
    · exfalso; have := (hLW x h).2.2.2.2.1; linarith
    · by_contra hne
      obtain ⟨hlt1, hlt2⟩ := u7 hne
      rcases hquadl x h with h' | h' <;> linarith
  have cs3 : chainSet (((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ al :: [d1R]) =
      ((chainSet (c0R :: Fl ++ [c1R]) ∪ ArtGallery.segment c1R a0) ∪ chainSet T) ∪
        ArtGallery.segment al d1R := by
    rw [chainSet_append_cons, ← cs2]
    simp
  -- step 4: U
  have st4 : ChainSimple ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) := by
    refine ChainSimple.join (by simpa using st3) (by simpa using hUs) ?_
    rintro x ⟨hx1, hx2⟩
    have hx1' : x ∈ chainSet (((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ al :: [d1R]) := by
      simpa using hx1
    have hx2' : x ∈ chainSet (d1R :: Up ++ [d0R]) := by simpa using hx2
    obtain ⟨v1, v2, v3, v4⟩ := hU1 x hx2'
    rw [cs3] at hx1'
    rcases hx1' with ((h | h) | h) | h
    · exfalso; have := (hF1 x h).2.2.2; linarith
    · exfalso; have := (hLW x h).2.1; linarith
    · exfalso; have := (hTbox h).1; linarith
    · exact (hUW x h).2.2.2.2.2.1 v2
  have cs4 : chainSet ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) =
      (((chainSet (c0R :: Fl ++ [c1R]) ∪ ArtGallery.segment c1R a0) ∪ chainSet T) ∪
        ArtGallery.segment al d1R) ∪ chainSet (d1R :: Up ++ [d0R]) := by
    rw [chainSet_append_cons, ← cs3]
    simp
  have hfull : (I.chainBefore ++ placedTmpl I k ++ I.chainAfter).map ratPoint =
      (((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R]) := by
    rw [List.map_append, List.map_append, hCB, hT, hCA, hT']
    simp
  rw [hfull]
  have hfst : fstPt ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) = c0R := rfl
  have hlst : lstPt ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) = d0R := by
    rw [show ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) =
      ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: Up) ++ [d0R] by simp]
    exact lstPt_append_single _ _
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_singleton]; omega,
    st4, hfst, hlst, ?_, ?_⟩
  · rw [hfst, hlst, cs4]
    rintro p ((((h | h) | h) | h) | h)
    · by_cases hx : p.1 ≤ S
      · exact Or.inr (Or.inl (hFlft p h hx))
      · exact Or.inl (lt_of_not_ge hx)
    · left; have := (hLW p h).1; linarith
    · left; have := (hTbox h).1; linarith
    · left; have := (hUW p h).1; linarith
    · by_cases hx : p.1 ≤ S
      · exact Or.inr (Or.inr (hUlft p h hx))
      · exact Or.inl (lt_of_not_ge hx)
  · rw [cs4]
    rintro p ((((h | h) | h) | h) | h)
    · obtain ⟨a, b, c, d⟩ := hF1 p h; exact ⟨a, by linarith, by linarith, by linarith⟩
    · obtain ⟨a, b, c, d, -⟩ := hLW p h; exact ⟨by linarith, d, by linarith, by linarith⟩
    · obtain ⟨a, b, c, d⟩ := hTbox h
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨a, b, c, d, -⟩ := hUW p h; exact ⟨by linarith, d, by linarith, by linarith⟩
    · obtain ⟨a, b, c, d⟩ := hU1 p h; exact ⟨a, by linarith, by linarith, d⟩

end Unit

end ArtGallery.Sec5

end
