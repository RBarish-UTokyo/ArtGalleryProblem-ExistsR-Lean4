module

public import ArtGallery.Hardness.BP.Assemble.TmplFacts
public import ArtGallery.Hardness.Sec5.Assemble.UnitChain

/-!
# Boundary-point variant: the chain of one unit is simple

As `Sec5/Assemble/UnitChain.lean`, for the boundary-point templates: for a good corridor input
`I` and a template kind `k`, the unit chain
```
F = c0, floor…, c1      LW = [c1, φ(V₀)]      T = φ(template)      UW = [φ(V_l), d1]
U = d1, upper wall…, d0
```
(`(I.chainBefore ++ placedTmplBP I k ++ I.chainAfter).map ratPoint`) is a simple chain
(`unit_featureBP`), packaged as `UnitFeature S H ρ f`.  The only difference to Section 5 is the
separation of the two walls `LW`, `UW`: the line `x + y = S + H + 2` no longer separates them
(`V_l.x + V_l.y < 0` for the addition kinds); instead `UW` lies strictly left of the directed line
`c1 → φ(V₀)` that carries `LW` (`(V_l.x + V_l.y) − (V₀.x + V₀.y) ≥ 1` and `|V| ≤ 50` give
`det(c1, φ(V₀), φ(V_l)) > 0`, and `det(c1, φ(V₀), d1) > 0`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input place)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- The placed template in real coordinates. -/
theorem placedTmplBP_map (I : Input) (k : Kind) (hS : (1000 : ℝ) ≤ I.S) :
    (placedTmplBP I k).map ratPoint = tmplPlacedBP k (I.S : ℝ) (I.H : ℝ) (S_ne_of hS) := by
  simp only [placedTmplBP, tmplPlacedBP, List.map_map]
  apply List.map_congr_left
  intro V _
  have hS0 : (I.S : ℝ) ≠ 0 := S_ne_of hS
  have hD : (tmplDBP k : ℝ) ≠ 0 := by exact_mod_cast (tmplDBP_pos k).ne'
  simp only [Function.comp, tmplMapBP_apply, ratPoint, place, tmplPtBP, intPoint]
  push_cast
  ext <;> simp only <;> field_simp

/-- The window in real coordinates: `(φ(V_l).x + φ(V_l).y) − (φ(V₀).x + φ(V₀).y) ≥ 1/S`. -/
theorem tmplBP_window_real (k : Kind) {S H : ℝ} (hS : 1000 ≤ S) :
    1 / S ≤ ((tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k))).1 +
      (tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k))).2) -
      ((tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k))).1 +
      (tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k))).2) := by
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hS0 : (0 : ℝ) < S := by linarith
  have hDS : (0 : ℝ) < (tmplDBP k : ℝ) * S := by positivity
  have hw' : (tmplDBP k : ℝ) ≤ ((tmplLstBP k).1 : ℝ) + ((tmplLstBP k).2 : ℝ) -
      (((tmplFstBP k).1 : ℝ) + ((tmplFstBP k).2 : ℝ)) := by exact_mod_cast tmplBP_window k
  have e : ((tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k))).1 +
      (tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k))).2) -
      ((tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k))).1 +
      (tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k))).2) =
      (((tmplLstBP k).1 : ℝ) + ((tmplLstBP k).2 : ℝ) -
        (((tmplFstBP k).1 : ℝ) + ((tmplFstBP k).2 : ℝ))) / ((tmplDBP k : ℝ) * S) := by
    simp only [tmplMapBP_apply, intPoint]
    field_simp
    ring
  rw [e, show 1 / S = (tmplDBP k : ℝ) / ((tmplDBP k : ℝ) * S) by field_simp]
  exact div_le_div_of_nonneg_right hw' hDS.le

/-- **Separation of the two channel walls**: the template ends `a0 = φ(V₀)`, `al = φ(V_l)` lie in
the box of radius `50/S` around `(S + 3, H − 1)` and satisfy the window inequality; then `al` and
`d1 = (S + 2, H + ρ)` lie strictly left of the directed line `c1 → a0`. -/
theorem walls_detBP {S H ρ : ℝ} {a0 al : Point} (hS : 800000 ≤ S) (hρ : 0 < ρ)
    (ha0 : S + 3 - 50 / S ≤ a0.1 ∧ a0.1 ≤ S + 3 + 50 / S ∧ H - 1 - 50 / S ≤ a0.2 ∧
      a0.2 ≤ H - 1 + 50 / S)
    (hal : S + 3 - 50 / S ≤ al.1 ∧ al.1 ≤ S + 3 + 50 / S ∧ H - 1 - 50 / S ≤ al.2 ∧
      al.2 ≤ H - 1 + 50 / S)
    (hwin : 1 / S ≤ (al.1 + al.2) - (a0.1 + a0.2)) :
    0 < det (S + 2, H) a0 al ∧ 0 < det (S + 2, H) a0 (S + 2, H + ρ) := by
  have hS0 : (0 : ℝ) < S := by linarith
  set r : ℝ := 50 / S with hr
  have hr2 : r * r * 2 < 1 / S := by
    rw [show r * r * 2 = (5000 / S) * (1 / S) by rw [hr]; ring]
    have h1S : 0 < 1 / S := by positivity
    have : 5000 / S < 1 := by rw [div_lt_one hS0]; linarith
    nlinarith
  have hr1 : r ≤ 1 / 1000 := by rw [hr, div_le_iff₀ hS0]; linarith
  obtain ⟨a1, a2, a3, a4⟩ := ha0
  obtain ⟨l1, l2, l3, l4⟩ := hal
  constructor
  · have e : det (S + 2, H) a0 al = ((al.1 - (S + 3)) + (al.2 - (H - 1))) -
        ((a0.1 - (S + 3)) + (a0.2 - (H - 1))) + (a0.1 - (S + 3)) * (al.2 - (H - 1)) -
        (a0.2 - (H - 1)) * (al.1 - (S + 3)) := by
      simp only [det]; ring
    rw [e]
    nlinarith [mul_nonneg (show 0 ≤ r + (a0.1 - (S + 3)) by linarith)
        (show 0 ≤ r + (al.2 - (H - 1)) by linarith),
      mul_nonneg (show 0 ≤ r - (a0.1 - (S + 3)) by linarith)
        (show 0 ≤ r - (al.2 - (H - 1)) by linarith),
      mul_nonneg (show 0 ≤ r + (a0.2 - (H - 1)) by linarith)
        (show 0 ≤ r - (al.1 - (S + 3)) by linarith),
      mul_nonneg (show 0 ≤ r - (a0.2 - (H - 1)) by linarith)
        (show 0 ≤ r + (al.1 - (S + 3)) by linarith)]
  · have e : det (S + 2, H) a0 (S + 2, H + ρ) = (a0.1 - (S + 2)) * ρ := by simp only [det]; ring
    rw [e]
    exact mul_pos (by linarith) hρ

section Unit

variable {I : Input} {N : ℚ} (hg : I.Good N) (k : Kind)
include hg

/-- **The unit chain is a simple chain hanging right of `x = S`.** -/
theorem unit_featureBP :
    UnitFeature (I.S : ℝ) (I.H : ℝ) I.rhoR
      ((I.chainBefore ++ placedTmplBP I k ++ I.chainAfter).map ratPoint) := by
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
  set T := tmplPlacedBP k S H (S_ne_of hS)
  set a0 := tmplMapBP k S H (S_ne_of hS) (intPoint (tmplFstBP k))
  set al := tmplMapBP k S H (S_ne_of hS) (intPoint (tmplLstBP k))
  have hFl0 : Fl ≠ [] := by simpa [Fl] using hg.floor_ne_nil
  have hUp0 : Up ≠ [] := by simpa [Up] using hg.upper_ne_nil
  -- the three pieces
  have hCB : I.chainBefore.map ratPoint = c0R :: Fl ++ [c1R] := by
    simp [chainBefore, ratPoint_c0', ratPoint_c1', c0R, c1R, Fl]
    exact ⟨rfl, rfl⟩
  have hCA : I.chainAfter.map ratPoint = d1R :: Up ++ [d0R] := by
    simp [chainAfter, ratPoint_d1', ratPoint_d0', d1R, d0R, Up]
    exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  have hT : (placedTmplBP I k).map ratPoint = T := placedTmplBP_map I k hS
  have hTs : ChainSimple T := tmplPlacedBP_simple k hS
  have hTl : 3 ≤ T.length := tmplPlacedBP_length k hS
  have hTf : fstPt T = a0 := tmplPlacedBP_fst k hS
  have hTla : lstPt T = al := tmplPlacedBP_lst k hS
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
  have hD : (0 : ℝ) < tmplDBP k := by exact_mod_cast tmplDBP_pos k
  have hDS : (0 : ℝ) < (tmplDBP k : ℝ) * S := by positivity
  have hTbox : ∀ {p : Point}, p ∈ chainSet T → S + 3 - 50 / S ≤ p.1 ∧ p.1 ≤ S + 3 + 50 / S ∧
      H - 1 - 50 / S ≤ p.2 ∧ p.2 ≤ H - 1 + 50 / S := fun hp => tmplPlacedBP_box k hS hp
  have ha0mem : a0 ∈ chainSet T := by rw [← hTf]; exact fstPt_mem (by omega)
  have halmem : al ∈ chainSet T := by rw [← hTla]; exact lstPt_mem (by omega)
  have ha0b := hTbox ha0mem
  have halb := hTbox halmem
  -- the two walls are separated by the line through the lower wall
  obtain ⟨hdetal, hdetd1⟩ := walls_detBP (H := H) hS8 hρ ha0b halb (tmplBP_window_real k hS)
  have hquad0 : ∀ p ∈ chainSet T, a0.1 ≤ p.1 ∨ p.2 ≤ a0.2 :=
    fun p hp => tmplPlacedBP_quad k hS (tmplBP_quadFst k) hp
  have hquadl : ∀ p ∈ chainSet T, al.1 ≤ p.1 ∨ p.2 ≤ al.2 :=
    fun p hp => tmplPlacedBP_quad k hS (tmplBP_quadLst k) hp
  -- the floor
  have hFv : ∀ v ∈ Fl, S + 1 / 4 ≤ v.1 ∧ v.1 ≤ S + 15 / 8 ∧ H - 1 / 4 ≤ v.2 ∧ v.2 ≤ H :=
    fun v hv => hg.floor_box v hv
  have hFall : ∀ v ∈ c0R :: Fl ++ [c1R], S ≤ v.1 ∧ v.1 ≤ S + 2 ∧ H - 1 / 4 ≤ v.2 ∧ v.2 ≤ H := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append,
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
    simp only [List.cons_append, List.mem_cons, List.mem_append,
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
      H - 1 - 1 / 1000 ≤ p.2 ∧ p.1 ≤ S + 4 ∧ det c1R a0 p = 0 ∧
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
    · obtain ⟨t, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
      simp only [det, Geometry.lerp]; ring
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
      p.2 ≤ H + ρ ∧ p.1 ≤ S + 4 ∧ 0 < det c1R a0 p ∧
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
    · obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
      have e : det c1R a0 (Geometry.lerp al d1R t) =
          (1 - t) * det c1R a0 al + t * det c1R a0 d1R := by
        simp only [det, Geometry.lerp]; ring
      rw [e]
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · subst h0; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact hdetal
      · nlinarith
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
  have hfull : (I.chainBefore ++ placedTmplBP I k ++ I.chainAfter).map ratPoint =
      (((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R]) := by
    rw [List.map_append, List.map_append, hCB, hT, hCA, hT']
    simp
  rw [hfull]
  have hfst : fstPt ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) = c0R := rfl
  have hlst : lstPt ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) = d0R := by
    rw [show ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: (Up ++ [d0R])) =
      ((((c0R :: Fl ++ [c1R]) ++ a0 :: T') ++ [al]) ++ d1R :: Up) ++ [d0R] by simp]
    exact lstPt_append_single _ _
  refine ⟨by simp only [List.length_append, List.length_cons]; omega,
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