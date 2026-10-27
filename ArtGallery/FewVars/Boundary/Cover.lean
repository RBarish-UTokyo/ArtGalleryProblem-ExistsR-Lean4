module

public import ArtGallery.FewVars.Boundary.Witness

/-!
# Finitely many witness points on the boundary

For edge `e = [u, v]` and guards `Γ`, the breakpoints are `ebT P Γ e α` (`α < m + 2`,
`m = n + g n`): `0`, `1` and, for every line `ℓ` of the arrangement (`lineR P Γ`) not parallel
to `e`, the parameter `-det ℓ u / (det ℓ v - det ℓ u)` where the line of `e` meets `ℓ` (divisor
`ebD P Γ e α`).

**`boundary_seen_of_witnesses`**: if the guards lie in the region and every point of an edge at
the midpoint of two breakpoints in `[0, 1]` is seen by a guard, every boundary point is seen by a
guard.
-/

@[expose] public section

namespace ArtGallery.FewVars.Boundary

open Set
open ArtGallery.Membership ArtGallery.FewVars
open ArtGallery.Geometry (lerp det_lerp det_lerp_self lerp_mem_segment)
open ArtGallery.Membership.Witness (det_eq_zero_of_collinear)

variable {P : Polygon}

/-- The divisor of breakpoint `α` of edge `e`. -/
noncomputable def ebD (P : Polygon) (Γ : ℕ → Point) (e α : ℕ) : ℝ :=
  if α < 2 then 1
  else det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx ((e + 1) % P.n)) -
    det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx e)

/-- Breakpoint `α` of edge `e`. -/
noncomputable def ebT (P : Polygon) (Γ : ℕ → Point) (e α : ℕ) : ℝ :=
  if α = 0 then 0 else if α = 1 then 1
  else -det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx e) / ebD P Γ e α

/-- Points of the segment between two points of a parametrised line. -/
theorem mem_segment_lerp_iff {u v z : Point} {p q : ℝ} :
    z ∈ ArtGallery.segment (lerp u v p) (lerp u v q) ↔ ∃ r ∈ uIcc p q, z = lerp u v r := by
  constructor
  · rintro ⟨w, h0, h1, rfl⟩
    refine ⟨p + w * (q - p), ?_, ?_⟩
    · rw [mem_uIcc]
      rcases le_total p q with h | h
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
    · ext <;> simp [lerp] <;> ring
  · rintro ⟨r, hr, rfl⟩
    by_cases hpq : p = q
    · subst hpq
      rw [uIcc_self, mem_singleton_iff] at hr
      subst hr
      exact Geometry.left_mem_segment _ _
    · have hpq' : q - p ≠ 0 := sub_ne_zero.2 (Ne.symm hpq)
      refine ⟨(r - p) / (q - p), ?_, ?_, ?_⟩
      · rw [mem_uIcc] at hr
        rcases lt_or_gt_of_ne hpq' with h | h
        · rw [div_nonneg_iff]; right; constructor
          · rcases hr with h' | h' <;> linarith [h'.1, h'.2]
          · linarith
        · rw [div_nonneg_iff]; left; constructor
          · rcases hr with h' | h' <;> linarith [h'.1, h'.2]
          · linarith
      · rw [mem_uIcc] at hr
        rcases lt_or_gt_of_ne hpq' with h | h
        · rw [div_le_one_of_neg h]; rcases hr with h' | h' <;> linarith [h'.1, h'.2]
        · rw [div_le_one h]; rcases hr with h' | h' <;> linarith [h'.1, h'.2]
      · ext <;> simp [lerp] <;> field_simp <;> ring

/-- **A guard on the line of an edge** that sees one point of the edge sees all of it. -/
theorem sees_of_collinear (hP : P.Simple) {e : ℕ} (he : e < P.n) {γ : Point}
    (hγe : det (P.vtx e) (P.vtx ((e + 1) % P.n)) γ = 0) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (hsee : P.Sees γ (lerp (P.vtx e) (P.vtx ((e + 1) % P.n)) s)) :
    P.Sees γ (lerp (P.vtx e) (P.vtx ((e + 1) % P.n)) s') := by
  set u := P.vtx e with hu
  set v := P.vtx ((e + 1) % P.n) with hv
  have huv : u ≠ v := Jordan.simple_vtx_succ_ne hP he
  have hL := Jordan.sqLen_pos huv
  unfold Jordan.sqLen at hL
  set c := ((γ.1 - u.1) * (v.1 - u.1) + (γ.2 - u.2) * (v.2 - u.2)) /
    ((v.1 - u.1) ^ 2 + (v.2 - u.2) ^ 2) with hc
  have hγc : γ = lerp u v c := by
    unfold det at hγe
    ext
    · simp only [lerp, hc]; field_simp; linear_combination (-(v.2 - u.2)) * hγe
    · simp only [lerp, hc]; field_simp; linear_combination (v.1 - u.1) * hγe
  rw [hγc] at hsee ⊢
  intro z hz
  obtain ⟨r, hr, rfl⟩ := mem_segment_lerp_iff.1 hz
  rcases uIcc_subset_uIcc_union_uIcc hr with h | h
  · exact hsee (mem_segment_lerp_iff.2 ⟨r, h, rfl⟩)
  · have h01 : r ∈ Icc (0 : ℝ) 1 := by
      rw [mem_uIcc] at h
      rcases h with h | h
      · exact ⟨by linarith [hs.1], by linarith [hs'.2]⟩
      · exact ⟨by linarith [hs'.1], by linarith [hs.2]⟩
    exact Jordan.boundary_subset_filled P ⟨e, he, lerp_mem_segment _ _ h01.1 h01.2⟩

/-- The line `n + a n + k` is the line through guard `a` and vertex `k`. -/
theorem lineR_guard {Γ : ℕ → Point} {a k : ℕ} (hk : k < P.n) :
    lineR P Γ (P.n + a * P.n + k) = (Γ a, P.vtx k) := by
  have h1 : ¬ (P.n + a * P.n + k < P.n) := by omega
  have h2 : P.n + a * P.n + k - P.n = a * P.n + k := by omega
  simp only [lineR, h1, ite_false, h2, pair_div hk, pair_mod hk]

/-- A breakpoint-free parameter is off a line of the arrangement, unless the whole edge lies on
the line. -/
theorem det_ne_of_not_bp {Γ : ℕ → Point} {e α : ℕ} (hα : 2 ≤ α) {t : ℝ}
    (hnot : ebD P Γ e α ≠ 0 → t ≠ ebT P Γ e α)
    (hline : ¬ (det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx e) = 0 ∧
      det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx ((e + 1) % P.n)) = 0)) :
    det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2
      (lerp (P.vtx e) (P.vtx ((e + 1) % P.n)) t) ≠ 0 := by
  have h2 : ¬ α < 2 := by omega
  have h0 : α ≠ 0 := by omega
  have h1 : α ≠ 1 := by omega
  intro hz
  rw [det_lerp] at hz
  by_cases hD : ebD P Γ e α = 0
  · simp only [ebD, h2, ite_false] at hD
    apply hline
    have hA : det (lineR P Γ (α - 2)).1 (lineR P Γ (α - 2)).2 (P.vtx e) = 0 := by
      linear_combination hz - t * hD
    exact ⟨hA, by linear_combination hD + hA⟩
  · apply hnot hD
    simp only [ebT, h0, h1, ite_false]
    rw [eq_div_iff hD]
    simp only [ebD, h2, ite_false]
    linarith

/-- **The boundary witness lemma.** -/
theorem boundary_seen_of_witnesses (hP : P.Simple) (Γ : ℕ → Point) (g : ℕ)
    (hΓ : ∀ a < g, Γ a ∈ P.filled)
    (h : ∀ e < P.n, ∀ α < numLines P.n g + 2, ∀ β < numLines P.n g + 2,
      ebD P Γ e α ≠ 0 → ebD P Γ e β ≠ 0 → 0 ≤ ebT P Γ e α → ebT P Γ e α ≤ 1 →
      0 ≤ ebT P Γ e β → ebT P Γ e β ≤ 1 →
      ∃ a < g, P.Sees (Γ a) (lerp (P.vtx e) (P.vtx ((e + 1) % P.n))
        ((ebT P Γ e α + ebT P Γ e β) / 2))) :
    ∀ p ∈ P.boundary, ∃ a < g, P.Sees (Γ a) p := by
  classical
  rintro _ ⟨e, he, s, hs0, hs1, rfl⟩
  change ∃ a < g, P.Sees (Γ a) (lerp (P.vtx e) (P.vtx ((e + 1) % P.n)) s)
  set u := P.vtx e with hu
  set v := P.vtx ((e + 1) % P.n) with hv
  set m := numLines P.n g + 2 with hm
  let T : Finset ℝ := ((Finset.range m).filter (fun α => ebD P Γ e α ≠ 0)).image (ebT P Γ e)
  have hmemT : ∀ x ∈ T, ∃ α < m, ebD P Γ e α ≠ 0 ∧ ebT P Γ e α = x := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter, Finset.mem_range] at hα
    exact ⟨α, hα.1, hα.2, rfl⟩
  have hTmem : ∀ α < m, ebD P Γ e α ≠ 0 → ebT P Γ e α ∈ T := fun α hα hD =>
    Finset.mem_image.2 ⟨α, Finset.mem_filter.2 ⟨Finset.mem_range.2 hα, hD⟩, rfl⟩
  have h0 : (0 : ℝ) ∈ T := by
    have := hTmem 0 (by omega) (by simp [ebD]); simpa [ebT] using this
  have h1 : (1 : ℝ) ∈ T := by
    have := hTmem 1 (by omega) (by simp [ebD]); simpa [ebT] using this
  by_cases hsT : s ∈ T
  · obtain ⟨α, hα, hD, rfl⟩ := hmemT s hsT
    obtain ⟨a, ha, hsee⟩ := h e he α hα α hα hD hD hs0 hs1 hs0 hs1
    exact ⟨a, ha, by rwa [show (ebT P Γ e α + ebT P Γ e α) / 2 = ebT P Γ e α by ring] at hsee⟩
  have hs0' : 0 < s := lt_of_le_of_ne hs0 (fun h => hsT (h ▸ h0))
  have hs1' : s < 1 := lt_of_le_of_ne hs1 (fun h => hsT (h ▸ h1))
  have hA : (T.filter (fun t => 0 ≤ t ∧ t < s)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨h0, le_rfl, hs0'⟩⟩
  have hB : (T.filter (fun t => s < t ∧ t ≤ 1)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨h1, hs1', le_rfl⟩⟩
  set lo := (T.filter (fun t => 0 ≤ t ∧ t < s)).max' hA with hlo_def
  set hi := (T.filter (fun t => s < t ∧ t ≤ 1)).min' hB with hhi_def
  have hloA := Finset.mem_filter.1 (Finset.max'_mem _ hA)
  have hhiB := Finset.mem_filter.1 (Finset.min'_mem _ hB)
  rw [← hlo_def] at hloA
  rw [← hhi_def] at hhiB
  have hgap : ∀ t ∈ T, t ≤ lo ∨ hi ≤ t := by
    intro t ht
    rcases lt_trichotomy t s with h' | h' | h'
    · by_cases ht0 : 0 ≤ t
      · left; exact Finset.le_max' _ t (Finset.mem_filter.2 ⟨ht, ht0, h'⟩)
      · left; linarith [hloA.2.1]
    · exact absurd (h' ▸ ht) hsT
    · by_cases ht1 : t ≤ 1
      · right; exact Finset.min'_le _ t (Finset.mem_filter.2 ⟨ht, h', ht1⟩)
      · right; linarith [hhiB.2.2]
  obtain ⟨α, hα, hDα, hTα⟩ := hmemT lo hloA.1
  obtain ⟨β, hβ, hDβ, hTβ⟩ := hmemT hi hhiB.1
  obtain ⟨a, ha, hsee⟩ := h e he α hα β hβ hDα hDβ (by rw [hTα]; exact hloA.2.1)
    (by rw [hTα]; linarith [hloA.2.2]) (by rw [hTβ]; linarith [hhiB.2.1])
    (by rw [hTβ]; exact hhiB.2.2)
  rw [hTα, hTβ] at hsee
  refine ⟨a, ha, ?_⟩
  have hsI : s ∈ Ioo lo hi := ⟨hloA.2.2, hhiB.2.1⟩
  have hmI : (lo + hi) / 2 ∈ Ioo lo hi :=
    ⟨by linarith [hloA.2.2, hhiB.2.1], by linarith [hloA.2.2, hhiB.2.1]⟩
  by_cases hγe : det u v (Γ a) = 0
  · exact sees_of_collinear hP he hγe ⟨by linarith [hmI.1, hloA.2.1], by linarith [hmI.2, hhiB.2.2]⟩
      ⟨hs0, hs1⟩ hsee
  have huv : u ≠ v := Jordan.simple_vtx_succ_ne hP he
  -- a parameter of the open piece is not a breakpoint
  have hnot : ∀ t ∈ Ioo lo hi, ∀ γ < m, ebD P Γ e γ ≠ 0 → t ≠ ebT P Γ e γ := by
    intro t ht γ hγ hD heq
    rcases hgap _ (hTmem γ hγ hD) with h' | h'
    · rw [← heq] at h'; linarith [ht.1]
    · rw [← heq] at h'; linarith [ht.2]
  refine sees_const_piece hP he hloA.2.1 hhiB.2.2 (hΓ a ha) hγe ?_ ?_ hmI hsI hsee
  · intro t ht k hk hγk
    have hidx : P.n + a * P.n + k + 2 < m := by
      have := pair_lt ha hk
      rw [hm]; unfold numLines; omega
    have := det_ne_of_not_bp (P := P) (Γ := Γ) (e := e) (α := P.n + a * P.n + k + 2) (by omega)
      (hnot t ht _ hidx) (by
        rw [show P.n + a * P.n + k + 2 - 2 = P.n + a * P.n + k by omega, lineR_guard hk]
        rintro ⟨e1, e2⟩
        exact hγe (det_eq_zero_of_collinear hγk e1 e2 (Geometry.det_self_outer _ _)))
    rwa [show P.n + a * P.n + k + 2 - 2 = P.n + a * P.n + k by omega, lineR_guard hk] at this
  · intro t ht j hj hjγ
    have hidx : j + 2 < m := by rw [hm]; unfold numLines; omega
    have hl : lineR P Γ j = (P.vtx j, P.vtx ((j + 1) % P.n)) := by simp [lineR, hj]
    have := det_ne_of_not_bp (P := P) (Γ := Γ) (e := e) (α := j + 2) (by omega)
      (hnot t ht _ hidx) (by
        rw [show j + 2 - 2 = j by omega, hl]
        rintro ⟨e1, e2⟩
        exact hγe (det_eq_zero_of_collinear (Jordan.simple_vtx_succ_ne hP hj) e1 e2 hjγ))
    rwa [show j + 2 - 2 = j by omega, hl] at this

end ArtGallery.FewVars.Boundary

end
