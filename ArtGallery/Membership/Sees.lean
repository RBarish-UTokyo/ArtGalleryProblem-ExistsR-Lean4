module

public import ArtGallery.Membership.Inside

/-!
# The formula SEES

`seesF n γ c base` expresses that the segment `[γ, c]` lies in the closed region of the polygon in
the vertex variables (`P.Sees γ c`).  Writing `p(s) = γ + s (c - γ)`, its fresh variables are

* `t_j = x_{base + j}` (`j < n`): the parameter where the line `γc` meets the line of edge `j`,
  `D_j t_j + det(v_j, v_{j+1}, γ) = 0`, unless the lines are parallel (`D_j = 0`);
* `t'_k = x_{base + n + k}` (`k < n`): the parameter of vertex `k`, `p(t'_k) = v_k`, unless
  `v_k` is not on the segment;
* for each ordered pair `(a, b)` of elements of `T = (0, 1, t_0, …, t_{n-1}, t'_0, …, t'_{n-1})`
  (index `p = a (2n + 2) + b`), a block of `n + 1` variables at `base + 2n + p (n + 1)`: the
  midpoint parameter `h` (`h + h = T_a + T_b`) and the parity variables of `p(h)`; if
  `T_a, T_b ∈ [0, 1]`, the point `p(h)` is INSIDE.

`segment_subset_filled_of_breakpoints` is the geometric heart: between two consecutive
breakpoints, the open piece of the segment either lies on one edge or misses the boundary, and in
the latter case it is a connected set off the boundary, so it has the parity of its tested
midpoint.  Main results: `sees_of_holds` and `exists_sees_holds`.
-/

@[expose] public section

namespace ArtGallery.Membership

open ArtGallery.ETR Geometry Set

/-! ## Geometry of breakpoints -/

/-- The determinant along a line. -/
theorem det_lerp_line (u w γ c : Point) (s : ℝ) :
    det u w (lerp γ c s) = det u w γ + crossR u w γ c * s := by
  unfold det lerp crossR; ring

/-- On an open parameter interval free of breakpoints, an edge contains either all or none of the
points of the segment. -/
theorem edge_piece {P : Polygon} {γ c : Point} (T : Finset ℝ)
    (hT1 : ∀ j < P.n, ∀ s : ℝ, crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c ≠ 0 →
      crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c * s +
        det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 → s ∈ T)
    (hT2 : ∀ k < P.n, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → lerp γ c s = P.vtx k → s ∈ T)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hgap : ∀ t ∈ T, t ≤ lo ∨ hi ≤ t)
    {j : ℕ} (hj : j < P.n) {s1 s2 : ℝ} (hs1 : s1 ∈ Ioo lo hi) (hs2 : s2 ∈ Ioo lo hi)
    (h1 : lerp γ c s1 ∈ P.edge j) : lerp γ c s2 ∈ P.edge j := by
  have hnotT : ∀ s ∈ Ioo lo hi, s ∉ T := by
    intro s hs hT
    rcases hgap s hT with h | h
    · linarith [hs.1]
    · linarith [hs.2]
  have h1' := mem_segment_iff_det_dot.1 h1
  by_cases hD : crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c = 0
  · have hdet : ∀ s, det (P.vtx j) (P.vtx ((j + 1) % P.n)) (lerp γ c s) =
        det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ := fun s => by
      rw [det_lerp_line, hD, zero_mul, add_zero]
    have hcol : det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 := by rw [← hdet s1]; exact h1'.1
    by_contra h2
    have h2' : 0 < dotR (P.vtx j) (lerp γ c s2) (P.vtx ((j + 1) % P.n)) (lerp γ c s2) := by
      by_contra hle
      exact h2 (mem_segment_iff_det_dot.2 ⟨by rw [hdet, hcol], not_lt.1 hle⟩)
    let f : ℝ → ℝ := fun s => dotR (P.vtx j) (lerp γ c s) (P.vtx ((j + 1) % P.n)) (lerp γ c s)
    have hf : Continuous f := by
      simp only [f, dotR, lerp]
      fun_prop
    have h0 : (0 : ℝ) ∈ uIcc (f s1) (f s2) := by
      rw [mem_uIcc]; left; exact ⟨h1'.2, h2'.le⟩
    obtain ⟨s3, hs3, hf3⟩ := intermediate_value_uIcc hf.continuousOn h0
    have hs3' : s3 ∈ Ioo lo hi := by
      rw [mem_uIcc] at hs3
      rcases hs3 with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨by linarith [hs1.1], by linarith [hs2.2]⟩
      · exact ⟨by linarith [hs2.1], by linarith [hs1.2]⟩
    have h01 : 0 ≤ s3 ∧ s3 ≤ 1 := ⟨by linarith [hs3'.1], by linarith [hs3'.2]⟩
    rcases eq_or_eq_of_det_dot_zero (by rw [hdet, hcol]) hf3 with hv | hv
    · exact hnotT s3 hs3' (hT2 j hj s3 h01.1 h01.2 hv)
    · exact hnotT s3 hs3' (hT2 _ (succ_mod_lt hj) s3 h01.1 h01.2 hv)
  · exfalso
    have e := h1'.1
    rw [det_lerp_line] at e
    exact hnotT s1 hs1 (hT1 j hj s1 hD (by linarith))

/-- **Breakpoint lemma.** Let `T` be a finite set of parameters containing `0`, `1`, the
parameters where the line `γc` meets the (non-parallel) edge lines, and the parameters of the
vertices on the segment.  If the point at the midpoint of any two parameters of `T ∩ [0, 1]` lies
in the region, the whole segment `[γ, c]` lies in the region. -/
theorem segment_subset_filled_of_breakpoints {P : Polygon} (hP : P.Simple) {γ c : Point}
    (T : Finset ℝ) (h0 : (0 : ℝ) ∈ T) (h1 : (1 : ℝ) ∈ T)
    (hT1 : ∀ j < P.n, ∀ s : ℝ, crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c ≠ 0 →
      crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c * s +
        det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ = 0 → s ∈ T)
    (hT2 : γ ≠ c → ∀ k < P.n, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → lerp γ c s = P.vtx k → s ∈ T)
    (hmid : ∀ a ∈ T, ∀ b ∈ T, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      lerp γ c ((a + b) / 2) ∈ P.filled) :
    ArtGallery.segment γ c ⊆ P.filled := by
  rintro p ⟨s, hs0, hs1, rfl⟩
  change lerp γ c s ∈ P.filled
  by_cases hγc : γ = c
  · subst hγc
    have := hmid 0 h0 0 h0 le_rfl zero_le_one le_rfl zero_le_one
    simpa [lerp_self] using this
  by_cases hsT : s ∈ T
  · have := hmid s hsT s hsT hs0 hs1 hs0 hs1
    rwa [show (s + s) / 2 = s by ring] at this
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
    rcases lt_trichotomy t s with h | h | h
    · by_cases ht0 : 0 ≤ t
      · left; exact Finset.le_max' _ t (Finset.mem_filter.2 ⟨ht, ht0, h⟩)
      · left; linarith [hloA.2.1]
    · exact absurd (h ▸ ht) hsT
    · by_cases ht1 : t ≤ 1
      · right; exact Finset.min'_le _ t (Finset.mem_filter.2 ⟨ht, h, ht1⟩)
      · right; linarith [hhiB.2.2]
  have hm := hmid lo hloA.1 hi hhiB.1 hloA.2.1 (by linarith [hloA.2.2])
    (by linarith [hhiB.2.1]) hhiB.2.2
  have hsI : s ∈ Ioo lo hi := ⟨hloA.2.2, hhiB.2.1⟩
  have hmI : (lo + hi) / 2 ∈ Ioo lo hi :=
    ⟨by linarith [hloA.2.2, hhiB.2.1], by linarith [hloA.2.2, hhiB.2.1]⟩
  by_cases hb : lerp γ c s ∈ P.boundary
  · exact Jordan.boundary_subset_filled P hb
  have hoff : lerp γ c '' Ioo lo hi ⊆ P.boundaryᶜ := by
    rintro _ ⟨s', hs', rfl⟩ ⟨j, hj, hje⟩
    exact hb ⟨j, hj, edge_piece T hT1 (hT2 hγc) hloA.2.1 hhiB.2.2 hgap hj hs' hsI hje⟩
  have hconn : IsPreconnected (lerp γ c '' Ioo lo hi) :=
    isPreconnected_Ioo.image _ (continuous_lerp γ c).continuousOn
  have hpar := Jordan.parity_eq_of_isPreconnected P hconn hoff (mem_image_of_mem _ hsI)
    (mem_image_of_mem _ hmI)
  have hmb : lerp γ c ((lo + hi) / 2) ∉ P.boundary := hoff (mem_image_of_mem _ hmI)
  have hodd : Jordan.parity P (lerp γ c ((lo + hi) / 2)) = true :=
    (Jordan.mem_filled_iff hP hmb).1 hm
  exact Jordan.odd_mem_filled P (hpar.trans hodd)

/-! ## The formula -/

/-- Number of fresh variables of `seesF n γ c base`. -/
def seesSize (n : ℕ) : ℕ := 2 * n + (2 * n + 2) * (2 * n + 2) * (n + 1)

/-- The parameter `t_j` of the intersection of the line `γc` with the line of edge `j`. -/
def tDefF (n : ℕ) (γ c : PTerm) (base j : ℕ) : Formula :=
  .or (.eq (.add (.mul (crossT (vt j) (vt ((j + 1) % n)) γ c) (.var (base + j)))
        (detT (vt j) (vt ((j + 1) % n)) γ)) .zero)
    (.eq (crossT (vt j) (vt ((j + 1) % n)) γ c) .zero)

/-- The parameter `t'_k` of vertex `k` along the segment `γc`. -/
def vDefF (n : ℕ) (γ c : PTerm) (base k : ℕ) : Formula :=
  .or (ptEq (lerpT γ c (.var (base + n + k))) (vt k)) (.not (onSegF (vt k) γ c))

/-- The breakpoint terms: `T_0 = 0`, `T_1 = 1`, `T_{α} = x_{base + α - 2}` for `α ≥ 2`. -/
def tTerm (base α : ℕ) : Term :=
  if α = 0 then .zero else if α = 1 then .one else .var (base + α - 2)

/-- `0 ≤ t ≤ 1`. -/
def unitF (t : Term) : Formula := .and (.le .zero t) (.le t .one)

/-- The first variable of the block of the pair `p`. -/
def pairBase (n base p : ℕ) : ℕ := base + 2 * n + p * (n + 1)

/-- The midpoint test for the pair `p = a (2n + 2) + b`. -/
def pairF (n : ℕ) (γ c : PTerm) (base p : ℕ) : Formula :=
  fImp (.and (unitF (tTerm base (p / (2 * n + 2)))) (unitF (tTerm base (p % (2 * n + 2)))))
    (.and (.eq (.add (.var (pairBase n base p)) (.var (pairBase n base p)))
        (.add (tTerm base (p / (2 * n + 2))) (tTerm base (p % (2 * n + 2)))))
      (.and (parDefF n (lerpT γ c (.var (pairBase n base p))) (pairBase n base p + 1))
        (insideF n (lerpT γ c (.var (pairBase n base p))) (pairBase n base p + 1))))

/-- **SEES**: the segment `[γ, c]` lies in the closed region; fresh variables
`base, …, base + seesSize n - 1`. -/
def seesF (n : ℕ) (γ c : PTerm) (base : ℕ) : Formula :=
  .and (bigAnd ((List.range n).map (tDefF n γ c base)))
    (.and (bigAnd ((List.range n).map (vDefF n γ c base)))
      (bigAnd ((List.range ((2 * n + 2) * (2 * n + 2))).map (pairF n γ c base))))

theorem tTerm_eval_of_ge {x : ℕ → ℝ} {base α : ℕ} (h : 2 ≤ α) :
    (tTerm base α).eval x = x (base + α - 2) := by
  have h0 : α ≠ 0 := by omega
  have h1 : α ≠ 1 := by omega
  simp [tTerm, h0, h1]

theorem holds_unitF (x : ℕ → ℝ) (t : Term) :
    (unitF t).Holds x ↔ 0 ≤ t.eval x ∧ t.eval x ≤ 1 := by
  simp [unitF]

/-! ## Soundness -/

/-- **SEES is sound.** -/
theorem sees_of_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x)
    {γ c : PTerm} {base : ℕ} (h : (seesF P.n γ c base).Holds x) :
    ArtGallery.segment (γ.eval x) (c.eval x) ⊆ P.filled := by
  obtain ⟨ht, hv, hp⟩ := h
  rw [holds_bigAnd_range] at ht hv hp
  let T : Finset ℝ := (Finset.range (2 * P.n + 2)).image fun α => (tTerm base α).eval x
  have hmemT : ∀ α < 2 * P.n + 2, (tTerm base α).eval x ∈ T := fun α hα =>
    Finset.mem_image.2 ⟨α, Finset.mem_range.2 hα, rfl⟩
  have h0 : (0 : ℝ) ∈ T := by
    have := hmemT 0 (by omega); simpa [tTerm] using this
  have h1 : (1 : ℝ) ∈ T := by
    have := hmemT 1 (by omega); simpa [tTerm] using this
  refine segment_subset_filled_of_breakpoints hP T h0 h1 ?_ ?_ ?_
  · intro j hj s hD hs
    have htj := ht j hj
    simp only [tDefF, holds_or, holds_eq, eval_add, eval_mul, eval_crossT, eval_detT, eval_var,
      eval_zero, hx j hj, hx _ (succ_mod_lt hj)] at htj
    rcases htj with e | e
    · have : crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) (γ.eval x) (c.eval x) *
          (x (base + j) - s) = 0 := by linear_combination e - hs
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hD
      · have hm := hmemT (j + 2) (by omega)
        rw [tTerm_eval_of_ge (by omega), show base + (j + 2) - 2 = base + j by omega] at hm
        rwa [show s = x (base + j) by linarith]
    · exact absurd e hD
  · intro hγc k hk s hs0 hs1 hs
    have hvk := hv k hk
    simp only [vDefF, holds_or, holds_ptEq, holds_not, holds_onSegF, eval_lerpT, eval_var,
      hx k hk] at hvk
    rcases hvk with e | e
    · have := lerp_injective hγc (e.trans hs.symm)
      have hm := hmemT (P.n + k + 2) (by omega)
      rw [tTerm_eval_of_ge (by omega),
        show base + (P.n + k + 2) - 2 = base + P.n + k by omega] at hm
      rwa [← this]
    · exact absurd (hs ▸ lerp_mem_segment _ _ hs0 hs1) e
  · intro a ha b hb ha0 ha1 hb0 hb1
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_range] at hα hβ
    have hpp := hp (α * (2 * P.n + 2) + β) (pair_lt hα hβ)
    rw [pairF, pair_div hβ, pair_mod hβ, holds_fImp] at hpp
    obtain ⟨e, hpd, hin⟩ := hpp ⟨(holds_unitF _ _).2 ⟨ha0, ha1⟩, (holds_unitF _ _).2 ⟨hb0, hb1⟩⟩
    rw [holds_insideF hP hx hpd] at hin
    simp only [holds_eq, eval_add, eval_var] at e
    simp only [eval_lerpT, eval_var] at hin
    rwa [show x (pairBase P.n base (α * (2 * P.n + 2) + β)) =
      ((tTerm base α).eval x + (tTerm base β).eval x) / 2 by linarith] at hin

/-! ## Completeness -/

/-- The value of `t_j` in the canonical assignment. -/
noncomputable def tVal (P : Polygon) (γ c : Point) (j : ℕ) : ℝ :=
  if crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c = 0 then 0
  else -det (P.vtx j) (P.vtx ((j + 1) % P.n)) γ / crossR (P.vtx j) (P.vtx ((j + 1) % P.n)) γ c

open Classical in
/-- The value of `t'_k` in the canonical assignment. -/
noncomputable def tVal' (P : Polygon) (γ c : Point) (k : ℕ) : ℝ :=
  if h : P.vtx k ∈ ArtGallery.segment γ c then Classical.choose h else 0

theorem FVars_unitF {S : ℕ → Prop} {t : Term} (ht : TVars S t) : FVars S (unitF t) :=
  ⟨⟨trivial, ht⟩, ⟨ht, trivial⟩⟩

theorem TVars_tTerm {S : ℕ → Prop} {base α : ℕ} (h : 2 ≤ α → S (base + α - 2)) :
    TVars S (tTerm base α) := by
  unfold tTerm
  split_ifs with h0 h1
  · trivial
  · trivial
  · exact h (by omega)

theorem FVars_pairF {S : ℕ → Prop} {n : ℕ} {γ c : PTerm} {base p : ℕ} (hγ : PVars S γ)
    (hc : PVars S c) (hv : VtxVars S n) (hT : ∀ i < 2 * n, S (base + i))
    (hblk : ∀ e ≤ n, S (pairBase n base p + e)) (hp : p < (2 * n + 2) * (2 * n + 2)) :
    FVars S (pairF n γ c base p) := by
  have hN : 0 < 2 * n + 2 := by omega
  have hα : p / (2 * n + 2) < 2 * n + 2 := Nat.div_lt_of_lt_mul hp
  have hβ : p % (2 * n + 2) < 2 * n + 2 := Nat.mod_lt _ hN
  have ha : TVars S (tTerm base (p / (2 * n + 2))) :=
    TVars_tTerm fun h2 => by
      have := hT (p / (2 * n + 2) - 2) (by omega)
      rwa [show base + (p / (2 * n + 2) - 2) = base + p / (2 * n + 2) - 2 by omega] at this
  have hb : TVars S (tTerm base (p % (2 * n + 2))) :=
    TVars_tTerm fun h2 => by
      have := hT (p % (2 * n + 2) - 2) (by omega)
      rwa [show base + (p % (2 * n + 2) - 2) = base + p % (2 * n + 2) - 2 by omega] at this
  have hh : TVars S (.var (pairBase n base p)) := by
    have := hblk 0 (by omega); simpa using this
  have hq : PVars S (lerpT γ c (.var (pairBase n base p))) := PVars_lerpT hγ hc hh
  have hpar : ∀ e < n, S (pairBase n base p + 1 + e) := fun e he => by
    have := hblk (e + 1) (by omega); rwa [show pairBase n base p + (e + 1) =
      pairBase n base p + 1 + e by omega] at this
  exact ⟨⟨FVars_unitF ha, FVars_unitF hb⟩, ⟨⟨hh, hh⟩, ⟨ha, hb⟩⟩,
    FVars_parDefF hq hv hpar, FVars_insideF hq hv hpar⟩

theorem FVars_seesF {S : ℕ → Prop} {n : ℕ} {γ c : PTerm} {base : ℕ} (hγ : PVars S γ)
    (hc : PVars S c) (hv : VtxVars S n)
    (hb : ∀ v, base ≤ v → v < base + seesSize n → S v) : FVars S (seesF n γ c base) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FVars_bigAnd]
    intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨j, hj, rfl⟩ := hφ
    have hD := TVars_crossT (hv.pv hj) (hv.pv (succ_mod_lt hj)) hγ hc
    have hs : S (base + j) := hb _ (by omega) (by unfold seesSize; omega)
    exact ⟨⟨⟨⟨hD, hs⟩, TVars_detT (hv.pv hj) (hv.pv (succ_mod_lt hj)) hγ⟩, trivial⟩, ⟨hD, trivial⟩⟩
  · rw [FVars_bigAnd]
    intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨k, hk, rfl⟩ := hφ
    have hs : S (base + n + k) := hb _ (by omega) (by unfold seesSize; omega)
    exact ⟨FVars_ptEq (PVars_lerpT hγ hc hs) (hv.pv hk), FVars_onSegF (hv.pv hk) hγ hc⟩
  · rw [FVars_bigAnd]
    intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨p, hp, rfl⟩ := hφ
    have hle : (p + 1) * (n + 1) ≤ (2 * n + 2) * (2 * n + 2) * (n + 1) :=
      Nat.mul_le_mul_right _ hp
    refine FVars_pairF hγ hc hv (fun i hi => hb _ (by omega) (by unfold seesSize; omega))
      (fun e he => hb _ (by unfold pairBase; omega) ?_) hp
    unfold pairBase seesSize
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega

/-- **SEES is complete**: if the segment lies in the region, the fresh variables can be chosen
to satisfy SEES. -/
theorem exists_sees_holds {P : Polygon} (hP : P.Simple) {x : ℕ → ℝ} (hx : VtxOK P x)
    {γ c : PTerm} {base : ℕ} (hγ : PVars (· < base) γ) (hc : PVars (· < base) c)
    (hb : 2 * P.n ≤ base) (hseg : ArtGallery.segment (γ.eval x) (c.eval x) ⊆ P.filled) :
    ∃ y : ℕ → ℝ, (∀ v < base, y v = x v) ∧ (seesF P.n γ c base).Holds y := by
  let y1 : ℕ → ℝ := fun v =>
    if base ≤ v ∧ v < base + P.n then tVal P (γ.eval x) (c.eval x) (v - base)
    else if base + P.n ≤ v ∧ v < base + 2 * P.n then tVal' P (γ.eval x) (c.eval x) (v - base - P.n)
    else x v
  have hy1 : ∀ v < base, y1 v = x v := fun v hv => by
    simp only [y1]
    split_ifs with h1 h2
    · exfalso; omega
    · exfalso; omega
    · rfl
  have hy1t : ∀ j < P.n, y1 (base + j) = tVal P (γ.eval x) (c.eval x) j := fun j hj => by
    simp only [y1]
    split_ifs with h1 h2
    · rw [show base + j - base = j by omega]
    · exfalso; omega
    · exfalso; omega
  have hy1t' : ∀ k < P.n, y1 (base + P.n + k) = tVal' P (γ.eval x) (c.eval x) k := fun k hk => by
    simp only [y1]
    split_ifs with h1 h2
    · exfalso; omega
    · rw [show base + P.n + k - base - P.n = k by omega]
    · exfalso; omega
  have hγ1 : γ.eval y1 = γ.eval x := PTerm.eval_congr (S := (· < base)) hy1 hγ
  have hc1 : c.eval y1 = c.eval x := PTerm.eval_congr (S := (· < base)) hy1 hc
  have hx1 : VtxOK P y1 := hx.congr fun v hv => hy1 v (by omega)
  -- the pair blocks
  have hvars : ∀ p < (2 * P.n + 2) * (2 * P.n + 2),
      FVars (InBlock (base + 2 * P.n) (P.n + 1) p) (pairF P.n γ c base p) := by
    intro p hp
    refine FVars_pairF (hγ.mono fun v hv => Or.inl (by omega))
      (hc.mono fun v hv => Or.inl (by omega))
      ((vtxVars_lt hb).mono fun v hv => Or.inl (by omega)) (fun i hi => Or.inl (by omega))
      (fun e he => Or.inr ⟨by unfold pairBase; omega, by unfold pairBase; omega⟩) hp
  have hex : ∀ p < (2 * P.n + 2) * (2 * P.n + 2), ∃ y : ℕ → ℝ,
      (∀ v < base + 2 * P.n, y v = y1 v) ∧ (pairF P.n γ c base p).Holds y := by
    intro p hp
    have hα : p / (2 * P.n + 2) < 2 * P.n + 2 := Nat.div_lt_of_lt_mul hp
    have hβ : p % (2 * P.n + 2) < 2 * P.n + 2 := Nat.mod_lt _ (by omega)
    have hAv : TVars (· < base + 2 * P.n) (tTerm base (p / (2 * P.n + 2))) :=
      TVars_tTerm fun h2 => by show _ < _; omega
    have hBv : TVars (· < base + 2 * P.n) (tTerm base (p % (2 * P.n + 2))) :=
      TVars_tTerm fun h2 => by show _ < _; omega
    by_cases hu : 0 ≤ (tTerm base (p / (2 * P.n + 2))).eval y1 ∧
        (tTerm base (p / (2 * P.n + 2))).eval y1 ≤ 1 ∧
        0 ≤ (tTerm base (p % (2 * P.n + 2))).eval y1 ∧
        (tTerm base (p % (2 * P.n + 2))).eval y1 ≤ 1
    · obtain ⟨hval, hhv⟩ : ∃ h : ℝ, h = ((tTerm base (p / (2 * P.n + 2))).eval y1 +
          (tTerm base (p % (2 * P.n + 2))).eval y1) / 2 := ⟨_, rfl⟩
      have hpb : base + 2 * P.n ≤ pairBase P.n base p := by unfold pairBase; omega
      let y2 : ℕ → ℝ := Function.update y1 (pairBase P.n base p) hval
      have hy2 : ∀ v < pairBase P.n base p, y2 v = y1 v := fun v hv => by
        simp [y2, show v ≠ pairBase P.n base p by omega]
      have hx2 : VtxOK P y2 := hx1.congr fun v hv => hy2 v (by omega)
      have hq : PVars (· < pairBase P.n base p + 1) (lerpT γ c (.var (pairBase P.n base p))) :=
        PVars_lerpT (hγ.mono fun v hv => by omega) (hc.mono fun v hv => by omega)
          (show pairBase P.n base p < pairBase P.n base p + 1 by omega)
      obtain ⟨y3, hy3, hpd⟩ := exists_parDef hx2 hq (by omega)
      have hy31 : ∀ v < base + 2 * P.n, y3 v = y1 v := fun v hv => by
        rw [hy3 v (by omega), hy2 v (by omega)]
      refine ⟨y3, hy31, ?_⟩
      rw [pairF, holds_fImp]
      intro _
      have hy3pb : y3 (pairBase P.n base p) = hval := by
        rw [hy3 _ (by omega)]; simp [y2]
      have hA3 := eval_congr (S := (· < base + 2 * P.n)) hy31 hAv
      have hB3 := eval_congr (S := (· < base + 2 * P.n)) hy31 hBv
      have hx3 : VtxOK P y3 := hx2.congr fun v hv => hy3 v (by omega)
      have hγ3 : γ.eval y3 = γ.eval x := by
        rw [← hγ1]; exact PTerm.eval_congr (S := (· < base)) (fun v hv => hy31 v (by omega)) hγ
      have hc3 : c.eval y3 = c.eval x := by
        rw [← hc1]; exact PTerm.eval_congr (S := (· < base)) (fun v hv => hy31 v (by omega)) hc
      refine ⟨?_, hpd, ?_⟩
      · simp only [holds_eq, eval_add, eval_var, hy3pb, hA3, hB3, hhv]; ring
      · rw [holds_insideF hP hx3 hpd, eval_lerpT, eval_var, hy3pb, hγ3, hc3]
        apply hseg
        exact lerp_mem_segment _ _ (by rw [hhv]; linarith [hu.1, hu.2.2.1])
          (by rw [hhv]; linarith [hu.2.1, hu.2.2.2])
    · refine ⟨y1, fun _ _ => rfl, ?_⟩
      rw [pairF, holds_fImp]
      intro h
      rw [holds_and, holds_unitF, holds_unitF] at h
      exact absurd ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩ hu
  obtain ⟨y, hy, hall⟩ := exists_glue hvars hex
  have hyx : ∀ v < base, y v = x v := fun v hv => by rw [hy v (by omega), hy1 v hv]
  have hVb : VtxVars (· < base + 2 * P.n) P.n := vtxVars_lt (by omega)
  have hγ2 : PVars (· < base + 2 * P.n) γ := hγ.mono fun v hv => by omega
  have hc2 : PVars (· < base + 2 * P.n) c := hc.mono fun v hv => by omega
  refine ⟨y, hyx, ?_, ?_, ?_⟩
  · rw [holds_bigAnd_range]
    intro j hj
    have hD := TVars_crossT (hVb.pv hj) (hVb.pv (succ_mod_lt hj)) hγ2 hc2
    have hS : FVars (· < base + 2 * P.n) (tDefF P.n γ c base j) :=
      ⟨⟨⟨⟨hD, show base + j < base + 2 * P.n by omega⟩,
        TVars_detT (hVb.pv hj) (hVb.pv (succ_mod_lt hj)) hγ2⟩, trivial⟩, ⟨hD, trivial⟩⟩
    rw [holds_congr_lt hy hS]
    simp only [tDefF, holds_or, holds_eq, eval_add, eval_mul, eval_crossT, eval_detT, eval_var,
      eval_zero, hγ1, hc1, hx1 j hj, hx1 _ (succ_mod_lt hj), hy1t j hj]
    unfold tVal
    split_ifs with hD0
    · right; exact hD0
    · left; field_simp; ring
  · rw [holds_bigAnd_range]
    intro k hk
    have hS : FVars (· < base + 2 * P.n) (vDefF P.n γ c base k) :=
      ⟨FVars_ptEq (PVars_lerpT hγ2 hc2 (show base + P.n + k < base + 2 * P.n by omega))
        (hVb.pv hk), FVars_onSegF (hVb.pv hk) hγ2 hc2⟩
    rw [holds_congr_lt hy hS]
    simp only [vDefF, holds_or, holds_ptEq, holds_not, holds_onSegF, eval_lerpT, eval_var, hγ1,
      hc1, hx1 k hk, hy1t' k hk]
    unfold tVal'
    split_ifs with hk'
    · left; exact ((Classical.choose_spec hk').2.2).symm
    · right; exact hk'
  · rw [holds_bigAnd_range]; exact hall

end ArtGallery.Membership

end
