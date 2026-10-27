module

public import ArtGallery.Hardness.Sec5.ConstraintTools

/-!
# Section 5, constraints (iv): the corridor copies values exactly

Let `I` be a good corridor input sitting in a simple counter-clockwise polygon `Q`
(`CorridorAt`, `CorridorClear`), with the unit room `K` (door the entrance), and let `G` be a set
of points seeing all of `Q` (a guard set).  Fix a pair `k` of the corridor: base slot `σ_k`,
receiver `τ_k`.  Suppose every point of `G` is

* a base guard `(27σ/2 + s, 0)` (`s ∈ [0, 3/2]`), with offset `s = t` if `σ = σ_k`;
* a foreign point (another unit of the same side, or the other side, `Foreign`);
* a corridor stationary guard `p_j`;
* the receiver guard `m + (T_τ + (t', 0))/S` of `τ_k`;
* or a template point `m + T/S` whose coordinate sum is far from that of the receiver `τ_k`
  (`FarTmpl`, this covers the other receivers and all other template positions).

Then **`t = t'`** (`Good.copy_eq`): if `t' < t` an umbra critical point strictly above the axis
is seen by nobody (`umbra_gap`; the base guard sees only through the entrance, the receiver only
through the window, all other guards are excluded by `sg_not_sees_umbra`, the band lemmas and
`foreign_not_sees_corr`); if `t < t'` a point of the nook top edge is seen by nobody
(`nook_gap`; a guard seeing a point of the top edge sees it past the mouth corner `z0` resp. `z1`:
`west_wall`, `east_wall`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon
open Corridor (Input CorridorAt CopyPair c0 c1 d0 d1 place Oc xiOf Xis RecvHyp)
open Corridor.Input
open ArtGallery.Sec5.Count (unitBox)

/-- A template point `m + T/S` (`|T| ≤ 50`) whose coordinate sum is at least `5` above or `4`
below that of the receiver of pair `k`. -/
def FarTmpl (I : Input) (k : ℕ) (g : Point) : Prop :=
  ∃ T : Point, -50 ≤ T.1 ∧ T.1 ≤ 50 ∧ -50 ≤ T.2 ∧ T.2 ≤ 50 ∧
    (((I.T0.1 : ℚ) : ℝ) + ((I.T0.2 : ℚ) : ℝ) - 27 * (I.tau k : ℝ) / 2 + 5 ≤ T.1 + T.2 ∨
      T.1 + T.2 ≤ ((I.T0.1 : ℚ) : ℝ) + ((I.T0.2 : ℚ) : ℝ) - 27 * (I.tau k : ℝ) / 2 - 4) ∧
    g = place (I.S : ℝ) (I.H : ℝ) T

/-- The classes of guards seen from the corridor of pair `k` (see the module docstring). -/
def CopyClass (I : Input) (N : ℚ) (k : ℕ) (t t' : ℝ) (g : Point) : Prop :=
  (∃ σ : ℕ, ∃ s : ℝ, 0 ≤ s ∧ s ≤ 3 / 2 ∧ 27 * (σ : ℝ) / 2 + s ≤ 14 * N ∧
      g = (27 * (σ : ℝ) / 2 + s, 0) ∧ (σ = I.sigma k → s = t)) ∨
    Foreign (I.S : ℝ) (I.H : ℝ) (N : ℝ) g ∨
    (∃ j < I.np, g = ratPoint (I.sgPt j)) ∨
    g = place (I.S : ℝ) (I.H : ℝ) (((I.Tt (I.tau k)).1 : ℝ) + t', ((I.Tt (I.tau k)).2 : ℝ)) ∨
    FarTmpl I k g

section Near

variable {I : Input} {N : ℚ} (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The umbra critical points are within `1/5` of `O_c`. -/
theorem Good.umbra_near {v₀ v₁ : ℝ} (h₀ : 0 ≤ v₀) (h₀' : v₀ ≤ 3 / 2) (h₁ : 0 ≤ v₁)
    (h₁' : v₁ ≤ 3 / 2) :
    |((I.umbraR k).X v₀ v₁).1 - ((I.S : ℝ) + 1)| ≤ 1 / 5 ∧
      |((I.umbraR k).X v₀ v₁).2 - ((I.H : ℝ) + 1)| ≤ 1 / 5 := by
  obtain ⟨-, -, -, -, hzX, hzY1, hzY2⟩ := hg.umbra_crit_eps hk h₀ h₀' h₁ h₁'
  set z := (I.umbraR k).X v₀ v₁
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hw : |(((I.rwE k - I.lwE k) / 2 : ℚ) : ℝ)| + 20 ≤ 456 * (N : ℝ) := by
    have h' := Corridor.rat_cast_le_of (hg.window_apex hk)
    push_cast at h' ⊢; exact h'
  have hab : |(((I.lwE k + I.rwE k) / 2 : ℚ) : ℝ)| ≤ 68 * (N : ℝ) + 410 := by
    have h' := Corridor.rat_cast_le_of (hg.ab_bound hk)
    push_cast at h' ⊢; exact h'
  push_cast at hw hab
  have hw2 : |(((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2| ≤ 456 * (N : ℝ) - 20 := by
    linarith
  rw [abs_le] at hzX hw2 hab
  exact ⟨hg.near_of_lXR (by rw [abs_le]; constructor <;> linarith),
    hg.near_of_lYR (by rw [abs_le]; constructor <;> linarith)⟩

/-- The nook top edge is within `1/5` of `O_c`. -/
theorem Good.nook_near {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k))) :
    |z.1 - ((I.S : ℝ) + 1)| ≤ 1 / 5 ∧ |z.2 - ((I.H : ℝ) + 1)| ≤ 1 / 5 := by
  obtain ⟨-, -, -, -, hx1, hx2, hy1, hy2⟩ := hg.nook_edge_loc hk hz
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hw : |(((I.rwE k - I.lwE k) / 2 : ℚ) : ℝ)| + 20 ≤ 456 * (N : ℝ) := by
    have h' := Corridor.rat_cast_le_of (hg.window_apex hk)
    push_cast at h' ⊢; exact h'
  have hab : |(((I.lwE k + I.rwE k) / 2 : ℚ) : ℝ)| ≤ 68 * (N : ℝ) + 410 := by
    have h' := Corridor.rat_cast_le_of (hg.ab_bound hk)
    push_cast at h' ⊢; exact h'
  push_cast at hw hab
  have hw2 : |(((I.rwE k : ℚ) : ℝ) - ((I.lwE k : ℚ) : ℝ)) / 2| ≤ 456 * (N : ℝ) - 20 := by
    linarith
  rw [abs_le] at hw2 hab
  exact ⟨hg.near_of_lXR (by rw [abs_le]; constructor <;> linarith),
    hg.near_of_lYR (by rw [abs_le]; constructor <;> linarith)⟩

end Near


/-! ### Seeing the nook top edge -/

section NookWalls

variable {I : Input} {N : ℚ} (hg : I.Good N) {Q : Polygon} {a b : ℕ} (hP : Q.Simple)
  (hL : Q.InteriorLeft) (hC : CorridorAt Q I a b) {k : ℕ} (hk : k < I.np)
include hg hP hL hC hk

/-- The mouth corners lie below the top-edge ends, and the top edge runs from `x = z0.x` to
`x = z1.x`. -/
theorem Good.nook_heights : ((I.z0 k).2 : ℝ) < (I.n0 k).2 ∧ ((I.z1 k).2 : ℝ) < (I.n1 k).2 := by
  have hS := hg.S_pos
  have h0 := hg.lY_n0 hk
  have h1 := hg.lY_n1 hk
  have e0 := lY_z0 hg hk
  have e1 := lY_z1 hg hk
  rw [abs_le] at h0 h1
  simp only [lY_def] at h0 h1 e0 e1
  have a0 : (I.z0 k).2 < (I.n0 k).2 := by
    by_contra hc; push Not at hc
    have : 8 * I.S * ((I.n0 k).2 - (I.H + 1)) ≤ 8 * I.S * ((I.z0 k).2 - (I.H + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have a1 : (I.z1 k).2 < (I.n1 k).2 := by
    by_contra hc; push Not at hc
    have : 8 * I.S * ((I.n1 k).2 - (I.H + 1)) ≤ 8 * I.S * ((I.z1 k).2 - (I.H + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  exact ⟨by exact_mod_cast a0, by exact_mod_cast a1⟩

omit hg hP hL hC hk in
/-- A point of the top edge strictly between the walls is an interior point of the edge
`n1 → n0`. -/
theorem nook_lerp {z : Point}
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k)))
    (hz0 : ((I.z0 k).1 : ℝ) < z.1) (hz1 : z.1 < ((I.z1 k).1 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = Geometry.lerp (ratPoint (I.n1 k)) (ratPoint (I.n0 k)) t := by
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  have e0 : (ratPoint (I.n0 k)).1 = ((I.z0 k).1 : ℝ) := rfl
  have e1 : (ratPoint (I.n1 k)).1 = ((I.z1 k).1 : ℝ) := rfl
  simp only [Geometry.lerp_fst, e0, e1] at hz0 hz1
  refine ⟨1 - s, ?_, ?_, ?_⟩
  · rcases eq_or_lt_of_le hs1 with h | h
    · subst h; linarith
    · linarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; linarith
    · linarith
  · simp only [Geometry.lerp]; ext <;> simp only <;> ring

/-- **A point west of the nook sees its top edge only past `z0`.** -/
theorem Good.nook_west {p z : Point} (hp : p.1 < ((I.z0 k).1 : ℝ))
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k)))
    (hz0 : ((I.z0 k).1 : ℝ) < z.1) (hz1 : z.1 < ((I.z1 k).1 : ℝ)) (hs : Q.Sees p z) :
    det p (ratPoint (I.z0 k)) z ≤ 0 := by
  have hn : 0 < Q.n := by have := hP.1; omega
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
  have hA' : I.chainAfter = (A₁ ++ [I.sgPt k, I.zp k, I.z1 k]) ++ [I.n1 k, I.n0 k, I.z0 k] ++
      ([I.nxt k] ++ A₂) := by rw [hA]; simp
  obtain ⟨v1, v0, v2, e0, e1⟩ := Corridor.vtx_triple hn hC.after hA'
  obtain ⟨t, ht0, ht1, hzt⟩ := nook_lerp hz hz0 hz1
  exact west_wall hP hL (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) v0 v1 v2 e0 e1 rfl
    (Good.nook_heights hg hP hL hC hk).1 (by show ((I.z0 k).1 : ℝ) < (I.z1 k).1; linarith)
    hp ht0 ht1 hzt hs

/-- **A point east of the nook sees its top edge only past `z1`.** -/
theorem Good.nook_east {q z : Point} (hq : ((I.z1 k).1 : ℝ) < q.1)
    (hz : z ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k)))
    (hz0 : ((I.z0 k).1 : ℝ) < z.1) (hz1 : z.1 < ((I.z1 k).1 : ℝ)) (hs : Q.Sees q z) :
    0 ≤ det q (ratPoint (I.z1 k)) z := by
  have hn : 0 < Q.n := by have := hP.1; omega
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
  have hA' : I.chainAfter = (A₁ ++ [I.sgPt k, I.zp k]) ++ [I.z1 k, I.n1 k, I.n0 k] ++
      ([I.z0 k, I.nxt k] ++ A₂) := by rw [hA]; simp
  obtain ⟨v1, v0, v2, e0, e1⟩ := Corridor.vtx_triple hn hC.after hA'
  obtain ⟨t, ht0, ht1, hzt⟩ := nook_lerp hz hz0 hz1
  exact east_wall hP hL (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) v0 v1 v2 e0 e1 rfl
    (Good.nook_heights hg hP hL hC hk).2 (by show ((I.z0 k).1 : ℝ) < (I.z1 k).1; linarith)
    hq ht0 ht1 hzt hs

end NookWalls


/-! ### The copy lemma -/

section Copy

variable {I : Input} {N : ℚ} (hg : I.Good N) {Q : Polygon} {a b : ℕ} (hP : Q.Simple)
  (hL : Q.InteriorLeft) (hC : CorridorAt Q I a b) (hcl : CorridorClear Q I) {K : Set Point}
  (hK : Q.IsRoom K I.entrance) (hKb : K ⊆ unitBox I.S I.H) (hc1K : ratPoint (c1 I.S I.H) ∈ K)
  {G : Set Point} (hcov : ∀ z ∈ Q.filled, ∃ g ∈ G, Q.Sees g z) {k : ℕ} (hk : k < I.np)
include hg hP hL hC hcl hK hKb hc1K hcov hk

/-- The receiver guard lies east of the window. -/
theorem Good.recv_east {t' : ℝ} (ht0' : 0 ≤ t') (_ht1' : t' ≤ 3 / 2) :
    (I.S : ℝ) + 2 < (place (I.S : ℝ) (I.H : ℝ)
      (((I.Tt (I.tau k)).1 : ℝ) + t', ((I.Tt (I.tau k)).2 : ℝ))).1 := by
  obtain ⟨hS8, -, -, -, -, -, -⟩ := Good.realFacts hg
  obtain ⟨T1, -, -, -⟩ := hg.T_bound _ (hg.tau_lt hk)
  have T1' : (-50 : ℝ) ≤ ((I.Tt (I.tau k)).1 : ℝ) := by exact_mod_cast T1
  simp only [place]
  have : -1 < (((I.Tt (I.tau k)).1 : ℝ) + t') / I.S := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  linarith

/-- **The copy lemma (iv).**  The base guard of slot `σ_k` and the receiver guard of `τ_k` have
the same offset. -/
theorem Good.copy_eq {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) (ht0' : 0 ≤ t')
    (ht1' : t' ≤ 3 / 2) (hcls : ∀ g ∈ G, CopyClass I N k t t' g) : t = t' := by
  obtain ⟨hS8, hN, hSN, hH1, hH2, hρ0, hρ1⟩ := Good.realFacts hg
  have hqE := Good.recv_east hg hP hL hC hcl hK hKb hc1K hcov hk ht0' ht1'
  have hσN : 27 * (I.sigma k : ℝ) / 2 + 3 / 2 ≤ 14 * N := by
    have := Corridor.rat_cast_le_of (hg.slot_le k hk)
    push_cast at this; exact this
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · -- `t < t'`: a nook critical point is not seen
    exfalso
    set v := (t + t') / 2 with hv
    have hC' := nookR_hyp hg.toValid k
    have hA := nookR_adm hg.toValid hk
    have hG := CopyPair.G_pos hC' hA (t₀ := v) (t₁ := v) (by linarith) (by linarith)
    obtain ⟨hgap, -⟩ := CopyPair.nook_gap hC' (CopyPair.w_X_pos hC' hA (by linarith)
      (by linarith)) ((I.nookR k).det2_X_left v v) ((I.nookR k).det2_X_right hG.ne')
      (by linarith : t < v) (by linarith : v < t')
    have hzE := hg.nookR_X_mem_edge hk (v := v) (by linarith) (by linarith)
    have hzx := CopyPair.X_fst_mem hC' hA (t₀ := v) (t₁ := v) (by linarith) (by linarith)
    rw [nookR_k0, nookR_k1] at hzx
    set z := (I.nookR k).X v v
    have hzP : z ∈ I.poly.filled :=
      Polygon.boundary_subset_filled _ (hg.nook_edge_boundary hk hzE)
    have hzQ := hg.poly_subset hP hL hC hcl hzP
    obtain ⟨hnx, hny⟩ := Good.nook_near hg hk hzE
    obtain ⟨hband, -, hxi⟩ := hg.nook_edge_band hk hzE
    have hn0 := (Good.nook_near hg hk (Geometry.left_mem_segment _ _)).1
    have hn1 := (Good.nook_near hg hk (Geometry.right_mem_segment _ _)).1
    have e0 : (ratPoint (I.n0 k)).1 = ((I.z0 k).1 : ℝ) := rfl
    have e1 : (ratPoint (I.n1 k)).1 = ((I.z1 k).1 : ℝ) := rfl
    rw [e0, abs_le] at hn0
    rw [e1, abs_le] at hn1
    obtain ⟨g, hgG, hgs⟩ := hcov z hzQ
    rcases hcls g hgG with ⟨σ, s, hs0, hs1, hsx, rfl, hst⟩ | hf | ⟨j, hj, rfl⟩ | rfl |
        ⟨T, a1, a2, a3, a4, hfar, rfl⟩
    · by_cases hσ : σ = I.sigma k
      · rw [hσ, hst hσ] at hgs
        have h := Good.nook_west hg hP hL hC hk (p := (27 * (I.sigma k : ℝ) / 2 + t, 0))
          (by simp only; nlinarith) hzE hzx.1 hzx.2 hgs
        apply hgap; left
        rw [nookR_p, nookR_k0, ← Corridor.det_eq_det2]; exact h
      · exact hg.base_not_sees_nook hP hL hC hk (Ne.symm hσ) hs0 hs1 (by linarith) hzE hgs
    · exact Good.foreign_not_sees_corr hg hP hL hC hcl hK hKb hc1K hzP hnx hny hf hgs
    · exact hg.sg_not_sees_nook hP hL hC hj hk hzE hgs
    · have h := Good.nook_east hg hP hL hC hk (by linarith) hzE hzx.1 hzx.2 hgs
      apply hgap; right
      rw [nookR_q, nookR_k1, ← Corridor.det_eq_det2]; exact h
    · exact Good.tmpl_not_sees_band hg hP hL hC a1 a2 a3 a4 hfar hzP hband hxi hgs
  · exact heq
  · -- `t' < t`: an umbra critical point is not seen
    exfalso
    set v₁ := t' + (t - t') / 3 with hv₁
    set v₀ := t' + 2 * (t - t') / 3 with hv₀
    have h₀ : 0 ≤ v₀ := by rw [hv₀]; linarith
    have h₀' : v₀ ≤ 3 / 2 := by rw [hv₀]; linarith
    have h₁ : 0 ≤ v₁ := by rw [hv₁]; linarith
    have h₁' : v₁ ≤ 3 / 2 := by rw [hv₁]; linarith
    have hv : v₁ < v₀ := by rw [hv₀, hv₁]; linarith
    have hC' := umbraR_hyp hg.toValid k
    have hA := umbraR_adm hg.toValid hk
    have hG := CopyPair.G_pos hC' hA (t₀ := v₀) (t₁ := v₁) h₀' h₁
    obtain ⟨hgap, -, -⟩ := CopyPair.umbra_gap hC' (CopyPair.w_X_pos hC' hA h₀' h₁)
      ((I.umbraR k).det2_X_left v₀ v₁) ((I.umbraR k).det2_X_right hG.ne')
      (by rw [hv₀]; linarith : v₀ < t) (by rw [hv₁]; linarith : t' < v₁) hv.le
    set z := (I.umbraR k).X v₀ v₁
    have hzP : z ∈ I.poly.filled := (hg.umbra_crit_mem hk h₀ h₀' h₁ h₁').1
    have hzQ := hg.poly_subset hP hL hC hcl hzP
    obtain ⟨hnx, hny⟩ := Good.umbra_near hg hk h₀ h₀' h₁ h₁'
    have hband := (hg.umbra_crit_loc hk h₀ h₀' h₁ h₁').1
    have hxi := (hg.umbra_crit_band hk h₀ h₀' h₁ h₁').2
    rw [abs_le] at hnx
    obtain ⟨g, hgG, hgs⟩ := hcov z hzQ
    rcases hcls g hgG with ⟨σ, s, hs0, hs1, hsx, rfl, hst⟩ | hf | ⟨j, hj, rfl⟩ | rfl |
        ⟨T, a1, a2, a3, a4, hfar, rfl⟩
    · by_cases hσ : σ = I.sigma k
      · rw [hσ, hst hσ] at hgs
        have h := (hg.sees_through_entrance hP hL hC (g := (27 * (I.sigma k : ℝ) / 2 + t, 0))
          (by simp only; nlinarith) hzP (by linarith) hgs).1
        apply hgap; left
        rw [umbraR_p, umbraR_k0, ← Corridor.det_eq_det2]; exact h
      · exact hg.base_not_sees_umbra hP hL hC hk (Ne.symm hσ) hs0 hs1 (by linarith) h₀ h₀' h₁
          h₁' hgs
    · rw [← abs_le] at hnx
      exact Good.foreign_not_sees_corr hg hP hL hC hcl hK hKb hc1K hzP hnx hny hf hgs
    · exact hg.sg_not_sees_umbra hP hL hC hj hk h₁ hv h₀' hgs
    · have h := (hg.sees_through_window hP hL hC hqE hzP (by linarith) hgs).1
      apply hgap; right
      rw [umbraR_q, umbraR_k1, ← Corridor.det_eq_det2]; exact h
    · exact Good.tmpl_not_sees_band hg hP hL hC a1 a2 a3 a4 hfar hzP hband hxi hgs

end Copy

end ArtGallery.Sec5.Constraint

end
