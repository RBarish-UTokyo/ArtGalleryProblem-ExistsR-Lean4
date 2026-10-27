module

public import ArtGallery.Hardness.Sec5.Corridor.Poly

/-!
# Section 5: corridors — the nook top edge contains the nook critical segment

The crossing points of a copy pair lie strictly between its shadow corners (`CopyPair.X_fst_mem`).
For the nook pair (shadow corners `z0`, `z1`, the mouth of the nook) this puts the nook critical
segment `[F1, F0]` strictly inside the abscissa range `[z0.x, z1.x]` of the nook top edge
`[n0, n1]` (both on the nook axis), hence `[F1, F0] ⊆ [n0, n1]` (`Good.nook_crit_subset`), and
every critical point `X v v` (`v ∈ [0, 3/2]`) of the nook copy statement `nook_copy_iff` lies on the
top edge (`Good.nookR_X_mem_edge`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

namespace CopyPair

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {C : CopyPair K}

/-- **Crossing points lie between the shadow corners.** -/
theorem X_fst_mem (hC : C.Hyp) {ℓ : K} (hA : C.Adm ℓ) {t₀ t₁ : K} (h₀ : t₀ ≤ ℓ) (h₁ : 0 ≤ t₁) :
    C.k0.1 < (C.X t₀ t₁).1 ∧ (C.X t₀ t₁).1 < C.k1.1 := by
  have hG := G_pos hC hA h₀ h₁
  rw [C.X_eq hC.hk hG.ne', lam]
  simp only
  have hp' : (C.p t₀).1 < C.k0.1 := by
    have := hA.hp; simp only [p] at this ⊢; nlinarith [hC.hs0]
  have hq' : C.k1.1 < (C.q t₁).1 := by
    have := hA.hq; simp only [q] at this ⊢; nlinarith [hC.hs1]
  have h1 := sub_pos.2 hA.hy1
  have h2 := sub_pos.2 hA.hk01
  have h3 := sub_pos.2 hp'
  have h4 := sub_pos.2 hA.hy0
  have h5 := sub_pos.2 hq'
  constructor
  · have : 0 < (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) / C.G t₀ t₁ * (C.k0.1 - (C.p t₀).1) := by
      positivity
    linarith
  · have hGdef : C.G t₀ t₁ = (C.k0.1 - (C.p t₀).1) * (C.k1.2 - C.a1.2) +
        ((C.q t₁).1 - C.k1.1) * (C.k0.2 - C.a0.2) := rfl
    have : (C.k1.2 - C.a1.2) * (C.k1.1 - C.k0.1) / C.G t₀ t₁ * (C.k0.1 - (C.p t₀).1) <
        C.k1.1 - C.k0.1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hG, hGdef]
      nlinarith [mul_pos (mul_pos h5 h4) h2]
    linarith

end CopyPair

/-- Points of a non-vertical line with abscissa between `a` and `b` lie on the segment between
the points of abscissae `a` and `b`. -/
theorem onLine_mem_segment {f₀ f₁ : Point} {a b x : ℝ} (hab : a < b) (hax : a ≤ x)
    (hxb : x ≤ b) : onLine f₀ f₁ x ∈ ArtGallery.segment (onLine f₀ f₁ a) (onLine f₀ f₁ b) := by
  refine ⟨(x - a) / (b - a), div_nonneg (by linarith) (by linarith),
    (div_le_one (by linarith)).2 (by linarith), ?_⟩
  have hba : b - a ≠ 0 := by linarith
  simp only [onLine, Prod.mk.injEq]
  constructor
  · field_simp; ring
  · by_cases h : f₁.1 - f₀.1 = 0
    · rw [h]; simp
    · field_simp; ring

namespace Input

variable {I : Input} {N : ℚ}

section Nook

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The nook critical points lie strictly between the mouth corners. -/
theorem Good.nook_X_fst {t₀ t₁ : ℚ} (h₀ : t₀ ≤ 3 / 2) (h₁ : 0 ≤ t₁) :
    (I.z0 k).1 < ((I.nookQ k).X t₀ t₁).1 ∧ ((I.nookQ k).X t₀ t₁).1 < (I.z1 k).1 :=
  CopyPair.X_fst_mem (nookQ_hyp hg.toValid k) (nookQ_adm hg.toValid hk) h₀ h₁

/-- **The nook top edge contains the nook critical segment**: `[F1, F0] ⊆ [n0, n1]`. -/
theorem Good.nook_crit_subset :
    ArtGallery.segment (ratPoint (I.F1 k)) (ratPoint (I.F0 k)) ⊆
      ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k)) := by
  have hlt := F0_fst_lt hg.toValid hk
  have hF0 := hg.nook_X_fst hk (t₀ := 3 / 2) (t₁ := 3 / 2) le_rfl (by norm_num)
  have hF1 := hg.nook_X_fst hk (t₀ := 0) (t₁ := 0) (by norm_num) le_rfl
  rw [← F0_eq] at hF0
  rw [← F1_eq] at hF1
  have hne : (I.F1 k).1 - (I.F0 k).1 ≠ 0 := by linarith
  have e0 : I.F0 k = onLine (I.F0 k) (I.F1 k) (I.F0 k).1 :=
    eq_onLine hne (by simp [det2])
  have e1 : I.F1 k = onLine (I.F0 k) (I.F1 k) (I.F1 k).1 :=
    eq_onLine hne (by simp [det2])
  have hz : ((I.z0 k).1 : ℝ) < ((I.z1 k).1 : ℝ) := by exact_mod_cast hF0.1.trans (hlt.trans hF1.2)
  apply Geometry.segment_subset_of_convex (Geometry.segment_convex _ _)
  · rw [e1, ratPoint_onLine, n0, n1, ratPoint_onLine, ratPoint_onLine]
    exact onLine_mem_segment hz (by exact_mod_cast (hF0.1.trans hlt).le) (by exact_mod_cast hF1.2.le)
  · rw [e0, ratPoint_onLine, n0, n1, ratPoint_onLine, ratPoint_onLine]
    exact onLine_mem_segment hz (by exact_mod_cast hF0.1.le) (by exact_mod_cast (hlt.trans hF1.2).le)

/-- The nook critical points `X v v` (`v ∈ [0, 3/2]`) lie on the nook top edge. -/
theorem Good.nookR_X_mem_edge {v : ℝ} (h₀ : 0 ≤ v) (h₁ : v ≤ 3 / 2) :
    (I.nookR k).X v v ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.n1 k)) :=
  hg.nook_crit_subset hk (nookR_X_mem hg.toValid hk h₀ h₁)

end Nook

end Input

end ArtGallery.Sec5.Corridor

end
