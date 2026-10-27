module

public import ArtGallery.Jordan.Jordan

/-!
# The witness lemma: elementary facts about lines

Lines are given by pairs of points `ℓ = (ℓ.1, ℓ.2)`; the line is *degenerate* when `ℓ.1 = ℓ.2`.
The side of a point `x` with respect to `ℓ` is the sign of `det ℓ.1 ℓ.2 x`.

* `exists_det_ne_zero`: a nonempty open set is not contained in a line;
* `exists_generic`: a nonempty open set contains a point on no nondegenerate line of a list;
* `det_eq_zero_of_collinear`: three points of a nondegenerate line are collinear;
* `det_cen`: the determinant is affine, evaluated at a centroid;
* `isOpen_forall_list`: finitely many strict inequalities define an open set.
-/

namespace ArtGallery.Membership.Witness

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp lerp_fst lerp_snd det_lerp continuous_lerp lerp_zero lerp_one
  continuous_det_right)

/-- `x` lies on no nondegenerate line of the list `L`. -/
def Generic (L : List (Point × Point)) (x : Point) : Prop :=
  ∀ ℓ ∈ L, ℓ.1 ≠ ℓ.2 → det ℓ.1 ℓ.2 x ≠ 0

/-- The centroid of three points (the same formula as `ArtGallery.Membership.centroid`). -/
noncomputable def cen (a b c : Point) : Point :=
  ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)

/-- The determinant along a translate by a multiple of the normal of the line. -/
theorem det_add_normal (a b q : Point) (t : ℝ) :
    det a b (q + t • ((-(b.2 - a.2), b.1 - a.1) : Point)) =
      det a b q + t * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
  unfold det
  simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst, Geometry.smul_snd]
  ring

/-- A nonempty open set is not contained in a nondegenerate line. -/
theorem exists_det_ne_zero {W : Set Point} (hW : IsOpen W) (hne : W.Nonempty) {a b : Point}
    (hab : a ≠ b) : ∃ q ∈ W, det a b q ≠ 0 := by
  obtain ⟨q₀, hq₀⟩ := hne
  by_cases h0 : det a b q₀ = 0
  swap
  · exact ⟨q₀, hq₀, h0⟩
  set nv : Point := (-(b.2 - a.2), b.1 - a.1) with hnv
  have hcont : Continuous (fun t : ℝ => q₀ + t • nv) := by fun_prop
  have htend : Tendsto (fun t : ℝ => q₀ + t • nv) (𝓝 0) (𝓝 q₀) := by
    have := hcont.tendsto 0
    simpa using this
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), q₀ + t • nv ∈ W ∧ t ≠ 0 :=
    ((htend.eventually_mem (hW.mem_nhds hq₀)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  obtain ⟨t, htW, ht0⟩ := hev.exists
  refine ⟨_, htW, ?_⟩
  rw [hnv, det_add_normal, h0, zero_add]
  exact mul_ne_zero ht0 (Jordan.sqLen_pos hab).ne'

/-- A nonempty open set contains a point on no nondegenerate line of `L`. -/
theorem exists_generic (L : List (Point × Point)) {W : Set Point} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ q ∈ W, Generic L q := by
  induction L generalizing W with
  | nil =>
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, hq, fun ℓ hℓ => absurd hℓ (List.not_mem_nil)⟩
  | cons m L ih =>
    by_cases hm : m.1 = m.2
    · obtain ⟨q, hq, hg⟩ := ih hW hne
      refine ⟨q, hq, fun ℓ hℓ hne' => ?_⟩
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · exact absurd hm hne'
      · exact hg ℓ hℓ hne'
    · obtain ⟨q₀, hq₀, hd⟩ := exists_det_ne_zero hW hne hm
      have hW' : IsOpen (W ∩ {q | det m.1 m.2 q ≠ 0}) :=
        hW.inter (isOpen_ne_fun (continuous_det_right _ _) continuous_const)
      obtain ⟨q, ⟨hqW, hqd⟩, hg⟩ := ih hW' ⟨q₀, hq₀, hd⟩
      refine ⟨q, hqW, fun ℓ hℓ hne' => ?_⟩
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · exact hqd
      · exact hg ℓ hℓ hne'

/-- Three points on a nondegenerate line are collinear. -/
theorem det_eq_zero_of_collinear {u v a b c : Point} (huv : u ≠ v) (ha : det u v a = 0)
    (hb : det u v b = 0) (hc : det u v c = 0) : det a b c = 0 := by
  have h1 : (v.1 - u.1) * det a b c = 0 := by
    unfold det at *
    linear_combination (b.1 - a.1) * (hc - ha) - (c.1 - a.1) * (hb - ha)
  have h2 : (v.2 - u.2) * det a b c = 0 := by
    unfold det at *
    linear_combination (b.2 - a.2) * (hc - ha) - (c.2 - a.2) * (hb - ha)
  by_contra h
  apply huv
  have e1 : v.1 - u.1 = 0 := (mul_eq_zero.1 h1).resolve_right h
  have e2 : v.2 - u.2 = 0 := (mul_eq_zero.1 h2).resolve_right h
  exact Prod.ext (by linarith) (by linarith)

/-- The determinant at a centroid is the mean of the determinants. -/
theorem det_cen (u v a b c : Point) :
    det u v (cen a b c) = (det u v a + det u v b + det u v c) / 3 := by
  unfold det cen
  ring

/-- Finitely many strict inequalities between continuous functions define an open set. -/
theorem isOpen_forall_list {ι : Type} (L : List ι) (Q : ι → Prop) (f : ι → Point → ℝ)
    (hf : ∀ i, Continuous (f i)) : IsOpen {q | ∀ i ∈ L, Q i → 0 < f i q} := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have e : {q | ∀ i ∈ a :: L, Q i → 0 < f i q} =
        {q | Q a → 0 < f a q} ∩ {q | ∀ i ∈ L, Q i → 0 < f i q} := by
      ext q
      simp only [List.forall_mem_cons, mem_ofPred_eq, mem_inter_iff]
    rw [e]
    refine IsOpen.inter ?_ ih
    by_cases hQ : Q a
    · simpa [hQ] using isOpen_lt continuous_const (hf a)
    · simp [hQ]

/-- Finitely many (or arbitrarily many) weak inequalities between continuous functions define a
closed set. -/
theorem isClosed_forall_list {ι : Type} (L : List ι) (f : ι → Point → ℝ)
    (hf : ∀ i, Continuous (f i)) : IsClosed {q | ∀ i ∈ L, 0 ≤ f i q} := by
  have e : {q | ∀ i ∈ L, 0 ≤ f i q} = ⋂ i ∈ {x | x ∈ L}, {q | 0 ≤ f i q} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter]
  rw [e]
  exact isClosed_biInter fun i _ => isClosed_le continuous_const (hf i)

end

end ArtGallery.Membership.Witness
