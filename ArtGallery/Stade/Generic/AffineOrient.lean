module

public import ArtGallery.Invariance.Affine
public import ArtGallery.Vis.API

/-!
# Orientation under affine maps (proof plan L2.1, §12 item 4)

An orientation-preserving invertible affine map `A` of the plane (positive determinant of its
linear part) carries a simple polygon with its interior to the left of every edge to a polygon
with the same property (`interiorLeft_mapPoly`).  With `ArtGallery/Invariance/Affine.lean`
(`simple_mapPoly`, `filled_mapPoly`, `boundary_mapPoly`) this transports the whole visibility
setting along rotations, translations and orientation-preserving affine maps; seeing is
transported by `sees_mapPoly_iff`.

Proof: near a point `y` of an open edge of `P`, the region is the closed half-plane of the edge
(`local_halfplane`), so points strictly to the left of the edge near `y` are interior points of the
region, i.e. off the boundary (`Jordan.interior_filled`).  The left-offset points of the image edge
are images of such points, because `det (A a) (A b) (A c) = κ · det a b c` with `κ > 0`
(`det_affine`).
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric
open ArtGallery.Hardening.Invariance

variable {P : Polygon}

/-- `A (x + w) = A x + A.linear w`. -/
theorem affine_add (A : Point ≃ᵃ[ℝ] Point) (x w : Point) : A (x + w) = A x + A.linear w := by
  have := A.map_vadd x w
  simp only [vadd_eq_add] at this
  rw [add_comm x w, this, add_comm]

/-- `A.linear (y − x) = A y − A x`. -/
theorem affine_linear_sub (A : Point ≃ᵃ[ℝ] Point) (x y : Point) :
    A.linear (y - x) = A y - A x := by
  have := affine_add A x (y - x)
  rw [add_sub_cancel] at this
  rw [this, add_sub_cancel_left]

/-- The orientation factor of an affine map: `det (A a) (A b) (A c) = κ A · det a b c`. -/
noncomputable def orientFactor (A : Point ≃ᵃ[ℝ] Point) : ℝ :=
  det 0 (A.linear (1, 0)) (A.linear (0, 1))

/-- Determinants scale by the orientation factor under an affine map. -/
theorem det_map (A : Point ≃ᵃ[ℝ] Point) (a b c : Point) :
    det (A a) (A b) (A c) = orientFactor A * det a b c :=
  det_affine A.toAffineMap a b c

/-- **Seeing is transported** by an invertible affine map. -/
theorem sees_mapPoly_iff (A : Point ≃ᵃ[ℝ] Point) {p q : Point} :
    (mapPoly A P).Sees (A p) (A q) ↔ P.Sees p q := by
  unfold Polygon.Sees
  rw [← image_segment', filled_mapPoly]
  exact image_subset_image_iff A.injective

/-- **Orientation is transported** by an orientation-preserving invertible affine map: if the
interior of the simple polygon `P` is to the left of every edge, the same holds for its image. -/
theorem interiorLeft_mapPoly (A : Point ≃ᵃ[ℝ] Point) (hA : 0 < orientFactor A)
    (hP : P.Simple) (hL : P.InteriorLeft) : (mapPoly A P).InteriorLeft := by
  intro i hi t ht0 ht1
  rw [n_mapPoly] at hi
  rw [vtx_succ_mapPoly A P hi, vtx_mapPoly A P hi]
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  have huv : u ≠ v := Jordan.simple_vtx_succ_ne hP hi
  set N := Polygon.leftNormal (A u) (A v) with hN
  set m := A.symm.linear N with hm
  have hAm : A.linear m = N := by rw [hm]; simp
  -- the point of the image edge is the image of the point of the edge
  set y := u + t • (v - u) with hy
  have hAy : A u + t • (A v - A u) = A y := by
    rw [hy, affine_add, map_smul, affine_linear_sub]
  -- the transported normal points strictly to the left of the edge
  have hlen : 0 < det (A u) (A v) (A u + N) := by
    have e : det (A u) (A v) (A u + N) = ((A v).1 - (A u).1) ^ 2 + ((A v).2 - (A u).2) ^ 2 := by
      rw [hN]; unfold det Polygon.leftNormal; simp only [Prod.fst_add, Prod.snd_add]; ring
    rw [e]
    exact Jordan.sqLen_pos (fun h => huv (A.injective h))
  have hpos : 0 < det u v (u + m) := by
    have := det_map A u v (u + m)
    rw [affine_add, hAm] at this
    rw [this] at hlen
    exact (mul_pos_iff_of_pos_left hA).1 hlen
  have hdy : det u v y = 0 := by
    rw [hy, ← Geometry.lerp_eq_add_smul]; exact Geometry.det_lerp_self u v t
  obtain ⟨r, hr, hloc⟩ := Polygon.local_halfplane hP hL hi ht0 ht1
  rw [← hy] at hloc
  have hint : interior P.filled = P.filled \ P.boundary := Jordan.interior_filled hP
  refine ⟨r / (2 * (‖m‖ + 1)), div_pos hr (by positivity), fun δ hδ0 hδ1 => ?_⟩
  have hsmall : δ * ‖m‖ < r := by
    have h1 : δ * ‖m‖ ≤ r / (2 * (‖m‖ + 1)) * ‖m‖ :=
      mul_le_mul_of_nonneg_right hδ1.le (norm_nonneg _)
    have h2 : r / (2 * (‖m‖ + 1)) * ‖m‖ < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg m]
    linarith
  have hdist : ∀ s : ℝ, |s| = δ → dist (y + s • m) y < r := by
    intro s hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hs]
    exact hsmall
  have hdet : ∀ s : ℝ, det u v (y + s • m) = s * det u v (u + m) := by
    intro s; rw [Geometry.det_add_smul, hdy, zero_add]
  have himg : ∀ s : ℝ, A y + s • N = A (y + s • m) := by
    intro s; rw [affine_add A y (s • m), map_smul, hAm]
  refine ⟨?_, ?_⟩
  · -- the left point is interior
    rw [hAy, himg]
    have hz : y + δ • m ∈ interior P.filled := by
      rw [mem_interior_iff_mem_nhds]
      have h1 : ∀ᶠ w in 𝓝 (y + δ • m), dist w y < r :=
        isOpen_ball.mem_nhds (mem_ball.2 (hdist δ (abs_of_pos hδ0)))
      have h2 : ∀ᶠ w in 𝓝 (y + δ • m), 0 < det u v w :=
        (Geometry.continuous_det_right u v).continuousAt.eventually
          (lt_mem_nhds (show 0 < det u v (y + δ • m) by rw [hdet]; exact mul_pos hδ0 hpos))
      filter_upwards [h1, h2] with w hw1 hw2 using (hloc w hw1).2 hw2.le
    rw [hint] at hz
    refine ⟨(mem_filled_mapPoly_iff A P).2 hz.1, fun hb => ?_⟩
    rw [boundary_mapPoly] at hb
    obtain ⟨x, hx, hxe⟩ := hb
    exact hz.2 (A.injective hxe ▸ hx)
  · -- the right point is outside
    rw [hAy, sub_eq_add_neg, ← neg_smul, himg, mem_filled_mapPoly_iff]
    intro hz
    have := (hloc _ (hdist (-δ) (by rw [abs_neg, abs_of_pos hδ0]))).1 hz
    rw [hdet] at this
    nlinarith [mul_pos hδ0 hpos]

end ArtGallery.Stade

end
