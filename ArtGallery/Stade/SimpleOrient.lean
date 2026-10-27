module

public import ArtGallery.Stade.Simple
public import ArtGallery.Stade.Counting

/-!
# Orientation of Stade's polygon (proof plan L2.1)

`interiorLeft n Φ`: the interior of `poly n Φ` lies to the left of every edge.  The closing edge
`(x_L, 2H) → (x_L, −1)` (the left wall) lies on the line `x = x_L`, all vertices have abscissa
`≥ x_L` (`poly_fst_ge`), and it is traversed downwards; `interiorLeft_of_left_edge`
(`ArtGallery/Stade/Counting.lean`) applies.
-/

namespace ArtGallery.Stade

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Irrational

/-- **L2.1: the interior of Stade's polygon is to the left of every edge.** -/
theorem interiorLeft (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((poly n Φ).map ratPoint)).InteriorLeft := by
  have hP := simple n Φ
  have hn : (Polygon.mk ((poly n Φ).map ratPoint)).n = (poly n Φ).length := n_map_ratPoint _
  have hlen := poly_length_ge n Φ
  have hH := paramH_ge_q n Φ
  refine interiorLeft_of_left_edge hP (i := (poly n Φ).length - 1) (by omega)
    (x₀ := (xL n Φ : ℝ)) ?_ ?_ ?_ ?_
  · intro j hj
    rw [hn] at hj
    rw [vtx_map_ratPoint, ratPoint_fst]
    have hm : (poly n Φ).getD j 0 ∈ poly n Φ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj
    exact_mod_cast poly_fst_ge _ hm
  · rw [vtx_map_ratPoint]
    have := poly_last n Φ
    simp only [Prod.zero_eq_mk] at this ⊢
    rw [this]; rfl
  · rw [hn, show (poly n Φ).length - 1 + 1 = (poly n Φ).length by omega, Nat.mod_self,
      vtx_map_ratPoint]
    have := poly_head n Φ
    simp only [Prod.zero_eq_mk] at this ⊢
    rw [this]; rfl
  · rw [hn, show (poly n Φ).length - 1 + 1 = (poly n Φ).length by omega, Nat.mod_self,
      vtx_map_ratPoint, vtx_map_ratPoint]
    have h1 := poly_head n Φ
    have h2 := poly_last n Φ
    simp only [Prod.zero_eq_mk] at h1 h2 ⊢
    rw [h1, h2]
    show (((-1 : ℚ)) : ℝ) < ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ)
    exact_mod_cast (by linarith : (-1 : ℚ) < 2 * (paramH n Φ : ℚ))

end

end ArtGallery.Stade
