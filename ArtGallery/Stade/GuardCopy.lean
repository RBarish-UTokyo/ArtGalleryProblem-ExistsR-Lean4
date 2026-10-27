module

public import ArtGallery.Stade.GuardWedges
public import ArtGallery.Stade.Copy

/-!
# The canonical guards see the copy pockets (proof plan L5.6)

For a copy nook relating the variable segment at `a` and the input segment at `b` (copy type
`ge`), the variable guard `σ(v) = (a, H + 2v − 1)` and the input guard `τ(v) = (b, 4v − 2)` of
the *same* value `v` see together every point of the pocket `N_bot, L_m, R_m, N_top`
(`copy_pocket_cover`): every nook point is reached through the mouth by one of them (the copy
lemmas of `Stade/CopyAlg.lean`), both see the whole mouth (it lies in the hall), and the fan /
Pasch argument of `pocket_cover` extends this to the whole pocket.
-/

@[expose] public section

namespace ArtGallery.Stade

variable {P : Polygon} {H a b : ℝ}

/-- **Copy pocket coverage.**  `A` is a convex part of the region (the hall) containing both
guards and the mouth; the pocket lies in the region. -/
theorem copy_pocket_cover (ge : Bool) (hp : CopyParams H a b) {A : Set Point}
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hmA : segment (copyLm ge H a b) (copyRm ge H a b) ⊆ A)
    (hKP : piece (copyPocket ge H a b) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hσA : varPt H a v ∈ A) (hτA : inPt b v ∈ A) :
    ∀ z ∈ piece (copyPocket ge H a b), P.Sees (varPt H a v) z ∨ P.Sees (inPt b v) z := by
  obtain ⟨h1, h2, h3, h4⟩ := copy_pocket_ccw ge hp
  have hcov := pocket_cover (P := P) (Gs := {varPt H a v, inPt b v}) h1 h2 h3 h4 hKP
    (fun g hg m hm => by
      rcases hg with rfl | rfl
      · exact sees_of_convex hA hAP hσA (hmA hm)
      · exact sees_of_convex hA hAP hτA (hmA hm))
    (fun s hs => by
      obtain ⟨e1, e2, e3⟩ := (copy_nook_iff ge hp).1 hs
      have e : s = (copyXN ge a b, s.2) := Prod.ext e1 rfl
      cases ge
      · by_cases hsh : s.2 ≤ copyShadow H v
        · obtain ⟨q, hq, hqs⟩ := copyLE_sig_cross hp hv1 hv2 e2 hsh
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyLE_tau_cross hp hv1 hv2 hsh.le e3
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩
      · by_cases hsh : copyShadow H v ≤ s.2
        · obtain ⟨q, hq, hqs⟩ := copyGE_sig_cross hp hv1 hv2 hsh e3
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyGE_tau_cross hp hv1 hv2 e2 hsh.le
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz

/-- The pocket piece of the polygon's copy-nook chain `R_m, N_top, N_bot, L_m` is `copyPocket`. -/
theorem piece_copyNook (ge : Bool) :
    piece (quad (copyRm ge H a b) (copyNtop ge H a b) (copyNbot ge H a b) (copyLm ge H a b)) =
      piece (copyPocket ge H a b) := by
  unfold copyPocket
  rw [piece_quad_rot, piece_quad_rot]

end ArtGallery.Stade

end
