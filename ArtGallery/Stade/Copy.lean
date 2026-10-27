module

public import ArtGallery.Stade.CopyAlg
public import ArtGallery.Stade.Exit
public import ArtGallery.Stade.Polygon

/-!
# Stade construction, §5: the copy nooks (geometry)

Visibility facts for one copy nook of `docs/stade/construction.md` §5 (notation of
`ArtGallery/Stade/CopyAlg.lean`): the pocket is the convex quadrilateral
`N_bot, L_m, R_m, N_top` hanging above the ceiling, entered through the mouth `[L_m, R_m]`.

The results are stated for an arbitrary polygon `P` and a **room** `R` of `P` with door
`[L_m, R_m]` (`Polygon.IsRoom`, `Vis/Rooms.lean`) containing the nook segment; when the three
pocket walls `N_bot → L_m`, `R_m → N_top`, `N_top → N_bot` are edges of the simple polygon `P`
with its interior on the left, the pocket piece is such a room (`copy_isRoom`, via the room lemma
of `Stade/Exit.lean`), and the `…_of_walls` versions need only these edges.

* **What each guard sees (L5.4)**: `copyGE_sig_sees`, `copyGE_tau_sees`, `copyLE_sig_sees`,
  `copyLE_tau_sees` — a nook point seen by the variable guard `σ(v)` lies above (GE) / below (LE)
  `copyShadow H v`; for the input guard `τ(w)` the other way round.
* **Coverage ⇒ copy inequality**: `copyGE_rel_of_cover`, `copyLE_rel_of_cover`
  (and `…_of_walls`): if every nook point is seen by `σ(v)` or `τ(w)`, then `w ≤ v` (GE),
  resp. `v ≤ w` (LE).
* **Positive visibility (L5.6)**: `copyGE_cover_of_rel`, `copyLE_cover_of_rel`, for a convex
  part `A` of the region (the hall) containing the guards and the mouth and a convex part `C`
  (the pocket) containing the mouth and the nook segment; the equivalences
  `copyGE_cover_iff`, `copyLE_cover_iff`.
* **Partial visibility (L5.5)**: `copy_viewer_mem_PV` — every viewer of a nook point outside the
  room lies in `copyPV`, whose band lemmas are in `CopyAlg.lean`.
* **Interface with the definition layer**: `CopyParams.of_rat`, `copyParams_of_input`
  (from `Params.s1`), and `ratPoint_nookTop`, … (`Polygon.lean`'s rational copy-nook vertices
  are the real points used here).
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon}

/-! ### Rooms -/

/-- A point outside a room that sees a point of the room sees it through the door. -/
theorem cross_of_sees_room {R D : Set Point} (hR : P.IsRoom R D) {g s : Point} (hsR : s ∈ R)
    (hgR : g ∉ R) (h : P.Sees g s) : ∃ q ∈ D, q ∈ segment g s := by
  obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door hR hsR hgR (Polygon.sees_comm.1 h)
  exact ⟨y, hyD, by rw [Geometry.segment_comm]; exact hy⟩

section

variable {H a b : ℝ}

/-! ### The pocket (L5.2) -/

/-- **The copy pocket is a strictly convex counter-clockwise quadrilateral** `N_bot, L_m, R_m,
N_top` (in the vertex convention `lo, dn, up, hi` of `Stade/Exit.lean`). -/
theorem copy_pocket_ccw (ge : Bool) (hp : CopyParams H a b) :
    0 < det (copyNbot ge H a b) (copyLm ge H a b) (copyRm ge H a b) ∧
      0 < det (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b) ∧
      0 < det (copyRm ge H a b) (copyNtop ge H a b) (copyNbot ge H a b) ∧
      0 < det (copyNtop ge H a b) (copyNbot ge H a b) (copyLm ge H a b) := by
  have hLR := copyLm_lt_Rm ge hp
  have hNB := copyNbot_snd_gt ge hp
  have hNN := copyNbot_lt_Ntop ge hp
  obtain ⟨hxL, hxR⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧
      copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  unfold det
  simp only [copyLm_snd, copyRm_snd, copyNtop_fst, copyNbot_fst]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The nook segment, explicitly. -/
theorem copy_nook_iff (ge : Bool) (hp : CopyParams H a b) {s : Point} :
    s ∈ segment (copyNbot ge H a b) (copyNtop ge H a b) ↔
      s.1 = copyXN ge a b ∧ (copyNbot ge H a b).2 ≤ s.2 ∧ s.2 ≤ (copyNtop ge H a b).2 := by
  have e1 : copyNbot ge H a b = (copyXN ge a b, (copyNbot ge H a b).2) := rfl
  have e2 : copyNtop ge H a b = (copyXN ge a b, (copyNtop ge H a b).2) := rfl
  rw [e1, e2, mem_segment_vert_iff (copyNbot_lt_Ntop ge hp).le]

/-- The pocket piece of `Stade/Exit.lean`. -/
noncomputable def copyPocket (ge : Bool) (H a b : ℝ) : Polygon :=
  quad (copyNbot ge H a b) (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b)

/-- The pocket is a convex piece. -/
theorem copyPocket_isPiece (ge : Bool) (hp : CopyParams H a b) :
    IsPiece (copyPocket ge H a b) := by
  obtain ⟨h1, h2, h3, h4⟩ := copy_pocket_ccw ge hp
  exact isPiece_quad h1 h2 h3 h4

/-- The nook segment lies in the pocket piece. -/
theorem copy_nook_subset_pocket (ge : Bool) (hp : CopyParams H a b) :
    segment (copyNbot ge H a b) (copyNtop ge H a b) ⊆ piece (copyPocket ge H a b) := by
  intro s hs
  refine edge_subset_piece (copyPocket_isPiece ge hp) (j := 3) (by simp [copyPocket, quad,
    Polygon.n]) ?_
  rw [Geometry.segment_comm] at hs
  simpa [Polygon.edge, copyPocket, quad, Polygon.vtx, Polygon.n] using hs

/-- The mouth lies in the pocket piece. -/
theorem copy_mouth_subset_pocket (ge : Bool) (hp : CopyParams H a b) :
    segment (copyLm ge H a b) (copyRm ge H a b) ⊆ piece (copyPocket ge H a b) := by
  intro s hs
  refine edge_subset_piece (copyPocket_isPiece ge hp) (j := 1) (by simp [copyPocket, quad,
    Polygon.n]) ?_
  simpa [Polygon.edge, copyPocket, quad, Polygon.vtx, Polygon.n] using hs

/-- Points strictly below the ceiling are not in the pocket piece. -/
theorem not_mem_copyPocket (ge : Bool) (hp : CopyParams H a b) {p : Point} (hp2 : p.2 < 2 * H) :
    p ∉ piece (copyPocket ge H a b) := by
  intro h
  have h1 := (mem_piece_quad.1 h).2.1
  rw [copy_det_mouth] at h1
  have hLR := copyLm_lt_Rm ge hp
  have : ((copyRm ge H a b).1 - (copyLm ge H a b).1) * (p.2 - 2 * H) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-- **The pocket is a room** of `P` with door `[L_m, R_m]`, if its three walls `N_bot → L_m`,
`R_m → N_top`, `N_top → N_bot` are edges of `P`. -/
theorem copy_isRoom (hP : P.Simple) (hL : P.InteriorLeft) (ge : Bool) (hp : CopyParams H a b)
    (hw0 : ∃ i < P.n, P.vtx i = copyNbot ge H a b ∧ P.vtx ((i + 1) % P.n) = copyLm ge H a b)
    (hw2 : ∃ i < P.n, P.vtx i = copyRm ge H a b ∧ P.vtx ((i + 1) % P.n) = copyNtop ge H a b)
    (hw3 : ∃ i < P.n, P.vtx i = copyNtop ge H a b ∧ P.vtx ((i + 1) % P.n) = copyNbot ge H a b) :
    P.IsRoom (piece (copyPocket ge H a b)) (segment (copyLm ge H a b) (copyRm ge H a b)) := by
  have h : P.IsRoom (piece (quad (copyNbot ge H a b) (copyLm ge H a b) (copyRm ge H a b)
      (copyNtop ge H a b))) (door (quad (copyNbot ge H a b) (copyLm ge H a b) (copyRm ge H a b)
      (copyNtop ge H a b)) (· = 1)) :=
    isRoom_piece hP hL (copyPocket_isPiece ge hp) (pocket_hWO hw0 hw2 hw3)
  rw [door_quad_one] at h
  exact h

/-! ### What each guard sees (L5.4) -/

section Seen

variable {R : Set Point}

/-- **Variable guard, GE**: a nook point seen from `σ(v)` is at or above `copyShadow H v`. -/
theorem copyGE_sig_sees (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm true H a b) (copyRm true H a b)))
    (hNR : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ R) {v : ℝ} (hv1 : 1 / 2 ≤ v)
    (hv2 : v ≤ 2) (hσR : varPt H a v ∉ R) {s : Point}
    (hs : s ∈ segment (copyNbot true H a b) (copyNtop true H a b))
    (hsees : P.Sees (varPt H a v) s) : copyShadow H v ≤ s.2 := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hσR hsees
  obtain ⟨h1, -, h3⟩ := (copy_nook_iff true hp).1 hs
  have e : s = (copyXN true a b, s.2) := Prod.ext h1 rfl
  rw [e] at hqs
  exact copyGE_sig_seen hp hv1 hv2 h3 hq hqs

/-- **Input guard, GE**: a nook point seen from `τ(w)` is at or below `copyShadow H w`. -/
theorem copyGE_tau_sees (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm true H a b) (copyRm true H a b)))
    (hNR : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ R) {w : ℝ} (hw1 : 1 / 2 ≤ w)
    (hw2 : w ≤ 2) (hτR : inPt b w ∉ R) {s : Point}
    (hs : s ∈ segment (copyNbot true H a b) (copyNtop true H a b))
    (hsees : P.Sees (inPt b w) s) : s.2 ≤ copyShadow H w := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hτR hsees
  obtain ⟨h1, h2, -⟩ := (copy_nook_iff true hp).1 hs
  have e : s = (copyXN true a b, s.2) := Prod.ext h1 rfl
  rw [e] at hqs
  exact copyGE_tau_seen hp hw1 hw2 h2 hq hqs

/-- **Variable guard, LE**: a nook point seen from `σ(v)` is at or below `copyShadow H v`. -/
theorem copyLE_sig_sees (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm false H a b) (copyRm false H a b)))
    (hNR : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ R) {v : ℝ} (hv1 : 1 / 2 ≤ v)
    (hv2 : v ≤ 2) (hσR : varPt H a v ∉ R) {s : Point}
    (hs : s ∈ segment (copyNbot false H a b) (copyNtop false H a b))
    (hsees : P.Sees (varPt H a v) s) : s.2 ≤ copyShadow H v := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hσR hsees
  obtain ⟨h1, h2, -⟩ := (copy_nook_iff false hp).1 hs
  have e : s = (copyXN false a b, s.2) := Prod.ext h1 rfl
  rw [e] at hqs
  exact copyLE_sig_seen hp hv1 hv2 h2 hq hqs

/-- **Input guard, LE**: a nook point seen from `τ(w)` is at or above `copyShadow H w`. -/
theorem copyLE_tau_sees (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm false H a b) (copyRm false H a b)))
    (hNR : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ R) {w : ℝ} (hw1 : 1 / 2 ≤ w)
    (hw2 : w ≤ 2) (hτR : inPt b w ∉ R) {s : Point}
    (hs : s ∈ segment (copyNbot false H a b) (copyNtop false H a b))
    (hsees : P.Sees (inPt b w) s) : copyShadow H w ≤ s.2 := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hτR hsees
  obtain ⟨h1, -, h3⟩ := (copy_nook_iff false hp).1 hs
  have e : s = (copyXN false a b, s.2) := Prod.ext h1 rfl
  rw [e] at hqs
  exact copyLE_tau_seen hp hw1 hw2 h3 hq hqs

/-! ### Coverage ⇒ copy inequality -/

/-- **Copy nook, GE: coverage ⇒ `v_var ≥ v_in`.** If every point of the nook segment is seen by
the variable guard `σ(v)` or by the input guard `τ(w)` (both outside the room), then `w ≤ v`. -/
theorem copyGE_rel_of_cover (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm true H a b) (copyRm true H a b)))
    (hNR : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ R) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσR : varPt H a v ∉ R) (hτR : inPt b w ∉ R)
    (hcov : ∀ s ∈ segment (copyNbot true H a b) (copyNtop true H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) : w ≤ v := by
  refine copyGE_rel_of_shadows hp hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
  have hs : (copyXN true a b, h) ∈ segment (copyNbot true H a b) (copyNtop true H a b) :=
    (copy_nook_iff true hp).2 ⟨rfl, hh1, hh2⟩
  rcases hcov _ hs with h' | h'
  · exact Or.inl (copyGE_sig_sees hp hR hNR hv1 hv2 hσR hs h')
  · exact Or.inr (copyGE_tau_sees hp hR hNR hw1 hw2 hτR hs h')

/-- **Copy nook, LE: coverage ⇒ `v_var ≤ v_in`.** -/
theorem copyLE_rel_of_cover (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm false H a b) (copyRm false H a b)))
    (hNR : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ R) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσR : varPt H a v ∉ R) (hτR : inPt b w ∉ R)
    (hcov : ∀ s ∈ segment (copyNbot false H a b) (copyNtop false H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) : v ≤ w := by
  refine copyLE_rel_of_shadows hp hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
  have hs : (copyXN false a b, h) ∈ segment (copyNbot false H a b) (copyNtop false H a b) :=
    (copy_nook_iff false hp).2 ⟨rfl, hh1, hh2⟩
  rcases hcov _ hs with h' | h'
  · exact Or.inl (copyLE_sig_sees hp hR hNR hv1 hv2 hσR hs h')
  · exact Or.inr (copyLE_tau_sees hp hR hNR hw1 hw2 hτR hs h')

/-! ### Partial visibility (L5.5) -/

/-- **Viewers of a copy nook.** A point outside the room that sees a point of the nook segment
lies in the partial-visibility region `copyPV` (whose band lemmas are `copyPV_var_band`,
`copyPV_in_band`, `copyPV_low`). -/
theorem copy_viewer_mem_PV (ge : Bool) (hp : CopyParams H a b)
    (hR : P.IsRoom R (segment (copyLm ge H a b) (copyRm ge H a b)))
    (hNR : segment (copyNbot ge H a b) (copyNtop ge H a b) ⊆ R) {s p : Point}
    (hs : s ∈ segment (copyNbot ge H a b) (copyNtop ge H a b)) (hpR : p ∉ R)
    (hsees : P.Sees p s) : p ∈ copyPV ge H a b := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hpR hsees
  rw [Geometry.segment_comm] at hqs
  exact mem_copyPV_of_cross ge hp hs hq hqs

end Seen

/-! ### Positive visibility (L5.6) -/

section Positive

variable {A C : Set Point}

/-- Seeing a nook point through the mouth, given convex parts of the region on both sides. -/
theorem sees_of_cross (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) {O₁ O₂ g s : Point} (hgA : g ∈ A) (hmA : segment O₁ O₂ ⊆ A)
    (hmC : segment O₁ O₂ ⊆ C) (hsC : s ∈ C)
    (hcross : ∃ q ∈ segment O₁ O₂, q ∈ segment g s) : P.Sees g s := by
  obtain ⟨q, hq, hqs⟩ := hcross
  exact sees_of_two_convex hA hC hAP hCP hgA hsC (hmA hq) (hmC hq) hqs

/-- **Copy nook, GE: `w ≤ v` ⇒ coverage.**  With a convex part `A` of the region (the hall)
containing both guards and the mouth, and a convex part `C` (the pocket) containing the mouth and
the nook segment, every nook point is seen by `σ(v)` or `τ(w)`. -/
theorem copyGE_cover_of_rel (hp : CopyParams H a b) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hmA : segment (copyLm true H a b) (copyRm true H a b) ⊆ A)
    (hmC : segment (copyLm true H a b) (copyRm true H a b) ⊆ C)
    (hNC : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ C) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσA : varPt H a v ∈ A) (hτA : inPt b w ∈ A) (hwv : w ≤ v) :
    ∀ s ∈ segment (copyNbot true H a b) (copyNtop true H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := (copy_nook_iff true hp).1 hs
  have e : s = (copyXN true a b, s.2) := Prod.ext h1 rfl
  by_cases hsh : copyShadow H v ≤ s.2
  · left
    refine sees_of_cross hA hAP hC hCP hσA hmA hmC (hNC hs) ?_
    rw [e]; exact copyGE_sig_cross hp hv1 hv2 hsh h3
  · right
    push Not at hsh
    have := (copyShadow_le_iff hp).2 hwv
    refine sees_of_cross hA hAP hC hCP hτA hmA hmC (hNC hs) ?_
    rw [e]; exact copyGE_tau_cross hp hw1 hw2 h2 (by linarith)

/-- **Copy nook, LE: `v ≤ w` ⇒ coverage.** -/
theorem copyLE_cover_of_rel (hp : CopyParams H a b) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hmA : segment (copyLm false H a b) (copyRm false H a b) ⊆ A)
    (hmC : segment (copyLm false H a b) (copyRm false H a b) ⊆ C)
    (hNC : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ C) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσA : varPt H a v ∈ A) (hτA : inPt b w ∈ A) (hvw : v ≤ w) :
    ∀ s ∈ segment (copyNbot false H a b) (copyNtop false H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := (copy_nook_iff false hp).1 hs
  have e : s = (copyXN false a b, s.2) := Prod.ext h1 rfl
  by_cases hsh : s.2 ≤ copyShadow H v
  · left
    refine sees_of_cross hA hAP hC hCP hσA hmA hmC (hNC hs) ?_
    rw [e]; exact copyLE_sig_cross hp hv1 hv2 h2 hsh
  · right
    push Not at hsh
    have := (copyShadow_le_iff hp).2 hvw
    refine sees_of_cross hA hAP hC hCP hτA hmA hmC (hNC hs) ?_
    rw [e]; exact copyLE_tau_cross hp hw1 hw2 (by linarith) h3

/-- **Copy nook, GE: covered iff `v_var ≥ v_in`** (room and convex parts as above). -/
theorem copyGE_cover_iff (hp : CopyParams H a b) {R : Set Point}
    (hR : P.IsRoom R (segment (copyLm true H a b) (copyRm true H a b)))
    (hNR : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ R)
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hmA : segment (copyLm true H a b) (copyRm true H a b) ⊆ A)
    (hmC : segment (copyLm true H a b) (copyRm true H a b) ⊆ C)
    (hNC : segment (copyNbot true H a b) (copyNtop true H a b) ⊆ C) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσR : varPt H a v ∉ R) (hτR : inPt b w ∉ R) (hσA : varPt H a v ∈ A)
    (hτA : inPt b w ∈ A) :
    (∀ s ∈ segment (copyNbot true H a b) (copyNtop true H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) ↔ w ≤ v :=
  ⟨copyGE_rel_of_cover hp hR hNR hv1 hv2 hw1 hw2 hσR hτR,
    copyGE_cover_of_rel hp hA hAP hC hCP hmA hmC hNC hv1 hv2 hw1 hw2 hσA hτA⟩

/-- **Copy nook, LE: covered iff `v_var ≤ v_in`** (room and convex parts as above). -/
theorem copyLE_cover_iff (hp : CopyParams H a b) {R : Set Point}
    (hR : P.IsRoom R (segment (copyLm false H a b) (copyRm false H a b)))
    (hNR : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ R)
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hmA : segment (copyLm false H a b) (copyRm false H a b) ⊆ A)
    (hmC : segment (copyLm false H a b) (copyRm false H a b) ⊆ C)
    (hNC : segment (copyNbot false H a b) (copyNtop false H a b) ⊆ C) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hσR : varPt H a v ∉ R) (hτR : inPt b w ∉ R) (hσA : varPt H a v ∈ A)
    (hτA : inPt b w ∈ A) :
    (∀ s ∈ segment (copyNbot false H a b) (copyNtop false H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) ↔ v ≤ w :=
  ⟨copyLE_rel_of_cover hp hR hNR hv1 hv2 hw1 hw2 hσR hτR,
    copyLE_cover_of_rel hp hA hAP hC hCP hmA hmC hNC hv1 hv2 hw1 hw2 hσA hτA⟩

end Positive

/-! ### Versions with the pocket walls as edges of `P` -/

/-- **Copy nook (GE), walls form**: if the pocket walls are edges of `P` and every nook point is
seen by `σ(v)` or `τ(w)`, then `w ≤ v`. -/
theorem copyGE_rel_of_walls (hP : P.Simple) (hL : P.InteriorLeft) (hp : CopyParams H a b)
    (hw0 : ∃ i < P.n, P.vtx i = copyNbot true H a b ∧ P.vtx ((i + 1) % P.n) = copyLm true H a b)
    (hw2 : ∃ i < P.n, P.vtx i = copyRm true H a b ∧ P.vtx ((i + 1) % P.n) = copyNtop true H a b)
    (hw3 : ∃ i < P.n, P.vtx i = copyNtop true H a b ∧ P.vtx ((i + 1) % P.n) = copyNbot true H a b)
    {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2' : w ≤ 2)
    (hcov : ∀ s ∈ segment (copyNbot true H a b) (copyNtop true H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) : w ≤ v :=
  copyGE_rel_of_cover hp (copy_isRoom hP hL true hp hw0 hw2 hw3) (copy_nook_subset_pocket true hp)
    hv1 hv2 hw1 hw2' (not_mem_copyPocket true hp (varPt_snd_lt hp hv2))
    (not_mem_copyPocket true hp (inPt_snd_lt hp hw2')) hcov

/-- **Copy nook (LE), walls form**: if the pocket walls are edges of `P` and every nook point is
seen by `σ(v)` or `τ(w)`, then `v ≤ w`. -/
theorem copyLE_rel_of_walls (hP : P.Simple) (hL : P.InteriorLeft) (hp : CopyParams H a b)
    (hw0 : ∃ i < P.n, P.vtx i = copyNbot false H a b ∧ P.vtx ((i + 1) % P.n) = copyLm false H a b)
    (hw2 : ∃ i < P.n, P.vtx i = copyRm false H a b ∧ P.vtx ((i + 1) % P.n) = copyNtop false H a b)
    (hw3 : ∃ i < P.n,
      P.vtx i = copyNtop false H a b ∧ P.vtx ((i + 1) % P.n) = copyNbot false H a b)
    {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2' : w ≤ 2)
    (hcov : ∀ s ∈ segment (copyNbot false H a b) (copyNtop false H a b),
      P.Sees (varPt H a v) s ∨ P.Sees (inPt b w) s) : v ≤ w :=
  copyLE_rel_of_cover hp (copy_isRoom hP hL false hp hw0 hw2 hw3)
    (copy_nook_subset_pocket false hp) hv1 hv2 hw1 hw2'
    (not_mem_copyPocket false hp (varPt_snd_lt hp hv2))
    (not_mem_copyPocket false hp (inPt_snd_lt hp hw2')) hcov

/-- **Viewers of a copy nook, walls form**: a point strictly below the ceiling that sees a point of
the nook segment lies in `copyPV`. -/
theorem copy_viewer_mem_PV_of_walls (hP : P.Simple) (hL : P.InteriorLeft) (ge : Bool)
    (hp : CopyParams H a b)
    (hw0 : ∃ i < P.n, P.vtx i = copyNbot ge H a b ∧ P.vtx ((i + 1) % P.n) = copyLm ge H a b)
    (hw2 : ∃ i < P.n, P.vtx i = copyRm ge H a b ∧ P.vtx ((i + 1) % P.n) = copyNtop ge H a b)
    (hw3 : ∃ i < P.n, P.vtx i = copyNtop ge H a b ∧ P.vtx ((i + 1) % P.n) = copyNbot ge H a b)
    {s p : Point} (hs : s ∈ segment (copyNbot ge H a b) (copyNtop ge H a b)) (hp2 : p.2 < 2 * H)
    (hsees : P.Sees p s) : p ∈ copyPV ge H a b :=
  copy_viewer_mem_PV ge hp (copy_isRoom hP hL ge hp hw0 hw2 hw3) (copy_nook_subset_pocket ge hp)
    hs (not_mem_copyPocket ge hp hp2) hsees

end

/-! ### Interface with the definition layer (`Params.lean`, `Polygon.lean`) -/

/-- Standing hypotheses from rational parameters. -/
theorem CopyParams.of_rat {H a b : ℚ} (h1 : 1000 ≤ H) (h2 : H ≤ b - a) (h3 : b - a ≤ 2 * H) :
    CopyParams (H : ℝ) (a : ℝ) (b : ℝ) where
  hH := by exact_mod_cast h1
  hlo := by
    have : ((H : ℚ) : ℝ) ≤ ((b - a : ℚ) : ℝ) := by exact_mod_cast h2
    push_cast at this; exact this
  hhi := by
    have : ((b - a : ℚ) : ℝ) ≤ ((2 * H : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at this; exact this

/-- **S1 ⇒ standing hypotheses.** For a variable `k < n` and an input `b = g_c + δ` of a slot
`c < C` (`30 ≤ δ ≤ 600`), the copy-nook parameters satisfy `CopyParams`. -/
theorem copyParams_of_input {n : ℕ} {Φ : List ETRINVREV.Constraint} {k c : ℕ} (hk : k < n)
    (hc : c < paramC Φ) {δ : ℚ} (hδ0 : 30 ≤ δ) (hδ1 : δ ≤ 600) :
    CopyParams ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) (((slotG n Φ c : ℚ) + δ : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := s1 (Φ := Φ) hk hc hδ0 hδ1
  exact CopyParams.of_rat (paramH_ge_q n Φ) (by linarith) (by linarith)

/-- The copy offsets of `Polygon.lean` and of this file agree. -/
theorem copyE_cast (ge : Bool) : ((copyE ge : ℚ) : ℝ) = copyOff ge := by
  cases ge <;> simp [copyE, copyOff]

/-- The nook abscissa of `Polygon.lean` is `copyXN`. -/
theorem nookX_cast (a b : ℚ) (ge : Bool) :
    ((nookX a b ge : ℚ) : ℝ) = copyXN ge (a : ℝ) (b : ℝ) := by
  simp only [nookX, copyXN, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, copyE_cast]

/-- The rational vertex `nookTop` of `Polygon.lean` is `copyNtop`. -/
theorem ratPoint_nookTop (a b : ℚ) (ge : Bool) (H : ℚ) :
    ratPoint (nookTop a b ge H) = copyNtop ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  simp only [ratPoint, nookTop, copyNtop, nookX_cast]
  push_cast; rfl

/-- The rational vertex `nookBot` of `Polygon.lean` is `copyNbot`. -/
theorem ratPoint_nookBot (a b : ℚ) (ge : Bool) (H : ℚ) :
    ratPoint (nookBot a b ge H) = copyNbot ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  simp only [ratPoint, nookBot, copyNbot, nookX_cast]
  push_cast; rfl

/-- The rational vertex `nookPs` of `Polygon.lean` is `copyPs`. -/
theorem ratPoint_nookPs (a b : ℚ) (ge : Bool) (H : ℚ) :
    ratPoint (nookPs a b ge H) = copyPs ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  simp only [ratPoint, nookPs, copyPs]
  push_cast
  rw [nookX_cast]

/-- The rational vertex `nookPt` of `Polygon.lean` is `copyPt`. -/
theorem ratPoint_nookPt (a b : ℚ) (ge : Bool) (H : ℚ) :
    ratPoint (nookPt a b ge H) = copyPt ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  simp only [ratPoint, nookPt, copyPt]
  push_cast
  rw [nookX_cast]

/-- The copy nook chain of `Polygon.lean` is `R_m, N_top, N_bot, L_m`. -/
theorem copyNook_map (a b : ℚ) (ge : Bool) (H : ℚ) :
    (copyNook a b ge H).map ratPoint =
      [copyRm ge (H : ℝ) (a : ℝ) (b : ℝ), copyNtop ge (H : ℝ) (a : ℝ) (b : ℝ),
        copyNbot ge (H : ℝ) (a : ℝ) (b : ℝ), copyLm ge (H : ℝ) (a : ℝ) (b : ℝ)] := by
  cases ge <;> simp [copyNook, ratPoint_nookTop, ratPoint_nookBot, ratPoint_nookPs,
    ratPoint_nookPt]

end Stade

end ArtGallery

end
