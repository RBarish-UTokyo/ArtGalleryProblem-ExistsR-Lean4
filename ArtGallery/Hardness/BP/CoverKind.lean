module

public import ArtGallery.Hardness.BP.CoverChanData
public import ArtGallery.Hardness.Sec5.CoverKind

/-!
# Boundary-point variant, coverage: the template facts by kind

Uniform access (by `Kind`) to the facts of the boundary-point templates used for the coverage of
a unit, for an arbitrary simple counter-clockwise polygon `P` containing the template chain
(`ChainAt P (tmplVBP k) a`) with the separation `SepAt … (tmplRBP k)` (template coordinates), as
`Sec5/CoverKind.lean`:

* the closed template chain `tKBP k` (the template room, door the mouth `tMouthBP k`),
  `tKBP_room`, `tKBP_subset`;
* the cover pieces `cvPiecesBP k`, `tRBP_subset`, and the channel certificate `chanOfBP k`
  (`chanOfBP_ok`);
* the canonical template guards `tGuardBP k v j` (`j < tNumBP k`, in the order of the template
  positions: `ge`, `le`: `g, B, W, C, A`; `orient`: `g, p, B, W, A`; `inv`: `g, r_i, r_j`) for the
  receiver values `v τ`; the weak copy `A` gets the value of `W`;
* **T-cover** `tKBP_cover`: under the constraint of the kind (`Sec5.CoverT.KindCons`, unchanged:
  the receivers of a unit carry the same values as in Section 5), every point of the template room
  is seen by a canonical template guard;
* the receivers: `recvIdxBP k τ` (the position of receiver `τ`); its canonical guard lies on the
  receiver segment of the channel certificate (`tGuardBP_recv_mem`) and is the corridor receiver
  point at the copied offset (`tGuardBP_recv_place`).
-/

@[expose] public section

namespace ArtGallery.BP.CoverK

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl Tmpl
open ArtGallery.Sec5 (Kind)
open ArtGallery.Sec5.CoverT (ChanD RecvD KindCons placeR)

/-! ### Channel certificates and cover pieces -/

/-- The channel certificate of a kind. -/
def chanOfBP : Kind → ChanD
  | .orient => chanORBP
  | .ge => chanGEBP
  | .le => chanLEBP
  | .inv => chanInvBP

/-- The cover pieces of the template region of a kind. -/
def cvPiecesBP : Kind → List (List IPt)
  | .orient => bpORCvPieces
  | .ge => bpGECvPieces
  | .le => bpLECvPieces
  | .inv => bpInvCvPieces

theorem chanOfBP_ok (k : Kind) : (chanOfBP k).chanB (tmplRBP k) (cvPiecesBP k) = true := by
  cases k
  · exact chanORBP_ok
  · exact chanGEBP_ok
  · exact chanLEBP_ok
  · exact chanInvBP_ok

@[simp] theorem chanOfBP_V (k : Kind) : (chanOfBP k).V = tmplVBP k := by cases k <;> rfl

@[simp] theorem chanOfBP_D (k : Kind) : (chanOfBP k).D = (tmplDBP k : ℤ) := by cases k <;> rfl

/-! ### The template room -/

/-- The closed template chain (the template room). -/
noncomputable def tKBP (k : Kind) : Polygon := Polygon.mk ((tmplVBP k).map intPoint)

/-- The mouth: from the last chain vertex back to the first. -/
def tMouthBP (k : Kind) : Set Point :=
  ArtGallery.segment (intPoint (cv (tmplVBP k) ((tmplVBP k).length - 1)))
    (intPoint (cv (tmplVBP k) 0))

theorem tKBP_simple (k : Kind) : (tKBP k).Simple := by
  cases k
  · rw [tKBP, tmplVBP_orient]; exact bpORK_simple
  · rw [tKBP, tmplVBP_ge]; exact bpGEK_simple
  · rw [tKBP, tmplVBP_le]; exact bpLEK_simple
  · rw [tKBP, tmplVBP_inv]; exact bpInvK_simple

theorem tKBP_ccw (k : Kind) : (tKBP k).InteriorLeft := by
  cases k
  · rw [tKBP, tmplVBP_orient]; exact bpORK_ccw
  · rw [tKBP, tmplVBP_ge]; exact bpGEK_ccw
  · rw [tKBP, tmplVBP_le]; exact bpLEK_ccw
  · rw [tKBP, tmplVBP_inv]; exact bpInvK_ccw

theorem tKBP_sub_TR (k : Kind) : (tKBP k).filled ⊆ unionHull (cvPiecesBP k) := by
  cases k
  · rw [tKBP, tmplVBP_orient]; exact bpORK_sub_TR
  · rw [tKBP, tmplVBP_ge]; exact bpGEK_sub_TR
  · rw [tKBP, tmplVBP_le]; exact bpLEK_sub_TR
  · rw [tKBP, tmplVBP_inv]; exact bpInvK_sub_TR

section Poly

variable {P : Polygon} {a : ℕ} {k : Kind}

theorem tKBP_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplVBP k) a) :
    P.IsRoom (tKBP k).filled (tMouthBP k) := by
  cases k
  · rw [tKBP, tMouthBP]; rw [tmplVBP_orient] at hC ⊢; exact bpOR_room hP hL hC
  · rw [tKBP, tMouthBP]; rw [tmplVBP_ge] at hC ⊢; exact bpGE_room hP hL hC
  · rw [tKBP, tMouthBP]; rw [tmplVBP_le] at hC ⊢; exact bpLE_room hP hL hC
  · rw [tKBP, tMouthBP]; rw [tmplVBP_inv] at hC ⊢; exact bpInv_room hP hL hC

theorem tRBP_subset (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplVBP k) a)
    (hS : SepAt P (tmplVBP k) a (tmplRBP k)) : unionHull (cvPiecesBP k) ⊆ P.filled := by
  cases k
  · rw [tmplVBP_orient] at hC hS; exact bpORTR_subset hP hL hC hS
  · rw [tmplVBP_ge] at hC hS; exact bpGETR_subset hP hL hC hS
  · rw [tmplVBP_le] at hC hS; exact bpLETR_subset hP hL hC hS
  · rw [tmplVBP_inv] at hC hS; exact bpInvTR_subset hP hL hC hS

theorem tKBP_subset (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplVBP k) a)
    (hS : SepAt P (tmplVBP k) a (tmplRBP k)) : (tKBP k).filled ⊆ P.filled :=
  (tKBP_sub_TR k).trans (tRBP_subset hP hL hC hS)

end Poly

/-! ### The canonical template guards -/

/-- The number of template positions of a kind. -/
def tNumBP : Kind → ℕ
  | .orient => 5
  | .ge => 5
  | .le => 5
  | .inv => 3

/-- The canonical template guards (template coordinates) for the receiver values `v τ`
(`τ = 0` belongs to the largest working slot), in the order of the template positions:
* `ge`, `le` (`g, B, W, C, A`): `g`, `B (v 2)`, `W (v 1)`, `C (v 0)`, `A (v 1)`;
* `orient` (`g, p, B, W, A`): `g`, `p`, `B (v 1)`, `W (v 0)`, `A (v 0)`;
* `inv` (`g, r_i, r_j`): `g`, `r_i (v 1)`, `r_j (5/2 − v 0)` (`r_j` is read from the right). -/
noncomputable def tGuardBP : Kind → (ℕ → ℝ) → ℕ → Point
  | .ge, v, j => [intPoint (cv bpGEV 65), bpGEB (v 2), bpGEW (v 1), bpGEC (v 0), bpGEA (v 1)].getD j 0
  | .le, v, j => [intPoint (cv bpLEV 65), bpLEB (v 2), bpLEW (v 1), bpLEC (v 0), bpLEA (v 1)].getD j 0
  | .orient, v, j => [intPoint (cv bpORV 61), bpORC, bpORB (v 1), bpORW (v 0), bpORA (v 0)].getD j 0
  | .inv, v, j => [intPoint (cv bpInvV 32), bpInvGp (v 1), bpInvGq (5 / 2 - v 0)].getD j 0

/-- **T-cover**: under the constraint of the kind, every point of the template room is seen by a
canonical template guard. -/
theorem tKBP_cover {P : Polygon} {a : ℕ} {k : Kind} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P (tmplVBP k) a) (hS : SepAt P (tmplVBP k) a (tmplRBP k)) {v : ℕ → ℝ}
    (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) (hc : KindCons k v) :
    ∀ z ∈ (tKBP k).filled, ∃ j < tNumBP k, P.Sees (tGuardBP k v j) z := by
  intro z hz
  cases k
  · rw [tmplVBP_orient] at hC hS
    rw [tKBP, tmplVBP_orient] at hz
    simp only [KindCons] at hc
    rcases bpOR_cover_K hP hL hC hS (hv 0).1 (hv 0).2 (hv 1).1 (hv 1).2 (by linarith) z hz with
      h | h | h | h | h
    · exact ⟨4, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨0, by decide, h⟩
  · rw [tmplVBP_ge] at hC hS
    rw [tKBP, tmplVBP_ge] at hz
    simp only [KindCons] at hc
    rcases bpGE_cover_K hP hL hC hS (hv 1).1 (hv 1).2 (hv 2).1 (hv 2).2 (hv 0).1 (hv 0).2
      (by linarith) z hz with h | h | h | h | h
    · exact ⟨4, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨0, by decide, h⟩
  · rw [tmplVBP_le] at hC hS
    rw [tKBP, tmplVBP_le] at hz
    simp only [KindCons] at hc
    rcases bpLE_cover_K hP hL hC hS (hv 1).1 (hv 1).2 (hv 2).1 (hv 2).2 (hv 0).1 (hv 0).2
      (by linarith) z hz with h | h | h | h | h
    · exact ⟨4, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨0, by decide, h⟩
  · rw [tmplVBP_inv] at hC hS
    rw [tKBP, tmplVBP_inv] at hz
    simp only [KindCons] at hc
    have h0 := hv 0
    rcases bpInv_cover_K hP hL hC hS (hv 1).1 (hv 1).2 (y := 5 / 2 - v 0) (by linarith)
      (by linarith) hc z hz with h | h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨0, by decide, h⟩

/-! ### The receivers -/

/-- The position of receiver `τ` among the template positions. -/
def recvIdxBP : Kind → ℕ → ℕ
  | .orient, τ => if τ = 0 then 3 else 2
  | .ge, τ => if τ = 0 then 3 else if τ = 1 then 2 else 1
  | .le, τ => if τ = 0 then 3 else if τ = 1 then 2 else 1
  | .inv, τ => if τ = 0 then 2 else 1

theorem recvBP_length (k : Kind) : (chanOfBP k).recv.length = (tmplTBP k).length := by
  cases k <;> rfl

theorem recvIdxBP_lt (k : Kind) (τ : ℕ) : recvIdxBP k τ < tNumBP k := by
  cases k <;> simp only [recvIdxBP, tNumBP] <;> split_ifs <;> decide

theorem hull_pair_mem {A B : IPt} {u : ℝ} (h0 : 1 / 2 ≤ u) (h1 : u ≤ 2) :
    segGuard A B u ∈ ArtGallery.segment (intPoint A) (intPoint B) := by
  rw [← Sec5.CoverT.hull_pair_eq]; exact segGuard_mem h0 h1

/-- The canonical guard of receiver `τ` lies on the receiver of the channel certificate. -/
theorem tGuardBP_recv_mem (k : Kind) {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) {τ : ℕ}
    (hτ : τ < (tmplTBP k).length) :
    tGuardBP k v (recvIdxBP k τ) ∈
      ArtGallery.segment (intPoint ((chanOfBP k).recv.getD τ default).R0)
        (intPoint ((chanOfBP k).recv.getD τ default).R1) := by
  cases k <;> simp only [tmplTBP, tmplTORBP, tmplTGEBP, tmplTLEBP, tmplTInvBP, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ
  · exact hull_pair_mem (hv 0).1 (hv 0).2
  · exact hull_pair_mem (hv 1).1 (hv 1).2
  · exact hull_pair_mem (hv 0).1 (hv 0).2
  · exact hull_pair_mem (hv 1).1 (hv 1).2
  · exact hull_pair_mem (hv 2).1 (hv 2).2
  · exact hull_pair_mem (hv 0).1 (hv 0).2
  · exact hull_pair_mem (hv 1).1 (hv 1).2
  · exact hull_pair_mem (hv 2).1 (hv 2).2
  · have h := bpInvGq_mem (y := 5 / 2 - v 0) (by linarith [(hv 0).2]) (by linarith [(hv 0).1])
    rw [show bpInvRj = [((chanOfBP .inv).recv.getD 0 default).R0,
      ((chanOfBP .inv).recv.getD 0 default).R1] by decide, Sec5.CoverT.hull_pair_eq] at h
    exact h
  · have h := bpInvGp_mem (hv 1).1 (hv 1).2
    rw [show bpInvRi = [((chanOfBP .inv).recv.getD 1 default).R0,
      ((chanOfBP .inv).recv.getD 1 default).R1] by decide, Sec5.CoverT.hull_pair_eq] at h
    exact h

/-- **The canonical receiver guard is the corridor receiver point** at the copied offset
`v τ − 1/2`. -/
theorem tGuardBP_recv_place (k : Kind) (v : ℕ → ℝ) {S H : ℝ} (hS : S ≠ 0) {τ : ℕ}
    (hτ : τ < (tmplTBP k).length) :
    tmplMapBP k S H hS (tGuardBP k v (recvIdxBP k τ)) =
      placeR S H ((tmplTBP k).getD τ 0) (v τ - 1 / 2) := by
  rw [tmplMapBP_apply]
  cases k <;> simp only [tmplTBP, tmplTORBP, tmplTGEBP, tmplTLEBP, tmplTInvBP, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;>
    simp +decide only [tGuardBP, recvIdxBP, placeR, tmplDBP, tmplTBP, tmplTORBP, tmplTGEBP, tmplTLEBP,
      tmplTInvBP, segGuard, bpORB, bpORW, bpGEB, bpGEW, bpGEC, bpLEB, bpLEW, bpLEC, bpInvGp,
      bpInvGq, bpInvD, Geometry.lerp, intPoint, List.getD_cons_zero, List.getD_cons_succ,
      ↓reduceIte, OfNat.ofNat_ne_zero, one_ne_zero] <;>
    ext <;> push_cast <;> field_simp <;> ring

end ArtGallery.BP.CoverK

end
