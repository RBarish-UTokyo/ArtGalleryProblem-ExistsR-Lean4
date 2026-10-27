module

public import ArtGallery.Hardness.Sec5.CoverChanKinds

/-!
# Section 5, sufficiency (vi): the template facts by kind

Uniform access (by `Kind`) to the template facts used for the coverage of a unit, for an
arbitrary simple counter-clockwise polygon `P` containing the template chain (`ChainAt`) with the
separation `SepAt` (template coordinates):

* the closed template chain `tK k` (the template room, door the mouth), `tK_room`,
  `tK_subset` (it lies in the region);
* the cover pieces `cvPieces k` and `tR_subset`;
* the channel certificate `chanOf k` (`chanOf_ok`);
* **T-cover** `tK_cover`: under the constraint of the kind (`KindCons`), every point of the
  template room is seen by one of the canonical template guards `tGuard k v X`;
* the receivers: `recvIdx k τ` (the position of receiver `τ`), its guard segment is the receiver
  `[R₀, R₁]` of the channel certificate (`tGuard_recv_mem`) and the canonical guard is the
  corridor receiver point at the copied offset (`tGuard_recv_place`).
-/

@[expose] public section

namespace ArtGallery.Sec5.CoverT

open ArtGallery Set Polygon Vis.Cert Tmpl ArtGallery.Sec5.Count

/-- The channel certificate of a kind. -/
def chanOf : Kind → ChanD
  | .orient => chanOR
  | .ge => chanGE
  | .le => chanLE
  | .inv => chanInv

/-- The cover pieces of the template region of a kind. -/
def cvPieces : Kind → List (List IPt)
  | .orient => addORCvPieces
  | .ge => addGECvPieces
  | .le => addLECvPieces
  | .inv => invCvPieces

theorem chanOf_ok (k : Kind) : (chanOf k).chanB (tmplR k) (cvPieces k) = true := by
  cases k
  · exact chanOR_ok
  · exact chanGE_ok
  · exact chanLE_ok
  · exact chanInv_ok

@[simp] theorem chanOf_V (k : Kind) : (chanOf k).V = tmplV k := by cases k <;> rfl

@[simp] theorem chanOf_D (k : Kind) : (chanOf k).D = (tmplD k : ℤ) := by cases k <;> rfl

/-- The closed template chain (the template room). -/
noncomputable def tK (k : Kind) : Polygon := Polygon.mk ((tmplV k).map intPoint)

/-- The mouth: from the last chain vertex back to the first. -/
def tMouth (k : Kind) : Set Point :=
  ArtGallery.segment (intPoint (cv (tmplV k) ((tmplV k).length - 1))) (intPoint (cv (tmplV k) 0))

theorem tK_simple (k : Kind) : (tK k).Simple := by
  cases k
  · rw [tK, tmplV_orient]; exact addORK_simple
  · rw [tK, tmplV_ge]; exact addGEK_simple
  · rw [tK, tmplV_le]; exact addLEK_simple
  · rw [tK, tmplV_inv]; exact invK_simple

theorem tK_ccw (k : Kind) : (tK k).InteriorLeft := by
  cases k
  · rw [tK, tmplV_orient]; exact addORK_ccw
  · rw [tK, tmplV_ge]; exact addGEK_ccw
  · rw [tK, tmplV_le]; exact addLEK_ccw
  · rw [tK, tmplV_inv]; exact invK_ccw

theorem tK_sub_TR (k : Kind) : (tK k).filled ⊆ unionHull (cvPieces k) := by
  cases k
  · rw [tK, tmplV_orient]; exact addORK_sub_TR
  · rw [tK, tmplV_ge]; exact addGEK_sub_TR
  · rw [tK, tmplV_le]; exact addLEK_sub_TR
  · rw [tK, tmplV_inv]; exact invK_sub_TR

section Poly

variable {P : Polygon} {a : ℕ} {k : Kind}

theorem tK_room (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplV k) a) :
    P.IsRoom (tK k).filled (tMouth k) := by
  cases k
  · rw [tK, tMouth]; rw [tmplV_orient] at hC ⊢; exact addOR_room hP hL hC
  · rw [tK, tMouth]; rw [tmplV_ge] at hC ⊢; exact addGE_room hP hL hC
  · rw [tK, tMouth]; rw [tmplV_le] at hC ⊢; exact addLE_room hP hL hC
  · rw [tK, tMouth]; rw [tmplV_inv] at hC ⊢; exact inv_room hP hL hC

theorem tR_subset (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplV k) a)
    (hS : SepAt P (tmplV k) a (tmplR k)) : unionHull (cvPieces k) ⊆ P.filled := by
  cases k
  · rw [tmplV_orient] at hC hS; exact addORTR_subset hP hL hC hS
  · rw [tmplV_ge] at hC hS; exact addGETR_subset hP hL hC hS
  · rw [tmplV_le] at hC hS; exact addLETR_subset hP hL hC hS
  · rw [tmplV_inv] at hC hS; exact invTR_subset hP hL hC hS

theorem tK_subset (hP : P.Simple) (hL : P.InteriorLeft) (hC : ChainAt P (tmplV k) a)
    (hS : SepAt P (tmplV k) a (tmplR k)) : (tK k).filled ⊆ P.filled :=
  (tK_sub_TR k).trans (tR_subset hP hL hC hS)

end Poly

/-- **The template positions lie in the region** (every point of a position sees one of its
witnesses). -/
theorem spot_subset {P : Polygon} {a : ℕ} {k : Kind} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P (tmplV k) a) (hS : SepAt P (tmplV k) a (tmplR k)) (X : Fin (tsysOf k).r) :
    convexHull ℝ (intSet ((tsysOf k).spot X)) ⊆ P.filled := by
  have key : ∀ {L : List IPt} {w : Point}, (∀ x ∈ convexHull ℝ (intSet L), P.Sees x w) →
      convexHull ℝ (intSet L) ⊆ P.filled := fun h x hx =>
    h x hx (Geometry.left_mem_segment _ _)
  cases k
  · rw [tmplV_orient] at hC hS
    change Fin 5 at X
    fin_cases X
    · exact key (addOR_sees_qa hP hL hC hS)
    · exact key (addOR_sees_pqa hP hL hC hS)
    · exact key (addOR_sees_rjT0 hP hL hC hS)
    · exact key (addOR_sees_rit0 hP hL hC hS)
    · exact key (addOR_sees_ri2t0 hP hL hC hS)
  · rw [tmplV_ge] at hC hS
    change Fin 5 at X
    fin_cases X
    · exact key (addGE_sees_qa hP hL hC hS)
    · exact key (addGE_sees_rjT0 hP hL hC hS)
    · exact key (addGE_sees_rit0 hP hL hC hS)
    · exact key (addGE_sees_rlt0 hP hL hC hS)
    · exact key (addGE_sees_ri2t0 hP hL hC hS)
  · rw [tmplV_le] at hC hS
    change Fin 5 at X
    fin_cases X
    · exact key (addLE_sees_qa hP hL hC hS)
    · exact key (addLE_sees_rjT0 hP hL hC hS)
    · exact key (addLE_sees_rit0 hP hL hC hS)
    · exact key (addLE_sees_rlt0 hP hL hC hS)
    · exact key (addLE_sees_ri2t0 hP hL hC hS)
  · rw [tmplV_inv] at hC hS
    change Fin 3 at X
    fin_cases X
    · exact key (inv_sees_qa hP hL hC hS)
    · exact key (inv_sees_riT0 hP hL hC hS)
    · exact key (inv_sees_rjT0 hP hL hC hS)

/-! ### The constraint of a unit and T-cover -/

/-- The constraint enforced by the template of kind `k` on the receiver values `v τ`. -/
def KindCons : Kind → (ℕ → ℝ) → Prop
  | .orient, v => 5 / 2 ≤ v 1 + v 0
  | .ge, v => v 0 ≤ v 2 + v 1
  | .le, v => v 0 + 5 / 2 ≤ v 2 + v 1
  | .inv, v => v 1 * (5 / 2 - v 0) = 1

/-- **T-cover**: every point of the template room is seen by a canonical template guard. -/
theorem tK_cover {P : Polygon} {a : ℕ} {k : Kind} (hP : P.Simple) (hL : P.InteriorLeft)
    (hC : ChainAt P (tmplV k) a) (hS : SepAt P (tmplV k) a (tmplR k)) {v : ℕ → ℝ}
    (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) (hc : KindCons k v) :
    ∀ z ∈ (tK k).filled, ∃ X, P.Sees (tGuard k v X) z := by
  intro z hz
  cases k
  · rw [tmplV_orient] at hC hS
    rw [tK, tmplV_orient] at hz
    rcases addOR_cover_K hP hL hC hS (hv 1).1 (hv 1).2 (hv 0).1 (hv 0).2 hc z hz with
      h | h | h | h | h
    · exact ⟨(4 : Fin 5), h⟩
    · exact ⟨(2 : Fin 5), h⟩
    · exact ⟨(1 : Fin 5), h⟩
    · exact ⟨(3 : Fin 5), h⟩
    · exact ⟨(0 : Fin 5), h⟩
  · rw [tmplV_ge] at hC hS
    rw [tK, tmplV_ge] at hz
    rcases addGE_cover_K hP hL hC hS (hv 2).1 (hv 2).2 (hv 1).1 (hv 1).2 (hv 0).1 (hv 0).2 hc z hz
      with h | h | h | h | h
    · exact ⟨(4 : Fin 5), h⟩
    · exact ⟨(1 : Fin 5), h⟩
    · exact ⟨(3 : Fin 5), h⟩
    · exact ⟨(2 : Fin 5), h⟩
    · exact ⟨(0 : Fin 5), h⟩
  · rw [tmplV_le] at hC hS
    rw [tK, tmplV_le] at hz
    rcases addLE_cover_K hP hL hC hS (hv 2).1 (hv 2).2 (hv 1).1 (hv 1).2 (hv 0).1 (hv 0).2 hc z hz
      with h | h | h | h | h
    · exact ⟨(4 : Fin 5), h⟩
    · exact ⟨(1 : Fin 5), h⟩
    · exact ⟨(3 : Fin 5), h⟩
    · exact ⟨(2 : Fin 5), h⟩
    · exact ⟨(0 : Fin 5), h⟩
  · rw [tmplV_inv] at hC hS
    rw [tK, tmplV_inv] at hz
    have h0 := hv 0
    rcases inv_cover_K hP hL hC hS (hv 1).1 (hv 1).2 (by linarith) (by linarith) hc z hz with
      h | h | h
    · exact ⟨(1 : Fin 3), h⟩
    · exact ⟨(2 : Fin 3), h⟩
    · exact ⟨(0 : Fin 3), h⟩

/-! ### The receivers -/

/-- The position of receiver `τ` among the template positions. -/
def recvIdx : (k : Kind) → ℕ → Fin (tsysOf k).r
  | .orient, τ => if τ = 0 then (2 : Fin 5) else (3 : Fin 5)
  | .ge, τ => if τ = 0 then (3 : Fin 5) else if τ = 1 then (1 : Fin 5) else (2 : Fin 5)
  | .le, τ => if τ = 0 then (3 : Fin 5) else if τ = 1 then (1 : Fin 5) else (2 : Fin 5)
  | .inv, τ => if τ = 0 then (2 : Fin 3) else (1 : Fin 3)

theorem recv_length (k : Kind) : (chanOf k).recv.length = (tmplT k).length := by cases k <;> rfl

/-- The guard segment of receiver `τ` is the receiver of the channel certificate. -/
theorem recv_spot (k : Kind) {τ : ℕ} (hτ : τ < (tmplT k).length) :
    (tsysOf k).spot (recvIdx k τ) =
      [((chanOf k).recv.getD τ default).R0, ((chanOf k).recv.getD τ default).R1] := by
  cases k <;> simp only [tmplT, tmplTOR, tmplTGE, tmplTLE, tmplTInv, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;> rfl

theorem hull_pair_eq (A B : IPt) :
    convexHull ℝ (intSet [A, B]) = ArtGallery.segment (intPoint A) (intPoint B) := by
  rw [Geometry.segment_eq, intSet_cons, intSet_cons, intSet_nil, insert_empty_eq,
    convexHull_pair]

/-- The canonical guard of receiver `τ` lies on the receiver of the channel certificate. -/
theorem tGuard_recv_mem (k : Kind) {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) {τ : ℕ}
    (hτ : τ < (tmplT k).length) :
    tGuard k v (recvIdx k τ) ∈ ArtGallery.segment (intPoint ((chanOf k).recv.getD τ default).R0)
      (intPoint ((chanOf k).recv.getD τ default).R1) := by
  rw [← hull_pair_eq, ← recv_spot k hτ]
  exact tGuard_mem k hv (recvIdx k τ)

/-- The canonical guard of receiver `τ`, explicitly. -/
noncomputable def recvG : Kind → (ℕ → ℝ) → ℕ → Point
  | .orient, v, τ => if τ = 0 then addORB (v 0) else addORI (v 1)
  | .ge, v, τ => if τ = 0 then addGEC (v 0) else if τ = 1 then addGEB (v 1) else addGEI (v 2)
  | .le, v, τ => if τ = 0 then addLEC (v 0) else if τ = 1 then addLEB (v 1) else addLEI (v 2)
  | .inv, v, τ => if τ = 0 then invGq (5 / 2 - v 0) else invGp (v 1)

theorem tGuard_recv_eq (k : Kind) (v : ℕ → ℝ) {τ : ℕ} (hτ : τ < (tmplT k).length) :
    tGuard k v (recvIdx k τ) = recvG k v τ := by
  cases k <;> simp only [tmplT, tmplTOR, tmplTGE, tmplTLE, tmplTInv, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;> rfl

/-- The receiver points of the corridor: `place S H (T_τ + (t, 0))`, as a real point. -/
noncomputable def placeR (S H : ℝ) (T : Q2) (t : ℝ) : Point :=
  (S + 3 + ((T.1 : ℝ) + t) / S, H - 1 + (T.2 : ℝ) / S)

/-- **The canonical receiver guard is the corridor receiver point** at the copied offset
`v τ − 1/2`. -/
theorem tGuard_recv_place (k : Kind) (v : ℕ → ℝ) {S H : ℝ} (hS : 1000 ≤ S) {τ : ℕ}
    (hτ : τ < (tmplT k).length) :
    tmplMap k S H (S_ne_of hS) (tGuard k v (recvIdx k τ)) =
      placeR S H ((tmplT k).getD τ 0) (v τ - 1 / 2) := by
  have hS0 : S ≠ 0 := S_ne_of hS
  rw [tGuard_recv_eq k v hτ, tmplMap_apply]
  cases k <;> simp only [tmplT, tmplTOR, tmplTGE, tmplTLE, tmplTInv, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;>
    simp only [recvG, placeR, tmplD, tmplT, tmplTOR, tmplTGE, tmplTLE, tmplTInv,
      segGuard, addORB, addORI, addGEB, addGEI, addGEC, addLEB, addLEI, addLEC,
      invGp, invGq, invD, Geometry.lerp, intPoint, List.getD_cons_zero, List.getD_cons_succ,
      ↓reduceIte, OfNat.ofNat_ne_zero, one_ne_zero] <;>
    ext <;> push_cast <;> field_simp <;> ring

end ArtGallery.Sec5.CoverT

end
