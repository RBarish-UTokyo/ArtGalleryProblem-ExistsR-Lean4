module

public import ArtGallery.Stade.GuardAddGe
public import ArtGallery.Stade.GuardInv

/-!
# The canonical guards see the gadget slots (proof plan §9)

For a slot with origin `G` holding a gadget of kind `k`, `slotPieces k G H` lists the convex
pieces of the region below the floor belonging to the slot (corridors, pockets, rooms, bay, aux
wedge, needles), and `slotGuards k G v_x v_y v_z` its guards (inputs at the values of the
variables of the constraint, and the canonical aux point).  `slot_cover`: if the constraint
holds (`kRel`), every point of every piece is seen by one of the slot's guards.
-/

@[expose] public section

namespace ArtGallery.Stade

variable {P : Polygon}

/-- The pieces of the region of a slot (origin `G`, needle depth `H`) below the floor. -/
noncomputable def slotPieces (k : TKind) (G H : ℝ) : List Polygon :=
  match k with
  | .invGe => [needleL (G + 40) (-1) H, igCorridor G, igPocket G, needleR (G + 100) (-1) H]
  | .invRevLe => [irCorridor G, irPocket G, irNeedle G H, needleR (G + 104) (-1) H]
  | .addLe => alPieces G H ++ [needleR (G + 530) (-1) H]
  | .addGe => agPieces G H ++ [needleR (G + 370) (-1) H]

/-- The guards of a slot: the input guards (values `v_x, v_y, v_z` of the variables) and the
canonical aux point. -/
noncomputable def slotGuards (k : TKind) (G vx vy vz : ℝ) : Set Point :=
  match k with
  | .invGe => {inPt (G + 40) vx, inPt (G + 100) vy}
  | .invRevLe => {inPt (G + 60) vx, inPt (G + 104) vy}
  | .addLe => {alI G vx vy, inPt (G + 370) vx, inPt (G + 210) vy, inPt (G + 530) vz}
  | .addGe => {agI G vx vy, inPt (G + 370) vx, inPt (G + 210) vy, inPt (G + 185 / 2) vz}

/-- The relation enforced by a gadget of kind `k`. -/
def kRel (k : TKind) (vx vy vz : ℝ) : Prop :=
  match k with
  | .invGe => 1 ≤ vx * vy
  | .invRevLe => vx * (5 / 2 - vy) ≤ 1
  | .addLe => vx + vy ≤ vz
  | .addGe => vz ≤ vx + vy

/-- The walls of the pockets of an addition gadget are edges of `P`. -/
def kWalls (P : Polygon) (k : TKind) (G : ℝ) : Prop :=
  match k with
  | .addLe => AlWalls P G
  | .addGe => AgWalls P G
  | _ => True

/-- **Slot coverage.**  `A` (the hall) is a convex part of the region containing the floor line
`[G + 30, G + 600] × {−1}` and the input band `[G + 30, G + 600] × [0, 6]`; the pieces of the
slot lie in the region; for an addition gadget the pocket walls are edges of `P`.  If the values
lie in `[1/2, 2]` and satisfy the relation of the gadget, every point of every piece of the slot
is seen by a guard of the slot. -/
theorem slot_cover (hP : P.Simple) (hL : P.InteriorLeft) (k : TKind) {G H : ℝ}
    (hH : 1000 ≤ H) {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hFA : ∀ x, G + 30 ≤ x → x ≤ G + 600 → ((x, -1) : Point) ∈ A)
    (hBA : ∀ x y, G + 30 ≤ x → x ≤ G + 600 → 0 ≤ y → y ≤ 6 → ((x, y) : Point) ∈ A)
    (hKP : ∀ K ∈ slotPieces k G H, piece K ⊆ P.filled) (hW : kWalls P k G) {vx vy vz : ℝ}
    (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz)
    (hz2 : vz ≤ 2) (hrel : kRel k vx vy vz) :
    ∀ K ∈ slotPieces k G H, ∀ z ∈ piece K, ∃ g ∈ slotGuards k G vx vy vz, P.Sees g z := by
  have hH0 : 0 < H := by linarith
  have hin : ∀ (δ v : ℝ), 30 ≤ δ → δ ≤ 600 → 1 / 2 ≤ v → v ≤ 2 → inPt (G + δ) v ∈ A :=
    fun δ v h1 h2 h3 h4 => hBA _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  have hfl : ∀ u w : ℝ, G + 30 ≤ u → u ≤ G + 600 → G + 30 ≤ w → w ≤ G + 600 →
      segment ((u, -1) : Point) (w, -1) ⊆ A := fun u w h1 h2 h3 h4 =>
    seg_floor_subset hA hFA h1 h2 h3 h4
  cases k with
  | invGe =>
    have hfA : segment (igC1 G) (igC2 G) ⊆ A := hfl _ _ (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hxA := hin 40 vx (by norm_num) (by norm_num) hx1 hx2
    have hyA := hin 100 vy (by norm_num) (by norm_num) hy1 hy2
    have hBP := hKP (igCorridor G) (by simp [slotPieces])
    have hCP := hKP (igPocket G) (by simp [slotPieces])
    intro K hK z hz
    simp only [slotPieces, List.mem_cons, List.mem_nil_iff, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, needleL_sees hA hAP hH0 (by linarith) hxA
        (hfl _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hKP _ (by simp [slotPieces])) z hz⟩
    · exact ⟨_, Or.inl rfl, ig_corridor_sees hA hAP hfA hBP hxA
        (by simp only [inPt_fst]; linarith) (by simp only [inPt_fst]; linarith)
        (by simp only [inPt_snd]; linarith) (by simp only [inPt_snd]; linarith) z hz⟩
    · rcases ig_pocket_cover hA hAP hfA hBP hCP hx1 hx2 hy1 hy2 hxA hyA hrel z hz with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    · exact ⟨_, Or.inr rfl, needleR_sees hA hAP hH0 (by linarith) hyA
        (hfl _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hKP _ (by simp [slotPieces])) z hz⟩
  | invRevLe =>
    have hfA : segment (irP G) (irQ' G) ⊆ A := hfl _ _ (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hxA := hin 60 vx (by norm_num) (by norm_num) hx1 hx2
    have hyA := hin 104 vy (by norm_num) (by norm_num) hy1 hy2
    have hBP := hKP (irCorridor G) (by simp [slotPieces])
    have hCP := hKP (irPocket G) (by simp [slotPieces])
    intro K hK z hz
    simp only [slotPieces, List.mem_cons, List.mem_nil_iff, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, ir_corridor_sees_x hA hAP hfA hBP hx1 hxA z hz⟩
    · rcases ir_pocket_cover hA hAP hfA hBP hCP hx1 hx2 hy1 hy2 hxA hyA hrel z hz with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    · exact ⟨_, Or.inl rfl, ir_needle_sees hA hAP hfA hBP hCP hH0
        (hKP _ (by simp [slotPieces])) hx1 hx2 hxA z hz⟩
    · exact ⟨_, Or.inr rfl, needleR_sees hA hAP hH0 (by linarith) hyA
        (hfl _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hKP _ (by simp [slotPieces])) z hz⟩
  | addLe =>
    have hWA : segment (alWL G) (alWR G) ⊆ A := hfl _ _ (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hxA := hin 370 vx (by norm_num) (by norm_num) hx1 hx2
    have hyA := hin 210 vy (by norm_num) (by norm_num) hy1 hy2
    have hzA := hin 530 vz (by norm_num) (by norm_num) hz1 hz2
    intro K hK z hz
    simp only [slotPieces, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hK
    rcases hK with hK | rfl
    · exact al_slot_cover hP hL hW hA hAP hWA hH0
        (fun K hK => hKP K (by simp only [slotPieces, List.mem_append]; exact Or.inl hK))
        hx1 hy1 hz2 hrel hxA hyA hzA K hK z hz
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), needleR_sees hA hAP hH0 (by linarith) hzA
        (hfl _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hKP _ (by simp [slotPieces])) z hz⟩
  | addGe =>
    have hWA : segment (agWL G) (agWR G) ⊆ A := hfl _ _ (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hxA := hin 370 vx (by norm_num) (by norm_num) hx1 hx2
    have hyA := hin 210 vy (by norm_num) (by norm_num) hy1 hy2
    have hzA := hin (185 / 2) vz (by norm_num) (by norm_num) hz1 hz2
    intro K hK z hz
    simp only [slotPieces, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hK
    rcases hK with hK | rfl
    · exact ag_slot_cover hP hL hW hA hAP hWA hH0
        (fun K hK => hKP K (by simp only [slotPieces, List.mem_append]; exact Or.inl hK))
        hx1 hx2 hy1 hy2 hz1 hz2 hrel hxA hyA hzA K hK z hz
    · exact ⟨_, Or.inr (Or.inl rfl), needleR_sees hA hAP hH0 (by linarith) hxA
        (hfl _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hKP _ (by simp [slotPieces])) z hz⟩

end ArtGallery.Stade

end
