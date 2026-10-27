module

public import ArtGallery.Stade.Wedges
public import ArtGallery.Stade.Counting

/-!
# Stade's construction: the lower bound (a) and the guard assignment (proof plan §4, §8.1)

The guard regions of `poly n Φ` are indexed by `Idx n Φ = Fin n ⊕ Fin m ⊕ Fin A` (variables,
input segments, addition slots), `|Idx n Φ| = guards n Φ` (`card_Idx`).  Each region `X` has a
**witness** `wit X` on the boundary (the tip of its top wedge `W1`, resp. the aux tip) and a
**viewer set** `vset X` (the slab `|x − s| ≤ 4`, resp. the aux region) containing every point that
sees the witness; the viewer sets are pairwise disjoint (`vset_disj`, Wedges.lean).

* **(a)** `card_le_of_boundaryGuard'`: every boundary guard set has at least `guards n Φ`
  points (boundary pigeonhole, `boundaryGuard_viewerSets`).
* **Assignment (§8.1, L4.4)** `exists_assign`: a boundary guard set `G` with `|G| = guards n Φ`
  carries a bijection `γ : Idx n Φ → G` such that `γ (variable k)` lies on the variable segment
  `{a_k} × [H, H+3]` (at height `H + 1` if `x_k = 1` is a constraint), `γ (input j)` on the input
  segment `{b_j} × [0, 6]` and `γ (aux j)` in its aux region (`Assign`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain ArtGallery.Irrational Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### The index type -/

/-- The addition slots, in increasing order. -/
def addSlotList (Φ : List Constraint) : List ℕ :=
  (List.range (paramC Φ)).filter (fun c => isAdd (gadAt Φ c))

theorem lower_map_getD_range {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem addSlotList_length (Φ : List Constraint) :
    (addSlotList Φ).length = ((gad Φ).filter isAdd).length := by
  unfold addSlotList
  conv_rhs => rw [← lower_map_getD_range (gad Φ) (.one 0)]
  rw [List.filter_map, List.length_map]
  rfl

/-- `guards n Φ = n + m + A`. -/
theorem guards_eq (n : ℕ) (Φ : List Constraint) :
    guards n Φ = n + (inputs n Φ).length + (addSlotList Φ).length := by
  rw [guards, addSlotList_length]

/-- The guard regions: variables, inputs, addition slots. -/
abbrev Idx (n : ℕ) (Φ : List Constraint) : Type :=
  Fin n ⊕ (Fin (inputs n Φ).length ⊕ Fin (addSlotList Φ).length)

theorem card_Idx (n : ℕ) (Φ : List Constraint) : Fintype.card (Idx n Φ) = guards n Φ := by
  simp only [Fintype.card_sum, Fintype.card_fin, guards_eq]
  omega

/-- The slot of the `j`-th addition gadget. -/
def addSlot (Φ : List Constraint) (j : Fin (addSlotList Φ).length) : ℕ := (addSlotList Φ)[j]

theorem addSlot_spec (j : Fin (addSlotList Φ).length) :
    addSlot Φ j < paramC Φ ∧ isAdd (gadAt Φ (addSlot Φ j)) = true := by
  have h := List.getElem_mem (l := addSlotList Φ) j.isLt
  simp only [addSlotList, List.mem_filter, List.mem_range] at h
  exact h

theorem isAdd_kind {c : Constraint} (h : isAdd c = true) : IsAdd (cKind c) := by
  cases c <;> simp_all [isAdd, cKind, IsAdd]

theorem addSlot_isAdd (j : Fin (addSlotList Φ).length) : IsAdd (cKind (gadAt Φ (addSlot Φ j))) :=
  isAdd_kind (addSlot_spec j).2

theorem addSlotList_nodup (Φ : List Constraint) : (addSlotList Φ).Nodup :=
  (List.nodup_range).filter _

theorem addSlot_inj {j j' : Fin (addSlotList Φ).length} (h : addSlot Φ j = addSlot Φ j') :
    j = j' :=
  Fin.ext ((addSlotList_nodup Φ).getElem_inj_iff.1 h)

theorem inputs_nodup (n : ℕ) (Φ : List Constraint) : (inputs n Φ).Nodup :=
  inputs_pw.imp fun {i j} h hij => by rw [hij] at h; linarith

theorem input_inj {j j' : Fin (inputs n Φ).length} (h : (inputs n Φ)[j] = (inputs n Φ)[j']) :
    j = j' :=
  Fin.ext ((inputs_nodup n Φ).getElem_inj_iff.1 h)

theorem input_mem (j : Fin (inputs n Φ).length) : (inputs n Φ)[j] ∈ inputs n Φ :=
  List.getElem_mem _

/-- The witness of a guard region: the tip of `W1`, resp. the aux tip. -/
def wit (n : ℕ) (Φ : List Constraint) : Idx n Φ → Point
  | .inl k => tipW1 n Φ (varA Φ k)
  | .inr (.inl j) => tipW1 n Φ (inputs n Φ)[j].b
  | .inr (.inr j) => auxTipPt n Φ (addSlot Φ j)

/-- The viewer set of a guard region: the slab, resp. the aux region. -/
def vset (n : ℕ) (Φ : List Constraint) : Idx n Φ → Set Point
  | .inl k => slab ((varA Φ k : ℚ) : ℝ)
  | .inr (.inl j) => slab ((inputs n Φ)[j].b : ℝ)
  | .inr (.inr j) => auxRegion (cKind (gadAt Φ (addSlot Φ j))) (slotG n Φ (addSlot Φ j))

theorem wit_mem (X : Idx n Φ) : wit n Φ X ∈ (SP n Φ).boundary := by
  rcases X with k | j | j
  · exact (var_tips k.isLt).1
  · obtain ⟨-, -, h, -⟩ := input_tips (input_mem j)
    exact h
  · exact (aux_viewer (addSlot_spec j).1 (addSlot_isAdd j)).1

theorem wit_vset (X : Idx n Φ) {p : Point} (hp : (SP n Φ).Sees p (wit n Φ X)) :
    p ∈ vset n Φ X := by
  rcases X with k | j | j
  · exact (var_tips k.isLt).2.2.2.1 p hp
  · obtain ⟨-, -, -, -, h, -⟩ := input_tips (input_mem j)
    exact h p hp
  · exact (aux_viewer (addSlot_spec j).1 (addSlot_isAdd j)).2 p hp

theorem vset_disj (X Y : Idx n Φ) (h : X ≠ Y) : Disjoint (vset n Φ X) (vset n Φ Y) := by
  rcases X with k | j | j <;> rcases Y with k' | j' | j'
  · exact slab_var_var (fun e => h (congrArg Sum.inl (Fin.ext e)))
  · exact slab_var_input k.isLt (input_mem j')
  · exact slab_var_aux k.isLt (addSlot_isAdd j')
  · exact (slab_var_input k'.isLt (input_mem j)).symm
  · exact slab_input_input (input_mem j) (input_mem j')
      (fun e => h (congrArg (fun x => Sum.inr (Sum.inl x)) (input_inj e)))
  · exact slab_input_aux (input_mem j) (addSlot_spec j').1 (addSlot_isAdd j')
  · exact (slab_var_aux k'.isLt (addSlot_isAdd j)).symm
  · exact (slab_input_aux (input_mem j') (addSlot_spec j).1 (addSlot_isAdd j)).symm
  · exact aux_aux (fun e => h (congrArg (fun x => Sum.inr (Sum.inr x)) (addSlot_inj e)))
      (addSlot_isAdd j) (addSlot_isAdd j')

/-! ### (a): the lower bound -/

/-- The boundary pigeonhole for Stade's polygon. -/
theorem pigeonhole (G : Finset Point) (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) :
    Fintype.card (Idx n Φ) ≤ G.card ∧
      (G.card = Fintype.card (Idx n Φ) →
        ∃ γ : Idx n Φ → Point, (∀ X, γ X ∈ G ∧ γ X ∈ vset n Φ X ∧
            (SP n Φ).Sees (γ X) (wit n Φ X)) ∧
          Function.Injective γ ∧ (∀ q ∈ G, ∃ X, γ X = q) ∧
          (∀ X, ∀ w ∈ (SP n Φ).boundary,
            (∀ p ∈ (SP n Φ).filled, (SP n Φ).Sees p w → ∀ Y, Y ≠ X → p ∉ vset n Φ Y) →
            (∀ q ∈ G, (SP n Φ).Sees q w → q = γ X) ∧ (SP n Φ).Sees (γ X) w)) :=
  boundaryGuard_viewerSets G hG (wit n Φ) wit_mem (vset n Φ) (fun X _ _ hp => wit_vset X hp)
    vset_disj

/-- **(a) Lower bound.** Every boundary guard set of Stade's polygon has at least `guards n Φ`
points. -/
theorem card_le_of_boundaryGuard' (n : ℕ) (Φ : List Constraint) (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    guards n Φ ≤ G.card := by
  rw [← card_Idx]
  exact (pigeonhole G hG).1

/-! ### The assignment of the guards (L4.4) -/

/-- The guard assignment of a boundary guard set of cardinality `guards n Φ`: every guard region
`X` gets the guard `γ X ∈ G` (bijectively), placed on its segment resp. in its aux region. -/
structure Assign (n : ℕ) (Φ : List Constraint) (G : Finset Point) where
  /-- The guard of each region. -/
  γ : Idx n Φ → Point
  /-- The guards are in `G`. -/
  mem : ∀ X, γ X ∈ G
  /-- Every point of `G` is a guard of some region. -/
  onto : ∀ q ∈ G, ∃ X, γ X = q
  /-- Variable guards lie on the variable segments. -/
  var : ∀ k : Fin n, (γ (.inl k)).1 = ((varA Φ k : ℚ) : ℝ) ∧ (paramH n Φ : ℝ) ≤ (γ (.inl k)).2 ∧
    (γ (.inl k)).2 ≤ (paramH n Φ : ℝ) + 3
  /-- A variable with a constraint `x = 1` has its guard at height `H + 1`. -/
  one : ∀ k : Fin n, hasOne Φ k = true → (γ (.inl k)).2 = (paramH n Φ : ℝ) + 1
  /-- Input guards lie on the input segments. -/
  inp : ∀ j : Fin (inputs n Φ).length, (γ (.inr (.inl j))).1 = ((inputs n Φ)[j].b : ℝ) ∧
    0 ≤ (γ (.inr (.inl j))).2 ∧ (γ (.inr (.inl j))).2 ≤ 6
  /-- Aux guards lie in their aux regions. -/
  aux : ∀ j : Fin (addSlotList Φ).length,
    γ (.inr (.inr j)) ∈ auxRegion (cKind (gadAt Φ (addSlot Φ j))) (slotG n Φ (addSlot Φ j))

/-- **Guard positions (§8.1, L4.4).** A boundary guard set with `guards n Φ` points has a guard
assignment. -/
theorem exists_assign (G : Finset Point) (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guards n Φ) : Nonempty (Assign n Φ G) := by
  obtain ⟨-, h⟩ := pigeonhole G hG
  obtain ⟨γ, hγ, -, honto, huniq⟩ := h (by rw [card_Idx]; exact hcard)
  -- a boundary point all of whose viewers lie in `vset X` is seen by `γ X`
  have hsees : ∀ X, ∀ w ∈ (SP n Φ).boundary, (∀ p, (SP n Φ).Sees p w → p ∈ vset n Φ X) →
      (SP n Φ).Sees (γ X) w := by
    intro X w hw hV
    refine (huniq X w hw fun p _ hp Y hYX hpY => ?_).2
    exact Set.disjoint_left.1 (vset_disj X Y (Ne.symm hYX)) (hV p hp) hpY
  refine ⟨⟨γ, fun X => (hγ X).1, honto, fun k => ?_, fun k hk => ?_, fun j => ?_, fun j => ?_⟩⟩
  · obtain ⟨-, hb2, hb3, -, hv2, hv3, hpos⟩ := var_tips (Φ := Φ) k.isLt
    exact hpos _ (hγ (.inl k)).2.2 (hsees (.inl k) _ hb2 fun p hp => hv2 p hp)
      (hsees (.inl k) _ hb3 fun p hp => hv3 p hp)
  · obtain ⟨-, hb2, -, -, hv2, -, -⟩ := var_tips (Φ := Φ) k.isLt
    obtain ⟨hb4, hb5, hv4, hv5, hpos⟩ := var_tips_one (Φ := Φ) k.isLt hk
    exact (hpos _ (hγ (.inl k)).2.2 (hsees (.inl k) _ hb2 fun p hp => hv2 p hp)
      (hsees (.inl k) _ hb4 fun p hp => hv4 p hp) (hsees (.inl k) _ hb5 fun p hp => hv5 p hp)).2
  · obtain ⟨w2, hb2, -, hb3, -, hv2, hv3, hpos⟩ := input_tips (input_mem j)
    exact hpos _ (hγ (.inr (.inl j))).2.2 (hsees (.inr (.inl j)) _ hb2 fun p hp => hv2 p hp)
      (hsees (.inr (.inl j)) _ hb3 fun p hp => hv3 p hp)
  · exact (hγ (.inr (.inr j))).2.1

/-- Every boundary point is seen by some assigned guard. -/
theorem Assign.cover {G : Finset Point} (A : Assign n Φ G)
    (hG : (SP n Φ).IsBoundaryGuardSet (G : Set Point)) {s : Point}
    (hs : s ∈ (SP n Φ).boundary) : ∃ X, (SP n Φ).Sees (A.γ X) s := by
  obtain ⟨q, hq, hqs⟩ := hG.2 s hs
  obtain ⟨X, rfl⟩ := A.onto q hq
  exact ⟨X, hqs⟩

end ArtGallery.Stade

end
