module

public import ArtGallery.Vis.Pinning
public import ArtGallery.Vis.Rooms

/-!
# Counting for boundary guard sets; global bounds of the region (proof plan L4.3, L2.1, L4.2)

**Boundary pigeonhole (L4.3).**  The counting arguments of `Vis/Pinning.lean` are stated for guard
sets; here they are proved for any finite set `G` of points of the region that sees every point of
a *target set* `T` (`Covers P G T`), and specialised to boundary guard sets (`T = P.boundary`) and
guard sets (`T = P.filled`).  Witnesses `m X` (`X : ι`, a finite type) are points of `T` no two of
which are seen from a common point of the region.
* `card_le_of_covers` / `card_le_of_boundaryGuardSet`: `|ι| ≤ |G|`;
* `assignment_of_covers` / `boundaryGuard_assignment`: if `|G| = |ι|` there is a bijection
  `γ : ι → G` with `γ X` seeing `m X`; `γ X` is the only guard seeing `m X`, and the only guard
  seeing any target point `w` that is not seen together with any other witness;
* `pinned_of_covers`: the two-stage pinning argument of `Vis.pinned_of_card_eq` for covering sets;
* `disj_of_viewerSets`: the disjointness hypothesis from pairwise disjoint viewer sets `V X`.

**Global bounds.**  `filled_linear_ge` (and the coordinate versions `filled_fst_ge`, …): if every
vertex satisfies a linear inequality `c ≤ α x + β y` then so does every point of the region (a ray
in the direction `−(α, β)` avoids the boundary).  This gives `filled ⊆ strip` (L4.2).

**Orientation (L2.1).**  `interiorLeft_of_left_edge` (and the right/top/bottom versions): a simple
polygon with an extreme edge traversed in the counter-clockwise direction has its interior to the
left of every edge (from `Polygon.interiorLeft_of_supporting_edge`).
-/

@[expose] public section

namespace ArtGallery.Stade

open Set

variable {P : Polygon}

/-! ### Covering sets -/

/-- `G` covers `T`: the points of `G` lie in the region and every point of `T` is seen by a point
of `G`. -/
def Covers (P : Polygon) (G : Set Point) (T : Set Point) : Prop :=
  G ⊆ P.filled ∧ ∀ p ∈ T, ∃ g ∈ G, P.Sees g p

/-- A boundary guard set covers the boundary. -/
theorem covers_of_boundaryGuardSet {G : Set Point} (hG : P.IsBoundaryGuardSet G) :
    Covers P G P.boundary := hG

/-- A guard set covers the region. -/
theorem covers_of_guardSet {G : Set Point} (hG : P.IsGuardSet G) : Covers P G P.filled := hG

/-- A guard set guards the boundary. -/
theorem isBoundaryGuardSet_of_isGuardSet {G : Set Point} (hG : P.IsGuardSet G) :
    P.IsBoundaryGuardSet G :=
  ⟨hG.1, fun p hp => hG.2 p (Polygon.boundary_subset_filled P hp)⟩

section Pigeonhole

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The disjointness hypothesis from pairwise disjoint viewer sets. -/
theorem disj_of_viewerSets (m : ι → Point) (V : ι → Set Point)
    (hV : ∀ X, ∀ p ∈ P.filled, P.Sees p (m X) → p ∈ V X)
    (hVd : ∀ X Y, X ≠ Y → Disjoint (V X) (V Y)) :
    ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y) := fun X Y hXY p hp h1 h2 =>
  Set.disjoint_left.1 (hVd X Y hXY) (hV X p hp h1) (hV Y p hp h2)

/-- **Lower bound.** A finite set covering `T` has at least as many points as there are
witnesses in `T` with pairwise disjoint viewer sets. -/
theorem card_le_of_covers (G : Finset Point) {T : Set Point} (hG : Covers P (G : Set Point) T)
    (m : ι → Point) (hm : ∀ X, m X ∈ T)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y)) :
    Fintype.card ι ≤ G.card := by
  classical
  choose g hgG hgs using fun X => hG.2 (m X) (hm X)
  have hinj : Set.InjOn g (Finset.univ : Finset ι) := by
    intro X _ Y _ hXY
    by_contra hne
    exact hdisj X Y hne (g X) (hG.1 (hgG X)) (hgs X) (hXY ▸ hgs Y)
  have := Finset.card_le_card_of_injOn g (fun X _ => hgG X) hinj
  simpa using this

/-- **Exact count: the assignment.** If a set `G` covering `T` has exactly as many points as
there are witnesses, the guards are assigned bijectively to the witnesses: `γ X ∈ G` sees `m X`,
`γ` is injective and onto `G`, `γ X` is the only point of `G` seeing `m X`, and `γ X` is the only
point of `G` seeing a target point `w` that is seen with no other witness (and it does see `w`). -/
theorem assignment_of_covers (G : Finset Point) {T : Set Point}
    (hG : Covers P (G : Set Point) T) (m : ι → Point) (hm : ∀ X, m X ∈ T)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) :
    ∃ γ : ι → Point, (∀ X, γ X ∈ G ∧ P.Sees (γ X) (m X)) ∧ Function.Injective γ ∧
      (∀ q ∈ G, ∃ X, γ X = q) ∧ (∀ X, ∀ q ∈ G, P.Sees q (m X) → q = γ X) ∧
      (∀ X, ∀ w ∈ T, (∀ Y, Y ≠ X → ∀ p ∈ P.filled, P.Sees p (m Y) → ¬ P.Sees p w) →
        (∀ q ∈ G, P.Sees q w → q = γ X) ∧ P.Sees (γ X) w) := by
  classical
  choose g hgG hgs using fun X => hG.2 (m X) (hm X)
  have hinj : Function.Injective g := by
    intro X Y hXY
    by_contra hne
    exact hdisj X Y hne (g X) (hG.1 (hgG X)) (hgs X) (hXY ▸ hgs Y)
  have hsub : Finset.univ.image g ⊆ G := by
    intro q hq
    obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hq
    exact hgG X
  have heq : Finset.univ.image g = G := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective _ hinj, hcard, Finset.card_univ]
  have honto : ∀ q ∈ G, ∃ X, g X = q := by
    intro q hq
    rw [← heq] at hq
    obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨X, rfl⟩
  have honly : ∀ X, ∀ w, (∀ Y, Y ≠ X → ∀ p ∈ P.filled, P.Sees p (m Y) → ¬ P.Sees p w) →
      ∀ q ∈ G, P.Sees q w → q = g X := by
    intro X w hw q hq hqw
    obtain ⟨Y, rfl⟩ := honto q hq
    by_cases hYX : Y = X
    · rw [hYX]
    · exact absurd hqw (hw Y hYX (g Y) (hG.1 (hgG Y)) (hgs Y))
  refine ⟨g, fun X => ⟨hgG X, hgs X⟩, hinj, honto, fun X q hq hqX => ?_, fun X w hwT hw => ?_⟩
  · refine honly X (m X) (fun Y hYX p hp h1 h2 => hdisj Y X hYX p hp h1 h2) q hq hqX
  · refine ⟨honly X w hw, ?_⟩
    obtain ⟨q, hq, hqw⟩ := hG.2 w hwT
    rw [← honly X w hw q hq hqw]
    exact hqw

/-- **Pinning for covering sets.** The two-stage argument of `Polygon.pinned_of_card_eq`, for a
set `G` covering a target set `T` containing the witnesses `m X` and the witness sets `W X`. -/
theorem pinned_of_covers (G : Finset Point) {T : Set Point} (hG : Covers P (G : Set Point) T)
    (m : ι → Point) (hm : ∀ X, m X ∈ T)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (W : ι → Set Point) (hW : ∀ X, W X ⊆ T)
    (Spot : ι → Set Point) (hSpot : ∀ X, ∀ p ∈ P.filled, (∀ w ∈ W X, P.Sees p w) → p ∈ Spot X)
    (r : ι → ι → Prop) (hr : WellFounded r)
    (hearly : ∀ X Y, Y ≠ X → r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, p ∈ Spot Y →
      P.Sees p (m Y) → ¬ P.Sees p w)
    (hlate : ∀ X Y, Y ≠ X → ¬ r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, P.Sees p (m Y) →
      ¬ P.Sees p w) :
    ∀ X, ∀ q ∈ G, P.Sees q (m X) → q ∈ Spot X := by
  obtain ⟨γ, hγ, -, honto, huniq, -⟩ := assignment_of_covers G hG m hm hdisj hcard
  intro X
  induction X using hr.induction with
  | _ X ih =>
    intro q hq hqX
    refine hSpot X q (hG.1 hq) fun w hw => ?_
    obtain ⟨q', hq', hq'w⟩ := hG.2 w (hW X hw)
    obtain ⟨Y, rfl⟩ := honto q' hq'
    by_cases hYX : Y = X
    · subst hYX
      rw [huniq Y q hq hqX]
      exact hq'w
    · by_cases hrYX : r Y X
      · exact absurd hq'w (hearly X Y hYX hrYX w hw (γ Y) (hG.1 hq')
          (ih Y hrYX (γ Y) hq' (hγ Y).2) (hγ Y).2)
      · exact absurd hq'w (hlate X Y hYX hrYX w hw (γ Y) (hG.1 hq') (hγ Y).2)

/-- **Boundary pigeonhole, lower bound (L4.3).** A boundary guard set has at least as many
points as there are boundary witnesses with pairwise disjoint viewer sets. -/
theorem card_le_of_boundaryGuardSet (G : Finset Point)
    (hG : P.IsBoundaryGuardSet (G : Set Point)) (m : ι → Point) (hm : ∀ X, m X ∈ P.boundary)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y)) :
    Fintype.card ι ≤ G.card :=
  card_le_of_covers G hG m hm hdisj

/-- **Boundary pigeonhole, exact count (L4.3).** For a boundary guard set with exactly as many
points as boundary witnesses (pairwise disjoint viewer sets), the guards are assigned bijectively
to the witnesses (`γ`), `γ X` is the only guard seeing `m X`, and for every boundary point `w`
not seen together with any other witness, `γ X` sees `w` and is the only guard seeing it. -/
theorem boundaryGuard_assignment (G : Finset Point) (hG : P.IsBoundaryGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.boundary)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) :
    ∃ γ : ι → Point, (∀ X, γ X ∈ G ∧ P.Sees (γ X) (m X)) ∧ Function.Injective γ ∧
      (∀ q ∈ G, ∃ X, γ X = q) ∧ (∀ X, ∀ q ∈ G, P.Sees q (m X) → q = γ X) ∧
      (∀ X, ∀ w ∈ P.boundary, (∀ Y, Y ≠ X → ∀ p ∈ P.filled, P.Sees p (m Y) → ¬ P.Sees p w) →
        (∀ q ∈ G, P.Sees q w → q = γ X) ∧ P.Sees (γ X) w) :=
  assignment_of_covers G hG m hm hdisj hcard

/-- **Boundary pigeonhole with viewer sets (L4.3, as in the plan).** Let `m X` be boundary points
and `V X` pairwise disjoint sets containing every point of the region that sees `m X`.  Then every
boundary guard set has at least `|ι|` points; if it has exactly `|ι|`, there is a bijection
`γ : ι → G` with `γ X ∈ V X` seeing `m X`, and every boundary point `w` all of whose viewers lie
outside `⋃_{Y ≠ X} V Y` is seen by `γ X` and by no other guard. -/
theorem boundaryGuard_viewerSets (G : Finset Point) (hG : P.IsBoundaryGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.boundary) (V : ι → Set Point)
    (hV : ∀ X, ∀ p ∈ P.filled, P.Sees p (m X) → p ∈ V X)
    (hVd : ∀ X Y, X ≠ Y → Disjoint (V X) (V Y)) :
    Fintype.card ι ≤ G.card ∧
      (G.card = Fintype.card ι →
        ∃ γ : ι → Point, (∀ X, γ X ∈ G ∧ γ X ∈ V X ∧ P.Sees (γ X) (m X)) ∧
          Function.Injective γ ∧ (∀ q ∈ G, ∃ X, γ X = q) ∧
          (∀ X, ∀ w ∈ P.boundary, (∀ p ∈ P.filled, P.Sees p w → ∀ Y, Y ≠ X → p ∉ V Y) →
            (∀ q ∈ G, P.Sees q w → q = γ X) ∧ P.Sees (γ X) w)) := by
  have hdisj := disj_of_viewerSets m V hV hVd
  refine ⟨card_le_of_boundaryGuardSet G hG m hm hdisj, fun hcard => ?_⟩
  obtain ⟨γ, hγ, hinj, honto, -, hw⟩ := boundaryGuard_assignment G hG m hm hdisj hcard
  refine ⟨γ, fun X => ⟨(hγ X).1, hV X _ (hG.1 (hγ X).1) (hγ X).2, (hγ X).2⟩, hinj, honto,
    fun X w hwb hwV => hw X w hwb fun Y hYX p hp h1 h2 => hwV p hp h2 Y hYX (hV Y p hp h1)⟩

end Pigeonhole

/-! ### Global bounds of the region -/

/-- **Linear bounds.** If every vertex satisfies `c ≤ α x + β y` (with `(α, β) ≠ 0`), so does
every point of the region. -/
theorem filled_linear_ge (P : Polygon) {α β c : ℝ} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (h : ∀ j < P.n, c ≤ α * (P.vtx j).1 + β * (P.vtx j).2) :
    ∀ x ∈ P.filled, c ≤ α * x.1 + β * x.2 := by
  have hbd : ∀ x ∈ P.boundary, c ≤ α * x.1 + β * x.2 := by
    rintro x ⟨j, hj, τ, hτ0, hτ1, rfl⟩
    have h1 := h j hj
    have h2 := h ((j + 1) % P.n) (Nat.mod_lt _ (by omega : 0 < P.n))
    simp only
    nlinarith [mul_nonneg hτ0 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hτ1) (sub_nonneg.2 h1)]
  intro x hx
  by_contra hlt
  push Not at hlt
  have hxb : x ∉ P.boundary := fun hb => absurd (hbd x hb) (not_le.2 hlt)
  have hd : ((-α, -β) : Point) ≠ 0 := by
    intro h0
    have e1 : -α = 0 := congrArg Prod.fst h0
    have e2 : -β = 0 := congrArg Prod.snd h0
    rcases hαβ with h' | h'
    · exact h' (by linarith)
    · exact h' (by linarith)
  have hsq : 0 < α ^ 2 + β ^ 2 := by
    rcases hαβ with h' | h'
    · have := pow_pos (abs_pos.2 h') 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h') 2; rw [sq_abs] at this; positivity
  refine Jordan.not_isBoundedSet_connectedComponentIn_of_ray P hd ?_
    ((Jordan.mem_filled_iff_bounded P hxb).1 hx)
  rintro _ ⟨s, hs, rfl⟩ hp
  have := hbd _ hp
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this
  nlinarith [mul_nonneg (mem_Ici.1 hs) hsq.le]

/-- Every point of the region has abscissa `≥ x₀` if every vertex has. -/
theorem filled_fst_ge (P : Polygon) {x₀ : ℝ} (h : ∀ j < P.n, x₀ ≤ (P.vtx j).1) :
    ∀ x ∈ P.filled, x₀ ≤ x.1 := by
  intro x hx
  have := filled_linear_ge P (α := 1) (β := 0) (c := x₀) (Or.inl one_ne_zero)
    (fun j hj => by simpa using h j hj) x hx
  simpa using this

/-- Every point of the region has abscissa `≤ x₁` if every vertex has. -/
theorem filled_fst_le (P : Polygon) {x₁ : ℝ} (h : ∀ j < P.n, (P.vtx j).1 ≤ x₁) :
    ∀ x ∈ P.filled, x.1 ≤ x₁ := by
  intro x hx
  have := filled_linear_ge P (α := -1) (β := 0) (c := -x₁) (Or.inl (by norm_num))
    (fun j hj => by have := h j hj; simp; linarith) x hx
  simp at this; linarith

/-- Every point of the region has ordinate `≥ y₀` if every vertex has. -/
theorem filled_snd_ge (P : Polygon) {y₀ : ℝ} (h : ∀ j < P.n, y₀ ≤ (P.vtx j).2) :
    ∀ x ∈ P.filled, y₀ ≤ x.2 := by
  intro x hx
  have := filled_linear_ge P (α := 0) (β := 1) (c := y₀) (Or.inr one_ne_zero)
    (fun j hj => by simpa using h j hj) x hx
  simpa using this

/-- Every point of the region has ordinate `≤ y₁` if every vertex has. -/
theorem filled_snd_le (P : Polygon) {y₁ : ℝ} (h : ∀ j < P.n, (P.vtx j).2 ≤ y₁) :
    ∀ x ∈ P.filled, x.2 ≤ y₁ := by
  intro x hx
  have := filled_linear_ge P (α := 0) (β := -1) (c := -y₁) (Or.inr (by norm_num))
    (fun j hj => by have := h j hj; simp; linarith) x hx
  simp at this; linarith

/-- **Strip bound (L4.2).** The region lies in the horizontal strip spanned by the vertices. -/
theorem filled_subset_strip (P : Polygon) {y₀ y₁ : ℝ} (h₀ : ∀ j < P.n, y₀ ≤ (P.vtx j).2)
    (h₁ : ∀ j < P.n, (P.vtx j).2 ≤ y₁) : P.filled ⊆ {x | y₀ ≤ x.2 ∧ x.2 ≤ y₁} :=
  fun x hx => ⟨filled_snd_ge P h₀ x hx, filled_snd_le P h₁ x hx⟩

/-! ### Orientation from an extreme edge (L2.1) -/

/-- A simple polygon whose vertices all have abscissa `≥ x₀`, with an edge on the line `x = x₀`
traversed downwards, has its interior to the left of every edge. -/
theorem interiorLeft_of_left_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {x₀ : ℝ}
    (hext : ∀ j < P.n, x₀ ≤ (P.vtx j).1) (hu : (P.vtx i).1 = x₀)
    (hv : (P.vtx ((i + 1) % P.n)).1 = x₀) (hdir : (P.vtx ((i + 1) % P.n)).2 < (P.vtx i).2) :
    P.InteriorLeft := by
  refine Polygon.interiorLeft_of_supporting_edge hP hi fun j hj => ?_
  unfold det
  rw [hu, hv]
  have := hext j hj
  nlinarith

/-- A simple polygon whose vertices all have abscissa `≤ x₁`, with an edge on the line `x = x₁`
traversed upwards, has its interior to the left of every edge. -/
theorem interiorLeft_of_right_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {x₁ : ℝ}
    (hext : ∀ j < P.n, (P.vtx j).1 ≤ x₁) (hu : (P.vtx i).1 = x₁)
    (hv : (P.vtx ((i + 1) % P.n)).1 = x₁) (hdir : (P.vtx i).2 < (P.vtx ((i + 1) % P.n)).2) :
    P.InteriorLeft := by
  refine Polygon.interiorLeft_of_supporting_edge hP hi fun j hj => ?_
  unfold det
  rw [hu, hv]
  have := hext j hj
  nlinarith

/-- A simple polygon whose vertices all have ordinate `≤ y₁`, with an edge on the line `y = y₁`
traversed from right to left, has its interior to the left of every edge. -/
theorem interiorLeft_of_top_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {y₁ : ℝ}
    (hext : ∀ j < P.n, (P.vtx j).2 ≤ y₁) (hu : (P.vtx i).2 = y₁)
    (hv : (P.vtx ((i + 1) % P.n)).2 = y₁) (hdir : (P.vtx ((i + 1) % P.n)).1 < (P.vtx i).1) :
    P.InteriorLeft := by
  refine Polygon.interiorLeft_of_supporting_edge hP hi fun j hj => ?_
  unfold det
  rw [hu, hv]
  have := hext j hj
  nlinarith

/-- `interiorLeft_of_bottom_edge`, restated for convenience: vertices with ordinate `≥ y₀` and
an edge on `y = y₀` traversed from left to right. -/
theorem interiorLeft_of_bottom_edge' (hP : P.Simple) {i : ℕ} (hi : i < P.n) {y₀ : ℝ}
    (hext : ∀ j < P.n, y₀ ≤ (P.vtx j).2) (hu : (P.vtx i).2 = y₀)
    (hv : (P.vtx ((i + 1) % P.n)).2 = y₀) (hdir : (P.vtx i).1 < (P.vtx ((i + 1) % P.n)).1) :
    P.InteriorLeft :=
  Polygon.interiorLeft_of_bottom_edge hP hi hext hu hv hdir

end ArtGallery.Stade

end
