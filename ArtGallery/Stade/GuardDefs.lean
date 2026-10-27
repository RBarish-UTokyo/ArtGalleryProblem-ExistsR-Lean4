module

public import ArtGallery.Stade.GuardTools
public import ArtGallery.Stade.Simple
public import ArtGallery.Stade.AdditionAlg

/-!
# The canonical guard set of a solution (construction.md §8, proof plan §9)

For a solution `v` of `Φ`, the canonical guards are
* the **variable guards** `varGuard k = (a_k, H + 2 v_k − 1)` for `k < n`;
* the **input guards** `inGuard i = (b_i, 4 v_{var i} − 2)` for every input segment `i`
  (the input copies the value of its variable);
* the **aux guards** `auxGuard c = I(v_x, v_y)` for every addition slot `c`: the canonical aux
  point of construction.md §7.1 (`alI g_c`, `agI g_c` of `Stade/AdditionAlg.lean`).

`canonList n Φ v` lists them (variables, inputs, aux guards); its length is `guards n Φ`
(`canonList_length`).  We also define the real parameters `hH`, the hall `hallPoly` (the rectangle
`[x_L, x_R] × [−1, 2H]`) and its membership lemma.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

/-! ### Guards -/

/-- The guard of variable `k`: `(a_k, H + 2 v_k − 1)`. -/
noncomputable def varGuard (n : ℕ) (Φ : List Constraint) (v : ℕ → ℝ) (k : ℕ) : Point :=
  ((varA Φ k : ℝ), (paramH n Φ : ℝ) + 2 * v k - 1)

/-- The guard of an input segment: `(b, 4 v_var − 2)`. -/
noncomputable def inGuard (v : ℕ → ℝ) (i : InputSeg) : Point := ((i.b : ℝ), 4 * v i.var - 2)

/-- The `j`-th variable of the `c`-th gadget constraint. -/
def gadVar (Φ : List Constraint) (c j : ℕ) : ℕ := (cVars (gadAt Φ c)).getD j 0

/-- The canonical aux point of a gadget of kind `k` in a slot with origin `G` (`(0, 0)` for the
inversion gadgets, which have no aux guard). -/
noncomputable def auxPt (k : TKind) (G vx vy : ℝ) : Point :=
  match k with
  | .addLe => alI G vx vy
  | .addGe => agI G vx vy
  | _ => (0, 0)

/-- The aux guard of slot `c`: the canonical aux point `I(v_x, v_y)`. -/
noncomputable def auxGuard (n : ℕ) (Φ : List Constraint) (v : ℕ → ℝ) (c : ℕ) : Point :=
  auxPt (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (v (gadVar Φ c 0)) (v (gadVar Φ c 1))

/-- The addition slots. -/
def addSlots (Φ : List Constraint) : List ℕ :=
  (List.range (paramC Φ)).filter (fun c => isAdd (gadAt Φ c))

/-- **The canonical guards** of a solution `v`, as a list: variables, inputs, aux guards. -/
noncomputable def canonList (n : ℕ) (Φ : List Constraint) (v : ℕ → ℝ) : List Point :=
  (List.range n).map (varGuard n Φ v) ++ (inputs n Φ).map (inGuard v) ++
    (addSlots Φ).map (auxGuard n Φ v)

/-- **The canonical guard set** of a solution `v`. -/
noncomputable def canonGuards (n : ℕ) (Φ : List Constraint) (v : ℕ → ℝ) : Finset Point :=
  (canonList n Φ v).toFinset

/-! ### Length -/

/-- A list is the map of `getD` over the range of its length. -/
theorem map_getD_range {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Filtering the indices of a list by a predicate of the entries counts the entries satisfying
it. -/
theorem length_filter_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter (fun i => p (l.getD i d))).length = (l.filter p).length := by
  conv_rhs => rw [← map_getD_range l d]
  rw [List.filter_map, List.length_map]
  rfl

/-- The number of canonical guards is `guards n Φ`. -/
theorem canonList_length (n : ℕ) (Φ : List Constraint) (v : ℕ → ℝ) :
    (canonList n Φ v).length = guards n Φ := by
  simp only [canonList, List.length_append, List.length_map, List.length_range, guards, addSlots]
  congr 1
  exact length_filter_range_getD (gad Φ) (.one 0) isAdd

/-! ### Real parameters and the hall -/

/-- The height parameter `H` as a real number. -/
noncomputable abbrev hH (n : ℕ) (Φ : List Constraint) : ℝ := (paramH n Φ : ℝ)

/-- The hall `[x_L, x_R] × [−1, 2H]`, as a counter-clockwise quadrilateral. -/
noncomputable def hallPoly (n : ℕ) (Φ : List Constraint) : Polygon :=
  quad ((xL n Φ : ℝ), -1) ((xR n Φ : ℝ), -1) ((xR n Φ : ℝ), 2 * hH n Φ) ((xL n Φ : ℝ), 2 * hH n Φ)

/-- The left wall is left of the right wall. -/
theorem xL_lt_xR_real (n : ℕ) (Φ : List Constraint) : (xL n Φ : ℝ) < (xR n Φ : ℝ) := by
  exact_mod_cast xL_lt_xR n Φ

/-- `H ≥ 1000`, over `ℝ`. -/
theorem hH_ge (n : ℕ) (Φ : List Constraint) : (1000 : ℝ) ≤ hH n Φ := by
  have := paramH_ge n Φ
  unfold hH; exact_mod_cast this

/-- Membership in the hall. -/
theorem mem_hall {n : ℕ} {Φ : List Constraint} {p : Point} :
    p ∈ piece (hallPoly n Φ) ↔
      (xL n Φ : ℝ) ≤ p.1 ∧ p.1 ≤ (xR n Φ : ℝ) ∧ -1 ≤ p.2 ∧ p.2 ≤ 2 * hH n Φ := by
  have hx := xL_lt_xR_real n Φ
  have hH := hH_ge n Φ
  rw [hallPoly, mem_piece_quad]
  unfold det
  simp only
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The hall is a piece. -/
theorem hallPoly_isPiece (n : ℕ) (Φ : List Constraint) : IsPiece (hallPoly n Φ) := by
  have hx := xL_lt_xR_real n Φ
  have hH := hH_ge n Φ
  unfold hallPoly
  apply isPiece_quad <;> unfold det <;> simp only <;> nlinarith

end ArtGallery.Stade

end
