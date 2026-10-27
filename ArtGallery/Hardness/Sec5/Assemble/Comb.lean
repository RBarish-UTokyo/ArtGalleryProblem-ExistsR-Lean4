module

public import ArtGallery.Hardness.Sec5.Assemble.Glue

/-!
# Section 5: units hanging from a vertical line (comb lemma)

The right units of the construction hang from the line `x = S` (08 §4): unit `m` is a simple chain
from `(S, H_m)` to `(S, H_m + 2ρ)`, strictly right of the line except at its two ends
(`UnitFeature`).  Joined by the vertical segments of the line, units ordered by height with
pairwise disjoint chains form a simple chain (`comb_vertical`).  This is Stade's `comb_floor`
(`ArtGallery/Stade/Chains.lean`) turned by a quarter rotation (`rotCW : (x, y) ↦ (y, −x)`).
The left side is the mirror image of a comb of the same form (see `Assemble/Simple.lean`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-- A unit chain hanging right of the line `x = S` at heights `H`, `H + 2ρ`. -/
structure UnitFeature (S H ρ : ℝ) (f : List Point) : Prop where
  /-- At least two vertices. -/
  len : 2 ≤ f.length
  /-- A simple chain. -/
  simple : ChainSimple f
  /-- It starts at `(S, H)` (the corridor corner `c0`). -/
  fst : fstPt f = (S, H)
  /-- It ends at `(S, H + 2ρ)` (the corridor corner `d0`). -/
  lst : lstPt f = (S, H + 2 * ρ)
  /-- Strictly right of `x = S` except at the two ends. -/
  right : ∀ p ∈ chainSet f, S < p.1 ∨ p = fstPt f ∨ p = lstPt f
  /-- The unit box. -/
  box : ∀ p ∈ chainSet f, S ≤ p.1 ∧ p.1 ≤ S + 4 ∧ H - 1 - 1 / 100 ≤ p.2 ∧ p.2 ≤ H + 3 / 2

/-- The quarter rotation `(x, y) ↦ (y, −x)`. -/
noncomputable def rotCWL : Point ≃ₗ[ℝ] Point where
  toFun p := (p.2, -p.1)
  invFun p := (-p.2, p.1)
  map_add' p q := by ext <;> simp; ring
  map_smul' s p := by ext <;> simp
  left_inv p := by simp
  right_inv p := by simp

/-- The quarter rotation as an affine equivalence. -/
noncomputable def rotCW : Point ≃ᵃ[ℝ] Point := rotCWL.toAffineEquiv

@[simp] theorem rotCW_apply (p : Point) : rotCW p = (p.2, -p.1) := rfl

theorem rotCW_symm_apply (p : Point) : rotCW.symm p = (-p.2, p.1) := by
  apply rotCW.injective
  rw [AffineEquiv.apply_symm_apply, rotCW_apply]
  ext <;> simp

/-- A feature hanging right of `x = X₀`, inside the horizontal strip `lo < y < hi`. -/
def VFeature (X₀ lo hi : ℝ) (f : List Point) : Prop :=
  2 ≤ f.length ∧ ChainSimple f ∧ (fstPt f).1 = X₀ ∧ (lstPt f).1 = X₀ ∧
    (fstPt f).2 < (lstPt f).2 ∧ (∀ p ∈ chainSet f, X₀ < p.1 ∨ p = fstPt f ∨ p = lstPt f) ∧
    (∀ p ∈ chainSet f, lo < p.2 ∧ p.2 < hi)

theorem ne_nil_of_two_le {f : List Point} (h : 2 ≤ f.length) : f ≠ [] := by
  intro e; rw [e] at h; simp at h

theorem VFeature.rot {X₀ lo hi : ℝ} {f : List Point} (h : VFeature X₀ lo hi f) :
    FloorFeature (-X₀) lo hi (f.map rotCW) := by
  obtain ⟨hlen, hcs, hf1, hl1, hfl, hr, hy⟩ := h
  have hne := ne_nil_of_two_le hlen
  have hfst : fstPt (f.map rotCW) = rotCW (fstPt f) := fstPt_map _ hne
  have hlst : lstPt (f.map rotCW) = rotCW (lstPt f) := lstPt_map _ hne
  refine ⟨by simpa using hlen, chainSimple_map rotCW hcs, by rw [hfst]; simp [hf1],
    by rw [hlst]; simp [hl1], by rw [hfst, hlst]; simpa using hfl, ?_, ?_⟩
  · intro p hp
    rw [chainSet_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hfst, hlst]
    rcases hr q hq with h | h | h
    · left; simp; linarith
    · right; left; rw [h]
    · right; right; rw [h]
  · intro p hp
    rw [chainSet_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simpa using hy q hq

/-- **Comb on a vertical line.**  Features hanging right of `x = X₀`, ordered by height and
pairwise disjoint, joined by the segments of the line from `(X₀, s)` to `(X₀, hi)`, form a simple
chain; it lies on the line or on the features. -/
theorem comb_vertical {X₀ lo hi s : ℝ} (fs : List (List Point)) (hs : s < hi)
    (hF : ∀ f ∈ fs, VFeature X₀ lo hi f) (hfst : ∀ f ∈ fs, s < (fstPt f).2)
    (hpw : fs.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).2 < (fstPt g).2)) :
    ChainSimple ((X₀, s) :: fs.flatten ++ [(X₀, hi)]) ∧
      chainSet ((X₀, s) :: fs.flatten ++ [(X₀, hi)]) ⊆
        {p | p.1 = X₀ ∧ s ≤ p.2 ∧ p.2 ≤ hi} ∪ {p | ∃ f ∈ fs, p ∈ chainSet f} := by
  have hF' : ∀ f ∈ fs.map (List.map rotCW), FloorFeature (-X₀) lo hi f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (hF g hg).rot
  have hfst' : ∀ f ∈ fs.map (List.map rotCW), s < (fstPt f).1 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    rw [fstPt_map _ (ne_nil_of_two_le (hF g hg).1)]
    simpa using hfst g hg
  have hpw' : (fs.map (List.map rotCW)).Pairwise
      (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1) := by
    rw [List.pairwise_map]
    refine hpw.imp_of_mem (fun {f g} hf hg hfg => ⟨?_, ?_⟩)
    · rw [chainSet_map, chainSet_map]
      exact (Set.disjoint_image_iff rotCW.injective).2 hfg.1
    · rw [lstPt_map _ (ne_nil_of_two_le (hF f hf).1), fstPt_map _ (ne_nil_of_two_le (hF g hg).1)]
      simpa using hfg.2
  obtain ⟨h1, h2⟩ := comb_floor _ s hs hF' hfst' hpw'
  have e : (s, -X₀) :: (fs.map (List.map rotCW)).flatten ++ [(hi, -X₀)] =
      ((X₀, s) :: fs.flatten ++ [(X₀, hi)]).map rotCW := by
    simp [List.map_flatten]
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · have := chainSimple_map rotCW.symm h1
    rwa [List.map_map, show (⇑rotCW.symm ∘ ⇑rotCW) = id from funext rotCW.symm_apply_apply,
      List.map_id] at this
  · intro p hp
    have hp' : rotCW p ∈ chainSet (((X₀, s) :: fs.flatten ++ [(X₀, hi)]).map rotCW) := by
      rw [chainSet_map]; exact ⟨p, hp, rfl⟩
    rcases h2 hp' with ⟨hy, hx1, hx2⟩ | ⟨f, hf, hpf⟩
    · left
      simp at hy hx1 hx2
      exact ⟨by linarith, hx1, hx2⟩
    · right
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      rw [chainSet_map] at hpf
      obtain ⟨q, hq, hqp⟩ := hpf
      exact ⟨g, hg, by rw [← rotCW.injective hqp]; exact hq⟩

/-- **The units of one side** (`fs[j]` hanging at height `S + 3j + 1`) joined along `x = S` from
`(S, S)` to `(S, top)`: a simple chain right of `x = S`, below `y = top`, reaching `y = top` only at
`(S, top)`. -/
theorem comb_units {S ρ top : ℝ} (fs : List (List Point)) (hρ : 0 < ρ) (hρ1 : ρ < 1 / 100)
    (hF : ∀ j (hj : j < fs.length), UnitFeature S (S + 3 * j + 1) ρ fs[j])
    (htop : S + 3 * fs.length ≤ top) (hst : S < top) :
    ChainSimple ((S, S) :: fs.flatten ++ [(S, top)]) ∧
      (∀ p ∈ chainSet ((S, S) :: fs.flatten ++ [(S, top)]),
        S ≤ p.1 ∧ p.2 ≤ top ∧ (top ≤ p.2 → p = (S, top))) ∧
      (∀ p ∈ chainSet ((S, S) :: fs.flatten ++ [(S, top)]), p.1 = S ∨ ∃ f ∈ fs, p ∈ chainSet f) := by
  have hV : ∀ f ∈ fs, VFeature S (S - 1) top f ∧ ∃ j : ℕ, j < fs.length ∧
      UnitFeature S (S + 3 * j + 1) ρ f := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have u := hF j hj
    have hjl : (j : ℝ) + 1 ≤ fs.length := by exact_mod_cast hj
    refine ⟨⟨u.len, u.simple, by rw [u.fst], by rw [u.lst], by rw [u.fst, u.lst]; simp; linarith,
      u.right, fun p hp => ?_⟩, j, hj, u⟩
    obtain ⟨-, -, b3, b4⟩ := u.box p hp
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor <;> linarith
  have hlen : (0 : ℝ) ≤ fs.length := Nat.cast_nonneg _
  obtain ⟨h1, h2⟩ := comb_vertical (X₀ := S) (lo := S - 1) (hi := top) (s := S) fs
    hst
    (fun f hf => (hV f hf).1)
    (fun f hf => by
      obtain ⟨-, j, -, u⟩ := hV f hf
      rw [u.fst]; simp; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    (by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have ui := hF i hi
      have uj := hF j hj
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      refine ⟨Set.disjoint_left.2 fun p hp1 hp2 => ?_, ?_⟩
      · have a := (ui.box p hp1).2.2.2
        have b := (uj.box p hp2).2.2.1
        linarith
      · rw [ui.lst, uj.fst]; simp; linarith)
  refine ⟨h1, fun p hp => ?_, fun p hp => ?_⟩
  swap
  · rcases h2 hp with ⟨hx, -, -⟩ | ⟨f, hf, hpf⟩
    · exact Or.inl hx
    · exact Or.inr ⟨f, hf, hpf⟩
  rcases h2 hp with ⟨hx, hy1, hy2⟩ | ⟨f, hf, hpf⟩
  · exact ⟨hx.ge, hy2, fun h => Prod.ext hx (le_antisymm hy2 h)⟩
  · obtain ⟨-, j, hj, u⟩ := hV f hf
    obtain ⟨b1, -, -, b4⟩ := u.box p hpf
    have hjl : (j : ℝ) + 1 ≤ fs.length := by exact_mod_cast hj
    refine ⟨b1, by linarith, fun h => by linarith⟩

end ArtGallery.Sec5

end
