module

public import ArtGallery.Stade.Chains

/-!
# Robust simplicity checks for chains depending linearly on a parameter

The gadget templates of Stade's construction contain *needles* whose tips lie at depth `H`
below their base points, where `H ≥ 1000` is a parameter of the instance.  A template vertex is
therefore given as a triple `(x, y₀, d) : RPt` standing for the point `(x, y₀ − d·H)`
(`RPt.inst`), translated by the slot origin `ox`.

All orientation determinants and all differences of ordinates of such points are affine in `H`
(the abscissae do not depend on `H`), `α + β H`.  The Boolean test `rposB H₀ α β`
(`0 < α + β H₀` and `0 ≤ β`) guarantees `0 < α + β H` for every `H ≥ H₀`.  Replacing every sign
test of the simplicity check of `ArtGallery.Irrational.Checker` by this robust version gives
checks that are evaluated once by `decide` on the fixed template data and are sound for every
`H ≥ H₀` and every translation `ox`:

* `rChainB_sound`: the instantiated chain is `ChainSimple`;
* `rFloorFeatB_sound`: the instantiated chain is a `FloorFeature` of the line `y = y₀`.
-/

namespace ArtGallery.Stade.Chain

@[expose] public section

open ArtGallery.Geometry ArtGallery.Irrational Set

/-! ### Points depending on `H` -/

/-- A template vertex `(x, y₀, d)`, standing for the point `(x, y₀ − d·H)`. -/
abbrev RPt : Type := ℚ × ℚ × ℚ

/-- The rational point of a template vertex for the parameter `H`, translated by `ox`. -/
def RPt.inst (H ox : ℚ) (p : RPt) : ℚ × ℚ := (ox + p.1, p.2.1 - p.2.2 * H)

/-- The real points of a template chain. -/
def rpts (H ox : ℚ) (ch : List RPt) : List Point := ch.map (fun p => ratPoint (p.inst H ox))

/-- Robust positivity of `α + β H` for all `H ≥ H₀`. -/
def rposB (H₀ α β : ℚ) : Bool := decide (0 < α + β * H₀) && decide (0 ≤ β)

theorem rpos_sound {H₀ H α β : ℚ} (h : rposB H₀ α β = true) (hH : H₀ ≤ H) : 0 < α + β * H := by
  simp only [rposB, Bool.and_eq_true, decide_eq_true_eq] at h
  nlinarith [mul_nonneg h.2 (sub_nonneg.2 hH)]

/-- The constant part of the determinant of three template vertices. -/
def rdetA (a b c : RPt) : ℚ := (b.1 - a.1) * (c.2.1 - a.2.1) - (c.1 - a.1) * (b.2.1 - a.2.1)

/-- The coefficient of `H` in the determinant of three template vertices. -/
def rdetB (a b c : RPt) : ℚ := -(b.1 - a.1) * (c.2.2 - a.2.2) + (c.1 - a.1) * (b.2.2 - a.2.2)

theorem qdet_inst (H ox : ℚ) (a b c : RPt) :
    qdet (a.inst H ox) (b.inst H ox) (c.inst H ox) = rdetA a b c + rdetB a b c * H := by
  simp only [qdet, RPt.inst, rdetA, rdetB]; ring

/-- Robustly `a` lies strictly below `c`. -/
def rylt (H₀ : ℚ) (a c : RPt) : Bool := rposB H₀ (c.2.1 - a.2.1) (a.2.2 - c.2.2)

theorem rylt_sound {H₀ H ox : ℚ} {a c : RPt} (h : rylt H₀ a c = true) (hH : H₀ ≤ H) :
    (a.inst H ox).2 < (c.inst H ox).2 := by
  have := rpos_sound h hH
  simp only [RPt.inst]; linarith

/-- Robust strict positivity of the determinant. -/
def rdetPos (H₀ : ℚ) (a b c : RPt) : Bool := rposB H₀ (rdetA a b c) (rdetB a b c)

/-- Robust strict negativity of the determinant. -/
def rdetNeg (H₀ : ℚ) (a b c : RPt) : Bool := rposB H₀ (-rdetA a b c) (-rdetB a b c)

theorem rdetPos_sound {H₀ H ox : ℚ} {a b c : RPt} (h : rdetPos H₀ a b c = true) (hH : H₀ ≤ H) :
    0 < qdet (a.inst H ox) (b.inst H ox) (c.inst H ox) := by
  rw [qdet_inst]; exact rpos_sound h hH

theorem rdetNeg_sound {H₀ H ox : ℚ} {a b c : RPt} (h : rdetNeg H₀ a b c = true) (hH : H₀ ≤ H) :
    qdet (a.inst H ox) (b.inst H ox) (c.inst H ox) < 0 := by
  rw [qdet_inst]; have := rpos_sound h hH; linarith

/-- Robustly distinct points. -/
def rneB (H₀ : ℚ) (a b : RPt) : Bool := decide (a.1 ≠ b.1) || rylt H₀ a b || rylt H₀ b a

theorem rneB_sound {H₀ H ox : ℚ} {a b : RPt} (h : rneB H₀ a b = true) (hH : H₀ ≤ H) :
    a.inst H ox ≠ b.inst H ox := by
  simp only [rneB, Bool.or_eq_true, decide_eq_true_eq] at h
  intro he
  rcases h with (h | h) | h
  · apply h
    have := congrArg Prod.fst he
    simp only [RPt.inst] at this; linarith
  · have := rylt_sound (ox := ox) h hH; rw [he] at this; exact lt_irrefl _ this
  · have := rylt_sound (ox := ox) h hH; rw [he] at this; exact lt_irrefl _ this

/-- Robust separation of the segments `[a, b]` and `[c, d]` (the eight tests of
`Irrational.sepB`, each made robust). -/
def rsepB (H₀ : ℚ) (a b c d : RPt) : Bool :=
  decide (a.1 < c.1 ∧ a.1 < d.1 ∧ b.1 < c.1 ∧ b.1 < d.1) ||
  decide (c.1 < a.1 ∧ c.1 < b.1 ∧ d.1 < a.1 ∧ d.1 < b.1) ||
  (rylt H₀ a c && rylt H₀ a d && rylt H₀ b c && rylt H₀ b d) ||
  (rylt H₀ c a && rylt H₀ c b && rylt H₀ d a && rylt H₀ d b) ||
  (rdetPos H₀ a b c && rdetPos H₀ a b d) || (rdetNeg H₀ a b c && rdetNeg H₀ a b d) ||
  (rdetPos H₀ c d a && rdetPos H₀ c d b) || (rdetNeg H₀ c d a && rdetNeg H₀ c d b)

theorem rsepB_sound {H₀ H ox : ℚ} {a b c d : RPt} (h : rsepB H₀ a b c d = true) (hH : H₀ ≤ H) :
    sepB (a.inst H ox) (b.inst H ox) (c.inst H ox) (d.inst H ox) = true := by
  simp only [rsepB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [sepB, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))))
    simp only [RPt.inst, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))
    simp only [RPt.inst, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨rylt_sound h.1.1.1 hH, rylt_sound h.1.1.2 hH⟩,
      ⟨rylt_sound h.1.2 hH, rylt_sound h.2 hH⟩⟩
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨rylt_sound h.1.1.1 hH, rylt_sound h.1.1.2 hH⟩,
      ⟨rylt_sound h.1.2 hH, rylt_sound h.2 hH⟩⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rdetPos_sound h.1 hH, rdetPos_sound h.2 hH⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨rdetNeg_sound h.1 hH, rdetNeg_sound h.2 hH⟩))
  · exact Or.inl (Or.inr ⟨rdetPos_sound h.1 hH, rdetPos_sound h.2 hH⟩)
  · exact Or.inr ⟨rdetNeg_sound h.1 hH, rdetNeg_sound h.2 hH⟩

/-! ### Chains -/

/-- `f` holds for every edge of the chain. -/
def edgesAll (f : RPt → RPt → Bool) : List RPt → Bool
  | a :: b :: l => f a b && edgesAll f (b :: l)
  | _ => true

theorem edgesAll_sound {f : RPt → RPt → Bool} {H ox : ℚ} :
    ∀ {l : List RPt}, edgesAll f l = true → ∀ {x : Point}, x ∈ chainSet (rpts H ox l) →
      ∃ u v, f u v = true ∧ x ∈ ArtGallery.segment (ratPoint (u.inst H ox)) (ratPoint (v.inst H ox))
  | [], _, _, hx => by simp [rpts] at hx
  | [_], _, _, hx => by simp [rpts] at hx
  | a :: b :: l, h, x, hx => by
    simp only [edgesAll, Bool.and_eq_true] at h
    simp only [rpts, List.map_cons, chainSet_cons_cons, mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨a, b, h.1, hx⟩
    · exact edgesAll_sound h.2 (by simpa [rpts] using hx)

/-- The conditions on the first edge `[a, b]` of a chain `a, b, l…`: robustly non-collinear with
the next edge, robustly separated from all later edges. -/
def rFirstOK (H₀ : ℚ) (a b : RPt) : List RPt → Bool
  | [] => true
  | c :: l => (rdetPos H₀ a b c || rdetNeg H₀ a b c) && edgesAll (rsepB H₀ a b) (c :: l)

/-- The robust simplicity check of an open chain of template vertices. -/
def rChainB (H₀ : ℚ) : List RPt → Bool
  | a :: b :: l => rneB H₀ a b && rFirstOK H₀ a b l && rChainB H₀ (b :: l)
  | _ => true

theorem rChainB_sound {H₀ H ox : ℚ} (hH : H₀ ≤ H) :
    ∀ {l : List RPt}, rChainB H₀ l = true → ChainSimple (rpts H ox l)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    simp only [rChainB, Bool.and_eq_true] at h
    obtain ⟨⟨hne, hfirst⟩, hrest⟩ := h
    have ih := rChainB_sound (ox := ox) hH hrest
    simp only [rpts, List.map_cons] at ih ⊢
    refine ⟨fun e => rneB_sound hne hH (ratPoint_injective e), ?_, ih⟩
    cases l with
    | nil => simp
    | cons c l =>
      simp only [rFirstOK, Bool.and_eq_true, Bool.or_eq_true] at hfirst
      obtain ⟨hdet, hall⟩ := hfirst
      simp only [List.map_cons, chainSet_cons_cons]
      rintro x ⟨hx1, hx2 | hx2⟩
      · have hd : det (ratPoint (a.inst H ox)) (ratPoint (b.inst H ox))
            (ratPoint (c.inst H ox)) ≠ 0 := by
          rw [det_ratPoint]
          rcases hdet with hd | hd
          · exact_mod_cast (rdetPos_sound hd hH).ne'
          · exact_mod_cast (rdetNeg_sound hd hH).ne
        exact eq_of_mem_segment_adjacent hd hx1 hx2
      · have hx2' : x ∈ chainSet (rpts H ox (c :: l)) := by simpa [rpts] using hx2
        obtain ⟨u, v, huv, hxuv⟩ := edgesAll_sound hall hx2'
        exact (disjoint_of_sepB (rsepB_sound huv hH) hx1 hxuv).elim

/-! ### Floor features -/

/-- A point of a segment whose first end point is strictly below the line `y = y₀` and whose
second end point is not above it is strictly below the line or equal to the second end point. -/
theorem seg_below {y₀ : ℝ} {u z x : Point} (hu : u.2 < y₀) (hz : z.2 ≤ y₀)
    (hx : x ∈ ArtGallery.segment u z) : x.2 < y₀ ∨ x = z := by
  obtain ⟨t, h0, h1, rfl⟩ := hx
  rcases eq_or_lt_of_le h1 with rfl | ht
  · right; ext <;> simp
  · left; simp only; nlinarith

theorem chainSet_below {y₀ : ℝ} : ∀ (u : Point) (rest : List Point) (z : Point), u.2 < y₀ →
    (∀ p ∈ rest, p.2 < y₀) → z.2 ≤ y₀ → ∀ x ∈ chainSet (u :: rest ++ [z]), x.2 < y₀ ∨ x = z
  | u, [], z, hu, _, hz, x, hx => by
    simp only [List.nil_append, List.cons_append, chainSet_cons_cons, chainSet_single,
      union_empty] at hx
    exact seg_below hu hz hx
  | u, v :: rest, z, hu, hr, hz, x, hx => by
    have e : u :: (v :: rest) ++ [z] = u :: v :: (rest ++ [z]) := rfl
    rw [e, chainSet_cons_cons] at hx
    rcases hx with hx | hx
    · have hv := hr v (by simp)
      rcases seg_below hu hv.le hx with h | rfl
      · exact Or.inl h
      · exact Or.inl hv
    · exact chainSet_below v rest z (hr v (by simp)) (fun p hp => hr p (by simp [hp])) hz x hx

/-- The floor feature check: at least three vertices, a robustly simple chain, first and last
vertex on the line `y = y₀` (with first abscissa smaller), and all other vertices robustly
strictly below the line. -/
def rFloorFeatB (H₀ y₀ : ℚ) (ch : List RPt) : Bool :=
  decide (3 ≤ ch.length) && rChainB H₀ ch &&
  decide ((ch.headD 0).2.1 = y₀ ∧ (ch.headD 0).2.2 = 0 ∧ (ch.getLastD 0).2.1 = y₀ ∧
    (ch.getLastD 0).2.2 = 0 ∧ (ch.headD 0).1 < (ch.getLastD 0).1) &&
  ch.tail.dropLast.all (fun p => rposB H₀ (y₀ - p.2.1) p.2.2)

theorem convex_open_strip (lo hi : ℝ) : Convex ℝ {p : Point | lo < p.1 ∧ p.1 < hi} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at ha hb ⊢
  have : s = 1 - t := by linarith
  subst this
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp only [sub_zero, one_mul, zero_mul, add_zero]; exact ha
  · constructor
    · nlinarith [mul_nonneg hs (sub_nonneg.2 ha.1.le), mul_pos ht' (sub_pos.2 hb.1)]
    · nlinarith [mul_nonneg hs (sub_nonneg.2 ha.2.le), mul_pos ht' (sub_pos.2 hb.2)]

theorem convex_closed_strip (lo hi : ℝ) : Convex ℝ {p : Point | lo ≤ p.1 ∧ p.1 ≤ hi} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at ha hb ⊢
  have : s = 1 - t := by linarith
  subst this
  constructor <;> nlinarith

/-- **Soundness of the floor feature check.**  For every `H ≥ H₀` and every translation `ox`
keeping the template strictly inside `x_lo < x < x_hi`, the instantiated chain is a floor
feature of the line `y = y₀`. -/
theorem rFloorFeatB_sound {H₀ H y₀ ox : ℚ} {xlo xhi : ℝ} {ch : List RPt}
    (h : rFloorFeatB H₀ y₀ ch = true) (hH : H₀ ≤ H)
    (hx : ∀ p ∈ ch, xlo < ((ox + p.1 : ℚ) : ℝ) ∧ ((ox + p.1 : ℚ) : ℝ) < xhi) :
    FloorFeature (y₀ : ℝ) xlo xhi (rpts H ox ch) := by
  simp only [rFloorFeatB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h3, hch⟩, ⟨hay, had, hzy, hzd, haz⟩⟩, hmid⟩ := h
  -- decompose the chain
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, ch = a :: b :: l := by
    match ch, h3 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hne : (b :: l) ≠ [] := by simp
  set z := (b :: l).getLast hne
  set m := (b :: l).dropLast
  have hbl : b :: l = m ++ [z] := (List.dropLast_append_getLast hne).symm
  have hzlast : (a :: b :: l).getLastD 0 = z := by
    rw [List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
  simp only [List.headD_cons, List.tail_cons] at hay had haz hmid
  rw [hzlast] at hzy hzd haz
  have hm : m ≠ [] := by
    intro hm0
    have := congrArg List.length hm0
    simp only [m, List.length_dropLast, List.length_cons, List.length_nil] at this h3
    omega
  -- the instantiated chain
  have hR : rpts H ox (a :: b :: l) =
      ratPoint (a.inst H ox) :: (rpts H ox m ++ [ratPoint (z.inst H ox)]) := by
    rw [hbl]; simp [rpts]
  have hfst : fstPt (rpts H ox (a :: b :: l)) = ratPoint (a.inst H ox) := rfl
  have hlst : lstPt (rpts H ox (a :: b :: l)) = ratPoint (z.inst H ox) := by
    rw [hR]; unfold lstPt; rw [List.getLastD_cons, List.getLastD_concat]
  have hay' : (ratPoint (a.inst H ox)).2 = (y₀ : ℝ) := by
    simp only [ratPoint, RPt.inst, hay, had, zero_mul, sub_zero]
  have hzy' : (ratPoint (z.inst H ox)).2 = (y₀ : ℝ) := by
    simp only [ratPoint, RPt.inst, hzy, hzd, zero_mul, sub_zero]
  have hmid' : ∀ p ∈ rpts H ox m, p.2 < (y₀ : ℝ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have := rpos_sound (hmid q hq) hH
    simp only [ratPoint, RPt.inst]
    have : q.2.1 - q.2.2 * H < y₀ := by linarith
    exact_mod_cast this
  refine ⟨by simp [rpts], rChainB_sound hH hch, by rw [hfst]; exact hay',
    by rw [hlst]; exact hzy', ?_, ?_, ?_⟩
  · rw [hfst, hlst]
    simp only [ratPoint, RPt.inst]
    exact_mod_cast (by linarith : ox + a.1 < ox + z.1)
  · intro p hp
    rw [hfst, hlst]
    rw [hR] at hp
    obtain ⟨v, rest, hvr⟩ : ∃ v rest, rpts H ox m = v :: rest := by
      obtain ⟨v0, rest0, hv0⟩ := List.exists_cons_of_ne_nil hm
      exact ⟨_, _, by rw [hv0]; rfl⟩
    rw [hvr] at hp hmid'
    have e : ratPoint (a.inst H ox) :: (v :: rest ++ [ratPoint (z.inst H ox)]) =
        ratPoint (a.inst H ox) :: v :: (rest ++ [ratPoint (z.inst H ox)]) := rfl
    rw [e, chainSet_cons_cons] at hp
    rcases hp with hp | hp
    · rw [segment_comm] at hp
      rcases seg_below (hmid' v (by simp)) hay'.le hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases chainSet_below v rest _ (hmid' v (by simp)) (fun q hq => hmid' q (by simp [hq]))
          hzy'.le p hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · apply chainSet_subset_of_convex (convex_open_strip xlo xhi)
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hx q hq

/-! ### Abscissa bounds of template chains -/

/-- The smallest abscissa of a template chain. -/
def xminR : List RPt → ℚ
  | [] => 0
  | [p] => p.1
  | p :: l => min p.1 (xminR l)

/-- The largest abscissa of a template chain. -/
def xmaxR : List RPt → ℚ
  | [] => 0
  | [p] => p.1
  | p :: l => max p.1 (xmaxR l)

theorem xminR_le : ∀ {l : List RPt} {p : RPt}, p ∈ l → xminR l ≤ p.1
  | [], _, h => by simp at h
  | [q], p, h => by simp at h; subst h; simp [xminR]
  | q :: r :: l, p, h => by
    simp only [xminR]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (xminR_le h)

theorem le_xmaxR : ∀ {l : List RPt} {p : RPt}, p ∈ l → p.1 ≤ xmaxR l
  | [], _, h => by simp at h
  | [q], p, h => by simp at h; subst h; simp [xmaxR]
  | q :: r :: l, p, h => by
    simp only [xmaxR]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_xmaxR h).trans (le_max_right _ _)

/-- `r a b` holds for every pair `a` before `b` in the list. -/
def pairwiseB {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (r a) && pairwiseB r l

theorem pairwiseB_sound {α : Type} {r : α → α → Bool} :
    ∀ {l : List α}, pairwiseB r l = true → l.Pairwise (fun a b => r a b = true)
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [pairwiseB, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwiseB_sound h.2)

end

end ArtGallery.Stade.Chain
