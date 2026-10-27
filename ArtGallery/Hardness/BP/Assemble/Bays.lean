module

public import ArtGallery.Hardness.BP.Assemble.Sep
public import ArtGallery.Hardness.BP.Bay

/-!
# Boundary-point variant: the receiver bays of the templates

Every receiver of a unit (and the weak copy `A` of an addition template) lies on the floor of a
bay (`BP/Bay.lean`, without `one` spikes): `tmplBaysBP k` lists, for the template of kind `k`, the
index `b` of the first bay vertex in the chain `tmplVBP k` and the left end point `x₀` of the
segment.  In the integer template coordinates the bay is placed by the frame
`tmplFrame D x₀ = (D x₀, scale D)`.

* `bay_of_chainAt` (generic): in a simple polygon `P` containing an integer chain `V`
  (`Tmpl.ChainAt P V a`) whose other edges avoid a region `R` (`Tmpl.SepAt P V a R`), a bay of `V`
  is a bay of `P` (`BayAt`) and is separated (`BaySep`), provided three kernel checks hold: the
  12 chain vertices from `b` are the bay vertices (`bayVtxB`), the other chain edges avoid the bay
  box (`bayAvoidB`, each edge has both ends weakly beyond one side of the box), and the bay box lies
  in `R` (`bayInRB`, checked at the corners of the box).
* `tmplBays_ok`: the checks for all bays of all four kinds.
* `SideAtBP.bayAt`, `SideAtBP.baySep`: for unit `m` of a side, every bay of its template is a
  separated bay of the polygon in template coordinates `hQ.tPoly hm`
  (`= φ⁻¹(Q)`, `φ = tmplMapBP`), at index `hQ.tStart hm + b`.
* `SideAtBP.bayAt_real`, `SideAtBP.baySep_real`: the same bays in the polygon `Q` itself (frame
  `(tmplFrame D x₀).place (S + 3, H − 1) (1/(D S))`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set Polygon
open ArtGallery.Sec5
open ArtGallery.Sec5.Tmpl (ChainAt SepAt Region cv)
open ArtGallery.Irrational (HP)
open ArtGallery.Vis.Cert (IPt)

/-! ### Frames of template bays -/

/-- The frame of a bay with left end point `x₀` (template point) in integer template coordinates
(denominator `D`): origin `D x₀`, scale `D`. -/
noncomputable def tmplFrame (D : ℕ) (x₀ : Q2) : Frame := ⟨(D : ℝ) * x₀.1, (D : ℝ) * x₀.2, D⟩

/-! ### Kernel checks -/

/-- The chain vertices `b, …, b + 11` are the vertices of the bay with left end point `x₀`. -/
def bayVtxB (V : List IPt) (b D : ℕ) (x₀ : Q2) : Bool :=
  (List.range 12).all fun j =>
    decide (((cv V (b + j)).1 : ℚ) = D * x₀.1 + D * ((bayRel false).getD j 0).1) &&
      decide (((cv V (b + j)).2 : ℚ) = D * x₀.2 + D * ((bayRel false).getD j 0).2)

/-- Both points weakly beyond one side of the box `[L, R] × [B, T]`. -/
def outBoxB (L R B T : ℚ) (u v : IPt) : Bool :=
  (decide ((u.1 : ℚ) ≤ L) && decide ((v.1 : ℚ) ≤ L)) ||
    (decide (R ≤ (u.1 : ℚ)) && decide (R ≤ (v.1 : ℚ))) ||
    (decide ((u.2 : ℚ) ≤ B) && decide ((v.2 : ℚ) ≤ B)) ||
    (decide (T ≤ (u.2 : ℚ)) && decide (T ≤ (v.2 : ℚ)))

/-- Every chain edge other than the 11 bay edges has both ends weakly beyond one side of the bay
box `D x₀ + D·((−1, 5/2) × (0, 1/8))`. -/
def bayAvoidB (V : List IPt) (b D : ℕ) (x₀ : Q2) : Bool :=
  (List.range (V.length - 1)).all fun j =>
    decide (b ≤ j ∧ j < b + 11) ||
      outBoxB (D * (x₀.1 - 1)) (D * (x₀.1 + 5 / 2)) (D * x₀.2) (D * (x₀.2 + 1 / 8))
        (cv V j) (cv V (j + 1))

/-- The four corners of the bay box. -/
def bayCorners (D : ℕ) (x₀ : Q2) : List Q2 :=
  [(D * (x₀.1 - 1), D * x₀.2), (D * (x₀.1 - 1), D * (x₀.2 + 1 / 8)),
    (D * (x₀.1 + 5 / 2), D * x₀.2), (D * (x₀.1 + 5 / 2), D * (x₀.2 + 1 / 8))]

/-- The bay box lies in the region `R`: every box constraint is positive at the four corners, and
every zone has a non-constant constraint that is `≤ 0` at the four corners. -/
def bayInRB (R : Region) (D : ℕ) (x₀ : Q2) : Bool :=
  R.box.all (fun c => (bayCorners D x₀).all fun q => decide (0 < c.qval q)) &&
    R.zones.all fun W => W.any fun c =>
      (decide (c.1 ≠ 0) || decide (c.2.1 ≠ 0)) && (bayCorners D x₀).all fun q => decide (c.qval q ≤ 0)

/-! ### Affine functions on a rectangle -/

theorem val_pos_of_corners {c : HP} {L R B T : ℝ} {p : Point} (h1 : L ≤ p.1) (h2 : p.1 ≤ R)
    (h3 : B ≤ p.2) (h4 : p.2 ≤ T) (hLB : 0 < c.val (L, B)) (hLT : 0 < c.val (L, T))
    (hRB : 0 < c.val (R, B)) (hRT : 0 < c.val (R, T)) : 0 < c.val p := by
  simp only [Irrational.HP.val] at *
  rcases le_total 0 (c.1 : ℝ) with ha | ha <;> rcases le_total 0 (c.2.1 : ℝ) with hb | hb
  · nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h3)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 h4)]
  · nlinarith [mul_nonneg (neg_nonneg.2 ha) (sub_nonneg.2 h2), mul_nonneg hb (sub_nonneg.2 h3)]
  · nlinarith [mul_nonneg (neg_nonneg.2 ha) (sub_nonneg.2 h2),
      mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 h4)]

theorem val_neg_of_corners {c : HP} {L R B T : ℝ} {p : Point} (h1 : L < p.1) (h2 : p.1 < R)
    (h3 : B < p.2) (h4 : p.2 < T) (hnz : c.1 ≠ 0 ∨ c.2.1 ≠ 0) (hLB : c.val (L, B) ≤ 0)
    (hLT : c.val (L, T) ≤ 0) (hRB : c.val (R, B) ≤ 0) (hRT : c.val (R, T) ≤ 0) :
    c.val p < 0 := by
  simp only [Irrational.HP.val] at *
  have hnz' : (c.1 : ℝ) ≠ 0 ∨ (c.2.1 : ℝ) ≠ 0 := by
    rcases hnz with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rcases lt_trichotomy (c.1 : ℝ) 0 with ha | ha | ha <;>
    rcases lt_trichotomy (c.2.1 : ℝ) 0 with hb | hb | hb
  · nlinarith [mul_pos (neg_pos.2 ha) (sub_pos.2 h1), mul_pos (neg_pos.2 hb) (sub_pos.2 h3)]
  · nlinarith [mul_pos (neg_pos.2 ha) (sub_pos.2 h1)]
  · nlinarith [mul_pos (neg_pos.2 ha) (sub_pos.2 h1), mul_pos hb (sub_pos.2 h4)]
  · nlinarith [mul_pos (neg_pos.2 hb) (sub_pos.2 h3)]
  · exfalso; rcases hnz' with h | h <;> exact h (by assumption)
  · nlinarith [mul_pos hb (sub_pos.2 h4)]
  · nlinarith [mul_pos ha (sub_pos.2 h2), mul_pos (neg_pos.2 hb) (sub_pos.2 h3)]
  · nlinarith [mul_pos ha (sub_pos.2 h2)]
  · nlinarith [mul_pos ha (sub_pos.2 h2), mul_pos hb (sub_pos.2 h4)]

/-! ### The generic bay lemma -/

section Generic

variable {P : Polygon} {V : List IPt} {a : ℕ} {R : Region} {b D : ℕ} {x₀ : Q2}

theorem tmplFrame_pt (q : Q2) : (tmplFrame D x₀).pt q =
    (((D * x₀.1 + D * q.1 : ℚ) : ℝ), ((D * x₀.2 + D * q.2 : ℚ) : ℝ)) := by
  simp only [Frame.pt, Frame.abs, tmplFrame, ratPoint]; push_cast; rfl

/-- The bay box in absolute template coordinates. -/
theorem tmplFrame_rel_box (hD : 0 < D) {p : Point} (h : (tmplFrame D x₀).rel p ∈ bayBox) :
    ((D * (x₀.1 - 1) : ℚ) : ℝ) < p.1 ∧ p.1 < ((D * (x₀.1 + 5 / 2) : ℚ) : ℝ) ∧
      ((D * x₀.2 : ℚ) : ℝ) < p.2 ∧ p.2 < ((D * (x₀.2 + 1 / 8) : ℚ) : ℝ) := by
  obtain ⟨b1, b2, b3, b4⟩ := h
  simp only [Frame.rel, tmplFrame] at b1 b2 b3 b4
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [lt_div_iff₀ hD'] at b1 b3
  rw [div_lt_iff₀ hD'] at b2 b4
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem bayAt_of_chainAt (hC : ChainAt P V a) (hb : b + 12 ≤ V.length) (hD : 0 < D)
    (hv : bayVtxB V b D x₀ = true) : BayAt P false (tmplFrame D x₀) (a + b) := by
  refine ⟨by simp only [tmplFrame]; exact_mod_cast hD, fun j hj => ?_⟩
  have hj' : j < 12 := by simpa [bayRel, bayL, bayW1, bayF, bayW2, bayR] using hj
  simp only [bayVtxB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨e1, e2⟩ := hv j hj'
  rw [show a + b + j = a + (b + j) by omega, hC (b + j) (by omega), tmplFrame_pt]
  simp only [intPoint]
  rw [← e1, ← e2]
  push_cast; rfl

theorem not_mem_box_of_outBoxB {L R B T : ℚ} {u v : IPt} (h : outBoxB L R B T u v = true)
    {p : Point} (hp : p ∈ ArtGallery.segment (intPoint u) (intPoint v))
    (hbox : (L : ℝ) < p.1 ∧ p.1 < (R : ℝ) ∧ (B : ℝ) < p.2 ∧ p.2 < (T : ℝ)) : False := by
  obtain ⟨b1, b2, b3, b4⟩ := hbox
  simp only [outBoxB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have f1 := Irrational.seg_fst_le hp
  have f2 := Irrational.seg_fst_ge hp
  have f3 := Irrational.seg_snd_le hp
  have f4 := Irrational.seg_snd_ge hp
  simp only [intPoint] at f1 f2 f3 f4
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · have h1' : ((u.1 : ℚ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    have h2' : ((v.1 : ℚ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h2
    push_cast at h1' h2'
    have := f1.trans (max_le h1' h2'); linarith
  · have h1' : (R : ℝ) ≤ ((u.1 : ℚ) : ℝ) := by exact_mod_cast h1
    have h2' : (R : ℝ) ≤ ((v.1 : ℚ) : ℝ) := by exact_mod_cast h2
    push_cast at h1' h2'
    have := (le_min h1' h2').trans f2; linarith
  · have h1' : ((u.2 : ℚ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h1
    have h2' : ((v.2 : ℚ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h2
    push_cast at h1' h2'
    have := f3.trans (max_le h1' h2'); linarith
  · have h1' : (T : ℝ) ≤ ((u.2 : ℚ) : ℝ) := by exact_mod_cast h1
    have h2' : (T : ℝ) ≤ ((v.2 : ℚ) : ℝ) := by exact_mod_cast h2
    push_cast at h1' h2'
    have := (le_min h1' h2').trans f4; linarith

theorem mem_of_bayInRB (hR : bayInRB R D x₀ = true) {p : Point}
    (hbox : ((D * (x₀.1 - 1) : ℚ) : ℝ) < p.1 ∧ p.1 < ((D * (x₀.1 + 5 / 2) : ℚ) : ℝ) ∧
      ((D * x₀.2 : ℚ) : ℝ) < p.2 ∧ p.2 < ((D * (x₀.2 + 1 / 8) : ℚ) : ℝ)) : R.Mem p := by
  obtain ⟨b1, b2, b3, b4⟩ := hbox
  simp only [bayInRB, bayCorners, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, decide_eq_true_eq,
    Bool.or_eq_true, ne_eq] at hR
  obtain ⟨hbx, hz⟩ := hR
  have cv : ∀ (c : HP) (q : Q2), c.val (ratPoint q) = (c.qval q : ℝ) := Irrational.HP.val_ratPoint
  refine ⟨fun c hc => ?_, fun W hW => ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hbx c hc
    refine val_pos_of_corners (L := ((D * (x₀.1 - 1) : ℚ) : ℝ)) (R := ((D * (x₀.1 + 5 / 2) : ℚ) : ℝ))
      (B := ((D * x₀.2 : ℚ) : ℝ)) (T := ((D * (x₀.2 + 1 / 8) : ℚ) : ℝ)) b1.le b2.le b3.le b4.le
      ?_ ?_ ?_ ?_
    · have := cv c (D * (x₀.1 - 1), D * x₀.2); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c1
    · have := cv c (D * (x₀.1 - 1), D * (x₀.2 + 1 / 8)); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c2
    · have := cv c (D * (x₀.1 + 5 / 2), D * x₀.2); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c3
    · have := cv c (D * (x₀.1 + 5 / 2), D * (x₀.2 + 1 / 8)); simp only [ratPoint] at this
      rw [this]; exact_mod_cast c4
  · obtain ⟨c, hc, hnz, c1, c2, c3, c4⟩ := hz W hW
    refine ⟨c, hc, val_neg_of_corners b1 b2 b3 b4 hnz ?_ ?_ ?_ ?_⟩
    · have := cv c (D * (x₀.1 - 1), D * x₀.2); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c1
    · have := cv c (D * (x₀.1 - 1), D * (x₀.2 + 1 / 8)); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c2
    · have := cv c (D * (x₀.1 + 5 / 2), D * x₀.2); simp only [ratPoint] at this; rw [this]
      exact_mod_cast c3
    · have := cv c (D * (x₀.1 + 5 / 2), D * (x₀.2 + 1 / 8)); simp only [ratPoint] at this
      rw [this]; exact_mod_cast c4

/-- **A bay of a template chain is a separated bay of the polygon.** -/
theorem bay_of_chainAt (hC : ChainAt P V a) (hS : SepAt P V a R) (hb : b + 12 ≤ V.length)
    (hD : 0 < D) (hv : bayVtxB V b D x₀ = true) (hav : bayAvoidB V b D x₀ = true)
    (hR : bayInRB R D x₀ = true) :
    BayAt P false (tmplFrame D x₀) (a + b) ∧ BaySep P false (tmplFrame D x₀) (a + b) := by
  refine ⟨bayAt_of_chainAt hC hb hD hv, ?_⟩
  intro i hi hnot p hp hbox
  have hbox' := tmplFrame_rel_box hD hbox
  have hlen12 : (bayRel false).length = 12 := by decide
  by_cases hch : ∃ j, j + 1 < V.length ∧ (a + j) % P.n = i
  · obtain ⟨j, hj, rfl⟩ := hch
    by_cases hin : b ≤ j ∧ j < b + 11
    · exact hnot (j - b) (by rw [hlen12]; omega)
        (by rw [show a + b + (j - b) = a + j by omega])
    · simp only [bayAvoidB, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        decide_eq_true_eq] at hav
      rcases hav j (by omega) with h | h
      · exact hin h
      · rw [hC.edge_eq hj] at hp
        exact not_mem_box_of_outBoxB h hp hbox'
  · push Not at hch
    exact hS i hi (fun j hj h => hch j hj h) p hp (mem_of_bayInRB hR hbox')

end Generic

/-! ### The checks for the four kinds -/

/-- **The bays of the templates pass the checks.** -/
theorem tmplBays_ok (k : Kind) : ∀ bx ∈ tmplBaysBP k, bx.1 + 12 ≤ (tmplVBP k).length ∧
    bayVtxB (tmplVBP k) bx.1 (tmplDBP k) bx.2 = true ∧
    bayAvoidB (tmplVBP k) bx.1 (tmplDBP k) bx.2 = true ∧
    bayInRB (tmplRBP k) (tmplDBP k) bx.2 = true := by
  cases k <;> decide +kernel

/-! ### The bays of the units of a side -/

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)

/-- The polygon in the template coordinates of unit `m`. -/
noncomputable abbrev SideAtBP.tPoly : Polygon :=
  Hardening.Invariance.mapPoly (tmplMapBP (us[m]'hm).kind (unitInputBP n k m (us[m]'hm)).S
    (unitInputBP n k m (us[m]'hm)).H (S_ne_of (hQ.good hm).S_ge_k)).symm Q

include hQ hm

/-- **The bays of unit `m`** (template coordinates). -/
theorem SideAtBP.bay {bx : ℕ × Q2} (hbx : bx ∈ tmplBaysBP (us[m]'hm).kind) :
    BayAt (hQ.tPoly hm) false (tmplFrame (tmplDBP (us[m]'hm).kind) bx.2) (hQ.tStart hm + bx.1) ∧
      BaySep (hQ.tPoly hm) false (tmplFrame (tmplDBP (us[m]'hm).kind) bx.2)
        (hQ.tStart hm + bx.1) := by
  obtain ⟨h1, h2, h3, h4⟩ := tmplBays_ok _ bx hbx
  exact bay_of_chainAt (hQ.chainAt hm) (hQ.sepAt hm) h1 (tmplDBP_pos _) h2 h3 h4

theorem SideAtBP.bayAt {bx : ℕ × Q2} (hbx : bx ∈ tmplBaysBP (us[m]'hm).kind) :
    BayAt (hQ.tPoly hm) false (tmplFrame (tmplDBP (us[m]'hm).kind) bx.2) (hQ.tStart hm + bx.1) :=
  (hQ.bay hm hbx).1

theorem SideAtBP.baySep {bx : ℕ × Q2} (hbx : bx ∈ tmplBaysBP (us[m]'hm).kind) :
    BaySep (hQ.tPoly hm) false (tmplFrame (tmplDBP (us[m]'hm).kind) bx.2) (hQ.tStart hm + bx.1) :=
  (hQ.bay hm hbx).2

end Side

/-! ### The bays in the polygon itself -/

/-- The frame of a template bay in the polygon itself: `φ ∘ (tmplFrame D x₀)` with
`φ(V) = (S + 3, H − 1) + V/(D S)`. -/
noncomputable def realFrame (D : ℕ) (S H : ℝ) (x₀ : Q2) : Frame :=
  (tmplFrame D x₀).place (S + 3, H - 1) (1 / ((D : ℝ) * S))

theorem tmplMapBP_symm_apply (kd : Kind) {S H : ℝ} (hS : S ≠ 0) (p : Point) :
    (tmplMapBP kd S H hS).symm p =
      ((p.1 - (S + 3)) * ((tmplDBP kd : ℝ) * S), (p.2 - (H - 1)) * ((tmplDBP kd : ℝ) * S)) := by
  have hD : (tmplDBP kd : ℝ) ≠ 0 := by exact_mod_cast (tmplDBP_pos kd).ne'
  apply (tmplMapBP kd S H hS).injective
  rw [AffineEquiv.apply_symm_apply, tmplMapBP_apply]
  ext <;> simp only <;> field_simp <;> ring

theorem realFrame_rel (kd : Kind) {S H : ℝ} (hS : 0 < S) (x₀ : Q2) (p : Point) :
    (realFrame (tmplDBP kd) S H x₀).rel p =
      (tmplFrame (tmplDBP kd) x₀).rel ((tmplMapBP kd S H hS.ne').symm p) := by
  have hD : (0 : ℝ) < tmplDBP kd := by exact_mod_cast tmplDBP_pos kd
  rw [tmplMapBP_symm_apply]
  simp only [realFrame, Frame.place, Frame.rel, tmplFrame]
  ext <;> simp only <;> field_simp <;> ring

theorem realFrame_pt (kd : Kind) {S H : ℝ} (hS : 0 < S) (x₀ q : Q2) :
    (realFrame (tmplDBP kd) S H x₀).pt q =
      tmplMapBP kd S H hS.ne' ((tmplFrame (tmplDBP kd) x₀).pt q) := by
  rw [tmplMapBP_apply]
  simp only [realFrame, Frame.pt, Frame.place_abs]
  ext <;> simp only <;> ring

section SideReal

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

theorem SideAtBP.S_pos : (0 : ℝ) < ((unitInputBP n k m (us[m]'hm)).S : ℝ) := by
  have := (hQ.good hm).S_ge_k; linarith

/-- **The bays of unit `m` in the polygon `Q`.** -/
theorem SideAtBP.bayAt_real {bx : ℕ × Q2} (hbx : bx ∈ tmplBaysBP (us[m]'hm).kind) :
    BayAt Q false (realFrame (tmplDBP (us[m]'hm).kind) ((unitInputBP n k m (us[m]'hm)).S : ℝ)
      ((unitInputBP n k m (us[m]'hm)).H : ℝ) bx.2) (hQ.tStart hm + bx.1) := by
  have hB := hQ.bayAt hm hbx
  have hS := hQ.S_pos hm
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [realFrame, Frame.place, tmplFrame]
    have hD : (0 : ℝ) < tmplDBP (us[m]'hm).kind := by exact_mod_cast tmplDBP_pos _
    positivity
  · have h := hB.vtx j hj
    have hn : 0 < Q.n := by have := hQ.simple.1; omega
    simp only [SideAtBP.tPoly, Hardening.Invariance.n_mapPoly] at h
    rw [Hardening.Invariance.vtx_mapPoly _ _ (Nat.mod_lt _ hn)] at h
    rw [realFrame_pt _ hS, ← h, AffineEquiv.apply_symm_apply]

/-- **The bays of unit `m` in the polygon `Q` are separated.** -/
theorem SideAtBP.baySep_real {bx : ℕ × Q2} (hbx : bx ∈ tmplBaysBP (us[m]'hm).kind) :
    BaySep Q false (realFrame (tmplDBP (us[m]'hm).kind) ((unitInputBP n k m (us[m]'hm)).S : ℝ)
      ((unitInputBP n k m (us[m]'hm)).H : ℝ) bx.2) (hQ.tStart hm + bx.1) := by
  have hB := hQ.baySep hm hbx
  have hS := hQ.S_pos hm
  intro i hi hnot p hp hbox
  rw [realFrame_rel _ hS] at hbox
  refine hB i (by simp only [SideAtBP.tPoly, Hardening.Invariance.n_mapPoly]; exact hi)
    (by simpa only [SideAtBP.tPoly, Hardening.Invariance.n_mapPoly] using hnot) _ ?_ hbox
  simp only [SideAtBP.tPoly]
  rw [Hardening.Invariance.edge_mapPoly _ _ hi]
  exact ⟨p, hp, rfl⟩

end SideReal

end ArtGallery.BP

end
