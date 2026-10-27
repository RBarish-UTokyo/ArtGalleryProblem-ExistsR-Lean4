module

public import ArtGallery.FewVars.Inside
public import ArtGallery.FewVars.SegInter
public import ArtGallery.Membership.Simple

/-!
# SIMPLE without auxiliary variables

`rsimpleF C` expresses that the polygon with corner list `C` is simple: `n ≥ 3`, the corners
are pairwise distinct, adjacent edges only meet in their common corner (`radjF`, the test of
`Membership.adjF`), and non-adjacent edges do not meet (`rmeetF`, the criterion
`segments_meet_iff`; no separating-line variables).  Main result: `holds_rsimpleF`.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry

variable {x : ℕ → ℝ} {P : Polygon} {C : List RPt}

/-- The two rational points are different. -/
def rptNeF (p q : RPt) : Formula := .not (.and (reqF p.1 q.1) (reqF p.2 q.2))

/-- Adjacent edges `[a, b]`, `[b, d]` meet only in `b`. -/
def radjF (a b d : RPt) : Formula := .not (.and (rzeroF (rdetT a b d)) (rposF (rdotT b a b d)))

/-- The parameter `T` of `segments_meet_iff`. -/
def rparT (p1 p2 p3 p4 : RPt) : RTerm := rdiv (rcrossT p1 p3 p3 p4) (rcrossT p1 p2 p3 p4)

/-- The parameter `U` of `segments_meet_iff`. -/
def rparU (p1 p2 p3 p4 : RPt) : RTerm := rdiv (rcrossT p1 p3 p1 p2) (rcrossT p1 p2 p3 p4)

/-- The segments `[p1, p2]` and `[p3, p4]` meet. -/
def rmeetF (p1 p2 p3 p4 : RPt) : Formula :=
  .or (.and (rneF (rcrossT p1 p2 p3 p4))
      (.and (runitF (rparT p1 p2 p3 p4)) (runitF (rparU p1 p2 p3 p4))))
    (.and (rzeroF (rcrossT p1 p2 p3 p4))
      (.or (ronSegF p3 p1 p2) (.or (ronSegF p4 p1 p2) (ronSegF p1 p3 p4))))

/-- Edges `i` and `j` meet exactly in their common endpoints. -/
def redgePairF (C : List RPt) (i j : ℕ) : Formula :=
  if i = j then fTrue
  else if j = (i + 1) % C.length then radjF (cr C i) (cr C j) (cr C ((j + 1) % C.length))
  else if i = (j + 1) % C.length then radjF (cr C j) (cr C i) (cr C ((i + 1) % C.length))
  else .not (rmeetF (cr C i) (cr C ((i + 1) % C.length)) (cr C j) (cr C ((j + 1) % C.length)))

/-- The conditions for the pair `(b / n, b % n)`. -/
def rsimplePairF (C : List RPt) (b : ℕ) : Formula :=
  .and (if b / C.length = b % C.length then fTrue
      else rptNeF (cr C (b / C.length)) (cr C (b % C.length)))
    (redgePairF C (b / C.length) (b % C.length))

/-- **SIMPLE** (variable-free): the polygon with corner list `C` is simple. -/
def rsimpleF (C : List RPt) : Formula :=
  .and (if 3 ≤ C.length then fTrue else fFalse)
    (bigAnd ((List.range (C.length * C.length)).map (rsimplePairF C)))

variable {p q d : RPt} {p' q' d' : Point}

theorem holds_rptNeF (hp : PRep x p p') (hq : PRep x q q') : (rptNeF p q).Holds x ↔ p' ≠ q' := by
  rw [rptNeF, holds_not, holds_and, holds_reqF hp.1 hq.1, holds_reqF hp.2 hq.2, Ne,
    Prod.ext_iff]

theorem holds_radjF (hp : PRep x p p') (hq : PRep x q q') (hd : PRep x d d') :
    (radjF p q d).Holds x ↔ ¬ (det p' q' d' = 0 ∧ 0 < dotR q' p' q' d') := by
  rw [radjF, holds_not, holds_and, holds_rzeroF (Rep.det hp hq hd),
    holds_rposF (Rep.dot hq hp hq hd)]

theorem holds_rmeetF {p1 p2 p3 p4 : RPt} {p1' p2' p3' p4' : Point} (h1 : PRep x p1 p1')
    (h2 : PRep x p2 p2') (h3 : PRep x p3 p3') (h4 : PRep x p4 p4') :
    (rmeetF p1 p2 p3 p4).Holds x ↔
      (ArtGallery.segment p1' p2' ∩ ArtGallery.segment p3' p4').Nonempty := by
  rw [segments_meet_iff, SegMeet, rmeetF, holds_or, holds_and, holds_and, holds_and, holds_or,
    holds_or, holds_rneF (Rep.cross h1 h2 h3 h4), holds_rzeroF (Rep.cross h1 h2 h3 h4),
    holds_ronSegF h3 h1 h2, holds_ronSegF h4 h1 h2, holds_ronSegF h1 h3 h4]
  have hD := Rep.cross h1 h2 h3 h4
  constructor
  · rintro (⟨hne, hT, hU⟩ | h)
    · left
      rw [rparT, holds_runitF (Rep.div (Rep.cross h1 h3 h3 h4) hD hne)] at hT
      rw [rparU, holds_runitF (Rep.div (Rep.cross h1 h3 h1 h2) hD hne)] at hU
      exact ⟨hne, hT.1, hT.2, hU.1, hU.2⟩
    · exact Or.inr h
  · rintro (⟨hne, hT0, hT1, hU0, hU1⟩ | h)
    · left
      refine ⟨hne, ?_, ?_⟩
      · rw [rparT, holds_runitF (Rep.div (Rep.cross h1 h3 h3 h4) hD hne)]; exact ⟨hT0, hT1⟩
      · rw [rparU, holds_runitF (Rep.div (Rep.cross h1 h3 h1 h2) hD hne)]; exact ⟨hU0, hU1⟩
    · exact Or.inr h

/-- Disjointness of two segments through `rmeetF`. -/
theorem disjoint_iff_not_meet {s t : Set Point} : Disjoint s t ↔ ¬ (s ∩ t).Nonempty := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.not_nonempty_iff_eq_empty]

/-- **SIMPLE is exact.** -/
theorem holds_rsimpleF (hC : CornersRep x P C) : (rsimpleF C).Holds x ↔ P.Simple := by
  have hn : C.length = P.n := hC.1
  constructor
  · rintro ⟨h3, hpairs⟩
    have hn3 : 3 ≤ P.n := by
      rw [← hn]
      by_contra h; rw [ite_eq_right h] at h3; exact not_holds_fFalse x h3
    rw [holds_bigAnd_range, hn] at hpairs
    have hp : ∀ i < P.n, ∀ j < P.n, (rsimplePairF C (i * P.n + j)).Holds x :=
      fun i hi j hj => hpairs _ (pair_lt hi hj)
    have hd : DistinctVtx P := by
      intro i j hi hj hij
      by_contra hne
      have := (hp i hi j hj).1
      rw [hn, pair_div hj, pair_mod hj, ite_eq_right hne, holds_rptNeF (hC.vtx hi) (hC.vtx hj)]
        at this
      exact this hij
    refine ⟨hn3, hd, ?_⟩
    intro i j hi hj hij
    have he := (hp i hi j hj).2
    rw [hn, pair_div hj, pair_mod hj] at he
    unfold redgePairF at he
    rw [ite_eq_right hij, hn] at he
    by_cases h1 : j = (i + 1) % P.n
    · rw [ite_eq_left h1, holds_radjF (hC.vtx hi) (hC.vtx hj) (hC.next' hj)] at he
      rw [edge_inter_adj hn3 hd hi hj h1]
      exact (inter_adj_iff _ _ _).2 he
    rw [ite_eq_right h1] at he
    by_cases h2 : i = (j + 1) % P.n
    · rw [ite_eq_left h2, holds_radjF (hC.vtx hj) (hC.vtx hi) (hC.next' hi)] at he
      rw [Set.inter_comm, commonEndpoints_comm, edge_inter_adj hn3 hd hj hi h2]
      exact (inter_adj_iff _ _ _).2 he
    rw [ite_eq_right h2, holds_not,
      holds_rmeetF (hC.vtx hi) (hC.next' hi) (hC.vtx hj) (hC.next' hj)] at he
    rw [edge_inter_nonadj hd hi hj hij h1 h2, Polygon.edge, Polygon.edge, disjoint_iff_not_meet]
    exact he
  · rintro ⟨hn3, hd, hedge⟩
    refine ⟨?_, ?_⟩
    · rw [ite_eq_left (hn ▸ hn3)]; exact holds_fTrue x
    rw [holds_bigAnd_range, hn]
    intro b hb
    have hn0 : 0 < P.n := by omega
    have hi : b / P.n < P.n := Nat.div_lt_of_lt_mul hb
    have hj : b % P.n < P.n := Nat.mod_lt _ hn0
    refine ⟨?_, ?_⟩
    · rw [hn]
      split_ifs with hij
      · exact holds_fTrue x
      · rw [holds_rptNeF (hC.vtx hi) (hC.vtx hj)]
        exact fun h => hij (hd _ _ hi hj h)
    · rw [hn]
      unfold redgePairF
      rw [hn]
      split_ifs with h0 h1 h2
      · exact holds_fTrue x
      · rw [holds_radjF (hC.vtx hi) (hC.vtx hj) (hC.next' hj)]
        exact (inter_adj_iff _ _ _).1
          ((edge_inter_adj hn3 hd hi hj h1).1 (hedge _ _ hi hj h0))
      · rw [holds_radjF (hC.vtx hj) (hC.vtx hi) (hC.next' hi)]
        have := hedge _ _ hi hj h0
        rw [Set.inter_comm, commonEndpoints_comm, edge_inter_adj hn3 hd hj hi h2] at this
        exact (inter_adj_iff _ _ _).1 this
      · rw [holds_not, holds_rmeetF (hC.vtx hi) (hC.next' hi) (hC.vtx hj) (hC.next' hj)]
        have := (edge_inter_nonadj hd hi hj h0 h1 h2).1 (hedge _ _ hi hj h0)
        rw [Polygon.edge, Polygon.edge, disjoint_iff_not_meet] at this
        exact this

/-! ## Variables -/

theorem FVars_rsimpleF {S : ℕ → Prop} (hC : CornersV S C) : FVars S (rsimpleF C) := by
  have hm : ∀ p1 p2 p3 p4 : RPt, PV S p1 → PV S p2 → PV S p3 → PV S p4 →
      FVars S (rmeetF p1 p2 p3 p4) := by
    intro p1 p2 p3 p4 h1 h2 h3 h4
    have hD := RVars.cross h1 h2 h3 h4
    exact ⟨⟨FVars_rneF hD, FVars_runitF ((RVars.cross h1 h3 h3 h4).div hD),
        FVars_runitF ((RVars.cross h1 h3 h1 h2).div hD)⟩,
      ⟨FVars_rzeroF hD, FVars_ronSegF h3 h1 h2, FVars_ronSegF h4 h1 h2, FVars_ronSegF h1 h3 h4⟩⟩
  have ha : ∀ p1 p2 p3 : RPt, PV S p1 → PV S p2 → PV S p3 → FVars S (radjF p1 p2 p3) :=
    fun p1 p2 p3 h1 h2 h3 => ⟨FVars_rzeroF (RVars.det h1 h2 h3), FVars_rposF (RVars.dot h2 h1 h2 h3)⟩
  refine ⟨by split_ifs <;> simp, ?_⟩
  rw [FVars_bigAnd]
  intro φ hφ
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hφ
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact FVars_fTrue S
    · exact ⟨FVars_reqF (hC _).1 (hC _).1, FVars_reqF (hC _).2 (hC _).2⟩
  · unfold redgePairF
    split_ifs
    · exact FVars_fTrue S
    · exact ha _ _ _ (hC _) (hC _) (hC _)
    · exact ha _ _ _ (hC _) (hC _) (hC _)
    · exact hm _ _ _ _ (hC _) (hC _) (hC _) (hC _)

end ArtGallery.FewVars

end
