module

public import ArtGallery.Membership.Combinators

/-!
# Rational terms

To write the art-gallery formula without auxiliary variables, every geometric quantity is built
as a *rational term*: a pair `(num, den)` of terms with a positive denominator.  `Rep x r v`
says that under the assignment `x` the rational term `r` represents the real number `v`
(`0 < den` and `num = v · den`).  The arithmetic operations (`radd`, `rsub`, `rmul`, `rneg`,
`rdiv`) act on numerators and denominators; `rdiv` multiplies through by the divisor's
numerator so that the denominator stays positive (if the divisor is nonzero).

Sign conditions become polynomial sign conditions on the numerators (`rposF`, `rzeroF`, …)
and comparisons are cross-multiplied (`rltF`, `rleF`, `reqF`).

Points are pairs of rational terms (`RPt`, `PRep`), and the geometric terms (`rdetT`, `rdotT`,
`rcrossT`, `rlerpT`) represent the real functions `det`, `dotR`, `crossR`, `lerp`.  `RVars`
and `PV` record that all variables of a rational term / point satisfy a predicate.
-/

@[expose] public section

namespace ArtGallery.FewVars

open ArtGallery.ETR ArtGallery.Membership Geometry

/-! ## Rational terms -/

/-- A rational term: a numerator and a denominator. -/
abbrev RTerm : Type := Term × Term

/-- The rational term `r` represents `v` under `x`: its denominator is positive and its numerator
is `v` times its denominator. -/
def Rep (x : ℕ → ℝ) (r : RTerm) (v : ℝ) : Prop := 0 < r.2.eval x ∧ r.1.eval x = v * r.2.eval x

/-- A term as a rational term (denominator `1`). -/
def rconst (t : Term) : RTerm := (t, .one)

/-- Sum. -/
def radd (a b : RTerm) : RTerm := (.add (.mul a.1 b.2) (.mul b.1 a.2), .mul a.2 b.2)

/-- Difference. -/
def rsub (a b : RTerm) : RTerm := (.sub (.mul a.1 b.2) (.mul b.1 a.2), .mul a.2 b.2)

/-- Product. -/
def rmul (a b : RTerm) : RTerm := (.mul a.1 b.1, .mul a.2 b.2)

/-- Negation. -/
def rneg (a : RTerm) : RTerm := (.sub .zero a.1, a.2)

/-- Quotient `a / b` (numerator and denominator multiplied by the numerator of `b`, so that the
denominator is positive when `b ≠ 0`). -/
def rdiv (a b : RTerm) : RTerm := (.mul (.mul a.1 b.2) b.1, .mul (.mul a.2 b.1) b.1)

/-- The constant `0`. -/
def rzero : RTerm := (.zero, .one)

/-- The constant `1`. -/
def rone : RTerm := (.one, .one)

/-- The constant `2`. -/
def rtwo : RTerm := (.add .one .one, .one)

/-- The constant `3`. -/
def rthree : RTerm := (.add (.add .one .one) .one, .one)

theorem Rep.const (x : ℕ → ℝ) (t : Term) : Rep x (rconst t) (t.eval x) := by
  simp [Rep, rconst]

theorem Rep.zero (x : ℕ → ℝ) : Rep x rzero 0 := by simp [Rep, rzero]

theorem Rep.one (x : ℕ → ℝ) : Rep x rone 1 := by simp [Rep, rone]

theorem Rep.two (x : ℕ → ℝ) : Rep x rtwo 2 := by simp [Rep, rtwo]; norm_num

theorem Rep.three (x : ℕ → ℝ) : Rep x rthree 3 := by simp [Rep, rthree]; norm_num

theorem Rep.frac {x : ℕ → ℝ} {s t : Term} (ht : 0 < t.eval x) :
    Rep x (s, t) (s.eval x / t.eval x) :=
  ⟨ht, by field_simp⟩

variable {x : ℕ → ℝ} {a b : RTerm} {u v : ℝ}

theorem Rep.add (ha : Rep x a u) (hb : Rep x b v) : Rep x (radd a b) (u + v) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨by simp only [radd, eval_mul]; positivity, ?_⟩
  simp only [radd, eval_add, eval_mul, ha1, hb1]; ring

theorem Rep.sub (ha : Rep x a u) (hb : Rep x b v) : Rep x (rsub a b) (u - v) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨by simp only [rsub, eval_mul]; positivity, ?_⟩
  simp only [rsub, eval_sub, eval_mul, ha1, hb1]; ring

theorem Rep.mul (ha : Rep x a u) (hb : Rep x b v) : Rep x (rmul a b) (u * v) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨by simp only [rmul, eval_mul]; positivity, ?_⟩
  simp only [rmul, eval_mul, ha1, hb1]; ring

theorem Rep.neg (ha : Rep x a u) : Rep x (rneg a) (-u) := by
  obtain ⟨ha0, ha1⟩ := ha
  refine ⟨ha0, ?_⟩
  simp only [rneg, eval_sub, eval_zero, ha1]; ring

theorem Rep.div (ha : Rep x a u) (hb : Rep x b v) (hv : v ≠ 0) : Rep x (rdiv a b) (u / v) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hb1' : b.1.eval x ≠ 0 := by rw [hb1]; exact mul_ne_zero hv hb0.ne'
  refine ⟨?_, ?_⟩
  · simp only [rdiv, eval_mul]
    rw [mul_assoc]
    exact mul_pos ha0 (mul_self_pos.2 hb1')
  · simp only [rdiv, eval_mul, ha1, hb1]; field_simp

/-- A represented value is unique. -/
theorem Rep.unique (ha : Rep x a u) (hb : Rep x a v) : u = v := by
  obtain ⟨h0, h1⟩ := ha
  obtain ⟨_, h2⟩ := hb
  have : (u - v) * a.2.eval x = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h h0.ne'

theorem Rep.congr {w : ℝ} (ha : Rep x a u) (h : u = w) : Rep x a w := h ▸ ha

/-- The numerator has the sign of the represented value. -/
theorem Rep.num_pos_iff (ha : Rep x a u) : 0 < a.1.eval x ↔ 0 < u := by
  rw [ha.2]; exact ⟨fun h => pos_of_mul_pos_left h ha.1.le, fun h => mul_pos h ha.1⟩

theorem Rep.num_nonneg_iff (ha : Rep x a u) : 0 ≤ a.1.eval x ↔ 0 ≤ u := by
  rw [ha.2]
  exact ⟨fun h => nonneg_of_mul_nonneg_left h ha.1, fun h => mul_nonneg h ha.1.le⟩

theorem Rep.num_eq_zero_iff (ha : Rep x a u) : a.1.eval x = 0 ↔ u = 0 := by
  rw [ha.2]; simp [ha.1.ne']

/-! ## Sign conditions -/

/-- `0 < a`. -/
def rposF (a : RTerm) : Formula := .lt .zero a.1

/-- `0 ≤ a`. -/
def rnonnegF (a : RTerm) : Formula := .le .zero a.1

/-- `a ≤ 0`. -/
def rnonposF (a : RTerm) : Formula := .le a.1 .zero

/-- `a = 0`. -/
def rzeroF (a : RTerm) : Formula := .eq a.1 .zero

/-- `a ≠ 0`. -/
def rneF (a : RTerm) : Formula := .not (.eq a.1 .zero)

/-- `a < b`. -/
def rltF (a b : RTerm) : Formula := .lt (.mul a.1 b.2) (.mul b.1 a.2)

/-- `a ≤ b`. -/
def rleF (a b : RTerm) : Formula := .le (.mul a.1 b.2) (.mul b.1 a.2)

/-- `a = b`. -/
def reqF (a b : RTerm) : Formula := .eq (.mul a.1 b.2) (.mul b.1 a.2)

/-- `0 ≤ a ≤ 1`. -/
def runitF (a : RTerm) : Formula := .and (rnonnegF a) (rleF a rone)

theorem holds_rposF (ha : Rep x a u) : (rposF a).Holds x ↔ 0 < u := by
  simp only [rposF, holds_lt, eval_zero]; exact ha.num_pos_iff

theorem holds_rnonnegF (ha : Rep x a u) : (rnonnegF a).Holds x ↔ 0 ≤ u := by
  simp only [rnonnegF, holds_le, eval_zero]; exact ha.num_nonneg_iff

theorem holds_rnonposF (ha : Rep x a u) : (rnonposF a).Holds x ↔ u ≤ 0 := by
  simp only [rnonposF, holds_le, eval_zero]
  have := (Rep.neg ha).num_nonneg_iff
  simp only [rneg, eval_sub, eval_zero] at this
  constructor
  · intro h; have := this.1 (by linarith); linarith
  · intro h; have := this.2 (by linarith); linarith

theorem holds_rzeroF (ha : Rep x a u) : (rzeroF a).Holds x ↔ u = 0 := by
  simp only [rzeroF, holds_eq, eval_zero]; exact ha.num_eq_zero_iff

theorem holds_rneF (ha : Rep x a u) : (rneF a).Holds x ↔ u ≠ 0 := by
  simp only [rneF, holds_not, holds_eq, eval_zero]; rw [ha.num_eq_zero_iff]

theorem holds_rltF (ha : Rep x a u) (hb : Rep x b v) : (rltF a b).Holds x ↔ u < v := by
  simp only [rltF, holds_lt, eval_mul, ha.2, hb.2]
  have := mul_pos ha.1 hb.1
  constructor
  · intro h; by_contra h'; have h'' := not_lt.1 h'; nlinarith
  · intro h; nlinarith

theorem holds_rleF (ha : Rep x a u) (hb : Rep x b v) : (rleF a b).Holds x ↔ u ≤ v := by
  simp only [rleF, holds_le, eval_mul, ha.2, hb.2]
  have := mul_pos ha.1 hb.1
  constructor
  · intro h; by_contra h'; have h'' := not_le.1 h'; nlinarith
  · intro h; nlinarith

theorem holds_reqF (ha : Rep x a u) (hb : Rep x b v) : (reqF a b).Holds x ↔ u = v := by
  simp only [reqF, holds_eq, eval_mul, ha.2, hb.2]
  have := mul_pos ha.1 hb.1
  constructor
  · intro h
    have : (u - v) * (a.2.eval x * b.2.eval x) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · intro h; rw [h]; ring

theorem holds_runitF (ha : Rep x a u) : (runitF a).Holds x ↔ 0 ≤ u ∧ u ≤ 1 := by
  rw [runitF, holds_and, holds_rnonnegF ha, holds_rleF ha (Rep.one x)]

/-! ## Rational points -/

/-- A point given by two rational terms. -/
abbrev RPt : Type := RTerm × RTerm

/-- The rational point `p` represents the point `z`. -/
def PRep (x : ℕ → ℝ) (p : RPt) (z : Point) : Prop := Rep x p.1 z.1 ∧ Rep x p.2 z.2

/-- The origin. -/
def r0 : RPt := (rzero, rzero)

theorem PRep.r0 (x : ℕ → ℝ) : PRep x r0 (0, 0) := ⟨Rep.zero x, Rep.zero x⟩

/-- The point whose coordinates are the variables `i`, `i + 1`. -/
def rvarPt (i : ℕ) : RPt := (rconst (.var i), rconst (.var (i + 1)))

theorem PRep.var (x : ℕ → ℝ) (i : ℕ) : PRep x (rvarPt i) (x i, x (i + 1)) :=
  ⟨Rep.const x _, Rep.const x _⟩

/-- The determinant `det a b c`. -/
def rdetT (a b c : RPt) : RTerm :=
  rsub (rmul (rsub b.1 a.1) (rsub c.2 a.2)) (rmul (rsub c.1 a.1) (rsub b.2 a.2))

/-- The scalar product `(q - p) · (s - r)`. -/
def rdotT (p q r s : RPt) : RTerm :=
  radd (rmul (rsub q.1 p.1) (rsub s.1 r.1)) (rmul (rsub q.2 p.2) (rsub s.2 r.2))

/-- The cross product `(q - p) × (s - r)`. -/
def rcrossT (p q r s : RPt) : RTerm :=
  rsub (rmul (rsub q.1 p.1) (rsub s.2 r.2)) (rmul (rsub q.2 p.2) (rsub s.1 r.1))

/-- The point `a + h (b - a)`. -/
def rlerpT (a b : RPt) (h : RTerm) : RPt :=
  (radd a.1 (rmul h (rsub b.1 a.1)), radd a.2 (rmul h (rsub b.2 a.2)))

variable {p q r s : RPt} {p' q' r' s' : Point}

theorem Rep.det (hp : PRep x p p') (hq : PRep x q q') (hr : PRep x r r') :
    Rep x (rdetT p q r) (det p' q' r') :=
  ((hq.1.sub hp.1).mul (hr.2.sub hp.2)).sub ((hr.1.sub hp.1).mul (hq.2.sub hp.2))

theorem Rep.dot (hp : PRep x p p') (hq : PRep x q q') (hr : PRep x r r') (hs : PRep x s s') :
    Rep x (rdotT p q r s) (dotR p' q' r' s') :=
  ((hq.1.sub hp.1).mul (hs.1.sub hr.1)).add ((hq.2.sub hp.2).mul (hs.2.sub hr.2))

theorem Rep.cross (hp : PRep x p p') (hq : PRep x q q') (hr : PRep x r r') (hs : PRep x s s') :
    Rep x (rcrossT p q r s) (crossR p' q' r' s') :=
  ((hq.1.sub hp.1).mul (hs.2.sub hr.2)).sub ((hq.2.sub hp.2).mul (hs.1.sub hr.1))

theorem PRep.lerp {h : RTerm} {t : ℝ} (hp : PRep x p p') (hq : PRep x q q') (hh : Rep x h t) :
    PRep x (rlerpT p q h) (lerp p' q' t) :=
  ⟨hp.1.add (hh.mul (hq.1.sub hp.1)), hp.2.add (hh.mul (hq.2.sub hp.2))⟩

/-- A represented point is unique. -/
theorem PRep.unique (hp : PRep x p p') (hq : PRep x p q') : p' = q' :=
  Prod.ext (hp.1.unique hq.1) (hp.2.unique hq.2)

/-! ## Variables -/

/-- All variables of the rational term satisfy `S`. -/
def RVars (S : ℕ → Prop) (r : RTerm) : Prop := TVars S r.1 ∧ TVars S r.2

/-- All variables of the rational point satisfy `S`. -/
def PV (S : ℕ → Prop) (p : RPt) : Prop := RVars S p.1 ∧ RVars S p.2

variable {S : ℕ → Prop}

theorem RVars.const {t : Term} (ht : TVars S t) : RVars S (rconst t) := ⟨ht, trivial⟩

theorem RVars.add (ha : RVars S a) (hb : RVars S b) : RVars S (radd a b) :=
  ⟨⟨⟨ha.1, hb.2⟩, ⟨hb.1, ha.2⟩⟩, ⟨ha.2, hb.2⟩⟩

theorem RVars.sub (ha : RVars S a) (hb : RVars S b) : RVars S (rsub a b) :=
  ⟨⟨⟨ha.1, hb.2⟩, ⟨hb.1, ha.2⟩⟩, ⟨ha.2, hb.2⟩⟩

theorem RVars.mul (ha : RVars S a) (hb : RVars S b) : RVars S (rmul a b) :=
  ⟨⟨ha.1, hb.1⟩, ⟨ha.2, hb.2⟩⟩

theorem RVars.neg (ha : RVars S a) : RVars S (rneg a) := ⟨⟨trivial, ha.1⟩, ha.2⟩

theorem RVars.div (ha : RVars S a) (hb : RVars S b) : RVars S (rdiv a b) :=
  ⟨⟨⟨ha.1, hb.2⟩, hb.1⟩, ⟨⟨ha.2, hb.1⟩, hb.1⟩⟩

theorem RVars.zero : RVars S rzero := ⟨trivial, trivial⟩
theorem RVars.one : RVars S rone := ⟨trivial, trivial⟩
theorem RVars.two : RVars S rtwo := ⟨⟨trivial, trivial⟩, trivial⟩
theorem RVars.three : RVars S rthree := ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩

theorem PV.r0 : PV S r0 := ⟨RVars.zero, RVars.zero⟩

theorem PV.var {i : ℕ} (h0 : S i) (h1 : S (i + 1)) : PV S (rvarPt i) :=
  ⟨RVars.const h0, RVars.const h1⟩

theorem RVars.det (hp : PV S p) (hq : PV S q) (hr : PV S r) : RVars S (rdetT p q r) :=
  ((hq.1.sub hp.1).mul (hr.2.sub hp.2)).sub ((hr.1.sub hp.1).mul (hq.2.sub hp.2))

theorem RVars.dot (hp : PV S p) (hq : PV S q) (hr : PV S r) (hs : PV S s) :
    RVars S (rdotT p q r s) :=
  ((hq.1.sub hp.1).mul (hs.1.sub hr.1)).add ((hq.2.sub hp.2).mul (hs.2.sub hr.2))

theorem RVars.cross (hp : PV S p) (hq : PV S q) (hr : PV S r) (hs : PV S s) :
    RVars S (rcrossT p q r s) :=
  ((hq.1.sub hp.1).mul (hs.2.sub hr.2)).sub ((hq.2.sub hp.2).mul (hs.1.sub hr.1))

theorem PV.lerp {h : RTerm} (hp : PV S p) (hq : PV S q) (hh : RVars S h) :
    PV S (rlerpT p q h) :=
  ⟨hp.1.add (hh.mul (hq.1.sub hp.1)), hp.2.add (hh.mul (hq.2.sub hp.2))⟩

theorem FVars_rposF (ha : RVars S a) : FVars S (rposF a) := ⟨trivial, ha.1⟩
theorem FVars_rnonnegF (ha : RVars S a) : FVars S (rnonnegF a) := ⟨trivial, ha.1⟩
theorem FVars_rnonposF (ha : RVars S a) : FVars S (rnonposF a) := ⟨ha.1, trivial⟩
theorem FVars_rzeroF (ha : RVars S a) : FVars S (rzeroF a) := ⟨ha.1, trivial⟩
theorem FVars_rneF (ha : RVars S a) : FVars S (rneF a) := ⟨ha.1, trivial⟩
theorem FVars_rltF (ha : RVars S a) (hb : RVars S b) : FVars S (rltF a b) :=
  ⟨⟨ha.1, hb.2⟩, ⟨hb.1, ha.2⟩⟩
theorem FVars_rleF (ha : RVars S a) (hb : RVars S b) : FVars S (rleF a b) :=
  ⟨⟨ha.1, hb.2⟩, ⟨hb.1, ha.2⟩⟩
theorem FVars_reqF (ha : RVars S a) (hb : RVars S b) : FVars S (reqF a b) :=
  ⟨⟨ha.1, hb.2⟩, ⟨hb.1, ha.2⟩⟩
theorem FVars_runitF (ha : RVars S a) : FVars S (runitF a) :=
  ⟨FVars_rnonnegF ha, FVars_rleF ha RVars.one⟩

end ArtGallery.FewVars

end
