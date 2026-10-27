module

public import ArtGallery.Hardness.Sec5.Corridor.Copy
public import ArtGallery.Hardness.Sec5.Corridor.Slabs

/-!
# Section 5: corridors — the copy algebra for the corridor's umbras and nooks

Instances of `CopyPair` (`Corridor/Copy.lean`) for pair `k` of a corridor `I : Input`:
* `I.umbraQ k`: shadow corners `c0, c1`; its crossing points `X (3/2) (3/2)`, `X 0 0` are the
  corridor's `f0`, `f1` (`umbra_eq`);
* `I.nookQ k`: shadow corners `z0, z1` (the nook mouth); `X (3/2) (3/2)`, `X 0 0` are `F0, F1`
  (`nook_eq`);
both with base segment `s_σ` (`a0 = (27σ/2, 0)`, scale `1`) and receiver `r_τ`
(`a1 = m + T_τ/S`, scale `1/S`); offsets `t ∈ [0, 3/2]`.  `umbraR`, `nookR` are the same pairs
over `ℝ` (`CopyPair.castR`), whose guards `p t`, `q t` are the real base / receiver guards.

Under `I.Valid N` (scale hypotheses, slots `27σ/2 + 3/2 ≤ 14N`, `|T_τ| ≤ 50`, at most three
pairs), for every pair `k < p`:
* both pairs satisfy `Hyp` and `Adm (3/2)` (`umbraQ_hyp`, `umbraQ_adm`, `nookQ_hyp`,
  `nookQ_adm` and the real versions);
* the axis vertices lie on the axes: `L(p_k) = L(z'_k) = 0` for the umbra, `L(n0) = L(n1) = 0`
  for the nook (`umbra_L_sgPt`, `umbra_L_zp`, `nook_L_n0`, `nook_L_n1`);
* **copy statements** (`umbra_copy_iff`, `nook_copy_iff`): for real offsets `t` (base guard) and
  `t'` (receiver guard) in `[0, 3/2]`, the umbra region on and above the critical segment is
  covered iff `t ≤ t'`, the nook critical segment is covered iff `t' ≤ t`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

/-! ## Copy pairs of a corridor (generic) -/

section Generic

variable {K : Type*} [Field K]

/-- The copy pair of base slot `σ` and the receiver with template left endpoint `T`, for the
shadow corners `k0`, `k1`. -/
def copyPair (S H : K) (σ : ℕ) (T k0 k1 : K × K) : CopyPair K :=
  ⟨k0, k1, baseA σ, recvA S H T, 1, 1 / S⟩

variable {S H : K} {σ : ℕ} {T k0 k1 : K × K}

/-- The base guard at offset `t` on slot `σ`. -/
theorem copyPair_p (t : K) : (copyPair S H σ T k0 k1).p t = (27 * (σ : K) / 2 + t, 0) := by
  simp [CopyPair.p, copyPair, baseA]

/-- The receiver guard at offset `t`. -/
theorem copyPair_q (t : K) : (copyPair S H σ T k0 k1).q t = place S H (T.1 + t, T.2) := by
  simp only [CopyPair.q, copyPair, recvA, place, Prod.mk.injEq, and_true]
  ring

/-- The axis points of the corridor are crossing points of the copy pair. -/
theorem pairAxis_eq : pairAxis S H σ T k0 k1 =
    ((copyPair S H σ T k0 k1).X (3 / 2) (3 / 2), (copyPair S H σ T k0 k1).X 0 0) := by
  simp only [pairAxis, CopyPair.X, copyPair_p, copyPair_q, baseA, baseB, recvA, recvB,
    add_zero]
  rfl

end Generic

/-! ## Casting copy pairs from `ℚ` to `ℝ` -/

namespace CopyPair

/-- A rational copy pair viewed over `ℝ`. -/
def castR (C : CopyPair ℚ) : CopyPair ℝ :=
  ⟨ratPoint C.k0, ratPoint C.k1, ratPoint C.a0, ratPoint C.a1, C.s0, C.s1⟩

variable (C : CopyPair ℚ)

theorem castR_p (t : ℚ) : C.castR.p t = ratPoint (C.p t) := by
  simp [castR, p, ratPoint]

theorem castR_q (t : ℚ) : C.castR.q t = ratPoint (C.q t) := by
  simp [castR, q, ratPoint]

theorem castR_X (a b : ℚ) : C.castR.X a b = ratPoint (C.X a b) := by
  rw [X, X, ratPoint_lineInter, castR_p, castR_q]; rfl

theorem castR_L (z : ℚ × ℚ) : C.castR.L (ratPoint z) = C.L z := by
  simp only [L, castR, ← det_eq_det2, det_ratPoint]
  push_cast
  ring

theorem castR_hyp (h : C.Hyp) : C.castR.Hyp :=
  ⟨by simp [castR, ratPoint, h.hk], by simp [castR, h.hs0], by simp [castR, h.hs1]⟩

theorem castR_adm {ℓ : ℚ} (h : C.Adm ℓ) : C.castR.Adm (ℓ : ℝ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [p, q] at h1 h3
  refine ⟨by exact_mod_cast h0, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [castR, p, q, ratPoint]
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5

end CopyPair

/-! ## Validity of a corridor input -/

namespace Input

variable (I : Input)

/-- The hypotheses under which the corridor works (`N = max(4n + k, 2)`): the scale hypotheses,
at most three pairs, slots with `27σ/2 + 3/2 ≤ 14N`, receivers with `|T_τ.x|, |T_τ.y| ≤ 50` and
coordinate sums spaced by `27/2`. -/
structure Valid (N : ℚ) : Prop where
  /-- The scale hypotheses. -/
  scale : ScaleHyp N I.S I.H
  /-- At most three copied pairs. -/
  np_le : I.np ≤ 3
  /-- The copied slots lie in `[0, 14N]`. -/
  slot_le : ∀ k < I.np, 27 * (I.sigma k : ℚ) / 2 + 3 / 2 ≤ 14 * N
  /-- The receivers' template left endpoints lie in `[-50, 50]²`. -/
  T_bound : ∀ τ < I.np, -50 ≤ (I.Tt τ).1 ∧ (I.Tt τ).1 ≤ 50 ∧ -50 ≤ (I.Tt τ).2 ∧ (I.Tt τ).2 ≤ 50
  /-- Coordinate sums spaced by `27/2` (generalised Lemma 39). -/
  T_sum : ∀ τ < I.np, (I.Tt τ).1 + (I.Tt τ).2 = I.T0.1 + I.T0.2 - 27 * τ / 2

/-- The umbra copy pair of pair `k` (shadow corners `c0`, `c1`). -/
def umbraQ (k : ℕ) : CopyPair ℚ :=
  copyPair I.S I.H (I.sigma k) (I.Tt (I.tau k)) (c0 I.S I.H) (c1 I.S I.H)

/-- The nook copy pair of pair `k` (shadow corners `z0`, `z1`). -/
def nookQ (k : ℕ) : CopyPair ℚ :=
  copyPair I.S I.H (I.sigma k) (I.Tt (I.tau k)) (I.z0 k) (I.z1 k)

/-- The umbra copy pair over `ℝ`. -/
def umbraR (k : ℕ) : CopyPair ℝ := (I.umbraQ k).castR

/-- The nook copy pair over `ℝ`. -/
def nookR (k : ℕ) : CopyPair ℝ := (I.nookQ k).castR

theorem umbra_eq (k : ℕ) : I.umbra k = ((I.umbraQ k).X (3 / 2) (3 / 2), (I.umbraQ k).X 0 0) :=
  pairAxis_eq

theorem nook_eq (k : ℕ) : I.nook k = ((I.nookQ k).X (3 / 2) (3 / 2), (I.nookQ k).X 0 0) :=
  pairAxis_eq

theorem f0_eq (k : ℕ) : I.f0 k = (I.umbraQ k).X (3 / 2) (3 / 2) := by
  rw [f0, umbra_eq]

theorem f1_eq (k : ℕ) : I.f1 k = (I.umbraQ k).X 0 0 := by
  rw [f1, umbra_eq]

theorem F0_eq (k : ℕ) : I.F0 k = (I.nookQ k).X (3 / 2) (3 / 2) := by
  rw [F0, nook_eq]

theorem F1_eq (k : ℕ) : I.F1 k = (I.nookQ k).X 0 0 := by
  rw [F1, nook_eq]

/-- The real base guard of pair `k` at offset `t` (umbra pair). -/
theorem umbraR_p (k : ℕ) (t : ℝ) : (I.umbraR k).p t = (27 * (I.sigma k : ℝ) / 2 + t, 0) := by
  simp [umbraR, umbraQ, CopyPair.castR, CopyPair.p, copyPair, baseA, ratPoint]

/-- The real base guard of pair `k` at offset `t` (nook pair). -/
theorem nookR_p (k : ℕ) (t : ℝ) : (I.nookR k).p t = (27 * (I.sigma k : ℝ) / 2 + t, 0) := by
  simp [nookR, nookQ, CopyPair.castR, CopyPair.p, copyPair, baseA, ratPoint]

/-- The real receiver guard of pair `k` at offset `t` (umbra pair). -/
theorem umbraR_q (k : ℕ) (t : ℝ) : (I.umbraR k).q t =
    place (I.S : ℝ) (I.H : ℝ) (((I.Tt (I.tau k)).1 : ℝ) + t, ((I.Tt (I.tau k)).2 : ℝ)) := by
  simp only [umbraR, umbraQ, CopyPair.castR, CopyPair.q, copyPair, recvA, place, ratPoint,
    Prod.mk.injEq]
  push_cast
  constructor <;> first | trivial | ring

/-- The real receiver guard of pair `k` at offset `t` (nook pair). -/
theorem nookR_q (k : ℕ) (t : ℝ) : (I.nookR k).q t =
    place (I.S : ℝ) (I.H : ℝ) (((I.Tt (I.tau k)).1 : ℝ) + t, ((I.Tt (I.tau k)).2 : ℝ)) := by
  simp only [nookR, nookQ, CopyPair.castR, CopyPair.q, copyPair, recvA, place, ratPoint,
    Prod.mk.injEq]
  push_cast
  constructor <;> first | trivial | ring

theorem umbraR_k0 (k : ℕ) : (I.umbraR k).k0 = ratPoint (c0 I.S I.H) := rfl

theorem umbraR_k1 (k : ℕ) : (I.umbraR k).k1 = ratPoint (c1 I.S I.H) := rfl

theorem nookR_k0 (k : ℕ) : (I.nookR k).k0 = ratPoint (I.z0 k) := rfl

theorem nookR_k1 (k : ℕ) : (I.nookR k).k1 = ratPoint (I.z1 k) := rfl

/-! ### Bounds from validity -/

variable {I} {N : ℚ}

theorem Valid.S_pos (hv : I.Valid N) : 0 < I.S := hv.scale.S_pos

/-- `ε ≤ 1/(8·800000)`. -/
theorem Valid.eps_le (hv : I.Valid N) : 0 < I.ε ∧ I.ε ≤ 1 / 6400000 := by
  have := hv.scale.S_ge
  have hS := hv.S_pos
  simp only [Input.ε, eps]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- The left wall levels are tiny. -/
theorem Valid.Lw_bound (hv : I.Valid N) {k : ℕ} (hk : k < I.np) :
    -1 / 100 ≤ I.Lw k ∧ I.Lw k ≤ 1 / 100 := by
  have h := hv.scale
  have hS := h.S_pos
  have hS8 := h.S_ge
  have hN := h.two_le
  have hσ := hv.slot_le k hk
  have hσ0 : (0 : ℚ) ≤ I.sigma k := Nat.cast_nonneg _
  have e : I.Lw k = ((I.H - I.S) + 27 * (I.sigma k : ℚ) / 2 + 3 - 1 / 4) / I.S := by
    simp only [Lw, Zs, zetaO, delta, rho, Input.ε, eps]; field_simp; ring
  rw [e]
  have h1 : 0 ≤ (I.H - I.S) + 27 * (I.sigma k : ℚ) / 2 + 3 - 1 / 4 := by
    have := h.hH1; linarith
  have h2 : (I.H - I.S) + 27 * (I.sigma k : ℚ) / 2 + 3 - 1 / 4 ≤ 17 * N + 3 := by
    have := h.hH2; linarith
  constructor
  · have : 0 ≤ ((I.H - I.S) + 27 * (I.sigma k : ℚ) / 2 + 3 - 1 / 4) / I.S := by positivity
    linarith
  · rw [div_le_iff₀ hS]
    have := h.hS
    nlinarith

/-- The right wall levels are tiny. -/
theorem Valid.Rw_bound (hv : I.Valid N) {k : ℕ} (hk : k < I.np) :
    -1 / 100 ≤ I.Rw k ∧ I.Rw k ≤ 1 / 100 := by
  have h := hv.scale
  have hS := h.S_pos
  have hS8 := h.S_ge
  have h0 : 0 < I.np := by omega
  obtain ⟨b1, b2, b3, b4⟩ := hv.T_bound 0 h0
  have hτ : (I.tau k : ℚ) ≤ 2 := by
    have : I.tau k ≤ 2 := by simp only [tau]; have := hv.np_le; omega
    exact_mod_cast this
  have hτ0 : (0 : ℚ) ≤ I.tau k := Nat.cast_nonneg _
  have e : I.Rw k = (-(I.T0.1 + 3 / 2 + I.T0.2) + 27 * (I.tau k : ℚ) / 2 + 3 - 1 / 4) / I.S := by
    simp only [Rw, Xis, xiRef, delta, rho, Input.ε, eps]; field_simp; ring
  rw [e]
  simp only [T0] at *
  constructor
  · rw [le_div_iff₀ hS]; nlinarith
  · rw [div_le_iff₀ hS]; nlinarith

/-! ### The umbra pair -/

theorem umbraQ_hyp (hv : I.Valid N) (k : ℕ) : (I.umbraQ k).Hyp :=
  ⟨rfl, by simp [umbraQ, copyPair], by simp [umbraQ, copyPair]; exact hv.S_pos⟩

theorem umbraQ_adm (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.umbraQ k).Adm (3 / 2) := by
  have h := hv.scale
  have hS := h.S_pos
  have hS8 := h.S_ge
  have hN := h.two_le
  have hσ := hv.slot_le k hk
  have hτ : I.tau k < I.np := by simp only [tau]; omega
  obtain ⟨b1, b2, b3, b4⟩ := hv.T_bound _ hτ
  have hT1 : -1 / 2 ≤ (I.Tt (I.tau k)).1 / I.S := by rw [le_div_iff₀ hS]; linarith
  have hT2 : (I.Tt (I.tau k)).2 / I.S ≤ 1 / 2 := by rw [div_le_iff₀ hS]; linarith
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [umbraQ, copyPair, CopyPair.p, CopyPair.q, baseA, recvA, place, c0, c1, mul_zero,
      add_zero]
  · have := h.hS
    nlinarith
  · linarith
  · linarith
  · linarith [h.hH1]
  · linarith

theorem umbraR_hyp (hv : I.Valid N) (k : ℕ) : (I.umbraR k).Hyp :=
  (I.umbraQ k).castR_hyp (umbraQ_hyp hv k)

theorem umbraR_adm (hv : I.Valid N) {k : ℕ} (hk : k < I.np) :
    (I.umbraR k).Adm (3 / 2) := by
  have := (I.umbraQ k).castR_adm (umbraQ_adm hv hk)
  rw [show ((3 / 2 : ℚ) : ℝ) = 3 / 2 by norm_num] at this
  exact this

/-! ### The nook pair -/

theorem nookQ_hyp (hv : I.Valid N) (k : ℕ) : (I.nookQ k).Hyp :=
  ⟨by simp [nookQ, copyPair, z0, z1, ofLocal],
    by simp [nookQ, copyPair], by simp [nookQ, copyPair]; exact hv.S_pos⟩

/-- The nook mouth in closed form: `z0 = Oc + (yN − Lw, yN)`, `z1 = Oc + (Rw − yN, yN)` with
`yN = (Lw + Rw)/2 − 3ε`. -/
theorem yN_eq (k : ℕ) : I.yN k = (I.Lw k + I.Rw k) / 2 - 3 * I.ε := by
  simp only [yN, apex, ofZetaXi]; ring

theorem nookQ_adm (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.nookQ k).Adm (3 / 2) := by
  have h := hv.scale
  have hS := h.S_pos
  have hS8 := h.S_ge
  have hN := h.two_le
  have hσ := hv.slot_le k hk
  have hτ : I.tau k < I.np := by simp only [tau]; omega
  obtain ⟨b1, b2, b3, b4⟩ := hv.T_bound _ hτ
  have hT1 : -1 / 2 ≤ (I.Tt (I.tau k)).1 / I.S := by rw [le_div_iff₀ hS]; linarith
  have hT2 : (I.Tt (I.tau k)).2 / I.S ≤ 1 / 2 := by rw [div_le_iff₀ hS]; linarith
  obtain ⟨hL1, hL2⟩ := hv.Lw_bound hk
  obtain ⟨hR1, hR2⟩ := hv.Rw_bound hk
  obtain ⟨he1, he2⟩ := hv.eps_le
  have hy := I.yN_eq k
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [nookQ, copyPair, CopyPair.p, CopyPair.q, baseA, recvA, place, z0, z1, ofLocal,
      Input.O, Oc, mul_zero, add_zero]
  · have := h.hS
    nlinarith
  · linarith
  · linarith
  · linarith [h.hH1]
  · linarith

theorem nookR_hyp (hv : I.Valid N) (k : ℕ) : (I.nookR k).Hyp :=
  (I.nookQ k).castR_hyp (nookQ_hyp hv k)

theorem nookR_adm (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.nookR k).Adm (3 / 2) := by
  have := (I.nookQ k).castR_adm (nookQ_adm hv hk)
  rw [show ((3 / 2 : ℚ) : ℝ) = 3 / 2 by norm_num] at this
  exact this

/-! ### The axis vertices lie on the axes -/

/-- A point of the line through the two critical-segment ends lies on the axis. -/
theorem L_onLine_zero {C : CopyPair ℚ} (hC : C.Hyp) (hA : C.Adm (3 / 2)) (x : ℚ) :
    C.L (onLine (C.X (3 / 2) (3 / 2)) (C.X 0 0) x) = 0 := by
  have hlt := CopyPair.X_fst_lt hC hA (by norm_num)
  have hG0 := CopyPair.G_pos hC hA (t₀ := 0) (t₁ := 0) (by norm_num) le_rfl
  have hGl := CopyPair.G_pos hC hA (t₀ := 3 / 2) (t₁ := 3 / 2) le_rfl (by norm_num)
  apply C.L_eq_zero_of_det2 (C.L_X_diag hC.hk hGl.ne') (C.L_X_diag hC.hk hG0.ne')
  · intro he; rw [he] at hlt; exact lt_irrefl _ hlt
  · exact det2_onLine _ _ _ (by linarith)

/-- The stationary guard `p_k` lies on the umbra axis. -/
theorem umbra_L_sgPt (hv : I.Valid N) {k : ℕ} (hk : k < I.np) :
    (I.umbraQ k).L (I.sgPt k) = 0 := by
  rw [sgPt, onUmbra, f0_eq, f1_eq]
  exact L_onLine_zero (umbraQ_hyp hv k) (umbraQ_adm hv hk) _

/-- The vertex `z'_k` lies on the umbra axis. -/
theorem umbra_L_zp (hv : I.Valid N) {k : ℕ} (hk : k < I.np) :
    (I.umbraQ k).L (I.zp k) = 0 := by
  rw [zp, onUmbra, f0_eq, f1_eq]
  exact L_onLine_zero (umbraQ_hyp hv k) (umbraQ_adm hv hk) _

/-- The nook top-edge end `n0` lies on the nook axis. -/
theorem nook_L_n0 (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.nookQ k).L (I.n0 k) = 0 := by
  rw [n0, F0_eq, F1_eq]
  exact L_onLine_zero (nookQ_hyp hv k) (nookQ_adm hv hk) _

/-- The nook top-edge end `n1` lies on the nook axis. -/
theorem nook_L_n1 (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.nookQ k).L (I.n1 k) = 0 := by
  rw [n1, F0_eq, F1_eq]
  exact L_onLine_zero (nookQ_hyp hv k) (nookQ_adm hv hk) _

/-! ### The real critical segments -/

theorem umbraR_X (k : ℕ) (a b : ℚ) : (I.umbraR k).X a b = ratPoint ((I.umbraQ k).X a b) :=
  CopyPair.castR_X _ a b

theorem nookR_X (k : ℕ) (a b : ℚ) : (I.nookR k).X a b = ratPoint ((I.nookQ k).X a b) :=
  CopyPair.castR_X _ a b

/-- The umbra critical segment over `ℝ` is `[f1, f0]`. -/
theorem umbraR_f (k : ℕ) : (I.umbraR k).X (3 / 2) (3 / 2) = ratPoint (I.f0 k) ∧
    (I.umbraR k).X 0 0 = ratPoint (I.f1 k) := by
  constructor
  · have := I.umbraR_X k (3 / 2) (3 / 2); push_cast at this; rw [this, f0_eq]
  · have := I.umbraR_X k 0 0; push_cast at this; rw [this, f1_eq]

/-- The nook critical segment over `ℝ` is `[F1, F0]`. -/
theorem nookR_F (k : ℕ) : (I.nookR k).X (3 / 2) (3 / 2) = ratPoint (I.F0 k) ∧
    (I.nookR k).X 0 0 = ratPoint (I.F1 k) := by
  constructor
  · have := I.nookR_X k (3 / 2) (3 / 2); push_cast at this; rw [this, F0_eq]
  · have := I.nookR_X k 0 0; push_cast at this; rw [this, F1_eq]

theorem umbraR_L (k : ℕ) (z : ℚ × ℚ) : (I.umbraR k).L (ratPoint z) = (I.umbraQ k).L z :=
  CopyPair.castR_L _ z

theorem nookR_L (k : ℕ) (z : ℚ × ℚ) : (I.nookR k).L (ratPoint z) = (I.nookQ k).L z :=
  CopyPair.castR_L _ z

/-- The umbra axis points `X v v` (`v ∈ [0, 3/2]`) lie on the critical segment `[f1, f0]`. -/
theorem umbraR_X_mem (hv : I.Valid N) {k : ℕ} (hk : k < I.np) {v : ℝ} (h₀ : 0 ≤ v)
    (h₁ : v ≤ 3 / 2) : (I.umbraR k).X v v ∈ ArtGallery.segment (ratPoint (I.f1 k))
      (ratPoint (I.f0 k)) := by
  obtain ⟨hf0, hf1⟩ := I.umbraR_f k
  obtain ⟨α, hα0, hα1, he⟩ :=
    CopyPair.X_diag_mem (umbraR_hyp hv k) (umbraR_adm hv hk) (by norm_num) h₀ h₁
  rw [hf0, hf1] at he
  exact ⟨α, hα0, hα1, he⟩

/-- The nook axis points `X v v` (`v ∈ [0, 3/2]`) lie on the critical segment `[F1, F0]`. -/
theorem nookR_X_mem (hv : I.Valid N) {k : ℕ} (hk : k < I.np) {v : ℝ} (h₀ : 0 ≤ v)
    (h₁ : v ≤ 3 / 2) : (I.nookR k).X v v ∈ ArtGallery.segment (ratPoint (I.F1 k))
      (ratPoint (I.F0 k)) := by
  obtain ⟨hf0, hf1⟩ := I.nookR_F k
  obtain ⟨α, hα0, hα1, he⟩ :=
    CopyPair.X_diag_mem (nookR_hyp hv k) (nookR_adm hv hk) (by norm_num) h₀ h₁
  rw [hf0, hf1] at he
  exact ⟨α, hα0, hα1, he⟩

/-- Above the umbra axis means strictly left of the eastward critical segment `f0 → f1`. -/
theorem umbraR_L_pos_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) (z : Point) :
    0 < (I.umbraR k).L z ↔ 0 < ArtGallery.det (ratPoint (I.f0 k)) (ratPoint (I.f1 k)) z := by
  obtain ⟨hf0, hf1⟩ := I.umbraR_f k
  rw [det_eq_det2, ← hf0, ← hf1]
  exact CopyPair.L_pos_iff (umbraR_hyp hv k) (umbraR_adm hv hk) (by norm_num) z

/-- On or above the umbra axis means on or left of the line `f0 → f1`. -/
theorem umbraR_L_nonneg_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) (z : Point) :
    0 ≤ (I.umbraR k).L z ↔ 0 ≤ ArtGallery.det (ratPoint (I.f0 k)) (ratPoint (I.f1 k)) z := by
  obtain ⟨hf0, hf1⟩ := I.umbraR_f k
  rw [det_eq_det2, ← hf0, ← hf1]
  exact CopyPair.L_nonneg_iff (umbraR_hyp hv k) (umbraR_adm hv hk) (by norm_num) z

/-- Above the nook axis means strictly left of the eastward critical segment `F0 → F1`. -/
theorem nookR_L_pos_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) (z : Point) :
    0 < (I.nookR k).L z ↔ 0 < ArtGallery.det (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) z := by
  obtain ⟨hf0, hf1⟩ := I.nookR_F k
  rw [det_eq_det2, ← hf0, ← hf1]
  exact CopyPair.L_pos_iff (nookR_hyp hv k) (nookR_adm hv hk) (by norm_num) z

/-- On or above the nook axis means on or left of the line `F0 → F1`. -/
theorem nookR_L_nonneg_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) (z : Point) :
    0 ≤ (I.nookR k).L z ↔ 0 ≤ ArtGallery.det (ratPoint (I.F0 k)) (ratPoint (I.F1 k)) z := by
  obtain ⟨hf0, hf1⟩ := I.nookR_F k
  rw [det_eq_det2, ← hf0, ← hf1]
  exact CopyPair.L_nonneg_iff (nookR_hyp hv k) (nookR_adm hv hk) (by norm_num) z

/-- The umbra critical segment runs west to east: `f0.x < f1.x`. -/
theorem f0_fst_lt (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.f0 k).1 < (I.f1 k).1 := by
  rw [f0_eq, f1_eq]
  exact CopyPair.X_fst_lt (umbraQ_hyp hv k) (umbraQ_adm hv hk) (by norm_num)

/-- The nook critical segment runs west to east: `F0.x < F1.x`. -/
theorem F0_fst_lt (hv : I.Valid N) {k : ℕ} (hk : k < I.np) : (I.F0 k).1 < (I.F1 k).1 := by
  rw [F0_eq, F1_eq]
  exact CopyPair.X_fst_lt (nookQ_hyp hv k) (nookQ_adm hv hk) (by norm_num)

/-! ### The copy statements -/

/-- **Umbra copy (corridor).** For the real base guard `p t` on slot `σ_k` and the receiver
guard `q t'` (offsets in `[0, 3/2]`), the points `X v₀ v₁` (`0 ≤ v₁ ≤ v₀ ≤ 3/2`: the critical
segment `[f1, f0]` and the region just above it) all lie on the `p`-side of `p c0`
(`det(p, c0, ·) ≥ 0`) or on the `q`-side of `q c1` (`det(q, c1, ·) ≤ 0`) iff `t ≤ t'`. -/
theorem umbra_copy_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) {t t' : ℝ} (ht : t ≤ 3 / 2)
    (ht' : 0 ≤ t') :
    (∀ v₀ v₁ : ℝ, 0 ≤ v₁ → v₁ ≤ v₀ → v₀ ≤ 3 / 2 →
      (I.umbraR k).UmbraCovered t t' ((I.umbraR k).X v₀ v₁)) ↔ t ≤ t' :=
  CopyPair.umbra_iff (umbraR_hyp hv k) (umbraR_adm hv hk) ht ht'

/-- **Nook copy (corridor).** For the real base guard `p t` and receiver guard `q t'` (offsets in
`[0, 3/2]`), every point `X v v` (`v ∈ [0, 3/2]`) of the nook critical segment `[F1, F0]` lies on
the `p`-side of `p z0` (`det(p, z0, ·) ≤ 0`) or on the `q`-side of `q z1` (`det(q, z1, ·) ≥ 0`)
iff `t' ≤ t`. -/
theorem nook_copy_iff (hv : I.Valid N) {k : ℕ} (hk : k < I.np) {t t' : ℝ} (ht : 0 ≤ t)
    (ht' : t' ≤ 3 / 2) :
    (∀ v : ℝ, 0 ≤ v → v ≤ 3 / 2 → (I.nookR k).NookCovered t t' ((I.nookR k).X v v)) ↔
      t' ≤ t :=
  CopyPair.nook_iff (nookR_hyp hv k) (nookR_adm hv hk) ht ht'

end Input

end ArtGallery.Sec5.Corridor

end
