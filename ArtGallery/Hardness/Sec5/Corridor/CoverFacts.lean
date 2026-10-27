module

public import ArtGallery.Hardness.Sec5.Corridor.CoverTools
public import ArtGallery.Hardness.Sec5.Corridor.Receiver

/-!
# Section 5: corridors — facts for the coverage proof

* `I.cA a b c`: the affine constraint `a lX + b lY + c` in the local `ε`-coordinates
  (`lXR`, `lYR`) of the corridor.
* **Boundary check** (`Good.bd_check`): to show that every boundary point of the corridor polygon
  violates one of a list of constraints it suffices to treat the floor edges, the window, the
  entrance, the upper-wall vertices east of `p_k` and west of `nxt_k`, and the six upper-wall
  edges `p_k → z'_k → z1 → n1 → n0 → z0 → nxt_k` of one pair `k`.
* **The umbra axis function** `I.AR k z = D lY − h lX − 8 S g` (positive strictly above the axis
  `A_k`), with its approximation `(ℓ + r)/2 − 16` in the window (`Good.AR_eq`, `Good.AR_pos_of`,
  `Good.AR_neg_of`).
* Real local coordinates of the corridor vertices (`Good.rl_*`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-! ## Constraints in local coordinates -/

/-- The affine constraint `z ↦ a lX(z) + b lY(z) + c` (local `ε`-coordinates). -/
noncomputable def cA (I : Input) (a b c : ℝ) : Aff :=
  ⟨8 * (I.S : ℝ) * a, 8 * (I.S : ℝ) * b,
    c - 8 * (I.S : ℝ) * a * ((I.S : ℝ) + 1) - 8 * (I.S : ℝ) * b * ((I.H : ℝ) + 1)⟩

@[simp] theorem ev_cA (a b c : ℝ) (z : Point) :
    (I.cA a b c).ev z = a * I.lXR z + b * I.lYR z + c := by
  simp only [cA, Aff.ev, lXR, lYR]; ring

/-- `det` in local coordinates. -/
theorem det_lXR (p q z : Point) :
    64 * (I.S : ℝ) ^ 2 * ArtGallery.det p q z =
      (I.lXR q - I.lXR p) * (I.lYR z - I.lYR p) - (I.lXR z - I.lXR p) * (I.lYR q - I.lYR p) := by
  simp only [ArtGallery.det, lXR, lYR]; ring

theorem lXR_lt_iff' (hg : I.Good N) {p q : Point} : I.lXR p < I.lXR q ↔ p.1 < q.1 := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lXR]
  constructor <;> intro h <;> nlinarith

theorem lXR_le_iff' (hg : I.Good N) {p q : Point} : I.lXR p ≤ I.lXR q ↔ p.1 ≤ q.1 := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lXR]
  constructor <;> intro h <;> nlinarith

theorem lYR_le_iff' (hg : I.Good N) {p q : Point} : I.lYR p ≤ I.lYR q ↔ p.2 ≤ q.2 := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lYR]
  constructor <;> intro h <;> nlinarith

theorem lYR_le_floor_iff (hg : I.Good N) {p : Point} :
    I.lYR p ≤ -(8 * (I.S : ℝ)) ↔ p.2 ≤ (I.H : ℝ) := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lYR]
  constructor <;> intro h <;> nlinarith

theorem lXR_eq_iff' (hg : I.Good N) {p q : Point} : I.lXR p = I.lXR q ↔ p.1 = q.1 := by
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  simp only [lXR]
  constructor
  · intro h
    have : 8 * (I.S : ℝ) * (p.1 - q.1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · intro h; rw [h]

@[simp] theorem lXR_c1' : I.lXR (ratPoint (c1 I.S I.H)) = 8 * I.S := by
  simp [lXR, ratPoint, c1]; ring

@[simp] theorem lXR_d1' : I.lXR (ratPoint (d1 I.S I.H)) = 8 * I.S := by
  simp [lXR, ratPoint, d1]; ring

@[simp] theorem lXR_c0' : I.lXR (ratPoint (c0 I.S I.H)) = -(8 * I.S) := by
  simp [lXR, ratPoint, c0]

@[simp] theorem lXR_d0' : I.lXR (ratPoint (d0 I.S I.H)) = -(8 * I.S) := by
  simp [lXR, ratPoint, d0]

@[simp] theorem lYR_c1' : I.lYR (ratPoint (c1 I.S I.H)) = -(8 * I.S) := by
  simp [lYR, ratPoint, c1]

@[simp] theorem lYR_c0' : I.lYR (ratPoint (c0 I.S I.H)) = -(8 * I.S) := by
  simp [lYR, ratPoint, c0]

theorem lYR_d1' (hg : I.Good N) : I.lYR (ratPoint (d1 I.S I.H)) = -(8 * I.S) + 12 := by
  rw [lYR_ratPoint, lY_d1 hg]; push_cast; ring

theorem lYR_d0' (hg : I.Good N) : I.lYR (ratPoint (d0 I.S I.H)) = -(8 * I.S) + 24 := by
  rw [lYR_ratPoint, lY_d0 hg]; push_cast; ring

/-- Size of the scale. -/
theorem Good.S_big (hg : I.Good N) : (2 : ℝ) ≤ N ∧ (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 ∧
    100000 * (N : ℝ) ≤ I.S ∧ 400000 * (N : ℝ) ^ 2 ≤ 2 * I.S ∧ (0 : ℝ) < I.S ∧
    (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hS : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  have hSp : (0 : ℝ) < I.S := by rw [hS]; positivity
  refine ⟨hN, hS, by rw [hS]; nlinarith, by rw [hS]; nlinarith, hSp, by positivity⟩

/-- Dividing a sign condition by a positive factor. -/
theorem nonneg_of_mul_nonneg_c {c d : ℝ} (hc : 0 < c) (h : 0 ≤ c * d) : 0 ≤ d := by
  by_contra hd; push Not at hd; nlinarith

/-- Dividing a strict sign condition by a positive factor. -/
theorem pos_of_mul_pos_c {c d : ℝ} (hc : 0 < c) (h : 0 < c * d) : 0 < d := by
  by_contra hd; push Not at hd; nlinarith

/-! ## The boundary check -/

section Check

variable (hg : I.Good N)
include hg

omit hg in
/-- An edge of a list each of whose vertices satisfies a constraint weakly negatively. -/
theorem edges_ev_le {L : List Point} {f : Aff} (hL : ∀ v ∈ L, f.ev v ≤ 0) :
    ∀ e ∈ edgesOf L, ∀ w ∈ segOf e, f.ev w ≤ 0 := by
  intro e he w hw
  have hm := mem_of_mem_edgesOf he
  exact f.ev_le_of_segment hw (hL _ hm.1) (hL _ hm.2)

/-- **Boundary check.** -/
theorem Good.bd_check {k : ℕ} (hk : k < I.np) {fs : List Aff}
    (hfl : ∀ e ∈ edgesOf (I.chainBefore.map ratPoint), ∃ f ∈ fs,
      f.ev e.1 ≤ 0 ∧ f.ev e.2 ≤ 0)
    (hwin : ∃ f ∈ fs, f.ev (ratPoint (c1 I.S I.H)) ≤ 0 ∧ f.ev (ratPoint (d1 I.S I.H)) ≤ 0)
    (hent : ∃ f ∈ fs, f.ev (ratPoint (d0 I.S I.H)) ≤ 0 ∧ f.ev (ratPoint (c0 I.S I.H)) ≤ 0)
    (hE : ∃ f ∈ fs, ∀ v : ℚ × ℚ, (I.sgPt k).1 ≤ v.1 → f.ev (ratPoint v) ≤ 0)
    (hW : ∃ f ∈ fs, ∀ v : ℚ × ℚ, v.1 ≤ (I.nxt k).1 → f.ev (ratPoint v) ≤ 0)
    (h1 : ∃ f ∈ fs, f.ev (ratPoint (I.sgPt k)) ≤ 0 ∧ f.ev (ratPoint (I.zp k)) ≤ 0)
    (h2 : ∃ f ∈ fs, f.ev (ratPoint (I.zp k)) ≤ 0 ∧ f.ev (ratPoint (I.z1 k)) ≤ 0)
    (h3 : ∃ f ∈ fs, f.ev (ratPoint (I.z1 k)) ≤ 0 ∧ f.ev (ratPoint (I.n1 k)) ≤ 0)
    (h4 : ∃ f ∈ fs, f.ev (ratPoint (I.n1 k)) ≤ 0 ∧ f.ev (ratPoint (I.n0 k)) ≤ 0)
    (h5 : ∃ f ∈ fs, f.ev (ratPoint (I.n0 k)) ≤ 0 ∧ f.ev (ratPoint (I.z0 k)) ≤ 0)
    (h6 : ∃ f ∈ fs, f.ev (ratPoint (I.z0 k)) ≤ 0 ∧ f.ev (ratPoint (I.nxt k)) ≤ 0) :
    ∀ w ∈ I.poly.boundary, ∃ f ∈ fs, f.ev w ≤ 0 := by
  have edge2 : ∀ {a b w : Point}, w ∈ ArtGallery.segment a b →
      (∃ f ∈ fs, f.ev a ≤ 0 ∧ f.ev b ≤ 0) → ∃ f ∈ fs, f.ev w ≤ 0 := by
    intro a b w hw ⟨f, hf, ha, hb⟩
    exact ⟨f, hf, f.ev_le_of_segment hw ha hb⟩
  intro w hw
  rcases poly_boundary_cases hw with ⟨e, he, hwe⟩ | hw | ⟨e, he, hwe⟩ | hw
  · exact edge2 hwe (hfl e he)
  · exact edge2 hw hwin
  · obtain ⟨A₁, A₂, hA⟩ := chainAfter_inner hg hk
    have hmono := hg.xMonoQ_chainAfter
    rw [hA] at hmono he
    have hsplit : (A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂).map
        ratPoint = ((A₁ ++ [I.sgPt k]).map ratPoint) ++ ratPoint (I.zp k) ::
          ([ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k), ratPoint (I.z0 k)] ++
            ratPoint (I.nxt k) :: A₂.map ratPoint) := by simp
    rw [hsplit, edgesOf_append, List.mem_append] at he
    rcases he with he | he
    · -- east part: vertices weakly right of `p_k` (the last edge is `… → p_k → z'_k`)
      have hpre := XMonoQ.prefix_ge (A := A₁) (m := I.sgPt k)
        (B := [I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k, I.nxt k] ++ A₂) (by simpa using hmono)
      -- the edges of `A₁ ++ [p_k, z'_k]`
      rw [show (A₁ ++ [I.sgPt k]).map ratPoint ++ [ratPoint (I.zp k)] =
          (A₁.map ratPoint) ++ ratPoint (I.sgPt k) :: [ratPoint (I.zp k)] by simp,
        edgesOf_append, List.mem_append] at he
      rcases he with he | he
      · obtain ⟨f, hf, hfv⟩ := hE
        refine ⟨f, hf, edges_ev_le (L := A₁.map ratPoint ++ [ratPoint (I.sgPt k)]) ?_ e he w
          hwe⟩
        intro v hv
        rcases List.mem_append.1 hv with hv | hv
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv; exact hfv y (hpre y hy)
        · rw [List.mem_singleton] at hv; subst hv; exact hfv _ le_rfl
      · simp only [edgesOf_cons_cons, edgesOf_single, List.mem_cons, List.not_mem_nil,
          or_false] at he
        subst he; exact edge2 hwe h1
    rw [show ratPoint (I.zp k) :: ([ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k),
        ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint) =
        [ratPoint (I.zp k), ratPoint (I.z1 k), ratPoint (I.n1 k), ratPoint (I.n0 k),
          ratPoint (I.z0 k)] ++ ratPoint (I.nxt k) :: A₂.map ratPoint from rfl,
      edgesOf_append, List.mem_append] at he
    rcases he with he | he
    · simp only [List.cons_append, List.nil_append, edgesOf_cons_cons, edgesOf_single,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · exact edge2 hwe h2
      · exact edge2 hwe h3
      · exact edge2 hwe h4
      · exact edge2 hwe h5
      · exact edge2 hwe h6
    · -- west part: vertices weakly left of `nxt_k`
      have hsuf : XMonoQ (I.nxt k :: A₂) := by
        have := XMonoQ.of_append (A := A₁ ++ [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k])
          (B := I.nxt k :: A₂) (by simpa using hmono)
        exact this
      have hle := hsuf.le_head
      obtain ⟨f, hf, hfv⟩ := hW
      refine ⟨f, hf, edges_ev_le (L := ratPoint (I.nxt k) :: A₂.map ratPoint) ?_ e he w hwe⟩
      intro v hv
      rw [← List.map_cons] at hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      exact hfv y (hle y hy)
  · exact edge2 hw hent

/-- The floor part of the boundary check for constraints violated on and below the floor line. -/
theorem Good.floor_check {fs : List Aff} {f : Aff} (hf : f ∈ fs)
    (hfv : ∀ w : Point, w.2 ≤ (I.H : ℝ) → f.ev w ≤ 0) :
    ∀ e ∈ edgesOf (I.chainBefore.map ratPoint), ∃ f ∈ fs, f.ev e.1 ≤ 0 ∧ f.ev e.2 ≤ 0 := by
  intro e he
  refine ⟨f, hf, hfv _ ?_, hfv _ ?_⟩
  · exact hg.floor_edges_le he (Geometry.left_mem_segment _ _)
  · exact hg.floor_edges_le he (Geometry.right_mem_segment _ _)

end Check

/-! ## Real local coordinates of the vertices -/

/-- `ℓ_k` as a real number (`Lw_k` in `ε`-units). -/
noncomputable def lwR (I : Input) (k : ℕ) : ℝ := ((I.lwE k : ℚ) : ℝ)

/-- `r_k` as a real number (`Rw_k` in `ε`-units). -/
noncomputable def rwR (I : Input) (k : ℕ) : ℝ := ((I.rwE k : ℚ) : ℝ)

/-- The umbra axis function of pair `k` in `ε`-units, `D lY − h lX − 8 S g` (positive strictly
above the axis `A_k`). -/
noncomputable def AR (I : Input) (k : ℕ) (z : Point) : ℝ :=
  ((I.DD k : ℚ) : ℝ) * I.lYR z - ((I.hh k : ℚ) : ℝ) * I.lXR z - 8 * (I.S : ℝ) * ((I.gg k : ℚ) : ℝ)

theorem AR_lerp (k : ℕ) (p q : Point) (t : ℝ) :
    I.AR k (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) = I.AR k p + t * (I.AR k q - I.AR k p) := by
  simp only [AR, lXR, lYR]; ring

/-- `AR` as a constraint. -/
theorem AR_eq_cA (k : ℕ) (z : Point) :
    I.AR k z = (I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ)
      (-(8 * (I.S : ℝ) * ((I.gg k : ℚ) : ℝ)))).ev z := by
  rw [ev_cA, AR]; ring

section Coords

variable (hg : I.Good N)
include hg

/-- The real umbra axis function: `8 S² L(z) = AR(z)`. -/
theorem Good.umbraR_L_AR (k : ℕ) (z : Point) :
    8 * (I.S : ℝ) ^ 2 * (I.umbraR k).L z = I.AR k z := by
  have hS : (I.S : ℝ) ≠ 0 := by exact_mod_cast hg.S_pos.ne'
  simp only [umbraR, umbraQ, CopyPair.castR, copyPair, CopyPair.L, det2, AR, lXR, lYR, DD, hh, gg,
    eta, tu, tw, bx, ratPoint, baseA, recvA, place, c0, c1]
  push_cast
  field_simp
  ring

theorem Good.AR_ratPoint (k : ℕ) (z : ℚ × ℚ) :
    I.AR k (ratPoint z) = ((8 * I.S ^ 2 * (I.umbraQ k).L z : ℚ) : ℝ) := by
  have h := hg.umbraR_L_AR k (ratPoint z)
  rw [Input.umbraR_L] at h
  rw [← h]; push_cast; ring

variable {k : ℕ} (hk : k < I.np)
include hk

/-- **The axis function near the axis**: `AR = D (lY − ((ℓ+r)/2 − 16)) − h lX + E` with
`|E| ≤ 4 (17N + 100)(14N + 50)`, `S ≤ D ≤ 2S + 50`, `|h| ≤ 3N + 50`. -/
theorem Good.AR_eq (z : Point) :
    ∃ E : ℝ, I.AR k z = ((I.DD k : ℚ) : ℝ) * (I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16)) -
      ((I.hh k : ℚ) : ℝ) * I.lXR z + E ∧ |E| ≤ 4 * (17 * (N : ℝ) + 100) * (14 * N + 50) := by
  refine ⟨4 * ((I.gg k : ℚ) : ℝ) * (((I.tu k : ℚ) : ℝ) - ((I.bx k : ℚ) : ℝ)), ?_, ?_⟩
  · have e1 : (I.lwR k + I.rwR k) / 2 = 4 * ((I.gg k : ℚ) : ℝ) + 16 := by
      simp only [lwR, rwR]; rw [← Rat.cast_add, ← Rat.cast_ofNat, ← Rat.cast_div, lw_add_rw]
      push_cast; ring
    have e2 : ((I.DD k : ℚ) : ℝ) = 2 * (I.S : ℝ) + (I.tu k : ℝ) - (I.bx k : ℝ) := by
      simp only [DD]; push_cast; ring
    rw [AR, e1, e2]; ring
  · have hg' := hg.gg_abs hk
    have hu := hg.tu_bound hk
    have hb0 := hg.bx_nonneg k
    have hb1 := hg.bx_le hk
    have h1 : |((I.gg k : ℚ) : ℝ)| ≤ 17 * (N : ℝ) + 100 := by
      have : ((|I.gg k| : ℚ) : ℝ) ≤ ((17 * N + 100 : ℚ) : ℝ) := by exact_mod_cast hg'
      push_cast at this; exact this
    have h2 : |((I.tu k : ℚ) : ℝ) - ((I.bx k : ℚ) : ℝ)| ≤ 14 * (N : ℝ) + 50 := by
      have : |I.tu k - I.bx k| ≤ 14 * N + 50 := by
        rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      have : ((|I.tu k - I.bx k| : ℚ) : ℝ) ≤ ((14 * N + 50 : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢; exact this
    have hm := mul_le_mul h1 h2 (abs_nonneg _) (by linarith [abs_nonneg ((I.gg k : ℚ) : ℝ)])
    calc |4 * ((I.gg k : ℚ) : ℝ) * (((I.tu k : ℚ) : ℝ) - ((I.bx k : ℚ) : ℝ))|
        = 4 * (|((I.gg k : ℚ) : ℝ)| * |((I.tu k : ℚ) : ℝ) - ((I.bx k : ℚ) : ℝ)|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; ring
      _ ≤ 4 * ((17 * (N : ℝ) + 100) * (14 * N + 50)) := by gcongr
      _ = 4 * (17 * (N : ℝ) + 100) * (14 * N + 50) := by ring

theorem Good.DDR_bounds : (I.S : ℝ) ≤ ((I.DD k : ℚ) : ℝ) ∧ ((I.DD k : ℚ) : ℝ) ≤ 2 * I.S + 50 := by
  have h1 := hg.DD_pos hk
  have hu := hg.tu_bound hk
  have hb0 := hg.bx_nonneg k
  constructor
  · exact_mod_cast h1
  · have : I.DD k ≤ 2 * I.S + 50 := by simp only [DD]; linarith [hu.2]
    exact_mod_cast this

theorem Good.hhR_abs : |((I.hh k : ℚ) : ℝ)| ≤ 3 * (N : ℝ) + 50 := by
  have : ((|I.hh k| : ℚ) : ℝ) ≤ ((3 * N + 50 : ℚ) : ℝ) := by exact_mod_cast hg.hh_abs hk
  push_cast at this; exact this

/-- Strictly above `(ℓ+r)/2 − 16 + 1/8` in the window: above the axis. -/
theorem Good.AR_pos_of {z : Point} (hX : |I.lXR z| ≤ 456 * N)
    (hY : (I.lwR k + I.rwR k) / 2 - 16 + 1 / 8 < I.lYR z) : 0 < I.AR k z := by
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk z
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hS : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  have hhX : |((I.hh k : ℚ) : ℝ) * I.lXR z| ≤ (3 * N + 50) * (456 * N) := by
    rw [abs_mul]; exact mul_le_mul hh hX (abs_nonneg _) (by linarith)
  rw [abs_le] at hEb hhX
  have hpos : (I.S : ℝ) / 8 < ((I.DD k : ℚ) : ℝ) * (I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16)) := by
    have : (1 : ℝ) / 8 < I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16) := by linarith
    have hSp : (0 : ℝ) < I.S := by rw [hS]; positivity
    nlinarith [mul_pos (show (0 : ℝ) < ((I.DD k : ℚ) : ℝ) by linarith) (sub_pos.2 this)]
  rw [hE]; nlinarith

/-- Strictly below `(ℓ+r)/2 − 16 − 1/8` in the window: below the axis. -/
theorem Good.AR_neg_of {z : Point} (hX : |I.lXR z| ≤ 456 * N)
    (hY : I.lYR z < (I.lwR k + I.rwR k) / 2 - 16 - 1 / 8) : I.AR k z < 0 := by
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk z
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have hS : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  have hhX : |((I.hh k : ℚ) : ℝ) * I.lXR z| ≤ (3 * N + 50) * (456 * N) := by
    rw [abs_mul]; exact mul_le_mul hh hX (abs_nonneg _) (by linarith)
  rw [abs_le] at hEb hhX
  have hneg : ((I.DD k : ℚ) : ℝ) * (I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16)) < -(I.S : ℝ) / 8 := by
    have : I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16) < -(1 : ℝ) / 8 := by linarith
    have hSp : (0 : ℝ) < I.S := by rw [hS]; positivity
    nlinarith [mul_pos (show (0 : ℝ) < ((I.DD k : ℚ) : ℝ) by linarith)
      (show (0 : ℝ) < -(1 / 8) - (I.lYR z - ((I.lwR k + I.rwR k) / 2 - 16)) by linarith)]
  rw [hE]; nlinarith

theorem Good.rl_z1 : I.lXR (ratPoint (I.z1 k)) = (I.rwR k - I.lwR k) / 2 + 3 ∧
    I.lYR (ratPoint (I.z1 k)) = (I.lwR k + I.rwR k) / 2 - 3 := by
  rw [lXR_ratPoint, lYR_ratPoint, lX_z1 hg hk, lY_z1 hg hk, lwR, rwR]; push_cast; constructor <;> ring

theorem Good.rl_z0 : I.lXR (ratPoint (I.z0 k)) = (I.rwR k - I.lwR k) / 2 - 3 ∧
    I.lYR (ratPoint (I.z0 k)) = (I.lwR k + I.rwR k) / 2 - 3 := by
  rw [lXR_ratPoint, lYR_ratPoint, lX_z0 hg hk, lY_z0 hg hk, lwR, rwR]; push_cast; constructor <;> ring

theorem Good.rl_n1 : I.lXR (ratPoint (I.n1 k)) = (I.rwR k - I.lwR k) / 2 + 3 ∧
    |I.lYR (ratPoint (I.n1 k)) - ((I.lwR k + I.rwR k) / 2 - 1)| ≤ 1 / 8 := by
  refine ⟨by rw [lXR_ratPoint, lX_n1, lX_z1 hg hk, lwR, rwR]; push_cast; ring, ?_⟩
  have := hg.lY_n1 hk
  rw [lYR_ratPoint, lwR, rwR]
  have : ((|I.lY (I.n1 k) - ((I.lwE k + I.rwE k) / 2 - 1)| : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by
    exact_mod_cast this
  push_cast at this; exact this

theorem Good.rl_n0 : I.lXR (ratPoint (I.n0 k)) = (I.rwR k - I.lwR k) / 2 - 3 ∧
    |I.lYR (ratPoint (I.n0 k)) - ((I.lwR k + I.rwR k) / 2 + 1)| ≤ 1 / 8 := by
  refine ⟨by rw [lXR_ratPoint, lX_n0, lX_z0 hg hk, lwR, rwR]; push_cast; ring, ?_⟩
  have := hg.lY_n0 hk
  rw [lYR_ratPoint, lwR, rwR]
  have : ((|I.lY (I.n0 k) - ((I.lwE k + I.rwE k) / 2 + 1)| : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by
    exact_mod_cast this
  push_cast at this; exact this

theorem Good.rl_zp : |I.lXR (ratPoint (I.zp k)) - ((I.rwR k - I.lwR k) / 2 + 16 + 3 / 16)| ≤ 3 / 16 ∧
    |I.lYR (ratPoint (I.zp k)) - ((I.lwR k + I.rwR k) / 2 - 16)| ≤ 1 / 8 ∧
    I.rwR k + 1 / 16 ≤ I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k)) ∧
    I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k)) ≤ I.rwR k + 5 / 16 ∧
    I.AR k (ratPoint (I.zp k)) = 0 := by
  have h1 := hg.lX_zp hk
  have h2 := hg.lY_zp hk
  have h3 := hg.xi_zp hk
  rw [lXR_ratPoint, lYR_ratPoint, lwR, rwR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ((|I.lX (I.zp k) - ((I.rwE k - I.lwE k) / 2 + 16 + 3 / 16)| : ℚ) : ℝ) ≤
        ((3 / 16 : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; exact this
  · have : ((|I.lY (I.zp k) - ((I.lwE k + I.rwE k) / 2 - 16)| : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by
      exact_mod_cast h2
    push_cast at this; exact this
  · have := rat_cast_le_of h3.1; push_cast at this; exact this
  · have := rat_cast_le_of h3.2; push_cast at this; exact this
  · rw [hg.AR_ratPoint, umbra_L_zp hg.toValid hk]; simp

theorem Good.AR_sgPt : I.AR k (ratPoint (I.sgPt k)) = 0 := by
  rw [hg.AR_ratPoint, umbra_L_sgPt hg.toValid hk]; simp

omit hg hk in
theorem rl_sgPt_zero : I.lXR (ratPoint (I.sgPt 0)) = 8 * I.S := by
  rw [lXR_ratPoint, lX_sgPt_zero]; push_cast; ring

theorem Good.rl_sgPt (hk1 : 1 ≤ k) :
    I.lXR (ratPoint (I.sgPt k)) = (I.rwR k - I.lwR (k - 1)) / 2 + 1 / 4 ∧
    |I.lYR (ratPoint (I.sgPt k)) - ((I.lwR k + I.rwR k) / 2 - 16)| ≤ 1 / 8 := by
  refine ⟨by rw [lXR_ratPoint, lX_sgPt hg hk hk1, lwR, rwR]; push_cast; ring, ?_⟩
  have := hg.lY_sgPt hk hk1
  rw [lYR_ratPoint, lwR, rwR]
  have : ((|I.lY (I.sgPt k) - ((I.lwE k + I.rwE k) / 2 - 16)| : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by
    exact_mod_cast this
  push_cast at this; exact this

theorem Good.rl_valley (_hk1 : 1 ≤ k) :
    I.lXR (ratPoint (I.valley k)) = (I.rwR k - I.lwR (k - 1)) / 2 + 1 / 4 ∧
    I.lYR (ratPoint (I.valley k)) = (I.rwR k + I.lwR (k - 1)) / 2 + 1 / 4 := by
  rw [lXR_ratPoint, lYR_ratPoint, lX_valley hg hk, lY_valley hg hk, lwR, rwR]
  push_cast; constructor <;> ring

end Coords

end Input

end ArtGallery.Sec5.Corridor

end
