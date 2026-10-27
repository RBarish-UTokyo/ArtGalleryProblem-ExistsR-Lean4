module

public import ArtGallery.Geometry.SpecExtra
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.List.Sort

/-!
# Section 5: corridors — definitions

The corridor of one unit (docs/section5/04_corridor.md), in the right-side working frame.

* **Generic planar primitives** over an arbitrary field `K`: the determinant `det2` (equal to
  `ArtGallery.det` on `ℝ × ℝ`), the intersection `lineInter a b c d` of the lines `ab` and `cd`
  with its characterising lemmas, the point `onLine f₀ f₁ x` of the line `f₀f₁` with abscissa
  `x`, and the local coordinates `ζ = Y − X`, `ξ = Y + X` relative to an origin `O`.
* **Corridor parameters** (generic): `ρ = 3/(2S)`, `δ = 9ρ`, `ε = 1/(8S)`, the corners
  `c0 = (S, H)`, `c1 = c0 + (2, 0)`, `d0 = c0 + (0, 2ρ)`, `d1 = c1 + (0, ρ)`, the local origin
  `Oc = c0 + (1, 1)`, the gadget point `m = c1 + (1, −1)`, base segments `s_σ = [a_σ, b_σ]`,
  receiver segments `r_τ = [m + T_τ/S, m + T_τ/S + (3/(2S), 0)]`, and the slab centres
  `Z(σ, γ) = (H − S)/S + σδ + γρ`, `Ξ(τ, γ) = −(T₀.x + 3/2 + T₀.y)/S + τδ + γρ`.
* **The corridor** (over `ℚ`, computable) for an `Input` (`S`, `H`, the increasing working slots,
  the template left endpoints `T_τ` of the receivers): per pair `k` (slot `σ_k`,
  `τ_k = p − 1 − k`) the apex, umbra axis `(f0, f1)`, stationary guard `sgPt`, `zp`, valley,
  nook mouth `z0, z1`, nook axis `(F0, F1)`, nook top edge `n0, n1`, the two floor witness slots;
  and the chains `chainBefore = c0, floor…, c1` and `chainAfter = d1, upper…, d0`.

The only non-field operation is the ceiling `⌈·⌉` used to put `zp` on the grid (rounding up plus
one grid unit, `Corridor.grid_x_up`).  (`roundHalfEven`, rounding half to even, is kept for the
nearest-grid-point helper `gridX`.)
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

/-! ## Generic planar primitives -/

section Generic

variable {K : Type*} [Field K]

/-- Twice the signed area of the triangle `a b c` (positive iff `c` is strictly left of the
directed line `a → b`); `ArtGallery.det` is the case `K = ℝ`. -/
def det2 (a b c : K × K) : K :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/-- The cross product of the directions of the lines `ab` and `cd`; nonzero iff the lines are
not parallel (and both are proper lines). -/
def lineDen (a b c d : K × K) : K :=
  (b.1 - a.1) * (d.2 - c.2) - (b.2 - a.2) * (d.1 - c.1)

/-- The intersection point of the lines `ab` and `cd` (`geom.line_inter`): `a + t (b − a)` with
`t = (c − a) × (d − c) / ((b − a) × (d − c))`.  Meaningful when `lineDen a b c d ≠ 0`. -/
def lineInter (a b c d : K × K) : K × K :=
  let t := ((c.1 - a.1) * (d.2 - c.2) - (c.2 - a.2) * (d.1 - c.1)) / lineDen a b c d
  (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

/-- The point of the line `f₀ f₁` with abscissa `x` (`Corridor.on_line`); meaningful when the
line is not vertical. -/
def onLine (f₀ f₁ : K × K) (x : K) : K × K :=
  (x, f₀.2 + (x - f₀.1) * (f₁.2 - f₀.2) / (f₁.1 - f₀.1))

/-- The local coordinate `ζ = Y − X` of `z` relative to the origin `O` (constant along lines of
slope `+1`). -/
def zetaOf (O z : K × K) : K := (z.2 - O.2) - (z.1 - O.1)

/-- The local coordinate `ξ = Y + X` of `z` relative to the origin `O` (constant along lines of
slope `−1`). -/
def xiOf (O z : K × K) : K := (z.2 - O.2) + (z.1 - O.1)

/-- The point with local coordinates `(ζ, ξ)` relative to `O` (`Corridor.xy`). -/
def ofZetaXi (O : K × K) (ζ ξ : K) : K × K := (O.1 + (ξ - ζ) / 2, O.2 + (ξ + ζ) / 2)

/-- The point with local Cartesian coordinates `(X, Y)` relative to `O` (`Corridor.rel`). -/
def ofLocal (O : K × K) (X Y : K) : K × K := (O.1 + X, O.2 + Y)

theorem det2_def (a b c : K × K) :
    det2 a b c = (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) := rfl

/-- `ArtGallery.det` is `det2` on `ℝ × ℝ`. -/
theorem det_eq_det2 (a b c : Point) : ArtGallery.det a b c = det2 a b c := rfl

/-- The intersection point lies on the first line. -/
theorem det2_lineInter_left (a b c d : K × K) : det2 a b (lineInter a b c d) = 0 := by
  simp only [lineInter]
  generalize (_ / lineDen a b c d) = t
  simp only [det2]
  ring

/-- The intersection point lies on the second line. -/
theorem det2_lineInter_right (a b c d : K × K) (h : lineDen a b c d ≠ 0) :
    det2 c d (lineInter a b c d) = 0 := by
  simp only [lineInter]
  set N := (c.1 - a.1) * (d.2 - c.2) - (c.2 - a.2) * (d.1 - c.1)
  have key : ∀ t : K, det2 c d (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) =
      N - t * lineDen a b c d := by
    intro t; simp only [det2, lineDen, N]; ring
  rw [key, div_mul_cancel₀ _ h, sub_self]

/-- **Characterisation of `lineInter`.** If the lines are not parallel, the intersection point
is the unique point on both lines. -/
theorem eq_lineInter {a b c d z : K × K} (h : lineDen a b c d ≠ 0) (h₁ : det2 a b z = 0)
    (h₂ : det2 c d z = 0) : z = lineInter a b c d := by
  obtain ⟨z1, z2⟩ := z
  simp only [det2] at h₁ h₂
  simp only [lineInter, Prod.mk.injEq]
  have k1 : lineDen a b c d * z1 = lineDen a b c d * a.1 +
      ((c.1 - a.1) * (d.2 - c.2) - (c.2 - a.2) * (d.1 - c.1)) * (b.1 - a.1) := by
    simp only [lineDen]
    linear_combination (d.1 - c.1) * h₁ + (a.1 - b.1) * h₂
  have k2 : lineDen a b c d * z2 = lineDen a b c d * a.2 +
      ((c.1 - a.1) * (d.2 - c.2) - (c.2 - a.2) * (d.1 - c.1)) * (b.2 - a.2) := by
    simp only [lineDen]
    linear_combination (d.2 - c.2) * h₁ + (a.2 - b.2) * h₂
  constructor
  · field_simp
    linear_combination k1
  · field_simp
    linear_combination k2

/-- `onLine f₀ f₁ x` lies on the line `f₀ f₁` (when it is not vertical). -/
theorem det2_onLine (f₀ f₁ : K × K) (x : K) (h : f₁.1 - f₀.1 ≠ 0) :
    det2 f₀ f₁ (onLine f₀ f₁ x) = 0 := by
  simp only [det2, onLine]
  field_simp
  ring

/-- The first coordinate of `onLine`. -/
@[simp] theorem onLine_fst (f₀ f₁ : K × K) (x : K) : (onLine f₀ f₁ x).1 = x := rfl

/-- A point of a non-vertical line is determined by its abscissa. -/
theorem eq_onLine {f₀ f₁ z : K × K} (h : f₁.1 - f₀.1 ≠ 0) (hz : det2 f₀ f₁ z = 0) :
    z = onLine f₀ f₁ z.1 := by
  obtain ⟨z1, z2⟩ := z
  simp only [det2] at hz
  simp only [onLine, Prod.mk.injEq, true_and]
  field_simp
  linear_combination hz

@[simp] theorem zetaOf_ofZetaXi [CharZero K] (O : K × K) (ζ ξ : K) : zetaOf O (ofZetaXi O ζ ξ) = ζ := by
  simp only [zetaOf, ofZetaXi]; field_simp; ring

@[simp] theorem xiOf_ofZetaXi [CharZero K] (O : K × K) (ζ ξ : K) : xiOf O (ofZetaXi O ζ ξ) = ξ := by
  simp only [xiOf, ofZetaXi]; field_simp; ring

@[simp] theorem zetaOf_ofLocal (O : K × K) (X Y : K) : zetaOf O (ofLocal O X Y) = Y - X := by
  simp only [zetaOf, ofLocal]; ring

@[simp] theorem xiOf_ofLocal (O : K × K) (X Y : K) : xiOf O (ofLocal O X Y) = Y + X := by
  simp only [xiOf, ofLocal]; ring

/-- Every point is the point with its own local coordinates. -/
theorem ofZetaXi_zetaOf_xiOf [CharZero K] (O z : K × K) :
    ofZetaXi O (zetaOf O z) (xiOf O z) = z := by
  obtain ⟨z1, z2⟩ := z
  simp only [ofZetaXi, zetaOf, xiOf, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

end Generic

/-! ### Casting from `ℚ` to `ℝ` -/

section Cast

@[simp] theorem ratPoint_fst (p : ℚ × ℚ) : (ratPoint p).1 = (p.1 : ℝ) := rfl

@[simp] theorem ratPoint_snd (p : ℚ × ℚ) : (ratPoint p).2 = (p.2 : ℝ) := rfl

theorem det_ratPoint (a b c : ℚ × ℚ) :
    ArtGallery.det (ratPoint a) (ratPoint b) (ratPoint c) = ((det2 a b c : ℚ) : ℝ) := by
  simp only [det_eq_det2, det2, ratPoint]
  push_cast
  ring

theorem lineDen_ratPoint (a b c d : ℚ × ℚ) :
    lineDen (ratPoint a) (ratPoint b) (ratPoint c) (ratPoint d) =
      ((lineDen a b c d : ℚ) : ℝ) := by
  simp only [lineDen, ratPoint]
  push_cast
  ring

theorem ratPoint_lineInter (a b c d : ℚ × ℚ) :
    ratPoint (lineInter a b c d) =
      lineInter (ratPoint a) (ratPoint b) (ratPoint c) (ratPoint d) := by
  simp only [lineInter, lineDen, ratPoint]
  push_cast
  rfl

theorem ratPoint_onLine (f₀ f₁ : ℚ × ℚ) (x : ℚ) :
    ratPoint (onLine f₀ f₁ x) = onLine (ratPoint f₀) (ratPoint f₁) (x : ℝ) := by
  simp only [onLine, ratPoint]
  push_cast
  rfl

theorem ratPoint_ofZetaXi (O : ℚ × ℚ) (ζ ξ : ℚ) :
    ratPoint (ofZetaXi O ζ ξ) = ofZetaXi (ratPoint O) (ζ : ℝ) (ξ : ℝ) := by
  simp only [ofZetaXi, ratPoint]
  push_cast
  rfl

theorem ratPoint_ofLocal (O : ℚ × ℚ) (X Y : ℚ) :
    ratPoint (ofLocal O X Y) = ofLocal (ratPoint O) (X : ℝ) (Y : ℝ) := by
  simp only [ofLocal, ratPoint]
  push_cast
  rfl

theorem zetaOf_ratPoint (O z : ℚ × ℚ) :
    zetaOf (ratPoint O) (ratPoint z) = ((zetaOf O z : ℚ) : ℝ) := by
  simp only [zetaOf, ratPoint]; push_cast; ring

theorem xiOf_ratPoint (O z : ℚ × ℚ) :
    xiOf (ratPoint O) (ratPoint z) = ((xiOf O z : ℚ) : ℝ) := by
  simp only [xiOf, ratPoint]; push_cast; ring

end Cast

/-! ## Corridor parameters (generic) -/

section Params

variable {K : Type*} [Field K]

/-- `ρ = 3/(2S)`: the slab spacing inside a group. -/
def rho (S : K) : K := 3 / (2 * S)

/-- `δ = 9ρ = 27/(2S)`: the spacing of slab groups. -/
def delta (S : K) : K := 27 / (2 * S)

/-- `ε = ρ/12 = 1/(8S)`: the slab half-width. -/
def eps (S : K) : K := 1 / (8 * S)

/-- The corner `c0 = (S, H)` (left end of the corridor floor). -/
def c0 (S H : K) : K × K := (S, H)

/-- The corner `c1 = c0 + (2, 0)` (right end of the corridor floor). -/
def c1 (S H : K) : K × K := (S + 2, H)

/-- The corner `d0 = c0 + (0, 2ρ)` (top of the left entrance). -/
def d0 (S H : K) : K × K := (S, H + 2 * rho S)

/-- The corner `d1 = c1 + (0, ρ)` (top of the right entrance). -/
def d1 (S H : K) : K × K := (S + 2, H + rho S)

/-- The local origin `Oc = c0 + (1, 1)`. -/
def Oc (S H : K) : K × K := (S + 1, H + 1)

/-- The gadget point `m = c1 + (1, −1)`; a template point `T` is placed at `m + T/S`. -/
def mPt (S H : K) : K × K := (S + 3, H - 1)

/-- The template point `T` placed in the unit: `m + T/S`. -/
def place (S H : K) (T : K × K) : K × K := (S + 3 + T.1 / S, H - 1 + T.2 / S)

/-- Left endpoint `a_σ = (27σ/2, 0)` of the base segment `s_σ`. -/
def baseA (σ : ℕ) : K × K := (27 * (σ : K) / 2, 0)

/-- Right endpoint `b_σ = a_σ + (3/2, 0)` of the base segment `s_σ`. -/
def baseB (σ : ℕ) : K × K := (27 * (σ : K) / 2 + 3 / 2, 0)

/-- Left endpoint `a'_τ = m + T_τ/S` of the receiver segment with template left endpoint `T`. -/
def recvA (S H : K) (T : K × K) : K × K := place S H T

/-- Right endpoint `b'_τ = a'_τ + (3/(2S), 0)` of the receiver segment. -/
def recvB (S H : K) (T : K × K) : K × K := place S H (T.1 + 3 / 2, T.2)

/-- `ζ_o = (H − S)/S`, the `ζ`-value of `o = ray(a_0, c0) ∩ {X = 0}`. -/
def zetaO (S H : K) : K := (H - S) / S

/-- The L-slab centre `Z(σ, γ) = ζ_o + σδ + γρ` (a `ζ`-value). -/
def Zs (S H : K) (σ : ℕ) (γ : K) : K := zetaO S H + (σ : K) * delta S + γ * rho S

/-- `ξ_ref = −(T₀.x + 3/2 + T₀.y)/S`: the `ξ`-value at `X = 0` (to first order) of the line from
the right endpoint of receiver `0` through `c1`. -/
def xiRef (S : K) (T₀ : K × K) : K := -(T₀.1 + 3 / 2 + T₀.2) / S

/-- The R-slab centre `Ξ(τ, γ) = ξ_ref + τδ + γρ` (a `ξ`-value). -/
def Xis (S : K) (T₀ : K × K) (τ : ℕ) (γ : K) : K := xiRef S T₀ + (τ : K) * delta S + γ * rho S

/-- The two crossing points `(f0, f1)` defining the perspective axis of the pair
(base slot `σ`, receiver with template left endpoint `T`) for the shadow corners `k0`
(base side) and `k1` (gadget side): `f0 = (b_σ k0) ∩ (b'_τ k1)`, `f1 = (a_σ k0) ∩ (a'_τ k1)`
(`Corridor.axis`). -/
def pairAxis (S H : K) (σ : ℕ) (T k0 k1 : K × K) : (K × K) × (K × K) :=
  (lineInter (baseB σ) k0 (recvB S H T) k1, lineInter (baseA σ) k0 (recvA S H T) k1)

end Params

/-! ### Casts of the parameters -/

section ParamsCast

theorem ratPoint_c0 (S H : ℚ) : ratPoint (c0 S H) = c0 (S : ℝ) (H : ℝ) := rfl

theorem ratPoint_c1 (S H : ℚ) : ratPoint (c1 S H) = c1 (S : ℝ) (H : ℝ) := by
  simp [ratPoint, c1]

theorem ratPoint_d0 (S H : ℚ) : ratPoint (d0 S H) = d0 (S : ℝ) (H : ℝ) := by
  simp [ratPoint, d0, rho]

theorem ratPoint_d1 (S H : ℚ) : ratPoint (d1 S H) = d1 (S : ℝ) (H : ℝ) := by
  simp [ratPoint, d1, rho]

theorem ratPoint_Oc (S H : ℚ) : ratPoint (Oc S H) = Oc (S : ℝ) (H : ℝ) := by
  simp [ratPoint, Oc]

theorem ratPoint_place (S H : ℚ) (T : ℚ × ℚ) :
    ratPoint (place S H T) = place (S : ℝ) (H : ℝ) (ratPoint T) := by
  simp [ratPoint, place]

theorem ratPoint_baseA (σ : ℕ) : ratPoint (baseA σ) = baseA (K := ℝ) σ := by
  simp [ratPoint, baseA]

theorem ratPoint_baseB (σ : ℕ) : ratPoint (baseB σ) = baseB (K := ℝ) σ := by
  simp [ratPoint, baseB]

theorem ratPoint_recvA (S H : ℚ) (T : ℚ × ℚ) :
    ratPoint (recvA S H T) = recvA (S : ℝ) (H : ℝ) (ratPoint T) := ratPoint_place S H T

theorem ratPoint_recvB (S H : ℚ) (T : ℚ × ℚ) :
    ratPoint (recvB S H T) = recvB (S : ℝ) (H : ℝ) (ratPoint T) := by
  simp [recvB, place, ratPoint]

theorem cast_rho (S : ℚ) : ((rho S : ℚ) : ℝ) = rho (S : ℝ) := by simp [rho]

theorem cast_delta (S : ℚ) : ((delta S : ℚ) : ℝ) = delta (S : ℝ) := by simp [delta]

theorem cast_eps (S : ℚ) : ((eps S : ℚ) : ℝ) = eps (S : ℝ) := by simp [eps]

theorem cast_Zs (S H : ℚ) (σ : ℕ) (γ : ℚ) :
    ((Zs S H σ γ : ℚ) : ℝ) = Zs (S : ℝ) (H : ℝ) σ (γ : ℝ) := by
  simp [Zs, zetaO, delta, rho]

theorem cast_Xis (S : ℚ) (T₀ : ℚ × ℚ) (τ : ℕ) (γ : ℚ) :
    ((Xis S T₀ τ γ : ℚ) : ℝ) = Xis (S : ℝ) (ratPoint T₀) τ (γ : ℝ) := by
  simp [Xis, xiRef, delta, rho, ratPoint]

theorem ratPoint_pairAxis (S H : ℚ) (σ : ℕ) (T k0 k1 : ℚ × ℚ) :
    Prod.map ratPoint ratPoint (pairAxis S H σ T k0 k1) =
      pairAxis (S : ℝ) (H : ℝ) σ (ratPoint T) (ratPoint k0) (ratPoint k1) := by
  simp only [pairAxis, Prod.map, ratPoint_lineInter, ratPoint_baseA, ratPoint_baseB,
    ratPoint_recvA, ratPoint_recvB]

end ParamsCast

/-! ## Rounding half to even -/

/-- `round(q)` for a fraction: the nearest integer, ties to the even one. -/
def roundHalfEven (q : ℚ) : ℤ :=
  let fl := q.num / (q.den : ℤ)
  let r := q.num % (q.den : ℤ)
  if 2 * r < q.den then fl
  else if 2 * r > q.den then fl + 1
  else if fl % 2 = 0 then fl else fl + 1

/-! ## The corridor (over `ℚ`, computable) -/

/-- The input of one corridor (right-side working frame): the scale `S`, the unit height `H`
(`c0 = (S, H)`), the copied working slots `σ_0 < … < σ_{p−1}` and the template left endpoints
`T_τ` of the receivers (`T.getD τ`; `τ = 0` belongs to the largest slot). -/
structure Input where
  /-- The scale `S = 200000 N²`. -/
  S : ℚ
  /-- The unit height `H = S + 3m + 1`. -/
  H : ℚ
  /-- The copied working slots, increasing. -/
  slots : List ℕ
  /-- `T.getD τ (0,0)`: template left endpoint of receiver `τ`. -/
  T : List (ℚ × ℚ)

namespace Input

variable (I : Input)

/-- Number of copied pairs `p`. -/
def np : ℕ := I.slots.length

/-- The slot of pair `k` (`k = 0` is the smallest slot). -/
def sigma (k : ℕ) : ℕ := I.slots.getD k 0

/-- The receiver index of pair `k`: `τ = p − 1 − k`. -/
def tau (k : ℕ) : ℕ := I.np - 1 - k

/-- Template left endpoint of receiver `τ`. -/
def Tt (τ : ℕ) : ℚ × ℚ := I.T.getD τ (0, 0)

/-- Template left endpoint of receiver `0`. -/
def T0 : ℚ × ℚ := I.Tt 0

/-- The local origin. -/
def O : ℚ × ℚ := Oc I.S I.H

/-- `ε` of the corridor. -/
def ε : ℚ := eps I.S

/-- The left wall `ζ`-level of pair `k`: `Lw = Z(σ_k, 2) − 2ε`. -/
def Lw (k : ℕ) : ℚ := Zs I.S I.H (I.sigma k) 2 - 2 * I.ε

/-- The right wall `ξ`-level of pair `k`: `Rw = Ξ(τ_k, 2) − 2ε`. -/
def Rw (k : ℕ) : ℚ := Xis I.S I.T0 (I.tau k) 2 - 2 * I.ε

/-- The apex `(ζ, ξ) = (Lw, Rw)` of pair `k`. -/
def apex (k : ℕ) : ℚ × ℚ := ofZetaXi I.O (I.Lw k) (I.Rw k)

/-- The umbra axis points `(f0, f1)` of pair `k` (shadow corners `c0`, `c1`). -/
def umbra (k : ℕ) : (ℚ × ℚ) × (ℚ × ℚ) :=
  pairAxis I.S I.H (I.sigma k) (I.Tt (I.tau k)) (c0 I.S I.H) (c1 I.S I.H)

/-- `f0` of the umbra of pair `k`. -/
def f0 (k : ℕ) : ℚ × ℚ := (I.umbra k).1

/-- `f1` of the umbra of pair `k`. -/
def f1 (k : ℕ) : ℚ × ℚ := (I.umbra k).2

/-- The point of the umbra axis of pair `k` with abscissa `x`. -/
def onUmbra (k : ℕ) (x : ℚ) : ℚ × ℚ := onLine (I.f0 k) (I.f1 k) x

/-- Local height of the umbra axis at the apex abscissa. -/
def ya (k : ℕ) : ℚ := (I.onUmbra k (I.apex k).1).2 - I.O.2

/-- Abscissa on the grid `Oc.x + (ε/8)ℤ` nearest to `x` (`Corridor.grid_x`). -/
def gridX (x unit : ℚ) : ℚ := I.O.1 + unit * (roundHalfEven ((x - I.O.1) / unit) : ℚ)

/-- Abscissa on the grid `Oc.x + unit·ℤ` obtained from `x` by rounding up and adding one more
grid unit (`Corridor.grid_x_up`): it lies in `[x + unit, x + 2 unit)`. -/
def gridXUp (x unit : ℚ) : ℚ := I.O.1 + unit * ((⌈(x - I.O.1) / unit⌉ : ℤ) + 1 : ℚ)

/-- `z'_k`: the umbra-axis vertex at the grid abscissa obtained by rounding the abscissa of
(the approximation `X = Rw − Y(apex-axis)` of) `A_k ∩ {ξ = Rw}` up and adding one grid unit
`ε/8`: `z'_k` lies strictly east of the line `ξ = Rw`, so the receiver's lines through `z1`
pass west of this reflex corner (docs/section5/04_corridor.md, §Receiver conditions). -/
def zp (k : ℕ) : ℚ × ℚ := I.onUmbra k (I.gridXUp (I.O.1 + (I.Rw k - I.ya k)) (I.ε / 8))

/-- The valley `(ζ, ξ) = (Lw_{k−1}, Rw_k + ε/2)` before pair `k ≥ 1` (shifted by `ε/2` beyond the
line `ξ = Rw_k`, so that the receiver's lines through `z1` pass below it). -/
def valley (k : ℕ) : ℚ × ℚ := ofZetaXi I.O (I.Lw (k - 1)) (I.Rw k + I.ε / 2)

/-- The base of the stationary pocket of pair `k`: `d1` for `k = 0`, else the valley. -/
def base (k : ℕ) : ℚ × ℚ := if k = 0 then d1 I.S I.H else I.valley k

/-- The stationary guard `p_k = (base.x, A_k(base.x))` (a convex vertex on the umbra axis). -/
def sgPt (k : ℕ) : ℚ × ℚ := I.onUmbra k (I.base k).1

/-- Local height `y_N = Y(apex) − 3ε` of the nook mouth of pair `k`. -/
def yN (k : ℕ) : ℚ := (I.apex k).2 - I.O.2 - 3 * I.ε

/-- Right mouth corner `z1` of the nook (on `ξ = Rw`). -/
def z1 (k : ℕ) : ℚ × ℚ := ofLocal I.O (I.Rw k - I.yN k) (I.yN k)

/-- Left mouth corner `z0` of the nook (on `ζ = Lw`). -/
def z0 (k : ℕ) : ℚ × ℚ := ofLocal I.O (I.yN k - I.Lw k) (I.yN k)

/-- The nook axis points `(F0, F1)` of pair `k` (shadow corners `z0`, `z1`). -/
def nook (k : ℕ) : (ℚ × ℚ) × (ℚ × ℚ) :=
  pairAxis I.S I.H (I.sigma k) (I.Tt (I.tau k)) (I.z0 k) (I.z1 k)

/-- `F0` of the nook of pair `k`. -/
def F0 (k : ℕ) : ℚ × ℚ := (I.nook k).1

/-- `F1` of the nook of pair `k`. -/
def F1 (k : ℕ) : ℚ × ℚ := (I.nook k).2

/-- Right end `n1` of the nook top edge (above `z1`, on the nook axis). -/
def n1 (k : ℕ) : ℚ × ℚ := onLine (I.F0 k) (I.F1 k) (I.z1 k).1

/-- Left end `n0` of the nook top edge (above `z0`, on the nook axis). -/
def n0 (k : ℕ) : ℚ × ℚ := onLine (I.F0 k) (I.F1 k) (I.z0 k).1

/-- Abscissa where the line of slope `s` through `p_k` meets the floor `y = H`. -/
def kx (k : ℕ) (s : ℚ) : ℚ := (I.sgPt k).1 - ((I.sgPt k).2 - I.H) / s

/-- Tip of the floor witness slot of pair `k` on the line of slope `s` through `p_k`. -/
def slotTip (k : ℕ) (s : ℚ) : ℚ × ℚ := (I.kx k s - 1 / 16, I.H - s / 16)

/-- The slope-2 floor witness slot of pair `k` (cone on the west side), eastward order. -/
def slot2 (k : ℕ) : List (ℚ × ℚ) :=
  [(I.kx k 2 - I.ε / 8, I.H), I.slotTip k 2, (I.kx k 2, I.H)]

/-- The slope-4 floor witness slot of pair `k` (cone on the east side), eastward order. -/
def slot4 (k : ℕ) : List (ℚ × ℚ) :=
  [(I.kx k 4, I.H), I.slotTip k 4, (I.kx k 4 + I.ε / 8, I.H)]

/-- The floor slots with their sort keys, in pair order. -/
def floorEntries : List (ℚ × List (ℚ × ℚ)) :=
  (List.range I.np).flatMap fun k => [(I.kx k 2, I.slot2 k), (I.kx k 4, I.slot4 k)]

/-- The floor vertices strictly between `c0` and `c1`: all witness slots, sorted (stably) by
their abscissa. -/
def floor : List (ℚ × ℚ) :=
  (I.floorEntries.mergeSort fun a b => decide (a.1 ≤ b.1)).flatMap (·.2)

/-- The upper-wall vertices contributed by pair `k`:
`[valley_k (k ≥ 1)], p_k, z'_k, z1, n1, n0, z0`. -/
def upperPair (k : ℕ) : List (ℚ × ℚ) :=
  (if k = 0 then [] else [I.valley k]) ++
    [I.sgPt k, I.zp k, I.z1 k, I.n1 k, I.n0 k, I.z0 k]

/-- The upper wall `Λ'` strictly between `d1` and `d0` (westward). -/
def upper : List (ℚ × ℚ) := (List.range I.np).flatMap I.upperPair

/-- The corridor chain before the gadget: `c0`, the floor slots, `c1` (eastward). -/
def chainBefore : List (ℚ × ℚ) := [c0 I.S I.H] ++ I.floor ++ [c1 I.S I.H]

/-- The corridor chain after the gadget: `d1`, the upper wall, `d0` (westward). -/
def chainAfter : List (ℚ × ℚ) := [d1 I.S I.H] ++ I.upper ++ [d0 I.S I.H]

/-- The base guard positions of all pairs (the stationary guards `p_k`). -/
def sgPts : List (ℚ × ℚ) := (List.range I.np).map I.sgPt

theorem base_zero : I.base 0 = d1 I.S I.H := rfl

theorem base_succ (k : ℕ) : I.base (k + 1) = I.valley (k + 1) := rfl

end Input

end ArtGallery.Sec5.Corridor

end
