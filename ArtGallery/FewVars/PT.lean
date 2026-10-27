module

public import ArtGallery.FewVars.Formula

/-!
# The guard-variable reduction is polynomial-time

`PT` lemmas (`@[fun_prop]`, compositional form) for all constructions of `ArtGallery/FewVars`:
rational terms and points, INSIDE (with the exclusive-or tree `PT.xorList`), SIMPLE, SEES,
GUARDS and the final formula `fvFormulaD`; then `PT.fvToETR` (via the decoder, as for
`agpToETRD`).  Every term is a fixed composition of constantly many corner and guard terms, so
the formulas have polynomial size.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.FewVars

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETR ArtGallery.Membership

variable {α : Type} [Code α]

/-! ### Rational terms -/

@[fun_prop] protected theorem PT.rconst {t : α → Term} (ht : PT t) : PT (fun a => rconst (t a)) := by
  unfold rconst; fun_prop

@[fun_prop] protected theorem PT.radd {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => radd (s a) (t a)) := by
  unfold radd; fun_prop

@[fun_prop] protected theorem PT.rsub {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => rsub (s a) (t a)) := by
  unfold rsub; fun_prop

@[fun_prop] protected theorem PT.rmul {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => rmul (s a) (t a)) := by
  unfold rmul; fun_prop

@[fun_prop] protected theorem PT.rneg {s : α → RTerm} (hs : PT s) : PT (fun a => rneg (s a)) := by
  unfold rneg; fun_prop

@[fun_prop] protected theorem PT.rdiv {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => rdiv (s a) (t a)) := by
  unfold rdiv; fun_prop

@[fun_prop] protected theorem PT.rzero : PT (fun _ : α => rzero) := PT.const _
@[fun_prop] protected theorem PT.rone : PT (fun _ : α => rone) := PT.const _
@[fun_prop] protected theorem PT.rtwo : PT (fun _ : α => rtwo) := PT.const _
@[fun_prop] protected theorem PT.rthree : PT (fun _ : α => rthree) := PT.const _
@[fun_prop] protected theorem PT.r0 : PT (fun _ : α => r0) := PT.const _

@[fun_prop] protected theorem PT.rposF {s : α → RTerm} (hs : PT s) : PT (fun a => rposF (s a)) := by
  unfold rposF; fun_prop

@[fun_prop] protected theorem PT.rnonnegF {s : α → RTerm} (hs : PT s) :
    PT (fun a => rnonnegF (s a)) := by
  unfold rnonnegF; fun_prop

@[fun_prop] protected theorem PT.rnonposF {s : α → RTerm} (hs : PT s) :
    PT (fun a => rnonposF (s a)) := by
  unfold rnonposF; fun_prop

@[fun_prop] protected theorem PT.rzeroF {s : α → RTerm} (hs : PT s) : PT (fun a => rzeroF (s a)) := by
  unfold rzeroF; fun_prop

@[fun_prop] protected theorem PT.rneF {s : α → RTerm} (hs : PT s) : PT (fun a => rneF (s a)) := by
  unfold rneF; fun_prop

@[fun_prop] protected theorem PT.rltF {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => rltF (s a) (t a)) := by
  unfold rltF; fun_prop

@[fun_prop] protected theorem PT.rleF {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => rleF (s a) (t a)) := by
  unfold rleF; fun_prop

@[fun_prop] protected theorem PT.reqF {s t : α → RTerm} (hs : PT s) (ht : PT t) :
    PT (fun a => reqF (s a) (t a)) := by
  unfold reqF; fun_prop

@[fun_prop] protected theorem PT.runitF {s : α → RTerm} (hs : PT s) : PT (fun a => runitF (s a)) := by
  unfold runitF; fun_prop

/-! ### Rational points -/

@[fun_prop] protected theorem PT.rvarPt {i : α → ℕ} (hi : PT i) : PT (fun a => rvarPt (i a)) := by
  unfold rvarPt; fun_prop

@[fun_prop] protected theorem PT.rdetT {p q r : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r) :
    PT (fun a => rdetT (p a) (q a) (r a)) := by
  unfold rdetT; fun_prop

@[fun_prop] protected theorem PT.rdotT {p q r s : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => rdotT (p a) (q a) (r a) (s a)) := by
  unfold rdotT; fun_prop

@[fun_prop] protected theorem PT.rcrossT {p q r s : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => rcrossT (p a) (q a) (r a) (s a)) := by
  unfold rcrossT; fun_prop

@[fun_prop] protected theorem PT.rlerpT {p q : α → RPt} {h : α → RTerm} (hp : PT p) (hq : PT q)
    (hh : PT h) : PT (fun a => rlerpT (p a) (q a) (h a)) := by
  unfold rlerpT; fun_prop

@[fun_prop] protected theorem PT.cr {C : α → List RPt} {k : α → ℕ} (hC : PT C) (hk : PT k) :
    PT (fun a => cr (C a) (k a)) := by
  unfold cr; fun_prop

/-! ### INSIDE -/

@[fun_prop] protected theorem PT.ronSegF {q p r : α → RPt} (hq : PT q) (hp : PT p) (hr : PT r) :
    PT (fun a => ronSegF (q a) (p a) (r a)) := by
  unfold ronSegF; fun_prop

@[fun_prop] protected theorem PT.rcrossesF {z u v : α → RPt} (hz : PT z) (hu : PT u)
    (hv : PT v) : PT (fun a => rcrossesF (z a) (u a) (v a)) := by
  unfold rcrossesF; fun_prop

@[fun_prop] protected theorem PT.rboundaryF {C : α → List RPt} {q : α → RPt} (hC : PT C)
    (hq : PT q) : PT (fun a => rboundaryF (C a) (q a)) := by
  unfold rboundaryF; fun_prop

@[fun_prop] protected theorem PT.crossList {C : α → List RPt} {q : α → RPt} (hC : PT C)
    (hq : PT q) : PT (fun a => crossList (C a) (q a)) := by
  unfold crossList; fun_prop

@[fun_prop] protected theorem PT.rinsideF {C : α → List RPt} {q : α → RPt} (hC : PT C)
    (hq : PT q) : PT (fun a => rinsideF (C a) (q a)) := by
  unfold rinsideF; fun_prop

/-! ### SIMPLE -/

@[fun_prop] protected theorem PT.rptNeF {p q : α → RPt} (hp : PT p) (hq : PT q) :
    PT (fun a => rptNeF (p a) (q a)) := by
  unfold rptNeF; fun_prop

@[fun_prop] protected theorem PT.radjF {p q r : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r) :
    PT (fun a => radjF (p a) (q a) (r a)) := by
  unfold radjF; fun_prop

@[fun_prop] protected theorem PT.rparT {p q r s : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => rparT (p a) (q a) (r a) (s a)) := by
  unfold rparT; fun_prop

@[fun_prop] protected theorem PT.rparU {p q r s : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => rparU (p a) (q a) (r a) (s a)) := by
  unfold rparU; fun_prop

@[fun_prop] protected theorem PT.rmeetF {p q r s : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r)
    (hs : PT s) : PT (fun a => rmeetF (p a) (q a) (r a) (s a)) := by
  unfold rmeetF; fun_prop

@[fun_prop] protected theorem PT.redgePairF {C : α → List RPt} {i j : α → ℕ} (hC : PT C)
    (hi : PT i) (hj : PT j) : PT (fun a => redgePairF (C a) (i a) (j a)) := by
  unfold redgePairF; fun_prop

@[fun_prop] protected theorem PT.rsimplePairF {C : α → List RPt} {b : α → ℕ} (hC : PT C)
    (hb : PT b) : PT (fun a => rsimplePairF (C a) (b a)) := by
  unfold rsimplePairF; fun_prop

@[fun_prop] protected theorem PT.rsimpleF {C : α → List RPt} (hC : PT C) :
    PT (fun a => rsimpleF (C a)) := by
  unfold rsimpleF; fun_prop

/-! ### SEES -/

@[fun_prop] protected theorem PT.bpD {C : α → List RPt} {γ c : α → RPt} {i : α → ℕ} (hC : PT C)
    (hγ : PT γ) (hc : PT c) (hi : PT i) : PT (fun a => bpD (C a) (γ a) (c a) (i a)) := by
  unfold bpD; fun_prop

@[fun_prop] protected theorem PT.bpT {C : α → List RPt} {γ c : α → RPt} {i : α → ℕ} (hC : PT C)
    (hγ : PT γ) (hc : PT c) (hi : PT i) : PT (fun a => bpT (C a) (γ a) (c a) (i a)) := by
  unfold bpT; fun_prop

@[fun_prop] protected theorem PT.rpairF {C : α → List RPt} {γ c : α → RPt} {p : α → ℕ}
    (hC : PT C) (hγ : PT γ) (hc : PT c) (hp : PT p) :
    PT (fun a => rpairF (C a) (γ a) (c a) (p a)) := by
  unfold rpairF; fun_prop

@[fun_prop] protected theorem PT.rseesF {C : α → List RPt} {γ c : α → RPt} (hC : PT C)
    (hγ : PT γ) (hc : PT c) : PT (fun a => rseesF (C a) (γ a) (c a)) := by
  unfold rseesF; fun_prop

/-! ### GUARDS -/

@[fun_prop] protected theorem PT.rguard {i : α → ℕ} (hi : PT i) : PT (fun a => rguard (i a)) := by
  unfold rguard; fun_prop

@[fun_prop] protected theorem PT.rline {C : α → List RPt} {i : α → ℕ} (hC : PT C) (hi : PT i) :
    PT (fun a => rline (C a) (i a)) := by
  unfold rline; fun_prop

@[fun_prop] protected theorem PT.rlineDen {l₁ l₂ : α → RPt × RPt} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => rlineDen (l₁ a) (l₂ a)) := by
  unfold rlineDen; fun_prop

@[fun_prop] protected theorem PT.rlineC {l : α → RPt × RPt} (hl : PT l) :
    PT (fun a => rlineC (l a)) := by
  unfold rlineC; fun_prop

@[fun_prop] protected theorem PT.rlineNumX {l₁ l₂ : α → RPt × RPt} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => rlineNumX (l₁ a) (l₂ a)) := by
  unfold rlineNumX; fun_prop

@[fun_prop] protected theorem PT.rlineNumY {l₁ l₂ : α → RPt × RPt} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => rlineNumY (l₁ a) (l₂ a)) := by
  unfold rlineNumY; fun_prop

@[fun_prop] protected theorem PT.rinter {l₁ l₂ : α → RPt × RPt} (h₁ : PT l₁) (h₂ : PT l₂) :
    PT (fun a => rinter (l₁ a) (l₂ a)) := by
  unfold rinter; fun_prop

@[fun_prop] protected theorem PT.rcentroid {p q r : α → RPt} (hp : PT p) (hq : PT q) (hr : PT r) :
    PT (fun a => rcentroid (p a) (q a) (r a)) := by
  unfold rcentroid; fun_prop

/-- Line number `k` of a witness, for a fixed `k`. -/
@[fun_prop] protected theorem PT.wLine {C : α → List RPt} {g L : α → ℕ} (hC : PT C) (hg : PT g)
    (hL : PT L) (k : ℕ) : PT (fun a => wLine (C a) (g a) (L a) k) := by
  unfold wLine; fun_prop

@[fun_prop] protected theorem PT.wDen {C : α → List RPt} {g L : α → ℕ} (hC : PT C) (hg : PT g)
    (hL : PT L) (k : ℕ) : PT (fun a => wDen (C a) (g a) (L a) k) := by
  unfold wDen; fun_prop

@[fun_prop] protected theorem PT.wPt {C : α → List RPt} {g L : α → ℕ} (hC : PT C) (hg : PT g)
    (hL : PT L) (k : ℕ) : PT (fun a => wPt (C a) (g a) (L a) k) := by
  unfold wPt; fun_prop

@[fun_prop] protected theorem PT.wCen {C : α → List RPt} {g L : α → ℕ} (hC : PT C) (hg : PT g)
    (hL : PT L) : PT (fun a => wCen (C a) (g a) (L a)) := by
  unfold wCen; fun_prop

@[fun_prop] protected theorem PT.rwitF {C : α → List RPt} {g L : α → ℕ} (hC : PT C) (hg : PT g)
    (hL : PT L) : PT (fun a => rwitF (C a) (g a) (L a)) := by
  unfold rwitF; fun_prop

@[fun_prop] protected theorem PT.rguardsF {C : α → List RPt} {g : α → ℕ} (hC : PT C)
    (hg : PT g) : PT (fun a => rguardsF (C a) (g a)) := by
  unfold rguardsF; fun_prop

/-! ### The reduction -/

@[fun_prop] protected theorem PT.cornerD {d : α → FracDigits} (hd : PT d) :
    PT (fun a => cornerD (d a)) := by
  unfold cornerD; fun_prop

@[fun_prop] protected theorem PT.cornersD {D : α → List FracDigits} (hD : PT D) :
    PT (fun a => cornersD (D a)) := by
  unfold cornersD; fun_prop

@[fun_prop] protected theorem PT.fvFormulaD {D : α → List FracDigits} {g : α → ℕ} (hD : PT D)
    (hg : PT g) : PT (fun a => fvFormulaD (D a) (g a)) := by
  unfold fvFormulaD; fun_prop

/-- **The guard-variable reduction is polynomial-time.** -/
protected theorem PT.fvToETR : PT fvToETR := by
  refine PT.of_optionCases (o := ArtGallery.decodeAGP) (d := fun _ => fFalse)
    (f := fun _ r => fvFormulaD r.1 (min (SAT.binaryValue r.2) (r.1.length + 3)))
    (PT.decodeAGP PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [fvToETR, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [fvToETR, h]

end ArtGallery.FewVars

end
