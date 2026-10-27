module

public import ArtGallery.PTime.CircuitCode
public import ArtGallery.PTime.INVinER
public import ArtGallery.ETR.Reduction

/-!
# ETR-INV is ∃ℝ-complete

The reduction `ArtGallery.etrToINV` of `ArtGallery.ETR.Reduction` (formula → ETR^{1,+,·}
system → scaled system → ETR-INV instance) is polynomial-time (`PT.etrToINV`), so

* `ArtGallery.etrReduction`: decode a formula, translate, encode (a non-code goes to the
  unsatisfiable instance `badINV = [x₀ = 1, x₀ + x₀ = x₀]`), is a polynomial-time reduction from
  `ETR` to `ETRINV` (`ArtGallery.etr_polyRed_etrinv`);
* **`ArtGallery.etrinv_erComplete : ERComplete ETRINV`**.

Also `PT.blocks` (the indexed concatenation `Gate.blocks` is a `flatMap` over `zipIdx`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code
open Gate Chain ETRINV

theorem blocks_eq_flatMap {β γ : Type} (f : ℕ → β → List γ) (j : ℕ) (l : List β) :
    blocks f j l = (l.zipIdx j).flatMap (fun p => f p.2 p.1) := by
  induction l generalizing j with
  | nil => rfl
  | cons a l ih => simp [blocks, ih, List.zipIdx_cons]

variable {α : Type} [Code α]

/-- The indexed concatenation `Gate.blocks` (its function in uncurried form). -/
@[fun_prop] protected theorem PT.blocks {β γ : Type} [Code β] [Code γ] {f : α → ℕ → β → List γ}
    (hf : PT (fun p : α × ℕ × β => f p.1 p.2.1 p.2.2)) {j : α → ℕ} {l : α → List β}
    (hj : PT j) (hl : PT l) : PT (fun a => blocks (f a) (j a) (l a)) := by
  have h : PT (fun a => ((l a).zipIdx (j a)).flatMap (fun p => f a p.2 p.1)) := by
    refine PT.flatMap (f := fun a p => f a p.2 p.1) ?_ (PT.zipIdx hl hj)
    exact hf.comp (PT.pair (PT.fst PT.id) (PT.pair (PT.snd (PT.snd PT.id))
      (PT.fst (PT.snd PT.id))))
  exact h.of_eq fun a => (blocks_eq_flatMap _ _ _).symm

theorem scaleGate_eq (N k j : ℕ) (g : Gate) : scaleGate N k j g = g.elim
    (fun x => [.add x (N + 1) (N + k)]) (fun x y z => [.add x y z])
    (fun x y z => [.mul x y (N + k + 1 + j), .mul (N + k) z (N + k + 1 + j)]) := by
  cases g <;> rfl

theorem invGate_eq (M j : ℕ) (g : Gate) : invGate M j g = g.elim
    (fun x => [.one x]) (fun x y z => [.add x y (blockBase M j), .add z (M + 6) (blockBase M j)])
    (fun x y z => prodGadget M x y z (blockBase M j)) := by
  cases g <;> rfl

@[fun_prop] protected theorem PT.scaleSystem {N k : α → ℕ} {S : α → List Gate} (hN : PT N)
    (hk : PT k) (hS : PT S) : PT (fun a => scaleSystem (N a) (k a) (S a)) := by
  have hg : PT (fun p : α × ℕ × Gate => scaleGate (N p.1) (k p.1) p.2.1 p.2.2) := by
    simp only [scaleGate_eq]
    fun_prop
  unfold scaleSystem scaleHeader
  fun_prop

@[fun_prop] protected theorem PT.prodGadget {M X Y Z b : α → ℕ} (hM : PT M) (hX : PT X)
    (hY : PT Y) (hZ : PT Z) (hb : PT b) :
    PT (fun a => prodGadget (M a) (X a) (Y a) (Z a) (b a)) := by
  unfold prodGadget sqGadget
  fun_prop

@[fun_prop] protected theorem PT.invSystem {M : α → ℕ} {T : α → List Gate} (hM : PT M)
    (hT : PT T) : PT (fun a => invSystem (M a) (T a)) := by
  have hg : PT (fun p : α × ℕ × Gate => invGate (M p.1) p.2.1 p.2.2) := by
    simp only [invGate_eq, blockBase]
    fun_prop
  unfold invSystem constHeader
  fun_prop

/-- **The reduction from ETR to ETR-INV is polynomial-time** (on formulas). -/
@[fun_prop] protected theorem PT.etrToINV {φ : α → ETR.Formula} (hφ : PT φ) :
    PT (fun a => etrToINV (φ a)) := by
  unfold etrToINV etrScaledVars etrScaled etrK ballExp
  fun_prop

/-- An unsatisfiable ETR-INV instance: `x₀ = 1` and `x₀ + x₀ = x₀`. -/
def badINV : List Constraint := [.one 0, .add 0 0 0]

theorem badINV_not_satisfiable : ¬ ETRINV.Satisfiable badINV := by
  rintro ⟨v, -, hv⟩
  have h1 := hv _ (List.mem_cons_self ..)
  have h2 := hv (.add 0 0 0) (by simp [badINV])
  simp only [Constraint.Holds] at h1 h2
  rw [h1] at h2
  norm_num at h2

/-- **The reduction from ETR to ETR-INV** on raw words. -/
def etrReduction (w : Word) : Word :=
  match ETR.decodeFormula w with
  | some φ => ETRINV.encode (etrToINV φ)
  | none => ETRINV.encode badINV

theorem etrReduction_correct (w : Word) : ArtGallery.ETR w ↔ ArtGallery.ETRINV (etrReduction w) := by
  unfold etrReduction
  cases h : ETR.decodeFormula w with
  | none =>
    simp only [ETRINV_encode_iff]
    constructor
    · rintro ⟨φ, rfl, _⟩
      rw [ETR.decodeFormula_encode] at h
      exact absurd h (by simp)
    · exact fun h' => absurd h' badINV_not_satisfiable
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, ETRINV_encode_iff, etrToINV_iff]

protected theorem PT.etrReduction : PT etrReduction := by
  refine PT.of_optionCases (o := ETR.decodeFormula) (d := fun _ => ETRINV.encode badINV)
    (f := fun _ φ => ETRINV.encode (etrToINV φ)) (PT.decodeFormula PT.id) (PT.const _)
    (by fun_prop) ?_ ?_
  · intro w h; simp [etrReduction, h]
  · intro w φ h; simp [etrReduction, h]

/-- `ETR` reduces to `ETRINV` in polynomial time. -/
theorem etr_polyRed_etrinv : PolyRed ETR ETRINV :=
  PT.polyRed PT.etrReduction etrReduction_correct

/-- **ETR-INV is ∃ℝ-complete.** -/
theorem etrinv_erComplete : ERComplete ETRINV :=
  ERComplete.of_polyRed_ETR etrinv_inER etr_polyRed_etrinv

end ArtGallery

end
