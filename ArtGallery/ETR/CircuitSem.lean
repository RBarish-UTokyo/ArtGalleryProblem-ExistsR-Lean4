module

public import ArtGallery.ETR.Circuit

/-!
# From ETR formulas to ETR^{1,+,·} systems: correctness

For the compilation of `ArtGallery.ETR.Circuit` we prove, by induction on terms and formulas in
negation normal form, the invariants

* `Comp.WF`: the circuit only uses auxiliary variables below its count;
* `Comp.OrigLt n`: the circuit only uses original variables below `n` (if the source does);
* terms: every solution gives the result variable the value of the term (`Term.comp_eval`), and
  every assignment of the original variables extends to a solution (`Term.comp_sat`);
* formulas: a solution with residual `0` makes the formula true (`NNF.comp_sound`), every
  assignment extends to a solution (`NNF.comp_sat`), and to one with residual `0` if the formula
  holds (`NNF.comp_complete`).

The main results are `ETR.Formula.toCircuit_vars`, `ETR.Formula.toCircuit_sound` and
`ETR.Formula.toCircuit_complete`.
-/

@[expose] public section

namespace ArtGallery

namespace Circuit

open ArtGallery.Gate

/-- The circuit only uses auxiliary variables below `c.cnt`. -/
def Comp.WF (c : Comp) : Prop := (∀ g ∈ c.gates, g.All (FLt c.cnt)) ∧ FLt c.cnt c.res

/-- The circuit only uses original variables below `n`. -/
def Comp.OrigLt (n : ℕ) (c : Comp) : Prop := (∀ g ∈ c.gates, g.All (OLt n)) ∧ OLt n c.res

/-- The original values `x` and auxiliary values `a` satisfy all equations of the circuit. -/
def Comp.Sat (c : Comp) (x a : ℕ → ℝ) : Prop := ∀ g ∈ c.gates, g.Holds (Sum.elim x a)

/-- Concatenation of auxiliary assignments: `a₁` below `n₁`, then `a₂` (shifted) below
`n₁ + n₂`, then `e` (shifted). -/
def merge (n₁ n₂ : ℕ) (a₁ a₂ e : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j < n₁ then a₁ j else if j < n₁ + n₂ then a₂ (j - n₁) else e (j - (n₁ + n₂))

/-- Universal quantification over the empty list. -/
theorem forall_mem_nil_iff {α : Type} (P : α → Prop) : (∀ x ∈ ([] : List α), P x) ↔ True := by
  simp

theorem FLt_inr {c j : ℕ} : FLt c (.inr j) ↔ j < c := Iff.rfl

theorem place_inr {n j : ℕ} : place n (.inr j) = n + j := rfl

theorem OLt_inr {n j : ℕ} : OLt n (.inr j) ↔ True := Iff.rfl

/-- Unfold the new equations of a combinator (at the goal or at hypotheses). -/
syntax "unfold_new" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| unfold_new $[$loc]?) =>
    `(tactic| simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.Holds, elim_shiftVar,
      Sum.elim_inr, and_true] $[$loc]?)

theorem FLt_shift {m : ℕ} (k₁ k₂ : ℕ) {v : CVar} (h : FLt m v) :
    FLt (k₁ + m + k₂) (shiftVar k₁ v) := by
  cases v with
  | inl i => trivial
  | inr j =>
    simp only [FLt] at h
    show j + k₁ < k₁ + m + k₂
    omega

theorem OLt_shift {n : ℕ} (k : ℕ) {v : CVar} (h : OLt n v) : OLt n (shiftVar k v) := by
  cases v with
  | inl i => exact h
  | inr j => trivial

theorem elim_congr {m : ℕ} {x a a' : ℕ → ℝ} (h : ∀ j < m, a j = a' j) :
    ∀ {v : CVar}, FLt m v → Sum.elim x a v = Sum.elim x a' v
  | .inl _, _ => rfl
  | .inr j, hj => h j hj

theorem Comp.sat_congr {c : Comp} (hc : c.WF) {x a a' : ℕ → ℝ} (h : ∀ j < c.cnt, a j = a' j) :
    c.Sat x a ↔ c.Sat x a' := by
  constructor
  · intro hs g hg
    exact (CGate.holds_congr (fun v hv => elim_congr h hv) (hc.1 g hg)).1 (hs g hg)
  · intro hs g hg
    exact (CGate.holds_congr (fun v hv => elim_congr h hv) (hc.1 g hg)).2 (hs g hg)

theorem Comp.res_congr {c : Comp} (hc : c.WF) {x a a' : ℕ → ℝ} (h : ∀ j < c.cnt, a j = a' j) :
    Sum.elim x a c.res = Sum.elim x a' c.res :=
  elim_congr h hc.2

theorem Comp.sat_ext (c d : Comp) (new : List CGate) (res : CVar) (k : ℕ) (x a : ℕ → ℝ) :
    (c.ext d new res k).Sat x a ↔
      c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧ ∀ g ∈ new, g.Holds (Sum.elim x a) := by
  simp only [Comp.Sat, Comp.ext, Comp.pair, List.forall_mem_append, List.forall_mem_map,
    CGate.holds_shift, and_assoc]

theorem Comp.wf_ext {c d : Comp} (hc : c.WF) (hd : d.WF) {new : List CGate} {res : CVar} {k : ℕ}
    (hnew : ∀ g ∈ new, g.All (FLt (c.cnt + d.cnt + k))) (hres : FLt (c.cnt + d.cnt + k) res) :
    (c.ext d new res k).WF := by
  refine ⟨?_, hres⟩
  show ∀ g ∈ c.pair d ++ new, g.All (FLt (c.cnt + d.cnt + k))
  intro g hg
  simp only [Comp.pair, List.mem_append, List.mem_map] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | hg
  · exact (hc.1 g hg).mono (fun v hv => hv.mono (by omega))
  · exact CGate.all_shift c.cnt (fun v hv => FLt_shift c.cnt k hv) (hd.1 g' hg')
  · exact hnew g hg

theorem Comp.orig_ext {n : ℕ} {c d : Comp} (hc : c.OrigLt n) (hd : d.OrigLt n) {new : List CGate}
    {res : CVar} {k : ℕ} (hnew : ∀ g ∈ new, g.All (OLt n)) (hres : OLt n res) :
    (c.ext d new res k).OrigLt n := by
  refine ⟨?_, hres⟩
  show ∀ g ∈ c.pair d ++ new, g.All (OLt n)
  intro g hg
  simp only [Comp.pair, List.mem_append, List.mem_map] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | hg
  · exact hc.1 g hg
  · exact CGate.all_shift c.cnt (fun v hv => OLt_shift c.cnt hv) (hd.1 g' hg')
  · exact hnew g hg

/-- Merging solutions of the two parts. -/
theorem Comp.sat_merge {c d : Comp} (hc : c.WF) (hd : d.WF) {x a₁ a₂ : ℕ → ℝ} (e : ℕ → ℝ)
    (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    c.Sat x (merge c.cnt d.cnt a₁ a₂ e) ∧
    d.Sat x (fun j => merge c.cnt d.cnt a₁ a₂ e (j + c.cnt)) ∧
    Sum.elim x (merge c.cnt d.cnt a₁ a₂ e) c.res = Sum.elim x a₁ c.res ∧
    Sum.elim x (fun j => merge c.cnt d.cnt a₁ a₂ e (j + c.cnt)) d.res = Sum.elim x a₂ d.res ∧
    merge c.cnt d.cnt a₁ a₂ e (c.cnt + d.cnt) = e 0 ∧
    ∀ i, merge c.cnt d.cnt a₁ a₂ e (c.cnt + d.cnt + i) = e i := by
  have k₁ : ∀ j < c.cnt, merge c.cnt d.cnt a₁ a₂ e j = a₁ j := fun j hj => by
    simp only [merge, ite_eq_left hj]
  have k₂ : ∀ j < d.cnt, merge c.cnt d.cnt a₁ a₂ e (j + c.cnt) = a₂ j := fun j hj => by
    simp only [merge]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel]
  have k₃ : ∀ i, merge c.cnt d.cnt a₁ a₂ e (c.cnt + d.cnt + i) = e i := fun i => by
    simp only [merge]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
  refine ⟨(Comp.sat_congr hc k₁).2 h₁, (Comp.sat_congr hd k₂).2 h₂, Comp.res_congr hc k₁,
    Comp.res_congr hd k₂, ?_, k₃⟩
  simpa using k₃ 0

/-! ### Scoping of the combinators -/

/-- Close the scoping goal for the new equations of a combinator (uses the hypotheses on the
result variables of the two parts). -/
macro "scope_new" : tactic =>
  `(tactic| (simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, FLt_inr, *,
    and_true, true_and] <;> omega))

section Scope

variable {c d : Comp}

theorem Comp.addC_wf (hc : c.WF) (hd : d.WF) : (c.addC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 1) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 1 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.subC_wf (hc : c.WF) (hd : d.WF) : (c.subC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 1) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 1 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.mulC_wf (hc : c.WF) (hd : d.WF) : (c.mulC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 1) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 1 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.orC_wf (hc : c.WF) (hd : d.WF) : (c.orC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 1) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 1 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.leC_wf (hc : c.WF) (hd : d.WF) : (c.leC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 4) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 4 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.ltC_wf (hc : c.WF) (hd : d.WF) : (c.ltC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 6) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 6 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

theorem Comp.andC_wf (hc : c.WF) (hd : d.WF) : (c.andC d).WF := by
  have hA : FLt (c.cnt + d.cnt + 3) c.res := hc.2.mono (by omega)
  have hB := FLt_shift c.cnt 3 hd.2
  apply Comp.wf_ext hc hd
  · scope_new
  · show _ < _; omega

variable {n : ℕ}

theorem Comp.addC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.addC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.subC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.subC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.mulC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.mulC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.orC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.orC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.leC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.leC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.ltC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.ltC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

theorem Comp.andC_orig (hc : c.OrigLt n) (hd : d.OrigLt n) : (c.andC d).OrigLt n := by
  have hB := OLt_shift c.cnt hd.2
  apply Comp.orig_ext hc hd
  · simp only [List.forall_mem_cons, forall_mem_nil_iff, CGate.All, OLt_inr, hc.2, hB, and_true]
  · trivial

end Scope

/-! ### Semantics of the combinators -/

section Sem

variable {c d : Comp} {x a : ℕ → ℝ}

theorem Comp.addC_spec (h : (c.addC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧
      Sum.elim x a (c.addC d).res =
        Sum.elim x a c.res + Sum.elim x (fun j => a (j + c.cnt)) d.res := by
  simp only [Comp.addC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  refine ⟨h₁, h₂, ?_⟩
  simp only [Comp.addC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.subC_spec (h : (c.subC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧
      Sum.elim x a (c.subC d).res =
        Sum.elim x a c.res - Sum.elim x (fun j => a (j + c.cnt)) d.res := by
  simp only [Comp.subC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  refine ⟨h₁, h₂, ?_⟩
  simp only [Comp.subC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.mulC_spec (h : (c.mulC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧
      Sum.elim x a (c.mulC d).res =
        Sum.elim x a c.res * Sum.elim x (fun j => a (j + c.cnt)) d.res := by
  simp only [Comp.mulC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  refine ⟨h₁, h₂, ?_⟩
  simp only [Comp.mulC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.orC_spec (h : (c.orC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧
      Sum.elim x a (c.orC d).res =
        Sum.elim x a c.res * Sum.elim x (fun j => a (j + c.cnt)) d.res := by
  simp only [Comp.orC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  refine ⟨h₁, h₂, ?_⟩
  simp only [Comp.orC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.andC_spec (h : (c.andC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧
      Sum.elim x a (c.andC d).res =
        Sum.elim x a c.res * Sum.elim x a c.res +
        Sum.elim x (fun j => a (j + c.cnt)) d.res * Sum.elim x (fun j => a (j + c.cnt)) d.res := by
  simp only [Comp.andC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  obtain ⟨e₁, e₂, e₃⟩ := h₃
  refine ⟨h₁, h₂, ?_⟩
  simp only [Comp.andC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.leC_spec (h : (c.leC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧ ∃ σ : ℝ,
      Sum.elim x a (c.leC d).res =
        (Sum.elim x (fun j => a (j + c.cnt)) d.res - Sum.elim x a c.res) - σ * σ := by
  simp only [Comp.leC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  obtain ⟨e₁, e₂, e₃⟩ := h₃
  refine ⟨h₁, h₂, a (c.cnt + d.cnt), ?_⟩
  simp only [Comp.leC, Comp.ext, Sum.elim_inr]
  linarith

theorem Comp.ltC_spec (h : (c.ltC d).Sat x a) :
    c.Sat x a ∧ d.Sat x (fun j => a (j + c.cnt)) ∧ ∃ σ : ℝ,
      Sum.elim x a (c.ltC d).res =
        (Sum.elim x (fun j => a (j + c.cnt)) d.res - Sum.elim x a c.res) * (σ * σ) - 1 := by
  simp only [Comp.ltC, Comp.sat_ext] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold_new at h₃
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h₃
  refine ⟨h₁, h₂, a (c.cnt + d.cnt), ?_⟩
  simp only [Comp.ltC, Comp.ext, Sum.elim_inr]
  have hd : Sum.elim x (fun j => a (j + c.cnt)) d.res - Sum.elim x a c.res =
      a (c.cnt + d.cnt + 2) := by linarith
  rw [hd, e₁]
  linarith

variable {a₁ a₂ : ℕ → ℝ}

theorem Comp.addC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    ∃ a, (c.addC d).Sat x a ∧
      Sum.elim x a (c.addC d).res = Sum.elim x a₁ c.res + Sum.elim x a₂ d.res := by
  obtain ⟨m₁, m₂, m₃, m₄, m₀, -⟩ :=
    Comp.sat_merge hc hd (fun _ => Sum.elim x a₁ c.res + Sum.elim x a₂ d.res) h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ (fun _ => Sum.elim x a₁ c.res + Sum.elim x a₂ d.res), ?_, ?_⟩
  · simp only [Comp.addC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄]
  · simp only [Comp.addC, Comp.ext, Sum.elim_inr, m₀]

theorem Comp.subC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    ∃ a, (c.subC d).Sat x a ∧
      Sum.elim x a (c.subC d).res = Sum.elim x a₁ c.res - Sum.elim x a₂ d.res := by
  obtain ⟨m₁, m₂, m₃, m₄, m₀, -⟩ :=
    Comp.sat_merge hc hd (fun _ => Sum.elim x a₁ c.res - Sum.elim x a₂ d.res) h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ (fun _ => Sum.elim x a₁ c.res - Sum.elim x a₂ d.res), ?_, ?_⟩
  · simp only [Comp.subC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄]
    ring
  · simp only [Comp.subC, Comp.ext, Sum.elim_inr, m₀]

theorem Comp.mulC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    ∃ a, (c.mulC d).Sat x a ∧
      Sum.elim x a (c.mulC d).res = Sum.elim x a₁ c.res * Sum.elim x a₂ d.res := by
  obtain ⟨m₁, m₂, m₃, m₄, m₀, -⟩ :=
    Comp.sat_merge hc hd (fun _ => Sum.elim x a₁ c.res * Sum.elim x a₂ d.res) h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ (fun _ => Sum.elim x a₁ c.res * Sum.elim x a₂ d.res), ?_, ?_⟩
  · simp only [Comp.mulC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄]
  · simp only [Comp.mulC, Comp.ext, Sum.elim_inr, m₀]

theorem Comp.orC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    ∃ a, (c.orC d).Sat x a ∧
      Sum.elim x a (c.orC d).res = Sum.elim x a₁ c.res * Sum.elim x a₂ d.res := by
  obtain ⟨m₁, m₂, m₃, m₄, m₀, -⟩ :=
    Comp.sat_merge hc hd (fun _ => Sum.elim x a₁ c.res * Sum.elim x a₂ d.res) h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ (fun _ => Sum.elim x a₁ c.res * Sum.elim x a₂ d.res), ?_, ?_⟩
  · simp only [Comp.orC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄]
  · simp only [Comp.orC, Comp.ext, Sum.elim_inr, m₀]

theorem Comp.andC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) :
    ∃ a, (c.andC d).Sat x a ∧
      Sum.elim x a (c.andC d).res = Sum.elim x a₁ c.res * Sum.elim x a₁ c.res +
        Sum.elim x a₂ d.res * Sum.elim x a₂ d.res := by
  let e : ℕ → ℝ := fun i =>
    if i = 0 then Sum.elim x a₁ c.res * Sum.elim x a₁ c.res
    else if i = 1 then Sum.elim x a₂ d.res * Sum.elim x a₂ d.res
    else Sum.elim x a₁ c.res * Sum.elim x a₁ c.res + Sum.elim x a₂ d.res * Sum.elim x a₂ d.res
  obtain ⟨m₁, m₂, m₃, m₄, m₀, m₅⟩ := Comp.sat_merge hc hd e h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ e, ?_, ?_⟩
  · simp only [Comp.andC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄, m₅, m₅]
    simp [e]
  · simp only [Comp.andC, Comp.ext, Sum.elim_inr, m₅]
    simp [e]

theorem Comp.leC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) (σ : ℝ) :
    ∃ a, (c.leC d).Sat x a ∧
      Sum.elim x a (c.leC d).res = (Sum.elim x a₂ d.res - Sum.elim x a₁ c.res) - σ * σ := by
  let e : ℕ → ℝ := fun i =>
    if i = 0 then σ else if i = 1 then σ * σ
    else if i = 2 then Sum.elim x a₂ d.res - Sum.elim x a₁ c.res
    else Sum.elim x a₂ d.res - Sum.elim x a₁ c.res - σ * σ
  obtain ⟨m₁, m₂, m₃, m₄, m₀, m₅⟩ := Comp.sat_merge hc hd e h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ e, ?_, ?_⟩
  · simp only [Comp.leC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    rw [m₀, m₃, m₄, m₅, m₅, m₅]
    simp only [e]
    norm_num
  · simp only [Comp.leC, Comp.ext, Sum.elim_inr, m₅]
    simp [e]

theorem Comp.ltC_sat (hc : c.WF) (hd : d.WF) (h₁ : c.Sat x a₁) (h₂ : d.Sat x a₂) (σ : ℝ) :
    ∃ a, (c.ltC d).Sat x a ∧
      Sum.elim x a (c.ltC d).res = (Sum.elim x a₂ d.res - Sum.elim x a₁ c.res) * (σ * σ) - 1 := by
  let e : ℕ → ℝ := fun i =>
    if i = 0 then σ else if i = 1 then σ * σ
    else if i = 2 then Sum.elim x a₂ d.res - Sum.elim x a₁ c.res
    else if i = 3 then (Sum.elim x a₂ d.res - Sum.elim x a₁ c.res) * (σ * σ)
    else if i = 4 then 1
    else (Sum.elim x a₂ d.res - Sum.elim x a₁ c.res) * (σ * σ) - 1
  obtain ⟨m₁, m₂, m₃, m₄, m₀, m₅⟩ := Comp.sat_merge hc hd e h₁ h₂
  refine ⟨merge c.cnt d.cnt a₁ a₂ e, ?_, ?_⟩
  · simp only [Comp.ltC, Comp.sat_ext]
    refine ⟨m₁, m₂, ?_⟩
    unfold_new
    simp only [m₀, m₃, m₄, m₅]
    simp only [e]
    norm_num
  · simp only [Comp.ltC, Comp.ext, Sum.elim_inr, m₅]
    simp [e]

end Sem

end Circuit

/-! ## Correctness of the compilation -/

namespace ETR

open Circuit

theorem Term.comp_wf (t : Term) : t.comp.WF := by
  induction t with
  | var i => exact ⟨fun g hg => by simp [Term.comp] at hg, trivial⟩
  | zero => exact ⟨by simp [Term.comp, CGate.All, FLt], by simp [Term.comp, FLt]⟩
  | one => exact ⟨by simp [Term.comp, CGate.All, FLt], by simp [Term.comp, FLt]⟩
  | add s t ihs iht => exact Comp.addC_wf ihs iht
  | sub s t ihs iht => exact Comp.subC_wf ihs iht
  | mul s t ihs iht => exact Comp.mulC_wf ihs iht

theorem Term.comp_orig {n : ℕ} (t : Term) (h : t.VarsLt n) : t.comp.OrigLt n := by
  induction t with
  | var i => exact ⟨fun g hg => by simp [Term.comp] at hg, h⟩
  | zero => exact ⟨by simp [Term.comp, CGate.All, OLt], trivial⟩
  | one => exact ⟨by simp [Term.comp, CGate.All, OLt], trivial⟩
  | add s t ihs iht => obtain ⟨h₁, h₂⟩ := h; exact Comp.addC_orig (ihs h₁) (iht h₂)
  | sub s t ihs iht => obtain ⟨h₁, h₂⟩ := h; exact Comp.subC_orig (ihs h₁) (iht h₂)
  | mul s t ihs iht => obtain ⟨h₁, h₂⟩ := h; exact Comp.mulC_orig (ihs h₁) (iht h₂)

/-- In every solution of the circuit of a term, the result variable carries the value of the
term. -/
theorem Term.comp_eval (t : Term) :
    ∀ (x a : ℕ → ℝ), t.comp.Sat x a → Sum.elim x a t.comp.res = t.eval x := by
  induction t with
  | var i => intro x a _; rfl
  | zero =>
    intro x a h
    simp only [Comp.Sat, Term.comp] at h
    unfold_new at h
    simp only [Term.comp, Term.eval, Sum.elim_inr]
    linarith
  | one =>
    intro x a h
    simp only [Comp.Sat, Term.comp] at h
    unfold_new at h
    simp only [Term.comp, Term.eval, Sum.elim_inr]
    exact h
  | add s t ihs iht =>
    intro x a h
    simp only [Term.comp, Term.eval] at h ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.addC_spec h
    rw [h₃, ihs x a h₁, iht x _ h₂]
  | sub s t ihs iht =>
    intro x a h
    simp only [Term.comp, Term.eval] at h ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.subC_spec h
    rw [h₃, ihs x a h₁, iht x _ h₂]
  | mul s t ihs iht =>
    intro x a h
    simp only [Term.comp, Term.eval] at h ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.mulC_spec h
    rw [h₃, ihs x a h₁, iht x _ h₂]

/-- Every assignment of the original variables extends to a solution of the circuit of a term. -/
theorem Term.comp_sat (t : Term) (x : ℕ → ℝ) : ∃ a, t.comp.Sat x a := by
  induction t with
  | var i => exact ⟨fun _ => 0, by simp [Comp.Sat, Term.comp]⟩
  | zero => exact ⟨fun _ => 0, by simp [Comp.Sat, Term.comp, CGate.Holds]⟩
  | one => exact ⟨fun _ => 1, by simp [Comp.Sat, Term.comp, CGate.Holds]⟩
  | add s t ihs iht =>
    obtain ⟨a₁, h₁⟩ := ihs
    obtain ⟨a₂, h₂⟩ := iht
    obtain ⟨a, ha, -⟩ := Comp.addC_sat s.comp_wf t.comp_wf h₁ h₂
    exact ⟨a, ha⟩
  | sub s t ihs iht =>
    obtain ⟨a₁, h₁⟩ := ihs
    obtain ⟨a₂, h₂⟩ := iht
    obtain ⟨a, ha, -⟩ := Comp.subC_sat s.comp_wf t.comp_wf h₁ h₂
    exact ⟨a, ha⟩
  | mul s t ihs iht =>
    obtain ⟨a₁, h₁⟩ := ihs
    obtain ⟨a₂, h₂⟩ := iht
    obtain ⟨a, ha, -⟩ := Comp.mulC_sat s.comp_wf t.comp_wf h₁ h₂
    exact ⟨a, ha⟩

theorem NNF.comp_wf (ψ : NNF) : ψ.comp.WF := by
  induction ψ with
  | eq s t => exact Comp.subC_wf s.comp_wf t.comp_wf
  | lt s t => exact Comp.ltC_wf s.comp_wf t.comp_wf
  | le s t => exact Comp.leC_wf s.comp_wf t.comp_wf
  | and φ ψ ih₁ ih₂ => exact Comp.andC_wf ih₁ ih₂
  | or φ ψ ih₁ ih₂ => exact Comp.orC_wf ih₁ ih₂

theorem NNF.comp_orig {n : ℕ} (ψ : NNF) (h : ψ.VarsLt n) : ψ.comp.OrigLt n := by
  induction ψ with
  | eq s t => obtain ⟨h₁, h₂⟩ := h; exact Comp.subC_orig (s.comp_orig h₁) (t.comp_orig h₂)
  | lt s t => obtain ⟨h₁, h₂⟩ := h; exact Comp.ltC_orig (s.comp_orig h₁) (t.comp_orig h₂)
  | le s t => obtain ⟨h₁, h₂⟩ := h; exact Comp.leC_orig (s.comp_orig h₁) (t.comp_orig h₂)
  | and φ ψ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := h; exact Comp.andC_orig (ih₁ h₁) (ih₂ h₂)
  | or φ ψ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := h; exact Comp.orC_orig (ih₁ h₁) (ih₂ h₂)

/-- A solution of the circuit of a formula with residual `0` satisfies the formula. -/
theorem NNF.comp_sound (ψ : NNF) :
    ∀ (x a : ℕ → ℝ), ψ.comp.Sat x a → Sum.elim x a ψ.comp.res = 0 → ψ.Holds x := by
  induction ψ with
  | eq s t =>
    intro x a h hr
    simp only [NNF.comp, NNF.Holds] at h hr ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.subC_spec h
    rw [h₃, s.comp_eval x a h₁, t.comp_eval x _ h₂] at hr
    linarith
  | lt s t =>
    intro x a h hr
    simp only [NNF.comp, NNF.Holds] at h hr ⊢
    obtain ⟨h₁, h₂, σ, h₃⟩ := Comp.ltC_spec h
    rw [h₃, s.comp_eval x a h₁, t.comp_eval x _ h₂] at hr
    have hσ := mul_self_nonneg σ
    have hpos : 0 < t.eval x - s.eval x := by nlinarith
    linarith
  | le s t =>
    intro x a h hr
    simp only [NNF.comp, NNF.Holds] at h hr ⊢
    obtain ⟨h₁, h₂, σ, h₃⟩ := Comp.leC_spec h
    rw [h₃, s.comp_eval x a h₁, t.comp_eval x _ h₂] at hr
    nlinarith [mul_self_nonneg σ]
  | and φ ψ ih₁ ih₂ =>
    intro x a h hr
    simp only [NNF.comp, NNF.Holds] at h hr ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.andC_spec h
    rw [h₃] at hr
    set A := Sum.elim x a φ.comp.res
    set B := Sum.elim x (fun j => a (j + φ.comp.cnt)) ψ.comp.res
    have hA : A * A = 0 := by nlinarith [mul_self_nonneg A, mul_self_nonneg B]
    have hB : B * B = 0 := by nlinarith [mul_self_nonneg A, mul_self_nonneg B]
    exact ⟨ih₁ x a h₁ (mul_self_eq_zero.mp hA), ih₂ x _ h₂ (mul_self_eq_zero.mp hB)⟩
  | or φ ψ ih₁ ih₂ =>
    intro x a h hr
    simp only [NNF.comp, NNF.Holds] at h hr ⊢
    obtain ⟨h₁, h₂, h₃⟩ := Comp.orC_spec h
    rw [h₃] at hr
    rcases mul_eq_zero.mp hr with hr | hr
    · exact Or.inl (ih₁ x a h₁ hr)
    · exact Or.inr (ih₂ x _ h₂ hr)

/-- Every assignment of the original variables extends to a solution of the circuit of a
formula. -/
theorem NNF.comp_sat (ψ : NNF) (x : ℕ → ℝ) : ∃ a, ψ.comp.Sat x a := by
  induction ψ with
  | eq s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    obtain ⟨a, ha, -⟩ := Comp.subC_sat s.comp_wf t.comp_wf h₁ h₂
    exact ⟨a, ha⟩
  | lt s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    obtain ⟨a, ha, -⟩ := Comp.ltC_sat s.comp_wf t.comp_wf h₁ h₂ 0
    exact ⟨a, ha⟩
  | le s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    obtain ⟨a, ha, -⟩ := Comp.leC_sat s.comp_wf t.comp_wf h₁ h₂ 0
    exact ⟨a, ha⟩
  | and φ ψ ih₁ ih₂ =>
    obtain ⟨a₁, h₁⟩ := ih₁
    obtain ⟨a₂, h₂⟩ := ih₂
    obtain ⟨a, ha, -⟩ := Comp.andC_sat φ.comp_wf ψ.comp_wf h₁ h₂
    exact ⟨a, ha⟩
  | or φ ψ ih₁ ih₂ =>
    obtain ⟨a₁, h₁⟩ := ih₁
    obtain ⟨a₂, h₂⟩ := ih₂
    obtain ⟨a, ha, -⟩ := Comp.orC_sat φ.comp_wf ψ.comp_wf h₁ h₂
    exact ⟨a, ha⟩

/-- If the formula holds, the assignment extends to a solution with residual `0`. -/
theorem NNF.comp_complete (ψ : NNF) (x : ℕ → ℝ) (hψ : ψ.Holds x) :
    ∃ a, ψ.comp.Sat x a ∧ Sum.elim x a ψ.comp.res = 0 := by
  induction ψ with
  | eq s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    obtain ⟨a, ha, hr⟩ := Comp.subC_sat s.comp_wf t.comp_wf h₁ h₂
    refine ⟨a, ha, ?_⟩
    simp only [NNF.Holds] at hψ
    simp only [NNF.comp, hr, s.comp_eval x a₁ h₁, t.comp_eval x a₂ h₂, hψ, sub_self]
  | lt s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    simp only [NNF.Holds] at hψ
    have hpos : 0 < t.eval x - s.eval x := by linarith
    obtain ⟨a, ha, hr⟩ := Comp.ltC_sat s.comp_wf t.comp_wf h₁ h₂ (Real.sqrt (t.eval x - s.eval x)⁻¹)
    refine ⟨a, ha, ?_⟩
    simp only [NNF.comp, hr, s.comp_eval x a₁ h₁, t.comp_eval x a₂ h₂,
      Real.mul_self_sqrt (inv_nonneg.mpr hpos.le), mul_inv_cancel₀ hpos.ne', sub_self]
  | le s t =>
    obtain ⟨a₁, h₁⟩ := s.comp_sat x
    obtain ⟨a₂, h₂⟩ := t.comp_sat x
    simp only [NNF.Holds] at hψ
    have hnn : 0 ≤ t.eval x - s.eval x := by linarith
    obtain ⟨a, ha, hr⟩ := Comp.leC_sat s.comp_wf t.comp_wf h₁ h₂ (Real.sqrt (t.eval x - s.eval x))
    refine ⟨a, ha, ?_⟩
    simp only [NNF.comp, hr, s.comp_eval x a₁ h₁, t.comp_eval x a₂ h₂,
      Real.mul_self_sqrt hnn, sub_self]
  | and φ ψ ih₁ ih₂ =>
    obtain ⟨a₁, h₁, r₁⟩ := ih₁ hψ.1
    obtain ⟨a₂, h₂, r₂⟩ := ih₂ hψ.2
    obtain ⟨a, ha, hr⟩ := Comp.andC_sat φ.comp_wf ψ.comp_wf h₁ h₂
    refine ⟨a, ha, ?_⟩
    simp only [NNF.comp, hr, r₁, r₂, mul_zero, add_zero]
  | or φ ψ ih₁ ih₂ =>
    rcases hψ with hψ | hψ
    · obtain ⟨a₁, h₁, r₁⟩ := ih₁ hψ
      obtain ⟨a₂, h₂⟩ := ψ.comp_sat x
      obtain ⟨a, ha, hr⟩ := Comp.orC_sat φ.comp_wf ψ.comp_wf h₁ h₂
      refine ⟨a, ha, ?_⟩
      simp only [NNF.comp, hr, r₁, zero_mul]
    · obtain ⟨a₁, h₁⟩ := φ.comp_sat x
      obtain ⟨a₂, h₂, r₂⟩ := ih₂ hψ
      obtain ⟨a, ha, hr⟩ := Comp.orC_sat φ.comp_wf ψ.comp_wf h₁ h₂
      refine ⟨a, ha, ?_⟩
      simp only [NNF.comp, hr, r₂, mul_zero]

/-! ## The system of a formula -/

/-- Every variable of `φ.toCircuit` is below `φ.circuitVars`. -/
theorem Formula.toCircuit_vars (φ : Formula) : ∀ g ∈ φ.toCircuit, g.VarsLt φ.circuitVars := by
  intro g hg
  simp only [Formula.toCircuit, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  apply CGate.varsLt_toGate
  have hwf : φ.compiled.WF := φ.nnf.1.comp_wf
  have hor : φ.compiled.OrigLt φ.varBound :=
    φ.nnf.1.comp_orig (φ.nnf_varsLt φ.varsLt_varBound).1
  have key : ∀ v, (FLt (φ.compiled.cnt + 1) v ∧ OLt φ.varBound v) →
      place φ.varBound v < φ.circuitVars := by
    rintro (i | j) ⟨h₁, h₂⟩
    · simp only [OLt] at h₂
      simp only [place, Formula.circuitVars]
      omega
    · simp only [FLt] at h₁
      simp only [place, Formula.circuitVars]
      omega
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg'
  rcases hg' with hg' | rfl | rfl
  · exact (((hwf.1 g' hg').mono (fun v hv => hv.mono (Nat.le_succ _))).and (hor.1 g' hg')).mono key
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [place, Formula.circuitVars] <;> omega
  · refine ⟨key _ ⟨hwf.2.mono (Nat.le_succ _), hor.2⟩, ?_, ?_⟩ <;>
      simp only [place, Formula.circuitVars] <;> omega

/-- **Soundness of the circuit**: every solution of `φ.toCircuit` satisfies `φ`. -/
theorem Formula.toCircuit_sound (φ : Formula) (v : ℕ → ℝ) (h : Gate.Solves φ.toCircuit v) :
    φ.Holds v := by
  have hρ : (fun w => v (place φ.varBound w)) = Sum.elim v (fun j => v (φ.varBound + j)) := by
    funext w
    cases w <;> rfl
  have hall : ∀ g ∈ φ.compiled.gates ++ [.add (.inr φ.compiled.cnt) (.inr φ.compiled.cnt)
      (.inr φ.compiled.cnt), .add φ.compiled.res (.inr φ.compiled.cnt) (.inr φ.compiled.cnt)],
      g.Holds (Sum.elim v (fun j => v (φ.varBound + j))) := by
    intro g hg
    have := h _ (List.mem_map_of_mem (f := CGate.toGate φ.varBound) hg)
    rw [CGate.holds_toGate, hρ] at this
    exact this
  rw [List.forall_mem_append] at hall
  obtain ⟨h₁, h₂⟩ := hall
  unfold_new at h₂
  obtain ⟨hz, hr⟩ := h₂
  have hr0 : Sum.elim v (fun j => v (φ.varBound + j)) φ.compiled.res = 0 := by linarith
  exact (φ.nnf_holds v).1.1 (φ.nnf.1.comp_sound v _ h₁ hr0)

/-- **Completeness of the circuit**: a satisfying assignment of `φ` extends to a solution of
`φ.toCircuit`. -/
theorem Formula.toCircuit_complete (φ : Formula) (x : ℕ → ℝ) (h : φ.Holds x) :
    ∃ v, Gate.Solves φ.toCircuit v ∧ ∀ i < φ.varBound, v i = x i := by
  obtain ⟨a, ha, hr⟩ := φ.nnf.1.comp_complete x ((φ.nnf_holds x).1.2 h)
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun i => if i < φ.varBound then x i else
      if i - φ.varBound < φ.compiled.cnt then a (i - φ.varBound) else 0 := ⟨_, rfl⟩
  refine ⟨v, ?_, fun i hi => by rw [hv]; exact ite_eq_left hi⟩
  have hwf : φ.compiled.WF := φ.nnf.1.comp_wf
  have hor : φ.compiled.OrigLt φ.varBound :=
    φ.nnf.1.comp_orig (φ.nnf_varsLt φ.varsLt_varBound).1
  have agree : ∀ w, (FLt φ.compiled.cnt w ∧ OLt φ.varBound w) →
      v (place φ.varBound w) = Sum.elim x a w := by
    rintro (i | j) ⟨h₁, h₂⟩
    · simp only [OLt] at h₂
      simp only [place, hv, Sum.elim_inl, ite_eq_left h₂]
    · simp only [FLt] at h₁
      simp only [place, hv, Sum.elim_inr]
      rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  have hz : v (φ.varBound + φ.compiled.cnt) = 0 := by
    rw [hv]
    simp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hres : v (place φ.varBound φ.compiled.res) = 0 := by
    rw [agree _ ⟨hwf.2, hor.2⟩]
    exact hr
  intro g hg
  simp only [Formula.toCircuit, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rw [CGate.holds_toGate]
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg'
  rcases hg' with hg' | rfl | rfl
  · exact (CGate.holds_congr agree ((hwf.1 g' hg').and (hor.1 g' hg'))).2 (ha g' hg')
  · simp only [CGate.Holds, place_inr, hz, add_zero]
  · simp only [CGate.Holds, place_inr, hz, hres, add_zero]

end ETR

end ArtGallery

end
