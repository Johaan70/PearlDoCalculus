/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Adjustment

/-!
# Expressions of the do-calculus: syntax and semantics

This file starts the formalization of the completeness of the do-calculus for
identification (`docs/design-docalc-completeness.md`, phase 1). The goal of that project
is to show that every identifiable effect `P(Y | do(X))` can be rewritten, by the three
rules of the do-calculus and a fixed list of probability steps, into an expression
without `do` that mentions only observed variables. To state this we need a syntax for
such expressions, and a meaning for them in a causal model. Both are defined here.

**Syntax.** An `Expr V` is built from

* `prob Y Z X`, read as `P(Y | Z, do(X))`;
* `one`, the constant `1`;
* `mul e₁ e₂` and `div e₁ e₂`, product and quotient;
* `sum S e`, the sum of `e` over all values of the variables in `S`.

There are no names for values. An expression is read at one total assignment `σ` of all
the variables, and `sum S e` ranges over the values of the set `S`. So there is no
variable capture, and every rule is a statement about finite sets. `query Y X` is the
effect `P(Y | do(X))`, that is `prob Y ∅ X`.

**Predicates on expressions.** `DoFree e` says that no `prob` in `e` has an
intervention. `vars e` is the set of variables that occur in `e`, and `free e` the set
of variables that `e` reads from the assignment (`vars` minus those bound by an
enclosing `sum`). `WellFormed e` says that in every `prob Y Z X` of `e` the three sets
are pairwise disjoint and `Y` is nonempty.

**Semantics.** `eval M e σ ∈ ℝ≥0∞` is the value of `e` in the causal model `M` at the
assignment `σ : ∀ v, α v`.

* `prob Y Z X` is `P_x(y, z) / P_x(z)`: two marginals of the intervened model
  `doModel M X x` (from `DoCalculus`) with `x = σ_X`, `y = σ_Y`, `z = σ_Z`. We write
  `doProb M X S σ` for `P_{do(X = σ_X)}(S = σ_S)`.
* `one` is `1`, and `mul`, `div` are pointwise.
* `sum S e` at `σ` is the sum, over all assignments `τ` of `S`, of `e` at `σ` with the
  values on `S` replaced by `τ` (`updateOn σ S τ`). The sum is a `tsum`, as in the rest of
  the project.

Division is the only delicate point. When `Z = ∅` the denominator is the marginal on
`∅`, which is `1` (`eval_query`). In general the denominator can be `0`; the companion
file `DoCalc/Positivity` shows that this does not happen when the observed marginal is
positive and all variables are observed.

**Main results.** The definitions `Expr`, `Expr.query`, `Expr.DoFree`, `Expr.vars`,
`Expr.free`, `Expr.WellFormed`, `doProb` and `eval`; the equations `eval_prob`,
`eval_one`, `eval_mul`, `eval_div`, `eval_sum`, `eval_query`; `doProb_empty` (without
intervention `doProb` is an observed marginal) and `eval_congr_free` (`eval` reads only
the free variables).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus

open scoped ENNReal

namespace DoCalc

/-! ## Syntax -/

/-- Expressions of the do-calculus over the variables `V`. They are read at one total
assignment of the variables; `sum S e` sums over the values of the set `S`. -/
inductive Expr (V : Type*) where
  /-- `P(Y | Z, do(X))`, read at the current values of `Y`, `Z` and `X`. -/
  | prob (Y Z X : Finset V)
  /-- The constant `1`. -/
  | one
  /-- The product of two expressions. -/
  | mul (e₁ e₂ : Expr V)
  /-- The quotient of two expressions. -/
  | div (e₁ e₂ : Expr V)
  /-- The sum of `e` over all values of the variables in `S`. -/
  | sum (S : Finset V) (e : Expr V)

namespace Expr

variable {V : Type*}

/-- The effect `P(Y | do(X))`. -/
def query (Y X : Finset V) : Expr V := prob Y ∅ X

/-! ## Predicates on expressions -/

/-- No `prob` in `e` has an intervention. -/
@[simp] def DoFree : Expr V → Prop
  | prob _ _ X => X = ∅
  | one => True
  | mul e₁ e₂ => e₁.DoFree ∧ e₂.DoFree
  | div e₁ e₂ => e₁.DoFree ∧ e₂.DoFree
  | sum _ e => e.DoFree

/-- In every `prob Y Z X` of `e`, the sets `Y`, `Z` and `X` are pairwise disjoint and
`Y` is nonempty. -/
@[simp] def WellFormed : Expr V → Prop
  | prob Y Z X => Y.Nonempty ∧ Disjoint Y Z ∧ Disjoint Y X ∧ Disjoint Z X
  | one => True
  | mul e₁ e₂ => e₁.WellFormed ∧ e₂.WellFormed
  | div e₁ e₂ => e₁.WellFormed ∧ e₂.WellFormed
  | sum _ e => e.WellFormed

/-- `query Y X` has no intervention exactly when `X = ∅`. -/
@[simp] lemma doFree_query (Y X : Finset V) : (query Y X).DoFree ↔ X = ∅ := Iff.rfl

/-- `query Y X` is well formed exactly when `Y` is nonempty and disjoint from `X`. -/
@[simp] lemma wellFormed_query (Y X : Finset V) :
    (query Y X).WellFormed ↔ Y.Nonempty ∧ Disjoint Y X := by
  simp [query]

variable [DecidableEq V]

/-- The variables that occur in `e`: the sets of every `prob` and every summed set. -/
@[simp] def vars : Expr V → Finset V
  | prob Y Z X => Y ∪ Z ∪ X
  | one => ∅
  | mul e₁ e₂ => e₁.vars ∪ e₂.vars
  | div e₁ e₂ => e₁.vars ∪ e₂.vars
  | sum S e => S ∪ e.vars

/-- The variables that `e` reads from the assignment: those of `vars e` that are not
bound by an enclosing `sum`. -/
@[simp] def free : Expr V → Finset V
  | prob Y Z X => Y ∪ Z ∪ X
  | one => ∅
  | mul e₁ e₂ => e₁.free ∪ e₂.free
  | div e₁ e₂ => e₁.free ∪ e₂.free
  | sum S e => e.free \ S

/-- Every free variable occurs. -/
lemma free_subset_vars (e : Expr V) : e.free ⊆ e.vars := by
  induction e with
  | prob Y Z X => exact Finset.Subset.refl _
  | one => exact Finset.Subset.refl _
  | mul e₁ e₂ h₁ h₂ => exact Finset.union_subset_union h₁ h₂
  | div e₁ e₂ h₁ h₂ => exact Finset.union_subset_union h₁ h₂
  | sum S e h => exact Finset.sdiff_subset.trans (h.trans Finset.subset_union_right)

/-- The variables of `query Y X` are `Y ∪ X`. -/
@[simp] lemma vars_query (Y X : Finset V) : (query Y X).vars = Y ∪ X := by
  simp [query]

/-- The free variables of `query Y X` are `Y ∪ X`. -/
@[simp] lemma free_query (Y X : Finset V) : (query Y X).free = Y ∪ X := by
  simp [query]

end Expr

/-! ## Reading an assignment on a set -/

section Assignments

variable {V : Type*} {α : V → Type*}

/-- The values of the total assignment `σ` on the set `S`. -/
def valuesOn (σ : ∀ v, α v) (S : Finset V) : Assignment (α := α) S := fun v => σ v.1

/-- Restricting the values on `S` to `T ⊆ S` gives the values on `T`. -/
@[simp] lemma restrict_valuesOn (σ : ∀ v, α v) {S T : Finset V} (h : T ⊆ S) :
    (valuesOn σ S).restrict h = valuesOn σ T := rfl

/-- Two assignments that agree on `S` have the same values on `S`. -/
lemma valuesOn_congr {σ σ' : ∀ v, α v} {S : Finset V} (h : ∀ v ∈ S, σ v = σ' v) :
    valuesOn σ S = valuesOn σ' S := by
  funext ⟨v, hv⟩
  exact h v hv

variable [DecidableEq V]

/-- `σ` with the values on `S` replaced by `τ`. -/
def updateOn (σ : ∀ v, α v) (S : Finset V) (τ : Assignment (α := α) S) : ∀ v, α v :=
  fun v => if h : v ∈ S then τ ⟨v, h⟩ else σ v

/-- After the update, the values on `S` are `τ`. -/
@[simp] lemma valuesOn_updateOn (σ : ∀ v, α v) (S : Finset V) (τ : Assignment (α := α) S) :
    valuesOn (updateOn σ S τ) S = τ := by
  funext ⟨v, hv⟩
  simp [valuesOn, updateOn, hv]

/-- Outside `S` the update changes nothing. -/
lemma updateOn_of_notMem (σ : ∀ v, α v) {S : Finset V} (τ : Assignment (α := α) S)
    {v : V} (hv : v ∉ S) : updateOn σ S τ v = σ v := by
  simp [updateOn, hv]

end Assignments

/-! ## Semantics -/

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `P_{do(X = σ_X)}(S = σ_S)`: the marginal on `S` of the model under the intervention
`do(X = σ_X)`, at the values of `σ` on `S`. -/
noncomputable def doProb (M : G.CausalModel α) (X S : Finset V) (σ : ∀ v, α v) : ℝ≥0∞ :=
  (doModel M X (valuesOn σ X)).marginal S (valuesOn σ S)

/-- The value of an expression in the model `M` at the total assignment `σ`. -/
noncomputable def eval (M : G.CausalModel α) : Expr V → (∀ v, α v) → ℝ≥0∞
  | .prob Y Z X, σ => doProb M X (Y ∪ Z) σ / doProb M X Z σ
  | .one, _ => 1
  | .mul e₁ e₂, σ => eval M e₁ σ * eval M e₂ σ
  | .div e₁ e₂, σ => eval M e₁ σ / eval M e₂ σ
  | .sum S e, σ => ∑' τ : Assignment (α := α) S, eval M e (updateOn σ S τ)

section EvalEquations

variable (M : G.CausalModel α) (σ : ∀ v, α v)

@[simp] lemma eval_prob (Y Z X : Finset V) :
    eval M (.prob Y Z X) σ = doProb M X (Y ∪ Z) σ / doProb M X Z σ := rfl

@[simp] lemma eval_one : eval M .one σ = 1 := rfl

@[simp] lemma eval_mul (e₁ e₂ : Expr V) :
    eval M (.mul e₁ e₂) σ = eval M e₁ σ * eval M e₂ σ := rfl

@[simp] lemma eval_div (e₁ e₂ : Expr V) :
    eval M (.div e₁ e₂) σ = eval M e₁ σ / eval M e₂ σ := rfl

@[simp] lemma eval_sum (S : Finset V) (e : Expr V) :
    eval M (.sum S e) σ = ∑' τ : Assignment (α := α) S, eval M e (updateOn σ S τ) := rfl

/-- The marginal on `∅` is `1`, under every intervention. -/
@[simp] lemma doProb_emptyset (X : Finset V) : doProb M X ∅ σ = 1 :=
  Adjustment.marginal_empty _ _

/-- **The effect `P(Y | do(X))`.** The denominator of `query Y X` is the marginal on `∅`,
so `query Y X` evaluates to `P_{do(X = σ_X)}(Y = σ_Y)`. -/
@[simp] lemma eval_query (Y X : Finset V) : eval M (Expr.query Y X) σ = doProb M X Y σ := by
  simp [Expr.query]

/-- **Without intervention, `doProb` is an observed marginal.** `do(∅)` changes nothing
(`doModel_empty`). -/
lemma doProb_empty (S : Finset V) :
    doProb M ∅ S σ = M.marginal S (valuesOn σ S) := by
  unfold doProb CausalModel.marginal
  rw [show (doModel M ∅ (valuesOn σ ∅)).fullJoint = M.fullJoint from
    PMF.ext (doModel_empty M _)]

end EvalEquations

/-- **`eval` reads only the free variables.** Two assignments that agree on `free e`
give `e` the same value. -/
lemma eval_congr_free (M : G.CausalModel α) (e : Expr V) {σ σ' : ∀ v, α v}
    (h : ∀ v ∈ e.free, σ v = σ' v) : eval M e σ = eval M e σ' := by
  induction e generalizing σ σ' with
  | prob Y Z X =>
    have hS : ∀ S, S ⊆ Y ∪ Z ∪ X → valuesOn σ S = valuesOn σ' S :=
      fun S hS => valuesOn_congr (fun v hv => h v (hS hv))
    have hX : X ⊆ Y ∪ Z ∪ X := Finset.subset_union_right
    have hYZ : Y ∪ Z ⊆ Y ∪ Z ∪ X := Finset.subset_union_left
    have hZ : Z ⊆ Y ∪ Z ∪ X := Finset.subset_union_right.trans hYZ
    simp only [eval_prob, doProb, hS X hX, hS _ hYZ, hS Z hZ]
  | one => rfl
  | mul e₁ e₂ h₁ h₂ =>
    simp only [Expr.free, Finset.mem_union] at h
    simp only [eval_mul, h₁ (fun v hv => h v (Or.inl hv)), h₂ (fun v hv => h v (Or.inr hv))]
  | div e₁ e₂ h₁ h₂ =>
    simp only [Expr.free, Finset.mem_union] at h
    simp only [eval_div, h₁ (fun v hv => h v (Or.inl hv)), h₂ (fun v hv => h v (Or.inr hv))]
  | sum S e ih =>
    simp only [Expr.free, Finset.mem_sdiff] at h
    simp only [eval_sum]
    refine tsum_congr (fun τ => ih (fun v hv => ?_))
    by_cases hvS : v ∈ S
    · simp [updateOn, hvS]
    · rw [updateOn_of_notMem _ _ hvS, updateOn_of_notMem _ _ hvS]
      exact h v ⟨hv, hvS⟩

end DoCalc
