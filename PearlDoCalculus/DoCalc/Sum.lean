/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Expr
import PearlDoCalculus.Util.ENNReal

/-!
# Sums over the values of a set of variables

The expression `sum S e` (`DoCalc/Expr`) is read at an assignment `σ` as the sum, over all
assignments `τ` of `S`, of `e` at `updateOn σ S τ`. Three of the probability steps of a
derivation (`docs/design-docalc-completeness.md`, section "Derivations") are laws of such
sums: a sum over the empty set is its summand, a sum over a union of disjoint sets is a
double sum, and two sums over disjoint sets can be swapped. This file proves them, first
for an arbitrary function `f : (∀ v, α v) → ℝ≥0∞` and then for `eval`.

**Updates.** The sums are about the map `updateOn σ S τ`, which replaces the values of
`σ` on `S` by `τ`. The facts used are elementary and are proved pointwise:

* updating with the current values changes nothing (`updateOn_valuesOn`), and neither
  does updating the empty set (`updateOn_empty`);
* an update on `T` does not change the values on a set disjoint from `T`
  (`valuesOn_updateOn_of_disjoint`);
* updates on disjoint sets commute (`updateOn_comm`);
* an update on `S ∪ T` is an update on `S` followed by one on `T`, for disjoint `S`
  and `T`, with the two halves of the assignment joined by `Assignment.join`
  (`updateOn_join`).

**Sums.** A sum over the assignments of `∅` has one term (`tsum_updateOn_empty`). For
disjoint `S` and `T` every assignment of `S ∪ T` is the join of exactly one pair of
assignments of `S` and `T`, so a sum over `S ∪ T` is a double sum
(`tsum_updateOn_union`, by `ENNReal.tsum_eq_tsum_tsum_of_iff`). Two sums over disjoint
sets can be swapped, since the updates commute (`tsum_updateOn_comm`, by
`ENNReal.tsum_comm`). The disjointness in the last two results is what the derivation
steps assume; for the split it is needed, since otherwise the double sum counts every
term once for each value on `S ∩ T`.

**Main results.** `updateOn_valuesOn`, `updateOn_empty`, `valuesOn_updateOn_of_disjoint`,
`updateOn_comm`, `updateOn_join`, `tsum_updateOn_empty`, `tsum_updateOn_union`,
`tsum_updateOn_comm`, and for expressions `eval_sum_empty`, `eval_sum_union`,
`eval_sum_comm`.
-/

open PearlDoCalculus DAG DAG.CausalModel

open scoped ENNReal

namespace DoCalc

variable {V : Type*} [DecidableEq V] {α : V → Type*}

/-! ## Updates -/

section Updates

/-- Updating with the current values changes nothing. -/
@[simp] lemma updateOn_valuesOn (σ : ∀ v, α v) (S : Finset V) :
    updateOn σ S (valuesOn σ S) = σ := by
  funext v
  by_cases hv : v ∈ S
  · simp [updateOn, valuesOn, hv]
  · exact updateOn_of_notMem _ _ hv

/-- Updating the empty set changes nothing. -/
@[simp] lemma updateOn_empty (σ : ∀ v, α v) (τ : Assignment (α := α) (∅ : Finset V)) :
    updateOn σ ∅ τ = σ := by
  funext v
  exact updateOn_of_notMem _ _ (Finset.notMem_empty v)

/-- An update on `T` does not change the values on a set `S` disjoint from `T`. -/
lemma valuesOn_updateOn_of_disjoint (σ : ∀ v, α v) {S T : Finset V} (h : Disjoint S T)
    (τ : Assignment (α := α) T) : valuesOn (updateOn σ T τ) S = valuesOn σ S :=
  valuesOn_congr fun _ hv => updateOn_of_notMem _ _ (Finset.disjoint_left.mp h hv)

/-- **Updates on disjoint sets commute.** -/
lemma updateOn_comm (σ : ∀ v, α v) {S T : Finset V} (h : Disjoint S T)
    (τ₁ : Assignment (α := α) S) (τ₂ : Assignment (α := α) T) :
    updateOn (updateOn σ S τ₁) T τ₂ = updateOn (updateOn σ T τ₂) S τ₁ := by
  funext v
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.mp h hS
    simp [updateOn, hS, hT]
  · by_cases hT : v ∈ T
    · simp [updateOn, hS, hT]
    · simp [updateOn, hS, hT]

/-- **An update on a disjoint union is two updates**, with the two halves joined. -/
lemma updateOn_join (σ : ∀ v, α v) {S T : Finset V} (h : Disjoint S T)
    (τ₁ : Assignment (α := α) S) (τ₂ : Assignment (α := α) T) :
    updateOn σ (S ∪ T) (τ₁.join τ₂) = updateOn (updateOn σ S τ₁) T τ₂ := by
  funext v
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.mp h hS
    simp [updateOn, Assignment.join, hS, hT]
  · by_cases hT : v ∈ T
    · simp [updateOn, Assignment.join, hS, hT]
    · simp [updateOn, hS, hT]

end Updates

/-! ## Sums over updates -/

section Sums

variable (f : (∀ v, α v) → ℝ≥0∞) (σ : ∀ v, α v)

/-- **A sum over the empty set has one term.** -/
lemma tsum_updateOn_empty :
    ∑' τ : Assignment (α := α) (∅ : Finset V), f (updateOn σ ∅ τ) = f σ := by
  let τ₀ : Assignment (α := α) (∅ : Finset V) := fun v => absurd v.2 (Finset.notMem_empty v.1)
  have hτ₀ : ∀ τ, τ = τ₀ := fun τ => funext fun v => absurd v.2 (Finset.notMem_empty v.1)
  rw [tsum_eq_single τ₀ (fun τ hτ => absurd (hτ₀ τ) hτ), updateOn_empty]

/-- **A sum over a disjoint union is a double sum.** -/
lemma tsum_updateOn_union {S T : Finset V} (h : Disjoint S T) :
    ∑' τ : Assignment (α := α) (S ∪ T), f (updateOn σ (S ∪ T) τ) =
      ∑' τ₁ : Assignment (α := α) S, ∑' τ₂ : Assignment (α := α) T,
        f (updateOn (updateOn σ S τ₁) T τ₂) := by
  have hsplit : ∀ (c : Assignment (α := α) (S ∪ T)) (a : Assignment (α := α) S)
      (b : Assignment (α := α) T), c = a.join b ↔
        a = c.restrict Finset.subset_union_left ∧ b = c.restrict Finset.subset_union_right := by
    intro c a b
    constructor
    · rintro rfl
      refine ⟨(Assignment.restrict_join_left a b).symm,
        (Assignment.restrict_join_right a b fun v ha hb => ?_).symm⟩
      exact absurd hb (Finset.disjoint_left.mp h ha)
    · rintro ⟨rfl, rfl⟩
      funext ⟨v, hv⟩
      by_cases hS : v ∈ S
      · simp [Assignment.join, Assignment.restrict, hS]
      · simp [Assignment.join, Assignment.restrict, hS]
  rw [ENNReal.tsum_eq_tsum_tsum_of_iff
    (fun (a : Assignment (α := α) S) (b : Assignment (α := α) T) => a.join b) _ _ hsplit]
  simp only [updateOn_join σ h]

/-- **Two sums over disjoint sets can be swapped.** -/
lemma tsum_updateOn_comm {S T : Finset V} (h : Disjoint S T) :
    ∑' τ₁ : Assignment (α := α) S, ∑' τ₂ : Assignment (α := α) T,
        f (updateOn (updateOn σ S τ₁) T τ₂) =
      ∑' τ₂ : Assignment (α := α) T, ∑' τ₁ : Assignment (α := α) S,
        f (updateOn (updateOn σ T τ₂) S τ₁) := by
  rw [ENNReal.tsum_comm]
  simp only [updateOn_comm σ h]

end Sums

/-! ## Sums of expressions -/

section Expressions

variable [Fintype V] {G : DAG V} (M : G.CausalModel α) (σ : ∀ v, α v)

/-- A sum over the empty set is its summand. -/
lemma eval_sum_empty (e : Expr V) : eval M (.sum ∅ e) σ = eval M e σ :=
  tsum_updateOn_empty (eval M e) σ

/-- A sum over a disjoint union is a double sum. -/
lemma eval_sum_union {S T : Finset V} (h : Disjoint S T) (e : Expr V) :
    eval M (.sum (S ∪ T) e) σ = eval M (.sum S (.sum T e)) σ :=
  tsum_updateOn_union (eval M e) σ h

/-- Two sums over disjoint sets can be swapped. -/
lemma eval_sum_comm {S T : Finset V} (h : Disjoint S T) (e : Expr V) :
    eval M (.sum S (.sum T e)) σ = eval M (.sum T (.sum S e)) σ :=
  tsum_updateOn_comm (eval M e) σ h

end Expressions

end DoCalc
