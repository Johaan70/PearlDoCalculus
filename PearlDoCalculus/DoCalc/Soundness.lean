/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Rules
import PearlDoCalculus.DoCalc.Sum

/-!
# Soundness of derivations

A derivation `Derives G U e₁ e₂` (`DoCalc/Derives`) is only worth something if each of its
steps is valid. This file proves that it is: `e₁` and `e₂` have the same value, at every
assignment, in every causal model on `G` whose observed marginal (on `Uᶜ`) is positive
(`derives_sound`). This is the class of models of `Identification.Identifiable`
(`docs/design-docalc-completeness.md`, decision 2).

**How the proof goes.** By induction on the derivation, one case per step.

* *Equality steps.* Reflexivity, symmetry and transitivity of equality; congruence
  because `eval` is defined pointwise.
* *The rules.* `eval_rule1`, `eval_rule2`, `eval_rule3` (`DoCalc/Rules`), from the rule
  theorems in product form.
* *Marginalization.* Under one intervention, summing the marginal on `S ∪ W` over the
  values of `W` gives the marginal on `S` (`marginal_tsum_updateOn`); the denominator does
  not read `W` and comes out of the sum (`eval_marg`).
* *Chain rule.* `a / c = (a / b) · (b / c)` for the three marginals `a`, `b`, `c` of the
  chain rule. If `b = 0`, then `a = 0` as well, since `a` is the mass of an assignment
  that restricts to `b`'s; otherwise `b` cancels (`eval_chain`). No positivity is needed.
* *Semiring laws* are those of `ℝ≥0∞`; the unit law of `sum` is `eval_sum_empty`
  (`DoCalc/Sum`).
* *Cancellations.* The divisor is `Positive`, so it is neither `0` nor `∞`
  (`eval_positive`, `DoCalc/Positivity`).
* *Sums.* Pulling a factor out of a sum uses that the factor does not read the summed
  variables (`eval_congr_free`, `eval_sum_mul`); splitting and swapping sums are
  `eval_sum_union` and `eval_sum_comm` (`DoCalc/Sum`).

**Consequence.** If `P(Y | do(X))` derives an expression without `do` over observed
variables, the effect is identifiable (`identifiable_of_derives`): two positive models
with the same observed marginal give such an expression the same value
(`eval_eq_of_doFree`), and soundness transports this to the effect.

**Main results.** `marginal_tsum_updateOn`, `eval_marg`, `eval_chain`, `eval_sum_mul`,
`derives_sound`, `eval_eq_of_doFree`, `identifiable_of_derives`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification

open scoped ENNReal

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-! ## Marginalization and the chain rule -/

/-- **Summing out a set.** Summing the marginal on `S ∪ W` over the values of `W`, with
the values on `S` fixed by `σ`, gives the marginal on `S`, for `W` disjoint from `S`. -/
lemma marginal_tsum_updateOn {H : DAG V} (N : H.CausalModel α) {S W : Finset V}
    (h : Disjoint S W) (σ : ∀ v, α v) :
    ∑' τ : Assignment (α := α) W, N.marginal (S ∪ W) (valuesOn (updateOn σ W τ) (S ∪ W)) =
      N.marginal S (valuesOn σ S) := by
  classical
  rw [← marginal_restrict N (Finset.subset_union_left : S ⊆ S ∪ W), PMF.map_apply]
  refine (ENNReal.tsum_ite_eq_tsum_of_iff (fun τ => valuesOn (updateOn σ W τ) (S ∪ W))
    (fun c => c.restrict Finset.subset_union_left) (fun c => c.restrict Finset.subset_union_right)
    (valuesOn σ S) (fun c τ => ?_) _).symm
  constructor
  · rintro rfl
    exact ⟨(valuesOn_updateOn_of_disjoint σ h τ).symm, (valuesOn_updateOn σ W τ).symm⟩
  · rintro ⟨hS, rfl⟩
    funext ⟨v, hv⟩
    by_cases hW : v ∈ W
    · simp [valuesOn, updateOn, Assignment.restrict, hW]
    · have hvS : v ∈ S := (Finset.mem_union.mp hv).resolve_right hW
      show c ⟨v, hv⟩ = updateOn σ W (c.restrict Finset.subset_union_right) v
      rw [updateOn_of_notMem _ _ hW]
      exact (congrFun hS ⟨v, hvS⟩).symm

variable (M : G.CausalModel α) (σ : ∀ v, α v)

/-- **Marginalization for expressions.** `P(Y | Z, do X) = Σ_W P(Y ∪ W | Z, do X)` for `W`
disjoint from `Y ∪ Z ∪ X`. -/
theorem eval_marg (Y Z X W : Finset V) (h : Disjoint W (Y ∪ Z ∪ X)) :
    eval M (.prob Y Z X) σ = eval M (.sum W (.prob (Y ∪ W) Z X)) σ := by
  have hX : Disjoint X W := (Finset.disjoint_of_subset_right Finset.subset_union_right h).symm
  have hZ : Disjoint Z W := (Finset.disjoint_of_subset_right
    (Finset.subset_union_right.trans Finset.subset_union_left) h).symm
  have hYZ : Disjoint (Y ∪ Z) W := (Finset.disjoint_of_subset_right Finset.subset_union_left h).symm
  simp only [eval_sum, eval_prob, doProb, valuesOn_updateOn_of_disjoint σ hX,
    valuesOn_updateOn_of_disjoint σ hZ, div_eq_mul_inv]
  rw [Finset.union_right_comm Y W Z, ENNReal.tsum_mul_right, marginal_tsum_updateOn _ hYZ]

/-- **The chain rule for expressions.**
`P(Y ∪ W | Z, do X) = P(Y | W ∪ Z, do X) · P(W | Z, do X)`, with no side condition. -/
theorem eval_chain (Y W Z X : Finset V) :
    eval M (.prob (Y ∪ W) Z X) σ = eval M (.mul (.prob Y (W ∪ Z) X) (.prob W Z X)) σ := by
  simp only [eval_prob, eval_mul, Finset.union_assoc Y W Z]
  by_cases hb : doProb M X (W ∪ Z) σ = 0
  · have ha : doProb M X (Y ∪ (W ∪ Z)) σ = 0 := by
      by_contra ha
      exact marginal_restrict_ne_zero (doModel M X (valuesOn σ X))
        (Finset.subset_union_right : W ∪ Z ⊆ Y ∪ (W ∪ Z)) (valuesOn σ _) ha hb
    rw [ha, hb]
    simp
  · simp only [div_eq_mul_inv]
    rw [show ∀ a b c : ℝ≥0∞, a * b⁻¹ * (b * c⁻¹) = a * c⁻¹ * (b⁻¹ * b) from
      fun a b c => by ring, ENNReal.inv_mul_cancel hb (doProb_ne_top M X _ σ), mul_one]

/-- **Pulling a factor out of a sum**, when the factor does not read the summed
variables. -/
theorem eval_sum_mul (S : Finset V) (a e : Expr V) (h : Disjoint S a.free) :
    eval M (.sum S (.mul a e)) σ = eval M (.mul a (.sum S e)) σ := by
  simp only [eval_sum, eval_mul]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun τ => ?_
  rw [eval_congr_free M a (fun v hv => updateOn_of_notMem σ τ (Finset.disjoint_right.mp h hv))]

/-! ## Soundness -/

/-- **Soundness of derivations.** If `e₁` derives `e₂`, they have the same value in every
model on `G` with a positive observed marginal. -/
theorem derives_sound {U : Finset V} {e₁ e₂ : Expr V} (hd : Derives G U e₁ e₂)
    (M : G.CausalModel α) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0) : eval M e₁ = eval M e₂ := by
  induction hd with
  | refl e => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul _ _ ih₁ ih₂ => funext σ; simp only [eval_mul, ih₁, ih₂]
  | div _ _ ih₁ ih₂ => funext σ; simp only [eval_div, ih₁, ih₂]
  | sum S _ ih => funext σ; simp only [eval_sum, ih]
  | rule1 X Y Z W hY hW hO h => funext σ; exact eval_rule1 M U hpos X Y Z W hY hW hO h σ
  | rule2 X Y Z W hYZ hXWZ hYXW hO h =>
    funext σ; exact eval_rule2 M U hpos X Y Z W hYZ hXWZ hYXW hO h σ
  | rule3 X Y Z W hYZ hXWZ hYXW hO h =>
    funext σ; exact eval_rule3 M U hpos X Y Z W hYZ hXWZ hYXW hO h σ
  | marg Y Z X W h => funext σ; exact eval_marg M σ Y Z X W h
  | chain Y W Z X => funext σ; exact eval_chain M σ Y W Z X
  | mul_comm a b => funext σ; exact mul_comm _ _
  | mul_assoc a b c => funext σ; exact mul_assoc _ _ _
  | one_mul a => funext σ; exact one_mul _
  | sum_empty e => funext σ; exact eval_sum_empty M σ e
  | div_self e he =>
    funext σ
    obtain ⟨h0, ht⟩ := eval_positive M U hpos he σ
    exact ENNReal.div_self h0 ht
  | mul_div_cancel a b hb =>
    funext σ
    obtain ⟨h0, ht⟩ := eval_positive M U hpos hb σ
    exact ENNReal.mul_div_cancel_right h0 ht
  | sum_mul S a e h => funext σ; exact eval_sum_mul M σ S a e h
  | sum_union S T e h => funext σ; exact eval_sum_union M σ h e
  | sum_comm S T e h => funext σ; exact eval_sum_comm M σ h e

/-! ## Derivations give identifiability -/

/-- **An expression without `do` over observed variables is identified.** Two models with
the same marginal on `O` give it the same value, if it mentions only variables of `O`. -/
theorem eval_eq_of_doFree {M₁ M₂ : G.CausalModel α} {O : Finset V}
    (hM : M₁.marginal O = M₂.marginal O) {e : Expr V} (hfree : e.DoFree) (hvars : e.vars ⊆ O) :
    eval M₁ e = eval M₂ e := by
  induction e with
  | prob Y Z X =>
    simp only [Expr.DoFree] at hfree
    subst hfree
    simp only [Expr.vars, Finset.union_empty] at hvars
    funext σ
    rw [eval_prob, eval_prob, doProb_empty, doProb_empty, doProb_empty, doProb_empty,
      marginal_eq_of_subset hM hvars,
      marginal_eq_of_subset hM (Finset.subset_union_right.trans hvars)]
  | one => rfl
  | mul e₁ e₂ h₁ h₂ =>
    simp only [Expr.vars, Finset.union_subset_iff] at hvars
    funext σ
    simp only [eval_mul, h₁ hfree.1 hvars.1, h₂ hfree.2 hvars.2]
  | div e₁ e₂ h₁ h₂ =>
    simp only [Expr.vars, Finset.union_subset_iff] at hvars
    funext σ
    simp only [eval_div, h₁ hfree.1 hvars.1, h₂ hfree.2 hvars.2]
  | sum S e ih =>
    simp only [Expr.vars, Finset.union_subset_iff] at hvars
    funext σ
    simp only [eval_sum, ih hfree hvars.2]

/-- **A derivation of the effect gives identifiability.** If `P(Y | do(X))` derives an
expression without `do` that mentions only observed variables, then `P(Y | do(X))` is
identifiable in the sense of `Identification.Identifiable`, for every family of value
types. -/
theorem identifiable_of_derives {U X Y : Finset V} {e : Expr V}
    (hd : Derives G U (Expr.query Y X) e) (hfree : e.DoFree) (hvars : e.vars ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  intro M₁ M₂ hM hpos t
  haveI : ∀ v, Nonempty (α v) := nonempty_of_model M₁
  have hpos₂ : ∀ a, M₂.marginal Uᶜ a ≠ 0 := fun a => hM ▸ hpos a
  let σ : ∀ v, α v := fun v => if hv : v ∈ Y ∪ X then t ⟨v, hv⟩ else Classical.arbitrary _
  have key : doProb M₁ X Y σ = doProb M₂ X Y σ := by
    rw [← eval_query, ← eval_query, congrFun (derives_sound hd M₁ hpos) σ,
      congrFun (derives_sound hd M₂ hpos₂) σ, eval_eq_of_doFree hM hfree hvars]
  have hS : ∀ (S : Finset V) (hS : S ⊆ Y ∪ X), valuesOn σ S = t.restrict hS := by
    intro S hS
    funext ⟨v, hv⟩
    show (if h : v ∈ Y ∪ X then t ⟨v, h⟩ else _) = t ⟨v, hS hv⟩
    rw [dif_pos (hS hv)]
  unfold doProb at key
  rwa [hS X Finset.subset_union_right, hS Y Finset.subset_union_left] at key

end DoCalc
