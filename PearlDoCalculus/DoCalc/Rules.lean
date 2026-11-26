/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Derives
import PearlDoCalculus.Idc

/-!
# The three rules of the do-calculus for expressions

A derivation (`DoCalc/Derives`) may rewrite one `prob` term by one of the three rules of the
do-calculus. This file shows that each such rewrite preserves the value of the term in
every model with a positive observed marginal (`eval_rule1`, `eval_rule2`, `eval_rule3`).
These are the rule cases of the soundness theorem `derives_sound` (`DoCalc/Soundness`).

The rules are not proved again. The existing theorems `DoCalculus.rule1`,
`DoCalculus.rule2` and `Rule3Flag.rule3_general` state them as an equation between two
products of interventional marginals, `A · D = C · B`, without positivity. The value of
the two `prob` terms is `A / B` and `C / D`, so it suffices to divide by the
denominators `B` and `D`, which are positive and finite when the sets they are taken on
are observed (`doProb_ne_zero`, `doProb_ne_top`).

**Bookkeeping.** Three small facts translate the rule theorems into the language of
`doProb`.

* *The intervened variables can be added.* Under `do(X = σ_X)` the variables of `X` have
  the values `σ_X` with probability one, so adding variables of `X` to the set of a
  marginal does not change it (`doProb_union_of_subset`, `doProb_eq_of_union_eq`). The
  rule theorems condition on `X ∪ W`; the `prob` terms on `W` only.
* *Two interventions are one.* `do(X = σ_X)` followed by `do(Z = σ_Z)` is
  `do(X ∪ Z = σ_{X ∪ Z})` for disjoint `X` and `Z` (`doProb_doModel`, from
  `Idc.doModel_doModel_marginal`). Rules 2 and 3 are stated with nested interventions.
* *Values on a union.* Joining the values of `σ` on `A` and on `B` gives its values on
  `A ∪ B` (`valuesOn_join`).

At a total assignment `σ` the assignment `t` of the rule theorems is `valuesOn σ` of the
union of all their sets, and every restriction of it is again a `valuesOn σ`, by
definition.

**Main results.** `doProb_union_of_subset`, `doProb_eq_of_union_eq`, `doProb_doModel`,
`eval_rule1`, `eval_rule2`, `eval_rule3`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus

open scoped ENNReal

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-! ## Bookkeeping for `doProb` -/

omit [Fintype V] in
/-- Joining the values of `σ` on `A` and on `B` gives its values on `A ∪ B`. -/
lemma valuesOn_join (σ : ∀ v, α v) (A B : Finset V) :
    (valuesOn σ A).join (valuesOn σ B) = valuesOn σ (A ∪ B) := by
  funext ⟨v, hv⟩
  by_cases hA : v ∈ A
  · simp [Assignment.join, valuesOn, hA]
  · simp [Assignment.join, valuesOn, hA]

/-- **The intervened variables can be added.** Under `do(X = σ_X)`, the marginal on
`S ∪ T` with `T ⊆ X` is the marginal on `S`: every other assignment of `S ∪ T` that agrees
with `σ` on `S` differs from `σ_X` on `X`, so it has probability `0`. -/
lemma doProb_union_of_subset (M : G.CausalModel α) (X S T : Finset V) (hT : T ⊆ X)
    (σ : ∀ v, α v) : doProb M X (S ∪ T) σ = doProb M X S σ := by
  unfold doProb
  rw [← marginal_restrict (doModel M X (valuesOn σ X)) (Finset.subset_union_left : S ⊆ S ∪ T),
    PMF.map_apply, tsum_eq_single (valuesOn σ (S ∪ T))]
  · exact (if_pos rfl).symm
  · intro t ht
    split_ifs with h
    · obtain ⟨⟨v, hv⟩, hne⟩ := Function.ne_iff.mp ht
      have hvS : v ∉ S := fun hvS => hne (congrFun h ⟨v, hvS⟩).symm
      have hvT : v ∈ T := (Finset.mem_union.mp hv).resolve_left hvS
      exact Idc.doModel_marginal_eq_zero M X (valuesOn σ X) (S ∪ T) t v hv (hT hvT) hne
    · rfl

/-- Under `do(X)`, two sets that differ only by variables of `T ⊆ X` have the same
marginal. -/
lemma doProb_eq_of_union_eq (M : G.CausalModel α) {X S S' T : Finset V} (hT : T ⊆ X)
    (h : S ∪ T = S' ∪ T) (σ : ∀ v, α v) : doProb M X S σ = doProb M X S' σ := by
  rw [← doProb_union_of_subset M X S T hT, h, doProb_union_of_subset M X S' T hT]

/-- **Two interventions are one.** `do(X = σ_X)` followed by `do(Z = σ_Z)` is
`do(X ∪ Z = σ_{X ∪ Z})`, for disjoint `X` and `Z`. -/
lemma doProb_doModel (M : G.CausalModel α) {X Z : Finset V} (hXZ : Disjoint X Z)
    (S : Finset V) (σ : ∀ v, α v) :
    (doModel (doModel M X (valuesOn σ X)) Z (valuesOn σ Z)).marginal S (valuesOn σ S) =
      doProb M (X ∪ Z) S σ := by
  rw [Idc.doModel_doModel_marginal M X Z hXZ, valuesOn_join]
  rfl

/-! ## The rules -/

section Rules

variable (M : G.CausalModel α) (U : Finset V) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0)
include hpos

/-- **Rule 1 for expressions.** `P(Y | Z, W, do(X)) = P(Y | Z, do(X))` when `Y` and `W`
are d-separated by `X ∪ Z` in `G_{X̄}`, from `DoCalculus.rule1`. -/
theorem eval_rule1 (X Y Z W : Finset V) (hY : Disjoint Y (X ∪ Z)) (hW : Disjoint W (X ∪ Z))
    (hO : Z ∪ W ∪ X ⊆ Uᶜ) (h : SetSound.DSeparatedSet (cutIn G X) (X ∪ Z) Y W)
    (σ : ∀ v, α v) : eval M (.prob Y (Z ∪ W) X) σ = eval M (.prob Y Z X) σ := by
  have hX : X ⊆ Uᶜ := Finset.subset_union_right.trans hO
  have hZW : Z ∪ W ⊆ Uᶜ := Finset.subset_union_left.trans hO
  have hZ : Z ⊆ Uᶜ := Finset.subset_union_left.trans hZW
  have r : doProb M X (Y ∪ W ∪ (X ∪ Z)) σ * doProb M X (X ∪ Z) σ =
      doProb M X (Y ∪ (X ∪ Z)) σ * doProb M X (W ∪ (X ∪ Z)) σ :=
    rule1 M X Z Y W (valuesOn σ X) hY hW h (valuesOn σ _)
  rw [doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ W ∪ (X ∪ Z) ∪ X = Y ∪ (Z ∪ W) ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        X ∪ Z ∪ X = Z ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ (X ∪ Z) ∪ X = Y ∪ Z ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        W ∪ (X ∪ Z) ∪ X = Z ∪ W ∪ X)] at r
  rw [eval_prob, eval_prob, ENNReal.div_eq_div_iff (doProb_ne_zero M U hpos hX hZ σ)
    (doProb_ne_top M X Z σ) (doProb_ne_zero M U hpos hX hZW σ) (doProb_ne_top M X _ σ),
    mul_comm (doProb M X Z σ), mul_comm (doProb M X (Z ∪ W) σ), r]

/-- **Rule 2 for expressions.** `P(Y | Z, W, do(X)) = P(Y | W, do(X ∪ Z))` when `Y` and
`Z` are d-separated by `X ∪ W` in `G_{X̄Z̲}`, from `DoCalculus.rule2`. -/
theorem eval_rule2 (X Y Z W : Finset V) (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z)
    (hYXW : Disjoint Y (X ∪ W)) (hO : Z ∪ W ∪ X ⊆ Uᶜ)
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z) (σ : ∀ v, α v) :
    eval M (.prob Y (Z ∪ W) X) σ = eval M (.prob Y W (X ∪ Z)) σ := by
  have hX : X ⊆ Uᶜ := Finset.subset_union_right.trans hO
  have hZW : Z ∪ W ⊆ Uᶜ := Finset.subset_union_left.trans hO
  have hZ : Z ⊆ Uᶜ := Finset.subset_union_left.trans hZW
  have hW : W ⊆ Uᶜ := Finset.subset_union_right.trans hZW
  have hXZ : Disjoint X Z := Finset.disjoint_of_subset_left Finset.subset_union_left hXWZ
  have hXX : X ⊆ X ∪ Z := Finset.subset_union_left
  have r : doProb M X (Y ∪ Z ∪ (X ∪ W)) σ * doProb M (X ∪ Z) (X ∪ W) σ =
      doProb M (X ∪ Z) (Y ∪ (X ∪ W)) σ * doProb M X (Z ∪ (X ∪ W)) σ := by
    have r := rule2 M X Y Z W (valuesOn σ X) (valuesOn σ Z) hYZ hXWZ hYXW h (valuesOn σ _) rfl
    simp only [restrict_valuesOn] at r
    rw [doProb_doModel M hXZ, doProb_doModel M hXZ] at r
    exact r
  rw [doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ Z ∪ (X ∪ W) ∪ X = Y ∪ (Z ∪ W) ∪ X),
    doProb_eq_of_union_eq M hXX
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        X ∪ W ∪ X = W ∪ X),
    doProb_eq_of_union_eq M hXX
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ (X ∪ W) ∪ X = Y ∪ W ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Z ∪ (X ∪ W) ∪ X = Z ∪ W ∪ X)] at r
  rw [eval_prob, eval_prob, ENNReal.div_eq_div_iff
    (doProb_ne_zero M U hpos (Finset.union_subset hX hZ) hW σ) (doProb_ne_top M _ W σ)
    (doProb_ne_zero M U hpos hX hZW σ) (doProb_ne_top M X _ σ),
    mul_comm (doProb M (X ∪ Z) W σ), mul_comm (doProb M X (Z ∪ W) σ), r]

/-- **Rule 3 for expressions.** `P(Y | W, do(X ∪ Z)) = P(Y | W, do(X))` when `Y` and `Z`
are d-separated by `X ∪ W` in `G_{X̄, \overline{Z(W)}}`, from `Rule3Flag.rule3_general`. -/
theorem eval_rule3 (X Y Z W : Finset V) (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z)
    (hYXW : Disjoint Y (X ∪ W)) (hO : Z ∪ W ∪ X ⊆ Uᶜ)
    (h : SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z)
    (σ : ∀ v, α v) : eval M (.prob Y W (X ∪ Z)) σ = eval M (.prob Y W X) σ := by
  have hX : X ⊆ Uᶜ := Finset.subset_union_right.trans hO
  have hZW : Z ∪ W ⊆ Uᶜ := Finset.subset_union_left.trans hO
  have hZ : Z ⊆ Uᶜ := Finset.subset_union_left.trans hZW
  have hW : W ⊆ Uᶜ := Finset.subset_union_right.trans hZW
  have hXZ : Disjoint X Z := Finset.disjoint_of_subset_left Finset.subset_union_left hXWZ
  have hXX : X ⊆ X ∪ Z := Finset.subset_union_left
  have r : doProb M (X ∪ Z) (Y ∪ (X ∪ W)) σ * doProb M X (X ∪ W) σ =
      doProb M X (Y ∪ (X ∪ W)) σ * doProb M (X ∪ Z) (X ∪ W) σ := by
    have r := Rule3Flag.rule3_general M X Y Z W (valuesOn σ X) hYZ hXWZ hYXW h (valuesOn σ _)
    simp only [restrict_valuesOn] at r
    rw [doProb_doModel M hXZ, doProb_doModel M hXZ] at r
    exact r
  rw [doProb_eq_of_union_eq M hXX
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ (X ∪ W) ∪ X = Y ∪ W ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        X ∪ W ∪ X = W ∪ X),
    doProb_eq_of_union_eq M (Finset.Subset.refl X)
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        Y ∪ (X ∪ W) ∪ X = Y ∪ W ∪ X),
    doProb_eq_of_union_eq M hXX
      (Finset.ext fun v => by simp only [Finset.mem_union]; tauto :
        X ∪ W ∪ X = W ∪ X)] at r
  rw [eval_prob, eval_prob, ENNReal.div_eq_div_iff
    (doProb_ne_zero M U hpos hX hW σ) (doProb_ne_top M X W σ)
    (doProb_ne_zero M U hpos (Finset.union_subset hX hZ) hW σ) (doProb_ne_top M _ W σ),
    mul_comm (doProb M X W σ), mul_comm (doProb M (X ∪ Z) W σ), r]

end Rules

end DoCalc
