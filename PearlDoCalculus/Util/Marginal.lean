/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Util.Assignment

/-!
# Marginals on a subset

`M.marginal S` is the distribution of a causal model `M` on the vertices of `S`, and
`marginal_restrict` (`CausalModel`) says that marginalizing further from `S` to `T ⊆ S`
gives `M.marginal T`. This file collects the consequences of that fact that are used in
several unrelated places: the soundness of d-separation (`DSepSound`), the completeness
of the do-rules (`Completeness/SingleRules`, `Completeness/SetRules`), the adjustment
formulas (`Adjustment`), the identification layer (`Identification/*`) and Verma's
constraint (`Verma`). The three basic proofs rewrite the smaller marginal as the image
of the larger one under restriction (`marginal_restrict`, `PMF.map_apply`) and read off
the resulting sum; the other two results are short corollaries.

**Contents.**

1. *Equal marginals pass to subsets.* If two models have the same marginal on `O`,
   they have the same marginal on every `T ⊆ O` (`marginal_eq_of_subset`).
2. *Positivity passes to subsets.* If `a` has positive mass on `S`, its restriction has
   positive mass on `T ⊆ S` (`marginal_restrict_ne_zero`): the mass of `a|_T` is a sum
   with `a` as one of its terms. So a marginal that is positive everywhere on `O` is
   positive everywhere on every `T ⊆ O` (`marginal_ne_zero_of_subset`); every
   assignment on `T` is a restriction (`Assignment.restrict_surjective`).
3. *Injective restrictions keep the mass.* If the restriction from `S` to `T` is
   injective, then the mass of `a|_T` on `T` equals the mass of `a` on `S`
   (`marginal_restrict_of_injective`): only one term of the sum is nonzero. With
   `Assignment.restrict_injective_of_subset` this rewrites a marginal on a set written
   in one way (`X ∪ Y ∪ Z`) to the same set written in another (`Y ∪ X ∪ Z`); the
   corollary `marginal_eq_restrict_of_subset_of_subset` does this in one step.

**Main results.** `marginal_eq_of_subset`, `marginal_restrict_ne_zero`,
`marginal_ne_zero_of_subset`, `marginal_restrict_of_injective`,
`marginal_eq_restrict_of_subset_of_subset`, all in namespace
`PearlDoCalculus.DAG.CausalModel`.
-/

namespace PearlDoCalculus.DAG.CausalModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-! ## Equal marginals pass to subsets -/

/-- Two models with the same marginal on `O` have the same marginal on every `T ⊆ O`. -/
lemma marginal_eq_of_subset {M₁ M₂ : G.CausalModel α} {O T : Finset V}
    (h : M₁.marginal O = M₂.marginal O) (hT : T ⊆ O) :
    M₁.marginal T = M₂.marginal T := by
  rw [← marginal_restrict M₁ hT, ← marginal_restrict M₂ hT, h]

/-! ## Positivity passes to subsets -/

/-- If `a` has positive mass on `S`, its restriction has positive mass on `T ⊆ S`. -/
lemma marginal_restrict_ne_zero (M : G.CausalModel α) {S T : Finset V} (h : T ⊆ S)
    (a : Assignment (α := α) S) (ha : M.marginal S a ≠ 0) :
    M.marginal T (a.restrict h) ≠ 0 := by
  rw [← marginal_restrict M h, PMF.map_apply]
  intro h0
  apply ha
  have h1 := (ENNReal.tsum_eq_zero.mp h0) a
  rwa [if_pos rfl] at h1

/-- A marginal that is positive everywhere on `O` is positive everywhere on `T ⊆ O`. -/
lemma marginal_ne_zero_of_subset [∀ w, Nonempty (α w)] {M : G.CausalModel α}
    {O T : Finset V} (hpos : ∀ a, M.marginal O a ≠ 0) (hT : T ⊆ O)
    (b : Assignment (α := α) T) : M.marginal T b ≠ 0 := by
  obtain ⟨a, rfl⟩ := Assignment.restrict_surjective hT b
  exact marginal_restrict_ne_zero M hT a (hpos a)

/-! ## Injective restrictions keep the mass -/

/-- For an injective restriction, the marginal on `T` at `a|_T` equals the marginal on
`S` at `a`: only one term of the sum is nonzero. -/
lemma marginal_restrict_of_injective (M : G.CausalModel α) {S T : Finset V}
    (h : T ⊆ S) (hinj : Function.Injective (Assignment.restrict (α := α) h))
    (a : Assignment (α := α) S) :
    (M.marginal T) (a.restrict h) = (M.marginal S) a := by
  rw [← marginal_restrict M h, PMF.map_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    have hne : a.restrict h ≠ b.restrict h := fun e => hb (hinj e).symm
    simp [hne]

/-- The same set written in two ways: if `S ⊆ T` and `T ⊆ S`, the marginal on `T` at `u`
equals the marginal on `S` at `u|_S`. This rewrites, say, `M.marginal (X ∪ Y ∪ Z)` to
`M.marginal (Y ∪ X ∪ Z)`. -/
lemma marginal_eq_restrict_of_subset_of_subset (M : G.CausalModel α) {S T : Finset V}
    (hST : S ⊆ T) (hTS : T ⊆ S) (u : Assignment (α := α) T) :
    M.marginal T u = M.marginal S (u.restrict hST) :=
  (marginal_restrict_of_injective M hST (Assignment.restrict_injective_of_subset hST hTS) u).symm

end PearlDoCalculus.DAG.CausalModel
