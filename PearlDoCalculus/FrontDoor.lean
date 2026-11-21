/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The front-door model: structural form and the cancellation lemma

This file defines the front-door causal model on a fixed graph and proves two theorems:

1. `frontdoor_structural`: the structural form of the front-door adjustment.
2. `frontdoor_X_cancellation`: the algebraic core that removes the reference to the
   unobserved confounder `U`.

The graph is `U → X`, `U → Y`, `X → Z`, `Z → Y`, where `U` is an unobserved confounder
and `Z` an observed mediator (classically: X = smoking, Z = tar, Y = cancer,
U = disposition). The model is hand-built for this one graph, before the general
`CausalModel` of `CausalModel.lean`; the general front-door criterion for arbitrary
graphs is `Adjustment.frontdoor_adjustment_criterion`.

**What is proved.** `frontdoor_structural` shows that the intervention can be written as
`Σ_z P(Z=z | X=x*) · Σ_u P(U=u) · P(Y=y | Z=z, U=u)`, a rearrangement by exchanging the
order of summation that still refers to `U`. `frontdoor_X_cancellation` is the
cancellation lemma: summing over `x'` with weights `pX_given_U(u, x')`, these weights sum
to `1` (since `pX_given_U u` is a PMF), and the result collapses to a sum weighted by
`pU` alone.

These two theorems are the algebraic basis of the observable front-door formula in
`FrontDoorObservable.lean`, which adds the observational joint, the conditionals with
the `0/0 = 0` convention, and the reduction under positivity.

**Main results.** `FrontDoorModel`, `frontdoor_structural`, `frontdoor_X_cancellation`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
The front-door model on four variables `U, X, Z, Y` with the graph
`U → X`, `U → Y`, `X → Z`, `Z → Y`.

The signatures encode the graph:
* `pX_given_U` depends only on `U` (`Z` is not a parent of `X`).
* `pZ_given_X` depends only on `X` (`U` is not a direct parent of `Z`).
* `pY_given_ZU` depends on `(Z, U)` (`X` is not a direct parent of `Y`).
-/
structure FrontDoorModel (ΩU ΩX ΩZ ΩY : Type*) where
  /-- The marginal distribution of the unobserved confounder `U`. -/
  pU          : PMF ΩU
  /-- The conditional distribution of `X` given `U`. -/
  pX_given_U  : ΩU → PMF ΩX
  /-- The conditional distribution of `Z` given `X` (the mediator). -/
  pZ_given_X  : ΩX → PMF ΩZ
  /-- The conditional distribution of `Y` given `(Z, U)`. -/
  pY_given_ZU : ΩZ → ΩU → PMF ΩY

namespace FrontDoorModel

variable {ΩU ΩX ΩZ ΩY : Type*}

/-- The full observational joint distribution `P(U, X, Z, Y)`. -/
noncomputable def joint (M : FrontDoorModel ΩU ΩX ΩZ ΩY) :
    PMF (ΩU × ΩX × ΩZ × ΩY) :=
  M.pU.bind fun u =>
    (M.pX_given_U u).bind fun x =>
      (M.pZ_given_X x).bind fun z =>
        (M.pY_given_ZU z u).map fun y => (u, x, z, y)

/--
The interventional marginal `P(Y | do(X = x*))` by truncated factorization.
`pX_given_U` is replaced by a point mass at `x*`; the result is marginalised over
`(U, Z)`.
-/
noncomputable def doX (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) : PMF ΩY :=
  M.pU.bind fun u =>
    (M.pZ_given_X x_star).bind fun z =>
      M.pY_given_ZU z u

/--
**Front-door adjustment, structural form.**

For the graph `U → X`, `U → Y`, `X → Z`, `Z → Y`:

  `P(Y = y | do(X = x*)) = Σ_z P(Z=z | X=x*) · Σ_u P(U=u) · P(Y=y | Z=z, U=u)`.

The intervention propagates through the mediator `Z` (outer sum), while the contribution
of `U` factors as an inner sum weighted by the marginal `pU`.
-/
theorem frontdoor_structural [Fintype ΩU] [Fintype ΩZ]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) (y : ΩY) :
    (M.doX x_star) y =
      ∑ z, (M.pZ_given_X x_star) z * ∑ u, M.pU u * (M.pY_given_ZU z u) y := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  have inner_unfold : ∀ u,
      ((M.pZ_given_X x_star).bind (fun z => M.pY_given_ZU z u)) y =
        ∑ z, M.pZ_given_X x_star z * (M.pY_given_ZU z u) y := by
    intro u
    rw [PMF.bind_apply, tsum_fintype]
  simp_rw [inner_unfold]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => ?_
  ring

/--
**Front-door, the cancellation lemma.**

The algebraic core of front-door identification:

  `Σ_x' Σ_u pU(u) · pX_given_U(u, x') · pY_given_ZU(z, u, y)`
   ` = Σ_u pU(u) · pY_given_ZU(z, u, y)`

Reading: the sum over `x'` with weights `pX_given_U(u, x')` collapses because
`pX_given_U u` is a PMF (it sums to `1`). This is exactly what removes the reference to
`U` in the observable form: the `x'`-sum of the front-door formula "absorbs" the factor
`pX_given_U`, and what is left is a sum weighted by `pU` alone.

Proof:
1. Exchange the order of summation (`Finset.sum_comm`).
2. For each `u`, factor out the term that does not depend on `x'`.
3. Pull the factor out of the sum (`Finset.mul_sum`).
4. The inner sum `Σ_x' pX_given_U(u, x') = 1`, since `pX_given_U u` is a PMF.
5. `mul_one` finishes.
-/
theorem frontdoor_X_cancellation [Fintype ΩX] [Fintype ΩU]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (z : ΩZ) (y : ΩY) :
    ∑ x' : ΩX, ∑ u : ΩU, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y =
      ∑ u : ΩU, M.pU u * (M.pY_given_ZU z u) y := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h_factor : ∀ x' : ΩX,
      M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y =
      (M.pU u * (M.pY_given_ZU z u) y) * (M.pX_given_U u) x' := by
    intro x'; ring
  simp_rw [h_factor]
  rw [← Finset.mul_sum]
  have h_sum_one : ∑ x' : ΩX, (M.pX_given_U u) x' = 1 := by
    simpa using (M.pX_given_U u).tsum_coe
  rw [h_sum_one, mul_one]

end FrontDoorModel

end PearlDoCalculus
