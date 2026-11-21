/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The minimal confounder model

This file sets up the smallest nontrivial causal model in which the do-operator differs
from conditioning: three variables `Z`, `X`, `Y` with the graph `Z → X`, `Z → Y`,
`X → Y`. Here `Z` is a confounder of the causal effect of `X` on `Y`. It is the first
and simplest instance of the back-door adjustment; the general graphical criterion is
`Adjustment.backdoor_adjustment_criterion`.

The main result `backdoor_adjustment` says that the interventional distribution
`P(Y | do(X = x*))` equals the back-door adjusted formula
`Σ_z P(Y | X = x*, Z = z) · P(Z = z)`.

## Minimal assumptions

We assume only:
* three types `Ωz Ωx Ωy` (value sets of `Z`, `X`, `Y`); for `backdoor_adjustment` also
  that `Ωz` is finite (`Fintype Ωz`);
* a marginal `P(Z)` on `Z` (field `pZ`);
* conditional kernels `P(X | Z)` and `P(Y | X, Z)` (fields `pX_given_Z`, `pY_given_XZ`).

Nothing else is needed for this case. The graph is encoded implicitly in the
*signatures* of the kernels.

## The conceptual core

In this minimal model the proof is essentially a computation: we *construct* the joint
distribution from the factorization, so the conditional `P(Y | X, Z)` is by definition
the kernel `pY_given_XZ`. The mathematical content lies in separating the two
distributions, observational and interventional, precisely, and in making the relation
between them explicit:

* `joint` builds the observational joint distribution.
* `doX` builds the interventional marginal by *truncated factorization*: the factor
  `P(X | Z)` is replaced by a point mass at `x*`.
* `backdoor_adjustment` shows that interventional quantities can be expressed as a
  weighted sum of observational quantities when `Z` "blocks" every back-door path from
  `X` to `Y`. In the triangle here the only back-door path is `X ← Z → Y`, and `{Z}`
  blocks it.

The observable form, with `P(Y | X, Z)` computed from the joint by division, is in
`SimpleConfounderObservable.lean`.

**Main results.** `SimpleConfounderModel`, `doX`, `backdoor_adjustment`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
A minimal structural causal model on three variables `Z, X, Y` with the graph
`Z → X`, `Z → Y`, `X → Y`.

The signatures encode the graph: `pX_given_Z` depends only on `Z`, and `pY_given_XZ` on
`(X, Z)`. There is no kernel for `Z` itself, only the marginal `pZ`, since `Z` has no
parents.
-/
structure SimpleConfounderModel (Ωz Ωx Ωy : Type*) where
  /-- The marginal distribution of the confounder `Z`. -/
  pZ          : PMF Ωz
  /-- The conditional distribution of `X` given `Z`. -/
  pX_given_Z  : Ωz → PMF Ωx
  /-- The conditional distribution of `Y` given `(X, Z)`. -/
  pY_given_XZ : Ωx → Ωz → PMF Ωy

namespace SimpleConfounderModel

variable {Ωz Ωx Ωy : Type*}

/--
The observational joint distribution `P(Z, X, Y)`, built from the factorization along
the graph: `P(Z, X, Y) = P(Z) · P(X | Z) · P(Y | X, Z)`.
-/
noncomputable def joint (M : SimpleConfounderModel Ωz Ωx Ωy) :
    PMF (Ωz × Ωx × Ωy) :=
  M.pZ.bind fun z =>
    (M.pX_given_Z z).bind fun x =>
      (M.pY_given_XZ x z).map fun y => (z, x, y)

/--
The interventional marginal `P(Y | do(X = x*))` by Pearl's truncated factorization.

In the expression `P(Z) · P(X | Z) · P(Y | X, Z)` the intervention `do(X = x*)` replaces
the factor `P(X | Z)` by a point mass at `x*`. After summing out `Z` we are left with

  `P(Y = y | do(X = x*)) = Σ_z P(Z = z) · P(Y = y | X = x*, Z = z)`.

This differs from the observational conditional `P(Y = y | X = x*)`, which would have
`P(Z = z | X = x*)` (not `P(Z = z)`) in the sum, and that difference is exactly the
confounding bias.
-/
noncomputable def doX (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) :
    PMF Ωy :=
  M.pZ.bind fun z => M.pY_given_XZ x_star z

/--
**Back-door adjustment (the minimal case).**

For the graph `Z → X`, `Z → Y`, `X → Y` the interventional distribution
`P(Y | do(X = x*))` is identifiable from the observational distribution as

  `Σ_z P(Y | X = x*, Z = z) · P(Z = z)`.

Conceptually: the right side can be computed from observational data alone (no
intervention needed), and the theorem says that it gives the same answer as actually
intervening on `X`. The structural premise that makes this possible is that `{Z}` blocks
the only back-door path `X ← Z → Y`.

In this minimal model the proof is a computation that reduces the `PMF.bind` structure
of `doX` to the adjustment sum with `PMF.bind_apply` and the finite-type identity
`tsum = Finset.sum`.
-/
theorem backdoor_adjustment [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, M.pY_given_XZ x_star z y * M.pZ z := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/--
A variant with the factors in the natural "observational" order: `P(Z) · P(Y | X, Z)`.
Algebraically identical to `backdoor_adjustment`, but sometimes easier to use.
-/
theorem backdoor_adjustment_mul_comm [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, M.pZ z * M.pY_given_XZ x_star z y := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]

end SimpleConfounderModel

end PearlDoCalculus
