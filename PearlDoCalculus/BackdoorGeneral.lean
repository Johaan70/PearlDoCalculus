/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.SimpleConfounderObservable

/-!
# The back-door adjustment formula, abstractly

Pearl's back-door theorem has two halves. Given a finite DAG, a treatment `X`, an
outcome `Y` and an adjustment set `Z`:

* (a) If `Z` has the *distributional* consequence of the back-door criterion (where `Z`
  has mass, the observational conditional `P(Y | X=x*, Z=z)` equals the interventional
  kernel `P(Y | do(X=x*), Z=z)`), then the adjustment formula
  `P(Y | do(X=x*)) = Σ_z P(Y|X=x*,Z=z) · P(Z=z)` holds.
* (b) The graphical back-door criterion *implies* that consequence.

This file proves (a), `backdoor_general`: the part that needs no d-separation. It is
needed as the probabilistic core of every adjustment formula; part (b) needs the
soundness of d-separation and is done in `Adjustment.lean`
(`Adjustment.backdoor_adjustment_criterion`).

**Proof.** The law of total probability for the interventional distribution, plus the
substitution that the hypothesis allows where `Z` has mass.

**Generality.** `backdoor_general` is abstract on purpose: the confounder space `Ωz`, the
marginal `pZ`, the interventional kernel `qY` and the observational conditional `condY`
are arbitrary, so every concrete back-door model is an instance. The two `example`s at
the end show that the minimal confounder model (`SimpleConfounder.lean`) and its
observable form (`SimpleConfounderObservable.lean`) factor through `backdoor_general`:
the first with a trivial back-door identity (`condY` is the kernel by definition), the
second with the real one, `condY_eq_kernel` under overlap.

**Main result.** `backdoor_general`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
**General back-door adjustment: the core of the adjustment formula.**

Let `Z` have marginal `pZ`. Let `qY z` be the interventional distribution of `Y` given
`Z = z` under `do(X = x*)`, so that `P(Y | do(X=x*))` is `pZ.bind qY`. Let `condY z y` be
the observational conditional `P(Y=y | X=x*, Z=z)`.

The hypothesis `hbd` is the distributional consequence of the back-door criterion: where
`Z` has mass, the observational conditional agrees with the interventional kernel. Then
the adjustment formula holds:

  `P(Y=y | do(X=x*)) = Σ_z condY z y · pZ z`.

Proof: the law of total probability for `pZ.bind qY` gives `Σ_z (qY z) y · pZ z`; where
`pZ z = 0` the term is zero on both sides, and otherwise `hbd` replaces the kernel by
`condY`.
-/
theorem backdoor_general {Ωz Ωy : Type*} [Fintype Ωz]
    (pZ : PMF Ωz) (qY : Ωz → PMF Ωy) (condY : Ωz → Ωy → ENNReal) (y : Ωy)
    (hbd : ∀ z, pZ z ≠ 0 → condY z y = (qY z) y) :
    (pZ.bind qY) y = ∑ z, condY z y * pZ z := by
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : pZ z = 0
  · simp [hz]
  · rw [hbd z hz]
    exact mul_comm _ _

/-!
## The concrete confounder models are instances of `backdoor_general`
-/

/-- The minimal confounder model as an instance of `backdoor_general`. Here the back-door
identity is trivial: `condY` is the kernel by definition. -/
example {Ωz Ωx Ωy : Type*} [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, (M.pY_given_XZ x_star z) y * M.pZ z :=
  backdoor_general M.pZ (fun z => M.pY_given_XZ x_star z)
    (fun z y => (M.pY_given_XZ x_star z) y) y (fun _ _ => rfl)

/-- The observable confounder model as an instance of `backdoor_general`. Here the
back-door identity is the real one: `condY_eq_kernel`, valid under overlap. -/
example {Ωz Ωx Ωy : Type*} [Fintype Ωz] [Fintype Ωy]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy)
    (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z :=
  backdoor_general M.pZ (fun z => M.pY_given_XZ x_star z)
    (fun z y => M.condY y x_star z) y
    (fun z hz => M.condY_eq_kernel y x_star z (mul_ne_zero hz (hpos z)))

end PearlDoCalculus
