/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Back-door adjustment with a mediator

The third hand-built back-door model, after `SimpleConfounder.lean` and
`SimpleConfounderObservable.lean`. The model has a mediator on the causal path: the
graph `Z → X`, `Z → Y`, `X → M`, `M → Y`. Here `Z` is still a confounder, but the effect
of `X` on `Y` now goes through the mediator `M`.

The subtle point: the adjustment set is the confounder `{Z}`, not the mediator `M`. `M`
is a descendant of `X` and lies on the causal path; adjusting for it would block exactly
the effect we want to measure. The back-door criterion says precisely this: the
adjustment set may not contain descendants of `X`.

## The results

* `backdoor_mediator`, structural form: `P(Y | do(X=x*))` expressed as
  `Σ_z (Σ_m P(M=m|X=x*) · P(Y=y|M=m,Z=z)) · P(Z=z)`. The inner `Σ_m` is the
  observational conditional `P(Y|X,Z)` written out through the mediator.
* `backdoor_mediator_observable`: the same, with `P(Y|X,Z)` the real observational
  conditional `condY`, defined from the joint distribution by division, under the
  overlap assumption `P(X=x*|Z=z) ≠ 0`.

**Proof.** Summing out `M` and `Y` gives `P(Z, X) = P(Z) · P(X | Z)` (`pZX_eq`), summing
out `M` alone gives `P(Z,X,Y)` as `P(Z)·P(X|Z)` times the mediator sum (`pZXY_eq`), and
where `P(Z, X) ≠ 0` the two cancel to the mediator sum (`condY_eq_mediatorsum`).

## Conditional independence

The identity rests on two independences that the graph encodes in the signatures of
the kernels: `M` depends only on `X` (so `M` is independent of `Z` given `X`), and `Y`
depends only on `(M, Z)` (so `Y` is independent of `X` given `M, Z`). Both are built
into the types of `pM_given_X` and `pY_given_MZ`.

As in `SimpleConfounderObservable.lean`, `jointMass` is the factorized joint law; the
bridge to the `joint` built with `bind` is a routine `tsum` collapse, not included.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
A structural causal model with a mediator, on four variables `Z, X, M, Y` with the
graph `Z → X`, `Z → Y`, `X → M`, `M → Y`.

`Z` is a confounder; `M` is a mediator on the causal path `X → M → Y`. The signatures
encode the graph: `pM_given_X` depends only on `X`, `pY_given_MZ` on `(M, Z)`.
-/
structure MediatorModel (Ωz Ωx Ωm Ωy : Type*) where
  /-- The marginal distribution of the confounder `Z`. -/
  pZ          : PMF Ωz
  /-- The conditional distribution of `X` given `Z`. -/
  pX_given_Z  : Ωz → PMF Ωx
  /-- The conditional distribution of the mediator `M` given `X`. -/
  pM_given_X  : Ωx → PMF Ωm
  /-- The conditional distribution of `Y` given `(M, Z)`. -/
  pY_given_MZ : Ωm → Ωz → PMF Ωy

namespace MediatorModel

variable {Ωz Ωx Ωm Ωy : Type*} (M : MediatorModel Ωz Ωx Ωm Ωy)

/-- The observational joint distribution `P(Z, X, M, Y)` from the factorization along
the graph. -/
noncomputable def joint : PMF (Ωz × Ωx × Ωm × Ωy) :=
  M.pZ.bind fun z =>
    (M.pX_given_Z z).bind fun x =>
      (M.pM_given_X x).bind fun m =>
        (M.pY_given_MZ m z).map fun y => (z, x, m, y)

/--
The interventional marginal `P(Y | do(X = x*))` by truncated factorization: the factor
`P(X | Z)` is replaced by a point mass at `x*`. `M` still follows `P(M | X = x*)`, and
`Y` follows `P(Y | M, Z)`.
-/
noncomputable def doX (x_star : Ωx) : PMF Ωy :=
  M.pZ.bind fun z =>
    (M.pM_given_X x_star).bind fun m =>
      M.pY_given_MZ m z

/-- The point mass `P(Z=z, X=x, M=m, Y=y)` of the joint distribution, by the
factorization. -/
noncomputable def jointMass (z : Ωz) (x : Ωx) (m : Ωm) (y : Ωy) : ENNReal :=
  M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m * (M.pY_given_MZ m z) y

/-- The marginal `P(Z=z, X=x)`, by summing out `M` and `Y`. -/
noncomputable def pZX [Fintype Ωm] [Fintype Ωy] (z : Ωz) (x : Ωx) : ENNReal :=
  ∑ m, ∑ y, M.jointMass z x m y

/-- The marginal `P(Z=z, X=x, Y=y)`, by summing out `M`. -/
noncomputable def pZXY [Fintype Ωm] (z : Ωz) (x : Ωx) (y : Ωy) : ENNReal :=
  ∑ m, M.jointMass z x m y

/-- The observational conditional `P(Y=y | X=x, Z=z) = P(Z,X,Y) / P(Z,X)`. -/
noncomputable def condY [Fintype Ωm] [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz) :
    ENNReal :=
  M.pZXY z x y / M.pZX z x

/--
**Back-door with a mediator, structural form.**

For the graph `Z → X`, `Z → Y`, `X → M`, `M → Y`:

  `P(Y=y | do(X=x*)) = Σ_z (Σ_m P(M=m|X=x*)·P(Y=y|M=m,Z=z)) · P(Z=z)`.

The inner `Σ_m` is the observational conditional `P(Y|X=x*,Z=z)` written out through the
mediator. The proof reduces the nested `bind` of `doX` to the double sum.
-/
theorem backdoor_mediator [Fintype Ωz] [Fintype Ωm]
    (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y
      = ∑ z, (∑ m, (M.pM_given_X x_star) m * (M.pY_given_MZ m z) y) * M.pZ z := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [PMF.bind_apply, tsum_fintype]
  exact mul_comm _ _

/--
**Marginalisation lemma: `P(Z, X) = P(Z) · P(X | Z)`.**

Sum out `M` and `Y`; `pM_given_X` and `pY_given_MZ` each sum to `1`.
-/
theorem pZX_eq [Fintype Ωm] [Fintype Ωy] (z : Ωz) (x : Ωx) :
    M.pZX z x = M.pZ z * (M.pX_given_Z z) x := by
  unfold pZX jointMass
  have hinner : ∀ m,
      ∑ y, M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m * (M.pY_given_MZ m z) y
        = M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m := by
    intro m
    rw [← Finset.mul_sum]
    have h1 : ∑ y, (M.pY_given_MZ m z) y = 1 := by
      simpa using (M.pY_given_MZ m z).tsum_coe
    rw [h1, mul_one]
  simp only [hinner]
  rw [← Finset.mul_sum]
  have hM : ∑ m, (M.pM_given_X x) m = 1 := by
    simpa using (M.pM_given_X x).tsum_coe
  rw [hM, mul_one]

/--
**Factorization of `P(Z, X, Y)`.**

`P(Z,X,Y) = P(Z)·P(X|Z) · Σ_m P(M=m|X)·P(Y|M,Z)`; the inner sum sums out the mediator.
-/
theorem pZXY_eq [Fintype Ωm] (z : Ωz) (x : Ωx) (y : Ωy) :
    M.pZXY z x y
      = (M.pZ z * (M.pX_given_Z z) x)
          * ∑ m, (M.pM_given_X x) m * (M.pY_given_MZ m z) y := by
  unfold pZXY jointMass
  simp_rw [mul_assoc (M.pZ z * (M.pX_given_Z z) x)]
  rw [← Finset.mul_sum]

/--
**The observational conditional equals the mediator sum, under positivity.**

When `P(Z=z, X=x) ≠ 0`, `condY = P(Y|X,Z)` agrees with `Σ_m P(M=m|X)·P(Y|M,Z)`. The
proof is cancellation: `(c · S) / c = S`.
-/
theorem condY_eq_mediatorsum [Fintype Ωm] [Fintype Ωy]
    (y : Ωy) (x : Ωx) (z : Ωz)
    (hpos : M.pZ z * (M.pX_given_Z z) x ≠ 0) :
    M.condY y x z = ∑ m, (M.pM_given_X x) m * (M.pY_given_MZ m z) y := by
  have hctop : M.pZ z * (M.pX_given_Z z) x ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  unfold condY
  rw [M.pZXY_eq z x y, M.pZX_eq z x,
      mul_comm (M.pZ z * (M.pX_given_Z z) x) _, mul_div_assoc,
      ENNReal.div_self hpos hctop, mul_one]

/--
**Back-door with a mediator, observable form.**

Under the overlap assumption `∀ z, P(X=x* | Z=z) ≠ 0`:

  `P(Y=y | do(X=x*)) = Σ_z P(Y=y | X=x*, Z=z) · P(Z=z)`,

where `P(Y|X,Z)` is the real observational conditional `condY`. The adjustment set is
the confounder `Z` alone: the mediator `M` is summed out inside `condY`, not conditioned
on.
-/
theorem backdoor_mediator_observable [Fintype Ωz] [Fintype Ωm] [Fintype Ωy]
    (x_star : Ωx) (y : Ωy) (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z := by
  rw [M.backdoor_mediator x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : M.pZ z = 0
  · simp [hz]
  · rw [M.condY_eq_mediatorsum y x_star z (mul_ne_zero hz (hpos z))]

end MediatorModel

end PearlDoCalculus
