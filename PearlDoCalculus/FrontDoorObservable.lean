/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.FrontDoor

/-!
# The front-door formula in observable form

This file proves Pearl's front-door formula (1995) for the hand-built front-door model
of `FrontDoor.lean`, in a form that refers only to observable quantities:

  `P(Y=y | do(X=x*)) = Σ_z P(Z=z|X=x*) · Σ_x' P(X=x') · P(Y=y|X=x',Z=z)`

(`frontdoor_adjustment_observable`). It shows that a causal effect can be identified
even though the confounder `U` is unobserved. The general graphical version is
`Adjustment.frontdoor_adjustment_criterion`.

**Argument convention.** The kernels of `FrontDoorModel` are curried as
`condition → PMF outcome`: `pX_given_U u x`, `pZ_given_X x z`, `pY_given_ZU z u y`. The
observable conditionals are defined with the outcome first: `pU_given_X u x`
("P(U=u | X=x)"), `pY_given_XZ y x z`. The marginals: `pX x`, `pXZ x z`, `pXZY x z y`.

**Contents.**
* `pX`, `pXZ`, `pXZY`: observable marginals, with `U` summed out.
* `pU_given_X`, `pY_given_XZ`: observable conditionals by `ENNReal` division.
* `pXZ_eq_pX_mul_pZ_given_X`: the structural lemma `P(X,Z) = P(X) * P(Z|X)`.
* `sum_pU_given_X_times_pY`: the key step `Σ_u P(U|X) * P(Y|Z,U) = P(Y|X,Z)`, the
  conditional independence that carries front-door identification.

**Proof of the formula.** Start from the structural form `frontdoor_structural`, which
still sums over `U`; expand the inner `U`-sum with the cancellation lemma
`frontdoor_X_cancellation` into a sum over `x'`; for each `x'` with `P(X=x') ≠ 0`,
`sum_pU_given_X_times_pY` turns the `U`-sum into the observable conditional.

**On the hypothesis.** The key step needs only `P(Z=z | X=x') ≠ 0`, not full positivity
of `P(X)`. The reason: the cancellation `(A*c)/(b*c) = A/b` in `ENNReal` holds for every
`b` as long as `c ≠ 0` and `c ≠ ⊤`, also when `b = 0` (both sides are then `⊤` or `0`
consistently).

**Main results.** `sum_pU_given_X_times_pY`, `frontdoor_adjustment_observable`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

namespace FrontDoorModel

variable {ΩU ΩX ΩZ ΩY : Type*} [Fintype ΩU] (M : FrontDoorModel ΩU ΩX ΩZ ΩY)

/-- The observable marginal `P(X = x)`, with `U` summed out. -/
noncomputable def pX (x : ΩX) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x

/-- The observable marginal `P(X = x, Z = z)`, with `U` summed out. -/
noncomputable def pXZ (x : ΩX) (z : ΩZ) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x * (M.pZ_given_X x) z

/-- The observable marginal `P(X = x, Z = z, Y = y)`, with `U` summed out. -/
noncomputable def pXZY (x : ΩX) (z : ΩZ) (y : ΩY) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x * (M.pZ_given_X x) z * (M.pY_given_ZU z u) y

/-- The conditional `P(U = u | X = x) = P(U, X) / P(X)`. -/
noncomputable def pU_given_X (u : ΩU) (x : ΩX) : ENNReal :=
  (M.pU u * (M.pX_given_U u) x) / M.pX x

/-- The observable conditional `P(Y = y | X = x, Z = z) = P(X, Z, Y) / P(X, Z)`. -/
noncomputable def pY_given_XZ (y : ΩY) (x : ΩX) (z : ΩZ) : ENNReal :=
  M.pXZY x z y / M.pXZ x z

/-- Unfolding lemma for `pU_given_X` (by definition). -/
theorem pU_given_X_eq (u : ΩU) (x : ΩX) :
    M.pU_given_X u x = (M.pU u * (M.pX_given_U u) x) / M.pX x := rfl

/-- Unfolding lemma for `pY_given_XZ` (by definition). -/
theorem pY_given_XZ_eq (y : ΩY) (x : ΩX) (z : ΩZ) :
    M.pY_given_XZ y x z = M.pXZY x z y / M.pXZ x z := rfl

omit [Fintype ΩU] in
/-- Every value of a PMF is finite, so `P(Z | X) ≠ ⊤`. -/
theorem pZ_given_X_ne_top (x : ΩX) (z : ΩZ) : (M.pZ_given_X x) z ≠ ⊤ :=
  PMF.apply_ne_top _ _

/--
**Structural lemma: `P(X, Z) = P(X) * P(Z | X)`.**

The factor `P(Z | X)` is constant in the `U`-sum and is pulled out with
`Finset.sum_mul`. It holds unconditionally (also when `P(X) = 0`): a purely algebraic
identity.
-/
theorem pXZ_eq_pX_mul_pZ_given_X (x : ΩX) (z : ΩZ) :
    M.pXZ x z = M.pX x * (M.pZ_given_X x) z := by
  unfold pXZ pX
  rw [Finset.sum_mul]

/--
**Front-door, the key step: conditional independence by summing out `U`.**

  `Σ_u P(U=u | X=x') * P(Y=y | Z=z, U=u) = P(Y=y | X=x', Z=z)`

This is the conditional-independence step that removes the reference to the unobserved
`U` in the front-door formula. The only hypothesis: `P(Z=z | X=x') ≠ 0`.

Proof:
1. `hLHS`: the left side is `(Σ_u P(U,X)*P(Y|Z,U)) / P(X)`; pull the division out of
   the sum with `div_eq_mul_inv` and `Finset.sum_mul`.
2. `hNum`: the numerator `P(X,Z,Y)` factors as `(Σ_u ...) * P(Z|X)`.
3. `pXZ_eq_pX_mul_pZ_given_X` gives the denominator as `P(X) * P(Z|X)`.
4. `h_cancel`: cancel `P(Z|X)` in numerator and denominator.
-/
theorem sum_pU_given_X_times_pY (x' : ΩX) (z : ΩZ) (y : ΩY)
    (h_pZ_ne : (M.pZ_given_X x') z ≠ 0) :
    ∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y = M.pY_given_XZ y x' z := by
  have h_pZ_top : (M.pZ_given_X x') z ≠ ⊤ := PMF.apply_ne_top _ _
  -- (1) Left side: pull 1 / P(X) out of the sum.
  have hLHS : (∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y)
      = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y) / M.pX x' := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold pU_given_X
    rw [div_eq_mul_inv, mul_right_comm]
  -- (2) The numerator P(X,Z,Y) has the factor P(Z|X).
  have hNum : M.pXZY x' z y
      = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y)
          * (M.pZ_given_X x') z := by
    unfold pXZY
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  -- (3) The cancellation step, isolated. The only use of an ENNReal division lemma.
  have h_cancel : ∀ A : ENNReal,
      A * (M.pZ_given_X x') z / (M.pX x' * (M.pZ_given_X x') z) = A / M.pX x' := by
    intro A
    exact ENNReal.mul_div_mul_right A (M.pX x') h_pZ_ne h_pZ_top
  -- Put together.
  rw [hLHS, pY_given_XZ_eq, hNum, pXZ_eq_pX_mul_pZ_given_X, h_cancel]

omit [Fintype ΩU] in
/--
**Front-door adjustment, fully observable form.**

For the graph `U → X`, `U → Y`, `X → Z`, `Z → Y`, and under the positivity assumption
`∀ x' z, P(Z=z | X=x') ≠ 0`:

  `P(Y=y | do(X=x*)) = Σ_z P(Z=z|X=x*) · Σ_x' P(X=x') · P(Y=y|X=x',Z=z)`.

This is the front-door formula itself (Pearl 1995) in its fully estimable form: no
reference to the unobserved `U` is left. The proof combines `frontdoor_structural`
(structural form with `U`), `frontdoor_X_cancellation` (algebraic cancellation of the
`U`-sum by summing over `x'`), and `sum_pU_given_X_times_pY` (the key step: the `U`-sum
becomes an observable conditional).
-/
theorem frontdoor_adjustment_observable [Fintype ΩU] [Fintype ΩX] [Fintype ΩZ]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) (y : ΩY)
    (hpos : ∀ x' z, (M.pZ_given_X x') z ≠ 0) :
    (M.doX x_star) y =
      ∑ z, (M.pZ_given_X x_star) z * ∑ x', M.pX x' * M.pY_given_XZ y x' z := by
  rw [M.frontdoor_structural x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  rw [← M.frontdoor_X_cancellation z y]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have hxtop : M.pX x' ≠ ⊤ := by
    have hbind : M.pX x' = (M.pU.bind M.pX_given_U) x' := by
      unfold FrontDoorModel.pX
      rw [PMF.bind_apply, tsum_fintype]
    rw [hbind]
    exact PMF.apply_ne_top _ _
  by_cases hx : M.pX x' = 0
  · have hz : ∀ u, M.pU u * (M.pX_given_U u) x' = 0 := by
      have hsum0 : ∑ u, M.pU u * (M.pX_given_U u) x' = 0 := hx
      exact fun u => (Finset.sum_eq_zero_iff.mp hsum0) u (Finset.mem_univ u)
    simp only [hz, zero_mul, Finset.sum_const_zero]
    rw [hx, zero_mul]
  · have hSumDiv : (∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y)
        = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y) / M.pX x' := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [M.pU_given_X_eq, div_eq_mul_inv, mul_right_comm]
    have hEq := M.sum_pU_given_X_times_pY x' z y (hpos x' z)
    rw [hSumDiv] at hEq
    have hcancel : (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y)
          / M.pX x' * M.pX x'
        = ∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y :=
      ENNReal.div_mul_cancel hx hxtop
    rw [hEq] at hcancel
    rw [mul_comm] at hcancel
    exact hcancel.symm

end FrontDoorModel

end PearlDoCalculus
