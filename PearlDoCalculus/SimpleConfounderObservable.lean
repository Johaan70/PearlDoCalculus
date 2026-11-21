/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.SimpleConfounder

/-!
# The back-door formula in observable form

The second step after `SimpleConfounder.lean`: replace the kernel `pY_given_XZ` by the
*real* observational conditional probability `P(Y | X, Z)`, defined from the joint
distribution by division, and prove the back-door adjustment in that form
(`backdoor_adjustment_observable`).

## Background

`SimpleConfounderModel` has the graph `Z → X`, `Z → Y`, `X → Y`. The observable
back-door formula is

  `P(Y = y | do(X = x*)) = Σ_z P(Y = y | X = x*, Z = z) · P(Z = z)`

where `P(Y | X, Z)` is a conditional probability computed from observational data, not
the kernel itself. This is the form that can actually be estimated.

## The observational conditional

The joint distribution of the causal model is, by the factorization along the graph,
`P(Z, X, Y) = P(Z) · P(X | Z) · P(Y | X, Z)`: this is `jointMass`, the *definition* of
the joint distribution of a causal Bayesian network. The observational conditional is
then the ratio `condY = P(Z,X,Y) / P(Z,X)`, exactly the definition of conditional
probability.

**Proof.** Summing out `Y` gives `P(Z, X) = P(Z) · P(X | Z)` (`pZX_eq`); where this is
nonzero, `condY` cancels to the kernel (`condY_eq_kernel`); and the kernel form is
`backdoor_adjustment`. Terms with `P(Z = z) = 0` vanish on both sides.

The PMF `SimpleConfounderModel.joint`, built with `bind`, is another representation of
the same law. The identity `joint (z,x,y) = jointMass z x y` is a routine collapse of a
triple `tsum` over the nested `bind`/`map`; it is not included here, and it is the only
missing link for a full equivalence of the two representations.

## The positivity assumption

`backdoor_adjustment_observable` needs overlap: `P(X = x* | Z = z) ≠ 0` for every `z`.
This is the classical positivity and overlap assumption of causal inference: without it
`P(Y | do(X=x*))` cannot be estimated, because `x*` never occurs together with some
`z`. When the assumption fails the formula genuinely fails; it is not a technical
convenience.

**Main results.** `pZX_eq`, `condY_eq_kernel`, `backdoor_adjustment_observable`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

namespace SimpleConfounderModel

variable {Ωz Ωx Ωy : Type*} (M : SimpleConfounderModel Ωz Ωx Ωy)

/-- The point mass `P(Z=z, X=x, Y=y)` of the joint distribution, by the factorization
along the graph. -/
noncomputable def jointMass (z : Ωz) (x : Ωx) (y : Ωy) : ENNReal :=
  M.pZ z * (M.pX_given_Z z) x * (M.pY_given_XZ x z) y

/-- The marginal `P(Z=z, X=x)`, by summing out `Y`. -/
noncomputable def pZX [Fintype Ωy] (z : Ωz) (x : Ωx) : ENNReal :=
  ∑ y, M.jointMass z x y

/-- The observational conditional `P(Y=y | X=x, Z=z) = P(Z,X,Y) / P(Z,X)`. -/
noncomputable def condY [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz) : ENNReal :=
  M.jointMass z x y / M.pZX z x

/--
**Marginalisation lemma: `P(Z, X) = P(Z) · P(X | Z)`.**

Sum out `Y`; the factors that do not depend on `y` are pulled out, and `pY_given_XZ`
sums to `1`.
-/
theorem pZX_eq [Fintype Ωy] (z : Ωz) (x : Ωx) :
    M.pZX z x = M.pZ z * (M.pX_given_Z z) x := by
  unfold pZX jointMass
  rw [← Finset.mul_sum]
  have hsum : ∑ y, (M.pY_given_XZ x z) y = 1 := by
    simpa using (M.pY_given_XZ x z).tsum_coe
  rw [hsum, mul_one]

/--
**The observational conditional equals the kernel, under positivity.**

When `P(Z=z, X=x) = P(Z=z)·P(X=x|Z=z) ≠ 0` the conditional is well defined, and
`condY y x z = P(Y=y | X=x, Z=z)` agrees with the kernel `pY_given_XZ x z y`. The proof
is cancellation: `(c · b) / c = b`.
-/
theorem condY_eq_kernel [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz)
    (hpos : M.pZ z * (M.pX_given_Z z) x ≠ 0) :
    M.condY y x z = (M.pY_given_XZ x z) y := by
  have hctop : M.pZ z * (M.pX_given_Z z) x ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  unfold condY
  rw [M.pZX_eq z x]
  unfold jointMass
  rw [mul_comm (M.pZ z * (M.pX_given_Z z) x) ((M.pY_given_XZ x z) y),
      mul_div_assoc, ENNReal.div_self hpos hctop, mul_one]

/--
**Back-door adjustment, observable form.**

For the graph `Z → X`, `Z → Y`, `X → Y`, under the overlap assumption
`∀ z, P(X=x* | Z=z) ≠ 0`:

  `P(Y = y | do(X = x*)) = Σ_z P(Y=y | X=x*, Z=z) · P(Z=z)`

where `P(Y | X, Z)` is the observational conditional `condY`, computed from the joint
distribution, not the kernel. This is the form that can actually be estimated from
observational data.

Proof: start from `backdoor_adjustment` (kernel form), and replace `pY_given_XZ` by
`condY` term by term with `condY_eq_kernel`. When `P(Z=z) = 0` both sides are zero;
otherwise overlap makes the conditional well defined.
-/
theorem backdoor_adjustment_observable [Fintype Ωy] [Fintype Ωz]
    (x_star : Ωx) (y : Ωy) (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z := by
  rw [M.backdoor_adjustment x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : M.pZ z = 0
  · simp [hz]
  · rw [M.condY_eq_kernel y x_star z (mul_ne_zero hz (hpos z))]

end SimpleConfounderModel

end PearlDoCalculus
