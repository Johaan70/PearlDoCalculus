# PearlDoCalculus

[![Build](https://github.com/Johaan70/PearlDoCalculus/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/Johaan70/PearlDoCalculus/actions/workflows/build.yml)

A Lean 4 formalization, on Mathlib, of Pearl's causal identification theory for finite
graphs: from d-separation to the completeness of the ID algorithm.

**License:** Apache 2.0 ([LICENSE](LICENSE))  
**Author:** Johan Magnus Aanderaa  
**Status:** v4.220. The proofs are complete: no `sorry`, the main results use only Lean's
three standard axioms, and a clean build prints no warnings. No external expert has
reviewed the definitions yet.

## What is proved

The headline result is the completeness of the ID algorithm, in
[`Hedge/Complete.lean`](PearlDoCalculus/Hedge/Complete.lean):

```lean
namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem idCheck_iff (G : DAG V) (U X Y : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hXY : ∀ y ∈ Y, y ∉ X) :
    idCheck G U X Y = true ↔
      ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y
```

`G` is a finite directed acyclic graph. The vertices in `U` are hidden (latent) and have no
parents (`hroot`); `X` and `Y` are disjoint sets of observed vertices. `idCheck` is a
computable function with the answer yes or no. It is the ID algorithm as a check: Tian's
IDENTIFY, run on each c-component of the ancestors of `Y` in the graph without the edges
into `X`. On a small concrete graph, `by decide` evaluates it.
`Identifiable G α Uᶜ X Y` says that `P(Y | do(X))` is determined by the observed data: any
two causal models on `G` with value types `α` that have the same, everywhere positive,
distribution on the observed vertices `Uᶜ` have the same `P(Y | do(X))`. A causal model
(`CausalModel`) has finite value types and one probability kernel per vertex, given its
parents.

So the theorem says: the check answers yes exactly when the effect is identifiable for every
choice of nonempty value types. For the direction from no to not identifiable, the proof
builds, for every hedge, two models that agree on the data but not on the effect. It needed a
repair of one step of the published argument, as we read it: see
[notes/tails-gap.md](notes/tails-gap.md).

The other main results:

| Name | File (in `PearlDoCalculus/`) | Meaning |
|---|---|---|
| `SetSound.dsep_sound_set` | [Soundness/SetSound](PearlDoCalculus/Soundness/SetSound.lean) | d-separation of sets (`Z` disjoint from `X`, `Y`) implies conditional independence, in every model |
| `Completeness.dsepSet_iff` | [Completeness/SetRules](PearlDoCalculus/Completeness/SetRules.lean) | for disjoint sets, d-separation holds iff independence holds in every model valued in bit vectors (\*) |
| `DoCalculus.rule1`, `DoCalculus.rule2` | [DoCalculus](PearlDoCalculus/DoCalculus.lean) | rules 1 and 2 of the do-calculus, as products, for disjoint sets, without positivity |
| `Rule3Flag.rule3_general` | [Rule3Flag](PearlDoCalculus/Rule3Flag.lean) | rule 3 with Pearl's `Z(W)`, as a product, for disjoint sets, without positivity |
| `Completeness.rule1_iff_set`, `rule2_iff_set` | [Completeness/SetRules](PearlDoCalculus/Completeness/SetRules.lean) | the graphical condition of rule 1 (2) holds iff the rule holds in every model (\*) |
| `Completeness.rule3_iff_set` | [Completeness/Rule3SetIff](PearlDoCalculus/Completeness/Rule3SetIff.lean) | the same for rule 3 (\*) |
| `Adjustment.backdoor_adjustment_criterion` | [Adjustment](PearlDoCalculus/Adjustment.lean) | for disjoint sets, the back-door formula from Pearl's path criterion, if `P(x, z) > 0` for all `z` |
| `Adjustment.frontdoor_adjustment_criterion` | [Adjustment](PearlDoCalculus/Adjustment.lean) | for disjoint sets, the front-door formula from Pearl's path criterion, if `P(x) > 0` and `P(z, x') > 0` for all `z`, `x'` |
| `Identification.CFactor.tian_identifiable_sets` | [Identification/CFactorSets](PearlDoCalculus/Identification/CFactorSets.lean) | if no `x ∈ X` (observed) has a child in its own c-component, `P(Y \| do(X))` is identifiable for every observed `Y` |
| `Identification.CFactor.tian_iff` | [Identification/TianIff](PearlDoCalculus/Identification/TianIff.lean) | one observed `x`, parentless latents, binary variables: the effect on all other observed vertices is identifiable iff `x` has no child in its c-component |
| `IdAlgo.idCheck_sound` | [IdAlgo](PearlDoCalculus/IdAlgo.lean) | if `idCheck` says yes, the effect is identifiable; latents may have parents, and `X`, `Y` may overlap |
| `Hedge.idCheck_false_hedge` | [Hedge/FromID](PearlDoCalculus/Hedge/FromID.lean) | if `idCheck` says no (`X` observed), the graph has a hedge for `P(Y \| do(X))` |
| `Hedge.PM.hedge_not_ident_Y` | [Hedge/Complete](PearlDoCalculus/Hedge/Complete.lean) | a hedge makes `P(Y \| do(X))` not identifiable for the value types `Val2 U` (finite bit vectors), under the hypotheses of `idCheck_iff` |
| `Idc.idc_sound` | [Idc](PearlDoCalculus/Idc.lean) | soundness of one IDC step for `P(Y \| do(X), Z, W)`: if rule 2 moves `Z` into the intervention and `P(Y, X, W \| do(X ∪ Z))` is identifiable, so is the conditional effect |
| `Verma.verma_constraint` | [Verma](PearlDoCalculus/Verma.lean) | on `a → b → c → d`, `b ↔ d`, with positive observed `P`: `Σ_b P(a,b,c,d) P(a,b) / (P(a,b,c) P(a))` does not depend on `a` |

(\*) The models in these equivalences have value type `Fin (k + 1) → Bool` at every vertex,
for all `k`; the direction from the graph holds for all finite value types.

[docs/results.md](docs/results.md) has the results in detail, with the ideas of the proofs.

## Building

```bash
git clone https://github.com/Johaan70/PearlDoCalculus && cd PearlDoCalculus
lake exe cache get    # download the compiled Mathlib
lake build            # must end in "Build completed successfully"
```

Requires Lean 4 (`lean-toolchain`: `leanprover/lean4:v4.30.0-rc2`, installed by elan) and
Mathlib (pinned in `lake-manifest.json`).

## Checking

```bash
lake env lean verification/AuditFinal.lean   # definitions, statements, axioms
lake env lean verification/AxiomCheck.lean   # the axioms of the other main results
scripts/check.sh                             # the gate; must end in "CHECK OK"
```

[AuditFinal.lean](verification/AuditFinal.lean) prints the definitions and statements of the
main results, proves from `idCheck_iff` that on the bow graph identifiability fails for some
value types, and prints 15 axiom lines, which must all read
`[propext, Classical.choice, Quot.sound]`.
[scripts/check.sh](scripts/check.sh) runs before every commit: full build, no `sorry` or
other forbidden constructs, these axioms only, and the statements of the public results
unchanged. The output of a fresh-clone audit is in
[audit_final_output.txt](verification/audit_final_output.txt).

## Scope limits

- **Finite and discrete.** Finite graphs and finite value types; no continuous variables.
- **Interventions only.** No counterfactuals, transportability or selection bias.
- **Latents without parents.** `idCheck_iff`, `hedge_not_ident_Y` and `tian_iff` assume it;
  the soundness results do not.
- **All value types.** Completeness quantifies over the value types, and the countermodels
  are bit vectors. That a no from `idCheck` excludes identifiability when all variables are
  binary is proved only in special cases (`tian_iff`, and hedge families).
- **Positivity.** `Identifiable` compares only models with a positive observed distribution.
- **Yes or no.** `idCheck` returns no formula. Formulas are proved for the back-door,
  front-door and Tian cases.
- **Not proved:** that every identifiable effect can be derived with the three rules
  (completeness of the do-calculus for identification); the IDC algorithm beyond the one
  step above, and its completeness; that no conditional independence implies the Verma
  constraint.
- **Definitions.** Lean checks that the proofs follow from the definitions, not that the
  definitions mean what the literature means.

## More

- [EXPLAINER.md](EXPLAINER.md): the project in plain language, for a non-specialist reader.
- [docs/results.md](docs/results.md): the results in detail, scope, related work.
- [notes/tails-gap.md](notes/tails-gap.md): the gap in the published hedge argument, and the
  repair.
- [HANDOFF.md](HANDOFF.md): for those who continue the work: file map, techniques, pitfalls,
  technical debt, release and audit history.
