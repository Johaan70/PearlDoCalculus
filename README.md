# PearlDoCalculus

Formal verification of causal inference in Pearl's framework, in Lean 4 on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** v1.0 — `dsep_sound` machine-checked, no `sorry` in the project. Definitional audit in progress (see below).

---

## Main result

```lean
theorem DSepSound.dsep_sound (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y) : CondIndep M {x} {y} Z
```

For every `CausalModel` (finite vertex set, finite value types, kernels
P(v | pa(v)) as PMFs): if `x` and `y` are d-separated given `Z`, then `x` and
`y` are conditionally independent given `Z` in the product-form sense of
`CondIndep`. All assumptions are those built into `CausalModel`; the theorem
adds none.

Two precisions. First, d-separation is defined over *walks* (`Walk.Blocked`),
not paths; see Audit status. Second, the joint distribution is proved equal to
the classical Bayesian-network factorisation (`fullJoint_apply_prod`), so the
layered construction coincides with the textbook definition.

```
'DSepSound.dsep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Audit status

The build log establishes that `dsep_sound` has no hidden `sorry`. Whether the
formal statement matches the classical one is a separate question, audited here.

Checked:
- `fullJoint` equals the product of kernels over all vertices (`fullJoint_apply_prod`).
- `marginal` is the pushforward along restriction (summing out).
- `CondIndep` is the product form P(x,y,z)·P(z) = P(x,z)·P(y,z), equivalent to
  the conditional form wherever P(z) > 0.
- Blocking follows Pearl's criterion: non-colliders block when in `Z`; colliders
  block when no descendant-or-self is in `Z` (`Reaches` is reflexive-transitive).
- The hypothesis is non-vacuous: `DSeparated ∅ 0 1` is proved for the collider
  `0 → 2 ← 1` (`Counterexample.lean`); adjacent vertices are never d-separated.

Open:
- Equivalence of walk-based and path-based d-separation. Walk-based is at least
  as strong a hypothesis, so the theorem is at most as strong as the path-based
  classical statement until this is proved.
- A negative sanity check that `CondIndep` can fail.
- A check that conditioning on a collider opens it (`¬ DSeparated {2} 0 1`).
- The result is for single vertices `x`, `y`; the set version is planned.

---

## Proof architecture

1. **Graph side (Lauritzen).** D-separation implies separation in the moral graph
   of the ancestral set of `{x, y} ∪ Z` — `Lauritzen.moral_sep_of_dsep_lauritzen`,
   proved via the Bayes-Ball algorithm (`BayesBall.lean`).
2. **Separator partition.** `separator_partition` splits the ancestral set into
   two sides separated by `Z`.
3. **Ancestral marginalisation.** `marginal_eq_restricted_joint`: the marginal on
   an ancestrally closed set equals the marginal of the restricted model. Proved
   via an explicit product form of the joint (`kfac`, `jointUpTo_apply_prod`,
   `fullJoint_apply_prod`) and a normalisation argument through an auxiliary model
   with pinned kernels (`pinTo`, `sum_compl_kfac_eq_one`).
4. **Factorisation.** `joint_splits`, `product_form_mono`.
5. **Conditional independence.** `condIndep_of_product_form`, `condIndep_transfer`.

---

## Negative results

The naive graph-side statement — d-separation implies separation in the moral
graph of the *whole* DAG — is false. `Counterexample.lean` gives an explicit
counterexample (`moral_sep_of_dsep_counterexample`). The correct statement
restricts to the ancestral set, as in step 1 above. An auxiliary converse
(`open_walk_of_moral`) was likewise shown false and removed.

---

## Other verified results

- **Adjustment:** `backdoor_general`; front-door: `frontdoor_structural`,
  `frontdoor_X_cancellation`, `frontdoor_adjustment_observable`.
- **Graph-to-distribution bridge:** `moral_walk_of_open`, `dsep_of_moral_sep`.
- **Bayes-Ball:** `bbReachable_imp_open_walk`, `DSeparated_imp_not_bbReachable`.

---

## Scope

Not yet covered: the three rules of the do-calculus as such, completeness of
d-separation, and identification algorithms. Planned for v2, building on the
explicit product form (`kfac`), which gives truncated factorisation directly.

---

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned in `lake-manifest.json`).

---

## Related work

- **CausalSmith** (github.com/Jiyuan-Tan/CausalSmith; Tan & Syrgkanis,
  arXiv:2607.22511) — sorry-free declarations covering the do-calculus stack,
  including `full_globalMarkov` (corresponding to `dsep_sound` here) and the
  ID algorithm.
- **Statlib** — ongoing discussion at leanprover.zulipchat.com (#Statlib) of a
  unified Lean library for causal inference and potential outcomes.
