# PearlDoCalculus

Formal verification of causal inference in Pearl's framework, in Lean 4 on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** v1.0 — soundness of d-separation fully machine-verified. No `sorry` in the project.

---

## Main result

```lean
theorem DSepSound.dsep_sound (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y) : CondIndep M {x} {y} Z
```

For every causal model on a finite DAG with finite value types: if `x` and `y`
are d-separated given `Z`, then `x` and `y` are conditionally independent given
`Z` in the joint distribution (Verma–Pearl soundness, the directed global Markov
property). No further hypotheses.

```
'DSepSound.dsep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

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
