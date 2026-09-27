# PearlDoCalculus

Formal verification of causal inference in Pearl's framework, in Lean 4 on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** v2.0 — d-separation soundness (vertices and sets) and the three rules of the do-calculus machine-checked, rule 3 under a positivity assumption. No `sorry` in the project. Audit: see below.

---

## Main result

```lean
theorem WalkPath.dsep_sound_path (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparatedPath Z x y) : CondIndep M {x} {y} Z
```

For every `CausalModel` (finite vertex set, finite value types, kernels
P(v | pa(v)) as PMFs): if every *path* between `x` and `y` is blocked by `Z` in
Pearl's sense, then `x` and `y` are conditionally independent given `Z` in the
product-form sense of `CondIndep`. All assumptions are those built into
`CausalModel`; the theorem adds none. This is the classical soundness statement
for d-separation in discrete Bayesian networks, for single vertices `x`, `y`.

The set version:

```lean
theorem SetSound.dsep_sound_set (M : CausalModel G α) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : DSeparatedSet G Z X Y) : CondIndep M X Y Z
```

where `DSeparatedSet G Z X Y` means every pair `x ∈ X`, `y ∈ Y` is d-separated
by `Z` in the path-based sense. Pairwise conditional independence does not imply
set independence in general, so this is not a corollary of the vertex version;
it is proved through separation in the moral graph of An(X ∪ Y ∪ Z), with
Lauritzen's theorem and the separator partition generalised to sets
(`SetSound.lean`). `X ∩ Y = ∅` is not assumed: it follows from the hypothesis,
since a vertex is never d-separated from itself.

The proof goes through the walk-based formulation (`DSepSound.dsep_sound`) and
the equivalence

```lean
theorem DAG.dsepPath_iff_dsep : G.DSeparatedPath Z x y ↔ G.DSeparated Z x y
```

proved by loop erasure: from an open walk, jump to the last occurrence of the
head vertex, keep its incoming edge, and recurse on the shorter rest
(`exists_open_path`). Openness is preserved at every jump; the case where the
jump creates a new collider uses acyclicity (`descend_of_open`). The joint
distribution is proved equal to the classical Bayesian-network factorisation
(`fullJoint_apply_prod`).

```
'WalkPath.dsep_sound_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'DSepSound.dsep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Do-calculus

Interventions are modelled by `DoCalculus.doModel M X x`, a causal model on the
mutilated graph `cutIn G X` (Pearl's G_{X̄}) in which the vertices of `X` have
point masses at `x`. Its joint distribution is the truncated factorisation

```
P_x(u) = [u_X = x] · ∏_{v ∉ X} P(u_v | u_pa(v))        (doModel_fullJoint)
```

and two semantic checks confirm that it behaves as an intervention: the marginal
on `X` is a point mass at `x` (`doModel_marginal_self`), and `do(∅)` leaves the
model unchanged (`doModel_empty`).

All three rules are proved in product form, which avoids division and holds also
where the conditional probabilities are undefined.

| Rule | Theorem | Graphical condition |
|---|---|---|
| 1: insert/delete observation | `DoCalculus.rule1` | Y ⊥ Z \| X, W in G_{X̄} |
| 2: action/observation exchange | `DoCalculus.rule2` | Y ⊥ Z \| X, W in G_{X̄Z̲} |
| 3: insert/delete action | `Rule3.rule3` | Y ⊥ Z \| X, W in G_{X̄, Z(W)‾} |

Rule 1 is d-separation soundness applied to the intervened model. Rule 2 is
proved without an augmented graph, through a *clamp model* on G_{Z̲}
(`clampModel`): every vertex keeps its kernel, but parents in `Z` are read from
`z₀`. It coincides with the observational model where `Z = z₀`, and with the
intervention off `Z` (the vertices of `Z` are sinks in G_{Z̲}), so d-separation
in the clamp model yields the rule. Rule 3 splits `Z` into the part `Z₁` that is
ancestral to `W` and the rest `Z₂ = Z(W)`: `do(Z₂)` is removed by ancestral
marginalisation, and `do(Z₁)` by rule 2 together with d-separation soundness.
`Z(W)` is taken in G_{X̄}, as in Pearl (`Z2_cutIn_eq`).

**Rule 3 carries a positivity assumption:** P_x(z₁, x, w) > 0 for the part of `Z`
that is ancestral to `W`. Pearl's rule 3 holds without it; removing it requires
the augmented-graph argument with intervention nodes, which is not yet
formalised. Rules 1 and 2 need no such assumption.

A semantic check shows that the condition of rule 2 does real work: for a hidden
confounder `Z ← U → Y`, the product identity fails
(`DoAudit.rule2_fails_with_confounder`).

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
- Clean build of tag `v1.0` from a fresh clone; signature, definitions and axioms
  archived in `verification/audit_v1_output.txt`. No kernel-bypassing constructs
  (`axiom`, `unsafe`, `implemented_by`, `native_decide`, `skipKernelTC`) in the sources.
- `CondIndep` can fail: `Audit.not_condIndep_dep` for `x → y` with non-degenerate
  uniform kernels, where P(x=1, y=0) = 0 but P(x=1) > 0 and P(y=0) > 0.
- Regression suite for d-separation semantics (`Audit.lean`), all mechanisms in
  both directions: chain `0 → 1 → 2` open given `∅`, blocked given `{1}` (the
  latter over all walks, including those that bounce through the open collider
  formed at `1`); collider `0 → 2 ← 1` blocked given `∅`, opened given `{2}`.
- Walk-based and path-based d-separation are equivalent (`dsepPath_iff_dsep`,
  `WalkPath.lean`), so the walk formulation is a faithful implementation of
  Pearl's path criterion. Tag `v1.0` states the walk-based theorem; `v1.1` adds
  the equivalence and the classical `dsep_sound_path`.
- Set version (`SetSound.dsep_sound_set`): five of the seven links in the proof
  chain were already stated for sets; Lauritzen's theorem (via Bayes-Ball from
  any `x ∈ X`) and the separator partition were generalised. Tag `v1.2`.
- Do-calculus semantics: the intervened model sets `X` (`doModel_marginal_self`),
  `do(∅)` is the identity (`doModel_empty`), and rule 2 fails without its
  condition in a confounded model (`DoAudit.rule2_fails_with_confounder`).
  Tag `v2.0`.

Open:
- Rule 3 without the positivity assumption (requires an augmented graph with
  intervention nodes).

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

Not yet covered: rule 3 without positivity, completeness of d-separation and of
the do-calculus, and identification algorithms (such as the ID algorithm).

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
