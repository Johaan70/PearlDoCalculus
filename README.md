# PearlDoCalculus

Formal verification of Judea Pearl's do-calculus in Lean 4, built on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** Active — ten sorry-free results, four documented open problems

---

## What is verified

All ten results below are sorry-free and depend only on `[propext, Classical.choice, Quot.sound]`.

### Causal adjustment
- **`backdoor_general`** — The backdoor adjustment formula.
- **`frontdoor_condIndep`**, **`frontdoor_marginal`**, **`frontdoor_adjustment`** — The front-door criterion and adjustment formula.

### Graph-to-distribution bridge
- **`moral_walk_of_open`** — Every active walk in a DAG induces a walk in the moral graph that avoids Z. The hard direction of the moralization criterion.
- **`dsep_of_moral_sep`** — Separation in the moral graph implies d-separation in the DAG.

### Factorization machinery
- **`extendOverList_factorizes'`** — The joint distribution factors along the structural causal model.
- **`jointUpTo_factorizes`** — The joint up to topological level n factorizes along the separator.
- **`joint_splits`** — The full joint splits into a product when conditioned on a separator.
- **`condIndep_of_product_form`** — Product form implies conditional independence.

---

## What remains open

Four `sorry` remain, each with a precise explanation of the mathematical obstacle.

### `open_walk_of_moral` (Skeleton.lean ~1294)
Converse of `moral_walk_of_open`: a moral walk avoiding Z should yield an active walk in G.

**The obstacle:** The `bwd`-step and marriage-edge case require the collider node `c` to lie in `bbZAncestors Z`. This does not follow from `hclosed` alone. The formulation with `forall inc : DAG.Incoming` in the conclusion is too strong.

### `moral_sep_of_dsep` (Skeleton.lean ~1354)
D-separation implies separation in the moral graph.

**The obstacle:** Depends on `open_walk_of_moral` (contrapositive).

### `dsep_sound'` (Skeleton.lean ~1848)
The main soundness theorem: d-separation implies conditional independence in every causal model.

**The obstacle:** The proof chain goes `moral_sep_of_dsep -> separator_partition -> joint_splits -> condIndep_of_product_form`. All steps after the first are proved.

### `all_goals sorry` in `jointUpTo_factorizes` (Skeleton.lean ~979)
An unresolved metavariable from `restrict_cast_eq` calls. Not a false goal.

---

## Bayes-Ball (Probe139.lean)

As an alternative route, we formalized the Bayes-Ball algorithm. The following are sorry-free:

- `bbNext`, `bbReachable` — the algorithm
- `not_blockedAux_imp_open` — bridge between blockedAux and Walk.Open
- `bbReachable_imp_open_walk` — Bayes-Ball reachability implies an open Walk
- `DSeparated_imp_not_bbReachable` — d-separation implies no Bayes-Ball path

The missing piece is `open_walk_imp_bbReachable` (open Walk implies Bayes-Ball reachable). Walk.Open permits colliders in Z, but bbNext requires non-collider nodes to be outside Z — a stronger induction hypothesis is needed.

---

## Why the obstacles are genuine

Both open problems reduce to the same fact: the moralization criterion requires knowing which colliders are activated by Z, encoded in `bbZAncestors Z`. Our hypothesis `hclosed` (ancestral closure) is weaker.

CausalSmith (Tan & Syrgkanis, arXiv:2607.22511) solved this by building Bayes-Ball as the primary primitive. Their `full_globalMarkov` corresponds to our `dsep_sound'`.

---

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned in `lakefile.lean`).

---

## Related work

- **CausalSmith** (github.com/Jiyuan-Tan/CausalSmith) — 8,675 sorry-free declarations covering the full do-calculus stack including `full_globalMarkov` and the ID algorithm.
- **Statlib** — ongoing discussion at leanprover.zulipchat.com (#Statlib) of a unified Lean library for causal inference and potential outcomes.
