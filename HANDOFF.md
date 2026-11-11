# Handoff: state of PearlDoCalculus and how to continue

Written for whoever continues this project (including the author working
alone). Status as of tag `v3.6`.

## 1. What is proved

Everything below builds with no `sorry` and depends only on `propext`,
`Classical.choice` and `Quot.sound`. Causal models are finite DAGs with finite
value types (`PMF`-based, no measure theory).

| Result | Main declarations | File |
|---|---|---|
| d-separation soundness (walks, paths, sets) | `dsep_sound`, `dsep_sound_path`, `dsep_sound_set` | `DSepSound`, `WalkPath`, `SetSound` |
| d-separation completeness | `dsep_complete` | `Completeness` |
| d-separation as an exact criterion (vertices, sets) | `dsep_iff`, `dsepPath_iff`, `dsepSet_iff` | `Completeness` |
| Do-calculus rules 1–3, Pearl's form, no positivity | `rule1`, `rule2`, `rule3_general` | `DoCalculus`, `Rule3Flag` |
| Back-door and front-door, Pearl's path criteria | `backdoor_adjustment_criterion`, `frontdoor_adjustment_criterion` | `Adjustment` |
| Rules 1 and 2 exact (vertices and sets) | `rule1_iff`, `rule1_iff_set`, `rule2_iff`, `rule2_iff_set` | `Completeness` |
| Rule 3 exact when no vertex of `Z` is an ancestor of `W` | `rule3_iff_nonanc`, `rule3_iff_set_nonanc` | `Completeness` |
| Rule 3 fails when `Y`, `Z` are d-connected in G_{X̄Z̄} | `rule3_complete_root`, `rule3_complete_set_root` | `Completeness` |
| Decomposition (semi-graphoid) | `condIndep_single` | `Completeness` |

Audits of each tagged version from a fresh clone are archived in
`verification/`. `verification/rule3_search.py` is the exhaustive search
described in section 2.

## 2. The open problem

**Completeness of rule 3 when some vertex of `Z` is an ancestor of `W` in
G_{X̄}.** For singletons the statement would be:

```lean
theorem rule3_complete_anc (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∈ ancestors (cutIn G X) W)
    (h : ¬ (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z) :
    ∃ k M x t, ¬ (the product form of rule3_general)
```

Here Z(W) = ∅, so the condition is y ⊥ z | X ∪ W in G_{X̄} itself.

**Narrowed in v3.6.** `rule3_complete_root` covers every case where `y` and
`z` are d-connected given X ∪ W in G_{X̄z̄}, even when `z` is an ancestor of `W`.
What remains open is exactly: `y` and `z` are d-separated in G_{X̄z̄} but
d-connected in G_{X̄}, with `z` an ancestor of `W`. Among all DAGs with up to 5
vertices this is 10 029 of 201 923 failing cases (`verification/rule3_gap.py`);
in 9 200 of them there is a directed path y → … → z avoiding X ∪ W. The
smallest instance is y → z → w with W = {w}.

**Evidence that it is true.** `verification/rule3_search.py` checks all DAGs
with 3 and 4 vertices and all choices of y, z, X, W. In each of the 2 267 cases
where the condition fails, the rule fails in one of 25 random binary models. In
each of the 4 789 cases where the condition holds, the rule holds in all models
(a check of the script against `rule3_general`).

**Why the existing technique does not reach it.** Every completeness proof so
far takes the chain model of `dsep_complete` on a graph where the intervened
vertices have no parents (rule 1, rule 3 non-ancestor case) or no children
(rule 2), lifts it to `G` (`liftSub`, `marginal_eq_of_kfac`), and reduces the
rule to `CondIndep` in the chain model. That cannot work here. Take
`y → z → w` with W = {w}. Rule 3 fails (observing `w` informs about `y`
through `z`; do(z) breaks this). But in any model where `z` ignores its
parents, `y` is independent of everything, so no model with `z` as a root
witnesses the failure.

**A direct witness in that example.** z copies y, w copies z, all uniform
bits. With z₀ = 1: P_z(y=0, w=1) · P(w=1) = 1/2 · 1/2, while
P(y=0, w=1) · P_z(w=1) = 0. The failure is visible from zero/non-zero
probabilities alone, as in all other completeness proofs here.

**Suggested approach (not checked).** Since `z` is an ancestor of `W`, take a
directed path z → … → w₁ to the first vertex of `W` on it, with interior
outside X ∪ W. Combine the chain model for the open walk from `y` to `z` with
a copy of the value of `z` along this path, so that observing w₁ amounts to
observing `z`, while do(z) fixes w₁ independently of the rest. The difficulty
is that the path and the chain may share vertices; that interaction is where
a careful paper proof is needed before any Lean.

## 3. Workflow that worked

- One branch per piece of work; fast-forward merge to `main`; tag milestones;
  audit commits go on `main` after the tag.
- **Paper first.** Write the argument out, split it into lemmas of a few dozen
  lines, and only then write Lean.
- **Statement before proof.** Check that the statement type-checks with
  `sorry`, then fill in the proof.
- Edits are made by small Python scripts that `assert` the exact old text
  occurs once, and that skip if the change is already there. This made it safe
  to rerun blocks.
- Builds are gated: tag only if `lake build` shows no `error` and no
  `declaration uses 'sorry'`.
- One error at a time. To see the first goal:
  `lake build X 2>&1 | sed -n '/X.lean:[0-9]*:[0-9]*: \(unsolved\|error\)/,/^info\|^warning\|^error: Lean/p' | head -50`
- Audit each tag from a fresh clone: `#check @thm` for exact statements,
  `#print axioms` for each main result, and grep for `sorry`, `axiom`,
  `native_decide`, `implemented_by`.

## 4. Techniques and pitfalls

Techniques:
- Compare models on different graphs through their kernel factors
  (`marginal_eq_of_kfac`), never through equality of the models; this avoids
  transport between dependent types.
- Build assignments with membership proofs directly instead of `cast`.
- For zero/non-zero arguments, `Audit.marginal_eq_zero_of` and
  `Audit.marginal_ne_zero_of` reduce marginals to kernel factors.
- Proof-irrelevance: restrictions of restrictions are definitionally equal to
  direct restrictions; use `exact` or a `have` with a stated type when `rw`
  fails to see this.

Pitfalls that cost rounds:
- `decide` refuses goals in a context with free variables; use the named
  lemma (`Bool.false_ne_true`).
- Names drift between Mathlib versions (`Finset.not_mem_empty` vs
  `notMem_empty`); prefer term proofs that avoid them.
- `Incoming` lives in `PearlDoCalculus.DAG`, not in `DAG.Walk`.
- When a rewrite lemma has a set as an implicit argument and the goal has
  several marginals of the same model, give the sets explicitly
  (`(S := …) (T := …)`), or the pattern hits the first marginal.
- Before `induction` on a copy of a hypothesis, `clear` the original, or the
  induction hypothesis gets an extra argument.
- In Python heredocs with `'EOF'`, write `"\n"`, not `"\\n"`.
- Pasting a new block while `lake build` is still running interrupts it.

## 5. Draft for Lean Zulip (#Statlib)

**Title:** Completeness of d-separation and of do-calculus rules, machine-checked

Hi all. I'd like to share a Lean 4 project, PearlDoCalculus
(github.com/Johaan70/PearlDoCalculus, tag `v3.5`), for causal models on finite
DAGs with finite value types (PMF-based, no measure theory). All results depend
only on `propext`, `Classical.choice` and `Quot.sound`.

What is proved:
- **d-separation as an exact criterion** (`dsepPath_iff`, `dsepSet_iff`): for
  disjoint sets, d-separation holds iff conditional independence holds in every
  causal model on G. Soundness (Verma–Pearl) plus completeness
  (Geiger–Verma–Pearl), via an explicit model with one bit per source, OR
  outside Z and XOR at the conditioned colliders.
- **The three rules of the do-calculus** in Pearl's form, rule 3 with the Z(W)
  premise and without positivity.
- **Each rule as an exact equivalence**: rules 1 and 2 in full (with sets), and
  rule 3 when no vertex of Z is an ancestor of W. The remaining case of rule 3
  is open; an exhaustive search over small graphs found no counterexample.
- **Back-door and front-door adjustment** under Pearl's criteria stated in terms
  of paths.

Relation to CausalSmith/Causalean: that library is much broader and
measure-theoretic. As far as I could find by searching its source (commit
`1769741`), it has global Markov, rule 1, restricted forms of rules 2–3 and ID
soundness, but not completeness of d-separation or of individual rules.
Corrections welcome, and I'd be glad to hear if anyone has done this before.

Disclosure: the proofs were developed with substantial help from Claude
(Anthropic). All proofs are checked by Lean; the README documents an audit of
each tagged version from a fresh clone.
