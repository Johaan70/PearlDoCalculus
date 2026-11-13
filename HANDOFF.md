# Handoff: state of PearlDoCalculus and how to continue

Written for whoever continues this project (including the author working
alone). Status as of tag `v4.19`.

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
| Rule 3 fails at a trek through `z` into `W` | `rule3_complete_copy` | `Completeness` |
| Rule 3 exact for single vertices | `rule3_complete`, `rule3_iff` | `Completeness` |
| Rule 3 exact for sets | `rule3_complete_set`, `rule3_iff_set` | `Completeness` |
| Back-door, front-door and fully observed ⇒ identifiable | `backdoor_identifiable`, `frontdoor_identifiable`, `observed_identifiable` | `Identification` |
| Bow graph not identifiable | `Bow.bow_not_identifiable` | `Identification` |
| Bow inside any graph not identifiable | `BowGen.bow_not_identifiable_general` | `Identification` |
| Observed parents ⇒ identifiable | `Parents.parents_identifiable` | `Identification` |
| Two-latent hedge not identifiable | `Hedge2.hedge2_not_identifiable` | `Identification` |
| Hedge chains of any length not identifiable | `HedgeChain.chain_not_identifiable` | `Identification` |
| Hedge template | `HedgeTmpl.Tm.not_ident` | `Identification` |
| Latent path with directed tree towards `y` not identifiable | `PathTree.pathTree_not_identifiable` | `Identification` |
| Latent tree with directed tree towards `y` not identifiable | `LatentTree.latentTree_not_identifiable` | `Identification` |
| Identifiability passes to subsets of `Y` | `Identifiable.mono_Y` | `Identification` |
| Non-identifiable for `y` ⇒ for every `Y ∋ y` | `not_identifiable_of_mem` | `Identification` |
| Template with a set `X` | `HedgeTmpl.Tm.not_ident_X` | `Identification` |
| Latent tree with sets `X` and `Y` | `latentTree_not_identifiable_XY` | `Identification` |
| Two-root c-forest not identifiable | `TwoRoot.twoRoot_not_identifiable` | `Identification` |
| Multi-root c-forest not identifiable | `MultiRoot.multiRoot_not_identifiable` | `Identification` |
| `x` into any root, along a latent path | `RootPath.rootPath_not_identifiable` | `Identification` |
| `x` into any root, path constructed | `RootTree.rootTree_not_identifiable` | `Identification` |
| Embedded hedge, any `Y ⊇` roots | `RootTree.embedded_not_identifiable` | `Identification` |
| Channel step: a root may be replaced by its child | `Channel.channel_step` | `Identification` |
| Whole paths: a root may be replaced by the end of a directed path | `Channel.path_not_identifiable` | `Identification` |
| C-component factorization (Tian's Lemma 1), closed blocks | `CFactor.marginal_factor` | `Identification` |
| Intervention in a block changes only that block's factor | `CFactor.do_marginal_factor` | `Identification` |
| Tian's Lemma 2: factors determined by the observed distribution | `CFactor.Q_identifiable`, `CFactor.Q_step` | `Identification` |
| Tian's theorem: no child of `x` in its block ⇒ identifiable, explicit formula | `CFactor.tian_identifiable`, `CFactor.tian_formula` | `Identification` |
| C-component is the least closed block; Tian's theorem with the c-component | `CFactor.ccomp_isLeast`, `CFactor.tian_cond_iff`, `CFactor.tian_identifiable_ccomp` | `Identification` |
| Dividing line for a single `x` (latent roots, Bool): identifiable iff no child of `x` in its c-component | `CFactor.tian_iff`, `CFactor.not_ident_of_child` | `Identification` |
| Decomposition (semi-graphoid) | `condIndep_single` | `Completeness` |

Audits of each tagged version from a fresh clone are archived in
`verification/`. `verification/rule3_search.py` is the exhaustive search
described in section 2.

## 2. Rule 3: closed in v3.8 (vertices) and v3.9 (sets)

`rule3_iff` states that, for `y, z ∉ X ∪ W` with `y ≠ z`, the condition of
rule 3 holds if and only if the product form holds in every model on `G`.
`rule3_complete` splits into three cases:

1. `z` is not an ancestor of `W` in G_{X̄}: `rule3_complete_nonanc` (v3.3).
2. `y` and `z` are d-connected in G_{X̄z̄}: `rule3_complete_root` (v3.6).
3. Otherwise (`rule3_complete_gap`): take a chain from `y` to `z` in G_{X̄}
   with the fewest colliders (`Nat.find`), and the first `w₁ ∈ X ∪ W` that `z`
   reaches (it lies in `W`, since `X` has no parents in G_{X̄}). By minimality
   no source but the last reaches `z`. If `w₁` were a collider `z_j`,
   `Chain.take`, `Chain.snoc` and `Chain.cut` give a chain in G_{X̄z̄}, which
   `no_chain_of_dsep` rules out. Likewise `z` cannot reach `y`. So
   `rule3_complete_chaincopy` applies: the chain model with `w₁` copying the
   last component.

`verification/rule3_chaincopy.py` checks the chain-copy witness numerically in
all 10 029 case-3 instances with up to 5 vertices (0 failures).
`rule3_complete_copy` (v3.7) is the special case of a chain with no colliders.

**Sets: closed in v3.9.** `rule3_iff_set` is rule 3 as an exact equivalence for
disjoint sets `Y`, `Z` outside `X ∪ W`. `rule3_complete_set` has two cases: if
some pair is d-connected in G_{X̄Z̄}, `rule3_complete_set_root` (v3.6); otherwise
`rule3_complete_set_gap`. There `set_gap_core` takes a chain with fewest
colliders over all pairs in G_{X̄Z(W)̄}, and `z` the vertex of `Z` of highest rank
reached by the last source, so that `z` reaches no other vertex of `Z`. If `z`
were in Z(W), or `z` reached `y`, or the first `w₁ ∈ W` reached by `z` were a
collider, `Chain.cutset` would give a chain in G_{X̄Z̄}. One copy vertex is
enough: `rule3_complete_chaincopy_set` sets `z` to 1 and the rest of `Z` to 0
under do(Z). `verification/rule3_set.py` checks the witness in all 7 312 such
cases with |Z| ≥ 2 and up to 5 vertices (0 failures).

**Identification (v4.0).** `Identification.lean` defines identifiability with
latent variables and proves the results listed in the README. The bow proof
avoids numerical sums: the two joints agree after a bijection on assignments
(`full_map`), and the interventional values come from B2 and FD1.

**Open next, in order.**
1. The bow inside any graph: if `U ∉ O` has edges to `X` and `Y` and `X → Y`,
   then `P(Y | do(X))` is not identifiable. Idea: let every other vertex be an
   independent uniform bit, so the observed distribution stays positive.
2. Tian's c-component factorization (the first building block of ID).
3. The hedge criterion (Shpitser–Pearl): hedge ⇒ not identifiable. Together
   with soundness of ID this gives completeness of the do-calculus for
   identification. Causalean already has ID soundness, so the hedge side is
   the part that would be new.

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

## 6. Open problems and technical debt

Open problems (identification, single intervention `x`):
- **Merging tails.** `Channel.path_not_identifiable` replaces a root by the end
  of a directed path (disjoint tails: once per tail). Open is the case where tails
  from several roots meet before reaching `Y`: the meeting vertex reads several
  parents, and a xor of them can lose the difference unless it sits in the parity
  of the roots. A generic lemma would need that the difference between the two
  models has a non-zero parity component on the merged roots.
- **`X` meeting the hedge in several vertices.** Model B needs one channel per
  `x_i`, and the bijection one path per `x_i`; shifts on shared latents add in
  `ZMod 2`. Generalise `pth` and `parZ_φ` to a sum of shifts.
- Beyond that: the ID algorithm and completeness of the do-calculus for
  identification. Roadmap for the positive side below.

Roadmap for the positive side (start from `CFactor`, round 20):
1. **Tian's Lemma 1 for many blocks.** Round 20 has two blocks (`S`, `Sᶜ`).
   Induction over a list of pairwise disjoint closed blocks gives
   `P(Uᶜ = a) = ∏_j Q[S_j](a)`. Only `full2`/`val1`/`val2` need generalising.
2. **Tian's Lemma 2. DONE (v4.17, `Q_identifiable`, `Q_step`).** Proved by
   induction over ancestral sets instead of a topological list; no root assumption.
3. **Tian's theorem. DONE (v4.17, `tian_identifiable`, `tian_formula`)** for a
   single observed `x`. Next natural step: `X` a set (sum over `X ∩ S` in
   `sum_Q_upd`, needs no child of any `x ∈ X` in `S`), then a theorem that states
   the dividing line in one place: for single `x`, identifiable iff no child of `x`
   in its c-component. DONE (v4.19, `tian_iff`) for latents that are roots and
   Bool-valued variables. Open generalisations: (a) latents with latent parents
   (a shortest chain may then pass latent → latent, which `RT` does not fit; it
   would need an `RT` variant whose tree edges are latent paths); (b) other value
   types than `Bool` (embed `Bool` into each `α v` with at least two values);
   (c) `Y` smaller than `O ∖ {x}` (needs the ancestral
   reduction of the ID algorithm).
4. **ID algorithm, soundness.** Seven lines (Shpitser–Pearl 2006); each line is
   a marginalisation, a factorization (steps 1–2) or a restriction to an
   ancestral set (`marginal_ancestral_apply`). Define it as a recursive
   function returning `Option` of a formula, prove soundness by recursion.
5. **Completeness.** Line 5 of ID fails exactly at a hedge; rounds 14–19 cover
   single-`x` hedges with disjoint tails. Merging tails and `X` in several
   vertices (above) remain.

Technical debt (harmless, but worth cleaning):
- Many `first | a | b | c` fallbacks were written because the exact Mathlib
  lemma form could not be checked in advance. Each could be pruned to the branch
  that succeeds.
- `Identification.lean` is about 6 730 lines; one file per round
  (`Identification/Bow.lean`, …) would be easier to navigate.
- Small helpers (`pure1`, `pure0`, `c2`, `pOf`/`parOf`/`parOfA`) are repeated in
  several namespaces.
- `TwoRoot` (round 13) is mathematically the case `n = 0`, `r = 1` of `RootTree`,
  but is not yet derived from it.
- The Zulip draft in section 5 describes tag `v3.5`.
