# Handoff: state of PearlDoCalculus and how to continue

Written for whoever continues this project (including the author working
alone). Status as of tag `v4.35`.

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
| Tian's theorem for a set `X` in a closed block (corollaries since v4.23) | `CFactor.tian_identifiableX`, `CFactor.tian_identifiable_ccompX` | `Identification` |
| Factorization over many closed blocks (ID line 4) | `CFactor.Q_split`, `CFactor.Q_prod`, `CFactor.marginal_prod` | `Identification` |
| Sets `X`: one sum per c-component; no `x` with a child in its own c-component ⇒ identifiable | `CFactor.tian_formula_blocks`, `CFactor.tian_identifiable_sets` | `Identification` |
| Each factor is a causal effect: `P_{do(O ∖ S)} = [·] · Q[S]` | `CFactor.Q_causal`, `CFactor.lat_one` | `Identification` |
| Tian's lemma: `Σ_{T∖S} Q[T] = Q[T ∩ S]` for `S` ancestral in `T` | `CFactor.Q_marg`, `CFactor.Q_marg_eq` | `Identification` |
| Tian's lemma 11: `Q[T]` known ⇒ `Q[T ∩ S]` known for `S` closed inside `T` | `CFactor.Q_ident_within`, `CFactor.Q_split_rel`, `CFactor.Q_le_one` | `Identification` |
| Tian's IDENTIFY is sound: `C` reachable from `V` ⇒ `Q[C]` determined by `P(O)` | `CFactor.Reach`, `CFactor.reach_sound`, `CFactor.reach_ident` | `Identification` |
| ID soundness for sets (lines 4, 6, 7): all c-components of `G_{X̄}` reachable ⇒ identifiable | `CFactor.id_sound`, `CFactor.id_sound_blocks` | `Identification` |
| ID soundness with line 2: c-components of `G_{X̄}[S]`, `S ⊇ Y` ancestral, reachable ⇒ identifiable | `CFactor.id_sound_anc`, `CFactor.id_sound_anc_blocks`, `CFactor.fiber_eq` | `Identification` |
| Test case: `x ↔ b ↔ y`, `x → y` — Tian's set criterion fails, ID recursion succeeds | `IdAudit.id_audit`, `IdAudit.tian_sets_fails` | `IdAudit` |
| Verma constraints: `Q[T]` is local; sums over a non-ancestral part depend only on the rest | `CFactor.Q_local`, `CFactor.verma_sum` | `Identification` |
| Verma's example: `Σ_b P(b|a) P(d|a,b,c)` independent of `a` | `Verma.verma_constraint`, `Verma.vermaF_eq_Q` | `Verma` |
| ID as a computable check: `identifyTop = true` ⇒ `Reach` | `IdAlgo.identifyTop_sound`, `IdAlgo.identifyN_sound`, `IdAlgo.iter_fix` | `IdAlgo` |
| The whole ID check: `idCheck G U X Y = true` ⇒ `P(Y | do(X))` identifiable | `IdAlgo.idCheck_sound`, `IdAlgo.ccIn_eq` | `IdAlgo` |
| IDC: rule 2 moves `Z`, `P(Y,X,W | do(X ∪ Z))` identifiable ⇒ `P(Y | do(X), Z, W)` identifiable | `Idc.idc_sound`, `Idc.IdentifiableCond` | `Idc` |
| Two interventions in a row are one; positive `P` ⇒ positive interventional marginals | `Idc.doModel_doModel_marginal`, `Idc.doModel_marginal_ne_zero` | `Idc` |
| `idCheck = false` ⇒ IDENTIFY stuck at `T ⊋ D`, `T` ancestral to `D`, `T` meets `X` | `Hedge.idCheck_false_meets`, `Hedge.stuck_meets_X`, `Hedge.identifyN_false` | `Hedge` |
| Decomposition (semi-graphoid) | `condIndep_single` | `Completeness` |

Fresh-clone audits (exact statements via `#check @`, axioms) are archived in
`verification/` for tags `v1.0`, `v2.0`, `v2.2` and `v4.23`. Every other tag was checked
by the regular build with `#print axioms` on its main results, not from a fresh
clone. `verification/rule3_search.py` is the exhaustive search
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
   identification. Causalean already has ID soundness (also the recursive
   version), so the hedge side is the part that would be new.

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
- `tsum` carries a summation filter in this Mathlib; `rw [← tsum_fintype]` gets stuck
  on `SummationFilter.LeAtTop ?m`. Write the step as `calc` with the `tsum` stated.
- When a set such as `(T ∩ Sᶜ) \ U` occurs inside the goal, give general set lemmas
  their arguments (`Finset.sdiff_eq_inter_compl T S`); otherwise `rw` may hit the
  inner set and fail with "motive is not type correct". Likewise, give explicit
  arguments instead of `_` when they only occur under a function application.

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
`a7085d8`), it has global Markov, rule 1, restricted forms of rules 2–3 and
soundness of the full recursive ID algorithm, but not completeness of
d-separation or of individual rules, and no non-identifiability results for
hedges. Our c-component factorization and Tian's theorem overlap with its ID
soundness; the hedge families and `tian_iff` do not.
Corrections welcome, and I'd be glad to hear if anyone has done this before.

Disclosure: the proofs were developed with substantial help from Claude
(Anthropic). All proofs are checked by Lean; the README lists which tags have
fresh-clone audits.

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
   single observed `x`; for a set `X` DONE (v4.20, `tian_identifiableX`) as a
   sufficient condition. Then a theorem that states
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
4b. **The ID algorithm line by line (status v4.21).** Shpitser–Pearl 2006, Fig. 3.
   - Line 1 (`X = ∅`, marginalise): `marginal_restrict`.
   - Line 2 (restrict to `An(Y)`): ingredients `CausalModel.restrictTo`,
     `marginal_eq_restricted_joint`. Missing: the do-version (intervening and then
     restricting commute) and that the restricted model's observed marginal is
     determined by `P`.
   - Line 3 (add `W` to `X`): rule 3. `Rule3Flag.rule3_general` is stated in a
     product form with a conditioning set; check that it gives the nested
     `doModel` form line 3 needs.
   - Line 4 (factor over the c-components of `G ∖ X`): DONE as building blocks.
     `Q_prod`, `marginal_prod` give the factorization, and `Q_causal` (v4.22) shows
     that each factor is the causal effect `P_{do(O ∖ S)}`, so the recursion can
     call ID on it. Still to do: the same for the c-components of `G ∖ X` (blocks
     closed only in the graph without `X`), i.e. apply `Q_causal` inside
     `doModel M X x`.
   - Line 5 (fail): rounds 14–19 (single `x`), `tian_iff`.
   - Line 6 (`S` a c-component of `G`): `Q_identifiable`, `Q_step`.
   - Line 7 (`S ⊂ S' ∈ C(G)`): first building block DONE (v4.25, `Q_marg`):
     summing a factor over the observed vertices outside an ancestral part gives
     that part's factor. No sub-model needed. Tian's lemma 11 DONE (v4.26,
     `Q_ident_within`). The recursion DONE (v4.27): inductive predicate `Reach`
     (shape after Causalean's `CFactorReachableRec`), soundness `reach_ident`.
     Put together for sets in v4.28 (`id_sound`): the c-components of `G_{X̄}`
     are `{x}`, purely latent blocks, and blocks outside `X`, whose factors equal
     `Q[D]` in the original model. Line 2 in v4.29 (`id_sound_anc`): `S` ancestral
     in `G_{X̄}`, blocks the c-components of `G_{X̄}[S]`. With `S = An(Y)` in
     `G_{X̄}` this also covers what line 3 achieves (nodes outside `S` are summed
     out in the intervened model), so no separate rule-3 step is needed.
   - Test case beyond `tian_identifiable_sets`: DONE (v4.30, `IdAudit`).
     ID as a computable check: step H1 in section 7.
5. **Completeness.** Line 5 of ID fails exactly at a hedge; rounds 14–19 cover
   single-`x` hedges with disjoint tails. Merging tails and `X` in several
   vertices (above) remain. Step-by-step plan: section 7.

Technical debt (harmless, but worth cleaning):
- Many `first | a | b | c` fallbacks were written because the exact Mathlib
  lemma form could not be checked in advance. Each could be pruned to the branch
  that succeeds.
- `Identification.lean` is about 8 280 lines; one file per round
  (`Identification/Bow.lean`, …) would be easier to navigate.
- Small helpers (`pure1`, `pure0`, `c2`, `pOf`/`parOf`/`parOfA`) are repeated in
  several namespaces.
- `full2` (round 20), `full3` (round 21) and `join2` (round 26) are three versions of
  the same splitting of latent assignments. `marginal_factor` could be derived from
  `anc_factor` or `Q_split`, but the dependent `Assignment` types (`Uᶜ ∩ univ` vs
  `Uᶜ`) make that a refactor of its own.
- Round 25 was superseded by round 27 within the same session; since v4.23 its
  theorems are corollaries (round 29) and only its helper lemmas remain.
- `TwoRoot` (round 13) is mathematically the case `n = 0`, `r = 1` of `RootTree`,
  but is not yet derived from it.
- The Zulip draft in section 5 describes tag `v3.5`.

## 7. Plan: completeness of the ID algorithm for sets (the hedge criterion)

Written at v4.31. The positive side is done (`id_sound_anc`); this section says
how to finish the negative side so that the two meet in one `iff`. Nobody has
formalised this part as far as we know (Causalean's `identifyMassRec_hedge` is
only the failing branch of the recursion; it does not prove non-identifiability).

**Target theorem** (Shpitser & Pearl 2006, Thm 4; Huang & Valtorta 2006). For a
graph whose latents are roots, `X`, `Y` observed and disjoint:

  `P(Y | do(X))` is identifiable  ⟺  ID succeeds  ⟺  there is no hedge for
  `P_X(Y)`.

**What is already there.**
- Positive: `id_sound_anc` (any `Reach` witness for each c-component of
  `G_{X̄}[S]`, `S ⊇ Y` ancestral in `G_{X̄}`); `Reach`, `reach_closed`, `Reach.trans`.
- Negative, single `x`, `Bool` values, latents roots: `tian_iff`,
  `not_ident_of_child`; hedge families `RootTree.embedded_not_identifiable` (roots
  in `Y`), `HedgeTmpl.Tm.not_ident_X` (template with a set `X`), tails by
  `Channel.path_not_identifiable` and `Channel.rootTree_tail` (one disjoint path per
  root).
- Transfer lemmas: `Channel.not_ident_of_sub` (more edges never help),
  `Identifiable.mono_Y`, `not_identifiable_of_mem`.
- Test graphs: `IdAudit.idG` (ID succeeds, Tian's set criterion fails), the bow
  `bowG` (ID fails), `Verma.vG`.

**Step H0: fix the scope (decide before writing code).**
- Latents are roots (`hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u`), as in `tian_iff`.
- Value types. The existing negative results use `Bool`. With merging tails
  `Bool` is not enough in general (xor can cancel). As we read Shpitser–Pearl's
  proof, the tail step lets variables on the tails carry tuples of bits (check
  this against the paper before relying on it). Recommended
  statement: "not identifiable for `α v = Fin (2 ^ |V|)`" (or any `α` with at
  least that many values, via an embedding — open item (b) in section 6). The
  `iff` is then: identifiable for every `α` ⟺ ID succeeds.

**Step H1: ID as a decidable function. DONE (v4.32–v4.33, `IdAlgo.lean`):**
`ancIn`, `ccIn`, `identifyN`, `identifyTop`, `identifyTop_sound`, `idCheck`,
`idCheck_sound`, `ccIn_eq`; `decide` checks on `IdAudit.idG` (true, `id_audit'`) and
the bow (false). For H2 note: `identifyN` uses fuel; completeness needs that
`Fintype.card V + 1` is enough (each step shrinks `T` strictly).
Original plan:
- `ancIn G T C`: vertices of `T` with a directed path inside `G[T]` into `C`.
  Lemma: it satisfies the `anc` side condition of `Reach`
  (`∀ v ∈ T ∩ A, ∀ p ∈ T, G.edge p v → p ∈ A`).
- `ccIn G U T C`: union over `c ∈ C` of `ccomp (DAG.induce G T) U c`. Lemma: it
  satisfies the `block` side condition of `Reach` inside `T`.
- `identify G U T C : Bool`, by well-founded recursion on `T.card` (Tian's
  IDENTIFY): `A := ancIn G T C`; if `A = C` then `true`; else if `A = T` then
  `false`; else `identify G U (ccIn G U A C) C`. Termination: the new set is
  `⊆ A ⊊ T`.
- `identify_sound : identify G U T C = true → Reach G U T C` (anc step, block
  step, induction on the recursion). With `reach_closed` and `Reach.trans`, start
  from `T := ccomp G U` of the block.
- `idCheck G U X Y : Bool`: `identify` on every c-component of
  `G_{X̄}[An(Y)]` with an observed vertex outside `X`. Corollary of
  `id_sound_anc`: `idCheck = true → Identifiable`. Check it with `decide` on the
  three test graphs (true, false, true).

**Step H2: failure gives a hedge. Partly DONE (v4.35, `Hedge.lean`):** `Stuck`,
`identifyN_false` (the fuel suffices), `idCheck_false`, and (i) as `stuck_meets_X`.
On (ii): in Shpitser–Pearl a C-forest is a *subgraph* (each vertex keeps at most one
child edge), so the roots need not be childless in `G[F']`. With `R :=` the vertices
of `D` without a child in `D`, both `D` and `T` are `R`-rooted: every vertex of `D`
reaches `R` inside `D` (follow children; the rank grows), and every vertex of `T`
reaches `D` inside `T`. So `(D, T)` is the hedge; what remains is c-connectivity of
`D` and `T` inside themselves. Original plan: When
`identify` returns `false` it stops at a `T*` with `C ⊊ T*`, `ancIn G T* C = T*`,
and `T*` a single c-component of `G[T*]` (it came out of a block step).
- Define `IsCForest G U F R` (Shpitser–Pearl Def. 4): `F` is one c-component of
  `G[F]`, `R` is the set of vertices of `F` with no child in `F`, every vertex
  of `F` has a directed path in `G[F]` to `R`. `IsHedge G U X Y F F'`:
  `F ⊊ F'`, both `R`-forests with the same `R ⊆ An(Y)_{G_{X̄}}`, `F ∩ X = ∅`,
  `F' ∩ X ≠ ∅`.
- Prove: at the failure point, `(C, T*)` is a hedge, after trimming `C` to its
  own root set. Two facts carry it: (i) `T* ∩ X ≠ ∅` (otherwise all of `T*` lies
  in `G_{X̄}[S]` and is c-connected to `C`, contradicting that `C` is a
  c-component there); (ii) the root sets agree. (ii) is the delicate point.
  Follow the line-5 case of Shpitser–Pearl's proof, where the roots are the
  current target `Y'` and every vertex of the current graph is an ancestor of
  `Y'`. It may be easier to carry `Y' := roots` explicitly through the recursion
  than to recover it at the end.

**Step H3: a hedge is not identifiable on its roots (3–5 rounds).** Generalise
`HedgeTmpl.Tm` / `RootTree.RT` from one `x` to `X ∩ F'` arbitrary. Model A: every
observed vertex in `F'` is the xor of its parents in `F'`, latents fair coins.
Model B: the same on `F`, with the extra parents in `F' ∖ F` read through one
channel per `x ∈ X ∩ F'`. The open item "X meeting the hedge in several
vertices" (section 6) is exactly this: the shifts on shared latents add in
`ZMod 2`; generalise `pth` and `parZ_φ` to a sum of shifts. Result:
`¬ Identifiable G α O X R` for the hedge's root set `R`.

**Step H4: from the roots to `Y` (2–3 rounds).** `R ⊆ An(Y)_{G_{X̄}}`, so each
root has a directed path to `Y` avoiding `X`. With disjoint paths
`Channel.rootTree_tail` already does it. The open item is merging tails. With
`α v = Fin (2 ^ |V|)` (H0) each tail vertex can store the tuple of the bits it
receives, so nothing cancels. Choose one outgoing tail edge per vertex (an
in-forest towards `Y`) and prove a `Channel` lemma for a tree of tails instead
of a path; `not_ident_of_sub` removes all other edges first.

**Step H5: put it together (1 round).**
`id_iff : idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y` (with the
H0 assumptions). `→` is H1. `←` is the contrapositive: H2 gives a hedge, H3
and H4 give `¬ Identifiable` for the chosen `α`.

**Estimate.** 10–15 rounds of the size of rounds 30–36. Highest risk: H2 (ii)
and H4. Lowest risk: H1 (same proof patterns as rounds 32–35, and `decide`
works on the concrete graphs). H1 is worth doing on its own: it turns the
`Reach` hypothesis into a computable check.
