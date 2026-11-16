# Handoff: state of PearlDoCalculus and how to continue

Written for whoever continues this project: the author, another person, or an
AI assistant starting without the conversations that produced it. Status as of
tag `v4.45` (November 2026).

## 0. Start here

**What this is.** A Lean 4 formalisation of Pearl's causal calculus for finite
DAGs with finite value types (`PMF`-based, no measure theory): d-separation, the
three rules of the do-calculus, adjustment formulas, and an identification layer
with latent variables (Tian's c-factors, the ID algorithm, IDC, the hedge
criterion). About 21 000 lines. No `sorry`; every main result depends only on
`propext`, `Classical.choice` and `Quot.sound`.

**Use tag `v4.38` or later.** Tag `v4.37` does not build (an `omit` in
`Hedge.lean` named an instance that `nxt` uses, and the release script committed
on a stale build log). It is kept only because it was already pushed.

**Build.**
```
git clone https://github.com/Johaan70/PearlDoCalculus && cd PearlDoCalculus
lake exe cache get      # Mathlib cache
lake build              # must end in "Build completed", no "declaration uses 'sorry'"
```
Toolchain `leanprover/lean4:v4.30.0-rc2` (`lean-toolchain`); Mathlib pinned in
`lake-manifest.json`. Most docstrings and section comments are in Norwegian;
declaration names, this file and the README are in English.

**The one big open target.** Completeness of the ID algorithm for sets: if ID
fails, the effect is not identifiable. The positive side (ID ⇒ identifiable) and
the first half of the negative side (ID fails ⇒ a hedge exists) are done. What
remains is *hedge ⇒ not identifiable* in general (steps H3–H5, section 2).
Begin with step H3 below; the construction is written out there, from the paper.

**Where things are.** Section 1 lists what is proved, section 2 the plan,
section 3 the scope limits, section 4 a map of the files, sections 5–6 how to
work, section 7 history worth keeping, section 8 technical debt.

## 1. What is proved

Causal models are finite DAGs with finite value types. Latent vertices are a
set `U`; observed are `O = Uᶜ`. `Identifiable G α O X Y` means: any two models on
`G` with value types `α` whose observed distributions agree and are positive give
the same `P(Y | do(X))`.

| Result | Main declarations | File |
|---|---|---|
| d-separation soundness (walks, paths, sets) | `dsep_sound`, `dsep_sound_path`, `dsep_sound_set` | `DSepSound`, `WalkPath`, `SetSound` |
| d-separation completeness | `dsep_complete` | `Completeness` |
| d-separation as an exact criterion (vertices, sets) | `dsep_iff`, `dsepPath_iff`, `dsepSet_iff` | `Completeness` |
| Do-calculus rules 1–3, Pearl's form, no positivity | `rule1`, `rule2`, `rule3_general` | `DoCalculus`, `Rule3Flag` |
| Back-door and front-door, Pearl's path criteria | `backdoor_adjustment_criterion`, `frontdoor_adjustment_criterion` | `Adjustment` |
| Rules 1 and 2 exact (vertices and sets) | `rule1_iff`, `rule1_iff_set`, `rule2_iff`, `rule2_iff_set` | `Completeness` |
| Rule 3 exact (vertices and sets) | `rule3_iff`, `rule3_iff_set` (cases: `rule3_iff_nonanc`, `rule3_complete_root`, `rule3_complete_copy`, `rule3_complete_set`) | `Completeness` |
| Back-door, front-door and fully observed ⇒ identifiable | `backdoor_identifiable`, `frontdoor_identifiable`, `observed_identifiable` | `Identification` |
| Observed parents ⇒ identifiable | `Parents.parents_identifiable` | `Identification` |
| Bow graph not identifiable, also inside any graph | `Bow.bow_not_identifiable`, `BowGen.bow_not_identifiable_general` | `Identification` |
| Hedge families not identifiable (special shapes) | `Hedge2.hedge2_not_identifiable`, `HedgeChain.chain_not_identifiable`, `HedgeTmpl.Tm.not_ident`, `HedgeTmpl.Tm.not_ident_X`, `PathTree.pathTree_not_identifiable`, `LatentTree.latentTree_not_identifiable`, `latentTree_not_identifiable_XY`, `TwoRoot.twoRoot_not_identifiable`, `MultiRoot.multiRoot_not_identifiable`, `RootPath.rootPath_not_identifiable`, `RootTree.rootTree_not_identifiable`, `RootTree.embedded_not_identifiable` | `Identification` |
| Transfer: subsets of `Y`, supersets of `y`, more edges never help | `Identifiable.mono_Y`, `not_identifiable_of_mem`, `Channel.not_ident_of_sub` | `Identification` |
| Tails: a root may be replaced by the end of a directed path | `Channel.channel_step`, `Channel.path_not_identifiable`, `Channel.rootTree_tail` | `Identification` |
| C-component factorization (Tian's Lemma 1), many blocks | `CFactor.marginal_factor`, `CFactor.Q_split`, `CFactor.Q_prod`, `CFactor.marginal_prod` | `Identification` |
| Intervention in a block changes only that block's factor; each factor is a causal effect | `CFactor.do_marginal_factor`, `CFactor.Q_causal` | `Identification` |
| Tian's Lemma 2: factors determined by `P(O)` | `CFactor.Q_identifiable`, `CFactor.Q_step` | `Identification` |
| Tian's theorem, explicit formula; with the c-component; for sets | `CFactor.tian_identifiable`, `CFactor.tian_formula`, `CFactor.tian_identifiable_ccomp`, `CFactor.tian_identifiableX`, `CFactor.tian_identifiable_sets` | `Identification` |
| Single `x` (latents roots, `Bool`): identifiable iff no child of `x` in its c-component | `CFactor.tian_iff`, `CFactor.not_ident_of_child` | `Identification` |
| Tian's lemmas: `Σ_{T∖S} Q[T] = Q[T ∩ S]`; lemma 11 | `CFactor.Q_marg`, `CFactor.Q_ident_within` | `Identification` |
| Tian's IDENTIFY is sound | `CFactor.Reach`, `CFactor.reach_sound`, `CFactor.reach_ident` | `Identification` |
| ID soundness for sets, including line 2 | `CFactor.id_sound`, `CFactor.id_sound_anc`, `CFactor.fiber_eq` | `Identification` |
| Verma constraints; Verma's classic example | `CFactor.Q_local`, `CFactor.verma_sum`, `Verma.verma_constraint` | `Identification`, `Verma` |
| ID as a computable check: `idCheck G U X Y = true` ⇒ identifiable | `IdAlgo.idCheck_sound`, `IdAlgo.identifyTop_sound`, `IdAlgo.ccIn_eq` | `IdAlgo` |
| Test case where ID needs the recursion; `decide` on concrete graphs | `IdAudit.id_audit`, `IdAudit.tian_sets_fails`, `IdAlgo.id_audit'`, `IdAlgo.bow_idCheck` | `IdAudit`, `IdAlgo` |
| IDC: conditional effects `P(Y | do(X), Z, W)` | `Idc.idc_sound`, `Idc.IdentifiableCond`, `Idc.doModel_doModel_marginal` | `Idc` |
| `idCheck = false` ⇒ IDENTIFY stuck, and the stuck set meets `X` | `Hedge.idCheck_false_meets`, `Hedge.stuck_meets_X`, `Hedge.identifyN_false` | `Hedge` |
| `idCheck = false` ⇒ a hedge exists (Shpitser–Pearl Def. 5, set form) | `Hedge.idCheck_false_hedge`, `Hedge.IsHedge`, `Hedge.bow_hedge` | `Hedge` |
| In a hedge: a forest into the roots (one chosen child per non-root) | `Hedge.nxt`, `Hedge.hedge_nxt`, `Hedge.hedge_reaches_root`, `Hedge.hedge_rootOf` | `Hedge` |
| Decomposition (semi-graphoid) | `condIndep_single` | `Completeness` |

**Audits.** Fresh-clone audits (exact statements via `#check @`, axioms, grep for
`sorry`, `axiom`, `native_decide`, `implemented_by`) are archived in
`verification/` for tags `v1.0`, `v2.0`, `v2.2`, `v4.23`, `v4.33` and `v4.38`. Other tags
were checked by the regular build with `#print axioms` on their main results.
`verification/rule3_*.py` are the exhaustive searches described in section 7.

## 2. Plan: completeness of the ID algorithm (the hedge criterion)

**Target theorem** (Shpitser & Pearl 2006, Thm 4; Huang & Valtorta 2006). For a
graph whose latents are roots, `X`, `Y` observed and disjoint:

  `P(Y | do(X))` identifiable  ⟺  `idCheck G U X Y = true`  ⟺  no hedge for `P_X(Y)`.

As far as we know nobody has formalised the negative direction in general
(CausalSmith/Causalean's `identifyMassRec_hedge` is the failing branch of the
recursion; it does not prove non-identifiability). Check this again before
claiming it.

**H0: scope (decided).**
- Latents are roots (`hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u`), as in `tian_iff`.
- Value types: binary. Read in Shpitser & Pearl, JMLR 9 (2008), appendix, proof
  of Thm 17: the construction is binary throughout, also on the tails; merging is
  handled by independent flip noise, not by tuples. An earlier version of this
  plan recommended `Fin (2 ^ |V|)`; that is withdrawn. See the caveat under H3
  for latents.
- Final statement (H5): `idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y`.
  For `←` one `α` is enough, so the witness may choose the latent value types.

**H1: ID as a decidable function. DONE (v4.32–v4.33, `IdAlgo`).**
`ancIn`, `ccIn` (computable closures), `identifyN` (with fuel),
`identifyTop` (fuel `Fintype.card V + 1`, shown sufficient), `idCheck`,
`idCheck_sound`. `decide` works on the test graphs.

**H2: ID failure gives a hedge. DONE (v4.35–v4.36, `Hedge`).**
`idCheck_false_hedge : idCheck G U X Y = false → ∃ F F', IsHedge G U X Y F F'`,
with `F = D` (the c-component block of some `y` in `G_{X̄}[An(Y)]`) and `F' = T`
(where IDENTIFY gets stuck). `IsHedge` has the fields
`sub : F ⊆ F'`, `ne : F ≠ F'`, `rootF`/`rootF'` (every vertex of `F` resp. `F'`
reaches `R := rootsIn G F` inside itself, stated as `ancIn … = …`),
`out : F ∩ X = ∅`, `meet : F' ∩ X ≠ ∅`, `anc : R ⊆ An(Y)` in `G_{X̄}`,
`conn`/`conn'` (`CConn`: c-connected inside itself). Note: `F`, `F'` may contain
latent vertices; a latent in a c-component always has a child there.
The key insight was that a C-forest in Shpitser–Pearl is a *subgraph* (each
vertex keeps at most one child edge), so the roots need not be childless in
`G[F']`; `R := rootsIn G F` works for both.

**H3: a hedge is not identifiable on its roots. IN PROGRESS.**
Done (v4.38): `nxt` chooses one child per non-root vertex of `F'` (inside `F`
for vertices of `F`); `hedge_reaches_root`: iterating `nxt` reaches `R`.
Done (v4.39): `nxt` fixes the roots (`nxt_root`) and stays in `F` and `F'`
(`hedge_iter_memF`, `hedge_iter_mem`); one number of steps brings every vertex of `F'`
to a root (`hedge_root_uniform`); `hedge_rootOf` gives the root map `r`, constant
along `nxt`. This is the bookkeeping the parity models need.
Done (v4.40), spanning tree step 1: `sib G U F a b` (`a`, `b` in `F` with a common
latent parent in `F`); `cconn_sib`: with latents as roots, `CConn G U F` gives a chain
of siblings between any two observed vertices of `F`.
Done (v4.41), spanning tree steps 2–3: `lay` (layers by number of sibling steps from a
chosen observed `ρ`), `lay_of_chain`, and `sib_tree`: every other observed vertex of a
c-connected `F` has a sibling `par v` with strictly smaller distance `d`.
Done (v4.42), spanning tree finished: `hedge_tree` gives, for an observed `ρ ∈ F`, a
parent `par v` (a sibling in `F'`, strictly smaller `d`) for every other observed vertex
of `F'`, and for `v ∈ F` the sibling relation holds inside `F`. So the tree of `F'`
contains a spanning tree of `F` (suggested-order step 1 below is done). Done (v4.43):
`hedge_obs` (with latents as roots, `F` has an observed vertex), `sib_obs` (siblings are
observed), `hedge_spanning` (every hedge has an observed `ρ ∈ F` and such a tree).
Done (v4.44): `Channel.not_ident_of_sub` holds only for `Bool` on every vertex, which
the bit-vector latents of the caveat below need beyond; `Hedge.not_ident_of_subα` is the
same result for any value types `α`.
Done (v4.45), step 2 set up: `keepDAG G K` (the subgraph with the edges satisfying `K`),
`not_ident_keep` (not identifiable there ⇒ not identifiable in `G`, any `α`), `hedgeKeep`
(the forest edges `v → nxt v` and the tree's latent edges `u → v`, `u → par v`), and
`hedge_red_nxt`, `hedge_red_lat` (those edges are in the reduced graph). Next: the parity
models on `keepDAG G (hedgeKeep …)`, step 3 below; the latent `u` behind each tree edge
comes from `sib` (pick it with `choose`).

The construction, as read in JMLR 9 (2008), appendix, proof of Thm 17 (= Thm 4 of
the AAAI 2006 paper). Their hedge has `F' ⊆ F` with `X` only in `F`, so **the roles
are swapped relative to `IsHedge`: their `F` is our `F'`**. Both are `R`-rooted
C-forests.
1. Binary variables; each latent has exactly two observed children (in the
   forest). `M1`: every variable in the larger forest (our `F'`) is the parity of
   its parents. `M2`: the same, except the vertices of the smaller forest (our
   `F`) ignore their parents outside it. Latents are fair coins in both. Without
   intervention `R` has even parity in both models (each latent reaches `R` along
   two paths, and the bits cancel), and latents → observed is one-to-one in both,
   so the observational distributions agree. Some latent has one child among the
   ancestors of `X` in `F'` and one outside, so under `do(x)`
   `P(odd parity of R)` is 1/2 in `M1` and 0 in `M2`.
2. Positivity (`Identifiable` requires `P(O) > 0`): for each `r ∈ R` an
   independent latent flips `r` with small probability `p`. This changes the gap
   to `1/2` vs `p`-dependent, still different.
3. Larger graphs: extra edges are removed with `Channel.not_ident_of_sub`;
   vertices outside the hedge are independent uniform bits (`Completeness.liftSub`
   style, as in `BowGen`).

**Caveat for this formalisation (decide first).** Our latents are vertices that
may have more than two children, and removing edges cannot split a latent into
several. A latent with `k` children contributes its bit `k` times to the parity
of `R`. Recommended: give latents a bit-vector value type (one independent bit
per edge of the chosen latent spanning tree) and let each tree edge's two
children read their own bit. Then every "virtual latent" has exactly two
children and the paper's argument applies unchanged; observed vertices stay
`Bool`. This is allowed because the H5 statement quantifies over `α`.
Alternative: keep `Bool` and count multiplicities mod 2 (messier).

Suggested order:
1. From `CConn G U F'` extract a spanning tree of latent edges (pairs of observed
   vertices of `F'` sharing a latent parent in `F'`), such that its restriction
   to `F` is a spanning tree of `F` (grow `F`'s tree first, then extend).
2. Reduce the graph with `not_ident_of_sub` to: the `nxt` edges, the latent tree
   edges, and nothing else.
3. Define `M1`, `M2` on the reduced graph; prove `marginal O` equal via a
   bijection on latent assignments (the technique of `full_map` in the bow proof,
   no numerical sums).
4. Prove the `do(x)` difference on the parity of `R`.
5. Add the flip latents for positivity (or start with them).
Existing pieces that may be reused: `HedgeTmpl.Tm` (template with a set `X`),
`RootTree.RT`, `pth`, `parZ_φ`; their parity bookkeeping is in `ZMod 2`.
Before writing Lean, write the proof out on paper for one small hedge (e.g. the
bow and `IdAudit.idG` with an extra edge) and check it numerically if in doubt.

**H4: from the roots to `Y`.** `R ⊆ An(Y)` in `G_{X̄}`. Per the paper: the
vertices `I = An(Y) ∩ De(R)` each keep at most one child (WLOG, again by
`not_ident_of_sub`); each is the parity of its parents plus its own independent
flip with probability `p`. Then the parity of `Y` is tied to that of `R` and the
flips, and the gap from H3 survives. With disjoint tails
`Channel.rootTree_tail` already does it; the new part is tails that merge.
Prove a `Channel` lemma for a tree of tails instead of a path.

**H5: put it together.**
`id_iff : idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y` (with `hroot`,
`X ∩ U = ∅`, `X ∩ Y = ∅`). `→` is `idCheck_sound` (for every `α`). `←` is the
contrapositive: H2 gives a hedge, H3 and H4 give `¬ Identifiable` for the chosen
`α`.

**Estimate.** 8–12 rounds of the size of rounds 30–45. Highest risk: the latent
spanning tree (step 1 of H3) and merging tails (H4).

## 3. Scope and limits (what the results do not say)

- Finite DAGs, finite value types, `PMF`. No continuous variables.
- Identification results assume positivity of `P(O)` where stated; the negative
  results are for specific value types (`Bool` mostly), lifted to larger `α` only
  where stated.
- `tian_iff` and the planned `id_iff` assume latents are roots (semi-Markovian
  models). Latents with latent parents are not covered.
- Interventional (rung 2) only. Counterfactuals, probabilities of causation,
  transportability and selection bias are not formalised.
- No external expert has reviewed the definitions. Lean guarantees the proofs
  follow from the definitions; that `Identifiable`, `IsHedge`, `doModel` etc.
  mean what the literature means rests on the audits (section 1) and the test
  graphs. An expert review of `Identification.lean` lines 1–60 and
  `Hedge.IsHedge` would be the most valuable single check.

## 4. Map of the files (`PearlDoCalculus/`)

- Graph foundations: `DAG`, `Reachability`, `Walks`, `Blocking`, `DSeparation`,
  `WalkPath`, `BayesBall`, `Lauritzen`, `Counterexample` (a false lemma, kept).
- Models and d-separation: `CausalModel`, `DSepSoundSkeleton`, `DSepSound`,
  `SetSound`, `Completeness` (3 600 lines: completeness of d-separation and of
  each rule).
- Do-calculus: `DoCalculus` (`cutIn`, `doModel`, rule 1), `Rule3`, `Rule3Flag`
  (rule 3 without positivity), `DoAudit`.
- Adjustment: `SimpleConfounder*`, `MediatorAdjustment`, `BackdoorGeneral`,
  `FrontDoor*`, `Adjustment`, `AdjAudit`.
- Identification: `Identification` (8 300 lines, one namespace per round: `Bow`,
  `BowGen`, `Hedge2`, `HedgeChain`, `HedgeTmpl`, `RootTree`, `Channel`, `CFactor`,
  …), `IdAudit`, `Verma`, `IdAlgo`, `Idc`, `Hedge`.
- `EpistemicScope`: no proofs about causality; states what the project does not
  claim.
- `verification/`: audit files and outputs, Python searches for rule 3.

## 5. Workflow that worked

- One branch per piece of work; fast-forward merge to `main`; tag milestones.
- **Paper first.** Write the argument out, split it into lemmas of a few dozen
  lines, and only then write Lean. For constructions from the literature, read
  the paper; do not work from memory (the value-type mistake in H0 came from
  that).
- **Statement before proof.** Check that the statement type-checks with
  `sorry`, then fill in the proof.
- Edits are made by small Python scripts that `assert` the exact old text occurs
  once, and skip if the change is already there.
- **Release gating, strictly:** `rm -f` the build logs first; build; tag and
  push only if the *fresh* log shows `Build completed`, no `error`, no
  `declaration uses 'sorry'`. Check that the log file exists before grepping it.
  `v4.37` broke because a stale log from the previous release passed the gate.
- If edit scripts are tested against a local copy, make that copy a fresh clone
  of the current `main`; a copy that drifts from the repo makes scripts fail.
- One error at a time. To see the first goal:
  `lake build X 2>&1 | sed -n '/X.lean:[0-9]*:[0-9]*: \(unsolved\|error\)/,/^info\|^warning\|^error: Lean/p' | head -50`
- Audit tags from a fresh clone: `#check @thm`, `#print axioms`, and grep for
  `sorry`, `axiom`, `native_decide`, `implemented_by`.

## 6. Techniques and pitfalls

Techniques:
- Compare models on different graphs through their kernel factors
  (`marginal_eq_of_kfac`), never through equality of the models; this avoids
  transport between dependent types.
- Build assignments with membership proofs directly instead of `cast`.
- For zero/non-zero arguments, `Audit.marginal_eq_zero_of` and
  `Audit.marginal_ne_zero_of` reduce marginals to kernel factors.
- Observational equality by a bijection on latent assignments (`full_map`)
  rather than by computing sums.
- Fixed points of monotone set operators on a `Fintype`: `IdAlgo.iter_sub`,
  `iter_sup`, `iter_fix` (iterate `card` times).
- Proof-irrelevance: restrictions of restrictions are definitionally equal to
  direct restrictions; use `exact` or a `have` with a stated type when `rw`
  fails to see this.

Pitfalls that cost rounds:
- `Assignment` lives in `DAG.CausalModel`; `Incoming` in `PearlDoCalculus.DAG`.
- `decide` refuses goals with free variables; use named lemmas
  (`Bool.false_ne_true`). `Bool.true_ne_false` does not exist; in a closed goal
  `(by decide)` works.
- `push_neg` is deprecated in this Mathlib; use `simp only [not_forall, not_exists]`.
- Some Mathlib iff-lemmas take explicit arguments:
  `(PMF.mem_support_map_iff f p b).mp`, not `.mp` directly.
- `omit [Fintype V] in` fails ("cannot omit referenced section variable") when the
  statement uses a definition that includes the instance (e.g. `Hedge.nxt`).
  Unused-instance linter warnings are harmless; prefer leaving them to breaking
  the build.
- Names drift between Mathlib versions (`Finset.not_mem_empty` vs
  `notMem_empty`); prefer term proofs that avoid them.
- When a rewrite lemma has a set as an implicit argument and the goal has
  several marginals of the same model, give the sets explicitly
  (`(S := …) (T := …)`).
- Before `induction` on a copy of a hypothesis, `clear` the original.
- `tsum` carries a summation filter here; `rw [← tsum_fintype]` gets stuck on
  `SummationFilter.LeAtTop ?m`. Write the step as `calc` with the `tsum` stated.
- When a set such as `(T ∩ Sᶜ) \ U` occurs inside the goal, give general set
  lemmas their arguments, or `rw` may hit the inner set ("motive is not type
  correct").
- In Python heredocs with `'EOF'`, write `"\n"`, not `"\\n"`. Pasting a new block
  while `lake build` runs interrupts it.

## 7. History worth keeping

**Rule 3 (closed in v3.8 for vertices, v3.9 for sets).** `rule3_complete`
splits into: (1) `z` not an ancestor of `W` in `G_{X̄}` (`rule3_complete_nonanc`);
(2) `y`, `z` d-connected in `G_{X̄z̄}` (`rule3_complete_root`); (3) otherwise
(`rule3_complete_gap`): a chain from `y` to `z` in `G_{X̄}` with fewest colliders
(`Nat.find`), and the first `w₁ ∈ X ∪ W` that `z` reaches; minimality rules out
the bad cases via `Chain.take`, `Chain.snoc`, `Chain.cut` and `no_chain_of_dsep`,
so the chain-copy model applies (`rule3_complete_chaincopy`). Sets:
`rule3_complete_set_gap` via `set_gap_core`, one copy vertex suffices
(`rule3_complete_chaincopy_set`). Witnesses checked numerically:
`verification/rule3_chaincopy.py` (10 029 instances), `rule3_set.py` (7 312), 0
failures.

**ID algorithm line by line** (Shpitser–Pearl 2006, Fig. 3), all covered by
`id_sound_anc`: line 1 `marginal_restrict`; line 2 `S` ancestral in `G_{X̄}`;
line 3 is subsumed (vertices outside `S = An(Y)` are summed out in the intervened
model); lines 4, 6, 7 via `Q_prod`, `Q_causal`, `Q_identifiable`, `Q_marg`,
`Q_ident_within`, `Reach`; line 5 (failure) is the hedge side, section 2.

**Superseded open items.** Earlier notes listed "merging tails" and "`X` meeting
the hedge in several vertices" as separate problems for the hand-built hedge
families. The paper's construction (section 2, H3–H4) handles both; the old
families remain as special cases and as reusable parity machinery.

**Relation to other work.** CausalSmith/Causalean (github.com/Jiyuan-Tan/CausalSmith)
is broader and measure-theoretic; as far as we found (commit `a7085d8`) it has
global Markov, rule 1, restricted rules 2–3 and soundness of the recursive ID
algorithm, but not completeness of d-separation or of individual rules, and no
non-identifiability results. Our `Reach` follows the shape of its
`CFactorReachableRec`; the proofs are ours.

**Disclosure.** The proofs were developed with substantial help from Claude
(Anthropic). All proofs are checked by Lean. The author's Lean Zulip account is
deactivated, so the project has not been announced there; a draft announcement
is in the git history of this file (tag `v4.36`, section 5).

## 8. Technical debt

- Many `first | a | b | c` fallbacks were written because the exact Mathlib
  lemma form could not be checked in advance; each could be pruned.
- `Identification.lean` is about 8 300 lines; one file per namespace would be
  easier to navigate.
- Small helpers (`pure1`, `pure0`, `c2`, `pOf`/`parOf`/`parOfA`) are repeated in
  several namespaces; `full2`, `full3`, `join2` are three versions of the same
  splitting of latent assignments.
- `TwoRoot` is the case `n = 0`, `r = 1` of `RootTree` but not derived from it.
- Round 25 is superseded by round 27; only its helper lemmas remain needed.
- Several files have unused-instance linter warnings (harmless).
