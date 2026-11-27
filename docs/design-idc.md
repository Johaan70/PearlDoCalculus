# Design note: identification of conditional effects (IDC)

*26 November 2026. Part A of an owner-approved project.*

## Goal

`Idc.idc_sound` proves one step of Shpitser and Pearl's IDC algorithm: if rule 2 lets a
set `Z` be moved from the conditioning set into the intervention, then `P(Y | do(X), Z, W)`
is identifiable whenever the unconditional effect `P(Y, X, W | do(X ∪ Z))` is. The full
IDC algorithm decides the conditional effect `P(Y | do(X), W)`:

1. Start with nothing moved, `M = ∅` and `W' = W`.
2. While some `w ∈ W'` satisfies the condition of rule 2, move it from the conditioning
   set into the intervention: `W' := W' ∖ {w}`, `M := M ∪ {w}`.
3. Answer with the ID check for the effect `P(Y ∪ W' | do(X ∪ M))`.

Part A formalizes this check, shows that it does not depend on the order of the moves,
and proves it sound, both semantically (identifiability) and syntactically (a derivation
in the do-calculus of `DoCalc/Derives`).

**Part B, the converse (identifiable implies `idcCheck = true`, the completeness of IDC),
is postponed** until the appendix of the paper has been read and its construction has
been checked by exact computation. Part B, steps 1 and 2 (reading the appendix, and the exact
check), are in the section "Part B" below.

## Definitions

All names are in the namespace `Idc`, in the new folder `PearlDoCalculus/Idc/`;
`PearlDoCalculus/Idc.lean` stays where it is.

* **The single move.** `w` is movable from the state `(M, W')` when `w ∈ W'` and
  `Y ⊥ {w} | (X ∪ M) ∪ (W' ∖ {w})` in `G` without the edges into `X ∪ M` and out of `w`:

  ```lean
  SetSound.DSeparatedSet (cutOut (cutIn G (X ∪ M)) {w}) ((X ∪ M) ∪ (W' \ {w})) Y {w}
  ```

  This is exactly the side condition `h` of the constructor `Derives.rule2` with
  `X := X ∪ M`, `Z := {w}` and `W := W' ∖ {w}`, and of `idc_sound`. A move goes from
  `(M, W')` to `(insert w M, W'.erase w)`. Reachability is the reflexive-transitive
  closure of moves, starting from `(∅, W)`.
* **The check.** `idcCheck G U X Y W : Bool` computes the moved set `M*` (below), and
  returns `idCheck G U (X ∪ M*) (Y ∪ (W ∖ M*))`.

## Design choices

1. **One round moves every movable vertex.** A `Finset` has no canonical order, so a
   loop "pick some movable `w`" is not a function. Instead, one round
   `M ↦ M ∪ {w ∈ W ∖ M | w movable from (M, W ∖ M)}` moves all currently movable vertices
   at once. This map is inflationary and stays inside `W`, so after `|W|` rounds it stands
   still (`IdAlgo.iter_fix`); the fuel is `W.card`. It is deterministic, and step 2 below
   shows that it ends in the same set as every sequential order. The state is the moved
   set `M` alone; the rest is always `W' = W ∖ M`.
2. **Decidability.** `DSeparatedSet` is a `Prop`. The project proves that d-separation
   implies Bayes-ball unreachability and moral separation (`BayesBall`, `Lauritzen`), but
   not the converse, so there is no proved decidable criterion to compute with. The round
   is therefore defined with classical decidability, and `idcCheck` is `noncomputable`.
   Small examples cannot be run by `decide`, so none are added.
3. **Monotonicity is subgraph monotonicity.** In every state reachable from `(∅, W)`,
   `W' = W ∖ M`, so the conditioning set `(X ∪ M) ∪ (W' ∖ {w})` is `X ∪ (W ∖ {w})`,
   whatever `M` is. Moving more vertices only removes edges (those into the new members
   of `M`), and d-separation survives the removal of edges (`Rule3.dsepSet_mono`). So a
   vertex that is movable stays movable after any other move. The owner asked for an
   exhaustive check on small graphs before this is proved in Lean; it is
   `verification/idc_monotone_check.py`.
4. **Soundness through expressions.** `idc_sound` goes from `Identifiable` to
   `IdentifiableCond` in one step, and `idCheck` gives `Identifiable (X ∪ M*) (Y ∪ W')`,
   not the `Y ∪ (X ∪ W')` that `idc_sound` wants. Instead of a chain of semantic
   variants of `idc_sound`, the moves are one derivation: one `Derives.rule2` step per
   move, then the chain rule, a cancellation and a marginalization give

   ```
   P(Y | W, do X)  ⊢  P(Y ∪ W' | do(X ∪ M*)) / Σ_Y P(Y ∪ W' | do(X ∪ M*))
   ```

   with no hypothesis on the latents. `derives_sound` and `idCheck_sound` then give the
   semantic soundness (step 3), and `docalc_complete` gives an expression without `do`
   for the numerator (step 4). The bridge between `eval (prob Y W X)`, a ratio at a total
   assignment, and the cross-multiplied `IdentifiableCond` is proved once and used by
   steps 3 and 5.

## The five steps and their target statements

Hypotheses as needed: `X`, `Y`, `W` observed (`⊆ Uᶜ`) and pairwise disjoint; for step 4
also `hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u`, as in `docalc_complete`.

1. `idcCheck G U X Y W : Bool`, the single move and reachability.
2. **The moved set is the unique maximal one, independent of order.** Every set reachable
   from `(∅, W)` by single moves is contained in `M*`; `M*` is reachable; no vertex is
   movable from `M*`. The key graph lemma: if `w` and `w'` are both movable from `(M, W')`,
   then `w` is still movable after moving `w'`. The owner cites Lemma 2 and Corollary 1
   of Shpitser and Pearl (UAI 2006) for this step; the numbering matches the arXiv version
   (Lemma 2 on pp. 4–5, Corollary 1 on p. 5), which states them for sets `Z ⊆ W`.
3. **Soundness.** `idcCheck G U X Y W = true → ∀ (α : V → Type) [∀ v, Nonempty (α v)],
   Idc.IdentifiableCond G α Uᶜ X Y ∅ W`, the identifiability of `P(Y | do X, W)`.
4. **Derivation.** `idcCheck G U X Y W = true → ∃ e, e.DoFree ∧ e.vars ⊆ Uᶜ ∧
   Derives G U (.prob Y W X) e`.
5. **Derivations give conditional identifiability.** `Derives G U (.prob Y W X) e →
   e.DoFree → e.vars ⊆ Uᶜ → Idc.IdentifiableCond G α Uᶜ X Y ∅ W`, for every family of
   value types, through `derives_sound` and `eval_eq_of_doFree`.

## Part B: the appendix proof of Theorem 6

*Step 1 of Part B: a summary of the proof as printed in arXiv:1206.6876, appendix,
pp. 7–8. It is written in the paper's naming, where a hedge is `F' ⊊ F` with `F` meeting
`X` and `F'` avoiding it (`Hedge.IsHedge G U X Y F F'` swaps the names). The remarks marked
**Reading** are ours.*

### The statement

Theorem 6 in the main text (p. 5): if `Z ⊆ W` is the maximal set with
`P_x(y | w) = P_{x,z}(y | w ∖ z)`, then `P_x(y | w)` is identifiable iff `P_{x,z}(y, w ∖ z)`
is. The appendix proves it in the form: *if every `W ∈ W` has a back-door path to `Y` in
`G ∖ X` given `W ∖ {W}`, then `P_x(y | w)` is identifiable iff `P_x(y, w)` is.* (This is
the statement after the moves of Part A; "every `W` has a back-door path" is "no `W` is
movable".) The "if" direction is marginalization and division. The "only if" direction:

1. **`P_x(w)` identifiable.** Then `P_x(y, w) = P_x(y | w) P_x(w)` would be identifiable
   if `P_x(y | w)` were.
2. **`P_x(w)` not identifiable.** Fix `W ∈ W` and `Y ∈ Y` with a back-door path, and a
   subgraph `p` of `G` that forms it. Fix the hedge `F' ⊊ F` for `P_{x'}(w')`, with
   `X' ⊆ X`, `W' ⊆ W`. Put `H = De(F) ∪ An(W')`. The goal is to show that
   `P_{x'}(Y | w)` is not identifiable in `H ∪ p`. *Without loss of generality:*
   (i) only the part `W'' ⊆ W` that lies in `H ∪ p` is kept; (ii) every observed node of
   `H` has at most one child; (iii) `p` starts at `H`, ends at `Y` and does not meet `H`
   otherwise, so `Y ∉ H` (the case `Y ∈ H` is handled in a base case).

**Reading.**
- The text prints `H = De(F) ∪ An(W')`; Theorem 2 (p. 3) uses `An(Y) ∩ De(F)`, and only
  the intersection makes "the models from Theorem 2 which induce `H`" fit. We read `∩`.
- "Fix such `W`" must be a `W ∈ W'`: for a `W` outside `H`, the back-door path need not
  meet `H` at all, and (iii) fails.
- "The hedge for `P_{x'}(w')`, `X' ⊆ X`, `W' ⊆ W`" uses the hedge criterion over subsets
  (Theorem 3, p. 3), whose AAAI 2006 form Shpitser (arXiv:2307.03750) shows to be false.
  In Lean, `Hedge.idCheck_false_hedge` gives a hedge for `P_x(W)` itself, so `X' = X` and
  `W' = W` can be used.
- (ii) is the same "without loss of generality" as in the hedge proof of the JMLR paper,
  the one at issue in `notes/tails-gap.md`: `H` is the tail set `I` of that note with `W'`
  in place of `Y`.

### Two lemmas

- **Lemma 4.** In a causal model, if `P(y) > 0` then for every `X` disjoint from `Y` some
  `x` has `P_x(y) > 0`. Proof: fix a value `u` of the latents with `Y(u) = y`; the model is
  deterministic given `u`; take `x = X(u)`.
- **Lemma 5.** If `F, F'` is a hedge for `P_x(y)`, then `F ⊆ F' ∪ X`. Proof: the hedge
  returned by line 5 of ID has this form. **Reading:** this holds for the hedge that ID
  returns, not for every hedge; the proof uses it only for that hedge.

### The models

`M1`, `M2` are the models of Theorem 2 on `H`: all variables binary, the latents fair
coins, and every observed node of `H` the parity (sum mod 2) of its parents; in `M2` the
nodes of `F'` disregard their parents in `F ∖ F'`. They agree on `P(H)`, and
`P1(x | Pa(X) ∖ X) > 0` (both "shown already", in the AAAI 2006 paper).

**The extension along `p`.** Binary variables are added for the nodes of `p`. Each one is
the parity of its parents if it has any, and a fair coin otherwise. A node of `H` with a
parent in `p` becomes the parity of *all* its parents, that one included. The models are
`M1*`, `M2*`. Since `M1`, `M2` agree on `P(H)` and the functions of `p` are the same in
both, the paper concludes `P1* = P2*`.

**The event.** `w''` assigns 0 to every node of `W''`. In `M1*`, `w''` is the parity of
the latents of `H` and of the parentless nodes of `p`; in `M2*` of the latents in `F'` and
the parentless nodes of `p`. Hence `P1*(w'') > 0`, `P2*(w'') > 0`, and by Lemma 4
`P1*_x(w'') > 0`, `P2*_x(w'') > 0`. It remains to show
`P1*_x(y | w'') ≠ P2*_x(y | w'')`, by induction on the structure of `p`.

### The induction

Matrices: "marginalization is written as multiplication by a matrix, summing only over
values with positive probability in the context".

**Inductive cases** (Figs. 6, 7). A node `Y'` between `H` and `Y` on `p`; if
`P_{x'}(y' | w'')` is not identifiable, neither is `P_{x'}(y | w'')`.
- *(I1) `Y'` a parent of `Y`*, neither with a descendant in `W''` (Fig. 6a):
  `P_{x'}(y | w'') = Σ_{y'} P(y | y') P_{x'}(y' | w'')`, and `P(Y | Y')` is the 2×2
  identity, so the map is one to one.
- *(I2) `Y` a parent of `Y'`*, neither with a descendant in `W''` (Fig. 6b): the next node
  of `p` is then a child of `Y'`, and the same formula and identity matrix apply.
- *(I3) a hidden common parent of `Y'` and `Y`* (Fig. 7b): "combine the previous two".
- *(I4) a common child `C` of `Y'` and `Y`, in `W''` or with a descendant in `W''`*
  (Fig. 7a): `P_{x'}(y | w'') = Σ_{y'} P(y | y', c) P_{x'}(y' | w'')`, and since all of
  `W''` is observed 0, `P(y | y', c)` is again the identity.

**Base cases** (Fig. 8). `Y` is the first node of `p` outside `H`, `Y'` the last node in
`H`.
- *(B1) `Y` a parent of `Y'`* (Fig. 8a). By Lemma 5, `Y ∉ An(F ∖ F')_H`. "By
  construction" `ΣW'' = Y + 2ΣU (mod 2)` in `M1*` and `ΣW'' = Y + 2Σ(U ∩ F')` in `M2*`
  (**Reading:** `2ΣU` is 0 mod 2; the intent seems to be that every latent is counted
  twice, once per child). With `W''` observed 0 and do(x), `Y = 0` with probability 1 in
  `M2*_x` ("by construction"). In `M1_x`, by the AAAI
  2006 paper, `Σw'' = x + ΣU' (mod 2)`, where `U'` are the latents with one child in
  `An(X)_F` and one in `F ∖ An(X)_F`; since `Y ∉ An(F ∖ F')_H`, given `w''` we get
  `Y = x + ΣU'` in `M1*_{x'}`, so `Y = 0` with probability below 1. So
  `P1*_{x'}(y | w'') ≠ P2*_{x'}(y | w'')`.
- *(B2) `Y` a child of `Y'`*. Let `G'` be `H ∪ p` without the unique outgoing arrow of `Y'`
  in `H`. If `P_{x'}(y | w'')` is not identifiable in `G'`, done (an edge subgraph). Else:
  if `Y' ∈ F` with root set `R`, removing the arrow from `F` gives c-forests with root set
  `R ∪ {Y'}`, and since `Y` is a child of `Y'` they form a hedge for `P_{x'}(y, w'')`; if
  `Y' ∈ H ∖ F`, removing it "substitutes `Y` for the `W ∈ W'' ∩ De(Y')_H`", and `F, F'`
  form a hedge for `P_{x'}(y, w'' ∖ {w})` in `G'`. Either way `P_{x'}(y, w'')` is not
  identifiable in `G'`. If `P_{x'}(w'')` is identifiable in `G'`, done (case 1). If not,
  take a smaller hedge `H' ⊂ H` for it, and the segment `p'` of `p` between `Y` and `H'`,
  and repeat the argument with `H'`, `p'`, `Y` (Fig. 8b). This also covers `Y ∈ H`: let
  `Y = Y'`.
- *(B3) a hidden common parent of `Y'` and `Y`* (Fig. 8c): combine (I1) and (B1).

### Where the proof uses parity

1. The models of Theorem 2 on `H` (every node the parity of its parents; `F'` ignoring
   `F ∖ F'`), for `P1 = P2` on `H` and for `Σw'' = x + ΣU'` in `M1_x`, both imported from
   the AAAI 2006 paper.
2. The extension along `p` (parity of the parents in `p`, fair coins at the sources, and
   the nodes of `H` reading their parents in `p`), for `P1* = P2*`.
3. The event `w'' = 0` has positive probability because `w''` is a parity of fair coins.
4. (I1)–(I3): `P(Y | Y')` is the identity because a node of `p` copies its only parent.
5. (I4): `P(y | y', c)` is the identity because `C = Y + Y'` and `C`, or its descendant in
   `W''`, is observed 0.
6. (B1): the parity identities `ΣW'' = Y + …` in `M1*` and `M2*`, and `Y = x + ΣU'`.
7. (B2) uses parity only through Theorem 2 for the new hedges; the rest is a case
   distinction on identifiability, and it gives no models.

### Points to check (step 2)

- `P1* = P2*` when `p` enters `H` at more than one node (a collider of `p` whose chain to
  `W''` runs back into `H`), and when the back-door path leaves `H` and comes back before
  its last node in `H`.
- (B2), whose recursion gives no models, and whose hedge `H'` is claimed to be smaller.
- A collider of `p` right after `Y'`: (B2) then takes `Y` := the collider, which lies in
  `W''` or has a descendant there.
- Tails of `H` that pass back through `F` (`notes/tails-gap.md`), since `H` is that
  note's tail set.
- Positivity: the models are deterministic, so the observed law is not positive, and the
  Lean `IdentifiableCond` compares only models with a positive observed law.

### Results of the exact check (step 2)

`verification/idc_checks.py` (output `verification/idc_checks_output.txt`) builds `M1*`,
`M2*` exactly as summarized above, with `H = De(F) ∩ An(W')` and the models on `H ∪ p`
only, and computes all laws exactly (fractions). It checks `P1* = P2*`,
`P*(w'' = 0) > 0` and `P*_x(w'' = 0) > 0`, and `P1*_x(y | w'' = 0) ≠ P2*_x(y | w'' = 0)`.
Graphs: one hand-made graph per case; five hedge structures (the bow, a three-node hedge,
the bow with a tail, two roots, and Example C of `notes/tails-gap.md`); and 4000 random
tries per structure. Each try attaches a segment `p` of length 1–3 at a random node `Y'`.
Its colliders are opened by a chain into a new `W`, or into `H` ("back into the hedge"),
and half the tries add an excursion that lets the back-door path leave `H` and come back
(found by enumerating the d-connected back-door paths). Results:

1. **Where `H` has no tail through `F`, the construction holds as written** in every base
   case (B1), (B3), and every inductive case. That is 9 268 random instances on the
   first four structures: in 1 246 the back-door path leaves `H` and re-enters it, in 485
   a collider chain runs back into `H`. Also the hand-made graph `r1 <- e -> r2 <-> y`,
   where the path leaves `H` at `e` and re-enters at `r2`.
2. **(B2) works after one step of its recursion, read constructively.** The direct
   extension separates the models in only 9 of the (B2) instances, and the paper does not
   claim it does.
   But in every one of the 1 206 (B2) instances on those structures, the forest without
   the outgoing arrow of `Y'` is a hedge in `G'` with root set `R ∪ {Y'}`. Its Theorem 2
   models, extended along the rest of `p`, agree on the observed law and differ on
   `P_x(y | w'' = 0)`. The branch "a smaller hedge `H' ⊂ H`" was never needed.
3. **A collider right after `Y'` is not covered as written** (section 5:
   `w <- a -> q1 <- y`, `q1 ∈ W`). (B2) takes `Y := q1`, which is observed, and the hedge it
   yields in `G'` is not smaller than `H`. The constructive reading of 2. still works
   there, and so does Theorem 6 (section 6).
4. **The construction fails on Example C**, the tail of `H` that passes back through `F`.
   In all 2 252 (B1)/(B3) instances on that structure, the Theorem 2 models on `H` already
   disagree on the observed law, because `w` reads its parent `r`. With only the forest
   edges they agree, but do not differ on `P_x(y | z)` (section 3). This is the gap of
   `notes/tails-gap.md`, inherited through "the models from Theorem 2 which induce `H`".
   Theorem 6 itself holds on that graph: positive linear parity models with noise
   separate `P_x(y | z)` (section 6).
5. **Positivity.** None of the models of the construction has a positive observed law.
   Positive pairs exist on the graphs tested in section 6, but they had to be found by
   search; the paper gives no recipe for them.

So Theorem 6 stands on every graph tested. Its printed proof needs three repairs: the
models of Theorem 2 on `H` must be replaced by the repaired hedge models
(`Hedge/ParityModels` onwards, the product construction of `notes/tails-gap.md`); (B2)
needs the constructive reading of 2., including the collider case of 3.; and positive
models are needed for `IdentifiableCond`. A Lean proof of Part B can probably avoid the
induction on `p`: start from the positive bit-vector countermodels that `Hedge` already
builds for `P_x(Y ∪ W)`, and carry them over to the conditional. That route has not been
checked.

## References

- I. Shpitser and J. Pearl, *Identification of Conditional Interventional
  Distributions*, UAI 2006; arXiv:1206.6876 (8 pages, the version read for Part B). The
  IDC algorithm (Fig. 3); Lemma 2 and Corollary 1 (step 2); Theorem 6 and its proof in the
  appendix (pp. 7–8).
- I. Shpitser and J. Pearl, *Complete Identification Methods for the Causal Hierarchy*,
  JMLR 9 (2008).
- PearlDoCalculus: `Idc.idc_sound`, `Idc.IdentifiableCond`, `IdAlgo.idCheck`,
  `IdAlgo.idCheck_sound`, `Hedge.idCheck_iff`, `DoCalc.Derives`, `DoCalc.derives_sound`,
  `DoCalc.docalc_complete`; `docs/design-docalc-completeness.md`.

## Progress:

- Unit 0: this design note (v4.243).
- Unit 1: the single moves `Movable`, `Move`, `Reachable`, the round `moveRound`, the
  moved set `movedSet` and the check `idcCheck`, classical and `noncomputable`
  (`Idc/Check`, v4.244).
- Unit 2: the order of the moves does not matter. The exhaustive search
  `verification/idc_monotone_check.py` (all DAGs up to 5 vertices with all disjoint roles
  exhaustively, 100 000 random instances each on 6 and 7 vertices) found no
  counterexample; then `Movable.after_move`, `movable_mono`,
  `Reachable.subset_movedSet`, `reachable_movedSet`, `not_movable_movedSet`
  (`Idc/Maximal`, v4.245).
- Unit 3: soundness, `idcCheck_sound`, with no hypothesis on the latents and for every
  family of value types. Not by iterating `idc_sound`, but through the expressions of
  design choice 4 (`derives_of_reachable`, `derives_ratio`, `derives_frame`), with
  `idCheck_sound`, `derives_sound` and the bridge `identifiableCond_of_eval`; not as a
  corollary of units 4 and 5 (`Idc/Sound`, v4.246).
- Unit 4: the check gives a derivation, `idcCheck_derives`: the frame, with
  `docalc_complete` substituted in the numerator and under the sum by congruence; the
  case `W' = ∅` needs no special treatment (`Idc/Derivation`, v4.247).
- Unit 5: a derivation gives conditional identifiability, `identifiableCond_of_derives`,
  for every family of value types and with no hypothesis on the latents; with the
  optional `idcCheck_derives_identifiableCond`, which collects units 4 and 5
  (`Idc/Derivation`, v4.248). Part A is done.
- Audit: `verification/AuditIdc.lean`, run from a fresh clone of v4.248, output
  `verification/audit_idc_output.txt` (v4.249).
- Part B, step 1: the summary of the appendix proof of Theorem 6, section "Part B"
  (v4.250). The text was extracted from arXiv:1206.6876 with `pypdf` (poppler-utils
  could not be installed without a password) and read in full.
- Part B, step 2: the exact check `verification/idc_checks.py`, output
  `verification/idc_checks_output.txt`, and the results above (v4.251).
