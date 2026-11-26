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
been checked by exact computation.

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
   of Shpitser and Pearl (UAI 2006) for this step; the numbering is as cited by the owner
   and has not been checked against the paper here.
3. **Soundness.** `idcCheck G U X Y W = true → ∀ (α : V → Type) [∀ v, Nonempty (α v)],
   Idc.IdentifiableCond G α Uᶜ X Y ∅ W`, the identifiability of `P(Y | do X, W)`.
4. **Derivation.** `idcCheck G U X Y W = true → ∃ e, e.DoFree ∧ e.vars ⊆ Uᶜ ∧
   Derives G U (.prob Y W X) e`.
5. **Derivations give conditional identifiability.** `Derives G U (.prob Y W X) e →
   e.DoFree → e.vars ⊆ Uᶜ → Idc.IdentifiableCond G α Uᶜ X Y ∅ W`, for every family of
   value types, through `derives_sound` and `eval_eq_of_doFree`.

## References

- I. Shpitser and J. Pearl, *Identification of Conditional Interventional
  Distributions*, UAI 2006. The IDC algorithm. Lemma 2 and Corollary 1 as cited by the
  owner for step 2 (numbering not checked here).
- I. Shpitser and J. Pearl, *Complete Identification Methods for the Causal Hierarchy*,
  JMLR 9 (2008).
- PearlDoCalculus: `Idc.idc_sound`, `Idc.IdentifiableCond`, `IdAlgo.idCheck`,
  `IdAlgo.idCheck_sound`, `Hedge.idCheck_iff`, `DoCalc.Derives`, `DoCalc.derives_sound`,
  `DoCalc.docalc_complete`; `docs/design-docalc-completeness.md`.

## Progress:

- Unit 0: this design note (v4.243).
