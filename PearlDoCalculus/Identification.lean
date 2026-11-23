import PearlDoCalculus.Identification.Basic
import PearlDoCalculus.Identification.Bow
import PearlDoCalculus.Identification.HedgeChain
import PearlDoCalculus.Identification.HedgeTemplate
import PearlDoCalculus.Identification.LatentTree
import PearlDoCalculus.Identification.RootPathModels
import PearlDoCalculus.Identification.RootPath
import PearlDoCalculus.Identification.RootTree
import PearlDoCalculus.Identification.CFactor
import PearlDoCalculus.Identification.TianIff
import PearlDoCalculus.Identification.CFactorSets
import PearlDoCalculus.Identification.Identify
import PearlDoCalculus.Identification.IdSound

/-!
# Identification with latent variables

This file only collects the files of the `Identification` folder, so that
`import PearlDoCalculus.Identification` brings in the whole layer. With latent vertices
`U` and observed vertices `O = Uᶜ`, `Identifiable G α O X Y` says that `P(Y | do(X))` is
the same in any two models on `G` with the same positive observed distribution. The
folder proves the positive results (back-door, front-door, Tian's theorem, the soundness
of Tian's IDENTIFY and of the ID algorithm for sets) and the first negative ones (the bow
and other hedge families are not identifiable); the general negative result, the hedge
criterion, is in `Hedge/*`. The files, in order:

1. `Basic`: the definition `Identifiable`, back-door, front-door, fully observed,
   transfer to subsets of `Y`.
2. `Bow`: the bow graph is not identifiable, alone and inside any graph.
3. `HedgeChain`, `HedgeTemplate`, `LatentTree`: hedge families (chains, the general
   template and latent paths with a tree towards `y`, latent trees with the bottom-up
   solution of a forest system).
4. `RootPathModels`, `RootPath`, `RootTree`: c-forests with many roots, root paths,
   the latent path always exists, embedded hedges.
5. `LatentSplit`, `CFactor`, `TianIff`, `CFactorSets`: the splits of an assignment of
   the latent variables (`LatentSplit`, imported through `CFactor`), Tian's
   factorization and identification theorem, `tian_iff`, sets and c-factors as causal
   effects.
6. `Identify`: `Q_marg`, Tian's lemma 11, `IdentifyDerives` and the Verma sums.
7. `IdSound`: ID soundness for sets, including line 2 (`id_sound_anc`).

## Glossary of the hedge families

Each hedge family is a structure named as its namespace (`HedgeChain`, `HedgeTemplate`,
`PathTree`, `LatentTree`, `MultiRoot`, `RootPath`, `RootTree`; the bow is the graph
`Bow.bowG`, and inside any graph the namespace `BowEmbedded`). Its main theorem is
`not_identifiable`, reached as `P.not_identifiable` (for the bow,
`Bow.bow_not_identifiable` and `BowEmbedded.bow_not_identifiable_general`). Every family
proves it the same way, with two counter-models A and B and a bijection `φ`, and uses
the same short names for the steps. Not every family has every name; the shared ones
are:

*Nodes.* `x`, `y`: the treatment and the outcome (in the forest families the outcome
is the set `Y`); `u j`: the latent nodes; `w i`: the observed nodes of a chain or path
(`HedgeChain`, `HedgeTemplate`); `nd k`: the observed nodes of a forest, with the latent
`u k` above them (`MultiRoot`, `RootPath`, `RootTree`). `Rt` and `Y` are the roots of
that forest and the set of their nodes.

*Graphs and models.*
- `gA`, `gB`, `gC`: the graphs of models A, B (and C in `RootPath`), subgraphs of `G`
  by `gA_parents_subset`, `gB_parents_subset`. Where model B needs only the edge
  `x → y`, its graph is `BowEmbedded.g1` (and `BowEmbedded.g2` has only `u → x`,
  `u → y`).
- `NA`, `NB`, `NC`: the models on these graphs; `NA_x`, `NA_y`, `NA_w`, `NA_o`, `NB_y`,
  `NB_u`, `NB_o`: their kernels at `x`, `y`, `w i`, `u j` and the other nodes (`o`).
- `mA`, `mB`: models A and B lifted to `G` (`Completeness.liftSub`).
- `A_x`, `A_y`, `A_u`, `A_w`, `A_o`, `B_x`, `B_y`, …: the kernel factors of `mA`, `mB`
  at a node, on a full assignment.
- `Bow.chan`: the noisy channel, output equal to input with probability `3/4`;
  `HedgeChain.chan_symm`: it is symmetric.

*The bijection.*
- `φ`: the bijection of full assignments, which changes only latent values (for the
  bow `U ↦ U xor Y`); `φ_u`, `φ_o`, `φ_invol`: its values and that it is an involution.
- `R`, `R5`: the remaining nodes; `mem_R`, `prod_split`: a product over all nodes split
  into the named nodes and the remaining ones.
- `joint_eq`: model B gives `φ s` the probability that model A gives `s`; `full_map`:
  so the joint distribution of model B is that of model A pushed forward along `φ`.

*The three facts.* `obsEq`: models A and B have the same observed distribution;
`posA`: that of model A is positive; `doA`: in model A, `P_x(y)` is the observed
`P(y)` of model B. In model B, `x` acts on `y` through the noisy channel `Bow.chan`,
so `P_x(y)` depends on `x` there; the two effects differ, which is `not_identifiable`.

*Configuration data.* `HedgeTemplate` holds the kernels `fx`, `fw`, `fy` of model A
and the shifts `off` that define `φ`, with the conditions `hfx` and `key` that make `φ`
work; `PathTree.toHedgeTemplate`, `LatentTree.toHedgeTemplate` and
`RootTree.toRootPath` reduce one family to another. The fields named `h…` of the
structures are the hypotheses of the configuration (its edges, the forest conditions,
and that the named nodes are different).

*Helpers.* `HedgeChain.ev s v`: the value of a full assignment `s` at `v`;
`HedgeChain.xx`, `HedgeChain.xb`: two facts about `xor`; `RootPath.Sb`: the sum of the
values at the roots, as a bit; `RootPath.c2`: the probability `1/2` of a bit.

*Other short names.* `CFactor.Q`: Tian's factor `Q[S]`; `CFactor.ccomp`: the
c-component of a node; `CFactor.IdentifyDerives`: the derivations of Tian's IDENTIFY.
-/
