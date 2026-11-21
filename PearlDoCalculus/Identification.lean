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
6. `Identify`: `Q_marg`, Tian's lemma 11, `Reach` and the Verma sums.
7. `IdSound`: ID soundness for sets, including line 2 (`id_sound_anc`).
-/
