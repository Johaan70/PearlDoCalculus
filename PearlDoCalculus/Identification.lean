import PearlDoCalculus.Identification.Basic
import PearlDoCalculus.Identification.Bow
import PearlDoCalculus.Identification.Hedge2
import PearlDoCalculus.Identification.HedgeChain
import PearlDoCalculus.Identification.HedgeTemplate
import PearlDoCalculus.Identification.LatentTree
import PearlDoCalculus.Identification.TwoRoot
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
`import PearlDoCalculus.Identification` brings in the whole layer. The files, in order:

1. `Basic`: the definition `Identifiable`, back-door, front-door, fully observed and
   observed parents, transfer to subsets of `Y`.
2. `Bow`: the bow graph is not identifiable, alone and inside any graph.
3. `Hedge2`, `HedgeChain`, `HedgeTemplate`, `LatentTree`: hedge families (two latent
   variables, chains, the general template, latent trees, sets `X` and `Y`).
4. `TwoRoot`, `RootPathModels`, `RootPath`, `RootTree`: c-forests with two roots, root
   paths, the latent path always exists, embedded hedges.
5. `CFactor`, `TianIff`, `CFactorSets`: Tian's factorization and identification
   theorem, `tian_iff`, sets and c-factors as causal effects.
6. `Identify`: `Q_marg`, Tian's lemma 11, `Reach` and the Verma sums.
7. `IdSound`: ID soundness for sets, including line 2 (`id_sound_anc`).
-/
