import PearlDoCalculus.Idc
import PearlDoCalculus.Hedge.Defs
import PearlDoCalculus.Hedge.FromID
import PearlDoCalculus.Hedge.Tree
import PearlDoCalculus.Hedge.ParityModels
import PearlDoCalculus.Hedge.ObsEq
import PearlDoCalculus.Hedge.Positivity
import PearlDoCalculus.Hedge.DoGapM1
import PearlDoCalculus.Hedge.DoGapM2
import PearlDoCalculus.Hedge.Roots
import PearlDoCalculus.Hedge.Tails
import PearlDoCalculus.Hedge.Product
import PearlDoCalculus.Hedge.ProductBias
import PearlDoCalculus.Hedge.Complete

/-!
# Completeness of the ID algorithm: the `Hedge` library

This file only collects the files of the `Hedge` folder, so that
`import PearlDoCalculus.Hedge` brings in the whole proof of the completeness theorem
`Hedge.idCheck_iff`: with the latent nodes as roots, `X` and `Y` observed and
`X ∩ Y = ∅`, the ID check says yes exactly when `P(Y | do(X))` is identifiable. The files,
in order:

1. `Hedge/Defs`: the definitions `rootsIn`, `CConn` and `IsHedge`.
2. `Hedge/FromID` (H2): a failing ID check gives a hedge (`idCheck_false_hedge`).
3. `Hedge/Tree`: the forest `nxt` into the roots of a hedge, its spanning tree
   (`hedge_spanning`), and incidence on trees (`ParTree`, `inc_inj`, `inc_surj`).
4. `Hedge/ParityModels`: the parity models `M1`, `M2` on a hedge and their kernel
   factors (`PM.M`, `PM.Good`, `PM.sb_read`).
5. `Hedge/ObsEq`: `M1` and `M2` have the same observed distribution (`PM.marg_eq`).
6. `Hedge/Positivity`: that distribution is positive (`PM.pos_M1`).
7. `Hedge/DoGapM1`: under `do(x)` the root parity is a fair coin in `M1`
   (`PM.parR_half`).
8. `Hedge/DoGapM2`: under `do(x)` the root parity is biased `3 : 1` in `M2`
   (`PM.cross_edge`, `PM.parR_three`).
9. `Hedge/Roots` (H3): every hedge blocks identification at its observed roots
   (`PM.hedge_not_ident`).
10. `Hedge/Tails` (H4): the tail pointer `tp` from the roots to `Y`, and the indicators
    `tI`.
11. `Hedge/Product` (H4): the product models `PM.MP`, their equal positive observed
    distribution, and a fair parity `Yb` on `Y` in `MP false` (`PM.Yb_half`).
12. `Hedge/ProductBias` (H4): `Yb` is biased in `MP true` (`PM.Yb_biased`).
13. `Hedge/Complete` (H4, H5): every hedge blocks identification at `Y`
    (`PM.hedge_not_ident_Y`), and completeness, `idCheck_iff`.
-/
