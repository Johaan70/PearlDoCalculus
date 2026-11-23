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

## Glossary

The proof uses short names. They are the notation of the proof plan in `HANDOFF.md`
section 2, so they are kept, and this glossary explains them. Graph-side names are in
namespace `Hedge`, the parity models and everything built on them in `Hedge.PM`
("parity models"). The prose writes `M1` for `PM.M … false` and `M2` for `PM.M … true`,
ψ for `psiS` and τ for `tauS`. In a hedge `F ⊊ F'`, `F` is the smaller set.

*Hedges and trees* (`Hedge`).
- `rootsIn G F`: the nodes of `F` with no child inside `F` (`Hedge/Defs`).
- `CConn`, `IsHedge`: `F` is c-connected inside itself; the hedge `F ⊊ F'` for
  `P_X(Y)` (`Hedge/Defs`).
- `Stuck`: IDENTIFY is stuck at a set `T` with target `C` (`Hedge/FromID`).
- `nxt G F F' v`: the chosen child of `v`, inside `F` for nodes of `F`, otherwise inside
  `F'`; `v` itself if there is none, as for the roots (`Hedge/Tree`).
- `ParTree S ρ par d`: a tree on `S` with root `ρ`, parent pointer `par` and a
  distance `d` that decreases towards the root (`Hedge/Tree`).
- `inc S ρ par c w`: the incidence value at `w` in `ZMod 2`, the bit `c` on the edge
  above `w` plus the bits on the edges to its children; an edge is indexed by its lower
  node (`Hedge/Tree`).
- `nreach G X F F' s w`, `nrI`: `w` is reached from `s` along `nxt` without meeting `X`,
  and its indicator in `ZMod 2` (`Hedge/DoGapM1`).
- `AY G X Y`: the ancestors of `Y` in `G_{X̄}`; `tp`: the tail pointer, a chosen child
  in `AY` towards `Y`; `tI s w`: the indicator that `w` lies on the tail from `s`
  (`Hedge/Tails`).

*Values and construction data* (`Hedge.PM`, `Hedge/ParityModels`).
- `kk U v`: the number of bits of a node, `|V|` if latent, `1` if observed;
  `Val U v`: the value type, `kk U v` bits.
- `rd x i`: bit `i` of a value; `ix c`: the index of the bit, inside a latent value,
  of the tree edge with lower node `c`; `cst U v b`: the value with every bit `b`.
- `noise`: the bit that is `1` with probability `1/4`.
- `Data`: the root `ρ` of the tree, the parent pointer `par`, the latent `lat c` behind
  the tree edge `(c, par c)`, and the observed root `r0` that carries the noise;
  `Good`: the conditions on this data.
- `scope v`: the children that `v` counts (in `M2` a node of `F` counts only children in
  `F`); `CH v`: its tree children; `NX v`: its `nxt` children.
- `sb v g`: the bit of an observed node `v`, its own tree bit plus the tree bits of its
  children `CH` plus the values of its `nxt` children `NX` (within `scope`), with the
  parents read through `g`.
- `M`: the parity model. An observed node of `F'` takes the value `sb`, `r0` adds
  `noise`, and all other nodes are uniform.
- `lb s c`, `ov s w`, `sbV s v`: read from a full assignment `s`: the bit on the tree
  edge `(c, par c)`, the value of an observed node, and `sb`.

*Equal observed distributions* (`Hedge/ObsEq`).
- `δ s v`: the defect at `v`, the terms `M1` has and `M2` does not.
- `EF`: the tree edges in `F`; `OF`: the observed nodes of `F`; `incF`: the incidence
  in the `F`-tree.
- `sh t s`: shift the `F`-tree bits of `s` by `t`; `tsel τ`: a shift that solves
  `incF t = τ` on `OF` when one exists; `phiS`: the involution, `sh` by the solution
  for `δ s`.

*The do-gap* (`Hedge/DoGapM1`, `Hedge/DoGapM2`, `Hedge/Roots`).
- `phiC c w`: whether ψ flips the value at `w`; `psiS c s`: ψ, which flips the bit on
  `(c, par c)` and those values.
- `parR s`: the parity of the observed roots of `F`.
- `tauS s`: τ, which flips the value at `r0`; `gS s`: the noise term at `r0` in `M2`.
- `RO`: the observed roots of `F`.

*The product models* (`Hedge/Product`, `Hedge/ProductBias`).
- `Val2 U`: a parity-model value and a tail bit `b`; `fstA s`: the first coordinates.
- `TC v`: the tail parents of `v`; `bIn`: the input to the tail bit at `v`;
  `etaS s v` (η_v in the prose): the noise term at `v`, `b_v` minus its input.
- `MP … two`: the product model, `M1` (`two = false`) or `M2` (`two = true`) in the first
  coordinate and the tail bits in the second.
- `betaC c w`: where ψ flips `b`; `psi2 c s`: ψ on the product models.
- `Yb s`: the parity of the tail bits over `Y`.
- `AO`, `AXo`: the observed nodes of `AY` outside and inside `X`.
- `sig v s`: flip `b` along the tail from `v`; `tau2 s`: flip the value at `r0` and `b`
  along the tail from `r0`; `fS S s`: the function `Yb + gS + Σ_{v ∈ S} η_v` of the
  induction.
-/
