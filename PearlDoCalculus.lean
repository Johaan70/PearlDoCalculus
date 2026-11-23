/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Util.ZMod2
import PearlDoCalculus.Util.PMF
import PearlDoCalculus.Util.ENNReal
import PearlDoCalculus.Util.Finset
import PearlDoCalculus.Util.Assignment
import PearlDoCalculus.Util.Marginal
import PearlDoCalculus.SimpleConfounder
import PearlDoCalculus.SimpleConfounderObservable
import PearlDoCalculus.MediatorAdjustment
import PearlDoCalculus.BackdoorGeneral
import PearlDoCalculus.FrontDoor
import PearlDoCalculus.FrontDoorObservable
import PearlDoCalculus.DAG
import PearlDoCalculus.Reachability
import PearlDoCalculus.Walks
import PearlDoCalculus.Blocking
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Soundness
import PearlDoCalculus.EpistemicScope
import PearlDoCalculus.Examples.DSeparation
import PearlDoCalculus.DoCalculus
import PearlDoCalculus.Examples.Rule2
import PearlDoCalculus.Rule3
import PearlDoCalculus.Rule3Flag
import PearlDoCalculus.Adjustment
import PearlDoCalculus.Examples.Backdoor
import PearlDoCalculus.Completeness
import PearlDoCalculus.Identification.Basic
import PearlDoCalculus.Identification.Bow
import PearlDoCalculus.Identification.HedgeChain
import PearlDoCalculus.Identification.HedgeTemplate
import PearlDoCalculus.Identification.LatentTree
import PearlDoCalculus.Identification.RootPathModels
import PearlDoCalculus.Identification.RootPath
import PearlDoCalculus.Identification.RootTree
import PearlDoCalculus.Identification.LatentSplit
import PearlDoCalculus.Identification.CFactor
import PearlDoCalculus.Identification.TianIff
import PearlDoCalculus.Identification.CFactorSets
import PearlDoCalculus.Identification.Identify
import PearlDoCalculus.Identification.IdSound
import PearlDoCalculus.Identification
import PearlDoCalculus.Verma
import PearlDoCalculus.IdAlgo
import PearlDoCalculus.Examples.IdRecursion
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
import PearlDoCalculus.Hedge

/-!
# PearlDoCalculus: Pearl's causal calculus in Lean 4

The root file. It imports every file of the project, so `import PearlDoCalculus` brings
in the whole library, and `lake build` checks all of it. The project formalises Pearl's
theory of causal identification for finite DAGs with finite value types (`PMF`-based, no
measure theory), from d-separation up to the completeness of the ID algorithm. Every main
result depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`
(`verification/AuditV480.lean`, and `verification/AuditFinal.lean` and
`verification/AxiomCheck.lean` for the final state; the modules themselves print no axioms).

## Layout, in the order of the imports

* `Util/*`: shared small facts (`ZMod 2`, `PMF`, `ENNReal` sums, `Finset`, assignments,
  marginals).
* Hand-built models on fixed small graphs, before the general theory:
  `SimpleConfounder`, `SimpleConfounderObservable`, `MediatorAdjustment` and
  `BackdoorGeneral` (back-door adjustment), `FrontDoor`, `FrontDoorObservable`
  (front-door adjustment).
* Graphs and d-separation: `DAG`, `Reachability`, `Walks`, `Blocking`, `DSeparation`;
  causal models on any DAG in `CausalModel` (imported through `Soundness`).
* Soundness of d-separation: `Soundness/*`, the layers of the Lauritzen route (with
  `Soundness/BayesBall` and `Soundness/Lauritzen`) and the assembly `Soundness/DSepSound`
  (`DSepSound.dsep_sound`); paths instead of walks in `Soundness/WalkPath`, sets in
  `Soundness/SetSound`. `Soundness/Counterexample` and `Examples/DSeparation` check the
  definitions on small graphs; `EpistemicScope` records what the library assumes rather
  than proves.
* The do-calculus: interventions and rules 1 and 2 in `DoCalculus`, rule 3 in `Rule3`
  (with positivity) and `Rule3Flag` (without), checked in `Examples/Rule2`.
* Adjustment formulas with Pearl's path criteria: `Adjustment`
  (`Adjustment.backdoor_adjustment_criterion`,
  `Adjustment.frontdoor_adjustment_criterion`), checked in `Examples/Backdoor`.
* Completeness of d-separation and of the three rules: `Completeness/*`
  (`Completeness.dsep_iff`, `Completeness.dsepSet_iff`, `Completeness.rule1_iff_set`,
  `Completeness.rule2_iff_set`, `Completeness.rule3_iff_set`).
* Identification with latent variables: `Identification/*` (the definition
  `Identification.Identifiable`, the bow and other hedge families, Tian's c-factors and
  `Identification.CFactor.tian_iff`, IDENTIFY and ID soundness), checked in `Examples/IdRecursion`;
  the Verma constraint in `Verma` (`Verma.verma_constraint`).
* The ID algorithm as a computable check: `IdAlgo` (`IdAlgo.idCheck`,
  `IdAlgo.idCheck_sound`); conditional effects in `Idc` (`Idc.idc_sound`).
* Completeness of the ID algorithm: `Hedge/*` (`Hedge.IsHedge`,
  `Hedge.idCheck_false_hedge`, `Hedge.PM.hedge_not_ident`, `Hedge.PM.hedge_not_ident_Y`,
  and the final theorem `Hedge.idCheck_iff`: with the latent variables as roots, the ID
  check says yes exactly when `P(Y | do(X))` is identifiable).

`HANDOFF.md` describes the mathematics and the history; `README.md` has the file map.
-/
