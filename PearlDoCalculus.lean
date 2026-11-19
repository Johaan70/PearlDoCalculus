/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
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
import PearlDoCalculus.DSepSoundSkeleton
import PearlDoCalculus.EpistemicScope
import PearlDoCalculus.Counterexample
import PearlDoCalculus.BayesBall
import PearlDoCalculus.Lauritzen
import PearlDoCalculus.DSepSound
import PearlDoCalculus.Audit
import PearlDoCalculus.WalkPath
import PearlDoCalculus.SetSound
import PearlDoCalculus.DoCalculus
import PearlDoCalculus.DoAudit
import PearlDoCalculus.Rule3
import PearlDoCalculus.Rule3Flag
import PearlDoCalculus.Adjustment
import PearlDoCalculus.AdjAudit
import PearlDoCalculus.Completeness
import PearlDoCalculus.Identification.Basic
import PearlDoCalculus.Identification.Bow
import PearlDoCalculus.Identification.Hedge2
import PearlDoCalculus.Identification.HedgeChain
import PearlDoCalculus.Identification.HedgeTemplate
import PearlDoCalculus.Identification.LatentTree
import PearlDoCalculus.Identification.RootPathModels
import PearlDoCalculus.Identification.RootPath
import PearlDoCalculus.Identification.RootTree
import PearlDoCalculus.Identification.TwoRoot
import PearlDoCalculus.Identification
import PearlDoCalculus.IdAudit
import PearlDoCalculus.Verma
import PearlDoCalculus.IdAlgo
import PearlDoCalculus.Idc
import PearlDoCalculus.Hedge.Defs
import PearlDoCalculus.Hedge.FromID
import PearlDoCalculus.Hedge.Tree
import PearlDoCalculus.Hedge.Reduce
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
# Pearls do-kalkyle i Lean 4 (hovedmodul)

Toppnivå-import. Hvis denne filen kompilerer uten feil, er alle milepæler
til og med trinn 4a av back-door verifisert.
-/
