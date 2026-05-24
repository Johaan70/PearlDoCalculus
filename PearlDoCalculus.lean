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

/-!
# Pearls do-kalkyle i Lean 4 (hovedmodul)

Toppnivå-import. Hvis denne filen kompilerer uten feil, er alle milepæler
til og med trinn 4a av back-door verifisert.
-/
