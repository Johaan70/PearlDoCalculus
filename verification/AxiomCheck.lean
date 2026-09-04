/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Aksiomsjekk: verifiserer at hovedresultatene bare hviler på Mathlibs tre
standardaksiomer, uten `sorryAx`.

Kjør med: lake env lean verification/AxiomCheck.lean
-/
import PearlDoCalculus

#print axioms PearlDoCalculus.backdoor_general
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_structural
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_X_cancellation
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_adjustment_observable
#print axioms PearlDoCalculus.moral_walk_of_open
#print axioms PearlDoCalculus.dsep_of_moral_sep
#print axioms PearlDoCalculus.condIndep_of_product_form
#print axioms PearlDoCalculus.jointUpTo_factorizes
