/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Axiom check: verifies that the main results rest only on Mathlib's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`), without `sorryAx`.

Run with: lake env lean verification/AxiomCheck.lean
-/
import PearlDoCalculus

#print axioms PearlDoCalculus.backdoor_general
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_structural
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_X_cancellation
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_adjustment_observable
#print axioms PearlDoCalculus.condIndep_of_product_form
#print axioms PearlDoCalculus.jointUpTo_factorizes
#print axioms PearlDoCalculus.joint_splits
