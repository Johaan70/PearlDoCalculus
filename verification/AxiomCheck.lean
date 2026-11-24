/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Axiom check: verifies that the main results rest only on Mathlib's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`), without `sorryAx`.

Together with `verification/AuditFinal.lean` (the public results of `docs/history/CLEANUP.md`) it
covers every declaration named in the results table of `HANDOFF.md`, section 1, and the
three public definitions. Since v4.213 the modules themselves contain no `#print axioms`
lines; these two files are where the axioms are checked.

Run with: lake env lean verification/AxiomCheck.lean
-/
import PearlDoCalculus

/-! ## Lemmas of the soundness and adjustment layers -/

#print axioms PearlDoCalculus.backdoor_general
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_structural
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_X_cancellation
#print axioms PearlDoCalculus.FrontDoorModel.frontdoor_adjustment_observable
#print axioms PearlDoCalculus.condIndep_of_product_form
#print axioms PearlDoCalculus.jointUpTo_factorizes
#print axioms PearlDoCalculus.joint_splits

/-! ## The public definitions (their statements are checked by `AuditFinal.lean`) -/

#print axioms Identification.Identifiable
#print axioms IdAlgo.idCheck
#print axioms Hedge.IsHedge

/-! ## The results table of `HANDOFF.md`, section 1, in its order

The entries that `AuditFinal.lean` already checks are not repeated. -/

#print axioms DSepSound.dsep_sound
#print axioms WalkPath.dsep_sound_path
#print axioms SetSound.dsep_sound_set
#print axioms Completeness.dsep_complete
#print axioms Completeness.dsepPath_iff
#print axioms DoCalculus.rule1
#print axioms DoCalculus.rule2
#print axioms Rule3Flag.rule3_general
#print axioms Completeness.rule1_iff
#print axioms Completeness.rule2_iff
#print axioms Completeness.rule3_iff
#print axioms Completeness.rule3_iff_nonanc
#print axioms Completeness.rule3_complete_root
#print axioms Completeness.rule3_complete_chaincopy
#print axioms Completeness.rule3_complete_set
#print axioms Identification.backdoor_identifiable
#print axioms Identification.frontdoor_identifiable
#print axioms Identification.observed_identifiable
#print axioms Identification.Bow.bow_not_identifiable
#print axioms Identification.BowEmbedded.bow_not_identifiable_general
#print axioms Identification.HedgeChain.not_identifiable
#print axioms Identification.HedgeTemplate.not_identifiable
#print axioms Identification.PathTree.not_identifiable
#print axioms Identification.LatentTree.not_identifiable
#print axioms Identification.MultiRoot.not_identifiable
#print axioms Identification.RootPath.not_identifiable
#print axioms Identification.RootTree.not_identifiable
#print axioms Identification.RootTree.embedded_not_identifiable
#print axioms Identification.Identifiable.mono_Y
#print axioms Identification.not_identifiable_of_mem
#print axioms Identification.CFactor.marginal_factor
#print axioms Identification.CFactor.Q_split
#print axioms Identification.CFactor.Q_prod
#print axioms Identification.CFactor.marginal_prod
#print axioms Identification.CFactor.do_marginal_factor
#print axioms Identification.CFactor.Q_causal
#print axioms Identification.CFactor.Q_identifiable
#print axioms Identification.CFactor.Q_step
#print axioms Identification.CFactor.tian_identifiable
#print axioms Identification.CFactor.tian_formula
#print axioms Identification.CFactor.tian_identifiable_ccomp
#print axioms Identification.CFactor.tian_identifiable_set_of_closed
#print axioms Identification.CFactor.tian_identifiable_sets
#print axioms Identification.CFactor.not_ident_of_child
#print axioms Identification.CFactor.Q_marg
#print axioms Identification.CFactor.Q_ident_within
#print axioms Identification.CFactor.IdentifyDerives
#print axioms Identification.CFactor.identifyDerives_sound
#print axioms Identification.CFactor.identifyDerives_ident
#print axioms Identification.CFactor.id_sound
#print axioms Identification.CFactor.id_sound_anc
#print axioms Identification.CFactor.fiber_eq
#print axioms Identification.CFactor.Q_local
#print axioms Identification.CFactor.verma_sum
#print axioms IdAlgo.identifyTop_sound
#print axioms IdAlgo.ccIn_eq
#print axioms Examples.IdRecursion.idG_identifiable
#print axioms Examples.IdRecursion.idG_not_tian_sets
#print axioms IdAlgo.idG_identifiable_of_idCheck
#print axioms IdAlgo.bow_idCheck
#print axioms Idc.IdentifiableCond
#print axioms Idc.doModel_doModel_marginal
#print axioms Hedge.idCheck_false_meets
#print axioms Hedge.stuck_meets_X
#print axioms Hedge.identifyN_false
#print axioms Hedge.bow_hedge
#print axioms Hedge.nxt
#print axioms Hedge.hedge_nxt
#print axioms Hedge.hedge_reaches_root
#print axioms Hedge.hedge_rootOf
#print axioms Completeness.condIndep_single
