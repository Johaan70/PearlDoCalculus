/-
Revisjon av tag v4.38 fra en fersk klon: definisjonene og de eksakte utsagnene for
IDC og hedge-laget (runde 39–45), hovedresultatene fra tidligere lag, og aksiomene
bak dem.

Kjør med: lake env lean verification/AuditV438.lean
-/
import PearlDoCalculus

-- Definisjonene utsagnene hviler på
#print Identification.Identifiable
#print IdAlgo.idCheck
#print Idc.IdentifiableCond
#print Hedge.Stuck
#print Hedge.rootsIn
#print Hedge.CConn
#print Hedge.IsHedge
#print Hedge.nxt

-- IDC (runde 39–40)
#check @Idc.idc_sound

-- Hedge (runde 41–45)
#check @Hedge.idCheck_false_meets
#check @Hedge.idCheck_false_hedge
#check @Hedge.bow_hedge
#check @Hedge.hedge_nxt
#check @Hedge.hedge_reaches_root

-- Hovedresultater fra tidligere lag
#check @Completeness.dsepSet_iff
#check @Completeness.rule1_iff_set
#check @Completeness.rule2_iff_set
#check @Completeness.rule3_iff_set
#check @IdAlgo.idCheck_sound

#print axioms Idc.idc_sound
#print axioms Hedge.idCheck_false_meets
#print axioms Hedge.idCheck_false_hedge
#print axioms Hedge.bow_hedge
#print axioms Hedge.hedge_nxt
#print axioms Hedge.hedge_reaches_root
#print axioms Completeness.dsep_iff
#print axioms Completeness.dsepSet_iff
#print axioms Completeness.rule1_iff_set
#print axioms Completeness.rule2_iff_set
#print axioms Completeness.rule3_iff_set
#print axioms Adjustment.backdoor_adjustment_criterion
#print axioms Adjustment.frontdoor_adjustment_criterion
#print axioms Identification.CFactor.tian_iff
#print axioms Identification.CFactor.id_sound_anc
#print axioms IdAlgo.idCheck_sound
#print axioms Verma.verma_constraint
#print axioms Identification.RootTree.embedded_not_identifiable
