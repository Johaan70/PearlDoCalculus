/-
The exact statements of the public results and definitions. `scripts/check.sh` runs this
file and compares the output with `verification/public_statements.txt`, frozen at v4.85.
A cleanup step may not change any line of that output.
-/
import PearlDoCalculus

set_option pp.fullNames true

#print Identification.Identifiable
#print IdAlgo.idCheck
#print Hedge.IsHedge

#check @Hedge.idCheck_iff
#check @IdAlgo.idCheck_sound
#check @Hedge.idCheck_false_hedge
#check @Hedge.PM.hedge_not_ident
#check @Hedge.PM.hedge_not_ident_Y
#check @Idc.idc_sound
#check @Completeness.dsep_iff
#check @Completeness.dsepSet_iff
#check @Completeness.rule1_iff_set
#check @Completeness.rule2_iff_set
#check @Completeness.rule3_iff_set
#check @Adjustment.backdoor_adjustment_criterion
#check @Adjustment.frontdoor_adjustment_criterion
#check @Identification.CFactor.tian_iff
#check @Verma.verma_constraint
