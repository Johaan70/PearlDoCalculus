/-
Revisjon av tag v4.80 fra en fersk klon: definisjonene og de eksakte utsagnene for
fullstendigheten av ID-algoritmen (H1–H5), en fornuftssjekk på buen, hovedresultatene fra
tidligere lag, og aksiomene bak dem.

Kjør med: lake env lean verification/AuditV480.lean
-/
import PearlDoCalculus

-- Definisjonene utsagnene hviler på
#print Identification.Identifiable
#print IdAlgo.idCheck
#print Hedge.IsHedge
#print Hedge.CConn
#print Hedge.rootsIn

-- Fullstendigheten (H2–H5)
#check @Hedge.idCheck_iff
#check @Hedge.idCheck_false_hedge
#check @Hedge.PM.hedge_not_ident
#check @Hedge.PM.hedge_not_ident_Y
#check @IdAlgo.idCheck_sound

-- Fornuftssjekk: med `idCheck_iff` er buen `x → y`, `x ↔ y` ikke identifiserbar for alle
-- verdityper (fordi `idCheck` sier nei).
example : ¬ ∀ (α : Fin 3 → Type) [∀ v, Nonempty (α v)],
    Identification.Identifiable Identification.Bow.bowG α ({0} : Finset (Fin 3))ᶜ {1} {2} := by
  intro h
  have h1 := (Hedge.idCheck_iff Identification.Bow.bowG {0} {1} {2}
    (by decide) (by decide) (by decide) (by decide)).mpr h
  rw [IdAlgo.bow_idCheck] at h1
  exact Bool.false_ne_true h1

-- Hovedresultater fra tidligere lag
#check @Completeness.dsepSet_iff
#check @Completeness.rule1_iff_set
#check @Completeness.rule2_iff_set
#check @Completeness.rule3_iff_set

#print axioms Hedge.idCheck_iff
#print axioms Hedge.idCheck_false_hedge
#print axioms Hedge.PM.hedge_not_ident
#print axioms Hedge.PM.hedge_not_ident_Y
#print axioms IdAlgo.idCheck_sound
#print axioms Idc.idc_sound
#print axioms Completeness.dsep_iff
#print axioms Completeness.dsepSet_iff
#print axioms Completeness.rule1_iff_set
#print axioms Completeness.rule2_iff_set
#print axioms Completeness.rule3_iff_set
#print axioms Adjustment.backdoor_adjustment_criterion
#print axioms Adjustment.frontdoor_adjustment_criterion
#print axioms Identification.CFactor.tian_iff
#print axioms Verma.verma_constraint
