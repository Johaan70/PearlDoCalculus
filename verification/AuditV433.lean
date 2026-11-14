/-
Revisjon av tag v4.33 fra en fersk klon: definisjonene og de eksakte utsagnene for
ID-laget (runde 30–38), Verma-begrensningen og testeksemplene, og aksiomene bak dem.

Kjør med: lake env lean verification/AuditV433.lean
-/
import PearlDoCalculus

-- Definisjonene utsagnene hviler på
#print Identification.Identifiable
#print Identification.CFactor.Q
#print Identification.CFactor.IsLatClosed
#print Identification.CFactor.Reach
#print IdAlgo.ancIn
#print IdAlgo.ccIn
#print IdAlgo.identifyN
#print IdAlgo.identifyTop
#print IdAlgo.idCheck

-- Byggesteinene (runde 30–31)
#check @Identification.CFactor.Q_marg
#check @Identification.CFactor.Q_ident_within

-- IDENTIFY og ID-sunnhet (runde 32–34)
#check @Identification.CFactor.reach_ident
#check @Identification.CFactor.id_sound
#check @Identification.CFactor.id_sound_anc
#check @Identification.CFactor.fiber_eq

-- Verma (runde 36)
#check @Identification.CFactor.verma_sum
#check @Verma.verma_constraint

-- ID som beregnbar sjekk (runde 37–38)
#check @IdAlgo.identifyTop_sound
#check @IdAlgo.ccIn_eq
#check @IdAlgo.idCheck_sound

-- Testeksemplene
#check @IdAudit.tian_sets_fails
#check @IdAudit.id_audit
#check @IdAlgo.id_audit'
#check @IdAlgo.bow_idCheck

#print axioms Identification.CFactor.Q_marg
#print axioms Identification.CFactor.Q_ident_within
#print axioms Identification.CFactor.reach_ident
#print axioms Identification.CFactor.id_sound
#print axioms Identification.CFactor.id_sound_anc
#print axioms Identification.CFactor.verma_sum
#print axioms Verma.verma_constraint
#print axioms IdAlgo.identifyTop_sound
#print axioms IdAlgo.ccIn_eq
#print axioms IdAlgo.idCheck_sound
#print axioms IdAudit.tian_sets_fails
#print axioms IdAudit.id_audit
#print axioms IdAlgo.id_audit'
#print axioms IdAlgo.bow_idCheck
#print axioms Identification.CFactor.tian_iff
#print axioms Identification.RootTree.embedded_not_identifiable
