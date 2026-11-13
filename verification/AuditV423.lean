/-
Revisjon av tag v4.23 fra en fersk klon: definisjonene og de eksakte utsagnene for
identifikasjonslaget (`#print`, `#check @`) og aksiomene bak hovedresultatene.

Kjør med: lake env lean verification/AuditV423.lean
-/
import PearlDoCalculus.Identification

-- Definisjonene utsagnene hviler på
#print Identification.Identifiable
#print Identification.CFactor.fill
#print Identification.CFactor.Q
#print Identification.CFactor.IsClosedBlock
#print Identification.CFactor.latStep
#print Identification.CFactor.ccomp

-- Den negative siden
#check @Identification.RootTree.embedded_not_identifiable
#check @Identification.Channel.path_not_identifiable
#check @Identification.CFactor.not_ident_of_child

-- Den positive siden
#check @Identification.CFactor.marginal_factor
#check @Identification.CFactor.Q_identifiable
#check @Identification.CFactor.Q_step
#check @Identification.CFactor.tian_formula
#check @Identification.CFactor.tian_identifiable_ccomp
#check @Identification.CFactor.ccomp_isLeast
#check @Identification.CFactor.marginal_prod
#check @Identification.CFactor.tian_formula_blocks
#check @Identification.CFactor.tian_identifiable_sets
#check @Identification.CFactor.Q_causal

-- Skillelinjen for én x
#check @Identification.CFactor.tian_iff

#print axioms Identification.RootTree.embedded_not_identifiable
#print axioms Identification.Channel.path_not_identifiable
#print axioms Identification.CFactor.not_ident_of_child
#print axioms Identification.CFactor.Q_identifiable
#print axioms Identification.CFactor.tian_formula
#print axioms Identification.CFactor.ccomp_isLeast
#print axioms Identification.CFactor.tian_formula_blocks
#print axioms Identification.CFactor.tian_identifiable_sets
#print axioms Identification.CFactor.Q_causal
#print axioms Identification.CFactor.tian_iff
