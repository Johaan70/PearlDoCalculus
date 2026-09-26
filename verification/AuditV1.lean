import PearlDoCalculus

-- 1. Nøyaktig statement, med alle implisitte argumenter og instanser
#check @DSepSound.dsep_sound

-- 2. Definisjonene teoremet hviler på
#print PearlDoCalculus.DAG
#print PearlDoCalculus.DAG.CausalModel
#print PearlDoCalculus.DAG.CausalModel.CondIndep
#print PearlDoCalculus.DAG.CausalModel.marginal
#print PearlDoCalculus.DAG.CausalModel.fullJoint
#print PearlDoCalculus.DAG.DSeparated
#print PearlDoCalculus.DAG.Walk
#print PearlDoCalculus.DAG.Walk.Blocked

-- 3. Aksiomer for hovedresultatet og de viktigste byggesteinene
#print axioms DSepSound.dsep_sound
#print axioms Lauritzen.moral_sep_of_dsep_lauritzen
#print axioms PearlDoCalculus.marginal_eq_restricted_joint
#print axioms PearlDoCalculus.fullJoint_apply_prod
#print axioms Counterexample.moral_sep_of_dsep_counterexample
