import PearlDoCalculus

-- 1. Nøyaktige statements, med alle implisitte argumenter og instanser
#check @DoCalculus.rule1
#check @DoCalculus.rule2
#check @Rule3.rule3
#check @Rule3.rule3_pos
#check @DoCalculus.doModel_fullJoint
#check @SetSound.dsep_sound_set
#check @WalkPath.dsep_sound_path

-- 2. Definisjonene reglene hviler på
#print DoCalculus.cutIn
#print DoCalculus.cutOut
#print DoCalculus.doModel
#print DoCalculus.clampModel
#print Rule3.Z1
#print Rule3.Z2
#print SetSound.DSeparatedSet
#print PearlDoCalculus.DAG.DSeparatedPath

-- 3. Aksiomer
#print axioms DSepSound.dsep_sound
#print axioms WalkPath.dsep_sound_path
#print axioms SetSound.dsep_sound_set
#print axioms DoCalculus.doModel_fullJoint
#print axioms DoCalculus.doModel_marginal_self
#print axioms DoCalculus.doModel_empty
#print axioms DoCalculus.rule1
#print axioms DoCalculus.rule2
#print axioms Rule3.rule3_pos
#print axioms Rule3.rule3
#print axioms DoAudit.rule2_fails_with_confounder
