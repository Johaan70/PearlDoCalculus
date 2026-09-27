import PearlDoCalculus

-- 1. Nøyaktige statements for de nye resultatene
#check @Rule3Flag.rule3_general
#check @Adjustment.backdoor_stratum
#check @Adjustment.backdoor_adjustment
#check @Adjustment.frontdoor_product
#check @Adjustment.frontdoor_adjustment

-- 2. Flaggmodellen regel 3 hviler på
#print Rule3Flag.flagModel
#print Rule3Flag.readVal

-- 3. Aksiomer for hele kjeden
#print axioms DSepSound.dsep_sound
#print axioms WalkPath.dsep_sound_path
#print axioms SetSound.dsep_sound_set
#print axioms DoCalculus.rule1
#print axioms DoCalculus.rule2
#print axioms Rule3Flag.rule3_general
#print axioms Adjustment.backdoor_stratum
#print axioms Adjustment.backdoor_adjustment
#print axioms Adjustment.frontdoor_product
#print axioms Adjustment.frontdoor_adjustment
