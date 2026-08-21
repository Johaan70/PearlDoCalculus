import PearlDoCalculus

open PearlDoCalculus FrontDoorModel
open scoped NNReal

namespace FrontDoorCheck

noncomputable def b (p : ℝ≥0) (h : p ≤ 1) : PMF Bool := PMF.bernoulli p h

noncomputable def testModel : FrontDoorModel Bool Bool Bool Bool where
  pU          := b (1/2) (by norm_num [div_le_one])
  pX_given_U  := fun u => b (if u then 3/4 else 1/4) (by split <;> norm_num [div_le_one])
  pZ_given_X  := fun x => b (if x then 4/5 else 1/5) (by split <;> norm_num [div_le_one, div_lt_one])
  pY_given_ZU := fun z u => b (if z && u then 9/10 else 2/5) (by split <;> norm_num [div_le_one, div_lt_one])

#check testModel
lemma hpos_testModel : ∀ x' z, (testModel.pZ_given_X x') z ≠ 0 := by
  intro x' z
  cases x' <;> cases z <;>
    simp [testModel, b, PMF.bernoulli_apply]
  all_goals rw [tsub_eq_zero_iff_le]
  all_goals push Not
  all_goals try rw [inv_eq_one_div]
  all_goals rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  all_goals simp
  all_goals norm_num
example :
    (testModel.doX true) true =
      ∑ z, (testModel.pZ_given_X true) z *
           ∑ x', testModel.pX x' * testModel.pY_given_XZ true x' z :=
  testModel.frontdoor_adjustment_observable true true hpos_testModel
end FrontDoorCheck

#print axioms FrontDoorCheck.hpos_testModel
