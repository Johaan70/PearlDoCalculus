import Mathlib.Probability.ProbabilityMassFunction.Basic
open scoped BigOperators ENNReal

#check @PMF.tsum_coe
#check @PMF.hasSum_coe_one
#check @hasSum_fintype
#check @HasSum.unique

example {α : Type*} [Fintype α] (p : PMF α) : ∑ a, p a = 1 :=
  (hasSum_fintype _).unique p.hasSum_coe_one

example {α : Type*} [Fintype α] (p : PMF α) : ∑ a, p a = 1 := by
  simpa using p.tsum_coe
