import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    (X Y Z : Finset V) (hXY : Disjoint X Y) (hXYZ : Disjoint (X ∪ Y) Z)
    (c : (Assignment (α := α) X × Assignment (α := α) Y) × Assignment (α := α) Z) :
    ((assignmentSplit3 X Y Z hXY hXYZ).symm c).restrict (subset_union3_right X Y Z) = c.2 := by
  funext v
  simp [assignmentSplit3, assignmentSplit, Assignment.restrict, Equiv.Finset.union]
