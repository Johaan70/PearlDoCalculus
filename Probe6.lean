import PearlDoCalculus
import Mathlib.Combinatorics.SimpleGraph.Clique
open PearlDoCalculus DAG
#check @SimpleGraph.fromRel_adj
#check @SimpleGraph.IsClique
#check @DAG.parents
example {V : Type} [DecidableEq V] [Fintype V] (G : DAG V) (u v : V) :
    u ∈ G.parents v ↔ G.edge u v := by simp [DAG.parents]
