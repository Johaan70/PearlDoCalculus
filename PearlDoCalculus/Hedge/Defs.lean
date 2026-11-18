import PearlDoCalculus.IdAlgo

/-!
# Hedges: the basic definitions

This file holds the three definitions that the completeness proof of the ID algorithm
(`Hedge.idCheck_iff`) is stated in terms of. They are needed by every later file in the
`Hedge` folder: the step where a failing ID check produces a hedge, the spanning tree
inside a hedge, and the parity models that show a hedge blocks identification.

* `rootsIn G F`: the nodes of `F` that have no child inside `F`.
* `CConn G U F`: `F` is c-connected inside itself, that is, any two nodes of `F` are
  joined by a path of latent steps inside `G[F]` (edges whose tail is a latent node in
  `U`, walked in either direction).
* `IsHedge G U X Y F F'`: Shpitser and Pearl's hedge for `P_X(Y)` (JMLR 2008, Def. 5)
  in set form. `F ⊊ F'`, both are c-connected, both reach the roots of `F` along
  edges inside themselves, `F` avoids `X`, `F'` meets `X`, and the roots of `F` are
  ancestors of `Y` in the graph with the edges into `X` cut.

There are no proofs here; the facts about these definitions live in `Hedge.lean`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Nodene i `F` uten barn i `F`. -/
def rootsIn (G : DAG V) (F : Finset V) : Finset V := F.filter (fun v => ∀ w ∈ F, ¬ G.edge v w)

/-- `F` er c-sammenhengende innenfor seg selv. -/
def CConn (G : DAG V) (U F : Finset V) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, b ∈ ccomp (DAG.induce G F) U a

/-- **Hedge for `P_X(Y)`** (Shpitser–Pearl Def. 5), på mengdeform. -/
structure IsHedge (G : DAG V) (U X Y F F' : Finset V) : Prop where
  sub : F ⊆ F'
  ne : F ≠ F'
  rootF : ancIn G F (rootsIn G F) = F
  rootF' : ancIn G F' (rootsIn G F) = F'
  out : ∀ v ∈ F, v ∉ X
  meet : ∃ x ∈ X, x ∈ F'
  anc : rootsIn G F ⊆ ancIn (cutIn G X) Finset.univ Y
  conn : CConn G U F
  conn' : CConn G U F'

end Hedge
