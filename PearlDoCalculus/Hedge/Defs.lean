import PearlDoCalculus.IdAlgo

/-!
# Hedges: the basic definitions

This file holds the three definitions that the completeness proof of the ID algorithm
(`Hedge.idCheck_iff`) is stated in terms of. A hedge is the obstruction to
identification: the proof shows that the ID check fails exactly when the graph contains a
hedge (step H2, `Hedge/FromID`), and that a hedge makes the effect non-identifiable
(steps H3 and H4, `Hedge/Roots` and `Hedge/Complete`). So every later file of the `Hedge`
folder uses these definitions: the step where a failing ID check produces a hedge, the
forest and spanning tree inside a hedge (`Hedge/Tree`), and the parity models on a hedge
(`Hedge/ParityModels` onwards).

* `rootsIn G F`: the nodes of `F` that have no child inside `F`.
* `CConn G U F`: `F` is c-connected inside itself, that is, any two nodes of `F` are
  joined by a path of latent steps inside `G[F]` (edges whose tail is a latent node in
  `U`, walked in either direction).
* `IsHedge G U X Y F F'`: Shpitser and Pearl's hedge for `P_X(Y)` (JMLR 2008, Def. 5)
  in set form. `F ⊊ F'`, both are c-connected, both reach the roots of `F` along
  edges inside themselves, `F` avoids `X`, `F'` meets `X`, and the roots of `F` are
  ancestors of `Y` in the graph with the edges into `X` cut.

There are no proofs here; the facts about these definitions live in the later files of
the `Hedge` folder (`ancIn_roots` and the c-connectedness lemmas in `Hedge/FromID`, the
forest and the tree in `Hedge/Tree`).

**Main definitions.** `rootsIn`, `CConn`, `IsHedge` (public).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The roots of `F`: the nodes of `F` that have no child inside `F`. They need not be
roots of `G`, nor childless in a larger set such as `F'`. -/
def rootsIn (G : DAG V) (F : Finset V) : Finset V := F.filter (fun v => ∀ w ∈ F, ¬ G.edge v w)

/-- `F` is c-connected inside itself: every node of `F` lies in the c-component of every
other node of `F`, computed in the induced graph `G[F]` with latent set `U`. -/
def CConn (G : DAG V) (U F : Finset V) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, b ∈ ccomp (DAG.induce G F) U a

/-- **A hedge for `P_X(Y)`** (Shpitser and Pearl, JMLR 2008, Def. 5), in set form.

Shpitser and Pearl's hedge is a pair of `R`-rooted c-forests `F' ⊆ F`; here the names
are swapped, so `F` is the smaller set and `F'` the larger one. With `R := rootsIn G F`
the fields say:

* `sub`, `ne`: `F ⊊ F'`;
* `rootF`, `rootF'`: every node of `F` (resp. `F'`) reaches `R` along edges inside `F`
  (resp. `F'`), stated as `ancIn … R = …`;
* `out`: `F` avoids `X`; `meet`: `F'` contains a node of `X`;
* `anc`: every root is an ancestor of `Y` in `G_{X̄}` (the edges into `X` cut);
* `conn`, `conn'`: `F` and `F'` are c-connected inside themselves (`CConn`).

A c-forest in the paper is a subgraph in which each node keeps at most one child edge,
so the roots need not be childless in `G[F']`; `R` is defined from `F` alone and serves
both sets. `F` and `F'` may contain latent nodes. -/
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
