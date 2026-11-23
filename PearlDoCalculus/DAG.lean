/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Finite directed acyclic graphs

This file defines the graphs that every causal model in the project lives on: finite
directed acyclic graphs (DAGs) on a vertex type `V`.

**Acyclicity through a rank.** Instead of forbidding cycles directly, a `DAG` carries a
rank function `V → ℕ` that strictly increases along every edge. For finite graphs this
is the same as having a topological order, and it is much easier to use in proofs:
induction on the rank replaces reasoning about cycles.

**Parents.** `DAG.parents G v` is the finite set of direct parents of `v`. Two small
facts about it are used throughout the project:

* `DAG.mem_parents`: `u ∈ G.parents v ↔ G.edge u v`. It is deliberately not a `simp`
  lemma: some `simp` calls rely on `∈ G.parents v` staying as it is (for example the
  case dispatch in `Soundness/Factorizes`); unfold with `DAG.mem_parents` or
  `DAG.parents` where needed;
* `DAG.parents_subset_of_closed`: if `S` is closed under taking parents (every edge into
  a vertex of `S` starts in `S`), then the parents of every `v ∈ S` lie in `S`.

## Main definitions and results

* `DAG`, `DAG.parents`
* `DAG.mem_parents`, `DAG.parents_subset_of_closed`
* `DAG.not_self_edge`: no vertex is its own parent.
-/

namespace PearlDoCalculus

/--
A finite directed acyclic graph on a vertex type `V`. Acyclicity is encoded by a rank
function: edges go strictly from lower to higher rank.

For finite graphs this is equivalent to a topological order, and it is the most
convenient formulation for proofs.
-/
structure DAG (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The edge relation `u → v`. -/
  edge : V → V → Prop
  /-- The edge relation is decidable, so that we can compute over finite sets. -/
  decEdge : DecidableRel edge
  /-- Topological rank: edges go strictly from lower to higher rank. -/
  rank : V → ℕ
  /-- Acyclicity: the rank strictly increases along edges. -/
  rank_strict_mono : ∀ u v, edge u v → rank u < rank v

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

attribute [instance] DAG.decEdge

/-- The set of direct parents of `v` in `G`. -/
def parents (G : DAG V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun u => G.edge u v)

/-- `u` is a parent of `v` exactly when there is an edge `u → v`. -/
theorem mem_parents {G : DAG V} {u v : V} : u ∈ G.parents v ↔ G.edge u v := by
  simp [parents]

/-- If every edge into a vertex of `S` starts in `S` (for example, `S` is closed under
ancestors), then the parents of every vertex of `S` lie in `S`. -/
theorem parents_subset_of_closed {G : DAG V} {S : Finset V}
    (hS : ∀ v ∈ S, ∀ w, G.edge w v → w ∈ S) (v : V) (hv : v ∈ S) : G.parents v ⊆ S :=
  fun w hw => hS v hv w (mem_parents.mp hw)

/-- Acyclicity, derived: no vertex is its own parent. -/
theorem not_self_edge (G : DAG V) (v : V) : ¬ G.edge v v := by
  intro h
  exact (lt_irrefl _) (G.rank_strict_mono v v h)

end DAG

end PearlDoCalculus
