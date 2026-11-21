/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DAG

/-!
# Directed reachability

The first building block of d-separation (followed by `Walks.lean`, `Blocking.lean`
and `DSeparation.lean`). It defines directed reachability in a finite DAG: the relation
`G.Reaches u v`, "`v` can be reached from `u` along directed edges", that is, `v` is a
descendant of `u` (every vertex is its own descendant). It is needed in two places:

* the back-door criterion requires that the adjustment set `Z` contains no descendants
  of the treatment `X`;
* the collider rule of d-separation refers to the descendants of the collider.

`Reaches` is the reflexive-transitive closure of the edge relation, so reflexivity,
single edges and transitivity come for free. The key property is `rank_le_of_reaches`:
reachability respects the rank function, by induction on the closure. This is the
acyclicity of a finite DAG in a form one can compute with. `not_reaches_of_edge` is
acyclicity at the level of edges.

**Main definitions and results.** `DAG.Reaches`, `DAG.rank_le_of_reaches`,
`DAG.not_reaches_of_edge`.
-/

namespace PearlDoCalculus

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `G.Reaches u v`: `v` can be reached from `u` by a possibly empty directed path, that
is, `v` is a descendant of `u`, where `u` counts as a descendant of itself. -/
def Reaches (G : DAG V) : V → V → Prop :=
  Relation.ReflTransGen G.edge

/-- Reachability is reflexive. -/
theorem Reaches.refl (G : DAG V) (u : V) : G.Reaches u u :=
  Relation.ReflTransGen.refl

/-- A single edge gives reachability. -/
theorem Reaches.of_edge (G : DAG V) {u v : V} (h : G.edge u v) :
    G.Reaches u v :=
  Relation.ReflTransGen.single h

/-- Reachability is transitive. -/
theorem Reaches.trans (G : DAG V) {u v w : V}
    (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  Relation.ReflTransGen.trans h₁ h₂

/--
**Reachability respects the rank.**

A descendant has at least the rank of its ancestor. This is the acyclicity of a finite
DAG in a form one can compute with: the rank is monotone along every directed path.
-/
theorem rank_le_of_reaches (G : DAG V) {u v : V} (h : G.Reaches u v) :
    G.rank u ≤ G.rank v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt (G.rank_strict_mono _ _ hbc))

/--
Acyclicity at the level of edges: after an edge `u → v` there is no directed path back
from `v` to `u`.
-/
theorem not_reaches_of_edge (G : DAG V) {u v : V} (h : G.edge u v) :
    ¬ G.Reaches v u := by
  intro hvu
  exact absurd (G.rank_strict_mono u v h)
    (not_lt.mpr (G.rank_le_of_reaches hvu))

end DAG

end PearlDoCalculus
