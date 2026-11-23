/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Blocking

/-!
# The d-separation relation

The fourth building block of d-separation. `Reachability.lean`, `Walks.lean` and
`Blocking.lean` give reachability, walks and blocking; here they are put together into
the relation itself:

`x` and `y` are d-separated by `Z` when *every* walk between them is blocked.

This is a quantification over the type `Walk G x y`. Its negation is clean: `x` and `y`
are not d-separated exactly when there is at least one open walk, an active channel of
information in Pearl's sense (`not_dSeparated_iff`).

`not_dSeparated_of_edge` is the first concrete consequence: adjacent vertices can never
be d-separated, since the edge itself is a short walk that is always open.

The weight-bearing theorem, that d-separation implies conditional independence in every
causal model on the graph, is `DSepSound.dsep_sound` (`Soundness/DSepSound`); its converse is
`Completeness.dsep_iff`. The path-based variant is in `Soundness/WalkPath`, the version for
sets in `Soundness/SetSound`.

**Main definitions and results.** `DAG.DSeparated`, `DAG.not_dSeparated_iff`,
`DAG.not_dSeparated_of_edge`.
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
`DSeparated G Z x y`: `x` and `y` are d-separated by `Z`, that is, every walk between
them is blocked.
-/
def DSeparated (G : DAG V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : Walk G x y, Walk.Blocked Z p

/--
`x` and `y` are *not* d-separated exactly when there is an open walk between them.
-/
theorem not_dSeparated_iff (G : DAG V) (Z : Finset V) (x y : V) :
    ¬ DSeparated G Z x y ↔ ∃ p : Walk G x y, Walk.Open Z p := by
  simp only [DSeparated, Walk.Open, not_forall]

/--
Adjacent vertices are never d-separated: the edge `x → y` is a walk of length 1, and a
walk without interior vertices is never blocked.
-/
theorem not_dSeparated_of_edge (G : DAG V) (Z : Finset V) {x y : V}
    (h : G.edge x y) : ¬ DSeparated G Z x y := by
  intro hsep
  have hb : Walk.Blocked Z (Walk.fwd h (Walk.nil (G := G) y)) :=
    hsep (Walk.fwd h (Walk.nil (G := G) y))
  simp [Walk.Blocked, Walk.blockedAux] at hb

end DAG

end PearlDoCalculus
