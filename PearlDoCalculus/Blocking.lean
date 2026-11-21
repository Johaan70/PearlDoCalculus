/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Walks

/-!
# Colliders and blocked walks

The third building block of d-separation, after DAGs with reachability
(`Reachability.lean`) and walks (`Walks.lean`); the d-separation relation itself is in
`DSeparation.lean`.

An interior vertex of a walk is either a collider or a non-collider, decided by the
directions of the two edges that meet there:

* `→ m ←` (step in `fwd`, step out `bwd`): collider.
* `→ m →`, `← m →`, `← m ←`: non-collider.

Pearl's blocking criterion: a walk is blocked by a set `Z` if it contains either a
non-collider in `Z`, or a collider such that neither the vertex itself nor any of its
descendants lies in `Z`. "Descendant" is `Reaches` from `Reachability.lean`.

`blockedAux` recurses over the walk and carries the direction of the step that led into
the start vertex of the remaining walk (`Incoming`). This is what classifies each
interior vertex: the step in is known from the parameter, the step out from the next
constructor.

**Main definitions.** `Incoming`, `Walk.blockedAux`, `Walk.Blocked`, `Walk.Open`.
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
The direction of the step that led into a vertex, seen in a larger walk. `start` means
that the vertex is the start of the walk; then it is not interior and cannot block.
`fwd`/`bwd` is the direction of the incoming edge.
-/
inductive Incoming
  | start
  | fwd
  | bwd

namespace Walk

/--
`blockedAux Z inc p`: the walk `p` contains a blocking vertex, given that the start
vertex of `p` was reached by a step with direction `inc`.

The start vertex `m` of a nonempty `p` is interior when `inc ≠ start`. It is a collider
when the step in is `fwd` and the step out is `bwd`, and then it blocks if
`∀ z ∈ Z, ¬ Reaches m z` (no descendant, `m` itself included, in `Z`). Otherwise it is a
non-collider and blocks if `m ∈ Z`.
-/
def blockedAux {G : DAG V} (Z : Finset V) :
    Incoming → {m t : V} → Walk G m t → Prop
  | _,      _, _, .nil _      => False
  | .start, _, _, .fwd _ rest => blockedAux Z .fwd rest
  | .start, _, _, .bwd _ rest => blockedAux Z .bwd rest
  | .fwd,   m, _, .fwd _ rest => m ∈ Z ∨ blockedAux Z .fwd rest
  | .bwd,   m, _, .fwd _ rest => m ∈ Z ∨ blockedAux Z .fwd rest
  | .fwd,   m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ blockedAux Z .bwd rest
  | .bwd,   m, _, .bwd _ rest => m ∈ Z ∨ blockedAux Z .bwd rest

/--
`Blocked Z p`: the walk `p` is blocked by `Z` by Pearl's criterion. The start vertex is
not treated as interior, hence `Incoming.start`.
-/
def Blocked {G : DAG V} (Z : Finset V) {s t : V} (p : Walk G s t) : Prop :=
  blockedAux Z .start p

/--
`Open Z p`: the walk is open (active) given `Z`, that is, not blocked. These are the
walks that d-separation must rule out.
-/
def Open {G : DAG V} (Z : Finset V) {s t : V} (p : Walk G s t) : Prop :=
  ¬ Blocked Z p

/-- The empty walk has no interior vertices and is never blocked. -/
theorem not_blocked_nil {G : DAG V} (Z : Finset V) (v : V) :
    ¬ Blocked Z (Walk.nil (G := G) v) := by
  simp [Blocked, blockedAux]

end Walk

end DAG

end PearlDoCalculus
