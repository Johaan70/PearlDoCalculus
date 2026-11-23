/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Reachability

/-!
# Walks with oriented steps

The second building block of d-separation, after directed reachability
(`Reachability.lean`). d-separation is about undirected walks: one follows edges without
regard to their direction, but remembers the direction of each edge, since it is the
pattern of directions at a vertex that decides whether the vertex is a collider.

`Walk G a b` is a walk from `a` to `b` built from oriented steps. Two cons constructors
keep the orientation:

* `fwd` adds an edge that points forward along the walk (`a → b` in the DAG),
* `bwd` adds an edge that points backward (`b → a` in the DAG).

This is the distinction that `Blocking.lean` needs: a collider is a vertex where the step
in is `fwd` and the step out is `bwd`, two arrows that meet.

Note: `Walk` allows repeated vertices, so it is a walk, not a path in the graph-theoretic
sense. The soundness of d-separation holds at the level of walks; paths (walks without
repeated vertices) are treated in `Soundness/WalkPath`, which shows that the two notions give
the same d-separation.

**Main definitions.** `DAG.Walk`, `Walk.length`, `Walk.support`, with
`Walk.length_support`.
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
`Walk G a b`: an undirected walk from `a` to `b` in the DAG `G`, built from oriented
steps. Each edge is remembered with its direction:

* `nil v`: the empty walk at `v`,
* `fwd e rest`: a step along a forward edge, then `rest`,
* `bwd e rest`: a step along a backward edge, then `rest`.
-/
inductive Walk (G : DAG V) : V → V → Type u
  | nil (v : V) : Walk G v v
  | fwd {a b c : V} : G.edge a b → Walk G b c → Walk G a c
  | bwd {a b c : V} : G.edge b a → Walk G b c → Walk G a c

namespace Walk

/-- The number of edges of the walk. -/
def length {G : DAG V} : {a b : V} → Walk G a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .fwd _ rest => length rest + 1
  | _, _, .bwd _ rest => length rest + 1

/-- The vertices the walk visits, in order from `a` to `b`. -/
def support {G : DAG V} : {a b : V} → Walk G a b → List V
  | a, _, .nil _ => [a]
  | a, _, .fwd _ rest => a :: support rest
  | a, _, .bwd _ rest => a :: support rest

/-- A walk visits exactly one vertex more than it has edges. -/
theorem length_support {G : DAG V} {a b : V} (p : Walk G a b) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil v => simp [support, length]
  | fwd e q ih => simp [support, length, ih]
  | bwd e q ih => simp [support, length, ih]

end Walk

end DAG

end PearlDoCalculus
