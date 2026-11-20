/-
# Soundness of d-separation (Verma–Pearl) — proof skeleton

## For the assistant filling this in

This file is a **decomposition**, not a proof. Every `sorry` is a separate
task. Work bottom-up: Layer 0 → Layer 1 → Layer 2 → Layer 3 → final.
Do not attempt `dsep_sound` directly; it is a short composition once the
layers below are closed.

Existing `PearlDoCalculus` definitions this file builds on, with their
verified signatures:

    DAG.lean
      structure DAG (V) [DecidableEq V] [Fintype V]
      DAG.edge : V → V → Prop          -- lowercase
      DAG.rank : V → ℕ
      DAG.parents (G) (v) : Finset V

    Reachability.lean
      DAG.Reaches (G) : V → V → Prop
      Reaches.refl, Reaches.of_edge, Reaches.trans
      rank_le_of_reaches, not_reaches_of_edge

    Walks.lean
      inductive DAG.Walk (G) : V → V → Type u
        | nil (v) : Walk G v v
        | fwd {a b c} : G.edge a b → Walk G b c → Walk G a c
        | bwd {a b c} : G.edge b a → Walk G b c → Walk G a c
      Walk.length, Walk.support : Walk G a b → List V

    Blocking.lean
      Walk.blockedAux, Walk.Blocked, Walk.Open

    DSeparation.lean
      DAG.DSeparated (G) (Z : Finset V) (x y : V) : Prop

    CausalModel.lean
      structure CausalModel (G : DAG V) (α : V → Type v)
      Assignment (S : Finset V) : Type (max u v) := ∀ v : {v // v ∈ S}, α v.1
      Assignment.restrict {S T} (h : T ⊆ S) : Assignment S → Assignment T
      Assignment.extend
      marginal (M) (S : Finset V) : PMF (Assignment (α := α) S)
      jointUpTo, fullJoint
      CondIndep (M) (X Y Z : Finset V) : Prop

**`marginal` returns a `PMF`, not a value.** Write `(M.marginal S) a`, with
the assignment applied to the PMF. `M.marginal S a` also elaborates but is
easy to misread; keep the parentheses.

**Namespaces.** Everything above lives under `PearlDoCalculus.DAG` or
`PearlDoCalculus`. Do *not* `open DAG` here — it shadows `CausalModel` and
`CondIndep` and turns them into field projections on `G`, which produces a
cascade of "invalid field" errors. `set_option autoImplicit false` is on so
a typo is an error rather than a silently invented variable.

Three properties of the existing code shape everything below.

1. `DAG.Walk` is an inductive *Type*, not a list. All induction in Layer 2
   goes over `nil`/`fwd`/`bwd`. `fwd` steps with the arrow along travel,
   `bwd` against it. A collider at `m` is: arrived by `fwd`, departs by
   `bwd`.

2. `blockedAux` threads an `Incoming` state through the walk. Its collider
   case reads

       | .fwd, m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ ...

   so "this collider is open" unfolds to `∃ z ∈ Z, G.Reaches m z`.
   Layer 2's central lemma is exactly that existential.

3. `CondIndep` is stated multiplicatively:

       P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)

   No division, no positivity hypotheses. A deliberate choice that avoids
   `ENNReal` division entirely, so Layer 3 lands directly in the target
   form. Do not reformulate it as a quotient.

## Proof strategy: moralisation, not walk induction

The `CausalModel.lean` docstring proposes structural induction directly
over blocked/active walks. That is how Pearl presents the result and it is
the harder path to formalise: because `blockedAux` carries state, being
blocked is not local to a single step, and the naive induction hypothesis
does not close.

This skeleton takes the Lauritzen route instead:

    d-separation in G
      ⟹ (restrict to ancestral subgraph)
    d-separation in G.induce (ancestors G ({x,y} ∪ Z))
      ⟹ (moralise)
    vertex separation in moralGraph
      ⟹ (factorisation splits along a separator)
    conditional independence

Graph content sits in Layer 2, probabilistic content in Layers 1 and 3.
They are independent and can be worked in parallel.

## Difficulty map

    Layer 0   routine       induce, ancestral sets, moral graph, cliques
    Layer 1   HARD          marginalisation onto an ancestral set
    Layer 2   HARDEST       d-separation ↔ moral separation
    Layer 3   medium        product form ⟹ CondIndep
    Final     short         composition

If Layer 2 resists, the induction is stated wrong. Change the statement
before fighting the tactic.

## Arithmetic warning

`jointUpTo` and `marginal` land in `ENNReal`, not `ℝ≥0`. Lemmas proved for
`ℝ≥0` do not apply and fail in confusing ways — `div_lt_one`, `norm_num` on
fractions, and `decide` on numerals all behave differently. When a goal
looks like it should close but does not, run `set_option pp.all true` and
read the type before reaching for another tactic. `ENNReal.div_lt_iff` and
`tsub_eq_zero_iff_le` are the workhorses; truncated subtraction is a trap.

## Placeholder convention

Hypotheses whose exact form is not yet known are written `True` rather than
`sorry`. A `sorry` in hypothesis position makes the whole declaration a
non-proposition and Lean rejects it outright. Replace each `True` with the
real statement as it becomes clear, working from the layer below.
-/

import PearlDoCalculus.DSepSoundSkeleton.Moralisation
import PearlDoCalculus.DSepSoundSkeleton.AncestralReduction
import PearlDoCalculus.DSepSoundSkeleton.Separator

/-! Sluttmonteringen er `DSepSound.dsep_sound` i `DSepSound.lean`. -/
