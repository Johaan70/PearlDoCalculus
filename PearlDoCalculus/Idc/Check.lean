/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Idc

/-!
# The IDC check

Shpitser and Pearl's IDC algorithm decides the conditional effect `P(Y | do(X), W)`. It
moves, one at a time, every variable `w` of the conditioning set `W` that rule 2 allows
into the intervention, and then asks the ID check about the unconditional effect that is
left. This file defines that check (`docs/design-idc.md`, step 1).

**The single move.** In the state `(M, W')` the set `M` has been moved into the
intervention and `W'` is still conditioned on. A vertex `w ∈ W'` is *movable*
(`Movable`) when `Y` and `{w}` are d-separated by `(X ∪ M) ∪ (W' ∖ {w})` in `G` without
the edges into `X ∪ M` and out of `w`. This is exactly the side condition of
`DoCalc.Derives.rule2` and of `idc_sound`, with `X ∪ M` as the intervention, `{w}` as
the set that is moved, and `W' ∖ {w}` as the rest. A move (`Move`) goes from `(M, W')` to
`(insert w M, W'.erase w)`, and `Reachable G X Y W` is the set of states that moves reach
from `(∅, W)`.

**The check.** A `Finset` has no canonical order, so "pick a movable vertex" is not a
function. One round (`moveRound`) therefore moves every vertex that is movable now:
`M ↦ M ∪ {w ∈ W ∖ M | w movable from (M, W ∖ M)}`. The round only adds vertices of `W`,
so after `|W|` rounds it stands still (`IdAlgo.iter_fix`); that is the moved set
`movedSet`. Then `idcCheck G U X Y W` is the ID check of `P(Y ∪ W' | do(X ∪ M))` for
`M = movedSet` and `W' = W ∖ M`. That the moved set is the same for every order of
single moves is proved in `Idc/Maximal`.

**Decidability.** `SetSound.DSeparatedSet` is a `Prop`, and the project has no proved
decidable criterion equivalent to it, so the round uses classical decidability and the
check is `noncomputable`. It cannot be run by `decide`.

**Main results.** `Idc.Movable`, `Idc.Move`, `Idc.Reachable`, `Idc.moveRound`,
`Idc.movedSet`, `Idc.idcCheck`; the facts `movedSet_subset` and `moveRound_movedSet`.
-/

open PearlDoCalculus DAG DoCalculus Classical

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Single moves -/

/-- **`w` is movable from the state `(M, W')`**: `w ∈ W'`, and rule 2 lets `w` move from
the conditioning set into the intervention, that is, `Y ⊥ {w} | (X ∪ M) ∪ (W' ∖ {w})` in
`G` without the edges into `X ∪ M` and out of `w`. -/
def Movable (G : DAG V) (X Y M W' : Finset V) (w : V) : Prop :=
  w ∈ W' ∧ SetSound.DSeparatedSet (cutOut (cutIn G (X ∪ M)) {w}) ((X ∪ M) ∪ (W' \ {w})) Y {w}

/-- **One move**: a movable `w` goes from `W'` to `M`. -/
def Move (G : DAG V) (X Y : Finset V) (s t : Finset V × Finset V) : Prop :=
  ∃ w, Movable G X Y s.1 s.2 w ∧ t = (insert w s.1, s.2.erase w)

/-- The states that single moves reach from `(∅, W)`, in any order. -/
def Reachable (G : DAG V) (X Y W : Finset V) (s : Finset V × Finset V) : Prop :=
  Relation.ReflTransGen (Move G X Y) (∅, W) s

/-! ## The check -/

/-- **One round**: every vertex of `W ∖ M` that is movable from `(M, W ∖ M)` is moved. -/
noncomputable def moveRound (G : DAG V) (X Y W M : Finset V) : Finset V :=
  M ∪ (W \ M).filter (fun w => Movable G X Y M (W \ M) w)

/-- **The moved set**: `|W|` rounds from `∅`. -/
noncomputable def movedSet (G : DAG V) (X Y W : Finset V) : Finset V :=
  (moveRound G X Y W)^[W.card] ∅

/-- **The IDC check** for `P(Y | do(X), W)`: the ID check of `P(Y ∪ W' | do(X ∪ M))`,
where `M` is the moved set and `W' = W ∖ M`. -/
noncomputable def idcCheck (G : DAG V) (U X Y W : Finset V) : Bool :=
  IdAlgo.idCheck G U (X ∪ movedSet G X Y W) (Y ∪ (W \ movedSet G X Y W))

/-! ## The moved set is a fixed point inside `W` -/

/-- A round only adds vertices. -/
lemma subset_moveRound (G : DAG V) (X Y W M : Finset V) : M ⊆ moveRound G X Y W M :=
  Finset.subset_union_left

/-- A round stays inside `W`. -/
lemma moveRound_subset (G : DAG V) (X Y W M : Finset V) (hM : M ⊆ W) :
    moveRound G X Y W M ⊆ W :=
  Finset.union_subset hM ((Finset.filter_subset _ _).trans Finset.sdiff_subset)

/-- The moved set lies in `W`. -/
lemma movedSet_subset (G : DAG V) (X Y W : Finset V) : movedSet G X Y W ⊆ W :=
  Finset.iterate_subset W (moveRound G X Y W) (moveRound_subset G X Y W)
    ∅ (Finset.empty_subset W) W.card

/-- **The moved set is a fixed point** of the round. -/
lemma moveRound_movedSet (G : DAG V) (X Y W : Finset V) :
    moveRound G X Y W (movedSet G X Y W) = movedSet G X Y W :=
  IdAlgo.iter_fix W (moveRound G X Y W) (subset_moveRound G X Y W) (moveRound_subset G X Y W)
    ∅ (Finset.empty_subset W)

end Idc
