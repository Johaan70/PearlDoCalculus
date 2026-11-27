/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Audit of the IDC check for conditional effects, Part A (`docs/design-idc.md`). The
output, run from a fresh clone, is kept in `verification/audit_idc_output.txt`.

1. The definitions the statements rest on (`#print`): the conditional identifiability
   `Idc.IdentifiableCond`, the single move (`Idc.Movable`, `Idc.Move`, `Idc.Reachable`),
   the round `Idc.moveRound`, the moved set `Idc.movedSet` and the check `Idc.idcCheck`.
2. The exact statements (`#check @`): the moved set is the unique maximal reachable one,
   independent of the order of the moves (`Idc.Reachable.subset_movedSet`,
   `Idc.reachable_movedSet`, `Idc.not_movable_movedSet`, with the key lemma
   `Idc.Movable.after_move`); soundness (`Idc.idcCheck_sound`); derivability
   (`Idc.idcCheck_derives`); derivations give conditional identifiability
   (`Idc.identifiableCond_of_derives`); the collecting theorem
   (`Idc.idcCheck_derives_identifiableCond`); and, for context, the one-step
   `Idc.idc_sound`.
3. Sanity checks: with nothing conditioned on, the IDC check is the ID check
   (`example`), so on the bow graph `x → y`, `x ↔ y` it says no (`example`).
4. The axioms (`#print axioms`); each line must read
   `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Run with: lake env lean verification/AuditIdc.lean
-/
import PearlDoCalculus

-- 1. The definitions the statements rest on
#print Idc.IdentifiableCond
#print Idc.Movable
#print Idc.Move
#print Idc.Reachable
#print Idc.moveRound
#print Idc.movedSet
#print Idc.idcCheck

-- 2. The moved set, soundness, derivability
#check @Idc.Movable.after_move
#check @Idc.Reachable.subset_movedSet
#check @Idc.reachable_movedSet
#check @Idc.not_movable_movedSet
#check @Idc.idcCheck_sound
#check @Idc.idcCheck_derives
#check @Idc.identifiableCond_of_derives
#check @Idc.idcCheck_derives_identifiableCond
#check @Idc.idc_sound

-- 3. Sanity checks: with `W = ∅` nothing is moved and the IDC check is the ID check;
-- so on the bow `x → y`, `x ↔ y` the IDC check for `P(y | do(x))` says no.
example {V : Type*} [DecidableEq V] [Fintype V] (G : PearlDoCalculus.DAG V)
    (U X Y : Finset V) :
    Idc.idcCheck G U X Y ∅ = IdAlgo.idCheck G U X Y := by
  simp [Idc.idcCheck, Idc.movedSet]

example : Idc.idcCheck Identification.Bow.bowG {0} {1} {2} ∅ = false := by
  simp only [Idc.idcCheck, Idc.movedSet, Finset.card_empty, Function.iterate_zero, id,
    Finset.union_empty, Finset.sdiff_empty]
  exact IdAlgo.bow_idCheck

-- 4. Axioms
#print axioms Idc.Movable.after_move
#print axioms Idc.Reachable.subset_movedSet
#print axioms Idc.reachable_movedSet
#print axioms Idc.not_movable_movedSet
#print axioms Idc.idcCheck_sound
#print axioms Idc.idcCheck_derives
#print axioms Idc.identifiableCond_of_derives
#print axioms Idc.idcCheck_derives_identifiableCond
#print axioms Idc.idc_sound
