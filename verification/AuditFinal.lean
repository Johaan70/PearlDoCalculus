/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Audit of the final state of the cleanup (tag `v4.208`, run from a fresh clone; the
output is kept in `verification/audit_final_output.txt`).

It makes the same checks as the frozen audit of tag `v4.80`
(`verification/AuditV480.lean`), with English comments:

1. the definitions the completeness theorem rests on (`#print`);
2. the exact statements of the completeness of the ID algorithm (steps H2–H5 of
   `HANDOFF.md`, section 2) and of its soundness (`#check @`);
3. a sanity check: by `Hedge.idCheck_iff`, the bow graph `x → y`, `x ↔ y` is not
   identifiable for all value types, because `idCheck` answers no (`example`);
4. the main results of the earlier layers (`#check @`);
5. the axioms behind the public results (`#print axioms`); each line must read
   `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Names. Every name used in `AuditV480.lean` still exists with the same meaning, so no
name had to be changed here: the public results and definitions kept their names, and
the helpers `Hedge.CConn`, `Hedge.rootsIn`, `Identification.Bow.bowG` and
`IdAlgo.bow_idCheck` were not renamed in step 6 of `CLEANUP.md` (names used in the frozen
audit file are not renamed). Nothing in `AuditV480.lean` lacks a counterpart.

The exact printed statements of all public results (with `pp.fullNames`) are compared
with `verification/public_statements.txt` by `scripts/check.sh` through
`verification/PublicStatements.lean`.

Run with: lake env lean verification/AuditFinal.lean
-/
import PearlDoCalculus

-- 1. The definitions the statements rest on
#print Identification.Identifiable
#print IdAlgo.idCheck
#print Hedge.IsHedge
#print Hedge.CConn
#print Hedge.rootsIn

-- 2. Completeness (H2–H5) and soundness of the ID algorithm
#check @Hedge.idCheck_iff
#check @Hedge.idCheck_false_hedge
#check @Hedge.PM.hedge_not_ident
#check @Hedge.PM.hedge_not_ident_Y
#check @IdAlgo.idCheck_sound

-- 3. Sanity check: by `idCheck_iff`, the bow `x → y`, `x ↔ y` is not identifiable for
-- all value types (because `idCheck` says no).
example : ¬ ∀ (α : Fin 3 → Type) [∀ v, Nonempty (α v)],
    Identification.Identifiable Identification.Bow.bowG α ({0} : Finset (Fin 3))ᶜ {1} {2} := by
  intro h
  have h1 := (Hedge.idCheck_iff Identification.Bow.bowG {0} {1} {2}
    (by decide) (by decide) (by decide) (by decide)).mpr h
  rw [IdAlgo.bow_idCheck] at h1
  exact Bool.false_ne_true h1

-- 4. Main results of the earlier layers
#check @Completeness.dsepSet_iff
#check @Completeness.rule1_iff_set
#check @Completeness.rule2_iff_set
#check @Completeness.rule3_iff_set

-- 5. Axioms behind the public results
#print axioms Hedge.idCheck_iff
#print axioms Hedge.idCheck_false_hedge
#print axioms Hedge.PM.hedge_not_ident
#print axioms Hedge.PM.hedge_not_ident_Y
#print axioms IdAlgo.idCheck_sound
#print axioms Idc.idc_sound
#print axioms Completeness.dsep_iff
#print axioms Completeness.dsepSet_iff
#print axioms Completeness.rule1_iff_set
#print axioms Completeness.rule2_iff_set
#print axioms Completeness.rule3_iff_set
#print axioms Adjustment.backdoor_adjustment_criterion
#print axioms Adjustment.frontdoor_adjustment_criterion
#print axioms Identification.CFactor.tian_iff
#print axioms Verma.verma_constraint
