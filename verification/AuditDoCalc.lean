/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude

Audit of the completeness of the do-calculus for identification
(`docs/design-docalc-completeness.md`, phase 6). The output, run from a fresh clone, is
kept in `verification/audit_docalc_output.txt`.

1. The definitions the statements rest on (`#print`): the expressions `DoCalc.Expr`, the
   predicates `DoFree`, `vars`, `free` and `Positive` used in the statements and in the
   side conditions of the steps, and the derivations `DoCalc.Derives` with all their
   steps. A reader can check here that the calculus is the fixed list of the design note.
2. The exact statements (`#check @`): soundness of derivations (`DoCalc.derives_sound`,
   `DoCalc.identifiable_of_derives`), completeness (`DoCalc.docalc_complete`), the
   triangle (`DoCalc.docalc_triangle`, `DoCalc.docalc_triangle_iff`), and, for context,
   the completeness of the ID algorithm (`Hedge.idCheck_iff`).
3. A sanity check: by the triangle, the effect in the bow graph `x → y`, `x ↔ y` has no
   derivation into an observed expression without `do`, because `idCheck` says no
   (`example`). So derivability is not trivial.
4. The axioms (`#print axioms`); each line must read
   `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Run with: lake env lean verification/AuditDoCalc.lean
-/
import PearlDoCalculus

-- 1. The definitions the statements rest on
#print DoCalc.Expr
#print DoCalc.Expr.query
#print DoCalc.Expr.DoFree
#print DoCalc.Expr.vars
#print DoCalc.Expr.free
#print DoCalc.Expr.Positive
#print DoCalc.Derives

-- 2. Soundness, completeness and the triangle
#check @DoCalc.derives_sound
#check @DoCalc.identifiable_of_derives
#check @DoCalc.docalc_complete
#check @DoCalc.docalc_triangle
#check @DoCalc.docalc_triangle_iff
#check @Hedge.idCheck_iff

-- 3. Sanity check: by the triangle, the bow `x → y`, `x ↔ y` has no derivation of
-- `P(y | do(x))` into an observed expression without `do` (because `idCheck` says no).
example : ¬ ∃ e : DoCalc.Expr (Fin 3), e.DoFree ∧ e.vars ⊆ ({0} : Finset (Fin 3))ᶜ ∧
    DoCalc.Derives Identification.Bow.bowG {0} (DoCalc.Expr.query {2} {1}) e := by
  intro h
  have h1 := ((DoCalc.docalc_triangle Identification.Bow.bowG {0} {1} {2}
    (by decide) (by decide) (by decide) (by decide)).out 0 2).mpr h
  rw [IdAlgo.bow_idCheck] at h1
  exact Bool.false_ne_true h1

-- 4. Axioms
#print axioms DoCalc.derives_sound
#print axioms DoCalc.identifiable_of_derives
#print axioms DoCalc.docalc_complete
#print axioms DoCalc.docalc_triangle
#print axioms DoCalc.docalc_triangle_iff
#print axioms Hedge.idCheck_iff
