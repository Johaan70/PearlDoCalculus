import PearlDoCalculus.Counterexample

/-!
# Audit: regresjonstester for d-separasjonssemantikken

Tre mekanismer testes:
* kjede `0 → 1 → 2`: uten betinging er kjeden åpen;
* kollider `0 → 2 ← 1`: uten betinging blokkerer kollideren;
* kollider `0 → 2 ← 1`: betinging på kollideren åpner den.

Den positive kjede-testen `DSeparated {1} 0 2` krever induksjon over
vandringer og kommer i en egen runde.
-/

open PearlDoCalculus DAG

namespace Audit

/-- Kjeden `0 → 1 → 2`. -/
def chainG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Kjede uten betinging: vandringen `0 → 1 → 2` er åpen. -/
theorem chain_not_dsep_empty : ¬ chainG.DSeparated ∅ 0 2 := by
  intro h
  have hb := h (Walk.fwd (Or.inl ⟨rfl, rfl⟩) (Walk.fwd (Or.inr ⟨rfl, rfl⟩) (Walk.nil 2)))
  simp [Walk.Blocked, Walk.blockedAux] at hb

/-- Kollider uten betinging: `0` og `1` er d-separert. -/
theorem collider_dsep_empty : Counterexample.ceG.DSeparated ∅ 0 1 :=
  fun p => Counterexample.blocked_from_source (by decide) (by decide) (by decide) p

/-- Kollider med betinging på kollideren: vandringen `0 → 2 ← 1` åpnes. -/
theorem collider_not_dsep_cond : ¬ Counterexample.ceG.DSeparated {2} 0 1 := by
  intro h
  have hb := h (Walk.fwd ⟨rfl, by decide⟩ (Walk.bwd ⟨rfl, by decide⟩ (Walk.nil 1)))
  simp only [Walk.Blocked, Walk.blockedAux, or_false] at hb
  exact hb 2 (Finset.mem_singleton_self 2) (DAG.Reaches.refl _ 2)

end Audit

#print axioms Audit.chain_not_dsep_empty
#print axioms Audit.collider_dsep_empty
#print axioms Audit.collider_not_dsep_cond
