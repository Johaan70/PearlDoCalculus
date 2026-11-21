import PearlDoCalculus.Identification

/-!
# Audit of ID soundness: an effect that needs Tian's recursion

A check that the soundness of the ID algorithm (`CFactor.id_sound_anc_blocks`) reaches
beyond Tian's theorem for sets: an effect that Tian's simpler criterion cannot identify,
but the recursion of IDENTIFY can. The same example is computed automatically in
`IdAlgo.lean` (`IdAlgo.id_audit'`).

Vertices: `0 = u₁`, `1 = u₂` (latent), `2 = x`, `3 = b`, `4 = y`.
Edges: `x → y`, `u₁ → x`, `u₁ → b`, `u₂ → b`, `u₂ → y`, that is, `x ↔ b ↔ y`.

* `x` has a child (`y`) in its own c-component `{u₁, u₂, x, b, y}`, so the hypothesis of
  Tian's theorem for sets (`tian_identifiable_sets`) fails (`tian_sets_fails`).
* Still, `P(y | do(x))` is identifiable (`id_audit`, through `id_sound_anc_blocks`).
  The ancestors of `y` in `G_{x̄}` are `S = {u₂, x, y}`. The block `{u₂, y}` is reached
  from `V` by first summing out `b`, which is not an ancestor of `y`, and then separating
  `{u₂, y}` from `{u₁, x}` (`reach_y`). The answer is `P(y | x)`: `b` is a collider on
  `x ↔ b ↔ y`.

**Main results.** `IdAudit.tian_sets_fails`, `IdAudit.reach_y`, `IdAudit.id_audit`.
-/

open PearlDoCalculus DAG DoCalculus Identification Identification.CFactor

namespace IdAudit

/-- The graph `x ↔ b ↔ y`, `x → y`, with latent `u₁ = 0`, `u₂ = 1`. -/
def idG : DAG (Fin 5) where
  edge u v := (u = 2 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 3)) ∨ (u = 1 ∧ (v = 3 ∨ v = 4))
  decEdge := fun u v => inferInstanceAs
    (Decidable ((u = 2 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 3)) ∨ (u = 1 ∧ (v = 3 ∨ v = 4))))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide

/-- The hypothesis of `tian_identifiable_sets` fails: `y` lies in the c-component of
`x` (through `x ← u₁ → b ← u₂ → y`), and `x → y`. -/
theorem tian_sets_fails :
    ¬ (∀ x ∈ ({2} : Finset (Fin 5)), ∀ v ∈ ccomp idG {0, 1} x, ¬ idG.edge x v) := by
  intro h
  have h4 : (4 : Fin 5) ∈ ccomp idG {0, 1} 2 := by
    rw [mem_ccomp]
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (Or.inr ⟨by decide, by decide⟩ : latStep idG {0, 1} 2 0))
      (Or.inl ⟨by decide, by decide⟩ : latStep idG {0, 1} 0 3))
      (Or.inr ⟨by decide, by decide⟩ : latStep idG {0, 1} 3 1))
      (Or.inl ⟨by decide, by decide⟩ : latStep idG {0, 1} 1 4)
  exact h 2 (by decide) 4 h4 (by decide)

/-- The block `{u₂, y}` is reached from `V`: sum out `b`, then split off `{u₂, y}`. -/
theorem reach_y : Reach idG {0, 1} Finset.univ ({4, 2, 1} ∩ {1, 4}) := by
  have e1 : ({4, 2, 1} ∩ {1, 4} : Finset (Fin 5)) = {1, 4} := by decide
  have e2 : ({0, 1, 2, 4} ∩ {1, 4} : Finset (Fin 5)) = {1, 4} := by decide
  rw [e1]
  refine Reach.anc Finset.univ {0, 1, 2, 4} {1, 4} (by decide) ?_
  rw [Finset.univ_inter]
  refine Reach.block {0, 1, 2, 4} {1, 4} {1, 4} (by decide) ?_
  rw [e2]
  exact Reach.refl _

/-- **Audit: `P(y | do(x))` is identifiable**, even though Tian's theorem for sets does
not apply. -/
theorem id_audit : Identifiable idG (fun _ => Bool) ({0, 1} : Finset (Fin 5))ᶜ {2} {4} := by
  refine id_sound_anc_blocks (G := idG) {0, 1} {2} (by decide) {4, 2, 1} (by decide) id
    ({{2}, {1, 4}} : Finset (Finset (Fin 5))) (by decide) (by decide) (by decide) ?_ {4}
    (by decide) (by decide)
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr ⟨by decide, reach_y⟩)

end IdAudit

#print axioms IdAudit.tian_sets_fails
#print axioms IdAudit.id_audit
