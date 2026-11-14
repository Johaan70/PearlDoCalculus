import PearlDoCalculus.Identification

/-!
# Audit av ID-sunnheten: en effekt som trenger Tians rekursjon

Noder: `0 = u₁`, `1 = u₂` (latente), `2 = x`, `3 = b`, `4 = y`.
Kanter: `x → y`, `u₁ → x`, `u₁ → b`, `u₂ → b`, `u₂ → y`, altså `x ↔ b ↔ y`.

* `x` har et barn (`y`) i sin egen c-komponent `{u₁, u₂, x, b, y}`, så hypotesen i Tians
  teorem for mengder (`tian_identifiable_sets`) holder ikke (`tian_sets_fails`).
* Likevel er `P(y | do(x))` identifiserbar (`id_audit`, via `id_sound_anc_blocks`).
  Forfedrene til `y` i `G_{x̄}` er `S = {u₂, x, y}`. Blokken `{u₂, y}` nås fra `V` ved
  først å marginalisere bort `b`, som ikke er forfar til `y`, og så skille `{u₂, y}` fra
  `{u₁, x}` (`reach_y`). Svaret er `P(y | x)`: `b` er en kollider på `x ↔ b ↔ y`.
-/

open PearlDoCalculus DAG DoCalculus Identification Identification.CFactor

namespace IdAudit

/-- Grafen `x ↔ b ↔ y`, `x → y`, med latente `u₁ = 0`, `u₂ = 1`. -/
def idG : DAG (Fin 5) where
  edge u v := (u = 2 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 3)) ∨ (u = 1 ∧ (v = 3 ∨ v = 4))
  decEdge := fun u v => inferInstanceAs
    (Decidable ((u = 2 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 3)) ∨ (u = 1 ∧ (v = 3 ∨ v = 4))))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide

/-- Hypotesen i `tian_identifiable_sets` holder ikke: `y` ligger i c-komponenten til `x`
(via `x ← u₁ → b ← u₂ → y`), og `x → y`. -/
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

/-- Blokken `{u₂, y}` nås fra `V`: marginaliser bort `b`, så skill ut `{u₂, y}`. -/
theorem reach_y : Reach idG {0, 1} Finset.univ ({4, 2, 1} ∩ {1, 4}) := by
  have e1 : ({4, 2, 1} ∩ {1, 4} : Finset (Fin 5)) = {1, 4} := by decide
  have e2 : ({0, 1, 2, 4} ∩ {1, 4} : Finset (Fin 5)) = {1, 4} := by decide
  rw [e1]
  refine Reach.anc Finset.univ {0, 1, 2, 4} {1, 4} (by decide) ?_
  rw [Finset.univ_inter]
  refine Reach.block {0, 1, 2, 4} {1, 4} {1, 4} (by decide) ?_
  rw [e2]
  exact Reach.refl _

/-- **Audit: `P(y | do(x))` er identifiserbar**, selv om Tians teorem for mengder ikke
gjelder. -/
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
