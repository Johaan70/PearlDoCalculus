import PearlDoCalculus.Adjustment

/-!
# Completeness of d-separation: directed paths that avoid `Z`

**What it proves.** The notion `ReachesAvoiding G Z s v`: a directed path from `s` to `v`
on which every vertex after `s` lies outside `Z`. Two facts about it: such a path from a
source `s ∉ Z` ends outside `Z` (`reach_notMem`), and a vertex `v ∉ Z` other than `s` is
reached exactly when one of its parents is (`reach_iff_parent`).

**Why it is needed.** The counter-models for the completeness of d-separation and of the
do-rules propagate a bit from a source `s ∉ Z` along directed paths outside `Z`
(`Completeness/Chain.lean`, `chainModel`). Every chain is made of such paths (its legs
are `ReachesAvoiding` paths and `ReachesParentAvoiding` steps into a collider), and the
support of the chain model is computed vertex by vertex with `reach_iff_parent`. A trek
`x ← … ← s → … → y` outside `Z` is the chain without colliders (`Chain.trek`).

**How the proof goes.** `ReachesAvoiding` is the reflexive transitive closure of the
edges into vertices outside `Z`; both facts follow by splitting off the last step
(`Relation.ReflTransGen.cases_tail`).

**Main results.** `ReachesAvoiding`, `reach_notMem`, `reach_iff_parent`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Directed paths outside `Z` -/

/-- A directed path from `s` to `v` on which every vertex after `s` lies outside `Z`. -/
def ReachesAvoiding (G : DAG V) (Z : Finset V) (s v : V) : Prop :=
  Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) s v

/-- If the path starts outside `Z`, it ends outside `Z`. -/
lemma reach_notMem {G : DAG V} {Z : Finset V} {s v : V} (hs : s ∉ Z)
    (h : ReachesAvoiding G Z s v) : v ∉ Z := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, _, hpv⟩
  · exact hs
  · exact hpv.2

/-- One step back: a vertex `v ∉ Z` other than `s` is reached from `s` outside `Z` exactly
when one of its parents is. -/
lemma reach_iff_parent {G : DAG V} {Z : Finset V} {s v : V} (hvZ : v ∉ Z) (hvs : v ≠ s) :
    ReachesAvoiding G Z s v ↔ ∃ p ∈ G.parents v, ReachesAvoiding G Z s p := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, hp, hpv⟩
    · exact absurd rfl hvs
    · exact ⟨p, DAG.mem_parents.2 hpv.1, hp⟩
  · rintro ⟨p, hp, hr⟩
    exact hr.tail ⟨DAG.mem_parents.1 hp, hvZ⟩

end Completeness
