import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    {G : DAG V} (M : CausalModel G α) (L Z R : Finset V)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    True := by
  have hbase : Assignment (α := α) (∅ : Finset V) :=
    fun v => absurd v.2 (show v.1 ∉ (∅ : Finset V) by
      first
      | exact Finset.not_mem_empty _
      | exact Finset.notMem_empty _
      | simp)
  have hpar0 : ∀ w ∈ (G.verticesUpTo 0).toList, G.parents w ⊆ (∅ : Finset V) := by
    intro w hw
    have hw2 : w ∈ G.verticesUpTo 0 := by simpa using hw
    have hr0 : G.rank w = 0 := by
      apply Nat.le_zero.mp
      simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
      exact hw2
    simp [G.parents_empty_of_rank_zero hr0]
  have hLR2 : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
    intro x _
    have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  obtain ⟨F0, Gf0, hF0⟩ := extendOverList_factorizes M (L ∪ Z) (R ∪ Z) ∅ hbase
    (G.verticesUpTo 0).toList hpar0 hLR2 (Finset.nodup_toList _)
    (fun w _ => by simp) (fun w _ => hclique w)
  have hS : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset = G.verticesUpTo 0 := by simp
  have hT := transport_factorization _ _ _ _ hS F0 Gf0 _ _ _ hF0
  simp only [eqRec_eq_cast] at hT
  trace_state
  trivial
