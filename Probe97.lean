import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    {G : DAG V} (M : CausalModel G α) (L Z R : Finset V)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) (L ∩ G.verticesUpTo 0) →
           Assignment (α := α) (Z ∩ G.verticesUpTo 0) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ G.verticesUpTo 0) →
            Assignment (α := α) (Z ∩ G.verticesUpTo 0) → ENNReal),
      ∀ a : Assignment (α := α) (G.verticesUpTo 0),
        (jointUpTo M 0) a =
          F (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) *
          Gf (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) := by
  have hLR2 : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
    intro x _
    have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  obtain ⟨F0, Gf0, hF0⟩ := extendOverList_factorizes M (L ∪ Z) (R ∪ Z) ∅
    (fun v => absurd (jointUpTo._proof_2 v) (jointUpTo._proof_3 v))
    (G.verticesUpTo 0).toList jointUpTo._proof_4 hLR2 (Finset.nodup_toList _)
    (fun w _ => by simp) (fun w _ => hclique w)
  refine ⟨fun p q => F0 (joinInter L Z _ (by simpa using p) (by simpa using q)),
    fun p q => Gf0 (joinInter R Z _ (by simpa using p) (by simpa using q)), ?_⟩
  intro a
  rw [jointUpTo_zero_apply, hF0]
  congr 1
  · simp [joinInter_restrict, restrict_cast_eq]
  · simp [joinInter_restrict, restrict_cast_eq]
