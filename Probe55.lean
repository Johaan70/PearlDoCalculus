import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    {G : DAG V} (M : CausalModel G α) (L R B : Finset V)
    (base : Assignment (α := α) B)
    (hpar : ∀ w ∈ ([] : List V), G.parents w ⊆ B)
    (hLR : B ∪ ([] : List V).toFinset ⊆ L ∪ R) :
    ∃ (F : Assignment (α := α) (L ∩ (B ∪ ([] : List V).toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ (B ∪ ([] : List V).toFinset)) → ENNReal),
      ∀ a : Assignment (α := α) (B ∪ ([] : List V).toFinset),
        (extendOverList M B base [] hpar) a =
          F (a.restrict Finset.inter_subset_right) *
          Gf (a.restrict Finset.inter_subset_right) := by
  have hcast : Assignment (α := α) B = Assignment (α := α) (B ∪ ([] : List V).toFinset) := by simp
  refine ⟨fun p => if p = (cast hcast base).restrict Finset.inter_subset_right then 1 else 0,
          fun q => if q = (cast hcast base).restrict Finset.inter_subset_right then 1 else 0, ?_⟩
  intro a
  rw [extendOverList_nil]
  simp only []
  rw [assignment_eq_iff_inter L R _ hLR (cast hcast base) a]
  simp only [ite_and, mul_ite, mul_one, mul_zero, ite_self]
  split_ifs <;> simp_all
