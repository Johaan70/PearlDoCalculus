import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical

lemma cast_eq_iff_eq_cast_symm {A B : Sort _} (h : A = B) (b : A) (a : B) :
    (cast h b = a) ↔ (b = cast h.symm a) := by
  subst h
  simp

example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    {G : DAG V} (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hv : v ∉ B ∪ vs.toFinset)
    (a : Assignment (α := α) (B ∪ (v :: vs).toFinset)) :
    (extendOverList M B base (v :: vs) hpar) a = 0 := by
  have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
      = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
    congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
    tauto
  simp only [extendOverList, PMF.bind_apply, PMF.map_apply, eq_comm (a := a)]
  simp only [cast_eq_iff_heq]
  simp only [← cast_eq_iff_heq (e := htype)]
  simp only [cast_eq_iff_eq_cast_symm]
  simp only [extend_eq_iff _ v hv]
  trace_state
  simp only [ite_and, tsum_ite_eq]
  trace_state
  sorry
  sorry
