import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type}
    {G : DAG V} (M : CausalModel G α) (L R B : Finset V) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hLR : B ∪ (v :: vs).toFinset ⊆ L ∪ R)
    (hnodup : (v :: vs).Nodup)
    (hdisj : ∀ w ∈ (v :: vs), w ∉ B)
    (hclique : ∀ w ∈ (v :: vs), (insert w (G.parents w) ⊆ L) ∨ (insert w (G.parents w) ⊆ R))
    (ih : ∃ (F : Assignment (α := α) (L ∩ B) →
                Assignment (α := α) (L ∩ (B ∪ vs.toFinset)) → ENNReal)
           (Gf : Assignment (α := α) (R ∩ B) →
                 Assignment (α := α) (R ∩ (B ∪ vs.toFinset)) → ENNReal),
           ∀ (base : Assignment (α := α) B) (a : Assignment (α := α) (B ∪ vs.toFinset)),
             (extendOverList M B base vs (fun w hw => hpar w (List.mem_cons_of_mem v hw))) a =
               F (base.restrict Finset.inter_subset_right)
                 (a.restrict Finset.inter_subset_right) *
               Gf (base.restrict Finset.inter_subset_right)
                 (a.restrict Finset.inter_subset_right)) :
    ∃ (F : Assignment (α := α) (L ∩ B) →
           Assignment (α := α) (L ∩ (B ∪ (v :: vs).toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) →
            Assignment (α := α) (R ∩ (B ∪ (v :: vs).toFinset)) → ENNReal),
      ∀ (base : Assignment (α := α) B)
        (a : Assignment (α := α) (B ∪ (v :: vs).toFinset)),
        (extendOverList M B base (v :: vs) hpar) a =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  obtain ⟨F0, Gf0, hF0⟩ := ih
  rcases hclique v List.mem_cons_self with hcl | hcl
  · refine ⟨fun bp p => F0 bp (p.restrict (inter_mono_cons L B v vs)) *
      (M.kernel v (p.restrict (parents_subset_inter L B v vs (hpar v List.mem_cons_self) hcl)))
        (p ⟨v, self_mem_inter L B v vs hcl⟩),
      fun bq q => Gf0 bq (q.restrict (inter_mono_cons R B v vs)), ?_⟩
    intro base a
    have hv : v ∉ B ∪ vs.toFinset := by
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact hdisj v List.mem_cons_self h
      · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
    have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
        = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
      congr 1
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    have hab : a = cast htype (cast htype.symm a) := by simp
    rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a), hF0]
    simp only [Assignment.restrict_restrict]
    simp only [cast_cast, cast_eq]
    simp only [Assignment.restrict]
    rw [restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
      restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
      restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
    all_goals first
      | (intro x hx; simp at hx ⊢; tauto)
      | (ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
      | skip
    ring
  · sorry
