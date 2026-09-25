import PearlDoCalculus.Lauritzen

/-!
# Soundness of d-separation: final assembly

Chain: Lauritzen (graph) → separator_partition → joint_splits on the model
restricted to A = ancestors({x, y} ∪ Z) → condIndep_of_product_form →
decomposition to {x}, {y} → transfer back to M via marginal_eq_restricted_joint.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace DSepSound

universe u v
variable {V : Type u} [DecidableEq V] [Fintype V] {α : V → Type v} {G : DAG V}

/-- Every value type is inhabited: the model defines a distribution on assignments. -/
lemma nonempty_of_model (M : CausalModel G α) : ∀ w, Nonempty (α w) := by
  intro w
  obtain ⟨a, _⟩ := M.fullJoint.support_nonempty
  exact ⟨a ⟨w, Finset.mem_univ w⟩⟩

/-- Ancestor sets are closed under parents. -/
lemma A_closed (S : Finset V) :
    ∀ w ∈ ancestors G S, ∀ u, G.edge u w → u ∈ ancestors G S := by
  intro w hw u e
  rw [mem_ancestors_iff] at hw ⊢
  obtain ⟨s, hs, hr⟩ := hw
  exact ⟨s, hs, Relation.ReflTransGen.head e hr⟩

lemma union_subset_A (x y : V) (Z : Finset V) :
    {x} ∪ {y} ∪ Z ⊆ ancestors G (insert x (insert y Z)) := by
  intro v hv
  refine subset_ancestors (G := G) _ ?_
  simp only [Finset.mem_union, Finset.mem_singleton] at hv
  simp only [Finset.mem_insert]
  tauto

/-- Families of the restricted graph lie on one side of the separator. -/
lemma family_side {A L Z R : Finset V} (hA : ∀ w ∈ A, ∀ u, G.edge u w → u ∈ A)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hnoadj : ∀ u ∈ L, ∀ w ∈ R, ¬ (moralGraph G A).Adj u w) :
    ∀ w, insert w ((DAG.induce G A).parents w) ⊆ L ∪ Z ∨
         insert w ((DAG.induce G A).parents w) ⊆ R ∪ Z := by
  sorry

/-- `joint_splits` + `condIndep_of_product_form`: a family-respecting
    partition gives L ⊥ R | Z. -/
lemma condIndep_of_split {G' : DAG V} (M : CausalModel G' α) (L Z R : Finset V)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w, insert w (G'.parents w) ⊆ L ∪ Z ∨ insert w (G'.parents w) ⊆ R ∪ Z) :
    CondIndep M L R Z := by
  sorry

/-- Decomposition: independence passes to subsets. -/
lemma condIndep_mono {G' : DAG V} (M : CausalModel G' α) {X Y Z X' Y' : Finset V}
    (h : CondIndep M X Y Z) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    CondIndep M X' Y' Z := by
  sorry

lemma condIndep_of_mem_left (M : CausalModel G α) {x y : V} {Z : Finset V} (hx : x ∈ Z) :
    CondIndep M {x} {y} Z := by
  sorry

lemma condIndep_of_mem_right (M : CausalModel G α) {x y : V} {Z : Finset V} (hy : y ∈ Z) :
    CondIndep M {x} {y} Z := by
  sorry

/-- Transfer from the restricted model back to `M` (uses marginal_eq_restricted_joint). -/
lemma condIndep_transfer (M : CausalModel G α) (A : Finset V)
    (hA : ∀ w ∈ A, ∀ u, G.edge u w → u ∈ A) [∀ w, Nonempty (α w)]
    {X Y Z : Finset V} (h : CondIndep (CausalModel.restrictTo M A hA) X Y Z)
    (hsub : X ∪ Y ∪ Z ⊆ A) : CondIndep M X Y Z := by
  sorry

/-- **Soundness of d-separation.** -/
theorem dsep_sound (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y) : CondIndep M {x} {y} Z := by
  haveI : ∀ w, Nonempty (α w) := nonempty_of_model M
  by_cases hxZ : x ∈ Z
  · exact condIndep_of_mem_left M hxZ
  by_cases hyZ : y ∈ Z
  · exact condIndep_of_mem_right M hyZ
  have hA := A_closed (G := G) (insert x (insert y Z))
  have hsep := Lauritzen.moral_sep_of_dsep_lauritzen x y h
  obtain ⟨L, R, hxL, hyR, hLR, hLZ, hRZ, hcover, hnoadj⟩ :=
    separator_partition hsep hxZ hyZ
  have hci : CondIndep (CausalModel.restrictTo M _ hA) L R Z :=
    condIndep_of_split _ L Z R hLZ hLR hRZ.symm hcover (family_side hA hcover hnoadj)
  have hci' : CondIndep (CausalModel.restrictTo M _ hA) {x} {y} Z :=
    condIndep_mono _ hci (Finset.singleton_subset_iff.mpr hxL)
      (Finset.singleton_subset_iff.mpr hyR)
  exact condIndep_transfer M _ hA hci' (union_subset_A x y Z)

end DSepSound

#print axioms DSepSound.dsep_sound
