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
  intro w
  by_cases hw : w ∈ A
  · rw [DAG.induce_parents_eq A hA w hw]
    have hpa : ∀ u ∈ G.parents w, u ∈ A :=
      fun u hu => hA w hw u (by simpa [DAG.parents] using hu)
    have hcl := moral_family_clique A w hw hpa
    by_contra hne
    rw [not_or] at hne
    obtain ⟨h1, h2⟩ := hne
    rw [Finset.not_subset] at h1 h2
    obtain ⟨u, hu, huLZ⟩ := h1
    obtain ⟨u', hu', huRZ⟩ := h2
    have huR : u ∈ R := by
      have hmem : u ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ u
      simp only [Finset.mem_union] at hmem huLZ
      tauto
    have huL : u' ∈ L := by
      have hmem : u' ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ u'
      simp only [Finset.mem_union] at hmem huRZ
      tauto
    have hne' : u' ≠ u := by
      rintro rfl
      simp only [Finset.mem_union] at huRZ
      exact huRZ (Or.inl huR)
    exact hnoadj u' huL u huR (hcl (Finset.mem_coe.mpr hu') (Finset.mem_coe.mpr hu) hne')
  · have hempty : (DAG.induce G A).parents w = ∅ := by
      ext u
      simp [DAG.parents, DAG.induce, hw]
    rw [hempty]
    have hmem : w ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ w
    simp only [Finset.mem_union] at hmem
    rcases hmem with (h | h) | h
    · left; simp [h]
    · left; simp [h]
    · right; simp [h]

/-- `joint_splits` + `condIndep_of_product_form`: a family-respecting
    partition gives L ⊥ R | Z. -/
lemma condIndep_of_split {G' : DAG V} (M : CausalModel G' α) (L Z R : Finset V)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w, insert w (G'.parents w) ⊆ L ∪ Z ∨ insert w (G'.parents w) ⊆ R ∪ Z) :
    CondIndep M L R Z := by
  obtain ⟨F, Gf, hF⟩ := joint_splits M L Z R hLZ hLR hZR hcover hclique
  refine condIndep_of_product_form M L R Z hLR hLZ hZR.symm
    (fun a => F (a.restrict Finset.subset_union_left) (a.restrict Finset.subset_union_right))
    (fun b => Gf (b.restrict Finset.subset_union_left) (b.restrict Finset.subset_union_right))
    F Gf (fun _ => rfl) (fun _ => rfl) ?_
  intro w
  rw [hF w]
  simp only [Assignment.restrict_restrict]

/-- Decomposition: independence passes to subsets. -/
lemma condIndep_mono {G' : DAG V} (M : CausalModel G' α) {X Y Z X' Y' : Finset V}
    (h : CondIndep M X Y Z) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    CondIndep M X' Y' Z := by
  sorry

/-- If `T ⊆ S ⊆ T`, restriction from `S` to `T` loses nothing. -/
lemma restrict_injective_of_subset {S T : Finset V} (h : T ⊆ S) (h' : S ⊆ T) :
    Function.Injective (Assignment.restrict (α := α) h) := by
  intro a b e
  funext v
  exact congrFun e ⟨v.1, h' v.2⟩

/-- For an injective restriction, the marginal on `T` at `a|_T` equals the
    marginal on `S` at `a`: only one term of the sum is nonzero. -/
lemma marginal_restrict_of_injective {G' : DAG V} (M : CausalModel G' α) {S T : Finset V}
    (h : T ⊆ S) (hinj : Function.Injective (Assignment.restrict (α := α) h))
    (a : Assignment (α := α) S) :
    (M.marginal T) (a.restrict h) = (M.marginal S) a := by
  rw [← marginal_restrict M h, PMF.map_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    have hne : a.restrict h ≠ b.restrict h := fun e => hb (hinj e).symm
    simp [hne]

lemma condIndep_of_mem_left (M : CausalModel G α) {x y : V} {Z : Finset V} (hx : x ∈ Z) :
    CondIndep M {x} {y} Z := by
  have h1 : {x} ∪ {y} ∪ Z ⊆ {y} ∪ Z := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
    rcases hv with (rfl | rfl) | hv
    · exact Or.inr hx
    · exact Or.inl rfl
    · exact Or.inr hv
  have h2 : {x} ∪ Z ⊆ Z := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact hx
    · exact hv
  intro w
  rw [← marginal_restrict_of_injective M (subset_union3_mid_right {x} {y} Z)
      (restrict_injective_of_subset _ h1) w,
    ← marginal_restrict_of_injective M (Finset.subset_union_right : Z ⊆ {x} ∪ Z)
      (restrict_injective_of_subset _ h2) (w.restrict (subset_union3_left_right {x} {y} Z))]
  simp only [Assignment.restrict_restrict]
  ring

lemma condIndep_of_mem_right (M : CausalModel G α) {x y : V} {Z : Finset V} (hy : y ∈ Z) :
    CondIndep M {x} {y} Z := by
  have h1 : {x} ∪ {y} ∪ Z ⊆ {x} ∪ Z := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
    rcases hv with (rfl | rfl) | hv
    · exact Or.inl rfl
    · exact Or.inr hy
    · exact Or.inr hv
  have h2 : {y} ∪ Z ⊆ Z := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact hy
    · exact hv
  intro w
  rw [← marginal_restrict_of_injective M (subset_union3_left_right {x} {y} Z)
      (restrict_injective_of_subset _ h1) w,
    ← marginal_restrict_of_injective M (Finset.subset_union_right : Z ⊆ {y} ∪ Z)
      (restrict_injective_of_subset _ h2) (w.restrict (subset_union3_mid_right {x} {y} Z))]
  simp only [Assignment.restrict_restrict]

/-- On subsets of `A`, `M` and the restricted model have the same marginals. -/
lemma marginal_eq_of_subset_A (M : CausalModel G α) (A : Finset V)
    (hA : ∀ w ∈ A, ∀ u, G.edge u w → u ∈ A) [∀ w, Nonempty (α w)]
    {S : Finset V} (hS : S ⊆ A) :
    M.marginal S = (CausalModel.restrictTo M A hA).marginal S := by
  have hAeq : M.marginal A = (CausalModel.restrictTo M A hA).marginal A :=
    PMF.ext (marginal_eq_restricted_joint M A hA)
  rw [← marginal_restrict M hS, ← marginal_restrict (CausalModel.restrictTo M A hA) hS, hAeq]

/-- Transfer from the restricted model back to `M` (uses marginal_eq_restricted_joint). -/
lemma condIndep_transfer (M : CausalModel G α) (A : Finset V)
    (hA : ∀ w ∈ A, ∀ u, G.edge u w → u ∈ A) [∀ w, Nonempty (α w)]
    {X Y Z : Finset V} (h : CondIndep (CausalModel.restrictTo M A hA) X Y Z)
    (hsub : X ∪ Y ∪ Z ⊆ A) : CondIndep M X Y Z := by
  have hZ : Z ⊆ A := (subset_union3_right X Y Z).trans hsub
  have hXZ : X ∪ Z ⊆ A := (subset_union3_left_right X Y Z).trans hsub
  have hYZ : Y ∪ Z ⊆ A := (subset_union3_mid_right X Y Z).trans hsub
  intro w
  have h1 := h w
  rw [← marginal_eq_of_subset_A M A hA hsub, ← marginal_eq_of_subset_A M A hA hZ,
    ← marginal_eq_of_subset_A M A hA hXZ, ← marginal_eq_of_subset_A M A hA hYZ] at h1
  exact h1

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
