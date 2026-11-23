import PearlDoCalculus.Identification.CFactor

/-!
# Tian's theorem for sets, factorization over many blocks, and `Q[S]` as a causal effect

This file extends Tian's identification theorem from one node `x` to a set `X` of observed
nodes. It factorizes the distribution over many blocks (line 4 of the ID algorithm),
gives Tian's theorem for sets with one sum per c-component, shows that each factor is a
causal effect (`Q[S] = P_{do(O ∖ S)}`), and derives the theorem for one closed block
around `X` as a corollary.

Why it is needed: the factorization over many blocks and the factors of an intervention
model (`IsLatClosed`, `Q_empty`, `Q_split_rel`, `Q_prod_rel`, `marginal_prod`, `Q_do_gen`,
`lat_one`) are what `Identification/Identify` and `Identification/IdSound` use for Tian's
IDENTIFY and the soundness of the ID algorithm. `tian_identifiable_sets` is
the general form of Tian's theorem (used by `Examples/IdRecursion`), and `ccomp_eq_of_mem`
is used by `IdSound` and `Hedge/FromID`.

How the proofs go: as in `Identification/CFactor`, with a sum over all values of `X`
instead of over one value `x` (`sum_Q_updX`, by `sum_assign_prod`: summed over all
assignments of `X`, a product of distributions is 1). The factorization over many blocks
is induction over the blocks with the split into two (`Q_split_rel`). With one block per
c-component, every block gets its own sum over the values of `X` in it, so only children
of `x` in its *own* c-component matter (`tian_formula_blocks`). That `Q[S]` is a causal
effect follows from the factorization of the intervention model, where the factor of the
latents outside `S` sums to 1 (`lat_one`).

Main results: `Identification.CFactor.tian_identifiable_sets`,
`Identification.CFactor.tian_identifiable_set_of_closed`,
`Identification.CFactor.tian_identifiable_set_ccomp`, `Identification.CFactor.marginal_prod`
and `Identification.CFactor.Q_causal`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Summing out a set `X`

The same proof as for one `x` (`Identification/CFactor`), with a sum over all values of
`X` instead of over `x`. Let `X ⊆ S` be observed, `S` a closed block, and let no node of
`X` have a child in `S`. Then

  `P_X(a) = [a_X = x] · (Σ_{x'} Q[S](a[X := x'])) · Q[Sᶜ](a)`,

and the effect of `X` is identifiable. (The theorems themselves are at the end of the
file, as corollaries of `tian_identifiable_sets`; this section holds only the lemmas.)

The only new ingredient is `sum_assign_prod`: the sum over all assignments of `X` of a
product of kernels is the product of the sums (`Fintype.prod_sum`), so 1. With
c-components: choose `S` as the union of the c-components of the nodes of `X`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **The product of the sums.** Summed over all assignments of `X`, a product of
probability distributions is 1. -/
lemma sum_assign_prod (M : G.CausalModel α) (X : Finset V)
    (K : ∀ v : {v // v ∈ X}, PMF (α v.1)) :
    ∑' x' : Assignment (α := α) X, ∏ v : {v // v ∈ X}, K v (x' v) = 1 := by
  haveI : ∀ v, Fintype (α v) := M.fin
  show ∑' x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v) = 1
  calc ∑' x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v)
      = ∑ x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v) := tsum_fintype _
    _ = ∏ v : {v // v ∈ X}, ∑ t : α v.1, K v t := (Fintype.prod_sum (fun v t => K v t)).symm
    _ = 1 := Finset.prod_eq_one (fun v _ => by
        calc ∑ t : α v.1, K v t = ∑' t : α v.1, K v t := (tsum_fintype _).symm
          _ = 1 := (K v).tsum_coe)

/-- **`X` is summed out.** If no node of `X` has a child in `S`, summing `Q[S]` over the
values of `X` removes the kernels of `X`. -/
theorem sum_Q_updX [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S X : Finset V)
    (hXO : X ⊆ Uᶜ) (hXS : X ⊆ S) (hch : ∀ x ∈ X, ∀ v ∈ S, ¬ G.edge x v)
    (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) X, Q M U S (updX U X a x') =
      ∑' w : Assignment (α := α) (U ∩ S), ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := by
  unfold Q
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun w => ?_)
  have hrest : ∀ x' : Assignment (α := α) X,
      ∏ v ∈ S \ X, kfac M Finset.univ (fill U S (updX U X a x') w) v =
        ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := fun x' =>
    Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
      (fill_updX_apply_of_notMem U S X a x' w v (Finset.mem_sdiff.mp hv).2)
      (fun u hu => fill_updX_apply_of_notMem U S X a x' w u
        (fun huX => hch u huX v (Finset.mem_sdiff.mp hv).1 (DAG.mem_parents.mp hu))))
  have hxk : ∀ x' : Assignment (α := α) X,
      ∏ v ∈ X, kfac M Finset.univ (fill U S (updX U X a x') w) v =
        ∏ v : {v // v ∈ X}, M.kernel v.1
          ((fill U S a w).restrict (Finset.subset_univ _)) (x' v) := by
    intro x'
    rw [← Finset.prod_coe_sort X]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    have hr : (fill U S (updX U X a x') w).restrict (Finset.subset_univ (G.parents v.1)) =
        (fill U S a w).restrict (Finset.subset_univ (G.parents v.1)) := by
      funext ⟨u, hu⟩
      exact fill_updX_apply_of_notMem U S X a x' w u
        (fun huX => hch u huX v.1 (hXS v.2) (DAG.mem_parents.mp hu))
    rw [kfac_univ, hr,
      fill_updX_apply_of_mem U S X a x' w v.1 v.2 (Finset.mem_compl.mp (hXO v.2))]
  have hSX : S ∩ X = X := Finset.inter_eq_right.mpr hXS
  calc ∑' x' : Assignment (α := α) X, ∏ v ∈ S, kfac M Finset.univ (fill U S (updX U X a x') w) v
      = ∑' x' : Assignment (α := α) X,
          (∏ v : {v // v ∈ X}, M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _)) (x' v)) *
            ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v :=
        tsum_congr (fun x' => by
          rw [← Finset.prod_inter_mul_prod_diff S X, hSX, hxk x', hrest x'])
    _ = (∑' x' : Assignment (α := α) X,
          ∏ v : {v // v ∈ X}, M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _)) (x' v)) *
            ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := ENNReal.tsum_mul_right
    _ = _ := by
        rw [sum_assign_prod M X
          (fun v => M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _))), one_mul]

end CFactor
end Identification

/-! ## Factorization over many blocks (line 4 of the ID algorithm)

`Identification/CFactor` split into two blocks, `S` and `Sᶜ`. The ID algorithm needs one
factor per c-component. Here:

1. `Q_split_rel`: for a set `T` that contains its latent parents (`IsLatClosed`) and a
   block `S` closed inside `T` (no latent edge into `T` crosses its boundary),
   `Q[T] = Q[T ∩ S] · Q[T ∩ Sᶜ]`. Pure algebra: the sum over the latents in `T` splits
   in two (`tsum_eq_tsum_joinBlocks`), and so does the product over `T`. `Q_split` is
   the case of a closed block `S`.
2. `marginal_eq_Q`: `P(O) = Q[V]`.
3. `Q_prod_rel`: for pairwise disjoint blocks `B i`, `i ∈ I`, closed inside a set
   `T₀ ⊇ T`, that cover `T`, `Q[T] = ∏_{i ∈ I} Q[T ∩ B i]`. Induction over `I` with
   `Q_split_rel`. `Q_prod` is the case `T₀ = V` (closed blocks); the blocks closed only
   inside an ancestral set are what line 2 of the ID algorithm needs (`IdSound`).
4. `marginal_prod`: `P(O) = ∏_i Q[B i]` when the blocks cover all nodes. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `T` contains all its latent parents. -/
def IsLatClosed (G : DAG V) (U T : Finset V) : Prop :=
  ∀ v ∈ T, ∀ u ∈ U, G.edge u v → u ∈ T

/-- The factor of the empty set is 1. -/
lemma Q_empty [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : Q M U ∅ a = 1 := by
  unfold Q
  simp only [Finset.prod_empty]
  have w0 : Assignment (α := α) (U ∩ ∅) := fun v => absurd v.2 (by simp)
  have hw : ∀ w w' : Assignment (α := α) (U ∩ ∅), w = w' :=
    fun w w' => funext (fun v => absurd v.2 (by simp))
  exact tsum_eq_single w0 (fun w hw' => absurd (hw w w0) hw')

/-- **Two blocks inside `T`, the block closed only inside `T`.** If `T` contains its latent
parents and no latent edge into `T` crosses the boundary of `S`, then
`Q[T] = Q[T ∩ S] · Q[T ∩ Sᶜ]`. -/
theorem Q_split_rel [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (a : Assignment (α := α) Uᶜ) :
    Q M U T a = Q M U (T ∩ S) a * Q M U (T ∩ Sᶜ) a := by
  have h2 : ∀ w1 w2, ∏ v ∈ T, kfac M Finset.univ (fill U T a (joinBlocks U T S w1 w2)) v =
      (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
        ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ (fill U (T ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl T S]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_joinBlocks_apply_left U T S a w1 w2 v (fun _ => hv))
        (fun u hu => fill_joinBlocks_apply_left U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (DAG.mem_parents.mp hu),
              (hcl u hu0 v (Finset.mem_inter.mp hv).1 (DAG.mem_parents.mp hu)).mpr
                (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_joinBlocks_apply_right U T S a w1 w2 v (fun _ => hv))
        (fun u hu => fill_joinBlocks_apply_right U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (DAG.mem_parents.mp hu),
              Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
                ((hcl u hu0 v (Finset.mem_inter.mp hv).1 (DAG.mem_parents.mp hu)).mp hus))⟩)))
  unfold Q
  rw [tsum_eq_tsum_joinBlocks U T S]
  simp only [h2]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **Two blocks inside `T`.** If `T` contains its latent parents and `S` is closed, then
`Q[T] = Q[T ∩ S] · Q[T ∩ Sᶜ]`. -/
theorem Q_split [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : IsClosedBlock G U S) (a : Assignment (α := α) Uᶜ) :
    Q M U T a = Q M U (T ∩ S) a * Q M U (T ∩ Sᶜ) a :=
  Q_split_rel M U T S hT (fun u hu v _ e => hcl u hu v e) a

/-- `P(O) = Q[V]`. -/
theorem marginal_eq_Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : M.marginal Uᶜ a = Q M U Finset.univ a := by
  rw [marginal_factor M U Finset.univ (fun _ _ _ _ => by simp) a, Finset.compl_univ,
    Q_empty, mul_one]

/-- **Product over blocks that are closed only inside `T₀`.** For pairwise disjoint blocks
closed inside `T₀` that cover `T ⊆ T₀`, `Q[T]` is the product of the factors `Q[T ∩ B i]`. -/
theorem Q_prod_rel [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι) (T0 : Finset V) :
    ∀ T : Finset V, T ⊆ T0 → IsLatClosed G U T →
      (∀ i ∈ I, ∀ u ∈ U, ∀ v ∈ T0, G.edge u v → (u ∈ B i ↔ v ∈ B i)) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k)) → T ⊆ I.biUnion B →
      ∀ a, Q M U T a = ∏ i ∈ I, Q M U (T ∩ B i) a := by
  induction I using Finset.induction_on with
  | empty =>
    intro T _ _ _ _ hTI a
    have hT0 : T = ∅ := by simpa using hTI
    rw [hT0, Finset.prod_empty, Q_empty]
  | insert j I' hj ih =>
    intro T hTT0 hT hcl hdisj hTI a
    have hclj : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ B j ↔ v ∈ B j) :=
      fun u hu v hv e => hcl j (Finset.mem_insert_self j I') u hu v (hTT0 hv) e
    rw [Finset.prod_insert hj, Q_split_rel M U T (B j) hT hclj a]
    congr 1
    have hT' : IsLatClosed G U (T ∩ (B j)ᶜ) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        Finset.mem_compl.mpr (fun huB => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
          ((hclj u hu v (Finset.mem_inter.mp hv).1 e).mp huB))⟩
    have hTI' : T ∩ (B j)ᶜ ⊆ I'.biUnion B := by
      intro v hv
      obtain ⟨hvT, hvB⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hTI hvT)
      rcases Finset.mem_insert.mp hi with hij | hi'
      · rw [hij] at hvi
        exact absurd hvi (Finset.mem_compl.mp hvB)
      · exact Finset.mem_biUnion.mpr ⟨i, hi', hvi⟩
    rw [ih (T ∩ (B j)ᶜ) (fun v hv => hTT0 (Finset.mem_inter.mp hv).1) hT'
      (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
      (fun i hi k hk => hdisj i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
      hTI' a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hne : i ≠ j := fun e => hj (e ▸ hi)
    have hs : T ∩ (B j)ᶜ ∩ B i = T ∩ B i := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_compl]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, fun h2 => Finset.disjoint_left.mp
          (hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j I') hne) h3 h2⟩, h3⟩
    rw [hs]

/-- **Factorization over many blocks.** For pairwise disjoint closed blocks that cover `T`,
`Q[T]` is the product of the factors `Q[T ∩ B i]`. -/
theorem Q_prod [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι) :
    ∀ T : Finset V, IsLatClosed G U T → (∀ i ∈ I, IsClosedBlock G U (B i)) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k)) → T ⊆ I.biUnion B →
      ∀ a, Q M U T a = ∏ i ∈ I, Q M U (T ∩ B i) a :=
  fun T hT hcl hdisj hTI =>
    Q_prod_rel M U B I Finset.univ T (Finset.subset_univ T) hT
      (fun i hi u hu v _ e => hcl i hi u hu v e) hdisj hTI

/-- **`P(O)` is the product of the block factors**, for blocks that cover all nodes. -/
theorem marginal_prod [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (a : Assignment (α := α) Uᶜ) :
    M.marginal Uᶜ a = ∏ i ∈ I, Q M U (B i) a := by
  rw [marginal_eq_Q, Q_prod M U B I Finset.univ (fun _ _ _ _ _ => Finset.mem_univ _) hcl hdisj
    (fun v _ => Finset.mem_biUnion.mpr (hcov v)) a]
  simp only [Finset.univ_inter]

end CFactor
end Identification

/-! ## Tian's theorem for sets, one sum per c-component

The first section required that no node of `X` has a child in the *union* of the
c-components of `X`. That is too strict: in `x₁ → z ↔ x₂` with `X = {x₁, x₂}`, `x₁` has
a child in the c-component of `x₂`, but the effect is identifiable. Here every block gets
its own sum:

  `P_X(a) = ∏_i [a_{X ∩ Bᵢ} = x] · Σ_{x'} Q[Bᵢ](a[X ∩ Bᵢ := x'])`   (`tian_formula_blocks`).

Kernels in `Bᵢ` that read nodes of `X` outside `Bᵢ` see only the fixed values. So the
condition is only that no `x ∈ X` has a child in *its own* c-component
(`tian_identifiable_sets`). For one `x` this is exactly the condition of `tian_iff`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- The factor of a block `T` in the intervention model, for any `X`: the indicator of the
values on `T ∩ X`, times the factor of `T` without the kernels of `X`. -/
theorem Q_do_gen [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T X : Finset V)
    (hXO : X ⊆ Uᶜ) (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M X xv) U T a =
      (∏ v : {v // v ∈ T ∩ X}, if a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
        xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) *
      ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T \ X, kfac M Finset.univ (fill U T a w) v := by
  unfold Q
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun w => ?_)
  rw [← Finset.prod_inter_mul_prod_diff T X]
  congr 1
  · rw [← Finset.prod_coe_sort (T ∩ X)]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [kfac_doModel, dif_pos (Finset.mem_inter.mp v.2).2]
    have hf := fill_x U T (Finset.mem_compl.mp (hXO (Finset.mem_inter.mp v.2).2)) a w
    by_cases h : a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
        xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ <;> simp [hf, h]
  · exact Finset.prod_congr rfl (fun v hv => by
      rw [kfac_doModel, dif_neg (Finset.mem_sdiff.mp hv).2])

/-- The sum over the values of `X ∩ T` removes the kernels of `X ∩ T` from `Q[T]`. -/
lemma sum_block [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T X : Finset V)
    (hXO : X ⊆ Uᶜ) (hch : ∀ x ∈ T ∩ X, ∀ v ∈ T, ¬ G.edge x v) (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) (T ∩ X), Q M U T (updX U (T ∩ X) a x') =
      ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T \ X, kfac M Finset.univ (fill U T a w) v := by
  rw [sum_Q_updX M U T (T ∩ X) (fun v hv => hXO (Finset.mem_inter.mp hv).2)
    Finset.inter_subset_left hch a, Finset.sdiff_inter_self_left]

/-- **The formula with one sum per block.** If no node of `X` has a child in its own block,
then `P_X(a) = ∏_i [a_{X ∩ Bᵢ} = x] · Σ_{x'} Q[Bᵢ](a[X ∩ Bᵢ := x'])`. -/
theorem tian_formula_blocks [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι]
    (M : G.CausalModel α) (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (X : Finset V) (hXO : X ⊆ Uᶜ)
    (hch : ∀ i ∈ I, ∀ x ∈ B i ∩ X, ∀ v ∈ B i, ¬ G.edge x v)
    (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    (doModel M X xv).marginal Uᶜ a =
      ∏ i ∈ I, ((∏ v : {v // v ∈ B i ∩ X}, if a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
          xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) *
        ∑' x' : Assignment (α := α) (B i ∩ X), Q M U (B i) (updX U (B i ∩ X) a x')) := by
  rw [marginal_prod (doModel M X xv) U B I
    (fun i hi => by
      intro u hu v e
      exact hcl i hi u hu v (show G.edge u v ∧ v ∉ X from e).1) hdisj hcov a]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Q_do_gen M U (B i) X hXO xv a, sum_block M U (B i) X hXO (hch i hi) a]

/-- **Identifiability with blocks.** For pairwise disjoint closed blocks that cover all
nodes, if no node of `X` has a child in its own block, then the effect of `X` on any set
`Y` of observed nodes is identifiable. -/
theorem tian_identifiable_blocks [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι]
    (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (X : Finset V) (hXO : X ⊆ Uᶜ)
    (hch : ∀ i ∈ I, ∀ x ∈ B i ∩ X, ∀ v ∈ B i, ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hQ : ∀ i ∈ I, ∀ b, Q M1 U (B i) b = Q M2 U (B i) b := fun i hi b =>
    (Q_identifiable M1 M2 U (B i) (hcl i hi) hM hpos b).1
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Uᶜ = (doModel M2 X xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [tian_formula_blocks M1 U B I hcl hdisj hcov X hXO hch xv a,
      tian_formula_blocks M2 U B I hcl hdisj hcov X hXO hch xv a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [hQ i hi]
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

/-- A latent step can be taken in either direction. -/
lemma latStep_symm {U : Finset V} {a b : V} (h : latStep G U a b) : latStep G U b a :=
  Or.symm h

/-- Two nodes in the same c-component have the same c-component. -/
lemma ccomp_eq_of_mem {U : Finset V} {x v : V} (h : v ∈ ccomp G U x) :
    ccomp G U v = ccomp G U x := by
  have hsymm : Symmetric (Relation.ReflTransGen (latStep G U)) :=
    Relation.ReflTransGen.symmetric (fun _ _ h => latStep_symm h)
  have hxv := mem_ccomp.mp h
  ext w
  rw [mem_ccomp, mem_ccomp]
  exact ⟨fun hvw => hxv.trans hvw, fun hxw => (hsymm hxv).trans hxw⟩

/-- **Tian's theorem for sets.** If no `x ∈ X` has a child in its own c-component, then
the effect of `X` on any set `Y` of observed nodes is identifiable. -/
theorem tian_identifiable_sets [∀ v, Nonempty (α v)] (U X : Finset V)
    (hX : ∀ x ∈ X, x ∉ U) (hch : ∀ x ∈ X, ∀ v ∈ ccomp G U x, ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine tian_identifiable_blocks U id (Finset.univ.image (ccomp G U)) ?_ ?_ ?_ X
    (fun x hx => Finset.mem_compl.mpr (hX x hx)) ?_ Y hY
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed G U y
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v
    exact ⟨ccomp G U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, self_mem_ccomp G U v⟩
  · intro i hi x hx v hv
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    have hxy : x ∈ ccomp G U y := (Finset.mem_inter.mp hx).1
    exact hch x (Finset.mem_inter.mp hx).2 v (by rw [ccomp_eq_of_mem hxy]; exact hv)

end CFactor
end Identification

/-! ## Every factor is a causal effect (`Q[S] = P_{do(O ∖ S)}`)

Lines 4 and 7 of the ID algorithm call the algorithm again on the factors `Q[Sᵢ]`. That
only makes sense because every factor is a causal effect: if all observed nodes outside a
closed block `S` are held fixed, the distribution on the observed nodes is exactly `Q[S]`
(`Q_causal`):

  `P_{do(X = x)}(O = a) = [a_X = x] · Q[S](a)`,   `X = Sᶜ ∖ U`.

1. `lat_one`: summed over the latents of a set, the product of their kernels is 1. This
   follows directly from `sum_compl_kfac_eq_one` (the chain rule) by recounting
   (`fill_iff`, with the one-part split `ENNReal.tsum_ite_eq_tsum_of_iff`).
2. In the intervention model the factor of `S` is unchanged, and the factor of `Sᶜ` is
   the indicator of `X` times the kernels of the latents in `Sᶜ`, which sum to 1. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Outside the latents of `T`, the filled assignment does not depend on the latent values `w`. -/
lemma fill_out [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w w' : Assignment (α := α) (U ∩ T)) (v : V) (hv : v ∉ U ∩ T) :
    fill U T a w ⟨v, Finset.mem_univ v⟩ = fill U T a w' ⟨v, Finset.mem_univ v⟩ := by
  by_cases h0 : v ∈ U
  · have hT : v ∉ T := fun h => hv (Finset.mem_inter.mpr ⟨h0, h⟩)
    simp [fill, h0, hT]
  · simp [fill, h0]

/-- A full assignment is `fill U T a w` exactly when it agrees with `fill` outside the
latents of `T` and `w` is its restriction to them. -/
lemma fill_iff [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w0 w : Assignment (α := α) (U ∩ T)) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    u = fill U T a w ↔
      u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
        (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ) ∧
      w = u.restrict (Finset.subset_univ (U ∩ T)) := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict]
      exact fill_out U T a w w0 v (Finset.mem_compl.mp hv)
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      simp [fill, Assignment.restrict, h0, h1]
  · rintro ⟨hb, rfl⟩
    funext ⟨v, _⟩
    by_cases hv : v ∈ U ∩ T
    · obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      simp [fill, Assignment.restrict, h0, h1]
    · have e := congrFun hb ⟨v, Finset.mem_compl.mpr hv⟩
      simp only [Assignment.restrict] at e
      rw [e]
      exact fill_out U T a w0 _ v hv

/-- **The latents sum to 1:** summed over the latent values in `T`, the product of their kernels
is 1. -/
theorem lat_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) :
    ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ U ∩ T, kfac M Finset.univ (fill U T a w) v = 1 := by
  have w0 : Assignment (α := α) (U ∩ T) := fun _ => Classical.arbitrary _
  have key := sum_compl_kfac_eq_one M (U ∩ T)ᶜ
    ((fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ))
  rw [compl_compl] at key
  refine Eq.trans ?_ key
  symm
  refine (tsum_congr fun u => ?_).trans (ENNReal.tsum_ite_eq_tsum_of_iff _ _ _ _
    (fun u w => (fill_iff U T a w0 w u).trans (and_congr_left' eq_comm))
    (fun u => ∏ v ∈ U ∩ T, kfac M Finset.univ u v))
  rw [ite_mul, one_mul, zero_mul]
  exact if_congr eq_comm rfl rfl

/-- **Every factor is a causal effect.** If the observed nodes outside a closed block `S`
are held fixed, the distribution on the observed nodes is the indicator times `Q[S]`. -/
theorem Q_causal [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V)
    (hcl : IsClosedBlock G U S) (xv : Assignment (α := α) (Sᶜ \ U))
    (a : Assignment (α := α) Uᶜ) :
    (doModel M (Sᶜ \ U) xv).marginal Uᶜ a =
      (∏ v : {v // v ∈ Sᶜ ∩ (Sᶜ \ U)},
        if a ⟨v.1, (show Sᶜ \ U ⊆ Uᶜ from fun _ hz =>
            Finset.mem_compl.mpr (Finset.mem_sdiff.mp hz).2) (Finset.mem_inter.mp v.2).2⟩ =
          xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) * Q M U S a := by
  have hXO : Sᶜ \ U ⊆ Uᶜ := fun _ hz => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hz).2
  have hcl' : IsClosedBlock (cutIn G (Sᶜ \ U)) U S := by
    intro u hu v e
    exact hcl u hu v (show G.edge u v ∧ v ∉ Sᶜ \ U from e).1
  have h1 : Q (doModel M (Sᶜ \ U) xv) U S a = Q M U S a := by
    unfold Q
    refine tsum_congr (fun w => Finset.prod_congr rfl (fun v hv => ?_))
    have hvX : v ∉ Sᶜ \ U := fun h =>
      (Finset.mem_compl.mp (Finset.mem_sdiff.mp h).1) hv
    rw [kfac_doModel, dif_neg hvX]
  have hset : Sᶜ \ (Sᶜ \ U) = U ∩ Sᶜ := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [marginal_factor (doModel M (Sᶜ \ U) xv) U S hcl' a, h1,
    Q_do_gen M U Sᶜ (Sᶜ \ U) hXO xv a, hset, lat_one, mul_one, mul_comm]

end CFactor
end Identification

/-! ## Tian's theorem for one closed block around `X`, as corollaries

`tian_identifiable_sets` is the general theorem for sets. The versions with one closed
block (from the first section) follow from it: a closed block `S ⊇ X` contains the
c-component of every `x ∈ X` (`ccomp_subset`), and the union of the c-components contains
each of them. The explicit formula for one block is not stated separately;
`tian_formula_blocks` and `Q_do_gen` cover it. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Tian's theorem for a set `X` in a closed block.** If no node of `X` has a child in
the closed block `S ⊇ X`, then the effect of `X` on any set `Y` of observed nodes is
identifiable. -/
theorem tian_identifiable_set_of_closed [∀ v, Nonempty (α v)] (U S X : Finset V)
    (hXO : X ⊆ Uᶜ) (hXS : X ⊆ S) (hch : ∀ x ∈ X, ∀ v ∈ S, ¬ G.edge x v)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X (fun _ hx => Finset.mem_compl.mp (hXO hx))
    (fun x hx v hv => hch x hx v (ccomp_subset hcl (hXS hx) hv)) Y hY

/-- **With the union of the c-components.** If no node of `X` has a child in the union of
the c-components of `X`, then the effect of `X` is identifiable. -/
theorem tian_identifiable_set_ccomp [∀ v, Nonempty (α v)] (U X : Finset V)
    (hX : ∀ x ∈ X, x ∉ U) (hch : ∀ x ∈ X, ∀ v ∈ X.biUnion (ccomp G U), ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X hX
    (fun x hx v hv => hch x hx v (Finset.mem_biUnion.mpr ⟨x, hx, hv⟩)) Y hY

end CFactor
end Identification
