import PearlDoCalculus.Identification.LatentSplit

/-!
# Tian's factorization and identification theorem (c-factor side, first part)

The positive side of the identification theory begins here. Let `U` be the latent
nodes and `O = Uᶜ` the observed ones. A block `S` is *closed* when every latent edge
`u → v` stays inside `S` or inside `Sᶜ`. Then the distribution on the observed nodes
factors with one factor `Q[S]` per block (Tian's lemma 1), the factors are identifiable
from `P(O)` (Tian's lemma 2), this gives Tian's identification theorem for one node `x`,
and the c-component is the smallest closed block.

Why it is needed: `Q[S]` and its factorization are the c-factor side of the whole
identification layer. `TianIff` uses `tian_identifiable_ccomp` for the positive half of
`tian_iff`; `CFactorSets`, `Identify` and `IdSound` build Tian's theorem for sets, Tian's
IDENTIFY and the soundness of the ID algorithm on `Q`, `marginal_factor`,
`Q_identifiable` and `ccomp`; `Verma` uses `anc_factor`, and `Hedge/FromID` uses
`latStep` and `ccomp`.

How the proofs go. *Factorization*: the marginal on the observed nodes of an ancestral set
`A` is a sum over the latent values in `A`; the closedness of `S` splits both the sum and
the product of kernel factors into a part for `A ∩ S` and one for `A ∩ Sᶜ`
(`Identification/LatentSplit`), and the sum of a product of independent parts is the
product of the sums. *Identifiability*: removing a node `v` of maximal rank from an
ancestral set `A` keeps it ancestral, and `Q_step` relates the factors before and after
by the observed marginals on `A` and `A ∖ {v}`; induction on `|A|` gives
`Q_identifiable`. *Tian's theorem*: under `do(x)` only `Q[S]` changes, and when no child
of `x` lies in `S`, summing `Q[S]` over the values of `x` removes exactly the kernel of
`x` (`sum_Q_upd`), which gives an explicit formula in terms of the two factors, both
determined by `P(O)` (`tian_formula`).

Main results:
* `CFactor.Q`, `CFactor.kfac_congr`: the factors and their basic facts. The full
  assignments the factors read (`fill`, `joinBlocks`) and how they split into their parts
  are in `Identification/LatentSplit`.
* `CFactor.anc_factor`, `CFactor.marginal_factor`, `CFactor.do_marginal_factor`: the
  factorization on an ancestral set, its case `A = univ`, and that an intervention in `S`
  changes only `Q[S]`.
* `CFactor.Q_identifiable`, `CFactor.Q_step`: the factors are determined by `P(O)`.
* `CFactor.tian_identifiable`, `CFactor.tian_identifiable_ccomp`: Tian's theorem.
* `CFactor.ccomp_isLeast`, `CFactor.tian_cond_iff`: the c-component is the smallest
  closed block, so Tian's condition is a condition on the c-component.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## C-component factorization (Tian's lemma 1)

The positive side begins here. Let `U` be the latent nodes and `O = Uᶜ` the observed ones.
A block `S` is *closed* when every latent edge `u → v` (`u ∈ U`) stays inside `S` or
inside `Sᶜ`. Then the distribution on the observed nodes factors with one factor per
block:

  `P(O = a) = Q[S](a) · Q[Sᶜ](a)`,   `Q[T](a) = Σ_{w latent in T} Π_{v ∈ T} P(v | pa(v))`.

Under an intervention in `S` only `Q[S]` changes; `Q[Sᶜ]` stays the same
(`do_marginal_factor`). This is the core of the ID algorithm. Tian requires the latents
to be roots; here only closedness is needed. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **The factor `Q[T]`:** the sum over the latent values in `T` of the product of the
kernel factors of the nodes of `T`, at the observed values `a`. -/
noncomputable def Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) : ENNReal :=
  ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T, kfac M Finset.univ (fill U T a w) v

/-- The kernel factor of `v` depends only on the values at `v` and at its parents. -/
lemma kfac_congr (M : G.CausalModel α) (s s' : Assignment (α := α) (Finset.univ : Finset V))
    (v : V) (hv : s ⟨v, Finset.mem_univ v⟩ = s' ⟨v, Finset.mem_univ v⟩)
    (hp : ∀ u ∈ G.parents v, s ⟨u, Finset.mem_univ u⟩ = s' ⟨u, Finset.mem_univ u⟩) :
    kfac M Finset.univ s v = kfac M Finset.univ s' v := by
  have hr : s.restrict (Finset.subset_univ (G.parents v)) =
      s'.restrict (Finset.subset_univ (G.parents v)) := by
    funext ⟨u, hu⟩
    exact hp u hu
  rw [kfac_univ, kfac_univ, hr, hv]

/-- **Factorization on an ancestral set.** For a closed block `S` and an ancestral set `A`,
`P(O ∩ A) = Q[A ∩ S] · Q[A ∩ Sᶜ]`. -/
theorem anc_factor [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U A S : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (a : Assignment (α := α) Uᶜ) :
    M.marginal (Uᶜ ∩ A) (a.restrict (compl_inter_subset_compl U A)) =
      Q M U (A ∩ S) a * Q M U (A ∩ Sᶜ) a := by
  have hpa : ∀ v ∈ A, G.parents v ⊆ A := DAG.parents_subset_of_closed hA
  -- 1. The marginal is a sum over the latent values in `A ∩ S` and in `A ∩ Sᶜ`
  have h1 : M.marginal (Uᶜ ∩ A) (a.restrict (compl_inter_subset_compl U A)) =
      ∑' w1 : Assignment (α := α) (U ∩ (A ∩ S)), ∑' w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)),
        ∏ v ∈ A, kfac M Finset.univ (fill U A a (joinBlocks U A S w1 w2)) v := by
    rw [← marginal_restrict M (compl_inter_subset U A), PMF.map_apply,
      ENNReal.tsum_ite_eq_tsum_tsum_of_iff _ _ _ _ _
        (fun b w1 w2 => eq_restrict_fill_joinBlocks_iff U A S a w1 w2 b)]
    refine tsum_congr (fun w1 => tsum_congr (fun w2 => ?_))
    rw [marginal_ancestral_apply M A hA]
    exact Finset.prod_congr rfl
      (fun v hv => kfac_restrict M (Finset.subset_univ A) _ hv (hpa v hv))
  -- 2. The product over `A` splits into the factors of the blocks
  have h2 : ∀ w1 w2, ∏ v ∈ A, kfac M Finset.univ (fill U A a (joinBlocks U A S w1 w2)) v =
      (∏ v ∈ A ∩ S, kfac M Finset.univ (fill U (A ∩ S) a w1) v) *
        ∏ v ∈ A ∩ Sᶜ, kfac M Finset.univ (fill U (A ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff A S, Finset.sdiff_eq_inter_compl]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_joinBlocks_apply_left U A S a w1 w2 v (fun _ => hv))
        (fun u hu => fill_joinBlocks_apply_left U A S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr ⟨hA v (Finset.mem_inter.mp hv).1 u (DAG.mem_parents.mp hu),
            (hcl u hu0 v (DAG.mem_parents.mp hu)).mpr (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_joinBlocks_apply_right U A S a w1 w2 v (fun _ => hv))
        (fun u hu => fill_joinBlocks_apply_right U A S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr ⟨hA v (Finset.mem_inter.mp hv).1 u (DAG.mem_parents.mp hu),
            Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
              ((hcl u hu0 v (DAG.mem_parents.mp hu)).mp hus))⟩)))
  -- 3. The sum of a product is the product of the sums
  rw [h1]
  simp only [h2]
  unfold Q
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **C-component factorization.** For a closed block `S`, `P(O) = Q[S] · Q[Sᶜ]`. This is
`anc_factor` with `A` all vertices. -/
theorem marginal_factor [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (a : Assignment (α := α) Uᶜ) :
    M.marginal Uᶜ a = Q M U S a * Q M U Sᶜ a := by
  rw [marginal_eq_restrict_of_subset_of_subset M (compl_inter_subset_compl U Finset.univ)
      (fun v hv => Finset.mem_inter.mpr ⟨hv, Finset.mem_univ v⟩) a,
    anc_factor M U Finset.univ S (fun _ _ _ _ => Finset.mem_univ _) hcl a,
    Finset.univ_inter, Finset.univ_inter]

/-- **An intervention in `S` changes only the factor of `S`.** The factor of the rest is
the same as without the intervention. -/
theorem do_marginal_factor [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S X : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (hX : X ⊆ S)
    (x : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    (doModel M X x).marginal Uᶜ a = Q (doModel M X x) U S a * Q M U Sᶜ a := by
  rw [marginal_factor (doModel M X x) U S
    (fun u hu v h => hcl u hu v (show G.edge u v ∧ v ∉ X from h).1) a]
  congr 1
  unfold Q
  refine tsum_congr (fun w => Finset.prod_congr rfl (fun v hv => ?_))
  have hvX : v ∉ X := fun h => (Finset.mem_compl.mp hv) (hX h)
  rw [kfac_doModel, dif_neg hvX]

end CFactor
end Identification

#print axioms Identification.CFactor.anc_factor
#print axioms Identification.CFactor.marginal_factor
#print axioms Identification.CFactor.do_marginal_factor

/-! ## The factors are identifiable (Tian's lemma 2)

The previous section split `P(O)` into `Q[S] · Q[Sᶜ]`. Here every factor is shown to be
determined by the observed distribution alone.

1. `anc_factor` (proved before `marginal_factor` above, which is its case `A = univ`):
   the factorization holds on every ancestral set `A`: `P(O ∩ A) = Q[A ∩ S] · Q[A ∩ Sᶜ]`.
2. `Q_step` (the explicit formula): removing a node `v ∈ T` without children in `A` gives
   `P(O ∩ A) · Q[A' ∩ T] = P(O ∩ A') · Q[A ∩ T]`, with `A' = A ∖ {v}`. So
   `Q[A ∩ T] = Q[A' ∩ T] · P(O ∩ A) / P(O ∩ A')`, and for an observed `v` the fraction is
   `P(v | O ∩ A')`. Repeated from `A = ∅` up to all nodes this gives Tian's product
   `Q[S] = ∏_{o ∈ S} P(o | the predecessors of o)`.
3. `Q_identifiable`: two models with the same positive distribution on `O` have the same
   `Q[S]` and the same `Q[Sᶜ]`. The proof is induction over ancestral sets with `Q_step`.

There is no assumption that the latents are roots. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **The explicit formula (one step).** `Q[A ∩ T] = Q[A' ∩ T] · P(O ∩ A) / P(O ∩ A')`,
written without division, where `A' = A ∖ {v}` is still ancestral. -/
theorem Q_step [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U A T : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ T ↔ v ∈ T)) (v : V) (hvT : v ∈ T)
    (hA' : ∀ z ∈ A.erase v, ∀ w, G.edge w z → w ∈ A.erase v) (a : Assignment (α := α) Uᶜ) :
    M.marginal (Uᶜ ∩ A) (a.restrict (compl_inter_subset_compl U A)) * Q M U (A.erase v ∩ T) a =
      M.marginal (Uᶜ ∩ A.erase v) (a.restrict (compl_inter_subset_compl U (A.erase v))) *
        Q M U (A ∩ T) a := by
  rw [anc_factor M U A T hA hcl a, anc_factor M U (A.erase v) T hA' hcl a,
    ← Finset.inter_eq_erase_inter_of_notMem (A := A) (fun h => (Finset.mem_compl.mp h) hvT)]
  ring

/-- Induction over ancestral sets of size `n`: both factors of a closed block are equal in
the two models. -/
theorem Q_ident_anc [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U S : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hM : M1.marginal Uᶜ = M2.marginal Uᶜ) (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0) (n : ℕ) :
    ∀ A : Finset V, A.card = n → (∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) →
      ∀ a, Q M1 U (A ∩ S) a = Q M2 U (A ∩ S) a ∧ Q M1 U (A ∩ Sᶜ) a = Q M2 U (A ∩ Sᶜ) a := by
  have hpos2 : ∀ a, M2.marginal Uᶜ a ≠ 0 := fun a => by rw [← hM]; exact hpos a
  have hMA : ∀ B : Finset V, M1.marginal (Uᶜ ∩ B) = M2.marginal (Uᶜ ∩ B) := fun B => by
    rw [← marginal_restrict M1 (compl_inter_subset_compl U B),
      ← marginal_restrict M2 (compl_inter_subset_compl U B), hM]
  have hclc : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ Sᶜ ↔ v ∈ Sᶜ) := fun u hu v h => by
    simp only [Finset.mem_compl]
    exact not_congr (hcl u hu v h)
  induction n with
  | zero =>
    intro A hc _ a
    obtain rfl := Finset.card_eq_zero.mp hc
    simp only [Finset.empty_inter]
    exact ⟨by simp [Q], by simp [Q]⟩
  | succ n ih =>
    intro A hc hA a
    obtain ⟨v, hvA, hmax⟩ := Finset.exists_max_image A G.rank (Finset.card_pos.mp (by omega))
    have hA' : ∀ z ∈ A.erase v, ∀ w, G.edge w z → w ∈ A.erase v := by
      intro z hz w hw
      refine Finset.mem_erase.mpr ⟨?_, hA z (Finset.mem_of_mem_erase hz) w hw⟩
      intro hwv
      subst hwv
      exact absurd (hmax z (Finset.mem_of_mem_erase hz)) (not_le.mpr (G.rank_strict_mono _ _ hw))
    have hc' : (A.erase v).card = n := by
      rw [Finset.card_erase_of_mem hvA]
      omega
    obtain ⟨ih1, ih2⟩ := ih (A.erase v) hc' hA' a
    have hP0 :
        M2.marginal (Uᶜ ∩ A.erase v) (a.restrict (compl_inter_subset_compl U (A.erase v))) ≠ 0 :=
      marginal_restrict_ne_zero M2 _ a (hpos2 a)
    have hPt :
        M2.marginal (Uᶜ ∩ A.erase v) (a.restrict (compl_inter_subset_compl U (A.erase v))) ≠ ⊤ :=
      PMF.apply_ne_top _ _
    have key : ∀ T : Finset V, (∀ u ∈ U, ∀ z, G.edge u z → (u ∈ T ↔ z ∈ T)) → v ∈ T →
        Q M1 U (A.erase v ∩ T) a = Q M2 U (A.erase v ∩ T) a →
        Q M1 U (A ∩ T) a = Q M2 U (A ∩ T) a := by
      intro T hT hvT hq
      have e1 := Q_step M1 U A T hA hT v hvT hA' a
      have e2 := Q_step M2 U A T hA hT v hvT hA' a
      rw [hMA A, hMA (A.erase v), hq] at e1
      exact (ENNReal.mul_right_inj hP0 hPt).mp (e1.symm.trans e2)
    by_cases hvS : v ∈ S
    · refine ⟨key S hcl hvS ih1, ?_⟩
      rw [Finset.inter_eq_erase_inter_of_notMem (A := A) (fun h => (Finset.mem_compl.mp h) hvS)]
      exact ih2
    · refine ⟨?_, key Sᶜ hclc (Finset.mem_compl.mpr hvS) ih2⟩
      rw [Finset.inter_eq_erase_inter_of_notMem (A := A) hvS]
      exact ih1

/-- **Tian's lemma 2 (identifiability).** The same positive distribution on the observed
nodes gives the same `Q[S]` and the same `Q[Sᶜ]`, for every closed block `S`. -/
theorem Q_identifiable [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U S : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hM : M1.marginal Uᶜ = M2.marginal Uᶜ) (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0)
    (a : Assignment (α := α) Uᶜ) :
    Q M1 U S a = Q M2 U S a ∧ Q M1 U Sᶜ a = Q M2 U Sᶜ a := by
  have h := Q_ident_anc M1 M2 U S hcl hM hpos _ Finset.univ rfl
    (fun _ _ _ _ => Finset.mem_univ _) a
  simpa only [Finset.univ_inter] using h

end CFactor
end Identification

#print axioms Identification.CFactor.Q_step
#print axioms Identification.CFactor.Q_identifiable

/-! ## Tian's identification theorem

Let `x` be observed and lie in a closed block `S` that contains no child of `x`. Then
`P(· | do(x))` is identifiable, with the explicit formula (`tian_formula`)

  `P_x(a) = [a_x = x] · (Σ_{x'} Q[S](a[x := x'])) · Q[Sᶜ](a)`.

Both factors are determined by the observed distribution (the previous section;
`Q_step` gives them explicitly), so the effect is identifiable (`tian_identifiable`). The
converse direction, where a child of `x` lies in the block, is given by the hedges of
`Identification/RootPath` and `Identification/RootTree` (see `TianIff`).

The core is `sum_Q_upd`: summed over the values of `x`, the kernel of `x` drops out (it
sums to 1), and no other kernel in `S` reads `x`. What is left is exactly the factor the
intervention model uses (`Q_do`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `a` with the value at `x` replaced by `x'`. -/
noncomputable def upd (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ)
    (x' : α x) : Assignment (α := α) Uᶜ :=
  Function.update a ⟨x, Finset.mem_compl.mpr hx⟩ x'

/-- `upd` takes the new value `x'` at `x`. -/
lemma upd_self (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ) (x' : α x)
    (h : x ∈ Uᶜ) : upd U hx a x' ⟨x, h⟩ = x' :=
  Function.update_self _ _ _

/-- `upd` does not change the values outside `x`. -/
lemma upd_ne (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ) (x' : α x)
    {z : V} (h : z ∈ Uᶜ) (hzx : z ≠ x) : upd U hx a x' ⟨z, h⟩ = a ⟨z, h⟩ :=
  Function.update_of_ne (fun e => hzx (congrArg Subtype.val e)) _ _

/-- Overwriting the value at `x` does not change the filled assignment outside `x`. -/
lemma fill_upd_ne [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (x' : α x) (w : Assignment (α := α) (U ∩ T)) (z : V)
    (hzx : z ≠ x) :
    fill U T (upd U hx a x') w ⟨z, Finset.mem_univ z⟩ = fill U T a w ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [fill, h0]
  · simp only [fill, dif_neg h0]
    exact upd_ne U hx a x' (Finset.mem_compl.mpr h0) hzx

/-- At `x`, the filled assignment takes the new value `x'`. -/
lemma fill_upd_x [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (x' : α x) (w : Assignment (α := α) (U ∩ T)) :
    fill U T (upd U hx a x') w ⟨x, Finset.mem_univ x⟩ = x' := by
  simp only [fill, dif_neg hx]
  exact upd_self U hx a x' _

/-- At an observed `x`, the filled assignment takes its value from `a`. -/
lemma fill_x [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (w : Assignment (α := α) (U ∩ T)) :
    fill U T a w ⟨x, Finset.mem_univ x⟩ = a ⟨x, Finset.mem_compl.mpr hx⟩ := by
  simp [fill, hx]

/-- **`x` is summed out.** No kernel in `S` other than that of `x` reads `x`, and the kernel
of `x` sums to 1. -/
theorem sum_Q_upd [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V) {x : V}
    (hx : x ∉ U) (hxS : x ∈ S) (hch : ∀ v ∈ S, ¬ G.edge x v) (a : Assignment (α := α) Uᶜ) :
    ∑' x' : α x, Q M U S (upd U hx a x') =
      ∑' w : Assignment (α := α) (U ∩ S), ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S a w) v := by
  unfold Q
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun w => ?_)
  have hrest : ∀ x' : α x, ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S (upd U hx a x') w) v =
      ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S a w) v := fun x' =>
    Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
      (fill_upd_ne U S hx a x' w v (Finset.ne_of_mem_erase hv))
      (fun u hu => fill_upd_ne U S hx a x' w u (fun h => hch v (Finset.mem_of_mem_erase hv)
        (by have e := DAG.mem_parents.mp hu; rw [h] at e; exact e))))
  have hxk : ∀ x' : α x, kfac M Finset.univ (fill U S (upd U hx a x') w) x =
      M.kernel x ((fill U S a w).restrict (Finset.subset_univ _)) x' := by
    intro x'
    have hr : (fill U S (upd U hx a x') w).restrict (Finset.subset_univ (G.parents x)) =
        (fill U S a w).restrict (Finset.subset_univ (G.parents x)) := by
      funext ⟨u, hu⟩
      exact fill_upd_ne U S hx a x' w u (fun h => DAG.not_self_edge G x
        (by have e := DAG.mem_parents.mp hu; rw [h] at e; exact e))
    rw [kfac_univ, hr, fill_upd_x U S hx a x' w]
  calc ∑' x' : α x, ∏ v ∈ S, kfac M Finset.univ (fill U S (upd U hx a x') w) v
      = ∑' x' : α x, M.kernel x ((fill U S a w).restrict (Finset.subset_univ _)) x' *
          ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S a w) v :=
        tsum_congr (fun x' => by rw [← Finset.mul_prod_erase S _ hxS, hxk x', hrest x'])
    _ = (∑' x' : α x, M.kernel x ((fill U S a w).restrict (Finset.subset_univ _)) x') *
          ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S a w) v := ENNReal.tsum_mul_right
    _ = _ := by rw [PMF.tsum_coe, one_mul]

/-- The factor of `S` in the intervention model: the indicator of `x`, times what is left
of `Q[S]` when the kernel of `x` is removed. -/
theorem Q_do [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V) {x : V}
    (hx : x ∉ U) (hxS : x ∈ S) (xv : Assignment (α := α) {x}) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M {x} xv) U S a =
      (if a ⟨x, Finset.mem_compl.mpr hx⟩ = xv ⟨x, Finset.mem_singleton_self x⟩
        then (1 : ENNReal) else 0) *
      ∑' w : Assignment (α := α) (U ∩ S), ∏ v ∈ S.erase x, kfac M Finset.univ (fill U S a w) v := by
  unfold Q
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun w => ?_)
  rw [← Finset.mul_prod_erase S _ hxS, kfac_doModel, dif_pos (Finset.mem_singleton_self x)]
  congr 1
  · by_cases h : a ⟨x, Finset.mem_compl.mpr hx⟩ = xv ⟨x, Finset.mem_singleton_self x⟩ <;>
      simp [fill_x U S hx a w, h]
  · exact Finset.prod_congr rfl (fun v hv => by
      rw [kfac_doModel, dif_neg (fun h => Finset.ne_of_mem_erase hv (Finset.mem_singleton.mp h))])

/-- **Tian's formula.** If `x` lies in a closed block `S` that contains no child of `x`,
then `P_x(a) = [a_x = x] · (Σ_{x'} Q[S](a[x := x'])) · Q[Sᶜ](a)`. -/
theorem tian_formula [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V) {x : V}
    (hx : x ∉ U) (hxS : x ∈ S) (hch : ∀ v ∈ S, ¬ G.edge x v)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S))
    (xv : Assignment (α := α) {x}) (a : Assignment (α := α) Uᶜ) :
    (doModel M {x} xv).marginal Uᶜ a =
      (if a ⟨x, Finset.mem_compl.mpr hx⟩ = xv ⟨x, Finset.mem_singleton_self x⟩
        then (1 : ENNReal) else 0) *
      (∑' x' : α x, Q M U S (upd U hx a x')) * Q M U Sᶜ a := by
  rw [do_marginal_factor M U S {x} hcl (Finset.singleton_subset_iff.mpr hxS) xv a,
    Q_do M U S hx hxS xv a, sum_Q_upd M U S hx hxS hch a]

/-- **Tian's identification theorem.** If no child of `x` lies in the closed block of `x`,
then the effect of `x` on any set `Y` of observed nodes is identifiable. -/
theorem tian_identifiable [∀ v, Nonempty (α v)] (U S : Finset V) {x : V}
    (hx : x ∉ U) (hxS : x ∈ S) (hch : ∀ v ∈ S, ¬ G.edge x v)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ {x} Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have h1 : ∀ b, Q M1 U S b = Q M2 U S b := fun b =>
    (Q_identifiable M1 M2 U S hcl hM hpos b).1
  have h2 : ∀ b, Q M1 U Sᶜ b = Q M2 U Sᶜ b := fun b =>
    (Q_identifiable M1 M2 U S hcl hM hpos b).2
  have hD : ∀ xv : Assignment (α := α) {x},
      (doModel M1 {x} xv).marginal Uᶜ = (doModel M2 {x} xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [tian_formula M1 U S hx hxS hch hcl xv a, tian_formula M2 U S hx hxS hch hcl xv a]
    simp only [h1, h2]
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

end CFactor
end Identification

#print axioms Identification.CFactor.tian_formula
#print axioms Identification.CFactor.tian_identifiable

/-! ## The c-component is the smallest closed block

A *latent step* is an edge with a latent tail, taken in either direction. The c-component
of `x` is the set of all nodes that `x` reaches by latent steps (`ccomp`). It

* is closed (`ccomp_closed`): no latent edge crosses its boundary,
* contains `x`,
* and lies in every closed block that contains `x` (`ccomp_subset`).

So it is the smallest closed block around `x` (`ccomp_isLeast`). As a consequence, the
condition of Tian's theorem ("a closed block around `x` without children of `x`") is
exactly "no child of `x` in the c-component of `x`" (`tian_cond_iff`), and the theorem can
be stated with the c-component directly (`tian_identifiable_ccomp`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {α : V → Type*}

/-- One latent step between `a` and `b`: an edge with a latent tail, in either direction. -/
def latStep (G : DAG V) (U : Finset V) (a b : V) : Prop :=
  (a ∈ U ∧ G.edge a b) ∨ (b ∈ U ∧ G.edge b a)

/-- A block is closed when no latent edge crosses its boundary. -/
def IsClosedBlock (G : DAG V) (U S : Finset V) : Prop :=
  ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)

/-- **The c-component of `x`:** all nodes that `x` reaches by latent steps. -/
noncomputable def ccomp (G : DAG V) (U : Finset V) (x : V) : Finset V :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (latStep G U) x v)

/-- Membership in the c-component. -/
lemma mem_ccomp {G : DAG V} {U : Finset V} {x v : V} :
    v ∈ ccomp G U x ↔ Relation.ReflTransGen (latStep G U) x v := by
  simp [ccomp]

/-- `x` lies in its own c-component. -/
lemma self_mem_ccomp (G : DAG V) (U : Finset V) (x : V) : x ∈ ccomp G U x :=
  mem_ccomp.mpr Relation.ReflTransGen.refl

/-- The c-component is closed. -/
theorem ccomp_closed (G : DAG V) (U : Finset V) (x : V) : IsClosedBlock G U (ccomp G U x) := by
  intro u hu v e
  rw [mem_ccomp, mem_ccomp]
  exact ⟨fun h => h.tail (Or.inl ⟨hu, e⟩), fun h => h.tail (Or.inr ⟨hu, e⟩)⟩

/-- The c-component lies in every closed block that contains `x`. -/
theorem ccomp_subset {G : DAG V} {U S : Finset V} {x : V} (hS : IsClosedBlock G U S)
    (hx : x ∈ S) : ccomp G U x ⊆ S := by
  have key : ∀ v, Relation.ReflTransGen (latStep G U) x v → v ∈ S := by
    intro v h
    induction h with
    | refl => exact hx
    | tail _ hst ih =>
      rcases hst with ⟨hb, e⟩ | ⟨hc, e⟩
      · exact (hS _ hb _ e).mp ih
      · exact (hS _ hc _ e).mpr ih
  exact fun v hv => key v (mem_ccomp.mp hv)

/-- **The c-component is the smallest closed block that contains `x`.** -/
theorem ccomp_isLeast (G : DAG V) (U : Finset V) (x : V) :
    IsLeast {S : Finset V | IsClosedBlock G U S ∧ x ∈ S} (ccomp G U x) := by
  refine ⟨?_, ?_⟩
  · show IsClosedBlock G U (ccomp G U x) ∧ x ∈ ccomp G U x
    exact ⟨ccomp_closed G U x, self_mem_ccomp G U x⟩
  · intro S hS
    simp only [Set.mem_setOf_eq] at hS
    exact ccomp_subset hS.1 hS.2

/-- **Tian's condition is a condition on the c-component.** There is a closed block around
`x` without children of `x` if and only if the c-component of `x` contains no child of
`x`. -/
theorem tian_cond_iff {G : DAG V} {U : Finset V} {x : V} :
    (∃ S, IsClosedBlock G U S ∧ x ∈ S ∧ ∀ v ∈ S, ¬ G.edge x v) ↔
      ∀ v ∈ ccomp G U x, ¬ G.edge x v := by
  constructor
  · rintro ⟨S, hS, hxS, h⟩ v hv
    exact h v (ccomp_subset hS hxS hv)
  · intro h
    exact ⟨ccomp G U x, ccomp_closed G U x, self_mem_ccomp G U x, h⟩

/-- **Tian's theorem with the c-component.** If no child of `x` lies in the c-component
of `x`, then the effect of `x` on any set `Y` of observed nodes is identifiable. -/
theorem tian_identifiable_ccomp {G : DAG V} [∀ v, Nonempty (α v)] (U : Finset V) {x : V}
    (hx : x ∉ U) (hch : ∀ v ∈ ccomp G U x, ¬ G.edge x v) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ {x} Y :=
  tian_identifiable U (ccomp G U x) hx (self_mem_ccomp G U x) hch (ccomp_closed G U x) Y hY

end CFactor
end Identification

#print axioms Identification.CFactor.ccomp_isLeast
#print axioms Identification.CFactor.tian_cond_iff
#print axioms Identification.CFactor.tian_identifiable_ccomp
