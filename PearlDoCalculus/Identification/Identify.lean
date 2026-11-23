import PearlDoCalculus.Identification.CFactorSets

/-!
# Tian's IDENTIFY, `Q_marg`, Tian's lemma 11 and the Verma sums

This file holds the c-factor side of the recursive part of the ID algorithm.

* Tian's marginalization lemma `Q_marg`. If `S` is ancestral inside `T` and `T` contains
  its latent parents, summing `Q[T]` over the observed nodes of `T ∖ S` gives `Q[T ∩ S]`.
* Tian's lemma 11 (`Q_ident_within`): knowing `Q[T]` determines `Q[T ∩ S]` and
  `Q[T ∩ Sᶜ]` for every block `S` closed inside `T`. The proof is the one of
  `Q_identifiable`, by induction over sets that are ancestral inside `T`, with `Q_marg`
  in the role of the marginal.
* Tian's IDENTIFY as the inductive predicate `IdentifyDerives`, with soundness
  (`identifyDerives_sound`, `identifyDerives_ident`).
* The Verma constraints `Q_local` and `verma_sum`.

Why it is needed: `Identification/IdSound` proves the soundness of the ID algorithm by
reaching every c-component with `IdentifyDerives` and using `identifyDerives_ident`, and it
marginalizes to an ancestral set with `Q_marg`. `IdAlgo` builds `IdentifyDerives`
derivations for the algorithm, and `Verma` uses `verma_sum`.

How the proofs go: for `Q_marg`, the sum over the latents of `T` splits into those of
`T ∩ S` and `T ∩ Sᶜ`; the kernels in `T ∩ S` read nothing in `T ∖ S`; and the kernels in
`T ∩ Sᶜ`, summed over all their values (observed and latent), give 1 (`inner_one`, by the
chain rule `sum_compl_kfac_eq_one` and a recount, `upd_join_iff`). The other results
follow from `Q_marg` by the induction of `Identification/CFactor`.

Main results: `Identification.CFactor.Q_marg`, `Identification.CFactor.Q_ident_within`,
`Identification.CFactor.IdentifyDerives`, `Identification.CFactor.identifyDerives_ident`,
`Identification.CFactor.verma_sum`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Tian's lemma on marginalizing factors (`Q_marg`)

The foundation of the recursive part of the ID algorithm (line 7, Tian's IDENTIFY): if
`S` is ancestral *inside* `T` (every parent in `T` of a node in `T ∩ S` lies in `S`), and
`T` contains its latent parents, then

  `Σ_{values of the observed nodes in T ∖ S} Q[T] = Q[T ∩ S]`.

The idea is Tian & Pearl (2002) and follows `q_factor_marginal_fixing` in Causalean
(J. Tan, Apache 2.0), which proves it at the measure level through an induced sub-SCM and
rule 3. The proof here is our own in the `PMF` setting and needs neither:

1. the sum over the latents in `T` splits into `T ∩ S` and `T ∩ Sᶜ`
   (`tsum_eq_tsum_joinBlocks`, `Identification/LatentSplit`);
2. the kernels in `T ∩ S` read nothing in `T ∖ S` (`fill_upd_join_in`);
3. the kernels in `T ∩ Sᶜ`, summed over all values there (observed and latent), give 1
   (`inner_one`, from `sum_compl_kfac_eq_one` and the recount in `upd_join_iff`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Outside `T ∩ Sᶜ`, the filled assignment does not depend on the overwritten observed values
or on the latent values in `T ∩ Sᶜ`. -/
lemma fill_upd_join_out [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' x'' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 w2' : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∉ T ∩ Sᶜ) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U T (updX U ((T ∩ Sᶜ) \ U) a x'') (joinBlocks U T S w1 w2') ⟨z, Finset.mem_univ z⟩ := by
  have hzD : z ∉ (T ∩ Sᶜ) \ U := fun h => hz (Finset.mem_sdiff.mp h).1
  by_cases h0 : z ∈ U
  · by_cases hT : z ∈ T
    · have hS : z ∈ S := by
        by_contra hS
        exact hz (Finset.mem_inter.mpr ⟨hT, Finset.mem_compl.mpr hS⟩)
      simp only [fill, dif_pos h0, dif_pos hT, joinBlocks, dif_pos hS]
    · simp only [fill, dif_pos h0, dif_neg hT]
  · simp only [fill, dif_neg h0, updX, dif_neg hzD]

/-- At an observed node of `T ∩ Sᶜ`, the filled assignment takes the overwritten value. -/
lemma fill_upd_join_D [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∈ (T ∩ Sᶜ) \ U) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      x' ⟨z, hz⟩ := by
  have h0 : z ∉ U := (Finset.mem_sdiff.mp hz).2
  simp only [fill, dif_neg h0, updX, dif_pos hz]

/-- At a latent node of `T ∩ Sᶜ`, the filled assignment takes the value from `w2`. -/
lemma fill_upd_join_W2 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∈ U ∩ (T ∩ Sᶜ)) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      w2 ⟨z, hz⟩ := by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hz
  obtain ⟨hT, hS⟩ := Finset.mem_inter.mp h1
  have hS' : z ∉ S := Finset.mem_compl.mp hS
  simp only [fill, dif_pos h0, dif_pos hT, joinBlocks, dif_neg hS']

/-- Outside the observed nodes of `T ∩ Sᶜ`, at a node that is observed or a latent of `T ∩ S`,
filling `T` agrees with filling `T ∩ S` from `w1`. -/
lemma fill_upd_join_in [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hzD : z ∉ (T ∩ Sᶜ) \ U)
    (hz : z ∈ U → z ∈ T ∩ S) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp only [fill, dif_pos h0, dif_pos hT, joinBlocks, dif_pos hS, dif_pos (hz h0)]
  · simp only [fill, dif_neg h0, updX, dif_neg hzD]

/-- Recount: a full assignment has the form `fill … (updX … x') (joinBlocks … w2)` exactly
when it agrees with a fixed such assignment outside `T ∩ Sᶜ` (and `x'`, `w2` are its
restrictions). -/
lemma upd_join_iff [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (x0 x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w20 w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    u = fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2) ↔
      u.restrict (Finset.subset_univ (T ∩ Sᶜ)ᶜ) =
          (fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (joinBlocks U T S w1 w20)).restrict
            (Finset.subset_univ (T ∩ Sᶜ)ᶜ) ∧
        x' = u.restrict (Finset.subset_univ ((T ∩ Sᶜ) \ U)) ∧
        w2 = u.restrict (Finset.subset_univ (U ∩ (T ∩ Sᶜ))) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict]
      exact fill_upd_join_out U T S a x' x0 w1 w2 w20 v (Finset.mem_compl.mp hv)
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict]
      exact (fill_upd_join_D U T S a x' w1 w2 v hv).symm
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict]
      exact (fill_upd_join_W2 U T S a x' w1 w2 v hv).symm
  · rintro ⟨hb, rfl, rfl⟩
    funext ⟨v, _⟩
    by_cases hv : v ∈ T ∩ Sᶜ
    · by_cases h0 : v ∈ U
      · exact (fill_upd_join_W2 U T S a (u.restrict (Finset.subset_univ ((T ∩ Sᶜ) \ U))) w1
          (u.restrict (Finset.subset_univ (U ∩ (T ∩ Sᶜ)))) v (Finset.mem_inter.mpr ⟨h0, hv⟩)).symm
      · exact (fill_upd_join_D U T S a (u.restrict (Finset.subset_univ ((T ∩ Sᶜ) \ U))) w1
          (u.restrict (Finset.subset_univ (U ∩ (T ∩ Sᶜ)))) v (Finset.mem_sdiff.mpr ⟨hv, h0⟩)).symm
    · have e := congrFun hb ⟨v, Finset.mem_compl.mpr hv⟩
      simp only [Assignment.restrict] at e
      rw [e]
      exact fill_upd_join_out U T S a x0 _ w1 w20 _ v hv

/-- **The kernels in `T ∩ Sᶜ` sum to 1**, summed over all values in `T ∩ Sᶜ`, observed and
latent. -/
theorem inner_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (a : Assignment (α := α) Uᶜ) (w1 : Assignment (α := α) (U ∩ (T ∩ S))) :
    ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
      ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ
        (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2)) v = 1 := by
  have x0 : Assignment (α := α) ((T ∩ Sᶜ) \ U) := fun _ => Classical.arbitrary _
  have w20 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)) := fun _ => Classical.arbitrary _
  have key := sum_compl_kfac_eq_one M (T ∩ Sᶜ)ᶜ
    ((fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (joinBlocks U T S w1 w20)).restrict
      (Finset.subset_univ (T ∩ Sᶜ)ᶜ))
  rw [compl_compl] at key
  refine Eq.trans ?_ key
  symm
  refine (tsum_congr fun u => ?_).trans (ENNReal.tsum_ite_eq_tsum_tsum_of_iff _ _ _ _ _
    (fun u x' w2 => (upd_join_iff U T S a w1 x0 x' w20 w2 u).trans (and_congr_left' eq_comm))
    (fun u => ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ u v))
  rw [ite_mul, one_mul, zero_mul]
  exact if_congr eq_comm rfl rfl

/-- **Tian's lemma on marginalizing factors.** If `S` is ancestral inside `T` and `T`
contains its latent parents, then the sum of `Q[T]` over the observed nodes of `T ∖ S` is
the factor `Q[T ∩ S]`. -/
theorem Q_marg [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
    (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), Q M U T (updX U ((T ∩ Sᶜ) \ U) a x') =
      Q M U (T ∩ S) a := by
  have hprod : ∀ (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U))
      (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))),
      ∏ v ∈ T, kfac M Finset.univ
          (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2)) v =
        (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
          ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ
            (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (joinBlocks U T S w1 w2)) v := by
    intro x' w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl T S]
    congr 1
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hvT, hvS⟩ := Finset.mem_inter.mp hv
    have hvD : v ∉ (T ∩ Sᶜ) \ U := fun h =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2) hvS
    refine kfac_congr M _ _ v (fill_upd_join_in U T S a x' w1 w2 v hvD (fun _ => hv))
      (fun p hp => ?_)
    have e := DAG.mem_parents.mp hp
    refine fill_upd_join_in U T S a x' w1 w2 p ?_ ?_
    · intro hpD
      obtain ⟨hpTS, _⟩ := Finset.mem_sdiff.mp hpD
      obtain ⟨hpT, hpS⟩ := Finset.mem_inter.mp hpTS
      exact (Finset.mem_compl.mp hpS) (hS v hv p hpT e)
    · intro hpU
      have hpT : p ∈ T := hT v hvT p hpU e
      exact Finset.mem_inter.mpr ⟨hpT, hS v hv p hpT e⟩
  unfold Q
  simp only [tsum_eq_tsum_joinBlocks U T S, hprod]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun w1 => ?_)
  simp only [ENNReal.tsum_mul_left]
  rw [inner_one M U T S a w1, mul_one]

/-- Equal factors on `T` give equal factors on every part `T ∩ S` that is ancestral in `T`. -/
theorem Q_marg_eq [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
    (h : ∀ b, Q M1 U T b = Q M2 U T b) (a : Assignment (α := α) Uᶜ) :
    Q M1 U (T ∩ S) a = Q M2 U (T ∩ S) a := by
  rw [← Q_marg M1 U T S hT hS a, ← Q_marg M2 U T S hT hS a]
  simp only [h]

end CFactor
end Identification

/-! ## Tian's lemma 11 (lemma 2 inside a factor)

If we know the factor `Q[T]`, we know the factors of every block `S` that is closed
*inside* `T` (no latent edge into `T` crosses the boundary of `S`):

  `Q₁[T] = Q₂[T]` (and positive)  ⟹  `Q₁[T ∩ S] = Q₂[T ∩ S]` and `Q₁[T ∩ Sᶜ] = Q₂[T ∩ Sᶜ]`
  (`Q_ident_within`).

For `T = V` this is `Q_identifiable` (`Identification/CFactor`), and the proof is the same:
induction over sets that are ancestral inside `T`, where `Q_marg` plays the role the
marginal had. The factor splits along such a block (`Q_split_rel`, in
`Identification/CFactorSets`). New along the way:

* `Q_le_one`: `Q[T] ≤ 1` (from `Q_marg` with `S = ∅`), which gives finiteness;
* `Q_marg_ne_zero`: positivity passes from `Q[T]` to the partial factors. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Overwriting the values on `X` by those already there changes nothing. -/
lemma updX_self (U X : Finset V) (hX : X ⊆ Uᶜ) (a : Assignment (α := α) Uᶜ) :
    updX U X a (a.restrict hX) = a := by
  funext v
  by_cases h : v.1 ∈ X
  · simp only [updX, dif_pos h, Assignment.restrict]
  · simp only [updX, dif_neg h]

/-- **`Q[T] ≤ 1`.** Summed over the observed nodes of `T`, the factor is 1 (`Q_marg` with `S =
∅`). -/
theorem Q_le_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (hT : IsLatClosed G U T) (a : Assignment (α := α) Uᶜ) : Q M U T a ≤ 1 := by
  have hD : (T ∩ (∅ : Finset V)ᶜ) \ U ⊆ Uᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have h := Q_marg M U T ∅ hT (fun v hv => by simp at hv) a
  rw [Finset.inter_empty, Q_empty] at h
  calc Q M U T a
      = Q M U T (updX U ((T ∩ (∅ : Finset V)ᶜ) \ U) a (a.restrict hD)) := by
        rw [updX_self]
    _ ≤ ∑' x' : Assignment (α := α) ((T ∩ (∅ : Finset V)ᶜ) \ U),
          Q M U T (updX U ((T ∩ (∅ : Finset V)ᶜ) \ U) a x') := ENNReal.le_tsum _
    _ = 1 := h

/-- **Positivity is inherited.** If `Q[T]` is positive everywhere, then so is `Q[T ∩ B]`, for
every `B` that is ancestral inside `T`. -/
theorem Q_marg_ne_zero [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T B : Finset V)
    (hT : IsLatClosed G U T) (hB : ∀ v ∈ T ∩ B, ∀ p ∈ T, G.edge p v → p ∈ B)
    (hpos : ∀ b, Q M U T b ≠ 0) (a : Assignment (α := α) Uᶜ) : Q M U (T ∩ B) a ≠ 0 := by
  have hD : (T ∩ Bᶜ) \ U ⊆ Uᶜ := fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  rw [← Q_marg M U T B hT hB a]
  intro h0
  have h1 := (ENNReal.tsum_eq_zero.mp h0) (a.restrict hD)
  rw [updX_self] at h1
  exact hpos a h1

/-- Induction over sets of size `n` that are ancestral inside `T`: both factors of a block
closed inside `T` are equal in the two models. -/
theorem Q_ident_in [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hQ : ∀ b, Q M1 U T b = Q M2 U T b) (hpos : ∀ b, Q M1 U T b ≠ 0) (n : ℕ) :
    ∀ B : Finset V, B.card = n → B ⊆ T → (∀ v ∈ B, ∀ p ∈ T, G.edge p v → p ∈ B) →
      ∀ a, Q M1 U (B ∩ S) a = Q M2 U (B ∩ S) a ∧ Q M1 U (B ∩ Sᶜ) a = Q M2 U (B ∩ Sᶜ) a := by
  have hpos2 : ∀ b, Q M2 U T b ≠ 0 := fun b => by rw [← hQ]; exact hpos b
  have hclc : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ Sᶜ ↔ v ∈ Sᶜ) := fun u hu v hv e => by
    simp only [Finset.mem_compl]
    exact not_congr (hcl u hu v hv e)
  -- facts about a set `B ⊆ T` that is ancestral inside `T`
  have hTB : ∀ B : Finset V, B ⊆ T → T ∩ B = B := fun B hBT => Finset.inter_eq_right.mpr hBT
  have hanc : ∀ B : Finset V, (∀ v ∈ B, ∀ p ∈ T, G.edge p v → p ∈ B) →
      ∀ v ∈ T ∩ B, ∀ p ∈ T, G.edge p v → p ∈ B :=
    fun B hB v hv p hp e => hB v (Finset.mem_inter.mp hv).2 p hp e
  have hlat : ∀ B : Finset V, B ⊆ T → (∀ v ∈ B, ∀ p ∈ T, G.edge p v → p ∈ B) →
      IsLatClosed G U B :=
    fun B hBT hB v hv u hu e => hB v hv u (hT v (hBT hv) u hu e) e
  have hP : ∀ B : Finset V, B ⊆ T → (∀ v ∈ B, ∀ p ∈ T, G.edge p v → p ∈ B) →
      ∀ a, Q M1 U B a = Q M2 U B a := fun B hBT hB a => by
    have h := Q_marg_eq M1 M2 U T B hT (hanc B hB) hQ a
    rwa [hTB B hBT] at h
  induction n with
  | zero =>
    intro B hc _ _ a
    obtain rfl := Finset.card_eq_zero.mp hc
    simp only [Finset.empty_inter]
    exact ⟨by rw [Q_empty, Q_empty], by rw [Q_empty, Q_empty]⟩
  | succ n ih =>
    intro B hc hBT hB a
    obtain ⟨v, hvB, hmax⟩ := Finset.exists_max_image B G.rank (Finset.card_pos.mp (by omega))
    have hB'T : B.erase v ⊆ T := (Finset.erase_subset v B).trans hBT
    have hB' : ∀ z ∈ B.erase v, ∀ p ∈ T, G.edge p z → p ∈ B.erase v := by
      intro z hz p hp e
      refine Finset.mem_erase.mpr ⟨?_, hB z (Finset.mem_of_mem_erase hz) p hp e⟩
      intro hpv
      subst hpv
      exact absurd (hmax z (Finset.mem_of_mem_erase hz)) (not_le.mpr (G.rank_strict_mono _ _ e))
    have hc' : (B.erase v).card = n := by
      rw [Finset.card_erase_of_mem hvB]
      omega
    obtain ⟨ih1, ih2⟩ := ih (B.erase v) hc' hB'T hB' a
    have hP0 : Q M2 U (B.erase v) a ≠ 0 := by
      have h := Q_marg_ne_zero M2 U T (B.erase v) hT (hanc _ hB') hpos2 a
      rwa [hTB _ hB'T] at h
    have hPt : Q M2 U (B.erase v) a ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (Q_le_one M2 U (B.erase v) (hlat _ hB'T hB') a)
    have key : ∀ S' : Finset V, (∀ u ∈ U, ∀ z ∈ T, G.edge u z → (u ∈ S' ↔ z ∈ S')) → v ∈ S' →
        Q M1 U (B.erase v ∩ S') a = Q M2 U (B.erase v ∩ S') a →
        Q M1 U (B ∩ S') a = Q M2 U (B ∩ S') a := by
      intro S' hS' hvS hq
      have hrelB : ∀ u ∈ U, ∀ z ∈ B, G.edge u z → (u ∈ S' ↔ z ∈ S') :=
        fun u hu z hz e => hS' u hu z (hBT hz) e
      have hrelB' : ∀ u ∈ U, ∀ z ∈ B.erase v, G.edge u z → (u ∈ S' ↔ z ∈ S') :=
        fun u hu z hz e => hS' u hu z (hB'T hz) e
      have hset : B.erase v ∩ S'ᶜ = B ∩ S'ᶜ :=
        (Finset.inter_eq_erase_inter_of_notMem (A := B) (fun h => (Finset.mem_compl.mp h) hvS)).symm
      have step : ∀ M : G.CausalModel α,
          Q M U B a * Q M U (B.erase v ∩ S') a = Q M U (B.erase v) a * Q M U (B ∩ S') a := by
        intro M
        rw [Q_split_rel M U B S' (hlat B hBT hB) hrelB a,
          Q_split_rel M U (B.erase v) S' (hlat _ hB'T hB') hrelB' a, hset]
        ring
      have e1 := step M1
      have e2 := step M2
      rw [hP B hBT hB a, hP _ hB'T hB' a, hq] at e1
      exact (ENNReal.mul_right_inj hP0 hPt).mp (e1.symm.trans e2)
    by_cases hvS : v ∈ S
    · refine ⟨key S hcl hvS ih1, ?_⟩
      rw [Finset.inter_eq_erase_inter_of_notMem (A := B) (fun h => (Finset.mem_compl.mp h) hvS)]
      exact ih2
    · refine ⟨?_, key Sᶜ hclc (Finset.mem_compl.mpr hvS) ih2⟩
      rw [Finset.inter_eq_erase_inter_of_notMem (A := B) hvS]
      exact ih1

/-- **Tian's lemma 11.** Equal and positive factors on `T` give equal factors on every
block that is closed inside `T`. -/
theorem Q_ident_within [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hQ : ∀ b, Q M1 U T b = Q M2 U T b) (hpos : ∀ b, Q M1 U T b ≠ 0)
    (a : Assignment (α := α) Uᶜ) :
    Q M1 U (T ∩ S) a = Q M2 U (T ∩ S) a ∧ Q M1 U (T ∩ Sᶜ) a = Q M2 U (T ∩ Sᶜ) a :=
  Q_ident_in M1 M2 U T S hT hcl hQ hpos _ T rfl (Finset.Subset.refl T)
    (fun _ _ _ hp _ => hp) a

end CFactor
end Identification

/-! ## Tian's IDENTIFY as an inductive predicate (`IdentifyDerives`)

Tian's recursive procedure IDENTIFY(C, T, Q[T]) takes two kinds of steps:

* marginalize out what is not ancestral for `C` inside `T` (`Q_marg`);
* go to a block that is closed inside `T` (`Q_ident_within`).

`IdentifyDerives G U T C` says that `C` can be reached from `T` by a finite sequence of such steps.
The form is borrowed from Causalean's `CFactorReachableRec` (Jiyuan Tan, CausalSmith,
Apache 2.0); the proof here is our own and uses only the `PMF` setting of this project.

`identifyDerives_sound`: equal and positive factors on `T` give equal and positive factors on `C`.
`identifyDerives_ident`: with `T = V`, `Q[C]` is determined by the observed distribution. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **`C` can be reached from `T`** by Tian's two steps. -/
inductive IdentifyDerives (G : DAG V) (U : Finset V) : Finset V → Finset V → Prop
  /-- Nothing to do. -/
  | refl (T : Finset V) : IdentifyDerives G U T T
  /-- Marginalize out `T ∖ S`, where `S` is ancestral inside `T`. -/
  | anc (T S C : Finset V) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
      (h : IdentifyDerives G U (T ∩ S) C) : IdentifyDerives G U T C
  /-- Go to a block that is closed inside `T`. -/
  | block (T S C : Finset V) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
      (h : IdentifyDerives G U (T ∩ S) C) : IdentifyDerives G U T C

/-- Steps can be put one after the other. -/
theorem IdentifyDerives.trans {U T S C : Finset V} (h1 : IdentifyDerives G U T S) :
    IdentifyDerives G U S C → IdentifyDerives G U T C := by
  induction h1 with
  | refl T0 => exact id
  | anc T0 S0 C0 hS _ ih => exact fun h2 => IdentifyDerives.anc T0 S0 C hS (ih h2)
  | block T0 S0 C0 hcl _ ih => exact fun h2 => IdentifyDerives.block T0 S0 C hcl (ih h2)

/-- A closed block is reached from `V` in one step. -/
theorem identifyDerives_of_isClosedBlock (U S : Finset V) (hcl : IsClosedBlock G U S) :
    IdentifyDerives G U Finset.univ S :=
  IdentifyDerives.block Finset.univ S S (fun u hu v _ e => hcl u hu v e)
    (by rw [Finset.univ_inter]; exact IdentifyDerives.refl S)

/-- **Soundness of `IdentifyDerives`.** If `C` is reached from `T`, then equal and positive factors
on `T` give equal and positive factors on `C`. -/
theorem identifyDerives_sound [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U : Finset V)
    {T C : Finset V} (hR : IdentifyDerives G U T C) :
    IsLatClosed G U T → (∀ b, Q M1 U T b = Q M2 U T b) → (∀ b, Q M1 U T b ≠ 0) →
      (∀ b, Q M1 U C b = Q M2 U C b) ∧ (∀ b, Q M1 U C b ≠ 0) := by
  induction hR with
  | refl T0 => exact fun _ hQ hpos => ⟨hQ, hpos⟩
  | anc T0 S0 C0 hS _ ih =>
    intro hT hQ hpos
    have hT' : IsLatClosed G U (T0 ∩ S0) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        hS v hv u (hT v (Finset.mem_inter.mp hv).1 u hu e) e⟩
    exact ih hT' (fun b => Q_marg_eq M1 M2 U T0 S0 hT hS hQ b)
      (fun b => Q_marg_ne_zero M1 U T0 S0 hT hS hpos b)
  | block T0 S0 C0 hcl _ ih =>
    intro hT hQ hpos
    have hT' : IsLatClosed G U (T0 ∩ S0) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        (hcl u hu v (Finset.mem_inter.mp hv).1 e).mpr (Finset.mem_inter.mp hv).2⟩
    refine ih hT' (fun b => (Q_ident_within M1 M2 U T0 S0 hT hcl hQ hpos b).1) (fun b => ?_)
    have h0 := hpos b
    rw [Q_split_rel M1 U T0 S0 hT hcl b] at h0
    exact left_ne_zero_of_mul h0

/-- **IDENTIFY is sound.** If `C` can be reached from `V`, then `Q[C]` is determined by the
observed distribution (when it is positive). -/
theorem identifyDerives_ident [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U C : Finset V)
    (hR : IdentifyDerives G U Finset.univ C)
    (hM : M1.marginal Uᶜ = M2.marginal Uᶜ) (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0)
    (a : Assignment (α := α) Uᶜ) : Q M1 U C a = Q M2 U C a :=
  (identifyDerives_sound M1 M2 U hR (fun _ _ _ _ _ => Finset.mem_univ _)
    (fun b => by rw [← marginal_eq_Q, ← marginal_eq_Q, hM])
    (fun b => by rw [← marginal_eq_Q]; exact hpos b)).1 a

end CFactor
end Identification

/-! ## Verma constraints

The factors `Q[T]` give equalities for the observed distribution that are not conditional
independences (Verma & Pearl 1990; Tian & Pearl 2002, section 4):

* `Q_local`: `Q[T]` depends only on the observed values in `T` and at the parents of `T`;
* `verma_sum`: if `S` is ancestral inside `T`, the sum of `Q[T]` over the observed nodes
  of `T ∖ S` is `Q[T ∩ S]` (`Q_marg`), and so depends only on the observed nodes in
  `T ∩ S` and at their parents.

If `Q[T]` is identifiable, this is a constraint on `P` itself. The file `Verma.lean`
works out the classical example. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **The factor is local:** `Q[T]` depends only on the observed values in `T` and at the
parents of `T`. -/
theorem Q_local [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a a' : Assignment (α := α) Uᶜ)
    (h : ∀ z (hz : z ∉ U), (z ∈ T ∨ ∃ t ∈ T, G.edge z t) →
      a ⟨z, Finset.mem_compl.mpr hz⟩ = a' ⟨z, Finset.mem_compl.mpr hz⟩) :
    Q M U T a = Q M U T a' := by
  unfold Q
  refine tsum_congr (fun w => Finset.prod_congr rfl (fun v hv => ?_))
  have hf : ∀ z, (z ∈ T ∨ ∃ t ∈ T, G.edge z t) →
      fill U T a w ⟨z, Finset.mem_univ z⟩ = fill U T a' w ⟨z, Finset.mem_univ z⟩ := by
    intro z hz
    by_cases h0 : z ∈ U
    · simp only [fill, dif_pos h0]
    · simp only [fill, dif_neg h0]
      exact h z h0 hz
  exact kfac_congr M _ _ v (hf v (Or.inl hv)) (fun u hu => hf u (Or.inr ⟨v, hv, DAG.mem_parents.mp hu⟩))

/-- **Verma constraint, general form.** If `S` is ancestral inside `T`, the sum of `Q[T]`
over the observed nodes of `T ∖ S` depends only on the observed values in `T ∩ S` and at
their parents. -/
theorem verma_sum [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
    (a a' : Assignment (α := α) Uᶜ)
    (h : ∀ z (hz : z ∉ U), (z ∈ T ∩ S ∨ ∃ t ∈ T ∩ S, G.edge z t) →
      a ⟨z, Finset.mem_compl.mpr hz⟩ = a' ⟨z, Finset.mem_compl.mpr hz⟩) :
    ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), Q M U T (updX U ((T ∩ Sᶜ) \ U) a x') =
      ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), Q M U T (updX U ((T ∩ Sᶜ) \ U) a' x') := by
  rw [Q_marg M U T S hT hS a, Q_marg M U T S hT hS a']
  exact Q_local M U (T ∩ S) a a' h

end CFactor
end Identification
