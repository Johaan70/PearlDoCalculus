import PearlDoCalculus.Identification.LatentTree
import PearlDoCalculus.Identification.RootPathModels
import PearlDoCalculus.Identification.TwoRoot
import PearlDoCalculus.Identification.RootPath
import PearlDoCalculus.Identification.RootTree
import PearlDoCalculus.Identification.Channel
import PearlDoCalculus.Identification.CFactor
import PearlDoCalculus.Identification.TianIff
import PearlDoCalculus.Identification.CFactorSets

/-!
# Identification with latent variables

This file is being split into the files of the folder `PearlDoCalculus/Identification/`.
So far `Identification/Basic` holds the definition `Identifiable` and the easy cases
(rounds 1, 2, 5 and the general part of round 11) and `Identification/Bow` the bow
graph (rounds 3 and 4), `Identification/Hedge2` the hedge with two latent variables
(round 6) and `Identification/HedgeChain` the hedge chains (round 7), `Identification/HedgeTemplate` the hedge template and latent
paths with a tree (rounds 8 and 8b) and `Identification/LatentTree` the latent trees
(rounds 9, 11 and 12), `Identification/TwoRoot` the c-forest with two roots (round 13), `Identification/RootPathModels` the configurations and models of rounds 14 and 15 and `Identification/RootPath` the proof that the root-path configurations are not identifiable (rest of round 15) and `Identification/RootTree` the latent path and embedded hedges (rounds 16 and 17), `Identification/Channel` the channel step and whole directed paths (rounds 18 and 19) and `Identification/CFactor` Tian's factorization and identification theorem (rounds 20 to 23), `Identification/TianIff` the dividing line for one `x`, `tian_iff` (round 24) and `Identification/CFactorSets` Tian's theorem for sets and the c-factors as causal effects (rounds 25 to 29).
The rest is still here.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 30: Tians lemma om marginalisering av faktorer (`Q_marg`)

Grunnsteinen i den rekursive delen av ID-algoritmen (linje 7, Tians IDENTIFY): er `S`
ancestral *innenfor* `T` (hver forelder i `T` til en node i `T ∩ S` ligger i `S`), og
inneholder `T` sine latente foreldre, er

  `Σ_{verdier på de observerte i T ∖ S} Q[T] = Q[T ∩ S]`.

Ideen er Tian & Pearl (2002) og følger `q_factor_marginal_fixing` i Causalean
(J. Tan, Apache 2.0), som beviser den på målnivå via en indusert del-SCM og regel 3.
Beviset her er vårt eget i `PMF`-settingen og trenger ingen av delene:

1. summen over de latente i `T` deles i `T ∩ S` og `T ∩ Sᶜ` (`tsum_join2`, runde 26);
2. kjernene i `T ∩ S` leser ingenting i `T ∖ S` (`fill_upd_join_in`);
3. kjernene i `T ∩ Sᶜ`, summert over alle verdiene der (observerte og latente), gir 1
   (`inner_one`, fra `sum_compl_kfac_eq_one` og omtelling i `upd_join_iff`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

lemma fill_upd_join_out [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' x'' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 w2' : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∉ T ∩ Sᶜ) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U T (updX U ((T ∩ Sᶜ) \ U) a x'') (join2 U T S w1 w2') ⟨z, Finset.mem_univ z⟩ := by
  have hzD : z ∉ (T ∩ Sᶜ) \ U := fun h => hz (Finset.mem_sdiff.mp h).1
  by_cases h0 : z ∈ U
  · by_cases hT : z ∈ T
    · have hS : z ∈ S := by
        by_contra hS
        exact hz (Finset.mem_inter.mpr ⟨hT, Finset.mem_compl.mpr hS⟩)
      simp only [fill, dif_pos h0, dif_pos hT, join2, dif_pos hS]
    · simp only [fill, dif_pos h0, dif_neg hT]
  · simp only [fill, dif_neg h0, updX, dif_neg hzD]

lemma fill_upd_join_D [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∈ (T ∩ Sᶜ) \ U) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      x' ⟨z, hz⟩ := by
  have h0 : z ∉ U := (Finset.mem_sdiff.mp hz).2
  simp only [fill, dif_neg h0, updX, dif_pos hz]

lemma fill_upd_join_W2 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hz : z ∈ U ∩ (T ∩ Sᶜ)) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      w2 ⟨z, hz⟩ := by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hz
  obtain ⟨hT, hS⟩ := Finset.mem_inter.mp h1
  have hS' : z ∉ S := Finset.mem_compl.mp hS
  simp only [fill, dif_pos h0, dif_pos hT, join2, dif_neg hS']

lemma fill_upd_join_in [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (z : V) (hzD : z ∉ (T ∩ Sᶜ) \ U)
    (hz : z ∈ U → z ∈ T ∩ S) :
    fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp only [fill, dif_pos h0, dif_pos hT, join2, dif_pos hS, dif_pos (hz h0)]
  · simp only [fill, dif_neg h0, updX, dif_neg hzD]

/-- Omtelling: en full tilordning er av formen `fill … (updX … x') (join2 … w2)` nøyaktig
når den stemmer med en fast slik tilordning utenfor `T ∩ Sᶜ`. -/
lemma upd_join_iff [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (x0 x' : Assignment (α := α) ((T ∩ Sᶜ) \ U)) (w20 w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    u = fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2) ↔
      u.restrict (Finset.subset_univ (T ∩ Sᶜ)ᶜ) =
          (fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (join2 U T S w1 w20)).restrict
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

/-- **Kjernene i `T ∩ Sᶜ` summerer til 1.** -/
theorem inner_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (a : Assignment (α := α) Uᶜ) (w1 : Assignment (α := α) (U ∩ (T ∩ S))) :
    ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
      ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ
        (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)) v = 1 := by
  have x0 : Assignment (α := α) ((T ∩ Sᶜ) \ U) := fun _ => Classical.arbitrary _
  have w20 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)) := fun _ => Classical.arbitrary _
  have key := sum_compl_kfac_eq_one M (T ∩ Sᶜ)ᶜ
    ((fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (join2 U T S w1 w20)).restrict
      (Finset.subset_univ (T ∩ Sᶜ)ᶜ))
  rw [compl_compl] at key
  refine Eq.trans ?_ key
  symm
  calc ∑' u : Assignment (α := α) (Finset.univ : Finset V),
        (if u.restrict (Finset.subset_univ (T ∩ Sᶜ)ᶜ) =
            (fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (join2 U T S w1 w20)).restrict
              (Finset.subset_univ (T ∩ Sᶜ)ᶜ) then (1 : ENNReal) else 0) *
          ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ u v
      = ∑' u : Assignment (α := α) (Finset.univ : Finset V),
          ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U),
            ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
              (if u = fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)
                then ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ u v else 0) := by
        refine tsum_congr (fun u => ?_)
        by_cases hu : u.restrict (Finset.subset_univ (T ∩ Sᶜ)ᶜ) =
            (fill U T (updX U ((T ∩ Sᶜ) \ U) a x0) (join2 U T S w1 w20)).restrict
              (Finset.subset_univ (T ∩ Sᶜ)ᶜ)
        · rw [if_pos hu, one_mul,
            tsum_eq_single (u.restrict (Finset.subset_univ ((T ∩ Sᶜ) \ U)))]
          · rw [tsum_eq_single (u.restrict (Finset.subset_univ (U ∩ (T ∩ Sᶜ))))]
            · rw [if_pos ((upd_join_iff U T S a w1 x0 _ w20 _ u).mpr ⟨hu, rfl, rfl⟩)]
            · intro w2 hw2
              rw [if_neg (fun h => hw2 ((upd_join_iff U T S a w1 x0 _ w20 w2 u).mp h).2.2)]
          · intro x' hx'
            exact ENNReal.tsum_eq_zero.mpr (fun w2 =>
              if_neg (fun h => hx' ((upd_join_iff U T S a w1 x0 x' w20 w2 u).mp h).2.1))
        · rw [if_neg hu, zero_mul]
          symm
          exact ENNReal.tsum_eq_zero.mpr (fun x' => ENNReal.tsum_eq_zero.mpr (fun w2 =>
            if_neg (fun h => hu ((upd_join_iff U T S a w1 x0 x' w20 w2 u).mp h).1)))
    _ = ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U),
          ∑' u : Assignment (α := α) (Finset.univ : Finset V),
            ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
              (if u = fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)
                then ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ u v else 0) := ENNReal.tsum_comm
    _ = ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U),
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
            ∑' u : Assignment (α := α) (Finset.univ : Finset V),
              (if u = fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)
                then ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ u v else 0) :=
        tsum_congr (fun x' => ENNReal.tsum_comm)
    _ = _ := by
        refine tsum_congr (fun x' => tsum_congr (fun w2 => ?_))
        rw [tsum_eq_single (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2))]
        · simp
        · intro u hu
          rw [if_neg hu]

/-- **Tians lemma om marginalisering av faktorer.** Er `S` ancestral innenfor `T`, og
inneholder `T` sine latente foreldre, gir summen av `Q[T]` over de observerte i `T ∖ S`
faktoren `Q[T ∩ S]`. -/
theorem Q_marg [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
    (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) ((T ∩ Sᶜ) \ U), Q M U T (updX U ((T ∩ Sᶜ) \ U) a x') =
      Q M U (T ∩ S) a := by
  have hprod : ∀ (x' : Assignment (α := α) ((T ∩ Sᶜ) \ U))
      (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))),
      ∏ v ∈ T, kfac M Finset.univ
          (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)) v =
        (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
          ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ
            (fill U T (updX U ((T ∩ Sᶜ) \ U) a x') (join2 U T S w1 w2)) v := by
    intro x' w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl T S]
    congr 1
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hvT, hvS⟩ := Finset.mem_inter.mp hv
    have hvD : v ∉ (T ∩ Sᶜ) \ U := fun h =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2) hvS
    refine kfac_congr M _ _ v (fill_upd_join_in U T S a x' w1 w2 v hvD (fun _ => hv))
      (fun p hp => ?_)
    have e := edge_of_par hp
    refine fill_upd_join_in U T S a x' w1 w2 p ?_ ?_
    · intro hpD
      obtain ⟨hpTS, _⟩ := Finset.mem_sdiff.mp hpD
      obtain ⟨hpT, hpS⟩ := Finset.mem_inter.mp hpTS
      exact (Finset.mem_compl.mp hpS) (hS v hv p hpT e)
    · intro hpU
      have hpT : p ∈ T := hT v hvT p hpU e
      exact Finset.mem_inter.mpr ⟨hpT, hS v hv p hpT e⟩
  unfold Q
  simp only [tsum_join2 U T S, hprod]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun w1 => ?_)
  simp only [ENNReal.tsum_mul_left]
  rw [inner_one M U T S a w1, mul_one]

/-- Like faktorer på `T` gir like faktorer på enhver del `T ∩ S` som er ancestral i `T`. -/
theorem Q_marg_eq [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
    (h : ∀ b, Q M1 U T b = Q M2 U T b) (a : Assignment (α := α) Uᶜ) :
    Q M1 U (T ∩ S) a = Q M2 U (T ∩ S) a := by
  rw [← Q_marg M1 U T S hT hS a, ← Q_marg M2 U T S hT hS a]
  simp only [h]

end CFactor
end Identification

#print axioms Identification.CFactor.inner_one
#print axioms Identification.CFactor.Q_marg
#print axioms Identification.CFactor.Q_marg_eq

/-! ## Runde 31: Tians lemma 11 (lemma 2 innenfor en faktor)

Kjenner vi faktoren `Q[T]`, kjenner vi faktorene for hver blokk `S` som er lukket
*innenfor* `T` (ingen latent kant i `T` krysser grensen til `S`):

  `Q₁[T] = Q₂[T]` (og positiv)  ⟹  `Q₁[T ∩ S] = Q₂[T ∩ S]` og `Q₁[T ∩ Sᶜ] = Q₂[T ∩ Sᶜ]`
  (`Q_ident_within`).

For `T = V` er dette runde 21 (`Q_identifiable`), og beviset er det samme: induksjon over
mengder som er ancestrale innenfor `T`, der `Q_marg` (runde 30) spiller rollen marginalen
hadde. Nytt underveis:

* `Q_split_rel`: `Q_split` med blokken lukket bare innenfor `T`;
* `Q_le_one`: `Q[T] ≤ 1` (fra `Q_marg` med `S = ∅`), som gir endelighet;
* `Q_marg_ne_zero`: positiviteten arves fra `Q[T]` til delfaktorene. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

lemma updX_self (U X : Finset V) (hX : X ⊆ Uᶜ) (a : Assignment (α := α) Uᶜ) :
    updX U X a (a.restrict hX) = a := by
  funext v
  by_cases h : v.1 ∈ X
  · simp only [updX, dif_pos h, Assignment.restrict]
  · simp only [updX, dif_neg h]

/-- **`Q_split` med blokken lukket bare innenfor `T`.** -/
theorem Q_split_rel [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (a : Assignment (α := α) Uᶜ) :
    Q M U T a = Q M U (T ∩ S) a * Q M U (T ∩ Sᶜ) a := by
  have h2 : ∀ w1 w2, ∏ v ∈ T, kfac M Finset.univ (fill U T a (join2 U T S w1 w2)) v =
      (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
        ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ (fill U (T ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl T S]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join1 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join1 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (edge_of_par hu),
              (hcl u hu0 v (Finset.mem_inter.mp hv).1 (edge_of_par hu)).mpr
                (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join2 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join2 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (edge_of_par hu),
              Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
                ((hcl u hu0 v (Finset.mem_inter.mp hv).1 (edge_of_par hu)).mp hus))⟩)))
  unfold Q
  rw [tsum_join2 U T S]
  simp only [h2]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **`Q[T] ≤ 1`.** Summert over de observerte i `T` er faktoren 1 (`Q_marg` med `S = ∅`). -/
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

/-- **Positiviteten arves.** Er `Q[T]` positiv overalt, er også `Q[T ∩ B]` det, for hver
`B` som er ancestral innenfor `T`. -/
theorem Q_marg_ne_zero [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T B : Finset V)
    (hT : IsLatClosed G U T) (hB : ∀ v ∈ T ∩ B, ∀ p ∈ T, G.edge p v → p ∈ B)
    (hpos : ∀ b, Q M U T b ≠ 0) (a : Assignment (α := α) Uᶜ) : Q M U (T ∩ B) a ≠ 0 := by
  have hD : (T ∩ Bᶜ) \ U ⊆ Uᶜ := fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  rw [← Q_marg M U T B hT hB a]
  intro h0
  have h1 := (ENNReal.tsum_eq_zero.mp h0) (a.restrict hD)
  rw [updX_self] at h1
  exact hpos a h1

/-- Induksjon over mengder som er ancestrale innenfor `T`. -/
theorem Q_ident_in [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hQ : ∀ b, Q M1 U T b = Q M2 U T b) (hpos : ∀ b, Q M1 U T b ≠ 0) (n : ℕ) :
    ∀ B : Finset V, B.card = n → B ⊆ T → (∀ v ∈ B, ∀ p ∈ T, G.edge p v → p ∈ B) →
      ∀ a, Q M1 U (B ∩ S) a = Q M2 U (B ∩ S) a ∧ Q M1 U (B ∩ Sᶜ) a = Q M2 U (B ∩ Sᶜ) a := by
  have hpos2 : ∀ b, Q M2 U T b ≠ 0 := fun b => by rw [← hQ]; exact hpos b
  have hclc : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ Sᶜ ↔ v ∈ Sᶜ) := fun u hu v hv e => by
    simp only [Finset.mem_compl]
    exact not_congr (hcl u hu v hv e)
  -- Fakta om en mengde `B ⊆ T` som er ancestral innenfor `T`
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
        (inter_erase_of_not_mem (A := B) (fun h => (Finset.mem_compl.mp h) hvS)).symm
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
      rw [inter_erase_of_not_mem (A := B) (fun h => (Finset.mem_compl.mp h) hvS)]
      exact ih2
    · refine ⟨?_, key Sᶜ hclc (Finset.mem_compl.mpr hvS) ih2⟩
      rw [inter_erase_of_not_mem (A := B) hvS]
      exact ih1

/-- **Tians lemma 11.** Like og positive faktorer på `T` gir like faktorer på hver blokk
som er lukket innenfor `T`. -/
theorem Q_ident_within [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hQ : ∀ b, Q M1 U T b = Q M2 U T b) (hpos : ∀ b, Q M1 U T b ≠ 0)
    (a : Assignment (α := α) Uᶜ) :
    Q M1 U (T ∩ S) a = Q M2 U (T ∩ S) a ∧ Q M1 U (T ∩ Sᶜ) a = Q M2 U (T ∩ Sᶜ) a :=
  Q_ident_in M1 M2 U T S hT hcl hQ hpos _ T rfl (Finset.Subset.refl T)
    (fun _ _ _ hp _ => hp) a

end CFactor
end Identification

#print axioms Identification.CFactor.Q_split_rel
#print axioms Identification.CFactor.Q_le_one
#print axioms Identification.CFactor.Q_ident_within

/-! ## Runde 32: Tians IDENTIFY som induktivt predikat (`Reach`)

Tians rekursive prosedyre IDENTIFY(C, T, Q[T]) gjør to slags steg:

* marginaliser bort det som ikke er ancestralt for `C` innenfor `T` (runde 30, `Q_marg`);
* gå til en blokk som er lukket innenfor `T` (runde 31, `Q_ident_within`).

`Reach G U T C` sier at `C` kan nås fra `T` med en endelig følge av slike steg. Formen er
lånt fra Causaleans `CFactorReachableRec` (Jiyuan Tan, CausalSmith, Apache 2.0); beviset
her er vårt eget og bruker bare PMF-oppsettet i denne fila.

`reach_sound`: like og positive faktorer på `T` gir like og positive faktorer på `C`.
`reach_ident`: med `T = V` er `Q[C]` bestemt av den observerte fordelingen. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **`C` kan nås fra `T`** med Tians to steg. -/
inductive Reach (G : DAG V) (U : Finset V) : Finset V → Finset V → Prop
  /-- Ingenting å gjøre. -/
  | refl (T : Finset V) : Reach G U T T
  /-- Marginaliser bort `T ∖ S`, der `S` er ancestral innenfor `T`. -/
  | anc (T S C : Finset V) (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S)
      (h : Reach G U (T ∩ S) C) : Reach G U T C
  /-- Gå til en blokk som er lukket innenfor `T`. -/
  | block (T S C : Finset V) (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
      (h : Reach G U (T ∩ S) C) : Reach G U T C

/-- Steg kan settes etter hverandre. -/
theorem Reach.trans {U T S C : Finset V} (h1 : Reach G U T S) :
    Reach G U S C → Reach G U T C := by
  induction h1 with
  | refl T0 => exact id
  | anc T0 S0 C0 hS _ ih => exact fun h2 => Reach.anc T0 S0 C hS (ih h2)
  | block T0 S0 C0 hcl _ ih => exact fun h2 => Reach.block T0 S0 C hcl (ih h2)

/-- En lukket blokk nås fra `V` i ett steg. -/
theorem reach_closed (U S : Finset V) (hcl : IsClosedBlock G U S) :
    Reach G U Finset.univ S :=
  Reach.block Finset.univ S S (fun u hu v _ e => hcl u hu v e)
    (by rw [Finset.univ_inter]; exact Reach.refl S)

/-- **Sunnhet for `Reach`.** -/
theorem reach_sound [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U : Finset V)
    {T C : Finset V} (hR : Reach G U T C) :
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

/-- **IDENTIFY er sunn.** Kan `C` nås fra `V`, er `Q[C]` bestemt av den observerte
fordelingen (når den er positiv). -/
theorem reach_ident [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U C : Finset V)
    (hR : Reach G U Finset.univ C)
    (hM : M1.marginal Uᶜ = M2.marginal Uᶜ) (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0)
    (a : Assignment (α := α) Uᶜ) : Q M1 U C a = Q M2 U C a :=
  (reach_sound M1 M2 U hR (fun _ _ _ _ _ => Finset.mem_univ _)
    (fun b => by rw [← marginal_eq_Q, ← marginal_eq_Q, hM])
    (fun b => by rw [← marginal_eq_Q]; exact hpos b)).1 a

end CFactor
end Identification

#print axioms Identification.CFactor.Reach.trans
#print axioms Identification.CFactor.reach_sound
#print axioms Identification.CFactor.reach_ident

/-! ## Runde 33: ID-algoritmen er sunn for mengder

Under `do(X = x)` lever modellen på `G_{X̄}` (`cutIn G X`). Dens c-komponenter er `{x}`
for hver `x ∈ X`, rene latente blokker, og blokker `D` utenfor `X`. Da er

  `P_X(O) = ∏_D Q_X[D]`  og  `Q_X[D] = Q[D]`  for `D` disjunkt med `X`

(`marginal_prod` på intervensjonsmodellen og `Q_do_gen`). Kan hver slik `D` nås fra `V`
med Tians steg (`Reach`, runde 32), er hver faktor bestemt av den observerte fordelingen
(`reach_ident`), og dermed hele `P_X` (`id_sound`). Dette er ID-algoritmens linje 4, 6
og 7 satt sammen; linje 2 (å kutte til forfedrene til `Y`) er ikke tatt med, så
hypotesen ser på alle c-komponentene, ikke bare dem som teller for `Y`.

* `Q_lat`: faktoren for en rent latent blokk er 1.
* `id_sound_blocks`: versjonen med vilkårlige blokker.
* `ccomp_cutIn_X`: i `G_{X̄}` er c-komponenten til `x ∈ X` bare `{x}`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **En rent latent blokk har faktor 1.** -/
lemma Q_lat [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V) (hT : T ⊆ U)
    (a : Assignment (α := α) Uᶜ) : Q M U T a = 1 := by
  unfold Q
  rw [← lat_one M U T a]
  refine tsum_congr (fun w => ?_)
  rw [Finset.inter_eq_right.mpr hT]

/-- **ID-sunnhet med blokker.** Blokkene er lukkede i `G_{X̄}`, disjunkte og dekker alt.
Hver blokk ligger i `X`, er rent latent, eller er disjunkt med `X` og kan nås fra `V`. -/
theorem id_sound_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock (cutIn G X) U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i)
    (hblk : ∀ i ∈ I, B i ⊆ X ∨ B i ⊆ U ∨ (Disjoint (B i) X ∧ Reach G U Finset.univ (B i)))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Uᶜ = (doModel M2 X xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [marginal_prod (doModel M1 X xv) U B I hcl hdisj hcov a,
      marginal_prod (doModel M2 X xv) U B I hcl hdisj hcov a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rcases hblk i hi with hsub | hlat | ⟨hdis, hRi⟩
    · rw [Q_do_gen M1 U (B i) X hXO xv a, Q_do_gen M2 U (B i) X hXO xv a]
      simp only [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
    · rw [Q_lat (doModel M1 X xv) U (B i) hlat a, Q_lat (doModel M2 X xv) U (B i) hlat a]
    · rw [Q_do_gen M1 U (B i) X hXO xv a, Q_do_gen M2 U (B i) X hXO xv a,
        Finset.sdiff_eq_self_of_disjoint hdis]
      congr 1
      have h := reach_ident M1 M2 U (B i) hRi hM hpos a
      unfold Q at h
      exact h
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

/-- I `G_{X̄}` har `x ∈ X` ingen latente naboer: c-komponenten er `{x}`. -/
theorem ccomp_cutIn_X (G : DAG V) (U X : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (cutIn G X) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from e).2 (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **ID-algoritmen er sunn.** Kan hver c-komponent av `G_{X̄}` som inneholder en
observert node utenfor `X` nås fra `V` med Tians steg, er `P(Y | do(X))` identifiserbar. -/
theorem id_sound [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (hR : ∀ y, y ∉ U → y ∉ X → Reach G U Finset.univ (ccomp (cutIn G X) U y))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_blocks U X hXO id (Finset.univ.image (ccomp (cutIn G X) U)) ?_ ?_ ?_ ?_ Y hY
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (cutIn G X) U y
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v
    exact ⟨ccomp (cutIn G X) U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (cutIn G X) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl ((ccomp_cutIn_X G U X hXO hyX).trans (Finset.singleton_subset_iff.mpr hyX))
    · by_cases hU : ccomp (cutIn G X) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        have hdis : Disjoint (ccomp (cutIn G X) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (cutIn G X) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (cutIn G X) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_cutIn_X G U X hXO hzX hyz)]
            exact hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis hv h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvU hvX
        rw [ccomp_eq_of_mem hv] at hRv
        exact hRv

end CFactor
end Identification

#print axioms Identification.CFactor.Q_lat
#print axioms Identification.CFactor.id_sound_blocks
#print axioms Identification.CFactor.id_sound

/-! ## Runde 34: ID-algoritmens linje 2, avgrensning til forfedrene til `Y`

Runde 33 krevde at *alle* c-komponentene i `G_{X̄}` kunne nås. Linje 2 i ID-algoritmen
(Shpitser–Pearl 2006; Tian & Pearl 2002) ser bare på en ancestral mengde `S ⊇ Y`:

  `Σ_{O ∖ S} P_X(O) = Q_X[S] = ∏_D Q_X[S ∩ D]`,

der `D` løper over c-komponentene til `G_{X̄}[S]` (`DAG.induce (cutIn G X) S`). Første
likhet er `Q_marg` (runde 30) i intervensjonsmodellen, den andre en ny produktsetning der
blokkene bare trenger å være lukket innenfor `S` (`Q_prod_rel`). Kan hver `S ∩ D` som
inneholder en observert node utenfor `X` nås fra `V` (`Reach`), er `P(Y | do(X))`
identifiserbar (`id_sound_anc`). Med `S = An(Y)` i `G_{X̄}` er dette linje 2, 4, 6 og 7.

Overgangen fra summer over `O ∖ S` til marginalen på `Y` går via en omtelling
(`upd_iff`, `tsum_updX`, `fiber_eq`): to funksjoner med like summer over hver fiber
`{a[D := x'] : x'}` har like marginaler på enhver `Y` utenfor `D`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Produkt over blokker som bare er lukket innenfor `T₀`.** -/
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

/-- **Én blokk under `do(X)`.** Ligger `C` i `X`, er den rent latent, eller er den disjunkt
med `X` og kan nås fra `V`, er faktoren i intervensjonsmodellen den samme for to modeller
med samme positive observerte fordeling. -/
lemma Q_do_eq [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hM : M1.marginal Uᶜ = M2.marginal Uᶜ)
    (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0) (C : Finset V)
    (hC : C ⊆ X ∨ C ⊆ U ∨ (Disjoint C X ∧ Reach G U Finset.univ C))
    (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M1 X xv) U C a = Q (doModel M2 X xv) U C a := by
  rcases hC with hsub | hlat | ⟨hdis, hRi⟩
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a]
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
  · rw [Q_lat (doModel M1 X xv) U C hlat a, Q_lat (doModel M2 X xv) U C hlat a]
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a,
      Finset.sdiff_eq_self_of_disjoint hdis]
    congr 1
    have h := reach_ident M1 M2 U C hRi hM hpos a
    unfold Q at h
    exact h

/-- Omtelling: `a'` er `a` med `D` byttet ut, og `a` har en fast verdi `c₀` på `D`,
nøyaktig når `a` er `a'` med `D` satt til `c₀` og `x'` er `a'` på `D`. -/
lemma upd_iff (U D : Finset V) (hD : D ⊆ Uᶜ) (c0 x' : Assignment (α := α) D)
    (a a' : Assignment (α := α) Uᶜ) :
    (a' = updX U D a x' ∧ a.restrict hD = c0) ↔ (a = updX U D a' c0 ∧ x' = a'.restrict hD) := by
  constructor
  · rintro ⟨rfl, h2⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · have e := congrFun h2 ⟨v.1, hv⟩
        simp only [Assignment.restrict] at e
        simp only [updX, dif_pos hv]
        exact e
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · simp only [updX, dif_pos hv, Assignment.restrict]
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]

/-- **Summen over alle tilordninger, fiber for fiber.** -/
lemma tsum_updX (U D : Finset V) (hD : D ⊆ Uᶜ) (c0 : Assignment (α := α) D)
    (g : Assignment (α := α) Uᶜ → ENNReal) :
    ∑' a', g a' = ∑' a : Assignment (α := α) Uᶜ,
      (if a.restrict hD = c0 then ∑' x' : Assignment (α := α) D, g (updX U D a x') else 0) := by
  calc ∑' a', g a'
      = ∑' a' : Assignment (α := α) Uᶜ, ∑' a : Assignment (α := α) Uᶜ,
          ∑' x' : Assignment (α := α) D,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) := by
        refine tsum_congr (fun a' => ?_)
        rw [tsum_eq_single (updX U D a' c0)]
        · rw [tsum_eq_single (a'.restrict hD)]
          · rw [if_pos ((upd_iff U D hD c0 (a'.restrict hD) (updX U D a' c0) a').mpr
              ⟨rfl, rfl⟩)]
          · intro x' hx'
            rw [if_neg (fun h => hx' ((upd_iff U D hD c0 x' (updX U D a' c0) a').mp h).2)]
        · intro a ha
          exact ENNReal.tsum_eq_zero.mpr (fun x' =>
            if_neg (fun h => ha ((upd_iff U D hD c0 x' a a').mp h).1))
    _ = ∑' a : Assignment (α := α) Uᶜ, ∑' a' : Assignment (α := α) Uᶜ,
          ∑' x' : Assignment (α := α) D,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) := ENNReal.tsum_comm
    _ = ∑' a : Assignment (α := α) Uᶜ, ∑' x' : Assignment (α := α) D,
          ∑' a' : Assignment (α := α) Uᶜ,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) :=
        tsum_congr (fun a => ENNReal.tsum_comm)
    _ = _ := by
        refine tsum_congr (fun a => ?_)
        by_cases hP : a.restrict hD = c0
        · rw [if_pos hP]
          refine tsum_congr (fun x' => ?_)
          rw [tsum_eq_single (updX U D a x')]
          · rw [if_pos ⟨rfl, hP⟩]
          · intro a'' h
            rw [if_neg (fun h' => h h'.1)]
        · rw [if_neg hP]
          exact ENNReal.tsum_eq_zero.mpr (fun x' => ENNReal.tsum_eq_zero.mpr (fun a'' =>
            if_neg (fun h => hP h.2)))

/-- **Like fibersummer gir like marginaler** på enhver `Y` utenfor `D`. -/
lemma fiber_eq [∀ v, Nonempty (α v)] (U D : Finset V) (hD : D ⊆ Uᶜ) (Y : Finset V)
    (hY : Y ⊆ Uᶜ) (hYD : ∀ v ∈ Y, v ∉ D) (P1 P2 : Assignment (α := α) Uᶜ → ENNReal)
    (h : ∀ a, ∑' x' : Assignment (α := α) D, P1 (updX U D a x') =
      ∑' x' : Assignment (α := α) D, P2 (updX U D a x'))
    (b : Assignment (α := α) Y) :
    ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0) =
      ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P2 a else 0) := by
  have c0 : Assignment (α := α) D := fun _ => Classical.arbitrary _
  have hr : ∀ (a : Assignment (α := α) Uᶜ) (x' : Assignment (α := α) D),
      (updX U D a x').restrict hY = a.restrict hY := fun a x' => by
    funext ⟨v, hv⟩
    simp only [Assignment.restrict, updX, dif_neg (hYD v hv)]
  calc ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0)
      = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P1 (updX U D a x') else 0) else 0) :=
        tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P1 a else 0)
    _ = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P2 (updX U D a x') else 0) else 0) := by
        refine tsum_congr (fun a => ?_)
        simp only [hr]
        by_cases hb : b = a.restrict hY
        · simp only [if_pos hb]
          rw [h a]
        · simp only [if_neg hb]
    _ = _ := (tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P2 a else 0)).symm

/-- **ID med avgrensning til en ancestral mengde, med blokker.** -/
theorem id_sound_anc_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (S : Finset V) (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, ∀ u ∈ U, ∀ v ∈ S, (cutIn G X).edge u v → (u ∈ B i ↔ v ∈ B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : S ⊆ I.biUnion B)
    (hblk : ∀ i ∈ I, S ∩ B i ⊆ X ∨ S ∩ B i ⊆ U ∨
      (Disjoint (S ∩ B i) X ∧ Reach G U Finset.univ (S ∩ B i)))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hlat : IsLatClosed (cutIn G X) U Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  have hlatS : IsLatClosed (cutIn G X) U S := fun v hv u _ e => hS v hv u e
  have hS' : ∀ v ∈ Finset.univ ∩ S, ∀ p ∈ Finset.univ, (cutIn G X).edge p v → p ∈ S :=
    fun v hv p _ e => hS v (Finset.mem_inter.mp hv).2 p e
  have hDO : (Finset.univ ∩ Sᶜ) \ U ⊆ Uᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hYD : ∀ v ∈ Y, v ∉ (Finset.univ ∩ Sᶜ) \ U := fun v hv hvD =>
    Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvD).1).2 (hYS hv)
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Y = (doModel M2 X xv).marginal Y := by
    intro xv
    have hQS : ∀ a, Q (doModel M1 X xv) U S a = Q (doModel M2 X xv) U S a := fun a => by
      rw [Q_prod_rel (doModel M1 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a,
        Q_prod_rel (doModel M2 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a]
      exact Finset.prod_congr rfl (fun i hi => Q_do_eq M1 M2 U X hXO hM hpos _ (hblk i hi) xv a)
    have hfib : ∀ a, ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M1 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') =
        ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M2 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') := fun a => by
      rw [Q_marg (doModel M1 X xv) U Finset.univ S hlat hS' a,
        Q_marg (doModel M2 X xv) U Finset.univ S hlat hS' a, Finset.univ_inter S]
      exact hQS a
    ext b
    rw [← marginal_restrict (doModel M1 X xv) hY, ← marginal_restrict (doModel M2 X xv) hY,
      PMF.map_apply, PMF.map_apply]
    simp only [marginal_eq_Q]
    exact fiber_eq U ((Finset.univ ∩ Sᶜ) \ U) hDO Y hY hYD
      (Q (doModel M1 X xv) U Finset.univ) (Q (doModel M2 X xv) U Finset.univ) hfib b
  rw [hD]

/-- I `G_{X̄}[S]` har `x ∈ X` ingen latente naboer: c-komponenten er `{x}`. -/
theorem ccomp_ind_X (G : DAG V) (U X S : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (DAG.induce (cutIn G X) S) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from
        (show u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v from e).2.2).2
        (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **ID-algoritmen med linje 2.** La `S ⊇ Y` være ancestral i `G_{X̄}` (for eksempel
forfedrene til `Y`). Kan hver c-komponent av `G_{X̄}[S]` med en observert node utenfor `X`
nås fra `V` med Tians steg, er `P(Y | do(X))` identifiserbar. -/
theorem id_sound_anc [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ) (S : Finset V)
    (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    (hR : ∀ y ∈ S, y ∉ U → y ∉ X →
      Reach G U Finset.univ (S ∩ ccomp (DAG.induce (cutIn G X) S) U y))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_anc_blocks U X hXO S hS id
    (Finset.univ.image (ccomp (DAG.induce (cutIn G X) S) U)) ?_ ?_ ?_ ?_ Y hYS hY
  · intro i hi u hu v hv e
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (DAG.induce (cutIn G X) S) U y u hu v
      (⟨hS v hv u e, hv, e⟩ : u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v)
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v _
    exact Finset.mem_biUnion.mpr ⟨ccomp (DAG.induce (cutIn G X) S) U v,
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (DAG.induce (cutIn G X) S) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl (fun z hz => (Finset.singleton_subset_iff.mpr hyX)
        (ccomp_ind_X G U X S hXO hyX (Finset.mem_inter.mp hz).2))
    · by_cases hU : S ∩ ccomp (DAG.induce (cutIn G X) S) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        obtain ⟨hvS, hvC⟩ := Finset.mem_inter.mp hv
        have hdis0 : Disjoint (ccomp (DAG.induce (cutIn G X) S) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (DAG.induce (cutIn G X) S) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (DAG.induce (cutIn G X) S) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_ind_X G U X S hXO hzX hyz)]
            exact hzX)
        have hdis : Disjoint (S ∩ ccomp (DAG.induce (cutIn G X) S) U y) X :=
          Finset.disjoint_left.mpr (fun z hz hzX =>
            Finset.disjoint_left.mp hdis0 (Finset.mem_inter.mp hz).2 hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis0 hvC h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvS hvU hvX
        rw [ccomp_eq_of_mem hvC] at hRv
        exact hRv

end CFactor
end Identification

#print axioms Identification.CFactor.Q_prod_rel
#print axioms Identification.CFactor.fiber_eq
#print axioms Identification.CFactor.id_sound_anc_blocks
#print axioms Identification.CFactor.id_sound_anc

/-! ## Runde 36: Verma-begrensninger

Faktorene `Q[T]` gir likheter for den observerte fordelingen som ikke er betingede
uavhengigheter (Verma & Pearl 1990; Tian & Pearl 2002, avsnitt 4):

* `Q_local`: `Q[T]` avhenger bare av de observerte verdiene i `T` og hos foreldrene til `T`;
* `verma_sum`: er `S` ancestral innenfor `T`, er summen av `Q[T]` over de observerte i
  `T ∖ S` lik `Q[T ∩ S]` (`Q_marg`), og avhenger derfor bare av de observerte i `T ∩ S`
  og hos foreldrene deres.

Er `Q[T]` identifiserbar, er dette en begrensning på `P` selv. Fila `Verma.lean` regner ut
det klassiske eksemplet. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Faktoren er lokal.** -/
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
  exact kfac_congr M _ _ v (hf v (Or.inl hv)) (fun u hu => hf u (Or.inr ⟨v, hv, edge_of_par hu⟩))

/-- **Verma-begrensning, generell form.** -/
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

#print axioms Identification.CFactor.Q_local
#print axioms Identification.CFactor.verma_sum
