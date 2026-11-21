import PearlDoCalculus.Identification.LatentSplit

/-!
# Tian's factorization and identification theorem (c-factor side, first part)

The positive side of the identification theory begins here. Let `U` be the latent
nodes and `O = Uᶜ` the observed ones. A block `S` is *closed* when every latent edge
`u → v` stays inside `S` or inside `Sᶜ`. Then the distribution on the observed nodes
factors with one factor `Q[S]` per block (round 20, Tian's lemma 1), the factors are
identifiable from `P(O)` (round 21, Tian's lemma 2), this gives Tian's identification
theorem (round 22), and the c-component is the smallest closed block (round 23).

Main results:
* `CFactor.Q`, `CFactor.kfac_congr`: the factors and their basic facts. The full
  assignments the factors read (`fill`, `joinBlocks`) and how they split into their parts
  are in `Identification/LatentSplit`.
* `CFactor.anc_factor`, `CFactor.marginal_factor`, `CFactor.do_marginal_factor`: the
  factorization on an ancestral set, its case `A = univ`, and that an intervention in `S`
  changes only `Q[S]`.
* `CFactor.Q_identifiable`, `CFactor.Q_step`: the factors are determined by `P(O)`.
* `CFactor.tian_identifiable`, `CFactor.tian_identifiable_ccomp`: Tian's theorem.
* `CFactor.ccomp_isLeast`: the c-component is the smallest closed block.

(The comments of the rounds below are still in Norwegian.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 20: c-komponent-faktorisering (Tians lemma 1)

Den positive siden begynner her. La `U` være de latente nodene og `O = Uᶜ` de observerte.
En blokk `S` er *lukket* når hver latent kant `u → v` (`u ∈ U`) går innenfor `S` eller
innenfor `Sᶜ`. Da faktoriserer fordelingen på de observerte i én faktor per blokk:

  `P(O = a) = Q[S](a) · Q[Sᶜ](a)`,   `Q[T](a) = Σ_{w latent i T} Π_{v ∈ T} P(v | pa(v))`.

Under en intervensjon i `S` endres bare `Q[S]`; `Q[Sᶜ]` er den samme (`do_marginal_factor`).
Det er kjernen i ID-algoritmen. Tian krever at de latente er røtter; her trengs bare
lukketheten. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Faktoren `Q[T]`:** summen over de latente i `T` av kjernene i `T`. -/
noncomputable def Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) : ENNReal :=
  ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T, kfac M Finset.univ (fill U T a w) v

/-- Kjernefaktoren avhenger bare av noden selv og foreldrene. -/
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

/-- **En intervensjon i `S` endrer bare faktoren for `S`.** Faktoren for resten er den
samme som uten intervensjon. -/
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

/-! ## Runde 21: faktorene er identifiserbare (Tians lemma 2)

Runde 20 delte `P(O)` i `Q[S] · Q[Sᶜ]`. Her vises at hver faktor er bestemt av den
observerte fordelingen alene.

1. `anc_factor` (proved before `marginal_factor` above, which is its case `A = univ`):
   the factorization holds on every ancestral set `A`: `P(O ∩ A) = Q[A ∩ S] · Q[A ∩ Sᶜ]`.
2. `Q_step` (den eksplisitte formelen): fjernes en node `v ∈ T` uten barn i `A`, er
   `P(O ∩ A) · Q[A' ∩ T] = P(O ∩ A') · Q[A ∩ T]`, med `A' = A ∖ {v}`. Altså
   `Q[A ∩ T] = Q[A' ∩ T] · P(O ∩ A) / P(O ∩ A')`, og for en observert `v` er brøken
   `P(v | O ∩ A')`. Gjentatt fra `A = ∅` til alle noder gir det Tians produkt
   `Q[S] = ∏_{o ∈ S} P(o | forgjengerne til o)`.
3. `Q_identifiable`: to modeller med samme positive fordeling på `O` har samme `Q[S]` og
   samme `Q[Sᶜ]`. Beviset er induksjon over ancestrale mengder med `Q_step`.

Ingen antagelse om at de latente er røtter. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Den eksplisitte formelen (ett steg).** `Q[A ∩ T] = Q[A' ∩ T] · P(O ∩ A) / P(O ∩ A')`,
skrevet uten divisjon. -/
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

/-- Induksjon over ancestrale mengder: begge faktorene er like i de to modellene. -/
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

/-- **Tians lemma 2 (identifiserbarhet).** Samme positive fordeling på de observerte gir
samme `Q[S]` og samme `Q[Sᶜ]`, for hver lukket blokk `S`. -/
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

/-! ## Runde 22: Tians identifikasjonsteorem

La `x` være observert og ligge i en lukket blokk `S` som ikke inneholder noe barn av `x`.
Da er `P(· | do(x))` identifiserbar, med den eksplisitte formelen (`tian_formula`)

  `P_x(a) = [a_x = x] · (Σ_{x'} Q[S](a[x := x'])) · Q[Sᶜ](a)`.

Begge faktorene er bestemt av den observerte fordelingen (runde 21, `Q_step` gir dem
eksplisitt), så effekten er identifiserbar (`tian_identifiable`). Den omvendte retningen,
der et barn av `x` ligger i blokken, er hedgene fra runde 14–19.

Kjernen er `sum_Q_upd`: summert over verdiene til `x` faller `x` sin egen kjerne bort
(den summerer til 1), og ingen annen kjerne i `S` leser `x`. Det som blir igjen er nøyaktig
faktoren intervensjonsmodellen bruker (`Q_do`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `a` med verdien i `x` byttet ut med `x'`. -/
noncomputable def upd (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ)
    (x' : α x) : Assignment (α := α) Uᶜ :=
  Function.update a ⟨x, Finset.mem_compl.mpr hx⟩ x'

lemma upd_self (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ) (x' : α x)
    (h : x ∈ Uᶜ) : upd U hx a x' ⟨x, h⟩ = x' :=
  Function.update_self _ _ _

lemma upd_ne (U : Finset V) {x : V} (hx : x ∉ U) (a : Assignment (α := α) Uᶜ) (x' : α x)
    {z : V} (h : z ∈ Uᶜ) (hzx : z ≠ x) : upd U hx a x' ⟨z, h⟩ = a ⟨z, h⟩ :=
  Function.update_of_ne (fun e => hzx (congrArg Subtype.val e)) _ _

lemma fill_upd_ne [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (x' : α x) (w : Assignment (α := α) (U ∩ T)) (z : V)
    (hzx : z ≠ x) :
    fill U T (upd U hx a x') w ⟨z, Finset.mem_univ z⟩ = fill U T a w ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [fill, h0]
  · simp only [fill, dif_neg h0]
    exact upd_ne U hx a x' (Finset.mem_compl.mpr h0) hzx

lemma fill_upd_x [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (x' : α x) (w : Assignment (α := α) (U ∩ T)) :
    fill U T (upd U hx a x') w ⟨x, Finset.mem_univ x⟩ = x' := by
  simp only [fill, dif_neg hx]
  exact upd_self U hx a x' _

lemma fill_x [∀ v, Nonempty (α v)] (U T : Finset V) {x : V} (hx : x ∉ U)
    (a : Assignment (α := α) Uᶜ) (w : Assignment (α := α) (U ∩ T)) :
    fill U T a w ⟨x, Finset.mem_univ x⟩ = a ⟨x, Finset.mem_compl.mpr hx⟩ := by
  simp [fill, hx]

/-- **`x` summeres bort.** Ingen kjerne i `S` utenom `x` sin egen leser `x`, og `x` sin
egen kjerne summerer til 1. -/
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

/-- Faktoren for `S` i intervensjonsmodellen: indikatoren for `x`, ganger det som blir
igjen av `Q[S]` når `x` sin kjerne fjernes. -/
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

/-- **Tians formel.** -/
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

/-- **Tians identifikasjonsteorem.** Ligger intet barn av `x` i `x` sin lukkede blokk, er
effekten av `x` på enhver mengde observerte `Y` identifiserbar. -/
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

/-! ## Runde 23: c-komponenten er den minste lukkede blokken

Et *latent steg* er en kant med latent hale, tatt i hvilken som helst retning. C-komponenten
til `x` er alle noder `x` når med latente steg (`ccomp`). Den er

* lukket (`ccomp_closed`): ingen latent kant krysser grensen,
* inneholder `x`,
* og ligger i hver lukket blokk som inneholder `x` (`ccomp_subset`).

Altså er den den minste lukkede blokken rundt `x` (`ccomp_isLeast`). Følgen er at Tians
betingelse i runde 22 ("en lukket blokk rundt `x` uten barn av `x`") er nøyaktig "intet barn
av `x` i c-komponenten til `x`" (`tian_cond_iff`), og teoremet kan skrives med
c-komponenten direkte (`tian_identifiable_ccomp`). -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {α : V → Type*}

/-- Ett latent steg mellom `a` og `b`: en kant med latent hale, i en av retningene. -/
def latStep (G : DAG V) (U : Finset V) (a b : V) : Prop :=
  (a ∈ U ∧ G.edge a b) ∨ (b ∈ U ∧ G.edge b a)

/-- En blokk er lukket når ingen latent kant krysser grensen. -/
def IsClosedBlock (G : DAG V) (U S : Finset V) : Prop :=
  ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)

/-- **C-komponenten til `x`:** alle noder `x` når med latente steg. -/
noncomputable def ccomp (G : DAG V) (U : Finset V) (x : V) : Finset V :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (latStep G U) x v)

lemma mem_ccomp {G : DAG V} {U : Finset V} {x v : V} :
    v ∈ ccomp G U x ↔ Relation.ReflTransGen (latStep G U) x v := by
  simp [ccomp]

lemma self_mem_ccomp (G : DAG V) (U : Finset V) (x : V) : x ∈ ccomp G U x :=
  mem_ccomp.mpr Relation.ReflTransGen.refl

/-- C-komponenten er lukket. -/
theorem ccomp_closed (G : DAG V) (U : Finset V) (x : V) : IsClosedBlock G U (ccomp G U x) := by
  intro u hu v e
  rw [mem_ccomp, mem_ccomp]
  exact ⟨fun h => h.tail (Or.inl ⟨hu, e⟩), fun h => h.tail (Or.inr ⟨hu, e⟩)⟩

/-- C-komponenten ligger i hver lukket blokk som inneholder `x`. -/
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

/-- **C-komponenten er den minste lukkede blokken som inneholder `x`.** -/
theorem ccomp_isLeast (G : DAG V) (U : Finset V) (x : V) :
    IsLeast {S : Finset V | IsClosedBlock G U S ∧ x ∈ S} (ccomp G U x) := by
  refine ⟨?_, ?_⟩
  · show IsClosedBlock G U (ccomp G U x) ∧ x ∈ ccomp G U x
    exact ⟨ccomp_closed G U x, self_mem_ccomp G U x⟩
  · intro S hS
    simp only [Set.mem_setOf_eq] at hS
    exact ccomp_subset hS.1 hS.2

/-- **Tians betingelse er en betingelse på c-komponenten.** Det finnes en lukket blokk rundt
`x` uten barn av `x` hvis og bare hvis c-komponenten til `x` ikke inneholder noe barn av `x`. -/
theorem tian_cond_iff {G : DAG V} {U : Finset V} {x : V} :
    (∃ S, IsClosedBlock G U S ∧ x ∈ S ∧ ∀ v ∈ S, ¬ G.edge x v) ↔
      ∀ v ∈ ccomp G U x, ¬ G.edge x v := by
  constructor
  · rintro ⟨S, hS, hxS, h⟩ v hv
    exact h v (ccomp_subset hS hxS hv)
  · intro h
    exact ⟨ccomp G U x, ccomp_closed G U x, self_mem_ccomp G U x, h⟩

/-- **Tians teorem med c-komponenten.** Er intet barn av `x` i c-komponenten til `x`, er
effekten av `x` på enhver mengde observerte `Y` identifiserbar. -/
theorem tian_identifiable_ccomp {G : DAG V} [∀ v, Nonempty (α v)] (U : Finset V) {x : V}
    (hx : x ∉ U) (hch : ∀ v ∈ ccomp G U x, ¬ G.edge x v) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ {x} Y :=
  tian_identifiable U (ccomp G U x) hx (self_mem_ccomp G U x) hch (ccomp_closed G U x) Y hY

end CFactor
end Identification

#print axioms Identification.CFactor.ccomp_isLeast
#print axioms Identification.CFactor.tian_cond_iff
#print axioms Identification.CFactor.tian_identifiable_ccomp
