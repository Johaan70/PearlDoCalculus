import PearlDoCalculus.SetSound

/-!
# Do-kalkulus: intervensjoner, trunkert faktorisering og regel 1

`cutIn G X` er Pearls `G_{X̄}` (innkommende kanter til `X` fjernet), og
`cutOut G X` er `G_{X̲}` (utgående kanter fra `X` fjernet). `doModel M X x` er
intervensjonen `do(X = x)`: en kausalmodell på `cutIn G X` der nodene i `X` har
punktmasse på `x`, og resten beholder kjernene sine.

`doModel_fullJoint` er den trunkerte faktoriseringen, og viser at `doModel` er
Pearls intervensjon. Regel 1 følger da av `dsep_sound_set` på den manipulerte
modellen.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace DoCalculus

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- Pearls `G_{X̄}`: innkommende kanter til `X` fjernet. -/
def cutIn (G : DAG V) (X : Finset V) : DAG V where
  edge u v := G.edge u v ∧ v ∉ X
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := fun u v h => G.rank_strict_mono u v h.1

/-- Pearls `G_{X̲}`: utgående kanter fra `X` fjernet. -/
def cutOut (G : DAG V) (X : Finset V) : DAG V where
  edge u v := G.edge u v ∧ u ∉ X
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := fun u v h => G.rank_strict_mono u v h.1

lemma mem_parents_cutIn {X : Finset V} {u v : V} :
    u ∈ (cutIn G X).parents v ↔ u ∈ G.parents v ∧ v ∉ X := by
  simp [DAG.parents, cutIn]

/-- Nodene i `X` har ingen foreldre i `G_{X̄}`. -/
lemma parents_cutIn_of_mem {X : Finset V} {v : V} (hv : v ∈ X) :
    (cutIn G X).parents v = ∅ := by
  ext u
  simp [DAG.parents, cutIn, hv]

/-- Utenfor `X` er foreldrene de samme som i `G`. -/
lemma parents_cutIn_of_not_mem {X : Finset V} {v : V} (hv : v ∉ X) :
    (cutIn G X).parents v = G.parents v := by
  ext u
  simp [DAG.parents, cutIn, hv]

/-- **Intervensjonen `do(X = x)`.** Punktmasse på `x` i `X`; utenfor `X` er
kjernen uendret, med foreldretilordningen bygd direkte (ingen transport). -/
noncomputable def doModel {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) : (cutIn G X).CausalModel α where
  fin := M.fin
  deq := M.deq
  kernel := fun v p =>
    if hv : v ∈ X then PMF.pure (x ⟨v, hv⟩)
    else M.kernel v (fun u => p ⟨u.1, mem_parents_cutIn.mpr ⟨u.2, hv⟩⟩)

/-- Kjernefaktorene til intervensjonsmodellen: indikator i `X`, uendret utenfor. -/
lemma kfac_doModel {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X)
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel M X x) Finset.univ u v =
      if hv : v ∈ X then (if u ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩ then 1 else 0)
      else kfac M Finset.univ u v := by
  have hc : v ∈ (Finset.univ : Finset V) ∧ (cutIn G X).parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  have hc' : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  simp only [dif_pos hc, dif_pos hc']
  by_cases hv : v ∈ X
  · simp only [doModel, dif_pos hv, PMF.pure_apply]
  · simp only [doModel, dif_neg hv]
    all_goals rfl

/-- **Trunkert faktorisering.** Fellesfordelingen under `do(X = x)` er
indikatoren på `u_X = x` ganger kjernene utenfor `X`. -/
theorem doModel_fullJoint {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel M X x).fullJoint u =
      (if u.restrict (Finset.subset_univ X) = x then 1 else 0) *
        ∏ v ∈ Xᶜ, kfac M Finset.univ u v := by
  rw [fullJoint_apply_prod, ← Finset.prod_mul_prod_compl X]
  congr 1
  · by_cases h : u.restrict (Finset.subset_univ X) = x
    · rw [if_pos h]
      refine Finset.prod_eq_one (fun v hv => ?_)
      rw [kfac_doModel, dif_pos hv, if_pos]
      exact congrFun h ⟨v, hv⟩
    · rw [if_neg h]
      obtain ⟨⟨v, hv⟩, hne⟩ := Function.ne_iff.mp h
      refine Finset.prod_eq_zero hv ?_
      rw [kfac_doModel, dif_pos hv,
        if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩) from hne)]
  · exact Finset.prod_congr rfl (fun v hv => by
      rw [kfac_doModel, dif_neg (Finset.mem_compl.mp hv)])

/-- **Kontroll: intervensjonen setter `X`.** Under `do(X = x)` er marginalen
på `X` en punktmasse på `x`. -/
theorem doModel_marginal_self {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) :
    (doModel M X x).marginal X x = 1 := by
  rw [PMF.apply_eq_one_iff]
  have hsub : ((doModel M X x).marginal X).support ⊆ {x} := by
    intro a ha
    unfold CausalModel.marginal at ha
    rw [PMF.support_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    rw [Set.mem_singleton_iff]
    by_contra hne
    rw [PMF.mem_support_iff, doModel_fullJoint, if_neg hne, zero_mul] at hu
    exact hu rfl
  exact (PMF.support_nonempty _).subset_singleton_iff.mp hsub

/-- **Kontroll: `do(∅)` endrer ingenting.** -/
theorem doModel_empty {α : V → Type*} (M : G.CausalModel α)
    (x : Assignment (α := α) (∅ : Finset V))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel M ∅ x).fullJoint u = M.fullJoint u := by
  have hemp : u.restrict (Finset.subset_univ (∅ : Finset V)) = x :=
    funext fun t => by obtain ⟨v, hv⟩ := t; simp at hv
  rw [doModel_fullJoint, if_pos hemp, one_mul, Finset.compl_empty, fullJoint_apply_prod]

/-- **Regel 1 (fjerning av observasjon).** Er `Y` og `Z` d-separert av `X ∪ W`
i `G_{X̄}`, er de betinget uavhengige gitt `X ∪ W` under `do(X = x)`. -/
theorem rule1 {α : V → Type*} (M : G.CausalModel α) (X W Y Z : Finset V)
    (x : Assignment (α := α) X)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W))
    (h : SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z) :
    (doModel M X x).CondIndep Y Z (X ∪ W) :=
  SetSound.dsep_sound_set (doModel M X x) Y Z (X ∪ W) hY hZ h

end DoCalculus

#print axioms DoCalculus.kfac_doModel
#print axioms DoCalculus.doModel_fullJoint
#print axioms DoCalculus.doModel_marginal_self
#print axioms DoCalculus.doModel_empty
#print axioms DoCalculus.rule1
