import PearlDoCalculus.Completeness

/-!
# Identifikasjon med latente variabler, runde 1

Bare nodene i `O` er observert. Effekten av `do(X)` på `Y` er **identifiserbar**
fra `O` i `G` hvis to modeller på `G` med samme positive fordeling på `O` alltid gir
samme intervensjonsfordeling på `Y`. Dette er Pearls og Shpitser–Pearls definisjon,
med positivitet slik den brukes i litteraturen.

Bevist her: back-door- og front-door-kriteriet gir identifiserbarhet når `X`, `Y` og
`Z` er observert, uansett hvilke andre noder som er latente.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Identifiserbarhet.** `P(Y | do(X))` er bestemt av den positive fordelingen på `O`. -/
def Identifiable (G : DAG V) (α : V → Type*) (O X Y : Finset V) : Prop :=
  ∀ M₁ M₂ : G.CausalModel α, M₁.marginal O = M₂.marginal O →
    (∀ a, M₁.marginal O a ≠ 0) →
    ∀ t : Assignment (α := α) (Y ∪ X),
      (doModel M₁ X (t.restrict (show X ⊆ Y ∪ X by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
          (t.restrict (show Y ⊆ Y ∪ X by
            intro v hv; simp only [Finset.mem_union]; tauto)) =
      (doModel M₂ X (t.restrict (show X ⊆ Y ∪ X by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
          (t.restrict (show Y ⊆ Y ∪ X by
            intro v hv; simp only [Finset.mem_union]; tauto))

/-- Samme fordeling på `O` gir samme fordeling på enhver delmengde. -/
lemma marginal_eq_of_sub {G : DAG V} {α : V → Type*} {M₁ M₂ : G.CausalModel α}
    {O T : Finset V} (h : M₁.marginal O = M₂.marginal O) (hT : T ⊆ O) :
    M₁.marginal T = M₂.marginal T := by
  rw [← marginal_restrict M₁ hT, ← marginal_restrict M₂ hT, h]

/-- Positivitet på `O` gir positivitet på enhver delmengde. -/
lemma marginal_pos_of_sub {G : DAG V} {α : V → Type*} [∀ w, Nonempty (α w)]
    {M : G.CausalModel α} {O T : Finset V} (hpos : ∀ a, M.marginal O a ≠ 0) (hT : T ⊆ O)
    (b : Assignment (α := α) T) : M.marginal T b ≠ 0 := by
  obtain ⟨a, ha⟩ := Completeness.exists_restrict_eq hT b
  rw [← marginal_restrict M hT, PMF.map_apply]
  intro h0
  rw [ENNReal.tsum_eq_zero] at h0
  have h1 := h0 a
  rw [if_pos ha.symm] at h1
  exact hpos a h1

/-- **Back-door gir identifiserbarhet.** Oppfyller `Z` back-door-kriteriet og er
`X`, `Y` og `Z` observert, er `P(Y | do(X))` identifiserbar. -/
theorem backdoor_identifiable (G : DAG V) (α : V → Type*) [∀ w, Nonempty (α w)]
    (O X Y Z : Finset V) (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hcrit : Adjustment.BackdoorCriterion G X Y Z) (hO : Y ∪ X ∪ Z ⊆ O) :
    Identifiable G α O X Y := by
  unfold Identifiable
  intro M₁ M₂ hM hpos t
  have hpos₂ : ∀ a, M₂.marginal O a ≠ 0 := by
    intro a
    rw [← hM]
    exact hpos a
  have hsub : Y ∪ X ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hZO : Z ⊆ O := fun v hv => hO (by simp only [Finset.mem_union]; tauto)
  have hXZO : X ∪ Z ⊆ O := by
    intro v hv; apply hO; simp only [Finset.mem_union] at hv ⊢; tauto
  obtain ⟨t', ht'⟩ := Completeness.exists_restrict_eq hsub t
  have eX : t.restrict (show X ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto) =
      t'.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto) := by
    rw [← ht', Assignment.restrict_restrict]
  have eY : t.restrict (show Y ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto) =
      t'.restrict (show Y ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto) := by
    rw [← ht', Assignment.restrict_restrict]
  rw [eX, eY,
    Adjustment.backdoor_adjustment_criterion M₁ X Y Z hYX hZX hYZ hcrit t'
      (fun z => marginal_pos_of_sub hpos hXZO _),
    Adjustment.backdoor_adjustment_criterion M₂ X Y Z hYX hZX hYZ hcrit t'
      (fun z => marginal_pos_of_sub hpos₂ hXZO _),
    marginal_eq_of_sub hM hO, marginal_eq_of_sub hM hZO, marginal_eq_of_sub hM hXZO]

/-- **Front-door gir identifiserbarhet.** Oppfyller `Z` front-door-kriteriet og er
`X`, `Y` og `Z` observert, er `P(Y | do(X))` identifiserbar, også når alt annet
(for eksempel en felles årsak til `X` og `Y`) er latent. -/
theorem frontdoor_identifiable (G : DAG V) (α : V → Type*) [∀ w, Nonempty (α w)]
    (O X Y Z : Finset V) (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (hc : Adjustment.FrontdoorCriterion G X Y Z) (hO : Y ∪ X ∪ Z ⊆ O) :
    Identifiable G α O X Y := by
  unfold Identifiable
  intro M₁ M₂ hM hpos t
  have hpos₂ : ∀ a, M₂.marginal O a ≠ 0 := by
    intro a
    rw [← hM]
    exact hpos a
  have hsub : Y ∪ X ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hXO : X ⊆ O := fun v hv => hO (by simp only [Finset.mem_union]; tauto)
  have hZXO : Z ∪ X ⊆ O := by
    intro v hv; apply hO; simp only [Finset.mem_union] at hv ⊢; tauto
  have hYZXO : Y ∪ Z ∪ X ⊆ O := by
    intro v hv; apply hO; simp only [Finset.mem_union] at hv ⊢; tauto
  obtain ⟨t', ht'⟩ := Completeness.exists_restrict_eq hsub t
  have eX : t.restrict (show X ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto) =
      t'.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto) := by
    rw [← ht', Assignment.restrict_restrict]
  have eY : t.restrict (show Y ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto) =
      t'.restrict (show Y ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto) := by
    rw [← ht', Assignment.restrict_restrict]
  rw [eX, eY,
    Adjustment.frontdoor_adjustment_criterion M₁ X Y Z hZX hYX hYZ hc t'
      (marginal_pos_of_sub hpos hXO _) (fun z x' => marginal_pos_of_sub hpos hZXO _),
    Adjustment.frontdoor_adjustment_criterion M₂ X Y Z hZX hYX hYZ hc t'
      (marginal_pos_of_sub hpos₂ hXO _) (fun z x' => marginal_pos_of_sub hpos₂ hZXO _),
    marginal_eq_of_sub hM hXO, marginal_eq_of_sub hM hZXO, marginal_eq_of_sub hM hYZXO]

end Identification

#print axioms Identification.backdoor_identifiable
#print axioms Identification.frontdoor_identifiable
