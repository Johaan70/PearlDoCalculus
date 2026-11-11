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

/-! ## Runde 2: monotoni og fullt observerte modeller -/

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Flere observerte noder gjør det ikke vanskeligere å identifisere. -/
theorem Identifiable.mono {G : DAG V} {α : V → Type*} {O O' X Y : Finset V} (hOO : O ⊆ O')
    (h : Identifiable G α O X Y) [∀ w, Nonempty (α w)] : Identifiable G α O' X Y := by
  unfold Identifiable at h ⊢
  intro M₁ M₂ hM hpos t
  exact h M₁ M₂ (marginal_eq_of_sub hM hOO) (marginal_pos_of_sub hpos hOO) t

/-- `v` og alle forfedrene til `v`. -/
noncomputable def ancSelf (G : DAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Reaches w v)

lemma ancSelf_closed (G : DAG V) (v : V) :
    ∀ u ∈ ancSelf G v, ∀ w, G.edge w u → w ∈ ancSelf G v := by
  intro u hu w hw
  simp only [ancSelf, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact Relation.ReflTransGen.head hw hu

lemma rank_le_of_reaches {G : DAG V} {a b : V} (h : G.Reaches a b) : G.rank a ≤ G.rank b := by
  have h' : Relation.ReflTransGen G.edge a b := h
  clear h
  induction h' with
  | refl => exact le_refl _
  | tail _ hbd ih => exact le_trans ih (le_of_lt (G.rank_strict_mono _ _ hbd))

lemma ancSelf_erase_closed (G : DAG V) (v : V) :
    ∀ u ∈ (ancSelf G v).erase v, ∀ w, G.edge w u → w ∈ (ancSelf G v).erase v := by
  intro u hu w hw
  rw [Finset.mem_erase] at hu ⊢
  refine ⟨fun hwv => ?_, ancSelf_closed G v u hu.2 w hw⟩
  rw [hwv] at hw
  have hr : G.Reaches u v := by
    simpa [ancSelf] using hu.2
  have h1 := rank_le_of_reaches hr
  have h2 := G.rank_strict_mono v u hw
  omega

lemma mem_ancSelf (G : DAG V) (v : V) : v ∈ ancSelf G v := by
  simp only [ancSelf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.ReflTransGen.refl

/-- **Kjernene er bestemt av den positive fellesfordelingen.** -/
lemma kfac_eq_of_joint {G : DAG V} {α : V → Type*} [∀ w, Nonempty (α w)]
    {M₁ M₂ : G.CausalModel α}
    (hM : M₁.marginal Finset.univ = M₂.marginal Finset.univ)
    (hpos : ∀ a, M₁.marginal Finset.univ a ≠ 0)
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac M₁ Finset.univ u v = kfac M₂ Finset.univ u v := by
  have hA := ancSelf_closed G v
  have hB := ancSelf_erase_closed G v
  have hvA := mem_ancSelf G v
  have hBA : (ancSelf G v).erase v ⊆ ancSelf G v := Finset.erase_subset v _
  have hpaA : G.parents v ⊆ ancSelf G v := fun w hw => hA v hvA w (by
    simpa [DAG.parents] using hw)
  set a := u.restrict (Finset.subset_univ (ancSelf G v)) with ha
  have split : ∀ M : G.CausalModel α, M.marginal (ancSelf G v) a =
      kfac M (ancSelf G v) a v * M.marginal ((ancSelf G v).erase v) (a.restrict hBA) := by
    intro M
    rw [marginal_ancestral_apply M _ hA a, marginal_ancestral_apply M _ hB (a.restrict hBA),
      ← Finset.mul_prod_erase _ _ hvA]
    congr 1
    refine Finset.prod_congr rfl (fun w hw => ?_)
    have hpaw : G.parents w ⊆ (ancSelf G v).erase v := fun x hx => hB w hw x (by
      simpa [DAG.parents] using hx)
    exact (kfac_restrict M hBA a hw hpaw).symm
  have hA12 := marginal_eq_of_sub hM (Finset.subset_univ (ancSelf G v))
  have hB12 := marginal_eq_of_sub hM (Finset.subset_univ ((ancSelf G v).erase v))
  have e := split M₁
  rw [hA12, split M₂, hB12] at e
  have hP0 : M₂.marginal ((ancSelf G v).erase v) (a.restrict hBA) ≠ 0 := by
    rw [← hB12]
    exact marginal_pos_of_sub hpos (Finset.subset_univ _) _
  have hPT : M₂.marginal ((ancSelf G v).erase v) (a.restrict hBA) ≠ ⊤ := PMF.apply_ne_top _ _
  have hk : kfac M₁ (ancSelf G v) a v = kfac M₂ (ancSelf G v) a v :=
    by
      first
      | exact ((ENNReal.mul_left_inj hP0 hPT).mp e).symm
      | exact (ENNReal.mul_right_cancel hP0 hPT e).symm
      | exact ((mul_left_inj' hP0).mp e).symm
      | exact (by
          have h1 := congrArg (· / M₂.marginal ((ancSelf G v).erase v) (a.restrict hBA)) e
          simp only [ENNReal.mul_div_cancel_right hP0 hPT] at h1
          exact h1.symm)
      | exact?
  rw [← kfac_restrict M₁ (Finset.subset_univ _) u hvA hpaA,
    ← kfac_restrict M₂ (Finset.subset_univ _) u hvA hpaA]
  exact hk

/-- **Fullt observert ⇒ identifiserbart.** Er alle noder observert, er enhver
intervensjonsfordeling bestemt av den positive fellesfordelingen (trunkert
faktorisering). -/
theorem observed_identifiable (G : DAG V) (α : V → Type*) [∀ w, Nonempty (α w)]
    (X Y : Finset V) : Identifiable G α Finset.univ X Y := by
  unfold Identifiable
  intro M₁ M₂ hM hpos t
  have hF : (doModel M₁ X (t.restrict (show X ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto))).fullJoint =
      (doModel M₂ X (t.restrict (show X ⊆ Y ∪ X by
        intro v hv; simp only [Finset.mem_union]; tauto))).fullJoint := by
    ext u
    rw [doModel_fullJoint, doModel_fullJoint]
    congr 1
    exact Finset.prod_congr rfl (fun v _ => kfac_eq_of_joint hM hpos u v)
  unfold CausalModel.marginal
  rw [hF]

end Identification

#print axioms Identification.observed_identifiable
