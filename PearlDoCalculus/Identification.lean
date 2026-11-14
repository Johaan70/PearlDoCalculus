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

/-! ## Runde 3: bue-grafen er ikke identifiserbar

`U = 0` (latent), `X = 1`, `Y = 2`, med `U → X`, `U → Y`, `X → Y`. To modeller gir
samme positive fordeling på `{X, Y}`, men ulik `P(Y | do(X))`.

* Modell A: `U` uniform, `X` en støyende kopi av `U`, `Y = U` (overser `X`).
* Modell B: `U = 0` fast, `X` uniform, `Y` en støyende kopi av `X`.

Fellesfordelingene er like etter en bijeksjon som bare endrer `U`. I A er
`P_x(Y)` lik for begge `x` (B2), i B er `P(x, y) = P_x(y) · P(x)` (FD1), og
kanalen skiller `x`: `3/4 ≠ 1/4`. -/

open scoped ENNReal

namespace Identification
namespace Bow

/-- Bue-grafen. -/
def bowG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v =>
    inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Grafen for modell A: `U → X`, `U → Y`. -/
def gA : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Grafen for modell B: `X → Y`. -/
def gB : DAG (Fin 3) where
  edge u v := u = 1 ∧ v = 2
  decEdge := fun u v => inferInstanceAs (Decidable (u = 1 ∧ v = 2))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩
    decide

lemma pA1 : (0 : Fin 3) ∈ gA.parents 1 := by simp [DAG.parents, gA]
lemma pA2 : (0 : Fin 3) ∈ gA.parents 2 := by simp [DAG.parents, gA]
lemma pB2 : (1 : Fin 3) ∈ gB.parents 2 := by simp [DAG.parents, gB]

lemma q_sum : (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  first
  | (rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
     exact ENNReal.div_self (by norm_num) (by norm_num))
  | (rw [ENNReal.div_add_div_same]; norm_num; exact ENNReal.div_self (by norm_num) (by norm_num))
  | norm_num
  | simp

lemma q_ne : (3 / 4 : ℝ≥0∞) ≠ 1 / 4 := by
  intro h
  first
  | (have h2 := congrArg ENNReal.toReal h; norm_num [ENNReal.toReal_div] at h2)
  | (rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at h
     norm_num at h)
  | (have h2 := congrArg (· * 4) h
     simp only at h2
     rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num),
       ENNReal.div_mul_cancel (by norm_num) (by norm_num)] at h2
     norm_num at h2)

lemma q_pos3 : (3 / 4 : ℝ≥0∞) ≠ 0 := by
  first
  | simp
  | norm_num
  | exact ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩

lemma q_pos1 : (1 / 4 : ℝ≥0∞) ≠ 0 := by
  first
  | simp
  | norm_num
  | exact ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩

/-- Støyende kanal: `c = b` med sannsynlighet 3/4. -/
noncomputable def chan (b : Bool) : PMF Bool :=
  PMF.ofFintype (fun c => if c = b then 3 / 4 else 1 / 4) (by
    rw [Fintype.sum_bool]
    cases b
    · rw [if_neg (show ¬ (true = false) by decide), if_pos (show false = false from rfl),
        add_comm]
      exact q_sum
    · rw [if_pos (show true = true from rfl), if_neg (show ¬ (false = true) by decide)]
      exact q_sum)

lemma chan_apply (b c : Bool) : chan b c = if c = b then 3 / 4 else 1 / 4 :=
  PMF.ofFintype_apply _ _

lemma chan_ne_zero (b c : Bool) : chan b c ≠ 0 := by
  rw [chan_apply]
  split_ifs
  · exact q_pos3
  · exact q_pos1

/-- Modell A: `U` uniform, `X` støyende kopi av `U`, `Y = U`. -/
noncomputable def NA : gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h1 : v = 1 then chan (pa ⟨0, by rw [h1]; exact pA1⟩)
    else if h2 : v = 2 then PMF.pure (pa ⟨0, by rw [h2]; exact pA2⟩)
    else PMF.uniformOfFintype Bool

/-- Modell B: `U = 0`, `X` uniform, `Y` støyende kopi av `X`. -/
noncomputable def NB : gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h2 : v = 2 then chan (pa ⟨1, by rw [h2]; exact pB2⟩)
    else if v = 1 then PMF.uniformOfFintype Bool
    else PMF.pure false

lemma NA_k0 (pa : {u // u ∈ gA.parents 0} → Bool) : NA.kernel 0 pa = PMF.uniformOfFintype Bool := by
  first | rfl | simp [NA]
lemma NA_k1 (pa : {u // u ∈ gA.parents 1} → Bool) : NA.kernel 1 pa = chan (pa ⟨0, pA1⟩) := by
  first | rfl | simp [NA]
lemma NA_k2 (pa : {u // u ∈ gA.parents 2} → Bool) : NA.kernel 2 pa = PMF.pure (pa ⟨0, pA2⟩) := by
  first | rfl | simp [NA]
lemma NB_k0 (pa : {u // u ∈ gB.parents 0} → Bool) : NB.kernel 0 pa = PMF.pure false := by
  first | rfl | simp [NB]
lemma NB_k1 (pa : {u // u ∈ gB.parents 1} → Bool) : NB.kernel 1 pa = PMF.uniformOfFintype Bool := by
  first | rfl | simp [NB]
lemma NB_k2 (pa : {u // u ∈ gB.parents 2} → Bool) : NB.kernel 2 pa = chan (pa ⟨1, pB2⟩) := by
  first | rfl | simp [NB]

lemma hsA : ∀ v, gA.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) := hu
  tauto

lemma hsB : ∀ v, gB.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : u = 1 ∧ v = 2 := hu
  tauto

noncomputable def mA : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub hsA NA
noncomputable def mB : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub hsB NB

lemma kfac_lift {G H : DAG (Fin 3)} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool))
    (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) (v : Fin 3) :
    kfac (Completeness.liftSub hsub N) Finset.univ u v = kfac N Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_do {G H : DAG (Fin 3)} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool)) (X : Finset (Fin 3))
    (x : Assignment (α := fun _ : Fin 3 => Bool) X)
    (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) (v : Fin 3) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ u v =
      kfac (doModel N X x) Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

/-- Bijeksjonen: endrer bare `U`, til `U xor Y`. -/
def φ (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3)) :=
  fun v => if v.1 = 0 then xor (u ⟨0, Finset.mem_univ 0⟩) (u ⟨2, Finset.mem_univ 2⟩) else u v

lemma φ_invol (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    φ (φ u) = u := by
  funext ⟨v, hv⟩
  by_cases h : v = 0
  · subst h
    simp [φ, Bool.xor_assoc]
  · simp [φ, h]

lemma joint_eq (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    mB.fullJoint (φ u) = mA.fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [mA, mB, kfac_lift]
  rcases Bool.eq_false_or_eq_true (u ⟨0, Finset.mem_univ 0⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨1, Finset.mem_univ 1⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨2, Finset.mem_univ 2⟩) with h2 | h2 <;>
  simp [DoAudit.kfac_univ, NA_k0, NA_k1, NA_k2, NB_k0, NB_k1, NB_k2, φ,
    Assignment.restrict, PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2,
    mul_comm, mul_left_comm]

lemma full_map : mB.fullJoint = mA.fullJoint.map φ := by
  ext w
  rw [PMF.map_apply, tsum_eq_single (φ w)]
  · rw [if_pos (φ_invol w).symm, ← joint_eq (φ w), φ_invol]
  · intro u hu
    rw [if_neg]
    intro hw
    apply hu
    rw [hw, φ_invol]

/-- **Samme observerte fordeling.** -/
lemma obsEq : mA.marginal {1, 2} = mB.marginal {1, 2} := by
  unfold CausalModel.marginal
  rw [full_map, PMF.map_comp]
  congr 1
  funext u
  funext ⟨v, hv⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  simp [Function.comp, Assignment.restrict, φ, hv0]

lemma kfac_eq {G : DAG (Fin 3)} (M : G.CausalModel (fun _ => Bool)) (S : Finset (Fin 3))
    (a : Assignment (α := fun _ : Fin 3 => Bool) S) (v : Fin 3) (hv : v ∈ S)
    (hpa : G.parents v ⊆ S) :
    kfac M S a v = M.kernel v (a.restrict hpa) (a ⟨v, hv⟩) := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩]

lemma ancB (S : Finset (Fin 3)) (h1 : (1 : Fin 3) ∈ S ∨ (2 : Fin 3) ∉ S) :
    ∀ v ∈ S, ∀ w, gB.edge w v → w ∈ S := by
  intro v hv w hw
  have hw' : w = 1 ∧ v = 2 := hw
  rcases hw' with ⟨rfl, rfl⟩
  rcases h1 with h | h
  · exact h
  · exact absurd hv h

lemma parB (v : Fin 3) (S : Finset (Fin 3)) (hS : ∀ v' ∈ S, ∀ w, gB.edge w v' → w ∈ S)
    (hv : v ∈ S) : gB.parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

/-- **Positivitet.** -/
lemma posA : ∀ a, mA.marginal {1, 2} a ≠ 0 := by
  intro a
  rw [obsEq, show mB.marginal {1, 2} = NB.marginal {1, 2} from
    Completeness.marginal_eq_of_kfac mB NB (kfac_lift hsB NB) {1, 2}]
  have hS := ancB {1, 2} (Or.inl (by simp))
  rw [marginal_ancestral_apply NB {1, 2} hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_eq NB {1, 2} a v hv (parB v {1, 2} hS hv)]
  have hv' : v = 1 ∨ v = 2 := by simpa using hv
  rcases hv' with rfl | rfl
  · rw [NB_k1]
    simp [PMF.uniformOfFintype_apply]
  · rw [NB_k2]
    exact chan_ne_zero _ _

/-- B2 i modell A: `P_x(Y)` er den observerte `P(Y)`. -/
lemma doA (x0 : Assignment (α := fun _ : Fin 3 => Bool) {1})
    (y0 : Assignment (α := fun _ : Fin 3 => Bool) {2}) :
    (doModel mA {1} x0).marginal {2} y0 = mB.marginal {2} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel mA {1} x0) (doModel NA {1} x0)
    (kfac_lift_do hsA NA {1} x0) {2}]
  have hanc : ∀ v ∈ ({0, 2} : Finset (Fin 3)), ∀ w, gA.edge w v → w ∈ ({0, 2} : Finset (Fin 3)) := by
    intro v _ w hw
    have hw' : (w = 0 ∧ v = 1) ∨ (w = 0 ∧ v = 2) := hw
    rcases hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  rw [Rule3.doModel_marginal_of_sub NA {1} x0 {0, 2} hanc (by decide) {2} (by decide) y0,
    ← Completeness.marginal_eq_of_kfac mA NA (kfac_lift hsA NA) {2},
    marginal_eq_of_sub obsEq (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide)]

/-- **Bue-grafen: `P(Y | do(X))` er ikke identifiserbar fra `{X, Y}`.** -/
theorem bow_not_identifiable : ¬ Identifiable bowG (fun _ => Bool) {1, 2} {1} {2} := by
  intro h
  have hnp : ∀ u, ¬ gB.edge u 1 := by
    intro u hu
    have hu' : u = 1 ∧ (1 : Fin 3) = 2 := hu
    exact absurd hu'.2 (by decide)
  have hS21 := ancB ({2} ∪ {1}) (Or.inl (by simp))
  have key : ∀ x : Bool,
      chan x true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        mB.marginal {2} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro x
    let t : Assignment (α := fun _ : Fin 3 => Bool) ({2} ∪ {1}) :=
      fun v => if v.1 = 1 then x else true
    have hx : t.restrict (show ({1} : Finset (Fin 3)) ⊆ {2} ∪ {1} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => x := by
      funext ⟨v, hv⟩
      have : v = 1 := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hy : t.restrict (show ({2} : Finset (Fin 3)) ⊆ {2} ∪ {1} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = 2 := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have e := h mA mB obsEq posA t
    rw [hx, hy, doA, Completeness.marginal_eq_of_kfac (doModel mB {1} _) (doModel NB {1} _)
      (kfac_lift_do hsB NB {1} _) {2}] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 NB {1} {2} (by decide)
      (Completeness.dsep_isolated hnp {2} (by decide)) t
    rw [hx, hy, ← e] at fd
    -- venstresiden: P(x, y) = P(x) · kanal
    rw [marginal_ancestral_apply NB _ hS21 t, Finset.prod_union (show Disjoint ({2} : Finset (Fin 3)) {1} by decide),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_eq NB _ t 2 (by simp) (parB 2 _ hS21 (by simp)),
      kfac_eq NB _ t 1 (by simp) (parB 1 _ hS21 (by simp))] at fd
    -- P(x) i modell B
    have hS1 := ancB {1} (Or.inr (by simp))
    rw [marginal_ancestral_apply NB {1} hS1, Finset.prod_singleton,
      kfac_eq NB {1} _ 1 (by simp) (parB 1 _ hS1 (by simp))] at fd
    rw [NB_k2, NB_k1, NB_k1] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : chan true true = chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [chan_apply, chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact q_ne hc

end Bow
end Identification

#print axioms Identification.Bow.bow_not_identifiable

/-! ## Runde 4: bue-grafen inne i en vilkårlig graf

Har en latent `u` piler til `x` og `y`, og `x → y`, er `P(y | do(x))` ikke
identifiserbar fra `O`, uansett resten av grafen. Alle andre noder er uavhengige
uniforme biter, så den observerte fordelingen forblir positiv. -/

namespace Identification
namespace BowGen

open Bow

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma ne_of_edge {G : DAG V} {a b : V} (h : G.edge a b) : a ≠ b := by
  rintro rfl
  exact lt_irrefl _ (G.rank_strict_mono _ _ h)

/-- Grafen med én kant `a → b`. -/
def g1 (G : DAG V) (a b : V) (hab : G.edge a b) : DAG V where
  edge s t := s = a ∧ t = b
  decEdge := fun s t => inferInstanceAs (Decidable (s = a ∧ t = b))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    exact G.rank_strict_mono _ _ hab

/-- Grafen med kantene `u → x` og `u → y`. -/
def g2 (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) : DAG V where
  edge s t := (s = u ∧ t = x) ∨ (s = u ∧ t = y)
  decEdge := fun s t => inferInstanceAs (Decidable ((s = u ∧ t = x) ∨ (s = u ∧ t = y)))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ huy

section
variable (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)

lemma p1 : x ∈ (g1 G x y hxy).parents y := by simp [DAG.parents, g1]
lemma p2x : u ∈ (g2 G u x y hux huy).parents x := by simp [DAG.parents, g2]
lemma p2y : u ∈ (g2 G u x y hux huy).parents y := by simp [DAG.parents, g2]

/-- Modell A: `u` uniform, `x` støyende kopi av `u`, `y = u`, resten uniform. -/
noncomputable def NA : (g2 G u x y hux huy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = x then chan (pa ⟨u, by rw [hvx]; exact p2x G u x y hux huy⟩)
    else if hvy : v = y then PMF.pure (pa ⟨u, by rw [hvy]; exact p2y G u x y hux huy⟩)
    else PMF.uniformOfFintype Bool

/-- Modell B: `u = 0`, `x` uniform, `y` støyende kopi av `x`, resten uniform. -/
noncomputable def NB : (g1 G x y hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = y then chan (pa ⟨x, by rw [hvy]; exact p1 G x y hxy⟩)
    else if v = u then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {w // w ∈ (g2 G u x y hux huy).parents x} → Bool) :
    (NA G u x y hux huy).kernel x pa = chan (pa ⟨u, p2x G u x y hux huy⟩) := by
  simp [NA]

lemma NA_y (hyx : y ≠ x) (pa : {w // w ∈ (g2 G u x y hux huy).parents y} → Bool) :
    (NA G u x y hux huy).kernel y pa = PMF.pure (pa ⟨u, p2y G u x y hux huy⟩) := by
  simp [NA, hyx]

lemma NA_o {v : V} (hvx : v ≠ x) (hvy : v ≠ y)
    (pa : {w // w ∈ (g2 G u x y hux huy).parents v} → Bool) :
    (NA G u x y hux huy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NA, hvx, hvy]

lemma NB_y (pa : {w // w ∈ (g1 G x y hxy).parents y} → Bool) :
    (NB G u x y hxy).kernel y pa = chan (pa ⟨x, p1 G x y hxy⟩) := by
  simp [NB]

lemma NB_u (huy' : u ≠ y) (pa : {w // w ∈ (g1 G x y hxy).parents u} → Bool) :
    (NB G u x y hxy).kernel u pa = PMF.pure false := by
  simp [NB, huy']

lemma NB_o {v : V} (hvy : v ≠ y) (hvu : v ≠ u)
    (pa : {w // w ∈ (g1 G x y hxy).parents v} → Bool) :
    (NB G u x y hxy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NB, hvy, hvu]

lemma hsA : ∀ v, (g2 G u x y hux huy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
  rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hux
  · rw [h1, h2]; exact huy

lemma hsB : ∀ v, (g1 G x y hxy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hw' : w = x ∧ v = y := hw
  rw [hw'.1, hw'.2]
  exact hxy

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsA G u x y hux huy) (NA G u x y hux huy)
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsB G x y hxy) (NB G u x y hxy)

end

lemma kfac_liftG {G H : DAG V} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool))
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) :
    kfac (Completeness.liftSub hsub N) Finset.univ w v = kfac N Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_doG {G H : DAG V} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool)) (X : Finset V)
    (x : Assignment (α := fun _ : V => Bool) X)
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ w v =
      kfac (doModel N X x) Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

lemma kfac_eqG {G : DAG V} (M : G.CausalModel (fun _ => Bool)) (S : Finset V)
    (a : Assignment (α := fun _ : V => Bool) S) (v : V) (hv : v ∈ S)
    (hpa : G.parents v ⊆ S) :
    kfac M S a v = M.kernel v (a.restrict hpa) (a ⟨v, hv⟩) := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩]

/-- Bijeksjonen: endrer bare `u`, til `u xor y`. -/
def φ (u y : V) (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 = u then xor (w ⟨u, Finset.mem_univ u⟩) (w ⟨y, Finset.mem_univ y⟩) else w v

lemma φ_invol {u y : V} (hyu : y ≠ u)
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ u y (φ u y w) = w := by
  funext ⟨v, hv⟩
  by_cases h : v = u
  · subst h
    simp [φ, hyu, Bool.xor_assoc]
  · simp [φ, h]

section
variable (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)

lemma joint_eq (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB G u x y hxy).fullJoint (φ u y w) = (mA G u x y hux huy).fullJoint w := by
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyu : y ≠ u := (ne_of_edge huy).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  have hux' : u ≠ x := ne_of_edge hux
  have huy' : u ≠ y := ne_of_edge huy
  have hxy' : x ≠ y := ne_of_edge hxy
  have hxU : x ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩
  have hyU : y ∈ (Finset.univ.erase u).erase x :=
    Finset.mem_erase.mpr ⟨hyx, Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, kfac_liftG]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase _ _ hxU, ← Finset.mul_prod_erase _ _ hxU,
    ← Finset.mul_prod_erase _ _ hyU, ← Finset.mul_prod_erase _ _ hyU]
  have hR : ∏ v ∈ ((Finset.univ.erase u).erase x).erase y,
        kfac (NB G u x y hxy) Finset.univ (φ u y w) v =
      ∏ v ∈ ((Finset.univ.erase u).erase x).erase y,
        kfac (NA G u x y hux huy) Finset.univ w v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    simp only [Finset.mem_erase] at hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o G u x y hxy hv.1 hv.2.2.1,
      NA_o G u x y hux huy hv.2.1 hv.1]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (w ⟨u, Finset.mem_univ u⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨x, Finset.mem_univ x⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨y, Finset.mem_univ y⟩) with h2 | h2 <;>
  simp [DoAudit.kfac_univ, NA_x, NA_y, NA_o, NB_y, NB_u, NB_o, φ, Assignment.restrict,
    PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, hxu, hyu, hyx,
    hux', huy', hxy', mul_comm, mul_left_comm, mul_assoc]

lemma full_map : (mB G u x y hxy).fullJoint = (mA G u x y hux huy).fullJoint.map (φ u y) := by
  have hyu : y ≠ u := (ne_of_edge huy).symm
  ext w
  rw [PMF.map_apply, tsum_eq_single (φ u y w)]
  · rw [if_pos (φ_invol hyu w).symm, ← joint_eq G u x y hux huy hxy (φ u y w), φ_invol hyu]
  · intro w' hw'
    rw [if_neg]
    intro hw
    apply hw'
    rw [hw, φ_invol hyu]

lemma obsEq (O : Finset V) (hu : u ∉ O) :
    (mA G u x y hux huy).marginal O = (mB G u x y hxy).marginal O := by
  unfold CausalModel.marginal
  rw [full_map G u x y hux huy hxy, PMF.map_comp]
  congr 1
  funext w
  funext ⟨v, hv⟩
  have hvu : v ≠ u := fun e => hu (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ, hvu]

lemma ancB (S : Finset V) (h : x ∈ S ∨ y ∉ S) :
    ∀ v ∈ S, ∀ w, (g1 G x y hxy).edge w v → w ∈ S := by
  intro v hv w hw
  have hw' : w = x ∧ v = y := hw
  rw [hw'.1]
  rcases h with h | h
  · exact h
  · rw [hw'.2] at hv
    exact absurd hv h

lemma parB (S : Finset V) (hS : ∀ v' ∈ S, ∀ w, (g1 G x y hxy).edge w v' → w ∈ S)
    (v : V) (hv : v ∈ S) : (g1 G x y hxy).parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

include hxy in
lemma posA (O : Finset V) (hu : u ∉ O) (hx : x ∈ O) :
    ∀ a, (mA G u x y hux huy).marginal O a ≠ 0 := by
  intro a
  rw [obsEq G u x y hux huy hxy O hu, show (mB G u x y hxy).marginal O =
      (NB G u x y hxy).marginal O from
    Completeness.marginal_eq_of_kfac _ _ (kfac_liftG (hsB G x y hxy) (NB G u x y hxy)) O]
  have hS := ancB G x y hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_eqG _ O a v hv (parB G x y hxy O hS v hv)]
  by_cases hvy : v = y
  · subst hvy
    rw [NB_y]
    exact chan_ne_zero _ _
  · rw [NB_o G u x y hxy hvy (fun e => hu (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu : u ∉ O) (hy : y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {x})
    (y0 : Assignment (α := fun _ : V => Bool) {y}) :
    (doModel (mA G u x y hux huy) {x} x0).marginal {y} y0 = (mB G u x y hxy).marginal {y} y0 := by
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  rw [Completeness.marginal_eq_of_kfac (doModel (mA G u x y hux huy) {x} x0)
    (doModel (NA G u x y hux huy) {x} x0)
    (kfac_lift_doG (hsA G u x y hux huy) (NA G u x y hux huy) {x} x0) {y}]
  have hanc : ∀ v ∈ ({u, y} : Finset V), ∀ w, (g2 G u x y hux huy).edge w v →
      w ∈ ({u, y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
    rcases hw' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({u, y} : Finset V) {x} := by
    rw [Finset.disjoint_singleton_right]
    simp [hxu, hyx.symm]
  rw [Rule3.doModel_marginal_of_sub (NA G u x y hux huy) {x} x0 {u, y} hanc hdisj {y}
      (by simp) y0,
    ← Completeness.marginal_eq_of_kfac (mA G u x y hux huy) (NA G u x y hux huy)
      (kfac_liftG (hsA G u x y hux huy) (NA G u x y hux huy)) {y},
    marginal_eq_of_sub (obsEq G u x y hux huy hxy O hu) (show ({y} : Finset V) ⊆ O by simpa using hy)]

end

/-- **Bue-grafen i en vilkårlig graf.** Har en latent `u` piler til `x` og `y`, og
`x → y`, er `P(y | do(x))` ikke identifiserbar fra noen `O` som inneholder `x`
og `y`, men ikke `u`. -/
theorem bow_not_identifiable_general (G : DAG V) (O : Finset V) (u x y : V)
    (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)
    (hu : u ∉ O) (hx : x ∈ O) (hy : y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y} := by
  intro h
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  have hnp : ∀ w, ¬ (g1 G x y hxy).edge w x := by
    intro w hw
    have hw' : w = x ∧ x = y := hw
    exact hyx hw'.2.symm
  have hS21 := ancB G x y hxy ({y} ∪ {x}) (Or.inl (by simp))
  have hS1 := ancB G x y hxy {x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        (mB G u x y hxy).marginal {y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({y} ∪ {x}) :=
      fun v => if v.1 = x then b else true
    have htx : t.restrict (show ({x} : Finset V) ⊆ {y} ∪ {x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({y} : Finset V) ⊆ {y} ∪ {x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h (mA G u x y hux huy) (mB G u x y hxy) (obsEq G u x y hux huy hxy O hu)
      (posA G u x y hux huy hxy O hu hx) t
    rw [htx, hty, doA G u x y hux huy hxy O hu hy,
      Completeness.marginal_eq_of_kfac (doModel (mB G u x y hxy) {x} _)
        (doModel (NB G u x y hxy) {x} _)
        (kfac_lift_doG (hsB G x y hxy) (NB G u x y hxy) {x} _) {y}] at e
    have fd := Adjustment.frontdoor_step1 (NB G u x y hxy) {x} {y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({y} : Finset V) {x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_eqG _ _ t y (by simp) (parB G x y hxy _ hS21 y (by simp)),
      kfac_eqG _ _ t x (by simp) (parB G x y hxy _ hS21 x (by simp))] at fd
    rw [marginal_ancestral_apply _ {x} hS1, Finset.prod_singleton,
      kfac_eqG _ {x} _ x (by simp) (parB G x y hxy _ hS1 x (by simp))] at fd
    rw [NB_y, NB_o G u x y hxy hyx.symm hxu, NB_o G u x y hxy hyx.symm hxu] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : chan true true = chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [chan_apply, chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact q_ne hc

end BowGen
end Identification

#print axioms Identification.BowGen.bow_not_identifiable_general

/-!
# Identifikasjon, runde 5: behandling uten latente foreldre

Har `x` bare observerte foreldre, er `P(Y | do(x))` identifiserbar for hver
observert `Y` utenfor `{x} ∪ pa(x)`, uansett hva som ellers er latent. Det er
Tians tilfelle der c-komponenten til `x` er `{x}`: foreldrene oppfyller alltid
back-door-kriteriet.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Identification
namespace Parents

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En vandring som ender langs en pil inn i `t`, er blokkert av `pa(t)`, med mindre
den bare er én kant fra en forelder (da har den ingen indre node). Den siste indre
noden er en forelder og en ikke-collider. -/
theorem ends_blocked {G : DAG V} {m t : V} (p : Walk G m t) :
    ∀ inc : Incoming, Adjustment.endsInto p → (inc = .start → ¬ G.edge m t) →
      Walk.blockedAux (G.parents t) inc p := by
  induction p with
  | nil v =>
    intro inc h _
    exact absurd h (by simp [Adjustment.endsInto])
  | fwd e q ih =>
    intro inc h hs
    by_cases hq : Adjustment.wIsNil q = true
    · cases q with
      | nil =>
        cases inc with
        | start => exact absurd e (hs rfl)
        | fwd =>
          first
            | exact Or.inl (by simp [DAG.parents, e])
            | simp [Walk.blockedAux, DAG.parents, e]
        | bwd =>
          first
            | exact Or.inl (by simp [DAG.parents, e])
            | simp [Walk.blockedAux, DAG.parents, e]
      | fwd _ _ => simp [Adjustment.wIsNil] at hq
      | bwd _ _ => simp [Adjustment.wIsNil] at hq
    · have h' : Adjustment.wIsNil q = true ∨ Adjustment.endsInto q := by
        first | exact h | simpa [Adjustment.endsInto] using h
      have ihr := ih .fwd (h'.resolve_left hq) (by intro hc; cases hc)
      cases inc with
      | start => first | exact ihr | (simp only [Walk.blockedAux]; exact ihr)
      | fwd => first | exact Or.inr ihr | (simp only [Walk.blockedAux]; exact Or.inr ihr)
      | bwd => first | exact Or.inr ihr | (simp only [Walk.blockedAux]; exact Or.inr ihr)
  | bwd e q ih =>
    intro inc h _
    have h' : Adjustment.wIsNil q = false ∧ Adjustment.endsInto q := by
      first | exact h | simpa [Adjustment.endsInto] using h
    have ihr := ih .bwd h'.2 (by intro hc; cases hc)
    cases inc with
    | start => first | exact ihr | (simp only [Walk.blockedAux]; exact ihr)
    | fwd => first | exact Or.inr ihr | (simp only [Walk.blockedAux]; exact Or.inr ihr)
    | bwd => first | exact Or.inr ihr | (simp only [Walk.blockedAux]; exact Or.inr ihr)

/-- Ingen forelder er etterkommer av barnet. -/
lemma not_reaches_parent {G : DAG V} {x z : V} (hz : z ∈ G.parents x) :
    ¬ G.Reaches x z := by
  intro hr
  have he : G.edge z x := by simpa [DAG.parents] using hz
  have h1 := rank_le_of_reaches hr
  have h2 := G.rank_strict_mono z x he
  omega

/-- **Foreldrene oppfyller back-door-kriteriet** for `(x, Y)` når `Y` ikke
inneholder noen forelder til `x`. -/
theorem parents_backdoor (G : DAG V) (x : V) (Y : Finset V)
    (hY : Disjoint Y (G.parents x)) :
    Adjustment.BackdoorCriterion G {x} Y (G.parents x) := by
  refine ⟨?_, ?_⟩
  · intro x' hx' z hz
    rw [Finset.mem_singleton] at hx'
    subst hx'
    exact not_reaches_parent hz
  · intro y hy x' hx' p _ hend
    rw [Finset.mem_singleton] at hx'
    subst hx'
    refine ends_blocked p .start hend ?_
    intro _ he
    exact Finset.disjoint_left.mp hY hy (by simp [DAG.parents, he])

/-- **Behandling uten latente foreldre er identifiserbar.** Er `x` og alle
foreldrene til `x` observert, er `P(Y | do(x))` identifiserbar for hver observert
`Y` som verken inneholder `x` eller en forelder til `x`. -/
theorem parents_identifiable (G : DAG V) (α : V → Type*) [∀ w, Nonempty (α w)]
    (O Y : Finset V) (x : V) (hYx : x ∉ Y) (hY : Disjoint Y (G.parents x))
    (hO : Y ∪ {x} ∪ G.parents x ⊆ O) :
    Identifiable G α O {x} Y := by
  have hYX : Disjoint Y {x} := Finset.disjoint_singleton_right.mpr hYx
  have hZX : Disjoint (G.parents x) {x} :=
    Finset.disjoint_singleton_right.mpr (by simp [DAG.parents, DAG.not_self_edge])
  exact backdoor_identifiable G α O {x} Y (G.parents x) hYX hZX hY
    (parents_backdoor G x Y hY) hO

end Parents
end Identification

#print axioms Identification.Parents.parents_identifiable

/-! ## Runde 6: hedge med to latente variabler

`x ← u₁ → w ← u₂ → y`, `w → y`, `x → y`, med `u₁` og `u₂` latente. Da er
`P(y | do(x))` ikke identifiserbar, også når `w` er observert. Det er et ekte
hedge-tilfelle: `F = {x, w, y}` og `F' = {w, y}`. Var ikke `w` forfar til `y`, ville
effekten vært identifiserbar (`P(y | x)`).

Modell A: `u₁, u₂` uniforme, `x` støyende kopi av `u₁`, `w = u₁ xor u₂`,
`y = w xor u₂` (altså `y = u₁`, upåvirket av `x`). Modell B: `u₁ = u₂ = 0`, `x` og
`w` uniforme, `y` støyende kopi av `x`. Fellesfordelingene er like etter
bijeksjonen `u₁ ↦ u₁ xor y`, `u₂ ↦ u₂ xor (w xor y)`, som bare endrer latente noder. -/

namespace Identification
namespace Hedge2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Hedge-konfigurasjonen inne i `G`. -/
structure Data (G : DAG V) where
  u1 : V
  u2 : V
  x : V
  w : V
  y : V
  h1x : G.edge u1 x
  h1w : G.edge u1 w
  h2w : G.edge u2 w
  h2y : G.edge u2 y
  hwy : G.edge w y
  hxy : G.edge x y
  h12 : u1 ≠ u2
  h2x : u2 ≠ x
  hxw : x ≠ w

namespace Data

variable {G : DAG V} (H : Data G)

lemma d1x : H.u1 ≠ H.x := BowGen.ne_of_edge H.h1x
lemma d1w : H.u1 ≠ H.w := BowGen.ne_of_edge H.h1w
lemma d2w : H.u2 ≠ H.w := BowGen.ne_of_edge H.h2w
lemma d2y : H.u2 ≠ H.y := BowGen.ne_of_edge H.h2y
lemma dwy : H.w ≠ H.y := BowGen.ne_of_edge H.hwy
lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy
lemma d1y : H.u1 ≠ H.y := by
  intro e
  have a := G.rank_strict_mono _ _ H.h1x
  have b := G.rank_strict_mono _ _ H.hxy
  rw [e] at a
  omega

/-- Grafen for modell A: `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y`, `w → y`. -/
def gA : DAG V where
  edge s t := (s = H.u1 ∧ t = H.x) ∨ (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨
    (s = H.u2 ∧ t = H.y) ∨ (s = H.w ∧ t = H.y)
  decEdge := fun s t => inferInstanceAs (Decidable ((s = H.u1 ∧ t = H.x) ∨
    (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.y) ∨
    (s = H.w ∧ t = H.y)))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> apply G.rank_strict_mono <;>
      first | exact H.h1x | exact H.h1w | exact H.h2w | exact H.h2y | exact H.hwy

lemma pAx : H.u1 ∈ (gA H).parents H.x := by simp [DAG.parents, gA]
lemma pAw1 : H.u1 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAw2 : H.u2 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAy2 : H.u2 ∈ (gA H).parents H.y := by simp [DAG.parents, gA]
lemma pAyw : H.w ∈ (gA H).parents H.y := by simp [DAG.parents, gA]

/-- Modell A. -/
noncomputable def NA : (gA H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u1, by rw [hvx]; exact pAx H⟩)
    else if hvw : v = H.w then
      PMF.pure (xor (pa ⟨H.u1, by rw [hvw]; exact pAw1 H⟩) (pa ⟨H.u2, by rw [hvw]; exact pAw2 H⟩))
    else if hvy : v = H.y then
      PMF.pure (xor (pa ⟨H.w, by rw [hvy]; exact pAyw H⟩) (pa ⟨H.u2, by rw [hvy]; exact pAy2 H⟩))
    else PMF.uniformOfFintype Bool

/-- Modell B (på grafen med bare `x → y`). -/
noncomputable def NB : (BowGen.g1 G H.x H.y H.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then Bow.chan (pa ⟨H.x, by rw [hvy]; exact BowGen.p1 G H.x H.y H.hxy⟩)
    else if v = H.u1 ∨ v = H.u2 then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {v // v ∈ (gA H).parents H.x} → Bool) :
    (NA H).kernel H.x pa = Bow.chan (pa ⟨H.u1, pAx H⟩) := by
  simp [Data.NA]

lemma NA_w (pa : {v // v ∈ (gA H).parents H.w} → Bool) :
    (NA H).kernel H.w pa = PMF.pure (xor (pa ⟨H.u1, pAw1 H⟩) (pa ⟨H.u2, pAw2 H⟩)) := by
  simp [Data.NA, H.hxw.symm]

lemma NA_y (pa : {v // v ∈ (gA H).parents H.y} → Bool) :
    (NA H).kernel H.y pa = PMF.pure (xor (pa ⟨H.w, pAyw H⟩) (pa ⟨H.u2, pAy2 H⟩)) := by
  simp [Data.NA, H.dxy.symm, H.dwy.symm]

lemma NA_o {v : V} (hvx : v ≠ H.x) (hvw : v ≠ H.w) (hvy : v ≠ H.y)
    (pa : {w // w ∈ (gA H).parents v} → Bool) :
    (NA H).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [Data.NA, hvx, hvw, hvy]

lemma NB_y (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.y} → Bool) :
    (NB H).kernel H.y pa = Bow.chan (pa ⟨H.x, BowGen.p1 G H.x H.y H.hxy⟩) := by
  simp [Data.NB]

lemma NB_u1 (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.u1} → Bool) :
    (NB H).kernel H.u1 pa = PMF.pure false := by
  simp [Data.NB, H.d1y]

lemma NB_u2 (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.u2} → Bool) :
    (NB H).kernel H.u2 pa = PMF.pure false := by
  simp [Data.NB, H.d2y]

lemma NB_o {v : V} (hvy : v ≠ H.y) (hv1 : v ≠ H.u1) (hv2 : v ≠ H.u2)
    (pa : {w // w ∈ (BowGen.g1 G H.x H.y H.hxy).parents v} → Bool) :
    (NB H).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [Data.NB, hvy, hv1, hv2]

lemma hsA : ∀ v, (gA H).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hw' : (w = H.u1 ∧ v = H.x) ∨ (w = H.u1 ∧ v = H.w) ∨ (w = H.u2 ∧ v = H.w) ∨
      (w = H.u2 ∧ v = H.y) ∨ (w = H.w ∧ v = H.y) := hw
  rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;>
    first | exact H.h1x | exact H.h1w | exact H.h2w | exact H.h2y | exact H.hwy

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsA H) (NA H)
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowGen.hsB G H.x H.y H.hxy) (NB H)

/-- Bijeksjonen: endrer bare `u₁` og `u₂`. -/
def φ2 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if v.1 = H.u1 then xor (s ⟨H.u1, Finset.mem_univ _⟩) (s ⟨H.y, Finset.mem_univ _⟩)
    else if v.1 = H.u2 then
      xor (s ⟨H.u2, Finset.mem_univ _⟩)
        (xor (s ⟨H.w, Finset.mem_univ _⟩) (s ⟨H.y, Finset.mem_univ _⟩))
    else s v

lemma φ2_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ2 H (φ2 H s) = s := by
  funext ⟨v, hv⟩
  by_cases h1 : v = H.u1
  · subst h1
    rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with a | a <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with b | b <;>
    simp [φ2, H.d1y.symm, H.d2y.symm, a, b]
  · by_cases h2 : v = H.u2
    · subst h2
      rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with a | a <;>
      rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with b | b <;>
      rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with c | c <;>
      simp [φ2, H.h12.symm, H.d1y.symm, H.d2y.symm, H.d1w.symm, H.d2w.symm, a, b, c]
    · simp [φ2, h1, h2]

lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB H).fullJoint (φ2 H s) = (mA H).fullJoint s := by
  have m2 : H.u2 ∈ Finset.univ.erase H.u1 := by simp [H.h12.symm]
  have mx : H.x ∈ (Finset.univ.erase H.u1).erase H.u2 := by
    simp [H.d1x.symm, H.h2x.symm]
  have mw : H.w ∈ ((Finset.univ.erase H.u1).erase H.u2).erase H.x := by
    simp [H.d1w.symm, H.d2w.symm, H.hxw.symm]
  have my : H.y ∈ (((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w := by
    simp [H.d1y.symm, H.d2y.symm, H.dxy.symm, H.dwy.symm]
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [Data.mA, Data.mB, BowGen.kfac_liftG]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase _ _ m2, ← Finset.mul_prod_erase _ _ m2,
    ← Finset.mul_prod_erase _ _ mx, ← Finset.mul_prod_erase _ _ mx,
    ← Finset.mul_prod_erase _ _ mw, ← Finset.mul_prod_erase _ _ mw,
    ← Finset.mul_prod_erase _ _ my, ← Finset.mul_prod_erase _ _ my]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NB H) Finset.univ (φ2 H s) v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    simp only [Finset.mem_erase] at hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o H hv.1 hv.2.2.2.2.1 hv.2.2.2.1,
      NA_o H hv.2.2.1 hv.2.1 hv.1]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NB_y, Data.NB_u1, Data.NB_u2, Data.NA_o, Data.NB_o, φ2, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.dwy, H.dwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma full_map : (mB H).fullJoint = (mA H).fullJoint.map (φ2 H) := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (φ2 H s)]
  · rw [if_pos (φ2_invol H s).symm, ← joint_eq H (φ2 H s), φ2_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, φ2_invol]

lemma obsEq (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) :
    (mA H).marginal O = (mB H).marginal O := by
  unfold CausalModel.marginal
  rw [full_map H, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv1 : v ≠ H.u1 := fun e => hu1 (e ▸ hv)
  have hv2 : v ≠ H.u2 := fun e => hu2 (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ2, hv1, hv2]

lemma posA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hx : H.x ∈ O) :
    ∀ a, (mA H).marginal O a ≠ 0 := by
  intro a
  rw [obsEq H O hu1 hu2, show (mB H).marginal O = (NB H).marginal O from
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_liftG (BowGen.hsB G H.x H.y H.hxy) (NB H)) O]
  have hS := BowGen.ancB G H.x H.y H.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (BowGen.parB G H.x H.y H.hxy O hS v hv)]
  by_cases hvy : v = H.y
  · subst hvy
    rw [NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [NB_o H hvy (fun e => hu1 (e ▸ hv)) (fun e => hu2 (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hy : H.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y}) :
    (doModel (mA H) {H.x} x0).marginal {H.y} y0 = (mB H).marginal {H.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel (mA H) {H.x} x0)
    (doModel (NA H) {H.x} x0)
    (BowGen.kfac_lift_doG (hsA H) (NA H) {H.x} x0) {H.y}]
  have hanc : ∀ v ∈ ({H.u1, H.u2, H.w, H.y} : Finset V), ∀ w, (gA H).edge w v →
      w ∈ ({H.u1, H.u2, H.w, H.y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = H.u1 ∧ v = H.x) ∨ (w = H.u1 ∧ v = H.w) ∨ (w = H.u2 ∧ v = H.w) ∨
        (w = H.u2 ∧ v = H.y) ∨ (w = H.w ∧ v = H.y) := hw
    rcases hw' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({H.u1, H.u2, H.w, H.y} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.d1x.symm, H.h2x.symm, H.hxw, H.dxy]
  rw [Rule3.doModel_marginal_of_sub (NA H) {H.x} x0 {H.u1, H.u2, H.w, H.y} hanc hdisj {H.y}
      (by simp) y0,
    ← Completeness.marginal_eq_of_kfac (mA H) (NA H) (BowGen.kfac_liftG (hsA H) (NA H)) {H.y},
    marginal_eq_of_sub (obsEq H O hu1 hu2) (show ({H.y} : Finset V) ⊆ O by simpa using hy)]

theorem not_ident (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} := by
  intro h
  have hxu1 : H.x ≠ H.u1 := H.d1x.symm
  have hxu2 : H.x ≠ H.u2 := H.h2x.symm
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G H.x H.y H.hxy).edge w H.x := by
    intro w hw
    have hw' : w = H.x ∧ H.x = H.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G H.x H.y H.hxy ({H.y} ∪ {H.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G H.x H.y H.hxy {H.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        (mB H).marginal {H.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else true
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({H.y} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = H.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h (mA H) (mB H) (obsEq H O hu1 hu2) (posA H O hu1 hu2 hx) t
    rw [htx, hty, doA H O hu1 hu2 hy,
      Completeness.marginal_eq_of_kfac (doModel (mB H) {H.x} _)
        (doModel (NB H) {H.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G H.x H.y H.hxy) (NB H) {H.x} _) {H.y}] at e
    have fd := Adjustment.frontdoor_step1 (NB H) {H.x} {H.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {H.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({H.y} : Finset V) {H.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t H.y (by simp) (BowGen.parB G H.x H.y H.hxy _ hS21 H.y (by simp)),
      BowGen.kfac_eqG _ _ t H.x (by simp) (BowGen.parB G H.x H.y H.hxy _ hS21 H.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {H.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {H.x} _ H.x (by simp) (BowGen.parB G H.x H.y H.hxy _ hS1 H.x (by simp))] at fd
    rw [NB_y, NB_o H hyx.symm hxu1 hxu2, NB_o H hyx.symm hxu1 hxu2] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end Data

/-- **Hedge med to latente variabler.** Har `G` kantene `u₁ → x`, `u₁ → w`,
`u₂ → w`, `u₂ → y`, `w → y` og `x → y`, er `u₁, u₂` latente og `x, y` observert, så
er `P(y | do(x))` ikke identifiserbar fra `O`, enten `w` er observert eller ikke.
Faller `u₁` og `u₂` sammen, eller `x` og `w`, er det buen. -/
theorem hedge2_not_identifiable (G : DAG V) (O : Finset V) (u1 u2 x w y : V)
    (h1x : G.edge u1 x) (h1w : G.edge u1 w) (h2w : G.edge u2 w) (h2y : G.edge u2 y)
    (hwy : G.edge w y) (hxy : G.edge x y)
    (hu1 : u1 ∉ O) (hu2 : u2 ∉ O) (hx : x ∈ O) (hy : y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y} := by
  by_cases h12 : u1 = u2
  · subst h12
    exact BowGen.bow_not_identifiable_general G O _ _ _ h1x h2y hxy hu1 hx hy
  by_cases hxw : x = w
  · subst hxw
    exact BowGen.bow_not_identifiable_general G O _ _ _ h2w h2y hxy hu2 hx hy
  have h2x : u2 ≠ x := fun e => hu2 (e ▸ hx)
  exact Data.not_ident ⟨u1, u2, x, w, y, h1x, h1w, h2w, h2y, hwy, hxy, h12, h2x, hxw⟩
    O hu1 hu2 hx hy

end Hedge2
end Identification

#print axioms Identification.Hedge2.hedge2_not_identifiable

/-! ## Runde 7: hedge-kjede av vilkårlig lengde

Latente `u₀, …, u_{n+1}` og noder `w₀, …, w_n` danner kjeden
`x ↔ w₀ ↔ w₁ ↔ … ↔ w_n ↔ y`: `u₀ → x`, `u_i → w_i`, `u_{i+1} → w_i`,
`w_i → w_{i+1}`, `w_n → y`, `u_{n+1} → y`, og `x → y`. Da er `P(y | do(x))` ikke
identifiserbar, enten `w`-ene er observert eller ikke.

Modell A: `u`-ene uniforme, `x` støyende kopi av `u₀`,
`w₀ = u₀ xor u₁`, `w_{i+1} = w_i xor u_{i+1} xor u_{i+2}`, `y = w_n xor u_{n+1}`.
Induktivt er `w_i = u₀ xor u_{i+1}` og `y = u₀`, så `y` er upåvirket av `x`.
Modell B: alle `u = 0`, `x` og `w`-ene uniforme, `y` støyende kopi av `x`.
Bijeksjonen `u₀ ↦ u₀ xor y`, `u_{i+1} ↦ u_{i+1} xor w_i xor y` fører den ene
fellesfordelingen over i den andre; likningssystemene er ekvivalente
(`condA_iff`, bevist ved induksjon langs kjeden). -/

namespace Identification
namespace HedgeChain

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Boolsk algebra langs kjeden -/

lemma bx2 {p q r : Bool} (h : r = xor p q) : q = xor r p := by
  rw [h]; cases p <;> cases q <;> rfl
lemma bx3 {p q r s t : Bool} (h1 : q = xor p t) (h2 : r = xor p (xor q s)) :
    s = xor r t := by
  rw [h2, h1]; cases p <;> cases s <;> cases t <;> rfl
lemma bx4 {p q c t : Bool} (h1 : c = xor p q) (h2 : q = xor p t) : t = c := by
  rw [h1, h2]; cases p <;> cases t <;> rfl
lemma bx5 {a0 a1 b0 c : Bool} (h0 : a0 = c) (h1 : a1 = xor b0 c) : b0 = xor a0 a1 := by
  rw [h0, h1]; cases b0 <;> cases c <;> rfl
lemma bx6 {bi bj A B c : Bool} (hA : A = xor bi c) (hB : B = xor bj c) :
    bj = xor bi (xor A B) := by
  rw [hA, hB]; cases bi <;> cases bj <;> cases c <;> rfl
lemma bx7 {bl al c : Bool} (h : al = xor bl c) : c = xor bl al := by
  rw [h]; cases bl <;> cases c <;> rfl
lemma xx (a k : Bool) : xor (xor a k) k = a := by cases a <;> cases k <;> rfl
lemma xb (a k : Bool) (h : xor a k = false) : a = k := by
  cases a <;> cases k <;> simp_all

/-- Forskyvningen i bijeksjonen: `0` for `u₀`, `w_i` for `u_{i+1}`. -/
def offB {n : ℕ} (b : Fin (n + 1) → Bool) (j : Fin (n + 2)) : Bool :=
  Fin.cases (motive := fun _ => Bool) false b j

lemma offB_zero {n : ℕ} (b : Fin (n + 1) → Bool) : offB b 0 = false := by simp [offB]
lemma offB_succ {n : ℕ} (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    offB b i.succ = b i := by simp [offB]

/-- Likningene i modell A. -/
abbrev condA {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) : Prop :=
  b 0 = xor (a 0) (a (Fin.succ 0)) ∧
  (∀ i : Fin n, b i.succ = xor (b i.castSucc) (xor (a i.succ.castSucc) (a i.succ.succ))) ∧
  c = xor (b (Fin.last n)) (a (Fin.last (n + 1)))

/-- Likningene i modell B (etter bijeksjonen). -/
abbrev condB {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) : Prop :=
  ∀ j, a j = xor (offB b j) c

lemma chain_aux {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool)
    (h1 : b 0 = xor (a 0) (a (Fin.succ 0)))
    (h2 : ∀ i : Fin n, b i.succ = xor (b i.castSucc) (xor (a i.succ.castSucc) (a i.succ.succ))) :
    ∀ i : Fin (n + 1), a i.succ = xor (b i) (a 0) := by
  intro i
  induction i using Fin.induction with
  | zero => exact bx2 h1
  | succ i ih =>
    have ee : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    have e : a i.succ.castSucc = xor (b i.castSucc) (a 0) := by rw [ee]; exact ih
    exact bx3 e (h2 i)

/-- **Ekvivalensen av likningssystemene**, ved induksjon langs kjeden. -/
lemma condA_iff {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) :
    condA a b c ↔ condB a b c := by
  have eel : Fin.last (n + 1) = (Fin.last n).succ := Fin.ext rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have aux := chain_aux a b h1 h2
    have hl : a (Fin.last (n + 1)) = xor (b (Fin.last n)) (a 0) := by rw [eel]; exact aux _
    have hc : a 0 = c := bx4 h3 hl
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [offB_zero]; simpa using hc
    · rw [offB_succ, aux i, hc]
  · intro h
    have h0 : a 0 = c := by simpa [offB_zero] using h 0
    have hs : ∀ i : Fin (n + 1), a i.succ = xor (b i) c := by
      intro i
      have := h i.succ
      rwa [offB_succ] at this
    refine ⟨bx5 h0 (hs 0), fun i => bx6 ?_ (hs i.succ), bx7 ?_⟩
    · have ee : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [ee]; exact hs i.castSucc
    · rw [eel]; exact hs _

lemma chan_symm (a b : Bool) : Bow.chan a b = Bow.chan b a := by
  rw [Bow.chan_apply, Bow.chan_apply]
  cases a <;> cases b <;> rfl

/-- Verdien til en full tilordning i en node. -/
def ev (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) : Bool :=
  s ⟨v, Finset.mem_univ v⟩

/-! ### Kjeden inne i `G` -/

/-- En hedge-kjede i `G` med `n + 1` mellomnoder. -/
structure Chain (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  hux : G.edge (u 0) x
  huw1 : ∀ i, G.edge (u i.castSucc) (w i)
  huw2 : ∀ i, G.edge (u i.succ) (w i)
  hww : ∀ i : Fin n, G.edge (w i.castSucc) (w i.succ)
  hwy : G.edge (w (Fin.last n)) y
  huy : G.edge (u (Fin.last (n + 1))) y
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace Chain

variable {G : DAG V} {n : ℕ} (H : Chain G n)

lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy

/-- Grafen for modell A. -/
noncomputable def gA : DAG V where
  edge s t := (s = H.u 0 ∧ t = H.x) ∨ (∃ i, s = H.u i.castSucc ∧ t = H.w i) ∨
    (∃ i, s = H.u i.succ ∧ t = H.w i) ∨ (∃ i : Fin n, s = H.w i.castSucc ∧ t = H.w i.succ) ∨
    (s = H.w (Fin.last n) ∧ t = H.y) ∨ (s = H.u (Fin.last (n + 1)) ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> apply G.rank_strict_mono <;>
      first | exact H.hux | exact H.huw1 _ | exact H.huw2 _ | exact H.hww _ | exact H.hwy | exact H.huy

lemma gA_edge (s t : V) : H.gA.edge s t ↔ ((s = H.u 0 ∧ t = H.x) ∨
    (∃ i, s = H.u i.castSucc ∧ t = H.w i) ∨ (∃ i, s = H.u i.succ ∧ t = H.w i) ∨
    (∃ i : Fin n, s = H.w i.castSucc ∧ t = H.w i.succ) ∨
    (s = H.w (Fin.last n) ∧ t = H.y) ∨ (s = H.u (Fin.last (n + 1)) ∧ t = H.y)) := Iff.rfl

lemma mem_par {a b : V} : a ∈ H.gA.parents b ↔ H.gA.edge a b := by
  simp [DAG.parents]

lemma pA_x : H.u 0 ∈ H.gA.parents H.x :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inl ⟨rfl, rfl⟩))
lemma pA_w1 (i : Fin (n + 1)) : H.u i.castSucc ∈ H.gA.parents (H.w i) :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))
lemma pA_w2 (i : Fin (n + 1)) : H.u i.succ ∈ H.gA.parents (H.w i) :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))))
lemma pA_ww (i : Fin n) : H.w i.castSucc ∈ H.gA.parents (H.w i.succ) :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))))
lemma pA_yw : H.w (Fin.last n) ∈ H.gA.parents H.y :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
lemma pA_yu : H.u (Fin.last (n + 1)) ∈ H.gA.parents H.y :=
  H.mem_par.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
lemma pA_w0 : H.u 0 ∈ H.gA.parents (H.w 0) := by simpa using H.pA_w1 0

lemma mem_cast {a b c : V} (e : b = c) (h : a ∈ H.gA.parents b) : a ∈ H.gA.parents c := by
  rw [← e]; exact h

/-- Kjernen til `w_j` i modell A. -/
noncomputable def kw (j : Fin (n + 1)) : ({v // v ∈ H.gA.parents (H.w j)} → Bool) → PMF Bool :=
  Fin.cases (motive := fun j : Fin (n + 1) => ({v // v ∈ H.gA.parents (H.w j)} → Bool) → PMF Bool)
    (fun pa => PMF.pure (xor (pa ⟨H.u 0, H.pA_w0⟩) (pa ⟨H.u (Fin.succ 0), H.pA_w2 0⟩)))
    (fun i pa => PMF.pure (xor (pa ⟨H.w i.castSucc, H.pA_ww i⟩)
      (xor (pa ⟨H.u i.succ.castSucc, H.pA_w1 i.succ⟩) (pa ⟨H.u i.succ.succ, H.pA_w2 i.succ⟩)))) j

lemma kw_zero (pa : {v // v ∈ H.gA.parents (H.w 0)} → Bool) :
    H.kw 0 pa = PMF.pure (xor (pa ⟨H.u 0, H.pA_w0⟩) (pa ⟨H.u (Fin.succ 0), H.pA_w2 0⟩)) := by
  first | rfl | simp [kw]

lemma kw_succ (i : Fin n) (pa : {v // v ∈ H.gA.parents (H.w i.succ)} → Bool) :
    H.kw i.succ pa = PMF.pure (xor (pa ⟨H.w i.castSucc, H.pA_ww i⟩)
      (xor (pa ⟨H.u i.succ.castSucc, H.pA_w1 i.succ⟩) (pa ⟨H.u i.succ.succ, H.pA_w2 i.succ⟩))) := by
  first | rfl | simp [kw]

/-- Modell A. -/
noncomputable def NA : H.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u 0, by rw [hvx]; exact H.pA_x⟩)
    else if hvy : v = H.y then
      PMF.pure (xor (pa ⟨H.w (Fin.last n), by rw [hvy]; exact H.pA_yw⟩)
        (pa ⟨H.u (Fin.last (n + 1)), by rw [hvy]; exact H.pA_yu⟩))
    else if h : ∃ j, H.w j = v then
      H.kw (Classical.choose h)
        (fun p => pa ⟨p.1, H.mem_cast (Classical.choose_spec h) p.2⟩)
    else PMF.uniformOfFintype Bool

/-- Modell B, på grafen med bare `x → y`. -/
noncomputable def NB : (BowGen.g1 G H.x H.y H.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then Bow.chan (pa ⟨H.x, by rw [hvy]; exact BowGen.p1 G H.x H.y H.hxy⟩)
    else if ∃ j, H.u j = v then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {v // v ∈ H.gA.parents H.x} → Bool) :
    H.NA.kernel H.x pa = Bow.chan (pa ⟨H.u 0, H.pA_x⟩) := by
  simp [NA]

lemma NA_y (pa : {v // v ∈ H.gA.parents H.y} → Bool) :
    H.NA.kernel H.y pa = PMF.pure (xor (pa ⟨H.w (Fin.last n), H.pA_yw⟩)
      (pa ⟨H.u (Fin.last (n + 1)), H.pA_yu⟩)) := by
  simp [NA, H.dxy.symm]

lemma NA_w (j : Fin (n + 1)) (pa : {v // v ∈ H.gA.parents (H.w j)} → Bool) :
    H.NA.kernel (H.w j) pa = H.kw j pa := by
  have h : ∃ j', H.w j' = H.w j := ⟨j, rfl⟩
  have key : ∀ (j' : Fin (n + 1)) (e : H.w j' = H.w j),
      H.kw j' (fun p => pa ⟨p.1, H.mem_cast e p.2⟩) = H.kw j pa := by
    intro j' e
    obtain rfl := H.winj e
    rfl
  simp only [NA, dif_neg (H.hwx j), dif_neg (H.hwy' j), dif_pos h]
  exact key _ (Classical.choose_spec h)

lemma NA_o {v : V} (hvx : v ≠ H.x) (hvy : v ≠ H.y) (hw : ∀ i, H.w i ≠ v)
    (pa : {w // w ∈ H.gA.parents v} → Bool) :
    H.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, H.w j = v := fun ⟨j, hj⟩ => hw j hj
  simp only [NA, dif_neg hvx, dif_neg hvy, dif_neg h]

lemma NB_y (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.y} → Bool) :
    H.NB.kernel H.y pa = Bow.chan (pa ⟨H.x, BowGen.p1 G H.x H.y H.hxy⟩) := by
  simp [NB]

lemma NB_u (j : Fin (n + 2)) (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents (H.u j)} → Bool) :
    H.NB.kernel (H.u j) pa = PMF.pure false := by
  have h : ∃ j', H.u j' = H.u j := ⟨j, rfl⟩
  simp only [NB, dif_neg (H.huy' j), if_pos h]

lemma NB_o {v : V} (hvy : v ≠ H.y) (hu : ∀ j, H.u j ≠ v)
    (pa : {w // w ∈ (BowGen.g1 G H.x H.y H.hxy).parents v} → Bool) :
    H.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, H.u j = v := fun ⟨j, hj⟩ => hu j hj
  simp only [NB, dif_neg hvy, if_neg h]

lemma hsA : ∀ v, H.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [H.mem_par] at ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (H.gA_edge a v).mp ha with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;>
    first | exact H.hux | exact H.huw1 _ | exact H.huw2 _ | exact H.hww _ | exact H.hwy | exact H.huy

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub H.hsA H.NA
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowGen.hsB G H.x H.y H.hxy) H.NB

/-- Bijeksjonen: endrer bare `u`-ene. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if h : ∃ j, H.u j = v.1 then
      xor (s v) (xor (offB (fun i => ev s (H.w i)) (Classical.choose h)) (ev s H.y))
    else s v

lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    ev (H.φ s) (H.u j) = xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) := by
  have h : ∃ j', H.u j' = H.u j := ⟨j, rfl⟩
  have hc : Classical.choose h = j := H.uinj (Classical.choose_spec h)
  simp only [ev, φ]
  rw [dif_pos h, hc]

lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, H.u j ≠ v) : ev (H.φ s) v = ev s v := by
  have h : ¬ ∃ j, H.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [ev, φ]
  rw [dif_neg h]

lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    H.φ (H.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (H.φ (H.φ s)) v = ev s v
  by_cases h : ∃ j, H.u j = v
  · obtain ⟨j, rfl⟩ := h
    have hw : ∀ i, ev (H.φ s) (H.w i) = ev s (H.w i) := fun i => H.φ_o s (fun j => H.huw j i)
    have hy : ev (H.φ s) H.y = ev s H.y := H.φ_o s H.huy'
    rw [H.φ_u (H.φ s) j]
    simp only [hw, hy]
    rw [H.φ_u s j]
    exact xx _ _
  · have hv' : ∀ j, H.u j ≠ v := fun j hj => h ⟨j, hj⟩
    rw [H.φ_o _ hv', H.φ_o _ hv']

/-- Resten av nodene. -/
def R : Finset V :=
  (insert H.x (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w)))ᶜ

lemma mem_R {v : V} : v ∈ H.R ↔
    v ≠ H.x ∧ v ≠ H.y ∧ (∀ j, H.u j ≠ v) ∧ (∀ i, H.w i ≠ v) := by
  simp [R]

lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f H.x * f H.y * (∏ j, f (H.u j)) * (∏ i, f (H.w i)) * ∏ v ∈ H.R, f v := by
  rw [← Finset.prod_mul_prod_compl
    (insert H.x (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w))) f]
  have hx : H.x ∉ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w) := by
    simp [H.dxy, H.hux', H.hwx]
  have hy : H.y ∉ Finset.univ.image H.u ∪ Finset.univ.image H.w := by
    simp [H.huy', H.hwy']
  have hd : Disjoint (Finset.univ.image H.u) (Finset.univ.image H.w) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨i, hi⟩ := hb
    exact H.huw j i hi.symm
  rw [Finset.prod_insert hx, Finset.prod_insert hy, Finset.prod_union hd]
  first
    | rw [Finset.prod_image H.uinj.injOn, Finset.prod_image H.winj.injOn]
    | rw [Finset.prod_image (H.uinj.injOn _), Finset.prod_image (H.winj.injOn _)]
    | rw [Finset.prod_image (fun a _ b _ h => H.uinj h), Finset.prod_image (fun a _ b _ h => H.winj h)]
  simp only [R, mul_assoc]

/-! ### Faktorene -/

lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s H.x = Bow.chan (ev s (H.u 0)) (ev s H.x) := by
  rw [DoAudit.kfac_univ, H.NA_x]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma A_y (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s H.y =
      PMF.pure (xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))) (ev s H.y) := by
  rw [DoAudit.kfac_univ, H.NA_y]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac H.NA Finset.univ s (H.u j) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, H.NA_o (H.hux' j) (H.huy' j) (fun i => (H.huw j i).symm),
    PMF.uniformOfFintype_apply]

lemma A_w0 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s (H.w 0) =
      PMF.pure (xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0)))) (ev s (H.w 0)) := by
  rw [DoAudit.kfac_univ, H.NA_w, H.kw_zero]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma A_ws (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin n) :
    kfac H.NA Finset.univ s (H.w i.succ) =
      PMF.pure (xor (ev s (H.w i.castSucc)) (xor (ev s (H.u i.succ.castSucc))
        (ev s (H.u i.succ.succ)))) (ev s (H.w i.succ)) := by
  rw [DoAudit.kfac_univ, H.NA_w, H.kw_succ]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ H.R) : kfac H.NA Finset.univ s v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨h1, h2, _, h4⟩ := H.mem_R.mp hv
  rw [DoAudit.kfac_univ, H.NA_o h1 h2 h4, PMF.uniformOfFintype_apply]

lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NB Finset.univ t H.x = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, H.NB_o H.dxy H.hux', PMF.uniformOfFintype_apply]

lemma B_y (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NB Finset.univ t H.y = Bow.chan (ev t H.x) (ev t H.y) := by
  rw [DoAudit.kfac_univ, H.NB_y]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac H.NB Finset.univ t (H.u j) = PMF.pure false (ev t (H.u j)) := by
  rw [DoAudit.kfac_univ, H.NB_u]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma B_w (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac H.NB Finset.univ t (H.w i) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, H.NB_o (H.hwy' i) (fun j => H.huw j i), PMF.uniformOfFintype_apply]

lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ H.R) : kfac H.NB Finset.univ t v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨_, h2, h3, _⟩ := H.mem_R.mp hv
  rw [DoAudit.kfac_univ, H.NB_o h2 h3, PMF.uniformOfFintype_apply]

/-! ### Fellesfordelingene -/

lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    H.mB.fullJoint (H.φ s) = H.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
  rw [H.prod_split, H.prod_split]
  have hR : ∏ v ∈ H.R, kfac H.NB Finset.univ (H.φ s) v =
      ∏ v ∈ H.R, kfac H.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [H.B_o _ v hv, H.A_o s v hv])
  have hx' : ev (H.φ s) H.x = ev s H.x := H.φ_o s H.hux'
  have hy' : ev (H.φ s) H.y = ev s H.y := H.φ_o s H.huy'
  rw [hR, H.A_x, H.A_y, H.B_x, H.B_y, hx', hy']
  by_cases hC : condA (fun j => ev s (H.u j)) (fun i => ev s (H.w i)) (ev s H.y)
  · have hB := (condA_iff _ _ _).mp hC
    obtain ⟨h1, h2, h3⟩ := hC
    have h1' : ev s (H.w 0) = xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0))) := h1
    have h2' : ∀ k : Fin n, ev s (H.w k.succ) = xor (ev s (H.w k.castSucc))
        (xor (ev s (H.u k.succ.castSucc)) (ev s (H.u k.succ.succ))) := h2
    have h3' : ev s H.y = xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1)))) := h3
    have hU : ∏ j, kfac H.NB Finset.univ (H.φ s) (H.u j) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hj : ev s (H.u j) = xor (offB (fun i => ev s (H.w i)) j) (ev s H.y) := hB j
      have hcond : xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) =
          false := by
        rw [hj]; first | exact Bool.xor_self _ | simp
      rw [H.B_u, H.φ_u, PMF.pure_apply, if_pos hcond]
    have hW : ∏ i, kfac H.NA Finset.univ s (H.w i) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [H.A_w0, PMF.pure_apply, if_pos h1']
      · rw [H.A_ws, PMF.pure_apply, if_pos (h2' k)]
    have h0 : ev s (H.u 0) = ev s H.y := by
      have hj0 : ev s (H.u 0) = xor (offB (fun i => ev s (H.w i)) 0) (ev s H.y) := hB 0
      rw [offB_zero] at hj0
      simpa using hj0
    rw [hU, hW]
    simp only [H.A_u, H.B_w, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [PMF.pure_apply, if_pos h3', h0, chan_symm (ev s H.y)]
    ring
  · have hB : ¬ ∀ j, ev s (H.u j) = xor (offB (fun i => ev s (H.w i)) j) (ev s H.y) :=
      fun h => hC ((condA_iff _ _ _).mpr h)
    have hU : ∏ j, kfac H.NB Finset.univ (H.φ s) (H.u j) = 0 := by
      push_neg at hB
      obtain ⟨j, hj⟩ := hB
      have hnc : ¬ (xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) =
          false) := fun hf => hj (xb _ _ hf)
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [H.B_u, H.φ_u, PMF.pure_apply, if_neg hnc]
    have hA : PMF.pure (xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))) (ev s H.y)
        = 0 ∨ ∏ i, kfac H.NA Finset.univ s (H.w i) = 0 := by
      by_cases h3 : ev s H.y = xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))
      · right
        by_cases h1 : ev s (H.w 0) = xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0)))
        · have h2 : ¬ ∀ k : Fin n, ev s (H.w k.succ) = xor (ev s (H.w k.castSucc))
              (xor (ev s (H.u k.succ.castSucc)) (ev s (H.u k.succ.succ))) :=
            fun h2 => hC ⟨h1, h2, h3⟩
          push_neg at h2
          obtain ⟨k, hk⟩ := h2
          exact Finset.prod_eq_zero (Finset.mem_univ k.succ)
            (by rw [H.A_ws, PMF.pure_apply, if_neg hk])
        · exact Finset.prod_eq_zero (Finset.mem_univ 0)
            (by rw [H.A_w0, PMF.pure_apply, if_neg h1])
      · left
        rw [PMF.pure_apply, if_neg h3]
    rcases hA with h | h
    · rw [hU, h]; simp
    · rw [hU, h]; simp

lemma full_map : H.mB.fullJoint = H.mA.fullJoint.map H.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (H.φ s)]
  · rw [if_pos (H.φ_invol s).symm, ← H.joint_eq (H.φ s), H.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, H.φ_invol]

lemma obsEq (O : Finset V) (hu : ∀ j, H.u j ∉ O) :
    H.mA.marginal O = H.mB.marginal O := by
  unfold CausalModel.marginal
  rw [H.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ∀ j, H.u j ≠ v := fun j e => hu j (e ▸ hv)
  show ev s v = ev (H.φ s) v
  exact (H.φ_o s hv').symm

lemma posA (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) :
    ∀ a, H.mA.marginal O a ≠ 0 := by
  intro a
  rw [H.obsEq O hu, show H.mB.marginal O = H.NB.marginal O from
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_liftG (BowGen.hsB G H.x H.y H.hxy) H.NB) O]
  have hS := BowGen.ancB G H.x H.y H.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (BowGen.parB G H.x H.y H.hxy O hS v hv)]
  by_cases hvy : v = H.y
  · subst hvy
    rw [H.NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [H.NB_o hvy (fun j e => hu j (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hy : H.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y}) :
    (doModel H.mA {H.x} x0).marginal {H.y} y0 = H.mB.marginal {H.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel H.mA {H.x} x0)
    (doModel H.NA {H.x} x0)
    (BowGen.kfac_lift_doG H.hsA H.NA {H.x} x0) {H.y}]
  have hanc : ∀ v ∈ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w), ∀ a,
      H.gA.edge a v → a ∈ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w) := by
    intro v _ a ha
    rcases (H.gA_edge a v).mp ha with ⟨h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> simp
  have hdisj : Disjoint (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w)) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.dxy, H.hux', H.hwx]
  rw [Rule3.doModel_marginal_of_sub H.NA {H.x} x0 _ hanc hdisj {H.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac H.mA H.NA (BowGen.kfac_liftG H.hsA H.NA) {H.y},
    marginal_eq_of_sub (H.obsEq O hu) (show ({H.y} : Finset V) ⊆ O by simpa using hy)]

/-- **Hedge-kjeden er ikke identifiserbar.** For en kjede `x ↔ w₀ ↔ … ↔ w_n ↔ y`
med latente `u`-er, `w_i → w_{i+1}`, `w_n → y` og `x → y` er `P(y | do(x))` ikke
identifiserbar fra noen `O` som inneholder `x` og `y`, men ingen `u`. -/
theorem not_ident (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} := by
  intro h
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G H.x H.y H.hxy).edge w H.x := by
    intro w hw
    have hw' : w = H.x ∧ H.x = H.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G H.x H.y H.hxy ({H.y} ∪ {H.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G H.x H.y H.hxy {H.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        H.mB.marginal {H.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else true
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({H.y} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = H.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h H.mA H.mB (H.obsEq O hu) (H.posA O hu hx) t
    rw [htx, hty, H.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel H.mB {H.x} _)
        (doModel H.NB {H.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G H.x H.y H.hxy) H.NB {H.x} _) {H.y}] at e
    have fd := Adjustment.frontdoor_step1 H.NB {H.x} {H.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {H.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({H.y} : Finset V) {H.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t H.y (by simp) (BowGen.parB G H.x H.y H.hxy _ hS21 H.y (by simp)),
      BowGen.kfac_eqG _ _ t H.x (by simp) (BowGen.parB G H.x H.y H.hxy _ hS21 H.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {H.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {H.x} _ H.x (by simp) (BowGen.parB G H.x H.y H.hxy _ hS1 H.x (by simp))] at fd
    rw [H.NB_y, H.NB_o hyx.symm H.hux', H.NB_o hyx.symm H.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end Chain

/-- **Hedge-kjeden**, som frittstående teorem. -/
theorem chain_not_identifiable {G : DAG V} {n : ℕ} (H : Chain G n) (O : Finset V)
    (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} :=
  H.not_ident O hu hx hy

end HedgeChain
end Identification

#print axioms Identification.HedgeChain.chain_not_identifiable

/-! ## Runde 8: en generell mal for hedge-motmodeller

Bevisene for kjeden bruker bare noen få egenskaper ved modell A: `x` er en støyende
kopi av `u₀`, hver `w_i` og `y` er en deterministisk funksjon av foreldrene sine i en
delgraf `gA`, og likningssystemet er ekvivalent med at hver `u_j` er
`off_j(w) xor y`, der `off₀ = 0`. Malen `Tm` samler disse egenskapene, og
`Tm.not_ident` gir ikke-identifiserbarhet for enhver slik konfigurasjon. -/

namespace Identification
namespace HedgeTmpl

open HedgeChain (ev xx xb chan_symm)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Malen for en hedge-motmodell inne i `G`. -/
structure Tm (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  gA : DAG V
  hsA : ∀ v, gA.parents v ⊆ G.parents v
  fx : Assignment (α := fun _ : V => Bool) (gA.parents x) → Bool
  src : ∀ b, ∀ a ∈ gA.parents b, (∃ j, u j = a) ∨ (∃ i, w i = a)
  fw : (i : Fin (n + 1)) → Assignment (α := fun _ : V => Bool) (gA.parents (w i)) → Bool
  fy : Assignment (α := fun _ : V => Bool) (gA.parents y) → Bool
  off : Fin (n + 2) → (Fin (n + 1) → Bool) → Bool → Bool
  hfx : ∀ s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V),
    (∀ j, ev s (u j) = off j (fun i => ev s (w i)) (ev s y)) →
      fx (s.restrict (Finset.subset_univ _)) = ev s y
  key : ∀ s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V),
    ((∀ i, ev s (w i) = fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s y = fy (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (u j) = off j (fun i => ev s (w i)) (ev s y)
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace Tm

variable {G : DAG V} {n : ℕ} (T : Tm G n)

lemma dxy : T.x ≠ T.y := BowGen.ne_of_edge T.hxy

lemma mem_cast {a b c : V} (e : b = c) (h : a ∈ T.gA.parents b) : a ∈ T.gA.parents c := by
  rw [← e]; exact h

/-- Modell A. -/
noncomputable def NA : T.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = T.x then Bow.chan (T.fx (fun p => pa ⟨p.1, T.mem_cast hvx.symm p.2⟩))
    else if hvy : v = T.y then PMF.pure (T.fy (fun p => pa ⟨p.1, T.mem_cast hvy.symm p.2⟩))
    else if h : ∃ i, T.w i = v then
      PMF.pure (T.fw (Classical.choose h)
        (fun p => pa ⟨p.1, T.mem_cast (Classical.choose_spec h) p.2⟩))
    else PMF.uniformOfFintype Bool

/-- Modell B, på grafen med bare `x → y`. -/
noncomputable def NB : (BowGen.g1 G T.x T.y T.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = T.y then Bow.chan (pa ⟨T.x, by rw [hvy]; exact BowGen.p1 G T.x T.y T.hxy⟩)
    else if ∃ j, T.u j = v then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents T.x)) :
    T.NA.kernel T.x pa = Bow.chan (T.fx pa) := by
  simp only [NA, dif_pos (rfl : T.x = T.x)]
  all_goals rfl

lemma NA_y (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents T.y)) :
    T.NA.kernel T.y pa = PMF.pure (T.fy pa) := by
  simp only [NA, dif_neg T.dxy.symm, dif_pos (rfl : T.y = T.y)]
  all_goals rfl

lemma NA_w (i : Fin (n + 1)) (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents (T.w i))) :
    T.NA.kernel (T.w i) pa = PMF.pure (T.fw i pa) := by
  have h : ∃ i', T.w i' = T.w i := ⟨i, rfl⟩
  have key : ∀ (i' : Fin (n + 1)) (e : T.w i' = T.w i),
      PMF.pure (T.fw i' (fun p => pa ⟨p.1, T.mem_cast e p.2⟩)) = PMF.pure (T.fw i pa) := by
    intro i' e
    obtain rfl := T.winj e
    rfl
  simp only [NA, dif_neg (T.hwx i), dif_neg (T.hwy' i), dif_pos h]
  exact key _ (Classical.choose_spec h)

lemma NA_o {v : V} (hvx : v ≠ T.x) (hvy : v ≠ T.y) (hw : ∀ i, T.w i ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents v)) :
    T.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ i, T.w i = v := fun ⟨i, hi⟩ => hw i hi
  simp only [NA, dif_neg hvx, dif_neg hvy, dif_neg h]

lemma NB_y (pa : {v // v ∈ (BowGen.g1 G T.x T.y T.hxy).parents T.y} → Bool) :
    T.NB.kernel T.y pa = Bow.chan (pa ⟨T.x, BowGen.p1 G T.x T.y T.hxy⟩) := by
  simp [NB]

lemma NB_u (j : Fin (n + 2)) (pa : {v // v ∈ (BowGen.g1 G T.x T.y T.hxy).parents (T.u j)} → Bool) :
    T.NB.kernel (T.u j) pa = PMF.pure false := by
  have h : ∃ j', T.u j' = T.u j := ⟨j, rfl⟩
  simp only [NB, dif_neg (T.huy' j), if_pos h]

lemma NB_o {v : V} (hvy : v ≠ T.y) (hu : ∀ j, T.u j ≠ v)
    (pa : {w // w ∈ (BowGen.g1 G T.x T.y T.hxy).parents v} → Bool) :
    T.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, T.u j = v := fun ⟨j, hj⟩ => hu j hj
  simp only [NB, dif_neg hvy, if_neg h]

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub T.hsA T.NA
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowGen.hsB G T.x T.y T.hxy) T.NB

/-- Bijeksjonen: endrer bare `u`-ene. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if h : ∃ j, T.u j = v.1 then
      xor (s v) (T.off (Classical.choose h) (fun i => ev s (T.w i)) (ev s T.y))
    else s v

lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    ev (T.φ s) (T.u j) = xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) := by
  have h : ∃ j', T.u j' = T.u j := ⟨j, rfl⟩
  have hc : Classical.choose h = j := T.uinj (Classical.choose_spec h)
  simp only [ev, φ]
  rw [dif_pos h, hc]

lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, T.u j ≠ v) : ev (T.φ s) v = ev s v := by
  have h : ¬ ∃ j, T.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [ev, φ]
  rw [dif_neg h]

lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    T.φ (T.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (T.φ (T.φ s)) v = ev s v
  by_cases h : ∃ j, T.u j = v
  · obtain ⟨j, rfl⟩ := h
    have hw : ∀ i, ev (T.φ s) (T.w i) = ev s (T.w i) := fun i => T.φ_o s (fun j => T.huw j i)
    have hy : ev (T.φ s) T.y = ev s T.y := T.φ_o s T.huy'
    rw [T.φ_u (T.φ s) j]
    simp only [hw, hy]
    rw [T.φ_u s j]
    exact xx _ _
  · have hv' : ∀ j, T.u j ≠ v := fun j hj => h ⟨j, hj⟩
    rw [T.φ_o _ hv', T.φ_o _ hv']

/-- Resten av nodene. -/
def R : Finset V :=
  (insert T.x (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)))ᶜ

lemma mem_R {v : V} : v ∈ T.R ↔
    v ≠ T.x ∧ v ≠ T.y ∧ (∀ j, T.u j ≠ v) ∧ (∀ i, T.w i ≠ v) := by
  simp [R]

lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f T.x * f T.y * (∏ j, f (T.u j)) * (∏ i, f (T.w i)) * ∏ v ∈ T.R, f v := by
  rw [← Finset.prod_mul_prod_compl
    (insert T.x (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w))) f]
  have hx : T.x ∉ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    simp [T.dxy, T.hux', T.hwx]
  have hy : T.y ∉ Finset.univ.image T.u ∪ Finset.univ.image T.w := by
    simp [T.huy', T.hwy']
  have hd : Disjoint (Finset.univ.image T.u) (Finset.univ.image T.w) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨i, hi⟩ := hb
    exact T.huw j i hi.symm
  rw [Finset.prod_insert hx, Finset.prod_insert hy, Finset.prod_union hd]
  first
    | rw [Finset.prod_image T.uinj.injOn, Finset.prod_image T.winj.injOn]
    | rw [Finset.prod_image (T.uinj.injOn _), Finset.prod_image (T.winj.injOn _)]
    | rw [Finset.prod_image (fun a _ b _ h => T.uinj h), Finset.prod_image (fun a _ b _ h => T.winj h)]
  simp only [R, mul_assoc]

/-! ### Faktorene -/

lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NA Finset.univ s T.x =
      Bow.chan (T.fx (s.restrict (Finset.subset_univ _))) (ev s T.x) := by
  rw [DoAudit.kfac_univ, T.NA_x]
  all_goals rfl

lemma A_y (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NA Finset.univ s T.y =
      PMF.pure (T.fy (s.restrict (Finset.subset_univ _))) (ev s T.y) := by
  rw [DoAudit.kfac_univ, T.NA_y]
  all_goals rfl

lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac T.NA Finset.univ s (T.u j) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, T.NA_o (T.hux' j) (T.huy' j) (fun i => (T.huw j i).symm),
    PMF.uniformOfFintype_apply]

lemma A_w (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac T.NA Finset.univ s (T.w i) =
      PMF.pure (T.fw i (s.restrict (Finset.subset_univ _))) (ev s (T.w i)) := by
  rw [DoAudit.kfac_univ, T.NA_w]
  all_goals rfl

lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ T.R) : kfac T.NA Finset.univ s v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨h1, h2, _, h4⟩ := T.mem_R.mp hv
  rw [DoAudit.kfac_univ, T.NA_o h1 h2 h4, PMF.uniformOfFintype_apply]

lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NB Finset.univ t T.x = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, T.NB_o T.dxy T.hux', PMF.uniformOfFintype_apply]

lemma B_y (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NB Finset.univ t T.y = Bow.chan (ev t T.x) (ev t T.y) := by
  rw [DoAudit.kfac_univ, T.NB_y]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac T.NB Finset.univ t (T.u j) = PMF.pure false (ev t (T.u j)) := by
  rw [DoAudit.kfac_univ, T.NB_u]
  all_goals first | rfl | simp [ev, Assignment.restrict]

lemma B_w (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac T.NB Finset.univ t (T.w i) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [DoAudit.kfac_univ, T.NB_o (T.hwy' i) (fun j => T.huw j i), PMF.uniformOfFintype_apply]

lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ T.R) : kfac T.NB Finset.univ t v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨_, h2, h3, _⟩ := T.mem_R.mp hv
  rw [DoAudit.kfac_univ, T.NB_o h2 h3, PMF.uniformOfFintype_apply]

/-! ### Fellesfordelingene -/

lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    T.mB.fullJoint (T.φ s) = T.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
  rw [T.prod_split, T.prod_split]
  have hR : ∏ v ∈ T.R, kfac T.NB Finset.univ (T.φ s) v =
      ∏ v ∈ T.R, kfac T.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [T.B_o _ v hv, T.A_o s v hv])
  have hx' : ev (T.φ s) T.x = ev s T.x := T.φ_o s T.hux'
  have hy' : ev (T.φ s) T.y = ev s T.y := T.φ_o s T.huy'
  rw [hR, T.A_x, T.A_y, T.B_x, T.B_y, hx', hy']
  by_cases hC : (∀ i, ev s (T.w i) = T.fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s T.y = T.fy (s.restrict (Finset.subset_univ _))
  · have hB := (T.key s).mp hC
    obtain ⟨hW', hY'⟩ := hC
    have hU : ∏ j, kfac T.NB Finset.univ (T.φ s) (T.u j) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hj := hB j
      have hcond : xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) =
          false := by
        rw [hj]; first | exact Bool.xor_self _ | simp
      rw [T.B_u, T.φ_u, PMF.pure_apply, if_pos hcond]
    have hW : ∏ i, kfac T.NA Finset.univ s (T.w i) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      rw [T.A_w, PMF.pure_apply, if_pos (hW' i)]
    have h0 : T.fx (s.restrict (Finset.subset_univ _)) = ev s T.y := T.hfx s hB
    rw [hU, hW]
    simp only [T.A_u, T.B_w, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [PMF.pure_apply, if_pos hY', h0, chan_symm (ev s T.y)]
    ring
  · have hB : ¬ ∀ j, ev s (T.u j) = T.off j (fun i => ev s (T.w i)) (ev s T.y) :=
      fun h => hC ((T.key s).mpr h)
    have hU : ∏ j, kfac T.NB Finset.univ (T.φ s) (T.u j) = 0 := by
      push_neg at hB
      obtain ⟨j, hj⟩ := hB
      have hnc : ¬ (xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) =
          false) := fun hf => hj (xb _ _ hf)
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [T.B_u, T.φ_u, PMF.pure_apply, if_neg hnc]
    have hA : PMF.pure (T.fy (s.restrict (Finset.subset_univ _))) (ev s T.y) = 0 ∨
        ∏ i, kfac T.NA Finset.univ s (T.w i) = 0 := by
      by_cases hY : ev s T.y = T.fy (s.restrict (Finset.subset_univ _))
      · right
        have hW : ¬ ∀ i, ev s (T.w i) = T.fw i (s.restrict (Finset.subset_univ _)) :=
          fun hW => hC ⟨hW, hY⟩
        push_neg at hW
        obtain ⟨i, hi⟩ := hW
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [T.A_w, PMF.pure_apply, if_neg hi])
      · left
        rw [PMF.pure_apply, if_neg hY]
    rcases hA with h | h
    · rw [hU, h]; simp
    · rw [hU, h]; simp

lemma full_map : T.mB.fullJoint = T.mA.fullJoint.map T.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (T.φ s)]
  · rw [if_pos (T.φ_invol s).symm, ← T.joint_eq (T.φ s), T.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, T.φ_invol]

lemma obsEq (O : Finset V) (hu : ∀ j, T.u j ∉ O) :
    T.mA.marginal O = T.mB.marginal O := by
  unfold CausalModel.marginal
  rw [T.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ∀ j, T.u j ≠ v := fun j e => hu j (e ▸ hv)
  show ev s v = ev (T.φ s) v
  exact (T.φ_o s hv').symm

lemma posA (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) :
    ∀ a, T.mA.marginal O a ≠ 0 := by
  intro a
  rw [T.obsEq O hu, show T.mB.marginal O = T.NB.marginal O from
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_liftG (BowGen.hsB G T.x T.y T.hxy) T.NB) O]
  have hS := BowGen.ancB G T.x T.y T.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (BowGen.parB G T.x T.y T.hxy O hS v hv)]
  by_cases hvy : v = T.y
  · subst hvy
    rw [T.NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [T.NB_o hvy (fun j e => hu j (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {T.x})
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mA {T.x} x0).marginal {T.y} y0 = T.mB.marginal {T.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel T.mA {T.x} x0)
    (doModel T.NA {T.x} x0)
    (BowGen.kfac_lift_doG T.hsA T.NA {T.x} x0) {T.y}]
  have hanc : ∀ v ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w), ∀ a,
      T.gA.edge a v → a ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    intro v _ a ha
    have hp : a ∈ T.gA.parents v := by simpa [DAG.parents] using ha
    rcases T.src v a hp with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> simp
  have hdisj : Disjoint (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)) {T.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [T.dxy, T.hux', T.hwx]
  rw [Rule3.doModel_marginal_of_sub T.NA {T.x} x0 _ hanc hdisj {T.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac T.mA T.NA (BowGen.kfac_liftG T.hsA T.NA) {T.y},
    marginal_eq_of_sub (T.obsEq O hu) (show ({T.y} : Finset V) ⊆ O by simpa using hy)]

/-- **Malen gir ikke-identifiserbarhet.** -/
theorem not_ident (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) (hy : T.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} {T.y} := by
  intro h
  have hyx : T.y ≠ T.x := T.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G T.x T.y T.hxy).edge w T.x := by
    intro w hw
    have hw' : w = T.x ∧ T.x = T.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G T.x T.y T.hxy ({T.y} ∪ {T.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G T.x T.y T.hxy {T.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        T.mB.marginal {T.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ {T.x}) :=
      fun v => if v.1 = T.x then b else true
    have htx : t.restrict (show ({T.x} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = T.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = T.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h T.mA T.mB (T.obsEq O hu) (T.posA O hu hx) t
    rw [htx, hty, T.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} _)
        (doModel T.NB {T.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB {T.x} _) {T.y}] at e
    have fd := Adjustment.frontdoor_step1 T.NB {T.x} {T.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {T.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({T.y} : Finset V) {T.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t T.y (by simp) (BowGen.parB G T.x T.y T.hxy _ hS21 T.y (by simp)),
      BowGen.kfac_eqG _ _ t T.x (by simp) (BowGen.parB G T.x T.y T.hxy _ hS21 T.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {T.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {T.x} _ T.x (by simp) (BowGen.parB G T.x T.y T.hxy _ hS1 T.x (by simp))] at fd
    rw [T.NB_y, T.NB_o hyx.symm T.hux', T.NB_o hyx.symm T.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end Tm

end HedgeTmpl
end Identification

#print axioms Identification.HedgeTmpl.Tm.not_ident

/-! ## Runde 8b: hedge langs en latent sti med vilkårlig rettet tre mot `y`

Latente `u₀, …, u_{n+1}` gir stien `x ↔ w₀ ↔ … ↔ w_n ↔ y`. De rettede kantene
mellom `w`-ene er et vilkårlig tre mot `y`: hver `w_j` har én forelder `p j`, enten
en annen `w_i` eller `y`. Kjeden (`p j = j + 1`) og stjernen (`p j = y` for alle `j`)
er spesialtilfeller.

Modell A er paritetsmodellen: hver `w_i` er summen (mod 2) av sine to latente
foreldre og barna sine i treet, og `y = u_{n+1} +` barna til `y`. Da er `y` summen av
alle latente bidrag, der hver indre `u` teller to ganger, så `y = u₀`. -/

namespace Identification
namespace PathTree

open HedgeChain (ev)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Bool og `ZMod 2` -/

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0
def z2b (z : ZMod 2) : Bool := decide (z = 1)

lemma b2z_z2b : ∀ z : ZMod 2, b2z (z2b z) = z := by decide
lemma eq_z2b : ∀ (b : Bool) (z : ZMod 2), b = z2b z ↔ b2z b = z := by decide
lemma b2z_xor : ∀ a b : Bool, b2z (xor a b) = b2z a + b2z b := by decide
lemma b2z_inj : ∀ a b : Bool, b2z a = b2z b → a = b := by decide
lemma two : ∀ z : ZMod 2, z + z = 0 := by decide
lemma L1 : ∀ us ucs u0 o wz c : ZMod 2, wz = ucs + us + c → ucs = u0 + o →
    us = u0 + (o + (wz + c)) := by decide
lemma L2 : ∀ yz ul u0 S cy : ZMod 2, yz = ul + cy → ul = u0 + S → S + cy = 0 → u0 = yz := by
  decide
lemma L3 : ∀ wz o yz c : ZMod 2, wz = o + yz + (o + (wz + c) + yz) + c := by decide
lemma L4 : ∀ yz S cy : ZMod 2, S + cy = 0 → yz = S + yz + cy := by decide

/-- Stien med et rettet tre mot `y`. -/
structure PT (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  p : Fin (n + 1) → Option (Fin (n + 1))
  hux : G.edge (u 0) x
  huw1 : ∀ i, G.edge (u i.castSucc) (w i)
  huw2 : ∀ i, G.edge (u i.succ) (w i)
  hpw : ∀ j i, p j = some i → G.edge (w j) (w i)
  hpy : ∀ j, p j = none → G.edge (w j) y
  huy : G.edge (u (Fin.last (n + 1))) y
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace PT

variable {G : DAG V} {n : ℕ} (P : PT G n)

/-- Grafen for modell A. -/
noncomputable def gA : DAG V where
  edge a b := (a = P.u 0 ∧ b = P.x) ∨ (∃ i, a = P.u i.castSucc ∧ b = P.w i) ∨
    (∃ i, a = P.u i.succ ∧ b = P.w i) ∨ (∃ j i, P.p j = some i ∧ a = P.w j ∧ b = P.w i) ∨
    (∃ j, P.p j = none ∧ a = P.w j ∧ b = P.y) ∨ (a = P.u (Fin.last (n + 1)) ∧ b = P.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨j, i, hp, h1, h2⟩ |
        ⟨j, hp, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.huw1 i)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.huw2 i)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hpw j i hp)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hpy j hp)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.huy

lemma gA_edge (a b : V) : P.gA.edge a b ↔ ((a = P.u 0 ∧ b = P.x) ∨
    (∃ i, a = P.u i.castSucc ∧ b = P.w i) ∨ (∃ i, a = P.u i.succ ∧ b = P.w i) ∨
    (∃ j i, P.p j = some i ∧ a = P.w j ∧ b = P.w i) ∨
    (∃ j, P.p j = none ∧ a = P.w j ∧ b = P.y) ∨ (a = P.u (Fin.last (n + 1)) ∧ b = P.y)) :=
  Iff.rfl

lemma mem_par {a b : V} : a ∈ P.gA.parents b ↔ P.gA.edge a b := by
  simp [DAG.parents]

lemma pAx : P.u 0 ∈ P.gA.parents P.x :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inl ⟨rfl, rfl⟩))
lemma pw1 (i : Fin (n + 1)) : P.u i.castSucc ∈ P.gA.parents (P.w i) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))
lemma pw2 (i : Fin (n + 1)) : P.u i.succ ∈ P.gA.parents (P.w i) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))))
lemma pww (j i : Fin (n + 1)) (h : P.p j = some i) : P.w j ∈ P.gA.parents (P.w i) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, i, h, rfl, rfl⟩)))))
lemma pyw (j : Fin (n + 1)) (h : P.p j = none) : P.w j ∈ P.gA.parents P.y :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, h, rfl, rfl⟩))))))
lemma pyu : P.u (Fin.last (n + 1)) ∈ P.gA.parents P.y :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))

lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [P.mem_par] at ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (P.gA_edge a v).mp ha with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨j, i, hp, h1, h2⟩ |
      ⟨j, hp, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact P.hux
  · rw [h1, h2]; exact P.huw1 i
  · rw [h1, h2]; exact P.huw2 i
  · rw [h1, h2]; exact P.hpw j i hp
  · rw [h1, h2]; exact P.hpy j hp
  · rw [h1, h2]; exact P.huy

lemma src : ∀ b, ∀ a ∈ P.gA.parents b, (∃ j, P.u j = a) ∨ (∃ i, P.w i = a) := by
  intro b a ha
  rw [P.mem_par] at ha
  rcases (P.gA_edge a b).mp ha with ⟨h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ | ⟨j, i, _, h1, _⟩ |
      ⟨j, _, h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl ⟨0, h1.symm⟩
  · exact Or.inl ⟨i.castSucc, h1.symm⟩
  · exact Or.inl ⟨i.succ, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩
  · exact Or.inl ⟨Fin.last (n + 1), h1.symm⟩

/-! ### Kjernene og likningene -/

noncomputable def fw (i : Fin (n + 1))
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.w i))) : Bool :=
  z2b (b2z (pa ⟨P.u i.castSucc, P.pw1 i⟩) + b2z (pa ⟨P.u i.succ, P.pw2 i⟩) +
    ∑ j, if h : P.p j = some i then b2z (pa ⟨P.w j, P.pww j i h⟩) else 0)

noncomputable def fy (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.y)) : Bool :=
  z2b (b2z (pa ⟨P.u (Fin.last (n + 1)), P.pyu⟩) +
    ∑ j, if h : P.p j = none then b2z (pa ⟨P.w j, P.pyw j h⟩) else 0)

/-- Barna til `w_i` i treet. -/
def C (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ZMod 2 :=
  ∑ j, if P.p j = some i then b2z (b j) else 0
/-- Barna til `y` i treet. -/
def Cy (b : Fin (n + 1) → Bool) : ZMod 2 :=
  ∑ j, if P.p j = none then b2z (b j) else 0
def rr (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ZMod 2 := b2z (b i) + P.C b i
def rN (b : Fin (n + 1) → Bool) (k : ℕ) : ZMod 2 :=
  if h : k < n + 1 then P.rr b ⟨k, h⟩ else 0
/-- Prefikssummen. -/
def offN (b : Fin (n + 1) → Bool) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 => offN b k + P.rN b k
def off (j : Fin (n + 2)) (b : Fin (n + 1) → Bool) (c : Bool) : Bool :=
  xor (z2b (P.offN b j.val)) c

lemma hu0 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (h : ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.w i)) (ev s P.y)) :
    ev s (P.u 0) = ev s P.y := by
  rw [h 0]
  first | rfl | simp [off, offN, z2b]

lemma offN_succ_fin (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    P.offN b (i.val + 1) = P.offN b i.val + P.rr b i := by
  show P.offN b i.val + P.rN b i.val = _
  rw [rN, dif_pos i.2]

lemma offN_sum (b : Fin (n + 1) → Bool) : ∀ k, P.offN b k = ∑ m ∈ Finset.range k, P.rN b m := by
  intro k
  induction k with
  | zero => simp [offN]
  | succ k ih => rw [Finset.sum_range_succ, ← ih] <;> rfl

lemma offN_last (b : Fin (n + 1) → Bool) : P.offN b (n + 1) = ∑ i, P.rr b i := by
  rw [P.offN_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [rN, i.2]

/-- **Kanselleringen**: hver `w_j` er barn av nøyaktig én node. -/
lemma sum_zero (b : Fin (n + 1) → Bool) : ∑ i, P.rr b i + P.Cy b = 0 := by
  have hpt : ∀ j, (∑ i, (if P.p j = some i then b2z (b j) else 0)) +
      (if P.p j = none then b2z (b j) else 0) = b2z (b j) := by
    intro j
    cases h : P.p j <;> simp [h]
  have hC : ∑ i, P.C b i + P.Cy b = ∑ j, b2z (b j) := by
    unfold C Cy
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpt j)
  calc ∑ i, P.rr b i + P.Cy b = ∑ i, b2z (b i) + (∑ i, P.C b i + P.Cy b) := by
        simp only [rr, Finset.sum_add_distrib, add_assoc]
    _ = ∑ i, b2z (b i) + ∑ j, b2z (b j) := by rw [hC]
    _ = 0 := two _

lemma fw_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    P.fw i (s.restrict (Finset.subset_univ _)) =
      z2b (b2z (ev s (P.u i.castSucc)) + b2z (ev s (P.u i.succ)) +
        P.C (fun k => ev s (P.w k)) i) := by
  unfold fw C
  congr 1
  all_goals first
    | rfl
    | (refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun j _ => ?_))
       by_cases h : P.p j = some i
       · rw [dif_pos h, if_pos h] <;> rfl
       · rw [dif_neg h, if_neg h])

lemma fy_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.fy (s.restrict (Finset.subset_univ _)) =
      z2b (b2z (ev s (P.u (Fin.last (n + 1)))) + P.Cy (fun k => ev s (P.w k))) := by
  unfold fy Cy
  congr 1
  all_goals first
    | rfl
    | (refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun j _ => ?_))
       by_cases h : P.p j = none
       · rw [dif_pos h, if_pos h] <;> rfl
       · rw [dif_neg h, if_neg h])

/-- **Likningssystemene er ekvivalente.** -/
lemma key (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ((∀ i, ev s (P.w i) = P.fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s P.y = P.fy (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.w i)) (ev s P.y) := by
  constructor
  · rintro ⟨hw, hy⟩
    have hw' : ∀ i, b2z (ev s (P.w i)) = b2z (ev s (P.u i.castSucc)) + b2z (ev s (P.u i.succ)) +
        P.C (fun k => ev s (P.w k)) i := fun i => (eq_z2b _ _).mp ((hw i).trans (P.fw_s s i))
    have hy' : b2z (ev s P.y) = b2z (ev s (P.u (Fin.last (n + 1)))) +
        P.Cy (fun k => ev s (P.w k)) := (eq_z2b _ _).mp (hy.trans (P.fy_s s))
    have hU : ∀ j : Fin (n + 2), b2z (ev s (P.u j)) =
        b2z (ev s (P.u 0)) + P.offN (fun k => ev s (P.w k)) j.val := by
      intro j
      refine Fin.induction ?_ (fun i ih => ?_) j
      · simp [offN]
      · have ih' : b2z (ev s (P.u i.castSucc)) =
            b2z (ev s (P.u 0)) + P.offN (fun k => ev s (P.w k)) i.val := by simpa using ih
        rw [Fin.val_succ, P.offN_succ_fin]
        exact L1 _ _ _ _ _ _ (hw' i) ih'
    have hl : b2z (ev s (P.u (Fin.last (n + 1)))) =
        b2z (ev s (P.u 0)) + ∑ i, P.rr (fun k => ev s (P.w k)) i := by
      rw [hU, Fin.val_last, P.offN_last]
    have h0 : b2z (ev s (P.u 0)) = b2z (ev s P.y) := L2 _ _ _ _ _ hy' hl (P.sum_zero _)
    intro j
    apply b2z_inj
    rw [off, b2z_xor, b2z_z2b, hU j, h0]
    ring
  · intro hB
    have hB' : ∀ j, b2z (ev s (P.u j)) = P.offN (fun k => ev s (P.w k)) j.val + b2z (ev s P.y) := by
      intro j
      have := congrArg b2z (hB j)
      rwa [off, b2z_xor, b2z_z2b] at this
    refine ⟨fun i => ?_, ?_⟩
    · rw [P.fw_s, eq_z2b, hB' i.castSucc, hB' i.succ, Fin.val_succ, P.offN_succ_fin,
        Fin.coe_castSucc]
      exact L3 _ _ _ _
    · rw [P.fy_s, eq_z2b, hB' (Fin.last (n + 1)), Fin.val_last, P.offN_last]
      exact L4 _ _ _ (P.sum_zero _)

/-- Konfigurasjonen som en mal. -/
noncomputable def toTm : HedgeTmpl.Tm G n where
  x := P.x
  y := P.y
  w := P.w
  u := P.u
  gA := P.gA
  hsA := P.hsA
  fx := fun pa => pa ⟨P.u 0, P.pAx⟩
  src := P.src
  fw := P.fw
  fy := P.fy
  off := P.off
  hfx := fun s h => P.hu0 s h
  key := P.key
  hxy := P.hxy
  winj := P.winj
  uinj := P.uinj
  huw := P.huw
  hux' := P.hux'
  huy' := P.huy'
  hwx := P.hwx
  hwy' := P.hwy'

end PT

/-- **Hedge langs en latent sti med et vilkårlig rettet tre mot `y`.** For
`x ↔ w₀ ↔ … ↔ w_n ↔ y` gjennom latente `u₀, …, u_{n+1}`, der hver `w_j` har en
pil til `w_{p j}` eller til `y`, og `x → y`, er `P(y | do(x))` ikke identifiserbar fra
noen `O` som inneholder `x` og `y`, men ingen `u`. -/
theorem pathTree_not_identifiable {G : DAG V} {n : ℕ} (P : PT G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} {P.y} :=
  P.toTm.not_ident O hu hx hy

end PathTree
end Identification

#print axioms Identification.PathTree.pathTree_not_identifiable

/-! ## Runde 9: latent tre

De latente forbindelsene danner et tre over `x` og de observerte nodene
`nd₀, …, nd_{n+1}` (med `y = nd_{n+1}`). Hver node `nd_k` har sin egen latente
`u_k` mot en forelder i treet, `bp k` (eller `x` når `k = 0`). De rettede kantene er
et tre mot `y`: hver `nd_j` (`j ≤ n`) peker på `nd_{dp j}`. Dette omfatter
stiene fra runde 8. Fra runde 10 kan `x` ha flere latente naboer: alle `u_j` med
`bp j = none` peker på `x`, og `x` er en støyende kopi av summen deres.

Modell A er paritetsmodellen. Likningssystemet løses nedenfra og opp i det latente
treet (`solN`, med en høydefunksjon `ht` som garanterer at barn ligger lavere), og
`u₀ = y` følger av en dobbelttelling over begge trærne (`dc`). -/

namespace Identification
namespace LatentTree

open HedgeChain (ev)
open PathTree (b2z z2b b2z_z2b eq_z2b b2z_xor b2z_inj two)

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma Lrearr : ∀ N L B D : ZMod 2, N = L + B + D ↔ L = N + D + B := by decide

/-- Et latent tre med et rettet tre mot `y`. -/
structure LT (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 1) → Fin (n + 2)
  hht : ∀ j k, bp j = some k → ht j < ht k
  hux : ∀ j, bp j = none → G.edge (u j) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j, G.edge (nd j.castSucc) (nd (dp j))
  hxy : G.edge x (nd (Fin.last (n + 1)))
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace LT

variable {G : DAG V} {n : ℕ} (P : LT G n)

/-- Grafen for modell A. -/
noncomputable def gA : DAG V where
  edge a b := (∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hux j0 h0)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j)

lemma gA_edge (a b : V) : P.gA.edge a b ↔ ((∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨
    (∃ k, a = P.u k ∧ b = P.nd k) ∨ (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))) := Iff.rfl

lemma mem_par {a b : V} : a ∈ P.gA.parents b ↔ P.gA.edge a b := by
  simp [DAG.parents]

lemma pxu (j : Fin (n + 2)) (h : P.bp j = none) : P.u j ∈ P.gA.parents P.x :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inl ⟨j, h, rfl, rfl⟩))
lemma pnu (k : Fin (n + 2)) : P.u k ∈ P.gA.parents (P.nd k) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩)))
lemma pnb (j k : Fin (n + 2)) (h : P.bp j = some k) : P.u j ∈ P.gA.parents (P.nd k) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))
lemma pnd (j : Fin (n + 1)) (k : Fin (n + 2)) (h : P.dp j = k) :
    P.nd j.castSucc ∈ P.gA.parents (P.nd k) :=
  P.mem_par.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, rfl, by rw [h]⟩))))

lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [P.mem_par] at ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (P.gA_edge a v).mp ha with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ |
      ⟨j, h1, h2⟩
  · rw [h1, h2]; exact P.hux j0 h0
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j

lemma src : ∀ b, ∀ a ∈ P.gA.parents b,
    (∃ j, P.u j = a) ∨ (∃ i, P.nd (Fin.castSucc i) = a) := by
  intro b a ha
  rw [P.mem_par] at ha
  rcases (P.gA_edge a b).mp ha with ⟨j0, _, h1, _⟩ | ⟨k, h1, _⟩ | ⟨j, k, _, h1, _⟩ | ⟨j, h1, _⟩
  · exact Or.inl ⟨j0, h1.symm⟩
  · exact Or.inl ⟨k, h1.symm⟩
  · exact Or.inl ⟨j, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩

/-! ### Kjernene -/

noncomputable def fn (k : Fin (n + 2))
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) : Bool :=
  z2b (b2z (pa ⟨P.u k, P.pnu k⟩) +
    (∑ j, if h : P.bp j = some k then b2z (pa ⟨P.u j, P.pnb j k h⟩) else 0) +
    ∑ j, if h : P.dp j = k then b2z (pa ⟨P.nd j.castSucc, P.pnd j k h⟩) else 0)

lemma fn_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.fn k (s.restrict (Finset.subset_univ _)) =
      z2b (b2z (ev s (P.u k)) +
        (∑ j, if P.bp j = some k then b2z (ev s (P.u j)) else 0) +
        ∑ j, if P.dp j = k then b2z (ev s (P.nd j.castSucc)) else 0) := by
  unfold fn
  congr 1
  all_goals first
    | rfl
    | (congr 1 <;> first
        | rfl
        | (congr 1 <;> first
            | rfl
            | (refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> rfl))
        | (refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> rfl))

noncomputable def fx (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) : Bool :=
  z2b (∑ j, if h : P.bp j = none then b2z (pa ⟨P.u j, P.pxu j h⟩) else 0)

lemma fx_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.fx (s.restrict (Finset.subset_univ _)) =
      z2b (∑ j, if P.bp j = none then b2z (ev s (P.u j)) else 0) := by
  unfold fx
  congr 1
  all_goals first
    | rfl
    | (refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> rfl)

/-! ### Løsningen nedenfra og opp -/

def solN (R : Fin (n + 2) → ZMod 2) : ℕ → Fin (n + 2) → ZMod 2
  | 0, k => R k
  | m + 1, k => R k + ∑ j, if P.bp j = some k then solN R m j else 0

def M : ℕ := Finset.univ.sup P.ht

lemma ht_le (k : Fin (n + 2)) : P.ht k ≤ P.M := Finset.le_sup (Finset.mem_univ k)

lemma stab (R : Fin (n + 2) → ZMod 2) :
    ∀ m k, P.ht k ≤ m → P.solN R (m + 1) k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then P.solN R 0 j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show R k + _ = R k
    rw [hz, add_zero]
  | succ m ih =>
    intro k hk
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma uniq (R ℓ : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) :
    ∀ m k, P.ht k ≤ m → ℓ k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then ℓ j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show ℓ k = R k
    rw [hE k, hz, add_zero]
  | succ m ih =>
    intro k hk
    rw [hE k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma sol_iff (R ℓ : Fin (n + 2) → ZMod 2) :
    (∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) ↔
      ∀ k, ℓ k = P.solN R (P.M + 1) k := by
  constructor
  · intro hE k
    exact P.uniq R ℓ hE (P.M + 1) k (by have := P.ht_le k; omega)
  · intro h k
    rw [h k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rw [h j, P.stab R P.M j (P.ht_le j)]
    · rfl

/-! ### Dobbelttellingen -/

lemma dc (ℓ N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = (N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
      ∑ j, if P.bp j = some k then ℓ j else 0) :
    (∑ j, if P.bp j = none then ℓ j else 0) = N (Fin.last (n + 1)) := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then ℓ j else 0) =
      if P.bp j = none then 0 else ℓ j := by
    intro j
    cases hb : P.bp j with
    | none => simp
    | some k0 => simp
  have h2 : ∀ j : Fin (n + 1), (∑ k, if P.dp j = k then N j.castSucc else 0) = N j.castSucc := by
    intro j
    simp
  have hsplit : ∑ j, ℓ j = (∑ j, if P.bp j = none then ℓ j else 0) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hD : ∑ k, ∑ j, (if P.dp j = k then N j.castSucc else 0) = ∑ j, N (Fin.castSucc j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hB : ∑ k, ∑ j, (if P.bp j = some k then ℓ j else 0) =
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hsum : ∑ k, ℓ k = (∑ k, N k + ∑ j, N (Fin.castSucc j)) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    calc ∑ k, ℓ k = ∑ k, ((N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ j, if P.bp j = some k then ℓ j else 0) := Finset.sum_congr rfl (fun k _ => hE k)
      _ = (∑ k, N k + ∑ k, ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ k, ∑ j, if P.bp j = some k then ℓ j else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ k, N k + ∑ j, N (Fin.castSucc j)) + ∑ j, (if P.bp j = none then 0 else ℓ j) := by
        rw [hD, hB]
  have hN : ∑ k, N k + ∑ j, N (Fin.castSucc j) = N (Fin.last (n + 1)) := by
    rw [Fin.sum_univ_castSucc]
    have := two (∑ j : Fin (n + 1), N j.castSucc)
    linear_combination this
  have := hsplit.symm.trans hsum
  rw [hN] at this
  exact add_right_cancel this

/-! ### Likningene -/

def nz (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  b2z (Fin.lastCases (motive := fun _ => Bool) c b k)

def rr (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  nz b c k + ∑ j, if P.dp j = k then nz b c j.castSucc else 0

def off (j : Fin (n + 2)) (b : Fin (n + 1) → Bool) (c : Bool) : Bool :=
  z2b (P.solN (P.rr b c) (P.M + 1) j)

lemma nz_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    nz (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      b2z (ev s (P.nd k)) := by
  refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [nz]

lemma rr_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      b2z (ev s (P.nd k)) + ∑ j, if P.dp j = k then b2z (ev s (P.nd j.castSucc)) else 0 := by
  simp only [rr, P.nz_eq]

lemma E_iff (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) ↔
      b2z (ev s (P.u k)) = P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k +
        ∑ j, if P.bp j = some k then b2z (ev s (P.u j)) else 0 := by
  rw [P.fn_s, eq_z2b, P.rr_eq]
  exact Lrearr _ _ _ _

lemma key (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1)))) := by
  have hall : ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
      ∀ k, ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) :=
    ⟨fun ⟨h1, h2⟩ k => Fin.lastCases (motive := fun k =>
        ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _))) h2 h1 k,
      fun h => ⟨fun i => h _, h _⟩⟩
  refine hall.trans ((forall_congr' fun k => P.E_iff s k).trans
    ((P.sol_iff (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))))
      (fun k => b2z (ev s (P.u k)))).trans (forall_congr' fun j => ?_)))
  unfold off
  exact (eq_z2b _ _).symm

lemma hfx (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (h : ∀ j, ev s (P.u j) =
      P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1))))) :
    P.fx (s.restrict (Finset.subset_univ _)) = ev s (P.nd (Fin.last (n + 1))) := by
  have h' : ∀ k, b2z (ev s (P.u k)) =
      P.solN (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1))))) (P.M + 1) k :=
    fun k => (eq_z2b _ _).mp (h k)
  have hE := (P.sol_iff _ (fun k => b2z (ev s (P.u k)))).mpr h'
  simp only [P.rr_eq] at hE
  have hd := P.dc (fun k => b2z (ev s (P.u k))) (fun k => b2z (ev s (P.nd k))) hE
  rw [P.fx_s]
  exact ((eq_z2b _ _).mpr hd.symm).symm

/-- Konfigurasjonen som en mal. -/
noncomputable def toTm : HedgeTmpl.Tm G n where
  x := P.x
  y := P.nd (Fin.last (n + 1))
  w := fun i => P.nd (Fin.castSucc i)
  u := P.u
  gA := P.gA
  hsA := P.hsA
  fx := P.fx
  src := P.src
  fw := fun i => P.fn (Fin.castSucc i)
  fy := P.fn (Fin.last (n + 1))
  off := P.off
  hfx := P.hfx
  key := P.key
  hxy := P.hxy
  winj := fun a b h => Fin.castSucc_injective _ (P.ndinj h)
  uinj := P.uinj
  huw := fun j i => P.hund j _
  hux' := P.hux'
  huy' := fun j => P.hund j _
  hwx := fun i => P.hndx _
  hwy' := fun i h => (Fin.castSucc_lt_last i).ne (P.ndinj h)

end LT

/-- **Latent tre.** Danner de latente forbindelsene et tre over `x` og de observerte
nodene, og danner de rettede kantene et tre mot `y`, og er `x → y`,
så er `P(y | do(x))` ikke identifiserbar fra noen `O` som inneholder `x` og `y`, men
ingen latent. -/
theorem latentTree_not_identifiable {G : DAG V} {n : ℕ} (P : LT G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} {P.nd (Fin.last (n + 1))} :=
  P.toTm.not_ident O hu hx hy

end LatentTree
end Identification

#print axioms Identification.LatentTree.latentTree_not_identifiable

/-! ## Runde 11: fra én `y` til en mengde `Y`

Er `P(Y | do(X))` identifiserbar og `Y' ⊆ Y` (med `Y` og `X` disjunkte), er også
`P(Y' | do(X))` identifiserbar: marginalisering bevarer likhet. Ikke-identifiserbarhet
for én `y` gir derfor ikke-identifiserbarhet for enhver `Y` som inneholder `y`. -/

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En tilordning på `Y ∪ X` satt sammen av delene. -/
def joinYX {α : V → Type*} {X Y : Finset V} (a : Assignment (α := α) Y)
    (b : Assignment (α := α) X) : Assignment (α := α) (Y ∪ X) :=
  fun v => if h : v.1 ∈ Y then a ⟨v.1, h⟩
    else b ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩

lemma joinYX_Y {α : V → Type*} {X Y : Finset V} (a : Assignment (α := α) Y)
    (b : Assignment (α := α) X) :
    (joinYX a b).restrict (show Y ⊆ Y ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = a := by
  funext ⟨v, hv⟩
  simp [joinYX, Assignment.restrict, hv]

lemma joinYX_X {α : V → Type*} {X Y : Finset V} (hd : Disjoint Y X)
    (a : Assignment (α := α) Y) (b : Assignment (α := α) X) :
    (joinYX a b).restrict (show X ⊆ Y ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = b := by
  funext ⟨v, hv⟩
  have hvY : v ∉ Y := Finset.disjoint_right.mp hd hv
  simp [joinYX, Assignment.restrict, hvY]

/-- **Identifiserbarhet går nedover i `Y`.** -/
theorem Identifiable.mono_Y {G : DAG V} {α : V → Type*} {O X Y Y' : Finset V}
    (hd : Disjoint Y X) (hY : Y' ⊆ Y) (h : Identifiable G α O X Y) :
    Identifiable G α O X Y' := by
  intro M₁ M₂ hM hpos t
  have hP : ∀ x0 : Assignment (α := α) X,
      (doModel M₁ X x0).marginal Y = (doModel M₂ X x0).marginal Y := by
    intro x0
    ext a
    have e := h M₁ M₂ hM hpos (joinYX a x0)
    rw [joinYX_X hd, joinYX_Y] at e
    exact e
  rw [← marginal_restrict (doModel M₁ X _) hY, ← marginal_restrict (doModel M₂ X _) hY, hP]

/-- Ikke-identifiserbarhet for én `y` gir det for enhver `Y ∋ y` disjunkt fra `X`. -/
theorem not_identifiable_of_mem {G : DAG V} {α : V → Type*} {O X Y : Finset V} {y : V}
    (h : ¬ Identifiable G α O X {y}) (hy : y ∈ Y) (hd : Disjoint Y X) :
    ¬ Identifiable G α O X Y :=
  fun hY => h (hY.mono_Y hd (Finset.singleton_subset_iff.mpr hy))

/-- **Latent tre, mengdeversjon.** -/
theorem latentTree_not_identifiable_set {G : DAG V} {n : ℕ} (P : LatentTree.LT G n)
    (O Y : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O)
    (hyY : P.nd (Fin.last (n + 1)) ∈ Y) (hd : Disjoint Y {P.x}) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} Y :=
  not_identifiable_of_mem (LatentTree.latentTree_not_identifiable P O hu hx hy) hyY hd

end Identification

#print axioms Identification.latentTree_not_identifiable_set

/-! ## Runde 12: mengder `X`

Inneholder `X` noden `x` og ellers bare noder utenfor hedgen (resten `R`), er
`P(y | do(X))` fortsatt ikke identifiserbar. I begge modellene er nodene i `R`
uniform støy uten etterkommere, så inngrep på dem endrer ingenting: i modell A gir
regel 3 (B2) det direkte, og i modell B skriver vi `do(X)` som `do(X ∖ {x})` etter
`do(x)` og bruker B2 på den indre modellen. -/

namespace Identification
namespace HedgeTmpl
namespace Tm

open HedgeChain (ev)

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : DAG V} {n : ℕ} (T : Tm G n)

/-- `do(X)` i modell A. -/
lemma doA_X (O X : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R)
    (x0 : Assignment (α := fun _ : V => Bool) X)
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mA X x0).marginal {T.y} y0 = T.mB.marginal {T.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel T.mA X x0) (doModel T.NA X x0)
    (BowGen.kfac_lift_doG T.hsA T.NA X x0) {T.y}]
  have hanc : ∀ v ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w), ∀ a,
      T.gA.edge a v → a ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    intro v _ a ha
    have hp : a ∈ T.gA.parents v := by simpa [DAG.parents] using ha
    rcases T.src v a hp with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> simp
  have hdisj : Disjoint (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)) X := by
    rw [Finset.disjoint_right]
    intro v hv
    rcases hX v hv with rfl | hR
    · simp [T.dxy, T.hux', T.hwx]
    · obtain ⟨_, h2, h3, h4⟩ := T.mem_R.mp hR
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, not_or, not_exists]
      exact ⟨h2, h3, h4⟩
  rw [Rule3.doModel_marginal_of_sub T.NA X x0 _ hanc hdisj {T.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac T.mA T.NA (BowGen.kfac_liftG T.hsA T.NA) {T.y},
    marginal_eq_of_sub (T.obsEq O hu) (show ({T.y} : Finset V) ⊆ O by simpa using hy)]

/-- `do(X)` i modell B er `do(x)`. -/
lemma doB_X (X : Finset V) (hxX : T.x ∈ X) (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R)
    (x0 : Assignment (α := fun _ : V => Bool) X)
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mB X x0).marginal {T.y} y0 =
      (doModel T.mB {T.x} (x0.restrict (Finset.singleton_subset_iff.mpr hxX))).marginal
        {T.y} y0 := by
  have hyX : T.y ∉ X := by
    intro hy
    rcases hX _ hy with h | h
    · exact T.dxy h.symm
    · exact (T.mem_R.mp h).2.1 rfl
  set x1 := x0.restrict (Finset.singleton_subset_iff.mpr hxX) with hx1
  set x2 := x0.restrict (Finset.erase_subset T.x X) with hx2
  rw [Completeness.marginal_eq_of_kfac (doModel T.mB X x0) (doModel T.NB X x0)
      (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB X x0) {T.y},
    Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} x1) (doModel T.NB {T.x} x1)
      (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB {T.x} x1) {T.y}]
  have hk : ∀ u v, kfac (doModel T.NB X x0) Finset.univ u v =
      kfac (doModel (doModel T.NB {T.x} x1) (X.erase T.x) x2) Finset.univ u v := by
    intro u v
    rw [kfac_doModel, kfac_doModel, kfac_doModel]
    by_cases h1 : v ∈ X.erase T.x
    · rw [dif_pos (Finset.mem_of_mem_erase h1), dif_pos h1]
      rfl
    · rw [dif_neg h1]
      by_cases h2 : v = T.x
      · subst h2
        rw [dif_pos hxX, dif_pos (Finset.mem_singleton_self _)]
        rfl
      · have h3 : v ∉ X := fun hv => h1 (Finset.mem_erase.mpr ⟨h2, hv⟩)
        rw [dif_neg h3, dif_neg (show v ∉ ({T.x} : Finset V) by simpa using h2)]
  rw [Completeness.marginal_eq_of_kfac (doModel T.NB X x0)
    (doModel (doModel T.NB {T.x} x1) (X.erase T.x) x2) hk {T.y}]
  have hA : ∀ v ∈ ({T.x, T.y} : Finset V), ∀ w,
      (cutIn (BowGen.g1 G T.x T.y T.hxy) {T.x}).edge w v → w ∈ ({T.x, T.y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = T.x ∧ v = T.y) ∧ v ∉ ({T.x} : Finset V) := hw
    simp [hw'.1.1]
  have hAX : Disjoint ({T.x, T.y} : Finset V) (X.erase T.x) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (Finset.mem_erase.mp hv').1 rfl
    · exact hyX (Finset.mem_of_mem_erase hv')
  exact Rule3.doModel_marginal_of_sub (doModel T.NB {T.x} x1) (X.erase T.x) x2
    {T.x, T.y} hA hAX {T.y} (by simp) y0

/-- Selvmotsigelsen fra `do(x)`-likheten alene. -/
lemma contra (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (hE : ∀ b : Bool, (doModel T.mA {T.x} (fun _ => b)).marginal {T.y} (fun _ => true) =
      (doModel T.mB {T.x} (fun _ => b)).marginal {T.y} (fun _ => true)) : False := by
  have hyx : T.y ≠ T.x := T.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G T.x T.y T.hxy).edge w T.x := by
    intro w hw
    have hw' : w = T.x ∧ T.x = T.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G T.x T.y T.hxy ({T.y} ∪ {T.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G T.x T.y T.hxy {T.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        T.mB.marginal {T.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ {T.x}) :=
      fun v => if v.1 = T.x then b else true
    have htx : t.restrict (show ({T.x} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = T.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = T.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := hE b
    rw [T.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} _)
        (doModel T.NB {T.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB {T.x} _) {T.y}] at e
    have fd := Adjustment.frontdoor_step1 T.NB {T.x} {T.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {T.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({T.y} : Finset V) {T.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t T.y (by simp) (BowGen.parB G T.x T.y T.hxy _ hS21 T.y (by simp)),
      BowGen.kfac_eqG _ _ t T.x (by simp) (BowGen.parB G T.x T.y T.hxy _ hS21 T.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {T.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {T.x} _ T.x (by simp) (BowGen.parB G T.x T.y T.hxy _ hS1 T.x (by simp))] at fd
    rw [T.NB_y, T.NB_o hyx.symm T.hux', T.NB_o hyx.symm T.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / (Fintype.card Bool : ℝ≥0∞)⁻¹) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

/-- **Malen med en mengde `X`.** -/
theorem not_ident_X (O X : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) (hy : T.y ∈ O)
    (hxX : T.x ∈ X) (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R) :
    ¬ Identifiable G (fun _ => Bool) O X {T.y} := by
  intro h
  have hyX : T.y ∉ X := by
    intro hy'
    rcases hX _ hy' with h' | h'
    · exact T.dxy h'.symm
    · exact (T.mem_R.mp h').2.1 rfl
  apply T.contra O hu hy
  intro b
  let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ X) :=
    fun v => if v.1 = T.y then true else b
  have htX : t.restrict (show X ⊆ {T.y} ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
    funext ⟨v, hv⟩
    have hvy : v ≠ T.y := fun e => hyX (e ▸ hv)
    simp [t, Assignment.restrict, hvy]
  have htY : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
    funext ⟨v, hv⟩
    have : v = T.y := Finset.mem_singleton.mp hv
    subst this
    simp [t, Assignment.restrict]
  have e := h T.mA T.mB (T.obsEq O hu) (T.posA O hu hx) t
  rw [htX, htY] at e
  calc (doModel T.mA {T.x} (fun _ => b)).marginal {T.y} (fun _ => true)
      = T.mB.marginal {T.y} (fun _ => true) := T.doA O hu hy _ _
    _ = (doModel T.mA X (fun _ => b)).marginal {T.y} (fun _ => true) :=
        (T.doA_X O X hu hy hX _ _).symm
    _ = (doModel T.mB X (fun _ => b)).marginal {T.y} (fun _ => true) := e
    _ = (doModel T.mB {T.x} (fun _ => b)).marginal {T.y} (fun _ => true) :=
        T.doB_X X hxX hX _ _

end Tm
end HedgeTmpl

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Latent tre med mengder `X` og `Y`.** -/
theorem latentTree_not_identifiable_XY {G : DAG V} {n : ℕ} (P : LatentTree.LT G n)
    (O X Y : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O)
    (hxX : P.x ∈ X) (hX : ∀ v ∈ X, v = P.x ∨ v ∈ P.toTm.R)
    (hyY : P.nd (Fin.last (n + 1)) ∈ Y) (hd : Disjoint Y X) :
    ¬ Identifiable G (fun _ => Bool) O X Y :=
  not_identifiable_of_mem (P.toTm.not_ident_X O X hu hx hy hxX hX) hyY hd

end Identification

#print axioms Identification.latentTree_not_identifiable_XY

/-! ## Runde 13: en c-skog med to røtter

`u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y` og `x → y`, med `u₁, u₂` latente. Her er
`P(y | do(x))` alene identifiserbar (`w` er en kollider på den eneste bakdørsstien),
men `P(y, w | do(x))` er det ikke: `F = {x, y, w}`, `F' = {y, w}` med røttene `y` og
`w`. Dette er det enkleste tilfellet som krever flere røtter.

Modell A: `x = chan(u₁)`, `w = u₁ xor u₂`, `y = u₂`, så `y xor w = u₁` og `do(x)`
endrer ingenting. Modell B: `u₁ = 0`, `w = u₂`, `y = chan(x) xor u₂`. Modell B
bruker selv en latent variabel; med bare kanten `x → y` ville det vært umulig.
De observerte fordelingene er like, og for å regne ut marginalene bruker vi en
tredje modell C med samme fellesfordeling som A, der `{y, w, x}` er forfedrelukket
(`y, w` uniforme, `x = chan(y xor w)`, `u₁ = y xor w`, `u₂ = y`). -/

namespace Identification
namespace TwoRoot

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Kanter følger av forfedrelukkethet. -/
lemma parOf {H : DAG V} {S : Finset V} (hS : ∀ v ∈ S, ∀ w, H.edge w v → w ∈ S)
    (v : V) (hv : v ∈ S) : H.parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

/-- Konfigurasjonen inne i `G`: `y` er roten med `x → y`, `w` er den andre roten. -/
structure Data (G : DAG V) where
  u1 : V
  u2 : V
  x : V
  w : V
  y : V
  h1x : G.edge u1 x
  h1w : G.edge u1 w
  h2w : G.edge u2 w
  h2y : G.edge u2 y
  hxy : G.edge x y
  h12 : u1 ≠ u2
  h2x : u2 ≠ x
  hxw : x ≠ w
  hwy : w ≠ y

namespace Data

variable {G : DAG V} (H : Data G)

lemma d1x : H.u1 ≠ H.x := BowGen.ne_of_edge H.h1x
lemma d1w : H.u1 ≠ H.w := BowGen.ne_of_edge H.h1w
lemma d2w : H.u2 ≠ H.w := BowGen.ne_of_edge H.h2w
lemma d2y : H.u2 ≠ H.y := BowGen.ne_of_edge H.h2y
lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy
lemma d1y : H.u1 ≠ H.y := by
  intro e
  have a := G.rank_strict_mono _ _ H.h1x
  have b := G.rank_strict_mono _ _ H.hxy
  rw [e] at a
  omega

/-! ### De tre grafene -/

noncomputable def gA : DAG V where
  edge s t := (s = H.u1 ∧ t = H.x) ∨ (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨
    (s = H.u2 ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h1x
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h1w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2y

noncomputable def gB : DAG V where
  edge s t := (s = H.u2 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.y) ∨ (s = H.x ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2y
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.hxy

noncomputable def gC : DAG V where
  edge s t := (s = H.y ∧ t = H.x) ∨ (s = H.w ∧ t = H.x) ∨ (s = H.y ∧ t = H.u1) ∨
    (s = H.w ∧ t = H.u1) ∨ (s = H.y ∧ t = H.u2)
  decEdge := fun _ _ => Classical.dec _
  rank := fun v => if v = H.y ∨ v = H.w then 0 else 1
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      simp [H.dxy, H.hxw, H.d1y, H.d1w, H.d2y, H.d2w, H.hwy, H.hwy.symm]

lemma pAx : H.u1 ∈ (gA H).parents H.x := by simp [DAG.parents, gA]
lemma pAw1 : H.u1 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAw2 : H.u2 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAy : H.u2 ∈ (gA H).parents H.y := by simp [DAG.parents, gA]
lemma pBw : H.u2 ∈ (gB H).parents H.w := by simp [DAG.parents, gB]
lemma pBy2 : H.u2 ∈ (gB H).parents H.y := by simp [DAG.parents, gB]
lemma pByx : H.x ∈ (gB H).parents H.y := by simp [DAG.parents, gB]
lemma pCxy : H.y ∈ (gC H).parents H.x := by simp [DAG.parents, gC]
lemma pCxw : H.w ∈ (gC H).parents H.x := by simp [DAG.parents, gC]
lemma pC1y : H.y ∈ (gC H).parents H.u1 := by simp [DAG.parents, gC]
lemma pC1w : H.w ∈ (gC H).parents H.u1 := by simp [DAG.parents, gC]
lemma pC2y : H.y ∈ (gC H).parents H.u2 := by simp [DAG.parents, gC]

/-! ### Modellene -/

noncomputable def NA : (gA H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u1, by rw [hvx]; exact pAx H⟩)
    else if hvw : v = H.w then
      PMF.pure (xor (pa ⟨H.u1, by rw [hvw]; exact pAw1 H⟩) (pa ⟨H.u2, by rw [hvw]; exact pAw2 H⟩))
    else if hvy : v = H.y then PMF.pure (pa ⟨H.u2, by rw [hvy]; exact pAy H⟩)
    else PMF.uniformOfFintype Bool

noncomputable def NB : (gB H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then
      Bow.chan (xor (pa ⟨H.x, by rw [hvy]; exact pByx H⟩) (pa ⟨H.u2, by rw [hvy]; exact pBy2 H⟩))
    else if hvw : v = H.w then PMF.pure (pa ⟨H.u2, by rw [hvw]; exact pBw H⟩)
    else if v = H.u1 then PMF.pure false
    else PMF.uniformOfFintype Bool

noncomputable def NC : (gC H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then
      Bow.chan (xor (pa ⟨H.y, by rw [hvx]; exact pCxy H⟩) (pa ⟨H.w, by rw [hvx]; exact pCxw H⟩))
    else if hv1 : v = H.u1 then
      PMF.pure (xor (pa ⟨H.y, by rw [hv1]; exact pC1y H⟩) (pa ⟨H.w, by rw [hv1]; exact pC1w H⟩))
    else if hv2 : v = H.u2 then PMF.pure (pa ⟨H.y, by rw [hv2]; exact pC2y H⟩)
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {v // v ∈ (gA H).parents H.x} → Bool) :
    (NA H).kernel H.x pa = Bow.chan (pa ⟨H.u1, pAx H⟩) := by simp [NA]
lemma NA_w (pa : {v // v ∈ (gA H).parents H.w} → Bool) :
    (NA H).kernel H.w pa = PMF.pure (xor (pa ⟨H.u1, pAw1 H⟩) (pa ⟨H.u2, pAw2 H⟩)) := by
  simp [NA, H.hxw.symm]
lemma NA_y (pa : {v // v ∈ (gA H).parents H.y} → Bool) :
    (NA H).kernel H.y pa = PMF.pure (pa ⟨H.u2, pAy H⟩) := by
  simp [NA, H.dxy.symm, H.hwy.symm]
lemma NA_o {v : V} (hvx : v ≠ H.x) (hvw : v ≠ H.w) (hvy : v ≠ H.y)
    (pa : {w // w ∈ (gA H).parents v} → Bool) :
    (NA H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NA, hvx, hvw, hvy]

lemma NB_y (pa : {v // v ∈ (gB H).parents H.y} → Bool) :
    (NB H).kernel H.y pa = Bow.chan (xor (pa ⟨H.x, pByx H⟩) (pa ⟨H.u2, pBy2 H⟩)) := by
  simp [NB]
lemma NB_w (pa : {v // v ∈ (gB H).parents H.w} → Bool) :
    (NB H).kernel H.w pa = PMF.pure (pa ⟨H.u2, pBw H⟩) := by simp [NB, H.hwy]
lemma NB_u1 (pa : {v // v ∈ (gB H).parents H.u1} → Bool) :
    (NB H).kernel H.u1 pa = PMF.pure false := by simp [NB, H.d1y, H.d1w]
lemma NB_o {v : V} (hvy : v ≠ H.y) (hvw : v ≠ H.w) (hv1 : v ≠ H.u1)
    (pa : {w // w ∈ (gB H).parents v} → Bool) :
    (NB H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NB, hvy, hvw, hv1]

lemma NC_x (pa : {v // v ∈ (gC H).parents H.x} → Bool) :
    (NC H).kernel H.x pa = Bow.chan (xor (pa ⟨H.y, pCxy H⟩) (pa ⟨H.w, pCxw H⟩)) := by
  simp [NC]
lemma NC_u1 (pa : {v // v ∈ (gC H).parents H.u1} → Bool) :
    (NC H).kernel H.u1 pa = PMF.pure (xor (pa ⟨H.y, pC1y H⟩) (pa ⟨H.w, pC1w H⟩)) := by
  simp [NC, H.d1x]
lemma NC_u2 (pa : {v // v ∈ (gC H).parents H.u2} → Bool) :
    (NC H).kernel H.u2 pa = PMF.pure (pa ⟨H.y, pC2y H⟩) := by
  simp [NC, H.h2x, H.h12.symm]
lemma NC_o {v : V} (hvx : v ≠ H.x) (hv1 : v ≠ H.u1) (hv2 : v ≠ H.u2)
    (pa : {w // w ∈ (gC H).parents v} → Bool) :
    (NC H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NC, hvx, hv1, hv2]

lemma hsA : ∀ v, (gA H).parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  have ha' : (a = H.u1 ∧ v = H.x) ∨ (a = H.u1 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.w) ∨
      (a = H.u2 ∧ v = H.y) := ha
  rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact H.h1x
  · rw [h1, h2]; exact H.h1w
  · rw [h1, h2]; exact H.h2w
  · rw [h1, h2]; exact H.h2y

lemma hsB : ∀ v, (gB H).parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  have ha' : (a = H.u2 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.y) ∨ (a = H.x ∧ v = H.y) := ha
  rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact H.h2w
  · rw [h1, h2]; exact H.h2y
  · rw [h1, h2]; exact H.hxy

noncomputable def mA : G.CausalModel (fun _ => Bool) := Completeness.liftSub (hsA H) (NA H)
noncomputable def mB : G.CausalModel (fun _ => Bool) := Completeness.liftSub (hsB H) (NB H)

/-! ### Fellesfordelingene -/

/-- Bijeksjonen: `u₁ ↦ u₁ xor y xor w`, `u₂ ↦ u₂ xor y xor w`. -/
def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if v.1 = H.u1 ∨ v.1 = H.u2 then
      xor (s v) (xor (s ⟨H.y, Finset.mem_univ _⟩) (s ⟨H.w, Finset.mem_univ _⟩))
    else s v

lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ H (φ H s) = s := by
  funext ⟨v, hv⟩
  by_cases h : v = H.u1 ∨ v = H.u2
  · have hy : ¬ (H.y = H.u1 ∨ H.y = H.u2) := by
      rintro (e | e)
      · exact H.d1y e.symm
      · exact H.d2y e.symm
    have hw : ¬ (H.w = H.u1 ∨ H.w = H.u2) := by
      rintro (e | e)
      · exact H.d1w e.symm
      · exact H.d2w e.symm
    rcases Bool.eq_false_or_eq_true (s ⟨v, hv⟩) with a | a <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with b | b <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with c | c <;>
    simp [φ, h, hy, hw, a, b, c]
  · simp [φ, h]

/-- Produktet over alle noder, delt opp i de fem spesielle og resten. -/
lemma split5 (f : V → ℝ≥0∞) :
    ∏ v, f v = f H.u1 * (f H.u2 * (f H.x * (f H.w * (f H.y *
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y, f v)))) := by
  have m2 : H.u2 ∈ Finset.univ.erase H.u1 := by simp [H.h12.symm]
  have mx : H.x ∈ (Finset.univ.erase H.u1).erase H.u2 := by
    simp [H.d1x.symm, H.h2x.symm]
  have mw : H.w ∈ ((Finset.univ.erase H.u1).erase H.u2).erase H.x := by
    simp [H.d1w.symm, H.d2w.symm, H.hxw.symm]
  have my : H.y ∈ (((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w := by
    simp [H.d1y.symm, H.d2y.symm, H.dxy.symm, H.hwy.symm]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase _ _ m2, ← Finset.mul_prod_erase _ _ mx,
    ← Finset.mul_prod_erase _ _ mw, ← Finset.mul_prod_erase _ _ my]

lemma mem_rest {v : V}
    (hv : v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y) :
    v ≠ H.y ∧ v ≠ H.w ∧ v ≠ H.x ∧ v ≠ H.u2 ∧ v ≠ H.u1 := by
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

lemma joint_AC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (NC H).fullJoint s = (mA H).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, BowGen.kfac_liftG]
  rw [split5 H, split5 H]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NC H) Finset.univ s v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hy, hw, hx, h2, h1⟩ := H.mem_rest hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NC_o H hx h1 h2, NA_o H hx hw hy]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NA_o, Data.NC_x, Data.NC_u1,
    Data.NC_u2, Data.NC_o, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.hwy, H.hwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma joint_BA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB H).fullJoint (φ H s) = (mA H).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
  rw [split5 H, split5 H]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NB H) Finset.univ (φ H s) v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hy, hw, hx, h2, h1⟩ := H.mem_rest hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o H hy hw h1, NA_o H hx hw hy]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NA_o, Data.NB_y, Data.NB_w,
    Data.NB_u1, Data.NB_o, φ, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.hwy, H.hwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma full_map : (mB H).fullJoint = (mA H).fullJoint.map (φ H) := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (φ H s)]
  · rw [if_pos (φ_invol H s).symm, ← joint_BA H (φ H s), φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, φ_invol]

lemma obsEq (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) :
    (mA H).marginal O = (mB H).marginal O := by
  unfold CausalModel.marginal
  rw [full_map H, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ¬ (v = H.u1 ∨ v = H.u2) := by
    rintro (e | e)
    · exact hu1 (e ▸ hv)
    · exact hu2 (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ, hv']

lemma margAC (T : Finset V) : (mA H).marginal T = (NC H).marginal T := by
  have hj : (NC H).fullJoint = (mA H).fullJoint := PMF.ext (joint_AC H)
  unfold CausalModel.marginal
  rw [hj]

/-! ### Utregninger i C og B -/

lemma ancC (S : Finset V) (hyS : H.y ∈ S) (hwS : H.w ∈ S) (h1 : H.u1 ∉ S) (h2 : H.u2 ∉ S) :
    ∀ v ∈ S, ∀ a, (gC H).edge a v → a ∈ S := by
  intro v hv a ha
  have ha' : (a = H.y ∧ v = H.x) ∨ (a = H.w ∧ v = H.x) ∨ (a = H.y ∧ v = H.u1) ∨
      (a = H.w ∧ v = H.u1) ∨ (a = H.y ∧ v = H.u2) := ha
  rcases ha' with ⟨e1, _⟩ | ⟨e1, _⟩ | ⟨_, e2⟩ | ⟨_, e2⟩ | ⟨_, e2⟩
  · rw [e1]; exact hyS
  · rw [e1]; exact hwS
  · exact absurd (e2 ▸ hv) h1
  · exact absurd (e2 ▸ hv) h1
  · exact absurd (e2 ▸ hv) h2

lemma posA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hy : H.y ∈ O) (hw : H.w ∈ O) :
    ∀ a, (mA H).marginal O a ≠ 0 := by
  intro a
  have hS := H.ancC O hy hw hu1 hu2
  rw [margAC H O, marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (parOf hS v hv)]
  have hv1 : v ≠ H.u1 := fun e => hu1 (e ▸ hv)
  have hv2 : v ≠ H.u2 := fun e => hu2 (e ▸ hv)
  by_cases hvx : v = H.x
  · subst hvx
    rw [NC_x]
    exact Bow.chan_ne_zero _ _
  · rw [NC_o H hvx hv1 hv2]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y, H.w}) :
    (doModel (mA H) {H.x} x0).marginal {H.y, H.w} y0 = (mA H).marginal {H.y, H.w} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel (mA H) {H.x} x0) (doModel (NA H) {H.x} x0)
    (BowGen.kfac_lift_doG (hsA H) (NA H) {H.x} x0) {H.y, H.w}]
  have hanc : ∀ v ∈ ({H.u1, H.u2, H.w, H.y} : Finset V), ∀ a, (gA H).edge a v →
      a ∈ ({H.u1, H.u2, H.w, H.y} : Finset V) := by
    intro v _ a ha
    have ha' : (a = H.u1 ∧ v = H.x) ∨ (a = H.u1 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.w) ∨
        (a = H.u2 ∧ v = H.y) := ha
    rcases ha' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({H.u1, H.u2, H.w, H.y} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.d1x.symm, H.h2x.symm, H.hxw, H.dxy]
  rw [Rule3.doModel_marginal_of_sub (NA H) {H.x} x0 {H.u1, H.u2, H.w, H.y} hanc hdisj
      {H.y, H.w} (by intro v hv; simp at hv ⊢; tauto) y0,
    ← Completeness.marginal_eq_of_kfac (mA H) (NA H) (BowGen.kfac_liftG (hsA H) (NA H))
      {H.y, H.w}]

/-- **To røtter: `P(y, w | do(x))` er ikke identifiserbar.** -/
theorem not_ident (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (hy : H.y ∈ O) (hw : H.w ∈ O) (hx : H.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y, H.w} := by
  intro h
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hwx : H.w ≠ H.x := H.hxw.symm
  have hYX : Disjoint ({H.y, H.w} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.dxy, H.hxw]
  have hnp : ∀ a, ¬ (gB H).edge a H.x := by
    intro a ha
    have ha' : (a = H.u2 ∧ H.x = H.w) ∨ (a = H.u2 ∧ H.x = H.y) ∨ (a = H.x ∧ H.x = H.y) := ha
    rcases ha' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
    · exact H.hxw e
    · exact H.dxy e
    · exact H.dxy e
  have hSx : ∀ v ∈ ({H.x} : Finset V), ∀ a, (gB H).edge a v → a ∈ ({H.x} : Finset V) := by
    intro v hv a ha
    rw [Finset.mem_singleton] at hv
    subst hv
    exact absurd ha (hnp a)
  have hOY : ({H.y, H.w} : Finset V) ∪ {H.x} ⊆ O := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with (rfl | rfl) | rfl
    · exact hy
    · exact hw
    · exact hx
  have hC1 := H.ancC ({H.y, H.w} ∪ {H.x}) (by simp) (by simp)
    (by simp [H.d1y, H.d1w, H.d1x]) (by simp [H.d2y, H.d2w, H.h2x])
  have hC2 := H.ancC ({H.y, H.w} : Finset V) (by simp) (by simp)
    (by simp [H.d1y, H.d1w]) (by simp [H.d2y, H.d2w])
  have key : ∀ b : Bool,
      Bow.chan true b * ((Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹) =
        ((Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹) *
          (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y, H.w} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else if v.1 = H.y then true else false
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y, H.w} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    -- Identifiserbarheten
    have e := h (mA H) (mB H) (obsEq H O hu1 hu2) (posA H O hu1 hu2 hy hw) t
    rw [htx, doA H O hu1 hu2,
      Completeness.marginal_eq_of_kfac (doModel (mB H) {H.x} _) (doModel (NB H) {H.x} _)
        (BowGen.kfac_lift_doG (hsB H) (NB H) {H.x} _) {H.y, H.w}] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 (NB H) {H.x} {H.y, H.w} hYX
      (Completeness.dsep_isolated hnp {H.y, H.w} (by simp [H.dxy, H.hxw])) t
    rw [htx, ← e] at fd
    -- P_B(y, w, x) = P_C(y, w, x)
    rw [show (NB H).marginal ({H.y, H.w} ∪ {H.x}) = (NC H).marginal ({H.y, H.w} ∪ {H.x}) from by
      rw [← Completeness.marginal_eq_of_kfac (mB H) (NB H) (BowGen.kfac_liftG (hsB H) (NB H)),
        ← marginal_eq_of_sub (obsEq H O hu1 hu2) hOY, margAC]] at fd
    rw [margAC H] at fd
    -- Produktene
    have hyw : H.y ∉ ({H.w} : Finset V) := by simp [H.hwy.symm]
    rw [marginal_ancestral_apply _ _ hC1 t, Finset.prod_union hYX, Finset.prod_insert hyw,
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t H.y (by simp) (parOf hC1 H.y (by simp)),
      BowGen.kfac_eqG _ _ t H.w (by simp) (parOf hC1 H.w (by simp)),
      BowGen.kfac_eqG _ _ t H.x (by simp) (parOf hC1 H.x (by simp)),
      NC_o H hyx H.d1y.symm H.d2y.symm, NC_o H hwx H.d1w.symm H.d2w.symm, NC_x] at fd
    rw [marginal_ancestral_apply _ _ hC2, Finset.prod_insert hyw, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ _ H.y (by simp) (parOf hC2 H.y (by simp)),
      BowGen.kfac_eqG _ _ _ H.w (by simp) (parOf hC2 H.w (by simp)),
      NC_o H hyx H.d1y.symm H.d2y.symm, NC_o H hwx H.d1w.symm H.d2w.symm] at fd
    rw [marginal_ancestral_apply _ {H.x} hSx, Finset.prod_singleton,
      BowGen.kfac_eqG _ {H.x} _ H.x (by simp) (parOf hSx H.x (by simp)),
      NB_o H hyx.symm H.hxw H.d1x.symm] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, hyx, hwx, H.hwy,
      mul_comm, mul_left_comm, mul_assoc] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  have hc : Bow.chan true true = Bow.chan true false := by
    first
    | exact (ENNReal.mul_left_inj hQ0 hQT).mp k
    | exact ENNReal.mul_right_cancel hQ0 hQT k
    | exact (by
        have h1 := congrArg (· / ((Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹)) k
        simp only [ENNReal.mul_div_cancel_right hQ0 hQT] at h1
        exact h1)
    | exact?
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (false = true) by decide)] at hc
  exact Bow.q_ne hc

end Data

/-- **c-skog med to røtter.** -/
theorem twoRoot_not_identifiable (G : DAG V) (O : Finset V) (u1 u2 x w y : V)
    (h1x : G.edge u1 x) (h1w : G.edge u1 w) (h2w : G.edge u2 w) (h2y : G.edge u2 y)
    (hxy : G.edge x y) (h12 : u1 ≠ u2) (hxw : x ≠ w) (hwy : w ≠ y)
    (hu1 : u1 ∉ O) (hu2 : u2 ∉ O) (hx : x ∈ O) (hy : y ∈ O) (hw : w ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y, w} :=
  Data.not_ident ⟨u1, u2, x, w, y, h1x, h1w, h2w, h2y, hxy, h12,
    fun e => hu2 (e ▸ hx), hxw, hwy⟩ O hu1 hu2 hy hw hx

end TwoRoot
end Identification

#print axioms Identification.TwoRoot.twoRoot_not_identifiable

/-! ## Runde 14: c-skoger med flere røtter

Et latent tre over `x` og nodene `nd₀, …, nd_{n+1}` (med `x` som blad, festet til
`nd₀`), og et rettet skog-mønster: hver node peker på en forelder `dp k` eller er en
rot (`dp k = none`). `x → nd₀`, og `nd₀` er en rot. Da er `P(R | do(x))` ikke
identifiserbar, der `R` er mengden av røtter.

Her står bare konfigurasjonen `MR` og hjelpefunksjonene `ext` og `chan_mix`.
Beviset ble generalisert i runde 15 (`RootPath`), og teoremet
`multiRoot_not_identifiable` står etter runde 15, som korollar med `r = 0` og
stien `{u₀}`. -/

namespace Identification
namespace MultiRoot

open HedgeChain (ev xx xb chan_symm)
open PathTree (b2z z2b b2z_z2b eq_z2b b2z_xor b2z_inj two)
open LatentTree (Lrearr)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Verdien av en delvis tilordning, med `false` utenfor. -/
def ext {S : Finset V} (pa : Assignment (α := fun _ : V => Bool) S) (v : V) : Bool :=
  if h : v ∈ S then pa ⟨v, h⟩ else false

lemma ext_restrict (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    {S : Finset V} {v : V} (hv : v ∈ S) :
    ext (s.restrict (Finset.subset_univ S)) v = ev s v := by
  simp [ext, hv, Assignment.restrict, ev]

lemma chan_mix (a b c : Bool) : Bow.chan (xor a (xor b c)) b = Bow.chan c a := by
  rw [Bow.chan_apply, Bow.chan_apply]
  cases a <;> cases b <;> cases c <;> rfl

/-- Konfigurasjonen. -/
structure MR (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hdp0 : dp 0 = none
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd 0)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace MR

variable {G : DAG V} {n : ℕ} (P : MR G n)

/-- Røttene. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- Røttene som noder. -/
def Y : Finset V := P.Rt.image P.nd

lemma mem_Rt0 : (0 : Fin (n + 2)) ∈ P.Rt := by simp [Rt, P.hdp0]

lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

end MR

end MultiRoot
end Identification

/-! ## Runde 15: x kan peke inn i en hvilken som helst rot

Som runde 14, men `x → nd_r` for en vilkårlig rot `r`, ikke bare `nd₀`. Den latente
naboen til `x` er fortsatt `u₀`. En *sti* `pth` av latente fra `u₀` til `u_r` er gitt
ved paritetsvilkåret

  `pth k + #{barn j av k på stien} = [k = r]`   (mod 2),

dvs. hver node har et partall sti-latente inntil seg, unntatt `nd_r`, som har ett.

* Bijeksjonen flytter hele stien med `ΣR`. Pariteten endres da bare i `nd_r`.
* Modell B legger støykanalen på `nd_r` i stedet for `nd₀`; ellers er alt som i
  runde 14. Runde 13 (to røtter) og runde 14 er spesialtilfeller. -/

namespace Identification
namespace RootPath

open HedgeChain (ev xx xb chan_symm)
open PathTree (b2z z2b b2z_z2b eq_z2b b2z_xor b2z_inj two)
open LatentTree (Lrearr)

variable {V : Type*} [DecidableEq V] [Fintype V]

open MultiRoot (ext ext_restrict chan_mix)

/-- Konfigurasjonen. -/
structure RP (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  r : Fin (n + 2)
  pth : Fin (n + 2) → Bool
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hr : dp r = none
  hp0 : pth 0 = true
  hpk : ∀ k, b2z (pth k) + (∑ j, if bp j = some k then b2z (pth j) else 0) =
    if k = r then 1 else 0
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd r)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace RP

variable {G : DAG V} {n : ℕ} (P : RP G n)

/-- Røttene. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- Røttene som noder. -/
def Y : Finset V := P.Rt.image P.nd

lemma mem_Rtr : P.r ∈ P.Rt := by simp [Rt, P.hr]

lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

/-! ### Grafene -/

noncomputable def gA : DAG V where
  edge a b := (a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)

noncomputable def gB : DAG V where
  edge a b := (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hxr

noncomputable def gC : DAG V where
  edge a b := (∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨ (∃ k j, a = P.nd k ∧ b = P.u j)
  decEdge := fun _ _ => Classical.dec _
  rank := fun v => if ∃ k, P.nd k = v then 0 else 1
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, _, h1, h2⟩ | ⟨k, j, h1, h2⟩
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.x := fun ⟨k', e⟩ => P.hndx k' e
      simp [this]
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.u j := fun ⟨k', e⟩ => P.hund j k' e.symm
      simp [this]

lemma eA (a b : V) : P.gA.edge a b ↔ ((a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)) := Iff.rfl
lemma eB (a b : V) : P.gB.edge a b ↔ ((∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)) := Iff.rfl
lemma eC (a b : V) : P.gC.edge a b ↔ ((∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨
    (∃ k j, a = P.nd k ∧ b = P.u j)) := Iff.rfl

lemma parA {a b : V} : a ∈ P.gA.parents b ↔ P.gA.edge a b := by simp [DAG.parents]
lemma parB {a b : V} : a ∈ P.gB.parents b ↔ P.gB.edge a b := by simp [DAG.parents]
lemma parC {a b : V} : a ∈ P.gC.parents b ↔ P.gC.edge a b := by simp [DAG.parents]

lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [P.parA] at ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (P.eA a v).mp ha with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
  · rw [h1, h2]; exact P.hux
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd

lemma hsB : ∀ v, P.gB.parents v ⊆ G.parents v := by
  intro v a ha
  rw [P.parB] at ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (P.eB a v).mp ha with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd
  · rw [h1, h2]; exact P.hxr

/-! ### Pariteten i en node -/

/-- Pariteten til foreldrene til `nd k` i A, lest av en verdifunksjon `g`. -/
def parZ (k : Fin (n + 2)) (g : V → Bool) : ZMod 2 :=
  b2z (g (P.u k)) + (∑ j, if P.bp j = some k then b2z (g (P.u j)) else 0) +
    ∑ j, if P.dp j = some k then b2z (g (P.nd j)) else 0

lemma parZ_congr (k : Fin (n + 2)) {g h : V → Bool} (hu : ∀ j, g (P.u j) = h (P.u j))
    (hn : ∀ j, g (P.nd j) = h (P.nd j)) : P.parZ k g = P.parZ k h := by
  simp only [parZ, hu, hn]

lemma parZ_extA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gA.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (P.parA.mpr ((P.eA _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩))))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (P.parA.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (P.parA.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

lemma parZ_extB (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gB.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (P.parB.mpr ((P.eB _ _).mpr (Or.inl ⟨k, rfl, rfl⟩)))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (P.parB.mpr ((P.eB _ _).mpr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (P.parB.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

/-! ### Løsningen nedenfra og opp (som i runde 9) -/

def solN (R : Fin (n + 2) → ZMod 2) : ℕ → Fin (n + 2) → ZMod 2
  | 0, k => R k
  | m + 1, k => R k + ∑ j, if P.bp j = some k then solN R m j else 0

def M : ℕ := Finset.univ.sup P.ht

lemma ht_le (k : Fin (n + 2)) : P.ht k ≤ P.M := Finset.le_sup (Finset.mem_univ k)

lemma stab (R : Fin (n + 2) → ZMod 2) :
    ∀ m k, P.ht k ≤ m → P.solN R (m + 1) k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then P.solN R 0 j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show R k + _ = R k
    rw [hz, add_zero]
  | succ m ih =>
    intro k hk
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma uniq (R ℓ : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) :
    ∀ m k, P.ht k ≤ m → ℓ k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then ℓ j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show ℓ k = R k
    rw [hE k, hz, add_zero]
  | succ m ih =>
    intro k hk
    rw [hE k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma sol_iff (R ℓ : Fin (n + 2) → ZMod 2) :
    (∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) ↔
      ∀ k, ℓ k = P.solN R (P.M + 1) k := by
  constructor
  · intro hE k
    exact P.uniq R ℓ hE (P.M + 1) k (by have := P.ht_le k; omega)
  · intro h k
    rw [h k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rw [h j, P.stab R P.M j (P.ht_le j)]
    · rfl


/-! ### Algebraen -/

lemma Z1 : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide
lemma Z2 : ∀ N Q S L : ZMod 2, N + Q = S + L → (N = Q ↔ L = S) := by decide
lemma z2b_add : ∀ (a : ZMod 2) (c : Bool), z2b (a + b2z c) = xor (z2b a) c := by decide

/-- **Residualidentiteten.** Summen av residualene over alle noder er
`Σ_{røtter} N + L₀`, uansett verdier. -/
lemma resid (L N : Fin (n + 2) → ZMod 2) :
    ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = (∑ k ∈ P.Rt, N k) + L 0 := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then L j else 0) = if j = 0 then 0 else L j := by
    intro j
    by_cases hj : j = 0
    · have hb : P.bp j = none := (P.hbp0 j).mpr hj
      rw [hb]
      simp [hj]
    · cases hb : P.bp j with
      | none => exact absurd ((P.hbp0 j).mp hb) hj
      | some k0 => simp [hj]
  have h2 : ∀ j, (∑ k, if P.dp j = some k then N j else 0) =
      if P.dp j = none then 0 else N j := by
    intro j
    cases hd : P.dp j <;> simp
  have hB : ∑ k, (∑ j, if P.bp j = some k then L j else 0) =
      ∑ j, (if j = 0 then 0 else L j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hD : ∑ k, (∑ j, if P.dp j = some k then N j else 0) =
      ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hL : ∑ j, L j = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
    calc ∑ j, L j = ∑ j, ((if j = 0 then L j else 0) + (if j = 0 then 0 else L j)) :=
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
      _ = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp
  have hN : ∑ j, N j = (∑ k ∈ P.Rt, N k) + ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Rt, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hsplit : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) =
      ∑ k, N k + ∑ k, L k + ∑ k, (∑ j, if P.bp j = some k then L j else 0) +
        ∑ k, (∑ j, if P.dp j = some k then N j else 0) := by
    simp only [Finset.sum_add_distrib]
    ring
  rw [hsplit, hB, hD, hL, hN]
  have t1 := two (∑ j, (if j = 0 then 0 else L j))
  have t2 := two (∑ j, (if P.dp j = none then 0 else N j))
  linear_combination t1 + t2

/-- Holder alle likningene, er `L₀` summen over røttene. -/
lemma eqs_sum (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [← hE k]; exact two _)
  rw [hz] at h
  exact Z1 _ _ h

/-- Holder likningene utenfor `nd_r`, er likningen i `nd_r` ekvivalent med
`L₀ = Σ_{røtter} N`. -/
lemma eqr_iff (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, k ≠ P.r → N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    (N P.r = L P.r + (∑ j, if P.bp j = some P.r then L j else 0) +
      ∑ j, if P.dp j = some P.r then N j else 0) ↔ L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k ∈ Finset.univ.erase P.r, (N k + (L k +
      (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k hk => by rw [← hE k (Finset.ne_of_mem_erase hk)]; exact two _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P.r), hz, add_zero] at h
  exact Z2 _ _ _ _ h

/-! ### C-modellens latente løsning -/

/-- `r_k = N_k + barna til k`, lest av `g`. -/
def Rg (g : V → Bool) (k : Fin (n + 2)) : ZMod 2 :=
  b2z (g (P.nd k)) + ∑ j, if P.dp j = some k then b2z (g (P.nd j)) else 0

lemma keyAC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (∀ k, ev s (P.nd k) = z2b (P.parZ k (ev s))) ↔
      ∀ j, ev s (P.u j) = z2b (P.solN (P.Rg (ev s)) (P.M + 1) j) := by
  have step : ∀ k, (ev s (P.nd k) = z2b (P.parZ k (ev s))) ↔
      (b2z (ev s (P.u k)) = P.Rg (ev s) k +
        ∑ j, if P.bp j = some k then b2z (ev s (P.u j)) else 0) := by
    intro k
    rw [eq_z2b]
    exact Lrearr _ _ _ _
  exact (forall_congr' step).trans ((P.sol_iff (P.Rg (ev s))
    (fun k => b2z (ev s (P.u k)))).trans (forall_congr' fun j => (eq_z2b _ _).symm))

/-! ### Modellene -/

lemma pAx : P.u 0 ∈ P.gA.parents P.x := P.parA.mpr ((P.eA _ _).mpr (Or.inl ⟨rfl, rfl⟩))
lemma pBx : P.x ∈ P.gB.parents (P.nd P.r) :=
  P.parB.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
lemma pCx (k : Fin (n + 2)) (hk : P.dp k = none) : P.nd k ∈ P.gC.parents P.x :=
  P.parC.mpr ((P.eC _ _).mpr (Or.inl ⟨k, hk, rfl, rfl⟩))
lemma pCu (k j : Fin (n + 2)) : P.nd k ∈ P.gC.parents (P.u j) :=
  P.parC.mpr ((P.eC _ _).mpr (Or.inr ⟨k, j, rfl, rfl⟩))

noncomputable def NA : P.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (ext pa (P.u 0))
    else if h : ∃ k, P.nd k = v then PMF.pure (z2b (P.parZ (Classical.choose h) (ext pa)))
    else PMF.uniformOfFintype Bool

noncomputable def NB : P.gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h : ∃ k, P.nd k = v then
      (if Classical.choose h = P.r then Bow.chan (xor (ext pa P.x) (z2b (P.parZ P.r (ext pa))))
       else PMF.pure (z2b (P.parZ (Classical.choose h) (ext pa))))
    else if v = P.u 0 then PMF.pure false
    else PMF.uniformOfFintype Bool

noncomputable def NC : P.gC.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (z2b (∑ k ∈ P.Rt, b2z (ext pa (P.nd k))))
    else if h : ∃ j, P.u j = v then
      PMF.pure (z2b (P.solN (P.Rg (ext pa)) (P.M + 1) (Classical.choose h)))
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) :
    P.NA.kernel P.x pa = Bow.chan (ext pa (P.u 0)) := by
  simp [NA]

lemma NA_nd (k : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) :
    P.NA.kernel (P.nd k) pa = PMF.pure (z2b (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NA, if_neg (P.hndx k), dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h)]

lemma NA_o {v : V} (hvx : v ≠ P.x) (hv : ∀ k, P.nd k ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents v)) :
    P.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NA, if_neg hvx, dif_neg h]

lemma NB_ndr (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd P.r))) :
    P.NB.kernel (P.nd P.r) pa = Bow.chan (xor (ext pa P.x) (z2b (P.parZ P.r (ext pa)))) := by
  have h : ∃ k', P.nd k' = P.nd P.r := ⟨P.r, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = P.r from P.ndinj (Classical.choose_spec h), if_pos rfl]

lemma NB_nd (k : Fin (n + 2)) (hk : k ≠ P.r)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd k))) :
    P.NB.kernel (P.nd k) pa = PMF.pure (z2b (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h), if_neg hk]

lemma NB_u0 (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.u 0))) :
    P.NB.kernel (P.u 0) pa = PMF.pure false := by
  have h : ¬ ∃ k, P.nd k = P.u 0 := fun ⟨k, hk⟩ => P.hund 0 k hk.symm
  simp only [NB, dif_neg h]
  all_goals first | rfl | exact if_pos rfl | simp

lemma NB_o {v : V} (hv : ∀ k, P.nd k ≠ v) (hv0 : v ≠ P.u 0)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents v)) :
    P.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NB, dif_neg h, if_neg hv0]

lemma NC_x (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents P.x)) :
    P.NC.kernel P.x pa = Bow.chan (z2b (∑ k ∈ P.Rt, b2z (ext pa (P.nd k)))) := by
  simp [NC]

lemma NC_u (j : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents (P.u j))) :
    P.NC.kernel (P.u j) pa = PMF.pure (z2b (P.solN (P.Rg (ext pa)) (P.M + 1) j)) := by
  have h : ∃ j', P.u j' = P.u j := ⟨j, rfl⟩
  simp only [NC, if_neg (P.hux' j), dif_pos h]
  rw [show Classical.choose h = j from P.uinj (Classical.choose_spec h)]

lemma NC_o {v : V} (hvx : v ≠ P.x) (hv : ∀ j, P.u j ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents v)) :
    P.NC.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, P.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [NC, if_neg hvx, dif_neg h]

noncomputable def mA : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsA P.NA
noncomputable def mB : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsB P.NB

lemma Rg_ext (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    P.Rg (ext (s.restrict (Finset.subset_univ (P.gC.parents (P.u j))))) = P.Rg (ev s) := by
  funext k
  unfold Rg
  rw [ext_restrict s (P.pCu k j)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [ext_restrict s (P.pCu i j)]
  · rfl

/-! ### Produktene -/

lemma pure1 {a b : Bool} (h : b = a) : PMF.pure a b = 1 := by
  rw [h]
  first | exact PMF.pure_apply_self _ | exact PMF.pure_apply_self | simp

lemma pure0 {a b : Bool} (h : ¬ b = a) : PMF.pure a b = 0 := by
  first | exact PMF.pure_apply_of_ne _ _ h | exact PMF.pure_apply_of_ne h | simp [PMF.pure_apply, h]

/-- Resten av nodene. -/
def R5 : Finset V := (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd))ᶜ

lemma mem_R5 {v : V} : v ∈ P.R5 ↔ v ≠ P.x ∧ (∀ j, P.u j ≠ v) ∧ (∀ k, P.nd k ≠ v) := by
  simp [R5]

lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f P.x * ((∏ j, f (P.u j)) * ((∏ k, f (P.nd k)) * ∏ v ∈ P.R5, f v)) := by
  rw [← Finset.prod_mul_prod_compl (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd)) f]
  have hx : P.x ∉ Finset.univ.image P.u ∪ Finset.univ.image P.nd := by
    simp [P.hux', P.hndx]
  have hd : Disjoint (Finset.univ.image P.u) (Finset.univ.image P.nd) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨k, hk⟩ := hb
    exact P.hund j k hk.symm
  rw [Finset.prod_insert hx, Finset.prod_union hd]
  first
    | rw [Finset.prod_image P.uinj.injOn, Finset.prod_image P.ndinj.injOn]
    | rw [Finset.prod_image (P.uinj.injOn _), Finset.prod_image (P.ndinj.injOn _)]
    | rw [Finset.prod_image (fun a _ b _ h => P.uinj h), Finset.prod_image (fun a _ b _ h => P.ndinj h)]
  simp only [R5, mul_assoc]

noncomputable abbrev c2 : ℝ≥0∞ := (Fintype.card Bool : ℝ≥0∞)⁻¹

lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NA Finset.univ s P.x = Bow.chan (ev s (P.u 0)) (ev s P.x) := by
  rw [DoAudit.kfac_univ, P.NA_x, ext_restrict s P.pAx]
  all_goals rfl

lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.u j) = c2 := by
  rw [DoAudit.kfac_univ, P.NA_o (P.hux' j) (fun k e => P.hund j k e.symm),
    PMF.uniformOfFintype_apply]

lemma A_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.nd k) = PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) := by
  rw [DoAudit.kfac_univ, P.NA_nd, P.parZ_extA]
  all_goals rfl

lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NA Finset.univ s v = c2 := by
  obtain ⟨h1, _, h3⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NA_o h1 h3, PMF.uniformOfFintype_apply]

lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t P.x = c2 := by
  rw [DoAudit.kfac_univ, P.NB_o P.hndx (fun e => P.hux' 0 e.symm), PMF.uniformOfFintype_apply]

lemma B_u0 (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.u 0) = PMF.pure false (ev t (P.u 0)) := by
  rw [DoAudit.kfac_univ, P.NB_u0]
  all_goals rfl

lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : j ≠ 0) : kfac P.NB Finset.univ t (P.u j) = c2 := by
  rw [DoAudit.kfac_univ, P.NB_o (fun k e => P.hund j k e.symm)
    (fun e => hj (P.uinj e)), PMF.uniformOfFintype_apply]

lemma B_ndr (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.nd P.r) =
      Bow.chan (xor (ev t P.x) (z2b (P.parZ P.r (ev t)))) (ev t (P.nd P.r)) := by
  rw [DoAudit.kfac_univ, P.NB_ndr, P.parZ_extB, ext_restrict t P.pBx]
  all_goals rfl

lemma B_nd (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2))
    (hk : k ≠ P.r) :
    kfac P.NB Finset.univ t (P.nd k) = PMF.pure (z2b (P.parZ k (ev t))) (ev t (P.nd k)) := by
  rw [DoAudit.kfac_univ, P.NB_nd k hk, P.parZ_extB]
  all_goals rfl

lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NB Finset.univ t v = c2 := by
  obtain ⟨_, h2, h3⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NB_o h3 (fun e => h2 0 e.symm), PMF.uniformOfFintype_apply]

lemma C_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NC Finset.univ s P.x =
      Bow.chan (z2b (∑ k ∈ P.Rt, b2z (ev s (P.nd k)))) (ev s P.x) := by
  have hs : ∑ k ∈ P.Rt, b2z (ext (s.restrict (Finset.subset_univ (P.gC.parents P.x))) (P.nd k)) =
      ∑ k ∈ P.Rt, b2z (ev s (P.nd k)) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [ext_restrict s (P.pCx k (by simpa [Rt] using hk))])
  rw [DoAudit.kfac_univ, P.NC_x, hs]
  all_goals rfl

lemma C_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.u j) =
      PMF.pure (z2b (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) := by
  rw [DoAudit.kfac_univ, P.NC_u, P.Rg_ext]
  all_goals rfl

lemma C_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.nd k) = c2 := by
  rw [DoAudit.kfac_univ, P.NC_o (P.hndx k) (fun j => P.hund j k), PMF.uniformOfFintype_apply]

lemma C_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NC Finset.univ s v = c2 := by
  obtain ⟨h1, h2, _⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NC_o h1 h2, PMF.uniformOfFintype_apply]

/-! ### A og C har samme fellesfordeling -/

lemma joint_AC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.NC.fullJoint s = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, BowGen.kfac_liftG]
  rw [P.prod_split, P.prod_split]
  have hR : ∏ v ∈ P.R5, kfac P.NC Finset.univ s v = ∏ v ∈ P.R5, kfac P.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [P.C_o s v hv, P.A_o s v hv])
  rw [hR, P.C_x, P.A_x]
  simp only [P.C_u, P.A_u, P.C_nd, P.A_nd]
  by_cases hE : ∀ k, ev s (P.nd k) = z2b (P.parZ k (ev s))
  · have hsol := (P.keyAC s).mp hE
    have h0 : ev s (P.u 0) = z2b (∑ k ∈ P.Rt, b2z (ev s (P.nd k))) := by
      apply b2z_inj
      rw [b2z_z2b]
      exact P.eqs_sum (fun k => b2z (ev s (P.u k))) (fun k => b2z (ev s (P.nd k)))
        (fun k => (eq_z2b _ _).mp (hE k))
    have hU : ∏ j, PMF.pure (z2b (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) = 1 :=
      Finset.prod_eq_one (fun j _ => pure1 (hsol j))
    have hN : ∏ k, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k _ => pure1 (hE k))
    rw [hU, hN, h0]
    ring
  · have hsol : ¬ ∀ j, ev s (P.u j) = z2b (P.solN (P.Rg (ev s)) (P.M + 1) j) :=
      fun h => hE ((P.keyAC s).mpr h)
    push_neg at hE hsol
    obtain ⟨k, hk⟩ := hE
    obtain ⟨j, hj⟩ := hsol
    have hU : ∏ j, PMF.pure (z2b (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (pure0 hj)
    have hN : ∏ k, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (pure0 hk)
    rw [hU, hN]
    simp

lemma margAC (T : Finset V) : P.mA.marginal T = P.NC.marginal T := by
  have hj : P.NC.fullJoint = P.mA.fullJoint := PMF.ext (P.joint_AC)
  unfold CausalModel.marginal
  rw [hj]

/-! ### Bijeksjonen mellom A og B -/

noncomputable def Sb (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) : Bool :=
  z2b (∑ k ∈ P.Rt, b2z (ev s (P.nd k)))

/-- Bijeksjonen: hver latent på stien flyttes med summen over røttene. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if ∃ j, P.pth j = true ∧ P.u j = v.1 then xor (s v) (P.Sb s) else s v

lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : P.pth j = true) : ev (P.φ s) (P.u j) = xor (ev s (P.u j)) (P.Sb s) := by
  have h : ∃ j', P.pth j' = true ∧ P.u j' = P.u j := ⟨j, hj, rfl⟩
  simp only [φ, ev, if_pos h]

lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, P.pth j = true → P.u j ≠ v) : ev (P.φ s) v = ev s v := by
  have h : ¬ ∃ j, P.pth j = true ∧ P.u j = v := fun ⟨j, hj, e⟩ => hv j hj e
  simp only [φ, ev, if_neg h]

lemma φ_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev (P.φ s) (P.nd k) = ev s (P.nd k) := P.φ_o s (fun j _ => P.hund j k)

lemma φ_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ev (P.φ s) P.x = ev s P.x := P.φ_o s (fun j _ => P.hux' j)

/-- `φ` i `ZMod 2`: latent `j` flyttes med `pth j · ΣR`. -/
lemma bz_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    b2z (ev (P.φ s) (P.u j)) = b2z (ev s (P.u j)) + b2z (P.pth j) * b2z (P.Sb s) := by
  cases hj : P.pth j
  · rw [P.φ_o s (fun j' hj' e => by rw [P.uinj e, hj] at hj'; exact Bool.false_ne_true hj')]
    simp [b2z]
  · rw [P.φ_u s j hj, b2z_xor]
    simp [b2z]

lemma Sb_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.Sb (P.φ s) = P.Sb s := by
  unfold Sb
  simp only [P.φ_nd]

lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.φ (P.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (P.φ (P.φ s)) v = ev s v
  by_cases h : ∃ j, P.pth j = true ∧ P.u j = v
  · obtain ⟨j, hj, rfl⟩ := h
    rw [P.φ_u _ j hj, P.Sb_φ, P.φ_u s j hj]
    exact xx _ _
  · have hv' : ∀ j, P.pth j = true → P.u j ≠ v := fun j hj e => h ⟨j, hj, e⟩
    rw [P.φ_o _ hv', P.φ_o _ hv']

/-- **Stivilkåret i bruk:** pariteten endres bare i `nd_r`. -/
lemma parZ_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.parZ k (ev (P.φ s)) = P.parZ k (ev s) + (if k = P.r then 1 else 0) * b2z (P.Sb s) := by
  have e1 : (∑ j, if P.bp j = some k then b2z (ev (P.φ s) (P.u j)) else 0) =
      (∑ j, if P.bp j = some k then b2z (ev s (P.u j)) else 0) +
        (∑ j, if P.bp j = some k then b2z (P.pth j) else 0) * b2z (P.Sb s) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · exact P.bz_φ s j
    · simp
  have e2 : (∑ j, if P.dp j = some k then b2z (ev (P.φ s) (P.nd j)) else 0) =
      ∑ j, if P.dp j = some k then b2z (ev s (P.nd j)) else 0 := by
    simp only [P.φ_nd]
  unfold parZ
  rw [P.bz_φ s k, e1, e2, ← P.hpk k]
  ring

lemma joint_BA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.mB.fullJoint (P.φ s) = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
  rw [P.prod_split, P.prod_split]
  have hR : ∏ v ∈ P.R5, kfac P.NB Finset.univ (P.φ s) v = ∏ v ∈ P.R5, kfac P.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [P.B_o _ v hv, P.A_o s v hv])
  have hBu : ∏ j, kfac P.NB Finset.univ (P.φ s) (P.u j) =
      PMF.pure false (xor (ev s (P.u 0)) (P.Sb s)) * ∏ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c2 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (n + 2))), P.B_u0,
      P.φ_u s 0 P.hp0]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => P.B_u _ j (Finset.ne_of_mem_erase hj))
  have hAu : ∏ j, kfac P.NA Finset.univ s (P.u j) = c2 * ∏ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c2 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    simp only [P.A_u]
  have hBn : ∏ k, kfac P.NB Finset.univ (P.φ s) (P.nd k) =
      Bow.chan (xor (ev s P.x) (z2b (P.parZ P.r (ev s) + b2z (P.Sb s)))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r), P.B_ndr, P.parZ_φ, if_pos (rfl : P.r = P.r),
      one_mul, P.φ_x, P.φ_nd]
    congr 1
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk' := Finset.ne_of_mem_erase hk
    rw [P.B_nd _ k hk', P.parZ_φ, if_neg hk', zero_mul, add_zero, P.φ_nd]
  have hAn : ∏ k, kfac P.NA Finset.univ s (P.nd k) =
      PMF.pure (z2b (P.parZ P.r (ev s))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r)]
    simp only [P.A_nd]
  rw [hR, P.B_x, P.A_x, hBu, hAu, hBn, hAn]
  by_cases hrest : ∀ k ∈ Finset.univ.erase P.r, ev s (P.nd k) = z2b (P.parZ k (ev s))
  · have hN : ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k hk => pure1 (hrest k hk))
    rw [hN]
    have hiff := P.eqr_iff (fun k => b2z (ev s (P.u k))) (fun k => b2z (ev s (P.nd k)))
      (fun k hk => (eq_z2b _ _).mp (hrest k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)))
    by_cases h0 : ev s (P.u 0) = P.Sb s
    · have he0 : ev s (P.nd P.r) = z2b (P.parZ P.r (ev s)) := by
        apply (eq_z2b _ _).mpr
        apply hiff.mpr
        show b2z (ev s (P.u 0)) = _
        rw [h0, Sb, b2z_z2b]
      have hxf : xor (ev s (P.u 0)) (P.Sb s) = false := by
        rw [h0]
        first | exact Bool.xor_self _ | simp
      rw [pure1 he0, pure1 hxf, z2b_add, ← he0, chan_mix, ← h0]
      ring
    · have he0 : ¬ ev s (P.nd P.r) = z2b (P.parZ P.r (ev s)) := by
        intro he
        apply h0
        apply b2z_inj
        rw [Sb, b2z_z2b]
        exact hiff.mp ((eq_z2b _ _).mp he)
      have hx0 : ¬ xor (ev s (P.u 0)) (P.Sb s) = false := fun hf => h0 (xb _ _ hf)
      rw [pure0 he0, pure0 hx0]
      simp
  · push_neg at hrest
    obtain ⟨k, hk, hi⟩ := hrest
    have hN : ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero hk (pure0 hi)
    rw [hN]
    simp

lemma full_map : P.mB.fullJoint = P.mA.fullJoint.map P.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (P.φ s)]
  · rw [if_pos (P.φ_invol s).symm, ← P.joint_BA (P.φ s), P.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, P.φ_invol]

lemma obsEq (O : Finset V) (hu : ∀ j, P.u j ∉ O) : P.mA.marginal O = P.mB.marginal O := by
  unfold CausalModel.marginal
  rw [P.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv0 : ∀ j, P.pth j = true → P.u j ≠ v := fun j _ e => hu j (by rw [e]; exact hv)
  first
    | exact (P.φ_o s hv0).symm
    | simp [Function.comp, Assignment.restrict, φ, hv0]

/-! ### Utregninger i C og B -/

lemma pOf {H : DAG V} {S : Finset V} (hS : ∀ v ∈ S, ∀ w, H.edge w v → w ∈ S)
    (v : V) (hv : v ∈ S) : H.parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

lemma ancC (S : Finset V) (hR : ∀ k, P.dp k = none → P.nd k ∈ S) (hu : ∀ j, P.u j ∉ S) :
    ∀ v ∈ S, ∀ a, P.gC.edge a v → a ∈ S := by
  intro v hv a ha
  rcases (P.eC a v).mp ha with ⟨k, hk, h1, _⟩ | ⟨k, j, _, h2⟩
  · rw [h1]
    exact hR k hk
  · exact absurd (by rw [← h2]; exact hv) (hu j)

lemma prodY (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hYS : ∀ v ∈ P.Y, v ∈ S) :
    ∏ v ∈ P.Y, kfac P.NC S a v = ∏ v ∈ P.Y, c2 := by
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hvS := hYS v hv
  obtain ⟨k, _, hk⟩ := P.mem_Y.mp hv
  have hvx : v ≠ P.x := by rw [← hk]; exact P.hndx k
  have hvu : ∀ j, P.u j ≠ v := by rw [← hk]; exact fun j => P.hund j k
  rw [BowGen.kfac_eqG _ S a v hvS (pOf hS v hvS), P.NC_o hvx hvu, PMF.uniformOfFintype_apply]

lemma Cx_val (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hxS : P.x ∈ S)
    (ha : ∀ k (hk : P.nd k ∈ S), b2z (a ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0) :
    kfac P.NC S a P.x = Bow.chan true (a ⟨P.x, hxS⟩) := by
  have hz : z2b (∑ k ∈ P.Rt, b2z (ext (a.restrict (pOf hS P.x hxS)) (P.nd k))) = true := by
    have hs : ∀ k ∈ P.Rt, b2z (ext (a.restrict (pOf hS P.x hxS)) (P.nd k)) =
        if k = P.r then 1 else 0 := by
      intro k hk
      have hp : P.nd k ∈ P.gC.parents P.x := P.pCx k (by simpa [Rt] using hk)
      have he : ext (a.restrict (pOf hS P.x hxS)) (P.nd k) = a ⟨P.nd k, pOf hS P.x hxS hp⟩ := by
        simp [MultiRoot.ext, hp, Assignment.restrict]
      rw [he]
      exact ha k (pOf hS P.x hxS hp)
    rw [Finset.sum_congr rfl hs]
    first
      | (rw [Finset.sum_ite_eq', if_pos P.mem_Rtr]; all_goals first | rfl | decide)
      | (simp [P.mem_Rtr]; all_goals first | rfl | decide)
  rw [BowGen.kfac_eqG _ S a P.x hxS (pOf hS P.x hxS), P.NC_x, hz]

lemma posA (O : Finset V) (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) :
    ∀ a, P.mA.marginal O a ≠ 0 := by
  intro a
  have hS := P.ancC O hY hu
  rw [P.margAC O, marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (pOf hS v hv)]
  have hvu : ∀ j, P.u j ≠ v := fun j e => hu j (by rw [e]; exact hv)
  by_cases hvx : v = P.x
  · subst hvx
    rw [P.NC_x]
    exact Bow.chan_ne_zero _ _
  · rw [P.NC_o hvx hvu]
    simp [PMF.uniformOfFintype_apply]

lemma doA (x0 : Assignment (α := fun _ : V => Bool) {P.x})
    (y0 : Assignment (α := fun _ : V => Bool) P.Y) :
    (doModel P.mA {P.x} x0).marginal P.Y y0 = P.mA.marginal P.Y y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel P.mA {P.x} x0) (doModel P.NA {P.x} x0)
    (BowGen.kfac_lift_doG P.hsA P.NA {P.x} x0) P.Y]
  have hanc : ∀ v ∈ (Finset.univ.image P.u ∪ Finset.univ.image P.nd), ∀ a, P.gA.edge a v →
      a ∈ (Finset.univ.image P.u ∪ Finset.univ.image P.nd) := by
    intro v hv a ha
    rcases (P.eA a v).mp ha with ⟨_, h2⟩ | ⟨k, h1, _⟩ | ⟨j, k, _, h1, _⟩ | ⟨j, k, _, h1, _⟩
    · exfalso
      rw [h2] at hv
      simp [P.hux', P.hndx] at hv
    · rw [h1]; simp
    · rw [h1]; simp
    · rw [h1]; simp
  have hdisj : Disjoint (Finset.univ.image P.u ∪ Finset.univ.image P.nd) {P.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [P.hux', P.hndx]
  have hYS : P.Y ⊆ Finset.univ.image P.u ∪ Finset.univ.image P.nd := by
    intro v hv
    obtain ⟨k, _, hk⟩ := P.mem_Y.mp hv
    rw [← hk]
    simp
  rw [Rule3.doModel_marginal_of_sub P.NA {P.x} x0 _ hanc hdisj P.Y hYS y0,
    ← Completeness.marginal_eq_of_kfac P.mA P.NA (BowGen.kfac_liftG P.hsA P.NA) P.Y]

/-- **Flere røtter: `P(R | do(x))` er ikke identifiserbar.** -/
theorem not_ident (O : Finset V) (hu : ∀ j, P.u j ∉ O)
    (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y := by
  intro h
  have hxY : P.x ∉ P.Y := by
    intro hm
    obtain ⟨k, _, hk⟩ := P.mem_Y.mp hm
    exact P.hndx k hk
  have hYX : Disjoint P.Y {P.x} := Finset.disjoint_singleton_right.mpr hxY
  have hnp : ∀ a, ¬ P.gB.edge a P.x := by
    intro a ha
    rcases (P.eB a P.x).mp ha with ⟨k, _, h2⟩ | ⟨j, k, _, _, h2⟩ | ⟨j, k, _, _, h2⟩ | ⟨_, h2⟩
    · exact P.hndx k h2.symm
    · exact P.hndx k h2.symm
    · exact P.hndx k h2.symm
    · exact P.hndx P.r h2.symm
  have hSx : ∀ v ∈ ({P.x} : Finset V), ∀ a, P.gB.edge a v → a ∈ ({P.x} : Finset V) := by
    intro v hv a ha
    rw [Finset.mem_singleton] at hv
    subst hv
    exact absurd ha (hnp a)
  have hOY : P.Y ∪ {P.x} ⊆ O := by
    intro v hv
    rcases Finset.mem_union.mp hv with h1 | h1
    · obtain ⟨k, hk, hk'⟩ := P.mem_Y.mp h1
      rw [← hk']
      exact hY k hk
    · rw [Finset.mem_singleton.mp h1]
      exact hx
  have huYx : ∀ j, P.u j ∉ P.Y ∪ {P.x} := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h1
    · obtain ⟨k, _, hk⟩ := P.mem_Y.mp h1
      exact P.hund j k hk.symm
    · exact P.hux' j (Finset.mem_singleton.mp h1)
  have huY : ∀ j, P.u j ∉ P.Y := fun j hj => huYx j (Finset.mem_union_left _ hj)
  have hC1 := P.ancC (P.Y ∪ {P.x})
    (fun k hk => Finset.mem_union_left _ (P.mem_Y.mpr ⟨k, hk, rfl⟩)) huYx
  have hC2 := P.ancC P.Y (fun k hk => P.mem_Y.mpr ⟨k, hk, rfl⟩) huY
  have hxS : P.x ∈ P.Y ∪ {P.x} := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have h2 : ∀ a : Assignment (α := fun _ : V => Bool) P.Y,
      P.NC.marginal P.Y a = ∏ v ∈ P.Y, c2 := by
    intro a
    rw [marginal_ancestral_apply _ _ hC2, P.prodY _ _ hC2 (fun v hv => hv)]
  have h3 : ∀ a : Assignment (α := fun _ : V => Bool) {P.x}, P.NB.marginal {P.x} a = c2 := by
    intro a
    rw [marginal_ancestral_apply _ {P.x} hSx, Finset.prod_singleton,
      BowGen.kfac_eqG _ {P.x} _ P.x (Finset.mem_singleton_self _)
        (pOf hSx P.x (Finset.mem_singleton_self _)),
      P.NB_o P.hndx (fun e => P.hux' 0 e.symm), PMF.uniformOfFintype_apply]
  have key : ∀ b : Bool, (∏ v ∈ P.Y, c2) * Bow.chan true b = (∏ v ∈ P.Y, c2) * c2 := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) (P.Y ∪ {P.x}) :=
      fun v => if v.1 = P.x then b else if v.1 = P.nd P.r then true else false
    have htx : t.restrict (show ({P.x} : Finset V) ⊆ P.Y ∪ {P.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = P.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hat : ∀ k (hk : P.nd k ∈ P.Y ∪ {P.x}), b2z (t ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0 := by
      intro k hk
      show b2z (if P.nd k = P.x then b else if P.nd k = P.nd P.r then true else false) = _
      rw [if_neg (P.hndx k)]
      by_cases h0 : k = P.r
      · subst h0
        simp [b2z]
      · rw [if_neg (fun e => h0 (P.ndinj e)), if_neg h0]
        all_goals first | rfl | decide | simp [b2z]
    have htxv : t ⟨P.x, hxS⟩ = b := by simp [t]
    have h1 : P.NC.marginal (P.Y ∪ {P.x}) t = (∏ v ∈ P.Y, c2) * Bow.chan true b := by
      rw [marginal_ancestral_apply _ _ hC1 t, Finset.prod_union hYX, Finset.prod_singleton,
        P.prodY _ t hC1 (fun v hv => Finset.mem_union_left _ hv), P.Cx_val _ t hC1 hxS hat, htxv]
    -- Identifiserbarheten
    have e := h P.mA P.mB (P.obsEq O hu) (P.posA O hu hY) t
    rw [htx, P.doA,
      Completeness.marginal_eq_of_kfac (doModel P.mB {P.x} _) (doModel P.NB {P.x} _)
        (BowGen.kfac_lift_doG P.hsB P.NB {P.x} _) P.Y] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 P.NB {P.x} P.Y hYX
      (Completeness.dsep_isolated hnp P.Y hxY) t
    rw [htx, ← e] at fd
    rw [show P.NB.marginal (P.Y ∪ {P.x}) = P.NC.marginal (P.Y ∪ {P.x}) from by
      rw [← Completeness.marginal_eq_of_kfac P.mB P.NB (BowGen.kfac_liftG P.hsB P.NB),
        ← marginal_eq_of_sub (P.obsEq O hu) hOY, margAC]] at fd
    rw [P.margAC, h1, h2, h3] at fd
    exact fd
  have k := (key true).trans (key false).symm
  have hQ0 : (∏ v ∈ P.Y, c2) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp [c2])
  have hQT : (∏ v ∈ P.Y, c2) ≠ ⊤ := by
    first
    | exact ENNReal.prod_ne_top (fun _ _ => by simp [c2])
    | (rw [Finset.prod_const]; exact ENNReal.pow_ne_top (by simp [c2]))
  have hc : Bow.chan true true = Bow.chan true false := by
    first
    | exact (ENNReal.mul_right_inj hQ0 hQT).mp k
    | exact (by
        have h1 := congrArg (fun z => (∏ v ∈ P.Y, c2)⁻¹ * z) k
        simp only [← mul_assoc, ENNReal.inv_mul_cancel hQ0 hQT, one_mul] at h1
        exact h1)
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (false = true) by decide)] at hc
  exact Bow.q_ne hc

end RP

/-- **Røtter langs en sti.** Som `multiRoot_not_identifiable`, men `x` peker inn i
en vilkårlig rot `nd_r`, og en sti av latente fra `u₀` til `u_r` er gitt. -/
theorem rootPath_not_identifiable {G : DAG V} {n : ℕ} (P : RP G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  P.not_ident O hu hY hx

/-- Runde 14 er spesialtilfellet `r = 0` med stien `{u₀}`. -/
theorem multiRoot_of_rootPath {G : DAG V} {n : ℕ} (P : MultiRoot.MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y := by
  have hpk : ∀ k, b2z (decide (k = 0)) +
      (∑ j, if P.bp j = some k then b2z (decide (j = 0)) else 0) = if k = 0 then 1 else 0 := by
    intro k
    have hz : (∑ j, if P.bp j = some k then b2z (decide (j = 0)) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : j = 0
      · subst hj
        rw [(P.hbp0 0).mpr rfl]
        simp
      · simp [hj, b2z]
    rw [hz, add_zero]
    by_cases hk : k = 0 <;> simp [hk, b2z]
  let Q : RP G n :=
    { x := P.x, nd := P.nd, u := P.u, bp := P.bp, ht := P.ht, dp := P.dp, r := 0,
      pth := fun k => decide (k = 0), hbp0 := P.hbp0, hht := P.hht, hr := P.hdp0,
      hp0 := by simp, hpk := hpk, hux := P.hux, hun := P.hun, hub := P.hub, hdp := P.hdp,
      hxr := P.hxr, ndinj := P.ndinj, uinj := P.uinj, hund := P.hund, hux' := P.hux',
      hndx := P.hndx }
  exact rootPath_not_identifiable Q O hu hY hx

end RootPath
end Identification

#print axioms Identification.RootPath.rootPath_not_identifiable
#print axioms Identification.RootPath.multiRoot_of_rootPath

/-! ### Runde 14 som korollar av runde 15 -/

namespace Identification
namespace MultiRoot

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **c-skog med flere røtter.** Et latent tre som binder `x` (gjennom `u₀`) til
nodene `nd₀, …, nd_{n+1}`, med `x → nd₀`, og et rettet skog-mønster blant nodene.
Er røttene og `x` observert og de latente uobservert, er `P(røtter | do(x))` ikke
identifiserbar. -/
theorem multiRoot_not_identifiable {G : DAG V} {n : ℕ} (P : MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  RootPath.multiRoot_of_rootPath P O hu hY hx

end MultiRoot
end Identification

#print axioms Identification.MultiRoot.multiRoot_not_identifiable

/-! ## Runde 16: stien finnes alltid

I runde 15 var stien av latente fra `u₀` til `u_r` en antakelse. Her konstrueres den:
`pth k` sier at `k` ligger på kjeden `r, bp r, bp (bp r), …`. Høyden vokser strengt
langs kjeden, så den er injektiv og ender i `0` (den eneste noden uten forelder).
Paritetsvilkåret følger: en node på kjeden (utenom `r`) har nøyaktig ett barn på
kjeden, `r` har ingen, og en node utenfor kjeden har ingen. -/

namespace Identification
namespace RootTree

open PathTree (b2z)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Konfigurasjonen fra runde 15, uten stien. -/
structure RT (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  r : Fin (n + 2)
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hr : dp r = none
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd r)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace RT

variable {G : DAG V} {n : ℕ} (T : RT G n)

/-- Røttene som noder. -/
def Y : Finset V := (Finset.univ.filter (fun k => T.dp k = none)).image T.nd

/-- Kjeden `r, bp r, bp (bp r), …` (til den går tom). -/
def chain : ℕ → Option (Fin (n + 2))
  | 0 => some T.r
  | m + 1 => (chain m).bind T.bp

lemma chain_succ (m : ℕ) : T.chain (m + 1) = (T.chain m).bind T.bp := rfl

/-- Langs kjeden vokser høyden minst med antall steg. -/
lemma chain_ht (m d : ℕ) {a b : Fin (n + 2)} (ha : T.chain m = some a)
    (hb : T.chain (m + d) = some b) : T.ht a + d ≤ T.ht b := by
  induction d generalizing b with
  | zero =>
    have e : a = b := Option.some.inj (ha.symm.trans hb)
    subst e
    omega
  | succ d ih =>
    rw [← Nat.add_assoc, T.chain_succ] at hb
    cases hc : T.chain (m + d) with
    | none =>
      rw [hc] at hb
      simp at hb
    | some c =>
      rw [hc] at hb
      change T.bp c = some b at hb
      have h1 := ih (b := c) hc
      have h2 := T.hht c b hb
      omega

lemma chain_le (m : ℕ) {a : Fin (n + 2)} (ha : T.chain m = some a) : m ≤ T.ht a := by
  have := T.chain_ht 0 m (a := T.r) (b := a) rfl (by simpa using ha)
  omega

/-- Kjeden besøker ingen node to ganger. -/
lemma chain_inj {m m' : ℕ} {a : Fin (n + 2)} (h : T.chain m = some a)
    (h' : T.chain m' = some a) : m = m' := by
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have := T.chain_ht m (d + 1) h (by rw [← Nat.add_assoc]; exact h')
    omega
  · exact heq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have := T.chain_ht m' (d + 1) h' (by rw [← Nat.add_assoc]; exact h)
    omega

lemma chain_some (m : ℕ) (h0 : ∀ m' ≤ m, T.chain m' ≠ some 0) :
    ∃ a, T.chain m = some a := by
  induction m with
  | zero => exact ⟨T.r, rfl⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih (fun m' hm' => h0 m' (by omega))
    have ha0 : a ≠ 0 := fun e => h0 m (by omega) (by rw [ha, e])
    cases hb : T.bp a with
    | none => exact absurd ((T.hbp0 a).mp hb) ha0
    | some b => exact ⟨b, by rw [T.chain_succ, ha]; exact hb⟩

/-- Kjeden når `0`. -/
lemma reach0 : ∃ m, T.chain m = some 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨a, ha⟩ := T.chain_some (Finset.univ.sup T.ht + 1) (fun m' _ => hc m')
  have h1 := T.chain_le _ ha
  have h2 : T.ht a ≤ Finset.univ.sup T.ht := Finset.le_sup (Finset.mem_univ a)
  omega

/-- **Stien:** `k` ligger på kjeden fra `r`. -/
noncomputable def pth (k : Fin (n + 2)) : Bool :=
  decide (∃ m ∈ Finset.range (Finset.univ.sup T.ht + 1), T.chain m = some k)

lemma pth_iff (k : Fin (n + 2)) : T.pth k = true ↔ ∃ m, T.chain m = some k := by
  unfold pth
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨m, _, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, Finset.mem_range.mpr ?_, hm⟩
    have h1 := T.chain_le m hm
    have h2 : T.ht k ≤ Finset.univ.sup T.ht := Finset.le_sup (Finset.mem_univ k)
    omega

/-- Forelderen til en node på kjeden ligger på kjeden, og er ikke `r`. -/
lemma child_on (j k : Fin (n + 2)) (hb : T.bp j = some k) (hj : T.pth j = true) :
    T.pth k = true ∧ k ≠ T.r := by
  obtain ⟨m, hm⟩ := (T.pth_iff j).mp hj
  have hk : T.chain (m + 1) = some k := by rw [T.chain_succ, hm]; exact hb
  refine ⟨(T.pth_iff k).mpr ⟨m + 1, hk⟩, fun e => ?_⟩
  rw [e] at hk
  have := T.chain_inj hk (rfl : T.chain 0 = some T.r)
  omega

/-- Antall barn på kjeden: ett for en kjedenode utenom `r`, ellers null. -/
lemma sum_children (k : Fin (n + 2)) :
    (∑ j, if T.bp j = some k then b2z (T.pth j) else 0) =
      if T.pth k = true ∧ k ≠ T.r then 1 else 0 := by
  by_cases hk : T.pth k = true ∧ k ≠ T.r
  · rw [if_pos hk]
    obtain ⟨m', hm'⟩ := (T.pth_iff k).mp hk.1
    cases m' with
    | zero => exact absurd (Option.some.inj hm').symm hk.2
    | succ m =>
      rw [T.chain_succ] at hm'
      cases hc : T.chain m with
      | none =>
        rw [hc] at hm'
        simp at hm'
      | some j0 =>
        rw [hc] at hm'
        change T.bp j0 = some k at hm'
        rw [Finset.sum_eq_single j0]
        · rw [if_pos hm', (T.pth_iff j0).mpr ⟨m, hc⟩]
          all_goals first | rfl | decide | simp [b2z]
        · intro j _ hj
          split_ifs with hb
          · cases hjp : T.pth j
            · rfl
            · exfalso
              obtain ⟨m2, hm2⟩ := (T.pth_iff j).mp hjp
              have e1 : T.chain (m2 + 1) = some k := by rw [T.chain_succ, hm2]; exact hb
              have e2 : T.chain (m + 1) = some k := by rw [T.chain_succ, hc]; exact hm'
              have e3 : m2 = m := by have := T.chain_inj e1 e2; omega
              rw [e3, hc] at hm2
              exact hj (Option.some.inj hm2).symm
          · rfl
        · intro h
          exact absurd (Finset.mem_univ j0) h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with hb
    · cases hjp : T.pth j
      · rfl
      · exact absurd (T.child_on j k hb hjp) hk
    · rfl

/-- **Paritetsvilkåret fra runde 15 holder.** -/
lemma hpk (k : Fin (n + 2)) :
    b2z (T.pth k) + (∑ j, if T.bp j = some k then b2z (T.pth j) else 0) =
      if k = T.r then 1 else 0 := by
  rw [T.sum_children]
  by_cases hkr : k = T.r
  · subst hkr
    have hr : T.pth T.r = true := (T.pth_iff _).mpr ⟨0, rfl⟩
    simp [hr, b2z]
  · rw [if_neg hkr]
    cases hp : T.pth k
    · rw [if_neg (fun h => Bool.false_ne_true h.1)]
      all_goals first | rfl | decide | simp [b2z]
    · rw [if_pos ⟨rfl, hkr⟩]
      all_goals first | rfl | decide | simp [b2z]

/-- Konfigurasjonen med den konstruerte stien. -/
noncomputable def toRP : RootPath.RP G n where
  x := T.x
  nd := T.nd
  u := T.u
  bp := T.bp
  ht := T.ht
  dp := T.dp
  r := T.r
  pth := T.pth
  hbp0 := T.hbp0
  hht := T.hht
  hr := T.hr
  hp0 := (T.pth_iff 0).mpr T.reach0
  hpk := T.hpk
  hux := T.hux
  hun := T.hun
  hub := T.hub
  hdp := T.hdp
  hxr := T.hxr
  ndinj := T.ndinj
  uinj := T.uinj
  hund := T.hund
  hux' := T.hux'
  hndx := T.hndx

end RT

/-- **c-skoger med flere røtter, uten stiantakelse.** Et latent tre som binder `x`
(gjennom `u₀`) til nodene, et rettet skog-mønster blant nodene, og `x → nd_r` for en
rot `r`. Er røttene og `x` observert og de latente ikke, er `P(røtter | do(x))` ikke
identifiserbar. -/
theorem rootTree_not_identifiable {G : DAG V} {n : ℕ} (T : RT G n) (O : Finset V)
    (hu : ∀ j, T.u j ∉ O) (hY : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} T.Y :=
  RootPath.rootPath_not_identifiable T.toRP O hu hY hx

end RootTree
end Identification

#print axioms Identification.RootTree.rootTree_not_identifiable

/-! ## Runde 17: innebygde hedger

En `RT`-struktur trenger bare å finnes *inne i* `G`: grafen kan ha flere kanter,
flere latente og flere noder enn strukturen bruker, og `Y` kan være større enn
røttene. Modellene ignorerer det overflødige (kjernene leser bare sine egne foreldre),
og `Identifiable.mono_Y` (runde 11) løfter resultatet fra røttene til `Y`.

Særlig dekker dette `x` med flere latente naboer. Er `x` et indre punkt i det latente
treet, er `F ∖ {x}` usammenhengende, så `(F, F ∖ {x})` er ingen hedge. Den riktige
hedgen er grenen som inneholder `nd_r`, med `x` som blad; den er en `RT`-struktur
inne i `G`. Det samme gjelder sykler blant de latente: velg et utspennende tre der
`x` er et blad. -/

namespace Identification
namespace RootTree

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Innebygd hedge.** Finnes en `RT`-struktur i `G` med røtter i `Y`, er
`P(Y | do(x))` ikke identifiserbar. -/
theorem embedded_not_identifiable {G : DAG V} {n : ℕ} (T : RT G n) (O Y : Finset V)
    (hu : ∀ j, T.u j ∉ O) (hR : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O)
    (hTY : T.Y ⊆ Y) (hd : Disjoint Y {T.x}) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} Y :=
  fun h => rootTree_not_identifiable T O hu hR hx (h.mono_Y hd hTY)

end RootTree
end Identification

#print axioms Identification.RootTree.embedded_not_identifiable

/-! ## Runde 18: kanalsteget

Shpitser og Pearl krever bare at røttene i en hedge er *forfedre* til `Y`. Dette
steget fører en ikke-identifiserbar effekt ett ledd videre langs en rettet kant
`ρ → y`: står `y` isolert i en delgraf `G'` der effekten på `Y ∋ ρ` ikke er
identifiserbar, så er effekten på `Y ∖ {ρ} ∪ {y}` ikke identifiserbar i `G`, når
`y` observeres gjennom en støyende kanal fra `ρ`.

* Modellene fra `G'` beholdes, og `y` får kjernen `chan(ρ)`. Siden ingen leser `y`,
  er fellesfordelingen den gamle marginalen uten `y`, utvidet med kanalen
  (`joint_ins`). Marginalene får samme form (`marg_ins`).
* Like observasjoner og positivitet går derfor rett over.
* Kanalen er inverterbar: fra fordelingen på `(Y ∖ {ρ}, y)` kan fordelingen på `Y`
  regnes tilbake (`Φ_inj`, et 2 × 2-likningssystem). Like svar etter steget gir
  like svar før steget, i strid med antakelsen. -/

namespace Identification
namespace Channel

open HedgeChain (ev)
open MultiRoot (ext ext_restrict)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Å utvide en tilordning med én node -/

/-- `b` på `T`, utvidet med verdien `c` i `w`, som tilordning på `U ⊆ insert w T`. -/
def ins (w : V) {T U : Finset V} (hU : U ⊆ insert w T)
    (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    Assignment (α := fun _ : V => Bool) U :=
  fun v => if h : v.1 = w then c else b ⟨v.1, (Finset.mem_insert.mp (hU v.2)).resolve_left h⟩

lemma ins_eq_iff (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool)
    (s : Assignment (α := fun _ : V => Bool) U) :
    ins w hU b c = s ↔ b = s.restrict hTU ∧ c = s ⟨w, hw⟩ := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      have hvw : v ≠ w := fun e => hwT (e ▸ hv)
      simp [ins, Assignment.restrict, hvw]
    · simp [ins]
  · rintro ⟨rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases h : v = w
    · subst h
      simp [ins]
    · simp [ins, Assignment.restrict, h]

lemma ins_restrict (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (s : Assignment (α := fun _ : V => Bool) U) :
    ins w hU (s.restrict hTU) (s ⟨w, hw⟩) = s :=
  (ins_eq_iff w hU hTU hw hwT _ _ s).mpr ⟨rfl, rfl⟩

lemma ins_restrict_T (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    (ins w hU b c).restrict hTU = b :=
  ((ins_eq_iff w hU hTU hw hwT b c _).mp rfl).1.symm

lemma ins_at (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hw : w ∈ U)
    (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) : (ins w hU b c) ⟨w, hw⟩ = c := by
  simp [ins]

lemma ins_inj (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) {b b' : Assignment (α := fun _ : V => Bool) T} {c c' : Bool}
    (h : ins w hU b c = ins w hU b' c') : b = b' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := (ins_eq_iff w hU hTU hw hwT b c _).mp h
  rw [ins_restrict_T w hU hTU hw hwT] at h1
  rw [ins_at w hU hw] at h2
  exact ⟨h1, h2⟩

lemma restrict_ins (w : V) {T U T' U' : Finset V} (hU : U ⊆ insert w T) (hU' : U' ⊆ insert w T')
    (hUU : U' ⊆ U) (hT : T' ⊆ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    (ins w hU b c).restrict hUU = ins w hU' (b.restrict hT) c := by
  funext ⟨v, hv⟩
  by_cases h : v = w
  · subst h
    simp [ins, Assignment.restrict]
  · simp [ins, Assignment.restrict, h]

/-- Summen over tilordninger av formen `ins w b c` faller sammen til ett ledd. -/
lemma tsum_ins (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (f : Assignment (α := fun _ : V => Bool) T → Bool → ℝ≥0∞)
    (s : Assignment (α := fun _ : V => Bool) U) :
    (∑' b, ∑' c, if s = ins w hU b c then f b c else 0) = f (s.restrict hTU) (s ⟨w, hw⟩) := by
  have key : ∀ b c, s = ins w hU b c ↔ b = s.restrict hTU ∧ c = s ⟨w, hw⟩ := fun b c =>
    eq_comm.trans (ins_eq_iff w hU hTU hw hwT b c s)
  rw [tsum_eq_single (s.restrict hTU)]
  · rw [tsum_eq_single (s ⟨w, hw⟩)]
    · rw [if_pos ((key _ _).mpr ⟨rfl, rfl⟩)]
    · intro c hc
      rw [if_neg (fun h => hc ((key _ _).mp h).2)]
  · intro b hb
    exact ENNReal.tsum_eq_zero.mpr (fun c => if_neg (fun h => hb ((key _ _).mp h).1))

/-- Bytte av summasjonsvariabel: en tilordning på `U` er det samme som en på `T`
pluss en verdi i `w`. -/
lemma tsum_reindex (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (g : Assignment (α := fun _ : V => Bool) U → ℝ≥0∞) :
    (∑' s, g s) = ∑' b, ∑' c, g (ins w hU b c) := by
  calc (∑' s, g s) = ∑' s, ∑' b, ∑' c, (if s = ins w hU b c then g (ins w hU b c) else 0) := by
        refine tsum_congr (fun s => ?_)
        rw [tsum_ins w hU hTU hw hwT (fun b c => g (ins w hU b c)) s]
        exact (congrArg g (ins_restrict w hU hTU hw hwT s)).symm
    _ = ∑' b, ∑' c, ∑' s, (if s = ins w hU b c then g (ins w hU b c) else 0) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr (fun b => ?_)
        rw [ENNReal.tsum_comm]
    _ = ∑' b, ∑' c, g (ins w hU b c) := by
        refine tsum_congr (fun b => tsum_congr (fun c => ?_))
        rw [tsum_eq_single (ins w hU b c)]
        · first | rw [if_pos rfl] | simp
        · intro s hs
          rw [if_neg hs]

/-! ### Et blad med kanal -/

/-- Alle noder unntatt `y`. -/
abbrev Ay (y : V) : Finset V := Finset.univ.erase y

lemma memA {ρ y : V} (h : ρ ≠ y) : ρ ∈ Ay y := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩

lemma univ_sub (y : V) : (Finset.univ : Finset V) ⊆ insert y (Ay y) := by
  intro v _
  by_cases h : v = y
  · rw [h]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (memA h)

lemma notA (y : V) : y ∉ Ay y := fun h => (Finset.mem_erase.mp h).1 rfl

lemma parOfA {H : DAG V} {S : Finset V} (hS : ∀ v ∈ S, ∀ w, H.edge w v → w ∈ S)
    (v : V) (hv : v ∈ S) : H.parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

section Leaf

variable {H H1 : DAG V} (K : H.CausalModel (fun _ => Bool)) (K1 : H1.CausalModel (fun _ => Bool))

/-- **Fellesfordelingen med bladet.** Leser ingen `y`, og har `y` kjernen `chan(ρ)`,
er fellesfordelingen marginalen uten `y`, utvidet med kanalen. -/
lemma joint_ins {ρ y : V} (hρy : ρ ≠ y)
    (hanc : ∀ v ∈ Ay y, ∀ a, H.edge a v → a ∈ Ay y)
    (hoff : ∀ s v, v ≠ y → kfac K1 Finset.univ s v = kfac K Finset.univ s v)
    (hyk : ∀ s, kfac K1 Finset.univ s y = Bow.chan (ev s ρ) (ev s y)) :
    K1.fullJoint = (K.marginal (Ay y)).bind (fun b =>
      (Bow.chan (b ⟨ρ, memA hρy⟩)).map (ins y (univ_sub y) b)) := by
  ext s
  rw [fullJoint_apply_prod, PMF.bind_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ y), hyk]
  have hp : ∏ v ∈ Ay y, kfac K1 Finset.univ s v =
      K.marginal (Ay y) (s.restrict (Finset.subset_univ _)) := by
    rw [marginal_ancestral_apply K (Ay y) hanc]
    refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [hoff s v (Finset.mem_erase.mp hv).1,
      kfac_restrict K (Finset.subset_univ _) s hv (parOfA hanc v hv)]
  rw [hp]
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_ins y (univ_sub y) (Finset.subset_univ _) (Finset.mem_univ y) (notA y)
    (fun b c => K.marginal (Ay y) b * Bow.chan (b ⟨ρ, memA hρy⟩) c) s]
  exact mul_comm _ _

/-- **Marginalene med bladet.** For `ρ ∈ S` og `y ∉ S`. -/
lemma marg_ins {ρ y : V} (hρy : ρ ≠ y)
    (hanc : ∀ v ∈ Ay y, ∀ a, H.edge a v → a ∈ Ay y)
    (hoff : ∀ s v, v ≠ y → kfac K1 Finset.univ s v = kfac K Finset.univ s v)
    (hyk : ∀ s, kfac K1 Finset.univ s y = Bow.chan (ev s ρ) (ev s y))
    (S : Finset V) (hρS : ρ ∈ S) (hyS : y ∉ S) :
    K1.marginal (insert y S) = (K.marginal S).bind (fun a =>
      (Bow.chan (a ⟨ρ, hρS⟩)).map (ins y (Finset.Subset.refl (insert y S)) a)) := by
  have hSA : S ⊆ Ay y := fun v hv =>
    Finset.mem_erase.mpr ⟨fun e => hyS (e ▸ hv), Finset.mem_univ _⟩
  show K1.fullJoint.map (Assignment.restrict (Finset.subset_univ _)) = _
  rw [joint_ins K K1 hρy hanc hoff hyk, PMF.map_bind]
  have hcomp : ∀ b : Assignment (α := fun _ : V => Bool) (Ay y),
      ((Bow.chan (b ⟨ρ, memA hρy⟩)).map (ins y (univ_sub y) b)).map
          (Assignment.restrict (Finset.subset_univ (insert y S))) =
        (Bow.chan ((b.restrict hSA) ⟨ρ, hρS⟩)).map
          (ins y (Finset.Subset.refl (insert y S)) (b.restrict hSA)) := by
    intro b
    rw [PMF.map_comp]
    congr 1
    all_goals (funext c; exact restrict_ins y (univ_sub y) (Finset.Subset.refl _) (Finset.subset_univ _) hSA b c)
  simp only [hcomp]
  rw [← marginal_restrict K hSA, PMF.bind_map]
  all_goals rfl

end Leaf

/-- Verdien av utvidelsen i ett punkt. -/
lemma bind_ins_apply {ρ y : V} {S : Finset V} (hρS : ρ ∈ S) (hyS : y ∉ S)
    (P : PMF (Assignment (α := fun _ : V => Bool) S))
    (s : Assignment (α := fun _ : V => Bool) (insert y S)) :
    (P.bind (fun a => (Bow.chan (a ⟨ρ, hρS⟩)).map (ins y (Finset.Subset.refl (insert y S)) a))) s =
      P (s.restrict (Finset.subset_insert y S)) *
        Bow.chan (s ⟨ρ, Finset.mem_insert_of_mem hρS⟩) (s ⟨y, Finset.mem_insert_self y S⟩) := by
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_ins y (Finset.Subset.refl _) (Finset.subset_insert y S) (Finset.mem_insert_self y S)
    hyS (fun a c => P a * Bow.chan (a ⟨ρ, hρS⟩) c) s]
  all_goals rfl

/-! ### Kanalen er inverterbar -/

/-- Fordelingen på `Y` sendt gjennom kanalen `ρ ↦ y`, med `ρ` summert ut. -/
noncomputable def Φ {ρ : V} {Y : Finset V} (hρY : ρ ∈ Y) (y : V)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y)) :
    PMF (Assignment (α := fun _ : V => Bool) (insert y (Y.erase ρ))) :=
  P.bind (fun a => (Bow.chan (a ⟨ρ, hρY⟩)).map
    (ins y (Finset.Subset.refl _) (a.restrict (Finset.erase_subset ρ Y))))

lemma hYW {ρ : V} {Y : Finset V} (hρY : ρ ∈ Y) : Y ⊆ insert ρ (Y.erase ρ) := fun v hv => by
  rw [Finset.insert_erase hρY]
  exact hv

lemma hρW (ρ : V) (Y : Finset V) : ρ ∉ Y.erase ρ := fun h => (Finset.mem_erase.mp h).1 rfl

lemma map_bind_ins {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y)) :
    (P.bind (fun a => (Bow.chan (a ⟨ρ, hρY⟩)).map (ins y (Finset.Subset.refl (insert y Y)) a))).map
        (Assignment.restrict (Finset.insert_subset_insert y (Finset.erase_subset ρ Y))) =
      Φ hρY y P := by
  rw [PMF.map_bind]
  unfold Φ
  congr 1
  funext a
  rw [PMF.map_comp]
  congr 1
  all_goals (funext c; exact restrict_ins y (Finset.Subset.refl _) (Finset.Subset.refl _) _ (Finset.erase_subset ρ Y) a c)

lemma Φ_apply {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y) (hyY : y ∉ Y)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y))
    (w : Assignment (α := fun _ : V => Bool) (Y.erase ρ)) (c : Bool) :
    Φ hρY y P (ins y (Finset.Subset.refl _) w c) =
      P (ins ρ (hYW hρY) w false) * Bow.chan false c +
        P (ins ρ (hYW hρY) w true) * Bow.chan true c := by
  have hyW : y ∉ Y.erase ρ := fun h => hyY (Finset.mem_of_mem_erase h)
  have inner : ∀ a : Assignment (α := fun _ : V => Bool) Y,
      (∑' d, if ins y (Finset.Subset.refl _) w c =
          ins y (Finset.Subset.refl _) (a.restrict (Finset.erase_subset ρ Y)) d
        then Bow.chan (a ⟨ρ, hρY⟩) d else 0) =
      if w = a.restrict (Finset.erase_subset ρ Y) then Bow.chan (a ⟨ρ, hρY⟩) c else 0 := by
    intro a
    rw [tsum_eq_single c]
    · by_cases hw : w = a.restrict (Finset.erase_subset ρ Y)
      · subst hw
        first | rw [if_pos rfl, if_pos rfl] | simp
      · rw [if_neg (fun e => hw (ins_inj y (Finset.Subset.refl _) (Finset.subset_insert y _)
          (Finset.mem_insert_self y _) hyW e).1), if_neg hw]
    · intro d hd
      exact if_neg (fun e => hd (ins_inj y (Finset.Subset.refl _) (Finset.subset_insert y _)
        (Finset.mem_insert_self y _) hyW e).2.symm)
  unfold Φ
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, inner]
  rw [tsum_reindex ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y)]
  simp only [ins_restrict_T ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y),
    ins_at ρ (hYW hρY) hρY]
  rw [tsum_eq_single w]
  · have hs : ∀ r : Bool, (P (ins ρ (hYW hρY) w r) * if w = w then Bow.chan r c else 0) =
        P (ins ρ (hYW hρY) w r) * Bow.chan r c := fun r => by first | rw [if_pos rfl] | simp
    simp only [hs]
    rw [tsum_fintype, Fintype.sum_bool]
    simp
    exact add_comm _ _
  · intro w' hw'
    exact ENNReal.tsum_eq_zero.mpr (fun r => by rw [if_neg (Ne.symm hw'), mul_zero])

/-- To likninger med kanalens koeffisienter bestemmer de to ukjente. -/
lemma lin2 {p q p' q' : ℝ≥0∞} (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp' : p' ≠ ⊤) (hq' : q' ≠ ⊤)
    (h1 : p * (3 / 4) + q * (1 / 4) = p' * (3 / 4) + q' * (1 / 4))
    (h2 : p * (1 / 4) + q * (3 / 4) = p' * (1 / 4) + q' * (3 / 4)) : p = p' ∧ q = q' := by
  have k1 : (1 / 4 : ℝ≥0∞) ≠ ⊤ := by
    first | exact ENNReal.div_ne_top (by simp) (by simp) | simp | norm_num
  have k3 : (3 / 4 : ℝ≥0∞) ≠ ⊤ := by
    first | exact ENNReal.div_ne_top (by simp) (by simp) | simp | norm_num
  have r1 : (1 / 4 : ℝ≥0∞).toReal = 1 / 4 := by
    first | norm_num [ENNReal.toReal_div] | simp [ENNReal.toReal_div]
  have r3 : (3 / 4 : ℝ≥0∞).toReal = 3 / 4 := by
    first | norm_num [ENNReal.toReal_div] | simp [ENNReal.toReal_div]
  have e1 := congrArg ENNReal.toReal h1
  have e2 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp k3) (ENNReal.mul_ne_top hq k1),
    ENNReal.toReal_add (ENNReal.mul_ne_top hp' k3) (ENNReal.mul_ne_top hq' k1),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, r1, r3] at e1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp k1) (ENNReal.mul_ne_top hq k3),
    ENNReal.toReal_add (ENNReal.mul_ne_top hp' k1) (ENNReal.mul_ne_top hq' k3),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, r1, r3] at e2
  have ep : p.toReal = p'.toReal := by linarith
  have eq : q.toReal = q'.toReal := by linarith
  constructor
  · first
    | exact (ENNReal.toReal_eq_toReal hp hp').mp ep
    | exact (ENNReal.toReal_eq_toReal_iff' hp hp').mp ep
  · first
    | exact (ENNReal.toReal_eq_toReal hq hq').mp eq
    | exact (ENNReal.toReal_eq_toReal_iff' hq hq').mp eq

/-- **Kanalen er inverterbar.** -/
lemma Φ_inj {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y) (hyY : y ∉ Y)
    (P1 P2 : PMF (Assignment (α := fun _ : V => Bool) Y)) (h : Φ hρY y P1 = Φ hρY y P2) :
    P1 = P2 := by
  ext a
  have key : ∀ c, P1 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) false) * Bow.chan false c +
      P1 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) true) * Bow.chan true c =
      P2 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) false) * Bow.chan false c +
      P2 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) true) * Bow.chan true c :=
    fun c => by rw [← Φ_apply hρY hyY, ← Φ_apply hρY hyY, h]
  have k0 := key false
  have k1 := key true
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show false = false from rfl),
    if_neg (show ¬ (false = true) by decide)] at k0
  rw [Bow.chan_apply, Bow.chan_apply, if_neg (show ¬ (true = false) by decide),
    if_pos (show true = true from rfl)] at k1
  have hl := lin2 (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _) k0 k1
  have ha := (ins_restrict ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y) a).symm
  rw [ha]
  cases hr : a ⟨ρ, hρY⟩
  · exact hl.1
  · exact hl.2

/-! ### Grafen og modellene -/

/-- Ett kanalsteg: `y` står isolert i `G'`, og `ρ → y` er en kant i `G`. -/
structure Step (G' G : DAG V) where
  ρ : V
  y : V
  hsub : ∀ a b, G'.edge a b → G.edge a b
  hρy : G.edge ρ y
  hiso : ∀ a, ¬ G'.edge a y ∧ ¬ G'.edge y a

namespace Step

variable {G' G : DAG V} (D : Step G' G)

lemma hne : D.ρ ≠ D.y := BowGen.ne_of_edge D.hρy

/-- `G'` med kanten `ρ → y`; rangen lånes fra `G`. -/
noncomputable def G1 : DAG V where
  edge a b := G'.edge a b ∨ (a = D.ρ ∧ b = D.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with h | ⟨h1, h2⟩
    · exact G.rank_strict_mono _ _ (D.hsub _ _ h)
    · rw [h1, h2]
      exact G.rank_strict_mono _ _ D.hρy

lemma edge1 {a b : V} : D.G1.edge a b ↔ G'.edge a b ∨ (a = D.ρ ∧ b = D.y) := Iff.rfl

lemma par1 {a v : V} : a ∈ D.G1.parents v ↔ D.G1.edge a v := by simp [DAG.parents]

lemma par'_sub {u v : V} (h : u ∈ G'.parents v) : u ∈ D.G1.parents v :=
  D.par1.mpr (D.edge1.mpr (Or.inl (by simpa [DAG.parents] using h)))

lemma sub1 : ∀ v, D.G1.parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (D.edge1.mp (D.par1.mp ha)) with h | ⟨h1, h2⟩
  · exact D.hsub _ _ h
  · rw [h1, h2]
    exact D.hρy

lemma hρpar : D.ρ ∈ D.G1.parents D.y := D.par1.mpr (D.edge1.mpr (Or.inr ⟨rfl, rfl⟩))

/-- Den gamle modellen, med kanalen `chan(ρ)` i `y`. -/
noncomputable def N (M : G'.CausalModel (fun _ => Bool)) : D.G1.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa => if v = D.y then Bow.chan (ext pa D.ρ)
    else M.kernel v (fun u => pa ⟨u.1, D.par'_sub u.2⟩)

lemma N_y (M : G'.CausalModel (fun _ => Bool))
    (pa : Assignment (α := fun _ : V => Bool) (D.G1.parents D.y)) :
    (D.N M).kernel D.y pa = Bow.chan (ext pa D.ρ) := by
  simp [N]

lemma N_o (M : G'.CausalModel (fun _ => Bool)) {v : V} (hv : v ≠ D.y)
    (pa : Assignment (α := fun _ : V => Bool) (D.G1.parents v)) :
    (D.N M).kernel v pa = M.kernel v (fun u => pa ⟨u.1, D.par'_sub u.2⟩) := by
  simp [N, hv]

lemma ancG' : ∀ v ∈ Ay D.y, ∀ a, G'.edge a v → a ∈ Ay D.y := by
  intro v _ a ha
  exact Finset.mem_erase.mpr ⟨fun e => (D.hiso v).2 (e ▸ ha), Finset.mem_univ _⟩

lemma ancCut (X : Finset V) : ∀ v ∈ Ay D.y, ∀ a, (cutIn G' X).edge a v → a ∈ Ay D.y :=
  fun v hv a ha => D.ancG' v hv a (show G'.edge a v ∧ v ∉ X from ha).1

lemma hoff (M : G'.CausalModel (fun _ => Bool)) :
    ∀ s v, v ≠ D.y → kfac (D.N M) Finset.univ s v = kfac M Finset.univ s v := by
  intro s v hv
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ, D.N_o M hv]
  all_goals rfl

lemma hyk (M : G'.CausalModel (fun _ => Bool)) :
    ∀ s, kfac (D.N M) Finset.univ s D.y = Bow.chan (ev s D.ρ) (ev s D.y) := by
  intro s
  rw [DoAudit.kfac_univ, D.N_y M, ext_restrict s D.hρpar]
  all_goals rfl

lemma hoff_do (M : G'.CausalModel (fun _ => Bool)) (X : Finset V)
    (x0 : Assignment (α := fun _ : V => Bool) X) :
    ∀ s v, v ≠ D.y → kfac (doModel (D.N M) X x0) Finset.univ s v =
      kfac (doModel M X x0) Finset.univ s v := by
  intro s v hv
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hvX : v ∈ X
  · simp only [doModel, dif_pos hvX]
  · simp only [doModel, dif_neg hvX]
    rw [D.N_o M hv]
    all_goals rfl

lemma hyk_do (M : G'.CausalModel (fun _ => Bool)) (X : Finset V) (hyX : D.y ∉ X)
    (x0 : Assignment (α := fun _ : V => Bool) X) :
    ∀ s, kfac (doModel (D.N M) X x0) Finset.univ s D.y = Bow.chan (ev s D.ρ) (ev s D.y) := by
  intro s
  rw [DoAudit.kfac_univ]
  simp only [doModel, dif_neg hyX]
  rw [D.N_y M]
  first
    | simp [MultiRoot.ext, D.hρpar, Assignment.restrict, ev]
    | (simp only [MultiRoot.ext, dif_pos D.hρpar]; rfl)

end Step

/-! ### Kanalsteget -/

/-- **Kanalsteget.** Er effekten på `Y ∋ ρ` ikke identifiserbar i `G'`, der `y` står
isolert, så er effekten på `Y ∖ {ρ} ∪ {y}` ikke identifiserbar i `G`, med `y` observert. -/
theorem channel_step {G' G : DAG V} (D : Step G' G) {O X Y : Finset V}
    (hρO : D.ρ ∈ O) (hyO : D.y ∉ O) (hρY : D.ρ ∈ Y) (hyY : D.y ∉ Y) (hyX : D.y ∉ X)
    (hYX : Disjoint Y X) (h : ¬ Identifiable G' (fun _ => Bool) O X Y) :
    ¬ Identifiable G (fun _ => Bool) (insert D.y O) X (insert D.y (Y.erase D.ρ)) := by
  intro hI
  apply h
  intro M1 M2 hM hpos t
  -- Observasjonene
  have hL : ∀ M : G'.CausalModel (fun _ => Bool),
      (Completeness.liftSub D.sub1 (D.N M)).marginal (insert D.y O) =
        (M.marginal O).bind (fun a =>
          (Bow.chan (a ⟨D.ρ, hρO⟩)).map (ins D.y (Finset.Subset.refl (insert D.y O)) a)) := by
    intro M
    rw [Completeness.marginal_eq_of_kfac _ (D.N M) (BowGen.kfac_liftG D.sub1 (D.N M))
      (insert D.y O)]
    exact marg_ins M (D.N M) D.hne D.ancG' (D.hoff M) (D.hyk M) O hρO hyO
  have hobs : (Completeness.liftSub D.sub1 (D.N M1)).marginal (insert D.y O) =
      (Completeness.liftSub D.sub1 (D.N M2)).marginal (insert D.y O) := by
    rw [hL M1, hL M2, hM]
  have hpos' : ∀ a, (Completeness.liftSub D.sub1 (D.N M1)).marginal (insert D.y O) a ≠ 0 := by
    intro a
    rw [hL M1, bind_ins_apply hρO hyO]
    exact mul_ne_zero (hpos _) (Bow.chan_ne_zero _ _)
  -- Intervensjonene
  have hd' : Disjoint (insert D.y (Y.erase D.ρ)) X := by
    rw [Finset.disjoint_insert_left]
    exact ⟨hyX, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYX⟩
  have hdo : ∀ x0 : Assignment (α := fun _ : V => Bool) X,
      (doModel (Completeness.liftSub D.sub1 (D.N M1)) X x0).marginal (insert D.y (Y.erase D.ρ)) =
        (doModel (Completeness.liftSub D.sub1 (D.N M2)) X x0).marginal
          (insert D.y (Y.erase D.ρ)) := by
    intro x0
    ext a
    have e := hI _ _ hobs hpos' (joinYX a x0)
    rw [joinYX_X hd', joinYX_Y] at e
    exact e
  have hT : ∀ (M : G'.CausalModel (fun _ => Bool)) (x0 : Assignment (α := fun _ : V => Bool) X),
      (doModel (Completeness.liftSub D.sub1 (D.N M)) X x0).marginal (insert D.y (Y.erase D.ρ)) =
        Φ hρY D.y ((doModel M X x0).marginal Y) := by
    intro M x0
    rw [Completeness.marginal_eq_of_kfac _ (doModel (D.N M) X x0)
        (BowGen.kfac_lift_doG D.sub1 (D.N M) X x0) _,
      ← marginal_restrict (doModel (D.N M) X x0)
        (Finset.insert_subset_insert D.y (Finset.erase_subset D.ρ Y)),
      marg_ins (doModel M X x0) (doModel (D.N M) X x0) D.hne (D.ancCut X) (D.hoff_do M X x0)
        (D.hyk_do M X hyX x0) Y hρY hyY]
    exact map_bind_ins hρY _
  have hx := hdo (t.restrict (show X ⊆ Y ∪ X by intro v hv; simp only [Finset.mem_union]; tauto))
  rw [hT M1, hT M2] at hx
  have e := Φ_inj hρY hyY _ _ hx
  exact congrArg (fun P : PMF (Assignment (α := fun _ : V => Bool) Y) =>
    P (t.restrict (show Y ⊆ Y ∪ X by intro v hv; simp only [Finset.mem_union]; tauto))) e

end Channel
end Identification

#print axioms Identification.Channel.channel_step

/-! ## Runde 19: en hel sti

Kanalsteget fra runde 18 gjentas langs en rettet sti `ρ → p₁ → … → p_m`. Før stien
legges på, står stinodene isolert (`isoSet`). Hvert steg legger på én kant, og til slutt
løftes resultatet til hele `G` (`not_ident_of_sub`: flere kanter gjør aldri en effekt
identifiserbar). Resultat: `ρ` i `Y` kan byttes ut med stiens endepunkt.

Flere disjunkte stier fra ulike røtter håndteres ved å bruke teoremet én gang per sti,
med grafen der de andre stiene ennå er isolert. Stier som møtes, er ikke dekket. -/

namespace Identification
namespace Channel

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Flere kanter skader aldri.** Er effekten ikke identifiserbar i en delgraf, er den
heller ikke identifiserbar i hele grafen. -/
theorem not_ident_of_sub {H G : DAG V} (hsub : ∀ a b, H.edge a b → G.edge a b)
    {O X Y : Finset V} (h : ¬ Identifiable H (fun _ => Bool) O X Y) :
    ¬ Identifiable G (fun _ => Bool) O X Y := by
  intro hG
  apply h
  intro M1 M2 hM hpos t
  have hp : ∀ v, H.parents v ⊆ G.parents v := fun v a ha => by
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hsub _ _ ha
  have hm : ∀ (M : H.CausalModel (fun _ => Bool)) (S : Finset V),
      (Completeness.liftSub hp M).marginal S = M.marginal S := fun M S =>
    Completeness.marginal_eq_of_kfac _ M (BowGen.kfac_liftG hp M) S
  have hd : ∀ (M : H.CausalModel (fun _ => Bool)) (x0 : Assignment (α := fun _ : V => Bool) X)
      (S : Finset V), (doModel (Completeness.liftSub hp M) X x0).marginal S =
        (doModel M X x0).marginal S := fun M x0 S =>
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_lift_doG hp M X x0) S
  have e := hG (Completeness.liftSub hp M1) (Completeness.liftSub hp M2)
    (by rw [hm, hm]; exact hM) (by intro a; rw [hm]; exact hpos a) t
  rw [hd, hd] at e
  exact e

/-- `G` uten kanter som berører `S`. -/
noncomputable def isoSet (G : DAG V) (S : Finset V) : DAG V where
  edge a b := G.edge a b ∧ a ∉ S ∧ b ∉ S
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := fun a b h => G.rank_strict_mono a b h.1

lemma isoSet_edge {G : DAG V} {S : Finset V} {a b : V} :
    (isoSet G S).edge a b ↔ G.edge a b ∧ a ∉ S ∧ b ∉ S := Iff.rfl

/-- `ρ → p₁ → … → p_m` er en rettet sti i `G`. -/
def IsPath (G : DAG V) : V → List V → Prop
  | _, [] => True
  | ρ, p :: rest => G.edge ρ p ∧ IsPath G p rest

/-- Stiens endepunkt. -/
def lastOf : V → List V → V
  | ρ, [] => ρ
  | _, p :: rest => lastOf p rest

/-- **En hel sti.** Er effekten på `Y ∋ ρ` ikke identifiserbar når stien `ρ → p₁ → … → p_m`
er fjernet, så er effekten på `Y ∖ {ρ} ∪ {p_m}` ikke identifiserbar i `G`, med stinodene
observert. -/
theorem path_not_identifiable {G : DAG V} {X : Finset V} (ps : List V) :
    ∀ (ρ : V) (O Y : Finset V), IsPath G ρ ps → (ρ :: ps).Nodup → ρ ∈ O → ρ ∈ Y →
      (∀ p ∈ ps, p ∉ O ∧ p ∉ Y ∧ p ∉ X) → Disjoint Y X →
      ¬ Identifiable (isoSet G ps.toFinset) (fun _ => Bool) O X Y →
      ¬ Identifiable G (fun _ => Bool) (O ∪ ps.toFinset) X (insert (lastOf ρ ps) (Y.erase ρ)) := by
  induction ps with
  | nil =>
    intro ρ O Y _ _ _ hρY _ _ h
    simp only [lastOf, List.toFinset_nil, Finset.union_empty, Finset.insert_erase hρY]
    exact not_ident_of_sub (fun a b hab => (isoSet_edge.mp hab).1) h
  | cons p1 rest ih =>
    intro ρ O Y hP hnd hρO hρY hps hYX h
    obtain ⟨hρp, hP'⟩ := hP
    have hnd' : (p1 :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have hρnot : ρ ∉ p1 :: rest := (List.nodup_cons.mp hnd).1
    have hp1rest : p1 ∉ rest := (List.nodup_cons.mp hnd').1
    obtain ⟨hp1O, hp1Y, hp1X⟩ := hps p1 (by simp)
    have hp1S : p1 ∈ (p1 :: rest).toFinset := by simp
    -- Ett kanalsteg: p₁ legges på
    let D : Step (isoSet G (p1 :: rest).toFinset) (isoSet G rest.toFinset) :=
      { ρ := ρ
        y := p1
        hsub := fun a b hab => by
          obtain ⟨h1, h2, h3⟩ := isoSet_edge.mp hab
          refine isoSet_edge.mpr ⟨h1, fun ha => h2 ?_, fun hb => h3 ?_⟩
          · simp only [List.mem_toFinset, List.mem_cons] at ha ⊢
            exact Or.inr ha
          · simp only [List.mem_toFinset, List.mem_cons] at hb ⊢
            exact Or.inr hb
        hρy := isoSet_edge.mpr ⟨hρp,
          fun h => hρnot (List.mem_cons_of_mem _ (List.mem_toFinset.mp h)),
          fun h => hp1rest (List.mem_toFinset.mp h)⟩
        hiso := fun a => ⟨fun hab => (isoSet_edge.mp hab).2.2 hp1S,
          fun hab => (isoSet_edge.mp hab).2.1 hp1S⟩ }
    have hs1 : ¬ Identifiable (isoSet G rest.toFinset) (fun _ => Bool) (insert p1 O) X
        (insert p1 (Y.erase ρ)) :=
      channel_step D hρO hp1O hρY hp1Y hp1X hYX h
    -- Resten av stien
    have hps' : ∀ p ∈ rest, p ∉ insert p1 O ∧ p ∉ insert p1 (Y.erase ρ) ∧ p ∉ X := by
      intro p hp
      obtain ⟨hO, hY, hX⟩ := hps p (List.mem_cons_of_mem _ hp)
      have hne : p ≠ p1 := fun e => hp1rest (e ▸ hp)
      refine ⟨?_, ?_, hX⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hO⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨hne, fun h => hY (Finset.mem_of_mem_erase h)⟩
    have hYX' : Disjoint (insert p1 (Y.erase ρ)) X :=
      Finset.disjoint_insert_left.mpr
        ⟨hp1X, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYX⟩
    have hrest := ih p1 (insert p1 O) (insert p1 (Y.erase ρ)) hP' hnd'
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) hps' hYX' hs1
    -- Mengdene på riktig form
    have e1 : O ∪ (p1 :: rest).toFinset = insert p1 O ∪ rest.toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    have e2 : (insert p1 (Y.erase ρ)).erase p1 = Y.erase ρ :=
      Finset.erase_insert (fun h => hp1Y (Finset.mem_of_mem_erase h))
    rw [e1]
    show ¬ Identifiable G (fun _ => Bool) (insert p1 O ∪ rest.toFinset) X
      (insert (lastOf p1 rest) (Y.erase ρ))
    rw [← e2]
    exact hrest

/-- **Hedge med hale.** En `RT`-hedge i grafen uten stien, og en rettet sti fra en av
røttene: røtten kan byttes ut med stiens endepunkt i `Y`. -/
theorem rootTree_tail {G : DAG V} {n : ℕ} (ps : List V)
    (T : RootTree.RT (isoSet G ps.toFinset) n) (O : Finset V) (ρ : V)
    (hu : ∀ j, T.u j ∉ O) (hR : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O)
    (hρ : ρ ∈ T.Y) (hP : IsPath G ρ ps) (hnd : (ρ :: ps).Nodup)
    (hps : ∀ p ∈ ps, p ∉ O ∧ p ∉ T.Y ∧ p ≠ T.x) :
    ¬ Identifiable G (fun _ => Bool) (O ∪ ps.toFinset) {T.x}
      (insert (lastOf ρ ps) (T.Y.erase ρ)) := by
  have hYX : Disjoint T.Y {T.x} := by
    rw [Finset.disjoint_singleton_right]
    intro hm
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact T.hndx k hk
  have hρO : ρ ∈ O := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hρ
    exact hR k (Finset.mem_filter.mp hk).2
  exact path_not_identifiable ps ρ O T.Y hP hnd hρO hρ
    (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1, by
      rw [Finset.mem_singleton]; exact (hps p hp).2.2⟩) hYX
    (RootTree.rootTree_not_identifiable T O hu hR hx)

end Channel
end Identification

#print axioms Identification.Channel.path_not_identifiable
#print axioms Identification.Channel.rootTree_tail

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

/-- Full tilordning: observerte fra `a`, latente i `T` fra `w`, andre latente vilkårlige. -/
noncomputable def fill [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w : Assignment (α := α) (U ∩ T)) : Assignment (α := α) (Finset.univ : Finset V) :=
  fun v => if h0 : v.1 ∈ U then
      (if h1 : v.1 ∈ T then w ⟨v.1, Finset.mem_inter.mpr ⟨h0, h1⟩⟩ else Classical.arbitrary _)
    else a ⟨v.1, Finset.mem_compl.mpr h0⟩

/-- **Faktoren `Q[T]`:** summen over de latente i `T` av kjernene i `T`. -/
noncomputable def Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) : ENNReal :=
  ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T, kfac M Finset.univ (fill U T a w) v

/-- Full tilordning satt sammen av de observerte og de latente i hver blokk. -/
noncomputable def full2 (U S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ S)) (w2 : Assignment (α := α) (U ∩ Sᶜ)) :
    Assignment (α := α) (Finset.univ : Finset V) :=
  fun v => if h0 : v.1 ∈ U then
      (if h1 : v.1 ∈ S then w1 ⟨v.1, Finset.mem_inter.mpr ⟨h0, h1⟩⟩
       else w2 ⟨v.1, Finset.mem_inter.mpr ⟨h0, Finset.mem_compl.mpr h1⟩⟩)
    else a ⟨v.1, Finset.mem_compl.mpr h0⟩

lemma full2_eq_iff (U S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ S)) (w2 : Assignment (α := α) (U ∩ Sᶜ))
    (s : Assignment (α := α) (Finset.univ : Finset V)) :
    s = full2 U S a w1 w2 ↔ a = s.restrict (Finset.subset_univ _) ∧
      w1 = s.restrict (Finset.subset_univ _) ∧ w2 = s.restrict (Finset.subset_univ _) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨v, hv⟩
      have h0 : v ∉ U := Finset.mem_compl.mp hv
      simp [full2, Assignment.restrict, h0]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      simp [full2, Assignment.restrict, h0, h1]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      have h1' : v ∉ S := Finset.mem_compl.mp h1
      simp [full2, Assignment.restrict, h0, h1']
  · rintro ⟨rfl, rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases h0 : v ∈ U
    · by_cases h1 : v ∈ S
      · simp [full2, Assignment.restrict, h0, h1]
      · simp [full2, Assignment.restrict, h0, h1]
    · simp [full2, Assignment.restrict, h0]

/-- Kjernefaktoren avhenger bare av noden selv og foreldrene. -/
lemma kfac_congr (M : G.CausalModel α) (s s' : Assignment (α := α) (Finset.univ : Finset V))
    (v : V) (hv : s ⟨v, Finset.mem_univ v⟩ = s' ⟨v, Finset.mem_univ v⟩)
    (hp : ∀ u ∈ G.parents v, s ⟨u, Finset.mem_univ u⟩ = s' ⟨u, Finset.mem_univ u⟩) :
    kfac M Finset.univ s v = kfac M Finset.univ s' v := by
  have hr : s.restrict (Finset.subset_univ (G.parents v)) =
      s'.restrict (Finset.subset_univ (G.parents v)) := by
    funext ⟨u, hu⟩
    exact hp u hu
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ, hr, hv]

lemma val1 [∀ v, Nonempty (α v)] (U S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ S)) (w2 : Assignment (α := α) (U ∩ Sᶜ)) (z : V)
    (hz : z ∈ U → z ∈ S) :
    full2 U S a w1 w2 ⟨z, Finset.mem_univ z⟩ = fill U S a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [full2, fill, h0, hz h0]
  · simp [full2, fill, h0]

lemma val2 [∀ v, Nonempty (α v)] (U S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ S)) (w2 : Assignment (α := α) (U ∩ Sᶜ)) (z : V)
    (hz : z ∈ U → z ∉ S) :
    full2 U S a w1 w2 ⟨z, Finset.mem_univ z⟩ = fill U Sᶜ a w2 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · have h1 : z ∉ S := hz h0
    have h1' : z ∈ Sᶜ := Finset.mem_compl.mpr h1
    simp [full2, fill, h0, h1, h1']
  · simp [full2, fill, h0]

lemma edge_of_par {u v : V} (h : u ∈ G.parents v) : G.edge u v := by
  simpa [DAG.parents] using h

/-- **C-komponent-faktorisering.** For en lukket blokk `S`. -/
theorem marginal_factor [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (a : Assignment (α := α) Uᶜ) :
    M.marginal Uᶜ a = Q M U S a * Q M U Sᶜ a := by
  -- 1. Marginalen er en sum over de latente i hver blokk
  have h1 : M.marginal Uᶜ a = ∑' w1 : Assignment (α := α) (U ∩ S),
      ∑' w2 : Assignment (α := α) (U ∩ Sᶜ), M.fullJoint (full2 U S a w1 w2) := by
    show (M.fullJoint.map (Assignment.restrict (Finset.subset_univ _))) a = _
    rw [PMF.map_apply]
    calc (∑' s : Assignment (α := α) (Finset.univ : Finset V),
            if a = s.restrict (Finset.subset_univ _) then M.fullJoint s else 0)
        = ∑' s, ∑' w1, ∑' w2,
            (if s = full2 U S a w1 w2 then M.fullJoint s else 0) := by
          refine tsum_congr (fun s => ?_)
          by_cases ha : a = s.restrict (Finset.subset_univ _)
          · rw [if_pos ha, tsum_eq_single (s.restrict (Finset.subset_univ (U ∩ S)))]
            · rw [tsum_eq_single (s.restrict (Finset.subset_univ (U ∩ Sᶜ)))]
              · rw [if_pos ((full2_eq_iff U S a _ _ s).mpr ⟨ha, rfl, rfl⟩)]
              · intro w2 hw2
                rw [if_neg (fun h => hw2 ((full2_eq_iff U S a _ _ s).mp h).2.2)]
            · intro w1 hw1
              exact ENNReal.tsum_eq_zero.mpr (fun w2 =>
                if_neg (fun h => hw1 ((full2_eq_iff U S a _ _ s).mp h).2.1))
          · rw [if_neg ha]
            symm
            exact ENNReal.tsum_eq_zero.mpr (fun w1 => ENNReal.tsum_eq_zero.mpr (fun w2 =>
              if_neg (fun h => ha ((full2_eq_iff U S a _ _ s).mp h).1)))
      _ = ∑' w1, ∑' s, ∑' w2,
            (if s = full2 U S a w1 w2 then M.fullJoint s else 0) := ENNReal.tsum_comm
      _ = ∑' w1, ∑' w2, ∑' s,
            (if s = full2 U S a w1 w2 then M.fullJoint s else 0) :=
          tsum_congr (fun w1 => ENNReal.tsum_comm)
      _ = _ := by
          refine tsum_congr (fun w1 => tsum_congr (fun w2 => ?_))
          rw [tsum_eq_single (full2 U S a w1 w2)]
          · simp
          · intro s hs
            rw [if_neg hs]
  -- 2. Fellesfordelingen deler seg i blokkenes faktorer
  have h2 : ∀ w1 w2, M.fullJoint (full2 U S a w1 w2) =
      (∏ v ∈ S, kfac M Finset.univ (fill U S a w1) v) *
        ∏ v ∈ Sᶜ, kfac M Finset.univ (fill U Sᶜ a w2) v := by
    intro w1 w2
    rw [fullJoint_apply_prod, ← Finset.prod_mul_prod_compl S]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (val1 U S a w1 w2 v (fun _ => hv)) (fun u hu => val1 U S a w1 w2 u
          (fun hu0 => (hcl u hu0 v (edge_of_par hu)).mpr hv)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (val2 U S a w1 w2 v (fun _ => Finset.mem_compl.mp hv)) (fun u hu => val2 U S a w1 w2 u
          (fun hu0 hus => Finset.mem_compl.mp hv ((hcl u hu0 v (edge_of_par hu)).mp hus))))
  -- 3. Summen av et produkt er produktet av summene
  rw [h1]
  simp only [h2]
  unfold Q
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

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

#print axioms Identification.CFactor.marginal_factor
#print axioms Identification.CFactor.do_marginal_factor

/-! ## Runde 21: faktorene er identifiserbare (Tians lemma 2)

Runde 20 delte `P(O)` i `Q[S] · Q[Sᶜ]`. Her vises at hver faktor er bestemt av den
observerte fordelingen alene.

1. `anc_factor`: faktoriseringen gjelder for hver ancestralt lukket mengde `A`:
   `P(O ∩ A) = Q[A ∩ S] · Q[A ∩ Sᶜ]`.
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

lemma subO (U A : Finset V) : Uᶜ ∩ A ⊆ Uᶜ := Finset.inter_subset_left
lemma subOA (U A : Finset V) : Uᶜ ∩ A ⊆ A := Finset.inter_subset_right
lemma subA1 (U A S : Finset V) : U ∩ (A ∩ S) ⊆ A :=
  fun _ hv => (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1
lemma subA2 (U A S : Finset V) : U ∩ (A ∩ Sᶜ) ⊆ A :=
  fun _ hv => (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1

/-- Full tilordning for en mengde `A`: observerte fra `a`, latente i `A ∩ S` fra `w1`,
latente i `A ∩ Sᶜ` fra `w2`, resten vilkårlig. -/
noncomputable def full3 [∀ v, Nonempty (α v)] (U A S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (A ∩ S))) (w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ))) :
    Assignment (α := α) (Finset.univ : Finset V) :=
  fun v => if h0 : v.1 ∈ U then
      (if h1 : v.1 ∈ A ∩ S then w1 ⟨v.1, Finset.mem_inter.mpr ⟨h0, h1⟩⟩
       else if h2 : v.1 ∈ A ∩ Sᶜ then w2 ⟨v.1, Finset.mem_inter.mpr ⟨h0, h2⟩⟩
       else Classical.arbitrary _)
    else a ⟨v.1, Finset.mem_compl.mpr h0⟩

lemma full3_iff [∀ v, Nonempty (α v)] (U A S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (A ∩ S))) (w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)))
    (b : Assignment (α := α) A) :
    b = (full3 U A S a w1 w2).restrict (Finset.subset_univ A) ↔
      a.restrict (subO U A) = b.restrict (subOA U A) ∧ w1 = b.restrict (subA1 U A S) ∧
        w2 = b.restrict (subA2 U A S) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨v, hv⟩
      have h0 : v ∉ U := Finset.mem_compl.mp (Finset.mem_inter.mp hv).1
      simp [full3, Assignment.restrict, h0]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      obtain ⟨hA, hS⟩ := Finset.mem_inter.mp h1
      simp [full3, Assignment.restrict, h0, hA, hS]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      obtain ⟨hA, hS⟩ := Finset.mem_inter.mp h1
      have hS' : v ∉ S := Finset.mem_compl.mp hS
      simp [full3, Assignment.restrict, h0, hA, hS']
  · rintro ⟨ha, rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases h0 : v ∈ U
    · by_cases hS : v ∈ S
      · simp [full3, Assignment.restrict, h0, hv, hS]
      · simp [full3, Assignment.restrict, h0, hv, hS]
    · have h := congrFun ha ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr h0, hv⟩⟩
      simpa [full3, Assignment.restrict, h0] using h.symm

lemma wal1 [∀ v, Nonempty (α v)] (U A S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (A ∩ S))) (w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ A ∩ S) :
    full3 U A S a w1 w2 ⟨z, Finset.mem_univ z⟩ = fill U (A ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hA, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp [full3, fill, h0, hA, hS]
  · simp [full3, fill, h0]

lemma wal2 [∀ v, Nonempty (α v)] (U A S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (A ∩ S))) (w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ A ∩ Sᶜ) :
    full3 U A S a w1 w2 ⟨z, Finset.mem_univ z⟩ = fill U (A ∩ Sᶜ) a w2 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hA, hS⟩ := Finset.mem_inter.mp (hz h0)
    have hS' : z ∉ S := Finset.mem_compl.mp hS
    simp [full3, fill, h0, hA, hS']
  · simp [full3, fill, h0]

/-- **Faktorisering på en ancestral mengde.** -/
theorem anc_factor [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U A S : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (a : Assignment (α := α) Uᶜ) :
    M.marginal (Uᶜ ∩ A) (a.restrict (subO U A)) = Q M U (A ∩ S) a * Q M U (A ∩ Sᶜ) a := by
  have hpa : ∀ v ∈ A, G.parents v ⊆ A := fun v hv u hu => hA v hv u (edge_of_par hu)
  -- 1. Marginalen er en sum over de latente i `A ∩ S` og i `A ∩ Sᶜ`
  have h1 : M.marginal (Uᶜ ∩ A) (a.restrict (subO U A)) =
      ∑' w1 : Assignment (α := α) (U ∩ (A ∩ S)), ∑' w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)),
        ∏ v ∈ A, kfac M Finset.univ (full3 U A S a w1 w2) v := by
    rw [← marginal_restrict M (subOA U A), PMF.map_apply]
    calc (∑' b : Assignment (α := α) A,
            if a.restrict (subO U A) = b.restrict (subOA U A) then M.marginal A b else 0)
        = ∑' b, ∑' w1, ∑' w2, (if b = (full3 U A S a w1 w2).restrict (Finset.subset_univ A)
            then M.marginal A b else 0) := by
          refine tsum_congr (fun b => ?_)
          by_cases ha : a.restrict (subO U A) = b.restrict (subOA U A)
          · rw [if_pos ha, tsum_eq_single (b.restrict (subA1 U A S))]
            · rw [tsum_eq_single (b.restrict (subA2 U A S))]
              · rw [if_pos ((full3_iff U A S a _ _ b).mpr ⟨ha, rfl, rfl⟩)]
              · intro w2 hw2
                rw [if_neg (fun h => hw2 ((full3_iff U A S a _ _ b).mp h).2.2)]
            · intro w1 hw1
              exact ENNReal.tsum_eq_zero.mpr (fun w2 =>
                if_neg (fun h => hw1 ((full3_iff U A S a _ _ b).mp h).2.1))
          · rw [if_neg ha]
            symm
            exact ENNReal.tsum_eq_zero.mpr (fun w1 => ENNReal.tsum_eq_zero.mpr (fun w2 =>
              if_neg (fun h => ha ((full3_iff U A S a _ _ b).mp h).1)))
      _ = ∑' w1, ∑' b, ∑' w2, (if b = (full3 U A S a w1 w2).restrict (Finset.subset_univ A)
            then M.marginal A b else 0) := ENNReal.tsum_comm
      _ = ∑' w1, ∑' w2, ∑' b, (if b = (full3 U A S a w1 w2).restrict (Finset.subset_univ A)
            then M.marginal A b else 0) := tsum_congr (fun w1 => ENNReal.tsum_comm)
      _ = _ := by
          refine tsum_congr (fun w1 => tsum_congr (fun w2 => ?_))
          rw [tsum_eq_single ((full3 U A S a w1 w2).restrict (Finset.subset_univ A))]
          · rw [if_pos rfl, marginal_ancestral_apply M A hA]
            exact Finset.prod_congr rfl
              (fun v hv => kfac_restrict M (Finset.subset_univ A) _ hv (hpa v hv))
          · intro b hb
            rw [if_neg hb]
  -- 2. Produktet over `A` deler seg i blokkenes faktorer
  have h2 : ∀ w1 w2, ∏ v ∈ A, kfac M Finset.univ (full3 U A S a w1 w2) v =
      (∏ v ∈ A ∩ S, kfac M Finset.univ (fill U (A ∩ S) a w1) v) *
        ∏ v ∈ A ∩ Sᶜ, kfac M Finset.univ (fill U (A ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff A S, Finset.sdiff_eq_inter_compl]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (wal1 U A S a w1 w2 v (fun _ => hv)) (fun u hu => wal1 U A S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr ⟨hA v (Finset.mem_inter.mp hv).1 u (edge_of_par hu),
            (hcl u hu0 v (edge_of_par hu)).mpr (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (wal2 U A S a w1 w2 v (fun _ => hv)) (fun u hu => wal2 U A S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr ⟨hA v (Finset.mem_inter.mp hv).1 u (edge_of_par hu),
            Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
              ((hcl u hu0 v (edge_of_par hu)).mp hus))⟩)))
  -- 3. Summen av et produkt er produktet av summene
  rw [h1]
  simp only [h2]
  unfold Q
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

lemma inter_erase_of_not_mem {A T : Finset V} {v : V} (h : v ∉ T) :
    A ∩ T = A.erase v ∩ T := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun e => h (by rw [← e]; exact h2), h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- **Den eksplisitte formelen (ett steg).** `Q[A ∩ T] = Q[A' ∩ T] · P(O ∩ A) / P(O ∩ A')`,
skrevet uten divisjon. -/
theorem Q_step [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U A T : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ T ↔ v ∈ T)) (v : V) (hvT : v ∈ T)
    (hA' : ∀ z ∈ A.erase v, ∀ w, G.edge w z → w ∈ A.erase v) (a : Assignment (α := α) Uᶜ) :
    M.marginal (Uᶜ ∩ A) (a.restrict (subO U A)) * Q M U (A.erase v ∩ T) a =
      M.marginal (Uᶜ ∩ A.erase v) (a.restrict (subO U (A.erase v))) * Q M U (A ∩ T) a := by
  rw [anc_factor M U A T hA hcl a, anc_factor M U (A.erase v) T hA' hcl a,
    ← inter_erase_of_not_mem (A := A) (fun h => (Finset.mem_compl.mp h) hvT)]
  ring

lemma marginal_restrict_ne_zero (M : G.CausalModel α) {S T : Finset V} (h : T ⊆ S)
    (a : Assignment (α := α) S) (ha : M.marginal S a ≠ 0) :
    M.marginal T (a.restrict h) ≠ 0 := by
  rw [← marginal_restrict M h, PMF.map_apply]
  intro h0
  apply ha
  have h1 := (ENNReal.tsum_eq_zero.mp h0) a
  rwa [if_pos rfl] at h1

/-- Induksjon over ancestrale mengder: begge faktorene er like i de to modellene. -/
theorem Q_ident_anc [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U S : Finset V)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hM : M1.marginal Uᶜ = M2.marginal Uᶜ) (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0) (n : ℕ) :
    ∀ A : Finset V, A.card = n → (∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) →
      ∀ a, Q M1 U (A ∩ S) a = Q M2 U (A ∩ S) a ∧ Q M1 U (A ∩ Sᶜ) a = Q M2 U (A ∩ Sᶜ) a := by
  have hpos2 : ∀ a, M2.marginal Uᶜ a ≠ 0 := fun a => by rw [← hM]; exact hpos a
  have hMA : ∀ B : Finset V, M1.marginal (Uᶜ ∩ B) = M2.marginal (Uᶜ ∩ B) := fun B => by
    rw [← marginal_restrict M1 (subO U B), ← marginal_restrict M2 (subO U B), hM]
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
    have hP0 : M2.marginal (Uᶜ ∩ A.erase v) (a.restrict (subO U (A.erase v))) ≠ 0 :=
      marginal_restrict_ne_zero M2 _ a (hpos2 a)
    have hPt : M2.marginal (Uᶜ ∩ A.erase v) (a.restrict (subO U (A.erase v))) ≠ ⊤ :=
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
      rw [inter_erase_of_not_mem (A := A) (fun h => (Finset.mem_compl.mp h) hvS)]
      exact ih2
    · refine ⟨?_, key Sᶜ hclc (Finset.mem_compl.mpr hvS) ih2⟩
      rw [inter_erase_of_not_mem (A := A) hvS]
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

#print axioms Identification.CFactor.anc_factor
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
        (by have e := edge_of_par hu; rw [h] at e; exact e))))
  have hxk : ∀ x' : α x, kfac M Finset.univ (fill U S (upd U hx a x') w) x =
      M.kernel x ((fill U S a w).restrict (Finset.subset_univ _)) x' := by
    intro x'
    have hr : (fill U S (upd U hx a x') w).restrict (Finset.subset_univ (G.parents x)) =
        (fill U S a w).restrict (Finset.subset_univ (G.parents x)) := by
      funext ⟨u, hu⟩
      exact fill_upd_ne U S hx a x' w u (fun h => DAG.not_self_edge G x
        (by have e := edge_of_par hu; rw [h] at e; exact e))
    rw [DoAudit.kfac_univ, hr, fill_upd_x U S hx a x' w]
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

/-! ## Runde 24: skillelinjen for én `x` som ett teorem

Når de latente er røtter (Tians standardsetting) og variablene er boolske, gjelder

  `P(O ∖ {x} | do(x))` identifiserbar  ⟺  intet barn av `x` i c-komponenten til `x`
  (`tian_iff`).

`⟸` er runde 22–23. `⟹` er den andre halvdelen av broen (`not_ident_of_child`): et barn
`c` av `x` i c-komponenten gir en hedge.

1. `rtg_chain`: latente steg fra `x` til `c` gir en kjede `f 0 = x, …, f m = c`.
2. Ta en korteste kjede fra `x` til et barn av `x` (`Nat.find`). Den har ingen gjentatte
   noder: en gjentakelse kunne kuttes bort (`chain_cut`), og kjeden ble kortere.
3. Når de latente er røtter, bytter hvert steg mellom observert og latent
   (`chain_parity`), så kjeden er `x ← u₀ → o₀ ← u₁ → o₁ ← ⋯ → o_p` med `x → o_p`.
4. `p = 1` er buen (`bow_not_identifiable_general`). For `p ≥ 2` er kjeden nøyaktig en
   `RT`-struktur med en latent sti som tre og alle `o_k` som røtter, og runde 17
   (`embedded_not_identifiable`) gir resten. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Relasjonssteg fra `x` til `v` gir en kjede indeksert med `ℕ`. -/
lemma rtg_chain {r : V → V → Prop} {x v : V} (h : Relation.ReflTransGen r x v) :
    ∃ m : ℕ, ∃ f : ℕ → V, f 0 = x ∧ f m = v ∧ ∀ i < m, r (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨m, f, h0, hm, hs⟩ := ih
    refine ⟨m + 1, fun i => if i ≤ m then f i else c, ?_, ?_, ?_⟩
    · show (if 0 ≤ m then f 0 else c) = x
      rw [if_pos (Nat.zero_le m), h0]
    · show (if m + 1 ≤ m then f (m + 1) else c) = c
      rw [if_neg (show ¬ (m + 1 ≤ m) by omega)]
    · intro i hi
      show r (if i ≤ m then f i else c) (if i + 1 ≤ m then f (i + 1) else c)
      by_cases hlt : i + 1 ≤ m
      · rw [if_pos (show i ≤ m by omega), if_pos hlt]
        exact hs i (by omega)
      · rw [if_pos (show i ≤ m by omega), if_neg hlt, show i = m by omega, hm]
        exact hbc

/-- **Kutt.** Er `f i = f j` med `i < j ≤ m`, finnes en kjede med samme ender som er
`j - i` kortere. -/
lemma chain_cut {r : V → V → Prop} {m i j : ℕ} {f : ℕ → V}
    (hs : ∀ k < m, r (f k) (f (k + 1))) (hij : i < j) (hjm : j ≤ m) (he : f i = f j) :
    ∃ g : ℕ → V, g 0 = f 0 ∧ g (m - (j - i)) = f m ∧
      ∀ k < m - (j - i), r (g k) (g (k + 1)) := by
  refine ⟨fun k => if k ≤ i then f k else f (k + (j - i)), ?_, ?_, ?_⟩
  · show (if 0 ≤ i then f 0 else f (0 + (j - i))) = f 0
    rw [if_pos (Nat.zero_le i)]
  · show (if m - (j - i) ≤ i then f (m - (j - i)) else f (m - (j - i) + (j - i))) = f m
    by_cases hle : m - (j - i) ≤ i
    · rw [if_pos hle, show m - (j - i) = i by omega, he, show j = m by omega]
    · rw [if_neg hle, show m - (j - i) + (j - i) = m by omega]
  · intro k hk
    show r (if k ≤ i then f k else f (k + (j - i)))
      (if k + 1 ≤ i then f (k + 1) else f (k + 1 + (j - i)))
    by_cases h1 : k + 1 ≤ i
    · rw [if_pos (show k ≤ i by omega), if_pos h1]
      exact hs k (by omega)
    · by_cases h2 : k ≤ i
      · rw [if_pos h2, if_neg h1, show k = i by omega, he,
          show i + 1 + (j - i) = j + 1 by omega]
        exact hs j (by omega)
      · rw [if_neg h2, if_neg h1, show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hs (k + (j - i)) (by omega)

/-- Når de latente er røtter, går et latent steg mellom en latent og en observert node,
langs en kant fra den latente. -/
lemma latStep_edges {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {a b : V} (h : latStep G U a b) :
    (a ∈ U → G.edge a b ∧ b ∉ U) ∧ (b ∈ U → G.edge b a ∧ a ∉ U) := by
  rcases h with ⟨_, e⟩ | ⟨_, e⟩
  · exact ⟨fun _ => ⟨e, fun hb => hroot b hb a e⟩, fun hb => absurd e (hroot b hb a)⟩
  · exact ⟨fun ha => absurd e (hroot a ha b), fun _ => ⟨e, fun ha => hroot a ha b e⟩⟩

/-- **Paritet.** Starter kjeden i en observert node, er nøyaktig de odde plassene latente. -/
lemma chain_parity {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {f : ℕ → V} {m : ℕ} (hf0 : f 0 ∉ U) (hs : ∀ i < m, latStep G U (f i) (f (i + 1))) :
    ∀ i ≤ m, (f i ∈ U ↔ i % 2 = 1) := by
  intro i
  induction i with
  | zero => intro _; simp [hf0]
  | succ i ih =>
    intro hi
    have h := hs i (by omega)
    have e := latStep_edges hroot h
    have ih' := ih (by omega)
    have hU : f i ∈ U ∨ f (i + 1) ∈ U := by
      rcases h with ⟨ha, _⟩ | ⟨hb, _⟩
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hU with ha | hb
    · have hb := (e.1 ha).2
      have hi1 : i % 2 = 1 := ih'.mp ha
      exact ⟨fun h' => absurd h' hb, fun h' => absurd h' (by omega)⟩
    · have ha := (e.2 hb).2
      have hi0 : i % 2 ≠ 1 := fun h' => ha (ih'.mpr h')
      exact ⟨fun _ => by omega, fun _ => hb⟩

/-- **Den andre halvdelen av broen.** Er de latente røtter og ligger et barn av `x` i
c-komponenten til `x`, er `P(O ∖ {x} | do(x))` ikke identifiserbar. -/
theorem not_ident_of_child {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {x c : V} (hx : x ∉ U) (hcc : c ∈ ccomp G U x) (hxc : G.edge x c) :
    ¬ Identifiable G (fun _ => Bool) Uᶜ {x} (Uᶜ.erase x) := by
  -- 1. En korteste kjede fra `x` til et barn av `x`
  have hex : ∃ m, ∃ f : ℕ → V, f 0 = x ∧ G.edge x (f m) ∧
      ∀ i < m, latStep G U (f i) (f (i + 1)) := by
    obtain ⟨m, f, h0, hm, hs⟩ := rtg_chain (mem_ccomp.mp hcc)
    exact ⟨m, f, h0, by rw [hm]; exact hxc, hs⟩
  have hmin : ∀ k, (∃ g : ℕ → V, g 0 = x ∧ G.edge x (g k) ∧
      ∀ i < k, latStep G U (g i) (g (i + 1))) → Nat.find hex ≤ k :=
    fun k hk => Nat.find_min' hex hk
  obtain ⟨f, hf0, hfm, hs⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  -- 2. Ingen gjentatte noder
  have hsimp : ∀ i j, i < j → j ≤ m → f i ≠ f j := by
    intro i j hij hjm he
    obtain ⟨g, hg0, hgm, hgs⟩ := chain_cut hs hij hjm he
    have := hmin (m - (j - i)) ⟨g, hg0.trans hf0, by rw [hgm]; exact hfm, hgs⟩
    omega
  -- 3. Paritet og kanter
  have hpar := chain_parity hroot (by rw [hf0]; exact hx) hs
  have hfmU : f m ∉ U := fun h => hroot _ h x hfm
  have hmeven : m % 2 = 0 := by
    by_contra h
    exact hfmU ((hpar m le_rfl).mpr (by omega))
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, hf0] at hfm
    exact DAG.not_self_edge G x hfm
  have hU1 : ∀ k, 2 * k + 1 ≤ m → f (2 * k + 1) ∈ U := fun k hk => (hpar _ hk).mpr (by omega)
  have hO2 : ∀ k, 2 * k + 2 ≤ m → f (2 * k + 2) ∉ U := fun k hk h => by
    have := (hpar _ hk).mp h
    omega
  have hE1 : ∀ k, 2 * k + 2 ≤ m → G.edge (f (2 * k + 1)) (f (2 * k + 2)) := fun k hk =>
    ((latStep_edges hroot (hs (2 * k + 1) (by omega))).1 (hU1 k (by omega))).1
  have hE0 : ∀ k, 2 * k + 2 ≤ m → G.edge (f (2 * k + 1)) (f (2 * k)) := fun k hk =>
    ((latStep_edges hroot (hs (2 * k) (by omega))).2 (hU1 k (by omega))).1
  have hx2 : ∀ k, 2 * k + 2 ≤ m → f (2 * k + 2) ≠ x := fun k hk e =>
    hsimp 0 (2 * k + 2) (by omega) hk (hf0.trans e.symm)
  -- 4. Buen eller en `RT`-struktur
  intro hid
  have hxO : x ∈ Uᶜ := Finset.mem_compl.mpr hx
  have hd : Disjoint (Uᶜ.erase x) {x} :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase x _)
  by_cases hm2 : m = 2
  · have e0 := hE0 0 (by omega)
    have e1 := hE1 0 (by omega)
    have o2 := hO2 0 (by omega)
    have x2 := hx2 0 (by omega)
    have u1 := hU1 0 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add] at e0 e1 o2 x2 u1
    rw [hf0] at e0
    have hb := BowGen.bow_not_identifiable_general G Uᶜ (f 1) x (f 2) e0 e1
      (by rw [hm2] at hfm; exact hfm) (fun h => (Finset.mem_compl.mp h) u1) hxO
      (Finset.mem_compl.mpr o2)
    apply hb
    refine hid.mono_Y hd ?_
    intro v hv
    rw [Finset.mem_singleton] at hv
    rw [hv]
    exact Finset.mem_erase.mpr ⟨x2, Finset.mem_compl.mpr o2⟩
  · obtain ⟨n, hn⟩ : ∃ n, m = 2 * (n + 2) := ⟨m / 2 - 2, by omega⟩
    let T : RootTree.RT G n :=
      { x := x
        nd := fun k => f (2 * k.val + 2)
        u := fun k => f (2 * k.val + 1)
        bp := fun j => if h : j.val = 0 then none else some ⟨j.val - 1, by have := j.isLt; omega⟩
        ht := fun j => n + 1 - j.val
        dp := fun _ => none
        r := Fin.last (n + 1)
        hbp0 := fun j => by
          by_cases h : j.val = 0
          · have hj : j = 0 := Fin.ext (by simp [h])
            simp [h, hj]
          · have hj : j ≠ 0 := fun e => h (by simp [e])
            simp [h, hj]
        hht := fun j k hjk => by
          by_cases h : j.val = 0
          · simp [h] at hjk
          · simp only [dif_neg h, Option.some.injEq] at hjk
            subst hjk
            have := j.isLt
            show n + 1 - j.val < n + 1 - (j.val - 1)
            omega
        hr := rfl
        hux := by
          have e := hE0 0 (by omega)
          simp only [Nat.mul_zero, Nat.zero_add] at e
          rw [hf0] at e
          show G.edge (f (2 * (0 : Fin (n + 2)).val + 1)) x
          simpa using e
        hun := fun k => hE1 k.val (by have := k.isLt; omega)
        hub := fun j k hjk => by
          by_cases h : j.val = 0
          · simp [h] at hjk
          · simp only [dif_neg h, Option.some.injEq] at hjk
            subst hjk
            have := j.isLt
            have e := hE0 j.val (by omega)
            show G.edge (f (2 * j.val + 1)) (f (2 * (j.val - 1) + 2))
            rw [show 2 * (j.val - 1) + 2 = 2 * j.val by omega]
            exact e
        hdp := fun j k h => ((Option.some_ne_none k).symm h).elim
        hxr := by
          show G.edge x (f (2 * (Fin.last (n + 1)).val + 2))
          rw [Fin.val_last, show 2 * (n + 1) + 2 = m by omega]
          exact hfm
        ndinj := fun a b hab => by
          have e : f (2 * a.val + 2) = f (2 * b.val + 2) := hab
          have ha := a.isLt
          have hb := b.isLt
          by_contra hne
          have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
          rcases Nat.lt_or_gt_of_ne hv with h | h
          · exact hsimp _ _ (show 2 * a.val + 2 < 2 * b.val + 2 by omega) (by omega) e
          · exact hsimp _ _ (show 2 * b.val + 2 < 2 * a.val + 2 by omega) (by omega) e.symm
        uinj := fun a b hab => by
          have e : f (2 * a.val + 1) = f (2 * b.val + 1) := hab
          have ha := a.isLt
          have hb := b.isLt
          by_contra hne
          have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
          rcases Nat.lt_or_gt_of_ne hv with h | h
          · exact hsimp _ _ (show 2 * a.val + 1 < 2 * b.val + 1 by omega) (by omega) e
          · exact hsimp _ _ (show 2 * b.val + 1 < 2 * a.val + 1 by omega) (by omega) e.symm
        hund := fun j k e => by
          have e' : f (2 * j.val + 1) = f (2 * k.val + 2) := e
          have := j.isLt
          have := k.isLt
          exact hO2 k.val (by omega) (by rw [← e']; exact hU1 j.val (by omega))
        hux' := fun j e => by
          have e' : f (2 * j.val + 1) = x := e
          have := j.isLt
          exact hx (by rw [← e']; exact hU1 j.val (by omega))
        hndx := fun k e => by
          have e' : f (2 * k.val + 2) = x := e
          have := k.isLt
          exact hx2 k.val (by omega) e' }
    refine RootTree.embedded_not_identifiable T Uᶜ (Uᶜ.erase x) ?_ ?_ hxO ?_ hd hid
    · intro j h
      have := j.isLt
      exact (Finset.mem_compl.mp h) (hU1 j.val (by omega))
    · intro k _
      have := k.isLt
      exact Finset.mem_compl.mpr (hO2 k.val (by omega))
    · intro v hv
      obtain ⟨k, -, hkv⟩ := Finset.mem_image.mp hv
      rw [← hkv]
      have := k.isLt
      exact Finset.mem_erase.mpr ⟨hx2 k.val (by omega), Finset.mem_compl.mpr (hO2 k.val (by omega))⟩

/-- **Skillelinjen for én `x`.** Med latente røtter og boolske variabler er
`P(O ∖ {x} | do(x))` identifiserbar hvis og bare hvis intet barn av `x` ligger i
c-komponenten til `x`. -/
theorem tian_iff {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {x : V} (hx : x ∉ U) :
    Identifiable G (fun _ => Bool) Uᶜ {x} (Uᶜ.erase x) ↔ ∀ v ∈ ccomp G U x, ¬ G.edge x v := by
  constructor
  · intro hid v hv hxv
    exact not_ident_of_child hroot hx hv hxv hid
  · intro h
    exact tian_identifiable_ccomp U hx h (Uᶜ.erase x) (Finset.erase_subset x _)

end CFactor
end Identification

#print axioms Identification.CFactor.not_ident_of_child
#print axioms Identification.CFactor.tian_iff

/-! ## Runde 25: Tians teorem for en mengde `X`

Samme bevis som runde 22, med en sum over alle verdiene til `X` i stedet for over `x`.
La `X ⊆ S` være observert, `S` en lukket blokk, og la ingen node i `X` ha et barn i `S`.
Da er

  `P_X(a) = [a_X = x] · (Σ_{x'} Q[S](a[X := x'])) · Q[Sᶜ](a)`,

og effekten av `X` er identifiserbar. (Runde 29: teoremene står nå etter runde 27, som
korollarer av `tian_identifiable_sets`; her står bare hjelpelemmaene.)

Nytt er bare `sum_assign_prod`: summen over alle tilordninger på `X` av et produkt av
kjerner er produktet av summene (`Fintype.prod_sum`), altså 1. Med c-komponenter: velg
`S` som unionen av c-komponentene til nodene i `X`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `a` med verdiene på `X` byttet ut med `x'`. -/
noncomputable def updX (U X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) : Assignment (α := α) Uᶜ :=
  fun v => if h : v.1 ∈ X then x' ⟨v.1, h⟩ else a v

lemma fill_updX_out [∀ v, Nonempty (α v)] (U T X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∉ X) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = fill U T a w ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [fill, h0]
  · simp [fill, h0, updX, hz]

lemma fill_updX_in [∀ v, Nonempty (α v)] (U T X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∈ X)
    (hzU : z ∉ U) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = x' ⟨z, hz⟩ := by
  simp [fill, hzU, updX, hz]

/-- **Produktet av summene.** Summert over alle tilordninger på `X` er et produkt av
sannsynlighetsfordelinger lik 1. -/
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

/-- **`X` summeres bort.** -/
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
      (fill_updX_out U S X a x' w v (Finset.mem_sdiff.mp hv).2)
      (fun u hu => fill_updX_out U S X a x' w u
        (fun huX => hch u huX v (Finset.mem_sdiff.mp hv).1 (edge_of_par hu))))
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
      exact fill_updX_out U S X a x' w u
        (fun huX => hch u huX v.1 (hXS v.2) (edge_of_par hu))
    rw [DoAudit.kfac_univ, hr,
      fill_updX_in U S X a x' w v.1 v.2 (Finset.mem_compl.mp (hXO v.2))]
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

/-! ## Runde 26: faktorisering over mange blokker (ID-algoritmens linje 4)

Runde 20–21 delte i to blokker, `S` og `Sᶜ`. ID-algoritmen trenger en faktor per
c-komponent. Her:

1. `Q_split`: for en mengde `T` som inneholder sine latente foreldre (`IsLatClosed`) og
   en lukket blokk `S`, er `Q[T] = Q[T ∩ S] · Q[T ∩ Sᶜ]`. Ren algebra: summen over de
   latente i `T` deles i to (`tsum_join2`), og produktet over `T` likeså.
2. `marginal_eq_Q`: `P(O) = Q[V]`.
3. `Q_prod`: for parvis disjunkte lukkede blokker `B i`, `i ∈ I`, som dekker `T`, er
   `Q[T] = ∏_{i ∈ I} Q[T ∩ B i]`. Induksjon over `I` med `Q_split`.
4. `marginal_prod`: `P(O) = ∏_i Q[B i]` når blokkene dekker alle noder. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `T` inneholder alle sine latente foreldre. -/
def IsLatClosed (G : DAG V) (U T : Finset V) : Prop :=
  ∀ v ∈ T, ∀ u ∈ U, G.edge u v → u ∈ T

/-- Faktoren for den tomme mengden er 1. -/
lemma Q_empty [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : Q M U ∅ a = 1 := by
  unfold Q
  simp only [Finset.prod_empty]
  have w0 : Assignment (α := α) (U ∩ ∅) := fun v => absurd v.2 (by simp)
  have hw : ∀ w w' : Assignment (α := α) (U ∩ ∅), w = w' :=
    fun w w' => funext (fun v => absurd v.2 (by simp))
  exact tsum_eq_single w0 (fun w hw' => absurd (hw w w0) hw')

lemma subT1 (U T S : Finset V) : U ∩ (T ∩ S) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

lemma subT2 (U T S : Finset V) : U ∩ (T ∩ Sᶜ) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

/-- De latente i `T`, satt sammen av delene i `T ∩ S` og `T ∩ Sᶜ`. -/
noncomputable def join2 (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) : Assignment (α := α) (U ∩ T) :=
  fun v => if h : v.1 ∈ S then
      w1 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, h⟩⟩⟩
    else w2 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, Finset.mem_compl.mpr h⟩⟩⟩

lemma join2_iff (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (w : Assignment (α := α) (U ∩ T)) :
    w = join2 U T S w1 w2 ↔ w1 = w.restrict (subT1 U T S) ∧ w2 = w.restrict (subT2 U T S) := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      have hS : v ∈ S := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [join2, Assignment.restrict, hS]
    · funext ⟨v, hv⟩
      have hS : v ∉ S := Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [join2, Assignment.restrict, hS]
  · rintro ⟨rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases hS : v ∈ S
    · simp [join2, Assignment.restrict, hS]
    · simp [join2, Assignment.restrict, hS]

/-- **Summen over de latente i `T` deler seg i to.** -/
lemma tsum_join2 (U T S : Finset V) (F : Assignment (α := α) (U ∩ T) → ENNReal) :
    ∑' w, F w = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
      ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)), F (join2 U T S w1 w2) := by
  calc ∑' w, F w
      = ∑' w, ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
            (if w = join2 U T S w1 w2 then F w else 0) := by
        refine tsum_congr (fun w => ?_)
        rw [tsum_eq_single (w.restrict (subT1 U T S))]
        · rw [tsum_eq_single (w.restrict (subT2 U T S))]
          · rw [if_pos ((join2_iff U T S _ _ w).mpr ⟨rfl, rfl⟩)]
          · intro w2 hw2
            rw [if_neg (fun h => hw2 ((join2_iff U T S _ _ w).mp h).2)]
        · intro w1 hw1
          exact ENNReal.tsum_eq_zero.mpr (fun w2 =>
            if_neg (fun h => hw1 ((join2_iff U T S _ _ w).mp h).1))
    _ = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)), ∑' w,
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
            (if w = join2 U T S w1 w2 then F w else 0) := ENNReal.tsum_comm
    _ = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)), ∑' w,
            (if w = join2 U T S w1 w2 then F w else 0) :=
        tsum_congr (fun w1 => ENNReal.tsum_comm)
    _ = _ := by
        refine tsum_congr (fun w1 => tsum_congr (fun w2 => ?_))
        rw [tsum_eq_single (join2 U T S w1 w2)]
        · simp
        · intro w hw
          rw [if_neg hw]

lemma fill_join1 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ S) :
    fill U T a (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp [fill, join2, h0, hT, hS]
  · simp [fill, h0]

lemma fill_join2 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ Sᶜ) :
    fill U T a (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ Sᶜ) a w2 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    have hS' : z ∉ S := Finset.mem_compl.mp hS
    simp [fill, join2, h0, hT, hS']
  · simp [fill, h0]

/-- **To blokker innenfor `T`.** -/
theorem Q_split [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : IsClosedBlock G U S) (a : Assignment (α := α) Uᶜ) :
    Q M U T a = Q M U (T ∩ S) a * Q M U (T ∩ Sᶜ) a := by
  have h2 : ∀ w1 w2, ∏ v ∈ T, kfac M Finset.univ (fill U T a (join2 U T S w1 w2)) v =
      (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
        ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ (fill U (T ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join1 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join1 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (edge_of_par hu),
              (hcl u hu0 v (edge_of_par hu)).mpr (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join2 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join2 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (edge_of_par hu),
              Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
                ((hcl u hu0 v (edge_of_par hu)).mp hus))⟩)))
  unfold Q
  rw [tsum_join2 U T S]
  simp only [h2]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

/-- `P(O) = Q[V]`. -/
theorem marginal_eq_Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : M.marginal Uᶜ a = Q M U Finset.univ a := by
  rw [marginal_factor M U Finset.univ (fun _ _ _ _ => by simp) a, Finset.compl_univ,
    Q_empty, mul_one]

/-- **Faktorisering over mange blokker.** -/
theorem Q_prod [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι) :
    ∀ T : Finset V, IsLatClosed G U T → (∀ i ∈ I, IsClosedBlock G U (B i)) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k)) → T ⊆ I.biUnion B →
      ∀ a, Q M U T a = ∏ i ∈ I, Q M U (T ∩ B i) a := by
  induction I using Finset.induction_on with
  | empty =>
    intro T _ _ _ hTI a
    have hT0 : T = ∅ := by simpa using hTI
    rw [hT0, Finset.prod_empty, Q_empty]
  | insert j I' hj ih =>
    intro T hT hcl hdisj hTI a
    have hclj : IsClosedBlock G U (B j) := hcl j (Finset.mem_insert_self j I')
    rw [Finset.prod_insert hj, Q_split M U T (B j) hT hclj a]
    congr 1
    have hT' : IsLatClosed G U (T ∩ (B j)ᶜ) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        Finset.mem_compl.mpr (fun huB => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
          ((hclj u hu v e).mp huB))⟩
    have hTI' : T ∩ (B j)ᶜ ⊆ I'.biUnion B := by
      intro v hv
      obtain ⟨hvT, hvB⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hTI hvT)
      rcases Finset.mem_insert.mp hi with hij | hi'
      · rw [hij] at hvi
        exact absurd hvi (Finset.mem_compl.mp hvB)
      · exact Finset.mem_biUnion.mpr ⟨i, hi', hvi⟩
    rw [ih (T ∩ (B j)ᶜ) hT' (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
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

/-- **`P(O)` er produktet av blokkfaktorene.** -/
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

#print axioms Identification.CFactor.Q_split
#print axioms Identification.CFactor.Q_prod
#print axioms Identification.CFactor.marginal_prod

/-! ## Runde 27: Tians teorem for mengder, én sum per c-komponent

Runde 25 krevde at ingen node i `X` hadde barn i *unionen* av c-komponentene til `X`.
Det er for strengt: i `x₁ → z ↔ x₂` med `X = {x₁, x₂}` har `x₁` et barn i c-komponenten
til `x₂`, men effekten er identifiserbar. Her får hver blokk sin egen sum:

  `P_X(a) = ∏_i [a_{X ∩ Bᵢ} = x] · Σ_{x'} Q[Bᵢ](a[X ∩ Bᵢ := x'])`   (`tian_formula_blocks`).

Kjerner i `Bᵢ` som leser noder i `X` utenfor `Bᵢ`, ser bare de faste verdiene. Kravet er
derfor bare at ingen `x ∈ X` har et barn i *sin egen* c-komponent
(`tian_identifiable_sets`). For én `x` er dette nøyaktig `tian_iff`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Faktoren for en blokk `T` i intervensjonsmodellen, for vilkårlig `X`. -/
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

/-- Summen over verdiene til `X ∩ T` fjerner kjernene til `X ∩ T` fra `Q[T]`. -/
lemma sum_block [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T X : Finset V)
    (hXO : X ⊆ Uᶜ) (hch : ∀ x ∈ T ∩ X, ∀ v ∈ T, ¬ G.edge x v) (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) (T ∩ X), Q M U T (updX U (T ∩ X) a x') =
      ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T \ X, kfac M Finset.univ (fill U T a w) v := by
  rw [sum_Q_updX M U T (T ∩ X) (fun v hv => hXO (Finset.mem_inter.mp hv).2)
    Finset.inter_subset_left hch a, Finset.sdiff_inter_self_left]

/-- **Formelen med én sum per blokk.** -/
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

/-- **Identifiserbarhet med blokker.** -/
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

lemma latStep_symm {U : Finset V} {a b : V} (h : latStep G U a b) : latStep G U b a :=
  Or.symm h

/-- To noder i samme c-komponent har samme c-komponent. -/
lemma ccomp_eq_of_mem {U : Finset V} {x v : V} (h : v ∈ ccomp G U x) :
    ccomp G U v = ccomp G U x := by
  have hsymm : Symmetric (Relation.ReflTransGen (latStep G U)) :=
    Relation.ReflTransGen.symmetric (fun _ _ h => latStep_symm h)
  have hxv := mem_ccomp.mp h
  ext w
  rw [mem_ccomp, mem_ccomp]
  exact ⟨fun hvw => hxv.trans hvw, fun hxw => (hsymm hxv).trans hxw⟩

/-- **Tians teorem for mengder.** Har ingen `x ∈ X` et barn i sin egen c-komponent, er
effekten av `X` på enhver mengde observerte `Y` identifiserbar. -/
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

#print axioms Identification.CFactor.tian_formula_blocks
#print axioms Identification.CFactor.tian_identifiable_blocks
#print axioms Identification.CFactor.tian_identifiable_sets

/-! ## Runde 28: hver faktor er en kausal effekt (`Q[S] = P_{do(O ∖ S)}`)

ID-algoritmens linje 4 og 7 kaller seg selv på faktorene `Q[Sᵢ]`. Det gir bare mening fordi
hver faktor er en kausal effekt: fastholdes alle observerte utenfor en lukket blokk `S`,
er fordelingen på de observerte nettopp `Q[S]` (`Q_causal`):

  `P_{do(X = x)}(O = a) = [a_X = x] · Q[S](a)`,   `X = Sᶜ ∖ U`.

1. `lat_one`: summert over de latente i en mengde er produktet av deres kjerner 1. Det
   følger direkte av `sum_compl_kfac_eq_one` (kjedeegenskapen) ved å telle om
   (`fill_iff`).
2. I intervensjonsmodellen er faktoren for `S` uendret, og faktoren for `Sᶜ` er
   indikatoren for `X` ganger kjernene til de latente i `Sᶜ`, som summerer til 1. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

lemma fill_out [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w w' : Assignment (α := α) (U ∩ T)) (v : V) (hv : v ∉ U ∩ T) :
    fill U T a w ⟨v, Finset.mem_univ v⟩ = fill U T a w' ⟨v, Finset.mem_univ v⟩ := by
  by_cases h0 : v ∈ U
  · have hT : v ∉ T := fun h => hv (Finset.mem_inter.mpr ⟨h0, h⟩)
    simp [fill, h0, hT]
  · simp [fill, h0]

/-- En full tilordning er en `fill` nøyaktig når den stemmer med `fill` utenfor de latente
i `T`; da er `w` dens restriksjon. -/
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

/-- **De latente summerer til 1.** -/
theorem lat_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) :
    ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ U ∩ T, kfac M Finset.univ (fill U T a w) v = 1 := by
  have w0 : Assignment (α := α) (U ∩ T) := fun _ => Classical.arbitrary _
  have key := sum_compl_kfac_eq_one M (U ∩ T)ᶜ
    ((fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ))
  rw [compl_compl] at key
  refine Eq.trans ?_ key
  symm
  calc ∑' u : Assignment (α := α) (Finset.univ : Finset V),
        (if u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
          (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ) then (1 : ENNReal) else 0) *
          ∏ v ∈ U ∩ T, kfac M Finset.univ u v
      = ∑' u : Assignment (α := α) (Finset.univ : Finset V),
          ∑' w : Assignment (α := α) (U ∩ T),
            (if u = fill U T a w then ∏ v ∈ U ∩ T, kfac M Finset.univ u v else 0) := by
        refine tsum_congr (fun u => ?_)
        by_cases hu : u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
            (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ)
        · rw [if_pos hu, one_mul, tsum_eq_single (u.restrict (Finset.subset_univ (U ∩ T)))]
          · rw [if_pos ((fill_iff U T a w0 _ u).mpr ⟨hu, rfl⟩)]
          · intro w hw
            rw [if_neg (fun h => hw ((fill_iff U T a w0 w u).mp h).2)]
        · rw [if_neg hu, zero_mul]
          symm
          exact ENNReal.tsum_eq_zero.mpr (fun w =>
            if_neg (fun h => hu ((fill_iff U T a w0 w u).mp h).1))
    _ = ∑' w : Assignment (α := α) (U ∩ T),
          ∑' u : Assignment (α := α) (Finset.univ : Finset V),
            (if u = fill U T a w then ∏ v ∈ U ∩ T, kfac M Finset.univ u v else 0) :=
        ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr (fun w => ?_)
        rw [tsum_eq_single (fill U T a w)]
        · simp
        · intro u hu
          rw [if_neg hu]

/-- **Hver faktor er en kausal effekt.** Fastholdes de observerte utenfor en lukket blokk
`S`, er fordelingen på de observerte indikatoren ganger `Q[S]`. -/
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

#print axioms Identification.CFactor.lat_one
#print axioms Identification.CFactor.Q_causal

/-! ## Runde 29: rydding — runde 25 som korollarer

`tian_identifiable_sets` (runde 27) er det generelle teoremet for mengder. Teoremene fra
runde 25 følger av det: en lukket blokk `S ⊇ X` inneholder c-komponenten til hver `x ∈ X`
(`ccomp_subset`), og unionen av c-komponentene inneholder hver av dem. `tian_formulaX` og
`Q_doX` er fjernet; `tian_formula_blocks` og `Q_do_gen` dekker dem. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Tians teorem for en mengde `X` i en lukket blokk.** -/
theorem tian_identifiableX [∀ v, Nonempty (α v)] (U S X : Finset V)
    (hXO : X ⊆ Uᶜ) (hXS : X ⊆ S) (hch : ∀ x ∈ X, ∀ v ∈ S, ¬ G.edge x v)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X (fun _ hx => Finset.mem_compl.mp (hXO hx))
    (fun x hx v hv => hch x hx v (ccomp_subset hcl (hXS hx) hv)) Y hY

/-- **Med unionen av c-komponentene.** -/
theorem tian_identifiable_ccompX [∀ v, Nonempty (α v)] (U X : Finset V)
    (hX : ∀ x ∈ X, x ∉ U) (hch : ∀ x ∈ X, ∀ v ∈ X.biUnion (ccomp G U), ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X hX
    (fun x hx v hv => hch x hx v (Finset.mem_biUnion.mpr ⟨x, hx, hv⟩)) Y hY

end CFactor
end Identification

#print axioms Identification.CFactor.tian_identifiableX
#print axioms Identification.CFactor.tian_identifiable_ccompX

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
    all_goals rfl
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
      all_goals rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · simp only [updX, dif_pos hv, Assignment.restrict]
        all_goals rfl
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]
      all_goals rfl

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
