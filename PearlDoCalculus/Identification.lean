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
