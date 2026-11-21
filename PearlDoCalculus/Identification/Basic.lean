import PearlDoCalculus.Completeness
import PearlDoCalculus.Util.Finset

/-!
# Identifiability with latent variables: the definition and the easy cases

Only the nodes in `O` are observed. The effect of `do(X)` on `Y` is **identifiable**
from `O` in `G` if two models on `G` with the same positive distribution on `O` always
give the same intervention distribution on `Y`. This is the definition of Pearl and of
Shpitser–Pearl, with positivity as used in the literature.

Main results:

* `Identification.Identifiable`: the definition.
* Back-door and front-door criteria give identifiability when `X`, `Y` and `Z` are
  observed, whatever other nodes are latent (round 1), and further fully observed
  cases (round 2).
* `Identification.Parents.parents_identifiable`: a treatment with only observed
  parents is identifiable (Tian's case where the c-component of `x` is `{x}`).
* `Identification.Identifiable.mono_Y` and `Identification.not_identifiable_of_mem`:
  identifiability passes to subsets of `Y`, so non-identifiability of one `y` gives it
  for every `Y` containing `y` (with `Y` and `X` disjoint).

The comments inside the file still carry the work round in which a block was written.
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

lemma ancSelf_erase_closed (G : DAG V) (v : V) :
    ∀ u ∈ (ancSelf G v).erase v, ∀ w, G.edge w u → w ∈ (ancSelf G v).erase v := by
  intro u hu w hw
  rw [Finset.mem_erase] at hu ⊢
  refine ⟨fun hwv => ?_, ancSelf_closed G v u hu.2 w hw⟩
  rw [hwv] at hw
  have hr : G.Reaches u v := by
    simpa [ancSelf] using hu.2
  have h1 := G.rank_le_of_reaches hr
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
  have hpaA : G.parents v ⊆ ancSelf G v := DAG.parents_subset_of_closed hA v hvA
  set a := u.restrict (Finset.subset_univ (ancSelf G v)) with ha
  have split : ∀ M : G.CausalModel α, M.marginal (ancSelf G v) a =
      kfac M (ancSelf G v) a v * M.marginal ((ancSelf G v).erase v) (a.restrict hBA) := by
    intro M
    rw [marginal_ancestral_apply M _ hA a, marginal_ancestral_apply M _ hB (a.restrict hBA),
      ← Finset.mul_prod_erase _ _ hvA]
    congr 1
    refine Finset.prod_congr rfl (fun w hw => ?_)
    have hpaw : G.parents w ⊆ (ancSelf G v).erase v := DAG.parents_subset_of_closed hB w hw
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
      exact ((ENNReal.mul_left_inj hP0 hPT).mp e).symm
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


open scoped ENNReal

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
          exact Or.inl (by simp [DAG.parents, e])
        | bwd =>
          exact Or.inl (by simp [DAG.parents, e])
      | fwd _ _ => simp [Adjustment.wIsNil] at hq
      | bwd _ _ => simp [Adjustment.wIsNil] at hq
    · have h' : Adjustment.wIsNil q = true ∨ Adjustment.endsInto q := by
        exact h
      have ihr := ih .fwd (h'.resolve_left hq) (by intro hc; cases hc)
      cases inc with
      | start => exact ihr
      | fwd => exact Or.inr ihr
      | bwd => exact Or.inr ihr
  | bwd e q ih =>
    intro inc h _
    have h' : Adjustment.wIsNil q = false ∧ Adjustment.endsInto q := by
      exact h
    have ihr := ih .bwd h'.2 (by intro hc; cases hc)
    cases inc with
    | start => exact ihr
    | fwd => exact Or.inr ihr
    | bwd => exact Or.inr ihr

/-- Ingen forelder er etterkommer av barnet. -/
lemma not_reaches_parent {G : DAG V} {x z : V} (hz : z ∈ G.parents x) :
    ¬ G.Reaches x z := by
  intro hr
  have he : G.edge z x := DAG.mem_parents.mp hz
  have h1 := G.rank_le_of_reaches hr
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

end Identification

#print axioms Identification.not_identifiable_of_mem
