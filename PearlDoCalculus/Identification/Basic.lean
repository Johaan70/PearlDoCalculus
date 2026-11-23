import PearlDoCalculus.Completeness
import PearlDoCalculus.Util.Finset

/-!
# Identifiability with latent variables: the definition and the easy cases

Only the nodes in `O` are observed. The effect of `do(X)` on `Y` is **identifiable**
from `O` in `G` if two models on `G` with the same positive distribution on `O` always
give the same intervention distribution on `Y`. This is the definition of Pearl and of
Shpitser–Pearl, with positivity as used in the literature.

Why it is needed: `Identifiable` is the notion that the whole identification layer is
about. The positive results (Tian's theorem in `CFactor`/`TianIff`, the soundness of
`IdAlgo.idCheck` in `IdSound`, `Idc`) conclude it, and the negative ones (the bow in
`Bow`, the hedge families in this folder, the hedge criterion in `Hedge/*`) refute it.
`Identifiable.mono_Y` is used by `RootTree` and `TianIff` (non-identifiability for a
subset of `Y` gives it for `Y`). The other results here are the textbook easy cases;
no other file uses them.

How the proofs go: back-door and front-door rewrite both sides with the adjustment
formulas of `Adjustment` and note that these only use the observed marginals, which agree.
In the fully observed case every kernel factor `P(v | pa(v))` is a ratio of two positive
marginals of ancestral sets, so it is fixed by the joint distribution, and the truncated
factorization of `doModel` gives the claim. Passing to a subset `Y' ⊆ Y` is
marginalization of equal distributions.

Main results:

* `Identification.Identifiable`: the definition.
* `Identification.backdoor_identifiable`, `Identification.frontdoor_identifiable`:
  the back-door and front-door criteria give identifiability when `X`, `Y` and `Z` are
  observed, whatever other nodes are latent.
* `Identification.Identifiable.mono`: more observed nodes never hurt.
* `Identification.observed_identifiable`: with every node observed, every effect is
  identifiable.
* `Identification.Identifiable.mono_Y` and `Identification.not_identifiable_of_mem`:
  identifiability passes to subsets of `Y`, so non-identifiability of one `y` gives it
  for every `Y` containing `y` (with `Y` and `X` disjoint).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Identifiability.** `P(Y | do(X))` is determined by the observed distribution on `O`:
any two models on `G` with the same marginal on `O`, positive everywhere, give the same
`P(Y = t_Y | do(X = t_X))` for every assignment `t` of `Y ∪ X`. -/
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

/-- **Back-door gives identifiability.** If `Z` satisfies the back-door criterion and
`X`, `Y` and `Z` are observed, then `P(Y | do(X))` is identifiable. -/
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
  obtain ⟨t', ht'⟩ := Assignment.restrict_surjective hsub t
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
      (fun z => marginal_ne_zero_of_subset hpos hXZO _),
    Adjustment.backdoor_adjustment_criterion M₂ X Y Z hYX hZX hYZ hcrit t'
      (fun z => marginal_ne_zero_of_subset hpos₂ hXZO _),
    marginal_eq_of_subset hM hO, marginal_eq_of_subset hM hZO, marginal_eq_of_subset hM hXZO]

/-- **Front-door gives identifiability.** If `Z` satisfies the front-door criterion and
`X`, `Y` and `Z` are observed, then `P(Y | do(X))` is identifiable, even when everything
else (for example a common cause of `X` and `Y`) is latent. -/
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
  obtain ⟨t', ht'⟩ := Assignment.restrict_surjective hsub t
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
      (marginal_ne_zero_of_subset hpos hXO _) (fun z x' => marginal_ne_zero_of_subset hpos hZXO _),
    Adjustment.frontdoor_adjustment_criterion M₂ X Y Z hZX hYX hYZ hc t'
      (marginal_ne_zero_of_subset hpos₂ hXO _) (fun z x' => marginal_ne_zero_of_subset hpos₂ hZXO _),
    marginal_eq_of_subset hM hXO, marginal_eq_of_subset hM hZXO, marginal_eq_of_subset hM hYZXO]

end Identification

/-! ## Monotonicity in `O` and fully observed models -/

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- More observed nodes do not make identification harder. -/
theorem Identifiable.mono {G : DAG V} {α : V → Type*} {O O' X Y : Finset V} (hOO : O ⊆ O')
    (h : Identifiable G α O X Y) [∀ w, Nonempty (α w)] : Identifiable G α O' X Y := by
  unfold Identifiable at h ⊢
  intro M₁ M₂ hM hpos t
  exact h M₁ M₂ (marginal_eq_of_subset hM hOO) (marginal_ne_zero_of_subset hpos hOO) t

/-- `v` together with all its ancestors. -/
noncomputable def ancSelf (G : DAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Reaches w v)

/-- `ancSelf G v` is ancestral: it contains the parents of each of its members. -/
lemma ancSelf_closed (G : DAG V) (v : V) :
    ∀ u ∈ ancSelf G v, ∀ w, G.edge w u → w ∈ ancSelf G v := by
  intro u hu w hw
  simp only [ancSelf, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact Relation.ReflTransGen.head hw hu

/-- The ancestors of `v` without `v` itself still form an ancestral set, since `v` is not an
ancestor of any of its ancestors. -/
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

/-- `v` belongs to `ancSelf G v`. -/
lemma mem_ancSelf (G : DAG V) (v : V) : v ∈ ancSelf G v := by
  simp only [ancSelf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.ReflTransGen.refl

/-- **The kernel factors are determined by the positive joint distribution.** Two models
with the same joint distribution, positive everywhere, have the same factor
`P(v = u_v | pa(v) = u_pa)` at every full assignment `u`: it is the quotient of the
marginals on the ancestral sets `ancSelf G v` and `(ancSelf G v).erase v`. -/
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
  have hA12 := marginal_eq_of_subset hM (Finset.subset_univ (ancSelf G v))
  have hB12 := marginal_eq_of_subset hM (Finset.subset_univ ((ancSelf G v).erase v))
  have e := split M₁
  rw [hA12, split M₂, hB12] at e
  have hP0 : M₂.marginal ((ancSelf G v).erase v) (a.restrict hBA) ≠ 0 := by
    rw [← hB12]
    exact marginal_ne_zero_of_subset hpos (Finset.subset_univ _) _
  have hPT : M₂.marginal ((ancSelf G v).erase v) (a.restrict hBA) ≠ ⊤ := PMF.apply_ne_top _ _
  have hk : kfac M₁ (ancSelf G v) a v = kfac M₂ (ancSelf G v) a v :=
    by
      exact ((ENNReal.mul_left_inj hP0 hPT).mp e).symm
  rw [← kfac_restrict M₁ (Finset.subset_univ _) u hvA hpaA,
    ← kfac_restrict M₂ (Finset.subset_univ _) u hvA hpaA]
  exact hk

/-- **Fully observed implies identifiable.** If every node is observed, every
intervention distribution is determined by the positive joint distribution (truncated
factorization). -/
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

/-! ## From one `y` to a set `Y`

If `P(Y | do(X))` is identifiable and `Y' ⊆ Y` (with `Y` and `X` disjoint), then
`P(Y' | do(X))` is identifiable too: marginalization preserves equality. So
non-identifiability for one `y` gives non-identifiability for every `Y` that contains
`y`. -/

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Identifiability passes to subsets of `Y`.** -/
theorem Identifiable.mono_Y {G : DAG V} {α : V → Type*} {O X Y Y' : Finset V}
    (hd : Disjoint Y X) (hY : Y' ⊆ Y) (h : Identifiable G α O X Y) :
    Identifiable G α O X Y' := by
  intro M₁ M₂ hM hpos t
  have hP : ∀ x0 : Assignment (α := α) X,
      (doModel M₁ X x0).marginal Y = (doModel M₂ X x0).marginal Y := by
    intro x0
    ext a
    have e := h M₁ M₂ hM hpos (a.join x0)
    rw [Assignment.restrict_join_right a x0
        (fun v hY hX => (Finset.disjoint_left.mp hd hY hX).elim),
      Assignment.restrict_join_left] at e
    exact e
  rw [← marginal_restrict (doModel M₁ X _) hY, ← marginal_restrict (doModel M₂ X _) hY, hP]

/-- Non-identifiability for one `y` gives it for every `Y ∋ y` disjoint from `X`. -/
theorem not_identifiable_of_mem {G : DAG V} {α : V → Type*} {O X Y : Finset V} {y : V}
    (h : ¬ Identifiable G α O X {y}) (hy : y ∈ Y) (hd : Disjoint Y X) :
    ¬ Identifiable G α O X Y :=
  fun hY => h (hY.mono_Y hd (Finset.singleton_subset_iff.mpr hy))

end Identification
