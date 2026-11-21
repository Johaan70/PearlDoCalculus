import PearlDoCalculus.Completeness.SingleRules

/-!
# Completeness of d-separation: the set versions of the do-rules

Builds on the single-node rules (`Completeness/SingleRules.lean`). It lifts
the completeness results from single nodes to sets: d-separation of sets is
equivalent to d-separation of all pairs of nodes, and rules 1 and 2 hold as
equivalences for sets. Rule 3 for sets is shown here when no `z ∈ Z` is an
ancestor of `W`; the general case is in `Completeness/Rule3SetFull.lean`.

Main results: `dsepSet_iff`, `rule1_iff_set`, `rule2_iff_set`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Dekomponering og mengdeversjonene -/

section SetVersions
open DoCalculus

/-- **Symmetri.** -/
lemma condIndep_symm {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (h : CondIndep M X Y Z) : CondIndep M Y X Z := by
  intro w
  rw [marginal_eq_restrict_of_subset_of_subset M (S := X ∪ Y ∪ Z) (T := Y ∪ X ∪ Z)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto),
    mul_comm (M.marginal (Y ∪ Z) _)]
  exact h _

/-- **Dekomponering, høyre side.** Er `X ⊥ Y | Z` og `Y' ⊆ Y`, så er `X ⊥ Y' | Z`. -/
lemma condIndep_drop_right {G : DAG V} {α : V → Type*} (M : G.CausalModel α)
    [∀ w, Nonempty (α w)] {X Y Y' Z : Finset V}
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z) (hY' : Y' ⊆ Y) (h : CondIndep M X Y Z) :
    CondIndep M X Y' Z := by
  have h1 := Finset.disjoint_left.mp hXY
  have h2 := Finset.disjoint_left.mp hYZ
  have hBA : X ∪ Y' ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDA : Y \ Y' ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hBD : Disjoint (X ∪ Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with (hv | hv) | hv
    · exact h1 hv hv'.1
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB : X ∪ Y ∪ Z ⊆ X ∪ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hYZA : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDYZ : Y \ Y' ⊆ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hB2 : Y' ∪ Z ⊆ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hBD2 : Disjoint (Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with hv | hv
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB2 : Y ∪ Z ⊆ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hZD : Disjoint Z (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact h2 (Finset.mem_sdiff.mp hv').1 hv
  have hXZD : Disjoint (X ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h1 hv (Finset.mem_sdiff.mp hv').1
    · exact h2 (Finset.mem_sdiff.mp hv').1 hv
  intro b
  obtain ⟨a, rfl⟩ := Assignment.restrict_surjective hBA b
  have e1 : M.marginal (X ∪ Y' ∪ Z) (a.restrict hBA) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (X ∪ Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d) :=
    (Rule3Flag.marginal_sum_Z M hDA hBA hBD hAB a).symm
  have e2 : M.marginal (Y' ∪ Z) ((a.restrict hBA).restrict
        (show Y' ∪ Z ⊆ X ∪ Y' ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (Y ∪ Z) (a.restrict hYZA) d) :=
    (Rule3Flag.marginal_sum_Z M hDYZ hB2 hBD2 hAB2 (a.restrict hYZA)).symm
  rw [e1, e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun d => ?_)
  have hci := h (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d)
  rw [Rule3Flag.setZ_restrict_disj _ hZD a d, Rule3Flag.setZ_restrict_disj _ hXZD a d] at hci
  exact hci

/-- **Dekomponering til enkeltnoder.** -/
lemma condIndep_single {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : CondIndep M X Y Z) {x y : V} (hx : x ∈ X) (hy : y ∈ Y) :
    CondIndep M {x} {y} Z := by
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have h1 := condIndep_drop_right M hXY hYZ (Finset.singleton_subset_iff.mpr hy) h
  have hyX : Disjoint ({y} : Finset V) X :=
    Finset.disjoint_singleton_left.mpr (fun hyX => Finset.disjoint_left.mp hXY hyX hy)
  exact condIndep_symm M (condIndep_drop_right M hyX hXZ
    (Finset.singleton_subset_iff.mpr hx) (condIndep_symm M h1))

/-- **d-separasjon av mengder ⇔ uavhengighet i alle modeller.** -/
theorem dsepSet_iff (G : DAG V) (Z X Y : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hXY : Disjoint X Y) :
    SetSound.DSeparatedSet G Z X Y ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool)), CondIndep M X Y Z := by
  constructor
  · intro h k M
    exact SetSound.dsep_sound_set M X Y Z hXZ hYZ h
  · intro H
    by_contra hn
    simp only [SetSound.DSeparatedSet, not_forall] at hn
    obtain ⟨x, hx, y, hy, hn⟩ := hn
    obtain ⟨k, M, hM⟩ := dsep_complete G Z x y (Finset.disjoint_left.mp hXZ hx)
      (Finset.disjoint_left.mp hYZ hy)
      (fun e => Finset.disjoint_left.mp hXY hx (by rw [e]; exact hy))
      (fun hd => hn (dsepPath_of_dsep hd))
    exact hM (condIndep_single M hXY hXZ hYZ (H k M) hx hy)

/-- **Fullstendighet for regel 1 med mengder.** -/
theorem rule1_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) Y Z (X ∪ W) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨k, M, x, hM⟩ := rule1_complete G X W y z (Finset.disjoint_left.mp hY hy)
    (Finset.disjoint_left.mp hZ hz)
    (fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz))
    (fun hd => hn (dsepPath_of_dsep hd))
  exact ⟨k, M, x, fun hci => hM (condIndep_single _ hYZ hY hZ hci hy hz)⟩

/-- **Regel 1 er eksakt, i nøyaktig den formen `rule1` har.** -/
theorem rule1_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X),
        CondIndep (doModel M X x) Y Z (X ∪ W) := by
  constructor
  · intro h k M x
    exact rule1 M X W Y Z x hY hZ h
  · intro H
    by_contra hn
    obtain ⟨k, M, x, hM⟩ := rule1_complete_set G X W Y Z hY hZ hYZ hn
    exact hM (H k M x)

end SetVersions

/-! ## Regel 2 for mengder -/

section Rule2Set
open DoCalculus

/-- **Fullstendighet for regel 2 med mengder.** -/
theorem rule2_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ ∧
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutOut (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutOut (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w.restrict hzs, w, rfl, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, Disjoint S Z →
      (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
        Z (w.restrict hzs)).marginal S = (chainModel C').marginal S := by
    intro S hS
    rw [marginal_eq_of_kfac _ (doModel (chainModel C') Z (w.restrict hzs))
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN)]
    refine PMF.ext fun s => Rule3.doModel_marginal_of_sub (chainModel C') Z _
      (Finset.univ \ Z) ?_ Finset.sdiff_disjoint S ?_ s
    · intro v _ w' e
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e.2⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, Finset.disjoint_left.mp hS hv⟩
  rw [hB (X ∪ W) hZ.symm, hB (Y ∪ (X ∪ W)) (Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩),
    hA, hA]
  exact hw

/-- **Regel 2 er eksakt, i nøyaktig den formen `rule2` har.** -/
theorem rule2_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ →
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x z₀ t ht
    exact rule2 M X Y Z W x z₀ hYZ hZ.symm hY h t ht
  · intro H
    by_contra hn
    obtain ⟨k, M, x, z₀, t, ht, hne⟩ := rule2_complete_set G X W Y Z hY hZ hYZ hn
    exact hne (H k M x z₀ t ht)

end Rule2Set

/-! ## Regel 3 for mengder, når ingen `z ∈ Z` er forfar til `W` -/

section Rule3Set
open DoCalculus

lemma walk_to_isolated_set {H : DAG V} {Z : Finset V}
    (hiso : ∀ z ∈ Z, ∀ u, ¬ H.edge u z ∧ ¬ H.edge z u) :
    ∀ {a b : V} (p : Walk H a b), b ∈ Z → a ∈ Z := by
  intro a b p
  induction p with
  | nil v =>
    intro h
    exact h
  | @fwd a b' _ e p ih =>
    intro hc
    exact absurd e (hiso b' (ih hc) a).1
  | @bwd a b' _ e p ih =>
    intro hc
    exact absurd e (hiso b' (ih hc) a).2

lemma dsep_isolated_set {H : DAG V} {Z : Finset V} (hnp : ∀ z ∈ Z, ∀ u, ¬ H.edge u z)
    (S : Finset V) (hS : Disjoint S Z) :
    SetSound.DSeparatedSet (cutOut H Z) ∅ S Z := by
  have hiso : ∀ z ∈ Z, ∀ u, ¬ (cutOut H Z).edge u z ∧ ¬ (cutOut H Z).edge z u :=
    fun z hz u => ⟨fun e => hnp z hz u e.1, fun e => e.2 hz⟩
  intro s hs z' hz' p _
  exfalso
  exact Finset.disjoint_left.mp hS hs (walk_to_isolated_set hiso p hz')

lemma Z2_all {H : DAG V} {Z W : Finset V} (h : ∀ z ∈ Z, z ∉ ancestors H W) :
    Rule3.Z2 H Z W = Z := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter]
  constructor
  · exact fun hv => hv.1
  · intro hv
    exact ⟨hv, h v hv⟩

/-- **Fullstendighet for regel 3 med mengder, når ingen `z ∈ Z` er forfar til `W`.** -/
theorem rule3_complete_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  rw [Z2_all hanc] at h
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ z ∈ Z, ∀ u, ¬ (cutIn (cutIn G X) Z).edge u z :=
    fun z hz u e => e.2 hz
  have hYXWZ : Disjoint (Y ∪ (X ∪ W)) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩
  have fa : (chainModel C').marginal (Y ∪ Z ∪ (X ∪ W)) w =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (Y ∪ (X ∪ W))
        (w.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := Y ∪ (X ∪ W) ∪ Z)
      (T := Y ∪ Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (Y ∪ (X ∪ W)) hYXWZ
      (dsep_isolated_set hnp _ hYXWZ) _
  have fd : (chainModel C').marginal (Z ∪ (X ∪ W))
        (w.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := X ∪ W ∪ Z)
      (T := Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (X ∪ W) hZ.symm
      (dsep_isolated_set hnp _ hZ.symm) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      Z (w.restrict hzs)).marginal S =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

/-- **Regel 3 er eksakt for mengder når ingen `z ∈ Z` er forfar til `W`.** -/
theorem rule3_iff_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W) :
    SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x t
    exact Rule3Flag.rule3_general M X Y Z W x hYZ hZ.symm hY h t
  · intro H
    by_contra hn
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_set_nonanc G X W Y Z hY hZ hYZ hanc hn
    exact hne (H k M x t)

/-- **Regel 3 svikter for mengder når `Y` og `Z` er d-forbundet i `G_{X̄Z̄}`.** -/
theorem rule3_complete_set_root (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ z ∈ Z, ∀ u, ¬ (cutIn (cutIn G X) Z).edge u z :=
    fun z hz u e => e.2 hz
  have hYXWZ : Disjoint (Y ∪ (X ∪ W)) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩
  have fa : (chainModel C').marginal (Y ∪ Z ∪ (X ∪ W)) w =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (Y ∪ (X ∪ W))
        (w.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := Y ∪ (X ∪ W) ∪ Z)
      (T := Y ∪ Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (Y ∪ (X ∪ W)) hYXWZ
      (dsep_isolated_set hnp _ hYXWZ) _
  have fd : (chainModel C').marginal (Z ∪ (X ∪ W))
        (w.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := X ∪ W ∪ Z)
      (T := Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (X ∪ W) hZ.symm
      (dsep_isolated_set hnp _ hZ.symm) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      Z (w.restrict hzs)).marginal S =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

end Rule3Set

end Completeness
