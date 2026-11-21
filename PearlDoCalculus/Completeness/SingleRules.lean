import PearlDoCalculus.Completeness.Chain

/-!
# Completeness of the do-rules for single vertices

**What it proves.** For single vertices `y` and `z` (and sets `X`, `W`), Pearl's rules are
exact: the graphical condition holds if and only if the equation of the rule holds in every
model on `G` and for all values. This is proved for rule 1 (`rule1_iff`), rule 2
(`rule2_iff`) and rule 3 when `z` is not an ancestor of `W` (`rule3_iff_nonanc`). The
failure directions are `rule1_complete`, `rule2_complete`, `rule3_complete_nonanc`, and
`rule3_complete_root`, which refutes rule 3 whenever `y` and `z` are d-connected in
`G_{X̄z̄}`.

**Why it is needed.** This is the step from the completeness of d-separation
(`Completeness/Chain.lean`) to the completeness of the do-calculus. The set versions
(`Completeness/SetRules.lean`) and rule 3 in all cases (`Completeness/Rule3Full.lean`, which
uses `rule3_complete_nonanc` and `rule3_complete_root`) build on it. The lifting tools of
this file, `liftSub` (a model on a subgraph seen as a model on the larger graph), its kernel
factors (`kfac_liftSub`, `kfac_doModel_liftSub`), the factorisation lemma
`marginal_eq_of_kfac` and `dsep_isolated`, are also used by every hedge counter-model of
`Identification` (`Bow`, `HedgeChain`, `HedgeTemplate`, `RootPathModels`, `RootPath`).

**How the proof goes.** Each condition is d-separation in a mutilated graph `H`
(`G_{X̄}`, `G_{X̄z̲}` or `G_{X̄z̄}`) whose parent sets are contained in those of `G`. If it
fails, `Completeness/Chain.lean` gives a chain model on `H` in which `y` and `z` are
dependent given `X ∪ W`. The vertices of `X` have no parents in `H`, so they are constant
`false` in that model (`chain_X_false`, `chain_noparent_false`). Lifted to `G` (`liftModel`,
`liftSub`: the kernels ignore the extra parents), the model under `do(X = false)` has the
same kernel factors and hence the same marginals (`marginal_eq_of_kfac`, `lift_do_kfac`,
`lift_do_do_kfac`). For rule 1 that already is the failure. For rule 2, `z` has no children
in `G_{X̄z̲}`, so `do(z)` leaves every marginal without `z` unchanged and the product form
of rule 2 reduces to conditional independence. For rule 3, `z` is a root of `G_{X̄z̄}`, and
for a root, setting `z` is the same as conditioning on `z` (front-door step 1 with
`dsep_isolated`), so again the product form reduces to conditional independence. When
`z ∉ An(W)` the graph of rule 3 is `G_{X̄z̄}` (`Z2_singleton`).

**Main results.** `rule1_iff`, `rule2_iff`, `rule3_iff_nonanc`, `rule1_complete`,
`rule2_complete`, `rule3_complete_nonanc`, `rule3_complete_root`, and the shared tools
`liftSub`, `kfac_liftSub`, `kfac_doModel_liftSub`, `marginal_eq_of_kfac`, `dsep_isolated`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Completeness of rule 1 -/

section Rule1
open DoCalculus

/-- Cutting the edges into `X` only removes parents. -/
lemma parents_cutIn_sub {G : DAG V} (X : Finset V) (v : V) :
    (cutIn G X).parents v ⊆ G.parents v := by
  intro u hu
  simp only [DAG.mem_parents] at hu ⊢
  exact hu.1

/-- A model on `G_{X̄}` lifted to `G`: the kernels ignore the parents along edges into
`X`. -/
noncomputable def liftModel {G : DAG V} {X : Finset V} {α : V → Type*}
    (N : (cutIn G X).CausalModel α) : G.CausalModel α where
  fin := N.fin
  deq := N.deq
  kernel := fun v pa => N.kernel v (fun u => pa ⟨u.1, parents_cutIn_sub X v u.2⟩)

/-- If every `X` kernel of `N` is the point mass at `x`, then `do(X = x)` in the lifted
model equals `N`. -/
theorem doModel_lift {G : DAG V} {X : Finset V} {α : V → Type*}
    (N : (cutIn G X).CausalModel α) (x : Assignment (α := α) X)
    (hX : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩)) :
    doModel (liftModel N) X x = N := by
  obtain ⟨fin, deq, ker⟩ := N
  simp only [doModel, liftModel, CausalModel.mk.injEq, true_and]
  funext v p
  split_ifs with hv
  · exact (hX v hv p).symm
  · rfl

/-- In the chain model on `G_{X̄}` with conditioning set `X ∪ W`, the vertices of `X` are
constant `false`: they have no parents, so they cannot be XOR vertices. -/
lemma chain_X_false {G : DAG V} {X W : Finset V} {y z : V}
    (C : Chain (cutIn G X) (X ∪ W) y z) :
    ∀ v (hv : v ∈ X) p, (chainModel C).kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X)
        ⟨v, hv⟩) := by
  intro v hv p
  simp only [chainModel]
  rw [if_pos (Finset.mem_union_left W hv), dif_neg]
  rintro ⟨j, hj⟩
  obtain ⟨q, hq, _⟩ := C.hl j
  rw [hj] at hq
  simp only [DAG.mem_parents] at hq
  exact hq.2 hv

/-- **Completeness of rule 1.** If `y` and `z` are not d-separated given `X ∪ W` in
`G_{X̄}`, there are a model on `G` and a value `x` for which
`P_x(y | z, x, w) = P_x(y | x, w)` fails. -/
theorem rule1_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn G X).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) {y} {z} (X ∪ W) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn G X) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  refine ⟨C'.k, liftModel (chainModel C'), fun _ _ => false, ?_⟩
  rw [doModel_lift (chainModel C') (fun _ _ => false) (chain_X_false C')]
  exact chain_not_condIndep C' hinj hyz

end Rule1

/-! ## Lifted models and the completeness of rule 2 -/

section Rule2
open DoCalculus

/-- Equal kernel factors give equal marginals, also on different graphs. -/
lemma marginal_eq_of_kfac {G1 G2 : DAG V} {α : V → Type*}
    (M1 : G1.CausalModel α) (M2 : G2.CausalModel α)
    (h : ∀ (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V),
      kfac M1 Finset.univ u v = kfac M2 Finset.univ u v)
    (S : Finset V) : M1.marginal S = M2.marginal S := by
  have hj : M1.fullJoint = M2.fullJoint := PMF.ext fun u => by
    rw [fullJoint_apply_prod, fullJoint_apply_prod]
    exact Finset.prod_congr rfl (fun v _ => h u v)
  unfold CausalModel.marginal
  rw [hj]

/-- Lift from a subgraph: the kernels ignore the parents that exist only in `G`. -/
noncomputable def liftSub {G H : DAG V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α) : G.CausalModel α where
  fin := N.fin
  deq := N.deq
  kernel := fun v pa => N.kernel v (fun u => pa ⟨u.1, hsub v u.2⟩)

/-- The lift has the same kernel factors as `N`. -/
lemma kfac_liftSub {G H : DAG V} {α : V → Type*} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (liftSub hsub N) Finset.univ w v = kfac N Finset.univ w v := by
  rw [kfac_univ, kfac_univ]
  rfl

/-- The lift has the same kernel factors as `N` also after an intervention `do(X = x)`. -/
lemma kfac_doModel_liftSub {G H : DAG V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (X : Finset V) (x : Assignment (α := α) X)
    (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (liftSub hsub N) X x) Finset.univ w v =
      kfac (doModel N X x) Finset.univ w v := by
  rw [kfac_univ, kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, liftSub] <;> rfl

/-- A vertex of the conditioning set without parents is constant `false` in the chain
model. -/
lemma chain_noparent_false {H : DAG V} {Z' : Finset V} {y z : V} (C : Chain H Z' y z)
    (v : V) (hvZ : v ∈ Z') (hnp : ∀ u, ¬ H.edge u v) :
    ∀ p, (chainModel C).kernel v p = PMF.pure (fun _ => false) := by
  intro p
  simp only [chainModel]
  rw [if_pos hvZ, dif_neg]
  rintro ⟨j, hj⟩
  obtain ⟨q, hq, _⟩ := C.hl j
  rw [hj] at hq
  simp only [DAG.mem_parents] at hq
  exact hnp q hq

/-- `do(X = x)` in the lifted model has the same kernel factors as `N`, when the `X`
kernels of `N` are already the point masses at `x`. -/
lemma lift_do_kfac {G H : DAG V} {X : Finset V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α)
    (x : Assignment (α := α) X)
    (hXN : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩))
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (liftSub hsub N) X x) Finset.univ u v = kfac N Finset.univ u v := by
  rw [kfac_univ, kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
    rw [hXN v hx]
  · simp only [doModel, dif_neg hx, liftSub] <;> rfl

/-- `do(X = x)` followed by `do(Z = z₀)` in the lifted model has the same kernel factors as
`do(Z = z₀)` in `N`, when the `X` kernels of `N` are the point masses at `x`. -/
lemma lift_do_do_kfac {G H : DAG V} {X Zs : Finset V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α)
    (x : Assignment (α := α) X) (z₀ : Assignment (α := α) Zs)
    (hXN : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩))
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (doModel (liftSub hsub N) X x) Zs z₀) Finset.univ u v =
      kfac (doModel N Zs z₀) Finset.univ u v := by
  rw [kfac_univ, kfac_univ]
  by_cases hz : v ∈ Zs
  · simp only [doModel, dif_pos hz]
  · by_cases hx : v ∈ X
    · simp only [doModel, dif_neg hz, dif_pos hx]
      rw [hXN v hx]
    · simp only [doModel, dif_neg hz, dif_neg hx, liftSub] <;> rfl

/-- **Completeness of rule 2.** If `y` and `z` are not d-separated given `X ∪ W` in
`G_{X̄z̲}`, there are a model on `G` and values for which the product form of `rule2`
fails. -/
theorem rule2_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutOut (cutIn G X) {z}).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) {z},
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ ∧
        (doModel M X x).marginal ({y} ∪ {z} ∪ (X ∪ W)) t *
          (doModel (doModel M X x) {z} z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel (doModel M X x) {z} z₀).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal ({z} ∪ (X ∪ W))
            (t.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutOut (cutIn G X) {z}) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hN := chain_not_condIndep C' hinj hyz
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutOut (cutIn G X) {z}).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w.restrict hzs, w, rfl, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN)
  have hB : ∀ S, z ∉ S → (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      {z} (w.restrict hzs)).marginal S = (chainModel C').marginal S := by
    intro S hS
    rw [marginal_eq_of_kfac _ (doModel (chainModel C') {z} (w.restrict hzs))
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN)]
    refine PMF.ext fun s => Rule3.doModel_marginal_of_sub (chainModel C') {z} _
      (Finset.univ.erase z) ?_ (by simp) S ?_ s
    · intro v _ w' e
      exact Finset.mem_erase.mpr ⟨fun hw' => e.2 (Finset.mem_singleton.mpr hw'), Finset.mem_univ _⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun e => hS (e ▸ hv), Finset.mem_univ v⟩
  have hz2 : z ∉ ({y} ∪ (X ∪ W) : Finset V) := fun hm =>
    (Finset.mem_union.mp hm).elim (fun e => hyz (Finset.mem_singleton.mp e).symm) hz
  rw [hB (X ∪ W) hz, hB ({y} ∪ (X ∪ W)) hz2, hA, hA]
  exact hw

end Rule2

/-! ## Completeness of rule 3 when `z` can be made a root

This covers the case `z ∉ An(W)` and, more generally, every case where `y` and `z` are
d-connected in `G_{X̄z̄}`. -/

section Rule3C
open DoCalculus

/-- In a graph where `z` has no edges, every walk that ends in `z` also starts in `z`. -/
lemma walk_to_isolated {H : DAG V} {z : V}
    (hiso : ∀ u, ¬ H.edge u z ∧ ¬ H.edge z u) :
    ∀ {a b : V} (p : Walk H a b), b = z → a = z := by
  intro a b p
  induction p with
  | nil v =>
    intro h
    exact h
  | @fwd a b' _ e p ih =>
    intro hc
    have h1 := ih hc
    rw [h1] at e
    exact absurd e (hiso a).1
  | @bwd a b' _ e p ih =>
    intro hc
    have h1 := ih hc
    rw [h1] at e
    exact absurd e (hiso a).2

/-- If `z` has no parents in `H`, then `z` is isolated in `H_{z̲}`, and hence d-separated
from every set without `z`, given `∅`. -/
lemma dsep_isolated {H : DAG V} {z : V} (hnp : ∀ u, ¬ H.edge u z)
    (S : Finset V) (hS : z ∉ S) :
    SetSound.DSeparatedSet (cutOut H {z}) ∅ S {z} := by
  have hiso : ∀ u, ¬ (cutOut H {z}).edge u z ∧ ¬ (cutOut H {z}).edge z u :=
    fun u => ⟨fun e => hnp u e.1, fun e => e.2 (Finset.mem_singleton_self z)⟩
  intro s hs z' hz' p _
  exfalso
  have hs' : s = z := walk_to_isolated hiso p (Finset.mem_singleton.mp hz')
  exact hS (hs' ▸ hs)

/-- If `z` is not an ancestor of `W`, then `Z(W) = {z}`. -/
lemma Z2_singleton {H : DAG V} {z : V} {W : Finset V} (h : z ∉ ancestors H W) :
    Rule3.Z2 H {z} W = {z} := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun hv => hv.1
  · rintro rfl
    exact ⟨rfl, h⟩

/-- **Completeness of rule 3 when `z` is not an ancestor of `W`.** If the condition of
`rule3_general` fails, there are a model on `G` and values for which the product form of
rule 3 fails. -/
theorem rule3_complete_nonanc (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∉ ancestors (cutIn G X) W)
    (h : ¬ (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  rw [Z2_singleton hanc] at h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) {z}) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hN := chain_not_condIndep C' hinj hyz
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) {z}).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ u, ¬ (cutIn (cutIn G X) {z}).edge u z :=
    fun u e => e.2 (Finset.mem_singleton_self z)
  have hzy : z ∉ ({y} ∪ (X ∪ W) : Finset V) := fun hm =>
    (Finset.mem_union.mp hm).elim (fun e => hyz (Finset.mem_singleton.mp e).symm) hz
  -- `z` is a root: setting `z` is conditioning on `z` (front-door step 1 with `X := {z}`).
  have fa : (chainModel C').marginal ({y} ∪ {z} ∪ (X ∪ W)) w =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal ({y} ∪ (X ∪ W))
        (w.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := {y} ∪ (X ∪ W) ∪ {z})
      (T := {y} ∪ {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} ({y} ∪ (X ∪ W))
      (Finset.disjoint_singleton_right.mpr hzy) (dsep_isolated hnp _ hzy) _
  have fd : (chainModel C').marginal ({z} ∪ (X ∪ W))
        (w.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := X ∪ W ∪ {z})
      (T := {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} (X ∪ W)
      (Finset.disjoint_singleton_right.mpr hz) (dsep_isolated hnp _ hz) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      {z} (w.restrict hzs)).marginal S =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

/-- **Rule 3 fails when `y` and `z` are d-connected in `G_{X̄z̄}`**, whether or not `z` is
an ancestor of `W`. Then `z` can be made a root. `rule3_complete_nonanc` is the special case
where this graph is the graph of rule 3. -/
theorem rule3_complete_root (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn (cutIn G X) {z}).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) {z}) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hN := chain_not_condIndep C' hinj hyz
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) {z}).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ u, ¬ (cutIn (cutIn G X) {z}).edge u z :=
    fun u e => e.2 (Finset.mem_singleton_self z)
  have hzy : z ∉ ({y} ∪ (X ∪ W) : Finset V) := fun hm =>
    (Finset.mem_union.mp hm).elim (fun e => hyz (Finset.mem_singleton.mp e).symm) hz
  -- `z` is a root: setting `z` is conditioning on `z` (front-door step 1 with `X := {z}`).
  have fa : (chainModel C').marginal ({y} ∪ {z} ∪ (X ∪ W)) w =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal ({y} ∪ (X ∪ W))
        (w.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := {y} ∪ (X ∪ W) ∪ {z})
      (T := {y} ∪ {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} ({y} ∪ (X ∪ W))
      (Finset.disjoint_singleton_right.mpr hzy) (dsep_isolated hnp _ hzy) _
  have fd : (chainModel C').marginal ({z} ∪ (X ∪ W))
        (w.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C') (S := X ∪ W ∪ {z})
      (T := {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} (X ∪ W)
      (Finset.disjoint_singleton_right.mpr hz) (dsep_isolated hnp _ hz) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      {z} (w.restrict hzs)).marginal S =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

end Rule3C

/-! ## The rules as equivalences -/

section RuleIff
open DoCalculus

/-- d-separation of two vertices is d-separation of the singleton sets. -/
lemma dsepSet_single {H : DAG V} {S : Finset V} {y z : V} (h : H.DSeparated S y z) :
    SetSound.DSeparatedSet H S {y} {z} := by
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  subst ha
  subst hb
  exact dsepPath_of_dsep h

/-- **Rule 1 is exact.** The condition of rule 1 holds if and only if the rule holds in
every model on `G` and for every value `x`. -/
theorem rule1_iff (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) :
    (cutIn G X).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X),
        CondIndep (doModel M X x) {y} {z} (X ∪ W) := by
  constructor
  · intro h k M x
    exact rule1 M X W {y} {z} x (Finset.disjoint_singleton_left.mpr hy)
      (Finset.disjoint_singleton_left.mpr hz) (dsepSet_single h)
  · intro H
    by_contra hn
    obtain ⟨k, M, x, hM⟩ := rule1_complete G X W y z hy hz hyz hn
    exact hM (H k M x)

/-- **Rule 2 is exact.** The condition of rule 2 holds if and only if the product form of
`rule2` holds in every model on `G` and for all values. -/
theorem rule2_iff (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) :
    (cutOut (cutIn G X) {z}).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) {z})
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W))),
        t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ →
        (doModel M X x).marginal ({y} ∪ {z} ∪ (X ∪ W)) t *
          (doModel (doModel M X x) {z} z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel (doModel M X x) {z} z₀).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal ({z} ∪ (X ∪ W))
            (t.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x z₀ t ht
    exact rule2 M X {y} {z} W x z₀ (Finset.disjoint_singleton.mpr hyz)
      (Finset.disjoint_singleton_right.mpr hz) (Finset.disjoint_singleton_left.mpr hy)
      (dsepSet_single h) t ht
  · intro H
    by_contra hn
    obtain ⟨k, M, x, z₀, t, ht, hne⟩ := rule2_complete G X W y z hy hz hyz hn
    exact hne (H k M x z₀ t ht)

/-- **Rule 3 is exact when `z` is not an ancestor of `W`.** The condition of rule 3 holds
if and only if its product form holds in every model on `G` and for all values. -/
theorem rule3_iff_nonanc (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∉ ancestors (cutIn G X) W) :
    (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W))),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x t
    exact Rule3Flag.rule3_general M X {y} {z} W x (Finset.disjoint_singleton.mpr hyz)
      (Finset.disjoint_singleton_right.mpr hz) (Finset.disjoint_singleton_left.mpr hy)
      (dsepSet_single h) t
  · intro H
    by_contra hn
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_nonanc G X W y z hy hz hyz hanc hn
    exact hne (H k M x t)

end RuleIff

end Completeness
