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
(`Completeness/SetRules.lean`) and rule 3 in all cases (`Completeness/Rule3Iff.lean`, which
uses `rule3_complete_nonanc` and `rule3_complete_root`) build on it. The lifting tools of
this file, `liftSub` (a model on a subgraph seen as a model on the larger graph), its kernel
factors (`kfac_liftSub`, `kfac_doModel_liftSub`), the factorisation lemma
`marginal_eq_of_kfac` and `dsep_isolated`, are also used by every hedge counter-model of
`Identification` (`Bow`, `HedgeChain`, `HedgeTemplate`, `RootPathModels`, `RootPath`).

**How the proof goes.** Each condition is d-separation in a mutilated graph `H`
(`G_{X̄}`, `G_{X̄z̲}` or `G_{X̄z̄}`) whose parent sets are contained in those of `G`. If it
fails, `Completeness/Chain.lean` gives a chain model on `H` in which `y` and `z` are
dependent given `X ∪ W` (`exists_chain_not_condIndep`). The vertices of `X` have no parents
in `H`, so they are constant `false` in that model (`chain_X_false`,
`chain_noparent_false`). Lifted to `G` (`liftSub`: the kernels ignore the extra parents),
the model under `do(X = false)` has the same kernel factors and hence the same marginals
(`marginal_eq_of_kfac`, `lift_do_kfac`, `lift_do_do_kfac`). For rule 1 that already is the
failure: for a model on `G_{X̄}` it gives back the chain model itself (`doModel_liftSub`). For rule 2, `z` has no children in `G_{X̄z̲}`, so `do(z)` leaves
every marginal without `z` unchanged and the product form of rule 2 reduces to conditional
independence. For rule 3, `z` is a root of `G_{X̄z̄}`, and for a root, setting `z` is the
same as conditioning on `z` (front-door step 1 with `dsep_isolated_set`), so again the
product form reduces to conditional independence. These two arguments are proved once, for
sets `Y` and `Z` in place of `{y}` and `{z}` (`rule2_fails_of_chain`,
`rule3_fails_of_chain`); the theorems here and the set versions of
`Completeness/SetRules.lean` only supply the chain. When `z ∉ An(W)` the graph of rule 3 is
`G_{X̄z̄}` (`Z2_singleton`).

**Main results.** `rule1_iff`, `rule2_iff`, `rule3_iff_nonanc`, `rule1_complete`,
`rule2_complete`, `rule3_complete_nonanc`, `rule3_complete_root`, the counter-models
`rule2_fails_of_chain` and `rule3_fails_of_chain`, and the shared tools `liftSub`,
`kfac_liftSub`, `kfac_doModel_liftSub`, `marginal_eq_of_kfac`, `dsep_isolated`,
`dsep_isolated_set`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Lifted models

A model on a subgraph `H` of `G` (every parent set of `H` contained in that of `G`) is a
model on `G` whose kernels ignore the extra parents (`liftSub`). It has the same kernel
factors, also after an intervention, and hence the same marginals. -/

section Lift
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

/-- Cutting the edges into `X` only removes parents. -/
lemma parents_cutIn_subset {G : DAG V} (X : Finset V) (v : V) :
    (cutIn G X).parents v ⊆ G.parents v := by
  intro u hu
  simp only [DAG.mem_parents] at hu ⊢
  exact hu.1

/-- A lift from `G_{X̄}`: if every `X` kernel of `N` is the point mass at `x`, then
`do(X = x)` in the lift equals `N`. -/
theorem doModel_liftSub {G : DAG V} {X : Finset V} {α : V → Type*}
    (hsub : ∀ v, (cutIn G X).parents v ⊆ G.parents v) (N : (cutIn G X).CausalModel α)
    (x : Assignment (α := α) X) (hX : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩)) :
    doModel (liftSub hsub N) X x = N := by
  obtain ⟨fin, deq, ker⟩ := N
  simp only [doModel, liftSub, CausalModel.mk.injEq, true_and]
  funext v p
  split_ifs with hv
  · exact (hX v hv p).symm
  · rfl

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

end Lift

/-! ## Completeness of rule 1 -/

section Rule1
open DoCalculus

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

/-- In a chain model with conditioning set `X ∪ W`, the vertices of `X` are constant
`false` when they have no parents: then they cannot be XOR vertices. -/
lemma chain_X_false {H : DAG V} {X W : Finset V} {y z : V}
    (C : Chain H (X ∪ W) y z) (hX : ∀ v ∈ X, ∀ u, ¬ H.edge u v) :
    ∀ v (hv : v ∈ X) p, (chainModel C).kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
  fun v hv p => chain_noparent_false C v (Finset.mem_union_left W hv) (hX v hv) p

/-- **Completeness of rule 1.** If `y` and `z` are not d-separated given `X ∪ W` in
`G_{X̄}`, there are a model on `G` and a value `x` for which
`P_x(y | z, x, w) = P_x(y | x, w)` fails. -/
theorem rule1_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn G X).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) {y} {z} (X ∪ W) := by
  obtain ⟨C, hC⟩ := exists_chain_not_condIndep hy hz hyz h
  refine ⟨C.k, liftSub (parents_cutIn_subset X) (chainModel C), fun _ _ => false, ?_⟩
  rw [doModel_liftSub _ (chainModel C) _ (chain_X_false C fun _ hv _ e => e.2 hv)]
  exact hC

end Rule1

/-! ## Completeness of rule 2 -/

section Rule2
open DoCalculus

/-- **The counter-model of rule 2.** If the chain model on `G_{X̄Z̲}` makes `Y` and `Z`
dependent given `X ∪ W`, its lift to `G` refutes the product form of `rule2`, with `x` all
`false` and `z₀` taken from the witness. Under `do(X = false)` the lift has the kernel
factors of the chain model, whose `X` vertices are already constant `false`; `do(Z)` does
not change the marginals without `Z`, since `Z` has no children in `G_{X̄Z̲}`. -/
lemma rule2_fails_of_chain {G : DAG V} {X W Y Z : Finset V} {y z : V}
    (C : Chain (cutOut (cutIn G X) Z) (X ∪ W) y z)
    (hYZ : Disjoint Y Z) (hZ : Disjoint Z (X ∪ W))
    (hN : ¬ CondIndep (chainModel C) Y Z (X ∪ W)) :
    ∃ M : G.CausalModel (fun _ => Fin (C.k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) Z,
      ∃ t : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
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
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutOut (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN := chain_X_false C fun _ hv _ e => e.1.2 hv
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  refine ⟨liftSub hsub (chainModel C), fun _ _ => false, w.restrict hzs, w, rfl, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C)) X (fun _ _ => false)).marginal S =
      (chainModel C).marginal S :=
    marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C) _ hXN)
  have hB : ∀ S, Disjoint S Z →
      (doModel (doModel (liftSub hsub (chainModel C)) X (fun _ _ => false))
        Z (w.restrict hzs)).marginal S = (chainModel C).marginal S := by
    intro S hS
    rw [marginal_eq_of_kfac _ (doModel (chainModel C) Z (w.restrict hzs))
      (lift_do_do_kfac hsub (chainModel C) _ (w.restrict hzs) hXN)]
    refine PMF.ext fun s => Rule3.doModel_marginal_of_subset (chainModel C) Z _
      (Finset.univ \ Z) ?_ Finset.sdiff_disjoint S ?_ s
    · intro v _ w' e
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e.2⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, Finset.disjoint_left.mp hS hv⟩
  rw [hB (X ∪ W) hZ.symm, hB (Y ∪ (X ∪ W)) (Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩),
    hA, hA]
  exact hw

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
  obtain ⟨C, hC⟩ := exists_chain_not_condIndep hy hz hyz h
  exact ⟨C.k, rule2_fails_of_chain C (Finset.disjoint_singleton.mpr hyz)
    (Finset.disjoint_singleton_left.mpr hz) hC⟩

end Rule2

/-! ## Completeness of rule 3 when `z` can be made a root

This covers the case `z ∉ An(W)` and, more generally, every case where `y` and `z` are
d-connected in `G_{X̄z̄}`. The counter-model is proved for a set `Z` of vertices that are
made roots (`rule3_fails_of_chain`), and `Completeness/SetRules.lean` uses it as well. -/

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

/-- In a graph where the vertices of `Z` have no edges, every walk that ends in `Z` also
starts in `Z`. -/
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

/-- If the vertices of `Z` have no parents in `H`, then they are isolated in `H_{Z̲}`, and
hence `Z` is d-separated from every set disjoint from `Z`, given `∅`. -/
lemma dsep_isolated_set {H : DAG V} {Z : Finset V} (hnp : ∀ z ∈ Z, ∀ u, ¬ H.edge u z)
    (S : Finset V) (hS : Disjoint S Z) :
    SetSound.DSeparatedSet (cutOut H Z) ∅ S Z := by
  have hiso : ∀ z ∈ Z, ∀ u, ¬ (cutOut H Z).edge u z ∧ ¬ (cutOut H Z).edge z u :=
    fun z hz u => ⟨fun e => hnp z hz u e.1, fun e => e.2 hz⟩
  intro s hs z' hz' p _
  exfalso
  exact Finset.disjoint_left.mp hS hs (walk_to_isolated_set hiso p hz')

/-- If `z` is not an ancestor of `W`, then `Z(W) = {z}`. -/
lemma Z2_singleton {H : DAG V} {z : V} {W : Finset V} (h : z ∉ ancestors H W) :
    Rule3.Z2 H {z} W = {z} := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun hv => hv.1
  · rintro rfl
    exact ⟨rfl, h⟩

/-- **The counter-model of rule 3.** If the chain model on `G_{X̄Z̄}` makes `Y` and `Z`
dependent given `X ∪ W`, its lift to `G` refutes the product form of rule 3, with `x` all
`false`. Under `do(X = false)` the lift has the kernel factors of the chain model, and
since the vertices of `Z` are roots of `G_{X̄Z̄}`, setting them is conditioning on them
(front-door step 1); this turns the failed independence into the failed rule. -/
lemma rule3_fails_of_chain {G : DAG V} {X W Y Z : Finset V} {y z : V}
    (C : Chain (cutIn (cutIn G X) Z) (X ∪ W) y z)
    (hYZ : Disjoint Y Z) (hZ : Disjoint Z (X ∪ W))
    (hN : ¬ CondIndep (chainModel C) Y Z (X ∪ W)) :
    ∃ M : G.CausalModel (fun _ => Fin (C.k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
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
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.mem_parents] at hu ⊢
    exact hu.1.1
  have hXN := chain_X_false C fun _ hv _ e => e.1.2 hv
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ z ∈ Z, ∀ u, ¬ (cutIn (cutIn G X) Z).edge u z :=
    fun z hz u e => e.2 hz
  have hYXWZ : Disjoint (Y ∪ (X ∪ W)) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩
  have fa : (chainModel C).marginal (Y ∪ Z ∪ (X ∪ W)) w =
      (doModel (chainModel C) Z (w.restrict hzs)).marginal (Y ∪ (X ∪ W))
        (w.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C).marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C) (S := Y ∪ (X ∪ W) ∪ Z)
      (T := Y ∪ Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C) Z (Y ∪ (X ∪ W)) hYXWZ
      (dsep_isolated_set hnp _ hYXWZ) _
  have fd : (chainModel C).marginal (Z ∪ (X ∪ W))
        (w.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C) Z (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C).marginal Z (w.restrict hzs) := by
    rw [marginal_eq_restrict_of_subset_of_subset (chainModel C) (S := X ∪ W ∪ Z)
      (T := Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C) Z (X ∪ W) hZ.symm
      (dsep_isolated_set hnp _ hZ.symm) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨liftSub hsub (chainModel C), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C)) X (fun _ _ => false)).marginal S =
      (chainModel C).marginal S :=
    marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C) _ hXN)
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C)) X (fun _ _ => false))
      Z (w.restrict hzs)).marginal S =
      (doModel (chainModel C) Z (w.restrict hzs)).marginal S :=
    marginal_eq_of_kfac _ _ (lift_do_do_kfac hsub (chainModel C) _ (w.restrict hzs) hXN)
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
  obtain ⟨C, hC⟩ := exists_chain_not_condIndep hy hz hyz h
  exact ⟨C.k, rule3_fails_of_chain C (Finset.disjoint_singleton.mpr hyz)
    (Finset.disjoint_singleton_left.mpr hz) hC⟩

/-- **Completeness of rule 3 when `z` is not an ancestor of `W`.** If the condition of
`rule3_general` fails, there are a model on `G` and values for which the product form of
rule 3 fails. Here `Z(W) = {z}`, so this is `rule3_complete_root`. -/
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
  exact rule3_complete_root G X W y z hy hz hyz h

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
