import PearlDoCalculus.DSepSoundSkeleton.Factorizes
/-!
# The joint as a product of kernels, and reduction to an ancestral set

**What it proves.** The joint distribution of a causal model is the product of its
kernel factors: `fullJoint M u = ∏ v, kfac M univ u v`, where `kfac M S a v` is the
kernel of `v` evaluated in `a` (`fullJoint_apply_prod`, and `jointUpTo_apply_prod` for each
rank level). For a set `A` closed under parents, the marginal on `A` is the product of
the factors of `A` alone (`marginal_ancestral_apply`), so it equals the marginal of the
model restricted to `A` (`CausalModel.restrictTo`, `marginal_eq_restricted_joint`).
Finally, d-separation in `G` implies d-separation in the subgraph induced on any set
that contains `ancestors G ({x, y} ∪ Z)` (`dsep_restrict`).

**Why it is needed.** This is layer 1c of the Lauritzen route to the soundness of
d-separation (see `DSepSoundSkeleton.lean`): `DSepSound.dsep_sound` proves conditional
independence in the restricted model on `A = ancestors G ({x, y} ∪ Z)` and transfers it
back to `M` with `marginal_eq_restricted_joint`; `SetSound.lean` does the same for sets.
The product form is used far beyond soundness: `kfac`, `kfac_univ` and
`fullJoint_apply_prod` are how almost every probability computation in the project
starts (`DoCalculus`, `Rule3`, `Rule3Flag`, `Idc`, `Completeness/*`, `Hedge/*`,
`Identification/*`), `marginal_ancestral_apply` is used by `Rule3` and
`Identification/*`, and `sum_compl_kfac_eq_one` by `DoCalculus`,
`Identification/CFactorSets` and `Identification/Identify`. The graph fact
`dsep_restrict` (with `DAG.Walk.lift`) has no users: soundness does not need
d-separation in the induced subgraph, because Lauritzen's theorem
(`Lauritzen.moral_sep_of_dsep_lauritzen`) works in `G` directly.

**How the proofs go.**
1. `jointUpTo_apply_prod` is proved by induction on the rank level. Level `n + 1` is a
   `bind` over level `n`; the sum collapses to one term (`jointUpTo_bind_collapse`), and
   the extension is a list product of kernels (`extendOverList_apply_prod`), which is a
   `Finset` product (`list_attach_prod_eq`). `fullJoint_apply_prod` is the top level.
2. For any `A` and any fixed `a` on `A`, the factors outside `A` sum to one over all
   extensions of `a` (`sum_compl_kfac_eq_one`). The trick: replace the kernels in `A` by
   point masses on `a` (the model `pinTo M A a`). The joint of that model is exactly the
   summand, and a joint sums to one.
3. If `A` is closed under parents, the factors inside `A` depend only on the restriction
   to `A` (`kfac_restrict`), so they come out of the sum, and step 2 removes the rest
   (`marginal_ancestral_apply`). The restricted model has the same kernel factors on `A`
   (`kfac_restrictTo`), which gives `marginal_eq_restricted_joint`.
4. For `dsep_restrict`, a walk in the induced subgraph lifts to a walk in `G`
   (`DAG.Walk.lift`), and a blocked lift was blocked already
   (`DAG.Walk.blockedAux_lift`).

**Main results.** `kfac` (with its unfolding lemmas `kfac_of_mem` and `kfac_univ`),
`jointUpTo_apply_prod`, `fullJoint_apply_prod`, `sum_compl_kfac_eq_one`,
`marginal_ancestral_apply`, `CausalModel.restrictTo`, `marginal_eq_restricted_joint` and
`dsep_restrict`.
-/

set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel

/-! ## Kernel factors -/

/-- The kernel factor of `v` evaluated in an assignment on `S`; equal to 1 if `v` or a
parent of `v` lies outside `S`. It is total in `v`, so products over different sets can
be compared without subtype bookkeeping. -/
noncomputable def kfac (M : CausalModel G α) (S : Finset V)
    (a : Assignment (α := α) S) (v : V) : ENNReal :=
  if h : v ∈ S ∧ G.parents v ⊆ S then M.kernel v (a.restrict h.2) (a ⟨v, h.1⟩) else 1

/-- When `v` and its parents lie in `S`, the kernel factor is the kernel of `v`
evaluated in `a`. -/
lemma kfac_of_mem (M : CausalModel G α) (S : Finset V) (a : Assignment (α := α) S) (v : V)
    (hv : v ∈ S) (hpa : G.parents v ⊆ S) :
    kfac M S a v = M.kernel v (a.restrict hpa) (a ⟨v, hv⟩) := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩]

/-- On `univ` the kernel factor is always the kernel evaluated in the assignment. -/
lemma kfac_univ (M : CausalModel G α) (u : Assignment (α := α) (Finset.univ : Finset V))
    (v : V) :
    kfac M Finset.univ u v =
      M.kernel v (u.restrict (Finset.subset_univ _)) (u ⟨v, Finset.mem_univ v⟩) :=
  kfac_of_mem M _ u v (Finset.mem_univ v) (Finset.subset_univ _)

/-- The kernel factor is unchanged by restriction as long as `v` and its parents lie in
the smaller set. -/
lemma kfac_restrict (M : CausalModel G α) {S T : Finset V} (hTS : T ⊆ S)
    (a : Assignment (α := α) S) {v : V} (hv : v ∈ T) (hpa : G.parents v ⊆ T) :
    kfac M T (a.restrict hTS) v = kfac M S a v := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩, dif_pos ⟨hTS hv, hpa.trans hTS⟩]
  rfl

/-! ## The joint as a product of kernel factors -/

/-- A list product over `l.attach` is a `Finset` product over `l.toFinset` when the list
has no duplicates and the factors agree pointwise. -/
lemma list_attach_prod_eq {β : Type*} [CommMonoid β] :
    ∀ (l : List V) (f : {w // w ∈ l} → β) (g : V → β),
      l.Nodup → (∀ w (hw : w ∈ l), f ⟨w, hw⟩ = g w) →
      (l.attach.map f).prod = ∏ w ∈ l.toFinset, g w := by
  intro l
  induction l with
  | nil => intro f g _ _; simp
  | cons v vs ih =>
    intro f g hnd hfg
    have hnd' := List.nodup_cons.mp hnd
    rw [List.attach_cons, List.map_cons, List.prod_cons, List.map_map, List.toFinset_cons,
      Finset.prod_insert (by simpa using hnd'.1), hfg v List.mem_cons_self]
    congr 1
    exact ih _ g hnd'.2 (fun w hw => hfg w (List.mem_cons_of_mem v hw))

/-- Explicit product form of `jointUpTo`: at every rank level the partial joint is the
product of the kernel factors of the vertices up to that level. -/
lemma jointUpTo_apply_prod (M : CausalModel G α) (n : ℕ)
    (a : Assignment (α := α) (G.verticesUpTo n)) :
    (jointUpTo M n) a = ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo n) a v := by
  have hpaUp : ∀ (m : ℕ) (v : V), v ∈ G.verticesUpTo m → G.parents v ⊆ G.verticesUpTo m := by
    intro m v hv u hu
    simp only [DAG.verticesUpTo, DAG.parents, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv hu ⊢
    exact le_trans (le_of_lt (G.rank_strict_mono u v hu)) hv
  induction n with
  | zero =>
    rw [jointUpTo_zero_apply, extendOverList_apply_prod M ∅ _ _ _ (Finset.nodup_toList _)
      (fun v _ h => by simp at h)]
    have hemp : ∀ x y : Assignment (α := α) (∅ : Finset V), x = y :=
      fun x y => funext fun t => by obtain ⟨u, hu⟩ := t; simp at hu
    rw [if_pos (hemp _ _), one_mul,
      list_attach_prod_eq _ _ (kfac M (G.verticesUpTo 0) a) (Finset.nodup_toList _),
      Finset.toList_toFinset]
    intro w hw
    have hw' : w ∈ G.verticesUpTo 0 := Finset.mem_toList.mp hw
    have hnopa : ∀ t : {u // u ∈ G.parents w}, False := fun t => by
      have hedge : G.edge t.1 w := by
        have ht := t.2
        simp only [DAG.mem_parents] at ht
        exact ht
      have hlt := G.rank_strict_mono t.1 w hedge
      simp only [DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      omega
    unfold kfac
    rw [dif_pos ⟨hw', hpaUp 0 w hw'⟩]
    refine congrArg₂ (fun p x => M.kernel w p x) (funext fun t => (hnopa t).elim) ?_
    exact cast_apply_eq _ _ (by simp) _ a w _ hw'
  | succ n ih =>
    have hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        = G.verticesUpTo (n + 1) := by
      ext x
      simp only [DAG.verticesUpTo, DAG.newAtRank, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.toList_toFinset]
      constructor <;> intro h <;> omega
    have hsub : G.verticesUpTo n ⊆ G.verticesUpTo (n + 1) := fun x hx => by
      simp only [DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    have hdisj' : Disjoint (G.verticesUpTo n) (G.newAtRank (n + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [DAG.verticesUpTo, DAG.newAtRank, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx hx'
      omega
    have hset2 : G.verticesUpTo (n + 1) = G.verticesUpTo n ∪ G.newAtRank (n + 1) := by
      rw [← hset, Finset.toList_toFinset]
    rw [jointUpTo_succ_apply M n hset (by rw [hset]) a, PMF.bind_apply,
      jointUpTo_bind_collapse, ih,
      extendOverList_apply_prod M _ _ _ _ (Finset.nodup_toList _)
        (fun v hv h => by
          simp only [Finset.mem_toList, DAG.newAtRank, DAG.verticesUpTo, Finset.mem_filter,
            Finset.mem_univ, true_and] at hv h
          omega),
      if_pos rfl, one_mul,
      list_attach_prod_eq _ _ (kfac M (G.verticesUpTo (n + 1)) a) (Finset.nodup_toList _),
      restrict_cast_eq _ _ _ hset _ a Finset.subset_union_left hsub,
      Finset.toList_toFinset]
    · have h1 : ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo n) (a.restrict hsub) v
          = ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo (n + 1)) a v :=
        Finset.prod_congr rfl (fun v hv => kfac_restrict M hsub a hv (hpaUp n v hv))
      rw [h1, ← Finset.prod_union hdisj']
      exact Finset.prod_congr hset2.symm (fun _ _ => rfl)
    · intro w hw
      have hwN : w ∈ G.newAtRank (n + 1) := Finset.mem_toList.mp hw
      have hwU : w ∈ G.verticesUpTo (n + 1) := by
        simp only [DAG.newAtRank, DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ,
          true_and] at hwN ⊢
        omega
      unfold kfac
      rw [dif_pos ⟨hwU, hpaUp (n + 1) w hwU⟩]
      refine congrArg₂ (fun p x => M.kernel w p x) ?_ ?_
      · funext t
        exact cast_apply_eq _ _ hset _ a t.1 _ (hpaUp (n + 1) w hwU t.2)
      · exact cast_apply_eq _ _ hset _ a w _ hwU

/-- The kernel factor is unchanged by transport along an equality of finsets. -/
lemma kfac_cast (M : CausalModel G α) {S T : Finset V} (hST : S = T)
    (h : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) :
    kfac M S (cast h a) v = kfac M T a v := by
  subst hST
  rfl

/-- Explicit product form of `fullJoint`: the joint is the product of all kernel
factors. -/
lemma fullJoint_apply_prod (M : CausalModel G α)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) u = ∏ v, kfac M Finset.univ u v := by
  rw [fullJoint_apply M (by rw [G.verticesUpTo_maxRank]) u, jointUpTo_apply_prod]
  exact Finset.prod_congr G.verticesUpTo_maxRank
    (fun v _ => kfac_cast M G.verticesUpTo_maxRank _ u v)

/-! ## Marginals on ancestral sets -/

/-- Auxiliary model for `sum_compl_kfac_eq_one`: the kernels in `A` are point masses on
`a`, the others are unchanged. Same graph as `M`, so no transport is needed. -/
noncomputable def pinTo (M : CausalModel G α) (A : Finset V)
    (a : Assignment (α := α) A) : CausalModel G α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v p => if hv : v ∈ A then PMF.pure (a ⟨v, hv⟩) else M.kernel v p }

/-- The kernel factor of the auxiliary model: an indicator in `A`, unchanged outside. -/
lemma kfac_pinTo (M : CausalModel G α) (A : Finset V) (a : Assignment (α := α) A)
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (pinTo M A a) Finset.univ u v =
      if hv : v ∈ A then (if u ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩ then 1 else 0)
      else kfac M Finset.univ u v := by
  have hc : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  simp only [dif_pos hc]
  by_cases hv : v ∈ A
  · simp only [pinTo, dif_pos hv, PMF.pure_apply]
  · simp only [pinTo, dif_neg hv]

/-- The kernel factors outside `A` sum to 1 over all extensions of a fixed assignment on
`A`. This holds for every `A`, closed under parents or not. -/
lemma sum_compl_kfac_eq_one (M : CausalModel G α) (A : Finset V)
    (a : Assignment (α := α) A) :
    ∑' u : Assignment (α := α) (Finset.univ : Finset V),
      (if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
        ∏ v ∈ Aᶜ, kfac M Finset.univ u v = 1 := by
  have hsplit : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
      ∏ v, kfac (pinTo M A a) Finset.univ u v =
        (if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
          ∏ v ∈ Aᶜ, kfac M Finset.univ u v := by
    intro u
    rw [← Finset.prod_mul_prod_compl A]
    congr 1
    · by_cases h : u.restrict (Finset.subset_univ A) = a
      · rw [if_pos h]
        refine Finset.prod_eq_one (fun v hv => ?_)
        rw [kfac_pinTo, dif_pos hv, if_pos]
        exact congrFun h ⟨v, hv⟩
      · rw [if_neg h]
        obtain ⟨⟨v, hv⟩, hne⟩ := Function.ne_iff.mp h
        refine Finset.prod_eq_zero hv ?_
        rw [kfac_pinTo, dif_pos hv,
          if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩) from hne)]
    · exact Finset.prod_congr rfl (fun v hv => by
        rw [kfac_pinTo, dif_neg (Finset.mem_compl.mp hv)])
  calc _ = ∑' u, (pinTo M A a).fullJoint u :=
        tsum_congr (fun u => by rw [fullJoint_apply_prod, hsplit])
    _ = 1 := (pinTo M A a).fullJoint.tsum_coe

/-- The marginal on a set closed under parents is the product of the kernel factors of
that set. -/
lemma marginal_ancestral_apply (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (a : Assignment (α := α) A) :
    (M.marginal A) a = ∏ v ∈ A, kfac M A a v := by
  have hpa : ∀ v ∈ A, G.parents v ⊆ A := DAG.parents_subset_of_closed hA
  have hterm : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
      (if a = u.restrict (Finset.subset_univ A) then (M.fullJoint) u else 0)
        = (∏ v ∈ A, kfac M A a v) *
          ((if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
            ∏ v ∈ Aᶜ, kfac M Finset.univ u v) := by
    intro u
    by_cases h : u.restrict (Finset.subset_univ A) = a
    · rw [if_pos h.symm, if_pos h, one_mul, fullJoint_apply_prod, ← h,
        ← Finset.prod_mul_prod_compl A]
      congr 1
      exact Finset.prod_congr rfl (fun v hv => (kfac_restrict M _ u hv (hpa v hv)).symm)
    · rw [if_neg (fun h' => h h'.symm), if_neg h, zero_mul, mul_zero]
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, sum_compl_kfac_eq_one, mul_one]

/-! ## The restricted model -/

/-- Restriction of a causal model to a vertex set closed under parents: a model on the
induced subgraph with the same kernels on `A`. Outside `A` the kernels are irrelevant
and are fed an arbitrary parent assignment. -/
noncomputable def CausalModel.restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)] :
    CausalModel (DAG.induce G A) α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v => by
      classical
      by_cases hv : v ∈ A
      · rw [DAG.induce_parents_eq A hA v hv]
        exact M.kernel v
      · exact fun _ => M.kernel v (fun u => Classical.arbitrary _) }

/-- `Eq.mpr` along an equality of parent sets only moves the membership proofs in the
argument of the kernel. -/
lemma mpr_kernel_apply {v : V} {s t : Finset V} (hst : s = t)
    (h : ((∀ u : {u // u ∈ s}, α u.1) → PMF (α v))
      = ((∀ u : {u // u ∈ t}, α u.1) → PMF (α v)))
    (f : (∀ u : {u // u ∈ t}, α u.1) → PMF (α v))
    (p : ∀ u : {u // u ∈ s}, α u.1) :
    (h.mpr f) p = f (fun u => p ⟨u.1, hst ▸ u.2⟩) := by
  subst hst
  rfl

/-- The restricted model has the same kernel factors on `A`. -/
lemma kfac_restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) {v : V} (hv : v ∈ A) :
    kfac (CausalModel.restrictTo M A hA) A a v = kfac M A a v := by
  have hpaM : G.parents v ⊆ A := fun u hu => by
    simp only [DAG.mem_parents] at hu
    exact hA v hv u hu
  have hpaN : (DAG.induce G A).parents v ⊆ A := by
    rw [DAG.induce_parents_eq A hA v hv]
    exact hpaM
  unfold kfac
  rw [dif_pos ⟨hv, hpaN⟩, dif_pos ⟨hv, hpaM⟩]
  simp only [CausalModel.restrictTo, dif_pos hv]
  rw [mpr_kernel_apply (DAG.induce_parents_eq A hA v hv)]
  all_goals rfl

/--
**Ancestral marginalisation.** The marginal of the full joint onto a set `A` closed
under parents agrees with the joint of the restricted model at every assignment.

Both sides are marginals on `A`, that is `PMF`s applied to an `Assignment`; both are
the product of the same kernel factors (`marginal_ancestral_apply`, `kfac_restrictTo`).
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) :
    (M.marginal A) a = ((CausalModel.restrictTo M A hA).marginal A) a := by
  rw [marginal_ancestral_apply M A hA a,
    marginal_ancestral_apply (CausalModel.restrictTo M A hA) A (fun _ _ _ hw => hw.1) a]
  exact Finset.prod_congr rfl (fun v hv => (kfac_restrictTo M A hA a hv).symm)
/-! ## d-separation in an induced subgraph -/

/-- Lifts a walk in the induced subgraph to a walk in `G`. -/
def DAG.Walk.lift {A : Finset V} : {u w : V} →
    DAG.Walk (DAG.induce G A) u w → DAG.Walk G u w
  | _, _, .nil v => .nil v
  | _, _, .fwd e rest => .fwd (DAG.induce_edge e) (lift rest)
  | _, _, .bwd e rest => .bwd (DAG.induce_edge e) (lift rest)

/-- If the lift of a walk is blocked in `G`, the walk is blocked in the induced
subgraph. -/
lemma DAG.Walk.blockedAux_lift {A Z : Finset V} (inc : DAG.Incoming) :
    ∀ {u w : V} (p : DAG.Walk (DAG.induce G A) u w),
      DAG.Walk.blockedAux (G := G) Z inc (DAG.Walk.lift p) →
      DAG.Walk.blockedAux (G := DAG.induce G A) Z inc p := by
  intro u w p
  induction p generalizing inc with
  | nil v => intro h; exact h
  | fwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      tauto
  | bwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      first
        | tauto
        | (rintro (hr | hb)
           · exact Or.inl fun z hz hcon => hr z hz (DAG.induce_reaches hcon)
           · exact Or.inr (ih _ hb))
/--
d-separation survives restriction to an ancestral set containing the relevant
vertices. This is pure graph theory and needs nothing from the probability part.
No other file uses it (see the module docstring).

The proof inducts on the `DAG.Walk` structure: a walk in `DAG.induce G A` lifts to a
walk in `G` via `DAG.induce_edge`, and `blockedAux` is preserved because
`DAG.induce_reaches` carries reachability upward.
-/
theorem dsep_restrict (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y)
    (A : Finset V) (hA : ancestors G ({x, y} ∪ Z) ⊆ A) :
    (DAG.induce G A).DSeparated Z x y := by
  intro p
  exact DAG.Walk.blockedAux_lift .start p (h (DAG.Walk.lift p))

end PearlDoCalculus
