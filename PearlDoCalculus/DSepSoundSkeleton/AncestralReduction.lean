import PearlDoCalculus.DSepSoundSkeleton.Factorizes
/-!
# Reduction to an ancestral set

Layer 1c of the Lauritzen route to soundness of d-separation (`DSepSound.dsep_sound`).
It shows that the joint distribution of a causal model is a product of kernel factors
`kfac`, and that the marginal on an ancestral set is the product of the factors of that
set. From this it follows that the marginal equals the joint of the restricted model
`CausalModel.restrictTo`. The file also contains the graph-theoretic fact `dsep_restrict`:
d-separation survives restriction to an ancestral set containing the relevant vertices.
The main results are `kfac` (with its unfolding lemmas `kfac_of_mem` and `kfac_univ`),
`jointUpTo_apply_prod`, `fullJoint_apply_prod`, `pinTo`, `marginal_ancestral_apply`,
`marginal_eq_restricted_joint` and `dsep_restrict`.
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

/-- Kjernefaktoren til `v` evaluert i en tilordning på `S`; lik 1 hvis `v`
eller en forelder ligger utenfor `S`. Total i `v`, så produkter over ulike
mengder kan sammenlignes uten subtype-bokføring. -/
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

/-- Kjernefaktoren er upåvirket av restriksjon så lenge `v` og foreldrene
ligger i den mindre mengden. -/
lemma kfac_restrict (M : CausalModel G α) {S T : Finset V} (hTS : T ⊆ S)
    (a : Assignment (α := α) S) {v : V} (hv : v ∈ T) (hpa : G.parents v ⊆ T) :
    kfac M T (a.restrict hTS) v = kfac M S a v := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩, dif_pos ⟨hTS hv, hpa.trans hTS⟩]
  rfl

/-- Listeprodukt over `l.attach` er Finset-produkt over `l.toFinset`
når listen er uten duplikater og faktorene stemmer punktvis. -/
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

/-- **Steg 2.** Eksplisitt produktform for `jointUpTo`. -/
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

/-- Kjernefaktoren er upåvirket av transport langs en mengdelikhet. -/
lemma kfac_cast (M : CausalModel G α) {S T : Finset V} (hST : S = T)
    (h : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) :
    kfac M S (cast h a) v = kfac M T a v := by
  subst hST
  rfl

/-- **Steg 3.** Eksplisitt produktform for `fullJoint`. -/
lemma fullJoint_apply_prod (M : CausalModel G α)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) u = ∏ v, kfac M Finset.univ u v := by
  rw [fullJoint_apply M (by rw [G.verticesUpTo_maxRank]) u, jointUpTo_apply_prod]
  exact Finset.prod_congr G.verticesUpTo_maxRank
    (fun v _ => kfac_cast M G.verticesUpTo_maxRank _ u v)

/-- Hjelpemodell for steg 4: kjernene i `A` er punktmasser på `a`,
resten er uendret. Samme graf som `M`, så ingen transport trengs. -/
noncomputable def pinTo (M : CausalModel G α) (A : Finset V)
    (a : Assignment (α := α) A) : CausalModel G α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v p => if hv : v ∈ A then PMF.pure (a ⟨v, hv⟩) else M.kernel v p }

/-- Kjernefaktoren til hjelpemodellen: indikator i `A`, uendret utenfor. -/
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

/-- **Steg 4.** Kjernefaktorene utenfor `A` summerer til 1 over alle
utvidelser av en fast tilordning på `A`. Gjelder for enhver `A`. -/
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

/-- **Steg 5.** Marginalen på en ancestralt lukket mengde er produktet av
kjernefaktorene over mengden. -/
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

/-- Restriction of a causal model to an ancestrally closed vertex set. -/
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

/-- `Eq.mpr` langs en likhet mellom foreldremengder flytter bare
medlemskapsbeviset i kjernens argument. -/
lemma mpr_kernel_apply {v : V} {s t : Finset V} (hst : s = t)
    (h : ((∀ u : {u // u ∈ s}, α u.1) → PMF (α v))
      = ((∀ u : {u // u ∈ t}, α u.1) → PMF (α v)))
    (f : (∀ u : {u // u ∈ t}, α u.1) → PMF (α v))
    (p : ∀ u : {u // u ∈ s}, α u.1) :
    (h.mpr f) p = f (fun u => p ⟨u.1, hst ▸ u.2⟩) := by
  subst hst
  rfl

/-- **Steg 6.** Den restrikterte modellen har samme kjernefaktorer på `A`. -/
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
**Ancestral marginalisation.** The marginal of the full joint onto an
ancestrally closed `A` agrees with the restricted model's joint at every
assignment.

Budget several sessions. This is where `ENNReal` bites hardest.

Note the shape: `marginal` is a `PMF`, so both sides are applications of a
`PMF` to an `Assignment`.
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) :
    (M.marginal A) a = ((CausalModel.restrictTo M A hA).marginal A) a := by
  rw [marginal_ancestral_apply M A hA a,
    marginal_ancestral_apply (CausalModel.restrictTo M A hA) A (fun _ _ _ hw => hw.1) a]
  exact Finset.prod_congr rfl (fun v hv => (kfac_restrictTo M A hA a hv).symm)
/-- Løft en vandring i den induserte grafen til en vandring i `G`. -/
def DAG.Walk.lift {A : Finset V} : {u w : V} →
    DAG.Walk (DAG.induce G A) u w → DAG.Walk G u w
  | _, _, .nil v => .nil v
  | _, _, .fwd e rest => .fwd (DAG.induce_edge e) (lift rest)
  | _, _, .bwd e rest => .bwd (DAG.induce_edge e) (lift rest)

/-- Blokkering bevares under løft. -/
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
d-separation survives restriction to an ancestral set containing the
relevant vertices. Pure graph theory — provable independently of Layer 1,
and a good second task after Layer 0.

Induct on the `DAG.Walk` structure: a walk in `DAG.induce G A` lifts to a
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
