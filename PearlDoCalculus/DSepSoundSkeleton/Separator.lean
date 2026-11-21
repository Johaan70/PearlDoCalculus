import PearlDoCalculus.DSepSoundSkeleton.Factorizes
/-!
# The separator splits the joint, and a product form gives independence

**What it proves.** Three steps from vertex separation to conditional independence.
1. If `Z` separates `x` from `y` in an undirected graph `H` and `x, y ∉ Z`, the vertices
   split as `L ∪ Z ∪ R`, pairwise disjoint, with `x ∈ L`, `y ∈ R` and no edge of `H`
   between `L` and `R` (`separator_partition`).
2. If every family `{w} ∪ parents w` lies in `L ∪ Z` or in `R ∪ Z`, the joint of a causal
   model has the product form `F(L, Z) · Gf(R, Z)` (`joint_splits`).
3. If the marginal on `X ∪ Y ∪ Z` is a product `f(X ∪ Z) · g(Y ∪ Z)`, then `X` and `Y` are
   conditionally independent given `Z` (`condIndep_of_product_form`).

**Why it is needed.** This is layer 2 of the Lauritzen route to the soundness of
d-separation (see `DSepSoundSkeleton.lean`), the probability half after the graph
half. `DSepSound.dsep_sound` gets separation in the moral graph from Lauritzen's theorem,
splits it with `separator_partition`, checks the family condition with
`moral_family_clique`, and then applies `joint_splits` and `condIndep_of_product_form`
(it also reuses `tsum_fixed_Z2`). `SetSound.lean` does the same for sets of vertices,
with its own partition lemma built on `ReachableAvoiding`.

**How the proofs go.**
1. `L` is the set of vertices outside `Z` that can be reached from `x` by a walk avoiding
   `Z`, and `R` is everything else outside `Z`. A walk to `y` must meet `Z`, so `y ∈ R`;
   an edge from `L` to a vertex outside `Z` extends the walk, so that vertex is in `L`.
2. `joint_splits` is `jointUpTo_factorizes` (`DSepSoundSkeleton/Factorizes`) at the top
   level `G.maxRank`, with the casts to `univ` removed by the `restrict_cast_*` lemmas.
3. `CondIndep` is stated multiplicatively,
   `P(X ∪ Y ∪ Z) · P(Z) = P(X ∪ Z) · P(Y ∪ Z)`, so no division and no positivity are
   needed. Each of the three marginals is a sum of the product form over the assignments
   that agree on its set (`marginal_left_factor`, `marginal_right_factor`,
   `marginal_base_factor`). The assignments on `X ∪ Y ∪ Z` split into their `X`, `Y` and
   `Z` parts (`assignmentSplit`), and the sums collapse or factorise
   (`tsum_fixed_XZ2`, `tsum_fixed_YZ2`, `tsum_fixed_Z2`); the two sides then agree by `ring`.

**Main results.** `separator_partition`, `joint_splits` and `condIndep_of_product_form`.
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

/-! ## A separator partitions the vertices

Once separation is undirected the argument is algebraic; graphs enter only
through the clique condition.

If `Z` separates `x` from `y` in `H`, the vertex set splits as
`L ∪ Z ∪ R` with no `L`–`R` edge, `x ∈ L`, `y ∈ R`. Every clique lies
wholly in `L ∪ Z` or wholly in `R ∪ Z`. Each factor `P(v | parents v)` is
supported on the family clique `{v} ∪ parents v` (`moral_family_clique`), so the
product splits as `f(L,Z) · g(R,Z)`, which gives `CondIndep` as already defined.
-/
/-- `v` can be reached from `x` by a walk in `H` that does not touch `Z`. -/
def ReachableAvoiding (H : SimpleGraph V) (Z : Finset V) (x v : V) : Prop :=
  ∃ p : H.Walk x v, ∀ z ∈ Z, z ∉ p.support

/-- Reflexivity, given that `x` itself does not lie in `Z`. -/
lemma reachableAvoiding_refl {H : SimpleGraph V} {Z : Finset V} {x : V} (hxZ : x ∉ Z) :
    ReachableAvoiding H Z x x :=
  ⟨SimpleGraph.Walk.nil, by
    intro z hz hzmem
    simp at hzmem
    subst hzmem
    exact hxZ hz⟩


/-- A separator partitions the graph with no crossing edges. -/
lemma separator_partition {H : SimpleGraph V} {Z : Finset V} {x y : V}
    (h : Separates H Z x y) (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    ∃ L R : Finset V,
      x ∈ L ∧ y ∈ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  classical
  set L := Finset.univ.filter (fun v => v ∉ Z ∧ ReachableAvoiding H Z x v) with hLdef
  set R := Finset.univ \ (L ∪ Z) with hRdef
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxZ, reachableAvoiding_refl hxZ⟩
  · simp only [hRdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, hLdef,
      Finset.mem_filter, not_or, not_and]
    refine ⟨?_, hyZ⟩
    intro _ hra
    obtain ⟨p, hp⟩ := hra
    obtain ⟨z, hzZ, hzmem⟩ := h p
    exact absurd hzmem (hp z hzZ)
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inl hvL)
  · rw [Finset.disjoint_left]
    intro v hvL hvZ
    simp only [hLdef, Finset.mem_filter] at hvL
    exact hvL.2.1 hvZ
  · rw [Finset.disjoint_left]
    intro v hvR hvZ
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inr hvZ)
  · rw [hRdef]
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hv : v ∈ L ∪ Z
    · rcases Finset.mem_union.mp hv with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
    · exact Or.inr (fun hc => hv (Finset.mem_union.mpr hc))
  · intro u huL w hwR hadj
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at huL
    obtain ⟨huZ, pu, hpu⟩ := huL
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and,
      not_or, hLdef, Finset.mem_filter, not_and] at hwR
    exact hwR.1 hwR.2 ⟨pu.concat hadj, by
      intro z hz hzmem
      rw [SimpleGraph.Walk.support_concat] at hzmem
      simp only [List.mem_append, List.mem_singleton] at hzmem
      rcases hzmem with h1 | h1
      · exact hpu z hz h1
      · subst h1; exact hwR.2 hz⟩

/-! ## The joint splits along the separator -/

/--
The joint splits into a product over the two sides of the separator: if every family
`{w} ∪ parents w` lies in `L ∪ Z` or in `R ∪ Z`, the marginal on `L ∪ R ∪ Z` (all
vertices) is a function of the `L` and `Z` coordinates times a function of the `R` and
`Z` coordinates.

The restrictions use `subset_union3_left` and its siblings from `CausalModel.lean`,
the same subset proofs that `CondIndep` uses.
-/
theorem joint_splits (M : CausalModel G α) (L Z R : Finset V)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) L → Assignment (α := α) Z → ENNReal)
      (Gf : Assignment (α := α) R → Assignment (α := α) Z → ENNReal),
      ∀ a : Assignment (α := α) (L ∪ R ∪ Z),
        (M.marginal (L ∪ R ∪ Z)) a =
          F (a.restrict (subset_union3_left L R Z)) (a.restrict (subset_union3_right L R Z)) *
          Gf (a.restrict (subset_union3_mid L R Z)) (a.restrict (subset_union3_right L R Z)) := by
  have htypeU : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank]
  have hLu : Assignment (α := α) L = Assignment (α := α) (L ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hZu : Assignment (α := α) Z = Assignment (α := α) (Z ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hRu : Assignment (α := α) R = Assignment (α := α) (R ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  obtain ⟨F0, Gf0, hF0⟩ := jointUpTo_factorizes M L Z R G.maxRank hLZ hLR hZR hcover hclique
  refine ⟨fun p q => F0 (cast hLu p) (cast hZu q),
    fun p q => Gf0 (cast hRu p) (cast hZu q), ?_⟩
  intro a
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  simp only [fullJoint_apply M htypeU, hF0]
  have hcov2 : L ∪ R ∪ Z = Finset.univ := by
    rw [← hcover]
    ext x
    simp
    tauto
  have htypeA : Assignment (α := α) (L ∪ R ∪ Z)
      = Assignment (α := α) (Finset.univ : Finset V) := by
    rw [hcov2]
  simp only [eq_restrict_iff_eq_cast (L ∪ R ∪ Z) hcov2 htypeA]
  rw [tsum_ite_eq]
  simp only [cast_cast]
  rw [restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) L
      (L ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hLu a (subset_union3_left L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) Z
      (Z ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hZu a (subset_union3_right L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) R
      (R ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hRu a (subset_union3_mid L R Z)]
/-! ## From a product form to conditional independence -/

/-- Restriction composes: `X ∪ Z`, then `X`, is `X` directly. -/
@[simp] lemma restrict_XZ_X (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_left X Y Z) := rfl

/-- Restriction composes: `X ∪ Z`, then `Z`, is `Z` directly. -/
@[simp] lemma restrict_XZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl

/-- Restriction composes: `Y ∪ Z`, then `Y`, is `Y` directly. -/
@[simp] lemma restrict_YZ_Y (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_mid X Y Z) := rfl

/-- Restriction composes: `Y ∪ Z`, then `Z`, is `Z` directly. -/
@[simp] lemma restrict_YZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl
/-- The marginal on `X ∪ Z` is `f` times the sum of the `g` factors. -/
lemma marginal_left_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (X ∪ Z)) (w.restrict (subset_union3_left_right X Y Z)) =
      f (w.restrict (subset_union3_left_right X Y Z)) *
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) =
           u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_left_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_left.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_left_right X Y Z) =
      u.restrict (subset_union3_left_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- The marginal on `Y ∪ Z` is the sum of the `f` factors times `g`. -/
lemma marginal_right_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (Y ∪ Z)) (w.restrict (subset_union3_mid_right X Y Z)) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) =
           u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) *
      g (w.restrict (subset_union3_mid_right X Y Z)) := by
  rw [← marginal_restrict M (subset_union3_mid_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_right.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_mid_right X Y Z) =
      u.restrict (subset_union3_mid_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- A sum over a disjoint union factorises when the summand does. -/
lemma tsum_assignmentSplit (s t : Finset V) (h : Disjoint s t)
    (F : Assignment (α := α) s → ENNReal)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        F ((assignmentSplit s t h u).1) * Gf ((assignmentSplit s t h u).2) =
      (∑' a : Assignment (α := α) s, F a) * (∑' b : Assignment (α := α) t, Gf b) := by
  rw [(assignmentSplit s t h).tsum_eq (fun p => F p.1 * Gf p.2)]
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
/-- When the first component is fixed, the sum collapses to the sum over the second. -/
lemma tsum_assignmentSplit_fixed_left (s t : Finset V) (h : Disjoint s t)
    (a0 : Assignment (α := α) s)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        (if a0 = (assignmentSplit s t h u).1 then Gf ((assignmentSplit s t h u).2) else 0) =
      ∑' b : Assignment (α := α) t, Gf b := by
  rw [(assignmentSplit s t h).tsum_eq
    (fun p => if a0 = p.1 then Gf p.2 else 0)]
  rw [ENNReal.tsum_prod']
  have h1 : ∀ a : Assignment (α := α) s,
      (∑' b : Assignment (α := α) t, if a0 = a then Gf b else 0)
      = if a0 = a then (∑' b, Gf b) else 0 := by
    intro a
    by_cases ha : a0 = a
    · simp [ha]
    · simp [ha]
  simp only [h1]
  simp only [eq_comm (a := a0)]
  rw [tsum_ite_eq]
/-- The first component of the split is the restriction. -/
@[simp] lemma assignmentSplit_fst (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).1 = u.restrict Finset.subset_union_left := rfl

/-- The second component of the split is the restriction. -/
@[simp] lemma assignmentSplit_snd (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).2 = u.restrict Finset.subset_union_right := rfl
/-- An assignment is the reconstruction from its own components. -/
@[simp] lemma assignmentSplit_symm_restrict (s t : Finset V) (h : Disjoint s t)
    (a : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h).symm
      (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right) = a := by
  have hp : (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right)
      = assignmentSplit s t h a := rfl
  rw [hp, Equiv.symm_apply_apply]
/-- Two assignments are equal exactly when both components are equal. -/
lemma assignment_ext_split (s t : Finset V) (h : Disjoint s t)
    (a b : Assignment (α := α) (s ∪ t)) :
    a = b ↔ (a.restrict Finset.subset_union_left = b.restrict Finset.subset_union_left
           ∧ a.restrict Finset.subset_union_right = b.restrict Finset.subset_union_right) := by
  constructor
  · intro hab
    subst hab
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have ha := assignmentSplit_symm_restrict s t h a
    have hb := assignmentSplit_symm_restrict s t h b
    rw [← ha, ← hb, h1, h2]
/-- With `X ∪ Z` fixed, the sum collapses to the sum over `Y`. -/
lemma tsum_fixed_XZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (a0 : Assignment (α := α) (X ∪ Z))
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' b : Assignment (α := α) Y, Gf b (a0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z))
             (a0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : a0 = u.restrict (subset_union3_left_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (X ∪ Z) Y := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY, hYZ.symm⟩
  rw! [Finset.union_assoc, Finset.union_comm Y Z, ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (X ∪ Z) Y hd a0
    (fun b => Gf b (a0.restrict Finset.subset_union_right))
/-- With `Y ∪ Z` fixed, the sum collapses to the sum over `X`. -/
lemma tsum_fixed_YZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (b0 : Assignment (α := α) (Y ∪ Z))
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' a : Assignment (α := α) X, F a (b0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z))
             (b0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : b0 = u.restrict (subset_union3_mid_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (Y ∪ Z) X := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY.symm, hXZ.symm⟩
  rw! [Finset.union_comm X Y, Finset.union_assoc, Finset.union_comm X Z,
    ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (Y ∪ Z) X hd b0
    (fun a => F a (b0.restrict Finset.subset_union_right))
/-- With only `Z` fixed, the sum factorises into the product of the sums over `X` and
over `Y`. -/
lemma tsum_fixed_Z2 (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (c0 : Assignment (α := α) Z)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      (∑' a : Assignment (α := α) X, F a c0) * (∑' b : Assignment (α := α) Y, Gf b c0) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) c0 *
             Gf (u.restrict (subset_union3_mid X Y Z)) c0 else 0) := by
    intro u
    by_cases hu : c0 = u.restrict (subset_union3_right X Y Z)
    · simp [hu]
    · simp [hu]
  simp only [step]
  have hd : Disjoint Z (X ∪ Y) := by
    simp [Finset.disjoint_union_right]
    exact ⟨hXZ.symm, hYZ.symm⟩
  rw! [Finset.union_comm (X ∪ Y) Z]
  have hXY_sub : X ∪ Y ⊆ Z ∪ (X ∪ Y) := Finset.subset_union_right
  simp only [← Assignment.restrict_restrict hXY_sub Finset.subset_union_left,
    ← Assignment.restrict_restrict hXY_sub Finset.subset_union_right,
    ← assignmentSplit_snd Z (X ∪ Y) hd, ← assignmentSplit_fst Z (X ∪ Y) hd]
  rw [tsum_assignmentSplit_fixed_left Z (X ∪ Y) hd c0
    (fun v => F (v.restrict Finset.subset_union_left) c0 *
              Gf (v.restrict Finset.subset_union_right) c0)]
  exact tsum_assignmentSplit X Y hXY (fun a => F a c0) (fun b => Gf b c0)




/-- The marginal on `Z` is the sum of the product over all assignments that agree on
`Z`. -/
lemma marginal_base_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal Z) (w.restrict (subset_union3_right X Y Z)) =
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_right X Y Z) =
           u.restrict (subset_union3_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) *
             g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_right X Y Z), PMF.map_apply]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_right X Y Z) =
      u.restrict (subset_union3_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]


/--
A product form gives `CondIndep` directly, since `CondIndep` is already
multiplicative: no division, no positivity side conditions.
The hypothesis `hfactor` says the marginal on `X ∪ Y ∪ Z` factors into a function `f`
of `X ∪ Z` and a function `g` of `Y ∪ Z`, as `joint_splits` provides; `hf` and `hg`
write `f` and `g` with separate `X`, `Y` and `Z` arguments.
-/
theorem condIndep_of_product_form (M : CausalModel G α) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal)
    (hf : ∀ a : Assignment (α := α) (X ∪ Z),
      f a = F (a.restrict Finset.subset_union_left) (a.restrict Finset.subset_union_right))
    (hg : ∀ b : Assignment (α := α) (Y ∪ Z),
      g b = Gf (b.restrict Finset.subset_union_left) (b.restrict Finset.subset_union_right))
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z))) :
    CondIndep M X Y Z := by
  intro w
  rw [hfactor w]
  rw [marginal_left_factor M X Y Z f g hfactor w,
      marginal_right_factor M X Y Z f g hfactor w,
      marginal_base_factor M X Y Z f g hfactor w]
  have key : (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
      if w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)
      then f (u.restrict (subset_union3_left_right X Y Z)) *
           g (u.restrict (subset_union3_mid_right X Y Z)) else 0) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) = u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0) *
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) = u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) := by
    simp only [hf, hg, restrict_XZ_X, restrict_XZ_Z, restrict_YZ_Y, restrict_YZ_Z]
    rw [tsum_fixed_Z2 X Y Z hXY hXZ hYZ (w.restrict (subset_union3_right X Y Z)) F Gf,
      tsum_fixed_XZ2 X Y Z hXY hYZ (w.restrict (subset_union3_left_right X Y Z)) Gf,
      tsum_fixed_YZ2 X Y Z hXY hXZ (w.restrict (subset_union3_mid_right X Y Z)) F]
    simp only [Assignment.restrict_restrict]
    ring
  rw [key]
  ring


end PearlDoCalculus
