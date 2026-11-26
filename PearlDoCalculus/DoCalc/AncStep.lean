/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.OuterFrame

/-!
# C-factors as expressions, and the `anc` step

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy") follows a run of Tian's IDENTIFY, written as the inductive predicate
`Identification.CFactor.IdentifyDerives`. Its objects are c-factors `Q[T]` of sets `T` of
vertices, which may contain latent vertices. This file gives the c-factor a syntax, and
derives the `anc` step of IDENTIFY and its base case in the calculus `Derives`.

**The c-factor.** With `O = Uᶜ` the observed vertices,

  `Q[T] = P(T ∩ O | do(O ∖ T))`,   `qExpr U T = prob (T ∖ U) ∅ (Uᶜ ∖ T)`.

It is a `prob` term over observed variables, so it is a safe divisor (`positive_qExpr`).
It depends only on the observed part of `T` (`qExpr_sdiff`). For an observed set `D` it is
the term `P(D | do(O ∖ D))` of the outer frame (`qExpr_of_subset`,
`Derives.query_ancestral_qExpr`).

**Base case** (step 3 of the strategy). `Q[V] = P(O)` has no intervention
(`qExpr_univ`, `doFree_qExpr_univ`).

**The `anc` step** (step 4). Let `T ∩ S` be ancestral inside `T`: every parent in `T` of a
vertex of `T ∩ S` lies in `S`, the hypothesis of `IdentifyDerives.anc`. Then

  `Q[T ∩ S] = Σ_{(T ∖ S) ∩ O} Q[T]`   (`Derives.anc_step`).

With `Y = (T ∩ S) ∖ U`, `X = O ∖ T` and `Z = (T ∖ S) ∖ U`, the intervention of `Q[T ∩ S]`
is on `O ∖ (T ∩ S) = X ∪ Z`.

1. *Rule 3* removes the intervention on `Z` (`Derives.query_rule3_nonanc`): no vertex of
   `Z` is an ancestor of `Y` in `G_{X̄}` (`disjoint_ancestors_anc`). A directed path from
   `T ∖ S` in `G_{X̄}` stays in `T ∖ S` (`mem_of_reaches_anc`): it cannot enter an observed
   vertex outside `T`, since those are in `X` and have no parents in `G_{X̄}`; it cannot
   enter a latent vertex, since latents are roots; and it cannot step from `T ∖ S` into
   `T ∩ S`, by the hypothesis of the step.
2. *Marginalization* over `Z` gives `P(Y | do X) = Σ_Z P(Y ∪ Z | do X)`, and
   `Y ∪ Z = T ∖ U`.

This is the only place where the latents must be roots (`hroot`, as in
`Hedge.idCheck_iff`).

**Main results.** `qExpr`, `positive_qExpr`, `qExpr_sdiff`, `qExpr_of_subset`,
`qExpr_univ`, `doFree_qExpr_univ`, `Derives.query_ancestral_qExpr`, `mem_of_reaches_anc`,
`disjoint_ancestors_anc`, `Derives.anc_step`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The c-factor as an expression -/

/-- **The c-factor** `Q[T] = P(T ∩ O | do(O ∖ T))` of a set `T` of vertices, which may
contain latent vertices, with `O = Uᶜ`. -/
def qExpr (U T : Finset V) : Expr V := .prob (T \ U) ∅ (Uᶜ \ T)

/-- `Q[T]` is a `prob` term over observed variables, so it is a safe divisor. -/
lemma positive_qExpr (U T : Finset V) : (qExpr U T).Positive U := by
  simp only [qExpr, Expr.Positive, Finset.union_empty]
  exact Finset.union_subset (fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2)
    Finset.sdiff_subset

/-- The variables of `Q[T]` are observed. -/
lemma vars_qExpr_subset (U T : Finset V) : (qExpr U T).vars ⊆ Uᶜ :=
  positive_qExpr U T

/-- `Q[T]` depends only on the observed part of `T`. -/
lemma qExpr_sdiff (U T : Finset V) : qExpr U (T \ U) = qExpr U T := by
  have h : Uᶜ \ (T \ U) = Uᶜ \ T := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_compl]
    tauto
  simp only [qExpr, Finset.sdiff_idem, h]

/-- For an observed set `D`, `Q[D] = P(D | do(O ∖ D))`. -/
lemma qExpr_of_subset (U : Finset V) {D : Finset V} (hD : D ⊆ Uᶜ) :
    qExpr U D = .prob D ∅ (Uᶜ \ D) := by
  rw [qExpr, Finset.sdiff_eq_self_of_disjoint (Finset.subset_compl_iff_disjoint_right.mp hD)]

/-- **The base case.** `Q[V] = P(O)`. -/
lemma qExpr_univ (U : Finset V) : qExpr U Finset.univ = .prob Uᶜ ∅ ∅ := by
  rw [qExpr, ← Finset.compl_eq_univ_sdiff,
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)]

/-- `Q[V]` has no intervention, and its variables are observed. -/
lemma doFree_qExpr_univ (U : Finset V) :
    (qExpr U Finset.univ).DoFree ∧ (qExpr U Finset.univ).vars ⊆ Uᶜ :=
  ⟨by rw [qExpr_univ]; rfl, vars_qExpr_subset U _⟩

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **The outer frame with c-factors.** `P(Y | do(X)) = Σ_{D ∖ Y} Q[D]`, for an observed
set `D` under the hypotheses of `query_ancestral`. -/
theorem query_ancestral_qExpr (X Y D : Finset V) (hXO : X ⊆ Uᶜ) (hDO : D ⊆ Uᶜ)
    (hYD : Y ⊆ D) (hDX : Disjoint D X)
    (hD : ∀ v ∈ ancestors (cutIn G X) D, v ∉ U → v ∉ X → v ∈ D) :
    Derives G U (Expr.query Y X) (.sum (D \ Y) (qExpr U D)) := by
  rw [qExpr_of_subset U hDO]
  exact query_ancestral X Y D hXO hYD hDX hD

end Derives

/-! ## The `anc` step -/

section AncStep

variable {G : DAG V} {U T S : Finset V}

/-- **Directed paths from `T ∖ S` stay in `T ∖ S`**, in `G` without the edges into the
observed vertices outside `T`, when the latents are roots and `T ∩ S` is ancestral inside
`T`. -/
lemma mem_of_reaches_anc (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S) {z w : V} (hz : z ∈ T) (hzS : z ∉ S)
    (hr : (cutIn G (Uᶜ \ T)).Reaches z w) : w ∈ T ∧ w ∉ S := by
  induction hr with
  | refl => exact ⟨hz, hzS⟩
  | @tail b c _ e ih =>
    obtain ⟨hb, hbS⟩ := ih
    obtain ⟨e, hc⟩ := e
    have hcU : c ∉ U := fun hcU => hroot c hcU b e
    have hcT : c ∈ T := by
      by_contra hcT
      exact hc (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hcU, hcT⟩)
    exact ⟨hcT, fun hcS => hbS (hS c (Finset.mem_inter.mpr ⟨hcT, hcS⟩) b hb e)⟩

/-- **No vertex of `(T ∖ S) ∩ O` is an ancestor of `(T ∩ S) ∩ O`** in `G` without the edges
into the observed vertices outside `T`, under the hypotheses of `mem_of_reaches_anc`. -/
lemma disjoint_ancestors_anc (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S) :
    Disjoint ((T \ S) \ U) (ancestors (cutIn G (Uᶜ \ T)) ((T ∩ S) \ U)) := by
  rw [Finset.disjoint_left]
  intro z hz hzA
  obtain ⟨y, hy, hr⟩ := mem_ancestors_iff.mp hzA
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hz hy
  exact (mem_of_reaches_anc hroot hS hz.1.1 hz.1.2 hr).2 hy.1.2

/-- **The `anc` step.** `Q[T ∩ S] = Σ_{(T ∖ S) ∩ O} Q[T]` when `T ∩ S` is ancestral inside
`T` (the hypothesis of `IdentifyDerives.anc`) and the latents are roots. -/
theorem Derives.anc_step (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hS : ∀ v ∈ T ∩ S, ∀ p ∈ T, G.edge p v → p ∈ S) :
    Derives G U (qExpr U (T ∩ S)) (.sum ((T \ S) \ U) (qExpr U T)) := by
  -- `Y = (T ∩ S) ∖ U`, `X = Uᶜ ∖ T`, `Z = (T ∖ S) ∖ U`
  have hXZ : Uᶜ \ (T ∩ S) = (Uᶜ \ T) ∪ ((T \ S) \ U) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  have hYZ : (T ∩ S) \ U ∪ (T \ S) \ U = T \ U := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  have hdXZ : Disjoint (Uᶜ \ T) ((T \ S) \ U) := by
    rw [Finset.disjoint_left]
    intro v
    simp only [Finset.mem_sdiff, Finset.mem_compl]
    tauto
  have hdYX : Disjoint ((T ∩ S) \ U) (Uᶜ \ T) := by
    rw [Finset.disjoint_left]
    intro v
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
    tauto
  have hdZ : Disjoint ((T \ S) \ U) ((T ∩ S) \ U ∪ ∅ ∪ (Uᶜ \ T)) := by
    rw [Finset.disjoint_left]
    intro v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
      Finset.notMem_empty]
    tauto
  have hO : (T \ S) \ U ∪ (Uᶜ \ T) ⊆ Uᶜ := by
    intro v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_compl]
    tauto
  have h3 := Derives.query_rule3_nonanc (G := G) (U := U) (Uᶜ \ T) ((T ∩ S) \ U)
    ((T \ S) \ U) hdXZ hdYX hO (disjoint_ancestors_anc hroot hS)
  have hm := Derives.marg (G := G) (U := U) ((T ∩ S) \ U) ∅ (Uᶜ \ T) ((T \ S) \ U) hdZ
  rw [hYZ] at hm
  rw [qExpr, qExpr, hXZ]
  exact Derives.trans h3 hm

end AncStep

end DoCalc
