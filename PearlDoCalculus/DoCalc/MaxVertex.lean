/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.AncStep
import PearlDoCalculus.DoCalc.MaxVertexGraph

/-!
# Splitting off a vertex without children

Phase 4 of `docs/design-docalc-completeness.md` derives c-component factorization and the
`block` step of IDENTIFY by Tian's recursion on a vertex of maximal rank. This file has the
two derivations that each step of that recursion uses, and two small helpers.

**Setting.** `U` are the latent vertices, all roots, and `O = Uᶜ`. `Q[T] = qExpr U T =
P(T ∖ U | do(O ∖ T))` (`DoCalc/AncStep`). The vertex `m ∈ T ∖ U` has no child in `T ∖ U`
(a vertex of maximal rank, `exists_childless`), and `T' = T ∖ {m}` (`T.erase m`). Write
`P_m = P(m | T' ∖ U, do(O ∖ T))`.

**Splitting `Q[T]`** (`Derives.qExpr_split`). `Q[T] = P_m · Q[T']`. The chain rule splits
`P(T ∖ U | do(O ∖ T))` into `P_m · P(T' ∖ U | do(O ∖ T))`, and rule 3 adds the
intervention on `m` in the second factor, since `m` is not an ancestor of `T' ∖ U` in
`G_{X̄}` (`disjoint_ancestors_childless`); `(O ∖ T) ∪ {m} = O ∖ T'`. So `P_m` is the ratio
`Q[T] / Q[T']` (`Derives.prob_split_ratio`).

**Splitting `Q[T ∩ S]`** (`Derives.qExpr_inter_split`). Let `S` be closed in `T` (the
hypothesis `hcl` of `IdentifyDerives.block`) with `m ∈ S`. Then `Q[T ∩ S] = P_m · Q[T' ∩ S]`.
With `W = (T' ∩ S) ∖ U`, `X = O ∖ T` and `A = (T ∖ U) ∖ S`, the intervention of
`Q[T ∩ S]` is on `O ∖ (T ∩ S) = X ∪ A`.

1. The chain rule gives `P(m | W, do(X ∪ A)) · P(W | do(X ∪ A))`.
2. Rule 3 adds the intervention on `m` in the second factor, as above: it becomes
   `Q[T' ∩ S]`.
3. Rule 2, backwards, turns the intervention on `A` in the first factor into conditioning:
   `P(m | W, do(X ∪ A)) = P(m | A ∪ W, do X)`, and `A ∪ W = T' ∖ U`, so this is `P_m`. Its
   side condition is the d-separation `dsepSet_rule2_block`.

The first factor is the same in both splits. This is what makes the recursion work.

**Helpers.** `P(∅ | Z, do X) = 1` for observed `Z` and `X` (`Derives.prob_empty`), from the
chain rule and the two cancellations; so `Q[T] = 1` when `T ∖ U = ∅`
(`Derives.qExpr_of_empty`).

**Main results.** `Derives.prob_empty`, `Derives.qExpr_of_empty`, `Derives.qExpr_split`,
`Derives.prob_split_ratio`, `Derives.qExpr_inter_split`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace Derives

variable {G : DAG V} {U : Finset V}

/-! ## The empty event -/

/-- **`P(∅ | Z, do X) = 1`** for observed `Z` and `X`. The chain rule gives
`P(Z | do X) = P(∅ | Z, do X) · P(Z | do X)`; divide by `P(Z | do X)`. -/
lemma prob_empty (Z X : Finset V) (hO : Z ∪ X ⊆ Uᶜ) :
    Derives G U (.prob ∅ Z X) .one := by
  have hd : (Expr.prob Z ∅ X).Positive U := by
    simpa only [Expr.Positive, Finset.union_empty] using hO
  have hc : Derives G U (.prob Z ∅ X) (.mul (.prob ∅ Z X) (.prob Z ∅ X)) := by
    have h := chain (G := G) (U := U) ∅ Z ∅ X
    rwa [Finset.empty_union, Finset.union_empty] at h
  exact trans (symm (mul_div_cancel _ _ hd))
    (trans (div (symm hc) (refl _)) (div_self _ hd))

/-- **`Q[T] = 1`** when `T` has no observed vertex. -/
lemma qExpr_of_empty {T : Finset V} (hT : T \ U = ∅) : Derives G U (qExpr U T) .one := by
  rw [qExpr, hT]
  exact prob_empty ∅ _ (by rw [Finset.empty_union]; exact Finset.sdiff_subset)

/-! ## Splitting off the vertex -/

variable {T S : Finset V} {m : V}

/-- **Splitting `Q[T]`.** `Q[T] = P(m | T' ∖ U, do(O ∖ T)) · Q[T']` with `T' = T ∖ {m}`,
for `m ∈ T ∖ U` without children in `T ∖ U` and latents that are roots. -/
theorem qExpr_split (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hm : m ∈ T \ U)
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    Derives G U (qExpr U T)
      (.mul (.prob {m} (T.erase m \ U) (Uᶜ \ T)) (qExpr U (T.erase m))) := by
  obtain ⟨hmT, hmU⟩ := Finset.mem_sdiff.mp hm
  have hYW : {m} ∪ T.erase m \ U = T \ U := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  have hX : Uᶜ \ T ∪ {m} = Uᶜ \ T.erase m := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  have h3 := rule3_nonanc (G := G) (U := U) (Uᶜ \ T) (T.erase m \ U) {m} ∅
    (Finset.disjoint_singleton_right.mpr (fun h => (Finset.mem_sdiff.mp h).2 hmT))
    (by rw [Finset.union_empty, Finset.disjoint_left]; intro v; simp; tauto)
    (by
      rw [Finset.union_empty]
      exact Finset.union_subset (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hmU))
        Finset.sdiff_subset)
    (disjoint_ancestors_childless hroot hmax (Finset.Subset.refl _) (by simp))
  have hc := chain (G := G) (U := U) {m} (T.erase m \ U) ∅ (Uᶜ \ T)
  rw [hYW, Finset.union_empty] at hc
  rw [hX] at h3
  rw [qExpr, qExpr]
  exact trans hc (mul (refl _) (symm h3))

/-- **The first factor is a ratio.** `P(m | T' ∖ U, do(O ∖ T)) = Q[T] / Q[T']`, under the
hypotheses of `qExpr_split`. -/
theorem prob_split_ratio (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hm : m ∈ T \ U)
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    Derives G U (.prob {m} (T.erase m \ U) (Uᶜ \ T))
      (.div (qExpr U T) (qExpr U (T.erase m))) :=
  symm (trans (div (qExpr_split hroot hm hmax) (refl _))
    (mul_div_cancel _ _ (positive_qExpr U _)))

/-- **Splitting `Q[T ∩ S]`.** For `S` closed in `T` (the hypothesis of
`IdentifyDerives.block`) with `m ∈ S`: `Q[T ∩ S] = P(m | T' ∖ U, do(O ∖ T)) · Q[T' ∩ S]`,
under the hypotheses of `qExpr_split`. -/
theorem qExpr_inter_split (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S)) (hm : m ∈ T \ U) (hmS : m ∈ S)
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    Derives G U (qExpr U (T ∩ S))
      (.mul (.prob {m} (T.erase m \ U) (Uᶜ \ T)) (qExpr U (T.erase m ∩ S))) := by
  obtain ⟨hmT, hmU⟩ := Finset.mem_sdiff.mp hm
  -- `W = (T' ∩ S) ∖ U`, `X = O ∖ T`, `A = (T ∖ U) ∖ S`
  have hYW : {m} ∪ (T.erase m ∩ S) \ U = (T ∩ S) \ U := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  have hXA : Uᶜ \ T ∪ (T \ U) \ S = Uᶜ \ (T ∩ S) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl, Finset.mem_inter]
    tauto
  have hAW : (T \ U) \ S ∪ (T.erase m ∩ S) \ U = T.erase m \ U := by
    ext v
    rcases eq_or_ne v m with rfl | hv
    · simp [*]
    · simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_erase, hv,
        ne_eq, not_false_eq_true, true_and]
      tauto
  have hX : Uᶜ \ (T ∩ S) ∪ {m} = Uᶜ \ (T.erase m ∩ S) := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  -- rule 2 for the first factor
  have h2 := rule2 (G := G) (U := U) (Uᶜ \ T) {m} ((T \ U) \ S) ((T.erase m ∩ S) \ U)
    (by simp [hmS]) (by rw [Finset.disjoint_left]; intro v; simp; tauto) (by simp [hmT])
    (by intro v; simp; tauto) (dsepSet_rule2_block hroot hcl hmU hmS hmax)
  rw [hXA, hAW] at h2
  -- rule 3 for the second factor
  have h3 := rule3_nonanc (G := G) (U := U) (Uᶜ \ (T ∩ S)) ((T.erase m ∩ S) \ U) {m} ∅
    (Finset.disjoint_singleton_right.mpr (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mpr ⟨hmT, hmS⟩)))
    (by rw [Finset.union_empty, Finset.disjoint_left]; intro v; simp; tauto)
    (by
      rw [Finset.union_empty]
      exact Finset.union_subset (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hmU))
        Finset.sdiff_subset)
    (disjoint_ancestors_childless hroot hmax
      (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.inter_subset_left) (by simp))
  rw [hX] at h3
  have hc := chain (G := G) (U := U) {m} ((T.erase m ∩ S) \ U) ∅ (Uᶜ \ (T ∩ S))
  rw [hYW, Finset.union_empty] at hc
  rw [qExpr, qExpr]
  exact trans hc (mul (symm h2) (symm h3))

end Derives

end DoCalc
