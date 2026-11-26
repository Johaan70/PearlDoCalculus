/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.NonAncestors
import PearlDoCalculus.IdAlgo

/-!
# The outer frame: marginalization over an ancestral set

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy", step 2) begins by rewriting the effect `P(Y | do(X))` as a sum over an
ancestral set `D ⊇ Y`:

  `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(O ∖ D))`,

where `O = Uᶜ` are the observed variables. The term `P(D | do(O ∖ D))` is the c-factor
`Q[D]`, and the later steps factor it into the c-factors of the c-components of `D`. This
file derives the equation in the calculus `Derives` (`Derives.query_ancestral`).

**Hypotheses.** `X` is observed, `Y ⊆ D`, `D` is disjoint from `X`, and every observed
ancestor of `D` in `G_{X̄}` that is not in `X` lies in `D`. No hypothesis on the latent
vertices is needed: the ancestors are taken in the graph with the latents.

**How the derivation goes.**

1. *Marginalization* onto `D` (`Derives.marg_superset`):
   `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(X))`.
2. *Rule 3*, backwards, inside the sum: the observed variables `Z = O ∖ D ∖ X` contain no
   ancestor of `D` in `G_{X̄}`, so `P(D | do(X)) = P(D | do(X ∪ Z))`
   (`Derives.query_rule3_nonanc`), and `X ∪ Z = O ∖ D`.

**The bridge to the ID algorithm.** The ID check (`IdAlgo.idCheck`) works with
`S = An(Y)` in `G_{X̄}`, computed as `IdAlgo.ancIn (cutIn G X) univ Y`; it may contain
latent vertices and vertices of `X`. Any set `S ⊇ Y` that is closed under parents in
`G_{X̄}` gives an ancestral set `D = S ∖ U ∖ X` in the sense above
(`Derives.query_ancestral_closed`), and the set of the ID check is such a set
(`Derives.query_ancIn`).

**Main results.** `ancestors_subset_of_closed`, `Derives.query_ancestral`,
`Derives.query_ancestral_closed`, `Derives.query_ancIn`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A set that is closed under parents contains all ancestors of its subsets. -/
lemma ancestors_subset_of_closed {H : DAG V} {S D : Finset V}
    (hS : ∀ v ∈ S, ∀ p, H.edge p v → p ∈ S) (hD : D ⊆ S) : ancestors H D ⊆ S := by
  intro v hv
  obtain ⟨d, hd, hr⟩ := mem_ancestors_iff.mp hv
  have hr' : Relation.ReflTransGen H.edge v d := hr
  clear hv hr
  induction hr' using Relation.ReflTransGen.head_induction_on with
  | refl => exact hD hd
  | head e _ ih => exact hS _ ih _ e

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **The outer frame.** `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(O ∖ D))`, for observed `X`, a
set `D ⊇ Y` disjoint from `X`, and `D` closed under the observed ancestors outside `X` in
`G_{X̄}`. -/
theorem query_ancestral (X Y D : Finset V) (hXO : X ⊆ Uᶜ) (hYD : Y ⊆ D) (hDX : Disjoint D X)
    (hD : ∀ v ∈ ancestors (cutIn G X) D, v ∉ U → v ∉ X → v ∈ D) :
    Derives G U (Expr.query Y X) (.sum (D \ Y) (.prob D ∅ (Uᶜ \ D))) := by
  -- the observed variables outside `D ∪ X`, to be added to the intervention
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset V, Z = (Uᶜ \ D) \ X := ⟨_, rfl⟩
  have hXZ : X ∪ Z = Uᶜ \ D := by
    ext v
    simp only [hZ, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hv | ⟨hv, _⟩)
      · exact ⟨hXO hv, fun hvD => Finset.disjoint_left.mp hDX hvD hv⟩
      · exact hv
    · intro hv
      by_cases hvX : v ∈ X
      · exact Or.inl hvX
      · exact Or.inr ⟨hv, hvX⟩
  have hZO : Z ∪ X ⊆ Uᶜ := by
    rw [Finset.union_comm, hXZ]
    exact Finset.sdiff_subset
  have hZanc : Disjoint Z (ancestors (cutIn G X) D) := by
    rw [Finset.disjoint_left]
    intro v hvZ hvA
    simp only [hZ, Finset.mem_sdiff, Finset.mem_compl] at hvZ
    exact hvZ.1.2 (hD v hvA hvZ.1.1 hvZ.2)
  have h3 : Derives G U (.prob D ∅ (Uᶜ \ D)) (.prob D ∅ X) := by
    rw [← hXZ]
    exact query_rule3_nonanc X D Z (hZ ▸ Finset.disjoint_sdiff) hDX hZO hZanc
  exact trans (marg_superset Y D ∅ X hYD (by rwa [Finset.empty_union])) (sum _ (symm h3))

/-- **The outer frame for a set closed under parents.** Let `S ⊇ Y` be closed under
parents in `G_{X̄}`; it may contain latent vertices and vertices of `X`. Then, with
`D = S ∖ U ∖ X`, `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(O ∖ D))`, for observed `X` and `Y`
with `Y` disjoint from `X`. -/
theorem query_ancestral_closed (X Y S : Finset V) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ)
    (hYX : Disjoint Y X) (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S) (hYS : Y ⊆ S) :
    Derives G U (Expr.query Y X)
      (.sum (((S \ U) \ X) \ Y) (.prob ((S \ U) \ X) ∅ (Uᶜ \ ((S \ U) \ X)))) := by
  refine query_ancestral X Y ((S \ U) \ X) hXO (fun y hy => ?_) Finset.sdiff_disjoint
    (fun v hv hvU hvX => ?_)
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hYS hy, Finset.mem_compl.mp (hY hy)⟩,
      Finset.disjoint_left.mp hYX hy⟩
  · have hDS : (S \ U) \ X ⊆ S := Finset.sdiff_subset.trans Finset.sdiff_subset
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨ancestors_subset_of_closed hS hDS hv, hvU⟩, hvX⟩

/-- **The outer frame of the ID check.** With `S = An(Y)` in `G_{X̄}`, as computed by
`IdAlgo.idCheck`, and `D = S ∖ U ∖ X`: `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(O ∖ D))`, for
observed `X` and `Y` with `Y` disjoint from `X`. -/
theorem query_ancIn (X Y : Finset V) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hYX : Disjoint Y X) :
    Derives G U (Expr.query Y X)
      (.sum (((IdAlgo.ancIn (cutIn G X) Finset.univ Y \ U) \ X) \ Y)
        (.prob ((IdAlgo.ancIn (cutIn G X) Finset.univ Y \ U) \ X) ∅
          (Uᶜ \ ((IdAlgo.ancIn (cutIn G X) Finset.univ Y \ U) \ X)))) :=
  query_ancestral_closed X Y _ hXO hY hYX
    (fun v hv p e => IdAlgo.anc_closed (cutIn G X) Finset.univ Y (Finset.subset_univ Y) p
      (Finset.mem_univ p) ⟨v, hv, e⟩)
    (IdAlgo.anc_sup (cutIn G X) Finset.univ Y)

end Derives

end DoCalc
