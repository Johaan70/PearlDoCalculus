/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Components
import PearlDoCalculus.DoCalc.Identify
import PearlDoCalculus.DoCalc.Products
import PearlDoCalculus.Hedge.Complete

/-!
# Completeness of the do-calculus for identification

This file proves the goal of `docs/design-docalc-completeness.md`: every identifiable
effect `P(Y | do(X))` can be rewritten, by the three rules of the do-calculus and the
fixed probability steps of `Derives`, into an expression without `do` that mentions only
observed variables (Huang and Valtorta 2006; Shpitser and Pearl 2006).

**The result** (`docalc_complete`). With the latents `U` as roots, `X` and `Y` observed and
disjoint, if `P(Y | do(X))` is identifiable for every family of nonempty value types, then
`P(Y | do(X))` derives an expression `e` with `e.DoFree` and `e.vars ⊆ Uᶜ`. The hypotheses
are those of `Hedge.idCheck_iff`.

**How the proof goes** (steps 1, 2 and 6 of "Completeness: proof strategy" in the note).
Write `S = An(Y)` in `G_{X̄}`, `D = (S ∖ U) ∖ X`, and `C_y` for the c-component of `y` in
`G_{X̄}[S]`, as the ID check does.

1. *From identifiability to a run.* `Hedge.idCheck_iff` gives `idCheck G U X Y = true`, so
   IDENTIFY reaches every `C_y` from `V` (`identifyDerives_of_idCheck`).
2. *The outer frame.* `P(Y | do(X)) = Σ_{D ∖ Y} Q[D]` (`Derives.query_ancIn`,
   `qExpr_of_subset`).
3. *The factorization.* `Q[D] = ∏ Q[C]` over the distinct `C_y`, `y ∈ D`
   (`Derives.qExpr_factor_ccIn`).
4. *Each factor.* The run of IDENTIFY for `C_y` is one derivation of `Q[C_y]` into an
   observed expression without `do` (`Derives.of_identifyDerives_univ`).
5. *Assembly.* The product of these expressions (`Derives.exists_prodExpr`), summed over
   `D ∖ Y`, is the expression `e`.

Every hypothesis is used: `hroot` by `idCheck_iff` and by every step of the derivation,
`hXO`, `hY` and `hXY` by `idCheck_iff` and the outer frame, and `h` to get the run.

**Main results.** `docalc_complete`.
-/

open PearlDoCalculus DAG DoCalculus IdAlgo Identification

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Completeness of the do-calculus for identification** (Huang and Valtorta 2006;
Shpitser and Pearl 2006). With the latent nodes `U` as roots, `X` and `Y` observed and
`X ∩ Y = ∅`: if `P(Y | do(X))` is identifiable for every choice of nonempty value types,
then it derives, in the do-calculus, an expression without `do` that mentions only observed
variables. -/
theorem docalc_complete (G : DAG V) (U X Y : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hXY : ∀ y ∈ Y, y ∉ X)
    (h : ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y) :
    ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (Expr.query Y X) e := by
  -- 1. the ID check says yes
  have hc : idCheck G U X Y = true := (Hedge.idCheck_iff G U X Y hroot hXO hY hXY).mpr h
  -- 2. the outer frame `P(Y | do(X)) = Σ_{D ∖ Y} Q[D]`
  have hDO : (ancIn (cutIn G X) Finset.univ Y \ U) \ X ⊆ Uᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
  have h1 := Derives.query_ancIn (G := G) (U := U) X Y hXO hY (Finset.disjoint_left.mpr hXY)
  rw [← qExpr_of_subset U hDO] at h1
  -- 3. the factorization `Q[D] = ∏ Q[C_y]`
  have h2 := Derives.qExpr_factor_ccIn hroot hXO (ancIn_cutIn_closed G X Y)
  -- 4. each factor `Q[C_y]` derives an observed expression without `do`
  obtain ⟨E, hE, hvE, hdE⟩ := Derives.exists_prodExpr (G := G) (U := U)
      ((((ancIn (cutIn G X) Finset.univ Y \ U) \ X).image
        (fun y => ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})).toList.map
          (qExpr U)) fun e he => by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hC)
    simp only [Finset.mem_sdiff] at hy
    exact Derives.of_identifyDerives_univ hroot
      (identifyDerives_of_idCheck hc y hy.1.1 hy.1.2 hy.2)
  -- 5. assembly
  exact ⟨.sum _ E, hE, Expr.vars_sum_subset (Finset.sdiff_subset.trans hDO) hvE,
    Derives.trans h1 (Derives.sum _ (Derives.trans h2 hdE))⟩

end DoCalc
