/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Idc.Sound
import PearlDoCalculus.DoCalc.Complete

/-!
# The IDC check and the do-calculus

If the IDC check (`Idc/Check`) says yes for `P(Y | do(X), W)`, the conditional effect can be
rewritten by the do-calculus (`DoCalc.Derives`) into an expression without `do` that
mentions only observed variables (`docs/design-idc.md`, step 4; `idcCheck_derives`).

**How the proof goes.** Write `M` for the moved set and `W' = W ∖ M`.

1. *The frame* (`derives_frame`, in `Idc/Sound`). One step of rule 2 per move, the chain
   rule, a cancellation and marginalization give
   `P(Y | W, do X) ⊢ Q / Σ_Y Q` with `Q = P(Y ∪ W' | do(X ∪ M))`.
2. *The effect left by the check.* The ID check says yes for `Q`, so `Q` is identifiable
   (`IdAlgo.idCheck_sound`), and by the completeness of the do-calculus
   (`DoCalc.docalc_complete`) it derives an expression `e₁` without `do` over observed
   variables. This is where the latents must be roots.
3. *Substitution.* Congruence replaces `Q` by `e₁` in the numerator and under the sum:
   the result is `e₁ / Σ_Y e₁`.

**Main results.** `idcCheck_derives`.
-/

open PearlDoCalculus DAG DoCalculus DoCalc

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The IDC check gives a derivation.** With the latents as roots, `X`, `Y`, `W` observed
and pairwise disjoint: if `idcCheck G U X Y W = true`, then `P(Y | do(X), W)` derives, in
the do-calculus, an expression without `do` that mentions only observed variables. -/
theorem idcCheck_derives (G : DAG V) (U X Y W : Finset V)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hWO : W ⊆ Uᶜ)
    (hYX : Disjoint Y X) (hYW : Disjoint Y W) (hXW : Disjoint X W)
    (h : idcCheck G U X Y W = true) :
    ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (.prob Y W X) e := by
  have hMW := movedSet_subset G X Y W
  have hX' : X ∪ movedSet G X Y W ⊆ Uᶜ := Finset.union_subset hXO (hMW.trans hWO)
  have hY' : Y ∪ (W \ movedSet G X Y W) ⊆ Uᶜ :=
    Finset.union_subset hY (Finset.sdiff_subset.trans hWO)
  have hXY' : ∀ y ∈ Y ∪ (W \ movedSet G X Y W), y ∉ X ∪ movedSet G X Y W := by
    intro y hy hyX
    simp only [Finset.mem_union, Finset.mem_sdiff] at hy hyX
    rcases hy with hyY | ⟨hyW, hyM⟩
    · rcases hyX with hyX | hyM
      · exact Finset.disjoint_left.mp hYX hyY hyX
      · exact Finset.disjoint_left.mp hYW hyY (hMW hyM)
    · rcases hyX with hyX | hyM'
      · exact Finset.disjoint_left.mp hXW hyX hyW
      · exact hyM hyM'
  -- the effect left by the check derives an observed expression without `do`
  obtain ⟨e₁, hf, hv, hd⟩ := docalc_complete G U _ _ hroot hX' hY' hXY'
    fun _ _ => IdAlgo.idCheck_sound G U _ _ hX' hY' h
  exact ⟨.div e₁ (.sum Y e₁), ⟨hf, hf⟩, Finset.union_subset hv (Finset.union_subset hY hv),
    Derives.trans (derives_frame hXO hWO hYX hYW hXW) (Derives.div hd (Derives.sum Y hd))⟩

end Idc
