/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Idc.Sound
import PearlDoCalculus.DoCalc.Complete

/-!
# The IDC check and the do-calculus

This file links the IDC check (`Idc/Check`) to the derivations of the do-calculus
(`DoCalc.Derives`), in both directions (`docs/design-idc.md`, steps 4 and 5).

**The check gives a derivation** (`idcCheck_derives`). If the check says yes for
`P(Y | do(X), W)`, the conditional effect derives an expression without `do` that
mentions only observed variables. Write `M` for the moved set and `W' = W ∖ M`.

1. *The frame* (`derives_frame`, in `Idc/Sound`). One step of rule 2 per move, the chain
   rule, a cancellation and marginalization give
   `P(Y | W, do X) ⊢ Q / Σ_Y Q` with `Q = P(Y ∪ W' | do(X ∪ M))`.
2. *The effect left by the check.* The ID check says yes for `Q`, so `Q` is identifiable
   (`IdAlgo.idCheck_sound`), and by the completeness of the do-calculus
   (`DoCalc.docalc_complete`) it derives an expression `e₁` without `do` over observed
   variables. This is where the latents must be roots.
3. *Substitution.* Congruence replaces `Q` by `e₁` in the numerator and under the sum:
   the result is `e₁ / Σ_Y e₁`.

**A derivation gives conditional identifiability** (`identifiableCond_of_derives`). If
`P(Y | do(X), W)` derives an expression without `do` over observed variables, then two
models with the same positive observed marginal give `prob Y W X` the same value: by
soundness of derivations (`DoCalc.derives_sound`) it has the value of the expression, and
the expression only reads the observed marginal (`DoCalc.eval_eq_of_doFree`). The bridge
from equal values to the cross-multiplied `IdentifiableCond` is
`identifiableCond_of_eval` (`Idc/Sound`). This direction needs no hypothesis on the
latents, and works for every family of value types.

**Together** (`idcCheck_derives_identifiableCond`): a yes of the check gives a
derivation, and the derivation gives conditional identifiability.

**Main results.** `idcCheck_derives`, `identifiableCond_of_derives`,
`idcCheck_derives_identifiableCond`.
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

/-- **A derivation gives conditional identifiability.** If `P(Y | do(X), W)` derives an
expression without `do` that mentions only observed variables, and `X` and `W` are
observed, then `P(Y | do(X), W)` is identifiable in the sense of `IdentifiableCond`, for
every family of value types. -/
theorem identifiableCond_of_derives {G : DAG V} {α : V → Type*} {U X Y W : Finset V}
    {e : Expr V} (hXO : X ⊆ Uᶜ) (hWO : W ⊆ Uᶜ) (hd : Derives G U (.prob Y W X) e)
    (hfree : e.DoFree) (hvars : e.vars ⊆ Uᶜ) :
    IdentifiableCond G α Uᶜ X Y ∅ W :=
  identifiableCond_of_eval hXO hWO fun M₁ M₂ hM hpos => by
    rw [derives_sound hd M₁ hpos, derives_sound hd M₂ (fun a => hM ▸ hpos a),
      eval_eq_of_doFree hM hfree hvars]

/-- **The IDC check, derivations and identifiability.** With the latents as roots and `X`,
`Y`, `W` observed and pairwise disjoint: if `idcCheck G U X Y W = true`, then
`P(Y | do(X), W)` derives an observed expression without `do`, and every such derivation
makes `P(Y | do(X), W)` identifiable for every family of value types. -/
theorem idcCheck_derives_identifiableCond (G : DAG V) (U X Y W : Finset V)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hWO : W ⊆ Uᶜ)
    (hYX : Disjoint Y X) (hYW : Disjoint Y W) (hXW : Disjoint X W)
    (h : idcCheck G U X Y W = true) :
    ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (.prob Y W X) e ∧
      ∀ α : V → Type*, IdentifiableCond G α Uᶜ X Y ∅ W := by
  obtain ⟨e, hf, hv, hd⟩ := idcCheck_derives G U X Y W hroot hXO hY hWO hYX hYW hXW h
  exact ⟨e, hf, hv, hd, fun _ => identifiableCond_of_derives hXO hWO hd hf hv⟩

end Idc
