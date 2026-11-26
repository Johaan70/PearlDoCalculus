/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Complete
import PearlDoCalculus.DoCalc.Soundness

/-!
# The triangle: the ID check, identifiability and derivability

This file closes the triangle of `docs/design-docalc-completeness.md`, section "Goal". With
the latents `U` as roots, `X` and `Y` observed and disjoint (the hypotheses of
`Hedge.idCheck_iff`), the following three statements are equivalent.

1. The ID check says yes: `idCheck G U X Y = true`.
2. The effect `P(Y | do(X))` is identifiable for every family of nonempty value types.
3. The effect is derivable: `P(Y | do(X))` derives, in the do-calculus, an expression
   without `do` that mentions only observed variables.

**How the proof goes.** Each arrow is a theorem proved elsewhere.

* `1 ↔ 2` is the completeness of the ID algorithm, `Hedge.idCheck_iff`.
* `2 → 3` is the completeness of the do-calculus, `docalc_complete` (`DoCalc/Complete`).
* `3 → 2` is the soundness of derivations: a derivation is valid in every model with a
  positive observed marginal (`derives_sound`), so the effect equals an expression that
  two such models with the same observed marginal evaluate alike
  (`identifiable_of_derives`, `DoCalc/Soundness`).

The result is stated with Mathlib's `List.TFAE` (`docalc_triangle`), and as two
equivalences (`docalc_triangle_iff`).

**Main results.** `docalc_triangle`, `docalc_triangle_iff`.
-/

open PearlDoCalculus DAG DoCalculus IdAlgo Identification

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The triangle.** With the latent nodes `U` as roots, `X` and `Y` observed and
`X ∩ Y = ∅`, these are equivalent: the ID check says yes; `P(Y | do(X))` is identifiable
for every choice of nonempty value types; and `P(Y | do(X))` derives, in the do-calculus,
an expression without `do` that mentions only observed variables. -/
theorem docalc_triangle (G : DAG V) (U X Y : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hXY : ∀ y ∈ Y, y ∉ X) :
    List.TFAE [idCheck G U X Y = true,
      ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y,
      ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (Expr.query Y X) e] := by
  tfae_have 1 ↔ 2 := Hedge.idCheck_iff G U X Y hroot hXO hY hXY
  tfae_have 2 → 3 := docalc_complete G U X Y hroot hXO hY hXY
  tfae_have 3 → 2 := fun ⟨_, hfree, hvars, hd⟩ _ _ => identifiable_of_derives hd hfree hvars
  tfae_finish

/-- **The triangle as two equivalences.** Under the hypotheses of `docalc_triangle`: the
ID check says yes iff `P(Y | do(X))` is identifiable for every choice of nonempty value
types, and that holds iff `P(Y | do(X))` derives an observed expression without `do`. -/
theorem docalc_triangle_iff (G : DAG V) (U X Y : Finset V)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ)
    (hXY : ∀ y ∈ Y, y ∉ X) :
    (idCheck G U X Y = true ↔
        ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y) ∧
      ((∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y) ↔
        ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (Expr.query Y X) e) :=
  ⟨(docalc_triangle G U X Y hroot hXO hY hXY).out 0 1,
    (docalc_triangle G U X Y hroot hXO hY hXY).out 1 2⟩

end DoCalc
