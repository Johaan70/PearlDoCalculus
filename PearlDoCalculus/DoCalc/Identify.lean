/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.BlockStep

/-!
# A run of IDENTIFY as a derivation

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy", step 6) follows a run of Tian's IDENTIFY, written as the inductive predicate
`Identification.CFactor.IdentifyDerives G U T C`: a chain of `anc` and `block` steps from
a set `T` down to a set `C`. This file turns the whole chain into one derivation.

**The result** (`Derives.of_identifyDerives`). If the latents are roots and
`IdentifyDerives G U T C`, then `Q[C]` derives an expression over observed variables whose
only `prob` term is `Q[T]`.

**How the proof goes.** Induction on `IdentifyDerives`.

* `refl`: the expression is `Q[T]` itself.
* `anc`: by induction, `Q[C]` derives an expression `E'` in `Q[T ∩ S]`. The `anc` step
  (`Derives.anc_step`) gives `Q[T ∩ S] = Σ_{(T ∖ S) ∩ O} Q[T]`. Substituting it into `E'`
  (`Derives.substProb`) gives an expression in `Q[T]`.
* `block`: the same, with the `block` step (`Derives.block_step`), which writes
  `Q[T ∩ S]` as an expression in `Q[T]`.

The substitution keeps the form (`Expr.onlyProb_substProb`) and the observed variables
(`Expr.vars_substProb_subset`).

**From `V`** (`Derives.of_identifyDerives_univ`). For `T = V`, the term `Q[V] = P(O)` has
no `do` (`qExpr_univ`), so the expression has no `do` either (`Expr.OnlyProb.doFree`).
This is how each c-component of the ID check gets an expression without `do`.

**Main results.** `Derives.of_identifyDerives`, `Derives.of_identifyDerives_univ`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **A run of IDENTIFY is a derivation.** If the latents are roots and IDENTIFY reaches
`C` from `T`, then `Q[C]` derives an expression over observed variables whose only `prob`
term is `Q[T]`. -/
theorem of_identifyDerives (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {T C : Finset V}
    (h : Identification.CFactor.IdentifyDerives G U T C) :
    ∃ E : Expr V, E.OnlyProb (qExpr U T) ∧ E.vars ⊆ Uᶜ ∧ Derives G U (qExpr U C) E := by
  induction h with
  | refl T => exact ⟨qExpr U T, rfl, vars_qExpr_subset U T, refl _⟩
  | anc T S C hS _ ih =>
    obtain ⟨E', hE', hvE', hd'⟩ := ih
    -- substitute `Q[T ∩ S] = Σ_{(T ∖ S) ∩ O} Q[T]` into `E'`
    have hR : (Expr.sum ((T \ S) \ U) (qExpr U T)).OnlyProb (qExpr U T) := rfl
    have hRv : (Expr.sum ((T \ S) \ U) (qExpr U T)).vars ⊆ Uᶜ :=
      Finset.union_subset (fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2)
        (vars_qExpr_subset U T)
    exact ⟨_, Expr.onlyProb_substProb hR E',
      (Expr.vars_substProb_subset _ _).trans (Finset.union_subset hvE' hRv),
      trans hd' (substProb (anc_step hroot hS) hE')⟩
  | block T S C hcl _ ih =>
    obtain ⟨E', hE', hvE', hd'⟩ := ih
    -- substitute the expression of `Q[T ∩ S]` in `Q[T]` into `E'`
    obtain ⟨R, hR, hRv, hdR⟩ := block_step hroot hcl
    exact ⟨_, Expr.onlyProb_substProb hR E',
      (Expr.vars_substProb_subset _ _).trans (Finset.union_subset hvE' hRv),
      trans hd' (substProb hdR hE')⟩

/-- **A run of IDENTIFY from `V` gives an expression without `do`.** If the latents are
roots and IDENTIFY reaches `C` from `V`, then `Q[C]` derives an expression without `do`
over observed variables. -/
theorem of_identifyDerives_univ (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {C : Finset V}
    (h : Identification.CFactor.IdentifyDerives G U Finset.univ C) :
    ∃ E : Expr V, E.DoFree ∧ E.vars ⊆ Uᶜ ∧ Derives G U (qExpr U C) E := by
  obtain ⟨E, hE, hvE, hd⟩ := of_identifyDerives hroot h
  exact ⟨E, hE.doFree (doFree_qExpr_univ U).1, hvE, hd⟩

end Derives

end DoCalc
