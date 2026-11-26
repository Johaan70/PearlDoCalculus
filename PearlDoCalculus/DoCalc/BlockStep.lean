/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Factorization
import PearlDoCalculus.DoCalc.Subst

/-!
# The `block` step of IDENTIFY as a derivation

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy", step 5) replaces each step of a run of Tian's IDENTIFY (`IdentifyDerives`) by a
derivation. The `anc` step is `Derives.anc_step` (`DoCalc/AncStep`). This file derives the
`block` step: for `S` closed in `T` (the hypothesis `hcl` of `IdentifyDerives.block`), the
c-factor `Q[T ∩ S]` is an expression in `Q[T]` alone.

**The result** (`Derives.block_step`). If the latents are roots and `S` is closed in `T`,
there is an expression `E` whose only `prob` term is `Q[T]` (`E.OnlyProb (qExpr U T)`),
with observed variables only, such that `Q[T ∩ S]` derives `E`. This is the form the
assembly needs: a chain of IDENTIFY steps from `V` to `C` composes, by the substitution
lemma `Derives.substProb`, into an expression for `Q[C]` in `Q[V] = P(O)` alone.

**How the proof goes.** Tian's recursion on a vertex of maximal rank. Strong induction on
the number of observed vertices of `T`.

* If `T ∖ U = ∅`, then `Q[T ∩ S] = 1` (`Derives.qExpr_of_empty`), and `E = 1`.
* Otherwise take `m ∈ T ∖ U` of maximal rank (`exists_childless`) and `T' = T ∖ {m}`. `S` is
  closed in `T'`, so by induction `Q[T' ∩ S]` derives an expression `E'` in `Q[T']`. `T'`
  is ancestral in `T`, because `m` has no child in `T`, so the `anc` step gives
  `Q[T'] = Σ_m Q[T]` (`Derives.qExpr_erase`). Substituting it into `E'` gives an
  expression `E''` in `Q[T]`.
  - If `m ∉ S`, then `T ∩ S = T' ∩ S`, and `E = E''`.
  - If `m ∈ S`, then `Q[T ∩ S] = P_m · Q[T' ∩ S]` (`Derives.qExpr_inter_split`) and
    `P_m = Q[T] / Q[T']` (`Derives.prob_split_ratio`), so
    `E = (Q[T] / Σ_m Q[T]) · E''`.

By construction, `E` is Tian's formula `∏_{v ∈ (T ∩ S) ∖ U} Q[T_{≤v}] / Q[T_{<v}]`, in
the order of the ranks, where `T_{≤v}` (`T_{<v}`) are the observed vertices of `T` up to
(before) `v` in that order, and each `Q[T_{≤v}]` is written as `Q[T]` summed over the
later vertices. Only the form of `E` is stated in Lean, not this explicit product.

**Main results.** `Derives.qExpr_erase`, `Derives.block_step`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **Removing a vertex without children** is an `anc` step: `Q[T ∖ {m}] = Σ_m Q[T]` for
`m ∈ T ∖ U` without children in `T ∖ U`, when the latents are roots. -/
theorem qExpr_erase {T : Finset V} {m : V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hm : m ∈ T \ U) (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    Derives G U (qExpr U (T.erase m)) (.sum {m} (qExpr U T)) := by
  obtain ⟨hmT, hmU⟩ := Finset.mem_sdiff.mp hm
  -- `T ∖ {m}` is ancestral in `T`: `m` is no parent of a vertex of `T`
  have hS : ∀ v ∈ T ∩ T.erase m, ∀ p ∈ T, G.edge p v → p ∈ T.erase m := by
    intro v hv p hp e
    refine Finset.mem_erase.mpr ⟨fun hpm => ?_, hp⟩
    subst hpm
    have hvU : v ∉ U := fun hvU => hroot v hvU p e
    exact hmax v (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).1, hvU⟩) e
  have h := anc_step hroot hS
  have h1 : T ∩ T.erase m = T.erase m := Finset.inter_eq_right.mpr (Finset.erase_subset m T)
  have h2 : (T \ T.erase m) \ U = {m} := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  rwa [h1, h2] at h

/-- **The `block` step.** If the latents are roots and `S` is closed in `T` (the hypothesis
of `IdentifyDerives.block`), then `Q[T ∩ S]` derives an expression over observed variables
whose only `prob` term is `Q[T]`. -/
theorem block_step (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {T S : Finset V}
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S)) :
    ∃ E : Expr V, E.OnlyProb (qExpr U T) ∧ E.vars ⊆ Uᶜ ∧
      Derives G U (qExpr U (T ∩ S)) E := by
  obtain ⟨n, hn⟩ : ∃ n, (T \ U).card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing T with
  | _ n ih =>
  rcases (T \ U).eq_empty_or_nonempty with hT | hT
  · -- no observed vertex: `Q[T ∩ S] = 1`
    have h1 : (T ∩ S) \ U = ∅ := Finset.subset_empty.mp
      (hT ▸ Finset.sdiff_subset_sdiff Finset.inter_subset_left (Finset.Subset.refl U))
    exact ⟨.one, trivial, Finset.empty_subset _, qExpr_of_empty h1⟩
  · obtain ⟨m, hm, hmax⟩ := exists_childless G hT
    have hlt : (T.erase m \ U).card < n := by
      rw [← hn, Finset.erase_sdiff_comm]
      exact Finset.card_erase_lt_of_mem hm
    have hcl' : ∀ u ∈ U, ∀ v ∈ T.erase m, G.edge u v → (u ∈ S ↔ v ∈ S) :=
      fun u hu v hv e => hcl u hu v (Finset.mem_of_mem_erase hv) e
    obtain ⟨E', hE', hvE', hd'⟩ := ih _ hlt hcl' rfl
    -- substitute `Q[T'] = Σ_m Q[T]` into `E'`
    have hR : Derives G U (qExpr U (T.erase m)) (.sum {m} (qExpr U T)) :=
      qExpr_erase hroot hm hmax
    have hRO : (Expr.sum {m} (qExpr U T)).OnlyProb (qExpr U T) := rfl
    have hRv : (Expr.sum {m} (qExpr U T)).vars ⊆ Uᶜ :=
      Finset.union_subset (Finset.singleton_subset_iff.mpr
        (Finset.mem_compl.mpr (Finset.mem_sdiff.mp hm).2)) (vars_qExpr_subset U T)
    have hE''v : (E'.substProb (.sum {m} (qExpr U T))).vars ⊆ Uᶜ :=
      (Expr.vars_substProb_subset _ _).trans (Finset.union_subset hvE' hRv)
    have hd'' := trans hd' (substProb hR hE')
    by_cases hmS : m ∈ S
    · refine ⟨.mul (.div (qExpr U T) (.sum {m} (qExpr U T)))
          (E'.substProb (.sum {m} (qExpr U T))),
        ⟨⟨rfl, hRO⟩, Expr.onlyProb_substProb hRO E'⟩,
        Finset.union_subset (Finset.union_subset (vars_qExpr_subset U T) hRv) hE''v, ?_⟩
      exact trans (qExpr_inter_split hroot hcl hm hmS hmax)
        (mul (trans (prob_split_ratio hroot hm hmax) (div (refl _) hR)) hd'')
    · have hTS : T.erase m ∩ S = T ∩ S := by
        rw [Finset.erase_inter, Finset.erase_eq_of_notMem
          (fun h => hmS (Finset.mem_inter.mp h).2)]
      exact ⟨_, Expr.onlyProb_substProb hRO E', hE''v, hTS ▸ hd''⟩

end Derives

end DoCalc
