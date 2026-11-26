/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.MaxVertex

/-!
# C-component factorization as a derivation

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy", step 2) needs the factorization of a c-factor into the c-factors of its
c-components, not only as an equation between numbers but as a derivation in `Derives`.
This file derives it.

**Binary form** (`Derives.qExpr_factor`). Let the latents be roots and `S` be closed in `T`:
no edge from a latent `u` into `T` has `u ∈ S` and its head outside `S`, or the other way
round (the hypothesis `hcl` of `IdentifyDerives.block`; it is symmetric in `S` and its
complement). Then

  `Q[T] = Q[T ∩ S] · Q[T ∖ S]`.

**How the proof goes.** Strong induction on the number of observed vertices of `T`.

* If `T ∖ U = ∅`, all three c-factors are `P(∅ | do(…)) = 1` (`Derives.qExpr_of_empty`).
* Otherwise take `m ∈ T ∖ U` of maximal rank (`exists_childless`) and `T' = T ∖ {m}`; `S`
  is closed in `T'` too. If `m ∈ S` (`Derives.qExpr_factor_step`):

    `Q[T] = P_m · Q[T']`                       (`Derives.qExpr_split`)
    `    = P_m · (Q[T' ∩ S] · Q[T' ∖ S])`       (induction)
    `    = (P_m · Q[T' ∩ S]) · Q[T ∖ S]`         (`mul_assoc`, and `T' ∖ S = T ∖ S`)
    `    = Q[T ∩ S] · Q[T ∖ S]`                  (`Derives.qExpr_inter_split`, backwards).

  If `m ∉ S`, the same argument for the complement of `S` gives
  `Q[T] = Q[T ∖ S] · Q[T ∩ S]`, and `mul_comm` finishes.

**Many blocks** (`Derives.qExpr_factor_list`). For a list of pairwise disjoint blocks, each
closed in `T`, that cover the observed vertices of `T`,

  `Q[T] = ∏ᵢ Q[T ∩ Sᵢ]`,

with the product of a list of expressions written `prodExpr` (`one` for the empty list).
It follows from the binary form by induction on the list: split off the first block, and
the others are closed in, and cover, what is left.

**Main results.** `Derives.qExpr_factor_step`, `Derives.qExpr_factor`, `prodExpr`,
`Derives.qExpr_factor_list`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

/-- The product of a list of expressions: `one` for the empty list. -/
def prodExpr {V : Type*} : List (Expr V) → Expr V
  | [] => .one
  | e :: l => .mul e (prodExpr l)

@[simp] lemma prodExpr_nil {V : Type*} : prodExpr ([] : List (Expr V)) = .one := rfl

@[simp] lemma prodExpr_cons {V : Type*} (e : Expr V) (l : List (Expr V)) :
    prodExpr (e :: l) = .mul e (prodExpr l) := rfl

variable {V : Type*} [DecidableEq V] [Fintype V]


namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **One step of the factorization.** For `m ∈ S` without children in `T ∖ U`, the
factorization of `Q[T']` with `T' = T ∖ {m}` gives that of `Q[T]`. -/
theorem qExpr_factor_step {T S : Finset V} {m : V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S)) (hm : m ∈ T \ U) (hmS : m ∈ S)
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v)
    (ih : Derives G U (qExpr U (T.erase m))
      (.mul (qExpr U (T.erase m ∩ S)) (qExpr U (T.erase m \ S)))) :
    Derives G U (qExpr U T) (.mul (qExpr U (T ∩ S)) (qExpr U (T \ S))) := by
  have hT : T.erase m \ S = T \ S := by
    ext v
    rcases eq_or_ne v m with rfl | hv <;> simp [*]
  rw [hT] at ih
  exact trans (qExpr_split hroot hm hmax) (trans (mul (refl _) ih)
    (trans (symm (mul_assoc _ _ _))
      (mul (symm (qExpr_inter_split hroot hcl hm hmS hmax)) (refl _))))

/-- **C-component factorization.** If the latents are roots and `S` is closed in `T`, then
`Q[T] = Q[T ∩ S] · Q[T ∖ S]`. -/
theorem qExpr_factor (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {T S : Finset V}
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S)) :
    Derives G U (qExpr U T) (.mul (qExpr U (T ∩ S)) (qExpr U (T \ S))) := by
  obtain ⟨n, hn⟩ : ∃ n, (T \ U).card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing T S with
  | _ n ih =>
  rcases (T \ U).eq_empty_or_nonempty with hT | hT
  · -- no observed vertex: every c-factor is `1`
    have h1 : (T ∩ S) \ U = ∅ := Finset.subset_empty.mp
      (hT ▸ Finset.sdiff_subset_sdiff Finset.inter_subset_left (Finset.Subset.refl U))
    have h2 : (T \ S) \ U = ∅ := Finset.subset_empty.mp
      (hT ▸ Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl U))
    exact trans (qExpr_of_empty hT) (trans (symm (one_mul .one))
      (mul (symm (qExpr_of_empty h1)) (symm (qExpr_of_empty h2))))
  · obtain ⟨m, hm, hmax⟩ := exists_childless G hT
    have hlt : (T.erase m \ U).card < n := by
      rw [← hn, Finset.erase_sdiff_comm]
      exact Finset.card_erase_lt_of_mem hm
    have hcl' : ∀ {S' : Finset V}, (∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S' ↔ v ∈ S')) →
        ∀ u ∈ U, ∀ v ∈ T.erase m, G.edge u v → (u ∈ S' ↔ v ∈ S') :=
      fun h u hu v hv e => h u hu v (Finset.mem_of_mem_erase hv) e
    by_cases hmS : m ∈ S
    · exact qExpr_factor_step hroot hcl hm hmS hmax (ih _ hlt (hcl' hcl) rfl)
    · -- the same for the complement of `S`, which is closed in `T` too
      have hclc : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ Sᶜ ↔ v ∈ Sᶜ) := fun u hu v hv e => by
        simpa only [Finset.mem_compl] using not_congr (hcl u hu v hv e)
      have h := qExpr_factor_step hroot hclc hm (Finset.mem_compl.mpr hmS) hmax
        (ih _ hlt (hcl' hclc) rfl)
      have h1 : T ∩ Sᶜ = T \ S := (Finset.sdiff_eq_inter_compl T S).symm
      have h2 : T \ Sᶜ = T ∩ S := by
        ext v
        simp
      rw [h1, h2] at h
      exact trans h (mul_comm _ _)

/-- **C-component factorization into many blocks.** If the latents are roots, and the
blocks of the list `l` are pairwise disjoint, each closed in `T`, and cover `T ∖ U`, then
`Q[T] = ∏_{S ∈ l} Q[T ∩ S]`. -/
theorem qExpr_factor_list (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (l : List (Finset V)) :
    ∀ {T : Finset V}, (∀ S ∈ l, ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S)) →
      l.Pairwise Disjoint → (∀ v ∈ T \ U, ∃ S ∈ l, v ∈ S) →
      Derives G U (qExpr U T) (prodExpr (l.map (fun S => qExpr U (T ∩ S)))) := by
  induction l with
  | nil =>
    intro T _ _ hcov
    have hT : T \ U = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
      obtain ⟨S, hS, -⟩ := hcov v hv
      exact absurd hS List.not_mem_nil
    exact qExpr_of_empty hT
  | cons S l ih =>
    intro T hcl hdisj hcov
    obtain ⟨hSl, hdisj⟩ := List.pairwise_cons.mp hdisj
    -- the other blocks are closed in `T ∖ S`, and cover its observed vertices
    have hcl' : ∀ S' ∈ l, ∀ u ∈ U, ∀ v ∈ T \ S, G.edge u v → (u ∈ S' ↔ v ∈ S') :=
      fun S' hS' u hu v hv e => hcl S' (List.mem_cons_of_mem S hS') u hu v
        (Finset.mem_sdiff.mp hv).1 e
    have hcov' : ∀ v ∈ (T \ S) \ U, ∃ S' ∈ l, v ∈ S' := by
      intro v hv
      simp only [Finset.mem_sdiff] at hv
      obtain ⟨S', hS', hvS'⟩ := hcov v (Finset.mem_sdiff.mpr ⟨hv.1.1, hv.2⟩)
      rcases List.mem_cons.mp hS' with rfl | hS'
      · exact absurd hvS' hv.1.2
      · exact ⟨S', hS', hvS'⟩
    have hmap : l.map (fun S' => qExpr U ((T \ S) ∩ S')) = l.map (fun S' => qExpr U (T ∩ S')) :=
      List.map_congr_left fun S' hS' => by
        rw [Finset.sdiff_inter_right_comm, Finset.sdiff_eq_self_of_disjoint
          (Finset.disjoint_of_subset_left Finset.inter_subset_right (hSl S' hS').symm)]
    have h := ih hcl' hdisj hcov'
    rw [hmap] at h
    simp only [List.map_cons, prodExpr_cons]
    exact trans (qExpr_factor hroot (hcl S List.mem_cons_self)) (mul (refl _) h)

end Derives

end DoCalc
