/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Factorization

/-!
# Products of expressions over a list

The completeness proof (`docs/design-docalc-completeness.md`, "Completeness: proof
strategy", step 6) writes `Q[D]` as a product `∏ᵢ Q[Cᵢ]` over the c-components of the
ID check (`prodExpr`, `Derives.qExpr_factor_ccIn`), and then derives each factor `Q[Cᵢ]`
separately into an expression without `do`. This file has the small facts about products
over a list that put the factors back together.

* **Congruence** (`Derives.prodExpr_map`): if `f i` derives `g i` for every `i` of the list,
  then `∏ᵢ f i` derives `∏ᵢ g i`. By induction on the list, with the congruence step for
  `mul`.
* **What is kept** (`doFree_prodExpr`, `vars_prodExpr_subset`, and `Expr.vars_sum_subset`
  for sums): a product of expressions without `do` has no `do`, and a product or sum of
  expressions over the variables `O` is over `O`.
* **Choosing a derivation per factor** (`Derives.exists_prodExpr`): if every factor of
  the list derives an expression without `do` over observed variables, so does the
  product. This is the form the assembly uses. It is proved by induction on the list, so
  no choice function over the list is needed.

**Main results.** `Derives.prodExpr_map`, `doFree_prodExpr`, `vars_prodExpr_subset`,
`Expr.vars_sum_subset`, `Derives.exists_prodExpr`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*}

/-! ## What products and sums keep -/

/-- **A product of expressions without `do` has no `do`.** -/
lemma doFree_prodExpr {l : List (Expr V)} (h : ∀ e ∈ l, e.DoFree) : (prodExpr l).DoFree := by
  induction l with
  | nil => trivial
  | cons e l ih =>
    exact ⟨h e List.mem_cons_self, ih fun e' he' => h e' (List.mem_cons_of_mem e he')⟩

variable [DecidableEq V]

/-- **A product of expressions over `O` is over `O`.** -/
lemma vars_prodExpr_subset {l : List (Expr V)} {O : Finset V} (h : ∀ e ∈ l, e.vars ⊆ O) :
    (prodExpr l).vars ⊆ O := by
  induction l with
  | nil => exact Finset.empty_subset _
  | cons e l ih =>
    exact Finset.union_subset (h e List.mem_cons_self)
      (ih fun e' he' => h e' (List.mem_cons_of_mem e he'))

/-- **A sum of an expression over `O`, over a set in `O`, is over `O`.** -/
lemma Expr.vars_sum_subset {S O : Finset V} {e : Expr V} (hS : S ⊆ O) (he : e.vars ⊆ O) :
    (Expr.sum S e).vars ⊆ O :=
  Finset.union_subset hS he

namespace Derives

variable [Fintype V] {G : DAG V} {U : Finset V}

/-! ## Derivations of products -/

/-- **Congruence for products over a list.** If `f i` derives `g i` for every `i` in `l`,
then `∏_{i ∈ l} f i` derives `∏_{i ∈ l} g i`. -/
theorem prodExpr_map {ι : Type*} (l : List ι) {f g : ι → Expr V}
    (h : ∀ i ∈ l, Derives G U (f i) (g i)) :
    Derives G U (prodExpr (l.map f)) (prodExpr (l.map g)) := by
  induction l with
  | nil => exact refl _
  | cons i l ih =>
    exact mul (h i List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem i hj))

/-- **A product of identified factors is identified.** If every expression of `l` derives
an expression without `do` over observed variables, so does their product. -/
theorem exists_prodExpr (l : List (Expr V))
    (h : ∀ e ∈ l, ∃ e' : Expr V, e'.DoFree ∧ e'.vars ⊆ Uᶜ ∧ Derives G U e e') :
    ∃ e' : Expr V, e'.DoFree ∧ e'.vars ⊆ Uᶜ ∧ Derives G U (prodExpr l) e' := by
  induction l with
  | nil => exact ⟨.one, trivial, Finset.empty_subset _, refl _⟩
  | cons e l ih =>
    obtain ⟨a, ha, hva, hda⟩ := h e List.mem_cons_self
    obtain ⟨b, hb, hvb, hdb⟩ := ih fun e' he' => h e' (List.mem_cons_of_mem e he')
    exact ⟨.mul a b, ⟨ha, hb⟩, Finset.union_subset hva hvb, mul hda hdb⟩

end Derives

end DoCalc
