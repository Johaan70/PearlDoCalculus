/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Data.Finset.Basic

/-!
# Small facts about `Finset`

A few facts about finite sets are needed in several unrelated files: the computable ID
algorithm and the hedge construction iterate set operators, and Tian's c-factor formulas
remove a vertex from one side of an intersection. Mathlib has the general theory but not
these particular forms, so they are stated here once.

**Contents.**

1. *Iterates that stay inside a set.* If `f` maps subsets of `T` to subsets of `T` and
   `A0 ⊆ T`, then every iterate `f^[k] A0` is a subset of `T` (`iterate_subset`). The
   proof is an induction on `k`. The ancestor and c-closure operators of `IdAlgo` are
   computed this way. The two companion facts, that an inflationary `f` gives growing
   iterates, are Mathlib's `Function.id_le_iterate_of_id_le` and
   `Function.monotone_iterate_of_id_le`.
2. *Erasing a vertex outside the other set.* If `v ∉ T`, then removing `v` from `A`
   does not change `A ∩ T` (`inter_eq_erase_inter_of_notMem`).

**Main results.** `Finset.iterate_subset`, `Finset.inter_eq_erase_inter_of_notMem`.
-/

namespace Finset

variable {α : Type*}

/-! ## Iterates that stay inside a set -/

/-- If `f` maps subsets of `T` to subsets of `T` and `A0 ⊆ T`, every iterate of `f` on
`A0` stays inside `T`. -/
lemma iterate_subset (T : Finset α) (f : Finset α → Finset α) (hbd : ∀ A, A ⊆ T → f A ⊆ T)
    (A0 : Finset α) (h0 : A0 ⊆ T) : ∀ k, f^[k] A0 ⊆ T := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [show f^[k + 1] A0 = f (f^[k] A0) from Function.iterate_succ_apply' f k A0]
    exact hbd _ ih

/-! ## Erasing a vertex outside the other set -/

/-- Removing a vertex `v ∉ T` from `A` does not change `A ∩ T`. -/
lemma inter_eq_erase_inter_of_notMem [DecidableEq α] {A T : Finset α} {v : α} (h : v ∉ T) :
    A ∩ T = A.erase v ∩ T := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun e => h (by rw [← e]; exact h2), h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

end Finset
