/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Ring

/-!
# Small facts about `ℝ≥0∞`

Probabilities in this project are values of `PMF`s, so they live in `ℝ≥0∞`. The rules of
the do-calculus are stated in product form (`P(y, w) · P'(w) = P'(y, w) · P(w)` instead of
a quotient), and several proofs end with the same piece of algebra: two such products with
a common factor are cancelled against each other. Several identification proofs also sum
over an assignment that is split into two parts. This file states these facts once.

**Contents.**

1. *Cross-multiplication.* From `A · d = c · B` and `C · d = c · D` with `d ≠ ∞` follows
   `A · D = C · B`, provided that `d = 0` forces `B = D = 0` (`cross_cancel`). The proof
   multiplies the goal by `d` and rewrites with the two hypotheses. When `d ≠ 0` the
   proviso holds trivially; rule 3 with positivity and the conditional effects of IDC use
   it that way, the flag model of rule 3 uses the general form. A common factor
   `k ≠ 0, ∞` on both sides of an equation can be struck out (`cancel_common_factor`).
2. *Summing over a split.* If every `c : C` is `J a b` for exactly one pair `(a, b)`,
   then a sum over `C` is a double sum over `A` and `B`
   (`tsum_eq_tsum_tsum_of_iff`). The proof turns `J` into an equivalence `A × B ≃ C` and
   uses `ENNReal.tsum_prod`.

**Main results.** `ENNReal.cross_cancel`, `ENNReal.cancel_common_factor`,
`ENNReal.tsum_eq_tsum_tsum_of_iff`.
-/

open scoped ENNReal

namespace ENNReal

/-! ## Cross-multiplication -/

/-- **Cross-multiplication.** From `A · d = c · B` and `C · d = c · D`, with `d ≠ ∞`,
follows `A · D = C · B`, provided that `d = 0` gives `B = 0` and `D = 0`. -/
theorem cross_cancel {A B C D c d : ℝ≥0∞} (hdt : d ≠ ⊤)
    (h1 : A * d = c * B) (h2 : C * d = c * D) (h0 : d = 0 → B = 0 ∧ D = 0) :
    A * D = C * B := by
  by_cases hd : d = 0
  · obtain ⟨hB, hD⟩ := h0 hd
    rw [hB, hD, mul_zero, mul_zero]
  · apply (ENNReal.mul_right_inj hd hdt).mp
    calc d * (A * D) = (A * d) * D := by ring
      _ = (c * B) * D := by rw [h1]
      _ = (c * D) * B := by ring
      _ = (C * d) * B := by rw [h2]
      _ = d * (C * B) := by ring

/-- Strike out a common factor `k ≠ 0, ∞`. -/
theorem cancel_common_factor {k A d c B : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (h : (k * A) * d = c * (k * B)) : A * d = c * B := by
  apply (ENNReal.mul_right_inj hk0 hkt).mp
  calc k * (A * d) = (k * A) * d := by ring
    _ = c * (k * B) := h
    _ = k * (c * B) := by ring

/-! ## Summing over a split -/

/-- **Summing over a split.** If every `c : C` is `J a b` for exactly one pair `(a, b)`,
namely `(pA c, pB c)`, then a sum over `C` is a double sum over `A` and `B`. -/
theorem tsum_eq_tsum_tsum_of_iff {A B C : Type*} (J : A → B → C) (pA : C → A) (pB : C → B)
    (h : ∀ c a b, c = J a b ↔ a = pA c ∧ b = pB c) (F : C → ℝ≥0∞) :
    ∑' c, F c = ∑' a, ∑' b, F (J a b) := by
  let e : A × B ≃ C :=
    { toFun := fun p => J p.1 p.2
      invFun := fun c => (pA c, pB c)
      left_inv := fun ⟨a, b⟩ => by
        obtain ⟨ha, hb⟩ := (h (J a b) a b).mp rfl
        simp only [← ha, ← hb]
      right_inv := fun c => ((h c (pA c) (pB c)).mpr ⟨rfl, rfl⟩).symm }
  rw [← e.tsum_eq]
  exact ENNReal.tsum_prod (f := fun a b => F (J a b))

end ENNReal
