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
   uses `ENNReal.tsum_prod`. Two variants restrict the split to a part of `C` or of `A`
   and follow by applying it to a subtype (`tsum_subtype`): a sum over the `c` with a
   fixed value `x = p c` (`tsum_ite_eq_tsum_tsum_of_iff`; the marginal of a factorized
   distribution), and a sum over all of `C` where only the `a` with `P a` are used
   (`tsum_eq_tsum_ite_tsum_of_iff`; summing fibre by fibre). The double sum of an
   indicator of `c = J a b` has the single term at `(a, b) = (pA c, pB c)`
   (`tsum_tsum_ite_eq_of_iff`).

These four lemmas replace the same four-step argument (`tsum_eq_single` twice,
`ENNReal.tsum_comm` twice) that was written out in each split of the identification
layer: `Identification/LatentSplit`, `Identification/CFactor` and
`Identification/IdSound` (and `Identification/Channel`, deleted in v4.158 and kept at
tag `v4.152`).

**Main results.** `ENNReal.cross_cancel`, `ENNReal.cancel_common_factor`,
`ENNReal.tsum_eq_tsum_tsum_of_iff`, `ENNReal.tsum_ite_eq_tsum_tsum_of_iff`,
`ENNReal.tsum_eq_tsum_ite_tsum_of_iff`, `ENNReal.tsum_tsum_ite_eq_of_iff`.
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

/-- **Summing over a split, with a fixed part.** If the `c : C` with `x = p c` are exactly
the `J a b`, each for the single pair `(pA c, pB c)`, then the sum over these `c` is a
double sum over `A` and `B`. -/
theorem tsum_ite_eq_tsum_tsum_of_iff {X A B C : Type*} (J : A → B → C) (p : C → X)
    (pA : C → A) (pB : C → B) (x : X) [∀ c, Decidable (x = p c)]
    (h : ∀ c a b, c = J a b ↔ x = p c ∧ a = pA c ∧ b = pB c) (F : C → ℝ≥0∞) :
    ∑' c, (if x = p c then F c else 0) = ∑' a, ∑' b, F (J a b) := by
  have hJ : ∀ a b, x = p (J a b) := fun a b => ((h _ a b).mp rfl).1
  calc ∑' c, (if x = p c then F c else 0)
      = ∑' c : {c // x = p c}, F c :=
        ((tsum_subtype {c | x = p c} F).trans
          (tsum_congr fun c => Set.indicator_apply _ _ _)).symm
    _ = _ := tsum_eq_tsum_tsum_of_iff (C := {c // x = p c}) (fun a b => ⟨J a b, hJ a b⟩)
        (fun c => pA c) (fun c => pB c)
        (fun c a b => by rw [Subtype.ext_iff, h]; exact and_iff_right c.2) (fun c => F c)

/-- **Summing over a split, fibre by fibre.** If every `c : C` is `J a b` with `P a` for
exactly one pair `(a, b)`, namely `(pA c, pB c)`, then a sum over `C` is a sum over the
`a` with `P a` of a sum over `B`. -/
theorem tsum_eq_tsum_ite_tsum_of_iff {A B C : Type*} (J : A → B → C) (P : A → Prop)
    [DecidablePred P] (pA : C → A) (pB : C → B)
    (h : ∀ c a b, c = J a b ∧ P a ↔ a = pA c ∧ b = pB c) (F : C → ℝ≥0∞) :
    ∑' c, F c = ∑' a, if P a then ∑' b, F (J a b) else 0 := by
  have hP : ∀ c, P (pA c) := fun c => ((h c _ _).mpr ⟨rfl, rfl⟩).2
  calc ∑' c, F c
      = ∑' a : {a // P a}, ∑' b, F (J a b) :=
        tsum_eq_tsum_tsum_of_iff (A := {a // P a}) (fun a b => J a b)
          (fun c => ⟨pA c, hP c⟩) pB
          (fun c a b => by rw [Subtype.ext_iff, ← h]; exact (and_iff_left a.2).symm) F
    _ = _ := (tsum_subtype {a | P a} (fun a => ∑' b, F (J a b))).trans
        (tsum_congr fun a => Set.indicator_apply _ _ _)

/-- **One term of a double sum.** If every `c : C` is `J a b` for exactly one pair `(a, b)`,
namely `(pA c, pB c)`, then the double sum of `f a b` over the pairs with `c = J a b` is
`f (pA c) (pB c)`. -/
theorem tsum_tsum_ite_eq_of_iff {A B C : Type*} (J : A → B → C) (pA : C → A) (pB : C → B)
    (h : ∀ c a b, c = J a b ↔ a = pA c ∧ b = pB c) (f : A → B → ℝ≥0∞) (c : C)
    [∀ a b, Decidable (c = J a b)] :
    ∑' a, ∑' b, (if c = J a b then f a b else 0) = f (pA c) (pB c) := by
  rw [tsum_eq_single (pA c), tsum_eq_single (pB c), if_pos ((h _ _ _).mpr ⟨rfl, rfl⟩)]
  · exact fun b hb => if_neg fun e => hb ((h _ _ _).mp e).2
  · exact fun a ha => ENNReal.tsum_eq_zero.mpr fun b => if_neg fun e => ha ((h _ _ _).mp e).1

end ENNReal
