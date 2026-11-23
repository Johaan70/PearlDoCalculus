/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Arithmetic and distributions in `ZMod 2`

The counter-models behind the non-identifiability results are parity models: every
variable carries bits in `ZMod 2`, and a value is the sum of the bits it reads. Both the
concrete hedge families (`Identification/HedgeTemplate`, `LatentTree`, `RootPathModels`,
`RootPath`, `RootTree`) and the general construction for an arbitrary hedge
(`Hedge/ParityModels`, `Product`, `ProductBias`, `ObsEq`, `Roots`, `DoGapM1`, `DoGapM2`)
compute with such bits. This file collects the facts about `ZMod 2` that they need, so
that each is stated once.

**How.** Every identity in parts 1-4 of the contents below is a statement about finitely
many bits and is proved by `decide`. The distribution facts of part 5 write a sum over
`ZMod 2` as its two terms (`univ_eq`, `Finset.sum_pair`). The involution lemmas of part 6
reindex the sum that defines `P(f = 0)` along the involution.

**Contents.**

1. *Finite structure.* `ZMod 2 = {0, 1}` (`univ_eq`, `eq_zero_or_eq_one`). The facts
   `x + x = 0` and `0 ≠ 1` are used directly from Mathlib, as
   `CharTwo.add_self_eq_zero` and `zero_ne_one`.
2. *Bits as booleans.* The hedge families use `Bool` as value type and compute in
   `ZMod 2`. `ofBool` and `toBool` translate between the two; `ofBool` turns `xor` into
   `+` (`ofBool_xor`).
3. *Solving an equation for one variable.* Since `-x = x`, an equation `a = b + c` can be
   solved for any of its terms (`eq_add_iff_eq_add`, `eq_add_add_iff_eq_add_add`, and a
   few special forms).
4. *Cancelling rearrangements.* Identities in which terms that occur twice cancel. Each is
   proved by `decide` and serves one step of one proof; the docstring of each shows the
   identity, and the name describes its shape.
5. *Distributions on `ZMod 2`.* `q 0 + q 1 = 1` (`pmf_zero_add_one`), and the four values
   of a distribution on `ZMod 2 × ZMod 2` give the distributions of its first coordinate
   and of the sum of its coordinates (`map_fst_zero` … `map_add_one`).
6. *Involutions that flip a bit.* If an involution `τ` flips a bit `f` and multiplies the
   weight by `k` where `f = 1`, then `P(f = 0) = k · P(f = 1)` (`map_ratio_of_invol`).
   With `k = 1` the bit is a fair coin (`map_fair_of_invol`). This is how the effect of
   `do(x)` is computed in the parity models.

**Main results.** `ZMod2.ofBool`, `ZMod2.toBool`, `ZMod2.eq_add_iff_eq_add`,
`ZMod2.pmf_zero_add_one`, `ZMod2.map_ratio_of_invol`, `ZMod2.map_fair_of_invol`.
-/

namespace ZMod2

/-! ## Finite structure -/

/-- `ZMod 2` has exactly the two elements `0` and `1`. -/
lemma univ_eq : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- Every bit is `0` or `1`. -/
lemma eq_zero_or_eq_one : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-! ## Bits as booleans -/

/-- The bit of a boolean: `true ↦ 1`, `false ↦ 0`. -/
def ofBool (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The boolean of a bit: `1 ↦ true`, `0 ↦ false`. -/
def toBool (z : ZMod 2) : Bool := decide (z = 1)

/-- Translating a bit to a boolean and back gives the bit. -/
lemma ofBool_toBool : ∀ z : ZMod 2, ofBool (toBool z) = z := by decide

/-- A boolean is the boolean of a bit exactly when its bit is that bit. -/
lemma eq_toBool_iff : ∀ (b : Bool) (z : ZMod 2), b = toBool z ↔ ofBool b = z := by decide

/-- `ofBool` turns `xor` into addition in `ZMod 2`. -/
lemma ofBool_xor : ∀ a b : Bool, ofBool (xor a b) = ofBool a + ofBool b := by decide

/-- Different booleans give different bits. -/
lemma ofBool_injective : Function.Injective ofBool := by
  intro a b
  cases a <;> cases b <;> decide

/-- Adding the bit of `c` to `a` flips the boolean of `a` exactly when `c` is `true`. -/
lemma toBool_add_ofBool :
    ∀ (a : ZMod 2) (c : Bool), toBool (a + ofBool c) = xor (toBool a) c := by decide

/-! ## Solving an equation for one variable -/

/-- `r = x + n ↔ n = r + x`: solve a sum of two bits for the second one. -/
lemma eq_add_iff_eq_add : ∀ r x n : ZMod 2, (r = x + n ↔ n = r + x) := by decide

/-- `n = l + b + d ↔ l = n + d + b`: solve a sum of three bits for the first one. -/
lemma eq_add_add_iff_eq_add_add : ∀ n l b d : ZMod 2, n = l + b + d ↔ l = n + d + b := by
  decide

/-- Two bits with sum `0` are equal. -/
lemma eq_of_zero_eq_add : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide

/-- If `n + q = s + l`, then `n = q` exactly when `l = s`. -/
lemma eq_iff_eq_of_add_eq_add : ∀ n q s l : ZMod 2, n + q = s + l → (n = q ↔ l = s) := by
  decide

/-- `0 = a + 1 ↔ 1 = a`: adding `1` flips a bit. -/
lemma zero_eq_add_one_iff : ∀ a : ZMod 2, (0 = a + 1 ↔ 1 = a) := by decide

/-- If `a + b = 1`, then `a + 1 + b = 0`. -/
lemma add_one_add_eq_zero_of_add_eq_one : ∀ a b : ZMod 2, a + b = 1 → a + 1 + b = 0 := by
  decide

/-- If `c + e = a + b + b + e`, then `a + c = 0`: the pair `b` and the common `e` cancel. -/
lemma add_eq_zero_of_add_eq_add_add_add :
    ∀ a b c e : ZMod 2, c + e = a + b + b + e → a + c = 0 := by decide

/-- From `wz = ucs + us + c` and `ucs = u0 + o` follows `us = u0 + (o + (wz + c))`:
`us` solved from two linear equations. -/
lemma eq_add_add_of_eq_add_add_of_eq_add : ∀ us ucs u0 o wz c : ZMod 2,
    wz = ucs + us + c → ucs = u0 + o → us = u0 + (o + (wz + c)) := by decide

/-- From `yz = ul + cy`, `ul = u0 + s` and `s + cy = 0` follows `u0 = yz`. -/
lemma eq_of_eq_add_of_eq_add_of_add_eq_zero : ∀ yz ul u0 s cy : ZMod 2,
    yz = ul + cy → ul = u0 + s → s + cy = 0 → u0 = yz := by decide

/-- If `s + cy = 0`, then `yz = s + yz + cy`. -/
lemma eq_add_add_of_add_eq_zero : ∀ yz s cy : ZMod 2, s + cy = 0 → yz = s + yz + cy := by
  decide

/-! ## Cancelling rearrangements -/

/-- `b + (a + b) = a`. -/
lemma add_add_cancel : ∀ a b : ZMod 2, b + (a + b) = a := by decide

/-- `a + p + (b + p) = a + b`. -/
lemma add_add_add_cancel : ∀ a b p : ZMod 2, a + p + (b + p) = a + b := by decide

/-- `a + b + c + b + c = a`. -/
lemma add_add_add_add_cancel : ∀ a b c : ZMod 2, a + b + c + b + c = a := by decide

/-- `g + e + q + g + e = q`. -/
lemma add_add_add_add_cancel_middle : ∀ g e q : ZMod 2, g + e + q + g + e = q := by decide

/-- `a + c = b + c + (a + b)`. -/
lemma add_eq_add_add_add : ∀ a b c : ZMod 2, a + c = b + c + (a + b) := by decide

/-- `a + (b + c) + (d + b + (e + c)) = a + (d + e)`: the pairs `b` and `c` cancel. -/
lemma add_add_add_cancel_pairs :
    ∀ a b c d e : ZMod 2, a + (b + c) + (d + b + (e + c)) = a + (d + e) := by decide

/-- `add_add_add_cancel_pairs` at `b = d = 0`, with the zeros kept. -/
lemma add_add_add_cancel_pairs_zero :
    ∀ a c e : ZMod 2, a + (0 + c) + (0 + (e + c)) = a + (0 + e) := by decide

/-- `a + (d + c) + (i + (e + c)) = a + (i + e) + d`: the pair `c` cancels. -/
lemma add_add_add_cancel_comm :
    ∀ a d c i e : ZMod 2, a + (d + c) + (i + (e + c)) = a + (i + e) + d := by decide

/-- `add_add_add_cancel_comm` at `d = 0`, with the zero kept on the left. -/
lemma add_add_add_cancel_comm_zero :
    ∀ a c i e : ZMod 2, a + (0 + c) + (i + (e + c)) = a + (i + e) := by decide

/-- `yb = p + (yb + m + (p + (m + q))) + q`. -/
lemma self_eq_add_add_cancel :
    ∀ yb m p q : ZMod 2, yb = p + (yb + m + (p + (m + q))) + q := by decide

/-- `wz = o + yz + (o + (wz + c) + yz) + c`. -/
lemma self_eq_add_add_add_cancel :
    ∀ wz o yz c : ZMod 2, wz = o + yz + (o + (wz + c) + yz) + c := by decide

/-- `y = y + g + 0 + g`. -/
lemma self_eq_add_add_zero_add : ∀ y g : ZMod 2, y = y + g + 0 + g := by decide

/-- `a + b + c = a + b + (e + c) + e`. -/
lemma add_eq_add_add_add_cancel : ∀ a b c e : ZMod 2, a + b + c = a + b + (e + c) + e := by
  decide

/-- `y + 1 + g + (e + 1) = y + g + e`. -/
lemma add_one_add_add_add_one : ∀ y g e : ZMod 2, y + 1 + g + (e + 1) = y + g + e := by decide

/-- `y + 1 + (g + 1) + e = y + g + e`. -/
lemma add_one_add_add_one_add : ∀ y g e : ZMod 2, y + 1 + (g + 1) + e = y + g + e := by decide

/-! ## Distributions on `ZMod 2` -/

/-- The two values of a distribution on `ZMod 2` add up to `1`. -/
lemma pmf_zero_add_one (q : PMF (ZMod 2)) : q 0 + q 1 = 1 := by
  have h := q.tsum_coe
  rw [tsum_fintype, univ_eq, Finset.sum_pair zero_ne_one] at h
  exact h

/-- The first coordinate of a distribution on `ZMod 2 × ZMod 2` is `0` with probability
`q (0, 0) + q (0, 1)`. -/
lemma map_fst_zero (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map Prod.fst) 0 = q (0, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, univ_eq, Finset.sum_pair zero_ne_one,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one, if_pos rfl, if_pos rfl,
    if_neg zero_ne_one, if_neg zero_ne_one]
  ring

/-- The first coordinate of a distribution on `ZMod 2 × ZMod 2` is `1` with probability
`q (1, 0) + q (1, 1)`. -/
lemma map_fst_one (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map Prod.fst) 1 = q (1, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, univ_eq, Finset.sum_pair zero_ne_one,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one, if_neg one_ne_zero,
    if_neg one_ne_zero, if_pos rfl, if_pos rfl]
  ring

/-- The sum of the coordinates of a distribution on `ZMod 2 × ZMod 2` is `0` with
probability `q (0, 0) + q (1, 1)`. -/
lemma map_add_zero (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 0 = q (0, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, univ_eq, Finset.sum_pair zero_ne_one,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one,
    if_pos (by decide : (0 : ZMod 2) = 0 + 0), if_neg (by decide : ¬ (0 : ZMod 2) = 0 + 1),
    if_neg (by decide : ¬ (0 : ZMod 2) = 1 + 0), if_pos (by decide : (0 : ZMod 2) = 1 + 1)]
  ring

/-- The sum of the coordinates of a distribution on `ZMod 2 × ZMod 2` is `1` with
probability `q (1, 0) + q (0, 1)`. -/
lemma map_add_one (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 1 = q (1, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, univ_eq, Finset.sum_pair zero_ne_one,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one,
    if_neg (by decide : ¬ (1 : ZMod 2) = 0 + 0), if_pos (by decide : (1 : ZMod 2) = 0 + 1),
    if_pos (by decide : (1 : ZMod 2) = 1 + 0), if_neg (by decide : ¬ (1 : ZMod 2) = 1 + 1)]
  ring

/-! ## Involutions that flip a bit -/

/-- **The ratio lemma.** An involution `τ` that flips the bit `f` and multiplies the weight
by `k` where `f = 1` gives `P(f = 0) = k · P(f = 1)`. -/
theorem map_ratio_of_invol {β : Type*} (p : PMF β) (τ : β → β) (f : β → ZMod 2) (k : ENNReal)
    (hinv : ∀ s, τ (τ s) = s) (hf : ∀ s, f (τ s) = f s + 1)
    (hp : ∀ s, f s = 1 → p (τ s) = k * p s) :
    (p.map f) 0 = k * (p.map f) 1 := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm τ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  simp only [Function.Involutive.coe_toPerm, hf]
  by_cases h1 : 1 = f s
  · rw [if_pos ((zero_eq_add_one_iff (f s)).mpr h1), if_pos h1, hp s h1.symm]
  · rw [if_neg (fun h => h1 ((zero_eq_add_one_iff (f s)).mp h)), if_neg h1, mul_zero]

/-- **A fair bit.** An involution that keeps the weights and flips the bit `f` gives
`P(f = 1) = P(f = 0)`: the ratio lemma with `k = 1`. -/
theorem map_fair_of_invol {β : Type*} (p : PMF β) (ψ : β → β) (f : β → ZMod 2)
    (hinv : ∀ s, ψ (ψ s) = s) (hp : ∀ s, p (ψ s) = p s) (hf : ∀ s, f (ψ s) = f s + 1) :
    (p.map f) 1 = (p.map f) 0 := by
  rw [map_ratio_of_invol p ψ f 1 hinv hf (fun s _ => by rw [hp, one_mul]), one_mul]

end ZMod2
