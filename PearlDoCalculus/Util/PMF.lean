/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.Distributions.Uniform

/-!
# Small facts about `PMF`

The causal models of this project are built from finite probability mass functions:
point masses, uniform distributions and their images under maps. A few facts about them
are needed in several unrelated places: the flag model of rule 3 (`Rule3Flag`), the
chain models of the completeness results (`Completeness/Chain`,
`Completeness/Rule3ChainCopy`, `Completeness/Rule3SetFull`), the root-path models of
the hedge families (`Identification/RootPath`) and the parity models of the general
hedge (`Hedge/ProductBias`, `Hedge/DoGapM2`). Mathlib has the general theory but not
these particular forms, so they are stated here once. The proofs unfold `PMF.map_apply`
or the support of a map and evaluate the resulting sum.

**Contents.**

1. *Point masses.* `pure a` gives mass `1` to any point equal to `a`
   (`pure_apply_of_eq`); this is the counterpart of Mathlib's `PMF.pure_apply_of_ne`.
2. *Images under `some`.* Mapping a distribution into `Option` with `some` keeps the
   mass of every `some a` and puts no mass on `none` (`map_some_apply_some`,
   `map_some_apply_none`). The flag model of rule 3 uses `none` as the flag
   "intervened on".
3. *Images of a uniform distribution.* A point has positive mass under the image of a
   uniform distribution exactly when it is in the range of the map
   (`map_uniformOfFintype_apply_ne_zero_iff`).
4. *Maps that agree on the support.* Two maps that agree wherever `p` has positive mass
   give the same image distribution (`map_congr_on_support`).

**Main results.** `PMF.pure_apply_of_eq`, `PMF.map_some_apply_some`,
`PMF.map_some_apply_none`, `PMF.map_uniformOfFintype_apply_ne_zero_iff`,
`PMF.map_congr_on_support`.
-/

namespace PMF

/-! ## Point masses -/

/-- `pure a` gives mass `1` to every point equal to `a`. -/
theorem pure_apply_of_eq {α : Type*} (a a' : α) (h : a' = a) : pure a a' = 1 :=
  if_pos h

/-! ## Images under `some` -/

/-- Mapping with `some` keeps the mass of `some a`. -/
theorem map_some_apply_some {β : Type*} (p : PMF β) (a : β) :
    (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- Mapping with `some` puts no mass on `none`. -/
theorem map_some_apply_none {β : Type*} (p : PMF β) : (p.map some) none = 0 := by
  rw [PMF.map_apply]
  simp

/-! ## Images of a uniform distribution -/

/-- A point has positive mass under the image of a uniform distribution exactly when it
is in the range of the map. -/
theorem map_uniformOfFintype_apply_ne_zero_iff {β γ : Type*} [Fintype β] [Nonempty β]
    (f : β → γ) (a : γ) :
    (PMF.map f (PMF.uniformOfFintype β)) a ≠ 0 ↔ ∃ b, f b = a := by
  rw [← PMF.mem_support_iff, PMF.support_map, PMF.support_uniformOfFintype]
  simp

/-! ## Maps that agree on the support -/

/-- Two maps that agree wherever `p` has positive mass give the same image
distribution. -/
theorem map_congr_on_support {β γ : Type*} (p : PMF β) (f g : β → γ)
    (h : ∀ s, p s ≠ 0 → f s = g s) : p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro s
  by_cases hs : p s = 0
  · rw [hs, ite_self, ite_self]
  · rw [h s hs]

end PMF
