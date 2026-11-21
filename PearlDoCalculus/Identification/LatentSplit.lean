/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Identification.Basic
import PearlDoCalculus.Util.ENNReal

/-!
# Splitting the latent variables

In the identification layer the vertices are split into latent ones `U` and observed ones
`O = Uᶜ`. Tian's factor `Q[T]` (`Identification/CFactor`) is a sum over the values of the
latent vertices in `T` of a product of kernel factors, and these factors read a *full*
assignment on all vertices. This file builds those full assignments from their parts, and
states how they split again into the parts. Every factorization proof of the c-factor
side (`marginal_factor`, `anc_factor`, `Q_split`, the IDENTIFY steps, ID soundness) uses
these facts to turn one sum over full assignments into nested sums over the parts.

**Contents.**

1. *Filling in the latent values.* `fill U T a w` takes the observed values from `a`,
   the latent values in `T` from `w`, and an arbitrary value for the other latent
   vertices.
2. *Joining the latent values of two blocks.* `joinBlocks U T S w1 w2` puts the latent
   values in `T ∩ S` and in `T ∩ Sᶜ` together to latent values in `T`. Latent values in
   `T` are of this form exactly when `w1` and `w2` are their restrictions
   (`eq_joinBlocks_iff`), so a sum over the latent values in `T` is a double sum over the
   two parts (`tsum_eq_tsum_joinBlocks`). Filling with the joined values agrees with
   filling with either part where that part is read.
3. *Restricting to a set `A`.* The restriction of `fill U A a (joinBlocks U A S w1 w2)` to
   `A` is determined by the restrictions of `a`, `w1` and `w2`
   (`eq_restrict_fill_joinBlocks_iff`). This is the split behind the factorization on an
   ancestral set (`anc_factor`), and, with `A` all vertices, behind the factorization of
   `P(O)` itself (`marginal_factor`). The named inclusions (`compl_inter_subset_compl`,
   ...) are the proof terms for these restrictions.
4. *Overwriting observed values.* `updX U X a x'` is `a` with the values on `X` replaced
   by `x'` (equal to `Rule3Flag.setZ`, `updX_eq_setZ`). Filling with it changes only the
   vertices of `X`, and `eq_updX_and_restrict_eq_iff` is the bijection behind summing
   fibre by fibre (`tsum_updX` in `Identification/IdSound`).

**How.** Each identity is a case split on whether a vertex is latent and in which block
it lies, closed by `simp` with the definitions. The sums are split by the generic
lemmas of `Util/ENNReal` (`ENNReal.tsum_eq_tsum_tsum_of_iff` and its variants), which
need only the bijection given by the `eq_..._iff` lemmas here.

**Main results.** `fill`, `joinBlocks`, `updX`, and `eq_joinBlocks_iff`,
`tsum_eq_tsum_joinBlocks`, `eq_restrict_fill_joinBlocks_iff`,
`eq_updX_and_restrict_eq_iff`, all in namespace `Identification.CFactor`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-! ## Filling in the latent values -/

/-- The full assignment with the observed values from `a`, the latent values in `T` from
`w`, and an arbitrary value at the other latent vertices. -/
noncomputable def fill [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w : Assignment (α := α) (U ∩ T)) : Assignment (α := α) (Finset.univ : Finset V) :=
  fun v => if h0 : v.1 ∈ U then
      (if h1 : v.1 ∈ T then w ⟨v.1, Finset.mem_inter.mpr ⟨h0, h1⟩⟩ else Classical.arbitrary _)
    else a ⟨v.1, Finset.mem_compl.mpr h0⟩

/-! ## Joining the latent values of two blocks -/

/-- The latent vertices of `T ∩ S` are latent vertices of `T`. -/
lemma inter_inter_subset_inter (U T S : Finset V) : U ∩ (T ∩ S) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

/-- The latent vertices of `T ∩ Sᶜ` are latent vertices of `T`. -/
lemma inter_inter_compl_subset_inter (U T S : Finset V) :
    U ∩ (T ∩ Sᶜ) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

/-- The latent values in `T`, put together from those in `T ∩ S` (from `w1`) and those in
`T ∩ Sᶜ` (from `w2`). -/
noncomputable def joinBlocks (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) : Assignment (α := α) (U ∩ T) :=
  fun v => if h : v.1 ∈ S then
      w1 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, h⟩⟩⟩
    else w2 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, Finset.mem_compl.mpr h⟩⟩⟩

/-- Latent values `w` in `T` are `joinBlocks U T S w1 w2` exactly when `w1` and `w2` are
the restrictions of `w`. -/
lemma eq_joinBlocks_iff (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (w : Assignment (α := α) (U ∩ T)) :
    w = joinBlocks U T S w1 w2 ↔ w1 = w.restrict (inter_inter_subset_inter U T S) ∧
      w2 = w.restrict (inter_inter_compl_subset_inter U T S) := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      have hS : v ∈ S := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [joinBlocks, Assignment.restrict, hS]
    · funext ⟨v, hv⟩
      have hS : v ∉ S := Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [joinBlocks, Assignment.restrict, hS]
  · rintro ⟨rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases hS : v ∈ S
    · simp [joinBlocks, Assignment.restrict, hS]
    · simp [joinBlocks, Assignment.restrict, hS]

/-- **A sum over the latent values in `T` splits in two:** one sum over the latent values
in `T ∩ S` and one over those in `T ∩ Sᶜ`. -/
lemma tsum_eq_tsum_joinBlocks (U T S : Finset V) (F : Assignment (α := α) (U ∩ T) → ENNReal) :
    ∑' w, F w = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
      ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)), F (joinBlocks U T S w1 w2) :=
  ENNReal.tsum_eq_tsum_tsum_of_iff (joinBlocks U T S) _ _
    (fun w w1 w2 => eq_joinBlocks_iff U T S w1 w2 w) F

/-- At a vertex that is observed or a latent vertex of `T ∩ S`, filling `T` with the joined
values agrees with filling `T ∩ S` from `w1` alone. -/
lemma fill_joinBlocks_apply_left [∀ v, Nonempty (α v)] (U T S : Finset V)
    (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ S) :
    fill U T a (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp [fill, joinBlocks, h0, hT, hS]
  · simp [fill, h0]

/-- At a vertex that is observed or a latent vertex of `T ∩ Sᶜ`, filling `T` with the joined
values agrees with filling `T ∩ Sᶜ` from `w2` alone. -/
lemma fill_joinBlocks_apply_right [∀ v, Nonempty (α v)] (U T S : Finset V)
    (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ Sᶜ) :
    fill U T a (joinBlocks U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ Sᶜ) a w2 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    have hS' : z ∉ S := Finset.mem_compl.mp hS
    simp [fill, joinBlocks, h0, hT, hS']
  · simp [fill, h0]

/-! ## Restricting to a set -/

/-- The observed vertices of `A` are observed. -/
lemma compl_inter_subset_compl (U A : Finset V) : Uᶜ ∩ A ⊆ Uᶜ := Finset.inter_subset_left

/-- The observed vertices of `A` lie in `A`. -/
lemma compl_inter_subset (U A : Finset V) : Uᶜ ∩ A ⊆ A := Finset.inter_subset_right

/-- The latent vertices of `A ∩ S` lie in `A`. -/
lemma inter_inter_subset (U A S : Finset V) : U ∩ (A ∩ S) ⊆ A :=
  fun _ hv => (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1

/-- The latent vertices of `A ∩ Sᶜ` lie in `A`. -/
lemma inter_inter_compl_subset (U A S : Finset V) : U ∩ (A ∩ Sᶜ) ⊆ A :=
  fun _ hv => (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1

/-- An assignment `b` on `A` is the restriction of the filled assignment with the joined
latent values exactly when `a` and `b` agree on the observed vertices of `A` and `w1`,
`w2` are restrictions of `b`. -/
lemma eq_restrict_fill_joinBlocks_iff [∀ v, Nonempty (α v)] (U A S : Finset V)
    (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (A ∩ S))) (w2 : Assignment (α := α) (U ∩ (A ∩ Sᶜ)))
    (b : Assignment (α := α) A) :
    b = (fill U A a (joinBlocks U A S w1 w2)).restrict (Finset.subset_univ A) ↔
      a.restrict (compl_inter_subset_compl U A) = b.restrict (compl_inter_subset U A) ∧
        w1 = b.restrict (inter_inter_subset U A S) ∧
        w2 = b.restrict (inter_inter_compl_subset U A S) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨v, hv⟩
      have h0 : v ∉ U := Finset.mem_compl.mp (Finset.mem_inter.mp hv).1
      simp [fill, Assignment.restrict, h0]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      obtain ⟨hA, hS⟩ := Finset.mem_inter.mp h1
      simp [fill, joinBlocks, Assignment.restrict, h0, hA, hS]
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      obtain ⟨hA, hS⟩ := Finset.mem_inter.mp h1
      have hS' : v ∉ S := Finset.mem_compl.mp hS
      simp [fill, joinBlocks, Assignment.restrict, h0, hA, hS']
  · rintro ⟨ha, rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases h0 : v ∈ U
    · by_cases hS : v ∈ S
      · simp [fill, joinBlocks, Assignment.restrict, h0, hv, hS]
      · simp [fill, joinBlocks, Assignment.restrict, h0, hv, hS]
    · have h := congrFun ha ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr h0, hv⟩⟩
      simpa [fill, Assignment.restrict, h0] using h.symm

/-! ## Overwriting observed values -/

/-- `a` with the values on `X` replaced by `x'`. -/
noncomputable def updX (U X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) : Assignment (α := α) Uᶜ :=
  fun v => if h : v.1 ∈ X then x' ⟨v.1, h⟩ else a v

/-- `updX` is `Rule3Flag.setZ` on the observed set `Uᶜ`. The two definitions are equal;
both are kept because both occur in the statements of public results (`setZ` in the
back-door and front-door adjustment formulas, `updX` in Verma's constraint). -/
lemma updX_eq_setZ (U X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) : updX U X a x' = Rule3Flag.setZ X Uᶜ a x' :=
  rfl

/-- Overwriting the values on `X` does not change the filled assignment outside `X`. -/
lemma fill_updX_apply_of_notMem [∀ v, Nonempty (α v)] (U T X : Finset V)
    (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∉ X) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = fill U T a w ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [fill, h0]
  · simp [fill, h0, updX, hz]

/-- At an observed vertex of `X`, the filled assignment takes the new value from `x'`. -/
lemma fill_updX_apply_of_mem [∀ v, Nonempty (α v)] (U T X : Finset V)
    (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∈ X)
    (hzU : z ∉ U) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = x' ⟨z, hz⟩ := by
  simp [fill, hzU, updX, hz]

/-- The bijection behind summing fibre by fibre: `a'` is `a` with `D` replaced by `x'`,
and `a` has the fixed value `c₀` on `D`, exactly when `a` is `a'` with `D` set to `c₀`
and `x'` is the restriction of `a'` to `D`. -/
lemma eq_updX_and_restrict_eq_iff (U D : Finset V) (hD : D ⊆ Uᶜ)
    (c0 x' : Assignment (α := α) D) (a a' : Assignment (α := α) Uᶜ) :
    (a' = updX U D a x' ∧ a.restrict hD = c0) ↔ (a = updX U D a' c0 ∧ x' = a'.restrict hD) := by
  constructor
  · rintro ⟨rfl, h2⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · have e := congrFun h2 ⟨v.1, hv⟩
        simp only [Assignment.restrict] at e
        simp only [updX, dif_pos hv]
        exact e
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · simp only [updX, dif_pos hv, Assignment.restrict]
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]

end CFactor
end Identification
