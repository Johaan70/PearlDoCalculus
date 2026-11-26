/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Expr

/-!
# Positivity of interventional marginals

The value of `prob Y Z X` (`DoCalc/Expr`) is a quotient `P_x(y, z) / P_x(z)`, and every
soundness proof for the do-calculus divides by such marginals. This file shows that the
denominators are never `0` in the models a derivation is about: those whose observed
marginal is positive everywhere, the same class as in `Identification.Identifiable`
(`docs/design-docalc-completeness.md`, section "Semantics" and decision 2).

**Statement.** Let `O = Uᶜ` be the observed vertices and suppose `P(O = a) ≠ 0` for every
assignment `a` of `O`. Then for observed `X` and `S`, every intervention value `x` and
every assignment `s` of `S` that agrees with `x` on `S ∩ X`, the marginal
`P_{do(X = x)}(S = s)` is positive (`doModel_marginal_ne_zero`). The agreement is
needed: under `do(X = x)` an assignment that differs from `x` on `X` has probability `0`
(`Idc.doModel_marginal_eq_zero`). No hypothesis on the latent vertices is needed; they
need not be roots.

**How the proof goes.**

1. *Dropping factors.* The joint of `doModel M X x` at a full assignment `u` with
   `u_X = x` is the joint of `M` at `u` with the kernel factors of `X` dropped
   (`doModel_fullJoint`). So if the joint of `M` is positive at `u`, so is the joint of
   the intervened model (`doModel_fullJoint_ne_zero`).
2. *The observed joint.* Take an observed assignment `a` with `a_X = x`. By positivity
   some full assignment `u` that extends `a` has positive mass in `M`, hence in the
   intervened model by step 1. It is a term of the sum that gives the marginal at `a`
   (`doModel_marginal_observed_ne_zero`).
3. *Smaller sets.* Join `s` and `x` to an assignment of `S ∪ X`, extend it to all of
   `O`, apply step 2, and restrict to `S` (`marginal_restrict_ne_zero`). Extending needs
   a value of every type; a causal model provides one, since its joint distribution has
   an element in its support (`nonempty_of_model`).

**Consequences for expressions.** At a total assignment `σ` the values `σ_X` and `σ_S`
always agree, so `doProb M X S σ ≠ 0` for all observed `X` and `S` (`doProb_ne_zero`).
Hence the value of `prob Y Z X` is neither `0` nor `∞` when `Y`, `Z` and `X` are
observed (`eval_prob_ne_zero`, `eval_prob_ne_top`). Well-formedness is not needed for
this.

**Safe divisors.** A derivation may divide by an expression only if it is `Positive`: a
syntactic condition saying that every `prob` in it is over observed variables, and that it
is built from such terms with `one`, `mul`, `div` and `sum`. Such an expression is
positive and finite in every model with a positive observed marginal (`eval_positive`),
by induction on the expression.

**Main results.** `nonempty_of_model`, `doModel_fullJoint_ne_zero`,
`doModel_marginal_observed_ne_zero`, `doModel_marginal_ne_zero`, `doProb_ne_zero`,
`doProb_ne_top`, `eval_prob_ne_zero`, `eval_prob_ne_top`, `Expr.Positive`,
`eval_positive`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus

open scoped ENNReal

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-! ## Positivity of the intervened model -/

/-- A causal model has a value of every type: its joint distribution has an element in
its support. -/
lemma nonempty_of_model (M : G.CausalModel α) (v : V) : Nonempty (α v) :=
  let ⟨u, _⟩ := M.fullJoint.support_nonempty
  ⟨u ⟨v, Finset.mem_univ v⟩⟩

/-- **Dropping factors.** If the joint of `M` is positive at `u` and `u` agrees with `x`
on `X`, the joint under `do(X = x)` is positive at `u`. -/
lemma doModel_fullJoint_ne_zero (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) (u : Assignment (α := α) (Finset.univ : Finset V))
    (hu : M.fullJoint u ≠ 0) (hux : u.restrict (Finset.subset_univ X) = x) :
    (doModel M X x).fullJoint u ≠ 0 := by
  rw [fullJoint_apply_prod] at hu
  rw [doModel_fullJoint, if_pos hux, one_mul]
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    Finset.prod_ne_zero_iff.mp hu v (Finset.mem_univ v)

/-- **Positivity of the interventional observed joint.** If the observed marginal is
positive and `X` is observed, every observed assignment that agrees with `x` on `X` has
positive mass under `do(X = x)`. -/
theorem doModel_marginal_observed_ne_zero (M : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0) (x : Assignment (α := α) X)
    (a : Assignment (α := α) Uᶜ) (hax : a.restrict hXO = x) :
    (doModel M X x).marginal Uᶜ a ≠ 0 := by
  have h0 := hpos a
  unfold CausalModel.marginal at h0 ⊢
  obtain ⟨u, hu, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr h0)
  have hux : u.restrict (Finset.subset_univ X) = x := by
    rw [← hax, Assignment.restrict_restrict]
  have hdo := doModel_fullJoint_ne_zero M X x u ((PMF.mem_support_iff _ _).mp hu) hux
  exact (PMF.mem_support_iff _ _).mp
    ((PMF.mem_support_map_iff _ _ _).mpr ⟨u, (PMF.mem_support_iff _ _).mpr hdo, rfl⟩)

/-- **Positive interventional marginals.** If the observed marginal is positive, the
marginal under `do(X = x)` on an observed set `S` is positive at every assignment that
agrees with `x` on `S ∩ X`. -/
theorem doModel_marginal_ne_zero (M : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0) (x : Assignment (α := α) X)
    (S : Finset V) (hS : S ⊆ Uᶜ) (s : Assignment (α := α) S)
    (hsx : ∀ v (hvS : v ∈ S) (hvX : v ∈ X), s ⟨v, hvS⟩ = x ⟨v, hvX⟩) :
    (doModel M X x).marginal S s ≠ 0 := by
  haveI : ∀ v, Nonempty (α v) := nonempty_of_model M
  obtain ⟨a, ha⟩ := Assignment.restrict_surjective (Finset.union_subset hS hXO) (s.join x)
  have hax : a.restrict hXO = x := by
    rw [← Assignment.restrict_join_right s x hsx, ← ha, Assignment.restrict_restrict]
  have has : a.restrict hS = s := by
    rw [← Assignment.restrict_join_left s x, ← ha, Assignment.restrict_restrict]
  rw [← has]
  exact marginal_restrict_ne_zero _ hS a (doModel_marginal_observed_ne_zero M U X hXO hpos x a hax)

/-! ## Positivity of `doProb` and of `prob` terms -/

section Expressions

variable (M : G.CausalModel α) (U : Finset V) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0)
include hpos

/-- **`doProb` is positive on observed sets.** At a total assignment the values on `X`
and on `S` agree, so no condition on `S ∩ X` is needed. -/
theorem doProb_ne_zero {X S : Finset V} (hXO : X ⊆ Uᶜ) (hS : S ⊆ Uᶜ) (σ : ∀ v, α v) :
    doProb M X S σ ≠ 0 :=
  doModel_marginal_ne_zero M U X hXO hpos _ S hS _ (fun _ _ _ => rfl)

omit hpos in
/-- `doProb` is a probability, so it is finite. -/
lemma doProb_ne_top (X S : Finset V) (σ : ∀ v, α v) : doProb M X S σ ≠ ⊤ :=
  PMF.apply_ne_top _ _

/-- **A `prob` term over observed variables is positive.** Its denominator is not `0`,
and neither is its numerator. -/
theorem eval_prob_ne_zero {Y Z X : Finset V} (hO : Y ∪ Z ∪ X ⊆ Uᶜ) (σ : ∀ v, α v) :
    eval M (.prob Y Z X) σ ≠ 0 := by
  have hYZ : Y ∪ Z ⊆ Uᶜ := Finset.subset_union_left.trans hO
  have hX : X ⊆ Uᶜ := Finset.subset_union_right.trans hO
  rw [eval_prob, Ne, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨doProb_ne_zero M U hpos hX hYZ σ, doProb_ne_top M X Z σ⟩

/-- **A `prob` term over observed variables is finite**, because its denominator is not
`0`. -/
theorem eval_prob_ne_top {Y Z X : Finset V} (hO : Y ∪ Z ∪ X ⊆ Uᶜ) (σ : ∀ v, α v) :
    eval M (.prob Y Z X) σ ≠ ⊤ := by
  have hZ : Z ⊆ Uᶜ := Finset.subset_union_right.trans (Finset.subset_union_left.trans hO)
  have hX : X ⊆ Uᶜ := Finset.subset_union_right.trans hO
  exact ENNReal.div_ne_top (doProb_ne_top M X (Y ∪ Z) σ) (doProb_ne_zero M U hpos hX hZ σ)

end Expressions

/-! ## Expressions that are safe divisors

The steps `e / e = 1` and `(a · b) / b = a` of a derivation (`DoCalc/Derives`) are only
sound when the divisor is neither `0` nor `∞`. `Expr.Positive U e` is a syntactic
condition that guarantees this in every model with a positive observed marginal: every
`prob` in `e` is over observed variables, and `e` is built from such terms with `one`,
`mul`, `div` and `sum`. -/

/-- `e` is built from `prob` terms over observed variables (`Y ∪ Z ∪ X ⊆ Uᶜ`) with `one`,
`mul`, `div` and `sum`. Such an expression is positive and finite in every model with a
positive observed marginal (`eval_positive`). -/
@[simp] def Expr.Positive (U : Finset V) : Expr V → Prop
  | .prob Y Z X => Y ∪ Z ∪ X ⊆ Uᶜ
  | .one => True
  | .mul e₁ e₂ => e₁.Positive U ∧ e₂.Positive U
  | .div e₁ e₂ => e₁.Positive U ∧ e₂.Positive U
  | .sum _ e => e.Positive U

/-- **A `Positive` expression is positive and finite** in every model with a positive
observed marginal. A sum is over the finitely many assignments of a set, at least one of
which exists (`nonempty_of_model`). -/
theorem eval_positive (M : G.CausalModel α) (U : Finset V) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0)
    {e : Expr V} (he : e.Positive U) (σ : ∀ v, α v) :
    eval M e σ ≠ 0 ∧ eval M e σ ≠ ⊤ := by
  induction e generalizing σ with
  | prob Y Z X => exact ⟨eval_prob_ne_zero M U hpos he σ, eval_prob_ne_top M U hpos he σ⟩
  | one => simp
  | mul e₁ e₂ h₁ h₂ =>
    obtain ⟨a0, at'⟩ := h₁ he.1 σ
    obtain ⟨b0, bt⟩ := h₂ he.2 σ
    exact ⟨mul_ne_zero a0 b0, ENNReal.mul_ne_top at' bt⟩
  | div e₁ e₂ h₁ h₂ =>
    obtain ⟨a0, at'⟩ := h₁ he.1 σ
    obtain ⟨b0, bt⟩ := h₂ he.2 σ
    rw [eval_div]
    exact ⟨ENNReal.div_ne_zero.mpr ⟨a0, bt⟩, ENNReal.div_ne_top at' b0⟩
  | sum S e ih =>
    haveI : ∀ v, Nonempty (α v) := nonempty_of_model M
    haveI : ∀ v, Fintype (α v) := M.fin
    haveI : Fintype (Assignment (α := α) S) :=
      inferInstanceAs (Fintype (∀ v : {v // v ∈ S}, α v.1))
    let τ : Assignment (α := α) S := fun _ => Classical.arbitrary _
    rw [eval_sum]
    refine ⟨fun h0 => (ih he _).1 (ENNReal.tsum_eq_zero.mp h0 τ), ?_⟩
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun τ _ => (ih he _).2

end DoCalc
