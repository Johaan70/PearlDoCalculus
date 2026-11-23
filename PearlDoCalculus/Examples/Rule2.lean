import PearlDoCalculus.Examples.DSeparation
import PearlDoCalculus.DoCalculus

/-!
# Examples for rule 2 of the do-calculus: it needs its condition, and is not vacuous

Two small examples that check rule 2 of the do-calculus (`DoCalculus.rule2_core`) in both
directions.

1. *The condition is needed* (`rule2_fails_with_confounder`). In the hidden-confounder
   graph `Z ← U → Y` (`confG`, `confModel`), `U` is uniform and `Z`, `Y` are copies of
   `U`. Here `Y` and `Z` are not d-separated in `G_{Z̲}`, and the conclusion of rule 2
   fails: `P(y=1, z=0) · P_{z=0}(∅) = 0`, but `P_{z=0}(y=1) · P(z=0) ≠ 0`. Observing `Z`
   and intervening on `Z` differ, as they should.
2. *The rule is not vacuous* (`rule2_holds_nontrivially`). In the graph `Z → Y`
   (`copyModel`: `Z` uniform, `Y` a copy of `Z`) the condition holds, and the identity of
   `rule2_core` has left side `P(y=1, z=1) · P_{z=1}(∅) = ½ ≠ 0`, so it is not true
   merely because both sides are `0`.

**Main results.** `Examples.Rule2.rule2_fails_with_confounder`,
`Examples.Rule2.rule2_holds_nontrivially`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical
open Examples.DSeparation (edgeG mem_parents_one)

namespace Examples.Rule2

/-- The confounder graph: `U = 0`, `Z = 1`, `Y = 2`, with `0 → 1` and `0 → 2`. -/
def confG : DAG (Fin 3) where
  edge u v := u = 0 ∧ (v = 1 ∨ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ (v = 1 ∨ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl | rfl⟩ <;> decide

/-- `U = 0` is a parent of every other vertex. -/
lemma zero_mem_parents {v : Fin 3} (hv : v ≠ 0) : (0 : Fin 3) ∈ confG.parents v := by
  fin_cases v <;> simp_all [DAG.mem_parents, confG]

/-- `U` uniform; `Z` and `Y` are copies of `U`. -/
noncomputable def confModel : confG.CausalModel (fun _ => Fin 2) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 0 then PMF.uniformOfFinset Finset.univ ⟨0, by simp⟩
    else PMF.pure (pa ⟨0, zero_mem_parents hv⟩)

/-- Assignments of bits to a set of vertices of `confG`. -/
abbrev A2 (S : Finset (Fin 3)) := Assignment (α := fun _ : Fin 3 => Fin 2) S

/-- The intervention value `z₀ = 0`. -/
def z₀ : A2 {1} := fun _ => 0

/-- The test assignment `y = 1, z = 0` on `Y ∪ Z ∪ W = {2} ∪ {1} ∪ ∅`. -/
def tT : A2 ({2} ∪ {1} ∪ ∅) := fun v => if v.1 = 2 then 1 else 0

/-- Witness for `P(z=0) > 0`: everything is `0`. -/
def uAll0 : A2 Finset.univ := fun _ => 0

/-- Witness for `P_{z=0}(y=1) > 0`: `U = 1`, `Z = 0` (set), `Y = 1`. -/
def uW : A2 Finset.univ := fun v => if v.1 = 1 then 0 else 1

/-- **Example: rule 2 needs the d-separation condition.** In the confounder model the
product identity of `rule2_core` fails. -/
theorem rule2_fails_with_confounder :
    confModel.marginal ({2} ∪ {1} ∪ ∅) tT *
      (doModel confModel {1} z₀).marginal ∅ (tT.restrict (by
        intro v hv; simp at hv)) ≠
    (doModel confModel {1} z₀).marginal ({2} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      confModel.marginal ({1} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  -- Left side: Z and Y are always equal, so P(y=1, z=0) = 0.
  have hL : confModel.marginal ({2} ∪ {1} ∪ ∅) tT = 0 := by
    refine marginal_eq_zero_of_kfac_eq_zero confModel _ tT (fun u hu => ?_)
    have h1 : u ⟨1, Finset.mem_univ 1⟩ = 0 := by
      have := congrFun hu ⟨1, by simp⟩
      simpa [Assignment.restrict, tT] using this
    have h2 : u ⟨2, Finset.mem_univ 2⟩ = 1 := by
      have := congrFun hu ⟨2, by simp⟩
      simpa [Assignment.restrict, tT] using this
    by_cases h0 : u ⟨0, Finset.mem_univ 0⟩ = 0
    · refine ⟨2, ?_⟩
      rw [kfac_univ]
      simp [confModel, Assignment.restrict, h0, h2, PMF.pure_apply]
    · have h0' : (0 : Fin 2) ≠ u ⟨0, Finset.mem_univ 0⟩ := Ne.symm h0
      refine ⟨1, ?_⟩
      rw [kfac_univ]
      simp [confModel, Assignment.restrict, h1, h0', PMF.pure_apply]
  -- Right side: both factors are positive.
  have hR1 : (doModel confModel {1} z₀).marginal ({2} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine marginal_ne_zero_of_kfac_ne_zero _ _ _ uW ?_ (fun v => ?_)
    · funext ⟨v, hv⟩
      have : v = 2 := by simpa using hv
      subst this
      simp [Assignment.restrict, tT, uW]
    · rw [kfac_doModel]
      fin_cases v <;> simp [z₀, uW, kfac_univ, confModel, Assignment.restrict,
        PMF.pure_apply, PMF.uniformOfFinset_apply]
  have hR2 : confModel.marginal ({1} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine marginal_ne_zero_of_kfac_ne_zero _ _ _ uAll0 ?_ (fun v => ?_)
    · funext ⟨v, hv⟩
      have : v = 1 := by simpa using hv
      subst this
      simp [Assignment.restrict, tT, uAll0]
    · rw [kfac_univ]
      fin_cases v <;> simp [uAll0, confModel, Assignment.restrict,
        PMF.pure_apply, PMF.uniformOfFinset_apply]
  intro heq
  rw [hL, zero_mul] at heq
  exact mul_ne_zero hR1 hR2 heq.symm

/-! ## Rule 2 holds, and is not vacuous

`Z → Y` on `Fin 2` (`Z = 0`, `Y = 1`) with `Z` uniform and `Y` a copy of `Z`. In `G_{Z̲}`
the only edge is removed, so the condition holds. The identity of `rule2_core` has left
side `P(y=1, z=1) · P_{z=1}(∅) = ½ ≠ 0`: the theorem is not true merely because both
sides are `0`. -/

/-- Assignments of bits to a set of vertices of `edgeG` (from `Examples/DSeparation`). -/
abbrev B2 (S : Finset (Fin 2)) := Assignment (α := fun _ : Fin 2 => Fin 2) S

/-- `Z` uniform; `Y` is a copy of `Z`. -/
noncomputable def copyModel : edgeG.CausalModel (fun _ => Fin 2) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 1 then PMF.pure (pa ⟨0, by subst hv; exact mem_parents_one⟩)
    else PMF.uniformOfFinset Finset.univ ⟨0, by simp⟩

/-- In `G_{Z̲}` with `Z = {0}` there are no edges, so no walk between distinct
vertices. -/
lemma no_walk_cutOut : ∀ {a b : Fin 2}, Walk (cutOut edgeG {0}) a b →
    a ≠ b → False := by
  intro a b p hab
  cases p with
  | nil => exact hab rfl
  | fwd e _ => exact e.2 (Finset.mem_singleton.mpr e.1.1)
  | bwd e _ => exact e.2 (Finset.mem_singleton.mpr e.1.1)

/-- The intervention value `z = 1`. -/
def zP : B2 {0} := fun _ => 1
/-- The test assignment `y = 1, z = 1`. -/
def tP : B2 ({1} ∪ {0} ∪ ∅) := fun _ => 1
/-- The full assignment with every vertex `1`. -/
def u11 : B2 Finset.univ := fun _ => 1

/-- **Example: rule 2 holds and is not vacuous.** The condition holds, and the identity of
`rule2_core` has a left side `≠ 0`. -/
theorem rule2_holds_nontrivially :
    copyModel.marginal ({1} ∪ {0} ∪ ∅) tP *
        (doModel copyModel {0} zP).marginal ∅ (tP.restrict (by intro v hv; simp at hv)) ≠ 0 ∧
    copyModel.marginal ({1} ∪ {0} ∪ ∅) tP *
        (doModel copyModel {0} zP).marginal ∅ (tP.restrict (by intro v hv; simp at hv)) =
      (doModel copyModel {0} zP).marginal ({1} ∪ ∅) (tP.restrict (by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
        copyModel.marginal ({0} ∪ ∅) (tP.restrict (by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have h : SetSound.DSeparatedSet (cutOut edgeG {0}) ∅ {1} {0} := by
    intro y hy z hz p _
    exfalso
    refine no_walk_cutOut p ?_
    simp only [Finset.mem_singleton] at hy hz
    subst hy
    subst hz
    decide
  refine ⟨mul_ne_zero ?_ ?_, rule2_core copyModel {1} {0} ∅ zP (by simp) (by simp) (by simp)
    h tP (by funext ⟨v, hv⟩; rfl)⟩
  · refine marginal_ne_zero_of_kfac_ne_zero _ _ _ u11 (by funext ⟨v, hv⟩; rfl) (fun v => ?_)
    rw [kfac_univ]
    fin_cases v <;> simp [copyModel, u11, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]
  · refine marginal_ne_zero_of_kfac_ne_zero _ _ _ u11 (by funext ⟨v, hv⟩; simp at hv) (fun v => ?_)
    rw [kfac_doModel]
    fin_cases v <;> simp [copyModel, u11, zP, kfac_univ, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]

end Examples.Rule2

#print axioms Examples.Rule2.rule2_fails_with_confounder
#print axioms Examples.Rule2.rule2_holds_nontrivially
