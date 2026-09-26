import PearlDoCalculus.Counterexample
import Mathlib.Probability.Distributions.Uniform

/-!
# Audit: regresjonstester for d-separasjonssemantikken

Tre mekanismer testes:
* kjede `0 → 1 → 2`: uten betinging er kjeden åpen;
* kollider `0 → 2 ← 1`: uten betinging blokkerer kollideren;
* kollider `0 → 2 ← 1`: betinging på kollideren åpner den.

Den positive kjede-testen `DSeparated {1} 0 2` krever induksjon over
vandringer og kommer i en egen runde.
-/

open PearlDoCalculus DAG DAG.CausalModel

namespace Audit

/-- Kjeden `0 → 1 → 2`. -/
def chainG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Kjede uten betinging: vandringen `0 → 1 → 2` er åpen. -/
theorem chain_not_dsep_empty : ¬ chainG.DSeparated ∅ 0 2 := by
  intro h
  have hb := h (Walk.fwd (Or.inl ⟨rfl, rfl⟩) (Walk.fwd (Or.inr ⟨rfl, rfl⟩) (Walk.nil 2)))
  simp [Walk.Blocked, Walk.blockedAux] at hb

/-- Kollider uten betinging: `0` og `1` er d-separert. -/
theorem collider_dsep_empty : Counterexample.ceG.DSeparated ∅ 0 1 :=
  fun p => Counterexample.blocked_from_source (by decide) (by decide) (by decide) p

/-- Kollider med betinging på kollideren: vandringen `0 → 2 ← 1` åpnes. -/
theorem collider_not_dsep_cond : ¬ Counterexample.ceG.DSeparated {2} 0 1 := by
  intro h
  have hb := h (Walk.fwd ⟨rfl, by decide⟩ (Walk.bwd ⟨rfl, by decide⟩ (Walk.nil 1)))
  simp only [Walk.Blocked, Walk.blockedAux, or_false] at hb
  exact hb 2 (Finset.mem_singleton_self 2) (DAG.Reaches.refl _ 2)

/-! ## `CondIndep` kan feile

Modell `x → y` på `Fin 2` med verdier i `Fin 3`. `x` er uniform på `{0, 1}`;
`y` er uniform på `{0, 1}` når `x = 0` og uniform på `{1, 2}` når `x = 1`.
Da er `P(x=1, y=0) = 0`, mens `P(x=1) > 0` og `P(y=0) > 0`, så produktformen
feiler. Kjernene er ikke-degenererte, men beviset trenger bare null/ikke-null. -/

/-- Marginalen er 0 når hver utvidelse har en kjernefaktor lik 0. -/
lemma marginal_eq_zero_of {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}
    {α : V → Type*} (M : G.CausalModel α) (S : Finset V) (a : Assignment (α := α) S)
    (h : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
      u.restrict (Finset.subset_univ S) = a → ∃ v, kfac M Finset.univ u v = 0) :
    M.marginal S a = 0 := by
  unfold CausalModel.marginal
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro u
  split_ifs with hu
  · rw [fullJoint_apply_prod]
    obtain ⟨v, hv⟩ := h u hu.symm
    exact Finset.prod_eq_zero (Finset.mem_univ v) hv
  · rfl

/-- Marginalen er ≠ 0 når én utvidelse har alle kjernefaktorer ≠ 0. -/
lemma marginal_ne_zero_of {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}
    {α : V → Type*} (M : G.CausalModel α) (S : Finset V) (a : Assignment (α := α) S)
    (u : Assignment (α := α) (Finset.univ : Finset V))
    (hu : u.restrict (Finset.subset_univ S) = a)
    (hpos : ∀ v, kfac M Finset.univ u v ≠ 0) :
    M.marginal S a ≠ 0 := by
  rw [← PMF.mem_support_iff]
  unfold CausalModel.marginal
  rw [PMF.support_map]
  refine ⟨u, (PMF.mem_support_iff _ _).mpr ?_, hu⟩
  rw [fullJoint_apply_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => hpos v)

/-- To-node-grafen `0 → 1`. -/
def edgeG : DAG (Fin 2) where
  edge u v := u = 0 ∧ v = 1
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ v = 1))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩
    decide

lemma mem_parents_one : (0 : Fin 2) ∈ edgeG.parents 1 := by
  simp [DAG.parents, edgeG]

/-- `x` uniform på `{0,1}`; `y` uniform på `{0,1}` eller `{1,2}` etter `x`. -/
noncomputable def depModel : edgeG.CausalModel (fun _ => Fin 3) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 1 then
      (if pa ⟨0, by subst hv; exact mem_parents_one⟩ = 0
        then PMF.uniformOfFinset {0, 1} ⟨0, by simp⟩
        else PMF.uniformOfFinset {1, 2} ⟨1, by simp⟩)
    else PMF.uniformOfFinset {0, 1} ⟨0, by simp⟩

lemma kfac_dep (u : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)))
    (v : Fin 2) :
    kfac depModel Finset.univ u v =
      depModel.kernel v (u.restrict (Finset.subset_univ _)) (u ⟨v, Finset.mem_univ v⟩) := by
  have hc : v ∈ (Finset.univ : Finset (Fin 2)) ∧ edgeG.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  rw [dif_pos hc]

/-- Test-tilordningen `x = 1, y = 0`. -/
def wTest : Assignment (α := fun _ : Fin 2 => Fin 3) (({0} ∪ {1} ∪ ∅ : Finset (Fin 2))) :=
  fun v => if v.1 = 0 then 1 else 0

/-- Vitner: `(1,1)` har positiv masse og `x = 1`; `(0,0)` har positiv masse og `y = 0`. -/
def u1 : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)) := fun _ => 1
def u0 : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)) := fun _ => 0

/-- **Audit C.** `CondIndep` er ikke trivielt sann. -/
theorem not_condIndep_dep : ¬ depModel.CondIndep {0} {1} ∅ := by
  intro h
  have hw := h wTest
  have hL : depModel.marginal ({0} ∪ {1} ∪ ∅) wTest = 0 := by
    refine marginal_eq_zero_of depModel _ wTest (fun u hu => ⟨1, ?_⟩)
    have h0 : u ⟨0, Finset.mem_univ 0⟩ = 1 := by
      have := congrFun hu ⟨0, by simp⟩
      simpa [Assignment.restrict, wTest] using this
    have h1 : u ⟨1, Finset.mem_univ 1⟩ = 0 := by
      have := congrFun hu ⟨1, by simp⟩
      simpa [Assignment.restrict, wTest] using this
    rw [kfac_dep]
    simp [depModel, Assignment.restrict, h0, h1, PMF.uniformOfFinset_apply]
  have posU1 : ∀ v, kfac depModel Finset.univ u1 v ≠ 0 := by
    intro v
    rw [kfac_dep]
    fin_cases v <;> simp [depModel, u1, Assignment.restrict, PMF.uniformOfFinset_apply]
  have posU0 : ∀ v, kfac depModel Finset.univ u0 v ≠ 0 := by
    intro v
    rw [kfac_dep]
    fin_cases v <;> simp [depModel, u0, Assignment.restrict, PMF.uniformOfFinset_apply]
  rw [hL, zero_mul] at hw
  refine absurd hw.symm (mul_ne_zero
    (marginal_ne_zero_of depModel _ _ u1 ?_ posU1)
    (marginal_ne_zero_of depModel _ _ u0 ?_ posU0))
  · funext ⟨v, hv⟩
    have : v = 0 := by simpa using hv
    subst this
    simp [Assignment.restrict, wTest, u1]
  · funext ⟨v, hv⟩
    have : v = 1 := by simpa using hv
    subst this
    simp [Assignment.restrict, wTest, u0]

end Audit

#print axioms Audit.chain_not_dsep_empty
#print axioms Audit.collider_dsep_empty
#print axioms Audit.collider_not_dsep_cond
#print axioms Audit.not_condIndep_dep
