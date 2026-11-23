import PearlDoCalculus.Soundness.Counterexample
import Mathlib.Probability.Distributions.Uniform

/-!
# Audit: regression tests for the semantics of d-separation

Definitions like `DSeparated` and `CondIndep` are easy to get subtly wrong, for example
so that every pair of vertices is separated, or every model is independent. Then the
soundness theorem would hold for the wrong reason. This file checks the definitions on
small graphs where the right answer is known.

Four mechanisms of d-separation are tested:
* chain `0 → 1 → 2` without conditioning: the chain is open (`chain_not_dsep_empty`);
* chain `0 → 1 → 2` conditioned on the middle vertex: `0` and `2` are d-separated
  (`chain_dsep_cond`, by induction over walks, `chain_blocked`);
* collider `0 → 2 ← 1` without conditioning: the collider blocks
  (`collider_dsep_empty`);
* collider `0 → 2 ← 1` conditioned on the collider: the collider opens
  (`collider_not_dsep_cond`).

Finally `not_condIndep_dep` checks that `CondIndep` can fail: in a model `x → y` where
`y` depends on `x`, the product form is violated.

**Main results.** `chain_not_dsep_empty`, `chain_dsep_cond`, `collider_dsep_empty`,
`collider_not_dsep_cond`, `not_condIndep_dep`. The helpers `marginal_eq_zero_of` and
`marginal_ne_zero_of` are reused by the other audit files.
-/

open PearlDoCalculus DAG DAG.CausalModel

namespace Audit

/-- The chain `0 → 1 → 2`. -/
def chainG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Chain without conditioning: the walk `0 → 1 → 2` is open. -/
theorem chain_not_dsep_empty : ¬ chainG.DSeparated ∅ 0 2 := by
  intro h
  have hb := h (Walk.fwd (Or.inl ⟨rfl, rfl⟩) (Walk.fwd (Or.inr ⟨rfl, rfl⟩) (Walk.nil 2)))
  simp [Walk.Blocked, Walk.blockedAux] at hb

/-- Collider without conditioning: `0` and `1` are d-separated. -/
theorem collider_dsep_empty : Counterexample.ceG.DSeparated ∅ 0 1 :=
  fun p => Counterexample.blocked_from_source (by decide) (by decide) (by decide) p

/-- Collider conditioned on the collider: the walk `0 → 2 ← 1` opens. -/
theorem collider_not_dsep_cond : ¬ Counterexample.ceG.DSeparated {2} 0 1 := by
  intro h
  have hb := h (Walk.fwd ⟨rfl, by decide⟩ (Walk.bwd ⟨rfl, by decide⟩ (Walk.nil 1)))
  simp only [Walk.Blocked, Walk.blockedAux, or_false] at hb
  exact hb 2 (Finset.mem_singleton_self 2) (DAG.Reaches.refl _ 2)

/-- State analysis for the chain with `Z = {1}`. Three claims are carried together
through the induction over the walk:
* if the walk stands at `1` with an incoming direction, the rest is blocked;
* if it stands at `0` after arriving backwards (from the collider at `1`), the rest is
  blocked;
* if it starts at `0`, it is blocked.
The collider at `1` (in `0 → 1 ← 0`) is open because `1 ∈ Z`, but it leads back to
`0`. -/
lemma chain_blocked : ∀ {s t : Fin 3} (p : Walk chainG s t), t = 2 →
    (s = 1 → ∀ inc : Incoming, inc ≠ Incoming.start → Walk.blockedAux {1} inc p) ∧
    (s = 0 → Walk.blockedAux {1} Incoming.bwd p) ∧
    (s = 0 → Walk.blockedAux {1} Incoming.start p) := by
  intro s t p
  induction p with
  | nil v =>
    intro ht
    subst ht
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
  | @fwd a b c e rest ih =>
    intro ht
    have ih' := ih ht
    refine ⟨fun hs inc hinc => ?_, fun hs => ?_, fun hs => ?_⟩
    · subst hs
      cases inc with
      | start => exact absurd rfl hinc
      | fwd => simp only [Walk.blockedAux]; exact Or.inl (by simp)
      | bwd => simp only [Walk.blockedAux]; exact Or.inl (by simp)
    · subst hs
      have hb : b = 1 := by
        rcases e with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (by decide)
      simp only [Walk.blockedAux]
      exact Or.inr (ih'.1 hb .fwd (fun h => by cases h))
    · subst hs
      have hb : b = 1 := by
        rcases e with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (by decide)
      simp only [Walk.blockedAux]
      exact ih'.1 hb .fwd (fun h => by cases h)
  | @bwd a b c e rest ih =>
    intro ht
    have ih' := ih ht
    refine ⟨fun hs inc hinc => ?_, fun hs => ?_, fun hs => ?_⟩
    · subst hs
      have hb : b = 0 := by
        rcases e with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · exact absurd h (by decide)
      cases inc with
      | start => exact absurd rfl hinc
      | fwd => simp only [Walk.blockedAux]; exact Or.inr (ih'.2.1 hb)
      | bwd => simp only [Walk.blockedAux]; exact Or.inl (by simp)
    · subst hs
      exfalso
      rcases e with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
    · subst hs
      exfalso
      rcases e with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- Chain conditioned on the middle vertex: `0` and `2` are d-separated. -/
theorem chain_dsep_cond : chainG.DSeparated {1} 0 2 :=
  fun p => (chain_blocked p rfl).2.2 rfl

/-! ## `CondIndep` can fail

Model `x → y` on `Fin 2` with values in `Fin 3`. `x` is uniform on `{0, 1}`; `y` is
uniform on `{0, 1}` when `x = 0` and uniform on `{1, 2}` when `x = 1`. Then
`P(x=1, y=0) = 0`, while `P(x=1) > 0` and `P(y=0) > 0`, so the product form fails. The
kernels are nondegenerate, but the proof only needs zero versus nonzero. -/

/-- The marginal is `0` when every extension has a kernel factor equal to `0`. -/
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

/-- The marginal is `≠ 0` when one extension has all kernel factors `≠ 0`. -/
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

/-- The two-vertex graph `0 → 1`. -/
def edgeG : DAG (Fin 2) where
  edge u v := u = 0 ∧ v = 1
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ v = 1))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩
    decide

/-- `0` is a parent of `1`. -/
lemma mem_parents_one : (0 : Fin 2) ∈ edgeG.parents 1 := by
  simp [DAG.parents, edgeG]

/-- `x` uniform on `{0,1}`; `y` uniform on `{0,1}` or `{1,2}` depending on `x`. -/
noncomputable def depModel : edgeG.CausalModel (fun _ => Fin 3) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 1 then
      (if pa ⟨0, by subst hv; exact mem_parents_one⟩ = 0
        then PMF.uniformOfFinset {0, 1} ⟨0, by simp⟩
        else PMF.uniformOfFinset {1, 2} ⟨1, by simp⟩)
    else PMF.uniformOfFinset {0, 1} ⟨0, by simp⟩

/-- The kernel factors of `depModel` on a full assignment. -/
lemma kfac_dep (u : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)))
    (v : Fin 2) :
    kfac depModel Finset.univ u v =
      depModel.kernel v (u.restrict (Finset.subset_univ _)) (u ⟨v, Finset.mem_univ v⟩) := by
  have hc : v ∈ (Finset.univ : Finset (Fin 2)) ∧ edgeG.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  rw [dif_pos hc]

/-- The test assignment `x = 1, y = 0`. -/
def wTest : Assignment (α := fun _ : Fin 2 => Fin 3) (({0} ∪ {1} ∪ ∅ : Finset (Fin 2))) :=
  fun v => if v.1 = 0 then 1 else 0

/-- Witness: `(1,1)` has positive mass and `x = 1`. -/
def u1 : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)) := fun _ => 1
/-- Witness: `(0,0)` has positive mass and `y = 0`. -/
def u0 : Assignment (α := fun _ : Fin 2 => Fin 3) (Finset.univ : Finset (Fin 2)) := fun _ => 0

/-- **Audit C.** `CondIndep` is not trivially true. -/
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
#print axioms Audit.chain_dsep_cond
