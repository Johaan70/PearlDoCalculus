import PearlDoCalculus.Identification.Basic

/-!
# The bow graph is not identifiable

The bow graph has a latent `u` with edges `u → x`, `u → y` and `x → y`. We show that
`P(y | do(x))` is not identifiable from the observed nodes `{x, y}`, first in the bow
graph itself (`Identification.Bow.bow_not_identifiable`) and then inside any graph that
contains such a bow (`Identification.BowEmbedded.bow_not_identifiable_general`).

Why it is needed: the bow is the smallest hedge, and the first case where Tian's
criterion fails. `TianIff` uses `bow_not_identifiable_general` for the case of a single
latent step in `tian_iff`. The noisy channel `Bow.chan` (with `chan_apply`,
`chan_ne_zero`, `q_ne`), the one-edge graph `BowEmbedded.g1` and its ancestral sets
(`BowEmbedded.ancB`) are reused by every later family of hedge counter-models (`HedgeChain`,
`HedgeTemplate`, `RootPathModels`, `RootPath`), and so is the way a model on a small
subgraph is embedded in a larger graph (`Completeness.liftSub`, with the kernel factors
`Completeness.kfac_liftSub` and `Completeness.kfac_doModel_liftSub`).

How the proof goes: two models give the same positive distribution on `{x, y}` but
different `P(y | do(x))`. In model A the latent `u` is uniform, `x` is a noisy copy of
`u` and `y = u`. In model B `u` is fixed, `x` is uniform and `y` is a noisy copy of `x`.
The joint distributions agree after the bijection `φ` that replaces `u` by `u xor y`.
In model A, `x` does not reach `y` once its incoming edge is cut, so `P(y | do(x))` is the
observed `P(y)` and does not depend on `x`. In model B, `x` has no parents, so
`P(y | do(x)) = P(x, y) / P(x)` (the first front-door step,
`Adjustment.frontdoor_step1`), which is the channel and does depend on `x`, since
`3/4 ≠ 1/4`. In the general case all other nodes are independent uniform bits, which
keeps the observed distribution positive.

Main results:

* `Identification.Bow.bow_not_identifiable`
* `Identification.BowEmbedded.bow_not_identifiable_general`
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical
open scoped ENNReal

/-! ## The bow graph itself

`U = 0` (latent), `X = 1`, `Y = 2`, with `U → X`, `U → Y`, `X → Y`. Two models give
the same positive distribution on `{X, Y}`, but different `P(Y | do(X))`.

* Model A: `U` uniform, `X` a noisy copy of `U`, `Y = U` (ignores `X`).
* Model B: `U = 0` fixed, `X` uniform, `Y` a noisy copy of `X`.

The joint distributions agree after a bijection that changes only `U`. In A,
`P_x(Y)` is the same for both values of `x` (`doA`); in B, `P(x, y) = P_x(y) · P(x)`
(the first front-door step), and the channel separates the two values of `x`:
`3/4 ≠ 1/4`. -/


namespace Identification
namespace Bow

/-- The bow graph on `Fin 3`: `0 → 1`, `0 → 2`, `1 → 2`, with `0` the latent node. -/
def bowG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v =>
    inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The graph of model A: `U → X`, `U → Y`. -/
def gA : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The graph of model B: `X → Y`. -/
def gB : DAG (Fin 3) where
  edge u v := u = 1 ∧ v = 2
  decEdge := fun u v => inferInstanceAs (Decidable (u = 1 ∧ v = 2))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩
    decide

/-- `U` is a parent of `X` in the graph of model A. -/
lemma pA1 : (0 : Fin 3) ∈ gA.parents 1 := by simp [DAG.parents, gA]
/-- `U` is a parent of `Y` in the graph of model A. -/
lemma pA2 : (0 : Fin 3) ∈ gA.parents 2 := by simp [DAG.parents, gA]
/-- `X` is a parent of `Y` in the graph of model B. -/
lemma pB2 : (1 : Fin 3) ∈ gB.parents 2 := by simp [DAG.parents, gB]

/-- The two probabilities of the channel add up to one. -/
lemma q_sum : (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- The two probabilities of the channel differ; this is what separates the two models. -/
lemma q_ne : (3 / 4 : ℝ≥0∞) ≠ 1 / 4 := by
  intro h
  have h2 := congrArg ENNReal.toReal h
  norm_num [ENNReal.toReal_div] at h2

/-- `3/4` is not zero. -/
lemma q_pos3 : (3 / 4 : ℝ≥0∞) ≠ 0 := by
  simp

/-- `1/4` is not zero. -/
lemma q_pos1 : (1 / 4 : ℝ≥0∞) ≠ 0 := by
  simp

/-- The noisy channel: the output `c` equals the input `b` with probability `3/4`. -/
noncomputable def chan (b : Bool) : PMF Bool :=
  PMF.ofFintype (fun c => if c = b then 3 / 4 else 1 / 4) (by
    rw [Fintype.sum_bool]
    cases b
    · rw [if_neg (show ¬ (true = false) by decide), if_pos (show false = false from rfl),
        add_comm]
      exact q_sum
    · rw [if_pos (show true = true from rfl), if_neg (show ¬ (false = true) by decide)]
      exact q_sum)

/-- The value of the channel at an output `c`. -/
lemma chan_apply (b c : Bool) : chan b c = if c = b then 3 / 4 else 1 / 4 :=
  PMF.ofFintype_apply _ _

/-- Every output of the channel has positive probability. -/
lemma chan_ne_zero (b c : Bool) : chan b c ≠ 0 := by
  rw [chan_apply]
  split_ifs
  · exact q_pos3
  · exact q_pos1

/-- Model A: `U` uniform, `X` a noisy copy of `U`, `Y = U`. -/
noncomputable def NA : gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h1 : v = 1 then chan (pa ⟨0, by rw [h1]; exact pA1⟩)
    else if h2 : v = 2 then PMF.pure (pa ⟨0, by rw [h2]; exact pA2⟩)
    else PMF.uniformOfFintype Bool

/-- Model B: `U = 0`, `X` uniform, `Y` a noisy copy of `X`. -/
noncomputable def NB : gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h2 : v = 2 then chan (pa ⟨1, by rw [h2]; exact pB2⟩)
    else if v = 1 then PMF.uniformOfFintype Bool
    else PMF.pure false

/-- The kernel of `U` in model A is uniform. -/
lemma NA_k0 (pa : {u // u ∈ gA.parents 0} → Bool) : NA.kernel 0 pa = PMF.uniformOfFintype Bool := by
  rfl
/-- The kernel of `X` in model A is the channel applied to `U`. -/
lemma NA_k1 (pa : {u // u ∈ gA.parents 1} → Bool) : NA.kernel 1 pa = chan (pa ⟨0, pA1⟩) := by
  rfl
/-- The kernel of `Y` in model A copies `U`. -/
lemma NA_k2 (pa : {u // u ∈ gA.parents 2} → Bool) : NA.kernel 2 pa = PMF.pure (pa ⟨0, pA2⟩) := by
  rfl
/-- The kernel of `U` in model B is the constant `false`. -/
lemma NB_k0 (pa : {u // u ∈ gB.parents 0} → Bool) : NB.kernel 0 pa = PMF.pure false := by
  rfl
/-- The kernel of `X` in model B is uniform. -/
lemma NB_k1 (pa : {u // u ∈ gB.parents 1} → Bool) : NB.kernel 1 pa = PMF.uniformOfFintype Bool := by
  rfl
/-- The kernel of `Y` in model B is the channel applied to `X`. -/
lemma NB_k2 (pa : {u // u ∈ gB.parents 2} → Bool) : NB.kernel 2 pa = chan (pa ⟨1, pB2⟩) := by
  rfl

/-- The graph of model A is a subgraph of the bow graph. -/
lemma gA_parents_subset : ∀ v, gA.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.mem_parents] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) := hu
  tauto

/-- The graph of model B is a subgraph of the bow graph. -/
lemma gB_parents_subset : ∀ v, gB.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.mem_parents] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : u = 1 ∧ v = 2 := hu
  tauto

/-- Model A as a model on the bow graph. -/
noncomputable def mA : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub gA_parents_subset NA
/-- Model B as a model on the bow graph. -/
noncomputable def mB : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub gB_parents_subset NB

/-- The bijection of full assignments: it changes only `U`, to `U xor Y`. -/
def φ (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3)) :=
  fun v => if v.1 = 0 then xor (u ⟨0, Finset.mem_univ 0⟩) (u ⟨2, Finset.mem_univ 2⟩) else u v

/-- `φ` is an involution. -/
lemma φ_invol (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    φ (φ u) = u := by
  funext ⟨v, hv⟩
  by_cases h : v = 0
  · subst h
    simp [φ, Bool.xor_assoc]
  · simp [φ, h]

/-- Model B gives `φ u` the probability that model A gives `u`. -/
lemma joint_eq (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    mB.fullJoint (φ u) = mA.fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [mA, mB, Completeness.kfac_liftSub]
  rcases Bool.eq_false_or_eq_true (u ⟨0, Finset.mem_univ 0⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨1, Finset.mem_univ 1⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨2, Finset.mem_univ 2⟩) with h2 | h2 <;>
  simp [kfac_univ, NA_k0, NA_k1, NA_k2, NB_k0, NB_k1, NB_k2, φ,
    Assignment.restrict, PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2,
    mul_comm, mul_left_comm]

/-- The joint distribution of model B is that of model A pushed forward along `φ`. -/
lemma full_map : mB.fullJoint = mA.fullJoint.map φ := by
  ext w
  rw [PMF.map_apply, tsum_eq_single (φ w)]
  · rw [if_pos (φ_invol w).symm, ← joint_eq (φ w), φ_invol]
  · intro u hu
    rw [if_neg]
    intro hw
    apply hu
    rw [hw, φ_invol]

/-- **Same observed distribution.** Models A and B agree on `{X, Y}`, since `φ` does not change
`X` or `Y`. -/
lemma obsEq : mA.marginal {1, 2} = mB.marginal {1, 2} := by
  unfold CausalModel.marginal
  rw [full_map, PMF.map_comp]
  congr 1
  funext u
  funext ⟨v, hv⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  simp [Function.comp, Assignment.restrict, φ, hv0]

/-- A set is ancestral in the graph of model B if it contains `X` or does not contain `Y`. -/
lemma ancB (S : Finset (Fin 3)) (h1 : (1 : Fin 3) ∈ S ∨ (2 : Fin 3) ∉ S) :
    ∀ v ∈ S, ∀ w, gB.edge w v → w ∈ S := by
  intro v hv w hw
  have hw' : w = 1 ∧ v = 2 := hw
  rcases hw' with ⟨rfl, rfl⟩
  rcases h1 with h | h
  · exact h
  · exact absurd hv h

/-- **Positivity.** The observed distribution of model A on `{X, Y}` is positive. -/
lemma posA : ∀ a, mA.marginal {1, 2} a ≠ 0 := by
  intro a
  rw [obsEq, show mB.marginal {1, 2} = NB.marginal {1, 2} from
    Completeness.marginal_eq_of_kfac mB NB (Completeness.kfac_liftSub gB_parents_subset NB) {1, 2}]
  have hS := ancB {1, 2} (Or.inl (by simp))
  rw [marginal_ancestral_apply NB {1, 2} hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_of_mem NB {1, 2} a v hv (DAG.parents_subset_of_closed hS v hv)]
  have hv' : v = 1 ∨ v = 2 := by simpa using hv
  rcases hv' with rfl | rfl
  · rw [NB_k1]
    simp [PMF.uniformOfFintype_apply]
  · rw [NB_k2]
    exact chan_ne_zero _ _

/-- In model A, `P_x(Y)` is the observed `P(Y)`: after the intervention `X` no longer
reaches `Y`. -/
lemma doA (x0 : Assignment (α := fun _ : Fin 3 => Bool) {1})
    (y0 : Assignment (α := fun _ : Fin 3 => Bool) {2}) :
    (doModel mA {1} x0).marginal {2} y0 = mB.marginal {2} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel mA {1} x0) (doModel NA {1} x0)
    (Completeness.kfac_doModel_liftSub gA_parents_subset NA {1} x0) {2}]
  have hanc : ∀ v ∈ ({0, 2} : Finset (Fin 3)), ∀ w, gA.edge w v → w ∈ ({0, 2} : Finset (Fin 3)) := by
    intro v _ w hw
    have hw' : (w = 0 ∧ v = 1) ∨ (w = 0 ∧ v = 2) := hw
    rcases hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  rw [Rule3.doModel_marginal_of_subset NA {1} x0 {0, 2} hanc (by decide) {2} (by decide) y0,
    ← Completeness.marginal_eq_of_kfac mA NA (Completeness.kfac_liftSub gA_parents_subset NA) {2},
    marginal_eq_of_subset obsEq (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide)]

/-- **The bow graph: `P(Y | do(X))` is not identifiable from `{X, Y}`.** -/
theorem bow_not_identifiable : ¬ Identifiable bowG (fun _ => Bool) {1, 2} {1} {2} := by
  intro h
  have hnp : ∀ u, ¬ gB.edge u 1 := by
    intro u hu
    have hu' : u = 1 ∧ (1 : Fin 3) = 2 := hu
    exact absurd hu'.2 (by decide)
  have hS21 := ancB ({2} ∪ {1}) (Or.inl (by simp))
  have key : ∀ x : Bool,
      chan x true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        mB.marginal {2} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro x
    let t : Assignment (α := fun _ : Fin 3 => Bool) ({2} ∪ {1}) :=
      fun v => if v.1 = 1 then x else true
    have hx : t.restrict (show ({1} : Finset (Fin 3)) ⊆ {2} ∪ {1} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => x := by
      funext ⟨v, hv⟩
      have : v = 1 := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hy : t.restrict (show ({2} : Finset (Fin 3)) ⊆ {2} ∪ {1} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = 2 := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have e := h mA mB obsEq posA t
    rw [hx, hy, doA, Completeness.marginal_eq_of_kfac (doModel mB {1} _) (doModel NB {1} _)
      (Completeness.kfac_doModel_liftSub gB_parents_subset NB {1} _) {2}] at e
    -- the first front-door step in model B
    have fd := Adjustment.frontdoor_step1 NB {1} {2} (by decide)
      (Completeness.dsep_isolated hnp {2} (by decide)) t
    rw [hx, hy, ← e] at fd
    -- the left-hand side: P(x, y) = P(x) · channel
    rw [marginal_ancestral_apply NB _ hS21 t, Finset.prod_union (show Disjoint ({2} : Finset (Fin 3)) {1} by decide),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_of_mem NB _ t 2 (by simp) (DAG.parents_subset_of_closed hS21 2 (by simp)),
      kfac_of_mem NB _ t 1 (by simp) (DAG.parents_subset_of_closed hS21 1 (by simp))] at fd
    -- P(x) in model B
    have hS1 := ancB {1} (Or.inr (by simp))
    rw [marginal_ancestral_apply NB {1} hS1, Finset.prod_singleton,
      kfac_of_mem NB {1} _ 1 (by simp) (DAG.parents_subset_of_closed hS1 1 (by simp))] at fd
    rw [NB_k2, NB_k1, NB_k1] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : chan true true = chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [chan_apply, chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact q_ne hc

end Bow
end Identification

#print axioms Identification.Bow.bow_not_identifiable

/-! ## The bow inside an arbitrary graph

If a latent `u` has edges to `x` and `y`, and `x → y`, then `P(y | do(x))` is not
identifiable from `O`, whatever the rest of the graph. All other nodes are independent
uniform bits, so the observed distribution stays positive. -/

namespace Identification
namespace BowEmbedded

open Bow

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The two ends of an edge are different. -/
lemma ne_of_edge {G : DAG V} {a b : V} (h : G.edge a b) : a ≠ b := by
  rintro rfl
  exact lt_irrefl _ (G.rank_strict_mono _ _ h)

/-- The graph with the single edge `a → b` (and the rank of `G`). -/
def g1 (G : DAG V) (a b : V) (hab : G.edge a b) : DAG V where
  edge s t := s = a ∧ t = b
  decEdge := fun s t => inferInstanceAs (Decidable (s = a ∧ t = b))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    exact G.rank_strict_mono _ _ hab

/-- The graph with the edges `u → x` and `u → y` (and the rank of `G`). -/
def g2 (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) : DAG V where
  edge s t := (s = u ∧ t = x) ∨ (s = u ∧ t = y)
  decEdge := fun s t => inferInstanceAs (Decidable ((s = u ∧ t = x) ∨ (s = u ∧ t = y)))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ huy

section
variable (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)

/-- `x` is a parent of `y` in `g1`. -/
lemma p1 : x ∈ (g1 G x y hxy).parents y := by simp [DAG.parents, g1]
/-- `u` is a parent of `x` in `g2`. -/
lemma p2x : u ∈ (g2 G u x y hux huy).parents x := by simp [DAG.parents, g2]
/-- `u` is a parent of `y` in `g2`. -/
lemma p2y : u ∈ (g2 G u x y hux huy).parents y := by simp [DAG.parents, g2]

/-- Model A: `u` uniform, `x` a noisy copy of `u`, `y = u`, the rest uniform. -/
noncomputable def NA : (g2 G u x y hux huy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = x then chan (pa ⟨u, by rw [hvx]; exact p2x G u x y hux huy⟩)
    else if hvy : v = y then PMF.pure (pa ⟨u, by rw [hvy]; exact p2y G u x y hux huy⟩)
    else PMF.uniformOfFintype Bool

/-- Model B: `u = 0`, `x` uniform, `y` a noisy copy of `x`, the rest uniform. -/
noncomputable def NB : (g1 G x y hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = y then chan (pa ⟨x, by rw [hvy]; exact p1 G x y hxy⟩)
    else if v = u then PMF.pure false
    else PMF.uniformOfFintype Bool

/-- The kernel of `x` in model A is the channel applied to `u`. -/
lemma NA_x (pa : {w // w ∈ (g2 G u x y hux huy).parents x} → Bool) :
    (NA G u x y hux huy).kernel x pa = chan (pa ⟨u, p2x G u x y hux huy⟩) := by
  simp [NA]

/-- The kernel of `y` in model A copies `u`. -/
lemma NA_y (hyx : y ≠ x) (pa : {w // w ∈ (g2 G u x y hux huy).parents y} → Bool) :
    (NA G u x y hux huy).kernel y pa = PMF.pure (pa ⟨u, p2y G u x y hux huy⟩) := by
  simp [NA, hyx]

/-- The kernel of any other node in model A is uniform. -/
lemma NA_o {v : V} (hvx : v ≠ x) (hvy : v ≠ y)
    (pa : {w // w ∈ (g2 G u x y hux huy).parents v} → Bool) :
    (NA G u x y hux huy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NA, hvx, hvy]

/-- The kernel of `y` in model B is the channel applied to `x`. -/
lemma NB_y (pa : {w // w ∈ (g1 G x y hxy).parents y} → Bool) :
    (NB G u x y hxy).kernel y pa = chan (pa ⟨x, p1 G x y hxy⟩) := by
  simp [NB]

/-- The kernel of `u` in model B is the constant `false`. -/
lemma NB_u (huy' : u ≠ y) (pa : {w // w ∈ (g1 G x y hxy).parents u} → Bool) :
    (NB G u x y hxy).kernel u pa = PMF.pure false := by
  simp [NB, huy']

/-- The kernel of any other node in model B is uniform. -/
lemma NB_o {v : V} (hvy : v ≠ y) (hvu : v ≠ u)
    (pa : {w // w ∈ (g1 G x y hxy).parents v} → Bool) :
    (NB G u x y hxy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NB, hvy, hvu]

/-- `g2` is a subgraph of `G`. -/
lemma g2_parents_subset : ∀ v, (g2 G u x y hux huy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.mem_parents] at hw ⊢
  have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
  rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hux
  · rw [h1, h2]; exact huy

/-- `g1` is a subgraph of `G`. -/
lemma g1_parents_subset : ∀ v, (g1 G x y hxy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.mem_parents] at hw ⊢
  have hw' : w = x ∧ v = y := hw
  rw [hw'.1, hw'.2]
  exact hxy

/-- Model A as a model on `G`. -/
noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (g2_parents_subset G u x y hux huy) (NA G u x y hux huy)
/-- Model B as a model on `G`. -/
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (g1_parents_subset G x y hxy) (NB G u x y hxy)

end

/-- The bijection of full assignments: it changes only `u`, to `u xor y`. -/
def φ (u y : V) (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 = u then xor (w ⟨u, Finset.mem_univ u⟩) (w ⟨y, Finset.mem_univ y⟩) else w v

/-- `φ u y` is an involution (as `y ≠ u`). -/
lemma φ_invol {u y : V} (hyu : y ≠ u)
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ u y (φ u y w) = w := by
  funext ⟨v, hv⟩
  by_cases h : v = u
  · subst h
    simp [φ, hyu, Bool.xor_assoc]
  · simp [φ, h]

section
variable (G : DAG V) (u x y : V) (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)

/-- Model B gives `φ u y w` the probability that model A gives `w`. -/
lemma joint_eq (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB G u x y hxy).fullJoint (φ u y w) = (mA G u x y hux huy).fullJoint w := by
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyu : y ≠ u := (ne_of_edge huy).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  have hux' : u ≠ x := ne_of_edge hux
  have huy' : u ≠ y := ne_of_edge huy
  have hxy' : x ≠ y := ne_of_edge hxy
  have hxU : x ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩
  have hyU : y ∈ (Finset.univ.erase u).erase x :=
    Finset.mem_erase.mpr ⟨hyx, Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, Completeness.kfac_liftSub]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase _ _ hxU, ← Finset.mul_prod_erase _ _ hxU,
    ← Finset.mul_prod_erase _ _ hyU, ← Finset.mul_prod_erase _ _ hyU]
  have hR : ∏ v ∈ ((Finset.univ.erase u).erase x).erase y,
        kfac (NB G u x y hxy) Finset.univ (φ u y w) v =
      ∏ v ∈ ((Finset.univ.erase u).erase x).erase y,
        kfac (NA G u x y hux huy) Finset.univ w v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    simp only [Finset.mem_erase] at hv
    rw [kfac_univ, kfac_univ, NB_o G u x y hxy hv.1 hv.2.2.1,
      NA_o G u x y hux huy hv.2.1 hv.1]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (w ⟨u, Finset.mem_univ u⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨x, Finset.mem_univ x⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨y, Finset.mem_univ y⟩) with h2 | h2 <;>
  simp [kfac_univ, NA_x, NA_y, NA_o, NB_y, NB_u, NB_o, φ, Assignment.restrict,
    PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, hxu, hyu, hyx,
    hux', huy', hxy', mul_comm, mul_left_comm, mul_assoc]

/-- The joint distribution of model B is that of model A pushed forward along `φ u y`. -/
lemma full_map : (mB G u x y hxy).fullJoint = (mA G u x y hux huy).fullJoint.map (φ u y) := by
  have hyu : y ≠ u := (ne_of_edge huy).symm
  ext w
  rw [PMF.map_apply, tsum_eq_single (φ u y w)]
  · rw [if_pos (φ_invol hyu w).symm, ← joint_eq G u x y hux huy hxy (φ u y w), φ_invol hyu]
  · intro w' hw'
    rw [if_neg]
    intro hw
    apply hw'
    rw [hw, φ_invol hyu]

/-- Models A and B agree on every `O` that does not contain `u`. -/
lemma obsEq (O : Finset V) (hu : u ∉ O) :
    (mA G u x y hux huy).marginal O = (mB G u x y hxy).marginal O := by
  unfold CausalModel.marginal
  rw [full_map G u x y hux huy hxy, PMF.map_comp]
  congr 1
  funext w
  funext ⟨v, hv⟩
  have hvu : v ≠ u := fun e => hu (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ, hvu]

/-- A set is ancestral in `g1` if it contains `x` or does not contain `y`. -/
lemma ancB (S : Finset V) (h : x ∈ S ∨ y ∉ S) :
    ∀ v ∈ S, ∀ w, (g1 G x y hxy).edge w v → w ∈ S := by
  intro v hv w hw
  have hw' : w = x ∧ v = y := hw
  rw [hw'.1]
  rcases h with h | h
  · exact h
  · rw [hw'.2] at hv
    exact absurd hv h

include hxy in
/-- The observed distribution of model A on `O` is positive when `x ∈ O` and `u ∉ O`. -/
lemma posA (O : Finset V) (hu : u ∉ O) (hx : x ∈ O) :
    ∀ a, (mA G u x y hux huy).marginal O a ≠ 0 := by
  intro a
  rw [obsEq G u x y hux huy hxy O hu, show (mB G u x y hxy).marginal O =
      (NB G u x y hxy).marginal O from
    Completeness.marginal_eq_of_kfac _ _
      (Completeness.kfac_liftSub (g1_parents_subset G x y hxy) (NB G u x y hxy)) O]
  have hS := ancB G x y hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_of_mem _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  by_cases hvy : v = y
  · subst hvy
    rw [NB_y]
    exact chan_ne_zero _ _
  · rw [NB_o G u x y hxy hvy (fun e => hu (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

/-- In model A, `P_x(y)` is the observed `P(y)` of model B: after the intervention `x` no longer
reaches `y`. -/
lemma doA (O : Finset V) (hu : u ∉ O) (hy : y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {x})
    (y0 : Assignment (α := fun _ : V => Bool) {y}) :
    (doModel (mA G u x y hux huy) {x} x0).marginal {y} y0 = (mB G u x y hxy).marginal {y} y0 := by
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  rw [Completeness.marginal_eq_of_kfac (doModel (mA G u x y hux huy) {x} x0)
    (doModel (NA G u x y hux huy) {x} x0)
    (Completeness.kfac_doModel_liftSub (g2_parents_subset G u x y hux huy)
      (NA G u x y hux huy) {x} x0) {y}]
  have hanc : ∀ v ∈ ({u, y} : Finset V), ∀ w, (g2 G u x y hux huy).edge w v →
      w ∈ ({u, y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
    rcases hw' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({u, y} : Finset V) {x} := by
    rw [Finset.disjoint_singleton_right]
    simp [hxu, hyx.symm]
  rw [Rule3.doModel_marginal_of_subset (NA G u x y hux huy) {x} x0 {u, y} hanc hdisj {y}
      (by simp) y0,
    ← Completeness.marginal_eq_of_kfac (mA G u x y hux huy) (NA G u x y hux huy)
      (Completeness.kfac_liftSub (g2_parents_subset G u x y hux huy) (NA G u x y hux huy)) {y},
    marginal_eq_of_subset (obsEq G u x y hux huy hxy O hu) (show ({y} : Finset V) ⊆ O by simpa using hy)]

end

/-- **The bow inside an arbitrary graph.** If `u` has edges to `x` and `y`, and `x → y`,
then `P(y | do(x))` is not identifiable from any `O` that contains `x` and `y` but not
`u`. -/
theorem bow_not_identifiable_general (G : DAG V) (O : Finset V) (u x y : V)
    (hux : G.edge u x) (huy : G.edge u y) (hxy : G.edge x y)
    (hu : u ∉ O) (hx : x ∈ O) (hy : y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y} := by
  intro h
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  have hnp : ∀ w, ¬ (g1 G x y hxy).edge w x := by
    intro w hw
    have hw' : w = x ∧ x = y := hw
    exact hyx hw'.2.symm
  have hS21 := ancB G x y hxy ({y} ∪ {x}) (Or.inl (by simp))
  have hS1 := ancB G x y hxy {x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        (mB G u x y hxy).marginal {y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({y} ∪ {x}) :=
      fun v => if v.1 = x then b else true
    have htx : t.restrict (show ({x} : Finset V) ⊆ {y} ∪ {x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({y} : Finset V) ⊆ {y} ∪ {x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h (mA G u x y hux huy) (mB G u x y hxy) (obsEq G u x y hux huy hxy O hu)
      (posA G u x y hux huy hxy O hu hx) t
    rw [htx, hty, doA G u x y hux huy hxy O hu hy,
      Completeness.marginal_eq_of_kfac (doModel (mB G u x y hxy) {x} _)
        (doModel (NB G u x y hxy) {x} _)
        (Completeness.kfac_doModel_liftSub (g1_parents_subset G x y hxy) (NB G u x y hxy)
          {x} _) {y}] at e
    have fd := Adjustment.frontdoor_step1 (NB G u x y hxy) {x} {y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({y} : Finset V) {x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_of_mem _ _ t y (by simp) (DAG.parents_subset_of_closed hS21 y (by simp)),
      kfac_of_mem _ _ t x (by simp) (DAG.parents_subset_of_closed hS21 x (by simp))] at fd
    rw [marginal_ancestral_apply _ {x} hS1, Finset.prod_singleton,
      kfac_of_mem _ {x} _ x (by simp) (DAG.parents_subset_of_closed hS1 x (by simp))] at fd
    rw [NB_y, NB_o G u x y hxy hyx.symm hxu, NB_o G u x y hxy hyx.symm hxu] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : chan true true = chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [chan_apply, chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact q_ne hc

end BowEmbedded
end Identification

#print axioms Identification.BowEmbedded.bow_not_identifiable_general
