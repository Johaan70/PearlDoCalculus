import PearlDoCalculus.Identification.Basic

/-!
# The bow graph is not identifiable

The bow graph has a latent `u` with edges `u → x`, `u → y` and `x → y`. We show that
`P(y | do(x))` is not identifiable from the observed nodes `{x, y}`, first in the bow
graph itself (`Identification.Bow.bow_not_identifiable`) and then inside any graph that
contains such a bow (`Identification.BowGen.bow_not_identifiable_general`).

Why it is needed: the channel `Bow.chan` and the kernel-lifting lemmas
`BowGen.kfac_lift*` are used by every later family of hedge counter-models.

How the proof goes: two models give the same positive distribution on `{x, y}` but
different `P(y | do(x))`. In model A the latent `u` is uniform, `x` is a noisy copy of
`u` and `y = u`. In model B `u` is fixed, `x` is uniform and `y` is a noisy copy of `x`.
The joint distributions agree after a bijection that changes only `u`. In the general
case all other nodes are independent uniform bits.

Main results:

* `Identification.Bow.bow_not_identifiable`
* `Identification.BowGen.bow_not_identifiable_general`
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical
open scoped ENNReal

/-! ## Runde 3: bue-grafen er ikke identifiserbar

`U = 0` (latent), `X = 1`, `Y = 2`, med `U → X`, `U → Y`, `X → Y`. To modeller gir
samme positive fordeling på `{X, Y}`, men ulik `P(Y | do(X))`.

* Modell A: `U` uniform, `X` en støyende kopi av `U`, `Y = U` (overser `X`).
* Modell B: `U = 0` fast, `X` uniform, `Y` en støyende kopi av `X`.

Fellesfordelingene er like etter en bijeksjon som bare endrer `U`. I A er
`P_x(Y)` lik for begge `x` (B2), i B er `P(x, y) = P_x(y) · P(x)` (FD1), og
kanalen skiller `x`: `3/4 ≠ 1/4`. -/


namespace Identification
namespace Bow

/-- Bue-grafen. -/
def bowG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v =>
    inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Grafen for modell A: `U → X`, `U → Y`. -/
def gA : DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Grafen for modell B: `X → Y`. -/
def gB : DAG (Fin 3) where
  edge u v := u = 1 ∧ v = 2
  decEdge := fun u v => inferInstanceAs (Decidable (u = 1 ∧ v = 2))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩
    decide

lemma pA1 : (0 : Fin 3) ∈ gA.parents 1 := by simp [DAG.parents, gA]
lemma pA2 : (0 : Fin 3) ∈ gA.parents 2 := by simp [DAG.parents, gA]
lemma pB2 : (1 : Fin 3) ∈ gB.parents 2 := by simp [DAG.parents, gB]

lemma q_sum : (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

lemma q_ne : (3 / 4 : ℝ≥0∞) ≠ 1 / 4 := by
  intro h
  have h2 := congrArg ENNReal.toReal h
  norm_num [ENNReal.toReal_div] at h2

lemma q_pos3 : (3 / 4 : ℝ≥0∞) ≠ 0 := by
  simp

lemma q_pos1 : (1 / 4 : ℝ≥0∞) ≠ 0 := by
  simp

/-- Støyende kanal: `c = b` med sannsynlighet 3/4. -/
noncomputable def chan (b : Bool) : PMF Bool :=
  PMF.ofFintype (fun c => if c = b then 3 / 4 else 1 / 4) (by
    rw [Fintype.sum_bool]
    cases b
    · rw [if_neg (show ¬ (true = false) by decide), if_pos (show false = false from rfl),
        add_comm]
      exact q_sum
    · rw [if_pos (show true = true from rfl), if_neg (show ¬ (false = true) by decide)]
      exact q_sum)

lemma chan_apply (b c : Bool) : chan b c = if c = b then 3 / 4 else 1 / 4 :=
  PMF.ofFintype_apply _ _

lemma chan_ne_zero (b c : Bool) : chan b c ≠ 0 := by
  rw [chan_apply]
  split_ifs
  · exact q_pos3
  · exact q_pos1

/-- Modell A: `U` uniform, `X` støyende kopi av `U`, `Y = U`. -/
noncomputable def NA : gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h1 : v = 1 then chan (pa ⟨0, by rw [h1]; exact pA1⟩)
    else if h2 : v = 2 then PMF.pure (pa ⟨0, by rw [h2]; exact pA2⟩)
    else PMF.uniformOfFintype Bool

/-- Modell B: `U = 0`, `X` uniform, `Y` støyende kopi av `X`. -/
noncomputable def NB : gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h2 : v = 2 then chan (pa ⟨1, by rw [h2]; exact pB2⟩)
    else if v = 1 then PMF.uniformOfFintype Bool
    else PMF.pure false

lemma NA_k0 (pa : {u // u ∈ gA.parents 0} → Bool) : NA.kernel 0 pa = PMF.uniformOfFintype Bool := by
  rfl
lemma NA_k1 (pa : {u // u ∈ gA.parents 1} → Bool) : NA.kernel 1 pa = chan (pa ⟨0, pA1⟩) := by
  rfl
lemma NA_k2 (pa : {u // u ∈ gA.parents 2} → Bool) : NA.kernel 2 pa = PMF.pure (pa ⟨0, pA2⟩) := by
  rfl
lemma NB_k0 (pa : {u // u ∈ gB.parents 0} → Bool) : NB.kernel 0 pa = PMF.pure false := by
  rfl
lemma NB_k1 (pa : {u // u ∈ gB.parents 1} → Bool) : NB.kernel 1 pa = PMF.uniformOfFintype Bool := by
  rfl
lemma NB_k2 (pa : {u // u ∈ gB.parents 2} → Bool) : NB.kernel 2 pa = chan (pa ⟨1, pB2⟩) := by
  rfl

lemma hsA : ∀ v, gA.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.mem_parents] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) := hu
  tauto

lemma hsB : ∀ v, gB.parents v ⊆ bowG.parents v := by
  intro v u hu
  simp only [DAG.mem_parents] at hu ⊢
  show (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  have hu' : u = 1 ∧ v = 2 := hu
  tauto

noncomputable def mA : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub hsA NA
noncomputable def mB : bowG.CausalModel (fun _ => Bool) := Completeness.liftSub hsB NB

lemma kfac_lift {G H : DAG (Fin 3)} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool))
    (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) (v : Fin 3) :
    kfac (Completeness.liftSub hsub N) Finset.univ u v = kfac N Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_do {G H : DAG (Fin 3)} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool)) (X : Finset (Fin 3))
    (x : Assignment (α := fun _ : Fin 3 => Bool) X)
    (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) (v : Fin 3) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ u v =
      kfac (doModel N X x) Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

/-- Bijeksjonen: endrer bare `U`, til `U xor Y`. -/
def φ (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3)) :=
  fun v => if v.1 = 0 then xor (u ⟨0, Finset.mem_univ 0⟩) (u ⟨2, Finset.mem_univ 2⟩) else u v

lemma φ_invol (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    φ (φ u) = u := by
  funext ⟨v, hv⟩
  by_cases h : v = 0
  · subst h
    simp [φ, Bool.xor_assoc]
  · simp [φ, h]

lemma joint_eq (u : Assignment (α := fun _ : Fin 3 => Bool) (Finset.univ : Finset (Fin 3))) :
    mB.fullJoint (φ u) = mA.fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [mA, mB, kfac_lift]
  rcases Bool.eq_false_or_eq_true (u ⟨0, Finset.mem_univ 0⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨1, Finset.mem_univ 1⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (u ⟨2, Finset.mem_univ 2⟩) with h2 | h2 <;>
  simp [DoAudit.kfac_univ, NA_k0, NA_k1, NA_k2, NB_k0, NB_k1, NB_k2, φ,
    Assignment.restrict, PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2,
    mul_comm, mul_left_comm]

lemma full_map : mB.fullJoint = mA.fullJoint.map φ := by
  ext w
  rw [PMF.map_apply, tsum_eq_single (φ w)]
  · rw [if_pos (φ_invol w).symm, ← joint_eq (φ w), φ_invol]
  · intro u hu
    rw [if_neg]
    intro hw
    apply hu
    rw [hw, φ_invol]

/-- **Samme observerte fordeling.** -/
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

lemma kfac_eq {G : DAG (Fin 3)} (M : G.CausalModel (fun _ => Bool)) (S : Finset (Fin 3))
    (a : Assignment (α := fun _ : Fin 3 => Bool) S) (v : Fin 3) (hv : v ∈ S)
    (hpa : G.parents v ⊆ S) :
    kfac M S a v = M.kernel v (a.restrict hpa) (a ⟨v, hv⟩) := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩]

lemma ancB (S : Finset (Fin 3)) (h1 : (1 : Fin 3) ∈ S ∨ (2 : Fin 3) ∉ S) :
    ∀ v ∈ S, ∀ w, gB.edge w v → w ∈ S := by
  intro v hv w hw
  have hw' : w = 1 ∧ v = 2 := hw
  rcases hw' with ⟨rfl, rfl⟩
  rcases h1 with h | h
  · exact h
  · exact absurd hv h

/-- **Positivitet.** -/
lemma posA : ∀ a, mA.marginal {1, 2} a ≠ 0 := by
  intro a
  rw [obsEq, show mB.marginal {1, 2} = NB.marginal {1, 2} from
    Completeness.marginal_eq_of_kfac mB NB (kfac_lift hsB NB) {1, 2}]
  have hS := ancB {1, 2} (Or.inl (by simp))
  rw [marginal_ancestral_apply NB {1, 2} hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_eq NB {1, 2} a v hv (DAG.parents_subset_of_closed hS v hv)]
  have hv' : v = 1 ∨ v = 2 := by simpa using hv
  rcases hv' with rfl | rfl
  · rw [NB_k1]
    simp [PMF.uniformOfFintype_apply]
  · rw [NB_k2]
    exact chan_ne_zero _ _

/-- B2 i modell A: `P_x(Y)` er den observerte `P(Y)`. -/
lemma doA (x0 : Assignment (α := fun _ : Fin 3 => Bool) {1})
    (y0 : Assignment (α := fun _ : Fin 3 => Bool) {2}) :
    (doModel mA {1} x0).marginal {2} y0 = mB.marginal {2} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel mA {1} x0) (doModel NA {1} x0)
    (kfac_lift_do hsA NA {1} x0) {2}]
  have hanc : ∀ v ∈ ({0, 2} : Finset (Fin 3)), ∀ w, gA.edge w v → w ∈ ({0, 2} : Finset (Fin 3)) := by
    intro v _ w hw
    have hw' : (w = 0 ∧ v = 1) ∨ (w = 0 ∧ v = 2) := hw
    rcases hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  rw [Rule3.doModel_marginal_of_sub NA {1} x0 {0, 2} hanc (by decide) {2} (by decide) y0,
    ← Completeness.marginal_eq_of_kfac mA NA (kfac_lift hsA NA) {2},
    marginal_eq_of_subset obsEq (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide)]

/-- **Bue-grafen: `P(Y | do(X))` er ikke identifiserbar fra `{X, Y}`.** -/
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
      (kfac_lift_do hsB NB {1} _) {2}] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 NB {1} {2} (by decide)
      (Completeness.dsep_isolated hnp {2} (by decide)) t
    rw [hx, hy, ← e] at fd
    -- venstresiden: P(x, y) = P(x) · kanal
    rw [marginal_ancestral_apply NB _ hS21 t, Finset.prod_union (show Disjoint ({2} : Finset (Fin 3)) {1} by decide),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_eq NB _ t 2 (by simp) (DAG.parents_subset_of_closed hS21 2 (by simp)),
      kfac_eq NB _ t 1 (by simp) (DAG.parents_subset_of_closed hS21 1 (by simp))] at fd
    -- P(x) i modell B
    have hS1 := ancB {1} (Or.inr (by simp))
    rw [marginal_ancestral_apply NB {1} hS1, Finset.prod_singleton,
      kfac_eq NB {1} _ 1 (by simp) (DAG.parents_subset_of_closed hS1 1 (by simp))] at fd
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

/-! ## Runde 4: bue-grafen inne i en vilkårlig graf

Har en latent `u` piler til `x` og `y`, og `x → y`, er `P(y | do(x))` ikke
identifiserbar fra `O`, uansett resten av grafen. Alle andre noder er uavhengige
uniforme biter, så den observerte fordelingen forblir positiv. -/

namespace Identification
namespace BowGen

open Bow

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma ne_of_edge {G : DAG V} {a b : V} (h : G.edge a b) : a ≠ b := by
  rintro rfl
  exact lt_irrefl _ (G.rank_strict_mono _ _ h)

/-- Grafen med én kant `a → b`. -/
def g1 (G : DAG V) (a b : V) (hab : G.edge a b) : DAG V where
  edge s t := s = a ∧ t = b
  decEdge := fun s t => inferInstanceAs (Decidable (s = a ∧ t = b))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    exact G.rank_strict_mono _ _ hab

/-- Grafen med kantene `u → x` og `u → y`. -/
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

lemma p1 : x ∈ (g1 G x y hxy).parents y := by simp [DAG.parents, g1]
lemma p2x : u ∈ (g2 G u x y hux huy).parents x := by simp [DAG.parents, g2]
lemma p2y : u ∈ (g2 G u x y hux huy).parents y := by simp [DAG.parents, g2]

/-- Modell A: `u` uniform, `x` støyende kopi av `u`, `y = u`, resten uniform. -/
noncomputable def NA : (g2 G u x y hux huy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = x then chan (pa ⟨u, by rw [hvx]; exact p2x G u x y hux huy⟩)
    else if hvy : v = y then PMF.pure (pa ⟨u, by rw [hvy]; exact p2y G u x y hux huy⟩)
    else PMF.uniformOfFintype Bool

/-- Modell B: `u = 0`, `x` uniform, `y` støyende kopi av `x`, resten uniform. -/
noncomputable def NB : (g1 G x y hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = y then chan (pa ⟨x, by rw [hvy]; exact p1 G x y hxy⟩)
    else if v = u then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {w // w ∈ (g2 G u x y hux huy).parents x} → Bool) :
    (NA G u x y hux huy).kernel x pa = chan (pa ⟨u, p2x G u x y hux huy⟩) := by
  simp [NA]

lemma NA_y (hyx : y ≠ x) (pa : {w // w ∈ (g2 G u x y hux huy).parents y} → Bool) :
    (NA G u x y hux huy).kernel y pa = PMF.pure (pa ⟨u, p2y G u x y hux huy⟩) := by
  simp [NA, hyx]

lemma NA_o {v : V} (hvx : v ≠ x) (hvy : v ≠ y)
    (pa : {w // w ∈ (g2 G u x y hux huy).parents v} → Bool) :
    (NA G u x y hux huy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NA, hvx, hvy]

lemma NB_y (pa : {w // w ∈ (g1 G x y hxy).parents y} → Bool) :
    (NB G u x y hxy).kernel y pa = chan (pa ⟨x, p1 G x y hxy⟩) := by
  simp [NB]

lemma NB_u (huy' : u ≠ y) (pa : {w // w ∈ (g1 G x y hxy).parents u} → Bool) :
    (NB G u x y hxy).kernel u pa = PMF.pure false := by
  simp [NB, huy']

lemma NB_o {v : V} (hvy : v ≠ y) (hvu : v ≠ u)
    (pa : {w // w ∈ (g1 G x y hxy).parents v} → Bool) :
    (NB G u x y hxy).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [NB, hvy, hvu]

lemma hsA : ∀ v, (g2 G u x y hux huy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.mem_parents] at hw ⊢
  have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
  rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hux
  · rw [h1, h2]; exact huy

lemma hsB : ∀ v, (g1 G x y hxy).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.mem_parents] at hw ⊢
  have hw' : w = x ∧ v = y := hw
  rw [hw'.1, hw'.2]
  exact hxy

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsA G u x y hux huy) (NA G u x y hux huy)
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsB G x y hxy) (NB G u x y hxy)

end

lemma kfac_liftG {G H : DAG V} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool))
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) :
    kfac (Completeness.liftSub hsub N) Finset.univ w v = kfac N Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_doG {G H : DAG V} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel (fun _ => Bool)) (X : Finset V)
    (x : Assignment (α := fun _ : V => Bool) X)
    (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ w v =
      kfac (doModel N X x) Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

lemma kfac_eqG {G : DAG V} (M : G.CausalModel (fun _ => Bool)) (S : Finset V)
    (a : Assignment (α := fun _ : V => Bool) S) (v : V) (hv : v ∈ S)
    (hpa : G.parents v ⊆ S) :
    kfac M S a v = M.kernel v (a.restrict hpa) (a ⟨v, hv⟩) := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩]

/-- Bijeksjonen: endrer bare `u`, til `u xor y`. -/
def φ (u y : V) (w : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 = u then xor (w ⟨u, Finset.mem_univ u⟩) (w ⟨y, Finset.mem_univ y⟩) else w v

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
  simp only [mA, mB, kfac_liftG]
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
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o G u x y hxy hv.1 hv.2.2.1,
      NA_o G u x y hux huy hv.2.1 hv.1]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (w ⟨u, Finset.mem_univ u⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨x, Finset.mem_univ x⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (w ⟨y, Finset.mem_univ y⟩) with h2 | h2 <;>
  simp [DoAudit.kfac_univ, NA_x, NA_y, NA_o, NB_y, NB_u, NB_o, φ, Assignment.restrict,
    PMF.pure_apply, chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, hxu, hyu, hyx,
    hux', huy', hxy', mul_comm, mul_left_comm, mul_assoc]

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

lemma obsEq (O : Finset V) (hu : u ∉ O) :
    (mA G u x y hux huy).marginal O = (mB G u x y hxy).marginal O := by
  unfold CausalModel.marginal
  rw [full_map G u x y hux huy hxy, PMF.map_comp]
  congr 1
  funext w
  funext ⟨v, hv⟩
  have hvu : v ≠ u := fun e => hu (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ, hvu]

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
lemma posA (O : Finset V) (hu : u ∉ O) (hx : x ∈ O) :
    ∀ a, (mA G u x y hux huy).marginal O a ≠ 0 := by
  intro a
  rw [obsEq G u x y hux huy hxy O hu, show (mB G u x y hxy).marginal O =
      (NB G u x y hxy).marginal O from
    Completeness.marginal_eq_of_kfac _ _ (kfac_liftG (hsB G x y hxy) (NB G u x y hxy)) O]
  have hS := ancB G x y hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_eqG _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  by_cases hvy : v = y
  · subst hvy
    rw [NB_y]
    exact chan_ne_zero _ _
  · rw [NB_o G u x y hxy hvy (fun e => hu (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu : u ∉ O) (hy : y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {x})
    (y0 : Assignment (α := fun _ : V => Bool) {y}) :
    (doModel (mA G u x y hux huy) {x} x0).marginal {y} y0 = (mB G u x y hxy).marginal {y} y0 := by
  have hxu : x ≠ u := (ne_of_edge hux).symm
  have hyx : y ≠ x := (ne_of_edge hxy).symm
  rw [Completeness.marginal_eq_of_kfac (doModel (mA G u x y hux huy) {x} x0)
    (doModel (NA G u x y hux huy) {x} x0)
    (kfac_lift_doG (hsA G u x y hux huy) (NA G u x y hux huy) {x} x0) {y}]
  have hanc : ∀ v ∈ ({u, y} : Finset V), ∀ w, (g2 G u x y hux huy).edge w v →
      w ∈ ({u, y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = u ∧ v = x) ∨ (w = u ∧ v = y) := hw
    rcases hw' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({u, y} : Finset V) {x} := by
    rw [Finset.disjoint_singleton_right]
    simp [hxu, hyx.symm]
  rw [Rule3.doModel_marginal_of_sub (NA G u x y hux huy) {x} x0 {u, y} hanc hdisj {y}
      (by simp) y0,
    ← Completeness.marginal_eq_of_kfac (mA G u x y hux huy) (NA G u x y hux huy)
      (kfac_liftG (hsA G u x y hux huy) (NA G u x y hux huy)) {y},
    marginal_eq_of_subset (obsEq G u x y hux huy hxy O hu) (show ({y} : Finset V) ⊆ O by simpa using hy)]

end

/-- **Bue-grafen i en vilkårlig graf.** Har en latent `u` piler til `x` og `y`, og
`x → y`, er `P(y | do(x))` ikke identifiserbar fra noen `O` som inneholder `x`
og `y`, men ikke `u`. -/
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
        (kfac_lift_doG (hsB G x y hxy) (NB G u x y hxy) {x} _) {y}] at e
    have fd := Adjustment.frontdoor_step1 (NB G u x y hxy) {x} {y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({y} : Finset V) {x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_eqG _ _ t y (by simp) (DAG.parents_subset_of_closed hS21 y (by simp)),
      kfac_eqG _ _ t x (by simp) (DAG.parents_subset_of_closed hS21 x (by simp))] at fd
    rw [marginal_ancestral_apply _ {x} hS1, Finset.prod_singleton,
      kfac_eqG _ {x} _ x (by simp) (DAG.parents_subset_of_closed hS1 x (by simp))] at fd
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

end BowGen
end Identification

#print axioms Identification.BowGen.bow_not_identifiable_general
