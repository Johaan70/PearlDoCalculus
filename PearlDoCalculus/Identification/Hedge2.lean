import PearlDoCalculus.Identification.Bow

/-!
# The hedge with two latent variables is not identifiable

The graph has edges `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y`, `w → y` and `x → y`, with
`u₁`, `u₂` latent. We show that `P(y | do(x))` is not identifiable from the observed
nodes (`Identification.Hedge2.hedge2_not_identifiable`), whether or not `w` is observed.
If `u₁ = u₂` or `x = w`, the graph degenerates to the bow and the bow result is used.

Why it is needed: it is the smallest genuine hedge (`F = {x, w, y}`, `F' = {w, y}`), and
the model of the later hedge families generalizes it.

How the proof goes: two models with the same positive distribution on the observed nodes
and different `P(y | do(x))`. See the round description below for the two models and the
bijection that changes only latent nodes.

Main result: `Identification.Hedge2.hedge2_not_identifiable`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 6: hedge med to latente variabler

`x ← u₁ → w ← u₂ → y`, `w → y`, `x → y`, med `u₁` og `u₂` latente. Da er
`P(y | do(x))` ikke identifiserbar, også når `w` er observert. Det er et ekte
hedge-tilfelle: `F = {x, w, y}` og `F' = {w, y}`. Var ikke `w` forfar til `y`, ville
effekten vært identifiserbar (`P(y | x)`).

Modell A: `u₁, u₂` uniforme, `x` støyende kopi av `u₁`, `w = u₁ xor u₂`,
`y = w xor u₂` (altså `y = u₁`, upåvirket av `x`). Modell B: `u₁ = u₂ = 0`, `x` og
`w` uniforme, `y` støyende kopi av `x`. Fellesfordelingene er like etter
bijeksjonen `u₁ ↦ u₁ xor y`, `u₂ ↦ u₂ xor (w xor y)`, som bare endrer latente noder. -/

namespace Identification
namespace Hedge2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Hedge-konfigurasjonen inne i `G`. -/
structure Data (G : DAG V) where
  u1 : V
  u2 : V
  x : V
  w : V
  y : V
  h1x : G.edge u1 x
  h1w : G.edge u1 w
  h2w : G.edge u2 w
  h2y : G.edge u2 y
  hwy : G.edge w y
  hxy : G.edge x y
  h12 : u1 ≠ u2
  h2x : u2 ≠ x
  hxw : x ≠ w

namespace Data

variable {G : DAG V} (H : Data G)

lemma d1x : H.u1 ≠ H.x := BowGen.ne_of_edge H.h1x
lemma d1w : H.u1 ≠ H.w := BowGen.ne_of_edge H.h1w
lemma d2w : H.u2 ≠ H.w := BowGen.ne_of_edge H.h2w
lemma d2y : H.u2 ≠ H.y := BowGen.ne_of_edge H.h2y
lemma dwy : H.w ≠ H.y := BowGen.ne_of_edge H.hwy
lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy
lemma d1y : H.u1 ≠ H.y := by
  intro e
  have a := G.rank_strict_mono _ _ H.h1x
  have b := G.rank_strict_mono _ _ H.hxy
  rw [e] at a
  omega

/-- Grafen for modell A: `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y`, `w → y`. -/
def gA : DAG V where
  edge s t := (s = H.u1 ∧ t = H.x) ∨ (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨
    (s = H.u2 ∧ t = H.y) ∨ (s = H.w ∧ t = H.y)
  decEdge := fun s t => inferInstanceAs (Decidable ((s = H.u1 ∧ t = H.x) ∨
    (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.y) ∨
    (s = H.w ∧ t = H.y)))
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> apply G.rank_strict_mono <;>
      first | exact H.h1x | exact H.h1w | exact H.h2w | exact H.h2y | exact H.hwy

lemma pAx : H.u1 ∈ (gA H).parents H.x := by simp [DAG.parents, gA]
lemma pAw1 : H.u1 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAw2 : H.u2 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAy2 : H.u2 ∈ (gA H).parents H.y := by simp [DAG.parents, gA]
lemma pAyw : H.w ∈ (gA H).parents H.y := by simp [DAG.parents, gA]

/-- Modell A. -/
noncomputable def NA : (gA H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u1, by rw [hvx]; exact pAx H⟩)
    else if hvw : v = H.w then
      PMF.pure (xor (pa ⟨H.u1, by rw [hvw]; exact pAw1 H⟩) (pa ⟨H.u2, by rw [hvw]; exact pAw2 H⟩))
    else if hvy : v = H.y then
      PMF.pure (xor (pa ⟨H.w, by rw [hvy]; exact pAyw H⟩) (pa ⟨H.u2, by rw [hvy]; exact pAy2 H⟩))
    else PMF.uniformOfFintype Bool

/-- Modell B (på grafen med bare `x → y`). -/
noncomputable def NB : (BowGen.g1 G H.x H.y H.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then Bow.chan (pa ⟨H.x, by rw [hvy]; exact BowGen.p1 G H.x H.y H.hxy⟩)
    else if v = H.u1 ∨ v = H.u2 then PMF.pure false
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {v // v ∈ (gA H).parents H.x} → Bool) :
    (NA H).kernel H.x pa = Bow.chan (pa ⟨H.u1, pAx H⟩) := by
  simp [Data.NA]

lemma NA_w (pa : {v // v ∈ (gA H).parents H.w} → Bool) :
    (NA H).kernel H.w pa = PMF.pure (xor (pa ⟨H.u1, pAw1 H⟩) (pa ⟨H.u2, pAw2 H⟩)) := by
  simp [Data.NA, H.hxw.symm]

lemma NA_y (pa : {v // v ∈ (gA H).parents H.y} → Bool) :
    (NA H).kernel H.y pa = PMF.pure (xor (pa ⟨H.w, pAyw H⟩) (pa ⟨H.u2, pAy2 H⟩)) := by
  simp [Data.NA, H.dxy.symm, H.dwy.symm]

lemma NA_o {v : V} (hvx : v ≠ H.x) (hvw : v ≠ H.w) (hvy : v ≠ H.y)
    (pa : {w // w ∈ (gA H).parents v} → Bool) :
    (NA H).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [Data.NA, hvx, hvw, hvy]

lemma NB_y (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.y} → Bool) :
    (NB H).kernel H.y pa = Bow.chan (pa ⟨H.x, BowGen.p1 G H.x H.y H.hxy⟩) := by
  simp [Data.NB]

lemma NB_u1 (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.u1} → Bool) :
    (NB H).kernel H.u1 pa = PMF.pure false := by
  simp [Data.NB, H.d1y]

lemma NB_u2 (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.u2} → Bool) :
    (NB H).kernel H.u2 pa = PMF.pure false := by
  simp [Data.NB, H.d2y]

lemma NB_o {v : V} (hvy : v ≠ H.y) (hv1 : v ≠ H.u1) (hv2 : v ≠ H.u2)
    (pa : {w // w ∈ (BowGen.g1 G H.x H.y H.hxy).parents v} → Bool) :
    (NB H).kernel v pa = PMF.uniformOfFintype Bool := by
  simp [Data.NB, hvy, hv1, hv2]

lemma hsA : ∀ v, (gA H).parents v ⊆ G.parents v := by
  intro v w hw
  simp only [DAG.mem_parents] at hw ⊢
  have hw' : (w = H.u1 ∧ v = H.x) ∨ (w = H.u1 ∧ v = H.w) ∨ (w = H.u2 ∧ v = H.w) ∨
      (w = H.u2 ∧ v = H.y) ∨ (w = H.w ∧ v = H.y) := hw
  rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;>
    first | exact H.h1x | exact H.h1w | exact H.h2w | exact H.h2y | exact H.hwy

noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (hsA H) (NA H)
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowGen.hsB G H.x H.y H.hxy) (NB H)

/-- Bijeksjonen: endrer bare `u₁` og `u₂`. -/
def φ2 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if v.1 = H.u1 then xor (s ⟨H.u1, Finset.mem_univ _⟩) (s ⟨H.y, Finset.mem_univ _⟩)
    else if v.1 = H.u2 then
      xor (s ⟨H.u2, Finset.mem_univ _⟩)
        (xor (s ⟨H.w, Finset.mem_univ _⟩) (s ⟨H.y, Finset.mem_univ _⟩))
    else s v

lemma φ2_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ2 H (φ2 H s) = s := by
  funext ⟨v, hv⟩
  by_cases h1 : v = H.u1
  · subst h1
    rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with a | a <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with b | b <;>
    simp [φ2, H.d1y.symm, H.d2y.symm, a, b]
  · by_cases h2 : v = H.u2
    · subst h2
      rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with a | a <;>
      rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with b | b <;>
      rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with c | c <;>
      simp [φ2, H.h12.symm, H.d1y.symm, H.d2y.symm, H.d1w.symm, H.d2w.symm, a, b, c]
    · simp [φ2, h1, h2]

lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB H).fullJoint (φ2 H s) = (mA H).fullJoint s := by
  have m2 : H.u2 ∈ Finset.univ.erase H.u1 := by simp [H.h12.symm]
  have mx : H.x ∈ (Finset.univ.erase H.u1).erase H.u2 := by
    simp [H.d1x.symm, H.h2x.symm]
  have mw : H.w ∈ ((Finset.univ.erase H.u1).erase H.u2).erase H.x := by
    simp [H.d1w.symm, H.d2w.symm, H.hxw.symm]
  have my : H.y ∈ (((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w := by
    simp [H.d1y.symm, H.d2y.symm, H.dxy.symm, H.dwy.symm]
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [Data.mA, Data.mB, BowGen.kfac_liftG]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase _ _ m2, ← Finset.mul_prod_erase _ _ m2,
    ← Finset.mul_prod_erase _ _ mx, ← Finset.mul_prod_erase _ _ mx,
    ← Finset.mul_prod_erase _ _ mw, ← Finset.mul_prod_erase _ _ mw,
    ← Finset.mul_prod_erase _ _ my, ← Finset.mul_prod_erase _ _ my]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NB H) Finset.univ (φ2 H s) v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    simp only [Finset.mem_erase] at hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o H hv.1 hv.2.2.2.2.1 hv.2.2.2.1,
      NA_o H hv.2.2.1 hv.2.1 hv.1]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NB_y, Data.NB_u1, Data.NB_u2, Data.NA_o, Data.NB_o, φ2, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.dwy, H.dwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma full_map : (mB H).fullJoint = (mA H).fullJoint.map (φ2 H) := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (φ2 H s)]
  · rw [if_pos (φ2_invol H s).symm, ← joint_eq H (φ2 H s), φ2_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, φ2_invol]

lemma obsEq (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) :
    (mA H).marginal O = (mB H).marginal O := by
  unfold CausalModel.marginal
  rw [full_map H, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv1 : v ≠ H.u1 := fun e => hu1 (e ▸ hv)
  have hv2 : v ≠ H.u2 := fun e => hu2 (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ2, hv1, hv2]

lemma posA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hx : H.x ∈ O) :
    ∀ a, (mA H).marginal O a ≠ 0 := by
  intro a
  rw [obsEq H O hu1 hu2, show (mB H).marginal O = (NB H).marginal O from
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_liftG (BowGen.hsB G H.x H.y H.hxy) (NB H)) O]
  have hS := BowGen.ancB G H.x H.y H.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  by_cases hvy : v = H.y
  · subst hvy
    rw [NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [NB_o H hvy (fun e => hu1 (e ▸ hv)) (fun e => hu2 (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hy : H.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y}) :
    (doModel (mA H) {H.x} x0).marginal {H.y} y0 = (mB H).marginal {H.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel (mA H) {H.x} x0)
    (doModel (NA H) {H.x} x0)
    (BowGen.kfac_lift_doG (hsA H) (NA H) {H.x} x0) {H.y}]
  have hanc : ∀ v ∈ ({H.u1, H.u2, H.w, H.y} : Finset V), ∀ w, (gA H).edge w v →
      w ∈ ({H.u1, H.u2, H.w, H.y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = H.u1 ∧ v = H.x) ∨ (w = H.u1 ∧ v = H.w) ∨ (w = H.u2 ∧ v = H.w) ∨
        (w = H.u2 ∧ v = H.y) ∨ (w = H.w ∧ v = H.y) := hw
    rcases hw' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({H.u1, H.u2, H.w, H.y} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.d1x.symm, H.h2x.symm, H.hxw, H.dxy]
  rw [Rule3.doModel_marginal_of_sub (NA H) {H.x} x0 {H.u1, H.u2, H.w, H.y} hanc hdisj {H.y}
      (by simp) y0,
    ← Completeness.marginal_eq_of_kfac (mA H) (NA H) (BowGen.kfac_liftG (hsA H) (NA H)) {H.y},
    marginal_eq_of_sub (obsEq H O hu1 hu2) (show ({H.y} : Finset V) ⊆ O by simpa using hy)]

theorem not_ident (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} := by
  intro h
  have hxu1 : H.x ≠ H.u1 := H.d1x.symm
  have hxu2 : H.x ≠ H.u2 := H.h2x.symm
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G H.x H.y H.hxy).edge w H.x := by
    intro w hw
    have hw' : w = H.x ∧ H.x = H.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G H.x H.y H.hxy ({H.y} ∪ {H.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G H.x H.y H.hxy {H.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        (mB H).marginal {H.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else true
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({H.y} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = H.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h (mA H) (mB H) (obsEq H O hu1 hu2) (posA H O hu1 hu2 hx) t
    rw [htx, hty, doA H O hu1 hu2 hy,
      Completeness.marginal_eq_of_kfac (doModel (mB H) {H.x} _)
        (doModel (NB H) {H.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G H.x H.y H.hxy) (NB H) {H.x} _) {H.y}] at e
    have fd := Adjustment.frontdoor_step1 (NB H) {H.x} {H.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {H.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({H.y} : Finset V) {H.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t H.y (by simp) (DAG.parents_subset_of_closed hS21 H.y (by simp)),
      BowGen.kfac_eqG _ _ t H.x (by simp) (DAG.parents_subset_of_closed hS21 H.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {H.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {H.x} _ H.x (by simp) (DAG.parents_subset_of_closed hS1 H.x (by simp))] at fd
    rw [NB_y, NB_o H hyx.symm hxu1 hxu2, NB_o H hyx.symm hxu1 hxu2] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end Data

/-- **Hedge med to latente variabler.** Har `G` kantene `u₁ → x`, `u₁ → w`,
`u₂ → w`, `u₂ → y`, `w → y` og `x → y`, er `u₁, u₂` latente og `x, y` observert, så
er `P(y | do(x))` ikke identifiserbar fra `O`, enten `w` er observert eller ikke.
Faller `u₁` og `u₂` sammen, eller `x` og `w`, er det buen. -/
theorem hedge2_not_identifiable (G : DAG V) (O : Finset V) (u1 u2 x w y : V)
    (h1x : G.edge u1 x) (h1w : G.edge u1 w) (h2w : G.edge u2 w) (h2y : G.edge u2 y)
    (hwy : G.edge w y) (hxy : G.edge x y)
    (hu1 : u1 ∉ O) (hu2 : u2 ∉ O) (hx : x ∈ O) (hy : y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y} := by
  by_cases h12 : u1 = u2
  · subst h12
    exact BowGen.bow_not_identifiable_general G O _ _ _ h1x h2y hxy hu1 hx hy
  by_cases hxw : x = w
  · subst hxw
    exact BowGen.bow_not_identifiable_general G O _ _ _ h2w h2y hxy hu2 hx hy
  have h2x : u2 ≠ x := fun e => hu2 (e ▸ hx)
  exact Data.not_ident ⟨u1, u2, x, w, y, h1x, h1w, h2w, h2y, hwy, hxy, h12, h2x, hxw⟩
    O hu1 hu2 hx hy

end Hedge2
end Identification

#print axioms Identification.Hedge2.hedge2_not_identifiable
