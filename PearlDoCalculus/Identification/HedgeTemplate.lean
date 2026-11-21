import PearlDoCalculus.Identification.HedgeChain
import PearlDoCalculus.Util.ZMod2

/-!
# A template for hedge counter-models, and latent paths with a tree to `y`

`HedgeTemplate` collects the few properties that the hedge-chain proof of
`Identification/HedgeChain` uses, so that `HedgeTemplate.not_identifiable` gives
non-identifiability for every configuration with these properties.
`PathTree.not_identifiable` applies the template to a hedge along a latent path
with an arbitrary directed tree towards `y`.

Why it is needed: `Identification/LatentTree` proves its theorem by building a `HedgeTemplate`
(`LatentTree.toHedgeTemplate`), so the template saves repeating the model construction there.
The root-path families (`RootPathModels`, `RootPath`) need a third model and do not fit
the template; they follow its plan by hand. `HedgeTemplate.not_identifiable` is used only by
`LatentTree`, and `PathTree.not_identifiable` by no other file; both are special cases of
the hedge criterion (`Hedge.PM.hedge_not_ident`).

How the proof goes: as for hedge chains. Model A computes `x` as a noisy copy of a
function `fx` of its parents and every `w_i` and `y` as functions `fw i`, `fy` of their
parents; model B has only `x → y`, with `y` a noisy copy of `x` and the latent `u`s fixed
to `false`. The bijection `u_j ↦ u_j xor off_j(w, y)` carries one joint distribution to
the other, provided the equations of model A are equivalent to `u_j = off_j(w, y)` for
every `j` (the field `key`) and then force `fx = y` (the field `hfx`). For the path with a
tree, model A is the parity model in `ZMod 2` (with `ofBool`, `toBool` from `Util/ZMod2`):
`off_j` is a prefix sum along the path, and `key` holds because every `w_j` is the child of
exactly one node of the tree, so the contributions of the tree cancel (`sum_zero`).

Main results: `Identification.HedgeTemplate.not_identifiable`,
`Identification.PathTree.not_identifiable`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## A general template for hedge counter-models

The proofs for the chain use only a few properties of model A: `x` is a noisy copy of
`u₀`, every `w_i` and `y` is a deterministic function of its parents in a subgraph
`gA`, and the system of equations is equivalent to every `u_j` being
`off_j(w) xor y`, where `off₀ = 0`. The template `HedgeTemplate` collects these properties, and
`HedgeTemplate.not_identifiable` gives non-identifiability for every such configuration. -/

namespace Identification

open HedgeChain (ev xx xb chan_symm)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The template for a hedge counter-model inside `G`: the nodes `x`, `y`, `w_i` and the
latent `u_j`, the subgraph `gA` of model A with the functions `fx`, `fw`, `fy` its kernels
compute, the shifts `off` of the bijection, the two equivalences `hfx` and `key` that make
the bijection work, the edge `x → y`, and the facts that all these nodes are different. -/
structure HedgeTemplate (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  gA : DAG V
  gA_parents_subset : ∀ v, gA.parents v ⊆ G.parents v
  fx : Assignment (α := fun _ : V => Bool) (gA.parents x) → Bool
  src : ∀ b, ∀ a ∈ gA.parents b, (∃ j, u j = a) ∨ (∃ i, w i = a)
  fw : (i : Fin (n + 1)) → Assignment (α := fun _ : V => Bool) (gA.parents (w i)) → Bool
  fy : Assignment (α := fun _ : V => Bool) (gA.parents y) → Bool
  off : Fin (n + 2) → (Fin (n + 1) → Bool) → Bool → Bool
  hfx : ∀ s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V),
    (∀ j, ev s (u j) = off j (fun i => ev s (w i)) (ev s y)) →
      fx (s.restrict (Finset.subset_univ _)) = ev s y
  key : ∀ s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V),
    ((∀ i, ev s (w i) = fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s y = fy (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (u j) = off j (fun i => ev s (w i)) (ev s y)
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace HedgeTemplate

variable {G : DAG V} {n : ℕ} (T : HedgeTemplate G n)

/-- `x` and `y` are different. -/
lemma dxy : T.x ≠ T.y := BowEmbedded.ne_of_edge T.hxy

/-- Transport a parent along an equality of children. -/
lemma mem_cast {a b c : V} (e : b = c) (h : a ∈ T.gA.parents b) : a ∈ T.gA.parents c := by
  rw [← e]; exact h

/-- Model A: `x` a noisy copy of `fx`, every `w_i` and `y` given by `fw i` and `fy`, every
other node uniform. -/
noncomputable def NA : T.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = T.x then Bow.chan (T.fx (fun p => pa ⟨p.1, T.mem_cast hvx.symm p.2⟩))
    else if hvy : v = T.y then PMF.pure (T.fy (fun p => pa ⟨p.1, T.mem_cast hvy.symm p.2⟩))
    else if h : ∃ i, T.w i = v then
      PMF.pure (T.fw (Classical.choose h)
        (fun p => pa ⟨p.1, T.mem_cast (Classical.choose_spec h) p.2⟩))
    else PMF.uniformOfFintype Bool

/-- Model B, on the graph with only `x → y`: `y` a noisy copy of `x`, the `u`s fixed to `false`,
every other node uniform. -/
noncomputable def NB : (BowEmbedded.g1 G T.x T.y T.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = T.y then Bow.chan (pa ⟨T.x, by rw [hvy]; exact BowEmbedded.p1 G T.x T.y T.hxy⟩)
    else if ∃ j, T.u j = v then PMF.pure false
    else PMF.uniformOfFintype Bool

/-- The kernel of `x` in model A. -/
lemma NA_x (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents T.x)) :
    T.NA.kernel T.x pa = Bow.chan (T.fx pa) := by
  simp only [NA, dif_pos (rfl : T.x = T.x)]
  all_goals rfl

/-- The kernel of `y` in model A. -/
lemma NA_y (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents T.y)) :
    T.NA.kernel T.y pa = PMF.pure (T.fy pa) := by
  simp only [NA, dif_neg T.dxy.symm, dif_pos (rfl : T.y = T.y)]
  all_goals rfl

/-- The kernel of `w_i` in model A. -/
lemma NA_w (i : Fin (n + 1)) (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents (T.w i))) :
    T.NA.kernel (T.w i) pa = PMF.pure (T.fw i pa) := by
  have h : ∃ i', T.w i' = T.w i := ⟨i, rfl⟩
  have key : ∀ (i' : Fin (n + 1)) (e : T.w i' = T.w i),
      PMF.pure (T.fw i' (fun p => pa ⟨p.1, T.mem_cast e p.2⟩)) = PMF.pure (T.fw i pa) := by
    intro i' e
    obtain rfl := T.winj e
    rfl
  simp only [NA, dif_neg (T.hwx i), dif_neg (T.hwy' i), dif_pos h]
  exact key _ (Classical.choose_spec h)

/-- The kernel of any other node in model A is uniform. -/
lemma NA_o {v : V} (hvx : v ≠ T.x) (hvy : v ≠ T.y) (hw : ∀ i, T.w i ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (T.gA.parents v)) :
    T.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ i, T.w i = v := fun ⟨i, hi⟩ => hw i hi
  simp only [NA, dif_neg hvx, dif_neg hvy, dif_neg h]

/-- The kernel of `y` in model B. -/
lemma NB_y (pa : {v // v ∈ (BowEmbedded.g1 G T.x T.y T.hxy).parents T.y} → Bool) :
    T.NB.kernel T.y pa = Bow.chan (pa ⟨T.x, BowEmbedded.p1 G T.x T.y T.hxy⟩) := by
  simp [NB]

/-- The kernel of `u_j` in model B. -/
lemma NB_u (j : Fin (n + 2))
    (pa : {v // v ∈ (BowEmbedded.g1 G T.x T.y T.hxy).parents (T.u j)} → Bool) :
    T.NB.kernel (T.u j) pa = PMF.pure false := by
  have h : ∃ j', T.u j' = T.u j := ⟨j, rfl⟩
  simp only [NB, dif_neg (T.huy' j), if_pos h]

/-- The kernel of any other node in model B is uniform. -/
lemma NB_o {v : V} (hvy : v ≠ T.y) (hu : ∀ j, T.u j ≠ v)
    (pa : {w // w ∈ (BowEmbedded.g1 G T.x T.y T.hxy).parents v} → Bool) :
    T.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, T.u j = v := fun ⟨j, hj⟩ => hu j hj
  simp only [NB, dif_neg hvy, if_neg h]

/-- Model A as a model on `G`. -/
noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub T.gA_parents_subset T.NA
/-- Model B as a model on `G`. -/
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowEmbedded.g1_parents_subset G T.x T.y T.hxy) T.NB

/-- The bijection of full assignments: it changes only the `u`s, `u_j ↦ u_j xor off_j(w, y)`. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if h : ∃ j, T.u j = v.1 then
      xor (s v) (T.off (Classical.choose h) (fun i => ev s (T.w i)) (ev s T.y))
    else s v

/-- The value of `φ s` at `u_j`. -/
lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    ev (T.φ s) (T.u j) = xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) := by
  have h : ∃ j', T.u j' = T.u j := ⟨j, rfl⟩
  have hc : Classical.choose h = j := T.uinj (Classical.choose_spec h)
  simp only [ev, φ]
  rw [dif_pos h, hc]

/-- `φ` does not change the nodes outside the `u`s. -/
lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, T.u j ≠ v) : ev (T.φ s) v = ev s v := by
  have h : ¬ ∃ j, T.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [ev, φ]
  rw [dif_neg h]

/-- `φ` is an involution. -/
lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    T.φ (T.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (T.φ (T.φ s)) v = ev s v
  by_cases h : ∃ j, T.u j = v
  · obtain ⟨j, rfl⟩ := h
    have hw : ∀ i, ev (T.φ s) (T.w i) = ev s (T.w i) := fun i => T.φ_o s (fun j => T.huw j i)
    have hy : ev (T.φ s) T.y = ev s T.y := T.φ_o s T.huy'
    rw [T.φ_u (T.φ s) j]
    simp only [hw, hy]
    rw [T.φ_u s j]
    exact xx _ _
  · have hv' : ∀ j, T.u j ≠ v := fun j hj => h ⟨j, hj⟩
    rw [T.φ_o _ hv', T.φ_o _ hv']

/-- The remaining nodes: all except `x`, `y`, the `u`s and the `w`s. -/
def R : Finset V :=
  (insert T.x (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)))ᶜ

/-- Membership in the remaining nodes. -/
lemma mem_R {v : V} : v ∈ T.R ↔
    v ≠ T.x ∧ v ≠ T.y ∧ (∀ j, T.u j ≠ v) ∧ (∀ i, T.w i ≠ v) := by
  simp [R]

/-- A product over all nodes splits into the factors at `x`, `y`, the `u`s, the `w`s and the
remaining nodes. -/
lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f T.x * f T.y * (∏ j, f (T.u j)) * (∏ i, f (T.w i)) * ∏ v ∈ T.R, f v := by
  rw [← Finset.prod_mul_prod_compl
    (insert T.x (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w))) f]
  have hx : T.x ∉ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    simp [T.dxy, T.hux', T.hwx]
  have hy : T.y ∉ Finset.univ.image T.u ∪ Finset.univ.image T.w := by
    simp [T.huy', T.hwy']
  have hd : Disjoint (Finset.univ.image T.u) (Finset.univ.image T.w) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨i, hi⟩ := hb
    exact T.huw j i hi.symm
  rw [Finset.prod_insert hx, Finset.prod_insert hy, Finset.prod_union hd]
  rw [Finset.prod_image T.uinj.injOn, Finset.prod_image T.winj.injOn]
  simp only [R, mul_assoc]

/-! ### The kernel factors of the two models -/

/-- The factor of `x` in model A. -/
lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NA Finset.univ s T.x =
      Bow.chan (T.fx (s.restrict (Finset.subset_univ _))) (ev s T.x) := by
  rw [kfac_univ, T.NA_x]
  all_goals rfl

/-- The factor of `y` in model A. -/
lemma A_y (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NA Finset.univ s T.y =
      PMF.pure (T.fy (s.restrict (Finset.subset_univ _))) (ev s T.y) := by
  rw [kfac_univ, T.NA_y]
  all_goals rfl

/-- The factor of `u_j` in model A is `1/2`. -/
lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac T.NA Finset.univ s (T.u j) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, T.NA_o (T.hux' j) (T.huy' j) (fun i => (T.huw j i).symm),
    PMF.uniformOfFintype_apply]

/-- The factor of `w_i` in model A. -/
lemma A_w (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac T.NA Finset.univ s (T.w i) =
      PMF.pure (T.fw i (s.restrict (Finset.subset_univ _))) (ev s (T.w i)) := by
  rw [kfac_univ, T.NA_w]
  all_goals rfl

/-- The factor of a remaining node in model A is `1/2`. -/
lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ T.R) : kfac T.NA Finset.univ s v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨h1, h2, _, h4⟩ := T.mem_R.mp hv
  rw [kfac_univ, T.NA_o h1 h2 h4, PMF.uniformOfFintype_apply]

/-- The factor of `x` in model B is `1/2`. -/
lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NB Finset.univ t T.x = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, T.NB_o T.dxy T.hux', PMF.uniformOfFintype_apply]

/-- The factor of `y` in model B. -/
lemma B_y (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac T.NB Finset.univ t T.y = Bow.chan (ev t T.x) (ev t T.y) := by
  rw [kfac_univ, T.NB_y]
  all_goals rfl

/-- The factor of `u_j` in model B. -/
lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac T.NB Finset.univ t (T.u j) = PMF.pure false (ev t (T.u j)) := by
  rw [kfac_univ, T.NB_u]
  all_goals rfl

/-- The factor of `w_i` in model B is `1/2`. -/
lemma B_w (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac T.NB Finset.univ t (T.w i) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, T.NB_o (T.hwy' i) (fun j => T.huw j i), PMF.uniformOfFintype_apply]

/-- The factor of a remaining node in model B is `1/2`. -/
lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ T.R) : kfac T.NB Finset.univ t v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨_, h2, h3, _⟩ := T.mem_R.mp hv
  rw [kfac_univ, T.NB_o h2 h3, PMF.uniformOfFintype_apply]

/-! ### The joint distributions and the end of the proof -/

/-- Model B gives `φ s` the probability that model A gives `s`: both are zero unless the
equations hold (by `key`), and then they are equal (by `hfx`). -/
lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    T.mB.fullJoint (T.φ s) = T.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, Completeness.kfac_liftSub]
  rw [T.prod_split, T.prod_split]
  have hR : ∏ v ∈ T.R, kfac T.NB Finset.univ (T.φ s) v =
      ∏ v ∈ T.R, kfac T.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [T.B_o _ v hv, T.A_o s v hv])
  have hx' : ev (T.φ s) T.x = ev s T.x := T.φ_o s T.hux'
  have hy' : ev (T.φ s) T.y = ev s T.y := T.φ_o s T.huy'
  rw [hR, T.A_x, T.A_y, T.B_x, T.B_y, hx', hy']
  by_cases hC : (∀ i, ev s (T.w i) = T.fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s T.y = T.fy (s.restrict (Finset.subset_univ _))
  · have hB := (T.key s).mp hC
    obtain ⟨hW', hY'⟩ := hC
    have hU : ∏ j, kfac T.NB Finset.univ (T.φ s) (T.u j) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hj := hB j
      have hcond : xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) =
          false := by
        rw [hj]; exact Bool.xor_self _
      rw [T.B_u, T.φ_u, PMF.pure_apply, if_pos hcond]
    have hW : ∏ i, kfac T.NA Finset.univ s (T.w i) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      rw [T.A_w, PMF.pure_apply, if_pos (hW' i)]
    have h0 : T.fx (s.restrict (Finset.subset_univ _)) = ev s T.y := T.hfx s hB
    rw [hU, hW]
    simp only [T.A_u, T.B_w, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [PMF.pure_apply, if_pos hY', h0, chan_symm (ev s T.y)]
    ring
  · have hB : ¬ ∀ j, ev s (T.u j) = T.off j (fun i => ev s (T.w i)) (ev s T.y) :=
      fun h => hC ((T.key s).mpr h)
    have hU : ∏ j, kfac T.NB Finset.univ (T.φ s) (T.u j) = 0 := by
      push_neg at hB
      obtain ⟨j, hj⟩ := hB
      have hnc : ¬ (xor (ev s (T.u j)) (T.off j (fun i => ev s (T.w i)) (ev s T.y)) =
          false) := fun hf => hj (xb _ _ hf)
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [T.B_u, T.φ_u, PMF.pure_apply, if_neg hnc]
    have hA : PMF.pure (T.fy (s.restrict (Finset.subset_univ _))) (ev s T.y) = 0 ∨
        ∏ i, kfac T.NA Finset.univ s (T.w i) = 0 := by
      by_cases hY : ev s T.y = T.fy (s.restrict (Finset.subset_univ _))
      · right
        have hW : ¬ ∀ i, ev s (T.w i) = T.fw i (s.restrict (Finset.subset_univ _)) :=
          fun hW => hC ⟨hW, hY⟩
        push_neg at hW
        obtain ⟨i, hi⟩ := hW
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [T.A_w, PMF.pure_apply, if_neg hi])
      · left
        rw [PMF.pure_apply, if_neg hY]
    rcases hA with h | h
    · rw [hU, h]; simp
    · rw [hU, h]; simp

/-- The joint distribution of model B is that of model A pushed forward along `φ`. -/
lemma full_map : T.mB.fullJoint = T.mA.fullJoint.map T.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (T.φ s)]
  · rw [if_pos (T.φ_invol s).symm, ← T.joint_eq (T.φ s), T.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, T.φ_invol]

/-- Models A and B agree on every `O` that contains no `u`. -/
lemma obsEq (O : Finset V) (hu : ∀ j, T.u j ∉ O) :
    T.mA.marginal O = T.mB.marginal O := by
  unfold CausalModel.marginal
  rw [T.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ∀ j, T.u j ≠ v := fun j e => hu j (e ▸ hv)
  show ev s v = ev (T.φ s) v
  exact (T.φ_o s hv').symm

/-- The observed distribution of model A on `O` is positive when `x ∈ O` and no `u` is in `O`. -/
lemma posA (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) :
    ∀ a, T.mA.marginal O a ≠ 0 := by
  intro a
  rw [T.obsEq O hu, show T.mB.marginal O = T.NB.marginal O from
    Completeness.marginal_eq_of_kfac _ _
      (Completeness.kfac_liftSub (BowEmbedded.g1_parents_subset G T.x T.y T.hxy) T.NB) O]
  have hS := BowEmbedded.ancB G T.x T.y T.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_of_mem _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  by_cases hvy : v = T.y
  · subst hvy
    rw [T.NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [T.NB_o hvy (fun j e => hu j (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

/-- In model A, `P_x(y)` is the observed `P(y)` of model B: after the intervention `x` no longer
reaches `y`. -/
lemma doA (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {T.x})
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mA {T.x} x0).marginal {T.y} y0 = T.mB.marginal {T.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel T.mA {T.x} x0)
    (doModel T.NA {T.x} x0)
    (Completeness.kfac_doModel_liftSub T.gA_parents_subset T.NA {T.x} x0) {T.y}]
  have hanc : ∀ v ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w), ∀ a,
      T.gA.edge a v → a ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    intro v _ a ha
    have hp : a ∈ T.gA.parents v := DAG.mem_parents.mpr ha
    rcases T.src v a hp with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> simp
  have hdisj : Disjoint (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)) {T.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [T.dxy, T.hux', T.hwx]
  rw [Rule3.doModel_marginal_of_subset T.NA {T.x} x0 _ hanc hdisj {T.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac T.mA T.NA
      (Completeness.kfac_liftSub T.gA_parents_subset T.NA) {T.y},
    marginal_eq_of_subset (T.obsEq O hu) (show ({T.y} : Finset V) ⊆ O by simpa using hy)]

/-- **The template gives non-identifiability.** For every configuration `T`, `P(y | do(x))`
is not identifiable from any `O` that contains `x` and `y` but no `u`. -/
theorem not_identifiable (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) (hy : T.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} {T.y} := by
  intro h
  have hyx : T.y ≠ T.x := T.dxy.symm
  have hnp : ∀ w, ¬ (BowEmbedded.g1 G T.x T.y T.hxy).edge w T.x := by
    intro w hw
    have hw' : w = T.x ∧ T.x = T.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowEmbedded.ancB G T.x T.y T.hxy ({T.y} ∪ {T.x}) (Or.inl (by simp))
  have hS1 := BowEmbedded.ancB G T.x T.y T.hxy {T.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        T.mB.marginal {T.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ {T.x}) :=
      fun v => if v.1 = T.x then b else true
    have htx : t.restrict (show ({T.x} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = T.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = T.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h T.mA T.mB (T.obsEq O hu) (T.posA O hu hx) t
    rw [htx, hty, T.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} _)
        (doModel T.NB {T.x} _)
        (Completeness.kfac_doModel_liftSub (BowEmbedded.g1_parents_subset G T.x T.y T.hxy)
          T.NB {T.x} _) {T.y}] at e
    have fd := Adjustment.frontdoor_step1 T.NB {T.x} {T.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {T.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({T.y} : Finset V) {T.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_of_mem _ _ t T.y (by simp) (DAG.parents_subset_of_closed hS21 T.y (by simp)),
      kfac_of_mem _ _ t T.x (by simp) (DAG.parents_subset_of_closed hS21 T.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {T.x} hS1, Finset.prod_singleton,
      kfac_of_mem _ {T.x} _ T.x (by simp) (DAG.parents_subset_of_closed hS1 T.x (by simp))] at fd
    rw [T.NB_y, T.NB_o hyx.symm T.hux', T.NB_o hyx.symm T.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end HedgeTemplate

end Identification

#print axioms Identification.HedgeTemplate.not_identifiable

/-! ## A hedge along a latent path with an arbitrary directed tree towards `y`

Latent `u₀, …, u_{n+1}` give the path `x ↔ w₀ ↔ … ↔ w_n ↔ y`. The directed edges
between the `w`s form an arbitrary tree towards `y`: every `w_j` has one parent `p j`
in the tree, either another `w_i` or `y`. The chain (`p j = j + 1`) and the star
(`p j = y` for all `j`) are special cases.

Model A is the parity model: every `w_i` is the sum (mod 2) of its two latent
parents and its children in the tree, and `y = u_{n+1} +` the children of `y`. Then `y`
is the sum of all latent contributions, in which every inner `u` counts twice, so
`y = u₀`. -/

namespace Identification

open HedgeChain (ev)
open ZMod2 (ofBool toBool ofBool_toBool eq_toBool_iff ofBool_xor ofBool_injective)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A latent path `x ↔ w₀ ↔ … ↔ w_n ↔ y` with a directed tree towards `y`: the nodes, the
latent `u`s, the parent map `p` of the tree (`none` for `y`), the edges, and the facts that
all these nodes are different. -/
structure PathTree (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  p : Fin (n + 1) → Option (Fin (n + 1))
  hux : G.edge (u 0) x
  huw1 : ∀ i, G.edge (u i.castSucc) (w i)
  huw2 : ∀ i, G.edge (u i.succ) (w i)
  hpw : ∀ j i, p j = some i → G.edge (w j) (w i)
  hpy : ∀ j, p j = none → G.edge (w j) y
  huy : G.edge (u (Fin.last (n + 1))) y
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace PathTree

variable {G : DAG V} {n : ℕ} (P : PathTree G n)

/-- The graph of model A: the latent edges of the path and the edges of the tree, without
`x → y`. -/
noncomputable def gA : DAG V where
  edge a b := (a = P.u 0 ∧ b = P.x) ∨ (∃ i, a = P.u i.castSucc ∧ b = P.w i) ∨
    (∃ i, a = P.u i.succ ∧ b = P.w i) ∨ (∃ j i, P.p j = some i ∧ a = P.w j ∧ b = P.w i) ∨
    (∃ j, P.p j = none ∧ a = P.w j ∧ b = P.y) ∨ (a = P.u (Fin.last (n + 1)) ∧ b = P.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨j, i, hp, h1, h2⟩ |
        ⟨j, hp, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.huw1 i)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.huw2 i)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hpw j i hp)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hpy j hp)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.huy

/-- The edges of the graph of model A. -/
lemma gA_edge (a b : V) : P.gA.edge a b ↔ ((a = P.u 0 ∧ b = P.x) ∨
    (∃ i, a = P.u i.castSucc ∧ b = P.w i) ∨ (∃ i, a = P.u i.succ ∧ b = P.w i) ∨
    (∃ j i, P.p j = some i ∧ a = P.w j ∧ b = P.w i) ∨
    (∃ j, P.p j = none ∧ a = P.w j ∧ b = P.y) ∨ (a = P.u (Fin.last (n + 1)) ∧ b = P.y)) :=
  Iff.rfl

/-- `u₀` is a parent of `x` in the graph of model A. -/
lemma pAx : P.u 0 ∈ P.gA.parents P.x :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inl ⟨rfl, rfl⟩))
/-- `u_i` is a parent of `w_i` in the graph of model A. -/
lemma pw1 (i : Fin (n + 1)) : P.u i.castSucc ∈ P.gA.parents (P.w i) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))
/-- `u_{i+1}` is a parent of `w_i` in the graph of model A. -/
lemma pw2 (i : Fin (n + 1)) : P.u i.succ ∈ P.gA.parents (P.w i) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))))
/-- A child `w_j` of `w_i` in the tree is a parent of `w_i` in the graph of model A. -/
lemma pww (j i : Fin (n + 1)) (h : P.p j = some i) : P.w j ∈ P.gA.parents (P.w i) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, i, h, rfl, rfl⟩)))))
/-- A child `w_j` of `y` in the tree is a parent of `y` in the graph of model A. -/
lemma pyw (j : Fin (n + 1)) (h : P.p j = none) : P.w j ∈ P.gA.parents P.y :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, h, rfl, rfl⟩))))))
/-- `u_{n+1}` is a parent of `y` in the graph of model A. -/
lemma pyu : P.u (Fin.last (n + 1)) ∈ P.gA.parents P.y :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))

/-- The graph of model A is a subgraph of `G`. -/
lemma gA_parents_subset : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.gA_edge a v).mp ha with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨j, i, hp, h1, h2⟩ |
      ⟨j, hp, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact P.hux
  · rw [h1, h2]; exact P.huw1 i
  · rw [h1, h2]; exact P.huw2 i
  · rw [h1, h2]; exact P.hpw j i hp
  · rw [h1, h2]; exact P.hpy j hp
  · rw [h1, h2]; exact P.huy

/-- Every parent in the graph of model A is a `u` or a `w`. -/
lemma src : ∀ b, ∀ a ∈ P.gA.parents b, (∃ j, P.u j = a) ∨ (∃ i, P.w i = a) := by
  intro b a ha
  rw [DAG.mem_parents] at ha
  rcases (P.gA_edge a b).mp ha with ⟨h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ | ⟨j, i, _, h1, _⟩ |
      ⟨j, _, h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl ⟨0, h1.symm⟩
  · exact Or.inl ⟨i.castSucc, h1.symm⟩
  · exact Or.inl ⟨i.succ, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩
  · exact Or.inl ⟨Fin.last (n + 1), h1.symm⟩

/-! ### The kernels and the equations -/

/-- The kernel function of `w_i` in model A: the sum (mod 2) of its two latent parents and its
children in the tree. -/
noncomputable def fw (i : Fin (n + 1))
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.w i))) : Bool :=
  toBool (ofBool (pa ⟨P.u i.castSucc, P.pw1 i⟩) + ofBool (pa ⟨P.u i.succ, P.pw2 i⟩) +
    ∑ j, if h : P.p j = some i then ofBool (pa ⟨P.w j, P.pww j i h⟩) else 0)

/-- The kernel function of `y` in model A: the sum (mod 2) of `u_{n+1}` and the children of `y`
in the tree. -/
noncomputable def fy (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.y)) : Bool :=
  toBool (ofBool (pa ⟨P.u (Fin.last (n + 1)), P.pyu⟩) +
    ∑ j, if h : P.p j = none then ofBool (pa ⟨P.w j, P.pyw j h⟩) else 0)

/-- The sum (mod 2) of the values of the children of `w_i` in the tree. -/
def C (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ZMod 2 :=
  ∑ j, if P.p j = some i then ofBool (b j) else 0
/-- The sum (mod 2) of the values of the children of `y` in the tree. -/
def Cy (b : Fin (n + 1) → Bool) : ZMod 2 :=
  ∑ j, if P.p j = none then ofBool (b j) else 0
/-- The contribution of `w_i` to the prefix sum: its own value plus those of its children. -/
def rr (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ZMod 2 := ofBool (b i) + P.C b i
/-- `rr` indexed by a natural number, `0` past the end of the path. -/
def rN (b : Fin (n + 1) → Bool) (k : ℕ) : ZMod 2 :=
  if h : k < n + 1 then P.rr b ⟨k, h⟩ else 0
/-- The prefix sum of the contributions `rN`. -/
def offN (b : Fin (n + 1) → Bool) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 => offN b k + P.rN b k
/-- The shift of `u_j` in the bijection: the prefix sum up to `j`, added to `y`. -/
def off (j : Fin (n + 2)) (b : Fin (n + 1) → Bool) (c : Bool) : Bool :=
  xor (toBool (P.offN b j.val)) c

/-- If every `u_j` equals its shift, then `u₀ = y` (the shift of `u₀` is `y` itself). -/
lemma hu0 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (h : ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.w i)) (ev s P.y)) :
    ev s (P.u 0) = ev s P.y := by
  rw [h 0]
  simp [off, offN, ZMod2.toBool]

/-- One step of the prefix sum inside the path. -/
lemma offN_succ_fin (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    P.offN b (i.val + 1) = P.offN b i.val + P.rr b i := by
  show P.offN b i.val + P.rN b i.val = _
  rw [rN, dif_pos i.2]

/-- The prefix sum as a sum over a range. -/
lemma offN_sum (b : Fin (n + 1) → Bool) : ∀ k, P.offN b k = ∑ m ∈ Finset.range k, P.rN b m := by
  intro k
  induction k with
  | zero => simp [offN]
  | succ k ih => rw [Finset.sum_range_succ, ← ih] <;> rfl

/-- The prefix sum over the whole path is the sum of all contributions. -/
lemma offN_last (b : Fin (n + 1) → Bool) : P.offN b (n + 1) = ∑ i, P.rr b i := by
  rw [P.offN_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [rN, i.2]

/-- **The cancellation**: every `w_j` is the child of exactly one node of the tree, so the
contributions of all `w`s and of the children of `y` add up to zero. -/
lemma sum_zero (b : Fin (n + 1) → Bool) : ∑ i, P.rr b i + P.Cy b = 0 := by
  have hpt : ∀ j, (∑ i, (if P.p j = some i then ofBool (b j) else 0)) +
      (if P.p j = none then ofBool (b j) else 0) = ofBool (b j) := by
    intro j
    cases h : P.p j <;> simp [h]
  have hC : ∑ i, P.C b i + P.Cy b = ∑ j, ofBool (b j) := by
    unfold C Cy
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpt j)
  calc ∑ i, P.rr b i + P.Cy b = ∑ i, ofBool (b i) + (∑ i, P.C b i + P.Cy b) := by
        simp only [rr, Finset.sum_add_distrib, add_assoc]
    _ = ∑ i, ofBool (b i) + ∑ j, ofBool (b j) := by rw [hC]
    _ = 0 := CharTwo.add_self_eq_zero _

/-- The kernel function of `w_i`, read off a full assignment. -/
lemma fw_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    P.fw i (s.restrict (Finset.subset_univ _)) =
      toBool (ofBool (ev s (P.u i.castSucc)) + ofBool (ev s (P.u i.succ)) +
        P.C (fun k => ev s (P.w k)) i) := by
  unfold fw C
  congr 1

/-- The kernel function of `y`, read off a full assignment. -/
lemma fy_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.fy (s.restrict (Finset.subset_univ _)) =
      toBool (ofBool (ev s (P.u (Fin.last (n + 1)))) + P.Cy (fun k => ev s (P.w k))) := by
  unfold fy Cy
  congr 1

/-- **The two systems of equations are equivalent**: the equations of model A hold exactly
when every `u_j` equals its shift. -/
lemma key (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ((∀ i, ev s (P.w i) = P.fw i (s.restrict (Finset.subset_univ _))) ∧
      ev s P.y = P.fy (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.w i)) (ev s P.y) := by
  constructor
  · rintro ⟨hw, hy⟩
    have hw' : ∀ i, ofBool (ev s (P.w i)) =
        ofBool (ev s (P.u i.castSucc)) + ofBool (ev s (P.u i.succ)) + P.C (fun k => ev s (P.w k)) i := fun i => (eq_toBool_iff _ _).mp ((hw i).trans (P.fw_s s i))
    have hy' : ofBool (ev s P.y) = ofBool (ev s (P.u (Fin.last (n + 1)))) +
        P.Cy (fun k => ev s (P.w k)) := (eq_toBool_iff _ _).mp (hy.trans (P.fy_s s))
    have hU : ∀ j : Fin (n + 2), ofBool (ev s (P.u j)) =
        ofBool (ev s (P.u 0)) + P.offN (fun k => ev s (P.w k)) j.val := by
      intro j
      refine Fin.induction ?_ (fun i ih => ?_) j
      · simp [offN]
      · have ih' : ofBool (ev s (P.u i.castSucc)) =
            ofBool (ev s (P.u 0)) + P.offN (fun k => ev s (P.w k)) i.val := by simpa using ih
        rw [Fin.val_succ, P.offN_succ_fin]
        exact ZMod2.eq_add_add_of_eq_add_add_of_eq_add _ _ _ _ _ _ (hw' i) ih'
    have hl : ofBool (ev s (P.u (Fin.last (n + 1)))) =
        ofBool (ev s (P.u 0)) + ∑ i, P.rr (fun k => ev s (P.w k)) i := by
      rw [hU, Fin.val_last, P.offN_last]
    have h0 : ofBool (ev s (P.u 0)) = ofBool (ev s P.y) :=
      ZMod2.eq_of_eq_add_of_eq_add_of_add_eq_zero _ _ _ _ _ hy' hl (P.sum_zero _)
    intro j
    apply ofBool_injective
    rw [off, ofBool_xor, ofBool_toBool, hU j, h0]
    ring
  · intro hB
    have hB' : ∀ j,
        ofBool (ev s (P.u j)) = P.offN (fun k => ev s (P.w k)) j.val + ofBool (ev s P.y) := by
      intro j
      have := congrArg ofBool (hB j)
      rwa [off, ofBool_xor, ofBool_toBool] at this
    refine ⟨fun i => ?_, ?_⟩
    · rw [P.fw_s, eq_toBool_iff, hB' i.castSucc, hB' i.succ, Fin.val_succ, P.offN_succ_fin,
        Fin.coe_castSucc]
      exact ZMod2.self_eq_add_add_add_cancel _ _ _ _
    · rw [P.fy_s, eq_toBool_iff, hB' (Fin.last (n + 1)), Fin.val_last, P.offN_last]
      exact ZMod2.eq_add_add_of_add_eq_zero _ _ _ (P.sum_zero _)

/-- The configuration as an instance of the template. -/
noncomputable def toHedgeTemplate : HedgeTemplate G n where
  x := P.x
  y := P.y
  w := P.w
  u := P.u
  gA := P.gA
  gA_parents_subset := P.gA_parents_subset
  fx := fun pa => pa ⟨P.u 0, P.pAx⟩
  src := P.src
  fw := P.fw
  fy := P.fy
  off := P.off
  hfx := fun s h => P.hu0 s h
  key := P.key
  hxy := P.hxy
  winj := P.winj
  uinj := P.uinj
  huw := P.huw
  hux' := P.hux'
  huy' := P.huy'
  hwx := P.hwx
  hwy' := P.hwy'

/-- **A hedge along a latent path with an arbitrary directed tree towards `y`.** For
`x ↔ w₀ ↔ … ↔ w_n ↔ y` through latent `u₀, …, u_{n+1}`, where every `w_j` has an edge to
`w_{p j}` or to `y`, and `x → y`, `P(y | do(x))` is not identifiable from any `O` that
contains `x` and `y` but no `u`. -/
theorem not_identifiable (O : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O)
    (hy : P.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} {P.y} :=
  P.toHedgeTemplate.not_identifiable O hu hx hy

end PathTree
end Identification

#print axioms Identification.PathTree.not_identifiable
