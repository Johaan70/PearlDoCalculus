import PearlDoCalculus.Identification.RootPathModels

/-!
# Non-identifiability along a root path

This file finishes the argument for c-forests with several roots. It proves that the
models A and C of `Identification/RootPathModels` have the same joint distribution,
and gives the bijection between the models A and B. From this it follows that
`P(roots | do(x))` is not identifiable.

Why it is needed: `RootTree.rootTree_not_identifiable` builds the latent path and then
applies `rootPath_not_identifiable`; through it and `RootTree.embedded_not_identifiable`
this is the negative half of `tian_iff` in every case except the bow.

How the proof goes. *A and C agree*: both joint distributions vanish unless the parity
equations hold, and then the solution of the forest system (`keyAC`) and `eqs_sum` make
the factors equal (`joint_AC`). So every observed marginal of A can be computed in C,
where the nodes are independent uniform bits: this gives positivity (`posA`). *A and B
agree on the observed nodes*: the bijection `φ` shifts every latent on the path by the
sum over the roots; by the path condition this changes the parity only at `nd_r`
(`parZ_φ`), where model B has moved the channel, so B gives `φ s` the probability that A
gives `s` (`joint_BA`). *The effects differ*: in A, `x` does not reach the roots once its
incoming edge is cut, so `P(roots | do(x))` is the observed `P(roots)` (`doA`); in B, `x`
has no parents, so the first front-door step gives `P(roots | do(x)) = P(roots, x) / P(x)`,
which, computed in C, is the channel at `nd_r` and depends on `x`.

Main results:
* `RootPath.rootPath_not_identifiable`: the theorem for `RootPath.RP`, where `x` may
  point into any root `nd_r` and a latent path from `u₀` to `u_r` is given.
* `RootPath.multiRoot_of_rootPath`: the configuration `MultiRoot.MR` is the special case
  `r = 0` with the path `{u₀}`.
* `MultiRoot.multiRoot_not_identifiable`: the corollary for `MultiRoot.MR`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

namespace Identification
namespace RootPath

open HedgeChain (ev xx xb chan_symm)
open ZMod2 (ofBool toBool ofBool_toBool eq_toBool_iff ofBool_xor ofBool_injective
  toBool_add_ofBool)

variable {V : Type*} [DecidableEq V] [Fintype V]

open MultiRoot (ext ext_restrict chan_mix)

namespace RP

variable {G : DAG V} {n : ℕ} (P : RP G n)

/-! ### Models A and C have the same joint distribution -/

/-- Models A and C give every full assignment the same probability. -/
lemma joint_AC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.NC.fullJoint s = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, Completeness.kfac_liftSub]
  rw [P.prod_split, P.prod_split]
  have hR : ∏ v ∈ P.R5, kfac P.NC Finset.univ s v = ∏ v ∈ P.R5, kfac P.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [P.C_o s v hv, P.A_o s v hv])
  rw [hR, P.C_x, P.A_x]
  simp only [P.C_u, P.A_u, P.C_nd, P.A_nd]
  by_cases hE : ∀ k, ev s (P.nd k) = toBool (P.parZ k (ev s))
  · have hsol := (P.keyAC s).mp hE
    have h0 : ev s (P.u 0) = toBool (∑ k ∈ P.Rt, ofBool (ev s (P.nd k))) := by
      apply ofBool_injective
      rw [ofBool_toBool]
      exact P.eqs_sum (fun k => ofBool (ev s (P.u k))) (fun k => ofBool (ev s (P.nd k)))
        (fun k => (eq_toBool_iff _ _).mp (hE k))
    have hU :
        ∏ j, PMF.pure (toBool (forestSolution P.bp P.ht (P.Rg (ev s)) j)) (ev s (P.u j)) = 1 :=
      Finset.prod_eq_one (fun j _ => PMF.pure_apply_of_eq _ _ (hsol j))
    have hN : ∏ k, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k _ => PMF.pure_apply_of_eq _ _ (hE k))
    rw [hU, hN, h0]
    ring
  · have hsol : ¬ ∀ j, ev s (P.u j) = toBool (forestSolution P.bp P.ht (P.Rg (ev s)) j) :=
      fun h => hE ((P.keyAC s).mpr h)
    push_neg at hE hsol
    obtain ⟨k, hk⟩ := hE
    obtain ⟨j, hj⟩ := hsol
    have hU :
        ∏ j, PMF.pure (toBool (forestSolution P.bp P.ht (P.Rg (ev s)) j)) (ev s (P.u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (PMF.pure_apply_of_ne _ _ hj)
    have hN : ∏ k, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (PMF.pure_apply_of_ne _ _ hk)
    rw [hU, hN]
    simp

/-- Models A and C have the same marginals. -/
lemma margAC (T : Finset V) : P.mA.marginal T = P.NC.marginal T := by
  have hj : P.NC.fullJoint = P.mA.fullJoint := PMF.ext (P.joint_AC)
  unfold CausalModel.marginal
  rw [hj]

/-! ### The bijection between models A and B -/

/-- The sum (mod 2) of the values at the roots, as a bit. -/
noncomputable def Sb (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) : Bool :=
  toBool (∑ k ∈ P.Rt, ofBool (ev s (P.nd k)))

/-- The bijection: every latent on the path is shifted by the sum over the roots. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if ∃ j, P.pth j = true ∧ P.u j = v.1 then xor (s v) (P.Sb s) else s v

/-- `φ` shifts a latent on the path. -/
lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : P.pth j = true) : ev (P.φ s) (P.u j) = xor (ev s (P.u j)) (P.Sb s) := by
  have h : ∃ j', P.pth j' = true ∧ P.u j' = P.u j := ⟨j, hj, rfl⟩
  simp only [φ, ev, if_pos h]

/-- `φ` does not change the nodes outside the path latents. -/
lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, P.pth j = true → P.u j ≠ v) : ev (P.φ s) v = ev s v := by
  have h : ¬ ∃ j, P.pth j = true ∧ P.u j = v := fun ⟨j, hj, e⟩ => hv j hj e
  simp only [φ, ev, if_neg h]

/-- `φ` does not change the nodes `nd_k`. -/
lemma φ_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev (P.φ s) (P.nd k) = ev s (P.nd k) := P.φ_o s (fun j _ => P.hund j k)

/-- `φ` does not change `x`. -/
lemma φ_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ev (P.φ s) P.x = ev s P.x := P.φ_o s (fun j _ => P.hux' j)

/-- `φ` in `ZMod 2`: latent `j` is shifted by `pth j · ΣR`. -/
lemma bz_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    ofBool (ev (P.φ s) (P.u j)) = ofBool (ev s (P.u j)) + ofBool (P.pth j) * ofBool (P.Sb s) := by
  cases hj : P.pth j
  · rw [P.φ_o s (fun j' hj' e => by rw [P.uinj e, hj] at hj'; exact Bool.false_ne_true hj')]
    simp [ZMod2.ofBool]
  · rw [P.φ_u s j hj, ofBool_xor]
    simp [ZMod2.ofBool]

/-- `φ` does not change the sum over the roots. -/
lemma Sb_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.Sb (P.φ s) = P.Sb s := by
  unfold Sb
  simp only [P.φ_nd]

/-- `φ` is an involution. -/
lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.φ (P.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (P.φ (P.φ s)) v = ev s v
  by_cases h : ∃ j, P.pth j = true ∧ P.u j = v
  · obtain ⟨j, hj, rfl⟩ := h
    rw [P.φ_u _ j hj, P.Sb_φ, P.φ_u s j hj]
    exact xx _ _
  · have hv' : ∀ j, P.pth j = true → P.u j ≠ v := fun j hj e => h ⟨j, hj, e⟩
    rw [P.φ_o _ hv', P.φ_o _ hv']

/-- **The path condition at work:** the parity changes only at `nd_r`. -/
lemma parZ_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.parZ k (ev (P.φ s)) = P.parZ k (ev s) + (if k = P.r then 1 else 0) * ofBool (P.Sb s) := by
  have e1 : (∑ j, if P.bp j = some k then ofBool (ev (P.φ s) (P.u j)) else 0) =
      (∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0) +
        (∑ j, if P.bp j = some k then ofBool (P.pth j) else 0) * ofBool (P.Sb s) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · exact P.bz_φ s j
    · simp
  have e2 : (∑ j, if P.dp j = some k then ofBool (ev (P.φ s) (P.nd j)) else 0) =
      ∑ j, if P.dp j = some k then ofBool (ev s (P.nd j)) else 0 := by
    simp only [P.φ_nd]
  unfold parZ
  rw [P.bz_φ s k, e1, e2, ← P.hpk k]
  ring

/-- Model B gives `φ s` the probability that model A gives `s`. -/
lemma joint_BA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.mB.fullJoint (P.φ s) = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, Completeness.kfac_liftSub]
  rw [P.prod_split, P.prod_split]
  have hR : ∏ v ∈ P.R5, kfac P.NB Finset.univ (P.φ s) v = ∏ v ∈ P.R5, kfac P.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [P.B_o _ v hv, P.A_o s v hv])
  have hBu : ∏ j, kfac P.NB Finset.univ (P.φ s) (P.u j) =
      PMF.pure false (xor (ev s (P.u 0)) (P.Sb s)) * ∏ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c2 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (n + 2))), P.B_u0,
      P.φ_u s 0 P.hp0]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => P.B_u _ j (Finset.ne_of_mem_erase hj))
  have hAu : ∏ j, kfac P.NA Finset.univ s (P.u j) = c2 * ∏ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c2 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    simp only [P.A_u]
  have hBn : ∏ k, kfac P.NB Finset.univ (P.φ s) (P.nd k) =
      Bow.chan (xor (ev s P.x) (toBool (P.parZ P.r (ev s) + ofBool (P.Sb s)))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r), P.B_ndr, P.parZ_φ, if_pos (rfl : P.r = P.r),
      one_mul, P.φ_x, P.φ_nd]
    congr 1
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk' := Finset.ne_of_mem_erase hk
    rw [P.B_nd _ k hk', P.parZ_φ, if_neg hk', zero_mul, add_zero, P.φ_nd]
  have hAn : ∏ k, kfac P.NA Finset.univ s (P.nd k) =
      PMF.pure (toBool (P.parZ P.r (ev s))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r)]
    simp only [P.A_nd]
  rw [hR, P.B_x, P.A_x, hBu, hAu, hBn, hAn]
  by_cases hrest : ∀ k ∈ Finset.univ.erase P.r, ev s (P.nd k) = toBool (P.parZ k (ev s))
  · have hN :
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k hk => PMF.pure_apply_of_eq _ _ (hrest k hk))
    rw [hN]
    have hiff := P.eqr_iff (fun k => ofBool (ev s (P.u k))) (fun k => ofBool (ev s (P.nd k)))
      (fun k hk => (eq_toBool_iff _ _).mp (hrest k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)))
    by_cases h0 : ev s (P.u 0) = P.Sb s
    · have he0 : ev s (P.nd P.r) = toBool (P.parZ P.r (ev s)) := by
        apply (eq_toBool_iff _ _).mpr
        apply hiff.mpr
        show ofBool (ev s (P.u 0)) = _
        rw [h0, Sb, ofBool_toBool]
      have hxf : xor (ev s (P.u 0)) (P.Sb s) = false := by
        rw [h0]
        exact Bool.xor_self _
      rw [PMF.pure_apply_of_eq _ _ he0, PMF.pure_apply_of_eq _ _ hxf, toBool_add_ofBool, ← he0, chan_mix, ← h0]
      ring
    · have he0 : ¬ ev s (P.nd P.r) = toBool (P.parZ P.r (ev s)) := by
        intro he
        apply h0
        apply ofBool_injective
        rw [Sb, ofBool_toBool]
        exact hiff.mp ((eq_toBool_iff _ _).mp he)
      have hx0 : ¬ xor (ev s (P.u 0)) (P.Sb s) = false := fun hf => h0 (xb _ _ hf)
      rw [PMF.pure_apply_of_ne _ _ he0, PMF.pure_apply_of_ne _ _ hx0]
      simp
  · push_neg at hrest
    obtain ⟨k, hk, hi⟩ := hrest
    have hN :
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero hk (PMF.pure_apply_of_ne _ _ hi)
    rw [hN]
    simp

/-- The joint distribution of model B is that of model A pushed forward along `φ`. -/
lemma full_map : P.mB.fullJoint = P.mA.fullJoint.map P.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (P.φ s)]
  · rw [if_pos (P.φ_invol s).symm, ← P.joint_BA (P.φ s), P.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, P.φ_invol]

/-- Models A and B agree on every `O` that contains no latent. -/
lemma obsEq (O : Finset V) (hu : ∀ j, P.u j ∉ O) : P.mA.marginal O = P.mB.marginal O := by
  unfold CausalModel.marginal
  rw [P.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv0 : ∀ j, P.pth j = true → P.u j ≠ v := fun j _ e => hu j (by rw [e]; exact hv)
  exact (P.φ_o s hv0).symm

/-! ### Computations in models C and B -/

/-- A set that contains all roots and no latent is ancestral in the graph of model C. -/
lemma ancC (S : Finset V) (hR : ∀ k, P.dp k = none → P.nd k ∈ S) (hu : ∀ j, P.u j ∉ S) :
    ∀ v ∈ S, ∀ a, P.gC.edge a v → a ∈ S := by
  intro v hv a ha
  rcases (P.eC a v).mp ha with ⟨k, hk, h1, _⟩ | ⟨k, j, _, h2⟩
  · rw [h1]
    exact hR k hk
  · exact absurd (by rw [← h2]; exact hv) (hu j)

/-- On an ancestral set of model C that contains the roots, the factors of the roots are `1/2`
each. -/
lemma prodY (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hYS : ∀ v ∈ P.Y, v ∈ S) :
    ∏ v ∈ P.Y, kfac P.NC S a v = ∏ v ∈ P.Y, c2 := by
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hvS := hYS v hv
  obtain ⟨k, _, hk⟩ := P.mem_Y.mp hv
  have hvx : v ≠ P.x := by rw [← hk]; exact P.hndx k
  have hvu : ∀ j, P.u j ≠ v := by rw [← hk]; exact fun j => P.hund j k
  rw [kfac_of_mem _ S a v hvS (DAG.parents_subset_of_closed hS v hvS), P.NC_o hvx hvu, PMF.uniformOfFintype_apply]

/-- If `nd_r` is `true` and every other node `nd_k` of the set is `false`, the factor of
`x` in model C is the channel from `true`. -/
lemma Cx_val (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hxS : P.x ∈ S)
    (ha : ∀ k (hk : P.nd k ∈ S), ofBool (a ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0) :
    kfac P.NC S a P.x = Bow.chan true (a ⟨P.x, hxS⟩) := by
  have hz : toBool (∑ k ∈ P.Rt, ofBool (ext (a.restrict (DAG.parents_subset_of_closed hS P.x hxS)) (P.nd k))) = true := by
    have hs : ∀ k ∈ P.Rt, ofBool (ext (a.restrict (DAG.parents_subset_of_closed hS P.x hxS)) (P.nd k)) =
        if k = P.r then 1 else 0 := by
      intro k hk
      have hp : P.nd k ∈ P.gC.parents P.x := P.pCx k (by simpa [Rt] using hk)
      have he : ext (a.restrict (DAG.parents_subset_of_closed hS P.x hxS)) (P.nd k) = a ⟨P.nd k, DAG.parents_subset_of_closed hS P.x hxS hp⟩ := by
        simp [MultiRoot.ext, hp, Assignment.restrict]
      rw [he]
      exact ha k (DAG.parents_subset_of_closed hS P.x hxS hp)
    rw [Finset.sum_congr rfl hs]
    rw [Finset.sum_ite_eq', if_pos P.mem_Rtr]
    all_goals rfl
  rw [kfac_of_mem _ S a P.x hxS (DAG.parents_subset_of_closed hS P.x hxS), P.NC_x, hz]

/-- The observed distribution of model A on `O` is positive when `O` contains the roots but no
latent. -/
lemma posA (O : Finset V) (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) :
    ∀ a, P.mA.marginal O a ≠ 0 := by
  intro a
  have hS := P.ancC O hY hu
  rw [P.margAC O, marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_of_mem _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  have hvu : ∀ j, P.u j ≠ v := fun j e => hu j (by rw [e]; exact hv)
  by_cases hvx : v = P.x
  · subst hvx
    rw [P.NC_x]
    exact Bow.chan_ne_zero _ _
  · rw [P.NC_o hvx hvu]
    simp [PMF.uniformOfFintype_apply]

/-- In model A, `P(roots | do(x))` is the observed `P(roots)`: after the intervention `x` no
longer reaches the roots. -/
lemma doA (x0 : Assignment (α := fun _ : V => Bool) {P.x})
    (y0 : Assignment (α := fun _ : V => Bool) P.Y) :
    (doModel P.mA {P.x} x0).marginal P.Y y0 = P.mA.marginal P.Y y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel P.mA {P.x} x0) (doModel P.NA {P.x} x0)
    (Completeness.kfac_doModel_liftSub P.hsA P.NA {P.x} x0) P.Y]
  have hanc : ∀ v ∈ (Finset.univ.image P.u ∪ Finset.univ.image P.nd), ∀ a, P.gA.edge a v →
      a ∈ (Finset.univ.image P.u ∪ Finset.univ.image P.nd) := by
    intro v hv a ha
    rcases (P.eA a v).mp ha with ⟨_, h2⟩ | ⟨k, h1, _⟩ | ⟨j, k, _, h1, _⟩ | ⟨j, k, _, h1, _⟩
    · exfalso
      rw [h2] at hv
      simp [P.hux', P.hndx] at hv
    · rw [h1]; simp
    · rw [h1]; simp
    · rw [h1]; simp
  have hdisj : Disjoint (Finset.univ.image P.u ∪ Finset.univ.image P.nd) {P.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [P.hux', P.hndx]
  have hYS : P.Y ⊆ Finset.univ.image P.u ∪ Finset.univ.image P.nd := by
    intro v hv
    obtain ⟨k, _, hk⟩ := P.mem_Y.mp hv
    rw [← hk]
    simp
  rw [Rule3.doModel_marginal_of_sub P.NA {P.x} x0 _ hanc hdisj P.Y hYS y0,
    ← Completeness.marginal_eq_of_kfac P.mA P.NA (Completeness.kfac_liftSub P.hsA P.NA) P.Y]

/-- **Several roots: `P(R | do(x))` is not identifiable**, where `R` is the set of roots. -/
theorem not_ident (O : Finset V) (hu : ∀ j, P.u j ∉ O)
    (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y := by
  intro h
  have hxY : P.x ∉ P.Y := by
    intro hm
    obtain ⟨k, _, hk⟩ := P.mem_Y.mp hm
    exact P.hndx k hk
  have hYX : Disjoint P.Y {P.x} := Finset.disjoint_singleton_right.mpr hxY
  have hnp : ∀ a, ¬ P.gB.edge a P.x := by
    intro a ha
    rcases (P.eB a P.x).mp ha with ⟨k, _, h2⟩ | ⟨j, k, _, _, h2⟩ | ⟨j, k, _, _, h2⟩ | ⟨_, h2⟩
    · exact P.hndx k h2.symm
    · exact P.hndx k h2.symm
    · exact P.hndx k h2.symm
    · exact P.hndx P.r h2.symm
  have hSx : ∀ v ∈ ({P.x} : Finset V), ∀ a, P.gB.edge a v → a ∈ ({P.x} : Finset V) := by
    intro v hv a ha
    rw [Finset.mem_singleton] at hv
    subst hv
    exact absurd ha (hnp a)
  have hOY : P.Y ∪ {P.x} ⊆ O := by
    intro v hv
    rcases Finset.mem_union.mp hv with h1 | h1
    · obtain ⟨k, hk, hk'⟩ := P.mem_Y.mp h1
      rw [← hk']
      exact hY k hk
    · rw [Finset.mem_singleton.mp h1]
      exact hx
  have huYx : ∀ j, P.u j ∉ P.Y ∪ {P.x} := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h1
    · obtain ⟨k, _, hk⟩ := P.mem_Y.mp h1
      exact P.hund j k hk.symm
    · exact P.hux' j (Finset.mem_singleton.mp h1)
  have huY : ∀ j, P.u j ∉ P.Y := fun j hj => huYx j (Finset.mem_union_left _ hj)
  have hC1 := P.ancC (P.Y ∪ {P.x})
    (fun k hk => Finset.mem_union_left _ (P.mem_Y.mpr ⟨k, hk, rfl⟩)) huYx
  have hC2 := P.ancC P.Y (fun k hk => P.mem_Y.mpr ⟨k, hk, rfl⟩) huY
  have hxS : P.x ∈ P.Y ∪ {P.x} := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have h2 : ∀ a : Assignment (α := fun _ : V => Bool) P.Y,
      P.NC.marginal P.Y a = ∏ v ∈ P.Y, c2 := by
    intro a
    rw [marginal_ancestral_apply _ _ hC2, P.prodY _ _ hC2 (fun v hv => hv)]
  have h3 : ∀ a : Assignment (α := fun _ : V => Bool) {P.x}, P.NB.marginal {P.x} a = c2 := by
    intro a
    rw [marginal_ancestral_apply _ {P.x} hSx, Finset.prod_singleton,
      kfac_of_mem _ {P.x} _ P.x (Finset.mem_singleton_self _)
        (DAG.parents_subset_of_closed hSx P.x (Finset.mem_singleton_self _)),
      P.NB_o P.hndx (fun e => P.hux' 0 e.symm), PMF.uniformOfFintype_apply]
  have key : ∀ b : Bool, (∏ v ∈ P.Y, c2) * Bow.chan true b = (∏ v ∈ P.Y, c2) * c2 := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) (P.Y ∪ {P.x}) :=
      fun v => if v.1 = P.x then b else if v.1 = P.nd P.r then true else false
    have htx : t.restrict (show ({P.x} : Finset V) ⊆ P.Y ∪ {P.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = P.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hat : ∀ k (hk : P.nd k ∈ P.Y ∪ {P.x}),
        ofBool (t ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0 := by
      intro k hk
      show ofBool (if P.nd k = P.x then b else if P.nd k = P.nd P.r then true else false) = _
      rw [if_neg (P.hndx k)]
      by_cases h0 : k = P.r
      · subst h0
        simp [ZMod2.ofBool]
      · rw [if_neg (fun e => h0 (P.ndinj e)), if_neg h0]
        all_goals rfl
    have htxv : t ⟨P.x, hxS⟩ = b := by simp [t]
    have h1 : P.NC.marginal (P.Y ∪ {P.x}) t = (∏ v ∈ P.Y, c2) * Bow.chan true b := by
      rw [marginal_ancestral_apply _ _ hC1 t, Finset.prod_union hYX, Finset.prod_singleton,
        P.prodY _ t hC1 (fun v hv => Finset.mem_union_left _ hv), P.Cx_val _ t hC1 hxS hat, htxv]
    -- identifiability
    have e := h P.mA P.mB (P.obsEq O hu) (P.posA O hu hY) t
    rw [htx, P.doA,
      Completeness.marginal_eq_of_kfac (doModel P.mB {P.x} _) (doModel P.NB {P.x} _)
        (Completeness.kfac_doModel_liftSub P.hsB P.NB {P.x} _) P.Y] at e
    -- the first front-door step in model B
    have fd := Adjustment.frontdoor_step1 P.NB {P.x} P.Y hYX
      (Completeness.dsep_isolated hnp P.Y hxY) t
    rw [htx, ← e] at fd
    rw [show P.NB.marginal (P.Y ∪ {P.x}) = P.NC.marginal (P.Y ∪ {P.x}) from by
      rw [← Completeness.marginal_eq_of_kfac P.mB P.NB (Completeness.kfac_liftSub P.hsB P.NB),
        ← marginal_eq_of_subset (P.obsEq O hu) hOY, margAC]] at fd
    rw [P.margAC, h1, h2, h3] at fd
    exact fd
  have k := (key true).trans (key false).symm
  have hQ0 : (∏ v ∈ P.Y, c2) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp [c2])
  have hQT : (∏ v ∈ P.Y, c2) ≠ ⊤ := by
    exact ENNReal.prod_ne_top (fun _ _ => by simp [c2])
  have hc : Bow.chan true true = Bow.chan true false := by
    exact (ENNReal.mul_right_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (false = true) by decide)] at hc
  exact Bow.q_ne hc

end RP

/-- **Roots along a path.** As `multiRoot_not_identifiable`, but `x` points into an
arbitrary root `nd_r`, and a path of latents from `u₀` to `u_r` is given. -/
theorem rootPath_not_identifiable {G : DAG V} {n : ℕ} (P : RP G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  P.not_ident O hu hY hx

/-- The configuration `MultiRoot.MR` is the special case `r = 0` with the path `{u₀}`. -/
theorem multiRoot_of_rootPath {G : DAG V} {n : ℕ} (P : MultiRoot.MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y := by
  have hpk : ∀ k, ofBool (decide (k = 0)) +
      (∑ j, if P.bp j = some k then ofBool (decide (j = 0)) else 0) = if k = 0 then 1 else 0 := by
    intro k
    have hz : (∑ j, if P.bp j = some k then ofBool (decide (j = 0)) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : j = 0
      · subst hj
        rw [(P.hbp0 0).mpr rfl]
        simp
      · simp [hj, ZMod2.ofBool]
    rw [hz, add_zero]
    by_cases hk : k = 0 <;> simp [hk, ZMod2.ofBool]
  let Q : RP G n :=
    { x := P.x, nd := P.nd, u := P.u, bp := P.bp, ht := P.ht, dp := P.dp, r := 0,
      pth := fun k => decide (k = 0), hbp0 := P.hbp0, hht := P.hht, hr := P.hdp0,
      hp0 := by simp, hpk := hpk, hux := P.hux, hun := P.hun, hub := P.hub, hdp := P.hdp,
      hxr := P.hxr, ndinj := P.ndinj, uinj := P.uinj, hund := P.hund, hux' := P.hux',
      hndx := P.hndx }
  exact rootPath_not_identifiable Q O hu hY hx

end RootPath
end Identification

#print axioms Identification.RootPath.rootPath_not_identifiable
#print axioms Identification.RootPath.multiRoot_of_rootPath

/-! ### Several roots as a corollary of root paths -/

namespace Identification
namespace MultiRoot

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **C-forest with several roots.** A latent tree that binds `x` (through `u₀`) to the
nodes `nd₀, …, nd_{n+1}`, with `x → nd₀`, and a directed forest pattern among the nodes.
If the roots and `x` are observed and the latents are not, then `P(roots | do(x))` is not
identifiable. -/
theorem multiRoot_not_identifiable {G : DAG V} {n : ℕ} (P : MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  RootPath.multiRoot_of_rootPath P O hu hY hx

end MultiRoot
end Identification

#print axioms Identification.MultiRoot.multiRoot_not_identifiable
