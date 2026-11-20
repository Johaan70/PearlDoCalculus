import PearlDoCalculus.Identification.RootPathModels

/-!
# Non-identifiability along a root path

This file finishes the argument for c-forests with several roots. It proves that the
models A and C of `Identification/RootPathModels` have the same joint distribution,
and gives the bijection between the models A and B. From this it follows that
`P(roots | do(x))` is not identifiable.

Main results:
* `RootPath.rootPath_not_identifiable`: the theorem for `RootPath.RP`, where `x` may
  point into any root `nd_r` and a latent path from `u₀` to `u_r` is given.
* `RootPath.multiRoot_of_rootPath`: round 14 is the special case `r = 0` of round 15.
* `MultiRoot.multiRoot_not_identifiable`: the corollary for `MultiRoot.MR`.

(The comments of the rounds below are still in Norwegian.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

namespace Identification
namespace RootPath

open HedgeChain (ev xx xb chan_symm)
open PathTree (b2z z2b b2z_z2b eq_z2b b2z_xor b2z_inj two)
open LatentTree (Lrearr)

variable {V : Type*} [DecidableEq V] [Fintype V]

open MultiRoot (ext ext_restrict chan_mix)

namespace RP

variable {G : DAG V} {n : ℕ} (P : RP G n)

/-! ### A og C har samme fellesfordeling -/

lemma joint_AC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.NC.fullJoint s = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, BowGen.kfac_liftG]
  rw [P.prod_split, P.prod_split]
  have hR : ∏ v ∈ P.R5, kfac P.NC Finset.univ s v = ∏ v ∈ P.R5, kfac P.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [P.C_o s v hv, P.A_o s v hv])
  rw [hR, P.C_x, P.A_x]
  simp only [P.C_u, P.A_u, P.C_nd, P.A_nd]
  by_cases hE : ∀ k, ev s (P.nd k) = z2b (P.parZ k (ev s))
  · have hsol := (P.keyAC s).mp hE
    have h0 : ev s (P.u 0) = z2b (∑ k ∈ P.Rt, b2z (ev s (P.nd k))) := by
      apply b2z_inj
      rw [b2z_z2b]
      exact P.eqs_sum (fun k => b2z (ev s (P.u k))) (fun k => b2z (ev s (P.nd k)))
        (fun k => (eq_z2b _ _).mp (hE k))
    have hU : ∏ j, PMF.pure (z2b (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) = 1 :=
      Finset.prod_eq_one (fun j _ => pure1 (hsol j))
    have hN : ∏ k, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k _ => pure1 (hE k))
    rw [hU, hN, h0]
    ring
  · have hsol : ¬ ∀ j, ev s (P.u j) = z2b (P.solN (P.Rg (ev s)) (P.M + 1) j) :=
      fun h => hE ((P.keyAC s).mpr h)
    push_neg at hE hsol
    obtain ⟨k, hk⟩ := hE
    obtain ⟨j, hj⟩ := hsol
    have hU : ∏ j, PMF.pure (z2b (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (pure0 hj)
    have hN : ∏ k, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (pure0 hk)
    rw [hU, hN]
    simp

lemma margAC (T : Finset V) : P.mA.marginal T = P.NC.marginal T := by
  have hj : P.NC.fullJoint = P.mA.fullJoint := PMF.ext (P.joint_AC)
  unfold CausalModel.marginal
  rw [hj]

/-! ### Bijeksjonen mellom A og B -/

noncomputable def Sb (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) : Bool :=
  z2b (∑ k ∈ P.Rt, b2z (ev s (P.nd k)))

/-- Bijeksjonen: hver latent på stien flyttes med summen over røttene. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if ∃ j, P.pth j = true ∧ P.u j = v.1 then xor (s v) (P.Sb s) else s v

lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : P.pth j = true) : ev (P.φ s) (P.u j) = xor (ev s (P.u j)) (P.Sb s) := by
  have h : ∃ j', P.pth j' = true ∧ P.u j' = P.u j := ⟨j, hj, rfl⟩
  simp only [φ, ev, if_pos h]

lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, P.pth j = true → P.u j ≠ v) : ev (P.φ s) v = ev s v := by
  have h : ¬ ∃ j, P.pth j = true ∧ P.u j = v := fun ⟨j, hj, e⟩ => hv j hj e
  simp only [φ, ev, if_neg h]

lemma φ_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev (P.φ s) (P.nd k) = ev s (P.nd k) := P.φ_o s (fun j _ => P.hund j k)

lemma φ_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ev (P.φ s) P.x = ev s P.x := P.φ_o s (fun j _ => P.hux' j)

/-- `φ` i `ZMod 2`: latent `j` flyttes med `pth j · ΣR`. -/
lemma bz_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    b2z (ev (P.φ s) (P.u j)) = b2z (ev s (P.u j)) + b2z (P.pth j) * b2z (P.Sb s) := by
  cases hj : P.pth j
  · rw [P.φ_o s (fun j' hj' e => by rw [P.uinj e, hj] at hj'; exact Bool.false_ne_true hj')]
    simp [b2z]
  · rw [P.φ_u s j hj, b2z_xor]
    simp [b2z]

lemma Sb_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.Sb (P.φ s) = P.Sb s := by
  unfold Sb
  simp only [P.φ_nd]

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

/-- **Stivilkåret i bruk:** pariteten endres bare i `nd_r`. -/
lemma parZ_φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.parZ k (ev (P.φ s)) = P.parZ k (ev s) + (if k = P.r then 1 else 0) * b2z (P.Sb s) := by
  have e1 : (∑ j, if P.bp j = some k then b2z (ev (P.φ s) (P.u j)) else 0) =
      (∑ j, if P.bp j = some k then b2z (ev s (P.u j)) else 0) +
        (∑ j, if P.bp j = some k then b2z (P.pth j) else 0) * b2z (P.Sb s) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · exact P.bz_φ s j
    · simp
  have e2 : (∑ j, if P.dp j = some k then b2z (ev (P.φ s) (P.nd j)) else 0) =
      ∑ j, if P.dp j = some k then b2z (ev s (P.nd j)) else 0 := by
    simp only [P.φ_nd]
  unfold parZ
  rw [P.bz_φ s k, e1, e2, ← P.hpk k]
  ring

lemma joint_BA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.mB.fullJoint (P.φ s) = P.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
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
      Bow.chan (xor (ev s P.x) (z2b (P.parZ P.r (ev s) + b2z (P.Sb s)))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r), P.B_ndr, P.parZ_φ, if_pos (rfl : P.r = P.r),
      one_mul, P.φ_x, P.φ_nd]
    congr 1
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk' := Finset.ne_of_mem_erase hk
    rw [P.B_nd _ k hk', P.parZ_φ, if_neg hk', zero_mul, add_zero, P.φ_nd]
  have hAn : ∏ k, kfac P.NA Finset.univ s (P.nd k) =
      PMF.pure (z2b (P.parZ P.r (ev s))) (ev s (P.nd P.r)) *
        ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P.r)]
    simp only [P.A_nd]
  rw [hR, P.B_x, P.A_x, hBu, hAu, hBn, hAn]
  by_cases hrest : ∀ k ∈ Finset.univ.erase P.r, ev s (P.nd k) = z2b (P.parZ k (ev s))
  · have hN : ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 1 :=
      Finset.prod_eq_one (fun k hk => pure1 (hrest k hk))
    rw [hN]
    have hiff := P.eqr_iff (fun k => b2z (ev s (P.u k))) (fun k => b2z (ev s (P.nd k)))
      (fun k hk => (eq_z2b _ _).mp (hrest k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)))
    by_cases h0 : ev s (P.u 0) = P.Sb s
    · have he0 : ev s (P.nd P.r) = z2b (P.parZ P.r (ev s)) := by
        apply (eq_z2b _ _).mpr
        apply hiff.mpr
        show b2z (ev s (P.u 0)) = _
        rw [h0, Sb, b2z_z2b]
      have hxf : xor (ev s (P.u 0)) (P.Sb s) = false := by
        rw [h0]
        exact Bool.xor_self _
      rw [pure1 he0, pure1 hxf, z2b_add, ← he0, chan_mix, ← h0]
      ring
    · have he0 : ¬ ev s (P.nd P.r) = z2b (P.parZ P.r (ev s)) := by
        intro he
        apply h0
        apply b2z_inj
        rw [Sb, b2z_z2b]
        exact hiff.mp ((eq_z2b _ _).mp he)
      have hx0 : ¬ xor (ev s (P.u 0)) (P.Sb s) = false := fun hf => h0 (xb _ _ hf)
      rw [pure0 he0, pure0 hx0]
      simp
  · push_neg at hrest
    obtain ⟨k, hk, hi⟩ := hrest
    have hN : ∏ k ∈ Finset.univ.erase P.r, PMF.pure (z2b (P.parZ k (ev s))) (ev s (P.nd k)) = 0 :=
      Finset.prod_eq_zero hk (pure0 hi)
    rw [hN]
    simp

lemma full_map : P.mB.fullJoint = P.mA.fullJoint.map P.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (P.φ s)]
  · rw [if_pos (P.φ_invol s).symm, ← P.joint_BA (P.φ s), P.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, P.φ_invol]

lemma obsEq (O : Finset V) (hu : ∀ j, P.u j ∉ O) : P.mA.marginal O = P.mB.marginal O := by
  unfold CausalModel.marginal
  rw [P.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv0 : ∀ j, P.pth j = true → P.u j ≠ v := fun j _ e => hu j (by rw [e]; exact hv)
  exact (P.φ_o s hv0).symm

/-! ### Utregninger i C og B -/

lemma pOf {H : DAG V} {S : Finset V} (hS : ∀ v ∈ S, ∀ w, H.edge w v → w ∈ S)
    (v : V) (hv : v ∈ S) : H.parents v ⊆ S := fun w hw => hS v hv w (by
  simpa [DAG.parents] using hw)

lemma ancC (S : Finset V) (hR : ∀ k, P.dp k = none → P.nd k ∈ S) (hu : ∀ j, P.u j ∉ S) :
    ∀ v ∈ S, ∀ a, P.gC.edge a v → a ∈ S := by
  intro v hv a ha
  rcases (P.eC a v).mp ha with ⟨k, hk, h1, _⟩ | ⟨k, j, _, h2⟩
  · rw [h1]
    exact hR k hk
  · exact absurd (by rw [← h2]; exact hv) (hu j)

lemma prodY (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hYS : ∀ v ∈ P.Y, v ∈ S) :
    ∏ v ∈ P.Y, kfac P.NC S a v = ∏ v ∈ P.Y, c2 := by
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hvS := hYS v hv
  obtain ⟨k, _, hk⟩ := P.mem_Y.mp hv
  have hvx : v ≠ P.x := by rw [← hk]; exact P.hndx k
  have hvu : ∀ j, P.u j ≠ v := by rw [← hk]; exact fun j => P.hund j k
  rw [BowGen.kfac_eqG _ S a v hvS (pOf hS v hvS), P.NC_o hvx hvu, PMF.uniformOfFintype_apply]

lemma Cx_val (S : Finset V) (a : Assignment (α := fun _ : V => Bool) S)
    (hS : ∀ v ∈ S, ∀ w, P.gC.edge w v → w ∈ S) (hxS : P.x ∈ S)
    (ha : ∀ k (hk : P.nd k ∈ S), b2z (a ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0) :
    kfac P.NC S a P.x = Bow.chan true (a ⟨P.x, hxS⟩) := by
  have hz : z2b (∑ k ∈ P.Rt, b2z (ext (a.restrict (pOf hS P.x hxS)) (P.nd k))) = true := by
    have hs : ∀ k ∈ P.Rt, b2z (ext (a.restrict (pOf hS P.x hxS)) (P.nd k)) =
        if k = P.r then 1 else 0 := by
      intro k hk
      have hp : P.nd k ∈ P.gC.parents P.x := P.pCx k (by simpa [Rt] using hk)
      have he : ext (a.restrict (pOf hS P.x hxS)) (P.nd k) = a ⟨P.nd k, pOf hS P.x hxS hp⟩ := by
        simp [MultiRoot.ext, hp, Assignment.restrict]
      rw [he]
      exact ha k (pOf hS P.x hxS hp)
    rw [Finset.sum_congr rfl hs]
    rw [Finset.sum_ite_eq', if_pos P.mem_Rtr]
    all_goals rfl
  rw [BowGen.kfac_eqG _ S a P.x hxS (pOf hS P.x hxS), P.NC_x, hz]

lemma posA (O : Finset V) (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) :
    ∀ a, P.mA.marginal O a ≠ 0 := by
  intro a
  have hS := P.ancC O hY hu
  rw [P.margAC O, marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (pOf hS v hv)]
  have hvu : ∀ j, P.u j ≠ v := fun j e => hu j (by rw [e]; exact hv)
  by_cases hvx : v = P.x
  · subst hvx
    rw [P.NC_x]
    exact Bow.chan_ne_zero _ _
  · rw [P.NC_o hvx hvu]
    simp [PMF.uniformOfFintype_apply]

lemma doA (x0 : Assignment (α := fun _ : V => Bool) {P.x})
    (y0 : Assignment (α := fun _ : V => Bool) P.Y) :
    (doModel P.mA {P.x} x0).marginal P.Y y0 = P.mA.marginal P.Y y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel P.mA {P.x} x0) (doModel P.NA {P.x} x0)
    (BowGen.kfac_lift_doG P.hsA P.NA {P.x} x0) P.Y]
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
    ← Completeness.marginal_eq_of_kfac P.mA P.NA (BowGen.kfac_liftG P.hsA P.NA) P.Y]

/-- **Flere røtter: `P(R | do(x))` er ikke identifiserbar.** -/
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
      BowGen.kfac_eqG _ {P.x} _ P.x (Finset.mem_singleton_self _)
        (pOf hSx P.x (Finset.mem_singleton_self _)),
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
    have hat : ∀ k (hk : P.nd k ∈ P.Y ∪ {P.x}), b2z (t ⟨P.nd k, hk⟩) = if k = P.r then 1 else 0 := by
      intro k hk
      show b2z (if P.nd k = P.x then b else if P.nd k = P.nd P.r then true else false) = _
      rw [if_neg (P.hndx k)]
      by_cases h0 : k = P.r
      · subst h0
        simp [b2z]
      · rw [if_neg (fun e => h0 (P.ndinj e)), if_neg h0]
        all_goals rfl
    have htxv : t ⟨P.x, hxS⟩ = b := by simp [t]
    have h1 : P.NC.marginal (P.Y ∪ {P.x}) t = (∏ v ∈ P.Y, c2) * Bow.chan true b := by
      rw [marginal_ancestral_apply _ _ hC1 t, Finset.prod_union hYX, Finset.prod_singleton,
        P.prodY _ t hC1 (fun v hv => Finset.mem_union_left _ hv), P.Cx_val _ t hC1 hxS hat, htxv]
    -- Identifiserbarheten
    have e := h P.mA P.mB (P.obsEq O hu) (P.posA O hu hY) t
    rw [htx, P.doA,
      Completeness.marginal_eq_of_kfac (doModel P.mB {P.x} _) (doModel P.NB {P.x} _)
        (BowGen.kfac_lift_doG P.hsB P.NB {P.x} _) P.Y] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 P.NB {P.x} P.Y hYX
      (Completeness.dsep_isolated hnp P.Y hxY) t
    rw [htx, ← e] at fd
    rw [show P.NB.marginal (P.Y ∪ {P.x}) = P.NC.marginal (P.Y ∪ {P.x}) from by
      rw [← Completeness.marginal_eq_of_kfac P.mB P.NB (BowGen.kfac_liftG P.hsB P.NB),
        ← marginal_eq_of_sub (P.obsEq O hu) hOY, margAC]] at fd
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

/-- **Røtter langs en sti.** Som `multiRoot_not_identifiable`, men `x` peker inn i
en vilkårlig rot `nd_r`, og en sti av latente fra `u₀` til `u_r` er gitt. -/
theorem rootPath_not_identifiable {G : DAG V} {n : ℕ} (P : RP G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  P.not_ident O hu hY hx

/-- Runde 14 er spesialtilfellet `r = 0` med stien `{u₀}`. -/
theorem multiRoot_of_rootPath {G : DAG V} {n : ℕ} (P : MultiRoot.MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y := by
  have hpk : ∀ k, b2z (decide (k = 0)) +
      (∑ j, if P.bp j = some k then b2z (decide (j = 0)) else 0) = if k = 0 then 1 else 0 := by
    intro k
    have hz : (∑ j, if P.bp j = some k then b2z (decide (j = 0)) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : j = 0
      · subst hj
        rw [(P.hbp0 0).mpr rfl]
        simp
      · simp [hj, b2z]
    rw [hz, add_zero]
    by_cases hk : k = 0 <;> simp [hk, b2z]
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

/-! ### Runde 14 som korollar av runde 15 -/

namespace Identification
namespace MultiRoot

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **c-skog med flere røtter.** Et latent tre som binder `x` (gjennom `u₀`) til
nodene `nd₀, …, nd_{n+1}`, med `x → nd₀`, og et rettet skog-mønster blant nodene.
Er røttene og `x` observert og de latente uobservert, er `P(røtter | do(x))` ikke
identifiserbar. -/
theorem multiRoot_not_identifiable {G : DAG V} {n : ℕ} (P : MR G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hY : ∀ k, P.dp k = none → P.nd k ∈ O) (hx : P.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} P.Y :=
  RootPath.multiRoot_of_rootPath P O hu hY hx

end MultiRoot
end Identification

#print axioms Identification.MultiRoot.multiRoot_not_identifiable
