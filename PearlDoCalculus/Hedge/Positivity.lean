import PearlDoCalculus.Hedge.ObsEq

/-!
# Positivity of the parity model `M1` (step H3)

This file proves `PM.pos_M1`: in the parity model `M1` on a hedge (`PM.M` with
`two = false`, from `Hedge/ParityModels.lean`), every assignment to a set of observed
nodes has positive probability.

**Why.** Identifiability, as defined in `Identification`, only constrains models whose
observed distribution is positive. Two models with the same observed distribution
(`PM.marg_eq`, in `Hedge/ObsEq.lean`) witness non-identifiability only if that
distribution is positive. By `PM.marg_eq` it is enough to prove this for `M1`.
`pos_M1` is used in `Hedge/Roots` (step H3) and for the product models in
`Hedge/Product` (step H4, together with `noise_pos`); the general shift lemma `obs_shE` is
reused, with `lb_shE` from `Hedge/ObsEq`, for the flip `ψ` in `Hedge/DoGapM1`.

**How.** Given an observed assignment `a` on `O`, the proof builds one full assignment
that extends `a` and has a nonzero product of kernel factors.

1. *Start and shift.* `baseA a` is `a` on `O` and `0` elsewhere. It is shifted along the
   whole tree for `F'` by bits `b`, using the shift `sh` with an arbitrary edge set
   (`lb_shE` of `Hedge/ObsEq`, `obs_shE`). The shift changes no observed value. At the shifted assignment
   the bit of `M1` at `v ∈ F'` is the incidence value `inc b v` plus the values of the
   `nxt` children of `v` (`sbV_base`).
2. *Choose the bits.* Let the target `tauP` be the value of `v` plus the values of its
   `nxt` children (`sigA`) for `v ≠ r0`, and at the noisy root `r0` whatever makes the
   total sum zero (`tauP_sum`). Then `inc_surj` on the tree for `F'` gives bits `b` with
   `inc b = tauP`.
3. *All factors are positive.* Latent nodes and nodes outside `F'` have uniform factors.
   Every observed node of `F'` other than `r0` satisfies its equation, so its factor is
   `1`. At `r0` the noise absorbs the difference, and both noise values have positive
   probability (`noise_pos`).

**Main results.** `PM.noise_pos`, `PM.sbV_base`, `PM.pos_M1`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Positivity in `M1`

`noise_pos`: both noise values have positive probability. `obs_shE` (with `lb_shE` of
`Hedge/ObsEq`): the shift `sh` with an arbitrary edge set `E` (here the whole `F'`-tree). `baseA a`: `a` on `O`,
else 0. `sbV_base`: at `sh U F' D b (baseA a)` the `M1` bit of `v ∈ F'` is `inc b v` plus
the values of the `nxt` children. `pos_M1`: choose `τ v` = the value of `v` plus the
values of its `nxt` children for `v ≠ r0`, and `τ r0` so that `Σ τ = 0`; `inc_surj` on the
`F'`-tree gives the bits `b`. Then every equation holds except at `r0`, and there the
noise absorbs the difference; so every `a` has positive probability. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Both noise values have positive probability. -/
lemma noise_pos (n : ZMod 2) : noise n ≠ 0 := by
  rw [← PMF.mem_support_iff]
  unfold noise
  rw [PMF.support_map, PMF.support_uniformOfFintype]
  obtain ⟨i, hi⟩ := (show ∀ m : ZMod 2, ∃ i : Fin 4, (if i = 0 then (1 : ZMod 2) else 0) = m by
    decide) n
  exact ⟨i, Set.mem_univ _, hi⟩

section posM1

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- The shift along the tree edges of `E` keeps every observed value, when the latents
behind those edges are latent. -/
lemma obs_shE (E : Finset V) (hE : ∀ c ∈ EF U E D, D.lat c ∈ U) (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V} (hu : u ∉ U) :
    sh U E D t s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ := by
  funext i
  simp only [sh]
  rw [Finset.sum_eq_zero, add_zero]
  intro c hc
  exfalso
  obtain ⟨hcE, hlat, -⟩ := Finset.mem_filter.mp hc
  have hl := hE c hcE
  rw [hlat] at hl
  exact hu hl

/-- Under `Good`, the latent behind every tree edge of `F'` is latent. -/
lemma EF_lat (hD : Good G U F F' D) : ∀ c ∈ EF U F' D, D.lat c ∈ U := fun c hc => by
  obtain ⟨hcF', hcU, hcρ⟩ := Finset.mem_filter.mp hc
  exact (hD.lat c hcF' hcU hcρ).1

/-- The base assignment: `a` on `O`, `0` elsewhere. -/
def baseA {O : Finset V} (a : Assignment (α := Val U) O) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u => if h : u.1 ∈ O then a ⟨u.1, h⟩ else 0

/-- At the base assignment every tree bit is `0` (latent nodes are outside `O`). -/
lemma lb_base {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) (a : Assignment (α := Val U) O) {c : V}
    (hl : D.lat c ∈ U) : lb U D (baseA U a) c = 0 := by
  have hn : D.lat c ∉ O := fun h => hO _ h hl
  have h0 : baseA U a ⟨D.lat c, Finset.mem_univ _⟩ = 0 := dif_neg hn
  unfold lb
  rw [h0]
  unfold rd
  split_ifs <;> rfl

/-- At the base assignment shifted by `b` along the `F'`-tree, the `M1` bit of an
observed `v ∈ F'` is the incidence value `inc b v` plus the values of its `nxt`
children. -/
theorem sbV_base (hD : Good G U F F' D) {O : Finset V} (hO : ∀ v ∈ O, v ∉ U)
    (a : Assignment (α := Val U) O) (b : V → ZMod 2) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D false (sh U F' D b (baseA U a)) v =
      inc (OF U F') D.ρ D.par b v + ∑ w ∈ NX G U F F' v, ov U (baseA U a) w := by
  have hE := EF_lat G U F F' D hD
  have hlb : ∀ c ∈ F', c ∉ U → c ≠ D.ρ → lb U D (sh U F' D b (baseA U a)) c = b c := by
    intro c hcF' hcU hcρ
    rw [lb_shE U D F' b _ (hD.lat c hcF' hcU hcρ).1, lb_base U D hO a (hD.lat c hcF' hcU hcρ).1,
      if_pos (show c ∈ EF U F' D from Finset.mem_filter.mpr ⟨hcF', hcU, hcρ⟩), zero_add]
  have hown : (if v = D.ρ then 0 else lb U D (sh U F' D b (baseA U a)) v) =
      (if v = D.ρ then 0 else b v) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ]
    · rw [if_neg hρ, if_neg hρ, hlb v hvF' hvU hρ]
  have hset : CH U F' D v = (OF U F').filter (fun c => c ≠ D.ρ ∧ D.par c = v) := by
    ext c
    simp only [CH, OF, Finset.mem_filter]
    tauto
  have hch : ∑ c ∈ CH U F' D v, lb U D (sh U F' D b (baseA U a)) c =
      ∑ c ∈ (OF U F').filter (fun c => c ≠ D.ρ ∧ D.par c = v), b c := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcρ, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU⟩ := Finset.mem_filter.mp hc1
    exact hlb c hcF' hcU hcρ
  have hnx : ∑ w ∈ NX G U F F' v, ov U (sh U F' D b (baseA U a)) w =
      ∑ w ∈ NX G U F F' v, ov U (baseA U a) w := by
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw
    unfold ov
    rw [obs_shE U D F' hE b _ hwU]
  unfold sbV inc
  rw [scope_false, filter_univ, filter_univ, hown, hch, hnx]

/-- The right-hand side of the equations without `inc`: the value of `v` plus the
values of its `nxt` children. -/
noncomputable def sigA {O : Finset V} (a : Assignment (α := Val U) O) (v : V) : ZMod 2 :=
  ov U (baseA U a) v + ∑ w ∈ NX G U F F' v, ov U (baseA U a) w

/-- The target for `inc_surj`: `sigA` away from `r0`, and at `r0` whatever makes the
sum `0`. -/
noncomputable def tauP {O : Finset V} (a : Assignment (α := Val U) O) (v : V) : ZMod 2 :=
  if v = D.r0 then ∑ u ∈ (OF U F').erase D.r0, sigA G U F F' a u else sigA G U F F' a v

/-- The target `tauP` sums to zero over the observed part of `F'`. -/
lemma tauP_sum {O : Finset V} (a : Assignment (α := Val U) O) (hr : D.r0 ∈ OF U F') :
    ∑ v ∈ OF U F', tauP G U F F' D a v = 0 := by
  rw [← Finset.add_sum_erase (OF U F') (tauP G U F F' D a) hr]
  have h : ∑ v ∈ (OF U F').erase D.r0, tauP G U F F' D a v =
      ∑ v ∈ (OF U F').erase D.r0, sigA G U F F' a v := by
    apply Finset.sum_congr rfl
    intro v hv
    unfold tauP
    rw [if_neg (Finset.ne_of_mem_erase hv)]
  rw [h]
  unfold tauP
  rw [if_pos rfl, CharTwo.add_self_eq_zero]

/-- **Positivity**: every observed assignment has positive probability in `M1`. -/
theorem pos_M1 {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    {d : V → ℕ} (T : ParTree (OF U F') D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) (a : Assignment (α := Val U) O) :
    (M G U F F' D false).marginal O a ≠ 0 := by
  have hE := EF_lat G U F F' D hD
  have hr0 : D.r0 ∈ OF U F' :=
    Finset.mem_filter.mpr ⟨hH.sub (Finset.mem_filter.mp hD.r0R).1, hD.r0U⟩
  obtain ⟨b, hb⟩ := inc_surj (OF U F').card (OF U F') (tauP G U F F' D a) rfl T
    (tauP_sum G U F F' D a hr0)
  have hrestr : (sh U F' D b (baseA U a)).restrict (Finset.subset_univ O) = a := by
    funext ⟨v, hv⟩
    show sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩
    rw [obs_shE U D F' hE b _ (hO v hv)]
    exact dif_pos hv
  have hj : (M G U F F' D false).fullJoint (sh U F' D b (baseA U a)) ≠ 0 := by
    rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff]
    intro v _
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D false _ hvU]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D false _ hvU hvF']
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    by_cases hr : v = D.r0
    · rw [kfac_r0 G U F F' D false _ hvU hvF' hr]
      exact noise_pos _
    have hov : rd (sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩) 0 = ov U (baseA U a) v := by
      unfold ov
      rw [obs_shE U D F' hE b _ hvU]
    have heq : rd (sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩) 0 =
        sb G U F F' D false v (rdS G U (sh U F' D b (baseA U a)) v) := by
      rw [sb_read G U F F' D false hH hD _ hvF' hvU, sbV_base G U F F' D hD hO a b hvF' hvU,
        hb v (Finset.mem_filter.mpr ⟨hvF', hvU⟩), hov]
      unfold tauP sigA
      rw [if_neg hr, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [kfac_obs G U F F' D false _ hvU hvF' hr, if_pos heq]
    exact one_ne_zero
  intro h0
  have hmem : a ∈ ((M G U F F' D false).marginal O).support := by
    unfold CausalModel.marginal
    rw [PMF.mem_support_map_iff]
    exact ⟨_, (PMF.mem_support_iff _ _).mpr hj, hrestr⟩
  exact (PMF.mem_support_iff _ _).mp hmem h0

end posM1

end PM
end Hedge
