import PearlDoCalculus.Hedge.ParityModels

/-!
# The two parity models have the same observed distribution (step H3)

This file proves `PM.marg_eq`: the parity models `M1` and `M2` on a hedge (`PM.M` with
`two = false` and `two = true`, defined in `Hedge/ParityModels.lean`) give the same
distribution on every set of observed nodes.

**Why.** A hedge blocks identification because these two models agree on everything that
can be observed but differ in the effect of `do(x)`. This file gives the first half; the
gap under `do(x)` comes later.

**How.** The proof builds an involution `phiS` on full assignments that keeps every
observed value and carries the joint distribution of `M1` to that of `M2`. Then
`marginal_eq_of_invol` gives equal marginals.

1. *The defect and the shift.* Inside `F`, the bit of `M1` is the bit of `M2` plus a defect
   `δ`, the terms `M1` counts and `M2` does not: tree children and `nxt` children outside `F`
   (`sbV_split`). Outside `F` the two bits agree (`sbV_out`). The shift `sh t` adds `t c`
   to the latent bit on each edge `(c, par c)` of the tree for `F` (`EF`). It changes no
   observed value (`sh_obs`) and is its own inverse (`sh_sh`).
2. *What the shift does to the bits.* The shift leaves `δ` unchanged (`δ_sh`) and adds the
   incidence value `incF t v` to the bit of `M2` at each `v ∈ F` (`sbV2_sh`). So if
   `incF t = δ`, the bits of `M2` at `sh t s` equal the bits of `M1` at `s`.
3. *The involution.* `incF` is the tree incidence `inc` on the observed part `OF` of `F`
   (`incF_eq_inc`). When `δ` sums to zero over `OF`, `inc_surj` gives a solution
   (`exists_shift`). `phiS s` shifts by a chosen solution, or by `0` if there is none. It
   is an involution because the shift does not change `δ`, so the same `t` is chosen
   both times (`phiS_invol`). It keeps the observed values (`phiS_restrict`).
4. *Equal factors.* When a solution exists, every kernel factor of `M2` at `phiS s` equals
   that of `M1` at `s` (`sbV1_sh_out`, `kfac_phiS`).
5. *Telescoping.* If every observed node of `F' \ F` (`Out`) satisfies its equation in
   `M1`, then `δ` sums to zero over `OF` (`tele`). The sum of `δ` collects the bits and
   values that flow from `Out` into `F`, and summing the equations over `Out` makes every
   tree bit appear twice. The bookkeeping lemmas are `fiber_sum`, `part_sum`, `CH_out`,
   `NX_out`, `CH_in_out`, `NX_in_out`, `par_cover` and `nxt_cover`.
6. *Equal joints.* If no solution exists, `δ` does not sum to zero, so by `tele` some
   node of `Out` breaks its equation. Then its factor is `0` in both models (`kfac_zero`),
   and `phiS s = s` (`phiS_fix`). In every case
   `M2.fullJoint (phiS s) = M1.fullJoint s` (`joint_phiS`), which gives `marg_eq`.

**Main results.** `PM.sbV_split`, `PM.sh_obs`, `PM.sbV2_sh`, `PM.exists_shift`,
`PM.phiS_invol`, `PM.phiS_restrict`, `PM.kfac_phiS`, `PM.tele`, `PM.joint_phiS`,
`PM.marg_eq`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 61: forskyvningen av `F`-trebitene

`δ s v`: leddene `M1` har i `v` og `M2` ikke har (trebarn og `nxt`-barn utenfor `F`).
`sbV_split`: i `F` er `M1`-biten lik `M2`-biten pluss `δ`; `sbV_out`: utenfor `F` er de like.
`EF`: trekantene i `F` (observerte `c ≠ ρ` i `F`). `sh t s`: legger `t c` til biten på hver
trekant `c ∈ EF` (komponent `ix c` i den latente `lat c`). `sh_obs`: observerte verdier
endres ikke; `lb_sh`: trebiten øker med `t c` nøyaktig for `c ∈ EF`; `sh_sh`: `sh t` er
sin egen invers. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section shift

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

lemma scope_false (v : V) : scope F false v = Finset.univ := by simp [scope]

lemma scope_true_in {v : V} (hv : v ∈ F) : scope F true v = F := by simp [scope, hv]

lemma scope_true_out {v : V} (hv : v ∉ F) : scope F true v = Finset.univ := by simp [scope, hv]

/-- Leddene `M1` har og `M2` ikke har. -/
noncomputable def δ (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∉ F), lb U D s c +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∉ F), ov U s w

lemma filter_univ (S : Finset V) : S.filter (fun c => c ∈ (Finset.univ : Finset V)) = S :=
  Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _)

/-- **I `F`: `M1`-biten = `M2`-biten + `δ`.** -/
theorem sbV_split (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ F) :
    sbV G U F F' D false s v = sbV G U F F' D true s v + δ G U F F' D s v := by
  unfold sbV δ
  first
    | rw [scope_false, scope_true_in F hv, filter_univ, filter_univ]
    | simp only [scope_false, scope_true_in F hv, Finset.mem_univ, Finset.filter_True]
  rw [← Finset.sum_filter_add_sum_filter_not (CH U F' D v) (fun c => c ∈ F),
    ← Finset.sum_filter_add_sum_filter_not (NX G U F F' v) (fun c => c ∈ F)]
  ring

/-- **Utenfor `F` er bitene like.** -/
theorem sbV_out (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ F) :
    sbV G U F F' D false s v = sbV G U F F' D true s v := by
  unfold sbV
  rw [scope_false, scope_true_out F hv]

/-- Trekantene i `F`. -/
def EF : Finset V := F.filter (fun c => c ∉ U ∧ c ≠ D.ρ)

/-- Forskyvningen av `F`-trebitene med `t`. -/
noncomputable def sh (t : V → ZMod 2) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u i => s u i + ∑ c ∈ (EF U F D).filter (fun c => D.lat c = u.1 ∧ ix c = i.val), t c

/-- **`sh t` er sin egen invers.** -/
lemma sh_sh (t : V → ZMod 2) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    sh U F D t (sh U F D t s) = s := by
  funext u i
  simp only [sh]
  rw [add_assoc, zmod2_add_self, add_zero]

/-- **Observerte verdier endres ikke.** -/
lemma sh_obs (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V} (hu : u ∉ U) :
    sh U F D t s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ := by
  funext i
  simp only [sh]
  rw [Finset.sum_eq_zero, add_zero]
  intro c hc
  exfalso
  obtain ⟨hcE, hlat, -⟩ := Finset.mem_filter.mp hc
  obtain ⟨hcF, hcU, hcρ⟩ := Finset.mem_filter.mp hcE
  have hl := (hD.lat c (hFF' hcF) hcU hcρ).1
  rw [hlat] at hl
  exact hu hl

/-- **Trebiten øker med `t c` nøyaktig for `c ∈ EF`.** -/
lemma lb_sh (hD : Good G U F F' D) (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {c : V} (hcF' : c ∈ F') (hcU : c ∉ U)
    (hcρ : c ≠ D.ρ) :
    lb U D (sh U F D t s) c = lb U D s c + (if c ∈ EF U F D then t c else 0) := by
  have hlU := (hD.lat c hcF' hcU hcρ).1
  have hk : ix c < kk U (D.lat c) := by
    rw [kk_lat hlU]
    exact ix_lt c
  unfold lb rd
  rw [dif_pos hk, dif_pos hk]
  simp only [sh]
  congr 1
  by_cases hc : c ∈ EF U F D
  · rw [if_pos hc]
    apply Finset.sum_eq_single c
    · intro b hb hbc
      exfalso
      obtain ⟨-, -, hix⟩ := Finset.mem_filter.mp hb
      exact hbc (ix_inj hix)
    · intro hn
      exfalso
      exact hn (Finset.mem_filter.mpr ⟨hc, rfl, rfl⟩)
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b hb
    exfalso
    obtain ⟨hbE, -, hix⟩ := Finset.mem_filter.mp hb
    have hbc : b = c := ix_inj hix
    rw [hbc] at hbE
    exact hc hbE

end shift

end PM
end Hedge

#print axioms Hedge.PM.sbV_split
#print axioms Hedge.PM.sh_obs
#print axioms Hedge.PM.lb_sh

/-! ## Runde 62: forskyvningen og bitene

`incF t v`: innfallsverdien til `t` i `F`-treet i `v` (kanten over `v` og kantene ned til
barna i `F`). `δ_sh`: forskyvningen endrer ikke `δ`, siden `δ` bare leser trekanter
utenfor `F` og observerte verdier. `sbV2_sh`: i `F` øker `M2`-biten med `incF t v`. Velges
`t` med `incF t = δ`, blir `M2`-biten av `sh t s` lik `M1`-biten av `s` i hele `F`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section shift2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- Innfallsverdien til `t` i `F`-treet. -/
noncomputable def incF (t : V → ZMod 2) (v : V) : ZMod 2 :=
  (if v = D.ρ then 0 else t v) + ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), t c

lemma ov_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V} (hw : w ∉ U) :
    ov U (sh U F D t s) w = ov U s w := by
  unfold ov
  rw [sh_obs G U F F' D hD hFF' t s hw]

/-- **Forskyvningen endrer ikke `δ`.** -/
theorem δ_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    δ G U F F' D (sh U F D t s) v = δ G U F F' D s v := by
  unfold δ
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcnF⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
    rw [lb_sh G U F F' D hD t s hcF' hcU hcρ,
      if_neg (show c ∉ EF U F D from fun h => hcnF (Finset.mem_filter.mp h).1), add_zero]
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU

/-- **I `F` øker `M2`-biten med `incF t v`.** -/
theorem sbV2_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∈ F) (hvU : v ∉ U) :
    sbV G U F F' D true (sh U F D t s) v = sbV G U F F' D true s v + incF U F F' D t v := by
  have hvF' := hFF' hvF
  have hown : (if v = D.ρ then 0 else lb U D (sh U F D t s) v) =
      (if v = D.ρ then 0 else lb U D s v) + (if v = D.ρ then 0 else t v) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ, if_pos hρ, add_zero]
    · rw [if_neg hρ, if_neg hρ, if_neg hρ, lb_sh G U F F' D hD t s hvF' hvU hρ,
        if_pos (show v ∈ EF U F D from Finset.mem_filter.mpr ⟨hvF, hvU, hρ⟩)]
  have hch : ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), lb U D (sh U F D t s) c =
      ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), lb U D s c +
        ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), t c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcF⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
    rw [lb_sh G U F F' D hD t s hcF' hcU hcρ, if_pos (show c ∈ EF U F D from Finset.mem_filter.mpr ⟨hcF, hcU, hcρ⟩)]
  have hnx : ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ F), ov U (sh U F D t s) w =
      ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ F), ov U s w := by
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU
  unfold sbV incF
  rw [scope_true_in F hvF]
  first
    | rw [hown, hch, hnx]
    | simp only [hown, hch, hnx]
  ring

end shift2

end PM
end Hedge

#print axioms Hedge.PM.δ_sh
#print axioms Hedge.PM.sbV2_sh

/-! ## Runde 63: involusjonen

`OF`: de observerte nodene i `F`. `incF_eq_inc`: `incF` er innfallsfunksjonen `inc` på `OF`
med rot `ρ`. `exists_shift`: er `F`-treet et `ParTree` og `Σ_{OF} τ = 0`, finnes `t` med
`incF t = τ` på `OF` (fra `inc_surj`). `tsel τ` velger en slik `t` (eller `0`), og
`phiS s = sh (tsel (δ s)) s`. `phiS_invol`: `phiS` er en involusjon, siden `δ` ikke endres av
forskyvningen og dermed velges samme `t` begge ganger. `phiS_restrict`: `phiS` endrer ingen
observerte verdier. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section invol

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- De observerte nodene i `F`. -/
def OF : Finset V := F.filter (fun v => v ∉ U)

lemma incF_eq_inc (hFF' : F ⊆ F') (t : V → ZMod 2) (v : V) :
    incF U F F' D t v = inc (OF U F) D.ρ D.par t v := by
  unfold incF inc
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [CH, OF, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, hU, hρ, hp⟩, hF⟩
    exact ⟨⟨hF, hU⟩, hρ, hp⟩
  · rintro ⟨⟨hF, hU⟩, hρ, hp⟩
    exact ⟨⟨hFF' hF, hU, hρ, hp⟩, hF⟩

/-- **Forskyvningen finnes** når `δ` summerer til null over `F`. -/
theorem exists_shift (hFF' : F ⊆ F') {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (τ : V → ZMod 2) (hτ : ∑ v ∈ OF U F, τ v = 0) :
    ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v := by
  obtain ⟨b, hb⟩ := inc_surj (OF U F).card (OF U F) τ rfl T hτ
  exact ⟨b, fun v hv => by rw [incF_eq_inc U F F' D hFF']; exact hb v hv⟩

open Classical in
/-- En forskyvning som løser `incF t = τ` på `OF`, når en finnes. -/
noncomputable def tsel (τ : V → ZMod 2) : V → ZMod 2 :=
  if h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v then Classical.choose h else 0

lemma tsel_spec (τ : V → ZMod 2)
    (h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v) :
    ∀ v ∈ OF U F, incF U F F' D (tsel U F F' D τ) v = τ v := by
  unfold tsel
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Involusjonen.** -/
noncomputable def phiS (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  sh U F D (tsel U F F' D (δ G U F F' D s)) s

theorem phiS_invol (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    phiS G U F F' D (phiS G U F F' D s) = s := by
  unfold phiS
  have h : δ G U F F' D (sh U F D (tsel U F F' D (δ G U F F' D s)) s) = δ G U F F' D s :=
    funext (δ_sh G U F F' D hD hFF' _ s)
  rw [h, sh_sh]

theorem phiS_restrict (hD : Good G U F F' D) (hFF' : F ⊆ F') {O : Finset V}
    (hO : ∀ v ∈ O, v ∉ U) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (phiS G U F F' D s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O) := by
  funext ⟨v, hv⟩
  exact sh_obs G U F F' D hD hFF' _ s (hO v hv)

end invol

end PM
end Hedge

#print axioms Hedge.PM.exists_shift
#print axioms Hedge.PM.phiS_invol
#print axioms Hedge.PM.phiS_restrict

/-! ## Runde 64: like faktorer når forskyvningen finnes

`sbV1_sh_out`: utenfor `F` leser `M1`-biten ingenting forskyvningen endrer (et trebarn av en
node utenfor `F` ligger selv utenfor `F`, siden `par` holder `F`). `kfac_phiS`: når
`tsel (δ s)` løser `incF t = δ s` på `OF`, er hver kjernefaktor i `M2` på `phiS s` lik
faktoren i `M1` på `s`: uniforme faktorer er like; i `F` er `M2`-biten + `incF t` =
`M2`-biten + `δ` = `M1`-biten; utenfor `F` er bitene like; observerte verdier er uendret. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section factors

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

theorem sbV1_sh_out (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∉ F) (hvF' : v ∈ F')
    (hvU : v ∉ U) :
    sbV G U F F' D false (sh U F D t s) v = sbV G U F F' D false s v := by
  unfold sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ, lb_sh G U F F' D hD t s hvF' hvU hρ,
          if_neg (show v ∉ EF U F D from fun h => hvF (Finset.mem_filter.mp h).1), add_zero]
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF', hcU, hcρ, hpc⟩ := Finset.mem_filter.mp hc1
      rw [lb_sh G U F F' D hD t s hcF' hcU hcρ,
        if_neg (show c ∉ EF U F D from fun h =>
          hvF (hpc ▸ hD.parF c (Finset.mem_filter.mp h).1 hcU hcρ)), add_zero]
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU

/-- **Like faktorer** når forskyvningen løser `incF t = δ s`. -/
theorem kfac_phiS {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hsol : ∀ v ∈ OF U F, incF U F F' D (tsel U F F' D (δ G U F F' D s)) v = δ G U F F' D s v)
    (v : V) :
    kfac (M G U F F' D true) Finset.univ (phiS G U F F' D s) v =
      kfac (M G U F F' D false) Finset.univ s v := by
  have hFF' := hH.sub
  by_cases hvU : v ∈ U
  · rw [kfac_lat G U F F' D true _ hvU, kfac_lat G U F F' D false _ hvU]
  by_cases hvF' : v ∈ F'
  swap
  · rw [kfac_out G U F F' D true _ hvU hvF', kfac_out G U F F' D false _ hvU hvF']
  have hrd : rd (phiS G U F F' D s ⟨v, Finset.mem_univ v⟩) 0 = rd (s ⟨v, Finset.mem_univ v⟩) 0 := by
    unfold phiS
    rw [sh_obs G U F F' D hD hFF' _ s hvU]
  have hsb : sb G U F F' D true v (rdS G U (phiS G U F F' D s) v) =
      sb G U F F' D false v (rdS G U s v) := by
    rw [sb_read G U F F' D true hH hD _ hvF' hvU, sb_read G U F F' D false hH hD _ hvF' hvU]
    by_cases hvF : v ∈ F
    · unfold phiS
      rw [sbV2_sh G U F F' D hD hFF' _ s hvF hvU, hsol v (Finset.mem_filter.mpr ⟨hvF, hvU⟩),
        sbV_split G U F F' D s hvF]
    · rw [← sbV_out G U F F' D _ hvF]
      unfold phiS
      exact sbV1_sh_out G U F F' D hD hFF' _ s hvF hvF' hvU
  by_cases hr : v = D.r0
  · rw [kfac_r0 G U F F' D true _ hvU hvF' hr, kfac_r0 G U F F' D false _ hvU hvF' hr, hrd, hsb]
  · rw [kfac_obs G U F F' D true _ hvU hvF' hr, kfac_obs G U F F' D false _ hvU hvF' hr, hrd, hsb]

end factors

end PM
end Hedge

#print axioms Hedge.PM.sbV1_sh_out
#print axioms Hedge.PM.kfac_phiS

/-! ## Runde 65: verktøy for teleskoperingen

`Out`: de observerte nodene i `F' \ F`. `fiber_sum`: `Σ_{v ∈ T} Σ_{c ∈ S, p c = v} g c` er
`Σ_{c ∈ S, p c ∈ T} g c`. `part_sum`: dekker `A` og `B` (disjunkte) alle `p c`, deles en sum
over `S` etter om `p c ∈ A` eller `p c ∈ B`. `CH_out`, `NX_out`: barna utenfor `F` til en
node er nodene i `Out` med den som forelder (`par` eller `nxt`); `CH_in_out`, `NX_in_out`:
for en node utenfor `F` ligger alle barna i `Out`. `par_cover`, `nxt_cover`: forelderen til en
node i `Out` ligger i `OF` eller i `Out`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma fiber_sum (T S : Finset V) (p : V → V) (g : V → ZMod 2) :
    ∑ v ∈ T, ∑ c ∈ S.filter (fun c => p c = v), g c = ∑ c ∈ S.filter (fun c => p c ∈ T), g c := by
  calc ∑ v ∈ T, ∑ c ∈ S.filter (fun c => p c = v), g c
      = ∑ v ∈ T, ∑ c ∈ S, (if p c = v then g c else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_filter]
    _ = ∑ c ∈ S, ∑ v ∈ T, (if p c = v then g c else 0) := Finset.sum_comm
    _ = ∑ c ∈ S, (if p c ∈ T then g c else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_ite_eq]
    _ = ∑ c ∈ S.filter (fun c => p c ∈ T), g c := by rw [Finset.sum_filter]

lemma part_sum (S A B : Finset V) (p : V → V) (g : V → ZMod 2)
    (hcov : ∀ c ∈ S, p c ∈ A ∨ p c ∈ B) (hdis : ∀ x, x ∈ A → x ∉ B) :
    ∑ c ∈ S, g c = ∑ c ∈ S.filter (fun c => p c ∈ A), g c + ∑ c ∈ S.filter (fun c => p c ∈ B), g c := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun c => p c ∈ A) g]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro c hc
  constructor
  · intro h
    rcases hcov c hc with h' | h'
    · exact absurd h' h
    · exact h'
  · intro h h'
    exact hdis _ h' h

section tele

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- De observerte nodene i `F' \ F`. -/
def Out : Finset V := F'.filter (fun w => w ∉ U ∧ w ∉ F)

lemma OF_Out_dis : ∀ x, x ∈ OF U F → x ∉ Out U F F' :=
  fun _ h1 h2 => (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).1

lemma CH_out (hD : Good G U F F' D) (v : V) :
    (CH U F' D v).filter (fun c => c ∉ F) = (Out U F F').filter (fun c => D.par c = v) := by
  ext c
  simp only [CH, Out, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hF', hU, -, hp⟩, hnF⟩
    exact ⟨⟨hF', hU, hnF⟩, hp⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hp⟩
    exact ⟨⟨hF', hU, fun h => hnF (h ▸ hD.ρF), hp⟩, hnF⟩

lemma NX_out (v : V) :
    (NX G U F F' v).filter (fun c => c ∉ F) = (Out U F F').filter (fun c => nxt G F F' c = v) := by
  ext c
  simp only [NX, Out, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hF', hU, -, hn⟩, hnF⟩
    exact ⟨⟨hF', hU, hnF⟩, hn⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hn⟩
    exact ⟨⟨hF', hU, fun h => hnF (Finset.mem_filter.mp h).1, hn⟩, hnF⟩

lemma CH_in_out (hD : Good G U F F' D) {w : V} (hw : w ∉ F) :
    CH U F' D w = (Out U F F').filter (fun c => D.par c = w) := by
  ext c
  simp only [CH, Out, Finset.mem_filter]
  constructor
  · rintro ⟨hF', hU, hρ, hp⟩
    exact ⟨⟨hF', hU, fun hcF => hw (hp ▸ hD.parF c hcF hU hρ)⟩, hp⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hp⟩
    exact ⟨hF', hU, fun h => hnF (h ▸ hD.ρF), hp⟩

lemma NX_in_out {X Y : Finset V} (hH : IsHedge G U X Y F F') {w : V} (hw : w ∉ F) :
    NX G U F F' w = (Out U F F').filter (fun c => nxt G F F' c = w) := by
  ext c
  simp only [NX, Out, Finset.mem_filter]
  constructor
  · rintro ⟨hF', hU, hR, hn⟩
    exact ⟨⟨hF', hU, fun hcF => hw (hn ▸ (hedge_nxt hH c hF' hR).1 hcF)⟩, hn⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hn⟩
    exact ⟨hF', hU, fun h => hnF (Finset.mem_filter.mp h).1, hn⟩

lemma par_cover (hD : Good G U F F' D) {c : V} (hc : c ∈ Out U F F') :
    D.par c ∈ OF U F ∨ D.par c ∈ Out U F F' := by
  obtain ⟨hF', hU, hnF⟩ := Finset.mem_filter.mp hc
  have hρ : c ≠ D.ρ := fun h => hnF (h ▸ hD.ρF)
  obtain ⟨hpF', hpU⟩ := hD.parF' c hF' hU hρ
  by_cases hpF : D.par c ∈ F
  · exact Or.inl (Finset.mem_filter.mpr ⟨hpF, hpU⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hpF', hpU, hpF⟩)

lemma nxt_cover {X Y : Finset V} (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {c : V} (hc : c ∈ Out U F F') :
    nxt G F F' c ∈ OF U F ∨ nxt G F F' c ∈ Out U F F' := by
  obtain ⟨hF', -, hnF⟩ := Finset.mem_filter.mp hc
  have hR : c ∉ rootsIn G F := fun h => hnF (Finset.mem_filter.mp h).1
  obtain ⟨-, hnF', he⟩ := hedge_nxt hH c hF' hR
  have hnU : nxt G F F' c ∉ U := fun h => hroot _ h c he
  by_cases hnF2 : nxt G F F' c ∈ F
  · exact Or.inl (Finset.mem_filter.mpr ⟨hnF2, hnU⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hnF', hnU, hnF2⟩)

end tele

end PM
end Hedge

#print axioms Hedge.PM.fiber_sum
#print axioms Hedge.PM.part_sum
#print axioms Hedge.PM.NX_in_out
#print axioms Hedge.PM.nxt_cover

/-! ## Runde 66: teleskoperingsidentiteten

`tele`: når hver observert node i `F' \ F` oppfyller sin ligning i `M1` (`ov w = sbV false w`),
summerer `δ` til null over `OF`. Bevis: `Σ_{OF} δ` er summen av trebitene og verdiene som går
fra `Out` inn i `F` (`hA`); summen av ligningene over `Out` (`hB`) og delingen etter om
forelderen ligger i `F` eller i `Out` (`part_sum`) gir `Σ_{OF} δ = 2 Σ_{Out} lb = 0`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_tele : ∀ a b c e : ZMod 2, c + e = a + b + b + e → a + c = 0 := by decide

section tele2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- **Teleskoperingsidentiteten.** -/
theorem tele {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hcons : ∀ w ∈ Out U F F', ov U s w = sbV G U F F' D false s w) :
    ∑ v ∈ OF U F, δ G U F F' D s v = 0 := by
  have hA : ∑ v ∈ OF U F, δ G U F F' D s v =
      ∑ c ∈ (Out U F F').filter (fun c => D.par c ∈ OF U F), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c ∈ OF U F), ov U s c := by
    unfold δ
    rw [Finset.sum_add_distrib]
    simp only [CH_out G U F F' D hD, NX_out G U F F']
    rw [fiber_sum (OF U F) (Out U F F') D.par (lb U D s),
      fiber_sum (OF U F) (Out U F F') (nxt G F F') (ov U s)]
  have hexp : ∀ w ∈ Out U F F', sbV G U F F' D false s w =
      lb U D s w + ∑ c ∈ (Out U F F').filter (fun c => D.par c = w), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c = w), ov U s c := by
    intro w hw
    obtain ⟨-, -, hwF⟩ := Finset.mem_filter.mp hw
    have hwρ : w ≠ D.ρ := fun h => hwF (h ▸ hD.ρF)
    unfold sbV
    first
      | rw [if_neg hwρ, scope_false, filter_univ, filter_univ, CH_in_out G U F F' D hD hwF,
          NX_in_out G U F F' hH hwF]
      | (simp only [if_neg hwρ, scope_false, Finset.mem_univ, Finset.filter_True]
         rw [CH_in_out G U F F' D hD hwF, NX_in_out G U F F' hH hwF])
  have hB : ∑ w ∈ Out U F F', ov U s w =
      ∑ w ∈ Out U F F', lb U D s w +
        ∑ c ∈ (Out U F F').filter (fun c => D.par c ∈ Out U F F'), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c ∈ Out U F F'), ov U s c := by
    rw [Finset.sum_congr rfl hcons, Finset.sum_congr rfl hexp, Finset.sum_add_distrib,
      Finset.sum_add_distrib, fiber_sum (Out U F F') (Out U F F') D.par (lb U D s),
      fiber_sum (Out U F F') (Out U F F') (nxt G F F') (ov U s)]
  have hP1 := part_sum (Out U F F') (OF U F) (Out U F F') D.par (lb U D s)
    (fun c hc => par_cover G U F F' D hD hc) (OF_Out_dis U F F')
  have hP2 := part_sum (Out U F F') (OF U F) (Out U F F') (nxt G F F') (ov U s)
    (fun c hc => nxt_cover G U F F' hH hroot hc) (OF_Out_dis U F F')
  rw [hP1, hP2] at hB
  rw [hA]
  exact zmod2_tele _ _ _ _ hB

end tele2

end PM
end Hedge

#print axioms Hedge.PM.tele

/-! ## Runde 67: felles-likheten og lik observert fordeling

`sh_zero`, `phiS_fix`: finnes ingen forskyvning, er `tsel = 0` og `phiS s = s`. `kfac_zero`:
bryter en node `w ∈ Out` sin ligning i `M1`, er faktoren hans 0 i begge modellene (utenfor `F`
er `M1`- og `M2`-biten like, og `w ≠ r0` siden `r0 ∈ F`). `joint_phiS`: `M2.fullJoint (phiS s)
= M1.fullJoint s`; finnes forskyvningen, er faktorene like (`kfac_phiS`); ellers er
`Σ_{OF} δ ≠ 0` (`exists_shift`), så etter `tele` bryter en `w ∈ Out` ligningen, og begge sider
er 0. `marg_eq`: `M1` og `M2` har samme fordeling på enhver mengde observerte noder. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section joint

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

lemma sh_zero (s : Assignment (α := Val U) (Finset.univ : Finset V)) : sh U F D 0 s = s := by
  funext u i
  simp only [sh, Pi.zero_apply, Finset.sum_const_zero, add_zero]

lemma phiS_fix (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (h : ¬ ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = δ G U F F' D s v) :
    phiS G U F F' D s = s := by
  have h0 : tsel U F F' D (δ G U F F' D s) = 0 := by
    unfold tsel
    exact dif_neg h
  unfold phiS
  rw [h0]
  exact sh_zero U F D s

/-- **En brutt ligning gir faktor 0** i begge modellene. -/
lemma kfac_zero {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D) (two : Bool)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V} (hw : w ∈ Out U F F')
    (hne : ov U s w ≠ sbV G U F F' D false s w) :
    kfac (M G U F F' D two) Finset.univ s w = 0 := by
  obtain ⟨hwF', hwU, hwF⟩ := Finset.mem_filter.mp hw
  have hr : w ≠ D.r0 := fun h => hwF (by rw [h]; exact (Finset.mem_filter.mp hD.r0R).1)
  have h2 : sbV G U F F' D two s w = sbV G U F F' D false s w := by
    cases two
    · rfl
    · exact (sbV_out G U F F' D s hwF).symm
  rw [kfac_obs G U F F' D two s hwU hwF' hr, sb_read G U F F' D two hH hD s hwF' hwU, if_neg]
  intro h
  exact hne (h.trans h2)

/-- **Felles-likheten.** -/
theorem joint_phiS {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (M G U F F' D true).fullJoint (phiS G U F F' D s) = (M G U F F' D false).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  by_cases h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = δ G U F F' D s v
  · exact Finset.prod_congr rfl
      (fun v _ => kfac_phiS G U F F' D hH hD s (tsel_spec U F F' D _ h) v)
  · have hsum : ∑ v ∈ OF U F, δ G U F F' D s v ≠ 0 :=
      fun h0 => h (exists_shift U F F' D hH.sub T _ h0)
    have hbad : ∃ w ∈ Out U F F', ov U s w ≠ sbV G U F F' D false s w := by
      by_contra hno
      push_neg at hno
      exact hsum (tele G U F F' D hH hD hroot s hno)
    obtain ⟨w, hw, hne⟩ := hbad
    rw [phiS_fix G U F F' D s h,
      Finset.prod_eq_zero (Finset.mem_univ w) (kfac_zero G U F F' D hH hD true s hw hne),
      Finset.prod_eq_zero (Finset.mem_univ w) (kfac_zero G U F F' D hH hD false s hw hne)]

/-- **Lik observert fordeling.** -/
theorem marg_eq {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    (M G U F F' D false).marginal O = (M G U F F' D true).marginal O :=
  marginal_eq_of_invol _ _ O (phiS G U F F' D) (phiS_invol G U F F' D hD hH.sub)
    (phiS_restrict G U F F' D hD hH.sub hO) (joint_phiS G U F F' D hH hD hroot T)

end joint

end PM
end Hedge

#print axioms Hedge.PM.joint_phiS
#print axioms Hedge.PM.marg_eq
