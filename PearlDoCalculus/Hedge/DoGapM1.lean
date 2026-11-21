import PearlDoCalculus.Hedge.Positivity

/-!
# The effect in `M1`: the root parity is a fair coin under `do(x)` (step H3)

This file proves `PM.parR_half`: under an intervention `do(x)`, the parity `parR` of the
observed roots of the hedge takes the values `0` and `1` with the same probability in the
parity model `M1` (`PM.M` with `two = false`, from `Hedge/ParityModels.lean`). This holds
when some tree edge `(c, par c)` has exactly one end that reaches a root along `nxt`
without passing through `X`.

**Why.** `M1` and `M2` have the same positive observed distribution (`Hedge/ObsEq.lean`,
`Hedge/Positivity.lean`). To show non-identifiability they must also differ under
`do(x)`. This file gives the `M1` half: `P(parR = 1) = P(parR = 0)`. The `M2` half,
`P(parR = 0) = 3 · P(parR = 1)`, comes in `Hedge/DoGapM2.lean`.

**How.**

1. *Paths along `nxt` that avoid `X`.* The rank grows along `nxt` away from the roots
   (`hedge_rank_iter`), so `nxt` has no cycles except at roots (`hedge_cycle`). The path
   from an observed node stays observed (`iter_obs`). `nreach s w` says that `w` is
   reached from `s` along `nxt` without passing through `X`, and `nrI` is its indicator in
   `ZMod 2`. For `v ∈ F' \ X` it satisfies `nrI s v = [v = s] + Σ_{w ∈ NX v} nrI s w`
   (`nrI_rec`), because a node has at most one predecessor on the path (`pred_aux`). A
   path reaches at most one root (`nreach_root_unique`, `sum_nrI_roots`).
2. *The map ψ.* `psiS c` flips the latent bit on the edge `(c, par c)` and then flips the
   value of every observed `w` with `phiC c w = 1`, where `phiC c = nrI c + nrI (par c)`.
   The flip of one edge bit is the shift `sh` with the edge set `{c}`; the lemmas
   `lb_shE` and `obs_shE` for it come from `Hedge/Positivity.lean`. Which bits and values
   are flipped does not depend on the assignment, so `psiS c` is an involution
   (`psiS_invol`). The bit of `M1` at `v ∈ F'` changes by
   `[v = c] + [v = par c] + Σ_{NX v} phiC` (`sbV_psi`), which is exactly `phiC c v`
   outside `X` (`phiC_rec`). No node of `X` is reached (`nrI_X`).
3. *ψ under `do(x)`.* So ψ keeps every kernel factor of `doModel M1 X x`: inside `X` the
   value is unchanged, and outside `X` the value and the bit of `M1` change together
   (`kfac_psi_do`). Hence ψ keeps the joint distribution (`joint_psi`). When exactly one
   of `c`, `par c` reaches a root, ψ flips `parR` (`parR_psi`). An involution that keeps
   the weights and flips a bit makes both values of the bit equally likely
   (`ZMod2.map_fair_of_invol`, from `Util/ZMod2.lean`), which gives `parR_half`.

**Main results.** `nrI_rec`, `sum_nrI_roots`, `PM.psiS_invol`, `PM.sbV_psi`,
`PM.phiC_rec`, `PM.joint_psi`, `PM.parR_half`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 69: stier langs `nxt` som unngår `X`

Forberedelse til do-forskjellen. `hedge_rank_iter`: fra en ikke-rot øker rangen langs `nxt`;
`hedge_cycle`: kommer `nxt` tilbake til `v`, er `v` en rot. `iter_obs`: fra en observert node
er hele `nxt`-stien observert (latente har ingen foreldre). `nreach s w`: `w` nås fra `s`
langs `nxt` uten å treffe `X` underveis (`w` selv og `s` medregnet); `nrI` er indikatoren i
`ZMod 2`. `nrI_rec`: for `v ∈ F' \ X` er `nrI s v = [v = s] + Σ_{w ∈ NX v} nrI s w` (høyst
én forgjenger på stien, `pred_aux`). `sum_nrI_roots`: en sti når høyst én rot. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

section nreach

variable {G : DAG V} {U X Y F F' : Finset V}

lemma hedge_rank_iter (hH : IsHedge G U X Y F F') {v : V} (hv : v ∈ F')
    (hR : v ∉ rootsIn G F) : ∀ m, G.rank v < G.rank ((nxt G F F')^[m + 1] v) := by
  intro m
  induction m with
  | zero =>
    show G.rank v < G.rank (nxt G F F' v)
    exact G.rank_strict_mono _ _ (hedge_nxt hH v hv hR).2.2
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases huR : (nxt G F F')^[m + 1] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ huR]
      exact ih
    · exact lt_trans ih
        (G.rank_strict_mono _ _ (hedge_nxt hH _ (hedge_iter_mem hH hv (m + 1)) huR).2.2)

lemma hedge_cycle (hH : IsHedge G U X Y F F') {v : V} (hv : v ∈ F') {m : ℕ}
    (h : (nxt G F F')^[m + 1] v = v) : v ∈ rootsIn G F := by
  by_contra hR
  have hlt := hedge_rank_iter hH hv hR m
  rw [h] at hlt
  exact lt_irrefl _ hlt

lemma iter_obs (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s : V}
    (hs : s ∈ F') (hsU : s ∉ U) : ∀ n, (nxt G F F')^[n] s ∉ U := by
  intro n
  induction n with
  | zero => exact hsU
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] s ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]
      exact ih
    · intro hU
      exact hroot _ hU _ (hedge_nxt hH _ (hedge_iter_mem hH hs n) hR).2.2

/-- `w` nås fra `s` langs `nxt` uten å treffe `X`. -/
abbrev nreach (G : DAG V) (X F F' : Finset V) (s w : V) : Prop :=
  ∃ k, (nxt G F F')^[k] s = w ∧ ∀ j ≤ k, (nxt G F F')^[j] s ∉ X

open Classical in
/-- Indikatoren for `nreach` i `ZMod 2`. -/
noncomputable def nrI (G : DAG V) (X F F' : Finset V) (s w : V) : ZMod 2 :=
  if nreach G X F F' s w then 1 else 0

lemma pred_aux (hH : IsHedge G U X Y F F') {s v w w' : V} (hs : s ∈ F') {k k' : ℕ} (hk : k < k')
    (h1 : (nxt G F F')^[k] s = w) (h2 : (nxt G F F')^[k'] s = w')
    (hwv : nxt G F F' w = v) (hw'v : nxt G F F' w' = v) (hw' : w' ∉ rootsIn G F) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hv : (nxt G F F')^[k + 1] s = v := by
    rw [Function.iterate_succ_apply', h1, hwv]
  have hw'm : (nxt G F F')^[m] v = w' := by
    rw [← hv, ← Function.iterate_add_apply, ← h2, show m + (k + 1) = k + m + 1 by omega]
  have hvF : v ∈ F' := by
    rw [← hv]
    exact hedge_iter_mem hH hs (k + 1)
  have hcyc : (nxt G F F')^[m + 1] v = v := by
    rw [Function.iterate_succ_apply', hw'm, hw'v]
  have hR := hedge_cycle hH hvF hcyc
  apply hw'
  rw [← hw'm, iter_root G F F' v hR m]
  exact hR

/-- **Rekursjonen for `nrI`** langs `nxt`. -/
theorem nrI_rec (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s v : V}
    (hs : s ∈ F') (hsU : s ∉ U) (hv : v ∈ F') (hvX : v ∉ X) :
    nrI G X F F' s v = (if v = s then 1 else 0) +
      ∑ w ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v), nrI G X F F' s w := by
  classical
  have huniq : ∀ w ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v),
      ∀ w' ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v),
      nreach G X F F' s w → nreach G X F F' s w' → w = w' := by
    intro w hw w' hw' h h'
    obtain ⟨-, -, hwR, hwv⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, -, hw'R, hw'v⟩ := Finset.mem_filter.mp hw'
    obtain ⟨k, hk, -⟩ := h
    obtain ⟨k', hk', -⟩ := h'
    rcases lt_trichotomy k k' with hl | he | hl
    · exact (pred_aux hH hs hl hk hk' hwv hw'v hw'R).elim
    · subst he
      exact hk.symm.trans hk'
    · exact (pred_aux hH hs hl hk' hk hw'v hwv hwR).elim
  by_cases hvs : v = s
  · have hr0 : nreach G X F F' s v :=
      ⟨0, hvs.symm, fun j hj => by rw [Nat.le_zero.mp hj, ← hvs]; exact hvX⟩
    have h1 : nrI G X F F' s v = 1 := by
      unfold nrI
      rw [if_pos hr0]
    rw [h1, if_pos hvs, Finset.sum_eq_zero, add_zero]
    intro w hw
    unfold nrI
    rw [if_neg]
    rintro ⟨k, hk, -⟩
    obtain ⟨-, -, hwR, hwv⟩ := Finset.mem_filter.mp hw
    have hcyc : (nxt G F F')^[k + 1] s = s := by
      rw [Function.iterate_succ_apply', hk, hwv, hvs]
    have hR := hedge_cycle hH hs hcyc
    apply hwR
    rw [← hk, iter_root G F F' s hR k]
    exact hR
  · rw [if_neg hvs, zero_add]
    by_cases hr : nreach G X F F' s v
    · obtain ⟨k, hk, hkX⟩ := hr
      have hr' : nreach G X F F' s v := ⟨k, hk, hkX⟩
      have hex : ∃ k, (nxt G F F')^[k] s = v := ⟨k, hk⟩
      have hk0 := Nat.find_spec hex
      have hle : Nat.find hex ≤ k := Nat.find_min' hex hk
      have hne0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0] at hk0
        exact hvs hk0.symm
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjv : (nxt G F F')^[j + 1] s = v := by
        rw [← hj]
        exact hk0
      have hwv : nxt G F F' ((nxt G F F')^[j] s) = v := by
        have h' := hjv
        rw [Function.iterate_succ_apply'] at h'
        exact h'
      have hwR : (nxt G F F')^[j] s ∉ rootsIn G F := by
        intro hR
        rw [nxt_root G F F' _ hR] at hwv
        exact Nat.find_min hex (show j < Nat.find hex by omega) hwv
      have hwmem : (nxt G F F')^[j] s ∈
          F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v) :=
        Finset.mem_filter.mpr ⟨hedge_iter_mem hH hs j, iter_obs hH hroot hs hsU j, hwR, hwv⟩
      have hwr : nreach G X F F' s ((nxt G F F')^[j] s) :=
        ⟨j, rfl, fun i hi => hkX i (by omega)⟩
      unfold nrI
      rw [if_pos hr', Finset.sum_eq_single ((nxt G F F')^[j] s)]
      · rw [if_pos hwr]
      · intro b hb hbw
        rw [if_neg]
        intro hbr
        exact hbw (huniq b hb _ hwmem hbr hwr)
      · intro hn
        exact absurd hwmem hn
    · unfold nrI
      rw [if_neg hr, Finset.sum_eq_zero]
      intro w hw
      rw [if_neg]
      rintro ⟨k, hk, hkX⟩
      obtain ⟨-, -, -, hwv⟩ := Finset.mem_filter.mp hw
      apply hr
      refine ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hwv], fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact hkX j (by omega)
      · rw [show j = k + 1 by omega, Function.iterate_succ_apply', hk, hwv]
        exact hvX

/-- Høyst én rot nås. -/
lemma nreach_root_unique {s r r' : V} (hr : r ∈ rootsIn G F) (hr' : r' ∈ rootsIn G F)
    (h : nreach G X F F' s r) (h' : nreach G X F F' s r') : r = r' := by
  obtain ⟨k, hk, -⟩ := h
  obtain ⟨k', hk', -⟩ := h'
  rcases le_total k k' with hl | hl
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, Function.iterate_add_apply, hk, iter_root G F F' r hr m] at hk'
    exact hk'
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, Function.iterate_add_apply, hk', iter_root G F F' r' hr' m] at hk
    exact hk.symm

open Classical in
/-- **Summen over røttene** er 1 nøyaktig når stien når en rot. -/
lemma sum_nrI_roots (s : V) :
    ∑ r ∈ rootsIn G F, nrI G X F F' s r =
      if ∃ r ∈ rootsIn G F, nreach G X F F' s r then 1 else 0 := by
  by_cases h : ∃ r ∈ rootsIn G F, nreach G X F F' s r
  · rw [if_pos h]
    obtain ⟨r, hr, hrr⟩ := h
    rw [Finset.sum_eq_single r]
    · unfold nrI
      rw [if_pos hrr]
    · intro b hb hbr
      unfold nrI
      rw [if_neg]
      intro hb'
      exact hbr (nreach_root_unique hb hr hb' hrr)
    · intro hn
      exact absurd hr hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro r hr
    unfold nrI
    rw [if_neg]
    intro hrr
    exact h ⟨r, hr, hrr⟩

end nreach

end Hedge

#print axioms Hedge.nrI_rec
#print axioms Hedge.sum_nrI_roots

/-! ## Runde 70: avbildningen ψ

`flipO Φ t`: legg `Φ w` til verdien til hver observert `w`. `phiC c w` = `nrI c w + nrI (par c) w`.
`psiS c s`: snu biten på trekanten `(c, par c)` (`sh` med `E = {c}`) og deretter verdiene der
`phiC c = 1`; ψ avhenger ikke av `s` og er en involusjon (`psiS_invol`). `ov_psi`, `lb_psi`:
virkningen på verdier og trebiter. `sbV_psi`: `M1`-biten til `v ∈ F'` endres med
`[v = c] + [v = par c] + Σ_{NX v} phiC`. `phiC_rec`: for `v ∈ F' \ X` er det nøyaktig
`phiC c v` (fra `nrI_rec`), så hver ligning utenfor `X` holder for `ψ s` når den holder for `s`.
`nrI_X`: ingen node i `X` nås. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section psi

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- Legg `Φ` til verdiene til de observerte nodene. -/
def flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u i => t u i + (if u.1 ∈ U then 0 else Φ u.1)

lemma flipO_obs (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V}
    (hw : w ∉ U) :
    flipO U Φ t ⟨w, Finset.mem_univ w⟩ = fun i => t ⟨w, Finset.mem_univ w⟩ i + Φ w := by
  funext i
  show t ⟨w, Finset.mem_univ w⟩ i + (if w ∈ U then 0 else Φ w) = _
  rw [if_neg hw]

lemma flipO_lat (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V}
    (hu : u ∈ U) : flipO U Φ t ⟨u, Finset.mem_univ u⟩ = t ⟨u, Finset.mem_univ u⟩ := by
  funext i
  show t ⟨u, Finset.mem_univ u⟩ i + (if u ∈ U then 0 else Φ u) = _
  rw [if_pos hu, add_zero]

lemma ov_flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V}
    (hw : w ∉ U) : ov U (flipO U Φ t) w = ov U t w + Φ w := by
  have h0 : 0 < kk U w := by
    rw [kk_obs hw]
    omega
  unfold ov
  rw [flipO_obs U Φ t hw]
  unfold rd
  rw [dif_pos h0, dif_pos h0]

lemma lb_flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {c : V}
    (hl : D.lat c ∈ U) : lb U D (flipO U Φ t) c = lb U D t c := by
  unfold lb
  rw [flipO_lat U Φ t hl]

/-- Hvilke observerte verdier ψ snur. -/
noncomputable def phiC (c w : V) : ZMod 2 := nrI G X F F' c w + nrI G X F F' (D.par c) w

/-- **ψ**: snu biten på `(c, par c)` og verdiene der `phiC c = 1`. -/
noncomputable def psiS (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  flipO U (phiC G F F' D X c) (sh U {c} D (fun _ => 1) s)

theorem psiS_invol (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    psiS G U F F' D X c (psiS G U F F' D X c s) = s := by
  funext u i
  simp only [psiS, flipO, sh]
  exact ZMod2.add_add_add_add_cancel _ _ _

lemma lb_psi (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) {c' : V}
    (hl : D.lat c' ∈ U) (hc'U : c' ∉ U) (hc'ρ : c' ≠ D.ρ) :
    lb U D (psiS G U F F' D X c s) c' = lb U D s c' + (if c' = c then 1 else 0) := by
  unfold psiS
  rw [lb_flipO U D _ _ hl, lb_shE U D {c} _ s hl]
  by_cases h : c' = c
  · rw [if_pos (show c' ∈ EF U {c} D from
      Finset.mem_filter.mpr ⟨Finset.mem_singleton.mpr h, hc'U, hc'ρ⟩), if_pos h]
  · rw [if_neg (show c' ∉ EF U {c} D from
      fun hm => h (Finset.mem_singleton.mp (Finset.mem_filter.mp hm).1)), if_neg h]

lemma ov_psi (c : V) (hcl : D.lat c ∈ U) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    {w : V} (hw : w ∉ U) :
    ov U (psiS G U F F' D X c s) w = ov U s w + phiC G F F' D X c w := by
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  unfold psiS
  rw [ov_flipO U _ _ hw]
  unfold ov
  rw [obs_shE U D {c} hE _ s hw]

/-- **`M1`-biten under ψ.** -/
theorem sbV_psi (hD : Good G U F F' D) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D false (psiS G U F F' D X c s) v = sbV G U F F' D false s v +
      ((if v = c then 1 else 0) + (if v = D.par c then 1 else 0) +
        ∑ w ∈ NX G U F F' v, phiC G F F' D X c w) := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hown : (if v = D.ρ then 0 else lb U D (psiS G U F F' D X c s) v) =
      (if v = D.ρ then 0 else lb U D s v) + (if v = c then 1 else 0) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ, if_neg (fun h => hcρ (h.symm.trans hρ)), add_zero]
    · rw [if_neg hρ, if_neg hρ, lb_psi G U F F' D X c s (hD.lat v hvF' hvU hρ).1 hvU hρ]
  have hch : ∑ c' ∈ CH U F' D v, lb U D (psiS G U F F' D X c s) c' =
      ∑ c' ∈ CH U F' D v, lb U D s c' + (if v = D.par c then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun c' hc' => by
      obtain ⟨hF, hU, hρ', -⟩ := Finset.mem_filter.mp hc'
      exact lb_psi G U F F' D X c s (hD.lat c' hF hU hρ').1 hU hρ'),
      Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq']
    congr 1
    by_cases hp : v = D.par c
    · rw [if_pos hp, if_pos (show c ∈ CH U F' D v from
        Finset.mem_filter.mpr ⟨hc, hcU, hcρ, hp.symm⟩)]
    · rw [if_neg hp, if_neg (fun hm => hp (Finset.mem_filter.mp hm).2.2.2.symm)]
  have hnx : ∑ w ∈ NX G U F F' v, ov U (psiS G U F F' D X c s) w =
      ∑ w ∈ NX G U F F' v, ov U s w + ∑ w ∈ NX G U F F' v, phiC G F F' D X c w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw
    exact ov_psi G U F F' D X c hcl s hwU
  unfold sbV
  rw [scope_false, filter_univ, filter_univ, hown, hch, hnx]
  ring

/-- **Rekursjonen for `phiC`** utenfor `X`. -/
theorem phiC_rec {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    {v : V} (hvF' : v ∈ F') (hvX : v ∉ X) :
    phiC G F F' D X c v = (if v = c then 1 else 0) + (if v = D.par c then 1 else 0) +
      ∑ w ∈ NX G U F F' v, phiC G F F' D X c w := by
  obtain ⟨hpc, hpcU⟩ := hD.parF' c hc hcU hcρ
  unfold phiC
  rw [nrI_rec hH hroot hc hcU hvF' hvX, nrI_rec hH hroot hpc hpcU hvF' hvX]
  unfold NX
  rw [Finset.sum_add_distrib]
  ring

lemma nrI_X {s v : V} (hv : v ∈ X) : nrI G X F F' s v = 0 := by
  unfold nrI
  rw [if_neg]
  rintro ⟨k, hk, hkX⟩
  apply hkX k le_rfl
  rw [hk]
  exact hv

end psi

end PM
end Hedge

#print axioms Hedge.PM.psiS_invol
#print axioms Hedge.PM.sbV_psi
#print axioms Hedge.PM.phiC_rec

/-! ## Runde 71: ψ under `do(x)` i `M1`: like sannsynligheter for odde og jevn paritet

`ZMod2.map_fair_of_invol` (i `Util/ZMod2.lean`): en involusjon som bevarer vektene og snur `f`
gir `P(f = 1) = P(f = 0)`.
`kfac_psi_do`: hver faktor i `doModel M1 X x` er den samme i `ψ s` og `s` (i `X` er verdien
uendret, `nrI_X`; utenfor `X` endres både verdien og `M1`-biten med `phiC c v`, `phiC_rec`).
`joint_psi`: fellesfordelingen er invariant. `parR`: pariteten til de observerte røttene.
`parR_psi`: når nøyaktig én av `c`, `par c` når en rot uten å treffe `X`, snur ψ `parR`.
`parR_half`: da er `P(parR = 1) = P(parR = 0)` under `do(x)` i `M1`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace PM

section psido

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- **Hver faktor i `do(x)` bevares av ψ.** -/
theorem kfac_psi_do {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (M G U F F' D false) X x) Finset.univ (psiS G U F F' D X c s) v =
      kfac (doModel (M G U F F' D false) X x) Finset.univ s v := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  rw [kfac_doModel, kfac_doModel]
  by_cases hv : v ∈ X
  · rw [dif_pos hv, dif_pos hv]
    have h0 : phiC G F F' D X c v = 0 := by
      unfold phiC
      rw [nrI_X G F F' X hv, nrI_X G F F' X hv, add_zero]
    have hpv : psiS G U F F' D X c s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
      unfold psiS
      rw [flipO_obs U _ _ (hXU v hv), obs_shE U D {c} hE _ s (hXU v hv), h0]
      funext i
      exact add_zero _
    rw [hpv]
  · rw [dif_neg hv, dif_neg hv]
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D false _ hvU, kfac_lat G U F F' D false _ hvU]
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D false _ hvU hvF', kfac_out G U F F' D false _ hvU hvF']
    have hrd : rd (psiS G U F F' D X c s ⟨v, Finset.mem_univ v⟩) 0 =
        rd (s ⟨v, Finset.mem_univ v⟩) 0 + phiC G F F' D X c v :=
      ov_psi G U F F' D X c hcl s hvU
    have hsb : sb G U F F' D false v (rdS G U (psiS G U F F' D X c s) v) =
        sb G U F F' D false v (rdS G U s v) + phiC G F F' D X c v := by
      rw [sb_read G U F F' D false hH hD _ hvF' hvU, sb_read G U F F' D false hH hD _ hvF' hvU,
        sbV_psi G U F F' D X hD hc hcU hcρ s hvF' hvU,
        ← phiC_rec G U F F' D X hH hD hroot hc hcU hcρ hvF' hv]
    by_cases hr : v = D.r0
    · rw [kfac_r0 G U F F' D false _ hvU hvF' hr, kfac_r0 G U F F' D false _ hvU hvF' hr, hrd, hsb,
        ZMod2.add_add_add_cancel]
    · rw [kfac_obs G U F F' D false _ hvU hvF' hr, kfac_obs G U F F' D false _ hvU hvF' hr, hrd,
        hsb]
      simp only [add_left_inj]

/-- **Fellesfordelingen under `do(x)` er invariant under ψ.** -/
theorem joint_psi {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (doModel (M G U F F' D false) X x).fullJoint (psiS G U F F' D X c s) =
      (doModel (M G U F F' D false) X x).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  exact Finset.prod_congr rfl
    (fun v _ => kfac_psi_do G U F F' D X hH hD hroot hXU hc hcU hcρ x s v)

/-- Pariteten til de observerte røttene. -/
noncomputable def parR (s : Assignment (α := Val U) (Finset.univ : Finset V)) : ZMod 2 :=
  ∑ r ∈ (rootsIn G F).filter (fun r => r ∉ U), ov U s r

lemma nrI_lat {Y : Finset V} (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {s r : V} (hs : s ∈ F') (hsU : s ∉ U) (hr : r ∈ U) : nrI G X F F' s r = 0 := by
  unfold nrI
  rw [if_neg]
  rintro ⟨k, hk, -⟩
  apply iter_obs hH hroot hs hsU k
  rw [hk]
  exact hr

/-- **ψ snur pariteten** når nøyaktig én av `c`, `par c` når en rot utenom `X`. -/
theorem parR_psi {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    parR G U F (psiS G U F F' D X c s) = parR G U F s + 1 := by
  have hcl := (hD.lat c hc hcU hcρ).1
  obtain ⟨hpc, hpcU⟩ := hD.parF' c hc hcU hcρ
  unfold parR
  rw [Finset.sum_congr rfl (fun r hr => ov_psi G U F F' D X c hcl s (Finset.mem_filter.mp hr).2),
    Finset.sum_add_distrib]
  congr 1
  have hz : ∀ r ∈ rootsIn G F, phiC G F F' D X c r ≠ 0 → r ∉ U := by
    intro r _ h hrU
    apply h
    unfold phiC
    rw [nrI_lat G U F F' X hH hroot hc hcU hrU, nrI_lat G U F F' X hH hroot hpc hpcU hrU, add_zero]
  rw [Finset.sum_filter_of_ne hz]
  unfold phiC
  rw [Finset.sum_add_distrib, sum_nrI_roots, sum_nrI_roots]
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

/-- **`P(parR = 1) = P(parR = 0)` under `do(x)` i `M1`.** -/
theorem parR_half {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (x : Assignment (α := Val U) X) :
    ((doModel (M G U F F' D false) X x).fullJoint.map (parR G U F)) 1 =
      ((doModel (M G U F F' D false) X x).fullJoint.map (parR G U F)) 0 :=
  ZMod2.map_fair_of_invol _ (psiS G U F F' D X c) (parR G U F) (psiS_invol G U F F' D X c)
    (joint_psi G U F F' D X hH hD hroot hXU hc hcU hcρ x)
    (parR_psi G U F F' D X hH hD hroot hc hcU hcρ hA)

end psido

end PM
end Hedge

#print axioms Hedge.PM.joint_psi
#print axioms Hedge.PM.parR_half
