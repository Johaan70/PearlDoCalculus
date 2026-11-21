import PearlDoCalculus.Hedge.Tree
import PearlDoCalculus.Util.ZMod2

/-!
# The parity models on a hedge (step H3)

This file defines the two causal models `M1` and `M2` on a hedge `(F, F')` (`IsHedge`, in
`Hedge/Defs.lean`) that are later shown to have the same positive observed distribution
but different effects of `do(x)`. It also computes their kernel factors on a full
assignment and rewrites the bit of each node without the proof guards used in the
definition.

**Why.** Non-identifiability is shown by two models that agree on every observed
distribution and disagree on the effect. These are those two models. Every later
file of step H3 (equal observed distributions, positivity, the gap under `do(x)`) works
from the formulas proved here.

**How.**

1. *General tools* (`marginal_eq_of_invol`). An involution on full assignments that
   keeps the values on `O` and carries the joint distribution of `M1` to that of `M2`
   gives equal marginals on `O`.
2. *Value types* (`Val`, `rd`, `obs_ext`, `noise`). A latent node carries one bit for
   each edge of the spanning tree, indexed by the lower end of the edge (`ix`); an
   observed node carries one bit. `rd x i` reads bit `i` and gives `0` out of range, so
   kernels can read their parents with no proof obligations. `noise` is `1` with
   probability `1/4`.
3. *The models* (`Data`, `sb`, `kern`, `M`). `Data` holds the tree root `ρ`, the parent
   pointer `par`, the latent `lat c` behind the edge `(c, par c)`, and the noisy root
   `r0`. The bit `sb` of an observed node in `F'` is its own tree bit plus the tree bits
   of its children `CH` plus the values of its `nxt` children `NX`. In `M2`
   (`two = true`) a node in `F` counts only children in `F` (`scope`). Latent nodes and
   observed nodes outside `F'` are uniform, and `r0` adds `noise`.
4. *Kernel factors* (`kfac_lat`, `kfac_out`, `kfac_obs`, `kfac_r0`). On a full assignment
   the factor is uniform, an indicator that the bit equals `sb`, or `noise` of
   `bit + sb`.
5. *Bits without guards* (`Good`, `sb_read`). `Good` lists what the data satisfy (they
   come from `hedge_spanning`). Under `Good` and a hedge, every parent that `sb` reads
   really is a parent, so `sb` equals `sbV`, the same sum read straight from the
   assignment (`lb` for tree bits, `ov` for observed values).

**Main results.** `marginal_eq_of_invol`, `PM.obs_ext`, `PM.M`, `PM.kfac_obs`,
`PM.kfac_r0`, `PM.Good`, `PM.sb_read`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 56: generelle verktøy for paritetsmodellene

`marginal_eq_of_invol`: finnes en involusjon `φ` på hele tilordninger som bevarer verdiene
på `O` og flytter `M1`s sannsynlighet til `M2` (`M2.fullJoint (φ s) = M1.fullJoint s`), har
modellene samme marginal på `O`. Det er argumentet hedge-familiene i `Identification`
bruker hver for seg (`full_map`, `obsEq`), her én gang for alle grafer og verdityper. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Samme marginal via en involusjon** som bevarer `O`. -/
theorem marginal_eq_of_invol {G1 G2 : DAG V} {α : V → Type*}
    (M1 : G1.CausalModel α) (M2 : G2.CausalModel α) (O : Finset V)
    (φ : Assignment (α := α) (Finset.univ : Finset V) → Assignment (α := α) (Finset.univ : Finset V))
    (hinv : ∀ s, φ (φ s) = s)
    (hO : ∀ s, (φ s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O))
    (hj : ∀ s, M2.fullJoint (φ s) = M1.fullJoint s) :
    M1.marginal O = M2.marginal O := by
  have hmap : M2.fullJoint = M1.fullJoint.map φ := by
    ext s
    rw [PMF.map_apply, tsum_eq_single (φ s)]
    · rw [if_pos (hinv s).symm, ← hj (φ s), hinv]
    · intro s' hs'
      rw [if_neg]
      intro hs
      apply hs'
      rw [hs, hinv]
  unfold CausalModel.marginal
  rw [hmap, PMF.map_comp]
  congr 1
  funext s
  exact (hO s).symm

end Hedge

#print axioms Hedge.marginal_eq_of_invol

/-! ## Runde 57: verdityper for paritetsmodellene

Alle noder får verditypen `Fin (kk U v) → ZMod 2`: `kk U v = |V|` for latente (én bit per
kant i treet, indeksert med kantens nedre node via `ix`) og `1` for observerte (én bit).
`rd x i` leser bit nummer `i` (og gir `0` utenfor rekkevidde), så kjernene kan lese
foreldre uten bevisforpliktelser. `obs_ext`: to observerte verdier er like nøyaktig når
biten er lik. `noise`: biten `1` med sannsynlighet `1/4`, til positivitet. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Antall biter: `|V|` for latente, `1` for observerte. -/
def kk (U : Finset V) (v : V) : ℕ := if v ∈ U then Fintype.card V else 1

/-- Verditypen. -/
abbrev Val (U : Finset V) (v : V) : Type := Fin (kk U v) → ZMod 2

/-- Bit nummer `i` (0 utenfor rekkevidde). -/
def rd {U : Finset V} {v : V} (x : Val U v) (i : ℕ) : ZMod 2 :=
  if h : i < kk U v then x ⟨i, h⟩ else 0

/-- Indeksen til kanten under `c` i en latent. -/
noncomputable def ix (c : V) : ℕ := (Fintype.equivFin V c).val

lemma kk_obs {U : Finset V} {v : V} (hv : v ∉ U) : kk U v = 1 := if_neg hv

lemma kk_lat {U : Finset V} {u : V} (hu : u ∈ U) : kk U u = Fintype.card V := if_pos hu

lemma ix_lt (c : V) : ix c < Fintype.card V := (Fintype.equivFin V c).isLt

lemma ix_inj {c c' : V} (h : ix c = ix c') : c = c' :=
  (Fintype.equivFin V).injective (Fin.ext h)

/-- En observert verdi med bit `b`. -/
def cst (U : Finset V) (v : V) (b : ZMod 2) : Val U v := fun _ => b

lemma rd_cst {U : Finset V} {v : V} (hv : v ∉ U) (b : ZMod 2) : rd (cst U v b) 0 = b := by
  have h0 : 0 < kk U v := by
    rw [kk_obs hv]
    omega
  simp only [rd, cst, dif_pos h0]

/-- **To observerte verdier er like nøyaktig når biten er lik.** -/
lemma obs_ext {U : Finset V} {v : V} (hv : v ∉ U) (x y : Val U v) :
    x = y ↔ rd x 0 = rd y 0 := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h0 : 0 < kk U v := by
      rw [kk_obs hv]
      omega
    unfold rd at h
    rw [dif_pos h0, dif_pos h0] at h
    funext i
    have hi : i.val = 0 := by
      have := i.isLt
      have h1 : kk U v = 1 := kk_obs hv
      omega
    have : i = ⟨0, h0⟩ := Fin.ext hi
    rw [this]
    exact h

lemma eq_cst {U : Finset V} {v : V} (hv : v ∉ U) (x : Val U v) : x = cst U v (rd x 0) :=
  (obs_ext hv x _).mpr (rd_cst hv _).symm

/-- Støy: `1` med sannsynlighet `1/4`. -/
noncomputable def noise : PMF (ZMod 2) :=
  PMF.map (fun i : Fin 4 => if i = 0 then (1 : ZMod 2) else 0) (PMF.uniformOfFintype (Fin 4))

end PM
end Hedge

#print axioms Hedge.PM.obs_ext
#print axioms Hedge.PM.eq_cst

/-! ## Runde 58: paritetsmodellene `M1` og `M2`

`Data`: roten `ρ` i `F`, foreldrepekeren `par`, den latente `lat c` bak trekanten
`(c, par c)`, og roten `r0` med støy. `CH v`: trebarna til `v` (observerte `c ≠ ρ` med
`par c = v`). `NX v`: `nxt`-barna til `v` (observerte ikke-røtter med `nxt w = v`).
`sb`: biten i `v` er egen trebit + trebarnas biter + `nxt`-barnas verdier; i `M2`
(`two = true`) teller en node i `F` bare barn i `F` (`scope`). Kjernen: uniform for latente
og for observerte utenfor `F'`; i `F'` er verdien `sb` (pluss `noise` i `r0`). Foreldre
leses med `rd`, beskyttet av `if h : w ∈ G.parents v`, så definisjonen har ingen
bevisforpliktelser. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Konstruksjonsdataene. -/
structure Data (W : Type*) where
  ρ : W
  par : W → W
  lat : W → W
  r0 : W

section models

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Hvilke barn en node teller: i `M2` teller noder i `F` bare barn i `F`. -/
def scope (v : V) : Finset V := if two = true ∧ v ∈ F then F else Finset.univ

/-- Trebarna til `v`. -/
def CH (v : V) : Finset V := F'.filter (fun c => c ∉ U ∧ c ≠ D.ρ ∧ D.par c = v)

/-- `nxt`-barna til `v`. -/
noncomputable def NX (v : V) : Finset V :=
  F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v)

/-- Biten i `v`, gitt en leser `g w i` for bit `i` hos forelder `w`. -/
noncomputable def sb (v : V) (g : V → ℕ → ZMod 2) : ZMod 2 :=
  (if v = D.ρ then 0 else g (D.lat v) (ix v)) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), g (D.lat c) (ix c) +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), g w 0

/-- Leseren for kjernen. -/
def rdp (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) (w : V) (i : ℕ) : ZMod 2 :=
  if h : w ∈ G.parents v then rd (pa ⟨w, h⟩) i else 0

/-- Kjernen. -/
noncomputable def kern (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) : PMF (Val U v) :=
  if v ∈ U then PMF.uniformOfFintype (Val U v)
  else if v ∈ F' then
    (if v = D.r0 then PMF.map (fun n => cst U v (sb G U F F' D two v (rdp G U v pa) + n)) noise
     else PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))))
  else PMF.uniformOfFintype (Val U v)

/-- **Modellen**: `M1` med `two = false`, `M2` med `two = true`. -/
noncomputable def M : G.CausalModel (Val U) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := kern G U F F' D two

lemma kern_lat {v : V} (hv : v ∈ U) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_pos hv]

lemma kern_out {v : V} (hv : v ∉ U) (hF : v ∉ F') (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_neg hv, if_neg hF]

lemma kern_obs {v : V} (hv : v ∉ U) (hF : v ∈ F') (hr : v ≠ D.r0)
    (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))) := by
  unfold kern
  rw [if_neg hv, if_pos hF, if_neg hr]

lemma kern_r0 {v : V} (hv : v ∉ U) (hF : v ∈ F') (hr : v = D.r0)
    (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa =
      PMF.map (fun n => cst U v (sb G U F F' D two v (rdp G U v pa) + n)) noise := by
  unfold kern
  rw [if_neg hv, if_pos hF, if_pos hr]

end models

end PM
end Hedge

#print axioms Hedge.PM.kern_obs
#print axioms Hedge.PM.kern_r0

/-! ## Runde 59: kjernefaktorene for en hel tilordning

For en hel tilordning `s`: `rdS s v w i` leser bit `i` hos `w` hvis `w` er forelder til
`v` (ellers `0`); `rdp_restrict`: kjernens leser er `rdS`. Faktorene (`kfac`) er
`1/|Val U v|` for latente og for observerte utenfor `F'` (`kfac_lat`, `kfac_out`), en
indikator på at biten er `sb` for observerte i `F'` (`kfac_obs`), og `noise` av
`bit + sb` i støyroten (`kfac_r0`; i `ZMod 2` er minus det samme som pluss). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section kfacs

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Leseren fra en hel tilordning. -/
def rdS (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v w : V) (i : ℕ) : ZMod 2 :=
  if w ∈ G.parents v then rd (s ⟨w, Finset.mem_univ w⟩) i else 0

lemma rdp_restrict (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    rdp G U v (s.restrict (Finset.subset_univ (G.parents v))) = rdS G U s v := by
  funext w i
  unfold rdp rdS
  split_ifs <;> rfl

lemma kfac_lat (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ U) :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_lat G U F F' D two hv, PMF.uniformOfFintype_apply]

lemma kfac_out (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∉ F') :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_out G U F F' D two hv hF, PMF.uniformOfFintype_apply]

/-- **Observerte i `F'`**: faktoren er 1 når biten er `sb`, ellers 0. -/
lemma kfac_obs (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∈ F') (hr : v ≠ D.r0) :
    kfac (M G U F F' D two) Finset.univ s v =
      if rd (s ⟨v, Finset.mem_univ v⟩) 0 = sb G U F F' D two v (rdS G U s v) then 1 else 0 := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_obs G U F F' D two hv hF hr, rdp_restrict, PMF.pure_apply]
  simp only [obs_ext hv, rd_cst hv]

/-- **Støyroten**: faktoren er `noise (bit + sb)`. -/
lemma kfac_r0 (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∈ F') (hr : v = D.r0) :
    kfac (M G U F F' D two) Finset.univ s v =
      noise (rd (s ⟨v, Finset.mem_univ v⟩) 0 + sb G U F F' D two v (rdS G U s v)) := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_r0 G U F F' D two hv hF hr, rdp_restrict, PMF.map_apply,
    tsum_eq_single (rd (s ⟨v, Finset.mem_univ v⟩) 0 + sb G U F F' D two v (rdS G U s v))]
  · rw [if_pos]
    exact (obs_ext hv _ _).mpr (by rw [rd_cst hv]; exact (ZMod2.eq_add_iff_eq_add _ _ _).mpr rfl)
  · intro n hn
    rw [if_neg]
    intro h
    have h2 : rd (s ⟨v, Finset.mem_univ v⟩) 0 = sb G U F F' D two v (rdS G U s v) + n := by
      rw [h, rd_cst hv]
    exact hn ((ZMod2.eq_add_iff_eq_add _ _ _).mp h2)

end kfacs

end PM
end Hedge

#print axioms Hedge.PM.kfac_obs
#print axioms Hedge.PM.kfac_r0

/-! ## Runde 60: `sb` uten vakter

`Good`: betingelsene konstruksjonsdataene oppfyller (fra `hedge_spanning`): `ρ` er en
observert node i `F`; for observerte `v ≠ ρ` i `F'` er `par v` observert i `F'` (i `F` når
`v ∈ F`), og `lat v` er latent med kanter til `v` og `par v`; `r0` er en observert rot.
`lb s c` er biten på trekanten `(c, par c)` og `ov s w` verdien til `w`, lest rett fra `s`.
`sb_read`: under `Good` og en hedge er `sb` bare summen av disse (vaktene i `rdS` holder:
`lat v → v`, `lat c → par c`, og `w → nxt w` fra `hedge_nxt`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Betingelsene på konstruksjonsdataene. -/
structure Good (G : DAG V) (U F F' : Finset V) (D : Data V) : Prop where
  ρF : D.ρ ∈ F
  ρU : D.ρ ∉ U
  parF' : ∀ v ∈ F', v ∉ U → v ≠ D.ρ → D.par v ∈ F' ∧ D.par v ∉ U
  parF : ∀ v ∈ F, v ∉ U → v ≠ D.ρ → D.par v ∈ F
  lat : ∀ v ∈ F', v ∉ U → v ≠ D.ρ →
    D.lat v ∈ U ∧ G.edge (D.lat v) v ∧ G.edge (D.lat v) (D.par v)
  r0R : D.r0 ∈ rootsIn G F
  r0U : D.r0 ∉ U

section read

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Biten på trekanten `(c, par c)`. -/
noncomputable def lb (s : Assignment (α := Val U) (Finset.univ : Finset V)) (c : V) : ZMod 2 :=
  rd (s ⟨D.lat c, Finset.mem_univ _⟩) (ix c)

/-- Verdien til en observert node. -/
def ov (s : Assignment (α := Val U) (Finset.univ : Finset V)) (w : V) : ZMod 2 :=
  rd (s ⟨w, Finset.mem_univ w⟩) 0

/-- `sb` lest rett fra tilordningen. -/
noncomputable def sbV (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  (if v = D.ρ then 0 else lb U D s v) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), lb U D s c +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), ov U s w

lemma rdS_edge (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v w : V}
    (h : G.edge w v) (i : ℕ) : rdS G U s v w i = rd (s ⟨w, Finset.mem_univ w⟩) i := by
  unfold rdS
  rw [if_pos (DAG.mem_parents.mpr h)]

/-- **`sb` uten vakter.** -/
theorem sb_read {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∈ F') (hvU : v ∉ U) :
    sb G U F F' D two v (rdS G U s v) = sbV G U F F' D two s v := by
  unfold sb sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ]
        exact rdS_edge G U s (hD.lat v hvF hvU hρ).2.1 (ix v)
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF, hcU, hcρ, hpc⟩ := Finset.mem_filter.mp hc1
      have e := (hD.lat c hcF hcU hcρ).2.2
      rw [hpc] at e
      exact rdS_edge G U s e (ix c)
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwF, -, hwR, hnx⟩ := Finset.mem_filter.mp hw1
    have e := (hedge_nxt hH w hwF hwR).2.2
    rw [hnx] at e
    exact rdS_edge G U s e 0

end read

end PM
end Hedge

#print axioms Hedge.PM.sb_read
