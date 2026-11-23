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
file of step H3 (equal observed distributions in `Hedge/ObsEq`, positivity in
`Hedge/Positivity`, the gap under `do(x)` in `Hedge/DoGapM1` and `Hedge/DoGapM2`) works
from the formulas proved here, and the product models of step H4 (`Hedge/Product`) run
`M` in their first coordinate. `marginal_eq_of_invol` is used for both pairs of models
(`Hedge/ObsEq`, `Hedge/Product`).

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

/-! ## Equal marginals from an involution

`marginal_eq_of_invol`: if an involution `φ` on full assignments keeps the values on `O`
and carries the probability of `M1` to `M2` (`M2.fullJoint (φ s) = M1.fullJoint s`), the
models have the same marginal on `O`. The hedge families in `Identification` each use
their own version of this argument (`full_map`, `obsEq`); here it is proved once for all
graphs and value types. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Equal marginals via an involution** that keeps `O`: the joint of `M2` is the image
of the joint of `M1` under `φ`, and restricting to `O` after `φ` is restricting to `O`. -/
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

/-! ## Value types of the parity models

Every node gets the value type `Fin (kk U v) → ZMod 2`: `kk U v = |V|` for latent nodes
(one bit per edge of the tree, indexed by the lower node of the edge via `ix`) and `1` for
observed nodes (one bit). `rd x i` reads bit number `i` (and gives `0` out of range), so
the kernels can read their parents with no proof obligations. `obs_ext`: two observed
values are equal exactly when their bits are equal. `noise`: the bit `1` with
probability `1/4`, for positivity. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The number of bits of a node: `|V|` for latent nodes, `1` for observed nodes. -/
def kk (U : Finset V) (v : V) : ℕ := if v ∈ U then Fintype.card V else 1

/-- The value type of node `v`: `kk U v` bits. A plain function type, so no type-level
`if` is needed. -/
abbrev Val (U : Finset V) (v : V) : Type := Fin (kk U v) → ZMod 2

/-- Bit number `i` of a value (`0` out of range). -/
def rd {U : Finset V} {v : V} (x : Val U v) (i : ℕ) : ZMod 2 :=
  if h : i < kk U v then x ⟨i, h⟩ else 0

/-- The index, inside a latent value, of the bit of the tree edge whose lower node is
`c`. -/
noncomputable def ix (c : V) : ℕ := (Fintype.equivFin V c).val

/-- An observed node has one bit. -/
lemma kk_obs {U : Finset V} {v : V} (hv : v ∉ U) : kk U v = 1 := if_neg hv

/-- A latent node has `|V|` bits. -/
lemma kk_lat {U : Finset V} {u : V} (hu : u ∈ U) : kk U u = Fintype.card V := if_pos hu

omit [DecidableEq V] in
/-- Every edge index is in range for a latent node. -/
lemma ix_lt (c : V) : ix c < Fintype.card V := (Fintype.equivFin V c).isLt

omit [DecidableEq V] in
/-- Different edges have different indices. -/
lemma ix_inj {c c' : V} (h : ix c = ix c') : c = c' :=
  (Fintype.equivFin V).injective (Fin.ext h)

/-- The constant value with every bit equal to `b` (for an observed node: the value
with bit `b`). -/
def cst (U : Finset V) (v : V) (b : ZMod 2) : Val U v := fun _ => b

/-- Reading the bit of an observed constant value gives `b`. -/
lemma rd_cst {U : Finset V} {v : V} (hv : v ∉ U) (b : ZMod 2) : rd (cst U v b) 0 = b := by
  have h0 : 0 < kk U v := by
    rw [kk_obs hv]
    omega
  simp only [rd, cst, dif_pos h0]

/-- **Two observed values are equal exactly when their bits are equal.** -/
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

/-- An observed value is the constant value of its bit. -/
lemma eq_cst {U : Finset V} {v : V} (hv : v ∉ U) (x : Val U v) : x = cst U v (rd x 0) :=
  (obs_ext hv x _).mpr (rd_cst hv _).symm

/-- The noise bit: `1` with probability `1/4`, `0` with probability `3/4`. -/
noncomputable def noise : PMF (ZMod 2) :=
  PMF.map (fun i : Fin 4 => if i = 0 then (1 : ZMod 2) else 0) (PMF.uniformOfFintype (Fin 4))

end PM
end Hedge

#print axioms Hedge.PM.obs_ext
#print axioms Hedge.PM.eq_cst

/-! ## The parity models `M1` and `M2`

`Data`: the root `ρ` in `F`, the parent pointer `par`, the latent `lat c` behind the tree
edge `(c, par c)`, and the root `r0` with noise. `CH v`: the tree children of `v`
(observed `c ≠ ρ` with `par c = v`). `NX v`: the `nxt` children of `v` (observed
non-roots with `nxt w = v`). `sb`: the bit at `v` is its own tree bit + the tree bits of
its children + the values of its `nxt` children; in `M2` (`two = true`) a node of `F`
counts only children in `F` (`scope`). The kernel: uniform for latent nodes and for
observed nodes outside `F'`; inside `F'` the value is `sb` (plus `noise` at `r0`). Parents
are read with `rd`, guarded by `if h : w ∈ G.parents v`, so the definition has no proof
obligations. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The construction data: the root `ρ` of the tree, the parent pointer `par`, the
latent `lat c` behind the tree edge `(c, par c)`, and the observed root `r0` that carries
the noise. -/
structure Data (W : Type*) where
  ρ : W
  par : W → W
  lat : W → W
  r0 : W

section models

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- The children a node counts: in `M2` a node of `F` counts only children in `F`. -/
def scope (v : V) : Finset V := if two = true ∧ v ∈ F then F else Finset.univ

/-- The tree children of `v`: the observed `c ≠ ρ` in `F'` with `par c = v`. -/
def CH (v : V) : Finset V := F'.filter (fun c => c ∉ U ∧ c ≠ D.ρ ∧ D.par c = v)

/-- The `nxt` children of `v`: the observed non-roots `w` of `F'` with `nxt w = v`. -/
noncomputable def NX (v : V) : Finset V :=
  F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v)

/-- The bit at `v`, given a reader `g w i` for bit `i` of parent `w`: the bit of the
tree edge above `v`, plus the bits of the tree edges to its children, plus the values of
its `nxt` children (all restricted to `scope`). -/
noncomputable def sb (v : V) (g : V → ℕ → ZMod 2) : ZMod 2 :=
  (if v = D.ρ then 0 else g (D.lat v) (ix v)) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), g (D.lat c) (ix c) +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), g w 0

/-- The reader a kernel uses: bit `i` of `w` if `w` is a parent of `v`, else `0`. -/
def rdp (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) (w : V) (i : ℕ) : ZMod 2 :=
  if h : w ∈ G.parents v then rd (pa ⟨w, h⟩) i else 0

/-- The kernel at `v`: uniform for latent nodes and for observed nodes outside `F'`;
for an observed node of `F'` the value `sb`, plus `noise` at `r0`. -/
noncomputable def kern (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) : PMF (Val U v) :=
  if v ∈ U then PMF.uniformOfFintype (Val U v)
  else if v ∈ F' then
    (if v = D.r0 then PMF.map (fun n => cst U v (sb G U F F' D two v (rdp G U v pa) + n)) noise
     else PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))))
  else PMF.uniformOfFintype (Val U v)

/-- **The parity model** on `G`: `M1` for `two = false`, `M2` for `two = true`. -/
noncomputable def M : G.CausalModel (Val U) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := kern G U F F' D two

/-- The kernel of a latent node is uniform. -/
lemma kern_lat {v : V} (hv : v ∈ U) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_pos hv]

/-- The kernel of an observed node outside `F'` is uniform. -/
lemma kern_out {v : V} (hv : v ∉ U) (hF : v ∉ F') (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_neg hv, if_neg hF]

/-- The kernel of an observed node of `F'` other than `r0` is the point mass at `sb`. -/
lemma kern_obs {v : V} (hv : v ∉ U) (hF : v ∈ F') (hr : v ≠ D.r0)
    (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))) := by
  unfold kern
  rw [if_neg hv, if_pos hF, if_neg hr]

/-- The kernel of `r0` is `sb` plus noise. -/
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

/-! ## The kernel factors of a full assignment

For a full assignment `s`: `rdS s v w i` reads bit `i` of `w` if `w` is a parent of `v`
(else `0`); `rdp_restrict`: the kernel's reader is `rdS`. The factors (`kfac`) are
`1/|Val U v|` for latent nodes and for observed nodes outside `F'` (`kfac_lat`,
`kfac_out`), an indicator that the bit is `sb` for observed nodes of `F'` (`kfac_obs`),
and `noise` of `bit + sb` at the noisy root (`kfac_r0`; in `ZMod 2` minus is the same as
plus). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section kfacs

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- The reader on a full assignment: bit `i` of `w` if `w` is a parent of `v`, else
`0`. -/
def rdS (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v w : V) (i : ℕ) : ZMod 2 :=
  if w ∈ G.parents v then rd (s ⟨w, Finset.mem_univ w⟩) i else 0

/-- On the restriction of a full assignment to the parents, the kernel's reader is
`rdS`. -/
lemma rdp_restrict (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    rdp G U v (s.restrict (Finset.subset_univ (G.parents v))) = rdS G U s v := by
  funext w i
  unfold rdp rdS
  split_ifs <;> rfl

/-- **Latent nodes**: the factor is `1/|Val U v|`. -/
lemma kfac_lat (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ U) :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_lat G U F F' D two hv, PMF.uniformOfFintype_apply]

/-- **Observed nodes outside `F'`**: the factor is `1/|Val U v|`. -/
lemma kfac_out (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∉ F') :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_out G U F F' D two hv hF, PMF.uniformOfFintype_apply]

/-- **Observed nodes of `F'`**: the factor is 1 when the bit is `sb`, else 0. -/
lemma kfac_obs (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∈ F') (hr : v ≠ D.r0) :
    kfac (M G U F F' D two) Finset.univ s v =
      if rd (s ⟨v, Finset.mem_univ v⟩) 0 = sb G U F F' D two v (rdS G U s v) then 1 else 0 := by
  rw [kfac_univ]
  show kern G U F F' D two v _ _ = _
  rw [kern_obs G U F F' D two hv hF hr, rdp_restrict, PMF.pure_apply]
  simp only [obs_ext hv, rd_cst hv]

/-- **The noisy root**: the factor is `noise (bit + sb)`. -/
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

/-! ## `sb` without guards

`Good`: the conditions the construction data satisfy (from `hedge_spanning`): `ρ` is an
observed node of `F`; for observed `v ≠ ρ` in `F'`, `par v` is observed and in `F'` (in
`F` when `v ∈ F`), and `lat v` is latent with edges to `v` and `par v`; `r0` is an
observed root. `lb s c` is the bit on the tree edge `(c, par c)` and `ov s w` the value of
`w`, read straight from `s`. `sb_read`: under `Good` and a hedge, `sb` is just the sum of
these (the guards in `rdS` hold: `lat v → v`, `lat c → par c`, and `w → nxt w` from
`hedge_nxt`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The conditions on the construction data. -/
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

/-- The bit on the tree edge `(c, par c)`, read from the latent `lat c`. -/
noncomputable def lb (s : Assignment (α := Val U) (Finset.univ : Finset V)) (c : V) : ZMod 2 :=
  rd (s ⟨D.lat c, Finset.mem_univ _⟩) (ix c)

/-- The value (bit) of an observed node. -/
def ov (s : Assignment (α := Val U) (Finset.univ : Finset V)) (w : V) : ZMod 2 :=
  rd (s ⟨w, Finset.mem_univ w⟩) 0

/-- `sb` read straight from the assignment, with no parent guards. -/
noncomputable def sbV (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  (if v = D.ρ then 0 else lb U D s v) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), lb U D s c +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), ov U s w

/-- Along an edge `w → v`, `rdS` reads the assignment directly. -/
lemma rdS_edge (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v w : V}
    (h : G.edge w v) (i : ℕ) : rdS G U s v w i = rd (s ⟨w, Finset.mem_univ w⟩) i := by
  unfold rdS
  rw [if_pos (DAG.mem_parents.mpr h)]

/-- **`sb` without guards**: under `Good` and a hedge, every parent `sb` reads is a
parent, so `sb` on a full assignment equals `sbV`. -/
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
