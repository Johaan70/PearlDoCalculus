import PearlDoCalculus.Identification.LatentTree

/-!
# Root-path configurations and their models

This file sets up the c-forests with several roots used for the non-identifiability
results of `Identification/RootPath`.

* `MultiRoot`: a latent tree over `x` and the nodes `nd₀, …, nd_{n+1}` with a
  directed forest pattern among the nodes and `x → nd₀`, together with the helpers `ext`
  and `chan_mix`.
* `RootPath`: the same, but `x` may point into any root `nd_r`; the latent path from
  `u₀` to `u_r` is given by a parity condition. The file defines the graphs, the parity
  algebra and the three models A, B and C with their kernel factors. The latent values
  of model C are the bottom-up solution `forestSolution` of `Identification/LatentTree`.

Why it is needed: these configurations are the hedges that the proof of `tian_iff` meets.
A shortest chain of latent steps from `x` to a child of `x` (`TianIff`) is a latent path
with every observed node a root, an `RT` structure of `Identification/RootTree`, which
becomes a `RootPath` once the path is built. Unlike the families of `HedgeTemplate`, the
effect here is on the set of roots, not on one `y`, and the proof uses a third model C to
compute the observed marginals.

How the proof goes: model A is the parity model (every `nd_k` is the sum (mod 2) of its
latent parents and its children in the forest, `x` a noisy copy of `u₀`); model B moves
the noisy channel from `x` to `nd_r`; model C reverses the latent edges (`x` and the `u`s
become children of the nodes), so that the nodes `nd_k` are independent uniform bits and
the observed marginals are easy to compute. The algebra in `ZMod 2` rests on one
identity (`resid`): the residuals of all equations add up to the sum over the roots plus
`u₀`. The proofs that use the models are in `Identification/RootPath`.

Main results: the configurations `MultiRoot` and `RootPath`, the models
`RootPath.NA`, `NB`, `NC`, and the identities `RootPath.resid`, `eqs_sum`,
`eqr_iff` and `keyAC`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## C-forests with several roots

A latent tree over `x` and the nodes `nd₀, …, nd_{n+1}` (with `x` a leaf, attached to
`nd₀` through `u₀`), and a directed forest pattern: every node points to a parent `dp k`
or is a root (`dp k = none`). `x → nd₀`, and `nd₀` is a root. Then `P(R | do(x))` is not
identifiable, where `R` is the set of roots.

This section only holds the configuration `MultiRoot` and the helpers `ext` and `chan_mix`.
The proof is the one for root paths (`RootPath`, next section), and the theorem
`MultiRoot.not_identifiable` is proved in `Identification/RootPath` as the corollary with
`r = 0` and the path `{u₀}`. -/

namespace Identification

open HedgeChain (ev xx xb chan_symm)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace MultiRoot

/-- The value of a partial assignment at a node, with `false` outside its domain. -/
def ext {S : Finset V} (pa : Assignment (α := fun _ : V => Bool) S) (v : V) : Bool :=
  if h : v ∈ S then pa ⟨v, h⟩ else false

/-- `ext` of a restricted full assignment is the value of the full assignment. -/
lemma ext_restrict (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    {S : Finset V} {v : V} (hv : v ∈ S) :
    ext (s.restrict (Finset.subset_univ S)) v = ev s v := by
  simp [ext, hv, Assignment.restrict, ev]

/-- The channel identity behind moving the noise from `x` to a root: shifting the input by `b
xor c` and evaluating at `b` is the channel from `a` evaluated at `c`. -/
lemma chan_mix (a b c : Bool) : Bow.chan (xor a (xor b c)) b = Bow.chan c a := by
  rw [Bow.chan_apply, Bow.chan_apply]
  cases a <;> cases b <;> cases c <;> rfl

end MultiRoot

/-- The configuration with several roots: `x`, the nodes `nd_k`, their latents `u_k`, the
latent tree `bp` (rooted at `0`) with its height function `ht`, the directed forest `dp`
(with `nd₀` a root), the edges with `x → nd₀`, and the facts that all these nodes are
different. -/
structure MultiRoot (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hdp0 : dp 0 = none
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd 0)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace MultiRoot

variable {G : DAG V} {n : ℕ} (P : MultiRoot G n)

/-- The roots of the directed forest. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- The roots as nodes. -/
def Y : Finset V := P.Rt.image P.nd

/-- `0` is a root. -/
lemma mem_Rt0 : (0 : Fin (n + 2)) ∈ P.Rt := by simp [Rt, P.hdp0]

/-- Membership in the set of roots. -/
lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

end MultiRoot

end Identification

/-! ## Root paths: `x` may point into any root

As in the previous section, but `x → nd_r` for an arbitrary root `r`, not only `nd₀`. The
latent neighbour of `x` is still `u₀`. A *path* `pth` of latents from `u₀` to `u_r` is
given by the parity condition

  `pth k + #{children j of k on the path} = [k = r]`   (mod 2),

that is, every node has an even number of path latents next to it, except `nd_r`, which
has one.

* The bijection shifts the whole path by `ΣR`, the sum over the roots. The parity then
  changes only at `nd_r`.
* Model B puts the noisy channel on `nd_r` instead of `nd₀`; otherwise everything is as in
  the previous section. Two roots and the configuration `MultiRoot` are special cases. -/

namespace Identification

open HedgeChain (ev xx xb chan_symm)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

open MultiRoot (ext ext_restrict chan_mix)

/-- The root-path configuration: as `MultiRoot`, but with `x → nd_r` for a root `r` and
a path `pth` of latents from `u₀` to `u_r`, given by the parity condition `hpk`. -/
structure RootPath (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  r : Fin (n + 2)
  pth : Fin (n + 2) → Bool
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hr : dp r = none
  hp0 : pth 0 = true
  hpk : ∀ k, ofBool (pth k) + (∑ j, if bp j = some k then ofBool (pth j) else 0) =
    if k = r then 1 else 0
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd r)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace RootPath

variable {G : DAG V} {n : ℕ} (P : RootPath G n)

/-- The roots of the directed forest. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- The roots as nodes. -/
def Y : Finset V := P.Rt.image P.nd

/-- `r` is a root. -/
lemma mem_Rtr : P.r ∈ P.Rt := by simp [Rt, P.hr]

/-- Membership in the set of roots. -/
lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

/-! ### The graphs -/

/-- The graph of model A: `u₀ → x`, the latent edges, and the directed forest. -/
noncomputable def gA : DAG V where
  edge a b := (a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)

/-- The graph of model B: the latent edges, the directed forest, and `x → nd_r`. -/
noncomputable def gB : DAG V where
  edge a b := (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hxr

/-- The graph of model C: every root points to `x`, and every node points to every latent. -/
noncomputable def gC : DAG V where
  edge a b := (∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨ (∃ k j, a = P.nd k ∧ b = P.u j)
  decEdge := fun _ _ => Classical.dec _
  rank := fun v => if ∃ k, P.nd k = v then 0 else 1
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, _, h1, h2⟩ | ⟨k, j, h1, h2⟩
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.x := fun ⟨k', e⟩ => P.hndx k' e
      simp [this]
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.u j := fun ⟨k', e⟩ => P.hund j k' e.symm
      simp [this]

/-- The edges of the graph of model A. -/
lemma eA (a b : V) : P.gA.edge a b ↔ ((a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)) := Iff.rfl
/-- The edges of the graph of model B. -/
lemma eB (a b : V) : P.gB.edge a b ↔ ((∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)) := Iff.rfl
/-- The edges of the graph of model C. -/
lemma eC (a b : V) : P.gC.edge a b ↔ ((∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨
    (∃ k j, a = P.nd k ∧ b = P.u j)) := Iff.rfl


/-- The graph of model A is a subgraph of `G`. -/
lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.eA a v).mp ha with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
  · rw [h1, h2]; exact P.hux
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd

/-- The graph of model B is a subgraph of `G`. -/
lemma hsB : ∀ v, P.gB.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.eB a v).mp ha with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd
  · rw [h1, h2]; exact P.hxr

/-! ### The parity at a node -/

/-- The parity of the parents of `nd_k` in model A, read off a value function `g`. -/
def parZ (k : Fin (n + 2)) (g : V → Bool) : ZMod 2 :=
  ofBool (g (P.u k)) + (∑ j, if P.bp j = some k then ofBool (g (P.u j)) else 0) +
    ∑ j, if P.dp j = some k then ofBool (g (P.nd j)) else 0

/-- `parZ` depends only on the values at the `u`s and the `nd`s. -/
lemma parZ_congr (k : Fin (n + 2)) {g h : V → Bool} (hu : ∀ j, g (P.u j) = h (P.u j))
    (hn : ∀ j, g (P.nd j) = h (P.nd j)) : P.parZ k g = P.parZ k h := by
  simp only [parZ, hu, hn]

/-- `parZ` read off the parents of `nd_k` in model A is `parZ` of the full assignment. -/
lemma parZ_extA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gA.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩))))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

/-- `parZ` read off the parents of `nd_k` in model B is `parZ` of the full assignment. -/
lemma parZ_extB (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gB.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inl ⟨k, rfl, rfl⟩)))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

/-! ### The algebra -/


/-- **The residual identity.** The sum of the residuals over all nodes is
`Σ_{roots} N + L₀`, whatever the values. -/
lemma resid (L N : Fin (n + 2) → ZMod 2) :
    ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = (∑ k ∈ P.Rt, N k) + L 0 := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then L j else 0) = if j = 0 then 0 else L j := by
    intro j
    by_cases hj : j = 0
    · have hb : P.bp j = none := (P.hbp0 j).mpr hj
      rw [hb]
      simp [hj]
    · cases hb : P.bp j with
      | none => exact absurd ((P.hbp0 j).mp hb) hj
      | some k0 => simp [hj]
  have h2 : ∀ j, (∑ k, if P.dp j = some k then N j else 0) =
      if P.dp j = none then 0 else N j := by
    intro j
    cases hd : P.dp j <;> simp
  have hB : ∑ k, (∑ j, if P.bp j = some k then L j else 0) =
      ∑ j, (if j = 0 then 0 else L j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hD : ∑ k, (∑ j, if P.dp j = some k then N j else 0) =
      ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hL : ∑ j, L j = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
    calc ∑ j, L j = ∑ j, ((if j = 0 then L j else 0) + (if j = 0 then 0 else L j)) :=
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
      _ = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp
  have hN : ∑ j, N j = (∑ k ∈ P.Rt, N k) + ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Rt, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hsplit : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) =
      ∑ k, N k + ∑ k, L k + ∑ k, (∑ j, if P.bp j = some k then L j else 0) +
        ∑ k, (∑ j, if P.dp j = some k then N j else 0) := by
    simp only [Finset.sum_add_distrib]
    ring
  rw [hsplit, hB, hD, hL, hN]
  have t1 := CharTwo.add_self_eq_zero (∑ j, (if j = 0 then 0 else L j))
  have t2 := CharTwo.add_self_eq_zero (∑ j, (if P.dp j = none then 0 else N j))
  linear_combination t1 + t2

/-- If all the equations hold, then `L₀` is the sum over the roots. -/
lemma eqs_sum (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [← hE k]; exact CharTwo.add_self_eq_zero _)
  rw [hz] at h
  exact ZMod2.eq_of_zero_eq_add _ _ h

/-- If the equations outside `nd_r` hold, then the equation at `nd_r` is equivalent to
`L₀ = Σ_{roots} N`. -/
lemma eqr_iff (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, k ≠ P.r → N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    (N P.r = L P.r + (∑ j, if P.bp j = some P.r then L j else 0) +
      ∑ j, if P.dp j = some P.r then N j else 0) ↔ L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k ∈ Finset.univ.erase P.r, (N k + (L k +
      (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k hk => by
      rw [← hE k (Finset.ne_of_mem_erase hk)]; exact CharTwo.add_self_eq_zero _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P.r), hz, add_zero] at h
  exact ZMod2.eq_iff_eq_of_add_eq_add _ _ _ _ h

/-! ### The latent solution of model C -/

/-- `r_k = N_k +` the children of `k`, read off `g`: the right-hand side of the forest system. -/
def Rg (g : V → Bool) (k : Fin (n + 2)) : ZMod 2 :=
  ofBool (g (P.nd k)) + ∑ j, if P.dp j = some k then ofBool (g (P.nd j)) else 0

/-- The equations of model A at the nodes hold exactly when every latent has the value of the
bottom-up solution, which is how model C sets them. -/
lemma keyAC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (∀ k, ev s (P.nd k) = toBool (P.parZ k (ev s))) ↔
      ∀ j, ev s (P.u j) = toBool (forestSolution P.bp P.ht (P.Rg (ev s)) j) := by
  have step : ∀ k, (ev s (P.nd k) = toBool (P.parZ k (ev s))) ↔
      (ofBool (ev s (P.u k)) = P.Rg (ev s) k +
        ∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0) := by
    intro k
    rw [eq_toBool_iff]
    exact ZMod2.eq_add_add_iff_eq_add_add _ _ _ _
  exact (forall_congr' step).trans ((forall_eq_forestSolution_iff P.hht (P.Rg (ev s))
    (fun k => ofBool (ev s (P.u k)))).trans (forall_congr' fun j => (eq_toBool_iff _ _).symm))

/-! ### The models -/

/-- `u₀` is a parent of `x` in the graph of model A. -/
lemma pAx : P.u 0 ∈ P.gA.parents P.x := DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inl ⟨rfl, rfl⟩))
/-- `x` is a parent of `nd_r` in the graph of model B. -/
lemma pBx : P.x ∈ P.gB.parents (P.nd P.r) :=
  DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
/-- A root is a parent of `x` in the graph of model C. -/
lemma pCx (k : Fin (n + 2)) (hk : P.dp k = none) : P.nd k ∈ P.gC.parents P.x :=
  DAG.mem_parents.mpr ((P.eC _ _).mpr (Or.inl ⟨k, hk, rfl, rfl⟩))
/-- Every node is a parent of every latent in the graph of model C. -/
lemma pCu (k j : Fin (n + 2)) : P.nd k ∈ P.gC.parents (P.u j) :=
  DAG.mem_parents.mpr ((P.eC _ _).mpr (Or.inr ⟨k, j, rfl, rfl⟩))

/-- Model A: `x` a noisy copy of `u₀`, every `nd_k` the parity of its parents, every other node
uniform. -/
noncomputable def NA : P.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (ext pa (P.u 0))
    else if h : ∃ k, P.nd k = v then PMF.pure (toBool (P.parZ (Classical.choose h) (ext pa)))
    else PMF.uniformOfFintype Bool

/-- Model B: `nd_r` a noisy copy of `x` shifted by its parity, every other `nd_k` the parity of
its parents, `u₀` fixed to `false`, every other node uniform. -/
noncomputable def NB : P.gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h : ∃ k, P.nd k = v then
      (if Classical.choose h = P.r then Bow.chan (xor (ext pa P.x) (toBool (P.parZ P.r (ext pa))))
       else PMF.pure (toBool (P.parZ (Classical.choose h) (ext pa))))
    else if v = P.u 0 then PMF.pure false
    else PMF.uniformOfFintype Bool

/-- Model C: `x` a noisy copy of the sum over the roots, every latent the bottom-up solution of
the forest system, every other node uniform. -/
noncomputable def NC : P.gC.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ext pa (P.nd k))))
    else if h : ∃ j, P.u j = v then
      PMF.pure (toBool (forestSolution P.bp P.ht (P.Rg (ext pa)) (Classical.choose h)))
    else PMF.uniformOfFintype Bool

/-- The kernel of `x` in model A. -/
lemma NA_x (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) :
    P.NA.kernel P.x pa = Bow.chan (ext pa (P.u 0)) := by
  simp [NA]

/-- The kernel of `nd_k` in model A. -/
lemma NA_nd (k : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) :
    P.NA.kernel (P.nd k) pa = PMF.pure (toBool (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NA, if_neg (P.hndx k), dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h)]

/-- The kernel of any other node in model A is uniform. -/
lemma NA_o {v : V} (hvx : v ≠ P.x) (hv : ∀ k, P.nd k ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents v)) :
    P.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NA, if_neg hvx, dif_neg h]

/-- The kernel of `nd_r` in model B. -/
lemma NB_ndr (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd P.r))) :
    P.NB.kernel (P.nd P.r) pa = Bow.chan (xor (ext pa P.x) (toBool (P.parZ P.r (ext pa)))) := by
  have h : ∃ k', P.nd k' = P.nd P.r := ⟨P.r, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = P.r from P.ndinj (Classical.choose_spec h), if_pos rfl]

/-- The kernel of `nd_k`, `k ≠ r`, in model B. -/
lemma NB_nd (k : Fin (n + 2)) (hk : k ≠ P.r)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd k))) :
    P.NB.kernel (P.nd k) pa = PMF.pure (toBool (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h), if_neg hk]

/-- The kernel of `u₀` in model B. -/
lemma NB_u0 (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.u 0))) :
    P.NB.kernel (P.u 0) pa = PMF.pure false := by
  have h : ¬ ∃ k, P.nd k = P.u 0 := fun ⟨k, hk⟩ => P.hund 0 k hk.symm
  simp only [NB, dif_neg h]
  all_goals rfl

/-- The kernel of any other node in model B is uniform. -/
lemma NB_o {v : V} (hv : ∀ k, P.nd k ≠ v) (hv0 : v ≠ P.u 0)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents v)) :
    P.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NB, dif_neg h, if_neg hv0]

/-- The kernel of `x` in model C. -/
lemma NC_x (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents P.x)) :
    P.NC.kernel P.x pa = Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ext pa (P.nd k)))) := by
  simp [NC]

/-- The kernel of `u_j` in model C. -/
lemma NC_u (j : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents (P.u j))) :
    P.NC.kernel (P.u j) pa = PMF.pure (toBool (forestSolution P.bp P.ht (P.Rg (ext pa)) j)) := by
  have h : ∃ j', P.u j' = P.u j := ⟨j, rfl⟩
  simp only [NC, if_neg (P.hux' j), dif_pos h]
  rw [show Classical.choose h = j from P.uinj (Classical.choose_spec h)]

/-- The kernel of any other node in model C is uniform. -/
lemma NC_o {v : V} (hvx : v ≠ P.x) (hv : ∀ j, P.u j ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents v)) :
    P.NC.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, P.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [NC, if_neg hvx, dif_neg h]

/-- Model A as a model on `G`. -/
noncomputable def mA : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsA P.NA
/-- Model B as a model on `G`. -/
noncomputable def mB : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsB P.NB

/-- `Rg` read off the parents of a latent in model C is `Rg` of the full assignment. -/
lemma Rg_ext (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    P.Rg (ext (s.restrict (Finset.subset_univ (P.gC.parents (P.u j))))) = P.Rg (ev s) := by
  funext k
  unfold Rg
  rw [ext_restrict s (P.pCu k j)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [ext_restrict s (P.pCu i j)]
  · rfl

/-! ### The kernel factors -/

/-- The remaining nodes: all except `x`, the `u`s and the `nd`s. -/
def R5 : Finset V := (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd))ᶜ

/-- Membership in the remaining nodes. -/
lemma mem_R5 {v : V} : v ∈ P.R5 ↔ v ≠ P.x ∧ (∀ j, P.u j ≠ v) ∧ (∀ k, P.nd k ≠ v) := by
  simp [R5]

/-- A product over all nodes splits into the factors at `x`, the `u`s, the `nd`s and the
remaining nodes. -/
lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f P.x * ((∏ j, f (P.u j)) * ((∏ k, f (P.nd k)) * ∏ v ∈ P.R5, f v)) := by
  rw [← Finset.prod_mul_prod_compl (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd)) f]
  have hx : P.x ∉ Finset.univ.image P.u ∪ Finset.univ.image P.nd := by
    simp [P.hux', P.hndx]
  have hd : Disjoint (Finset.univ.image P.u) (Finset.univ.image P.nd) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨k, hk⟩ := hb
    exact P.hund j k hk.symm
  rw [Finset.prod_insert hx, Finset.prod_union hd]
  rw [Finset.prod_image P.uinj.injOn, Finset.prod_image P.ndinj.injOn]
  simp only [R5, mul_assoc]

/-- The uniform probability `1/2` of a bit. -/
noncomputable abbrev c2 : ℝ≥0∞ := (Fintype.card Bool : ℝ≥0∞)⁻¹

/-- The factor of `x` in model A. -/
lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NA Finset.univ s P.x = Bow.chan (ev s (P.u 0)) (ev s P.x) := by
  rw [kfac_univ, P.NA_x, ext_restrict s P.pAx]
  all_goals rfl

/-- The factor of `u_j` in model A is `1/2`. -/
lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.u j) = c2 := by
  rw [kfac_univ, P.NA_o (P.hux' j) (fun k e => P.hund j k e.symm),
    PMF.uniformOfFintype_apply]

/-- The factor of `nd_k` in model A. -/
lemma A_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.nd k) = PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) := by
  rw [kfac_univ, P.NA_nd, P.parZ_extA]
  all_goals rfl

/-- The factor of a remaining node in model A is `1/2`. -/
lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NA Finset.univ s v = c2 := by
  obtain ⟨h1, _, h3⟩ := P.mem_R5.mp hv
  rw [kfac_univ, P.NA_o h1 h3, PMF.uniformOfFintype_apply]

/-- The factor of `x` in model B is `1/2`. -/
lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t P.x = c2 := by
  rw [kfac_univ, P.NB_o P.hndx (fun e => P.hux' 0 e.symm), PMF.uniformOfFintype_apply]

/-- The factor of `u₀` in model B. -/
lemma B_u0 (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.u 0) = PMF.pure false (ev t (P.u 0)) := by
  rw [kfac_univ, P.NB_u0]
  all_goals rfl

/-- The factor of `u_j`, `j ≠ 0`, in model B is `1/2`. -/
lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : j ≠ 0) : kfac P.NB Finset.univ t (P.u j) = c2 := by
  rw [kfac_univ, P.NB_o (fun k e => P.hund j k e.symm)
    (fun e => hj (P.uinj e)), PMF.uniformOfFintype_apply]

/-- The factor of `nd_r` in model B. -/
lemma B_ndr (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.nd P.r) =
      Bow.chan (xor (ev t P.x) (toBool (P.parZ P.r (ev t)))) (ev t (P.nd P.r)) := by
  rw [kfac_univ, P.NB_ndr, P.parZ_extB, ext_restrict t P.pBx]
  all_goals rfl

/-- The factor of `nd_k`, `k ≠ r`, in model B. -/
lemma B_nd (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2))
    (hk : k ≠ P.r) :
    kfac P.NB Finset.univ t (P.nd k) = PMF.pure (toBool (P.parZ k (ev t))) (ev t (P.nd k)) := by
  rw [kfac_univ, P.NB_nd k hk, P.parZ_extB]
  all_goals rfl

/-- The factor of a remaining node in model B is `1/2`. -/
lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NB Finset.univ t v = c2 := by
  obtain ⟨_, h2, h3⟩ := P.mem_R5.mp hv
  rw [kfac_univ, P.NB_o h3 (fun e => h2 0 e.symm), PMF.uniformOfFintype_apply]

/-- The factor of `x` in model C. -/
lemma C_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NC Finset.univ s P.x =
      Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ev s (P.nd k)))) (ev s P.x) := by
  have hs : ∑ k ∈ P.Rt, ofBool (ext (s.restrict (Finset.subset_univ (P.gC.parents P.x))) (P.nd k)) =
      ∑ k ∈ P.Rt, ofBool (ev s (P.nd k)) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [ext_restrict s (P.pCx k (by simpa [Rt] using hk))])
  rw [kfac_univ, P.NC_x, hs]
  all_goals rfl

/-- The factor of `u_j` in model C. -/
lemma C_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.u j) =
      PMF.pure (toBool (forestSolution P.bp P.ht (P.Rg (ev s)) j)) (ev s (P.u j)) := by
  rw [kfac_univ, P.NC_u, P.Rg_ext]
  all_goals rfl

/-- The factor of `nd_k` in model C is `1/2`. -/
lemma C_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.nd k) = c2 := by
  rw [kfac_univ, P.NC_o (P.hndx k) (fun j => P.hund j k), PMF.uniformOfFintype_apply]

/-- The factor of a remaining node in model C is `1/2`. -/
lemma C_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NC Finset.univ s v = c2 := by
  obtain ⟨h1, h2, _⟩ := P.mem_R5.mp hv
  rw [kfac_univ, P.NC_o h1 h2, PMF.uniformOfFintype_apply]

end RootPath
end Identification
