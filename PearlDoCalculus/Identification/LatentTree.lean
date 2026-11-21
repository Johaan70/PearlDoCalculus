import PearlDoCalculus.Identification.HedgeTemplate

/-!
# Latent trees

Hedge counter-models for graphs whose latent connections form a tree over `x` and the
observed nodes, and whose directed edges form a tree towards `y`. Here `x` may have
several latent neighbours.

Why it is needed: it covers a large family of non-identifiable graphs, and it holds the
bottom-up solution of a forest system (`forestSolution`), which
`Identification/RootPathModels` uses for the latent values of its model C and so, through
`RootPath` and `RootTree`, the proof of `tian_iff`. The theorem
`LatentTree.not_identifiable` itself is a special case of the hedge criterion
(`Hedge.PM.hedge_not_ident`) and has no other users.

How the proof goes: model A is the parity model: every observed node `nd_k` is the sum
(mod 2) of its latent parents and its children in the directed tree, and `x` is a noisy
copy of the sum of its latent neighbours. The system of equations is solved from the
bottom up in the latent tree (`forestSolution`, stated for any forest with a height
function, so that `Identification/RootPathModels` uses it too), and the value of `x`'s
neighbours equals `y` by a double count over both trees (`dc`). This makes the
configuration an instance of `HedgeTemplate` (`LatentTree.toHedgeTemplate`), and the
template does the rest.

Main results: `Identification.forall_eq_forestSolution_iff` (the forest system has
exactly one solution), `Identification.LatentTree.not_identifiable`.

(The versions for sets `X`, `HedgeTmpl.Tm.not_ident_X` and
`latentTree_not_identifiable_XY`, were deleted in v4.162, and the version for sets `Y`,
`latentTree_not_identifiable_set`, in v4.163; both are covered by the hedge criterion
`Hedge.PM.hedge_not_ident_Y` and kept at tag `v4.152`.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Bottom-up solution of a forest system

Both the latent tree here (`LatentTree`) and the root paths of `Identification/RootPathModels`
(`RootPath`) solve a system `ℓ k = R k + Σ_{j : bp j = some k} ℓ j`, where `bp j` is
the parent of `j` in a forest (`none` for a root). A height function `ht` with
`ht j < ht k` whenever `bp j = some k` makes the forest well-founded. Substituting
`m` times from the leaves upwards (`forestSubst`) fixes every node of height `≤ m`, so
after `sup ht + 1` rounds (`forestSolution`) the system has exactly one solution. -/

namespace Identification

section ForestSolution

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
variable {bp : ι → Option ι} {ht : ι → ℕ}

/-- `m` rounds of bottom-up substitution in the system
`ℓ k = R k + Σ_{j : bp j = some k} ℓ j`. -/
def forestSubst (bp : ι → Option ι) (R : ι → A) : ℕ → ι → A
  | 0, k => R k
  | m + 1, k => R k + ∑ j, if bp j = some k then forestSubst bp R m j else 0

/-- The solution of the forest system: one round more than the largest height. -/
def forestSolution (bp : ι → Option ι) (ht : ι → ℕ) (R : ι → A) : ι → A :=
  forestSubst bp R (Finset.univ.sup ht + 1)

/-- A node of height `≤ m` is already fixed after `m` rounds. -/
lemma forestSubst_succ_of_le (hht : ∀ j k, bp j = some k → ht j < ht k) (R : ι → A) :
    ∀ m k, ht k ≤ m → forestSubst bp R (m + 1) k = forestSubst bp R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if bp j = some k then forestSubst bp R 0 j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (hht j k h) (by omega)
      · rfl
    show R k + _ = R k
    rw [hz, add_zero]
  | succ m ih =>
    intro k hk
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := hht j k h; omega)
    · rfl

/-- Any solution `ℓ` of the system agrees with `m` rounds of substitution on the nodes of
height `≤ m`. -/
lemma eq_forestSubst_of_le (hht : ∀ j k, bp j = some k → ht j < ht k) (R ℓ : ι → A)
    (hE : ∀ k, ℓ k = R k + ∑ j, if bp j = some k then ℓ j else 0) :
    ∀ m k, ht k ≤ m → ℓ k = forestSubst bp R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if bp j = some k then ℓ j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (hht j k h) (by omega)
      · rfl
    show ℓ k = R k
    rw [hE k, hz, add_zero]
  | succ m ih =>
    intro k hk
    rw [hE k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := hht j k h; omega)
    · rfl

/-- `ℓ` solves the forest system if and only if it is `forestSolution`. -/
lemma forall_eq_forestSolution_iff (hht : ∀ j k, bp j = some k → ht j < ht k)
    (R ℓ : ι → A) :
    (∀ k, ℓ k = R k + ∑ j, if bp j = some k then ℓ j else 0) ↔
      ∀ k, ℓ k = forestSolution bp ht R k := by
  have ht_le : ∀ k, ht k ≤ Finset.univ.sup ht := fun k => Finset.le_sup (Finset.mem_univ k)
  constructor
  · intro hE k
    exact eq_forestSubst_of_le hht R ℓ hE _ k (by have := ht_le k; omega)
  · intro h k
    rw [h k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rw [h j, forestSolution, forestSubst_succ_of_le hht R _ j (ht_le j)]
    · rfl

end ForestSolution

end Identification

/-! ## Latent trees

The latent connections form a tree over `x` and the observed nodes
`nd₀, …, nd_{n+1}` (with `y = nd_{n+1}`). Every node `nd_k` has its own latent
`u_k` towards its parent `bp k` in the tree (or towards `x` when `bp k = none`). The
directed edges form a tree towards `y`: every `nd_j` (`j ≤ n`) points to `nd_{dp j}`. This
includes the paths with a tree of `Identification/HedgeTemplate`. Here `x` may have
several latent neighbours: every `u_j` with `bp j = none` points to `x`, and `x` is a
noisy copy of their sum.

Model A is the parity model. The system of equations is solved from the bottom up in the
latent tree (`forestSolution`, with a height function `ht` that puts children lower than
their parents), and the sum of `x`'s latent neighbours equals `y` by a double count over
both trees (`dc`). -/

namespace Identification

open HedgeChain (ev)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A latent tree with a directed tree towards `y`: the observed nodes `nd_k` (with
`y = nd_{n+1}`), their latents `u_k`, the latent tree `bp` with its height function `ht`,
the directed tree `dp`, the edges, and the facts that all these nodes are different. -/
structure LatentTree (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 1) → Fin (n + 2)
  hht : ∀ j k, bp j = some k → ht j < ht k
  hux : ∀ j, bp j = none → G.edge (u j) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j, G.edge (nd j.castSucc) (nd (dp j))
  hxy : G.edge x (nd (Fin.last (n + 1)))
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace LatentTree

variable {G : DAG V} {n : ℕ} (P : LatentTree G n)

/-- The graph of model A: the latent edges and the edges of the directed tree, without `x → y`. -/
noncomputable def gA : DAG V where
  edge a b := (∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hux j0 h0)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j)

/-- The edges of the graph of model A. -/
lemma gA_edge (a b : V) : P.gA.edge a b ↔ ((∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨
    (∃ k, a = P.u k ∧ b = P.nd k) ∨ (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))) := Iff.rfl

/-- A latent `u_j` with `bp j = none` is a parent of `x` in the graph of model A. -/
lemma pxu (j : Fin (n + 2)) (h : P.bp j = none) : P.u j ∈ P.gA.parents P.x :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inl ⟨j, h, rfl, rfl⟩))
/-- `u_k` is a parent of `nd_k` in the graph of model A. -/
lemma pnu (k : Fin (n + 2)) : P.u k ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩)))
/-- `u_j` is a parent of `nd_k` when `bp j = some k`. -/
lemma pnb (j k : Fin (n + 2)) (h : P.bp j = some k) : P.u j ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))
/-- `nd_j` is a parent of `nd_{dp j}` in the graph of model A. -/
lemma pnd (j : Fin (n + 1)) (k : Fin (n + 2)) (h : P.dp j = k) :
    P.nd j.castSucc ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, rfl, by rw [h]⟩))))

/-- The graph of model A is a subgraph of `G`. -/
lemma gA_parents_subset : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.gA_edge a v).mp ha with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ |
      ⟨j, h1, h2⟩
  · rw [h1, h2]; exact P.hux j0 h0
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j

/-- Every parent in the graph of model A is a `u` or one of `nd₀, …, nd_n`. -/
lemma src : ∀ b, ∀ a ∈ P.gA.parents b,
    (∃ j, P.u j = a) ∨ (∃ i, P.nd (Fin.castSucc i) = a) := by
  intro b a ha
  rw [DAG.mem_parents] at ha
  rcases (P.gA_edge a b).mp ha with ⟨j0, _, h1, _⟩ | ⟨k, h1, _⟩ | ⟨j, k, _, h1, _⟩ | ⟨j, h1, _⟩
  · exact Or.inl ⟨j0, h1.symm⟩
  · exact Or.inl ⟨k, h1.symm⟩
  · exact Or.inl ⟨j, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩

/-! ### The kernels -/

/-- The kernel function of `nd_k` in model A: the sum (mod 2) of its latent parents and its
children in the directed tree. -/
noncomputable def fn (k : Fin (n + 2))
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) : Bool :=
  toBool (ofBool (pa ⟨P.u k, P.pnu k⟩) +
    (∑ j, if h : P.bp j = some k then ofBool (pa ⟨P.u j, P.pnb j k h⟩) else 0) +
    ∑ j, if h : P.dp j = k then ofBool (pa ⟨P.nd j.castSucc, P.pnd j k h⟩) else 0)

/-- The kernel function of `nd_k`, read off a full assignment. -/
lemma fn_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.fn k (s.restrict (Finset.subset_univ _)) =
      toBool (ofBool (ev s (P.u k)) +
        (∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0) +
        ∑ j, if P.dp j = k then ofBool (ev s (P.nd j.castSucc)) else 0) := by
  unfold fn
  congr 1

/-- The function whose noisy copy `x` is in model A: the sum (mod 2) of its latent neighbours. -/
noncomputable def fx (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) : Bool :=
  toBool (∑ j, if h : P.bp j = none then ofBool (pa ⟨P.u j, P.pxu j h⟩) else 0)

/-- The function `fx`, read off a full assignment. -/
lemma fx_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.fx (s.restrict (Finset.subset_univ _)) =
      toBool (∑ j, if P.bp j = none then ofBool (ev s (P.u j)) else 0) := by
  unfold fx
  congr 1

/-! ### The double count -/

/-- **The double count.** If the latent values `ℓ` solve the system of equations of model A for
the observed values `N`, then the sum of the latent values at the roots of the latent tree
(the neighbours of `x`) is `N` at `y`: summing all equations, every inner latent and every
inner observed node is counted twice. -/
lemma dc (ℓ N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = (N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
      ∑ j, if P.bp j = some k then ℓ j else 0) :
    (∑ j, if P.bp j = none then ℓ j else 0) = N (Fin.last (n + 1)) := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then ℓ j else 0) =
      if P.bp j = none then 0 else ℓ j := by
    intro j
    cases hb : P.bp j with
    | none => simp
    | some k0 => simp
  have h2 : ∀ j : Fin (n + 1), (∑ k, if P.dp j = k then N j.castSucc else 0) = N j.castSucc := by
    intro j
    simp
  have hsplit : ∑ j, ℓ j = (∑ j, if P.bp j = none then ℓ j else 0) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hD : ∑ k, ∑ j, (if P.dp j = k then N j.castSucc else 0) = ∑ j, N (Fin.castSucc j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hB : ∑ k, ∑ j, (if P.bp j = some k then ℓ j else 0) =
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hsum : ∑ k, ℓ k = (∑ k, N k + ∑ j, N (Fin.castSucc j)) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    calc ∑ k, ℓ k = ∑ k, ((N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ j, if P.bp j = some k then ℓ j else 0) := Finset.sum_congr rfl (fun k _ => hE k)
      _ = (∑ k, N k + ∑ k, ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ k, ∑ j, if P.bp j = some k then ℓ j else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ k, N k + ∑ j, N (Fin.castSucc j)) + ∑ j, (if P.bp j = none then 0 else ℓ j) := by
        rw [hD, hB]
  have hN : ∑ k, N k + ∑ j, N (Fin.castSucc j) = N (Fin.last (n + 1)) := by
    rw [Fin.sum_univ_castSucc]
    have := CharTwo.add_self_eq_zero (∑ j : Fin (n + 1), N j.castSucc)
    linear_combination this
  have := hsplit.symm.trans hsum
  rw [hN] at this
  exact add_right_cancel this

/-! ### The equations -/

/-- The value at `nd_k` in `ZMod 2`, with `b` the values of `nd₀, …, nd_n` and `c` that of `y`. -/
def nz (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  ofBool (Fin.lastCases (motive := fun _ => Bool) c b k)

/-- The right-hand side of the forest system at `k`: the value of `nd_k` plus those of its
children in the directed tree. -/
def rr (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  nz b c k + ∑ j, if P.dp j = k then nz b c j.castSucc else 0

/-- The shift of `u_j` in the bijection: the bottom-up solution of the forest system. -/
def off (j : Fin (n + 2)) (b : Fin (n + 1) → Bool) (c : Bool) : Bool :=
  toBool (forestSolution P.bp P.ht (P.rr b c) j)

/-- `nz` read off a full assignment. -/
lemma nz_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    nz (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      ofBool (ev s (P.nd k)) := by
  refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [nz]

/-- `rr` read off a full assignment. -/
lemma rr_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      ofBool (ev s (P.nd k)) + ∑ j, if P.dp j = k then ofBool (ev s (P.nd j.castSucc)) else 0 := by
  simp only [rr, P.nz_eq]

/-- The equation of `nd_k` in model A is the equation of `u_k` in the forest system. -/
lemma E_iff (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) ↔
      ofBool (ev s (P.u k)) =
        P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k +
          ∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0 := by
  rw [P.fn_s, eq_toBool_iff, P.rr_eq]
  exact ZMod2.eq_add_add_iff_eq_add_add _ _ _ _

/-- The equations of model A hold exactly when every `u_j` equals its shift (the field `key` of
the template). -/
lemma key (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1)))) := by
  have hall : ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
      ∀ k, ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) :=
    ⟨fun ⟨h1, h2⟩ k => Fin.lastCases (motive := fun k =>
        ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _))) h2 h1 k,
      fun h => ⟨fun i => h _, h _⟩⟩
  refine hall.trans ((forall_congr' fun k => P.E_iff s k).trans
    ((forall_eq_forestSolution_iff P.hht
      (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))))
      (fun k => ofBool (ev s (P.u k)))).trans (forall_congr' fun j => ?_)))
  unfold off
  exact (eq_toBool_iff _ _).symm

/-- If every `u_j` equals its shift, then `fx = y` (the field `hfx` of the template), by the
double count. -/
lemma hfx (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (h : ∀ j, ev s (P.u j) =
      P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1))))) :
    P.fx (s.restrict (Finset.subset_univ _)) = ev s (P.nd (Fin.last (n + 1))) := by
  have h' : ∀ k, ofBool (ev s (P.u k)) =
      forestSolution P.bp P.ht
        (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1))))) k :=
    fun k => (eq_toBool_iff _ _).mp (h k)
  have hE := (forall_eq_forestSolution_iff P.hht _ (fun k => ofBool (ev s (P.u k)))).mpr h'
  simp only [P.rr_eq] at hE
  have hd := P.dc (fun k => ofBool (ev s (P.u k))) (fun k => ofBool (ev s (P.nd k))) hE
  rw [P.fx_s]
  exact ((eq_toBool_iff _ _).mpr hd.symm).symm

/-- The configuration as an instance of the template. -/
noncomputable def toHedgeTemplate : HedgeTemplate G n where
  x := P.x
  y := P.nd (Fin.last (n + 1))
  w := fun i => P.nd (Fin.castSucc i)
  u := P.u
  gA := P.gA
  gA_parents_subset := P.gA_parents_subset
  fx := P.fx
  src := P.src
  fw := fun i => P.fn (Fin.castSucc i)
  fy := P.fn (Fin.last (n + 1))
  off := P.off
  hfx := P.hfx
  key := P.key
  hxy := P.hxy
  winj := fun a b h => Fin.castSucc_injective _ (P.ndinj h)
  uinj := P.uinj
  huw := fun j i => P.hund j _
  hux' := P.hux'
  huy' := fun j => P.hund j _
  hwx := fun i => P.hndx _
  hwy' := fun i h => (Fin.castSucc_lt_last i).ne (P.ndinj h)

/-- **Latent tree.** If the latent connections form a tree over `x` and the observed nodes,
the directed edges form a tree towards `y`, and `x → y`, then `P(y | do(x))` is not
identifiable from any `O` that contains `x` and `y` but no latent. -/
theorem not_identifiable (O : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O)
    (hy : P.nd (Fin.last (n + 1)) ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} {P.nd (Fin.last (n + 1))} :=
  P.toHedgeTemplate.not_identifiable O hu hx hy

end LatentTree
end Identification

#print axioms Identification.LatentTree.not_identifiable
