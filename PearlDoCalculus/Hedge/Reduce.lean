import PearlDoCalculus.Hedge.Tree

/-!
# Reducing the graph of a hedge to the forest and the tree (step H3)

This file shows that it is enough to prove non-identifiability in a subgraph: more edges
never help. It then defines the subgraph that the parity models of step H3 live in, the
hedge with only the edges of the forest `nxt` and of the spanning tree kept.

**Why.** The parity models are built on a hedge `(F, F')` (`IsHedge`, in `Hedge/Defs.lean`)
whose only edges are the chosen child `v → nxt v` of each non-root node, and the latent
edges `u → v`, `u → par v` of the spanning tree (both from `Hedge/Tree.lean`). Building
models on this reduced graph is much easier than on the whole graph. Since the
reduced graph has fewer edges, non-identifiability there carries over to the whole graph.
The latent nodes in these models carry bit vectors, so the transfer is needed for
arbitrary value types, not only for `Bool` as in `Channel.not_ident_of_sub`.

**How.**

1. *More edges never help* (`not_ident_of_subα`). A model on the smaller graph `H` lifts
   to the larger graph `G` by ignoring the extra parents (`Completeness.liftSub`). The
   lift has the same kernel factors, with and without an intervention (`kfac_liftα`,
   `kfac_lift_doα`), so it has the same observed and interventional marginals. Two models
   on `H` that witness non-identifiability therefore lift to two witnesses on `G`.
2. *The reduced graph.* `keepDAG G K` keeps the edges of `G` that satisfy `K`. It is a DAG
   with the same rank, and `not_ident_keep` is the special case of step 1 for it.
   `hedgeKeep G U F F' par` is the choice of `K` for a hedge: the forest edges and the
   latent tree edges. `hedge_red_nxt` and `hedge_red_lat` check that these edges really
   are in the reduced graph.

**Main results.** `not_ident_of_subα`, `keepDAG`, `not_ident_keep`, `hedgeKeep`,
`hedge_red_nxt`, `hedge_red_lat`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 51: «flere kanter skader aldri» for alle verdityper

`Channel.not_ident_of_sub` er bevist for `Bool` på alle noder. Planen for H3 gir de latente
bit-vektorer (én bit per kant i det utspente treet), så her er samme resultat for vilkårlige
verdityper `α`: `not_ident_of_subα`. Beviset er det samme; det bruker ikke at verdiene er
`Bool`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma kfac_liftα {G H : DAG V} {α : V → Type*} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (Completeness.liftSub hsub N) Finset.univ w v = kfac N Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_doα {G H : DAG V} {α : V → Type*} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (X : Finset V) (x : Assignment (α := α) X)
    (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ w v =
      kfac (doModel N X x) Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

/-- **Flere kanter skader aldri**, for vilkårlige verdityper. -/
theorem not_ident_of_subα {H G : DAG V} {α : V → Type*} (hsub : ∀ a b, H.edge a b → G.edge a b)
    {O X Y : Finset V} (h : ¬ Identifiable H α O X Y) : ¬ Identifiable G α O X Y := by
  intro hG
  apply h
  intro M1 M2 hM hpos t
  have hp : ∀ v, H.parents v ⊆ G.parents v := fun v a ha => by
    simp only [DAG.mem_parents] at ha ⊢
    exact hsub _ _ ha
  have hm : ∀ (M : H.CausalModel α) (S : Finset V),
      (Completeness.liftSub hp M).marginal S = M.marginal S := fun M S =>
    Completeness.marginal_eq_of_kfac _ M (kfac_liftα hp M) S
  have hd : ∀ (M : H.CausalModel α) (x0 : Assignment (α := α) X)
      (S : Finset V), (doModel (Completeness.liftSub hp M) X x0).marginal S =
        (doModel M X x0).marginal S := fun M x0 S =>
    Completeness.marginal_eq_of_kfac _ _ (kfac_lift_doα hp M X x0) S
  have e := hG (Completeness.liftSub hp M1) (Completeness.liftSub hp M2)
    (by rw [hm, hm]; exact hM) (by intro a; rw [hm]; exact hpos a) t
  rw [hd, hd] at e
  exact e

end Hedge

#print axioms Hedge.not_ident_of_subα

/-! ## Runde 52: den reduserte grafen

`keepDAG G K`: delgrafen av `G` med bare kantene som oppfyller `K`. Den er en DAG med samme
rang, og `not_ident_keep`: ikke-identifiserbar i delgrafen gir ikke-identifiserbar i `G`
(for alle verdityper). `hedgeKeep`: kantene H3 beholder, nemlig `v → nxt v` (skogen inn i
røttene) og `u → v`, `u → par v` for latente `u` i `F'` (treet). `hedge_red_nxt` og
`hedge_red_lat`: disse kantene ligger i den reduserte grafen. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Delgrafen med bare kantene som oppfyller `K`. -/
noncomputable def keepDAG (G : DAG V) (K : V → V → Prop) : DAG V where
  edge a b := G.edge a b ∧ K a b
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := fun a b h => G.rank_strict_mono a b h.1

lemma keepDAG_edge {G : DAG V} {K : V → V → Prop} {a b : V} :
    (keepDAG G K).edge a b ↔ G.edge a b ∧ K a b := Iff.rfl

/-- **Ikke identifiserbar i delgrafen ⇒ ikke identifiserbar i `G`.** -/
theorem not_ident_keep {G : DAG V} {K : V → V → Prop} {α : V → Type*} {O X Y : Finset V}
    (h : ¬ Identifiable (keepDAG G K) α O X Y) : ¬ Identifiable G α O X Y :=
  not_ident_of_subα (fun a b (hab : (keepDAG G K).edge a b) => (keepDAG_edge.mp hab).1) h

/-- Kantene H3 beholder: skogen `v → nxt v`, og treets latente kanter `u → v`, `u → par v`. -/
def hedgeKeep (G : DAG V) (U F F' : Finset V) (par : V → V) (a b : V) : Prop :=
  (a ∈ F' ∧ b = nxt G F F' a) ∨
  (a ∈ U ∧ a ∈ F' ∧ ∃ v ∈ F', (b = v ∨ b = par v) ∧ G.edge a v ∧ G.edge a (par v))

/-- Skogkantene ligger i den reduserte grafen. -/
theorem hedge_red_nxt {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (par : V → V) {v : V} (hv : v ∈ F') (hR : v ∉ rootsIn G F) :
    (keepDAG G (hedgeKeep G U F F' par)).edge v (nxt G F F' v) :=
  keepDAG_edge.mpr ⟨(hedge_nxt hH v hv hR).2.2, by unfold hedgeKeep; exact Or.inl ⟨hv, rfl⟩⟩

/-- Treets latente kanter ligger i den reduserte grafen. -/
theorem hedge_red_lat (G : DAG V) (U F F' : Finset V) (par : V → V) {u v : V}
    (hu : u ∈ U) (huF : u ∈ F') (hv : v ∈ F') (e1 : G.edge u v) (e2 : G.edge u (par v)) :
    (keepDAG G (hedgeKeep G U F F' par)).edge u v ∧
      (keepDAG G (hedgeKeep G U F F' par)).edge u (par v) :=
  ⟨keepDAG_edge.mpr ⟨e1, by unfold hedgeKeep; exact Or.inr ⟨hu, huF, v, hv, Or.inl rfl, e1, e2⟩⟩,
   keepDAG_edge.mpr ⟨e2, by unfold hedgeKeep; exact Or.inr ⟨hu, huF, v, hv, Or.inr rfl, e1, e2⟩⟩⟩

end Hedge

#print axioms Hedge.not_ident_keep
#print axioms Hedge.hedge_red_nxt
#print axioms Hedge.hedge_red_lat
