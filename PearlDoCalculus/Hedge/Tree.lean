import PearlDoCalculus.Hedge.FromID

/-!
# The forest and the spanning tree inside a hedge (step H3, combinatorics)

This file builds the combinatorial structure on a hedge `(F, F')` (`IsHedge`, defined in
`Hedge/Defs.lean`) that the parity models of step H3 are made of, together with the
linear algebra over `ZMod 2` on trees that those models need. Nothing here mentions
probability.

**Why.** To show that a hedge blocks identification one builds two models that agree on
the observed distribution and disagree on the effect. Following Shpitser and Pearl (JMLR
2008, proof of Thm 17), each observed node passes its bit along one chosen child, so the
graph is first thinned to a forest that flows into the roots of `F`. The latent nodes
carry one bit for each edge of a spanning tree of latent edges, and the two models are
matched by shifting these bits. That shift exists because incidence on a tree reaches
every vector with sum zero.

**How.**

1. *A forest into the roots.* Every node of `F'` that is not a root of `F` gets a chosen
   child `nxt v`: inside `F` for nodes of `F`, otherwise inside `F'` (`nxt`,
   `hedge_nxt`). The child exists because `F'` consists of ancestors of the roots inside
   `F'` (`anc_has_child`). The rank grows along `nxt`, so every node reaches a root
   (`hedge_reaches_root`); one common number of steps works for all nodes
   (`hedge_root_uniform`), which gives a root map that is constant along `nxt`
   (`hedge_rootOf`).
2. *A spanning tree of latent edges.* When the latent nodes are roots, a latent path
   between two observed nodes goes through common latent parents. `sib G U F a b` says
   that `a` and `b` share a latent parent inside `F`; c-connectedness gives chains of
   siblings (`cconn_sib`). Sorting the nodes into layers `lay` by their sibling distance
   from an observed root `ρ` gives a parent pointer `par` with a strictly decreasing
   distance `d` (`sib_tree`). For a hedge, the tree for `F'` contains a tree for `F`
   (`hedge_tree`), and `F` always has an observed node (`hedge_obs`), so every hedge has
   such a tree (`hedge_spanning`).
3. *Incidence on a tree.* `ParTree S ρ par d` describes a tree by its parent pointer.
   The incidence value `inc S ρ par c w` is the bit on the edge above `w` plus the bits
   on the edges down to its children. Incidence reaches every vector whose sum is zero
   (`inc_surj`, by induction on `|S|`, removing a leaf).

**Who uses it.** The parity models (`Hedge/ParityModels` onwards) read their parents
along `nxt` and the tree; `hedge_spanning` and `hedge_reaches_root` provide the tree and
the forest in `Hedge/Roots` and `Hedge/Complete`; `ParTree` describes both trees there;
`inc_surj` gives the shift in `Hedge/ObsEq` and the positive solution in
`Hedge/Positivity`; `hedge_iter_mem` and `nxt_root` are used for the reach indicators in
`Hedge/DoGapM1`. The root map (`hedge_root_uniform`, `hedge_rootOf`) is used by no other
file. (The subtree lemma `ParTree.desc_par_iff` and the injectivity of incidence,
`ParTree.inc_inj`, were deleted in v4.191: the later proofs need only the existence part
`inc_surj`. They are kept at tag `v4.190`.)

**Main results.** `hedge_nxt`, `hedge_reaches_root`, `hedge_rootOf`, `cconn_sib`,
`sib_tree`, `hedge_tree`, `hedge_spanning`, `inc_surj`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## A forest into the roots

The construction of Shpitser and Pearl (JMLR 2008, proof of Thm 17) works on a C-forest:
every node keeps at most one child. Here that child (`nxt`) is chosen for every node of
`F'` that is not a root: inside `F` for nodes of `F`, otherwise inside `F'`
(`hedge_nxt`). The rank grows along the choices, so every node reaches a root after
finitely many steps (`hedge_reaches_root`). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A node of `ancIn G T C` is in `C` or has a child in `T`. -/
lemma anc_has_child (G : DAG V) (T C : Finset V) (hCT : C ⊆ T) :
    ∀ v ∈ ancIn G T C, v ∈ C ∨ ∃ w ∈ T, G.edge v w := by
  have hbd : ∀ A, A ⊆ C ∪ T.filter (fun v => ∃ w ∈ T, G.edge v w) →
      ancStep G T A ⊆ C ∪ T.filter (fun v => ∃ w ∈ T, G.edge v w) := by
    intro A hA w hw
    rcases Finset.mem_union.mp hw with h1 | h1
    · exact hA h1
    · obtain ⟨hwT, a, ha, e⟩ := Finset.mem_filter.mp h1
      have haT : a ∈ T := by
        rcases Finset.mem_union.mp (hA ha) with h2 | h2
        · exact hCT h2
        · exact (Finset.mem_filter.mp h2).1
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwT, a, haT, e⟩)
  have h := Finset.iterate_subset _ (ancStep G T) hbd C Finset.subset_union_left T.card
  intro v hv
  rcases Finset.mem_union.mp (h hv) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Finset.mem_filter.mp h1).2

/-- The chosen child of `v`: a child inside `F` for nodes of `F`, otherwise a child
inside `F'`; `v` itself if there is none (as for the roots). -/
noncomputable def nxt (G : DAG V) (F F' : Finset V) (v : V) : V :=
  if h : ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w then Classical.choose h else v

/-- If a suitable child exists, `nxt` picks one. -/
lemma nxt_spec (G : DAG V) (F F' : Finset V) (v : V)
    (h : ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w) :
    (v ∈ F → nxt G F F' v ∈ F) ∧ nxt G F F' v ∈ F' ∧ G.edge v (nxt G F F' v) := by
  unfold nxt
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **In a hedge every non-root has a chosen child**: inside `F` for nodes of `F`
(they are not roots of `F`), otherwise inside `F'` (`F'` consists of ancestors of the
roots inside `F'`). -/
theorem hedge_nxt {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') (v : V)
    (hv : v ∈ F') (hR : v ∉ rootsIn G F) :
    (v ∈ F → nxt G F F' v ∈ F) ∧ nxt G F F' v ∈ F' ∧ G.edge v (nxt G F F' v) := by
  apply nxt_spec
  by_cases hvF : v ∈ F
  · have hnot : ¬ ∀ w ∈ F, ¬ G.edge v w := fun h => hR (Finset.mem_filter.mpr ⟨hvF, h⟩)
    obtain ⟨w, hwF, e⟩ : ∃ w ∈ F, G.edge v w := by
      by_contra h'
      exact hnot (fun w hw e => h' ⟨w, hw, e⟩)
    exact ⟨w, fun _ => hwF, hH.sub hwF, e⟩
  · have hRF' : rootsIn G F ⊆ F' := (Finset.filter_subset _ _).trans hH.sub
    have hva : v ∈ ancIn G F' (rootsIn G F) := by rw [hH.rootF']; exact hv
    rcases anc_has_child G F' _ hRF' v hva with h | ⟨w, hw, e⟩
    · exact absurd h hR
    · exact ⟨w, fun h => absurd h hvF, hw, e⟩

/-- **Following the chosen children, one reaches a root.** By strong induction on the
rank gap to the largest rank in `F'`. -/
theorem hedge_reaches_root {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∀ v ∈ F', ∃ n, (nxt G F F')^[n] v ∈ rootsIn G F := by
  have key : ∀ k, ∀ v ∈ F', F'.sup G.rank - G.rank v = k →
      ∃ n, (nxt G F F')^[n] v ∈ rootsIn G F := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hk
      by_cases hR : v ∈ rootsIn G F
      · exact ⟨0, hR⟩
      · obtain ⟨_, hw, e⟩ := hedge_nxt hH v hv hR
        have hlt := G.rank_strict_mono v _ e
        have hle : G.rank (nxt G F F' v) ≤ F'.sup G.rank := Finset.le_sup hw
        obtain ⟨n, hn⟩ := ih (F'.sup G.rank - G.rank (nxt G F F' v)) (by omega) _ hw rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  exact fun v hv => key _ v hv rfl

end Hedge

#print axioms Hedge.hedge_nxt
#print axioms Hedge.hedge_reaches_root

/-! ## The root of each node

`nxt` stands still at the roots (`nxt_root`), and stays inside `F` and `F'`
(`hedge_iter_memF`, `hedge_iter_mem`). One common number of steps `N` takes every node
of `F'` to a root (`hedge_root_uniform`), so `r v := nxt^[N] v` is the root that `v`
feeds into, and `r` is constant along `nxt` (`hedge_rootOf`). This is the bookkeeping
the parity models of step H3 need. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- At a root, `nxt` stands still. -/
lemma nxt_root (G : DAG V) (F F' : Finset V) (v : V) (hv : v ∈ rootsIn G F) :
    nxt G F F' v = v := by
  have hn : ¬ ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w := by
    rintro ⟨w, hwF, _, e⟩
    have hvF : v ∈ F := (Finset.mem_filter.mp hv).1
    exact (Finset.mem_filter.mp hv).2 w (hwF hvF) e
  unfold nxt
  rw [dif_neg hn]

/-- At a root, every iterate of `nxt` stands still. -/
lemma iter_root (G : DAG V) (F F' : Finset V) (v : V) (hv : v ∈ rootsIn G F) :
    ∀ m, (nxt G F F')^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, nxt_root G F F' v hv]

/-- Following `nxt` from `F'`, one stays in `F'`. -/
theorem hedge_iter_mem {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    {v : V} (hv : v ∈ F') : ∀ n, (nxt G F F')^[n] v ∈ F' := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]; exact ih
    · exact (hedge_nxt hH _ ih hR).2.1

/-- Following `nxt` from `F`, one stays in `F`. -/
theorem hedge_iter_memF {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    {v : V} (hv : v ∈ F) : ∀ n, (nxt G F F')^[n] v ∈ F := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]; exact ih
    · exact (hedge_nxt hH _ (hH.sub ih) hR).1 ih

/-- **One number of steps works for all nodes**: the maximum over `F'` of the steps
each node needs, since `nxt` stands still once a root is reached. -/
theorem hedge_root_uniform {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∃ N, ∀ v ∈ F', (nxt G F F')^[N] v ∈ rootsIn G F := by
  choose! n hn using hedge_reaches_root hH
  refine ⟨F'.sup n, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hv)
  rw [hk, add_comm, Function.iterate_add_apply, iter_root G F F' _ (hn v hv) k]
  exact hn v hv

/-- **The root map:** every node of `F'` has a root, and the root is the same along
`nxt`. -/
theorem hedge_rootOf {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∃ r : V → V, (∀ v ∈ F', r v ∈ rootsIn G F) ∧ (∀ v ∈ F', r (nxt G F F' v) = r v) := by
  obtain ⟨N, hN⟩ := hedge_root_uniform hH
  refine ⟨fun v => (nxt G F F')^[N] v, fun v hv => hN v hv, fun v hv => ?_⟩
  show (nxt G F F')^[N] (nxt G F F' v) = (nxt G F F')^[N] v
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', nxt_root G F F' _ (hN v hv)]

end Hedge

#print axioms Hedge.nxt_root
#print axioms Hedge.hedge_iter_mem
#print axioms Hedge.hedge_iter_memF
#print axioms Hedge.hedge_root_uniform
#print axioms Hedge.hedge_rootOf

/-! ## Spanning tree: siblings

When the latent nodes are roots, every latent path between two observed nodes of `F`
goes through common latent parents. `sib G U F a b`: `a` and `b` are in `F` and have a
common latent parent in `F`. `cconn_sib`: in a c-connected `F` all observed nodes are
joined by a chain of siblings. This is the graph in which the spanning tree is chosen. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `a` and `b` are siblings in `F`: both in `F`, with a common latent parent in `F`. -/
def sib (G : DAG V) (U F : Finset V) (a b : V) : Prop :=
  a ∈ F ∧ b ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u a ∧ G.edge u b

/-- The sibling relation is symmetric. -/
lemma sib_symm {G : DAG V} {U F : Finset V} {a b : V} (h : sib G U F a b) : sib G U F b a := by
  obtain ⟨ha, hb, u, hu, huF, ea, eb⟩ := h
  exact (⟨hb, ha, u, hu, huF, eb, ea⟩ : b ∈ F ∧ a ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u b ∧ G.edge u a)

/-- **C-connectedness gives chains of siblings** (latent nodes are roots). By
induction along a latent path: an observed node on it is reached by siblings, and a
latent node on it has an observed child that is. -/
theorem cconn_sib (G : DAG V) (U F : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hF : CConn G U F) :
    ∀ a ∈ F, a ∉ U → ∀ b ∈ F, b ∉ U → Relation.ReflTransGen (sib G U F) a b := by
  intro a ha haU
  have key : ∀ x, Relation.ReflTransGen (latStep (DAG.induce G F) U) a x →
      (x ∉ U → Relation.ReflTransGen (sib G U F) a x) ∧
      (x ∈ U → ∃ c, c ∉ U ∧ c ∈ F ∧ x ∈ F ∧ G.edge x c ∧
        Relation.ReflTransGen (sib G U F) a c) := by
    intro x hx
    induction hx with
    | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => absurd h haU⟩
    | @tail b c _ hst ih =>
      rcases hst with ⟨hbU, e⟩ | ⟨hcU, e⟩
      · obtain ⟨hbF, hcF, ebc⟩ := (show b ∈ F ∧ c ∈ F ∧ G.edge b c from e)
        refine ⟨fun _ => ?_, fun hcU => absurd ebc (hroot c hcU b)⟩
        obtain ⟨d, _, hdF, _, ebd, hpath⟩ := ih.2 hbU
        exact hpath.tail (⟨hdF, hcF, b, hbU, hbF, ebd, ebc⟩ :
          d ∈ F ∧ c ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u d ∧ G.edge u c)
      · obtain ⟨hcF, hbF, ecb⟩ := (show c ∈ F ∧ b ∈ F ∧ G.edge c b from e)
        have hbU : b ∉ U := fun h => hroot b h c ecb
        exact ⟨fun h => absurd hcU h, fun _ => ⟨b, hbU, hbF, hcF, ecb, ih.1 hbU⟩⟩
  intro b hb hbU
  exact (key b (mem_ccomp.mp (hF a ha b hb))).1 hbU

end Hedge

#print axioms Hedge.sib_symm
#print axioms Hedge.cconn_sib

/-! ## Spanning tree: layers and parent pointer

`lay G U F ρ n v`: `v` is reached from `ρ` in at most `n` sibling steps. `lay_of_chain`: a
chain of siblings gives a layer. `sib_tree`: for an observed root `ρ ∈ F`, every other
observed node of `F` chooses a sibling `par v` with strictly smaller distance `d`. This
is a spanning tree of latent edges: following `par` decreases `d`, and only `ρ` has no
parent. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Layers: `v` is reached from `ρ` in at most `n` sibling steps inside `F`. -/
def lay (G : DAG V) (U F : Finset V) (ρ : V) : ℕ → V → Prop
  | 0, v => v = ρ
  | n + 1, v => lay G U F ρ n v ∨ ∃ w, lay G U F ρ n w ∧ sib G U F w v

/-- A chain of siblings from `ρ` to `v` puts `v` in some layer. -/
lemma lay_of_chain (G : DAG V) (U F : Finset V) (ρ v : V)
    (h : Relation.ReflTransGen (sib G U F) ρ v) : ∃ n, lay G U F ρ n v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨b, hn, hbc⟩⟩

/-- **Spanning tree:** every observed `v ≠ ρ` in `F` has a sibling `par v` closer to
`ρ`. The distance `d v` is the first layer containing `v`; a node in layer `j + 1` but
not in layer `j` has a sibling in layer `j`. -/
theorem sib_tree (G : DAG V) (U F : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hF : CConn G U F) (ρ : V) (hρ : ρ ∈ F) (hρU : ρ ∉ U) :
    ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F, v ∉ U → v ≠ ρ →
      sib G U F (par v) v ∧ d (par v) < d v := by
  classical
  have hex : ∀ v ∈ F, v ∉ U → ∃ n, lay G U F ρ n v := fun v hv hvU =>
    lay_of_chain G U F ρ v (cconn_sib G U F hroot hF ρ hρ hρU v hv hvU)
  have step : ∀ v ∈ F, v ∉ U → v ≠ ρ → ∃ w, sib G U F w v ∧
      (if h : ∃ n, lay G U F ρ n w then Nat.find h else 0) <
      (if h : ∃ n, lay G U F ρ n v then Nat.find h else 0) := by
    intro v hv hvU hvρ
    have h := hex v hv hvU
    rw [dif_pos h]
    have hne : Nat.find h ≠ 0 := by
      intro h0
      apply hvρ
      have hs := Nat.find_spec h
      rw [h0] at hs
      exact hs
    obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := ⟨Nat.find h - 1, by omega⟩
    have hs := Nat.find_spec h
    rw [hj] at hs
    have hs' : lay G U F ρ j v ∨ ∃ w, lay G U F ρ j w ∧ sib G U F w v := by
      exact hs
    rcases hs' with hs' | ⟨w, hw, hsib⟩
    · exact absurd hs' (Nat.find_min h (by omega))
    · refine ⟨w, hsib, ?_⟩
      have hw' : ∃ n, lay G U F ρ n w := ⟨j, hw⟩
      rw [dif_pos hw', hj]
      have := Nat.find_min' hw' hw
      omega
  choose! par hpar using step
  exact ⟨par, fun v => if h : ∃ n, lay G U F ρ n v then Nat.find h else 0, hpar⟩

end Hedge

#print axioms Hedge.lay_of_chain
#print axioms Hedge.sib_tree

/-! ## Spanning tree for the whole hedge

`hedge_tree`: with an observed root `ρ ∈ F`, every other observed node of `F'` gets a
sibling `par v` in `F'` with strictly smaller `d`, and for nodes of `F` the parent and
the common latent parent lie in `F`. So the tree of `F'` contains a spanning tree of `F`,
as the parity models of step H3 need. The distance is `d₁` (the tree of `F`) inside `F`,
and `max d₁ + 1 + d₂` (the tree of `F'`) outside. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Siblings in `F` are siblings in every `F' ⊇ F`. -/
lemma sib_mono {G : DAG V} {U F F' : Finset V} (hFF' : F ⊆ F') {a b : V}
    (h : sib G U F a b) : sib G U F' a b := by
  obtain ⟨ha, hb, u, hu, huF, ea, eb⟩ := h
  exact (⟨hFF' ha, hFF' hb, u, hu, hFF' huF, ea, eb⟩ :
    a ∈ F' ∧ b ∈ F' ∧ ∃ u ∈ U, u ∈ F' ∧ G.edge u a ∧ G.edge u b)

/-- **Spanning tree for the hedge**, with the tree of `F` inside it. -/
theorem hedge_tree {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (ρ : V) (hρ : ρ ∈ F) (hρU : ρ ∉ U) :
    ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F', v ∉ U → v ≠ ρ →
      sib G U F' (par v) v ∧ d (par v) < d v ∧ (v ∈ F → sib G U F (par v) v) := by
  classical
  obtain ⟨p1, d1, h1⟩ := sib_tree G U F hroot hH.conn ρ hρ hρU
  obtain ⟨p2, d2, h2⟩ := sib_tree G U F' hroot hH.conn' ρ (hH.sub hρ) hρU
  refine ⟨fun v => if v ∈ F then p1 v else p2 v,
    fun v => if v ∈ F then d1 v else F.sup d1 + 1 + d2 v, fun v hv hvU hvρ => ?_⟩
  by_cases hvF : v ∈ F
  · obtain ⟨hs, hd⟩ := h1 v hvF hvU hvρ
    have hpF : p1 v ∈ F := by
      obtain ⟨h, _⟩ := hs
      exact h
    simp only [if_pos hvF, if_pos hpF]
    exact ⟨sib_mono hH.sub hs, hd, fun _ => hs⟩
  · obtain ⟨hs, hd⟩ := h2 v hv hvU hvρ
    simp only [if_neg hvF]
    refine ⟨hs, ?_, fun h => absurd h hvF⟩
    by_cases hpF : p2 v ∈ F
    · rw [if_pos hpF]
      have := Finset.le_sup (f := d1) hpF
      omega
    · rw [if_neg hpF]
      omega

end Hedge

#print axioms Hedge.sib_mono
#print axioms Hedge.hedge_tree

/-! ## The tree without extra assumptions

`hedge_obs`: when the latent nodes are roots, `F` has an observed node. If all of `F`
were latent, the roots would have no parents, so `F' = ancIn G F' (rootsIn G F) ⊆ F`,
against `F ≠ F'`. `sib_obs`: siblings are observed. `hedge_spanning`: every hedge has an
observed root `ρ ∈ F` and a spanning tree of latent edges, with no assumption beyond the
latent nodes being roots. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Siblings are observed (latent nodes are roots, and siblings have a parent). -/
lemma sib_obs {G : DAG V} {U F : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {a b : V}
    (h : sib G U F a b) : a ∉ U ∧ b ∉ U := by
  obtain ⟨_, _, u, _, _, ea, eb⟩ := h
  exact ⟨fun h => hroot a h u ea, fun h => hroot b h u eb⟩

/-- **A hedge has an observed node in `F`** (latent nodes are roots). -/
theorem hedge_obs {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) : ∃ ρ ∈ F, ρ ∉ U := by
  by_contra hno
  have hall : ∀ v ∈ F, v ∈ U := fun v hv => by
    by_contra h
    exact hno ⟨v, hv, h⟩
  have hsub : ancIn G F' (rootsIn G F) ⊆ rootsIn G F :=
    ancIn_min G F' (rootsIn G F) (rootsIn G F) (Finset.Subset.refl _)
      (fun v _ hex => by
        obtain ⟨a, ha, e⟩ := hex
        exact absurd e (hroot a (hall a (Finset.mem_filter.mp ha).1) v))
  rw [hH.rootF'] at hsub
  exact hH.ne (Finset.Subset.antisymm hH.sub (hsub.trans (Finset.filter_subset _ _)))

/-- **Every hedge has a spanning tree** with an observed root `ρ` in `F`: a parent
pointer `par` on the observed nodes of `F'`, along sibling edges, with a strictly
decreasing distance `d`, whose restriction to `F` stays inside `F`. -/
theorem hedge_spanning {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) :
    ∃ ρ ∈ F, ρ ∉ U ∧ ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F', v ∉ U → v ≠ ρ →
      sib G U F' (par v) v ∧ d (par v) < d v ∧ (v ∈ F → sib G U F (par v) v) := by
  obtain ⟨ρ, hρ, hρU⟩ := hedge_obs hH hroot
  exact ⟨ρ, hρ, hρU, hedge_tree hH hroot ρ hρ hρU⟩

end Hedge

#print axioms Hedge.sib_obs
#print axioms Hedge.hedge_obs
#print axioms Hedge.hedge_spanning

/-! ## Trees given by a parent pointer, and incidence

`ParTree S ρ par d`: `par` is a parent pointer on `S` with root `ρ` (`par ρ = ρ`) and a
strictly decreasing distance `d`. `inc S ρ par c w`: the incidence value at `w`, that is
the bit on the edge above `w` (none for the root) plus the bits on the edges down to its
children. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A tree on `S` given by a parent pointer `par`, with root `ρ` (fixed by `par`) and a
distance `d` that decreases strictly from every other node to its parent. -/
structure ParTree (S : Finset V) (ρ : V) (par : V → V) (d : V → ℕ) : Prop where
  root : ρ ∈ S
  fix : par ρ = ρ
  step : ∀ v ∈ S, v ≠ ρ → par v ∈ S ∧ d (par v) < d v

/-- The incidence value at `w` over `ZMod 2`: the bit on the edge above `w` (not for
the root) plus the bits on the edges down to its children. Edges are indexed by their
lower node. -/
def inc (S : Finset V) (ρ : V) (par : V → V) (c : V → ZMod 2) (w : V) : ZMod 2 :=
  (if w = ρ then 0 else c w) + ∑ u ∈ S.filter (fun u => u ≠ ρ ∧ par u = w), c u

end Hedge

/-! ## Incidence on a tree reaches every vector with sum zero

`inc_surj`: for a tree `S` and a vector `τ` with `Σ_S τ = 0` there are bits `b` with
incidence value `τ` at every node. Proof by induction on `|S|`: a leaf `ℓ` (largest `d`)
has no children; solve for `S \ {ℓ}` with `τ ℓ` moved over to its parent, and set the
bit above `ℓ` to `τ ℓ`. The parity models need this so that `M1` and `M2` give the same
observed distribution (a shift of the bits of the `F`-tree), and for positivity. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Incidence reaches every vector with sum zero.** -/
theorem inc_surj {ρ : V} {par : V → V} {d : V → ℕ} :
    ∀ (n : ℕ) (S : Finset V) (τ : V → ZMod 2), S.card = n → ParTree S ρ par d →
      ∑ w ∈ S, τ w = 0 → ∃ b : V → ZMod 2, ∀ w ∈ S, inc S ρ par b w = τ w := by
  intro n
  induction n with
  | zero =>
    intro S τ hc T _
    have := Finset.card_pos.mpr ⟨ρ, T.root⟩
    omega
  | succ n ih =>
    intro S τ hc T hsum
    by_cases hS : ∃ v ∈ S, v ≠ ρ
    · obtain ⟨ℓ, hℓf, hmax⟩ := Finset.exists_max_image (S.filter (fun v => v ≠ ρ)) d
        (by
          obtain ⟨v, hv, hvr⟩ := hS
          exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvr⟩⟩)
      obtain ⟨hℓS, hℓρ⟩ := Finset.mem_filter.mp hℓf
      have noch : ∀ u ∈ S, u ≠ ρ → par u ≠ ℓ := by
        intro u hu hur hpu
        have h1 := (T.step u hu hur).2
        rw [hpu] at h1
        have h2' := hmax u (Finset.mem_filter.mpr ⟨hu, hur⟩)
        omega
      have hpℓ : par ℓ ∈ S.erase ℓ := by
        refine Finset.mem_erase.mpr ⟨fun e => ?_, (T.step ℓ hℓS hℓρ).1⟩
        have h1 := (T.step ℓ hℓS hℓρ).2
        rw [e] at h1
        exact lt_irrefl _ h1
      have T' : ParTree (S.erase ℓ) ρ par d :=
        { root := Finset.mem_erase.mpr ⟨fun e => hℓρ e.symm, T.root⟩
          fix := T.fix
          step := fun v hv hvr => by
            have hvS := Finset.mem_of_mem_erase hv
            exact ⟨Finset.mem_erase.mpr ⟨noch v hvS hvr, (T.step v hvS hvr).1⟩,
              (T.step v hvS hvr).2⟩ }
      have hc' : (S.erase ℓ).card = n := by
        rw [Finset.card_erase_of_mem hℓS]
        omega
      have hsum' : ∑ w ∈ S.erase ℓ, (τ w + if w = par ℓ then τ ℓ else 0) = 0 := by
        rw [Finset.sum_add_distrib]
        have hite : ∑ w ∈ S.erase ℓ, (if w = par ℓ then τ ℓ else 0) = τ ℓ := by
          rw [Finset.sum_ite_eq' (S.erase ℓ) (par ℓ) (fun _ => τ ℓ), if_pos hpℓ]
        rw [hite, Finset.sum_erase_add S τ hℓS]
        exact hsum
      obtain ⟨b', hb'⟩ := ih (S.erase ℓ) (fun w => τ w + if w = par ℓ then τ ℓ else 0) hc' T' hsum'
      refine ⟨fun w => if w = ℓ then τ ℓ else b' w, fun w hw => ?_⟩
      have split : ∑ u ∈ S.filter (fun u => u ≠ ρ ∧ par u = w),
          (fun w => if w = ℓ then τ ℓ else b' w) u =
          ∑ u ∈ (S.erase ℓ).filter (fun u => u ≠ ρ ∧ par u = w), b' u +
            (if ℓ ≠ ρ ∧ par ℓ = w then τ ℓ else 0) := by
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_erase_add S _ hℓS]
        congr 1
        · apply Finset.sum_congr rfl
          intro u hu
          simp only [if_neg (Finset.ne_of_mem_erase hu)]
        · simp
      unfold inc
      rw [split]
      by_cases hwℓ : w = ℓ
      · subst hwℓ
        have hempty : ∑ u ∈ (S.erase w).filter (fun u => u ≠ ρ ∧ par u = w), b' u = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          obtain ⟨hu1, hu2, hu3⟩ := Finset.mem_filter.mp hu
          exact absurd hu3 (noch u (Finset.mem_of_mem_erase hu1) hu2)
        have hpw : ¬ (w ≠ ρ ∧ par w = w) := fun h => noch w hℓS hℓρ h.2
        rw [hempty, if_neg hpw, if_neg hℓρ]
        simp
      · have hwe : w ∈ S.erase ℓ := Finset.mem_erase.mpr ⟨hwℓ, hw⟩
        have e : (if w = ρ then 0 else b' w) +
            ∑ u ∈ (S.erase ℓ).filter (fun u => u ≠ ρ ∧ par u = w), b' u =
            τ w + (if w = par ℓ then τ ℓ else 0) := hb' w hwe
        have hbw : (if w = ρ then 0 else (fun w => if w = ℓ then τ ℓ else b' w) w) =
            (if w = ρ then 0 else b' w) := by
          simp only [if_neg hwℓ]
        rw [hbw, ← add_assoc, e]
        by_cases hpw : par ℓ = w
        · rw [if_pos hpw.symm, if_pos ⟨hℓρ, hpw⟩, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [if_neg (fun e => hpw e.symm), if_neg (fun h => hpw h.2), add_zero, add_zero]
    · refine ⟨fun _ => 0, fun w hw => ?_⟩
      have hSρ : S = {ρ} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨T.root, fun v hv => by
          by_contra h
          exact hS ⟨v, hv, h⟩⟩
      have hwρ : w = ρ := by
        rw [hSρ] at hw
        exact Finset.mem_singleton.mp hw
      rw [hSρ, Finset.sum_singleton] at hsum
      unfold inc
      simp only [ite_self, Finset.sum_const_zero, add_zero]
      rw [hwρ]
      exact hsum.symm

end Hedge

#print axioms Hedge.inc_surj
