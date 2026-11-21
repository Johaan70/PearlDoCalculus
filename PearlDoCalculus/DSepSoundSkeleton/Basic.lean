import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Blocking
import PearlDoCalculus.Walks
import PearlDoCalculus.Reachability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Clique
/-!
# Induced subgraphs, ancestors and the moral graph

**What it proves.** This file holds the graph vocabulary of the Lauritzen route to the
soundness of d-separation: the induced subgraph `DAG.induce G A` (keep the edges with
both ends in `A`), the ancestor set `ancestors G S` (every vertex that reaches `S`), the
moral graph `moralGraph G A` (the edges of `G` inside `A` without direction, plus an edge
between any two parents of a common child in `A`) and vertex separation `Separates`
(every walk from `x` to `y` meets `Z`). It proves the basic facts about them: induced
edges and reachability are those of `G` (`DAG.induce_edge`, `DAG.induce_reaches`),
ancestor sets contain their seed, are closed under parents and are idempotent
(`subset_ancestors`, `ancestors_parent_closed`, `ancestors_ancestors`), and every family
`{v} ∪ parents v` inside `A` is a clique of the moral graph (`moral_family_clique`).

**Why it is needed.** This is layer 0 of the route (see `DSepSoundSkeleton.lean`); every
later layer is stated in these terms. Soundness (`DSepSound.dsep_sound`) restricts to
`ancestors G ({x, y} ∪ Z)`, uses Lauritzen's theorem (`Lauritzen.lean`) to get
separation in the moral graph, and uses `moral_family_clique` to see that each kernel
factor lies on one side of the separator. Outside the route, `DAG.induce` and
`ancestors` are used throughout: by the ID algorithm (`IdAlgo.lean`), the hedge files
(`Hedge/*`), the adjustment criteria (`Adjustment.lean`) and the do-calculus rules
(`Rule3.lean`, `Rule3Flag.lean`).

**How the proofs go.** All proofs are short. The induced graph keeps the rank of `G`,
so it is again a DAG. The facts about ancestors follow from `Reaches.refl` and
`Reaches.trans`. For the family clique, two members of `{v} ∪ parents v` are either `v`
and a parent (an edge of `G`) or two parents of `v` (a marriage edge).

**Main results.** `DAG.induce`, `ancestors`, `moralGraph`, `Separates` and
`moral_family_clique`.
-/

set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel
/-! ## Induced subgraphs -/

/--
Induced subgraph on `A`: keep only edges with both endpoints in `A`.

A `DAG` carries a rank function that strictly increases along edges (`DAG.lean`).
The induced graph reuses `G.rank` unchanged: its edge relation is a subrelation of
that of `G`, so the rank still increases along every edge.
-/
def DAG.induce (G : DAG V) (A : Finset V) : DAG V where
  edge u v := u ∈ A ∧ v ∈ A ∧ G.edge u v
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := by
    intro u v h
    exact G.rank_strict_mono u v h.2.2

/-- Edges of the induced subgraph are edges of `G`. -/
lemma DAG.induce_edge {A : Finset V} {u w : V}
    (h : (DAG.induce G A).edge u w) : G.edge u w := by
  exact h.2.2

/-- Reachability in the induced subgraph implies reachability in `G`. -/
lemma DAG.induce_reaches {A : Finset V} {u w : V}
    (h : (DAG.induce G A).Reaches u w) : G.Reaches u w := by
  exact Relation.ReflTransGen.mono (fun _ _ e => DAG.induce_edge e) h

/-! ## Ancestor sets -/

/--
Ancestors of `S`: every vertex reaching some element of `S`. Contains `S`
by `Reaches.refl`. Decidability of the filter comes from `open Classical`.
-/
noncomputable def ancestors (G : DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∃ s ∈ S, G.Reaches v s)

/-- Membership in `ancestors G S`: `v` reaches some element of `S`. -/
lemma mem_ancestors_iff {S : Finset V} {v : V} :
    v ∈ ancestors G S ↔ ∃ s ∈ S, G.Reaches v s := by
  simp [ancestors]
/-- `S ⊆ ancestors G S`, by `Reaches.refl`. -/
lemma subset_ancestors (S : Finset V) : S ⊆ ancestors G S := by
  intro s hs
  simp [ancestors]
  exact ⟨s, hs, DAG.Reaches.refl G s⟩

/-- Ancestor sets are closed under parents: a parent of an ancestor of `S` is an
ancestor of `S` (`Reaches.of_edge`, then `Reaches.trans`). -/
lemma ancestors_parent_closed {S : Finset V} {v w : V}
    (hv : v ∈ ancestors G S) (hw : G.edge w v) : w ∈ ancestors G S := by
  simp [ancestors] at hv ⊢
  obtain ⟨s, hs, hvs⟩ := hv
  exact ⟨s, hs, DAG.Reaches.trans G (DAG.Reaches.of_edge G hw) hvs⟩

/-- Taking ancestors twice gives nothing new (`Reaches.trans`). -/
lemma ancestors_ancestors (S : Finset V) :
    ancestors G (ancestors G S) = ancestors G S := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp [ancestors] at hv ⊢
    obtain ⟨t, ⟨s, hs, hts⟩, hvt⟩ := hv
    exact ⟨s, hs, DAG.Reaches.trans G hvt hts⟩
  · exact subset_ancestors _

/-! ## The moral graph and vertex separation -/

/--
Moral graph on `A`: `G`'s edges with direction forgotten, plus a marriage
edge between any two parents of a common child in `A`.

A marriage edge `u — w` stands for a collider `u → c ← w`. This correspondence
is the point of the construction; `Lauritzen.lean` and
`DSepSoundSkeleton/Moralisation` turn it into a link between open walks in `G`
and walks in the moral graph.
-/
noncomputable def moralGraph (G : DAG V) (A : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u w =>
    u ∈ A ∧ w ∈ A ∧
      (G.edge u w ∨ ∃ c ∈ A, G.edge u c ∧ G.edge w c))

/-- Vertex separation: every walk from `x` to `y` in `H` meets `Z`.
It is a plain definition in `PearlDoCalculus`, not `SimpleGraph.Separates`, so it is
written `Separates H Z x y` rather than with dot notation. -/
def Separates (H : SimpleGraph V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : H.Walk x y, ∃ z ∈ Z, z ∈ p.support

/-- The family `{v} ∪ parents v` is a clique in the moral graph on `A` when `v` and its
parents lie in `A`. `IsClique` wants a `Set V`, hence the coercion. -/
lemma moral_family_clique (A : Finset V) (v : V) (hv : v ∈ A)
    (hpa : ∀ w ∈ G.parents v, w ∈ A) :
    (moralGraph G A).IsClique (↑(insert v (G.parents v)) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
    DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  simp only [moralGraph, SimpleGraph.fromRel_adj]
  refine ⟨hab, ?_⟩
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact Or.inr ⟨hpa b (by simp [DAG.parents, hb]), hv, Or.inl hb⟩
  · rcases hb with rfl | hb
    · exact Or.inl ⟨hpa a (by simp [DAG.parents, ha]), hv, Or.inl ha⟩
    · exact Or.inl ⟨hpa a (by simp [DAG.parents, ha]),
        hpa b (by simp [DAG.parents, hb]), Or.inr ⟨v, hv, ha, hb⟩⟩

end PearlDoCalculus
