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

Layer 0 of the Lauritzen route to soundness of d-separation (`DSepSound.dsep_sound`).
It defines the induced subgraph `DAG.induce`, the ancestor set `ancestors`, the moral
graph `moralGraph` and vertex separation `Separates`, and proves the basic closure
facts about ancestors and that every family `{v} ∪ parents v` is a clique of the moral
graph (`moral_family_clique`). Everything later in the route builds on these.
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
/-! ## Layer 0 — induced subgraphs, ancestral sets, moral graph

Nothing here is deep, but `DAG.induce` does not exist yet and everything
downstream needs it. Start here: if Layer 0 does not typecheck, the rest
of the file is built on sand.
-/

/--
Induced subgraph on `A`: keep only edges with both endpoints in `A`.

`DAG` carries `rank` plus whatever acyclicity condition `DAG.lean` imposes
(see lines 39–56). Reuse `G.rank` unchanged — the induced edge relation is
a subrelation, so any rank condition holding for `G` still holds.
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

/--
Ancestors of `S`: every vertex reaching some element of `S`. Contains `S`
by `Reaches.refl`. Decidability of the filter comes from `open Classical`.
-/
noncomputable def ancestors (G : DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∃ s ∈ S, G.Reaches v s)

lemma mem_ancestors_iff {S : Finset V} {v : V} :
    v ∈ ancestors G S ↔ ∃ s ∈ S, G.Reaches v s := by
  simp [ancestors]
/-- `S ⊆ ancestors G S`, by `Reaches.refl`. -/
lemma subset_ancestors (S : Finset V) : S ⊆ ancestors G S := by
  intro s hs
  simp [ancestors]
  exact ⟨s, hs, DAG.Reaches.refl G s⟩

/-- Closure under parents, via `Reaches.of_edge` and `Reaches.trans`.
Short, but it does need proving — it does not come for free. -/
lemma ancestors_parent_closed {S : Finset V} {v w : V}
    (hv : v ∈ ancestors G S) (hw : G.edge w v) : w ∈ ancestors G S := by
  simp [ancestors] at hv ⊢
  obtain ⟨s, hs, hvs⟩ := hv
  exact ⟨s, hs, DAG.Reaches.trans G (DAG.Reaches.of_edge G hw) hvs⟩

/-- Idempotence, via `Reaches.trans`. -/
lemma ancestors_ancestors (S : Finset V) :
    ancestors G (ancestors G S) = ancestors G S := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp [ancestors] at hv ⊢
    obtain ⟨t, ⟨s, hs, hts⟩, hvt⟩ := hv
    exact ⟨s, hs, DAG.Reaches.trans G hvt hts⟩
  · exact subset_ancestors _

/--
Moral graph on `A`: `G`'s edges with direction forgotten, plus a marriage
edge between any two parents of a common child in `A`.

Marriage edges are exactly the colliders. That correspondence is the whole
point of the construction and drives Layer 2.
-/
noncomputable def moralGraph (G : DAG V) (A : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u w =>
    u ∈ A ∧ w ∈ A ∧
      (G.edge u w ∨ ∃ c ∈ A, G.edge u c ∧ G.edge w c))

/-- Vertex separation: every walk from `x` to `y` meets `Z`.
Defined free-standing — one cannot extend `SimpleGraph`'s namespace with
dot notation from here. -/
def Separates (H : SimpleGraph V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : H.Walk x y, ∃ z ∈ Z, z ∈ p.support

/-- The family `{v} ∪ parents v` is a clique in the moral graph.
`IsClique` wants a `Set V`, hence the coercion. -/
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
