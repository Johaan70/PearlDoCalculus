/-
# Soundness of d-separation (Verma–Pearl) — proof skeleton

## For the assistant filling this in

This file is a **decomposition**, not a proof. Every `sorry` is a separate
task. Work bottom-up: Layer 0 → Layer 1 → Layer 2 → Layer 3 → final.
Do not attempt `dsep_sound` directly; it is a short composition once the
layers below are closed.

Signatures were written against the actual `PearlDoCalculus` API.
Existing definitions this file depends on:

    DAG.lean          G.edge : V → V → Prop        (lowercase)
                      G.rank : V → ℕ               (topological order)
                      G.parents v : Finset V
    Reachability.lean G.Reaches : V → V → Prop     (reflexive-transitive)
                      Reaches.refl, Reaches.trans, rank_le_of_reaches
    Walks.lean        Walk G a b : Type u          (inductive: nil/fwd/bwd)
                      Walk.length, Walk.support
    Blocking.lean     blockedAux, Blocked, Open
    DSeparation.lean  DSeparated G Z x y
    CausalModel.lean  CausalModel, jointUpTo, marginal, CondIndep

Three properties of the existing code shape everything below.

1. `Walk` is an inductive *Type* with constructors `nil`, `fwd`, `bwd`.
   All induction in Layer 2 goes over this structure, not over lists.
   `fwd (e : G.edge a b)` steps `a → b` with the arrow along travel;
   `bwd (e : G.edge b a)` steps `a → b` with the arrow against travel.
   A collider at `m` is therefore: arrived by `fwd`, departs by `bwd`.

2. `blockedAux` threads an `Incoming` state (`start`/`fwd`/`bwd`) through
   the walk. Its collider case reads

       | .fwd, m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ ...

   so "this collider is open" unfolds to `∃ z ∈ Z, G.Reaches m z`.
   Layer 2's central lemma is exactly that existential.

3. `CondIndep` is stated multiplicatively:

       P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)

   No division, no positivity hypotheses. This is a deliberate design
   choice — it avoids `ENNReal` division entirely. Layer 3 therefore
   lands directly in the target form. Do not reformulate as a quotient.

## Proof strategy: moralisation, not walk induction

The `CausalModel.lean` docstring proposes structural induction directly
over blocked/active walks. That is how Pearl presents the result and it is
the harder path to formalise: because `blockedAux` carries state, being
blocked is not local to a single step, and the naive induction hypothesis
does not close.

This skeleton takes the Lauritzen route instead:

    d-separation in G
      ⟹ (restrict to ancestral subgraph)
    d-separation in G[An({x,y} ∪ Z)]
      ⟹ (moralise)
    vertex separation in moral(G[An({x,y} ∪ Z)])
      ⟹ (factorisation splits along a separator)
    conditional independence

The graph-theoretic content sits in Layer 2, the probabilistic content in
Layers 1 and 3. They are independent and can be worked in parallel.

## Difficulty map

    Layer 0   routine       ancestral sets, moral graph, cliques
    Layer 1   HARD          marginalisation onto an ancestral set
    Layer 2   HARDEST       d-separation ↔ moral separation
    Layer 3   medium        product form ⟹ CondIndep
    Final     short         composition

If Layer 2 resists, the induction is stated wrong. Change the statement
before fighting the tactic.

## Arithmetic warning

`jointUpTo` and `marginal` land in `ENNReal`, not `ℝ≥0`. Lemmas proved for
`ℝ≥0` do not apply and fail in confusing ways — `div_lt_one`, `norm_num` on
fractions, and `decide` on numerals all behave differently. When a goal
looks like it should close but does not, run `set_option pp.all true` and
read the type before reaching for another tactic. `ENNReal.div_lt_iff` and
`tsub_eq_zero_iff_le` are the workhorses; truncated subtraction is a trap.
-/

import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Blocking
import PearlDoCalculus.Walks
import PearlDoCalculus.Reachability
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open DAG

/-! ## Layer 0 — ancestral sets and the moral graph

`Reaches` already exists as a `Prop`. Missing: the `Finset` of ancestors,
and the moral graph built over it.
-/

/--
Ancestors of `S`: every vertex reaching some element of `S`. Contains `S`
by reflexivity of `Reaches`.

If `Reachability.lean` provides a `Decidable` instance for `G.Reaches`,
use it and drop `noncomputable`.
-/
noncomputable def ancestors (G : DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∃ s ∈ S, G.Reaches v s)

lemma mem_ancestors_iff {S : Finset V} {v : V} :
    v ∈ ancestors G S ↔ ∃ s ∈ S, G.Reaches v s := by
  sorry

/-- `S ⊆ ancestors G S`, by `Reaches.refl`. -/
lemma subset_ancestors (S : Finset V) : S ⊆ ancestors G S := by
  sorry

/-- Ancestral sets are closed under taking parents. -/
lemma ancestors_parent_closed {S : Finset V} {v w : V}
    (hv : v ∈ ancestors G S) (hw : G.edge w v) : w ∈ ancestors G S := by
  sorry

/-- Idempotence, via `Reaches.trans`. -/
lemma ancestors_ancestors (S : Finset V) :
    ancestors G (ancestors G S) = ancestors G S := by
  sorry

/--
Moral graph on vertex set `A`: `G`'s edges with direction forgotten, plus
a marriage edge between any two parents of a common child in `A`.

Marriage edges are exactly the colliders. That correspondence is the whole
point of the construction and drives Layer 2.
-/
noncomputable def moralGraph (G : DAG V) (A : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u w =>
    u ∈ A ∧ w ∈ A ∧
      (G.edge u w ∨ ∃ c ∈ A, G.edge u c ∧ G.edge w c))

/-- Vertex separation: every walk from `x` to `y` meets `Z`. -/
def SimpleGraph.Separates (H : SimpleGraph V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : H.Walk x y, ∃ z ∈ Z, z ∈ p.support

/-- The family `{v} ∪ parents v` is a clique in the moral graph. -/
lemma moral_family_clique (A : Finset V) (v : V) (hv : v ∈ A)
    (hpa : ∀ w ∈ G.parents v, w ∈ A) :
    (moralGraph G A).IsClique (insert v (G.parents v) : Finset V) := by
  sorry

/-! ## Layer 1 — ancestral reduction

Marginalising the joint onto an ancestrally closed set yields the joint of
the induced model.

**Use `G.rank`.** The `DAG` structure already carries a rank with
`rank_le_of_reaches`, so strong induction on the maximum rank among
non-ancestors is available without constructing a topological order.

Sketch: let `v` be a non-ancestor of maximal rank. No vertex of `A` has
`v` as a parent — otherwise `v` would be an ancestor. So `v` occurs in
exactly one factor, `P(v | pa v)`, which sums to 1 over `α v`. Sum it out
and recurse. `PMF.bind`, `Finset.sum_comm` and `tsum_eq_sum` do the work.
-/

/-- Restriction of a causal model to an ancestrally closed vertex set. -/
noncomputable def CausalModel.restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) :
    CausalModel (G.induce A) α :=
  sorry

/--
**Ancestral marginalisation.** The marginal of the full joint onto an
ancestrally closed `A` equals the joint of the restricted model.

Budget several sessions. This is where `ENNReal` bites hardest.
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (w : Assignment (α := α) A) :
    M.marginal A w = (M.restrictTo A hA).jointUpTo w := by
  sorry

/--
d-separation survives restriction to an ancestral set containing the
relevant vertices. Pure graph theory — provable independently of Layer 1.

Induct on the `Walk` structure: a walk in `G.induce A` lifts to a walk in
`G`, and `blockedAux` is preserved because reachability inside `A` implies
reachability in `G`.
-/
theorem dsep_restrict (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y)
    (A : Finset V) (hA : ancestors G ({x, y} ∪ Z) ⊆ A) :
    (G.induce A).DSeparated Z x y := by
  sorry

/-! ## Layer 2 — moralisation

The crux. Everything else is bookkeeping around this equivalence.

**Central observation.** A marriage edge `u — w` in `moralGraph G A` that
is not an edge of `G` comes from a shared child `c ∈ A`, i.e. `u → c ← w`
— a collider. Inside `A = ancestors G ({x,y} ∪ Z)` every vertex reaches
`x`, `y`, or some `z ∈ Z`. For an internal collider on a walk between `x`
and `y`, that witness can be pushed into `Z`, giving
`∃ z ∈ Z, G.Reaches c z` — precisely the negation of `blockedAux`'s
collider clause.

Marriage edges and open colliders are the same phenomenon. This is why the
ancestral reduction must come first: outside `A` the correspondence fails.

Only the forward direction is needed for soundness, but state both — the
converse is the completeness half, and proving them together tends to
force a cleaner statement.
-/

/-- A moral edge absent from `G` arises from a shared child. -/
lemma moral_edge_witness {A : Finset V} {u w : V}
    (h : (moralGraph G A).Adj u w) (h1 : ¬ G.edge u w) (h2 : ¬ G.edge w u) :
    ∃ c ∈ A, G.edge u c ∧ G.edge w c := by
  sorry

/-- Every vertex of an ancestral set reaches its seed. -/
lemma reaches_seed_of_mem_ancestors {S : Finset V} {v : V}
    (hv : v ∈ ancestors G S) : ∃ s ∈ S, G.Reaches v s := by
  sorry

/--
**Colliders inside the ancestral set are open.** This is the negation of
`blockedAux`'s collider clause, established for internal colliders of a
walk between `x` and `y`.

The `x` and `y` cases need care: a collider reaching only `x` or only `y`
is not automatically open. Handle it by taking the walk to be *minimal* in
`Walk.length`, so no internal vertex equals `x` or `y`; then the witness
must lie in `Z`. State minimality as a hypothesis here rather than
discovering the need three lemmas later.
-/
lemma collider_open_in_ancestral {Z : Finset V} {x y c : V}
    (hc : c ∈ ancestors G ({x, y} ∪ Z))
    (hmin : sorry) :
    ∃ z ∈ Z, G.Reaches c z := by
  sorry

/--
Lifting a moral walk: expand each marriage edge into `u → c ← w`, and
show the resulting `Walk G x y` is `Open Z`.

Induct on the `SimpleGraph.Walk` structure; each step produces either one
`fwd`/`bwd` constructor or the two-step collider expansion.
-/
lemma lift_moral_walk {A Z : Finset V} {x y : V}
    (hA : A = ancestors G ({x, y} ∪ Z))
    (p : (moralGraph G A).Walk x y)
    (hp : ∀ z ∈ Z, z ∉ p.support) :
    ∃ q : Walk G x y, Walk.Open Z q := by
  sorry

/--
**Moralisation.** Within the ancestral subgraph, d-separation and vertex
separation in the moral graph coincide.

Forward direction by contraposition via `lift_moral_walk`.
Reverse direction by collapsing colliders back to marriage edges.
-/
theorem dsep_iff_moral_sep (Z : Finset V) (x y : V)
    (A : Finset V) (hA : A = ancestors G ({x, y} ∪ Z)) :
    (G.induce A).DSeparated Z x y ↔ (moralGraph G A).Separates Z x y := by
  sorry

/-! ## Layer 3 — factorisation splits along a separator

Once separation is undirected the argument is algebraic; graphs enter only
through the clique condition.

If `Z` separates `x` from `y` in `H`, the vertex set splits as
`L ∪ Z ∪ R` with no `L`–`R` edge, `x ∈ L`, `y ∈ R`. Every clique lies
wholly in `L ∪ Z` or wholly in `R ∪ Z`. Each factor `P(v | pa v)` is
supported on the family clique `{v} ∪ pa v` (Layer 0), so the product
splits as `f(L,Z) · g(R,Z)` — which is `CondIndep` as already defined.
-/

/-- A separator partitions the graph with no crossing edges. -/
lemma separator_partition {H : SimpleGraph V} {Z : Finset V} {x y : V}
    (h : H.Separates Z x y) :
    ∃ L R : Finset V,
      x ∈ L ∧ y ∈ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  sorry

/-- Cliques do not cross a separator. -/
lemma clique_one_sided {H : SimpleGraph V} {Z L R K : Finset V}
    (hcross : ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hK : H.IsClique (K : Set V)) :
    K ⊆ L ∪ Z ∨ K ⊆ R ∪ Z := by
  sorry

/-- The joint splits into a product over the two sides of the separator. -/
theorem joint_splits (M : CausalModel G α) (Z L R : Finset V)
    (hsplit : sorry) :
    sorry := by
  sorry

/--
Product form gives `CondIndep` directly, since `CondIndep` is already
stated multiplicatively — no division, no positivity side conditions.
-/
theorem condIndep_of_product_form (M : CausalModel G α) (X Y Z : Finset V)
    (hfactor : sorry) :
    CondIndep M X Y Z := by
  sorry

/-! ## Final assembly

Should be short. If it is not, a layer statement is misaligned — fix the
statement, not this proof.
-/

theorem dsep_sound (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y) : CondIndep M {x} {y} Z := by
  sorry

end PearlDoCalculus
