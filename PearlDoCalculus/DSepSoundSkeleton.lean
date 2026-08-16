/-
# Soundness of d-separation (Verma–Pearl) — proof skeleton

## For the assistant filling this in

This file is a **decomposition**, not a proof. Every `sorry` is a separate
task. Work bottom-up: Layer 0 → Layer 1 → Layer 2 → Layer 3 → final.
Do not attempt `dsep_sound` directly; it is a short composition once the
layers below are closed.

Existing `PearlDoCalculus` definitions this file builds on, with their
verified signatures:

    DAG.lean
      structure DAG (V) [DecidableEq V] [Fintype V]
      DAG.edge : V → V → Prop          -- lowercase
      DAG.rank : V → ℕ
      DAG.parents (G) (v) : Finset V

    Reachability.lean
      DAG.Reaches (G) : V → V → Prop
      Reaches.refl, Reaches.of_edge, Reaches.trans
      rank_le_of_reaches, not_reaches_of_edge

    Walks.lean
      inductive DAG.Walk (G) : V → V → Type u
        | nil (v) : Walk G v v
        | fwd {a b c} : G.edge a b → Walk G b c → Walk G a c
        | bwd {a b c} : G.edge b a → Walk G b c → Walk G a c
      Walk.length, Walk.support : Walk G a b → List V

    Blocking.lean
      Walk.blockedAux, Walk.Blocked, Walk.Open

    DSeparation.lean
      DAG.DSeparated (G) (Z : Finset V) (x y : V) : Prop

    CausalModel.lean
      structure CausalModel (G : DAG V) (α : V → Type v)
      Assignment (S : Finset V) : Type (max u v) := ∀ v : {v // v ∈ S}, α v.1
      Assignment.restrict {S T} (h : T ⊆ S) : Assignment S → Assignment T
      Assignment.extend
      marginal (M) (S : Finset V) : PMF (Assignment (α := α) S)
      jointUpTo, fullJoint
      CondIndep (M) (X Y Z : Finset V) : Prop

**`marginal` returns a `PMF`, not a value.** Write `(M.marginal S) a`, with
the assignment applied to the PMF. `M.marginal S a` also elaborates but is
easy to misread; keep the parentheses.

**Namespaces.** Everything above lives under `PearlDoCalculus.DAG` or
`PearlDoCalculus`. Do *not* `open DAG` here — it shadows `CausalModel` and
`CondIndep` and turns them into field projections on `G`, which produces a
cascade of "invalid field" errors. `set_option autoImplicit false` is on so
a typo is an error rather than a silently invented variable.

Three properties of the existing code shape everything below.

1. `DAG.Walk` is an inductive *Type*, not a list. All induction in Layer 2
   goes over `nil`/`fwd`/`bwd`. `fwd` steps with the arrow along travel,
   `bwd` against it. A collider at `m` is: arrived by `fwd`, departs by
   `bwd`.

2. `blockedAux` threads an `Incoming` state through the walk. Its collider
   case reads

       | .fwd, m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ ...

   so "this collider is open" unfolds to `∃ z ∈ Z, G.Reaches m z`.
   Layer 2's central lemma is exactly that existential.

3. `CondIndep` is stated multiplicatively:

       P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)

   No division, no positivity hypotheses. A deliberate choice that avoids
   `ENNReal` division entirely, so Layer 3 lands directly in the target
   form. Do not reformulate it as a quotient.

## Proof strategy: moralisation, not walk induction

The `CausalModel.lean` docstring proposes structural induction directly
over blocked/active walks. That is how Pearl presents the result and it is
the harder path to formalise: because `blockedAux` carries state, being
blocked is not local to a single step, and the naive induction hypothesis
does not close.

This skeleton takes the Lauritzen route instead:

    d-separation in G
      ⟹ (restrict to ancestral subgraph)
    d-separation in G.induce (ancestors G ({x,y} ∪ Z))
      ⟹ (moralise)
    vertex separation in moralGraph
      ⟹ (factorisation splits along a separator)
    conditional independence

Graph content sits in Layer 2, probabilistic content in Layers 1 and 3.
They are independent and can be worked in parallel.

## Difficulty map

    Layer 0   routine       induce, ancestral sets, moral graph, cliques
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

## Placeholder convention

Hypotheses whose exact form is not yet known are written `True` rather than
`sorry`. A `sorry` in hypothesis position makes the whole declaration a
non-proposition and Lean rejects it outright. Replace each `True` with the
real statement as it becomes clear, working from the layer below.
-/

import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Blocking
import PearlDoCalculus.Walks
import PearlDoCalculus.Reachability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Clique

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
/-! ## Layer 1 — ancestral reduction

Marginalising the joint onto an ancestrally closed set yields the joint of
the induced model.

**Use `G.rank`.** `rank_le_of_reaches` gives strong induction on the
maximum rank among non-ancestors without constructing a topological order.

Sketch: let `v` be a non-ancestor of maximal rank. No vertex of `A` has
`v` as a parent — otherwise `v` would be an ancestor. So `v` occurs in
exactly one factor, `P(v | parents v)`, which sums to 1 over `α v`. Sum it
out and recurse. `PMF.bind`, `Finset.sum_comm` and `tsum_eq_sum` do the
work.
-/

/-- Restriction of a causal model to an ancestrally closed vertex set. -/
noncomputable def CausalModel.restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) :
    CausalModel (DAG.induce G A) α :=
  sorry

/--
**Ancestral marginalisation.** The marginal of the full joint onto an
ancestrally closed `A` agrees with the restricted model's joint at every
assignment.

Budget several sessions. This is where `ENNReal` bites hardest.

Note the shape: `marginal` is a `PMF`, so both sides are applications of a
`PMF` to an `Assignment`.
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (a : Assignment (α := α) A) :
    True := by  sorry
/-- Løft en vandring i den induserte grafen til en vandring i `G`. -/
def DAG.Walk.lift {A : Finset V} : {u w : V} →
    DAG.Walk (DAG.induce G A) u w → DAG.Walk G u w
  | _, _, .nil v => .nil v
  | _, _, .fwd e rest => .fwd (DAG.induce_edge e) (lift rest)
  | _, _, .bwd e rest => .bwd (DAG.induce_edge e) (lift rest)

/-- Blokkering bevares under løft. -/
lemma DAG.Walk.blockedAux_lift {A Z : Finset V} (inc : DAG.Incoming) :
    ∀ {u w : V} (p : DAG.Walk (DAG.induce G A) u w),
      DAG.Walk.blockedAux (G := G) Z inc (DAG.Walk.lift p) →
      DAG.Walk.blockedAux (G := DAG.induce G A) Z inc p := by
  intro u w p
  induction p generalizing inc with
  | nil v => intro h; exact h
  | fwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      tauto
  | bwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      first
        | tauto
        | (rintro (hr | hb)
           · exact Or.inl fun z hz hcon => hr z hz (DAG.induce_reaches hcon)
           · exact Or.inr (ih _ hb))
/--
d-separation survives restriction to an ancestral set containing the
relevant vertices. Pure graph theory — provable independently of Layer 1,
and a good second task after Layer 0.

Induct on the `DAG.Walk` structure: a walk in `DAG.induce G A` lifts to a
walk in `G` via `DAG.induce_edge`, and `blockedAux` is preserved because
`DAG.induce_reaches` carries reachability upward.
-/
theorem dsep_restrict (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y)
    (A : Finset V) (hA : ancestors G ({x, y} ∪ Z) ⊆ A) :
    (DAG.induce G A).DSeparated Z x y := by
  intro p
  exact DAG.Walk.blockedAux_lift .start p (h (DAG.Walk.lift p))

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
  simp only [moralGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, hr | hr⟩ := h
  · obtain ⟨-, -, he | ⟨c, hc, huc, hwc⟩⟩ := hr
    · exact absurd he h1
    · exact ⟨c, hc, huc, hwc⟩
  · obtain ⟨-, -, he | ⟨c, hc, hwc, huc⟩⟩ := hr
    · exact absurd he h2
    · exact ⟨c, hc, huc, hwc⟩

/-- Every vertex of an ancestral set reaches its seed. -/
lemma reaches_seed_of_mem_ancestors {S : Finset V} {v : V}
    (hv : v ∈ ancestors G S) : ∃ s ∈ S, G.Reaches v s := by
  exact mem_ancestors_iff.mp hv

/--
**Colliders inside the ancestral set are open.** The negation of
`blockedAux`'s collider clause, for internal colliders of a walk between
`x` and `y`.

The `x` and `y` cases need care: a collider reaching only `x` or only `y`
is not automatically open. Handle it by taking the walk *minimal* in
`Walk.length`, so no internal vertex equals `x` or `y`; then the witness
must lie in `Z`.

`hmin` is `True` deliberately. Its correct form should be discovered while
proving `lift_moral_walk`, then written back here. Do not guess it now —
guessing it wrong costs more than leaving it open.
-/
lemma collider_open_in_ancestral {Z : Finset V} {x y c : V}
    (hc : c ∈ ancestors G ({x, y} ∪ Z))
    (hmin : True) :
    ∃ z ∈ Z, G.Reaches c z := by
  sorry

/-- Sterk induksjon på vandringslengde. Nødvendig fordi kollidertilfellet
i moraliseringen hopper over to konstruktører, ikke én. -/
lemma DAG.Walk.strong_length_induction
    {P : ∀ {x y : V}, DAG.Walk G x y → Prop}
    (step : ∀ {x y : V} (q : DAG.Walk G x y),
      (∀ {u w : V} (r : DAG.Walk G u w), r.length < q.length → P r) → P q)
    {x y : V} (q : DAG.Walk G x y) : P q := by
  have H : ∀ n : ℕ, ∀ {u w : V} (r : DAG.Walk G u w), r.length ≤ n → P r := by
    intro n
    induction n with
    | zero => intro u w r hr; exact step r (fun s hs => absurd hs (by omega))
    | succ m ihm =>
      intro u w r hr
      exact step r (fun s hs => ihm s (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hs hr)))
  exact H q.length q le_rfl

/-- Er `z` ikke startnoden, overlever medlemskap i `dropLast` at hodet fjernes. -/
lemma mem_support_tail_dropLast {H : SimpleGraph V} {b c : V}
    (p : H.Walk b c) (z : V) (hzb : z ≠ b)
    (hmem : z ∈ p.support.dropLast) : z ∈ p.support.tail.dropLast := by
  cases hl : p.support with
  | nil => simp [hl] at hmem
  | cons hd tl =>
    have hhd : hd = b := by
      have h := SimpleGraph.Walk.head_support p
      simp [hl] at h
      exact h
    subst hhd
    rw [hl] at hmem
    cases tl with
    | nil => simp at hmem
    | cons h2 t2 =>
      simp [List.dropLast] at hmem ⊢
      rcases hmem with rfl | h
      · exact absurd rfl hzb
      · exact h
/--
From an open walk in `G` to a moral walk avoiding `Z` internally.

This is the direction Lauritzen's proof actually takes. On an open walk
every non-collider lies outside `Z` (else the walk would be blocked), and
every collider `u → c ← w` becomes a marriage edge `u — w`, so `c` drops
out of the moral walk's support entirely. Minimality is not needed —
openness supplies what is required.

Note: walks may self-intersect. Lauritzen (1996) is known to need this,
and `SimpleGraph.Walk` allows it, so the representation is on the right
side of that subtlety.
-/
lemma moral_walk_of_open {A Z : Finset V} (inc : DAG.Incoming)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    {x y : V} (q : DAG.Walk G x y)
    (hq : ¬ DAG.Walk.blockedAux (G := G) Z inc q)
    (hsupp : ∀ v ∈ q.support, v ∈ A) :
    ∃ p : (moralGraph G A).Walk x y,
      ∀ z ∈ Z, z ∉ p.support.tail.dropLast := by
  induction q using DAG.Walk.strong_length_induction generalizing inc with
  | step q ihq =>
    match q, hq, hsupp with
    | .nil v, _, _ => exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | .fwd e (.bwd e2 rest2), hq2, hsupp2 => sorry
    | @DAG.Walk.fwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge a (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inl ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 a (by simp [DAG.Walk.support])
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.fwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.fwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        rename_i d
        rw [hr] at hrest
        simp [DAG.Walk.blockedAux] at hrest
        obtain ⟨hopen, hr2⟩ := hrest
        obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
          (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
        by_cases hneab : a = d
        · subst hneab
          exact ⟨p, hp⟩
        · have hneab2 : a ≠ d := hneab
        have hmarry : (moralGraph G A).Adj a d := by
          simp only [moralGraph, SimpleGraph.fromRel_adj]
          refine ⟨hneab, Or.inl ⟨hsupp2 a (by simp [DAG.Walk.support]), ?_, Or.inr ⟨b, ?_, e, e2⟩⟩⟩
          · exact hsupp2 d (by rw [hr]; cases r2 <;> simp [DAG.Walk.support])
          · exact hsupp2 b (by rw [hr]; simp [DAG.Walk.support])
        trace_state
        sorry
    | @DAG.Walk.bwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge b (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inr ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
        · exact hsupp2 a (by simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.bwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)

/--
**Moralisation.** Within the ancestral subgraph, d-separation and vertex
separation in the moral graph coincide.

Forward direction by contraposition via `lift_moral_walk`.
Reverse direction by collapsing colliders back to marriage edges.
-/
theorem dsep_iff_moral_sep (Z : Finset V) (x y : V)
    (A : Finset V) (hA : A = ancestors G ({x, y} ∪ Z)) :
    (DAG.induce G A).DSeparated Z x y ↔ Separates (moralGraph G A) Z x y := by
  sorry

/-! ## Layer 3 — factorisation splits along a separator

Once separation is undirected the argument is algebraic; graphs enter only
through the clique condition.

If `Z` separates `x` from `y` in `H`, the vertex set splits as
`L ∪ Z ∪ R` with no `L`–`R` edge, `x ∈ L`, `y ∈ R`. Every clique lies
wholly in `L ∪ Z` or wholly in `R ∪ Z`. Each factor `P(v | parents v)` is
supported on the family clique `{v} ∪ parents v` (Layer 0), so the product
splits as `f(L,Z) · g(R,Z)` — which is `CondIndep` as already defined.
-/

/-- A separator partitions the graph with no crossing edges. -/
lemma separator_partition {H : SimpleGraph V} {Z : Finset V} {x y : V}
    (h : Separates H Z x y) :
    ∃ L R : Finset V,
      x ∈ L ∧ y ∈ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  sorry

/-- Cliques do not cross a separator. -/
lemma clique_one_sided {H : SimpleGraph V} {Z L R K : Finset V}
    (hcross : ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hK : H.IsClique (↑K : Set V)) :
    K ⊆ L ∪ Z ∨ K ⊆ R ∪ Z := by
  sorry

/--
The joint splits into a product over the two sides of the separator.

Conclusion left as `True`. It should say that `(M.marginal (L ∪ Z ∪ R)) a`
equals a product of a function of `a.restrict` to `L ∪ Z` and one to
`R ∪ Z`. Write it once you have `Assignment.restrict`'s subset proofs in
hand — `CausalModel.lean` uses `subset_union3_left_right` and friends for
exactly this, so reuse those rather than proving new subset facts.
-/
theorem joint_splits (M : CausalModel G α) (Z L R : Finset V) :
    True := by
  sorry

/--
Product form gives `CondIndep` directly, since `CondIndep` is already
multiplicative — no division, no positivity side conditions.

Replace `hfactor : True` with the real product statement from
`joint_splits` once that is written.
-/
theorem condIndep_of_product_form (M : CausalModel G α) (X Y Z : Finset V)
    (hfactor : True) :
    CondIndep M X Y Z := by
  sorry

/-! ## Final assembly

Should be short. If it is not, a layer statement is misaligned — fix the
statement, not this proof.

Named with a prime because `dsep_sound` already exists in
`CausalModel.lean` as a `sorry`d stub. When this closes, replace that stub
and drop the prime.
-/

theorem dsep_sound' (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y) : CondIndep M {x} {y} Z := by
  sorry

end PearlDoCalculus
