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
/-- For noder i en ancestralt lukket mengde er foreldrene uendret av `induce`. -/
lemma DAG.induce_parents_eq (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (v : V) (hv : v ∈ A) :
    (DAG.induce G A).parents v = G.parents v := by
  ext u
  simp [DAG.parents, DAG.induce]
  constructor
  · exact fun h => h.2.2
  · exact fun he => ⟨hA v hv u he, hv, he⟩
/-- Restriction of a causal model to an ancestrally closed vertex set. -/
noncomputable def CausalModel.restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)] :
    CausalModel (DAG.induce G A) α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v => by
      classical
      by_cases hv : v ∈ A
      · rw [DAG.induce_parents_eq A hA v hv]
        exact M.kernel v
      · exact fun _ => M.kernel v (fun u => Classical.arbitrary _) }

/--
**Ancestral marginalisation.** The marginal of the full joint onto an
ancestrally closed `A` agrees with the restricted model's joint at every
assignment.

Budget several sessions. This is where `ENNReal` bites hardest.

Note the shape: `marginal` is a `PMF`, so both sides are applications of a
`PMF` to an `Assignment`.
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) :
    (M.marginal A) a = ((CausalModel.restrictTo M A hA).marginal A) a := by
  sorry
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
        by_cases hneab : a = d
        · subst hneab
          exact ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
            (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
        · have hmarry : (moralGraph G A).Adj a d := by
            simp only [moralGraph, SimpleGraph.fromRel_adj]
            refine ⟨hneab, Or.inl ⟨hsupp2 a (by simp [DAG.Walk.support]), ?_, Or.inr ⟨b, ?_, e, e2⟩⟩⟩
            · exact hsupp2 d (by rw [hr]; cases r2 <;> simp [DAG.Walk.support])
            · exact hsupp2 b (by rw [hr]; simp [DAG.Walk.support])
          cases hr2c : r2 with
          | nil w =>
            refine ⟨SimpleGraph.Walk.cons hmarry SimpleGraph.Walk.nil, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
          | fwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
          | bwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
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
/-- En node i støtten som verken er start eller slutt, er en indre node.
Siste steg (`hgl`) er en teknisk identitet om `getLast` som gjenstår. -/
lemma mem_support_interior {H : SimpleGraph V} {x y : V}
    (p : H.Walk x y) (z : V) (hzx : z ≠ x) (hzy : z ≠ y)
    (hmem : z ∈ p.support) : z ∈ p.support.tail.dropLast := by
  have hc := SimpleGraph.Walk.cons_tail_support p
  rw [← hc] at hmem
  rw [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact absurd h hzx
  · have hne : p.support.tail ≠ [] := by
      intro he
      rw [he] at h
      simp at h
    refine List.mem_dropLast_of_mem_of_ne_getLast h ?_
    have hgl : p.support.tail.getLast hne = y := by
      simp
    rw [hgl]
    exact hzy

/--
**Moralisation.** Within the ancestral subgraph, d-separation and vertex
separation in the moral graph coincide.
Only the direction needed for soundness: separation in the moral graph
implies d-separation in `G`. The converse is completeness and is open.
-/
theorem dsep_of_moral_sep (Z : Finset V) (x y : V) (A : Finset V)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hsep : Separates (moralGraph G A) Z x y)
    (hxy : ∀ (q : DAG.Walk G x y), ∀ v ∈ q.support, v ∈ A)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    G.DSeparated Z x y := by
  intro q
  by_contra hopen
  obtain ⟨p, hp⟩ := moral_walk_of_open DAG.Incoming.start hclosed q hopen (hxy q)
  obtain ⟨z, hzZ, hzmem⟩ := hsep p
  by_cases hzx : z = x
  · exact hxZ (hzx ▸ hzZ)
  by_cases hzy : z = y
  · exact hyZ (hzy ▸ hzZ)
  exact hp z hzZ (mem_support_interior p z hzx hzy hzmem)

/-! ## Layer 3 — factorisation splits along a separator

Once separation is undirected the argument is algebraic; graphs enter only
through the clique condition.

If `Z` separates `x` from `y` in `H`, the vertex set splits as
`L ∪ Z ∪ R` with no `L`–`R` edge, `x ∈ L`, `y ∈ R`. Every clique lies
wholly in `L ∪ Z` or wholly in `R ∪ Z`. Each factor `P(v | parents v)` is
supported on the family clique `{v} ∪ parents v` (Layer 0), so the product
splits as `f(L,Z) · g(R,Z)` — which is `CondIndep` as already defined.
-/
/-- `v` er nåbar fra `x` uten å berøre `Z`. -/
def ReachAvoiding (H : SimpleGraph V) (Z : Finset V) (x v : V) : Prop :=
  ∃ p : H.Walk x v, ∀ z ∈ Z, z ∉ p.support

/-- Refleksivitet, gitt at `x` selv ikke ligger i `Z`. -/
lemma reachAvoiding_refl {H : SimpleGraph V} {Z : Finset V} {x : V} (hxZ : x ∉ Z) :
    ReachAvoiding H Z x x :=
  ⟨SimpleGraph.Walk.nil, by
    intro z hz hzmem
    simp at hzmem
    subst hzmem
    exact hxZ hz⟩


/-- A separator partitions the graph with no crossing edges. -/
lemma separator_partition {H : SimpleGraph V} {Z : Finset V} {x y : V}
    (h : Separates H Z x y) (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    ∃ L R : Finset V,
      x ∈ L ∧ y ∈ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  classical
  set L := Finset.univ.filter (fun v => v ∉ Z ∧ ReachAvoiding H Z x v) with hLdef
  set R := Finset.univ \ (L ∪ Z) with hRdef
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxZ, reachAvoiding_refl hxZ⟩
  · simp only [hRdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, hLdef,
      Finset.mem_filter, not_or, not_and]
    refine ⟨?_, hyZ⟩
    intro _ hra
    obtain ⟨p, hp⟩ := hra
    obtain ⟨z, hzZ, hzmem⟩ := h p
    exact absurd hzmem (hp z hzZ)
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inl hvL)
  · rw [Finset.disjoint_left]
    intro v hvL hvZ
    simp only [hLdef, Finset.mem_filter] at hvL
    exact hvL.2.1 hvZ
  · rw [Finset.disjoint_left]
    intro v hvR hvZ
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inr hvZ)
  · rw [hRdef]
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hv : v ∈ L ∪ Z
    · rcases Finset.mem_union.mp hv with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
    · exact Or.inr (fun hc => hv (Finset.mem_union.mpr hc))
  · intro u huL w hwR hadj
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at huL
    obtain ⟨huZ, pu, hpu⟩ := huL
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and,
      not_or, hLdef, Finset.mem_filter, not_and] at hwR
    trace_state
    exact hwR.1 hwR.2 ⟨pu.concat hadj, by
      intro z hz hzmem
      rw [SimpleGraph.Walk.support_concat] at hzmem
      simp only [List.mem_append, List.mem_singleton] at hzmem
      rcases hzmem with h1 | h1
      · exact hpu z hz h1
      · subst h1; exact hwR.2 hz⟩
lemma clique_one_sided {H : SimpleGraph V} {Z L R K : Finset V}
    (hcross : ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hK : H.IsClique (↑K : Set V)) :
    K ⊆ L ∪ Z ∨ K ⊆ R ∪ Z := by
  by_cases hKR : ∃ w ∈ K, w ∈ R
  · right
    obtain ⟨w, hwK, hwR⟩ := hKR
    intro v hv
    have hvcov : v ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hvcov with h1 | h1
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · by_cases hvw : v = w
        · subst hvw; exact Finset.mem_union_left _ hwR
        · exact absurd (hK (by simpa using hv) (by simpa using hwK) hvw) (hcross v h2 w hwR)
      · exact Finset.mem_union_right _ h2
    · exact Finset.mem_union_left _ h1
  · left
    push_neg at hKR
    intro v hv
    have hvcov : v ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hvcov with h1 | h1
    · exact h1
    · exact absurd h1 (hKR v hv)

/--
The joint splits into a product over the two sides of the separator.

Conclusion left as `True`. It should say that `(M.marginal (L ∪ Z ∪ R)) a`
equals a product of a function of `a.restrict` to `L ∪ Z` and one to
`R ∪ Z`. Write it once you have `Assignment.restrict`'s subset proofs in
hand — `CausalModel.lean` uses `subset_union3_left_right` and friends for
exactly this, so reuse those rather than proving new subset facts.
-/
theorem joint_splits (M : CausalModel G α) (L Z R : Finset V)
    (hcross : ∀ u ∈ L, ∀ w ∈ R, ∀ v : V, ¬ (u ∈ G.parents v ∧ w ∈ G.parents v)) :
    ∃ (F : Assignment (α := α) L → Assignment (α := α) Z → ENNReal)
      (Gf : Assignment (α := α) R → Assignment (α := α) Z → ENNReal),
      ∀ a : Assignment (α := α) (L ∪ R ∪ Z),
        (M.marginal (L ∪ R ∪ Z)) a =
          F (a.restrict (subset_union3_left L R Z)) (a.restrict (subset_union3_right L R Z)) *
          Gf (a.restrict (subset_union3_mid L R Z)) (a.restrict (subset_union3_right L R Z)) := by
  sorry
/-- Restriksjon komponerer: `X∪Z` deretter `X` er `X` direkte. -/
@[simp] lemma restrict_XZ_X (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_left X Y Z) := rfl

/-- Restriksjon komponerer: `X∪Z` deretter `Z` er `Z` direkte. -/
@[simp] lemma restrict_XZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl

/-- Restriksjon komponerer: `Y∪Z` deretter `Y` er `Y` direkte. -/
@[simp] lemma restrict_YZ_Y (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_mid X Y Z) := rfl

/-- Restriksjon komponerer: `Y∪Z` deretter `Z` er `Z` direkte. -/
@[simp] lemma restrict_YZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl
/-- Marginalen på `X ∪ Z` er `f` ganger summen av `g`-faktorene. -/
lemma marginal_left_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (X ∪ Z)) (w.restrict (subset_union3_left_right X Y Z)) =
      f (w.restrict (subset_union3_left_right X Y Z)) *
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) =
           u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_left_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_left.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_left_right X Y Z) =
      u.restrict (subset_union3_left_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- Marginalen på `Y ∪ Z` er summen av `f`-faktorene ganger `g`. -/
lemma marginal_right_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (Y ∪ Z)) (w.restrict (subset_union3_mid_right X Y Z)) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) =
           u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) *
      g (w.restrict (subset_union3_mid_right X Y Z)) := by
  rw [← marginal_restrict M (subset_union3_mid_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_right.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_mid_right X Y Z) =
      u.restrict (subset_union3_mid_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- Tilordninger over en disjunkt union splitter i et produkt. -/
def assignmentSplit (s t : Finset V) (h : Disjoint s t) :
    Assignment (α := α) (s ∪ t) ≃ Assignment (α := α) s × Assignment (α := α) t := by
  unfold Assignment
  exact (Equiv.piCongrLeft _ (Equiv.Finset.union s t h)).symm.trans
    (Equiv.sumPiEquivProdPi _)
/-- En sum over en disjunkt union faktoriserer når integranden gjør det. -/
lemma tsum_assignmentSplit (s t : Finset V) (h : Disjoint s t)
    (F : Assignment (α := α) s → ENNReal)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        F ((assignmentSplit s t h u).1) * Gf ((assignmentSplit s t h u).2) =
      (∑' a : Assignment (α := α) s, F a) * (∑' b : Assignment (α := α) t, Gf b) := by
  rw [(assignmentSplit s t h).tsum_eq (fun p => F p.1 * Gf p.2)]
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
/-- Er første komponent låst, kollapser summen til summen over andre. -/
lemma tsum_assignmentSplit_fixed_left (s t : Finset V) (h : Disjoint s t)
    (a0 : Assignment (α := α) s)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        (if a0 = (assignmentSplit s t h u).1 then Gf ((assignmentSplit s t h u).2) else 0) =
      ∑' b : Assignment (α := α) t, Gf b := by
  rw [(assignmentSplit s t h).tsum_eq
    (fun p => if a0 = p.1 then Gf p.2 else 0)]
  rw [ENNReal.tsum_prod']
  have h1 : ∀ a : Assignment (α := α) s,
      (∑' b : Assignment (α := α) t, if a0 = a then Gf b else 0)
      = if a0 = a then (∑' b, Gf b) else 0 := by
    intro a
    by_cases ha : a0 = a
    · simp [ha]
    · simp [ha]
  simp only [h1]
  simp only [eq_comm (a := a0)]
  rw [tsum_ite_eq]
/-- Tredelt splitting for parvis disjunkte mengder. -/
def assignmentSplit3 (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXYZ : Disjoint (X ∪ Y) Z) :
    Assignment (α := α) (X ∪ Y ∪ Z) ≃
      (Assignment (α := α) X × Assignment (α := α) Y) × Assignment (α := α) Z :=
  (assignmentSplit (X ∪ Y) Z hXYZ).trans
    (Equiv.prodCongrLeft (fun _ => assignmentSplit X Y hXY))
/-- Splittingens første komponent er restriksjonen. -/
@[simp] lemma assignmentSplit_fst (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).1 = u.restrict Finset.subset_union_left := rfl

/-- Splittingens andre komponent er restriksjonen. -/
@[simp] lemma assignmentSplit_snd (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).2 = u.restrict Finset.subset_union_right := rfl
/-- En tilordning er rekonstruksjonen av sine egne komponenter. -/
@[simp] lemma assignmentSplit_symm_restrict (s t : Finset V) (h : Disjoint s t)
    (a : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h).symm
      (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right) = a := by
  have hp : (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right)
      = assignmentSplit s t h a := rfl
  rw [hp, Equiv.symm_apply_apply]
/-- To tilordninger er like presis når begge komponenter er like. -/
lemma assignment_ext_split (s t : Finset V) (h : Disjoint s t)
    (a b : Assignment (α := α) (s ∪ t)) :
    a = b ↔ (a.restrict Finset.subset_union_left = b.restrict Finset.subset_union_left
           ∧ a.restrict Finset.subset_union_right = b.restrict Finset.subset_union_right) := by
  constructor
  · intro hab
    subst hab
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have ha := assignmentSplit_symm_restrict s t h a
    have hb := assignmentSplit_symm_restrict s t h b
    rw [← ha, ← hb, h1, h2]
/-- Indikatoren på `X ∪ Z` splitter i komponentene. -/
lemma restrict_XZ_eq_iff (X Y Z : Finset V) (hXZ : Disjoint X Z)
    (w u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (w.restrict (subset_union3_left_right X Y Z)
       = u.restrict (subset_union3_left_right X Y Z))
    ↔ (w.restrict (subset_union3_left X Y Z) = u.restrict (subset_union3_left X Y Z)
     ∧ w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)) := by
  rw [assignment_ext_split X Z hXZ]
  simp only [restrict_XZ_X, restrict_XZ_Z]

/-- Indikatoren på `Y ∪ Z` splitter i komponentene. -/
lemma restrict_YZ_eq_iff (X Y Z : Finset V) (hYZ : Disjoint Y Z)
    (w u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (w.restrict (subset_union3_mid_right X Y Z)
       = u.restrict (subset_union3_mid_right X Y Z))
    ↔ (w.restrict (subset_union3_mid X Y Z) = u.restrict (subset_union3_mid X Y Z)
     ∧ w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)) := by
  rw [assignment_ext_split Y Z hYZ]
  simp only [restrict_YZ_Y, restrict_YZ_Z]
/-- Med `X ∪ Z` låst kollapser summen til summen over `Y`. -/
lemma tsum_fixed_XZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (a0 : Assignment (α := α) (X ∪ Z))
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' b : Assignment (α := α) Y, Gf b (a0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z))
             (a0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : a0 = u.restrict (subset_union3_left_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (X ∪ Z) Y := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY, hYZ.symm⟩
  rw! [Finset.union_assoc, Finset.union_comm Y Z, ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (X ∪ Z) Y hd a0
    (fun b => Gf b (a0.restrict Finset.subset_union_right))
/-- Med `Y ∪ Z` låst kollapser summen til summen over `X`. -/
lemma tsum_fixed_YZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (b0 : Assignment (α := α) (Y ∪ Z))
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' a : Assignment (α := α) X, F a (b0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z))
             (b0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : b0 = u.restrict (subset_union3_mid_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (Y ∪ Z) X := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY.symm, hXZ.symm⟩
  rw! [Finset.union_comm X Y, Finset.union_assoc, Finset.union_comm X Z,
    ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (Y ∪ Z) X hd b0
    (fun a => F a (b0.restrict Finset.subset_union_right))
/-- Med bare `Z` låst faktoriserer summen i produktet over `X` og `Y`. -/
lemma tsum_fixed_Z2 (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (c0 : Assignment (α := α) Z)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      (∑' a : Assignment (α := α) X, F a c0) * (∑' b : Assignment (α := α) Y, Gf b c0) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) c0 *
             Gf (u.restrict (subset_union3_mid X Y Z)) c0 else 0) := by
    intro u
    by_cases hu : c0 = u.restrict (subset_union3_right X Y Z)
    · simp [hu]
    · simp [hu]
  simp only [step]
  have hd : Disjoint Z (X ∪ Y) := by
    simp [Finset.disjoint_union_right]
    exact ⟨hXZ.symm, hYZ.symm⟩
  rw! [Finset.union_comm (X ∪ Y) Z]
  have hXY_sub : X ∪ Y ⊆ Z ∪ (X ∪ Y) := Finset.subset_union_right
  simp only [← Assignment.restrict_restrict hXY_sub Finset.subset_union_left,
    ← Assignment.restrict_restrict hXY_sub Finset.subset_union_right,
    ← assignmentSplit_snd Z (X ∪ Y) hd, ← assignmentSplit_fst Z (X ∪ Y) hd]
  rw [tsum_assignmentSplit_fixed_left Z (X ∪ Y) hd c0
    (fun v => F (v.restrict Finset.subset_union_left) c0 *
              Gf (v.restrict Finset.subset_union_right) c0)]
  exact tsum_assignmentSplit X Y hXY (fun a => F a c0) (fun b => Gf b c0)




/-- Marginalen på `Z` er summen av produktet over alle tilordninger som
matcher på `Z`. -/
lemma marginal_base_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal Z) (w.restrict (subset_union3_right X Y Z)) =
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_right X Y Z) =
           u.restrict (subset_union3_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) *
             g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_right X Y Z), PMF.map_apply]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_right X Y Z) =
      u.restrict (subset_union3_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]


/--
Product form gives `CondIndep` directly, since `CondIndep` is already
multiplicative — no division, no positivity side conditions.
`joint_splits`. The hypothesis says the joint factors into a function of
`X ∪ Z` and one of `Y ∪ Z`.
-/
theorem condIndep_of_product_form (M : CausalModel G α) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal)
    (hf : ∀ a : Assignment (α := α) (X ∪ Z),
      f a = F (a.restrict Finset.subset_union_left) (a.restrict Finset.subset_union_right))
    (hg : ∀ b : Assignment (α := α) (Y ∪ Z),
      g b = Gf (b.restrict Finset.subset_union_left) (b.restrict Finset.subset_union_right))
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z))) :
    CondIndep M X Y Z := by
  intro w
  rw [hfactor w]
  rw [marginal_left_factor M X Y Z f g hfactor w,
      marginal_right_factor M X Y Z f g hfactor w,
      marginal_base_factor M X Y Z f g hfactor w]
  have key : (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
      if w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)
      then f (u.restrict (subset_union3_left_right X Y Z)) *
           g (u.restrict (subset_union3_mid_right X Y Z)) else 0) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) = u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0) *
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) = u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) := by
    simp only [hf, hg, restrict_XZ_X, restrict_XZ_Z, restrict_YZ_Y, restrict_YZ_Z]
    rw [tsum_fixed_Z2 X Y Z hXY hXZ hYZ (w.restrict (subset_union3_right X Y Z)) F Gf,
      tsum_fixed_XZ2 X Y Z hXY hYZ (w.restrict (subset_union3_left_right X Y Z)) Gf,
      tsum_fixed_YZ2 X Y Z hXY hXZ (w.restrict (subset_union3_mid_right X Y Z)) F]
    simp only [Assignment.restrict_restrict]
    ring
  rw [key]
  ring

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
