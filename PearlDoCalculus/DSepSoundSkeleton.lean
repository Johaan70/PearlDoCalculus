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

import PearlDoCalculus.DSepSoundSkeleton.Moralisation
import PearlDoCalculus.DSepSoundSkeleton.AncestralReduction
import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Blocking
import PearlDoCalculus.Walks
import PearlDoCalculus.Reachability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Clique
set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel

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
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) L → Assignment (α := α) Z → ENNReal)
      (Gf : Assignment (α := α) R → Assignment (α := α) Z → ENNReal),
      ∀ a : Assignment (α := α) (L ∪ R ∪ Z),
        (M.marginal (L ∪ R ∪ Z)) a =
          F (a.restrict (subset_union3_left L R Z)) (a.restrict (subset_union3_right L R Z)) *
          Gf (a.restrict (subset_union3_mid L R Z)) (a.restrict (subset_union3_right L R Z)) := by
  have htypeU : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank]
  have hLu : Assignment (α := α) L = Assignment (α := α) (L ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hZu : Assignment (α := α) Z = Assignment (α := α) (Z ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hRu : Assignment (α := α) R = Assignment (α := α) (R ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  obtain ⟨F0, Gf0, hF0⟩ := jointUpTo_factorizes M L Z R G.maxRank hLZ hLR hZR hcover hclique
  refine ⟨fun p q => F0 (cast hLu p) (cast hZu q),
    fun p q => Gf0 (cast hRu p) (cast hZu q), ?_⟩
  intro a
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  simp only [fullJoint_apply M htypeU, hF0]
  have hcov2 : L ∪ R ∪ Z = Finset.univ := by
    rw [← hcover]
    ext x
    simp
    tauto
  have htypeA : Assignment (α := α) (L ∪ R ∪ Z)
      = Assignment (α := α) (Finset.univ : Finset V) := by
    rw [hcov2]
  simp only [eq_restrict_iff_eq_cast (L ∪ R ∪ Z) hcov2 htypeA]
  rw [tsum_ite_eq]
  simp only [cast_cast]
  rw [restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) L
      (L ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hLu a (subset_union3_left L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) Z
      (Z ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hZu a (subset_union3_right L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) R
      (R ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hRu a (subset_union3_mid L R Z)]
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

/-! Sluttmonteringen er `DSepSound.dsep_sound` i `DSepSound.lean`. -/

end PearlDoCalculus
