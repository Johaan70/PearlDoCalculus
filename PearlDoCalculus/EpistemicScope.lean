/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DAG
import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation

/-!
# Epistemic scope

This module contains no proofs about causal relations. It exists to make explicit,
inside the formal system itself, where the line runs between what the library
*establishes* and what the library *assumes*. It is not imported by any proof.

## The distinction

**Deductive content: what Lean verifies.** Given a `DAG G` and a `CausalModel G α`, the
adjustment formulas follow necessarily from the structure of the model.
`frontdoor_adjustment_observable` is verified without `sorry`, and `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`. This is a result about a formal
calculus, like any other verified system of inference.

**Content outside the system: what Lean cannot verify, not even in principle.** Whether
a given `DAG G` is the correct representation of an empirical phenomenon. This includes:
whether the edge relation corresponds to actual causal mechanisms, whether every common
cause is among the vertices, whether the division into variables is the right one, and
whether intervention as formalised here (truncated factorization) is the right semantics
for the causal question being asked.

Collingwood's point, transposed: verifying a proof re-enacts the *logic* of an inference
from its premises. It does not, and cannot, re-enact the *judgement* that decided that
the premises hold in a given situation. That judgement is empirical, historical and
revisable in ways that a `sorry`-free Lean proof is not.

## What this module does

It names the assumptions and gives them a place to live in the signature, so that no
lemma of the library can be cited without also citing what it assumed.

The status marking is in the documentation, not in the type. This is on purpose: the
epistemic status of an assumption has no logical content, and putting it into the type
would suggest that Lean can check it.

**Main definitions.** The named assumptions `GraphFaithfulToPhenomenon`,
`CausalSufficiency`, `InterventionSemantics`, `VariableIndividuation`,
`FiniteDiscreteValues`; the wrapper `ScopedResult`; the weight of an argument,
`ArgumentWeight` and `WeightedCausalSufficiency`.
-/

namespace PearlDoCalculus.EpistemicScope

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## 1. Assumptions as named objects

Rather than letting assumptions like "no unmeasured confounders" live implicitly inside
a hypothesis without further comment, we name every recurring assumption. This gives no
deductive power. It gives a place to attach the epistemic status, and forces every
theorem that uses one of them to say so in its signature rather than in prose.
-/

/--
**The graph corresponds to the phenomenon.** That the edge relation of `G` actually
represents the causal mechanisms of the system under study.

*Status: empirical.* No check inside the graph certifies this. It is a substantive claim
about the world, justified (if at all) by experiment, domain knowledge or argument from
background science.

The field is `True` because there is nothing to fill in. It is not a placeholder for a
future proof.
-/
structure GraphFaithfulToPhenomenon (G : DAG V) : Prop where
  assumed : True

/--
**Causal sufficiency.** That every common cause of two or more variables of `V` lies in
`V` itself, that is, no unmeasured confounding.

This is the most consequential assumption behind identification results such as
front-door and back-door.

*Status: empirical, and strictly speaking unfalsifiable from observational data alone.*
The justification always lies outside the graph: study design, domain knowledge of what
was actually measured.

Note: `FrontDoorModel` in `FrontDoor.lean` encodes a *specific* confounding structure in
its type: `U` affects both `X` and `Y`. This is a strength of that construction: the
confounding is explicit, not assumed away. But that this structure is the *right* one
for a given phenomenon remains empirical.
-/
structure CausalSufficiency (G : DAG V) : Prop where
  assumed : True

/--
**Intervention semantics.** That `do(X = x)` as truncated factorization (replacing
`pX_given_U` by a point mass) is the right formalisation of the causal question.

*Status: conventional.* This is not true or false, but a choice with consequences. Other
notions of intervention exist (soft interventions, policy interventions conditioned on
observed variables), and they give other identification results.
-/
structure InterventionSemantics (G : DAG V) : Prop where
  assumed : True

/--
**Division into variables.** The choice to represent the vertex set with
`[DecidableEq V]` and `[Fintype V]`.

*Status: conventional.* It is a decision about how variables are individuated in the
formalism, taken for reasons of proof technique (`Finset` and decidable graph
operations). It is not neutral: it assumes that the identity of variables is always
decidable, and that the vertex set is finite.

This is the answer to the question Zixiao Jolene Wang asked in `#Statlib` on Zulip,
about why `DecidableEq V` sits at the level of the structure. The honest answer is that
it came from the `Finset` representation rather than from a choice of principle, and
that it should therefore be documented as a modelling decision, not as a technical
footnote.

The consequence is real: the library cannot express causal models over continuous or
infinite spaces of variables without another representation.
-/
structure VariableIndividuation : Prop where
  assumed : True

/--
**Finite discrete value spaces.** That every `α v` is a `Fintype` with `DecidableEq`, as
the `CausalModel` structure requires.

*Status: conventional.* Measure-theoretic causality with continuous variables needs
another foundation than `PMF` over finite types. This is not a weakness of the results,
but a limit on what they apply to.
-/
structure FiniteDiscreteValues (α : V → Type v) : Prop where
  assumed : True

/-! ## 2. The scope of a theorem, made explicit in the signature

The pattern below is the concrete deliverable: every identification theorem of this
library should be possible to wrap in this form, so that reading the *signature*,
without README or paper, already tells what kind of claim is being made.
-/

/--
An identification result with its scope attached: the deductive content `claim`,
together with the empirical and conventional assumptions it rests on, made into
arguments rather than context in prose.

`frontdoor_adjustment_observable` can be wrapped as an instance of this. The deductive
content stays exactly as strong as it already is. What changes is that the assumptions
become visible in the type, rather than having to be worked out by whoever cites the
result.
-/
structure ScopedResult (G : DAG V) (α : V → Type v) (claim : Prop) where
  /-- What Lean actually verifies. -/
  deductive_content : claim
  /-- That the graph corresponds to the phenomenon. Empirical. -/
  graph_faithful : GraphFaithfulToPhenomenon G
  /-- That every common cause is included. Empirical. -/
  sufficiency : CausalSufficiency G
  /-- That truncated factorization is the right notion of intervention. Conventional. -/
  intervention : InterventionSemantics G
  /-- That individuating variables with `DecidableEq` is adequate. Conventional. -/
  individuation : VariableIndividuation
  /-- That finite discrete value spaces are adequate. Conventional. -/
  finite_values : FiniteDiscreteValues α
  /--
  A free-text pointer to the empirical justification, if any, of the assumptions above in
  the concrete application the result is used in. Deliberately not machine-checkable;
  that is the whole point.
  -/
  empirical_note : String := ""

/-! ## 3. What this module cannot do

This is a comment because it cannot be a theorem.

**No definition here can verify that the assumptions hold for any actual set of
variables.** `assumed : True` is not a placeholder for a future proof; there is no proof
to fill in. These are empirical claims about causal structure in the world, checkable
(if at all) only by experiment, domain knowledge or argument outside the formalism.

**`ScopedResult` makes no lemma "more true".** It makes the *terms of use* of an already
true lemma readable at the point of use. The deductive guarantee was always exactly as
strong as what `frontdoor_adjustment_observable` proves. What was missing was a
structural reminder, visible in the type, that the guarantee is conditional.

**This is not a reservation about the value of the `sorry`-free results.** A sound
calculus for identification given a graph is a genuine result. The aim here is
narrower: to keep the result from being read, by the library's own users, as settling a
question it does not settle.

**Note also how status is decided.** The project has no `sorry`, and its main results
(`DSepSound.dsep_sound`, `Hedge.idCheck_iff` and the others) depend only on the standard
axioms. But it is `#print axioms` that decides such questions, not this module.
-/

/-! ## 4. The weight of an argument (Keynes)

The status tags above (empirical, conventional) distinguish what kind of assumption
something is. They say nothing about how well supported it is.

Keynes' distinction in *A Treatise on Probability*, chapter 6: the probability of a
claim is one thing, the *weight* of the argument for it another. The weight grows with
the amount of relevant evidence, whether the evidence speaks for or against. Two
assumptions can both be empirical and still rest on entirely different grounds: one on
ten years of data from many sources, the other on one season in one place.

The status tag alone does not carry that difference. This section gives it a place to
live.
-/

/-- How broadly the evidence covers the domain the assumption is to be used in. -/
inductive DomainCoverage where
  /-- The evidence spans the relevant variation in the domain. -/
  | broad
  /-- The evidence covers parts of the domain; use outside the tested region is
      extrapolation. -/
  | narrow
  /-- The coverage is not documented. Not the same as poor, but unknown, and that
      should be stated. -/
  | undocumented
deriving Repr, DecidableEq

/--
The weight of the argument for an assumption.

Note that `justification` is free text and not a number. Compressing weight into one
scalar is exactly the reduction Keynes warned against: weight is not a probability and
does not behave like one. The field `independent_sources` is included because the number
of independent sources is a rough but useful indicator, not because weight *is* a
number.
-/
structure ArgumentWeight where
  /-- The number of independent sources of observation the assumption has been tested
      against. Independent in the sense of different regimes, places or periods, not
      raw data points from the same source. -/
  independent_sources : Nat
  /-- How broadly the evidence covers the domain of application. -/
  coverage : DomainCoverage
  /-- The justification, in plain text. Deliberately not machine-checkable. -/
  justification : String

/--
An assumption of causal sufficiency with its weight attached.

`CausalSufficiency` is a `Prop` and cannot carry data. This structure is a `Type` that
holds both: the logical assumption, and the assessment of how well supported it is.
-/
structure WeightedCausalSufficiency (G : DAG V) where
  /-- The assumption itself. Deductive content: none. -/
  assumption : CausalSufficiency G
  /-- The weight of the argument for it. -/
  weight : ArgumentWeight

/-! ### Example: same status, different weight

The two instances below have the same status: both are empirical, since no check inside
the graph can decide whether every common cause is included. But they stand on entirely
different grounds, and that is exactly what `ArgumentWeight` makes visible.

The examples are hypothetical and use an arbitrary graph `G`; the point is the form, not
the content. (The `justification` strings are data and are left in Norwegian, as
written.)
-/

/-- Heavy weight: broad, long-running evidence from many independent sources. -/
def heavyWeightExample (G : DAG V) (h : CausalSufficiency G) :
    WeightedCausalSufficiency G where
  assumption := h
  weight :=
    { independent_sources := 50000
      coverage := .broad
      justification :=
        "Ti år, flere uavhengige innsamlingssteder, dekker den relevante " ++
        "variasjonen i driftsforhold." }

/-- Light weight: the same status, but a narrow basis and extrapolation. -/
def lightWeightExample (G : DAG V) (h : CausalSufficiency G) :
    WeightedCausalSufficiency G where
  assumption := h
  weight :=
    { independent_sources := 40
      coverage := .undocumented
      justification :=
        "Én sesong, ett sted. Brukes utenfor det testede området — " ++
        "ikke representativt for domenet forutsetningen anvendes på." }

/-! ### What the weight does not do

`ArgumentWeight` changes nothing logically. `heavyWeightExample` and
`lightWeightExample` have the same deductive content: both carry a `CausalSufficiency`,
and both say `assumed : True`.

The difference is readable by a human and by tools: a linter could flag results that
rest on assumptions with `coverage := .undocumented`. But it cannot decide whether the
weight is sufficient. That is a judgement, not a computation, and that is Keynes' whole
point.
-/
end PearlDoCalculus.EpistemicScope
