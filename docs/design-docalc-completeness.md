# Design note: completeness of the do-calculus for identification

*25 November 2026. Decided on 25 November 2026: all seven recommendations in
"Decisions" are accepted.*

## Goal

We prove that every identifiable effect `P(Y | do(X))` can be rewritten, using
the three rules of the do-calculus and a fixed list of probability
manipulations, into an expression that has no `do` and mentions only observed
variables. This is the completeness of the do-calculus for identification
(Huang and Valtorta 2006; Shpitser and Pearl 2006).

Together with `Hedge.idCheck_iff` this closes a triangle: the following three
statements are equivalent.

- The ID check says yes.
- The effect is identifiable.
- The effect is derivable.

```
idCheck = true  ⟺  identifiable for all value types  ⟺  ∃ e, do-free over O, with P(Y | do(X)) ⊢ e
```

The Lean shape we aim for, with the same hypotheses as `idCheck_iff`:

```lean
theorem docalc_complete (G : DAG V) (U X Y : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hXY : ∀ y ∈ Y, y ∉ X)
    (h : ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y) :
    ∃ e : Expr V, e.DoFree ∧ e.vars ⊆ Uᶜ ∧ Derives G U (Expr.query Y X) e

theorem derives_sound … (hd : Derives G U e₁ e₂) (M : G.CausalModel α)
    (hpos : ∀ a, M.marginal Uᶜ a ≠ 0) : eval M e₁ = eval M e₂
```

The second theorem is what makes the first one honest. A derivation is only
worth something if each of its steps is valid in every model.

## Starting point

Most of the mathematics is already in the project. What is new is a syntax for
derivations, and a proof that the existing semantic steps can be written as
derivations.

| Already proved | Where | Role here |
| --- | --- | --- |
| `Identifiable G α O X Y`: models with the same positive observed marginal have the same `P(Y \| do(X))` | `Identification/Basic` | the hypothesis of the theorem |
| `idCheck_iff`: the check says yes iff the effect is identifiable for all value types | `Hedge/Complete` | turns the hypothesis into a successful run |
| `IdentifyDerives G U T C`: inductive steps between c-factor sets: `refl`; `anc`, which marginalizes to an ancestral part; and `block`, which goes to a closed block | `Identification/Identify` | the skeleton the derivation follows |
| `identifyDerives_sound`: each step preserves equal and positive c-factors `Q M U T` | `Identification/Identify` | the semantic content of each step |
| Rules 1, 2 and 3 (`rule3_general` without positivity) and their set versions | `DoCalculus`, `Rule3Flag`, `Completeness/SetRules` | the rules a derivation may use |
| Tian's factorization of c-factors and `tian_identifiable_sets` | `Identification/CFactor*` | the formula behind the `block` step |

The proof of `idCheck_iff` gives more than a yes or no. When the check says
yes, `IdentifyDerives` holds for every c-component of `An(Y)` in the graph
without the edges into `X`. That is the handle for completeness.

## Expression language

We propose a small first-order syntax with no binders for values. An expression
is read at one total assignment of all the variables, and a sum ranges over the
values of a set of variables. This avoids variable capture, and it keeps every
rule a statement about finite sets.

```lean
inductive Expr (V : Type*)
  | prob (Y Z X : Finset V)   -- P(Y | Z, do(X)), read at the current values
  | one                       -- the constant 1
  | mul (e₁ e₂ : Expr V)
  | div (e₁ e₂ : Expr V)
  | sum (S : Finset V) (e : Expr V)   -- sum over all values of S
```

- `Expr.query Y X` is `prob Y ∅ X`.
- `DoFree e` holds when every `prob` in `e` has `X = ∅`.
- `vars e` is the set of variables that occur in `e`. The goal asks for
  `vars e ⊆ Uᶜ`, so no latent variable appears.
- `free e` is the set of variables read from the assignment: `vars e` minus
  those bound by an enclosing `sum`.

Well-formedness: in `prob Y Z X`, the three sets are disjoint and `Y` is
nonempty. A rule may only produce well-formed expressions.

## Semantics

An expression evaluates, in a causal model `M` at a total assignment `σ`, to a
value in `ℝ≥0∞`. This is the same number type the project already uses for
`PMF`.

```
[[ P(Y | Z, do(X)) ]]_M(σ) = P^M_{do(X=σ_X)}(Y=σ_Y, Z=σ_Z) / P^M_{do(X=σ_X)}(Z=σ_Z)
[[ Σ_S e ]]_M(σ)           = Σ_{τ ∈ α^S} [[ e ]]_M(σ[S ↦ τ])
```

- The interventional probabilities are marginals of `doModel M X`, which
  already exists.
- `mul` and `div` are pointwise, and `one` is 1.
- Two expressions are equal in `M` when they agree at every `σ`.

Division is the only delicate point. We compare only models whose observed
marginal is positive everywhere, as `Identifiable` does. Then every denominator
a derivation produces is positive.

The reason: suppose `P(v) > 0` for every observed `v`. Then `P_x(w) > 0` for
every value `w` of the other observed variables. Some latent value makes the
full product positive, and the interventional product is that same term with
some factors dropped. This lemma is short and should come first, since every
soundness proof needs it.

## Derivations

`Derives G U e₁ e₂` is an inductive relation: an equational calculus with three
kinds of steps. This list is the most important choice in the note. If it is
too generous, completeness becomes trivial.

1. **Equality steps.** Reflexivity, symmetry and transitivity, and congruence
   under `mul`, `div` and `sum`.
2. **The three rules.** Each rewrites one `prob` term. It is allowed when its
   graphical condition holds in `G` (latents included), using the
   d-separation predicates the rules are already stated with.
    - Rule 1: `P(Y | Z, W, do(X)) = P(Y | Z, do(X))` when `Y ⊥ W | X, Z` in
      `G` without the edges into `X`.
    - Rule 2: `P(Y | Z, W, do(X)) = P(Y | W, do(X ∪ Z))` when `Y ⊥ Z | X, W`
      in `G` without the edges into `X` and out of `Z`.
    - Rule 3: `P(Y | W, do(X ∪ Z)) = P(Y | W, do(X))` when `Y ⊥ Z | X, W` in
      `G` without the edges into `X` and into `Z(W)`.
3. **Probability calculus.** A fixed finite list of steps that hold in every
   distribution and use no graph:
    - marginalization: `P(Y | Z, do X) = Σ_W P(Y ∪ W | Z, do X)`;
    - chain rule: `P(Y ∪ W | Z, do X) = P(Y | W ∪ Z, do X) · P(W | Z, do X)`;
    - the commutative semiring laws for `mul`, `one` and `sum`;
    - `e / e = one` and `(a · b) / b = a`;
    - pulling a factor out of a sum when the factor does not read the summed
      variables;
    - splitting a sum over a union of disjoint sets, and swapping the order of
      two sums.

    No renaming step is needed, because sums bind sets of variables, not names.

The word "fixed" matters. We do not allow "any identity that holds for all
distributions" as a single rule. That would hide real work inside one step, and
it is the kind of definition the 2026 paper on universal identifiability warns
against.

## Soundness

Soundness (`derives_sound`) should be the easy half. It is an induction on the
derivation with one case per rule. Each case is closed by a theorem the project
already has, or by a short lemma about sums in `ℝ≥0∞`.

- **Rules 1 to 3.** The existing theorems state the rules as products of
  marginals, without positivity. Dividing both sides by the positive
  denominator turns them into the conditional form above.
- **Probability calculus.** Marginalization and the chain rule are properties
  of one `PMF`, and the semiring laws hold in `ℝ≥0∞`. Division needs
  positivity, which the lemma in the semantics section supplies.
- **Consequence.** A derivation of `P(Y | do X) = e`, with `e` do-free over the
  observed variables, gives identifiability directly: two positive models with
  the same observed marginal give `e` the same value. So soundness and
  completeness together close the triangle in the goal.

## Completeness: proof strategy

We follow Huang and Valtorta. Identifiability gives a successful run of the
check, and each step of that run is replaced by a derivation. The semantic
proof `identifyDerives_sound` already exists, so the work is to make each of
its steps syntactic.

1. **From the hypothesis to a run.** `idCheck_iff` turns identifiability into
   `idCheck = true`. Write `D = An(Y)` in `G` without the edges into `X`. Its
   proof gives, for each c-component `Sᵢ` of `D`, a chain
   `IdentifyDerives G U T Sᵢ` that starts from a set whose c-factor is
   observational.
2. **The outer frame.** Write `Q[S] = P(S | do(O ∖ S))`.
    - Derive `P(Y | do X) = Σ_{D ∖ Y} P(D | do(O ∖ D))`. This uses rule 3,
      because the variables outside `D` are not ancestors of `Y`, and then
      marginalization.
    - Then derive `P(D | do(O ∖ D)) = ∏ᵢ Q[Sᵢ]`, the c-component
      factorization.
3. **Base case.** `Q[O] = P(O)` needs no step, because there is no `do`.
4. **The `anc` step.** `Q[T ∩ S] = Σ_{T ∖ S} Q[T]` when `T ∩ S` is ancestral
   in `T`. Rule 3 removes the intervention on the non-ancestors, and then
   marginalization finishes the step.
5. **The `block` step.** `Q[S] = ∏_{v ∈ S} Q[T_{≤v}] / Q[T_{<v}]` in a
   topological order of `T`. It uses three moves:
    - the chain rule;
    - rule 2, to turn conditioning on earlier variables into intervention;
    - rule 3, to drop interventions that do not matter.

    Huang and Valtorta give such rule 2 and rule 3 derivations in their
    Lemmas 1 and 2. These must be checked against the paper before phase 4.
    This is the main lemma of the project.
6. **Assembly.** Induction on `IdentifyDerives` composes the steps by
   transitivity, and the frame of step 2 puts the pieces together. The result
   mentions only observed variables and has no `do`.

Steps 2 and 5 need c-component factorization as a derivation, not only as an
equation between numbers. That is where most of the time will go.

## Decisions

Seven choices fix the statement before any Lean is written. Each has a
recommendation. The first decides what the theorem is worth. Decided on
25 November 2026: all seven recommendations are accepted.

| # | Question | Options | Recommendation |
| --- | --- | --- | --- |
| 1 | What counts as a probability manipulation? | (a) the fixed list in Derivations; (b) any identity valid in all distributions | (a), because (b) makes the theorem much weaker and close to trivial |
| 2 | Which models must a derivation be valid in? | (a) models with a positive observed marginal; (b) all models | (a): it is the same class as `Identifiable`, and division stays meaningful |
| 3 | Number type | `ℝ≥0∞` or `ℝ` | `ℝ≥0∞`, where the project's `PMF` lives |
| 4 | Conditioning in the syntax | with `Z` in `prob Y Z X`, or interventions only | with `Z`, because rule 2 cannot be stated without it |
| 5 | Which graph do the rule conditions use? | the DAG with latents, or its latent projection | the DAG with latents, where the rules are already proved |
| 6 | Scope | `P(Y \| do X)` only, or conditional effects (IDC) too | `P(Y \| do X)` first, then IDC as its own step |
| 7 | Form of the result | existence of a derivation (`Prop`), or a function that computes one | `Prop` first; a computable version can follow |

One question stays open until step 5 is tried in Lean: whether the fixed list
of probability steps is long enough. If a step is missing, we add it to the
list, as long as it holds in every distribution and uses no graph.

## Work plan and risks

The estimate is five to eight weeks of evening sessions with the agent on the
server. Each phase is a separate tag behind `scripts/check.sh`. The estimate is
rough, and phase 4 decides it.

1. **Syntax, semantics and positivity** (about 1 week): `Expr`, `eval`,
   well-formedness, and the lemma that a positive observed marginal makes every
   interventional marginal positive.
2. **Derivations and soundness** (1 to 2 weeks): `Derives` and
   `derives_sound`, with the rules taken from the existing theorems.
3. **Simple derivable steps** (about 1 week): marginalization over ancestral
   sets, and the `anc` step.
4. **The block step** (2 to 3 weeks): c-component factorization and Tian's
   formula as derivations, following Lemmas 1 and 2 of Huang and Valtorta.
5. **Assembly** (about 1 week): induction on `IdentifyDerives`, the outer
   frame, and `docalc_complete`.
6. **Audit and docs** (a few days): an addition to `AuditFinal`, the public
   statements, and the README.

| Risk | Effect | Mitigation |
| --- | --- | --- |
| The fixed list of probability steps is too short | phase 4 stalls | add steps that use no graph and hold in every distribution, and record each one in this note |
| Bookkeeping of sets of variables in sums | long proofs | keep sums over sets, never over names, and prove a few rewriting lemmas once |
| Arithmetic in `ℝ≥0∞` with division | many small side conditions | the positivity lemma from phase 1, applied everywhere |
| Pro usage limits | phases take more evenings | plan phase by phase, and push after every unit |

Progress:

- Phase 1: `DoCalc/Expr` (v4.222), `DoCalc/Positivity` (v4.223).
- Phase 2: laws of sums over sets of variables, `DoCalc/Sum` (v4.224).
- Phase 2: the derivations `Derives` and the safe divisors `Expr.Positive`,
  `DoCalc/Derives` (v4.225).
- Phase 2: rules 1–3 for expressions, from the existing rule theorems, `DoCalc/Rules`
  (v4.226).
- Phase 2: soundness of derivations, `derives_sound`, and `identifiable_of_derives`,
  `DoCalc/Soundness` (v4.227). Phase 2 is done.
- Phase 3: rule 3 for non-ancestors, `Derives.rule3_nonanc`, and small derived steps,
  `DoCalc/NonAncestors` (v4.228).
- Phase 3: the outer frame, `P(Y | do(X)) = Σ_{D ∖ Y} P(D | do(O ∖ D))` for an ancestral
  `D`, `Derives.query_ancestral`, `DoCalc/OuterFrame` (v4.229).
- Phase 3: the c-factor `qExpr U T` as an expression and the `anc` step,
  `Derives.anc_step`, `DoCalc/AncStep` (v4.230). Phase 3 is done.
- Phase 4: the route is Tian's recursion on a maximal vertex, rules 2 and 3; not yet
  compared line by line with Huang–Valtorta. Graph lemmas for a vertex `m` of maximal rank
  (not an ancestor in `G_{X̄}`; the d-separation for rule 2, `dsepSet_rule2_block`),
  `DoCalc/MaxVertexGraph` (v4.231).

## References

- Y. Huang and M. Valtorta, *Pearl's Calculus of Intervention Is Complete*,
  UAI 2006 (https://arxiv.org/abs/1206.6831). The route followed here.
- I. Shpitser and J. Pearl, *Complete Identification Methods for the Causal
  Hierarchy*, JMLR 9 (2008). Theorem 17 and the ID algorithm.
- I. Shpitser, *When does the ID algorithm fail?*, arXiv:2307.03750 (2023).
  Corrects the hedge criterion. Our results use hedges for `P(Y | do(X))`
  itself.
- *On the Incompleteness of do-calculus for Universal Identifiability*,
  arXiv:2611.08916 (2026). Explains why the definition of a derivation must be
  chosen with care.
- J. Tan and V. Syrgkanis, Causalean / CausalSmith
  (https://github.com/Jiyuan-Tan/CausalSmith). Their ID checker is proved
  sound only. Completeness and hedges are not formalized there, as of the
  public commit of 12 October 2026.
- PearlDoCalculus: `Hedge.idCheck_iff`, `Identification.CFactor.IdentifyDerives`,
  `identifyDerives_sound`.
