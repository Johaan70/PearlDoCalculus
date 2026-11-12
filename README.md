# PearlDoCalculus

Formal verification of causal inference in Pearl's framework, in Lean 4 on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** v4.8 — d-separation soundness and completeness (vertices and sets), each rule of the do-calculus as an exact equivalence (all three rules in full, for sets), the three rules of the do-calculus in Pearl's formulation without additional assumptions, and the back-door and front-door adjustment formulas under Pearl's criteria stated in terms of paths, machine-checked; and a first identification layer with latent variables (identifiability as a definition, back-door, front-door and fully observed models give identifiable effects, and the bow graph does not). No `sorry` in the project. Audit: see below.

---

## Main result

```lean
theorem WalkPath.dsep_sound_path (M : CausalModel G α) (Z : Finset V) (x y : V)
    (h : G.DSeparatedPath Z x y) : CondIndep M {x} {y} Z
```

For every `CausalModel` (finite vertex set, finite value types, kernels
P(v | pa(v)) as PMFs): if every *path* between `x` and `y` is blocked by `Z` in
Pearl's sense, then `x` and `y` are conditionally independent given `Z` in the
product-form sense of `CondIndep`. All assumptions are those built into
`CausalModel`; the theorem adds none. This is the classical soundness statement
for d-separation in discrete Bayesian networks, for single vertices `x`, `y`.

The set version:

```lean
theorem SetSound.dsep_sound_set (M : CausalModel G α) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : DSeparatedSet G Z X Y) : CondIndep M X Y Z
```

where `DSeparatedSet G Z X Y` means every pair `x ∈ X`, `y ∈ Y` is d-separated
by `Z` in the path-based sense. Pairwise conditional independence does not imply
set independence in general, so this is not a corollary of the vertex version;
it is proved through separation in the moral graph of An(X ∪ Y ∪ Z), with
Lauritzen's theorem and the separator partition generalised to sets
(`SetSound.lean`). `X ∩ Y = ∅` is not assumed: it follows from the hypothesis,
since a vertex is never d-separated from itself.

The proof goes through the walk-based formulation (`DSepSound.dsep_sound`) and
the equivalence

```lean
theorem DAG.dsepPath_iff_dsep : G.DSeparatedPath Z x y ↔ G.DSeparated Z x y
```

proved by loop erasure: from an open walk, jump to the last occurrence of the
head vertex, keep its incoming edge, and recurse on the shorter rest
(`exists_open_path`). Openness is preserved at every jump; the case where the
jump creates a new collider uses acyclicity (`descend_of_open`). The joint
distribution is proved equal to the classical Bayesian-network factorisation
(`fullJoint_apply_prod`).

```
'WalkPath.dsep_sound_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'DSepSound.dsep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Do-calculus

Interventions are modelled by `DoCalculus.doModel M X x`, a causal model on the
mutilated graph `cutIn G X` (Pearl's G_{X̄}) in which the vertices of `X` have
point masses at `x`. Its joint distribution is the truncated factorisation

```
P_x(u) = [u_X = x] · ∏_{v ∉ X} P(u_v | u_pa(v))        (doModel_fullJoint)
```

and two semantic checks confirm that it behaves as an intervention: the marginal
on `X` is a point mass at `x` (`doModel_marginal_self`), and `do(∅)` leaves the
model unchanged (`doModel_empty`).

All three rules are proved in product form, which avoids division and holds also
where the conditional probabilities are undefined.

| Rule | Theorem | Graphical condition |
|---|---|---|
| 1: insert/delete observation | `DoCalculus.rule1` | Y ⊥ Z \| X, W in G_{X̄} |
| 2: action/observation exchange | `DoCalculus.rule2` | Y ⊥ Z \| X, W in G_{X̄Z̲} |
| 3: insert/delete action | `Rule3Flag.rule3_general` | Y ⊥ Z \| X, W in G_{X̄, Z(W)‾} |

Rule 1 is d-separation soundness applied to the intervened model. Rule 2 is
proved without an augmented graph, through a *clamp model* on G_{Z̲}
(`clampModel`): every vertex keeps its kernel, but parents in `Z` are read from
`z₀`. It coincides with the observational model where `Z = z₀`, and with the
intervention off `Z` (the vertices of `Z` are sinks in G_{Z̲}), so d-separation
in the clamp model yields the rule. Rule 3 splits `Z` into the part `Z₁` that is
ancestral to `W` and the rest `Z₂ = Z(W)`: `do(Z₂)` is removed by ancestral
marginalisation, and `do(Z₁)` through a *flag model* (`Rule3Flag.flagModel`).
Pearl's augmented graph adds an intervention node `F_z → z` for each `z ∈ Z`;
since `F_z` has a single child, the flag is placed inside the value of `z`
instead, as `Option (α z)`, with `none` meaning "intervened to `z₀`". The flag
model lives on the original graph and contains both the observational and the
intervened distribution, so d-separation soundness applies to it directly and
yields rule 3 without any positivity assumption (`rule3_nocut`, `rule3_gen`).
`Z(W)` is taken in G_{X̄}, as in Pearl (`Z2_cutIn_eq`).

An earlier version (`Rule3.rule3`, tag `v2.0`) removed `do(Z₁)` with rule 2
instead, which required P_x(z₁, x, w) > 0. `Rule3Flag.rule3_general` supersedes
it; no rule carries a positivity assumption.

A semantic check shows that the condition of rule 2 does real work: for a hidden
confounder `Z ← U → Y`, the product identity fails
(`DoAudit.rule2_fails_with_confounder`). A positive check shows that the identity
is not vacuous: for `Z → Y` with `Y` a copy of `Z`, the condition holds and both
sides are non-zero (`DoAudit.rule2_holds_nontrivially`).

The identities in rules 2 and 3 hold for every assignment `t`. They are
informative when the `X`-part of `t` equals the intervention value `x`;
otherwise every marginal under `do(X = x)` is zero and both sides vanish.

---

## Adjustment formulas

The back-door and front-door formulas are derived for a general `CausalModel`
from the rules of the do-calculus (`Adjustment.lean`). Each comes in a product
form without positivity, and in Pearl's form with sums and divisions.

| Result | Theorem | Positivity |
|---|---|---|
| Back-door, product form | `backdoor_stratum` | none |
| Back-door, Pearl's formula | `backdoor_adjustment` | P(x, z) > 0 |
| Back-door, Pearl's path criterion | `backdoor_adjustment_criterion` | P(x, z) > 0 |
| Front-door, product form | `frontdoor_product` | none |
| Front-door, Pearl's formula | `frontdoor_adjustment` | P(x) > 0, P(z, x′) > 0 |
| Front-door, Pearl's path criterion | `frontdoor_adjustment_criterion` | P(x) > 0, P(z, x′) > 0 |

Back-door: P(y | do(x)) = Σ_z P(y, x, z) · P(z) / P(x, z). The product form
P(y, x, z) · P(z) = P_x(y, z) · P(x, z) follows from rule 2 and the fact that
an intervention on `X` leaves the marginal on the non-descendants `Z`
unchanged.

Front-door: P(y | do(x)) = Σ_z [P(z, x) / P(x)] · Σ_{x′} P(y, z, x′) · P(x′) / P(z, x′).
The derivation uses rule 2 twice, the commutation of interventions together
with rule 3, and the back-door formula with `X` as adjustment set; the product
form is P_x(y) · P(x) = Σ_z P_z(y) · P(z, x).

The positivity in Pearl's forms is the textbook one: it is needed for the
divisions to be defined. The hypotheses are d-separation conditions. For
back-door they are exactly those Pearl's derivation uses: no vertex of `Z` is a
descendant of `X`, and Y ⊥ X | Z in G_{X̲}. For front-door, the conditions of
steps 2 and 3 are taken with an empty conditioning set (Y ⊥ Z in G_{X̄Z̲} and
Y ⊥ X in G_{Z̄X̄}), where Pearl conditions on `X` and on `Z` respectively; this
is what the rules need when applied inside the intervened models. Under the
front-door criterion both versions hold. For back-door, the step from the criterion
stated in terms of paths is proved: `cutOut_dsep_of_backdoor` derives
Y ⊥ X | Z in G_{X̲} from Pearl's condition that `Z` blocks every path between
`X` and `Y` with an arrow into `X`, and `backdoor_adjustment_criterion` takes the
criterion itself (`BackdoorCriterion`) as hypothesis. The paths are traversed
from `y` to `x`, ending with an arrow into `x`. For front-door, `FrontdoorCriterion`
states Pearl's three conditions: (i) every directed path from `X` to `Y` meets
`Z`; (ii) every path between `X` and `Z` with an arrow into `X` is blocked by ∅;
(iii) every path between `Z` and `Y` with an arrow into `Z` is blocked by `X`.
The lemmas `fd_h1`–`fd_h4` and `fd_hdesc` derive all five hypotheses of
`frontdoor_adjustment` from it, and `frontdoor_adjustment_criterion` takes the
criterion itself as hypothesis. The key fact is that a path open given ∅ has no
colliders, so in the manipulated graphs it is a directed path, or two directed
paths from a common source, which the criterion rules out.

---

## Completeness of d-separation

`Completeness.dsep_complete`: if `x, y ∉ Z`, `x ≠ y`, and `x` and `y` are not
d-separated given `Z` in `G`, there is a causal model on `G` in which `x` and `y`
are not conditionally independent given `Z`. Together with `dsep_sound`,
d-separation is exactly the graphical criterion for conditional independence:
it holds in every causal model on `G` precisely when the vertices are
d-separated (Geiger, Verma and Pearl, 1990).

The proof is constructive and uses only zero/non-zero probabilities:

- **Chains.** An open walk yields sources `s₀, …, s_k ∉ Z` and vertices
  `z₁, …, z_k ∈ Z`: `s₀` reaches `x`, `s_k` reaches `y`, and both `s_{j−1}` and
  `s_j` reach a parent of `z_j`, all along directed paths avoiding `Z`. Each
  `z_j` is the first vertex of `Z` below a collider (`chain_of_open`). A chain of
  minimal length has distinct `z_j` (`chain_injective`).
- **The model.** Every vertex carries one bit per source. Outside `Z`, a vertex
  takes a fresh uniform bit in component `i` if it is `s_i`, and otherwise the OR
  of component `i` over its parents outside `Z`. The vertex `z_j` is the XOR of
  components `j − 1` and `j`; other vertices of `Z` are constantly `false`
  (`chainModel`).
- **Dependence.** Component `i` of a vertex outside `Z` equals the bit of `s_i`
  exactly when `s_i` reaches it (`chain_support`), so `z_j = b_{j−1} ⊕ b_j`
  (`chain_z`). Given `Z = 0` all bits are equal, so `x = 0` and `y` showing
  `b_k = 1` cannot occur together, while each is possible with `Z = 0` on its own
  (all bits 0, all bits 1). The product form of `CondIndep` fails
  (`chain_not_condIndep`).

Special cases proved along the way: a trek avoiding `Z` (`trek_not_condIndep`,
one source, vertices the OR of their parents), and marginal independence
(`dsep_complete_marginal`, `Z = ∅`, where every open walk is collider-free).

---

## D-separation as an exact criterion, and completeness of rules 1 and 2

`Completeness.dsepPath_iff`: for `x, y ∉ Z` with `x ≠ y`, `x` and `y` are
d-separated given `Z` (classical, path-based) if and only if they are
conditionally independent given `Z` in every causal model on `G`
(`dsep_iff` is the walk-based version). As a semantic check,
`collider_explaining_away` shows for `0 → 2 ← 1` that `0` and `1` are
independent in every model, but dependent given `2` in some model.

`Completeness.rule1_complete`: if `Y` and `Z` are not d-separated given `X ∪ W`
in G_{X̄}, there is a causal model on `G` and a value `x` such that
P_x(y | z, x, w) = P_x(y | x, w) fails. Together with `rule1`, the graphical
condition of rule 1 is exact. The proof lifts the chain model of
`dsep_complete` from G_{X̄} to `G` (`liftModel`): there the vertices of `X`
are constant, so the lifted model under do(X = false) is the chain model
itself (`doModel_lift`).

`Completeness.rule2_complete`: if `y` and `z` are not d-separated given `X ∪ W`
in G_{X̄Z̲}, there is a causal model on `G` and values `x`, `z₀`, `t` at which
the product form of `rule2` fails. The chain model on G_{X̄Z̲} is lifted to `G`
(`liftSub`). There no vertex reads `z`, so do(z) leaves every marginal without
`z` unchanged (`doModel_marginal_of_sub`), and the product form of rule 2
reduces to `CondIndep` in the chain model, which fails. Models on different
graphs are compared through their kernel factors (`marginal_eq_of_kfac`), which
avoids any transport between graphs.

`Completeness.rule3_complete_nonanc`: if `z` is not an ancestor of `W` in
G_{X̄} and the condition of `rule3_general` fails, there is a causal model on
`G` and values at which the product form of rule 3 fails. Here Z(W) = {z}, so
the chain model lives on G_{X̄z̄}, where `z` is a root. For a root, setting `z`
equals conditioning on `z`: P(s, z) = P_z(s) · P(z), which is `frontdoor_step1`
with X := {z} (`z` is isolated in that graph with its out-edges removed). Rule 3
then implies `CondIndep` in the chain model, which fails. No positivity is used.

**The rules as equivalences.** `rule1_iff`, `rule2_iff` and `rule3_iff_nonanc`
state each rule as one equivalence: the graphical condition holds if and only if
the rule holds in every causal model on `G`. With the semi-graphoid
decomposition property (`condIndep_single`: X ⊥ Y | Z gives x ⊥ y | Z for
x ∈ X, y ∈ Y, proved by summing out with `marginal_sum_Z`), the same holds for
sets: `dsepSet_iff` for d-separation of sets, and `rule1_iff_set` for rule 1 in
exactly the form `rule1` is stated. The same holds for rule 2 with sets
(`rule2_iff_set`): in the chain model on G_{X̄Z̲} no vertex reads any vertex of
`Z`, so do(Z) leaves every marginal outside `Z` unchanged. For rule 3 with sets
(`rule3_iff_set_nonanc`), when no vertex of `Z` is an ancestor of `W`, all of `Z`
are roots in G_{X̄Z̄}, and `frontdoor_step1` with X := Z gives
P(s, z) = P_z(s) · P(z) for the whole of `Z` at once.

The same argument shows more (`rule3_complete_root`, `rule3_complete_set_root`):
whenever `Y` and `Z` are d-connected given `X ∪ W` in G_{X̄Z̄}, rule 3 fails in
some model, also when vertices of `Z` are ancestors of `W`. The ancestor
assumption above is only needed to make G_{X̄Z̄} the graph of rule 3.

A second model reaches most of the rest (`rule3_complete_copy`): if some
`s ∉ X ∪ W` has directed paths to `y` and to `z` avoiding `X ∪ W` in G_{X̄},
`z` reaches a parent of some `w₁ ∈ W` the same way, and `z` does not reach `y`,
then rule 3 fails. In the model `s` is a fair bit, every vertex outside `X ∪ W`
and `w₁` is the OR of its parents outside `X ∪ W`, and the rest of `X ∪ W` is
`false`. Observing `w₁ = 1` forces the bit to 1 and hence `y = 1`; setting
do(z = 1) makes `w₁ = 1` possible with `y = 0`.

Combining the two models closes rule 3 for single vertices (`rule3_complete`,
`rule3_iff`). In the remaining case `y` and `z` are d-connected in G_{X̄} but
d-separated in G_{X̄z̄}. Take a chain from `y` to `z` with fewest colliders and
the first vertex `w₁ ∈ W` that `z` reaches. If `w₁` were a collider of the
chain, cutting the chain there and ending it at `z` would give a chain in
G_{X̄z̄}, which is impossible. So `w₁` is not a collider, and the chain model
with `w₁` copying the last component (`rule3_complete_chaincopy`) breaks
rule 3: observing `w₁ = 1` with all colliders 0 forces every bit to 1 and
hence `y ≠ 0`, while under do(z = 1) all bits can be 0.

The same model gives rule 3 for sets (`rule3_complete_set`, `rule3_iff_set`).
Take a chain with fewest colliders over all pairs `y ∈ Y`, `z ∈ Z` in
G_{X̄Z(W)̄}, and let `z` be the vertex of `Z` of highest rank reached by its last
source. Then `z` reaches no other vertex of `Z`, and `z` is an ancestor of `W`
(otherwise the chain would survive in G_{X̄Z̄}). do(Z) sets `z` to 1 and the rest
of `Z` to 0 (`rule3_complete_chaincopy_set`, `set_gap_core`).

---

## Identification with latent variables

`Identification.Identifiable G α O X Y` says that `P(Y | do(X))` is determined by
the distribution on the observed vertices `O`: any two models on `G` whose
distributions on `O` agree and are positive give the same interventional
distribution on `Y` (the definition of Pearl and Shpitser–Pearl, with positivity).

- `backdoor_identifiable`, `frontdoor_identifiable`: if `X`, `Y` and `Z` are
  observed and `Z` satisfies the back-door (front-door) criterion, the effect is
  identifiable, whatever else is latent.
- `observed_identifiable`: with every vertex observed, every effect is
  identifiable (truncated factorization). `kfac_eq_of_joint` recovers each kernel
  as P(v, ancestors) / P(ancestors) from `marginal_ancestral_apply`.
- `Identifiable.mono`: observing more never hurts.
- `Parents.parents_identifiable`: if `x` and all parents of `x` are observed,
  `P(Y | do(x))` is identifiable for every observed `Y` that contains neither
  `x` nor a parent of `x`, whatever else is latent (Tian's case where the
  c-component of `x` is `{x}`). The parents always satisfy the back-door
  criterion: a path ending in an arrow into `x` has a parent as its last
  interior vertex, and that vertex is a non-collider (`Parents.ends_blocked`).
- `Bow.bow_not_identifiable`: for `U → X`, `U → Y`, `X → Y` with `U` latent,
  `P(Y | do(X))` is not identifiable from `{X, Y}`. Two models with the same
  positive `P(X, Y)`: in one `Y` copies `U`, in the other `Y` is a noisy copy of
  `X`. Their joints agree after a bijection that only changes `U`; rule 3 (B2)
  and FD1 then show that `P(Y | do(X))` differs (3/4 against 1/4).
- `BowGen.bow_not_identifiable_general`: the same holds inside any graph. If
  `u → x`, `u → y` and `x → y` are edges of `G`, `u ∉ O` and `x, y ∈ O`, then
  `P(y | do(x))` is not identifiable from `O`. Both models use only those
  three edges and make every other vertex independent uniform noise, so the
  joints again agree after a bijection that only changes `u`.
- `Hedge2.hedge2_not_identifiable`: a hedge with two latent variables. If `G`
  has edges `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y`, `w → y`, `x → y`, with
  `u₁, u₂` latent and `x, y` observed, `P(y | do(x))` is not identifiable,
  whether or not `w` is observed (`F = {x, w, y}`, `F' = {w, y}`). Model A sets
  `w = u₁ xor u₂`, `y = w xor u₂` (so `y = u₁`, unaffected by `x`); model B sets
  `u₁ = u₂ = 0` and makes `y` a noisy copy of `x`. The bijection
  `u₁ ↦ u₁ xor y`, `u₂ ↦ u₂ xor (w xor y)` carries one joint to the other.
  If `w` were not an ancestor of `y`, the effect would be `P(y | x)`.
- `HedgeChain.chain_not_identifiable`: hedge chains of any length. For
  `x ↔ w₀ ↔ … ↔ w_n ↔ y` through latent `u₀, …, u_{n+1}`, with `w_i → w_{i+1}`,
  `w_n → y` and `x → y`, `P(y | do(x))` is not identifiable, whether or not the
  `w_i` are observed. Model A propagates `u₀` along the chain by xor
  (`w_i = u₀ xor u_{i+1}`, `y = u₀`); the two systems of equations are shown
  equivalent by induction along the chain (`condA_iff`), and the products are
  compared after splitting the vertex set (`prod_split`).
- `HedgeTmpl.Tm.not_ident`: a reusable template. Any configuration where model A
  makes `x` a noisy copy of a function `fx` of its latent parents, makes each `w_i` and `y` a deterministic
  function of its parents in a subgraph, and whose equations are equivalent to
  `u_j = off_j(w, y)` with `fx = y` on solutions, gives a non-identifiable effect. Only
  the equivalence (`key`) has to be proved for each new hedge shape.
- `PathTree.pathTree_not_identifiable`: a latent path
  `x ↔ w₀ ↔ … ↔ w_n ↔ y` whose directed edges form any tree towards `y` (each
  `w_j` points to one `w_i` or to `y`; chains and stars are special cases).
  Model A is the parity model of Shpitser and Pearl, computed in `ZMod 2`: `y`
  sums all latent contributions, every inner `u` counts twice, so `y = u₀`
  (`sum_zero` is the double-counting step).
- `LatentTree.latentTree_not_identifiable`: the latent connections may form any
  tree over `x` and the observed vertices (`x` may have several latent
  neighbours; it is then a noisy copy of their xor), and the directed edges any
  tree towards `y`. The equations are solved bottom-up in the latent tree
  (`solN`, with a height function so that children lie lower; uniqueness by
  induction on height), and `fx = y` follows from double counting over both
  trees (`dc`).
  The models use only the edges of the chosen trees; all other vertices are
  independent uniform noise in both models. A latent component with cycles is
  therefore covered by choosing a spanning tree, and extra directed edges are
  harmless.
- `Identifiable.mono_Y` and `not_identifiable_of_mem`: identifiability passes to
  subsets of `Y` (marginalisation), so non-identifiability for one `y` gives it
  for every `Y ∋ y` disjoint from `X` (`latentTree_not_identifiable_set`).

Not covered: the general hedge criterion (c-forests with several roots, sets `X`), c-component
factorization, the ID algorithm, and completeness of the do-calculus for
identification. CausalSmith/Causalean (see Related work) has soundness of the
ID algorithm in a measure-theoretic setting.

---

## Audit status

The build log establishes that `dsep_sound` has no hidden `sorry`. Whether the
formal statement matches the classical one is a separate question, audited here.

Checked:
- `fullJoint` equals the product of kernels over all vertices (`fullJoint_apply_prod`).
- `marginal` is the pushforward along restriction (summing out).
- `CondIndep` is the product form P(x,y,z)·P(z) = P(x,z)·P(y,z), equivalent to
  the conditional form wherever P(z) > 0.
- Blocking follows Pearl's criterion: non-colliders block when in `Z`; colliders
  block when no descendant-or-self is in `Z` (`Reaches` is reflexive-transitive).
- The hypothesis is non-vacuous: `DSeparated ∅ 0 1` is proved for the collider
  `0 → 2 ← 1` (`Counterexample.lean`); adjacent vertices are never d-separated.
- Clean build of tag `v1.0` from a fresh clone; signature, definitions and axioms
  archived in `verification/audit_v1_output.txt`. No kernel-bypassing constructs
  (`axiom`, `unsafe`, `implemented_by`, `native_decide`, `skipKernelTC`) in the sources.
- `CondIndep` can fail: `Audit.not_condIndep_dep` for `x → y` with non-degenerate
  uniform kernels, where P(x=1, y=0) = 0 but P(x=1) > 0 and P(y=0) > 0.
- Regression suite for d-separation semantics (`Audit.lean`), all mechanisms in
  both directions: chain `0 → 1 → 2` open given `∅`, blocked given `{1}` (the
  latter over all walks, including those that bounce through the open collider
  formed at `1`); collider `0 → 2 ← 1` blocked given `∅`, opened given `{2}`.
- Walk-based and path-based d-separation are equivalent (`dsepPath_iff_dsep`,
  `WalkPath.lean`), so the walk formulation is a faithful implementation of
  Pearl's path criterion. Tag `v1.0` states the walk-based theorem; `v1.1` adds
  the equivalence and the classical `dsep_sound_path`.
- Set version (`SetSound.dsep_sound_set`): five of the seven links in the proof
  chain were already stated for sets; Lauritzen's theorem (via Bayes-Ball from
  any `x ∈ X`) and the separator partition were generalised. Tag `v1.2`.
- Do-calculus semantics: the intervened model sets `X` (`doModel_marginal_self`),
  `do(∅)` is the identity (`doModel_empty`), and rule 2 fails without its
  condition in a confounded model (`DoAudit.rule2_fails_with_confounder`).
  Tag `v2.0`.
- Rule 2 holds non-trivially: for `Z → Y` with `Y` a copy of `Z`, the condition
  holds and both sides of the identity are non-zero
  (`DoAudit.rule2_holds_nontrivially`).
- Clean build of tag `v2.0` from a fresh clone; signatures, definitions and axioms
  archived in `verification/audit_v2_output.txt`. `cutIn` removes edges into `X`,
  `cutOut` removes edges out of `X`, and `Z2` is Pearl's `Z(W)`; no hidden
  hypotheses beyond disjointness, the graphical condition, and (rule 3) positivity.
- Rule 3 without positivity (`Rule3Flag.rule3_general`, tag `v2.1`). The flag
  model's joint distribution equals (½)^|Z| · P on observations and
  (½)^|Z| · P_{z₀} on interventions (`flag_fullJoint_obs`, `flag_fullJoint_int`),
  and its marginals are related to those of P and P_{z₀} by explicit reindexing
  (`flag_marginal_obs`, `flag_marginal_int`, `flag_marginal_zero`).
- Back-door and front-door formulas for a general `CausalModel`, in product form
  and in Pearl's form (`Adjustment.lean`, tag `v2.2`).
- Clean build of tag `v2.2` from a fresh clone; signatures, the flag model and
  axioms archived in `verification/audit_v22_output.txt`. `rule3_general` has no
  positivity hypothesis; the adjustment formulas carry only the textbook one.
- Back-door in a confounded graph `Z → X, Z → Y, X → Y`: both hypotheses hold,
  and the identity of `backdoor_stratum` has non-zero sides
  (`AdjAudit.backdoor_holds_nontrivially`).
- Back-door criterion in path form (`BackdoorCriterion`,
  `cutOut_dsep_of_backdoor`, `backdoor_adjustment_criterion`, tag `v2.3`): a
  path in G_{X̲} is a path in G ending with an arrow into `X`, and blocking
  survives the removal of edges.
- Front-door criterion in path form (`FrontdoorCriterion`, `fd_h1`–`fd_h4`,
  `fd_hdesc`, `frontdoor_adjustment_criterion`, tag `v2.4`).
- Completeness of d-separation (`Completeness.dsep_complete`, tag `v3.0`): from
  an open walk to a chain of sources and vertices of `Z`, a chain of minimal
  length, and a model with one bit per source in which the product form of
  `CondIndep` fails.
- `dsep_iff` / `dsepPath_iff`, `collider_explaining_away`, and completeness of
  rule 1 (`rule1_complete`, tag `v3.1`).
- Completeness of rule 2 (`rule2_complete`, tag `v3.2`).
- Completeness of rule 3 when `z` is not an ancestor of `W`
  (`rule3_complete_nonanc`, tag `v3.3`).
- The rules as equivalences (`rule1_iff`, `rule2_iff`, `rule3_iff_nonanc`),
  decomposition (`condIndep_single`), and the set versions `dsepSet_iff` and
  `rule1_iff_set` (tag `v3.4`).
- Rules 2 and 3 with sets (`rule2_iff_set`, `rule3_iff_set_nonanc`, tag `v3.5`).
- Rule 3 fails whenever `Y` and `Z` are d-connected in G_{X̄Z̄}
  (`rule3_complete_root`, `rule3_complete_set_root`, tag `v3.6`).
- Rule 3 fails at a trek through `z` into `W` (`rule3_complete_copy`, tag `v3.7`).
- Rule 3 exact for single vertices (`rule3_complete`, `rule3_iff`, tag `v3.8`).
- Rule 3 exact for sets (`rule3_complete_set`, `rule3_iff_set`, tag `v3.9`).
- Identification layer (`Identification.lean`, tag `v4.0`).
- Bow inside any graph (`bow_not_identifiable_general`, tag `v4.1`).
- Unconfounded treatment (`parents_identifiable`, tag `v4.2`).
- Two-latent hedge (`hedge2_not_identifiable`, tag `v4.3`).
- Hedge chains of any length (`chain_not_identifiable`, tag `v4.4`).
- Hedge template and latent paths with a directed tree (`pathTree_not_identifiable`, tag `v4.5`).
- Latent trees (`latentTree_not_identifiable`, tag `v4.6`).
- Latent trees where `x` need not be a leaf (tag `v4.7`).
- From one `y` to sets `Y` (`not_identifiable_of_mem`, tag `v4.8`).

Open:
- None within the scope stated above; see Scope for what lies beyond it.

---

## Proof architecture

1. **Graph side (Lauritzen).** D-separation implies separation in the moral graph
   of the ancestral set of `{x, y} ∪ Z` — `Lauritzen.moral_sep_of_dsep_lauritzen`,
   proved via the Bayes-Ball algorithm (`BayesBall.lean`).
2. **Separator partition.** `separator_partition` splits the ancestral set into
   two sides separated by `Z`.
3. **Ancestral marginalisation.** `marginal_eq_restricted_joint`: the marginal on
   an ancestrally closed set equals the marginal of the restricted model. Proved
   via an explicit product form of the joint (`kfac`, `jointUpTo_apply_prod`,
   `fullJoint_apply_prod`) and a normalisation argument through an auxiliary model
   with pinned kernels (`pinTo`, `sum_compl_kfac_eq_one`).
4. **Factorisation.** `joint_splits`, `product_form_mono`.
5. **Conditional independence.** `condIndep_of_product_form`, `condIndep_transfer`.

---

## Negative results

The naive graph-side statement — d-separation implies separation in the moral
graph of the *whole* DAG — is false. `Counterexample.lean` gives an explicit
counterexample (`moral_sep_of_dsep_counterexample`). The correct statement
restricts to the ancestral set, as in step 1 above. An auxiliary converse
(`open_walk_of_moral`) was likewise shown false and removed.

---

## Other verified results

- **Adjustment:** `backdoor_general`; front-door: `frontdoor_structural`,
  `frontdoor_X_cancellation`, `frontdoor_adjustment_observable`.
- **Graph-to-distribution bridge:** `moral_walk_of_open`, `dsep_of_moral_sep`.
- **Bayes-Ball:** `bbReachable_imp_open_walk`, `DSeparated_imp_not_bbReachable`.

---

## Scope

Not yet covered: the ID algorithm, the hedge criterion beyond the bow graph,
and completeness of the do-calculus for identification (Shpitser–Pearl,
Huang–Valtorta).

---

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned in `lake-manifest.json`).

---

## Related work

- **CausalSmith / Causalean** (github.com/Jiyuan-Tan/CausalSmith; Tan &
  Syrgkanis, arXiv:2607.22511) — a much larger library on measure-theoretic
  structural causal models: global Markov property (`full_globalMarkov`,
  corresponding to `dsep_sound` here), rule 1, restricted forms of rules 2 and
  3 (its own documentation states that Pearl's full rule 3 premise is not
  formalised), back-door and front-door identification almost everywhere
  under positivity, and soundness of the ID algorithm. As of its commit
  `1769741` (2026-09-21), a text search did not find completeness of
  d-separation, completeness of individual do-calculus rules, or the
  back-door/front-door criteria stated in terms of paths. This comparison is
  based on searching source and documentation, not on building that project.
- **Statlib** — ongoing discussion at leanprover.zulipchat.com (#Statlib) of a
  unified Lean library for causal inference and potential outcomes.
