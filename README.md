# PearlDoCalculus

Formal verification of causal inference in Pearl's framework, in Lean 4 on Mathlib.

**License:** Apache 2.0  
**Author:** Johan Magnus Aanderaa  
**Status:** v4.31 — d-separation soundness and completeness (vertices and sets), each rule of the do-calculus as an exact equivalence (all three rules in full, for sets), the three rules of the do-calculus in Pearl's formulation without additional assumptions, and the back-door and front-door adjustment formulas under Pearl's criteria stated in terms of paths, machine-checked; and an identification layer with latent variables (identifiability as a definition; back-door, front-door and fully observed models give identifiable effects; hedge families are not identifiable; c-component factorization, Tian's identification theorem with an explicit formula, and the exact dividing line for a single intervention `x`, `tian_iff`). No `sorry` in the project. Audit: see below.

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
- `HedgeTmpl.Tm.not_ident_X`: sets `X`. If `X` contains `x` and otherwise only
  vertices outside the hedge, `P(y | do(X))` is still not identifiable. In model A
  rule 3 (B2) applies directly; in model B, `do(X)` is rewritten as
  `do(X ∖ {x})` after `do(x)` by comparing kernel factors, and B2 is applied to
  the inner model. Combined: `latentTree_not_identifiable_XY`.
- `TwoRoot.twoRoot_not_identifiable`: the smallest c-forest with two roots.
  With `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y`, `x → y`, the effect `P(y | do(x))`
  alone is identifiable (`w` is a collider on the only back-door path), but
  `P(y, w | do(x))` is not. Model B must itself use a latent variable
  (`w = u₂`, `y = chan(x) xor u₂`); with only the edge `x → y` it would be
  impossible. The observed marginals are computed through a third model C with
  the same joint distribution as A, on a graph where `{y, w, x}` is ancestral,
  so no sums over latent variables are needed.
- `MultiRoot.multiRoot_not_identifiable`: c-forests with arbitrarily many roots.
  A latent tree binds `x` (through `u₀`) to the nodes `nd₀, …, nd_{n+1}`, the
  nodes form a directed forest (each node points to a parent or is a root), and
  `x → nd₀` with `nd₀` a root. With the roots and `x` observed and the latents
  not, `P(roots | do(x))` is not identifiable. Model B drops `u₀ → x` and makes
  `nd₀` a noisy copy of `x xor` parity; the bijection changes only `u₀` (to
  `u₀ xor Σ roots`), and a residual identity over all nodes shows the joint
  distributions agree. Model C (uniform nodes, `x = chan(Σ roots)`, latents as
  functions of the nodes) makes the roots and `x` ancestral.
  Since v4.14 the theorem is derived from `RootPath` below (`multiRoot_of_rootPath`),
  and its separate proof is gone.
- `RootPath.rootPath_not_identifiable`: as above, but `x` may point into any
  root `nd_r`. A path of latents from `u₀` to `u_r` is given by the parity
  condition `pth k + #{children of k on the path} = [k = r]` (mod 2); the
  bijection shifts the whole path by `Σ roots`, which changes the parity only at
  `nd_r`, and model B puts its noisy channel there. `multiRoot_of_rootPath`
  recovers the previous theorem as the case `r = 0`, path `{u₀}`.
- `RootTree.rootTree_not_identifiable`: the same without the path hypothesis.
  The path is constructed as the chain `r, bp r, bp (bp r), …`; height grows
  strictly along it, so it never repeats a node and ends at `0`, and the parity
  condition becomes a count (one child on the chain for chain nodes other than
  `r`, none otherwise).
- `RootTree.embedded_not_identifiable`: the structure only has to sit *inside*
  `G` (extra edges, latents and nodes are ignored by the kernels), and `Y` may be
  any superset of the roots disjoint from `x` (via `Identifiable.mono_Y`). This
  covers `x` with several latent neighbours: if `x` is interior to the latent
  tree, `F ∖ {x}` is disconnected, so `(F, F ∖ {x})` is not a hedge; the right
  hedge is the branch containing `nd_r`, with `x` as a leaf. Cycles among the
  latents are handled the same way (a spanning tree with `x` as a leaf).
- `Channel.channel_step`: Shpitser–Pearl only require the roots of a hedge to be
  *ancestors* of `Y`. This step moves a non-identifiable effect one edge down: if
  the effect on `Y ∋ ρ` is not identifiable in a subgraph `G'` where `y` is
  isolated, and `ρ → y` is an edge of `G`, then the effect on `Y ∖ {ρ} ∪ {y}` is
  not identifiable in `G`, with `y` observed. The models keep their kernels and
  `y` becomes a noisy channel `chan(ρ)`; since nothing reads `y`, the joint is the
  old marginal extended by the channel (`joint_ins`, `marg_ins`), and the channel
  is invertible (a 2 × 2 system with determinant 1/2, `Φ_inj`), so equal answers
  after the step would give equal answers before it. The step works for any
  non-identifiable effect, not only the hedge families above, and can be repeated
  along a directed path.
- `Channel.path_not_identifiable`: the step repeated along a whole directed path
  `ρ → p₁ → … → p_m`, by induction over the path. If the effect on `Y ∋ ρ` is not
  identifiable in the graph where the path vertices are isolated (`isoSet`), then
  the effect on `Y ∖ {ρ} ∪ {p_m}` is not identifiable in `G`, with the path
  observed. `not_ident_of_sub` (extra edges never make an effect identifiable)
  lifts the base case. `rootTree_tail` combines this with `RootTree`: a hedge plus
  a tail from one of its roots. Disjoint tails from several roots follow by
  applying the theorem once per tail.
- `CFactor.marginal_factor` (c-component factorization, Tian's Lemma 1): let `U` be
  the latent vertices and `S` a block that no latent edge crosses. Then
  `P(Uᶜ = a) = Q[S](a) · Q[Sᶜ](a)`, where `Q[T](a)` sums, over the latents in `T`,
  the product of the kernels of the vertices in `T`. Latents need not be roots.
  `CFactor.do_marginal_factor`: an intervention on `X ⊆ S` changes only `Q[S]`;
  `Q[Sᶜ]` is the factor of the unintervened model. First step of the positive side.
- `CFactor.Q_identifiable` (Tian's Lemma 2): two models with the same positive
  distribution on the observed vertices have the same `Q[S]` and `Q[Sᶜ]`. Proved by
  induction over ancestral sets: `anc_factor` gives `P(O ∩ A) = Q[A ∩ S] · Q[A ∩ Sᶜ]`,
  and `Q_step` is the explicit recursion `Q[A ∩ S] = Q[A' ∩ S] · P(O ∩ A) / P(O ∩ A')`
  for `A' = A ∖ {v}`, `v` without children in `A` (written without division).
- `CFactor.tian_identifiable` (Tian's identification theorem): if `x` is observed and
  its closed block `S` contains no child of `x`, then `P(Y | do(x))` is identifiable
  for every observed `Y`, with `tian_formula`:
  `P_x(a) = [a_x = x] · (Σ_{x'} Q[S](a[x := x'])) · Q[Sᶜ](a)`.
  Latents need not be roots. The hedges above are the other side of this line.
- `CFactor.ccomp_isLeast`: the c-component of `x` (`ccomp`, every vertex reachable from
  `x` by edges with a latent tail, in either direction) is the least closed block
  containing `x`. Hence Tian's condition is a condition on the c-component
  (`tian_cond_iff`), and `tian_identifiable_ccomp` states the theorem in that form:
  no child of `x` in the c-component of `x` ⇒ `P(Y | do(x))` identifiable.
- `CFactor.tian_iff` (the dividing line for a single `x`): with latents as roots and
  Bool-valued variables, `P(O ∖ {x} | do(x))` is identifiable if and only if no child
  of `x` lies in the c-component of `x`. The hard direction `not_ident_of_child` takes
  a shortest chain of latent steps from `x` to a child of `x` (no repeated vertices,
  `chain_cut`), shows that it alternates observed/latent (`chain_parity`), and builds
  from it either the bow or an `RT` structure for `embedded_not_identifiable`.
- `CFactor.tian_identifiableX` (Tian's theorem for a set `X`): if `X ⊆ S` is observed,
  `S` a closed block and no vertex of `X` has a child in `S`, then `P(Y | do(X))` is
  identifiable. Since v4.23 a corollary of `tian_identifiable_sets` below, as is
  `tian_identifiable_ccompX` (`S` = the union of the c-components of `X`).
- `CFactor.marginal_prod` (factorization over many blocks, line 4 of the ID algorithm):
  for pairwise disjoint closed blocks covering all vertices, `P(O) = ∏ᵢ Q[Bᵢ]`
  (`Q_split`, `Q_prod`).
- `CFactor.tian_identifiable_sets`: one sum per c-component,
  `P_X(a) = ∏ᵢ [a_{X∩Bᵢ} = x] · Σ_{x'} Q[Bᵢ](a[X ∩ Bᵢ := x'])` (`tian_formula_blocks`).
  The effect of `X` is identifiable if no `x ∈ X` has a child in its *own*
  c-component (children in other components are allowed). For a single `x` this is
  exactly the condition of `tian_iff`.
- `CFactor.Q_causal` (each factor is a causal effect): fixing all observed vertices
  outside a closed block `S` gives `P_{do(X = x)}(O = a) = [a_X = x] · Q[S](a)`. Uses
  `lat_one`: the kernels of any set of latents sum to 1 (from `sum_compl_kfac_eq_one`).
- `CFactor.Q_marg` (Tian's lemma on marginalising factors, the base of the recursive
  part of ID): if `S` is ancestral inside `T` and `T` contains its latent parents,
  summing `Q[T]` over the observed vertices of `T ∖ S` gives `Q[T ∩ S]`. The
  statement follows Tian & Pearl (2002) and Causalean's `q_factor_marginal_fixing`;
  the proof here is independent and elementary (no sub-model, no rule 3).
- `CFactor.Q_ident_within` (Tian's lemma 11, lemma 2 inside a factor): two models
  with equal positive `Q[T]` have equal `Q[T ∩ S]` and `Q[T ∩ Sᶜ]` for every block
  `S` closed inside `T`. Same induction as `Q_identifiable`, with `Q_marg` in place
  of the marginal; uses `Q_split_rel`, `Q_le_one` (`Q[T] ≤ 1`) and `Q_marg_ne_zero`.
- `CFactor.Reach` (Tian's IDENTIFY as an inductive predicate): `C` is reachable from
  `T` by marginalising to a part ancestral inside `T` or moving to a block closed
  inside `T`. The shape follows Causalean's `CFactorReachableRec`; the proof is ours.
  `reach_sound`: equal positive factors on `T` give equal positive factors on `C`;
  `reach_ident`: if `C` is reachable from `V`, `Q[C]` is determined by `P(O)`.
- `CFactor.id_sound` (soundness of the ID algorithm for sets, lines 4, 6, 7): if every
  c-component of `G_{X̄}` with an observed vertex outside `X` is reachable from `V`,
  `P(Y | do(X))` is identifiable. Via `marginal_prod` on the intervened model,
  `Q_do_gen` and `reach_ident`; `id_sound_blocks` is the version for arbitrary blocks.
  Line 2 (restricting to the ancestors of `Y`) is not included here.
- `CFactor.id_sound_anc` (lines 2, 4, 6, 7, in Tian & Pearl's form): for `S ⊇ Y`
  ancestral in `G_{X̄}` (e.g. `An(Y)`), if every c-component of `G_{X̄}[S]` with an
  observed vertex outside `X` is reachable from `V`, `P(Y | do(X))` is identifiable.
  New: `Q_prod_rel` (blocks closed only inside `S`) and a recounting lemma
  (`tsum_updX`, `fiber_eq`): equal sums over the fibres `{a[D := x']}` give equal
  marginals on every `Y` outside `D`.
- `IdAudit` (test case): in `x ↔ b ↔ y`, `x → y` the hypothesis of
  `tian_identifiable_sets` fails (`tian_sets_fails`), but `P(y | do(x))` is
  identifiable by `id_sound_anc_blocks` (`id_audit`); the recursion first sums out
  `b` and then separates `{u₂, y}` from `{u₁, x}` (`reach_y`).
- Verma constraints. `CFactor.Q_local`: `Q[T]` depends only on the observed values in
  `T` and at the parents of `T`; `CFactor.verma_sum`: for `S` ancestral inside `T`, the
  sum of `Q[T]` over the observed vertices of `T ∖ S` depends only on `T ∩ S` and its
  parents. `Verma.verma_constraint` (the classical example `a → b → c → d`, `b ↔ d`):
  for every model with positive `P` and any value types,
  `Σ_b P(a,b,c,d) P(a,b) / (P(a,b,c) P(a))` does not depend on `a`
  (`verma_identify`, `vermaF_eq_Q`). That no conditional independence implies this is
  Verma & Pearl's observation and is not proved here.

Not covered: the general hedge criterion (tails from several roots that merge before reaching `Y`; `X` meeting the hedge in more than `x`),
hence completeness of the ID algorithm for sets, and completeness of the do-calculus for
identification. The positive side of ID (rounds 30–35) is stated with the recursion as
a predicate (`Reach`), not as an executable algorithm returning a formula. CausalSmith/
Causalean (see Related work) has soundness of the full recursive ID algorithm in a
measure-theoretic setting; what it does not have is the hedge side.

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
- Sets `X` (`not_ident_X`, `latentTree_not_identifiable_XY`, tag `v4.9`).
- Two-root c-forest (`twoRoot_not_identifiable`, tag `v4.10`).
- Multi-root c-forests (`multiRoot_not_identifiable`, tag `v4.11`).
- `x` into any root along a latent path (`rootPath_not_identifiable`, tag `v4.12`).
- Path constructed, no hypothesis (`rootTree_not_identifiable`, tag `v4.13`).
- Embedded hedges, any `Y ⊇` roots (`embedded_not_identifiable`); round 14 derived
  from round 15, about 880 lines removed; channel step for roots that are only
  ancestors of `Y` (`channel_step`, tag `v4.14`).
- Whole paths (`path_not_identifiable`, `rootTree_tail`, `not_ident_of_sub`, tag `v4.15`).
- C-component factorization and its do-version (`marginal_factor`,
  `do_marginal_factor`, tag `v4.16`).
- Tian's Lemma 2 and identification theorem (`Q_identifiable`, `Q_step`,
  `tian_formula`, `tian_identifiable`, tag `v4.17`).
- C-component as the least closed block (`ccomp_isLeast`, `tian_cond_iff`,
  `tian_identifiable_ccomp`, tag `v4.18`).
- The dividing line for a single `x` as one theorem (`tian_iff`,
  `not_ident_of_child`, tag `v4.19`).
- Tian's theorem for a set `X` (`tian_formulaX`, `tian_identifiableX`,
  `tian_identifiable_ccompX`, tag `v4.20`).
- Factorization over many blocks; Tian's theorem for sets with one sum per
  c-component (`marginal_prod`, `tian_identifiable_sets`, tag `v4.21`).
- Each factor is a causal effect (`Q_causal`, `lat_one`, tag `v4.22`).
- Cleanup: round 25 derived from round 27 as corollaries; `tian_formulaX` and
  `Q_doX` removed (covered by `tian_formula_blocks`, `Q_do_gen`); audit claims in
  HANDOFF corrected (tag `v4.23`).
- Clean build of tag `v4.23` from a fresh clone; the definitions, the statements of
  the identification results and their axioms archived in
  `verification/audit_v423_output.txt` (`verification/AuditV423.lean`). No
  kernel-bypassing constructs in the sources.
- Two unused variable names removed; the comparison with CausalSmith/Causalean
  updated to its commit `a7085d8`, and two further formalizations added under
  Related work (tag `v4.24`).
- Tian's lemma on marginalising factors (`Q_marg`, `Q_marg_eq`, tag `v4.25`).
- Tian's lemma 11 (`Q_ident_within`, `Q_split_rel`, `Q_le_one`, tag `v4.26`).
- Tian's IDENTIFY as `Reach` (`reach_sound`, `reach_ident`, `Reach.trans`, tag `v4.27`).
- ID soundness for sets (`id_sound`, `id_sound_blocks`, `Q_lat`, tag `v4.28`).
- ID soundness with line 2 (`id_sound_anc`, `Q_prod_rel`, `fiber_eq`, tag `v4.29`).
- Test case for the ID recursion (`IdAudit.id_audit`, `IdAudit.tian_sets_fails`, tag `v4.30`).
- Verma constraints (`Q_local`, `verma_sum`, `Verma.verma_constraint`, tag `v4.31`).

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

Covered for identification: non-identifiability for every hedge of the form
`(F, F ∖ {x})` with any number of roots, embedded in any larger graph, for any
`Y` containing the roots (`embedded_not_identifiable`), and the channel step that
moves a non-identifiable effect one edge down a directed path (`channel_step`).

Also covered: roots that are only ancestors of `Y`, along disjoint directed paths
(`path_not_identifiable`, `rootTree_tail`).

Positive side: c-component factorization for any closed block, and the fact
that an intervention inside a block leaves the other factor unchanged
(`marginal_factor`, `do_marginal_factor`); each factor determined by the observed
distribution (`Q_identifiable`); and Tian's theorem: for a single observed `x` whose
block contains no child of `x`, the effect is identifiable with an explicit formula
(`tian_identifiable`, `tian_formula`), stated with the c-component of `x`, which is
the least closed block containing `x` (`ccomp_isLeast`, `tian_identifiable_ccomp`).

Dividing line for a single `x` (`tian_iff`): with latents as roots and Bool-valued
variables, `P(O ∖ {x} | do(x))` is identifiable if and only if no child of `x` lies in
the c-component of `x`.

For a set `X`: identifiable when no `x ∈ X` has a child in its own c-component, with
an explicit formula (`tian_identifiable_sets`, `tian_formula_blocks`). Not the exact
line for sets: e.g. `x → c` with `x ↔ o ↔ c` and `o ∈ X` is identifiable but not
covered; that needs the recursion of the ID algorithm.

Not yet covered: paths from several roots that merge before reaching `Y`; `X` meeting the hedge in
more than one vertex; the ID algorithm for sets `X`; and
completeness of the do-calculus for identification (Shpitser–Pearl,
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
  under positivity, and soundness of the ID algorithm, including the recursive version with Tian's
  IDENTIFY fixing sequence (`id_sound_rec`), c-components, and a runnable ID
  checker proved sound. The c-component factorization and Tian's theorem here
  (rounds 20–28) therefore overlap with it, in a more elementary finite `PMF`
  setting. As of its commit `a7085d8` (2026-10-12), a text search found no
  non-identifiability results for hedges (its checker states that a `false`
  result carries no non-identifiability claim), no completeness of
  d-separation or of individual do-calculus rules, and no back-door/front-door
  criteria stated in terms of paths. Those, the hedge families (rounds 14–19)
  and the exact dividing line `tian_iff` are the parts of this project not found
  there. This comparison is based on searching source and documentation, not
  on building that project.
- **Cubical Agda** (Sargsyan, arXiv:2606.20351, 2026; from the abstract):
  soundness of d-separation and the three rules of the do-calculus in kernel
  form; no completeness, no identification.
- **Rocq** (Zhang, Luo, Bielicke, Jun, Chlipala, arXiv:2604.22041, 2026, and
  Zhang's MIT thesis 2025; from the abstracts): d-separation is equivalent to a
  semantic separation property; no do-calculus, no identification.
- **Statlib** — ongoing discussion at leanprover.zulipchat.com (#Statlib) of a
  unified Lean library for causal inference and potential outcomes.
