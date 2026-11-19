# Handoff: state of PearlDoCalculus and how to continue

Written for whoever continues this project: the author, another person, or an
AI assistant starting without the conversations that produced it. Status as of
tag `v4.111` (November 2026): cleanup in progress; `Hedge.lean` is split by topic into
`Hedge/*` (v4.86–v4.99); `Identification.lean` is being split into `Identification/*`
(`Identification/Basic` v4.102, `Bow` v4.103, `Hedge2` v4.104, `HedgeChain` v4.105, `HedgeTemplate` v4.106, `LatentTree` v4.107, `TwoRoot` v4.108, `RootPathModels` v4.109, `RootPath` v4.110, `RootTree` v4.111, `Channel` v4.112, 5 files to go).

## 0. Start here

**What this is.** A Lean 4 formalisation of Pearl's causal calculus for finite
DAGs with finite value types (`PMF`-based, no measure theory): d-separation, the
three rules of the do-calculus, adjustment formulas, and an identification layer
with latent variables (Tian's c-factors, the ID algorithm, IDC, the hedge
criterion). About 21 000 lines. No `sorry`; every main result depends only on
`propext`, `Classical.choice` and `Quot.sound`.

**Use tag `v4.38` or later.** Tag `v4.37` does not build (an `omit` in
`Hedge.lean` named an instance that `nxt` uses, and the release script committed
on a stale build log). It is kept only because it was already pushed.

**Build.**
```
git clone https://github.com/Johaan70/PearlDoCalculus && cd PearlDoCalculus
lake exe cache get      # Mathlib cache
lake build              # must end in "Build completed", no "declaration uses 'sorry'"
```
Toolchain `leanprover/lean4:v4.30.0-rc2` (`lean-toolchain`); Mathlib pinned in
`lake-manifest.json`. Most docstrings and section comments are in Norwegian;
declaration names, this file and the README are in English.

**Completeness of the ID algorithm is proved (v4.80).** `Hedge.idCheck_iff`: with
latent variables as roots, `X` and `Y` observed and `X ∩ Y = ∅`,
`idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y`. The steps H1–H5 are in
section 2. For the tails from the roots to `Y` (H4) the published argument needs repair;
the product construction used instead is described there, with numerical checks in
`verification/h4_checks.py`.

**Next: cleanup.** The goal is the simplest, best documented and most understandable
formalization possible: one clear idea per file, no duplicated helpers, no
`first | … | …` fallbacks, no superseded results, consistent names, short proofs, and
each file opening with a plain-language account of what it proves, why and how. It is
best done by an agent working directly on the server, where it can build and retry by
itself.
The step-by-step plan is in `CLEANUP.md`; working rules for an agent are in `CLAUDE.md`;
the agent itself is `.claude/agents/pearl-cleanup.md`, and `scripts/check.sh` is the
gate for every commit.

**Where things are.** Section 1 lists what is proved, section 2 the plan,
section 3 the scope limits, section 4 a map of the files, sections 5–6 how to
work, section 7 history worth keeping, section 8 technical debt.

## 1. What is proved

Causal models are finite DAGs with finite value types. Latent vertices are a
set `U`; observed are `O = Uᶜ`. `Identifiable G α O X Y` means: any two models on
`G` with value types `α` whose observed distributions agree and are positive give
the same `P(Y | do(X))`.

| Result | Main declarations | File |
|---|---|---|
| d-separation soundness (walks, paths, sets) | `dsep_sound`, `dsep_sound_path`, `dsep_sound_set` | `DSepSound`, `WalkPath`, `SetSound` |
| d-separation completeness | `dsep_complete` | `Completeness` |
| d-separation as an exact criterion (vertices, sets) | `dsep_iff`, `dsepPath_iff`, `dsepSet_iff` | `Completeness` |
| Do-calculus rules 1–3, Pearl's form, no positivity | `rule1`, `rule2`, `rule3_general` | `DoCalculus`, `Rule3Flag` |
| Back-door and front-door, Pearl's path criteria | `backdoor_adjustment_criterion`, `frontdoor_adjustment_criterion` | `Adjustment` |
| Rules 1 and 2 exact (vertices and sets) | `rule1_iff`, `rule1_iff_set`, `rule2_iff`, `rule2_iff_set` | `Completeness` |
| Rule 3 exact (vertices and sets) | `rule3_iff`, `rule3_iff_set` (cases: `rule3_iff_nonanc`, `rule3_complete_root`, `rule3_complete_copy`, `rule3_complete_set`) | `Completeness` |
| Back-door, front-door and fully observed ⇒ identifiable | `backdoor_identifiable`, `frontdoor_identifiable`, `observed_identifiable` | `Identification` |
| Observed parents ⇒ identifiable | `Parents.parents_identifiable` | `Identification` |
| Bow graph not identifiable, also inside any graph | `Bow.bow_not_identifiable`, `BowGen.bow_not_identifiable_general` | `Identification/Bow` |
| Hedge families not identifiable (special shapes) | `Hedge2.hedge2_not_identifiable`, `HedgeChain.chain_not_identifiable`, `HedgeTmpl.Tm.not_ident`, `HedgeTmpl.Tm.not_ident_X`, `PathTree.pathTree_not_identifiable`, `LatentTree.latentTree_not_identifiable`, `latentTree_not_identifiable_XY`, `TwoRoot.twoRoot_not_identifiable`, `MultiRoot.multiRoot_not_identifiable`, `RootPath.rootPath_not_identifiable`, `RootTree.rootTree_not_identifiable`, `RootTree.embedded_not_identifiable` | `Identification/Hedge2` (first), `Identification/HedgeChain`, `Identification/HedgeTemplate`, `Identification` |
| Transfer: subsets of `Y`, supersets of `y`, more edges never help | `Identifiable.mono_Y`, `not_identifiable_of_mem`, `Channel.not_ident_of_sub` | `Identification/Basic`, `Identification/Channel` |
| Tails: a root may be replaced by the end of a directed path | `Channel.channel_step`, `Channel.path_not_identifiable`, `Channel.rootTree_tail` | `Identification/Channel` |
| C-component factorization (Tian's Lemma 1), many blocks | `CFactor.marginal_factor`, `CFactor.Q_split`, `CFactor.Q_prod`, `CFactor.marginal_prod` | `Identification` |
| Intervention in a block changes only that block's factor; each factor is a causal effect | `CFactor.do_marginal_factor`, `CFactor.Q_causal` | `Identification` |
| Tian's Lemma 2: factors determined by `P(O)` | `CFactor.Q_identifiable`, `CFactor.Q_step` | `Identification` |
| Tian's theorem, explicit formula; with the c-component; for sets | `CFactor.tian_identifiable`, `CFactor.tian_formula`, `CFactor.tian_identifiable_ccomp`, `CFactor.tian_identifiableX`, `CFactor.tian_identifiable_sets` | `Identification` |
| Single `x` (latents roots, `Bool`): identifiable iff no child of `x` in its c-component | `CFactor.tian_iff`, `CFactor.not_ident_of_child` | `Identification` |
| Tian's lemmas: `Σ_{T∖S} Q[T] = Q[T ∩ S]`; lemma 11 | `CFactor.Q_marg`, `CFactor.Q_ident_within` | `Identification` |
| Tian's IDENTIFY is sound | `CFactor.Reach`, `CFactor.reach_sound`, `CFactor.reach_ident` | `Identification` |
| ID soundness for sets, including line 2 | `CFactor.id_sound`, `CFactor.id_sound_anc`, `CFactor.fiber_eq` | `Identification` |
| Verma constraints; Verma's classic example | `CFactor.Q_local`, `CFactor.verma_sum`, `Verma.verma_constraint` | `Identification`, `Verma` |
| ID as a computable check: `idCheck G U X Y = true` ⇒ identifiable | `IdAlgo.idCheck_sound`, `IdAlgo.identifyTop_sound`, `IdAlgo.ccIn_eq` | `IdAlgo` |
| Test case where ID needs the recursion; `decide` on concrete graphs | `IdAudit.id_audit`, `IdAudit.tian_sets_fails`, `IdAlgo.id_audit'`, `IdAlgo.bow_idCheck` | `IdAudit`, `IdAlgo` |
| IDC: conditional effects `P(Y | do(X), Z, W)` | `Idc.idc_sound`, `Idc.IdentifiableCond`, `Idc.doModel_doModel_marginal` | `Idc` |
| `idCheck = false` ⇒ IDENTIFY stuck, and the stuck set meets `X` | `Hedge.idCheck_false_meets`, `Hedge.stuck_meets_X`, `Hedge.identifyN_false` | `Hedge` |
| `idCheck = false` ⇒ a hedge exists (Shpitser–Pearl Def. 5, set form) | `Hedge.idCheck_false_hedge`, `Hedge.IsHedge`, `Hedge.bow_hedge` | `Hedge` |
| In a hedge: a forest into the roots (one chosen child per non-root) | `Hedge.nxt`, `Hedge.hedge_nxt`, `Hedge.hedge_reaches_root`, `Hedge.hedge_rootOf` | `Hedge` |
| Decomposition (semi-graphoid) | `condIndep_single` | `Completeness` |

**Audits.** Fresh-clone audits (exact statements via `#check @`, axioms, grep for
`sorry`, `axiom`, `native_decide`, `implemented_by`) are archived in
`verification/` for tags `v1.0`, `v2.0`, `v2.2`, `v4.23`, `v4.33`, `v4.38` and `v4.80` (the last one
covers the completeness theorem `Hedge.idCheck_iff`, with a sanity check on the bow). Other tags
were checked by the regular build with `#print axioms` on their main results.
`verification/rule3_*.py` are the exhaustive searches described in section 7.

## 2. Plan: completeness of the ID algorithm (the hedge criterion)

**Target theorem** (Shpitser & Pearl 2006, Thm 4; Huang & Valtorta 2006). For a
graph whose latents are roots, `X`, `Y` observed and disjoint:

  `P(Y | do(X))` identifiable  ⟺  `idCheck G U X Y = true`  ⟺  no hedge for `P_X(Y)`.

As far as we know nobody has formalised the negative direction in general
(CausalSmith/Causalean's `identifyMassRec_hedge` is the failing branch of the
recursion; it does not prove non-identifiability). Check this again before
claiming it.

**H0: scope (decided).**
- Latents are roots (`hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u`), as in `tian_iff`.
- Value types: binary. Read in Shpitser & Pearl, JMLR 9 (2008), appendix, proof
  of Thm 17: the construction is binary throughout, also on the tails; merging is
  handled by independent flip noise, not by tuples. An earlier version of this
  plan recommended `Fin (2 ^ |V|)`; that is withdrawn. See the caveat under H3
  for latents.
- Final statement (H5): `idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y`.
  For `←` one `α` is enough, so the witness may choose the latent value types.

**H1: ID as a decidable function. DONE (v4.32–v4.33, `IdAlgo`).**
`ancIn`, `ccIn` (computable closures), `identifyN` (with fuel),
`identifyTop` (fuel `Fintype.card V + 1`, shown sufficient), `idCheck`,
`idCheck_sound`. `decide` works on the test graphs.

**H2: ID failure gives a hedge. DONE (v4.35–v4.36, `Hedge`).**
`idCheck_false_hedge : idCheck G U X Y = false → ∃ F F', IsHedge G U X Y F F'`,
with `F = D` (the c-component block of some `y` in `G_{X̄}[An(Y)]`) and `F' = T`
(where IDENTIFY gets stuck). `IsHedge` has the fields
`sub : F ⊆ F'`, `ne : F ≠ F'`, `rootF`/`rootF'` (every vertex of `F` resp. `F'`
reaches `R := rootsIn G F` inside itself, stated as `ancIn … = …`),
`out : F ∩ X = ∅`, `meet : F' ∩ X ≠ ∅`, `anc : R ⊆ An(Y)` in `G_{X̄}`,
`conn`/`conn'` (`CConn`: c-connected inside itself). Note: `F`, `F'` may contain
latent vertices; a latent in a c-component always has a child there.
The key insight was that a C-forest in Shpitser–Pearl is a *subgraph* (each
vertex keeps at most one child edge), so the roots need not be childless in
`G[F']`; `R := rootsIn G F` works for both.

**H3: a hedge is not identifiable on its roots. DONE (v4.69).**
Done (v4.38): `nxt` chooses one child per non-root vertex of `F'` (inside `F`
for vertices of `F`); `hedge_reaches_root`: iterating `nxt` reaches `R`.
Done (v4.39): `nxt` fixes the roots (`nxt_root`) and stays in `F` and `F'`
(`hedge_iter_memF`, `hedge_iter_mem`); one number of steps brings every vertex of `F'`
to a root (`hedge_root_uniform`); `hedge_rootOf` gives the root map `r`, constant
along `nxt`. This is the bookkeeping the parity models need.
Done (v4.40), spanning tree step 1: `sib G U F a b` (`a`, `b` in `F` with a common
latent parent in `F`); `cconn_sib`: with latents as roots, `CConn G U F` gives a chain
of siblings between any two observed vertices of `F`.
Done (v4.41), spanning tree steps 2–3: `lay` (layers by number of sibling steps from a
chosen observed `ρ`), `lay_of_chain`, and `sib_tree`: every other observed vertex of a
c-connected `F` has a sibling `par v` with strictly smaller distance `d`.
Done (v4.42), spanning tree finished: `hedge_tree` gives, for an observed `ρ ∈ F`, a
parent `par v` (a sibling in `F'`, strictly smaller `d`) for every other observed vertex
of `F'`, and for `v ∈ F` the sibling relation holds inside `F`. So the tree of `F'`
contains a spanning tree of `F` (suggested-order step 1 below is done). Done (v4.43):
`hedge_obs` (with latents as roots, `F` has an observed vertex), `sib_obs` (siblings are
observed), `hedge_spanning` (every hedge has an observed `ρ ∈ F` and such a tree).
Done (v4.44): `Channel.not_ident_of_sub` holds only for `Bool` on every vertex, which
the bit-vector latents of the caveat below need beyond; `Hedge.not_ident_of_subα` is the
same result for any value types `α`.
Done (v4.45), step 2 set up: `keepDAG G K` (the subgraph with the edges satisfying `K`),
`not_ident_keep` (not identifiable there ⇒ not identifiable in `G`, any `α`), `hedgeKeep`
(the forest edges `v → nxt v` and the tree's latent edges `u → v`, `u → par v`), and
`hedge_red_nxt`, `hedge_red_lat` (those edges are in the reduced graph). Next: the parity
models on `keepDAG G (hedgeKeep …)`, step 3 below; the latent `u` behind each tree edge
comes from `sib` (pick it with `choose`).

**Plan for step 3, worked out for this formalisation (v4.46).** Bits: one latent bit per
tree edge `(v, par v)`, plus one flip latent `f` on one root `r₀` with `P(f = 1) = 1/4`.
`M1`: every observed `v ∈ F'` is the xor of the bits of the tree edges at `v` and the
values of its `nxt`-children (and `f` at `r₀`). `M2`: the same for `v ∉ F`; a vertex of
`F` reads only the edges of the `F`-tree and its `nxt`-children in `F`.
(i) Tree-incidence lemma over `ZMod 2`: for a parent-pointer tree,
`c v = Σ_{w in the subtree of v} inc c w` for `v ≠ ρ` (the parent of `u` lies below `v`
iff `u` does and `u ≠ v`, so the other terms cancel in pairs). Hence incidence is
injective using only non-root rows, and every `τ` with `Σ τ = 0` is hit.
(ii) Both observed maps (bits ↦ observed values, without `f`) are injective and land in
`H = {o : parity of R is even}`; equal cardinality makes both bijections onto `H`, so with
`f` both give `P(o) = (3/4 or 1/4) / |H|` by the parity of `R`: equal and positive. For
`M2`: the `F`-tree bits come from the `F` part by (i); the other edges form a tree on
`(F' \ F) ∪ {F contracted}`, and (i) with the contracted vertex as root gives them.
(iii) Under `do(x)`: in `M2` the values in `F` do not depend on `X` (`F ∩ X = ∅`, and `F`
reads only `F`), so `P(parity of R odd) = 1/4`. In `M1` let `A` be the observed vertices
whose `nxt`-path to the root avoids `X`; `R ⊆ A`, `x ∉ A`, so some tree edge joins `A` and
its complement, and its bit enters the parity of `R` once: `P(odd) = 1/2`.
(iv) Different parity probabilities give some `t` with different `P(R = t | do x)`.
Done (v4.46): `ParTree` (parent-pointer tree), `desc` (subtree), `iter_mem`, `iter_d_le`,
`desc_par_iff` — the first part of (i). Estimate for all of step 3: 20–30 rounds.
Done (v4.47): `inc` (incidence) and `ParTree.inc_inj`: equal incidence at every non-root
vertex gives equal bits, by induction from the leaves (children have larger `d`). This is
all of (i) that (ii) needs: injectivity, not the subtree-sum formula; (ii) then gets the
images from injectivity and cardinality.
Revised (v4.48): (ii) is easier without counting. In `M2` the values outside `F` depend
only on the bits `b_o` of the non-`F`-tree edges, the same function as in `M1`. In `M1` a
vertex `v ∈ F` reads in addition `δ(v)`: the `b_o` bits at `v` and its `nxt`-children
outside `F`; `δ` depends only on `b_o`, and `Σ_{v ∈ F} δ(v) = 0` (both sides count the
outside incidences twice). So shifting the `F`-tree bits by a solution `s(b_o)` of
`inc_F s = δ` turns `M1` into `M2` on every outcome; the shift preserves the uniform
bits, so `P(O)` agrees. Positivity: for any `o`, take `f` = parity of `o` on `R` and solve
for the bits. Both need only existence, `inc_surj`.
Done (v4.48): `inc_surj` — every `τ` with `Σ_S τ = 0` is the incidence of some bits, by
induction on `|S|` (remove a leaf, move its value to its parent).
Done (v4.49): `marginal_eq_of_invol` (an involution on full assignments that keeps `O`
and carries `M1`'s joint to `M2`'s gives equal marginals on `O`; the hedge families each
had their own copy, `full_map`/`obsEq`) and `exists_ne_of_sum_ne`. For (ii) the
involution shifts the `F`-tree bits by `s(u)`, chosen from the coordinates it does not
change, and is the identity where `Σ_{v ∈ F} δ ≠ 0` (there both joints are 0, since the
outside part, which is the same in both models, is then inconsistent). The models can
live on `G` itself (kernels may ignore parents); the noise for positivity can sit in the
kernel of one root (no extra latent vertex needed); latents get the value type
`Fin |V| → ZMod 2`, one bit per tree edge, indexed by the edge's lower vertex.
Done (v4.50), namespace `Hedge.PM`: every vertex has value type `Val U v = Fin (kk U v) →
ZMod 2` with `kk = |V|` for latents and `1` for observed vertices (no type-level `if`);
`rd x i` reads bit `i` (0 out of range), so kernels read parents without proof
obligations; `ix` indexes tree edges; `cst`, `rd_cst`, `obs_ext`, `eq_cst` (an observed
value is its bit); `noise` (`1` with probability `1/4`, from `Fin 4`). Final theorem then
uses `α = Val U`, which the H5 statement (`∀ α`) allows.
Done (v4.51): the models. `Data` (`ρ`, `par`, `lat c` = the latent behind tree edge
`(c, par c)`, `r0` = the root with noise); `CH v` (tree children), `NX v` (`nxt`-children,
observed non-roots), `scope` (in `M2` a vertex of `F` counts only children in `F`), `sb`
(own tree bit + children's tree bits + `nxt`-children's values), `rdp` (reads parents
through `if h : w ∈ G.parents v`, so no proof obligations), `kern`, `M G U F F' D two`
(`M1` = `two = false`, `M2` = `two = true`), and `kern_lat`, `kern_out`, `kern_obs`,
`kern_r0`. Next: the kernel factors of a full assignment (`kfac`) for each case, with
`rdp` turned into reading the assignment once the parent guards are shown to hold.
Done (v4.52): `rdS` (reads a full assignment, still guarded by parenthood),
`rdp_restrict`, and the kernel factors `kfac_lat`, `kfac_out` (`1/|Val U v|`), `kfac_obs`
(indicator that the bit is `sb … (rdS …)`), `kfac_r0` (`noise (bit + sb)`). Next: show the
parent guards hold for the parents `sb` reads (`lat v`, `lat c`, `nxt`-children), so
`rdS` reads the assignment directly; then the involution of (ii).
Done (v4.53): `Good` (the conditions on `Data`, all available from `hedge_spanning`:
`ρ` observed in `F`; `par v` observed in `F'`, in `F` when `v ∈ F`; `lat v` latent with
edges to `v` and `par v`; `r0` an observed root), `lb` (tree-edge bit), `ov` (observed
value), `sbV`, and `sb_read`: under `Good` and a hedge, `sb … (rdS …) = sbV …`.
Next, the involution of (ii): `δ v` = the terms `sbV` has in `M1` but not in `M2` (only
for `v ∈ F`: tree children and `nxt`-children outside `F`); shift the `F`-tree bits by a
solution of `inc t = δ` (`inc_surj`, on the observed vertices of `F` with root `ρ`); `δ`
reads only coordinates the shift leaves alone, so the map is an involution. The
telescoping identity `Σ_{v ∈ F} δ v = 0` holds when the vertices of `F' \ F` satisfy
their equations; otherwise both joints are 0 and the map is the identity.
Done (v4.54): `δ`, `sbV_split` (in `F`, `M1` bit = `M2` bit + `δ`), `sbV_out` (equal
outside `F`), `EF` (tree edges in `F`), `sh t` (shift the `F`-tree bits by `t`),
`sh_sh` (involution), `sh_obs` (observed values unchanged), `lb_sh` (tree bit grows by
`t c` exactly for `c ∈ EF`). Next: `δ` of `sh t s` equals `δ` of `s` (it reads only
non-`F` edges and observed values), then `M2` bit of `sh t s` = `M2` bit of `s` +
`inc (EF ∪ {ρ}) ρ par t` in `F`.
Done (v4.55): `incF` (incidence of `t` in the `F`-tree), `ov_sh`, `δ_sh` (the shift does
not change `δ`), `sbV2_sh` (in `F` the `M2` bit of `sh t s` is that of `s` plus
`incF t v`). Next: relate `incF` to `inc` on the observed vertices of `F` (root `ρ`), choose
`t` by `inc_surj` when `Σ_{v ∈ F obs} δ v = 0`, and assemble the involution.
Done (v4.56): `OF` (observed vertices of `F`), `incF_eq_inc`, `exists_shift` (needs the
`F`-tree as a `ParTree (OF U F) ρ par d`, so `Data.par` should fix `ρ`), `tsel`, `phiS`,
`phiS_invol`, `phiS_restrict`. Next: when `tsel (δ s)` solves `incF t = δ s`, every kernel
factor of `M2` at `phiS s` equals that of `M1` at `s`; when no solution exists,
`Σ_{OF} δ s ≠ 0`, and the telescoping identity gives a vertex of `F' \ F` whose factor
is 0 in both models (there `phiS s = s`, since `tsel = 0`).
Done (v4.57): `sbV1_sh_out` (outside `F` the `M1` bit reads nothing the shift changes)
and `kfac_phiS`: when `tsel (δ s)` solves `incF t = δ s` on `OF`, every kernel factor
of `M2` at `phiS s` equals that of `M1` at `s`. Next: the telescoping identity for the
case with no solution.
Done (v4.58), tools for telescoping: `Out` (observed vertices of `F' \ F`), `fiber_sum`,
`part_sum`, `CH_out`, `NX_out`, `CH_in_out`, `NX_in_out` (children sets moved onto
`Out`), `par_cover`, `nxt_cover`, `OF_Out_dis`. The identity, for the next round: if every
`w ∈ Out` has `ov w = sbV false w`, then `Σ_{OF} δ = Σ_{c ∈ Out, par c ∈ OF} lb c +
Σ_{w ∈ Out, nxt w ∈ OF} ov w`, and summing the equations over `Out` gives
`Σ_{w ∈ Out, nxt w ∈ OF} ov w = Σ_Out lb + Σ_{c ∈ Out, par c ∈ Out} lb c`; so
`Σ_{OF} δ = 2 Σ_Out lb = 0`.
Done (v4.59): `tele` — that identity, proved. Next: the joint equality
`M2.fullJoint (phiS s) = M1.fullJoint s` (if `tsel (δ s)` solves, `kfac_phiS`; if not,
`Σ_{OF} δ s ≠ 0` by `exists_shift`, so by `tele` some `w ∈ Out` breaks its equation, its
factor is 0 in both models, and `phiS s = s` since `tsel = 0`), then equal observed
marginals by `marginal_eq_of_invol`.
Done (v4.60): `joint_phiS` (the joint equality, both cases) and `marg_eq` (M1 and M2 have
the same marginal on every set of observed vertices). Next: positivity (the noise at `r0`
and `inc_surj`), the do-difference (M1 parity 1/2 vs M2 1/4), then the final assembly
with `Good` built from `hedge_spanning`.
Done (v4.61): `pos_M1` — every observed assignment has positive probability in `M1`
(needs the whole `F'`-tree as a `ParTree (OF U F') ρ par d`): start from `baseA a` (`a` on
`O`, 0 elsewhere), solve `inc b = tauP` by `inc_surj` (`tauP` = the right-hand sides, with
the value at `r0` chosen so the sum is 0), shift all `F'`-tree bits by `b`; every equation
holds except at `r0`, where the noise is positive (`noise_pos`). Next: the do-difference.
Plan for the do-difference (v4.62), fixing `x : X`. `M2`: the vertices of `F` are not in `X`
and read only `F`; summing their equations over `OF` cancels every tree bit and every
`nxt` value inside `F`, so the parity of `R` equals the noise `n` at `r0`. Nobody reads
`r0` (roots are not `nxt`-children, latents and `X` do not read it), so flipping `r0`'s
value changes only its own factor, by `noise 0 / noise 1 = 3`: `P(odd) = 1/4`. `M1`: let
`A` = the observed `s ∈ F'` whose `nxt`-path reaches a root without meeting `X`
(`R ⊆ A`, `X ∩ F' ⊄ A`), so some tree edge `(c, par c)` has exactly one end in `A`. The
map ψ flips the bit of that edge and the value of every `w` with
`φ w = nrI c w + nrI (par c) w = 1`; it does not depend on `s`. `nrI_rec` gives
`φ v = [v = c] + [v = par c] + Σ_{NX v} φ` for `v ∈ F' \ X`, which is exactly the change of
`v`'s equation, so every factor of `do(x)` is kept (also at `r0`, where the argument of
`noise` is unchanged); `X` is untouched. `sum_nrI_roots`: the parity of `R` flips by
`[c ∈ A] + [par c ∈ A] = 1`. So ψ is a weight-preserving involution swapping odd and
even: `P(odd) = 1/2`.
Done (v4.62): `hedge_rank_iter`, `hedge_cycle`, `iter_obs`, `nreach`, `nrI`, `nrI_rec`,
`nreach_root_unique`, `sum_nrI_roots`. Next: the map ψ and its effect on `lb`, `ov`, `sbV`.
Done (v4.63): `flipO`, `phiC`, `psiS` (ψ), `psiS_invol`, `lb_psi`, `ov_psi`, `sbV_psi` (the
`M1` bit changes by `[v = c] + [v = par c] + Σ_{NX v} phiC`), `phiC_rec` (outside `X` that is
exactly `phiC c v`), `nrI_X`. Next: every factor of `doModel M1 X x` is kept by ψ, the
joint is invariant, and the parity of `R` flips.
Done (v4.64): `map_flip_eq`, `kfac_psi_do`, `joint_psi`, `parR` (parity of the observed
roots), `nrI_lat`, `parR_psi`, `parR_half`: under `do(x)` in `M1`, `P(parR = 1) = P(parR = 0)`
whenever a tree edge `(c, par c)` has exactly one end reaching a root outside `X`
(assumes `X ∩ U = ∅`). Next: such an edge exists (some `x ∈ X ∩ F'` is observed and does not
reach a root; roots do; walk the tree), then `M2`: `P(parR = 0) = 3 · P(parR = 1)`.
Done (v4.65): `ParTree.iff_root`, `cross_edge` (that edge exists), and `map_ratio` (an
involution flipping `f` and multiplying the weight by `k` where `f = 1` gives
`P(f = 0) = k · P(f = 1)`). Next, `M2` under `do(x)`: on the support `parR` equals
`g s = ov r0 + sbV true s r0` (sum the equations of `OF`: tree bits and `nxt` values inside
`F` cancel); flipping `r0`'s value flips `g` and changes only `r0`'s factor, so
`map_ratio` with `k = noise 0 / noise 1` applies.
Done (v4.66): `noise_ratio` (`noise 0 = 3 · noise 1`), `sum_sbV2`, `parR_g` (on the support
of `do(x)` in `M2`, `parR s = ov r0 + sbV true r0`). Next: flip `r0`'s value; it changes only
`r0`'s factor, so `map_ratio` with `k = 3` gives `P(parR = 0) = 3 · P(parR = 1)` in `M2`.
Done (v4.67): `map_congr_supp`, `tauS` (flip `r0`), `sbV_tau`, `gS_tau`, `kfac_tau`,
`joint_tau`, `parR_three`: under `do(x)` in `M2`, `P(parR = 0) = 3 · P(parR = 1)`. Both halves
of (iii) are done. Next, the assembly: `Good` and the two `ParTree`s from `hedge_spanning`
(`par ρ := ρ`, `lat` from `sib`, `r0` an observed root of `F`); then from the parity gap to
some `t` with different `P(R = t | do x)`, and `¬ Identifiable G (Val U) Uᶜ X R`.
Done (v4.68): `not_ident_PM` — given `Good` and the two trees, `¬ Identifiable G (Val U) O X
(RO G U F)` for every observed `O` (`RO` = the observed roots of `F`). Via `pmf_two`,
`ennreal_contra`, `parY`, `parR_comp`. Next: build `Data`, `Good` and the two `ParTree`s
from `hedge_spanning`, which gives H3 for every hedge.
Done (v4.69), **H3 complete**: `mkData` (the construction data from `hedge_spanning`) and
`Hedge.PM.hedge_not_ident : IsHedge G U X Y F F' → (latents are roots) → (X observed) →
¬ Identifiable G (Val U) Uᶜ X (RO G U F)`, `RO` = the observed roots of `F`. Next: H4, from
the roots to `Y` (`RO ⊆ An(Y)` in `G_{X̄}`), then H5.

The construction, as read in JMLR 9 (2008), appendix, proof of Thm 17 (= Thm 4 of
the AAAI 2006 paper). Their hedge has `F' ⊆ F` with `X` only in `F`, so **the roles
are swapped relative to `IsHedge`: their `F` is our `F'`**. Both are `R`-rooted
C-forests.
1. Binary variables; each latent has exactly two observed children (in the
   forest). `M1`: every variable in the larger forest (our `F'`) is the parity of
   its parents. `M2`: the same, except the vertices of the smaller forest (our
   `F`) ignore their parents outside it. Latents are fair coins in both. Without
   intervention `R` has even parity in both models (each latent reaches `R` along
   two paths, and the bits cancel), and latents → observed is one-to-one in both,
   so the observational distributions agree. Some latent has one child among the
   ancestors of `X` in `F'` and one outside, so under `do(x)`
   `P(odd parity of R)` is 1/2 in `M1` and 0 in `M2`.
2. Positivity (`Identifiable` requires `P(O) > 0`): for each `r ∈ R` an
   independent latent flips `r` with small probability `p`. This changes the gap
   to `1/2` vs `p`-dependent, still different.
3. Larger graphs: extra edges are removed with `Channel.not_ident_of_sub`;
   vertices outside the hedge are independent uniform bits (`Completeness.liftSub`
   style, as in `BowGen`).

**Caveat for this formalisation (decide first).** Our latents are vertices that
may have more than two children, and removing edges cannot split a latent into
several. A latent with `k` children contributes its bit `k` times to the parity
of `R`. Recommended: give latents a bit-vector value type (one independent bit
per edge of the chosen latent spanning tree) and let each tree edge's two
children read their own bit. Then every "virtual latent" has exactly two
children and the paper's argument applies unchanged; observed vertices stay
`Bool`. This is allowed because the H5 statement quantifies over `α`.
Alternative: keep `Bool` and count multiplicities mod 2 (messier).

Suggested order:
1. From `CConn G U F'` extract a spanning tree of latent edges (pairs of observed
   vertices of `F'` sharing a latent parent in `F'`), such that its restriction
   to `F` is a spanning tree of `F` (grow `F`'s tree first, then extend).
2. Reduce the graph with `not_ident_of_sub` to: the `nxt` edges, the latent tree
   edges, and nothing else.
3. Define `M1`, `M2` on the reduced graph; prove `marginal O` equal via a
   bijection on latent assignments (the technique of `full_map` in the bow proof,
   no numerical sums).
4. Prove the `do(x)` difference on the parity of `R`.
5. Add the flip latents for positivity (or start with them).
Existing pieces that may be reused: `HedgeTmpl.Tm` (template with a set `X`),
`RootTree.RT`, `pth`, `parZ_φ`; their parity bookkeeping is in `ZMod 2`.
Before writing Lean, write the proof out on paper for one small hedge (e.g. the
bow and `IdAudit.idG` with an extra edge) and check it numerically if in doubt.

**H4: from the roots to `Y`. DONE (v4.79).** `RO ⊆ An(Y)` in `G_{X̄}`.

*The paper's argument has a gap here.* Shpitser–Pearl (r327 appendix, Lemma 12; thesis,
proof of Thm 5) take `I = An(Y) ∩ De(R)`, make each node of `I` the parity of its parents
(plus a flip), and claim the parity of `Y` equals that of `R`. A tail from a root may run
through `F' \ F` or back into `F`; then that fails. `verification/h4_checks.py` (exact,
with fractions) shows it on two small graphs: in example A (a tail re-enters `F`) the
paper's rule works only if `F` reads the tail in both models; in example C (`F` a full
c-component of `G_{X̄}[An(Y)]`, as from ID, and the only tail runs through `F' \ F`) the
paper's rule gives no difference in `P(z | do x)` in any variant tried. ID completeness
is still true (C has another hedge, a bow), but the formal proof must not rely on that rule.

*Construction that works (checked on A and C).* Keep the H3 models untouched in one
coordinate and carry the roots' values to `Y` in a second, so tails never interfere with
the kernels of `F` and `F'`:
- value type `α' v = Val U v × ZMod 2`; the first coordinate `a` follows `M G U F F' D two`
  (reading only the `a`-coordinates of the parents), the second is
  `b_v = [v ∈ RO] a_v + Σ_{w ∈ TC v} b_w + η_v`, with `η_v ~ noise` independently;
- `A = ancIn (cutIn G X) univ Y`; a tail pointer `tp w` for observed `w ∈ A \ Y`: a child
  of `w` in `A` and outside `X` (exists since `w ∈ An(Y)` in `G_{X̄}`); `TC v` = the
  observed `w ∈ A \ Y` with `tp w = v`. Iterating `tp` reaches `Y` (rank argument, as
  for `nxt`), and never enters `X`.
Steps, with an estimate of 14–18 rounds:
1. `tp`, its existence and reach lemmas; `tI s v` = `v` is on the `tp`-chain from `s`,
   with the recursion `tI s v = [v = s] + Σ_{TC v} tI s w` (as `nrI_rec`).
2. The models `M'` and the factorization `kfac' s v = kfac M (fst s) v · noise (η_v s)`,
   where `η_v s = b_v - [v ∈ RO] a_v - Σ_{TC v} b_w` (latents: `b` plain noise).
3. Equal observed marginals: `phiS` on `a`, `b` untouched; `η` reads only `b` and observed
   `a`, which `phiS` keeps, so `joint_phiS` lifts.
4. Positivity: take a positive `a` from `pos_M1`, put the target `b`; every `noise` factor
   is positive (`noise_pos`).
5. `M1'` under `do(x)`: ψ on `a`, and flip `b` along the chains of the roots `ψ` flips;
   every `η` is kept, `Yb = Σ_{y ∈ Y} b_y` flips (odd number of roots flip): `P(Yb = 1) =
   P(Yb = 0)` by `map_flip_eq`.
6. `M2'` under `do(x)`: for every `s`, `Yb = parR a + Σ_{v ∈ A, obs, ∉ X} η_v + Σ_{A ∩ X} b`
   (telescoping over the `tp`-forest); on the support `parR = gS` (`parR_g`). Involutions:
   `τ'` (flip `a_{r0}` and `b` along `r0`'s chain: flips `gS` and `Yb`, weight ×3 where
   `gS = 1`) and `σ_v` (flip `b` along `v`'s chain: flips `η_v` and `Yb`, weight ×3 where
   `η_v = 1`). Bias lemma by induction: with `ψ_j = Yb + Σ_{i ≥ j} e_i` (`e_0 = gS`,
   `e_i = η_{v_i}`), `ψ_0` is constant on the support, and `σ_j` keeps `ψ_j` and flips `e_j`,
   so `P(ψ_{j+1} = 0) = ¾ P(ψ_j = 0) + ¼ P(ψ_j = 1)`: never `½` if `ψ_j` is not. So
   `P(Yb = 1) ≠ ½` in `M2'`.
7. `¬ Identifiable G α' Uᶜ X Y` (as `not_ident_PM`, with `Yb` in place of `parR`).
Then H5.
Done (v4.71), step 1: `anc_child_in`, `AY`, `tp`, `tp_spec`, `iter_tpY`, `tp_iter_mem`,
`tp_iter_notX`, `tp_iter_obs`, `tp_rank_iter`, `tp_cycle`, `tp_reaches`, `tI`, `tI_rec`,
`sum_tI_Y`. Next: step 2, the product models.
Done (v4.72), step 2: `Val2`, `TC`, `tc_edge`, `bIn`, `kern2`, `MP`, `kern2_apply`, `fstA`,
`etaS`, `kfac2_eq` (factor of `MP` = factor of `M` on `fstA s` · `noise (etaS s v)`),
`joint2_eq`, `etaS_eq`. Next: step 3, equal observed marginals.
Done (v4.73), steps 3 and 4: `phiS_obs`, `phiS2`, `phiS2_invol`, `phiS2_restrict`,
`etaS_phiS2`, `joint2_phiS2`, `marg2_eq` (equal observed marginals) and `pos2`
(positivity of `MP false`). Next: step 5, `M1'` under `do(x)`.
Done (v4.74), step 5: `betaC` (where ψ flips `b`), `betaC_rec`, `betaC_X`, `psi2`,
`psi2_invol`, `psiS_X`, `etaS_psi2`, `kfac_psi2_do`, `joint_psi2`, `Yb`, `sum_phiC_RO`,
`Yb_psi2`, `Yb_half`: under `do(x)` in `MP false`, `P(Yb = 1) = P(Yb = 0)`. Next: step 6.
Done (v4.75), step 6a: `pair_ratio`, `map_fst0`, `map_fst1`, `map_add0`, `map_add1`,
`bias_step` (an involution keeping `f`, flipping `e`, tripling the weight where `e = 1`:
a bias of `f` gives a bias of `f + e`) and `bias_base` (`f` constant on the support).
Next, step 6b: the telescoping identity for `Yb`, the involutions `σ_v` and `τ'`, and the
induction over the observed vertices of `AY` outside `X`.
Done (v4.76), step 6b, part 1: `AO`, `AXo`, `Yb_tele` (for every `s`,
`Yb = parR a + Σ_{AO} η + Σ_{AXo} b`) and `fS_const` (on the support of `do(x)` in
`MP true`, `Yb + gS + Σ_{AO} η` is a constant depending only on `x`). Next: the involutions
`σ_v`, `τ'` and the induction.
Done (v4.77), step 6b, part 2: `tI_X`, `sig` (σ_v), `sig_invol`, `etaS_sig`, `Yb_sig`,
`kfac_sig_ne`, `joint_sig`, `tau2` (τ′), `tau2_invol`, `etaS_tau2`, `Yb_tau2`, `kfac_tau2_ne`,
`joint_tau2`. Next: the induction (`Yb_biased`).
Done (v4.78), step 6 complete: `fS`, `fS_sig`, `fS_tau2`, `Yb_biased`: under `do(x)` in
`MP true`, `P(Yb = 0) ≠ P(Yb = 1)`. Next: step 7, `¬ Identifiable G (Val2 U) Uᶜ X Y`.
Done (v4.79), step 7 and **H4 complete**: `YbY`, `Yb_comp`, `not_ident2`, `hedge_data`
(the construction data exist for every hedge) and
`Hedge.PM.hedge_not_ident_Y : IsHedge G U X Y F F' → (latents are roots) → (X, Y observed) →
X ∩ Y = ∅ → ¬ Identifiable G (Val2 U) Uᶜ X Y`. Next: H5.

**H5: put it together. DONE (v4.80).**
`id_iff : idCheck G U X Y = true ↔ ∀ α, Identifiable G α Uᶜ X Y` (with `hroot`,
`X ∩ U = ∅`, `X ∩ Y = ∅`). `→` is `idCheck_sound` (for every `α`). `←` is the
contrapositive: H2 gives a hedge, H3 and H4 give `¬ Identifiable` for the chosen
`α`.
Done (v4.80): `Hedge.idCheck_iff`, as stated (named `idCheck_iff`; `α : V → Type` with
`∀ v, Nonempty (α v)`; the witness type is `PM.Val2 U`).

**Estimate.** 8–12 rounds of the size of rounds 30–45. Highest risk: the latent
spanning tree (step 1 of H3) and merging tails (H4).

## 3. Scope and limits (what the results do not say)

- Finite DAGs, finite value types, `PMF`. No continuous variables.
- Identification results assume positivity of `P(O)` where stated; the negative
  results are for specific value types (`Bool` mostly), lifted to larger `α` only
  where stated.
- `tian_iff` and the planned `id_iff` assume latents are roots (semi-Markovian
  models). Latents with latent parents are not covered.
- Interventional (rung 2) only. Counterfactuals, probabilities of causation,
  transportability and selection bias are not formalised.
- No external expert has reviewed the definitions. Lean guarantees the proofs
  follow from the definitions; that `Identifiable`, `IsHedge`, `doModel` etc.
  mean what the literature means rests on the audits (section 1) and the test
  graphs. An expert review of `Identification.lean` lines 1–60 and
  `Hedge.IsHedge` would be the most valuable single check.

## 4. Map of the files (`PearlDoCalculus/`)

- Graph foundations: `DAG`, `Reachability`, `Walks`, `Blocking`, `DSeparation`,
  `WalkPath`, `BayesBall`, `Lauritzen`, `Counterexample` (a false lemma, kept).
- Models and d-separation: `CausalModel`, `DSepSoundSkeleton`, `DSepSound`,
  `SetSound`, `Completeness` (3 600 lines: completeness of d-separation and of
  each rule).
- Do-calculus: `DoCalculus` (`cutIn`, `doModel`, rule 1), `Rule3`, `Rule3Flag`
  (rule 3 without positivity), `DoAudit`.
- Adjustment: `SimpleConfounder*`, `MediatorAdjustment`, `BackdoorGeneral`,
  `FrontDoor*`, `Adjustment`, `AdjAudit`.
- Identification: `Identification/Basic` (the definition `Identifiable`, back-door,
  front-door, fully observed and observed parents, `mono_Y`), `Identification/Bow`
  (the bow graph, alone and inside any graph), `Identification/Hedge2` (the hedge with
  two latent variables), `Identification/HedgeChain` (hedge chains of any length),
  `Identification/HedgeTemplate` (the hedge template, latent paths with a tree),
  `Identification/LatentTree` (latent trees, sets `X` and `Y`),
  `Identification/TwoRoot` (the c-forest with two roots),
  `Identification/RootPathModels` (configurations and models for root paths, rounds 14 and 15 first part),
  `Identification/RootPath` (the proof that root-path configurations are not identifiable, rest of round 15),
  `Identification/RootTree` (the latent path always exists, embedded hedges, rounds 16 and 17),
  `Identification/Channel` (the channel step and whole directed paths, rounds 18 and 19),
  then `Identification`
  (the rest, about 2 500 lines, one namespace per round: `CFactor`,
  …), `IdAudit`, `Verma`, `IdAlgo`, `Idc`, `Hedge`.
- Completeness of ID: `Hedge/Defs` (the definitions `rootsIn`, `CConn`, `IsHedge`),
  `Hedge/FromID` (H2: a failing ID check gives a hedge, `idCheck_false_hedge`),
  `Hedge/Tree` (the forest `nxt` into the roots, the spanning tree `hedge_spanning`,
  incidence on trees `ParTree`, `inc_inj`, `inc_surj`),
  `Hedge/Reduce` (more edges never help, `not_ident_of_subα`; the reduced graph
  `keepDAG`, `hedgeKeep`),
  `Hedge/ParityModels` (the parity models `M1`, `M2` on a hedge: `PM.Data`, `PM.M`,
  their kernel factors, `PM.Good`, `PM.sb_read`),
  `Hedge/ObsEq` (`M1` and `M2` have the same observed distribution: `PM.phiS`,
  `PM.tele`, `PM.marg_eq`),
  `Hedge/Positivity` (the observed distribution of `M1` is positive, `PM.pos_M1`),
  `Hedge/DoGapM1` (under `do(x)` the root parity is a fair coin in `M1`: `nrI`, ψ,
  `PM.parR_half`),
  `Hedge/DoGapM2` (under `do(x)` the root parity is biased 3 : 1 in `M2`:
  `PM.cross_edge`, `PM.parR_three`),
  `Hedge/Roots` (H3: every hedge blocks identification at its observed roots,
  `PM.not_ident_PM`, `PM.hedge_not_ident`),
  `Hedge/Tails` (H4, first part: the tail pointer `tp` from the roots to `Y` and the
  indicators `tI`),
  `Hedge/Product` (H4, second part: the product models `PM.MP`, equal positive observed
  distribution, a fair `Yb` in `MP false`, `PM.Yb_half`),
  `Hedge/ProductBias` (H4, third part: the bias lemma and the induction that `Yb` is
  biased in `MP true`, `PM.Yb_biased`),
  `Hedge/Complete` (H4 at `Y`, `PM.hedge_not_ident_Y`; H5, the completeness theorem
  `idCheck_iff`),
  and `Hedge` itself, which only imports all of these.
- `EpistemicScope`: no proofs about causality; states what the project does not
  claim.
- `verification/`: audit files and outputs, Python searches for rule 3.

## 5. Workflow that worked

- One branch per piece of work; fast-forward merge to `main`; tag milestones.
- **Paper first.** Write the argument out, split it into lemmas of a few dozen
  lines, and only then write Lean. For constructions from the literature, read
  the paper; do not work from memory (the value-type mistake in H0 came from
  that).
- **Statement before proof.** Check that the statement type-checks with
  `sorry`, then fill in the proof.
- Edits are made by small Python scripts that `assert` the exact old text occurs
  once, and skip if the change is already there.
- **Release gating, strictly:** `rm -f` the build logs first; build; tag and
  push only if the *fresh* log shows `Build completed`, no `error`, no
  `declaration uses 'sorry'`. Check that the log file exists before grepping it.
  `v4.37` broke because a stale log from the previous release passed the gate.
- If edit scripts are tested against a local copy, make that copy a fresh clone
  of the current `main`; a copy that drifts from the repo makes scripts fail.
- One error at a time. To see the first goal:
  `lake build X 2>&1 | sed -n '/X.lean:[0-9]*:[0-9]*: \(unsolved\|error\)/,/^info\|^warning\|^error: Lean/p' | head -50`
- Audit tags from a fresh clone: `#check @thm`, `#print axioms`, and grep for
  `sorry`, `axiom`, `native_decide`, `implemented_by`.

## 6. Techniques and pitfalls

Techniques:
- Compare models on different graphs through their kernel factors
  (`marginal_eq_of_kfac`), never through equality of the models; this avoids
  transport between dependent types.
- Build assignments with membership proofs directly instead of `cast`.
- For zero/non-zero arguments, `Audit.marginal_eq_zero_of` and
  `Audit.marginal_ne_zero_of` reduce marginals to kernel factors.
- Observational equality by a bijection on latent assignments (`full_map`)
  rather than by computing sums.
- Fixed points of monotone set operators on a `Fintype`: `IdAlgo.iter_sub`,
  `iter_sup`, `iter_fix` (iterate `card` times).
- Proof-irrelevance: restrictions of restrictions are definitionally equal to
  direct restrictions; use `exact` or a `have` with a stated type when `rw`
  fails to see this.

Pitfalls that cost rounds:
- `Assignment` lives in `DAG.CausalModel`; `Incoming` in `PearlDoCalculus.DAG`.
- `decide` refuses goals with free variables; use named lemmas
  (`Bool.false_ne_true`). `Bool.true_ne_false` does not exist; in a closed goal
  `(by decide)` works.
- `push_neg` is deprecated in this Mathlib; use `simp only [not_forall, not_exists]`.
- Some Mathlib iff-lemmas take explicit arguments:
  `(PMF.mem_support_map_iff f p b).mp`, not `.mp` directly.
- `omit [Fintype V] in` fails ("cannot omit referenced section variable") when the
  statement uses a definition that includes the instance (e.g. `Hedge.nxt`).
  Unused-instance linter warnings are harmless; prefer leaving them to breaking
  the build.
- Names drift between Mathlib versions (`Finset.not_mem_empty` vs
  `notMem_empty`); prefer term proofs that avoid them.
- When a rewrite lemma has a set as an implicit argument and the goal has
  several marginals of the same model, give the sets explicitly
  (`(S := …) (T := …)`).
- Before `induction` on a copy of a hypothesis, `clear` the original.
- `tsum` carries a summation filter here; `rw [← tsum_fintype]` gets stuck on
  `SummationFilter.LeAtTop ?m`. Write the step as `calc` with the `tsum` stated.
- When a set such as `(T ∩ Sᶜ) \ U` occurs inside the goal, give general set
  lemmas their arguments, or `rw` may hit the inner set ("motive is not type
  correct").
- In Python heredocs with `'EOF'`, write `"\n"`, not `"\\n"`. Pasting a new block
  while `lake build` runs interrupts it.

## 7. History worth keeping

**Rule 3 (closed in v3.8 for vertices, v3.9 for sets).** `rule3_complete`
splits into: (1) `z` not an ancestor of `W` in `G_{X̄}` (`rule3_complete_nonanc`);
(2) `y`, `z` d-connected in `G_{X̄z̄}` (`rule3_complete_root`); (3) otherwise
(`rule3_complete_gap`): a chain from `y` to `z` in `G_{X̄}` with fewest colliders
(`Nat.find`), and the first `w₁ ∈ X ∪ W` that `z` reaches; minimality rules out
the bad cases via `Chain.take`, `Chain.snoc`, `Chain.cut` and `no_chain_of_dsep`,
so the chain-copy model applies (`rule3_complete_chaincopy`). Sets:
`rule3_complete_set_gap` via `set_gap_core`, one copy vertex suffices
(`rule3_complete_chaincopy_set`). Witnesses checked numerically:
`verification/rule3_chaincopy.py` (10 029 instances), `rule3_set.py` (7 312), 0
failures.

**ID algorithm line by line** (Shpitser–Pearl 2006, Fig. 3), all covered by
`id_sound_anc`: line 1 `marginal_restrict`; line 2 `S` ancestral in `G_{X̄}`;
line 3 is subsumed (vertices outside `S = An(Y)` are summed out in the intervened
model); lines 4, 6, 7 via `Q_prod`, `Q_causal`, `Q_identifiable`, `Q_marg`,
`Q_ident_within`, `Reach`; line 5 (failure) is the hedge side, section 2.

**Superseded open items.** Earlier notes listed "merging tails" and "`X` meeting
the hedge in several vertices" as separate problems for the hand-built hedge
families. The paper's construction (section 2, H3–H4) handles both; the old
families remain as special cases and as reusable parity machinery.

**Relation to other work.** CausalSmith/Causalean (github.com/Jiyuan-Tan/CausalSmith)
is broader and measure-theoretic; as far as we found (commit `a7085d8`) it has
global Markov, rule 1, restricted rules 2–3 and soundness of the recursive ID
algorithm, but not completeness of d-separation or of individual rules, and no
non-identifiability results. Our `Reach` follows the shape of its
`CFactorReachableRec`; the proofs are ours.

**Disclosure.** The proofs were developed with substantial help from Claude
(Anthropic). All proofs are checked by Lean. The author's Lean Zulip account is
deactivated, so the project has not been announced there; a draft announcement
is in the git history of this file (tag `v4.36`, section 5).

## 8. Technical debt

- Many `first | a | b | c` fallbacks were written because the exact Mathlib
  lemma form could not be checked in advance; each could be pruned.
- `Identification.lean` is about 8 300 lines; one file per namespace would be
  easier to navigate.
- Small helpers (`pure1`, `pure0`, `c2`, `pOf`/`parOf`/`parOfA`) are repeated in
  several namespaces; `full2`, `full3`, `join2` are three versions of the same
  splitting of latent assignments.
- `TwoRoot` is the case `n = 0`, `r = 1` of `RootTree` but not derived from it.
- Round 25 is superseded by round 27; only its helper lemmas remain needed.
- Several files have unused-instance linter warnings (harmless).
