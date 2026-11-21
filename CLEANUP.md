# Cleanup plan

**Goal.** The simplest, best documented and most understandable formalization of
PearlDoCalculus that is possible. The mathematics is done and audited (tag `v4.80`,
`verification/audit_v480_output.txt`). This task changes how the proofs read, never what
they prove.

## Public results (exact statements must not change)

`Hedge.idCheck_iff`, `IdAlgo.idCheck_sound`, `Hedge.idCheck_false_hedge`,
`Hedge.PM.hedge_not_ident`, `Hedge.PM.hedge_not_ident_Y`, `Idc.idc_sound`,
`Completeness.dsep_iff`, `Completeness.dsepSet_iff`, `Completeness.rule1_iff_set`,
`Completeness.rule2_iff_set`, `Completeness.rule3_iff_set`,
`Adjustment.backdoor_adjustment_criterion`, `Adjustment.frontdoor_adjustment_criterion`,
`Identification.CFactor.tian_iff`, `Verma.verma_constraint`, and the definitions
`Identification.Identifiable`, `IdAlgo.idCheck`, `Hedge.IsHedge`.
`verification/AuditV480.lean` checks them; it must still run at the end. They also keep
their names. `scripts/check.sh` compares their statements with
`verification/public_statements.txt` (frozen at `v4.85`) before every commit.

## State at the start (v4.82)

- About 25 700 lines in 33 files. Four files are too large:
  `Identification.lean` (8 281 lines), `Hedge.lean` (4 998), `Completeness.lean` (3 598),
  `DSepSoundSkeleton.lean` (2 096).
- 114 `first | … | …` fallbacks (written because the right lemma name or form could not
  be checked in advance). Most have one branch that works and others that never run.
- 24 small `zmod2_*` lemmas, each proved by `decide`, scattered through `Hedge.lean`.
- `Hedge.lean` is organized by work round (45 "Runde N" sections), not by topic.
- Docstrings and section comments are mostly in Norwegian.
- Some early results were later proved more generally (see `HANDOFF.md`, section 8).

## Steps, in order

1. **Split the large files by topic**, without changing any proof. Aim for files of at
   most about 800 lines, each with one idea. A natural split of `Hedge.lean`:
   `Hedge/Defs` (`IsHedge`, `CConn`, `rootsIn`), `Hedge/FromID` (H2: ID fails ⇒ hedge),
   `Hedge/Tree` (`nxt`, the spanning tree, `ParTree`, `inc`), `Hedge/ParityModels`
   (`Data`, `Good`, the models `M`), `Hedge/ObsEq` (telescoping, `phiS`, equal marginals),
   `Hedge/Positivity`, `Hedge/DoGap` (ψ, τ, `parR_half`, `parR_three`),
   `Hedge/Roots` (H3), `Hedge/Tails` (`tp`, `tI`), `Hedge/Product` (`MP`, `psi2`, the bias
   lemma), `Hedge/Complete` (H4, `idCheck_iff`). Do the same for `Identification.lean`
   (c-components, Tian, identifiability, the hedge families), `Completeness.lean` and
   `DSepSoundSkeleton.lean`. Build after each file. The split of `Identification.lean`
   is planned in detail in *Proposal: split of `Identification.lean`* below.
2. **Remove the `first` fallbacks.** For each one, keep the branch that works (try them
   one at a time) and delete the rest.
3. **Collect shared helpers.** One `ZMod2.lean` for the `zmod2_*` facts (merge duplicates);
   the same for repeated small lemmas about `Finset`, `PMF` and assignments (for example
   the three versions of splitting the latent variables).
4. **Remove superseded results** that nothing uses (`grep` for every use first), and the
   scratch files `Probe135.lean`–`Probe140.lean` in the root and the old `Check*.lean`,
   `Probe.lean` in `verification/` if nothing refers to them.

   **Owner's decisions (step 4).**
   - Delete the scratch files `Probe135.lean`–`Probe140.lean` (root),
     `verification/Check*.lean` and `verification/Probe.lean`.
   - Delete the superseded results `Identification/Hedge2`, `Identification/TwoRoot`,
     `Identification/Channel`, `Hedge/Reduce`, `Completeness/Rule3Copy`, the round 5
     `Parents` block, the unused set versions (round 12), and the unused lemmas listed
     for step 4 (C2 `union_inter_distrib`, `disjoint_inter_of_disjoint`;
     `Finset.exists_ne_of_sum_ne`; F4 `Channel.not_ident_of_sub` goes with `Channel`).
   - Keep `Identification/Bow` and `Completeness/Rule3ChainCopy`.
   - Delete the old audit files `verification/AuditV1.lean`, `AuditV2.lean`,
     `AuditV22.lean`, `AuditV423.lean`, `AuditV433.lean`, `AuditV438.lean`, but keep
     their `audit_v*_output.txt` files.
   - Keep `verification/AuditV480.lean` (frozen), `PublicStatements.lean`,
     `AxiomCheck.lean`, `Axioms.lean` (deleted in v4.172 on the owner's decision: its four
     lines were a subset of `AxiomCheck.lean`), and all Python scripts.
   - Everything deleted stays available at tag `v4.152`.
5. **Document every file.** Each file opens with a module docstring in plain English:
   what it proves, why it is needed, how the proof goes, and its main results. Rename
   sections by topic. Translate the Norwegian comments.
6. **Make the names consistent** (Mathlib style). Old public names stay as deprecated
   aliases until step 7.
7. **Shorten proofs** where a simpler tactic clearly works. Lowest priority.
8. **Finish.** Remove the deprecated aliases, run a fresh-clone audit like
   `verification/AuditV480.lean`, and update `README.md`, `HANDOFF.md` (file map) and
   `EXPLAINER.md` ("What is not elegant").

### Proposal: split of `Identification.lean` (step 1, surveyed at v4.100)

**Survey.** `PearlDoCalculus/Identification.lean` has 8 281 lines and imports only
`PearlDoCalculus.Completeness`. It is a sequence of 35 closed blocks, one per work round
("Runde 1" … "Runde 36"; there is no round 10 or 35, and round 15 ends with a short
block "Runde 14 som korollar av runde 15"). Every block opens and closes its own
`namespace Identification` (with a sub-namespace such as `Bow` or `CFactor`), so no cut
needs to fall inside a namespace except inside round 15 (see below). There are no
`private` declarations, no `section`s that cross a round, no instances and no
attributes. Things that a split must repeat at the top of every new file:

- the file-level line 15, `open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3
  Classical` (it applies to the whole file; `Classical` affects elaboration);
- `open scoped ENNReal` (line 258); it is in force for everything from round 3 on, so
  also for rounds 5 and 11 even when they move next to rounds 1 and 2;
- the selective `open X (…)` lines of each round, which are already inside the rounds.

One `include hxy in` (line 798) sits inside a `section` of round 4 and moves with it.
The file contains 62 `#print axioms` lines; they move with their rounds (removing them
belongs to step 4 or 5). 78 lines contain `first` (step 2).

The declaration-level dependencies (read off the compiled terms) only point from later
rounds to earlier ones, so the file order is already a valid order. The two halves are
independent of each other: the c-factor side (rounds 20–23, 25–34, 36) uses only round 1,
and the hedge families (rounds 3–19) never use the c-factor side. Round 24 (`tian_iff`)
is the only bridge: it uses rounds 4, 11, 16, 17 (the families) and 23 (`ccomp`), and
nothing uses round 24. Key edges: `Bow.chan`, `Bow.q_ne` and the `BowGen.kfac_lift*`
lemmas (rounds 3–4) are used by every family; `HedgeChain.ev` (round 7) and
`PathTree.b2z` (round 8b) are shared Bool/`ZMod 2` helpers; round 15 (`RootPath`)
builds on rounds 7, 8b, 9 (`Lrearr`) and 14 (`MultiRoot.MR`, `ext`); `CFactor.Q`,
`fill` and `kfac_congr` (round 20) are used by every later c-factor round.

**Public results in the file:** the definition `Identification.Identifiable` (round 1)
and `Identification.CFactor.tian_iff` (round 24). `verification/AuditV480.lean` also uses
`Identification.Bow.bowG` (round 3).

**Users outside the file** (all through `import PearlDoCalculus.Identification`):
`IdAudit` and `Verma` import it directly, `IdAlgo`, `Idc` and `Hedge/*` through
`IdAudit`, and `verification/AuditV423.lean` directly (deleted in v4.154, kept at tag `v4.152`). They use `Identifiable`,
`Bow.bowG`, `CFactor.ccomp`, `latStep`, `mem_ccomp`, `self_mem_ccomp` (round 23),
`IsLatClosed`, `Q_empty` (26), `ccomp_eq_of_mem` (27), `Reach` (32), `id_sound_anc`,
`id_sound_anc_blocks`, `ccomp_ind_X` (34), and for `Verma`: `Q` (20), `anc_factor`,
`marginal_restrict_ne_zero`, `subO` (21), `updX` (25), `verma_sum` (36). Keeping
`Identification.lean` as an import-only file means none of these files has to change.

**Proposed files** (folder `PearlDoCalculus/Identification/`, module
`PearlDoCalculus.Identification.<Name>`; line numbers refer to the file at v4.100):

| # | File | Rounds (current lines) | Lines | Contents | Imports |
|---|---|---|---|---|---|
| 1 | `Basic` | 1, 2 (1–245); 5 (916–1019); 11 without its last theorem (3032–3081) | ~420 | `Identifiable`; back-door, front-door, fully observed and observed parents give identifiability; transfer to subsets of `Y` (`joinYX`, `Identifiable.mono_Y`, `not_identifiable_of_mem`) | `Completeness` |
| 2 | `Bow` | 3, 4 (246–915) | ~670 | the bow graph is not identifiable, alone and inside any graph; the channel `Bow.chan` and the kernel-lifting lemmas `BowGen.kfac_lift*` used by all later families | `Basic` |
| 3 | `Hedge2` | 6 (1020–1373) | ~355 | the hedge with two latent variables | `Bow` |
| 4 | `HedgeChain` | 7 (1374–1965) | ~590 | hedge chains of any length; the helpers `ev`, `xx`, `xb`, `chan_symm` | `Bow` |
| 5 | `HedgeTemplate` | 8, 8b (1966–2684) | ~720 | the general template `HedgeTmpl.Tm` for hedge counter-models; latent paths with a directed tree to `y` (`PathTree`, with `b2z`, `z2b`) | `HedgeChain` |
| 6 | `LatentTree` | 9 (2685–3031); last theorem of 11 (3082–3093); 12 (3094–3301) | ~570 | latent trees; their versions for sets `Y` and sets `X` (`latentTree_not_identifiable_set`, `Tm.not_ident_X`, `latentTree_not_identifiable_XY`) | `HedgeTemplate` |
| 7 | `TwoRoot` | 13 (3302–3787) | ~490 | the c-forest with two roots | `Bow` |
| 8 | `RootPathModels` | 14 (3788–3862); 15 up to "A og C har samme fellesfordeling" (3863–4440) | ~655 | the configurations `MultiRoot.MR` and `RootPath.RP`, their graphs, the parity algebra and the three models | `LatentTree` |
| 9 | `RootPath` | rest of 15 and its corollary (4441–4884) | ~460 | the joint distributions and the bijection between the models; `rootPath_not_identifiable`, `multiRoot_not_identifiable` | `RootPathModels` |
| 10 | `RootTree` | 16, 17 (4885–5151) | ~270 | the latent path always exists (`rootTree_not_identifiable`); embedded hedges (`embedded_not_identifiable`) | `RootPath` |
| 11 | `Channel` | 18, 19 (5152–5793) | ~640 | the channel step and whole directed paths: a root may be replaced by the end of a path | `RootTree` |
| 12 | `CFactor` | 20–23 (5794–6455) | ~660 | Tian's lemmas 1 and 2, Tian's theorem for one `x`, the c-component is the least closed block | `Basic` |
| 13 | `TianIff` | 24 (6456–6729) | ~275 | `CFactor.not_ident_of_child` and the public `CFactor.tian_iff` | `RootTree`, `CFactor` |
| 14 | `CFactorSets` | 25–29 (6730–7335) | ~605 | Tian's theorem for sets `X`, factorization over many blocks, one sum per c-component, `Q[S]` is a causal effect | `CFactor` |
| 15 | `Identify` | 30–32 (7336–7813); 36 (8231–8281) | ~530 | `Q_marg`, Tian's lemma 11, IDENTIFY as `Reach`; the Verma sums used by `Verma.lean` | `CFactorSets` |
| 16 | `IdSound` | 33, 34 (7814–8230) | ~420 | the ID algorithm is sound for sets, with line 2 (`id_sound_anc`, `id_sound_anc_blocks`) | `Identify` |

Every line of the current file is in exactly one row. The imports form a DAG
(`Basic` ← `Bow` ← {`Hedge2`, `HedgeChain`, `TwoRoot`}, `HedgeChain` ← `HedgeTemplate`
← `LatentTree` ← `RootPathModels` ← `RootPath` ← `RootTree` ← {`Channel`, `TianIff`},
`Basic` ← `CFactor` ← {`TianIff`, `CFactorSets` ← `Identify` ← `IdSound`}).
Afterwards `Identification.lean` only imports the 16 files and has a module docstring
listing them, as `Hedge.lean` does now.

**Cuts that need care.**
- Round 15 (1 001 lines) is cut inside `namespace Identification.RootPath.RP`, before
  the block "A og C har samme fellesfordeling" (line 4441). File 8 ends with `end RP`,
  `end RootPath`, `end Identification`. File 9 reopens `namespace Identification`,
  `namespace RootPath`, repeats the round's `open HedgeChain (…)`, `open PathTree (…)`,
  `open LatentTree (Lrearr)`, the `variable {V …}` line, `open MultiRoot (…)`, then
  `namespace RP` and `variable {G : DAG V} {n : ℕ} (P : RP G n)`.
- Round 11 is split: its general part goes to `Basic`, its last theorem
  (`latentTree_not_identifiable_set`, which needs round 9) to `LatentTree`, each in its
  own `namespace Identification … end Identification` with the `variable` line.
  If the owner prefers whole rounds, round 11 stays whole in `LatentTree`; then
  `Channel`, `RootTree` and `TianIff` reach `mono_Y` and `joinYX` through `LatentTree`.
- Rounds 5, 11 and 36 are taken out of the middle or end of the file. This is safe:
  nothing uses round 5, and rounds 11 and 36 only use rounds that move with or before
  them.

**Order of the sub-steps** (one commit and one tag per file, as for `Hedge`): move the
files in the order of the table, 1 to 16. In each step the moved rounds leave
`Identification.lean`, the new file gets a short English module docstring, and
`Identification.lean` imports it and keeps the two `open` lines above at its top; also
add the module to `PearlDoCalculus.lean`, and update `HANDOFF.md` (file map) and
`README.md`. File 13 (`TianIff`) must come after 10 and 12. The last step (`IdSound`)
leaves `Identification.lean` as an import-only file.

**Open questions for the owner.**
- Is splitting round 11 between `Basic` and `LatentTree` acceptable (see above)?
- `Hedge2`, `TwoRoot`, `Channel`, `Parents` (round 5), the set versions in round 12 and
  most of `HedgeTemplate` are used by no public result and by no other file; only the
  chain `Bow` → `HedgeChain` → `PathTree` → `LatentTree` (`Lrearr`) → `MultiRoot` →
  `RootPath` → `RootTree` is needed, for `tian_iff`. They are listed as results in
  `HANDOFF.md` section 1, so this split keeps them; whether any of them count as
  superseded is a question for step 4.

### Proposal: split of `Completeness.lean` and `DSepSoundSkeleton.lean` (step 1, surveyed at v4.117)

#### `Completeness.lean`

**Survey.** 3 598 lines, one `namespace Completeness` around the whole file, imports
only `PearlDoCalculus.AdjAudit`. Lines 1-875 are not in sections: the models for
d-separation completeness (trek, chain); the headers are Norwegian ("Nivå 3a-3, runde N").
From line 876 on the file is a sequence of 11 closed `section`s, each starting with
`open DoCalculus` and none crossing another, so every cut falls between two sections.
The file has file-level `open PearlDoCalculus DAG DAG.CausalModel Classical` (line 14)
and `variable {V : Type*} [DecidableEq V] [Fintype V]` (line 18); both must be repeated
in every new file. There are no `private` declarations, instances, attributes or
`include`/`omit`. 40 `#print axioms` lines and 5 lines with `first` move with their code.

Blocks (lines at v4.117) and what each uses (declaration-level, read off by name; the
dependencies only point from later blocks to earlier ones):

| Block | Lines | Contents |
|---|---|---|
| A. trek | 17-271 | `ReachAvoid`, `trekModel`, `trek_not_condIndep`, `trek_of_open`, `dsep_complete_marginal` |
| B. chain | 272-839 | `Chain`, `chainModel`, `orpar`, witnesses, `chain_not_condIndep`, `chain_of_open`, `Chain.drop`, `chain_injective`, `dsep_complete` |
| C. dsep exact | 840-873 | `dsep_iff`, `dsepPath_iff`, `collider_explaining_away` (public: `dsep_iff`) |
| D. `Rule1` | 874-941 | `liftModel`, `doModel_lift`, `rule1_complete` |
| E. `Rule2` | 943-1072 | `marginal_eq_of_kfac`, `liftSub`, `lift_do_kfac`, `lift_do_do_kfac`, `rule2_complete` |
| F. `Rule3C` | 1074-1305 | `walk_to_isolated`, `dsep_isolated`, `rule3_complete_nonanc`, `rule3_complete_root` |
| G. `RuleIff` | 1307-1399 | `dsepSet_single`, `rule1_iff`, `rule2_iff`, `rule3_iff_nonanc` |
| H. `SetVersions` | 1401-1550 | `exists_restrict_eq`, `condIndep_symm`, `condIndep_drop_right`, `condIndep_single`, `dsepSet_iff`, `rule1_complete_set`, `rule1_iff_set` (public: `dsepSet_iff`, `rule1_iff_set`) |
| I. `Rule2Set` | 1552-1651 | `rule2_complete_set`, `rule2_iff_set` (public) |
| J. `Rule3Set` | 1653-1907 | `walk_to_isolated_set`, `dsep_isolated_set`, `rule3_complete_set_nonanc`, `rule3_iff_set_nonanc`, `rule3_complete_set_root` |
| K. `Rule3Copy` | 1909-2205 | `copyNet`, `ubObs`, `ubDo`, `rule3_complete_copy` |
| L. `Rule3ChainCopy` | 2207-2634 | `chainCopy`, `chain_support'`, `orpar_eq'`, `chain_z'`, `u1W`, `uDC`, `rule3_complete_chaincopy` |
| M. `Rule3Full` | 2636-2945 | `Chain.mono/cut/take/snoc`, `no_chain_of_dsep`, `rule3_complete_gap`, `rule3_complete`, `rule3_iff` |
| N. `Rule3SetFull` | 2947-3554 | `uDS`, `ptS`, `rule3_complete_chaincopy_set`, `Chain.cutset`, `set_gap_core`, `rule3_complete_set_gap`, `rule3_complete_set`, `rule3_iff_set` (public) |

Key edges: A is used by B, D-L (`ReachAvoid`, `reach_iff_parent`, `reach_not_mem`); B
(`Chain`, `chainModel`, `chain_of_open`, `chain_injective`, `chain_not_condIndep`) is used
by C and by every rule block; E (`marginal_eq_of_kfac`, `liftSub`, `lift_do_kfac`,
`lift_do_do_kfac`, `chain_noparent_false`) is used by F, H, I, J, K, L; F by G and M;
G (`dsepSet_single`) by M; H (`condIndep_single`) by I and J; J (`rule3_complete_set_root`)
by N; L by M and N; M (`Chain.take`, `Chain.snoc`, `no_chain_of_dsep`, `rank_le_of_reach`)
by N. **K (`Rule3Copy`) is used by no later block and by no other file** (it is
mentioned only in `HANDOFF.md` section 1 as one case of `rule3_iff`); it is a candidate
for step 4, but the split keeps it. Blocks H, I, J (set versions) are used by N only
through `rule3_complete_set_root`, and not at all by K, L, M.

**Public results in the file:** `dsep_iff`, `dsepSet_iff`, `rule1_iff_set`,
`rule2_iff_set`, `rule3_iff_set` (all in `public_statements.txt`; names stay because the
namespace `Completeness` is kept).

**Users outside the file:** only `Identification/Basic.lean` imports it directly (everything
else gets it through `Identification` or `Hedge`), plus `PearlDoCalculus.lean`. Outside
names used: `Completeness.marginal_eq_of_kfac` (about 40 uses), `liftSub` (about 39),
`dsep_isolated`, `exists_restrict_eq`, `dsep_iff`, `dsepSet_iff` and the `*_iff_set`
rules (verification files). Keeping `Completeness.lean` as an import-only file means no
user has to change.

**Proposed files** (folder `PearlDoCalculus/Completeness/`, module
`PearlDoCalculus.Completeness.<Name>`):

| # | File | Blocks | Lines | Imports |
|---|---|---|---|---|
| 1 | `Trek` | A (17-271), with the file header | ~270 | `AdjAudit` |
| 2 | `Chain` | B, C (272-873) | ~600 | `Trek` |
| 3 | `SingleRules` | D, E, F, G (874-1399) | ~530 | `Chain` |
| 4 | `SetRules` | H, I, J (1401-1907) | ~510 | `SingleRules` |
| 5 | `Rule3Copy` | K (1909-2205) | ~300 | `SingleRules` |
| 6 | `Rule3ChainCopy` | L (2207-2634) | ~430 | `SingleRules` |
| 7 | `Rule3Full` | M (2636-2945) | ~310 | `Rule3ChainCopy` |
| 8 | `Rule3SetFull` | N (2947-3554) | ~610 | `Rule3Full`, `SetRules` |

DAG: `Trek` ← `Chain` ← `SingleRules` ← {`SetRules`, `Rule3Copy`, `Rule3ChainCopy`};
`Rule3ChainCopy` ← `Rule3Full` ← `Rule3SetFull` (also `SetRules`). Every line is in
exactly one row. Afterwards `Completeness.lean` is import-only with a module docstring
listing the 8 files (as `Hedge.lean` and `Identification.lean`).

**Risks and cuts that need care.**
- No cut falls inside a `section` or inside a declaration; blocks D-G and H-J are
  merged by concatenating their `section ... end` pairs unchanged. Each new file needs the
  header `open PearlDoCalculus DAG DAG.CausalModel Classical`, `namespace Completeness`,
  the `variable` line, and `end Completeness`.
- Sections H-J are not used by K-M, so `SetRules` can be done at any time after
  `SingleRules`; `Rule3Full` must not import `SetRules` (and need not). If the build
  shows a missing name, add the import rather than moving code.
- The dependency edges above were read off by name matching (short names such as
  `trek`, `RZ` can give false positives); the build is the final judge.
- Cyclic imports cannot arise: all edges go from later blocks to earlier ones, and
  `Completeness.lean` is only imported (never importing the new files back) by
  `Identification/Basic.lean`.
- No deprecated aliases are needed: all declarations keep their names and namespace.
- The module docstring in the old file header (line 3, Norwegian, "Nivå 3a-1") describes
  only block A and moves to `Trek`; the other files need new docstrings (step 5 can
  translate; a short English one is enough for the split).
- Step 4 candidates noticed: `Rule3Copy` (K) unused. `chain_support'`, `orpar_eq'`,
  `chain_z'` (L) repeat `chain_support`, `orpar_eq_of_RZ`, `chain_z` (B, E) for the
  `chainCopy` model; they are duplicates only up to the model, so they stay for now.

**Order of the sub-steps:** one commit and one tag per file, in the order of the table
(1 to 8). `Completeness.lean` imports each new file as it appears and keeps the shared
header until the last step, which leaves it import-only. Also add each module to
`PearlDoCalculus.lean`, and update `HANDOFF.md` (file map) and `README.md` at the end.

#### `DSepSoundSkeleton.lean`

**Survey.** 2 096 lines, one `namespace PearlDoCalculus` (line 140 to 2096), no
`section`s. Lines 1-128 are one comment (`/-` not `/-!`, English but outdated: it is the
original "skeleton for the assistant" with `sorry` placeholders and instructions; the file
now has no `sorry`, the two hits are in this comment). Lines 129-149 are the imports
(after the comment), `set_option pp.proofs true`, `set_option autoImplicit false`,
`universe u v`, the `variable` lines (`V`, `α`, `G`), `open Classical` and
`open DAG DAG.CausalModel`. These must be repeated in every new file, with
`import PearlDoCalculus.CausalModel/DSeparation/Blocking/Walks/Reachability` and the
three Mathlib imports as needed (`SimpleGraph.Basic`, `Sym2`, `Clique` are only for layer
0 and 2/3). No `private`, instances or attributes; no `#print axioms`; 10 lines with
`first`. No public result is in this file. It builds the Lauritzen route for `DSepSound.dsep_sound`.

Blocks (lines at v4.117), by the layers named in the file:

| Block | Lines | Contents |
|---|---|---|
| L0 | 150-251 | `DAG.induce`, `ancestors`, `moralGraph`, `Separates`, `moral_family_clique` |
| L1a | 252-636 | casts and splits of assignments: `DAG.induce_parents_eq`, `extend_eq_iff`, `extendOverList_nil/cons`, `indicator_splits`, `joinInter`, `jointUpTo_zero/succ_apply`, `fullJoint_apply`, `restrict_cast_*` |
| L1b | 637-1053 | `extendOverList_factorizes_nil`, `jointUpTo_bind_collapse`, `extendOverList_factorizes'`, `jointUpTo_factorizes`, `extendOverList_apply_prod` |
| L1c | 1054-1354 | `kfac`, `jointUpTo_apply_prod`, `fullJoint_apply_prod`, `pinTo`, `marginal_ancestral_apply`, `CausalModel.restrictTo`, `marginal_eq_restricted_joint`, `Walk.lift`, `dsep_restrict` |
| L2 | 1355-1614 | `moral_edge_witness`, `moral_walk_of_open`, `dsep_of_moral_sep` (with the "Removed" note at 1567) |
| L3 | 1615-2094 | `ReachAvoiding`, `separator_partition`, `clique_one_sided`, `joint_splits`, `marginal_left/right_factor`, `tsum_*`, `assignmentSplit3`, `marginal_base_factor`, `condIndep_of_product_form` |

Dependencies: L0 ← everything; L1a ← L1b, L1c, L3; L1b ← L1c (`extendOverList_apply_prod`,
`jointUpTo_bind_collapse`) and L3 (`jointUpTo_factorizes`); L2 uses only L0 (so it is
independent of L1 and L3). Nothing outside the file uses `dsep_restrict` or
`dsep_of_moral_sep` by name; `DSepSound`, `SetSound` use `joint_splits`,
`condIndep_of_product_form`, `moralGraph`, `restrictTo`, `marginal_eq_restricted_joint`;
`Lauritzen` and `Counterexample` use `moralGraph`, `ancestors`; the rule files and
`Identification/*` use `kfac`, `ancestors` and `marginal_ancestral_apply` (`Identification`
files all reach it through `Completeness`). Importers of the file itself: `BayesBall`,
`Counterexample`, `PearlDoCalculus.lean` (`BayesBall` is imported by `Lauritzen`,
`Counterexample` by `Audit`). Keeping `DSepSoundSkeleton.lean` as an import-only file
means none of them changes.

**Proposed files** (folder `PearlDoCalculus/DSepSoundSkeleton/`):

| # | File | Blocks | Lines | Imports |
|---|---|---|---|---|
| 1 | `Basic` | header, L0 | ~100 (+ header) | `CausalModel`, `DSeparation`, `Blocking`, `Walks`, `Reachability`, Mathlib `SimpleGraph` files |
| 2 | `AssignmentCasts` | L1a | ~385 | `Basic` |
| 3 | `Factorizes` | L1b | ~420 | `AssignmentCasts` |
| 4 | `AncestralReduction` | L1c | ~300 | `Factorizes` |
| 5 | `Moralisation` | L2 | ~260 | `Basic` |
| 6 | `Separator` | L3 | ~480 | `Factorizes` |

DAG: `Basic` ← {`AssignmentCasts` ← `Factorizes` ← {`AncestralReduction`, `Separator`},
`Moralisation`}. The final comment (line 2094) goes to the import-only file. Every line
is in exactly one row.

**Risks and cuts that need care.**
- The header docstring (lines 1-128) is stale and misleading ("this file is a
  decomposition ... every `sorry`"). Do not move it verbatim into every file: leave it
  in the import-only file for the split steps and replace it in step 5 by a plain
  English docstring (what the layers prove, the Lauritzen route, why `jointUpTo` is
  used). A new docstring for each of the 6 files is short.
- `set_option pp.proofs true` is probably leftover from debugging; keep it in the new
  files only if a build fails without it (try removing it, since it only affects
  messages; if it changes nothing, that is a step 5 decision).
- The `variable {V : Type u} ... {α : V → Type v} {G : DAG V}` and `universe u v`
  must be repeated exactly, since declaration signatures depend on them. `open DAG
  DAG.CausalModel` must be kept (the old comment warns about `open DAG`, but the file
  opens it anyway).
- No cut is inside a declaration; the cuts L1a/L1b/L1c fall between lemmas of the same
  layer, so they are less natural than the layer boundaries; they are needed because L1 is
  about 1 100 lines. The edges from L1a to L3 (`assignmentSplit`, `restrict_cast_gen`,
  `eq_restrict_iff_eq_cast`, `fullJoint_apply`) mean `Separator` needs `AssignmentCasts`
  through `Factorizes`; this works transitively.
- Name matching used for the edges can miss uses through notation; the build decides.
- No deprecated aliases needed (names and namespace unchanged). The file name
  "Skeleton" is misleading now; a rename to a topic name belongs to step 6 and would
  need the three importers to change (a deprecated alias cannot stand in for a module),
  so leave it for now.
- 10 `first` lines move with their code (step 2).

**Order of the sub-steps:** `Completeness` and `DSepSoundSkeleton` are independent. Suggested
order: first `DSepSoundSkeleton` 1 to 6, then `Completeness` 1 to 8 (or the other way
round); one commit and one tag per file.

**Open questions for the owner.**
- Is it acceptable to keep the old file names (`Completeness.lean`, `DSepSoundSkeleton.lean`)
  as import-only files, so that no importer changes?
- Should `Rule3Copy` (unused, but listed in `HANDOFF.md`) get its own file now (as
  proposed) or be removed in step 4 first?

### Proposal: shared helpers (step 3, surveyed at v4.139)

**Method.** All 1 572 declarations in `PearlDoCalculus/` (there are no `private` ones)
were grouped by identical statement text, by equal short names in different files, and
by statement shape. Uses are counted with `grep -w` outside the defining line (exact for
distinctive names, approximate for short ones). Every claim "= Mathlib `X`" and every
"special case" claim marked *(checked)* was compiled in a scratch file with
`lake env lean`.

**Constraints found.**
- `Rule3Flag.setZ`, `Identification.CFactor.updX`, `Rule3.Z2`, `IdAlgo.ancIn`, `ccIn`,
  `identifyTop`, `Hedge.PM.Val`, `Val2`, `RO`, `DoCalculus.doModel`, `cutIn`, `cutOut`
  occur in the printed statements (`public_statements.txt`, `pp.fullNames`). They keep
  their full names; they may move only to another file with the same namespace.
- `lean_lib` builds only what `PearlDoCalculus.lean` imports, so every new file is
  imported by its first user and listed in `PearlDoCalculus.lean`.
- **Owner's decision (v4.141):** a moved or merged internal helper gets its final
  (Mathlib-style) name already in step 3, and every use is updated in the same commit.
  No deprecated alias is left for internal helpers. The "step 6 name" column below is
  that final name. Names in `public_statements.txt` (`setZ`, `updX`, `Rule3.Z2`, ...)
  stay as they are.

#### A. `ZMod 2` arithmetic (39 declarations: 24 `zmod2_*` in `Hedge`, 15 in `Identification`)

| Group | Declarations (file:line, uses) | Finding | Keep / step 6 name |
|---|---|---|---|
| A1 `x + x = 0` | `Hedge.zmod2_add_self` (Hedge/Tree:555, 9 uses in 6 files); `Identification.PathTree.two` (Identification/HedgeTemplate:466, 6 uses in 3 files); inline `show (1 : ZMod 2) + 1 = 0` (Hedge/ProductBias:413) | identical statements; Mathlib `CharTwo.add_self_eq_zero` *(checked)* | Mathlib; both old names aliases |
| A2 finite structure | `zmod2_univ` (ProductBias:64, 4; inline copy in `PM.pmf_two`, Roots:55), `zmod2_01` (:66, 12), `zmod2_cases` (:68, 1) | `zmod2_01` = Mathlib `zero_ne_one` | `ZMod2.univ_eq`, `ZMod2.eq_zero_or_eq_one` |
| A3 Bool and `ZMod 2` | `PathTree.b2z`, `z2b` (HedgeTemplate:459-460, ~95 / ~55 uses in 5 files), `b2z_z2b` (5), `eq_z2b` (14), `b2z_xor` (3), `b2z_inj` (3); `RootPath.RP.z2b_add` (RootPathModels:365, 1) | no duplicate, but one family spread over two namespaces; 4 files `open PathTree (...)` only for these | `ZMod2.ofBool`, `toBool`, ... |
| A4 solving `a = b + c` | `PM.zmod2_solve` (ParityModels:282, 3), `LatentTree.Lrearr` (LatentTree:49, 3), `RP.Z1`, `RP.Z2` (RootPathModels:363-364, 1 each), `zmod2_s0` (DoGapM2:71, 3), `zmod2_shift1` (DoGapM1:428, 2), `zmod2_one` (DoGapM2:311, 2), `zmod2_tele` (ObsEq:549, 1) | same idea, different shapes; `zmod2_shift1` is Mathlib `self_eq_add_left` up to `eq_comm` | keep side by side; `zmod2_solve`, `Lrearr` are the general ones |
| A5 cancelling rearrangements (all `by decide`) | Hedge: `zmod2_bab` (Product:65), `zmod2_l5`, `zmod2_l3` (Product:315, 317), `zmod2_cc`, `zmod2_pp` (DoGapM1:275, 456), `zmod2_g` (DoGapM2:175), `zmod2_tel`, `zmod2_geq` (ProductBias:186, 188), `zmod2_s4`, `zmod2_t1`, `zmod2_t0` (:332-336), `zmod2_ins`, `zmod2_fin`, `zmod2_fs`, `zmod2_ft` (:548-554); Identification: `PathTree.L1`-`L4` (HedgeTemplate:467-472). One use each. | `zmod2_t1 a c d e` is exactly `zmod2_l5 a 1 c d e`; `zmod2_t0` is `zmod2_s4` at `d = 0` and `zmod2_l3` is `zmod2_l5` at `b = d = 0`, each up to `add_zero`/`zero_add` | merge `t1` into `l5` (alias); keep `t0`, `l3` (`decide` is shorter than the derivation) next to the general form |

#### B. `PMF`

| Group | Declarations | Finding | Keep |
|---|---|---|---|
| B1 `pure` | `RootPath.RP.pure1`, `pure0` (RootPathModels:569, 573; 4 uses each, all in RootPath) | wrappers of Mathlib `PMF.pure_apply_self`, `PMF.pure_apply_of_ne` *(checked)* | Mathlib; aliases |
| B2 parity under an involution | `Hedge.map_flip_eq` (DoGapM1:431, 7), `Hedge.map_ratio` (DoGapM2:74, 6), `Hedge.map_congr_supp` (DoGapM2:299, 5); `pair_ratio`, `bias_step`, `bias_base` (ProductBias:71, 122, 156) | `map_flip_eq` is `map_ratio` with `k = 1` (same `hinv`, `hf`); `map_congr_supp` does not use `ZMod 2` (codomain can be any type) | `map_ratio`, `map_congr_supp` (generalised) move; `map_flip_eq` derived; the bias lemmas stay in `ProductBias` |
| B3 two-point distributions | `PM.pmf_two` (Roots:52, 3), `map_fst0`, `map_fst1`, `map_add0`, `map_add1` (ProductBias:93-113; 3, 1, 1, 3) | facts about `PMF (ZMod 2)`, `PMF (ZMod 2 × ZMod 2)` | move to `Util/ZMod2` |
| B4 generic maps | `Rule3Flag.map_some_apply`, `map_some_none` (Rule3Flag:21, 28; 2, 3), `Completeness.map_unif_ne_zero` (Completeness/Chain:66; 6 uses in 3 files) | generic, no twin in the project or in Mathlib found | move to `Util/PMF` |

#### C. `Finset`, iterates, `ENNReal`

| Group | Declarations | Finding | Keep |
|---|---|---|---|
| C1 iterates | `IdAlgo.iter_sup` (IdAlgo:39, 2), `Hedge.iter_mono` (Hedge/FromID:139, 2), `IdAlgo.iter_sub` (IdAlgo:29, 7 in 3 files) | `iter_sup` = Mathlib `Function.id_le_iterate_of_id_le`, `iter_mono` = `Function.monotone_iterate_of_id_le` *(checked)*; `iter_sub` has no direct twin | Mathlib for the first two; `iter_sub` to `Util/Finset` |
| C2 dead | `union_inter_distrib`, `disjoint_inter_of_disjoint` (DSepSoundSkeleton/AssignmentCasts:225, 232; 0 uses) | = `Finset.union_inter_distrib_right`, `Disjoint.mono` *(checked)* | delete in step 4 |
| C3 Mathlib one-liners | `CFactor.inter_erase_of_not_mem` (CFactor:357, 6), `Channel.hρW` (Channel:241, 3), `Channel.hYW` (Channel:237), `PM.filter_univ` (ObsEq:80, 4), `Hedge.exists_ne_of_sum_ne` (ParityModels:85, 3) | first three are `Finset.erase_inter` + `Finset.erase_eq_of_notMem`, `Finset.notMem_erase`, `(Finset.insert_erase h).symm.subset` *(checked)*; `filter_univ` is `simp`; no twin for `exists_ne_of_sum_ne` | `inter_erase_of_not_mem`, `exists_ne_of_sum_ne` to `Util/Finset`; the rest inline in step 7 |
| C4 cross-multiplication | `Rule3.cancel_aux` (Rule3:267, 1), `Idc.cross_cancel` (Idc:174, 1), `Rule3Flag.cancel_flag` (Rule3Flag:508, 2), `Rule3Flag.cancel_half` (:539, 1) | `cancel_aux` = `cancel_flag hdt h1.symm h2.symm (fun h => absurd h hd0)`, `cross_cancel` = `cancel_flag hdt r₁ r₂ (fun h => absurd h hd0)` *(checked)* | `cancel_flag` (most general) and `cancel_half` to `Util/ENNReal`; step 6 name `ENNReal.cross_cancel` |
| C5 summing over a split | the same `calc` (`tsum_eq_single` twice, `ENNReal.tsum_comm` twice) written out in `CFactor.marginal_factor` (CFactor:125), `CFactor.anc_factor` (:291), `CFactorSets.tsum_join2` (:189), `IdSound.tsum_updX` (:258), `Channel.tsum_ins`, `tsum_reindex` (:109, 125) | one generic lemma, *(checked)*: `tsum_eq_tsum_tsum_of_iff (J : A → B → C) (pA : C → A) (pB : C → B) (h : ∀ c a b, c = J a b ↔ a = pA c ∧ b = pB c) (F : C → ℝ≥0∞) : ∑' c, F c = ∑' a, ∑' b, F (J a b)`, 10 lines via `Equiv.tsum_eq` and `ENNReal.tsum_prod`; the fixed-observed-part versions follow with `tsum_ite_eq` | new lemma in `Util/ENNReal`; use sites rewritten in E |

Left where they are: the named inclusions `CFactor.subO`, `subOA`, `subA1`, `subA2`,
`CFactorSets.subT1`, `subT2` (readable names for proof terms inside `restrict`; `subO`
is also used 10 times in `Verma`), and `DAG.subset_union3_*` (CausalModel:165-179,
about 140 uses through `open DAG`).

#### D. Assignments, marginals, kernel factors

| Group | Declarations | Finding | Keep |
|---|---|---|---|
| D1 joining two assignments | `Idc.joinXZ` (Idc:23, 21), `joinXZ_left`, `joinXZ_right` (Idc:125, 132); `Identification.joinYX` (Identification/Basic:364, 6 in Basic and Channel), `joinYX_Y`, `joinYX_X` (:369, 376) | same body; `joinXZ` takes the sets explicitly, `joinYX` implicitly; `joinXZ_left` ≡ `joinYX_Y`; `joinYX_X` (needs `Disjoint`) is a special case of `joinXZ_right` (needs agreement on the overlap) | `joinXZ` and its lemmas to `Util/Assignment`; `joinYX a b := joinXZ _ _ a b`; step 6 name `Assignment.join` |
| D2 overwriting on a subset | `Rule3Flag.setZ` (Rule3Flag:459, 59), `Identification.CFactor.updX` (CFactorSets:43, 69) | same body: `updX U X a x' = setZ X Uᶜ a x'`; **both are in the public statements**, so both names stay | leave; at most define `updX` through `setZ` (prints the same), owner's call |
| D3 extension | `Completeness.exists_restrict_eq` (Completeness/SetRules:27, 4, also used by Identification/Basic) | generic | `Util/Assignment` |
| D4 marginal under restriction | `Identification.CFactor.marginal_restrict_ne_zero` (CFactor:379, 3), `Identification.marginal_pos_of_sub` (Basic:53, 6), `Identification.marginal_eq_of_sub` (Basic:47, 13), `DSepSound.restrict_injective_of_subset`, `marginal_restrict_of_injective` (DSepSound:179, 187; 4 each), `Adjustment.marginal_eq_of_subset'` (Adjustment:111, 17 in 3 files) | `marginal_pos_of_sub` re-proves `marginal_restrict_ne_zero` (plus `exists_restrict_eq`); `marginal_eq_of_subset'` is `(marginal_restrict_of_injective M hST (restrict_injective_of_subset hST hTS) u).symm` | general ones to `Util/Marginal`, the other two derived |
| D5 unfolding `kfac` | `Identification.Bow.kfac_eq` (Bow:225; `Fin 3`, `Bool`; 4), `BowGen.kfac_eqG` (Bow:463; `Bool`; 30 in 7 files), `DoAudit.kfac_univ` (DoAudit:18, about 95 in 21 files) | `kfac_eq` ⊂ `kfac_eqG` ⊂ the missing lemma for any `α`; `kfac_univ` is its case `S = univ` | add `kfac_of_mem` next to `kfac` (DSepSoundSkeleton/AncestralReduction:32); `kfac_eq`, `kfac_eqG` aliases (same explicit arguments); `kfac_univ` keeps its name |
| D6 `kfac` of `liftSub` | `Bow.kfac_lift`, `kfac_lift_do` (Bow:161, 168; `Fin 3`; 4, 2), `BowGen.kfac_liftG`, `kfac_lift_doG` (Bow:445, 452; `Bool`; 23, 18 in 8 files), `Hedge.kfac_liftα`, `kfac_lift_doα` (Hedge/Reduce:49, 55; any `α`; 2, 2) | three levels of generality, same proofs | the `α` versions next to `liftSub` (Completeness/SingleRules), the four others aliases |
| D7 extension by one vertex | `Identification.Channel.ins`, `ins_eq_iff` … `tsum_reindex` (Channel:54-135; `Bool`, `U ⊆ insert w T`); `Assignment.extend` (CausalModel:231), `extend_eq_iff` (DSepSoundSkeleton/AssignmentCasts:51) | similar, different generality | not merged; C5 shortens `Channel` |

#### E. Latent splits (the "three versions" of `HANDOFF.md` section 8)

`CFactor.fill` (CFactor:46, about 115 uses), `full2` with `full2_eq_iff`, `val1`
(CFactor:58-110, 19 uses), `full3` with `full3_iff`, `wal1`, `wal2` (CFactor:234-288,
19 uses), `CFactorSets.join2` with `join2_iff`, `tsum_join2`, `fill_join1`, `fill_join2`
(CFactorSets:162-235, 37 uses). Relation: `full3 U A S a w1 w2 = fill U A a (join2 U A S
w1 w2)` pointwise (the same case split); `full2` is `full3` at `A = univ` only up to
`U ∩ (univ ∩ S) = U ∩ S`, which is not definitional. Proposal: a new file
`Identification/LatentSplit.lean` (imports `Identification/Basic` and `Util/ENNReal`;
imported by `CFactor`) with `fill`, `join2` and its lemmas, the `sub*` inclusions, `updX`
and `upd_iff` (all still in namespace `Identification.CFactor`) and one split lemma from
C5. Then `full3` becomes `fill` of `join2` (or goes), `marginal_factor` and `anc_factor`
use the shared split, and `tsum_join2`, `tsum_updX` are one-line uses of C5. Expected
saving: about 150 lines.

#### F. Other duplicates

- **F1 parents of a closed set.** `TwoRoot.parOf` (TwoRoot:31, 7), `RootPath.RP.pOf`
  (RootPath:234, 8), `Channel.parOfA` (Channel:159, 1) have identical statements;
  `Bow.parB`, `BowGen.parB` (Bow:241, 552) are instances; inline copies in CFactor:297
  and AncestralReduction:214. Related: `CFactor.edge_of_par` (CFactor:121, 22),
  `Hedge.PM.mem_parents_iff` (ParityModels:372, 2) and 61 inline `simp [DAG.parents]`.
  Proposal: `@[simp] DAG.mem_parents` and `DAG.parents_subset_of_closed` in `DAG.lean`;
  the old names become aliases.
- **F2** `Identification.rank_le_of_reaches` (Identification/Basic:165, 2) duplicates
  `PearlDoCalculus.DAG.rank_le_of_reaches` (Reachability:61; `G` explicit there).
- **F3 bottom-up solution on a forest.** `LatentTree.LT.solN`, `M`, `ht_le`, `stab`,
  `uniq`, `sol_iff` (LatentTree:155-223) are verbatim copies of `RootPath.RP.*`
  (RootPathModels:291-359). They use only the fields `bp`, `ht`, `hht`. Proposal: one
  block with these three as parameters, in `LatentTree.lean`; both structures use it
  (about 70 lines saved).
- **F4 results, not helpers (for step 4).** `Channel.not_ident_of_sub` (Channel:526,
  `Bool`) is `Hedge.not_ident_of_subα` (Hedge/Reduce:66) at `α = Bool`.
- **F5 not merged.** The per-model APIs (`gA`, `NA`, `NA_x`, `mA`, `φ`, `φ_invol`,
  `full_map`, `obsEq`, `posA`, `doA`, `not_ident`, …) repeat in the 7 hedge-family
  structures of `Identification`. They are parallel developments, not shared helpers.
  Name clashes for step 6: `Walk.IsPath` / `Channel.IsPath`,
  `Completeness.chain_aux` / `HedgeChain.chain_aux`, `Rule3.Z1`, `Z2` / `RP.Z1`, `Z2`.

#### Module layout

| New file | Imports | Imported by (first users) | Contents |
|---|---|---|---|
| `Util/ZMod2.lean` | Mathlib only | `Identification/HedgeTemplate`, `LatentTree`, `Hedge/Tree` | A1-A5, B2 (`map_ratio`, `map_flip_eq`), B3 |
| `Util/PMF.lean` | Mathlib only | `Rule3Flag` | B1 (if not inlined), B4, `map_congr_supp` |
| `Util/ENNReal.lean` | Mathlib only | `Rule3` | C4, C5 |
| `Util/Finset.lean` | Mathlib only | `Identification/Basic` | `iter_sub`, `exists_ne_of_sum_ne`, `inter_erase_of_not_mem` |
| `Util/Assignment.lean` | `CausalModel` | `DSepSoundSkeleton/Basic` | D1, D3, `restrict_injective_of_subset` |
| `Util/Marginal.lean` | `Util/Assignment` | `DSepSoundSkeleton/Basic` | D4 |
| `Identification/LatentSplit.lean` | `Identification/Basic`, `Util/ENNReal` | `Identification/CFactor` | E |

Additions to existing files: `DAG.lean` (F1), `DSepSoundSkeleton/AncestralReduction`
(D5), `Completeness/SingleRules` (D6), `LatentTree` (F3). No cycles are possible: four
new files import only Mathlib, `Util/Assignment` imports only `CausalModel` (which
imports `DAG` and `DSeparation`), and `LatentSplit` only `Identification/Basic`.

#### Commit plan (one tag each; move verbatim first, aliases in the same commit)

1. `Util/ZMod2`: A1-A5, B2, B3; aliases `PathTree.two`, `zmod2_add_self` (if Mathlib
   is used), `zmod2_t1`. About 12 files.
2. `Util/PMF`: B1, B4, `map_congr_supp`.
3. `Util/ENNReal`: C4 (with `cancel_aux`, `cross_cancel` as corollaries) and the C5 lemma
   (no use sites yet).
4. `Util/Finset`: C1 (uses switched to Mathlib, aliases), C3.
5. `DAG.lean`: F1, F2.
6. `Util/Assignment`, `Util/Marginal`: D1, D3, D4.
7. `kfac` lemmas: D5, D6.
8. `Identification/LatentSplit`, moved verbatim.
9. Latent splits through C5: `marginal_factor`, `anc_factor`, `tsum_join2`, `tsum_updX`,
   `Channel.tsum_reindex`; `full3` through `fill` and `join2`.
10. F3 (forest solution).

Each step also updates `PearlDoCalculus.lean`, the file map in `HANDOFF.md` and
`README.md`. Step 3 is done after 10.

**Owner's decisions (v4.141).**
- Final names now: moved helpers get their final namespace and name in step 3, all uses
  are updated in the same commit, and no deprecated aliases are kept for internal
  helpers (see also `CLAUDE.md`). Where the plan above says "alias", read "rename and
  update the uses".
- D2: `setZ` and `updX` stay two definitions. Add a lemma `updX_eq_setZ`
  (`updX U X a x' = setZ X Uᶜ a x'`) with a comment saying why both exist (both occur
  in the public statements); this goes with step 3.6 (`Util/Assignment`).
- A5: step 7 may replace a `decide` proof only where the proof gets clearly shorter and
  not slower to build.

### Proposal: renaming (step 6, surveyed at v4.171)

**Method.** The full list of declarations (1 727 after removing compiler-generated names)
was read off the compiled environment (`Lean.Environment.constants`, filtered to the
modules `PearlDoCalculus.*`), with namespace and module of each. Uses are counted with
`grep -w` over every `.lean` file, `verification/` included (occurrences / files,
definition line included; approximate for short names). Checked against the Lean 4 and
Mathlib naming conventions: `UpperCamelCase` for types, structures, `Prop`-valued
definitions and namespaces; `lowerCamelCase` for other definitions; `snake_case` for
theorems, with `UpperCamelCase` names written in `lowerCamelCase` inside them
(`dSeparated_…`), `of` instead of `imp`, `notMem` instead of `not_mem` (Mathlib 2025),
`subset` instead of `sub`.

**Excluded (names frozen).** These keep their names, because they are public results or
occur in `verification/public_statements.txt` or in the frozen
`verification/AuditV480.lean` (which must still run after step 8, so an alias is no way
out):
- the public results and definitions of the list at the top of this file;
- the names in the printed statements: `PearlDoCalculus.DAG` (with `edge`, `DSeparated`),
  `DAG.CausalModel` (with `marginal`, `CondIndep`), `Assignment`, `Assignment.restrict`,
  `DoCalculus.doModel`, `cutIn`, `cutOut`, `Rule3.Z2`, `Rule3Flag.setZ`,
  `SetSound.DSeparatedSet`, `IdAlgo.ancIn`, `ccIn`, `identifyTop`, `Hedge.rootsIn`,
  `Hedge.CConn`, the fields of `Hedge.IsHedge` (`sub`, `ne`, `rootF`, `rootF'`, `out`,
  `meet`, `anc`, `conn`, `conn'`), `Hedge.PM.Val`, `Val2`, `RO`, `Idc.IdentifiableCond`,
  `Adjustment.BackdoorCriterion`, `FrontdoorCriterion`, `Identification.CFactor.ccomp`,
  `updX`, `Verma.vG`, `vermaF`;
- from `AuditV480.lean`: `Identification.Bow.bowG` and `IdAlgo.bow_idCheck`.

As a consequence the namespaces `Hedge`, `Hedge.PM`, `IdAlgo`, `Identification`,
`Identification.CFactor`, `Identification.Bow`, `DoCalculus`, `Rule3`, `Rule3Flag`,
`SetSound`, `Completeness`, `Adjustment`, `Idc`, `Verma` and `PearlDoCalculus.DAG` stay.
Opaque ones among them (`PM` = parity models, `Rule3Flag` = the flag model of rule 3) are
explained in their module docstrings; that is the only remedy.

**Overall finding.** The names are mostly consistent already (step 3 gave the shared
helpers Mathlib-style names). Two layers exist side by side: the basic theory (DAGs,
models, walks, the Lauritzen route) lives under `PearlDoCalculus`, every later topic in a
top-level namespace named after its file or folder. Both layers contain frozen names, so
they cannot be merged; the proposal keeps them and documents the rule in `HANDOFF.md`
section 4. The real problems are few: one file without a namespace, structure names that
are two-letter abbreviations, several different predicates all called `Reach…`, a handful
of names that break the conventions or describe the history of the project, and the
module name `DSepSoundSkeleton`.

#### A. Files and modules

Modules cannot have deprecated aliases. A renamed module either leaves the old file
behind as an import-only shim (`import PearlDoCalculus.<New>` and a comment, deleted in
step 8) or all importers change in the same commit. Since `AuditV480.lean` and
`PublicStatements.lean` only import the root `PearlDoCalculus`, no frozen file depends on
a module name. Proposal: update every importer in the same commit, no shim (the importers
are all in this repository).

| # | Old | New | Reason | Touches |
|---|---|---|---|---|
| A1 | `DSepSoundSkeleton.lean` and `DSepSoundSkeleton/{Basic, AssignmentCasts, Factorizes, AncestralReduction, Moralisation, Separator}` | **option (a):** folder `Soundness/` with these six files plus `BayesBall`, `Lauritzen`, `DSepSound`, `WalkPath`, `SetSound`, `Counterexample` moved in (`Soundness/BayesBall`, …); `Soundness.lean` import-only. **option (b):** only the folder becomes `DSepSound/` and the import-only `DSepSoundSkeleton.lean` goes (`DSepSound.lean` stays as the theorem file next to the folder, as `Hedge.lean` and `Hedge/`) | "Skeleton" is the history of the file (the original `sorry` skeleton); the content is the Lauritzen route to soundness. Option (a) mirrors `Completeness/` and puts the whole soundness side in one folder | (a) 12 files moved, about 25 import lines, 36 Lean lines and about 10 lines of `README.md`, `HANDOFF.md`, `EXPLAINER.md` that name the modules; (b) 6 files, about 12 import lines, the same docs. Namespaces unchanged |
| A2 | `Completeness/Rule3Full`, `Completeness/Rule3SetFull` | `Completeness/Rule3Iff`, `Completeness/Rule3SetIff` | "Full" refers to the order in which the cases were done; the files prove `rule3_iff` and `rule3_iff_set` | 2 files, 4 import lines, 18 Lean lines, 6 doc lines |
| A3 | `Audit`, `DoAudit`, `AdjAudit`, `IdAudit` (namespaces of the same names) | `Examples/DSeparation`, `Examples/Rule2`, `Examples/Backdoor`, `Examples/IdRecursion` (namespaces `Examples.DSeparation`, …) | "Audit" refers to the audit rounds; the files are sanity examples. **Blocker:** they sit inside the import spine (`Rule3Flag` ← `DoAudit` ← `Audit` ← `Counterexample`, `Completeness/Trek` ← `AdjAudit`, `IdAlgo` ← `IdAudit`, and `IdAlgo` names `IdAudit.idG`). Renaming them only makes sense if they first become leaves of the import graph (their importers import the real modules instead), which may need a build or two to find the right imports | 4 files, 9 import lines, about 115 Lean lines (`Audit` alone 81), about 38 doc lines |
| A4 | — (no change) | — | `Rule3Flag`, `Rule3ChainCopy`, `BackdoorGeneral`, `Hedge/DoGapM1`, `DoGapM2`, `SimpleConfounderObservable`, `FrontDoorObservable` name the mathematics (the flag model, the copy model, the do-gap of models `M1`, `M2`); keep | — |

#### B. Namespaces and structures

| # | Old | New | Reason | Touches |
|---|---|---|---|---|
| B1 | `BayesBall.lean` declares everything at the root (`BallDir`, `BallState`, `bbNext`, `bbReachable`, `incomingOfDir`, `instFintypeBallDir`, and four theorems) | namespace `BayesBall` (as `Lauritzen`, `DSepSound`, `WalkPath`) | the only file without a namespace; `bbReachable` at the root is a clash waiting to happen | 10 declarations, about 45 lines in `BayesBall`, `Lauritzen`, `SetSound` |
| B2 | `Identification.HedgeTmpl.Tm` (57 API declarations) | structure `Identification.HedgeTemplate` (API in the same namespace) | two abbreviations for one name; the file is already `HedgeTemplate` | 16 + 10 lines, 2 files |
| B3 | `Identification.PathTree.PT` (46) | structure `Identification.PathTree` | Mathlib style: the structure carries the namespace's name | 5 lines, 1 file |
| B4 | `Identification.LatentTree.LT` (39) | structure `Identification.LatentTree` | same | 8 lines, 2 files |
| B5 | `Identification.MultiRoot.MR` (23) | structure `Identification.MultiRoot` | same | 14 lines, 2 files |
| B6 | `Identification.RootPath.RP` (103) | structure `Identification.RootPath` | same | 21 lines, 4 files |
| B7 | `Identification.RootTree.RT` (34) | structure `Identification.RootTree` | same | 17 lines, 3 files |
| B8 | `Identification.HedgeChain.Chain` (68) | structure `Identification.HedgeChain` | same; also removes the clash with `Completeness.Chain` | 5 lines, 1 file |
| B9 | `Identification.BowGen` | `Identification.BowEmbedded` | "Gen" is opaque; the namespace is the bow inside an arbitrary graph (`bow_not_identifiable_general`) | 36 lines, 4 files |

For B2-B8 the old outer-namespace theorems become theorems of the structure's namespace;
where they are about one configuration they can shed the repeated prefix:
`RootPath.rootPath_not_identifiable` → `RootPath.not_identifiable`,
`LatentTree.latentTree_not_identifiable` → `LatentTree.not_identifiable`,
`PathTree.pathTree_not_identifiable` → `PathTree.not_identifiable`,
`RootTree.rootTree_not_identifiable` → `RootTree.not_identifiable`,
`MultiRoot.multiRoot_not_identifiable` → `MultiRoot.not_identifiable`,
`HedgeChain.chain_not_identifiable` → `HedgeChain.not_identifiable`, if their argument is
the structure (all six take it as their first explicit argument, so `P.not_identifiable`
works). Three structures already have a lemma `not_ident` (`Chain.not_ident`,
`Tm.not_ident`, `RP.not_ident`: the counter-models exist, stated for the model pair);
next to `not_identifiable` that name is confusing, so they become `not_ident_models`.
These theorems are listed in `HANDOFF.md` section 1, so they get deprecated aliases (see
policy below).

#### C. Definitions

| # | Old | New | Reason | Uses |
|---|---|---|---|---|
| C1 | `Lauritzen.Reach` | `Lauritzen.BallReaches` | five different predicates are called `Reach…`; this one is Bayes-ball reachability | 6 / 2 (the other 47 occurrences of `Reach` are C4) |
| C2 | `SetSound.ReachS` | `SetSound.BallReachesSet` | same | 9 / 1 |
| C3 | `Completeness.ReachAvoid` (directed path, vertices after `s` outside `Z`) and `PearlDoCalculus.ReachAvoiding` (undirected walk avoiding `Z`) | `Completeness.ReachesAvoiding` and `PearlDoCalculus.ReachableAvoiding` | near-identical names for different notions; follow `DAG.Reaches` (directed) and Mathlib's `SimpleGraph.Reachable` (undirected) | 93 / 5 and 6 / 2 |
| C4 | `Identification.CFactor.Reach` (the inductive predicate of IDENTIFY) | `CFactor.IdentifyDerives` (owner's choice of word) | it is a derivation of IDENTIFY, not reachability | 47 / 5 |
| C5 | `Completeness.RZ` | `Completeness.ReachesParentAvoiding` | opaque two-letter name of a `Prop` | 60 / 4 |
| C6 | `Lauritzen.NotZAnc` | `Lauritzen.NotAncOf` (or leave) | word order; low priority | 10 / 2 |
| C7 | `DSepSound.A_closed` | `ancestors_closed` in `DSepSoundSkeleton/Basic` (namespace `PearlDoCalculus`) | it is the general fact that ancestor sets are closed under parents (its unused twin `ancestors_parent_closed` was deleted in v4.170); the name refers to a local variable `A` | 8 / 5 |
| C8 | `DSepSound.union_subset_A`, `marginal_eq_of_subset_A`, `Lauritzen.mem_A_cases`, `SetSound.mem_A_cases_set` | `subset_ancestors_insert`, `marginal_eq_of_subset_ancestors`, `mem_ancestors_cases`, `mem_ancestors_cases_set` | same (names of a local variable) | 2, 5, 2, 2 |
| C9 | per-model `hsA`, `hsB` (Bow, BowGen, HedgeChain, HedgeTemplate, LatentTree, RootPathModels, …) | `gA_parents_subset`, `gB_parents_subset` | lemma names that look like hypotheses | 30 / 8 and 18 / 5 |

Not proposed (recorded so that the question is settled): the parity-model vocabulary of
`Hedge/*` (`nxt` 145 uses, `inc` 131, `OF` 112, `noise` 101, `Yb` 80, `tp` 75, `AY` 71,
`ov`, `lb`, `sb`, `sbV`, `rd`, `kk`, `ix`, `cst`, `CH`, `NX`, `EF`, `sh`, `tsel`, `δ`,
`TC`, `bIn`, `AO`, `AXo`, `fS`, `gS`, `nreach`, `nrI`, `phiC`, `parR`, `phiS`, `psiS`,
`tauS`, `sig`, `tau2`, `psi2`, `MP`, …) and the per-model API of the hedge families
(`gA`, `NA`, `mA`, `φ`, `A_x`, `NA_x`, `ev` with 310 uses, …). They are the notation of
the proof plan in `HANDOFF.md` section 2 (which uses `nxt` 21 times, `Yb` 17, `parR` 15,
`OF` 13, …); renaming them means rewriting that section too, and would touch well over
1 500 lines. Instead: a glossary table (name → meaning) in the module docstring of
`Hedge.lean`, and one in `Identification.lean` for the per-model API (step 6 or 7,
comments only). Likewise kept: `CFactor.Q` (Tian's `Q[S]`), `Rule3.Z1` (pairs with the
frozen `Z2`), the witness assignments of the completeness models (`u0C`, `u1C`, `wC`,
`u1W`, `uDC`, `uDS`, `ptS`, `ccPt`, `uB`, `wXY`; each local to one file, each with a
docstring), and the `h…` fields of the hedge-family structures.

#### D. Lemmas

| # | Old | New | Reason | Uses |
|---|---|---|---|---|
| D1 | `not_blockedAux_imp_open`, `bbReachable_imp_not_blocked`, `bbReachable_imp_open_walk`, `DSeparated_imp_not_bbReachable` (`BayesBall`), `start_imp_bwd` (`Rule3`) | `open_of_not_blockedAux`, `not_blocked_of_bbReachable`, `exists_open_walk_of_bbReachable`, `not_bbReachable_of_dSeparated`, `bwd_of_start` (done as `blockedAux_bwd_of_start`, v4.173) | Mathlib: `of`, not `imp`; `DSeparated` in lowerCamelCase | 2, 3, 5, 6, 2 (the first four go with B1) |
| D2 | `flag_kernel_some_not_mem`, `kfac_doModel_of_not_mem`, `parents_cutIn_of_not_mem`, `reach_not_mem`, `not_mem_of_notZAnc` | `…_notMem`, `notMem_of_…` | Mathlib 2025 spelling, already used by the step-3 helpers (`fill_updX_apply_of_notMem`) | 3, 2, 2, 19, 6 |
| D3 | `anc_sub`, `cc_sub` (`IdAlgo`), `parents_cutIn_sub`, `doModel_marginal_of_sub` | `ancIn_subset`, `ccIn_subset`, `parents_cutIn_subset`, `doModel_marginal_of_subset` | `subset`, and the full name of the definition | 6, 6, 2, 16 / 9 |
| D4 | primed variants: `chain_support'`, `orpar_eq'`, `chain_z'` (`Rule3ChainCopy`) | `chainCopy_support`, `chainCopy_orpar_eq`, `chainCopy_z` | they are about the model `chainCopy`, not variants of the originals | 6, 6, 4 |
| D5 | other primes: `doModel_comp_marginal'`, `extendOverList_cons'`, `extendOverList_factorizes'`, `reach_y'`, `SimpleConfounderModel.backdoor_adjustment'` | a name that says the difference (decided per lemma after reading it) | a prime says nothing | 7, 8, 4, 2, 1 |
| D6 | `IdAlgo.idAudit_check`, `IdAlgo.idAudit_idCheck`, `IdAlgo.id_audit'`, `IdAudit.id_audit`, `IdAudit.tian_sets_fails` | `identifyTop_idG`, `idCheck_idG`, `idG_identifiable_of_idCheck`, `IdAudit.idG_identifiable`, `IdAudit.idG_not_tian_sets` (namespaces follow A3) | history names ("audit"); `IdAlgo.bow_idCheck` already follows this pattern | 3, 2, 5, 12, 4 |
| D7 | `Rule3Flag.rule3_gen` (rule 3 without `X`) | `Rule3Flag.rule3_core` (as `DoCalculus.rule2_core`) | `rule3_gen` and `rule3_general` differ by three letters and mean different things | 6 / 2 |
| D8 | `CFactor.tian_identifiableX`, `CFactor.tian_identifiable_ccompX` | `tian_identifiable_set_of_closed`, `tian_identifiable_set_ccomp` | the rest of the project marks set versions by `_set` (`rule1_iff_set`, `dsep_sound_set`, `tian_identifiable_sets`), not by a capital suffix | 3, 3 |
| D9 | `Completeness.chain_aux`, `HedgeChain.chain_aux` | a name for what each proves (per lemma) | `_aux` says nothing, and the two clash in meaning | 5 / 2 |

Every name in D is used only inside the project. In D1-D3 the new name is mechanical;
in D5, D9 it is chosen when the lemma is read.

#### Policy for old names

**Decided by the owner (v4.172): no `@[deprecated]` aliases in step 6.** Every renamed
internal name, including the theorems listed in `HANDOFF.md` section 1 and the
structures B2-B8, is renamed at once; every use and `HANDOFF.md` are updated in the same
commit (rule added to `CLAUDE.md`). Names in `public_statements.txt` and in
`AuditV480.lean` are not renamed. The options as surveyed are kept below for the record.

`CLAUDE.md` said: a name that moves keeps a `@[deprecated]` alias until step 8; the
v4.141 exception (rename at once, no alias) covered only the helpers moved in step 3.
Proposed per group:
- **Excluded names** (above): unchanged, no question.
- **Results listed in `HANDOFF.md` section 1** (B2-B8 theorems such as
  `RootTree.rootTree_not_identifiable`, `HedgeChain.chain_not_identifiable`; D7
  `rule3_gen` is not listed, `rule3_general` is and stays): `@[deprecated] alias`
  with the old name until step 8, as `CLAUDE.md` says.
- **Structures B2-B8**: an alias for the type itself is possible
  (`@[deprecated] abbrev LatentTree.LT := LatentTree`), but not for the API reached
  through dot notation (`P.solN` works after the rename without any alias; qualified uses
  `LT.foo` would each need their own alias). Proposal: an alias for the structure only,
  none for its API (all qualified uses are updated in the same commit).
- **Everything else (B1, B9, C, D, and the modules of A)**: internal, used only in this
  repository. **The owner must decide:** either (i) `@[deprecated]` aliases as
  `CLAUDE.md` says (about 80 alias lines, all removed again in step 8; with every use
  updated they produce no warnings), or (ii) extend the v4.141 exception to step 6, that
  is rename and update every use in the same commit, no alias. Recommendation: (ii), since
  there is no user outside the repository and step 8 would delete the aliases anyway.

#### Commit plan (one tag each, each `scripts/check.sh` clean)

1. B1 + D1: `BayesBall` into namespace `BayesBall`, the `_imp_` lemmas renamed.
2. D2 + D3: `notMem`, `subset` spellings.
3. B8 (`HedgeChain`), 4. B2 + B3 (`HedgeTemplate`, `PathTree`), 5. B4 (`LatentTree`),
   6. B5 + B6 (`MultiRoot`, `RootPath`), 7. B7 (`RootTree`), 8. B9 (`BowEmbedded`) and C9
   (`hsA`, `hsB` in every family): one commit per family, each with the
   `*_not_identifiable` shortening (no aliases).
9. C1-C6: the `Reach…` predicates, with C4 named `IdentifyDerives` (largest: `ReachAvoid` 93, `RZ` 60, about 230 lines).
10. C7 + C8: ancestor-set lemmas of the soundness route.
11. D4-D9: primes, history names, `rule3_core`, `_set` suffixes, `_aux`.
12. A2: `Rule3Iff`, `Rule3SetIff`.
13. A1, option (a): the folder `Soundness/` with the five remaining files of
    `DSepSoundSkeleton/` (`Moralisation` was deleted in v4.172) and `BayesBall`,
    `Lauritzen`, `DSepSound`, `WalkPath`, `SetSound`, `Counterexample`; `Soundness.lean`
    import-only; with `README.md`, `HANDOFF.md` (file map, section 4) and `EXPLAINER.md`.
14. `HANDOFF.md` section 4 gets a short paragraph on the naming scheme (the two layers,
    one namespace per topic, structures named as their namespace), and the glossaries of
    section C go into `Hedge.lean` and `Identification.lean` (comments only).
15. A3, last: first make the example files leaves of the import graph (one commit), then
    rename them to `Examples/*` (one commit). If the import rewiring fails more than
    twice, the old names stay and the progress log says why.

Commit 0 (v4.172) records the owner's decisions and deletes `Moralisation` (question 4).

No commit is expected to touch more than about 300 lines, except 9 (about 230 lines) and
13 (file moves; few changed lines, but many paths in the documentation).

#### Open questions for the owner (all answered, v4.172)

Answers: 1. (ii), no aliases, also not for the theorems of `HANDOFF.md` section 1.
2. Option (a), folder `Soundness/`. 3. Yes, as the last commit (15 above); if the import
rewiring fails more than twice, keep the old names and log it. 4. Delete `Moralisation`
with its unused lemmas, remove its two `#print axioms` lines from
`verification/AxiomCheck.lean`, translate that file's header, and delete
`verification/Axioms.lean` if nothing refers to it (done in v4.172; the frozen
`AuditV480.lean` keeps its Norwegian header). 5. `IdentifyDerives`. 6. Yes: keep the
vocabulary, add the glossaries. 7. Keep the step-3 helpers in the Mathlib namespaces.

The questions as asked:

1. Policy for internal names: aliases (i) or the v4.141 exception extended to step 6 (ii)?
2. A1: folder `Soundness/` with the whole soundness side (a), or only
   `DSepSoundSkeleton/` → `DSepSound/` (b)? Or keep `DSepSoundSkeleton`?
3. A3: should the audit files become `Examples/*`, including the import rewiring, or keep
   their names?
4. `DSepSoundSkeleton/Moralisation` (v4.170): keep it as the converse of the graph step,
   or delete it with the two `#print axioms` lines in `verification/AxiomCheck.lean`? It
   decides whether A1 moves five or six files. (`AxiomCheck.lean` also still has a
   Norwegian header; may it be translated?)
5. C4: which word for the derivations of IDENTIFY (`IdentifyDerives`, `Derivable`, or
   keep `Reach`)?
6. Is it right to keep the `Hedge/*` and hedge-family vocabulary and add glossaries
   instead of renaming (section C, "Not proposed")?
7. The step-3 helpers in the Mathlib namespaces `PMF`, `ENNReal`, `Finset`
   (`PMF.pure_apply_of_eq`, `ENNReal.cross_cancel`, `Finset.iterate_subset`, …) could clash
   with future Mathlib names when Mathlib is updated. Keep them there (dot notation works,
   as Mathlib intends), or move them under `PearlDoCalculus`? Recommendation: keep.

## Progress

The agent (`.claude/agents/pearl-cleanup.md`) marks each item when its tag is pushed.
Write `blocked:` and the reason if an item had to be reverted.

- [x] 1. Split `Hedge.lean` (done v4.99; `Hedge.lean` now only imports `Hedge/*`)
  - [x] `Hedge/Defs` (`rootsIn`, `CConn`, `IsHedge`), v4.86
  - [x] `Hedge/FromID` (H2: `Stuck` … `idCheck_false_hedge`, `bow_hedge`), v4.87
  - [x] `Hedge/Tree` (`nxt` … `hedge_spanning`, `ParTree`, `inc_inj`, `inc_surj`), v4.88
  - [x] `Hedge/Reduce` (`not_ident_of_subα`, `keepDAG`, `hedgeKeep`), v4.89
  - [x] `Hedge/ParityModels` (`marginal_eq_of_invol`, `PM.Val`, `PM.M`, `PM.Good`, `PM.sb_read`), v4.90
  - [x] `Hedge/ObsEq` (`PM.sh`, `PM.phiS`, `PM.tele`, `PM.joint_phiS`, `PM.marg_eq`), v4.91
  - [x] `Hedge/Positivity` (`PM.noise_pos`, `PM.sbV_base`, `PM.pos_M1`), v4.92
  - [x] `Hedge/DoGapM1` (`nrI_rec`, `PM.psiS`, `PM.joint_psi`, `PM.parR_half`), v4.93
  - [x] `Hedge/DoGapM2` (`ParTree.iff_root`, `map_ratio`, `PM.cross_edge`, `PM.parR_three`), v4.94
  - [x] `Hedge/Roots` (H3: `PM.not_ident_PM`, `PM.mkData`, `PM.hedge_not_ident`), v4.95
  - [x] `Hedge/Tails` (`anc_child_in`, `AY`, `tp`, `tp_reaches`, `tI`, `tI_rec`, `sum_tI_Y`), v4.96
  - [x] `Hedge/Product` (`PM.MP`, `PM.marg2_eq`, `PM.pos2`, `PM.psi2`, `PM.Yb_half`), v4.97
  - [x] `Hedge/ProductBias` (`bias_step`, `bias_base`, `PM.Yb_tele`, `PM.sig`, `PM.tau2`, `PM.Yb_biased`), v4.98
  - [x] `Hedge/Complete` (`PM.not_ident2`, `PM.hedge_data`, `PM.hedge_not_ident_Y`, `idCheck_iff`); `Hedge.lean` is a thin import file, v4.99
- [x] 1. Split `Identification.lean`
  - [x] Survey and proposal (section *Proposal: split of `Identification.lean`*), v4.101
  - [x] `Identification/Basic` (rounds 1, 2, 5 and the general part of 11), v4.102
  - [x] `Identification/Bow` (rounds 3 and 4), v4.103
  - [x] `Identification/Hedge2` (round 6), v4.104
  - [x] `Identification/HedgeChain` (round 7), v4.105
  - [x] `Identification/HedgeTemplate` (rounds 8 and 8b), v4.106
  - [x] `Identification/LatentTree` (rounds 9, rest of 11, 12), v4.107
  - [x] `Identification/TwoRoot` (round 13), v4.108. It needs only `Bow`, as proposed; `Identification.lean` now imports `LatentTree` and `TwoRoot` explicitly, since the rest needs `LatentTree`.
  - [x] `Identification/RootPathModels` (round 14, first part of round 15 up to "A og C har samme fellesfordeling"), v4.109. Imports `LatentTree`. Namespaces closed at the cut and reopened in `Identification.lean`.
  - [x] `Identification/RootPath` (rest of round 15 and its corollary), v4.110. Imports `RootPathModels`; `Identification.lean` imports it as well as `LatentTree`, `RootPathModels` and `TwoRoot`.
  - [x] `Identification/RootTree` (rounds 16 and 17), v4.111. Imports `RootPath`; `Identification.lean` imports it too.
  - [x] `Identification/Channel` (rounds 18 and 19), v4.112. Imports `RootTree`; `Identification.lean` imports it too.
  - [x] `Identification/CFactor` (rounds 20 to 23), v4.113. Imports `Basic` only; `Identification.lean` imports it.
  - [x] `Identification/TianIff` (round 24, `tian_iff`), v4.114. Imports `RootTree` and `CFactor`; `Identification.lean` imports it.
  - [x] `Identification/CFactorSets` (rounds 25-29), v4.115. Imports `CFactor`; `Identification.lean` imports it.
  - [x] `Identification/Identify` (rounds 30-32 and 36), v4.116. Imports `CFactorSets`; `Identification.lean` imports it. Round 36 does not depend on rounds 33-34.
  - [x] `Identification/IdSound` (rounds 33 and 34), v4.117. Imports `Identify`; `Identification.lean` is now an import-only file importing all 16 files. Split of `Identification.lean` complete.
- [x] 1. Split `Completeness.lean`
  - [x] Survey and proposal (section *Proposal: split of `Completeness.lean` and `DSepSoundSkeleton.lean`*)
  - [x] `Completeness/Trek`, v4.125. `Completeness.lean` imports it.
  - [x] `Completeness/Chain`, v4.126. `Completeness.lean` imports it.
  - [x] `Completeness/SingleRules`, v4.127. `Completeness.lean` imports it.
  - [x] `Completeness/SetRules`, v4.128. `Completeness.lean` imports it.
  - [x] `Completeness/Rule3Copy`, v4.129. `Completeness.lean` imports it.
  - [x] `Completeness/Rule3ChainCopy`, v4.130. `Completeness.lean` imports it.
  - [x] `Completeness/Rule3Full`, v4.131. `Completeness.lean` imports it.
  - [x] `Completeness/Rule3SetFull`, v4.132. `Completeness.lean` is now import-only.
- [x] 1. Split `DSepSoundSkeleton.lean`
  - [x] Survey and proposal (same section)
  - [x] `DSepSoundSkeleton/Basic` (layer 0), v4.119. `DSepSoundSkeleton.lean` imports it.
  - [x] `DSepSoundSkeleton/AssignmentCasts` (layer 1a), v4.120.
  - [x] `DSepSoundSkeleton/Factorizes` (layer 1b), v4.121.
  - [x] `DSepSoundSkeleton/AncestralReduction` (layer 1c), v4.122.
  - [x] `DSepSoundSkeleton/Moralisation` (layer 2), v4.123 (deleted v4.172).
  - [x] `DSepSoundSkeleton/Separator` (layer 3), v4.124. `DSepSoundSkeleton.lean` is now import-only.
- [x] 2. Remove the `first` fallbacks (v4.133 to v4.138)
  - Hedge v4.133, v4.134; Identification v4.135, v4.136; DSepSoundSkeleton v4.137;
    top-level files (CausalModel) v4.138.
  - Kept on purpose, as genuine case dispatch (each alternative is needed in some case):
    - `Identification/HedgeChain.lean` lines 169 and 283 (pick the hypothesis field)
    - `Identification/Hedge2.lean` lines 88 and 158 (pick the hypothesis field; the file
      was deleted in v4.159)
    - `DSepSoundSkeleton/Factorizes.lean` lines 220, 224, 251, 255, 309, 368 (`all_goals first`)
    - `DSepSoundSkeleton/AncestralReduction.lean` line 312 (`tauto | rintro`; went with
      `DAG.Walk.blockedAux_lift` in v4.170)
    - `WalkPath.lean` lines 264 and 284 (after `cases inc`, each alternative closes one case)
    - `Rule3.lean` lines 46 and 51 (after `cases inc`, each alternative closes one case)
  - A project-wide grep for `first` tactics finds exactly these and no others.
- [x] 3. Collect shared helpers (done v4.152). Duplicated helpers from all over the
  project now live once, under final names: `Util/ZMod2`, `Util/PMF`, `Util/ENNReal`,
  `Util/Finset`, `Util/Assignment`, `Util/Marginal`, `Identification/LatentSplit`, plus
  additions to `DAG`, `AncestralReduction`, `SingleRules` and `LatentTree`. Left for
  later steps: C2 and F4 (step 4), `Channel.hYW`, `hρW`, `PM.filter_univ` and
  `CFactorSets.lat_one` (step 7).
  - [x] Survey and proposal (section *Proposal: shared helpers*), v4.140
  - [x] Owner's decisions recorded (final names now, `updX_eq_setZ`, `decide` in step 7), v4.141
  - [x] 3.1 `Util/ZMod2`, v4.142. A1-A5, B2 (`map_ratio`, `map_flip_eq`), B3 moved into
    namespace `ZMod2` with final names; `x + x = 0` and `0 ≠ 1` now use Mathlib
    (`CharTwo.add_self_eq_zero`, `zero_ne_one`); `zmod2_t1` replaced by
    `ZMod2.add_add_add_cancel_pairs _ 1 _ _ _`; `map_fair_of_invol` derived from
    `map_ratio_of_invol`. Imported by `Identification/HedgeTemplate` and
    `Hedge/ParityModels`; the other users get it through these imports.
  - [x] 3.2 `Util/PMF`, v4.143. B1, B4 and `map_congr_supp` moved into namespace `PMF`
    with final names: `RP.pure1` → `PMF.pure_apply_of_eq` (generalised from `Bool`, the
    counterpart of Mathlib's `PMF.pure_apply_of_ne`; kept because one use is inside a
    `rw` chain), `RP.pure0` → Mathlib `PMF.pure_apply_of_ne`,
    `Rule3Flag.map_some_apply` → `PMF.map_some_apply_some`, `Rule3Flag.map_some_none` →
    `PMF.map_some_apply_none`, `Completeness.map_unif_ne_zero` →
    `PMF.map_uniformOfFintype_apply_ne_zero_iff`, `Hedge.map_congr_supp` →
    `PMF.map_congr_on_support` (codomain generalised from `ZMod 2` to any type).
    Imported by `Rule3Flag`; the other users get it through that import.
  - [x] 3.3 `Util/ENNReal`, v4.144. C4 and C5 in namespace `ENNReal` with final names:
    `Rule3Flag.cancel_flag` → `ENNReal.cross_cancel` (the most general form),
    `Rule3Flag.cancel_half` → `ENNReal.cancel_common_factor`; `Rule3.cancel_aux` and
    `Idc.cross_cancel` removed, their single uses are now
    `ENNReal.cross_cancel _ h1.symm h2.symm (fun h => absurd h hd0)` and
    `ENNReal.cross_cancel _ r₁ r₂ (fun h => absurd h hd0)`. New lemma
    `ENNReal.tsum_eq_tsum_tsum_of_iff` (C5, no uses yet; step 3.9). Imported by `Rule3`
    (which gets an English module docstring); the other users get it through that import.
  - [x] 3.4 `Util/Finset`, v4.145. C1 and C3 (the part the module table lists) in
    namespace `Finset` with final names: `IdAlgo.iter_sub` → `Finset.iterate_subset`,
    `CFactor.inter_erase_of_not_mem` → `Finset.inter_eq_erase_inter_of_notMem` (same
    orientation, Mathlib has no direct twin), `Hedge.exists_ne_of_sum_ne` →
    `Finset.exists_ne_of_sum_ne` (no Mathlib twin; it has no uses, the survey's 3 counted
    mentions in comments, so step 4 may delete it). `IdAlgo.iter_sup` and
    `Hedge.iter_mono` removed, their uses now call Mathlib's
    `Function.id_le_iterate_of_id_le` and `Function.monotone_iterate_of_id_le`.
    `Channel.hYW`, `hρW` and `PM.filter_univ` stay for step 7. Imported by
    `Identification/Basic`; the other users get it through that import. `IdAlgo` gets an
    English module docstring.
  - [x] 3.5 `DAG.lean` (F1, F2), v4.146. New in `DAG.lean`: `DAG.mem_parents`
    (`u ∈ G.parents v ↔ G.edge u v`) and `DAG.parents_subset_of_closed`; `DAG.lean`
    gets an English module docstring. Deviation: `mem_parents` is **not** `@[simp]`;
    with the attribute the kept `all_goals first | (intro x hx; simp at hx ⊢; tauto) |
    skip` dispatch in `DSepSoundSkeleton/Factorizes` (lines 221, 252) no longer closes
    its goals. Removed, with every use switched: `TwoRoot.parOf`, `RootPath.RP.pOf`,
    `Channel.parOfA`, `Bow.parB`, `BowGen.parB` → `DAG.parents_subset_of_closed`;
    `CFactor.edge_of_par` → `DAG.mem_parents.mp`; `Hedge.PM.mem_parents_iff`,
    `RP.parA`, `parB`, `parC`, `HedgeChain.Chain.mem_par`, `LatentTree.LT.mem_par`,
    `PathTree.PT.mem_par`, `Channel.par1` → `DAG.mem_parents`; four inline copies of
    `parents_subset_of_closed` (`CFactor.anc_factor`, `marginal_ancestral_apply`, two in
    `Identification/Basic`) replaced. F2: `Identification.rank_le_of_reaches` removed,
    its two uses call `G.rank_le_of_reaches` (`Reachability`). Inline unfoldings: every
    `simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]` became
    `simp only [DAG.mem_parents]` and every `by simpa [DAG.parents] using h` became
    `DAG.mem_parents.mp h` (or `.mpr`), except in `Completeness/Trek` (Norwegian module
    docstring, left for step 5). 49 uses of `DAG.parents` inside `simp` remain: 44
    goal-closing `simp [DAG.parents, …]` with further unfoldings (left; step 7 may
    switch them to `DAG.mem_parents`), 4 in `Completeness/Trek`, and one combined
    `simp only [DAG.verticesUpTo, DAG.parents, …]` in `AncestralReduction`.
  - [x] 3.6 `Util/Assignment`, `Util/Marginal` (with `updX_eq_setZ`), v4.147. Both in
    namespace `PearlDoCalculus.DAG.CausalModel` with final names. D1: `Idc.joinXZ` and
    `Identification.joinYX` → `Assignment.join` (sets implicit, so `x.join z`);
    `Idc.joinXZ_left`, `Identification.joinYX_Y` → `Assignment.restrict_join_left`;
    `Idc.joinXZ_right` → `Assignment.restrict_join_right`; `Identification.joinYX_X`
    removed, its two uses (`Identifiable.mono_Y`, `Channel`) call
    `restrict_join_right` with the agreement on the overlap derived from disjointness.
    D3: `Completeness.exists_restrict_eq` → `Assignment.restrict_surjective` (stated as
    `Function.Surjective`). `DSepSound.restrict_injective_of_subset` →
    `Assignment.restrict_injective_of_subset`. D4: `DSepSound.marginal_restrict_of_injective`
    → `CausalModel.marginal_restrict_of_injective`, `CFactor.marginal_restrict_ne_zero` →
    `CausalModel.marginal_restrict_ne_zero`, `Identification.marginal_eq_of_sub` →
    `CausalModel.marginal_eq_of_subset`, `Identification.marginal_pos_of_sub` →
    `CausalModel.marginal_ne_zero_of_subset` (kept as a corollary, now a two-line proof
    through `restrict_surjective` and `marginal_restrict_ne_zero`; its statement, positive
    everywhere on `O`, is what the 6 uses need). `Adjustment.marginal_eq_of_subset'`
    removed here, restored in 3.6b as `CausalModel.marginal_eq_restrict_of_subset_of_subset`. D2: `Identification.CFactor.updX_eq_setZ`
    (`updX U X a x' = Rule3Flag.setZ X Uᶜ a x'`, by `rfl`) next to `updX` in
    `Identification/CFactorSets`, the lowest module that sees both definitions
    (`Util/Assignment` cannot, since `setZ` lives in `Rule3Flag`); no use sites changed.
    `Util/Marginal` is imported by `DSepSound`, its first user (the module table said
    `DSepSoundSkeleton/Basic`, which uses none of it); the other users get it through
    that import. `Adjustment` and `Idc` get English module docstrings.
  - [x] 3.6b restore short marginal lemma, v4.148. `Adjustment.marginal_eq_of_subset'` is
    back as `CausalModel.marginal_eq_restrict_of_subset_of_subset` in `Util/Marginal`, a
    one-line corollary of `marginal_restrict_of_injective`; its 17 uses (Adjustment,
    `Completeness/SingleRules`, `Completeness/SetRules`) have their v4.146 shape again.
  - [x] 3.7 `kfac` lemmas, v4.149. D5: new `kfac_of_mem` next to `kfac` in
    `DSepSoundSkeleton/AncestralReduction` (any `α`, same explicit arguments as the old
    ones); `Bow.kfac_eq` (`Fin 3`, `Bool`) and `BowGen.kfac_eqG` (`Bool`) removed, their
    uses call `kfac_of_mem`. `DoAudit.kfac_univ` moved next to it as `kfac_univ`
    (namespace `PearlDoCalculus`, short name kept), now the case `S = univ` of
    `kfac_of_mem`; its 108 qualified occurrences (90 lines in 20 files) dropped the
    `DoAudit.` prefix. D6: the `α`
    versions move next to `liftSub` in `Completeness/SingleRules` as
    `Completeness.kfac_liftSub` and `Completeness.kfac_doModel_liftSub`; `Bow.kfac_lift`,
    `kfac_lift_do`, `BowGen.kfac_liftG`, `kfac_lift_doG`, `Hedge.kfac_liftα`,
    `kfac_lift_doα` removed and every use switched. `DoAudit`, `AdjAudit` and
    `Completeness/Trek` get English module docstrings.
  - [x] 3.8 `Identification/LatentSplit`, v4.150. Group E moved verbatim (proofs
    unchanged apart from the names; not yet through `ENNReal.tsum_eq_tsum_tsum_of_iff`,
    that is 3.9) into the new file, namespace `Identification.CFactor`, with final names:
    `fill` (kept); `full2` → `fillBlocks`, `full2_eq_iff` → `eq_fillBlocks_iff`, `val1`,
    `val2` → `fillBlocks_apply_left`, `fillBlocks_apply_right`; `subO` →
    `compl_inter_subset_compl`, `subOA` → `compl_inter_subset`, `subA1` →
    `inter_inter_subset`, `subA2` → `inter_inter_compl_subset`; `full3` → `fillBlocksOn`,
    `full3_iff` → `eq_restrict_fillBlocksOn_iff`, `wal1`, `wal2` →
    `fillBlocksOn_apply_left`, `fillBlocksOn_apply_right` (from `CFactor`); `subT1` →
    `inter_inter_subset_inter`, `subT2` → `inter_inter_compl_subset_inter`, `join2` →
    `joinBlocks`, `join2_iff` → `eq_joinBlocks_iff`, `tsum_join2` →
    `tsum_eq_tsum_joinBlocks`, `fill_join1`, `fill_join2` → `fill_joinBlocks_apply_left`,
    `fill_joinBlocks_apply_right`; `updX` and `updX_eq_setZ` (names kept, `updX` is in the
    public statements), `fill_updX_out` → `fill_updX_apply_of_notMem`, `fill_updX_in` →
    `fill_updX_apply_of_mem` (from `CFactorSets`); `IdSound.upd_iff` →
    `eq_updX_and_restrict_eq_iff`. No exact duplicates in group E (`full3` equals `fill`
    of `join2` only pointwise, `full2` is `full3` at `A = univ` only up to a non-definitional
    set equality; both are for 3.9). `tsum_updX` stays in `IdSound` (3.9 rewrites it). Uses
    updated in `CFactor`, `CFactorSets`, `Identify`, `IdSound` and `Verma`; lines that the
    longer names pushed past 100 columns are rewrapped. `CFactor` now imports
    `LatentSplit` instead of `Identification/Basic`. Two `unusedSectionVars` warnings
    (`inter_inter_subset`, `inter_inter_subset_inter`, formerly `subA1`, `subT1`) move
    with their code.
  - [x] 3.9 Latent splits through the generic `tsum` lemma, v4.151. `Util/ENNReal` gets
    three variants of `ENNReal.tsum_eq_tsum_tsum_of_iff`, each a few lines:
    `tsum_ite_eq_tsum_tsum_of_iff` (the sum over the `c` with a fixed value `x = p c`;
    proved from the main lemma on a subtype), `tsum_eq_tsum_ite_tsum_of_iff` (only the `a`
    with `P a` are used; also on a subtype) and `tsum_tsum_ite_eq_of_iff` (the single term
    of a double indicator sum). Rewritten through them, statements unchanged (lines of the
    declaration before → after): `LatentSplit.tsum_eq_tsum_joinBlocks` 29 → 5,
    `CFactor.anc_factor` 68 → 42, `IdSound.tsum_updX` 38 → 7, `Channel.tsum_ins` 13 → 6,
    `Channel.tsum_reindex` 17 → 5 (no longer through `tsum_ins`), and, not in the survey
    list but the same four-step `calc`, `Identify.inner_one` 57 → 18. `CFactor.marginal_factor`
    59 → 7: it is now the case `A = univ` of `anc_factor` (the set equality
    `Uᶜ ∩ univ = Uᶜ` is handled by `marginal_eq_restrict_of_subset_of_subset` on the
    marginal and `Finset.univ_inter` on the argument of `Q`, so no dependent rewriting);
    `anc_factor` moves before it. Definitions merged: `fillBlocksOn U A S a w1 w2` is
    replaced by `fill U A a (joinBlocks U A S w1 w2)` (the form `CFactorSets` and
    `Identify` already used); `eq_restrict_fillBlocksOn_iff` becomes
    `eq_restrict_fill_joinBlocks_iff`, and `fillBlocksOn_apply_left`, `_right` are removed
    (their uses call the identical `fill_joinBlocks_apply_left`, `_right`). With
    `marginal_factor` derived, `fillBlocks`, `eq_fillBlocks_iff`, `fillBlocks_apply_left`
    and `fillBlocks_apply_right` have no uses and are removed. `LatentSplit` is regrouped
    (fill, joining two blocks, restricting to a set, overwriting). Left: `CFactorSets.lat_one`
    writes out a one-part version of the same argument (three steps); it would need a
    one-part variant of the fixed-part lemma (step 7).
  - [x] 3.10 Forest solution (F3), v4.152. The two verbatim copies in
    `LatentTree.LT` and `RootPath.RP` (`RootPathModels`) are one block in
    `Identification/LatentTree`, namespace `Identification`, stated for any finite index
    type `ι`, any `AddCommMonoid` of values and the forest `bp` with height `ht` and
    `hht` as explicit parameters (the copies did not differ otherwise). Final names:
    `solN` → `forestSubst`, `M` and `ht_le` removed (`Finset.univ.sup ht` inside the new
    `forestSolution bp ht R := forestSubst bp R (Finset.univ.sup ht + 1)`, the only level
    any user takes), `stab` → `forestSubst_succ_of_le`, `uniq` → `eq_forestSubst_of_le`,
    `sol_iff` → `forall_eq_forestSolution_iff` (with `hht` as first argument). Every
    `P.solN R (P.M + 1)` became `forestSolution P.bp P.ht R` (`LatentTree`,
    `RootPathModels`, `RootPath`).
- [x] 4. Remove superseded results and scratch files (done v4.163; everything deleted stays at tag `v4.152`).
  Scratch files, old audit files, unused lemmas, five superseded files, two unused
  blocks and two last unused results deleted (v4.153 to v4.163); no public result used any of them.
  - [x] Scratch files: `Probe135.lean`–`Probe140.lean`, `verification/Check.lean`,
    `Check3.lean`, `Check4.lean`, `Check5.lean`, `verification/Probe.lean`, v4.153.
    Nothing outside `CLEANUP.md` referred to them.
  - [x] Old audit files `verification/AuditV1`, `AuditV2`, `AuditV22`, `AuditV423`,
    `AuditV433`, `AuditV438` (`.lean` only; the `audit_v*_output.txt` files stay), v4.154.
    Only documentation referred to them (`README.md`, `CLEANUP.md`); updated.
  - [x] Unused lemmas, v4.155: C2 `union_inter_distrib`, `disjoint_inter_of_disjoint`
    (`DSepSoundSkeleton/AssignmentCasts`; Mathlib has `Finset.union_inter_distrib_right`,
    `Disjoint.mono`) and `Finset.exists_ne_of_sum_ne` (`Util/Finset`, with its
    `#print axioms` line in `Hedge/ParityModels`). No other uses. `Util/Finset` now imports
    only `Mathlib.Data.Finset.Basic`. F4 `Channel.not_ident_of_sub` goes with `Channel`.
  - [x] `Completeness/Rule3Copy`, v4.156. No proof used it; the only links were its
    import and two `#print axioms` lines in `Completeness/Rule3SetFull`, removed.
    `Rule3SetFull` and `Rule3ChainCopy` get everything they need through
    `Rule3Full` and `SingleRules`. Docs updated (`README.md`, `HANDOFF.md`).
  - [x] `Hedge/Reduce`, v4.157. No Lean file used its declarations (`not_ident_of_subα`,
    `keepDAG`, `keepDAG_edge`, `not_ident_keep`, `hedgeKeep`, `hedge_red_nxt`,
    `hedge_red_lat`); its own `#print axioms` lines went with it. Imports removed from
    `Hedge.lean` (list renumbered) and `PearlDoCalculus.lean`; docs updated
    (`README.md`, `HANDOFF.md`, `Completeness/SingleRules` docstring).
  - [x] `Identification/Channel` (with F4 `Channel.not_ident_of_sub`), v4.158. No Lean
    file used its declarations; its `#print axioms` lines went with it. Imports removed
    from `Identification.lean` and `PearlDoCalculus.lean`; docs updated (`README.md`,
    `HANDOFF.md`, `EXPLAINER.md`, the `Identification.lean` and `Util/ENNReal`
    docstrings). `ENNReal.tsum_tsum_ite_eq_of_iff` (`Util/ENNReal`) had no uses left; it
    was deleted in v4.163.
  - [x] `Identification/Hedge2`, v4.159. No Lean file used its declarations
    (`hedge2_not_identifiable` is the case `n = 0` of `HedgeChain.chain_not_identifiable`);
    its `#print axioms` line went with it. Imports removed from `Identification.lean`
    and `PearlDoCalculus.lean`; docs updated (`README.md`, `HANDOFF.md`, the
    `Identification.lean` docstring, the step 2 note above).
  - [x] `Identification/TwoRoot`, v4.160. No Lean file used its declarations
    (`twoRoot_not_identifiable` is the case `n = 0`, `r = 1` of `RootTree`); its
    `#print axioms` line went with it. Imports removed from `Identification.lean` and
    `PearlDoCalculus.lean`; docs updated (`README.md`, `HANDOFF.md`, the
    `Identification.lean` docstring).
  - [x] Round 5 `Parents` block (`Identification/Basic`), v4.161: `ends_blocked`,
    `not_reaches_parent`, `parents_backdoor`, `parents_identifiable`, with the block's
    `open` lines and `#print axioms` line (103 lines). No other Lean file used them, and
    the rest of `Basic` needs neither the block nor its `open scoped ENNReal`. Docs
    updated (`README.md`, `HANDOFF.md`, the `Basic` and `Identification.lean`
    docstrings).
  - [x] Round 12 set versions (`Identification/LatentTree`), v4.162: `HedgeTmpl.Tm.doA_X`,
    `doB_X`, `contra`, `not_ident_X` and `latentTree_not_identifiable_XY`, with the
    block's `open` and `variable` lines and `#print axioms` line (201 lines). They were
    used only inside the block. The forest solution, round 9 and
    `latentTree_not_identifiable_set` (round 11) stay; the chain `Bow` → `HedgeChain` →
    `PathTree` → `LatentTree` → `MultiRoot` → `RootPath` → `RootTree` for `tian_iff` is
    untouched. Docs updated (`README.md`, `HANDOFF.md`, the `LatentTree` and
    `Identification.lean` docstrings). `latentTree_not_identifiable_set` had no uses
    either; it is round 11, not part of this item, and was kept here (deleted in v4.163).
  - [x] The last two unused results, v4.163: `ENNReal.tsum_tsum_ite_eq_of_iff`
    (`Util/ENNReal`; its only uses were in `Identification/Channel`, deleted v4.158) and
    `Identification.latentTree_not_identifiable_set` (round 11 of
    `Identification/LatentTree`, superseded by `Hedge.PM.hedge_not_ident_Y`), with the
    latter's `namespace`/`variable` lines and `#print axioms` line. No Lean file or
    document used them. Docs updated (`README.md`, `HANDOFF.md`, the `Util/ENNReal` and
    `LatentTree` docstrings).
- [x] 5. Document every file (done v4.164–v4.169). Every `.lean` file under `PearlDoCalculus/`
  and the root `PearlDoCalculus.lean` now has an English module docstring (what it proves,
  why it is needed and who uses it, how the proof goes, main results), topic section
  headers instead of work-round headers, and a docstring on every declaration; all six
  commits change comments and docstrings only.
  - [x] Top-level files `PearlDoCalculus/*.lean` (34 files) and the root `PearlDoCalculus.lean`,
    v4.164. Comments and docstrings only (a comment-stripped diff against `main` is empty).
    All Norwegian comments and docstrings translated (about 310 comment blocks), the 15
    work-round section headers ("Runde N", "Fase N, runde M", "Front-door, runde N")
    replaced by topic headers, 55 docstrings added (every remaining declaration has one),
    and new or rewritten module docstrings (what, why, how, main results) in
    `BackdoorGeneral`, `BayesBall` (had none), `Blocking`, `CausalModel`, `Counterexample`,
    `DSepSound`, `DSeparation`, `DoCalculus`, `EpistemicScope`, `FrontDoor`,
    `FrontDoorObservable`, `IdAudit`, `Lauritzen`, `MediatorAdjustment`, `Reachability`,
    `SetSound`, `SimpleConfounder`, `SimpleConfounderObservable`, `Verma`, `WalkPath`,
    `Walks`; the import-only `Completeness.lean` and `Identification.lean` now say what
    the folder proves and list their parts; the outdated skeleton docstring of
    `DSepSoundSkeleton.lean` and the root docstring of `PearlDoCalculus.lean` are
    rewritten for the current layout. Left as they are: the `justification` strings of
    `EpistemicScope` (code, Norwegian). Found on the way (for step 4 or 7, not changed):
    nothing outside `DSepSoundSkeleton/Moralisation` uses its results
    (`moral_edge_witness`, `moral_walk_of_open`, `dsep_of_moral_sep`); soundness goes
    through `Lauritzen.moral_sep_of_dsep_lauritzen` instead.
  - [x] `Util/*` (6 files), v4.165. Comments and docstrings only (a comment-stripped diff
    against `main` is empty). The files were already in English with topic section
    headers, so there was nothing to translate or rename. The six module docstrings now
    name the files that use each one and say how the proofs go; 23 docstrings added in
    `Util/ZMod2` (every declaration in `Util/*` now has one). Found on the way (for step 7,
    not changed): `ZMod2.one_eq_add_one_iff` has no uses.
  - [x] `DSepSoundSkeleton/*` (6 files), v4.169. Comments and docstrings only (a
    comment-stripped diff against `main` is empty). All Norwegian comments and docstrings
    translated (68 comment blocks, in `AssignmentCasts`, `Factorizes`,
    `AncestralReduction`, `Moralisation` and `Separator`; `Basic` was already in English),
    the 5 old section headers ("Layer 0" … "Layer 3", and "Removed" in `Moralisation`)
    replaced by topic headers and 19 topic headers added; the proof-step labels
    ("Steg 2" … "Steg 6") in `AncestralReduction` and the work-session remarks ("budget
    several sessions", "nine attempts") replaced by plain descriptions; 3 docstrings
    added (`mem_ancestors_iff`, `extendOverList_factorizes'`, `clique_one_sided`; every
    declaration in `DSepSoundSkeleton/*` now has one). New module docstrings (what, why
    and who uses it, how, main results) in all six files. The misplaced "ancestral
    reduction" sketch at the top of `AssignmentCasts` (which also described an older
    proof) is gone; `AncestralReduction` now describes the actual proof (the pinned model
    `pinTo`). Outdated docstrings fixed: `joint_splits` ("conclusion left as `True`") and
    `dsep_of_moral_sep` ("the converse is open"; it is
    `Lauritzen.moral_sep_of_dsep_lauritzen`). `Moralisation` now says that no other file
    uses its results. The import-only `DSepSoundSkeleton.lean` was still accurate and is
    unchanged. Found on the way (for step 7, not changed): `transport_factorization`,
    `cast_fun_apply` (`AssignmentCasts`), `ancestors_parent_closed`, `ancestors_ancestors`
    (`Basic`), `reaches_seed_of_mem_ancestors`, `tail_dropLast_sublist_dropLast`
    (`Moralisation`), `clique_one_sided`, `assignmentSplit3`, `restrict_XZ_eq_iff`,
    `restrict_YZ_eq_iff` (`Separator`) have no uses at all; `dsep_restrict` (with
    `DAG.Walk.lift`, `DAG.Walk.blockedAux_lift`) and the results of `Moralisation` are
    used by no other file; the proof of `separator_partition` (`Separator`) still contains
    a `trace_state`, which prints the goal during every build.
  - [x] `Completeness/*` (7 files), v4.168. Comments and docstrings only (a comment-stripped
    diff against `main` is empty). All Norwegian comments and docstrings translated (about 130
    comment blocks), the 6 work-round section headers ("Nivå 3a-2", "Nivå 3a-3, runde 1" …
    "runde 4") replaced by topic headers, the 11 Norwegian topic headers translated, and 12
    topic headers added where one section held several topics; 41 docstrings added (every
    declaration in `Completeness/*` now has one; the public `dsep_iff`, `dsepSet_iff`,
    `rule1_iff_set`, `rule2_iff_set`, `rule3_iff_set` had one and are translated). New or
    rewritten module docstrings (what, why and who uses it, how, main results) in all seven
    files; the import-only `Completeness.lean` now describes `SingleRules` (rule 3 only when
    `z ∉ An(W)`) and `Rule3ChainCopy` (the hard case of rule 3) accurately. Found on the way
    (for step 7, not changed): the results of `Trek` (`trek_not_condIndep`,
    `not_condIndep_of_colliderFree`, `dsep_complete_marginal`) have no users, `dsep_complete`
    covers them; `chain_support'`, `orpar_eq'`, `chain_z'` (`Rule3ChainCopy`) repeat
    `chain_support`, `orpar_eq_of_RZ`, `chain_z` (`Chain`) with a weaker positivity
    hypothesis, so the originals could be derived from them; `rule3_complete_nonanc` is
    `rule3_complete_root` after `rw [Z2_singleton]` and repeats its proof, and likewise
    `rule3_complete_set_nonanc` and `rule3_complete_set_root`; `walk_to_isolated` and
    `dsep_isolated` are the singleton cases of `walk_to_isolated_set` and
    `dsep_isolated_set`; `liftModel` and `doModel_lift` (used only by `rule1_complete`) are a
    special case of `liftSub` and `lift_do_kfac`; the rule 2 and rule 3 proofs of
    `SingleRules` and `SetRules` repeat the same `hsub`, `hXN`, `hA`, `hB` blocks.
  - [x] `Identification/*` (14 files), v4.167. Comments and docstrings only (a comment-stripped
    diff against `main` is empty). All Norwegian comments and docstrings translated (about 190
    comment blocks), the 29 work-round section headers ("Runde 2" … "Runde 36") replaced by
    topic headers, and round numbers in prose replaced by topic or file references; 263
    docstrings added (every declaration in `Identification/*` now has one; the public
    `Identifiable` and `CFactor.tian_iff` had one and are translated). New or rewritten
    module docstrings (what, why and who uses it, how, main results) in all files except
    `LatentSplit`, which was already complete; the import-only `Identification.lean` no
    longer lists "sets `Y`" (deleted v4.163) among the hedge families. Found on the way (for
    step 7, not changed): `backdoor_identifiable`, `frontdoor_identifiable`,
    `observed_identifiable`, `not_identifiable_of_mem` (`Basic`),
    `HedgeChain.chain_not_identifiable`, `PathTree.pathTree_not_identifiable`,
    `LatentTree.latentTree_not_identifiable` and the c-factor results `tian_identifiableX`,
    `tian_identifiable_ccompX`, `Q_causal`, `Q_local`, `id_sound` have no users in other
    files; the proofs of
    `Q_split` (`CFactorSets`) and `Q_split_rel` (`Identify`) are the same up to the closedness
    hypothesis, and so are `Q_prod` and `Q_prod_rel` (`IdSound`); `id_sound_blocks` repeats
    the case split of `Q_do_eq`.
  - [x] `Hedge/*` (13 files), v4.166. Comments and docstrings only (a comment-stripped diff
    against `main` is empty). All Norwegian comments and docstrings translated (about 210
    comment blocks), the 43 work-round section headers ("Runde 42" … "Runde 87") replaced by
    topic headers, 113 docstrings added (every declaration in `Hedge/*` now has one,
    including the public `IsHedge`, `idCheck_false_hedge`, `PM.hedge_not_ident`,
    `PM.hedge_not_ident_Y` and `idCheck_iff`). Every module docstring now also says who
    uses the file; `Hedge/Defs` no longer points to the old `Hedge.lean`, and
    `Hedge/Product` records why the tails use a second coordinate (the gap in the
    published H4 argument). The import-only `Hedge.lean` was still accurate and is
    unchanged. Found on the way (for step 7, not changed): `hedge_root_uniform`,
    `hedge_rootOf`, `ParTree.desc_par_iff` (with `desc`, `ParTree.iter_mem`,
    `ParTree.iter_d_le`) and `ParTree.inc_inj` (`Hedge/Tree`) are used by no other file;
    `PM.lb_sh` (`Hedge/ObsEq`) is the case `E = F` of `PM.lb_shE` (`Hedge/Positivity`);
    the body of `PM.hedge_not_ident` (`Hedge/Roots`) repeats the construction that
    `PM.hedge_data` (`Hedge/Complete`) packages, so `hedge_data` could move to `Roots`
    and shorten `hedge_not_ident`.
- [x] 4b. Leftovers found in step 5, v4.170. The `justification` strings of
  `EpistemicScope` (`heavyWeightExample`, `lightWeightExample`) are in English, and the
  remark that they were left in Norwegian is gone; no public statement contains them. The
  `trace_state` in `separator_partition` (`DSepSoundSkeleton/Separator`) is removed. Unused
  lemmas deleted (each grepped in every `.lean` file, `verification/` included, and in
  `public_statements.txt`; none is a public result, none had a use outside its own group):
  `ancestors_parent_closed`, `ancestors_ancestors` (`Basic`); `transport_factorization`,
  `cast_fun_apply` (`AssignmentCasts`); `dsep_restrict` with `DAG.Walk.lift` and
  `DAG.Walk.blockedAux_lift`, and the section around them (`AncestralReduction`; the kept
  `first` of step 2 went with it); `clique_one_sided`, `assignmentSplit3`,
  `restrict_XZ_eq_iff`, `restrict_YZ_eq_iff` (`Separator`). Docstrings of `Basic`,
  `AncestralReduction`, `Separator` and `DSepSoundSkeleton.lean` updated.
  **Not deleted here: `DSepSoundSkeleton/Moralisation`** (deleted in v4.172 on the
  owner's decision). `verification/AxiomCheck.lean` (kept by the owner in step 4)
  prints the axioms of `moral_walk_of_open` and `dsep_of_moral_sep`, so the file stays until the owner decides (delete the file and
  the two `#print axioms` lines, or keep it as the converse direction). Its other
  results (`moral_edge_witness`, `reaches_seed_of_mem_ancestors`,
  `tail_dropLast_sublist_dropLast`) have no uses but stay with the file for now.
  Left for step 7: `DAG.induce_edge`, `DAG.induce_reaches` (`Basic`) and
  `assignment_ext_split` (`Separator`) now have no uses (they served `DAG.Walk.lift` and
  the two `restrict_*_eq_iff` lemmas); they are basic facts about `DAG.induce` and
  `assignmentSplit`, so they were kept.
- [ ] 6. Make the names consistent
  - [x] Survey and proposal (section *Proposal: renaming*), v4.171. Nothing renamed yet;
    the proposal awaits the owner's approval and answers to its open questions (policy
    for old names, `DSepSoundSkeleton` → `Soundness/` or `DSepSound/`, the audit files,
    `Moralisation`, the IDENTIFY predicate, the `Hedge` vocabulary, helpers in Mathlib
    namespaces).
  - [x] Owner's decisions recorded (section *Proposal: renaming*, open questions and
    commit plan), v4.172. In the same commit: the no-alias rule for step 6 in `CLAUDE.md`;
    `DSepSoundSkeleton/Moralisation` deleted (`moral_edge_witness`,
    `reaches_seed_of_mem_ancestors`, `DAG.Walk.strong_length_induction`,
    `tail_dropLast_sublist_dropLast`, `mem_support_tail_dropLast`, `moral_walk_of_open`,
    `mem_support_interior`, `dsep_of_moral_sep`; no Lean file used them, the soundness
    route goes through `Lauritzen.moral_sep_of_dsep_lauritzen`), its import removed from
    `DSepSoundSkeleton.lean` and the layers renumbered (`Separator` is now layer 2);
    the two `#print axioms` lines for it removed from `verification/AxiomCheck.lean`,
    whose header is now in English; `verification/Axioms.lean` deleted (nothing ran or
    imported it; only the file lists in `HANDOFF.md` section 4 and the step 4 record above
    named it, and its four `#print axioms` lines are all in `AxiomCheck.lean`). Docs
    updated (`README.md`, `HANDOFF.md`, the `DSepSoundSkeleton`, `Basic` and `Separator`
    docstrings).
  - [x] 6.1 `BayesBall` namespace and the `_imp_` lemmas (B1 + D1), v4.173. Everything in
    `BayesBall.lean` (`BallDir`, `BallState`, `bbNext`, `bbReachable`, `incomingOfDir`,
    the derived `instFintypeBallDir` and the four theorems) moved from the root namespace
    into namespace `BayesBall`; `Lauritzen.lean` and `SetSound.lean`, its only users, now
    `open BayesBall`, so their unqualified uses of `BallDir`, `BallState` and
    `bbReachable` are unchanged. Renamed, no aliases: `not_blockedAux_imp_open` →
    `open_of_not_blockedAux`, `bbReachable_imp_not_blocked` →
    `not_blocked_of_bbReachable`, `bbReachable_imp_open_walk` →
    `exists_open_walk_of_bbReachable`, `DSeparated_imp_not_bbReachable` →
    `not_bbReachable_of_dSeparated` (`BayesBall`), and `Rule3.start_imp_bwd` →
    `Rule3.blockedAux_bwd_of_start` (the survey said `bwd_of_start`; the longer name says
    what is concluded). 18 occurrences in 4 Lean files (13 in `BayesBall` with its
    docstring and `#check` line, 1 in `Lauritzen`, 2 in `SetSound`, 2 in `Rule3`) and 2 in
    `README.md`; `HANDOFF.md` and `EXPLAINER.md` did not name them.
  - [x] 6.2 `notMem` and `subset` spellings (D2 + D3), v4.174. Renamed, no aliases:
    `Rule3Flag.flag_kernel_some_not_mem` → `flag_kernel_some_notMem`,
    `Rule3.kfac_doModel_of_not_mem` → `kfac_doModel_of_notMem`,
    `DoCalculus.parents_cutIn_of_not_mem` → `parents_cutIn_of_notMem`,
    `Completeness.reach_not_mem` → `reach_notMem`, `Lauritzen.not_mem_of_notZAnc` →
    `notMem_of_notZAnc`; `IdAlgo.anc_sub` → `ancIn_subset`, `IdAlgo.cc_sub` →
    `ccIn_subset`, `Completeness.parents_cutIn_sub` → `parents_cutIn_subset`,
    `Rule3.doModel_marginal_of_sub` → `doModel_marginal_of_subset`. 62 occurrences in 18
    Lean files (`reach_not_mem` 19, `doModel_marginal_of_sub` 16) and 1 in `README.md`;
    `HANDOFF.md` and `EXPLAINER.md` did not name them. The survey table above keeps the
    old names.
  - [x] 6.3 `HedgeChain` (B8), v4.175. The structure `Identification.HedgeChain.Chain`
    is now `Identification.HedgeChain` itself, and its API moved from namespace
    `HedgeChain.Chain` to `HedgeChain` (the namespace of the helpers `ev`, `xx`, `xb`,
    `chan_symm`, `condA_iff`, which stay where they were). The model-level
    `Chain.not_ident` had exactly the statement of the standalone
    `chain_not_identifiable`, which only called it; the two are merged into
    `HedgeChain.not_identifiable` (no `not_ident_models` needed here, unlike the survey's
    guess). No aliases. Nothing outside `HedgeChain.lean` used the structure or the
    theorem (the other files only `open HedgeChain (ev …)`), so the commit changes about
    20 lines of that file (with its `#print axioms` line and docstring; the namespace is
    closed before the structure and reopened after it), `HANDOFF.md` section 1 and
    two lines of `README.md`. The clash with `Completeness.Chain` is gone.
  - [x] 6.4 `HedgeTemplate` and `PathTree` (B2 + B3), v4.176. The structures
    `Identification.HedgeTmpl.Tm` and `Identification.PathTree.PT` are now
    `Identification.HedgeTemplate` and `Identification.PathTree`, with their APIs in the
    namespaces of the same names (the namespace `HedgeTmpl` held nothing else and is
    gone). Renamed, no aliases: `Tm.not_ident` → `HedgeTemplate.not_identifiable` (it is
    the template's main theorem; there was no standalone twin, so nothing was merged),
    `PathTree.pathTree_not_identifiable` → `PathTree.not_identifiable` (still a one-line
    corollary of the template, not a duplicate), and the conversions `PT.toTm`,
    `LatentTree.LT.toTm` → `toHedgeTemplate` (the second ahead of item 5, because its
    type changed name). Uses: `HedgeTemplate.lean` (structure blocks, docstring,
    `#print axioms` lines) and 3 lines of `LatentTree.lean`; no other file used them.
    Docs: `HANDOFF.md` (section 1 table, the H-plan in section 2, status line) and 3
    lines of `README.md`; historical mentions of deleted declarations
    (`HedgeTmpl.Tm.not_ident_X`, in `LatentTree.lean` and `README.md`) keep their old
    names.
  - [x] 6.5 `LatentTree` (B4), v4.177. The structure `Identification.LatentTree.LT` is
    now `Identification.LatentTree`, with its API in namespace `LatentTree` (which held
    nothing else). Renamed, no aliases: `LatentTree.latentTree_not_identifiable` →
    `LatentTree.not_identifiable` (a one-line corollary of
    `HedgeTemplate.not_identifiable`, as before; nothing merged); `toHedgeTemplate`
    already had its final name (v4.176). The forest-solution block of the same file
    (`forestSubst`, `forestSolution`, namespace `Identification`) is unchanged. Uses: only
    `LatentTree.lean` itself (structure block, docstring, `#print axioms` line) and one
    docstring line of `HedgeTemplate.lean`; no other Lean file used the structure. Docs:
    `HANDOFF.md` (section 1 table, status line) and 2 lines of `README.md`.
  - [x] 6.6 `MultiRoot` and `RootPath` (B5 + B6), v4.178. The structures
    `Identification.MultiRoot.MR` and `Identification.RootPath.RP` are now
    `Identification.MultiRoot` and `Identification.RootPath`, with their APIs in the
    namespaces of the same names; the helpers `MultiRoot.ext`, `ext_restrict`,
    `chan_mix` keep their names (the namespace is closed before the structure and reopened
    after it, with the file's `open` lines moved up to `namespace Identification`). **Two
    duplicates merged**, no aliases: `RP.not_ident` had exactly the statement of the
    standalone `RootPath.rootPath_not_identifiable`, which only called it; both are now
    `RootPath.not_identifiable`. Likewise `MultiRoot.multiRoot_not_identifiable` only
    called `RootPath.multiRoot_of_rootPath` with the same statement; the proof of the
    latter (the case `r = 0`, path `{u₀}`) is now the proof of `MultiRoot.not_identifiable`,
    and `multiRoot_of_rootPath` is gone. The conversion `RootTree.RT.toRP` is now
    `toRootPath` (ahead of item 7, since its target type changed name). Uses:
    `RootPathModels.lean` (structure blocks, docstring), `RootPath.lean` (structure
    namespace, the merged theorems, docstring, `#print axioms` lines: three became two),
    `RootTree.lean` (the conversion, its use and 4 docstring lines) and one docstring line
    of `LatentTree.lean`. Docs: `HANDOFF.md` (section 1 table, status line) and 6 lines of
    `README.md`.
  - [x] 6.7 `RootTree` (B7), v4.179. The structure `Identification.RootTree.RT` is now
    `Identification.RootTree`, with its API in namespace `RootTree` (which held nothing
    else). Renamed, no aliases: `RootTree.rootTree_not_identifiable` →
    `RootTree.not_identifiable` (a one-line corollary of `RootPath.not_identifiable`
    through `toRootPath`; there was no `RT.not_ident`, so nothing was merged).
    `RootTree.embedded_not_identifiable` keeps its name (no repeated prefix). Uses:
    `RootTree.lean` (structure block, the two theorems, docstrings, `#print axioms` line),
    `TianIff.lean` (the `let T : RootTree G n` and 3 comment lines), one docstring line
    each of `RootPath.lean` and `RootPathModels.lean`. Docs: `HANDOFF.md` (section 1 table,
    one line of section 2, status line) and 3 lines of `README.md`. All seven hedge-family
    structures now carry the name of their namespace.
  - [x] 6.8 `BowEmbedded` and the subgraph lemmas (B9 + C9), v4.180. Renamed, no
    aliases: namespace `Identification.BowGen` → `Identification.BowEmbedded` (its 27
    declarations keep their short names, so `BowEmbedded.bow_not_identifiable_general`,
    `g1`, `g2`, `ancB`, `p1`, `ne_of_edge`, …; `Bow.bowG` and `IdAlgo.bow_idCheck`, frozen
    by `AuditV480.lean`, are untouched). The lemmas "the graph of model A/B is a subgraph
    of `G`": `hsA` → `gA_parents_subset`, `hsB` → `gB_parents_subset` in `Bow`,
    `HedgeChain`, `HedgeTemplate` (here also the structure field `hsA` and its use in
    `PathTree.toHedgeTemplate`), `PathTree`, `LatentTree` and `RootPath`
    (`RootPathModels`); in `BowEmbedded`, where the graphs are `g2` and `g1`, `hsA` →
    `g2_parents_subset` and `hsB` → `g1_parents_subset`. Local hypotheses called `hsA`
    in `Hedge/Product` and `Hedge/ProductBias` are not lemmas and were left. 74
    occurrences in 7 Lean files (`BowGen` 30, `hsA`/`hsB` 44) and 3 in the docs
    (`README.md` 1, `HANDOFF.md` 2); 12 lines that grew past 100 columns are rewrapped. Not done (not in
    the plan): `BowEmbedded.bow_not_identifiable_general` and `Bow.bow_not_identifiable`
    still repeat their namespace's name; shortening them to `not_identifiable` would match
    the other families.
  - [x] 6.9a The `Reach…` predicates outside `Completeness` (C1, C2, C3 undirected, C4),
    v4.181. None of the names occurs in `public_statements.txt` or `AuditV480.lean`.
    Renamed, no aliases: `Lauritzen.Reach` → `Lauritzen.BallReaches` (and its walk lemma
    `walk_reach` → `walk_ballReaches`), `SetSound.ReachS` → `SetSound.BallReachesSet`
    (`SetSound.walk_reach_set` is generic in its predicate and keeps its name),
    `PearlDoCalculus.ReachAvoiding` → `ReachableAvoiding` with `reachAvoiding_refl` →
    `reachableAvoiding_refl`, and `Identification.CFactor.Reach` → `IdentifyDerives`
    (constructors `refl`, `anc`, `block` and `IdentifyDerives.trans` follow), with
    `reach_closed` → `identifyDerives_of_isClosedBlock`, `reach_sound` →
    `identifyDerives_sound`, `reach_ident` → `identifyDerives_ident`, `IdAudit.reach_y` →
    `identifyDerives_y`, `IdAlgo.reach_y'` → `identifyDerives_y'` (the prime is item 11).
    Uses: 108 occurrences in 8 Lean files (`Identify`, `IdSound`, `IdAlgo`, `IdAudit`,
    `Identification.lean`, `Lauritzen`, `SetSound`, `Separator`), 3 lines rewrapped.
    Docs: `HANDOFF.md` (section 1 table, section 7) and 10 lines of `README.md`. The
    `Completeness` predicates `ReachAvoid` and `RZ` (C3 directed, C5) follow in 6.9b.
    C6 (`Lauritzen.NotZAnc`, marked optional in the survey) is left as it is.
  - [x] 6.9b The `Reach…` predicates of `Completeness` (C3 directed, C5), v4.182. Neither
    name occurs in `public_statements.txt` or `AuditV480.lean`. Renamed, no aliases:
    `Completeness.ReachAvoid` → `ReachesAvoiding` (93 occurrences) and `Completeness.RZ`
    → `ReachesParentAvoiding` (60), and the lemmas that carried the abbreviation `RZ`:
    `RZ_of_reach`, `RZ_mono`, `RZ_cut`, `RZ_cutset`, `RZ_avoid_mono`, `RZ_H_of_clean` →
    `reachesParentAvoiding_of_reach`, `_mono`, `_cut`, `_cutset`, `_avoid_mono`,
    `_H_of_clean`, and `orpar_eq_of_RZ` → `orpar_eq_of_reachesParentAvoiding` (23
    occurrences). The lemmas named with the plain word `reach` (`reach_mono`,
    `reach_cut`, `reach_iff_parent`, `reach_notMem`, `rank_le_of_reach`, …) keep their
    names. 176 occurrences in the 5 files `Trek`, `Chain`, `Rule3ChainCopy`, `Rule3Full`,
    `Rule3SetFull` (docstrings included); about 20 lines that grew past 100 columns are
    rewrapped. No other file and no document named them.
  - [x] 6.10 Ancestor-set lemmas of the soundness route (C7 + C8), v4.183. None of the
    names occurs in `public_statements.txt` or `AuditV480.lean`. No aliases.
    `DSepSound.A_closed` (ancestor sets are closed under parents) moved to
    `DSepSoundSkeleton/Basic` as `PearlDoCalculus.ancestors_closed`, next to
    `subset_ancestors`; its four users outside `DSepSound` (`Rule3`, `Rule3Flag`,
    `Adjustment`, `SetSound`) now call it unqualified. Renamed in place:
    `DSepSound.union_subset_A` → `subset_ancestors_insert`, `Lauritzen.mem_A_cases` →
    `mem_ancestors_cases`, `SetSound.mem_A_cases_set` → `mem_ancestors_cases_set`, and
    `DSepSound.marginal_eq_of_subset_A` → `marginal_eq_restrictTo_marginal` (deviation:
    the survey proposed `marginal_eq_of_subset_ancestors`, but the lemma is about any set
    `A` closed under parents, not only ancestor sets; the new name says what it states,
    `M.marginal S = (restrictTo M A hA).marginal S`). 19 occurrences in 7 Lean files
    (docstrings of `DSepSound` and `Basic` included); no document named them.
  - [x] 6.11 Primes, history names, `rule3_core`, `_set` suffixes, `_aux` (D4-D9), v4.184.
    None of the names occurs in `public_statements.txt` or `AuditV480.lean`. Renamed, no
    aliases:
    - D4 (`Rule3ChainCopy`): `chain_support'`, `orpar_eq'`, `chain_z'` →
      `chainCopy_support`, `chainCopy_orpar_eq`, `chainCopy_z`.
    - D5: `Rule3.doModel_comp_marginal'` → `doModel_comp_marginal_of_union_eq` (the union
      is given as an equation `A ∪ B = C`); `extendOverList_cons'` →
      `extendOverList_cons_insert` (stated on the `insert` form of the set);
      `extendOverList_factorizes'` → `extendOverList_factorizes` (there is no unprimed
      version); `SimpleConfounderModel.backdoor_adjustment'` →
      `backdoor_adjustment_mul_comm` (the factors in the other order); `IdAlgo.identifyDerives_y'`
      → `identifyDerives_idG_of_identifyTop`.
    - D6: `IdAlgo.idAudit_check` → `identifyTop_idG`, `IdAlgo.idAudit_idCheck` →
      `idCheck_idG`, `IdAlgo.id_audit'` → `idG_identifiable_of_idCheck`,
      `IdAudit.id_audit` → `IdAudit.idG_identifiable`, `IdAudit.tian_sets_fails` →
      `IdAudit.idG_not_tian_sets`, `IdAudit.identifyDerives_y` →
      `IdAudit.identifyDerives_idG` (the namespace `IdAudit` itself is item 15).
    - D7: `Rule3Flag.rule3_gen` → `rule3_core`.
    - D8: `CFactor.tian_identifiableX` → `tian_identifiable_set_of_closed`,
      `CFactor.tian_identifiable_ccompX` → `tian_identifiable_set_ccomp`.
    - D9: `Completeness.chain_aux` → `chain_of_not_blockedAux` (open walk gives a chain,
      both induction directions), `HedgeChain.chain_aux` → `u_succ_eq_w_xor_u_zero` (the
      chain equations give `u_{i+1} = w_i xor u₀`).
    100 occurrences: 81 in 13 Lean files, 19 in `README.md` (15) and `HANDOFF.md` (4); 5 lines
    rewrapped. The historical output `verification/audit_v433_output.txt` keeps the old
    names (it records what that audit printed).
- [ ] 7. Shorten proofs
- [ ] 8. Finish

