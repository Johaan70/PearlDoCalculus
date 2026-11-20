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
`IdAudit`, and `verification/AuditV423.lean` directly. They use `Identifiable`,
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
- [ ] 1. Split `Completeness.lean`
  - [x] Survey and proposal (section *Proposal: split of `Completeness.lean` and `DSepSoundSkeleton.lean`*)
  - [x] `Completeness/Trek`, v4.125. `Completeness.lean` imports it.
  - [ ] `Chain`, `SingleRules`, `SetRules`, `Rule3Copy`, `Rule3ChainCopy`, `Rule3Full`, `Rule3SetFull`
- [x] 1. Split `DSepSoundSkeleton.lean`
  - [x] Survey and proposal (same section)
  - [x] `DSepSoundSkeleton/Basic` (layer 0), v4.119. `DSepSoundSkeleton.lean` imports it.
  - [x] `DSepSoundSkeleton/AssignmentCasts` (layer 1a), v4.120.
  - [x] `DSepSoundSkeleton/Factorizes` (layer 1b), v4.121.
  - [x] `DSepSoundSkeleton/AncestralReduction` (layer 1c), v4.122.
  - [x] `DSepSoundSkeleton/Moralisation` (layer 2), v4.123.
  - [x] `DSepSoundSkeleton/Separator` (layer 3), v4.124. `DSepSoundSkeleton.lean` is now import-only.
- [ ] 2. Remove the `first` fallbacks
- [ ] 3. Collect shared helpers
- [ ] 4. Remove superseded results and scratch files
- [ ] 5. Document every file
- [ ] 6. Make the names consistent
- [ ] 7. Shorten proofs
- [ ] 8. Finish

