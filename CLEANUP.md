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
   `DSepSoundSkeleton.lean`. Build after each file.
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
- [ ] 1. Split `Identification.lean`
- [ ] 1. Split `Completeness.lean`
- [ ] 1. Split `DSepSoundSkeleton.lean`
- [ ] 2. Remove the `first` fallbacks
- [ ] 3. Collect shared helpers
- [ ] 4. Remove superseded results and scratch files
- [ ] 5. Document every file
- [ ] 6. Make the names consistent
- [ ] 7. Shorten proofs
- [ ] 8. Finish

