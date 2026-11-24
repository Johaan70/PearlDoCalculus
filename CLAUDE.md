# Working on PearlDoCalculus

Lean 4 formalization of Pearl's causal identification theory, from d-separation to the
completeness of the ID algorithm (`Hedge.idCheck_iff`). Read `HANDOFF.md` for the
mathematics and the history, and `docs/history/CLEANUP.md` for the current task.

## Rules

- Build after every change: `lake build PearlDoCalculus.<Module>` while working, a full
  `lake build` before every commit. A commit needs `Build completed`, no `error`, and no
  `declaration uses 'sorry'` in the log.
- Never add `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `admit`.
- Never run two cleanup agents at the same time.
- Run scripts/check.sh and lake build in the foreground. Never leave background shells or polling loops (pgrep -f matches itself).
- The public results listed in `docs/history/CLEANUP.md` keep their exact statements. If a name moves,
  keep the old name as a `@[deprecated]` alias until the end of the cleanup.
  Exception (owner's decision, v4.141): internal helpers moved or merged in step 3 get
  their final name at once, and every use is updated in the same commit; no deprecated
  alias is left for them. This does not apply to the public results, nor to helpers whose
  names occur in `verification/public_statements.txt` (for example `setZ`, `updX`),
  which keep their full names.
  Step 6 (owner's decision, v4.172): renamed internal names get no `@[deprecated]` alias,
  including the theorems listed in `HANDOFF.md` section 1. Every use, and `HANDOFF.md`,
  is updated in the same commit as the rename. Names in
  `verification/public_statements.txt` and in the frozen `verification/AuditV480.lean`
  are not renamed.
- Small steps: one commit per step, on a branch, fast-forward into `main`, tag `v4.NN`,
  push. If a step cannot be made to build, revert it rather than patching around it.
- Update `HANDOFF.md` (status line, file map) and `README.md` when the file layout changes.
- The repository owner reads Norwegian; code, comments and documentation are in English.

## Agent and gate

- The cleanup is done by the subagent `pearl-cleanup` (`.claude/agents/pearl-cleanup.md`).
- `scripts/check.sh` is the gate for every commit: full build, no `sorry`, no forbidden
  constructs outside comments, standard axioms only, and unchanged public statements.
  Commit only after `CHECK OK`.
- `scripts/check.sh`, `verification/AuditV480.lean`, `verification/PublicStatements.lean`
  and `verification/public_statements.txt` are frozen. Only the owner changes them.
