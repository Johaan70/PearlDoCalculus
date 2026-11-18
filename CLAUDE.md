# Working on PearlDoCalculus

Lean 4 formalization of Pearl's causal identification theory, from d-separation to the
completeness of the ID algorithm (`Hedge.idCheck_iff`). Read `HANDOFF.md` for the
mathematics and the history, and `CLEANUP.md` for the current task.

## Rules

- Build after every change: `lake build PearlDoCalculus.<Module>` while working, a full
  `lake build` before every commit. A commit needs `Build completed`, no `error`, and no
  `declaration uses 'sorry'` in the log.
- Never add `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `admit`.
- The public results listed in `CLEANUP.md` keep their exact statements. If a name moves,
  keep the old name as a `@[deprecated]` alias until the end of the cleanup.
- Small steps: one commit per step, on a branch, fast-forward into `main`, tag `v4.NN`,
  push. If a step cannot be made to build, revert it rather than patching around it.
- Update `HANDOFF.md` (status line, file map) and `README.md` when the file layout changes.
- The repository owner reads Norwegian; code, comments and documentation are in English.
