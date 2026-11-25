# A gap in the published hedge argument, and a repair

*November 2026. Found while formalising the completeness of the ID algorithm in
Lean 4 (`Hedge.idCheck_iff`, tag `v4.80`). All numbers below are exact
(rational arithmetic) and can be reproduced with `verification/h4_checks.py`.*

## Summary

The theorem is fine: when the ID algorithm fails, `P(y | do(x))` is not
identifiable. But one step in the published proof does not work as written.
That step carries non-identifiability from the roots of a hedge down to `Y`,
and it fails when a directed path from a root to `Y` passes back through the
hedge. Below is a small graph where this happens, the exact numbers, and a
construction that repairs the step. The repair is machine-checked.

## The step in question

Shpitser and Pearl (technical report R-327, appendix, Lemma 12; also Shpitser's
thesis, proof of Theorem 5) argue in two stages.

1. **Roots.** Given a hedge `F ⊊ F'` for `P(y | do(x))` with root set `R`,
   build two models `M1`, `M2` over bits (values in ZMod 2). Every node outputs
   the parity of what it reads. In `M2`, nodes of `F` ignore their parents in
   `F' \ F`. The two models agree on all observational data, but
   `P(R | do(x))` differs.
2. **Down to `Y`.** Extend both models to `I = An(Y) ∩ De(R)`. Each node in `I`
   outputs the parity of its parents, plus a little independent noise. The
   claim is that the parity of `Y` then tracks the parity of `R`, so the
   difference at `R` shows up at `Y`.

The journal version contains the same extension step: I. Shpitser and J. Pearl,
"Complete Identification Methods for the Causal Hierarchy", *JMLR* 9 (2008),
proof of Theorem 17, Appendix A, p. 1969 (the proof starts on p. 1968). It also
assumes, "without loss of generality", that every node in `I` has at most one
child. In its notation the names `F` and `F'` are swapped relative to this note.

Stage 1 is correct, and it is formalised as `Hedge.PM.hedge_not_ident`. Stage 2
is the problem. The path from a root to `Y` (a *tail*) may run through nodes of
`F'`, or re-enter `F`. Those nodes already have functions fixed by stage 1, and
those functions do not pass the root's bit along. If we change them so that they
do pass it along, the two models stop agreeing on observational data.

## Example C

Observed nodes are `x, r, w, r2, z`. Directed edges are
`x → w`, `r → w`, `w → r2`, `r2 → z`. Hidden common causes:

- `u` joins `r` and `r2`
- `u2` joins `w` and `x`
- `u4` joins `x` and `r2`

The query is `X = {x}`, `Y = {z}`.

The hedge is `F = {r, r2}` with root set `R = {r, r2}` and
`F' = {x, r, w, r2}`. This is the shape the ID algorithm itself produces: `F`
is a whole c-component of `G_{X̄}[An(Y)]`.

The only tail from `r` to `z` is `r → w → r2 → z`. It passes through
`w ∈ F' \ F` and re-enters `F` at `r2`.

The stage 1 models are as follows. In `M1`:

- `x = u2 + u4`
- `r = u + noise`, with `P(noise = 1) = 1/4`
- `w = u2 + x`
- `r2 = u + u4 + w`

`M2` is the same, except that `r2 = u`. The two models agree observationally,
and they differ on the joint of `(r, r2)` under `do(x)`.

Stage 2 can be applied in two ways:

| Variant | Same observational data? | `P(z=1 \| do x=0)` in M1 / M2 | `P(z=1 \| do x=1)` in M1 / M2 |
|---|---|---|---|
| `z = r2 + noise` (the tail is ignored) | yes | 1/2 / 1/2 | 1/2 / 1/2 |
| `w` also reads `r`, so that the tail carries `r` | **no** | 1/2 / 1/2 | 1/2 / 1/2 |

In the first variant the models agree on data but give the same answer, so
nothing is shown. In the second variant they no longer agree on data at all.

We also ran a full search over every linear parity model on this graph (every
node reads any subset of its parents), with several noise patterns. It finds
only a few positive pairs with different `P(z | do x)`. Each of them also
changes a node in `F' \ F`, and none of them follows a general rule.

The theorem still holds for this graph. It contains another hedge, the bow
`F = {w}`, `F' = {w, x}`, so `P(z | do x)` is indeed not identifiable. The
point is narrower: a proof that goes hedge by hedge needs a stage 2 that works
for every hedge, and the published stage 2 does not.

## The repair: a second bit

Give every node a pair of bits `(a_v, b_v)`.

- `a` is the stage 1 model, unchanged.
- `b` carries the roots' signal down to `Y` on its own channel:
  `b_v = [v ∈ R]·a_v + Σ_{w ∈ tail-children(v)} b_w + η_v`.
  Here `η_v` is independent noise with `P(η = 1) = 1/4`.

The tails are fixed in advance by choosing, for each node in `An_{G_X̄}(Y)`, one
pointer towards `R`.

The `b` bits never feed back into any `a` bit. So the observational argument
from stage 1 still goes through, and the two models agree on all data. The
`b` channel accumulates the parity of the roots on the way down. So the
difference at `R` reaches `Y`, damped by the noise but never cancelled.

On example C this gives the following:

- `M1` and `M2` agree on all observational data, and every observed value has
  positive probability.
- `P(b_z = 1 | do x = (0,0))` is `1/2` in `M1` and `31/64` in `M2`.

In general, the proof shows that the bias of the root parity survives each step
down the tail (`Hedge.bias_step`, `Hedge.bias_base`), and that the result is
non-identifiability at `Y` for every hedge (`Hedge.PM.hedge_not_ident_Y`).
Together with the hedge produced by the failing ID algorithm
(`Hedge.idCheck_false_hedge`) and soundness (`IdAlgo.idCheck_sound`), this gives
the following:

```lean
theorem idCheck_iff ... :
    idCheck G U X Y = true ↔ ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y
```

It depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`,
and the build has no `sorry` (audit: `verification/AuditV480.lean`).

## Related work

I. Shpitser, "When does the ID algorithm fail?", arXiv:2307.03750 (2023), shows that
Corollary 3 of the AAAI 2006 paper (Shpitser and Pearl), the hedge criterion quantified
over subsets `Y' ⊆ Y` and `A' ⊆ A`, is false. The correct statement is that ID fails if
and only if there is a hedge for `p(Y | do(a))` itself; this is the first of three
equivalent conditions in his Proposition 1. That is a different issue from the one here.
It concerns the statement of the criterion, while this note concerns the extension step
in the proof of Theorem 4 (JMLR 2008, Theorem 17), and his paper takes the statement of
Theorem 4 as correct. Our Lean results use hedges for `P(Y | do(X))` itself
(`Hedge.IsHedge G U X Y F F'`), as in his Proposition 1.

## Caveats

- The argument is stated on our reading of the published proof. If a fix for
  this already appears in the literature, we would be glad to hear of it.
- The values in the countermodels are pairs of bits (`Val2`). The completeness
  statement quantifies over all value types, so this is enough. A version with
  binary variables only would need more work.
- Example A in `h4_checks.py` shows a second, simpler failure: a tail that
  re-enters `F` directly. There the published rule works only if the node in
  `F` is also allowed to read the tail.
