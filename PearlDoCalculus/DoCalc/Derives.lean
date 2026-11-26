/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Positivity
import PearlDoCalculus.Rule3Flag

/-!
# Derivations in the do-calculus

`Derives G U e₁ e₂` says that the expression `e₁` can be rewritten into `e₂` by the
do-calculus in the DAG `G` whose latent vertices are `U`. It is an equational calculus with
three kinds of steps, exactly those listed in `docs/design-docalc-completeness.md`,
section "Derivations". The list is fixed: there is no step "any identity that holds in
every distribution", because such a step would make the completeness theorem close to
trivial (decision 1 of the note).

1. **Equality steps.** Reflexivity, symmetry, transitivity, and congruence under `mul`,
   `div` and `sum`.
2. **The three rules of the do-calculus.** Each rewrites one `prob` term, under its
   graphical condition in `G` (latents included), stated with the d-separation predicate
   `SetSound.DSeparatedSet` and the graph surgeries `cutIn` (`G_{X̄}`) and `cutOut`
   (`G_{Z̲}`) with which the rules are proved: `DoCalculus.rule1`, `DoCalculus.rule2` and
   `Rule3Flag.rule3_general`. In rule 3, `Z(W)` is `Rule3.Z2 (cutIn G X) Z W`, the part of
   `Z` that is not an ancestor of `W` in `G_{X̄}`.
3. **Probability calculus.** Marginalization, the chain rule, the commutative monoid laws
   of `mul` and `one`, the unit law of `sum`, the two cancellations `e / e = 1` and
   `(a · b) / b = a`, pulling a factor out of a sum, splitting a sum over a disjoint union,
   and swapping two sums. None of them uses the graph.

**Side conditions.** Each step carries the side conditions its soundness needs, stated
syntactically with `U` and nothing else:

* the rules need the usual disjointness of their sets, and that the sets they condition
  on or intervene on are observed (`⊆ Uᶜ`), so that their denominators are positive in a
  model with a positive observed marginal (`DoCalc/Positivity`);
* marginalization needs the summed set to be disjoint from the variables of the term, and
  pulling a factor out of a sum needs the summed set to be disjoint from the free
  variables of the factor;
* splitting and swapping sums need the two summed sets to be disjoint;
* the two cancellations need the divisor to be `Expr.Positive U` (`DoCalc/Positivity`):
  built from `prob` terms over observed variables, so that it is neither `0` nor `∞`.

The chain rule and the semiring laws need no side condition. Well-formedness of the
expressions is not required: no step needs it to be sound.

**The semiring laws.** The syntax has no addition, so "the commutative semiring laws for
`mul`, `one` and `sum`" are read as: `mul` is commutative and associative with unit `one`
(`mul_comm`, `mul_assoc`, `one_mul`), and a sum over the empty set is its summand
(`sum_empty`, the unit law of the sum). Distributivity of `mul` over `sum` is the step that
pulls a factor out of a sum (`sum_mul`), and the associativity and commutativity of sums
are the split and swap steps (`sum_union`, `sum_comm`).

Soundness, `derives_sound`, is in `DoCalc/Soundness`: every step is valid in every model
with a positive observed marginal.

**Main results.** `Derives`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Derivations in the do-calculus.** `Derives G U e₁ e₂`: `e₁` can be rewritten into
`e₂` in the DAG `G` with latent vertices `U`, by the steps of
`docs/design-docalc-completeness.md`, section "Derivations". -/
inductive Derives (G : DAG V) (U : Finset V) : Expr V → Expr V → Prop where
  /-- Equality steps (item 1 of the note): reflexivity. -/
  | refl (e : Expr V) : Derives G U e e
  /-- Equality steps (item 1 of the note): symmetry. -/
  | symm {e₁ e₂ : Expr V} : Derives G U e₁ e₂ → Derives G U e₂ e₁
  /-- Equality steps (item 1 of the note): transitivity. -/
  | trans {e₁ e₂ e₃ : Expr V} : Derives G U e₁ e₂ → Derives G U e₂ e₃ → Derives G U e₁ e₃
  /-- Equality steps (item 1 of the note): congruence under `mul`. -/
  | mul {a a' b b' : Expr V} : Derives G U a a' → Derives G U b b' →
      Derives G U (.mul a b) (.mul a' b')
  /-- Equality steps (item 1 of the note): congruence under `div`. -/
  | div {a a' b b' : Expr V} : Derives G U a a' → Derives G U b b' →
      Derives G U (.div a b) (.div a' b')
  /-- Equality steps (item 1 of the note): congruence under `sum`. -/
  | sum (S : Finset V) {e e' : Expr V} : Derives G U e e' →
      Derives G U (.sum S e) (.sum S e')
  /-- **Rule 1** (item 2 of the note): `P(Y | Z, W, do(X)) = P(Y | Z, do(X))` when `Y`
  and `W` are d-separated by `X ∪ Z` in `G_{X̄}`. -/
  | rule1 (X Y Z W : Finset V) (hY : Disjoint Y (X ∪ Z)) (hW : Disjoint W (X ∪ Z))
      (hO : Z ∪ W ∪ X ⊆ Uᶜ) (h : SetSound.DSeparatedSet (cutIn G X) (X ∪ Z) Y W) :
      Derives G U (.prob Y (Z ∪ W) X) (.prob Y Z X)
  /-- **Rule 2** (item 2 of the note): `P(Y | Z, W, do(X)) = P(Y | W, do(X ∪ Z))` when
  `Y` and `Z` are d-separated by `X ∪ W` in `G_{X̄Z̲}`. -/
  | rule2 (X Y Z W : Finset V) (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z)
      (hYXW : Disjoint Y (X ∪ W)) (hO : Z ∪ W ∪ X ⊆ Uᶜ)
      (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z) :
      Derives G U (.prob Y (Z ∪ W) X) (.prob Y W (X ∪ Z))
  /-- **Rule 3** (item 2 of the note): `P(Y | W, do(X ∪ Z)) = P(Y | W, do(X))` when `Y`
  and `Z` are d-separated by `X ∪ W` in `G_{X̄, \overline{Z(W)}}`, where `Z(W)` is the
  part of `Z` that is not an ancestor of `W` in `G_{X̄}`. -/
  | rule3 (X Y Z W : Finset V) (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z)
      (hYXW : Disjoint Y (X ∪ W)) (hO : Z ∪ W ∪ X ⊆ Uᶜ)
      (h : SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z) :
      Derives G U (.prob Y W (X ∪ Z)) (.prob Y W X)
  /-- **Marginalization** (item 3 of the note): `P(Y | Z, do X) = Σ_W P(Y ∪ W | Z, do X)`,
  for `W` disjoint from the variables of the term. -/
  | marg (Y Z X W : Finset V) (h : Disjoint W (Y ∪ Z ∪ X)) :
      Derives G U (.prob Y Z X) (.sum W (.prob (Y ∪ W) Z X))
  /-- **Chain rule** (item 3 of the note):
  `P(Y ∪ W | Z, do X) = P(Y | W ∪ Z, do X) · P(W | Z, do X)`. -/
  | chain (Y W Z X : Finset V) :
      Derives G U (.prob (Y ∪ W) Z X) (.mul (.prob Y (W ∪ Z) X) (.prob W Z X))
  /-- Semiring laws (item 3 of the note): `mul` is commutative. -/
  | mul_comm (a b : Expr V) : Derives G U (.mul a b) (.mul b a)
  /-- Semiring laws (item 3 of the note): `mul` is associative. -/
  | mul_assoc (a b c : Expr V) : Derives G U (.mul (.mul a b) c) (.mul a (.mul b c))
  /-- Semiring laws (item 3 of the note): `one` is a unit for `mul`. -/
  | one_mul (a : Expr V) : Derives G U (.mul .one a) a
  /-- Semiring laws (item 3 of the note): a sum over the empty set is its summand. -/
  | sum_empty (e : Expr V) : Derives G U (.sum ∅ e) e
  /-- `e / e = one` (item 3 of the note), for a divisor that is `Positive`. -/
  | div_self (e : Expr V) (he : e.Positive U) : Derives G U (.div e e) .one
  /-- `(a · b) / b = a` (item 3 of the note), for a divisor that is `Positive`. -/
  | mul_div_cancel (a b : Expr V) (hb : b.Positive U) : Derives G U (.div (.mul a b) b) a
  /-- Pulling a factor out of a sum (item 3 of the note), when the factor does not read
  the summed variables. -/
  | sum_mul (S : Finset V) (a e : Expr V) (h : Disjoint S a.free) :
      Derives G U (.sum S (.mul a e)) (.mul a (.sum S e))
  /-- Splitting a sum over a union of disjoint sets (item 3 of the note). -/
  | sum_union (S T : Finset V) (e : Expr V) (h : Disjoint S T) :
      Derives G U (.sum (S ∪ T) e) (.sum S (.sum T e))
  /-- Swapping two sums over disjoint sets (item 3 of the note). -/
  | sum_comm (S T : Finset V) (e : Expr V) (h : Disjoint S T) :
      Derives G U (.sum S (.sum T e)) (.sum T (.sum S e))

end DoCalc
