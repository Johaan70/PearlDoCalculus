/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Derives

/-!
# Expressions over one term, and substitution

The completeness proof follows a run of Tian's IDENTIFY (`IdentifyDerives`) from `V` down
to a c-component `C`. Each step derives the c-factor of the smaller set from that of the
larger one: `Q[T ∩ S]` becomes an expression in which the only probability term is `Q[T]`.
To chain the steps, the next step's derivation of `Q[T]` is substituted into that
expression. This file has the two notions this needs.

* `E.OnlyProb p`: every `prob` term of `E` is the expression `p`. So `E` is built from
  `one`, `mul`, `div`, `sum` and `p` only.
* `E.substProb e`: `E` with every `prob` term replaced by `e`. For `E.OnlyProb p` this is
  the substitution of `e` for `p`.

**The substitution lemma** (`Derives.substProb`). If `E.OnlyProb p` and `p` derives `e`,
then `E` derives `E.substProb e`. The proof is induction on `E`, with the congruence steps
of `Derives`.

**What is kept.** Substituting an expression over `q` gives an expression over `q`
(`Expr.onlyProb_substProb`), and the variables of the result are among those of `E` and
`e` (`Expr.vars_substProb_subset`). An expression over a term without `do` has no `do`
(`Expr.OnlyProb.doFree`), and one over a safe divisor is a safe divisor
(`Expr.OnlyProb.positive`). So once the chain reaches `Q[V] = P(O)`, which has no `do`, the
result has no `do`.

**Main results.** `Expr.OnlyProb`, `Expr.substProb`, `Derives.substProb`,
`Expr.onlyProb_substProb`, `Expr.vars_substProb_subset`, `Expr.OnlyProb.doFree`,
`Expr.OnlyProb.positive`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

namespace Expr

variable {V : Type*}

/-- Every `prob` term of `E` is `p`: `E` is built from `one`, `mul`, `div`, `sum` and `p`. -/
@[simp] def OnlyProb (E p : Expr V) : Prop :=
  match E with
  | prob Y Z X => prob Y Z X = p
  | one => True
  | mul a b => a.OnlyProb p ∧ b.OnlyProb p
  | div a b => a.OnlyProb p ∧ b.OnlyProb p
  | sum _ a => a.OnlyProb p

/-- `E` with every `prob` term replaced by `e`. -/
@[simp] def substProb (E e : Expr V) : Expr V :=
  match E with
  | prob _ _ _ => e
  | one => one
  | mul a b => mul (a.substProb e) (b.substProb e)
  | div a b => div (a.substProb e) (b.substProb e)
  | sum S a => sum S (a.substProb e)

/-- A term is an expression over itself. -/
@[simp] lemma onlyProb_prob (Y Z X : Finset V) : (prob Y Z X).OnlyProb (prob Y Z X) := rfl

/-- **Substitution keeps the form.** Replacing every `prob` term by an expression over `q`
gives an expression over `q`. -/
lemma onlyProb_substProb {e q : Expr V} (he : e.OnlyProb q) (E : Expr V) :
    (E.substProb e).OnlyProb q := by
  induction E with
  | prob => exact he
  | one => trivial
  | mul a b ha hb => exact ⟨ha, hb⟩
  | div a b ha hb => exact ⟨ha, hb⟩
  | sum S a ha => exact ha

/-- **An expression over a term without `do` has no `do`.** -/
lemma OnlyProb.doFree {E p : Expr V} (hE : E.OnlyProb p) (hp : p.DoFree) : E.DoFree := by
  induction E with
  | prob Y Z X => exact (show prob Y Z X = p from hE) ▸ hp
  | one => trivial
  | mul a b ha hb => exact ⟨ha hE.1, hb hE.2⟩
  | div a b ha hb => exact ⟨ha hE.1, hb hE.2⟩
  | sum S a ha => exact ha hE

/-- **An expression over a safe divisor is a safe divisor.** -/
lemma OnlyProb.positive [DecidableEq V] [Fintype V] {U : Finset V} {E p : Expr V} (hE : E.OnlyProb p)
    (hp : p.Positive U) : E.Positive U := by
  induction E with
  | prob Y Z X => exact (show prob Y Z X = p from hE) ▸ hp
  | one => trivial
  | mul a b ha hb => exact ⟨ha hE.1, hb hE.2⟩
  | div a b ha hb => exact ⟨ha hE.1, hb hE.2⟩
  | sum S a ha => exact ha hE

/-- **The variables after substitution** are among those of `E` and `e`. -/
lemma vars_substProb_subset [DecidableEq V] (E e : Expr V) :
    (E.substProb e).vars ⊆ E.vars ∪ e.vars := by
  induction E with
  | prob => exact Finset.subset_union_right
  | one => exact Finset.empty_subset _
  | mul a b ha hb =>
    exact Finset.union_subset
      (ha.trans (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)))
      (hb.trans (Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)))
  | div a b ha hb =>
    exact Finset.union_subset
      (ha.trans (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)))
      (hb.trans (Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)))
  | sum S a ha =>
    exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left)
      (ha.trans (Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)))

end Expr

/-- **The substitution lemma.** If every `prob` term of `E` is `p`, and `p` derives `e`,
then `E` derives `E.substProb e`. -/
theorem Derives.substProb {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {U : Finset V}
    {p e : Expr V} (h : Derives G U p e) {E : Expr V} (hE : E.OnlyProb p) :
    Derives G U E (E.substProb e) := by
  induction E with
  | prob Y Z X =>
    have hp : Expr.prob Y Z X = p := hE
    subst hp
    exact h
  | one => exact refl _
  | mul a b ha hb => exact mul (ha hE.1) (hb hE.2)
  | div a b ha hb => exact div (ha hE.1) (hb hE.2)
  | sum S a ha => exact sum S (ha hE)

end DoCalc
