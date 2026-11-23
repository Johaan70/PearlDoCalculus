import PearlDoCalculus.Soundness.Basic
import PearlDoCalculus.Soundness.AssignmentCasts
import PearlDoCalculus.Soundness.Factorizes
import PearlDoCalculus.Soundness.AncestralReduction
import PearlDoCalculus.Soundness.Separator
import PearlDoCalculus.Soundness.BayesBall
import PearlDoCalculus.Soundness.Lauritzen
import PearlDoCalculus.Soundness.DSepSound
import PearlDoCalculus.Soundness.WalkPath
import PearlDoCalculus.Soundness.SetSound
import PearlDoCalculus.Soundness.Counterexample

/-!
# Soundness of d-separation

This file only collects the files of the `Soundness` folder, so that
`import PearlDoCalculus.Soundness` brings in the whole layer. The folder proves that
d-separation is sound: if `x` and `y` are d-separated by `Z`, then in every causal model
on the graph `x` and `y` are conditionally independent given `Z` (`DSepSound.dsep_sound`),
also for the classical path-based definition (`WalkPath.dsep_sound_path`) and for sets of
vertices (`SetSound.dsep_sound_set`). The converse is the `Completeness` folder.

**The route.** Pearl proves soundness by induction over blocked and open walks. That is
hard to formalise, because `blockedAux` carries state along the walk, so being blocked is
not local to one step. The proof here follows Lauritzen instead, with the graph part and
the probability part kept apart:

    d-separation in G
      ⟹ (restrict to an ancestral set)
    d-separation in G.induce (ancestors G ({x, y} ∪ Z))
      ⟹ (moralise; Soundness/Lauritzen)
    vertex separation in the moral graph
      ⟹ (the joint factorizes along the separator)
    conditional independence

**The layers**, from the bottom:

0. `Soundness/Basic`: induced subgraphs `DAG.induce`, ancestor sets `ancestors`,
   the moral graph `moralGraph`, vertex separation `Separates`, and the fact that every
   family `{v} ∪ parents v` is a clique of the moral graph (`moral_family_clique`).
1. Probability:
   - `Soundness/AssignmentCasts` (1a): bookkeeping lemmas about assignments
     (`extend`, `extendOverList`, splitting indicators, `restrict_cast_*`).
   - `Soundness/Factorizes` (1b): `jointUpTo` factorizes into a left and a right
     part when the two sides are separated by `Z` (`jointUpTo_factorizes`).
   - `Soundness/AncestralReduction` (1c): the joint is a product of kernel factors
     `kfac`, and the marginal on an ancestral set is the joint of the restricted model
     (`marginal_eq_restricted_joint`).
2. `Soundness/Separator`: if `Z` separates `x` from `y` in an undirected graph,
   the vertices split as `L ∪ Z ∪ R`, the joint has the product form `f(L,Z) · g(R,Z)`
   (`joint_splits`), and the product form gives conditional independence
   (`condIndep_of_product_form`).
3. The graph step: `Soundness/BayesBall` (a Bayes ball that reaches `y` traces an open
   walk, `BayesBall.not_bbReachable_of_dSeparated`) and `Soundness/Lauritzen` (Lauritzen's
   theorem: d-separation gives separation in the moral graph of the smallest ancestral
   set, `Lauritzen.moral_sep_of_dsep_lauritzen`). `Soundness/Counterexample` shows why
   the ancestral set must be the smallest one (`Counterexample.moral_sep_of_dsep_counterexample`).
4. The theorems: `Soundness/DSepSound` puts the layers together (`DSepSound.dsep_sound`),
   `Soundness/WalkPath` shows that walks and paths give the same d-separation
   (`DAG.dsepPath_iff_dsep`), and `Soundness/SetSound` repeats the route for sets
   (`SetSound.dsep_sound_set`).

`CondIndep` is stated multiplicatively, `P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)`, so no layer
needs division or positivity.
-/
