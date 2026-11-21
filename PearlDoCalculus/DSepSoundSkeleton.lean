import PearlDoCalculus.DSepSoundSkeleton.Moralisation
import PearlDoCalculus.DSepSoundSkeleton.AncestralReduction
import PearlDoCalculus.DSepSoundSkeleton.Separator

/-!
# Soundness of d-separation: the layers of the Lauritzen route

This file only collects the files of the `DSepSoundSkeleton` folder. Together with
`Lauritzen.lean` they give everything that the soundness theorem `DSepSound.dsep_sound`
(in `DSepSound.lean`) puts together: if `x` and `y` are d-separated by `Z`, then in every
causal model on the graph `x` and `y` are conditionally independent given `Z`.

**The route.** Pearl proves soundness by induction over blocked and open walks. That is
hard to formalise, because `blockedAux` carries state along the walk, so being blocked is
not local to one step. The proof here follows Lauritzen instead, with the graph part and
the probability part kept apart:

    d-separation in G
      ⟹ (restrict to an ancestral set)
    d-separation in G.induce (ancestors G ({x, y} ∪ Z))
      ⟹ (moralise; Lauritzen.lean)
    vertex separation in the moral graph
      ⟹ (the joint factorizes along the separator)
    conditional independence

**The layers**, from the bottom:

0. `DSepSoundSkeleton/Basic`: induced subgraphs `DAG.induce`, ancestor sets `ancestors`,
   the moral graph `moralGraph`, vertex separation `Separates`, and the fact that every
   family `{v} ∪ parents v` is a clique of the moral graph (`moral_family_clique`).
1. Probability:
   - `DSepSoundSkeleton/AssignmentCasts` (1a): bookkeeping lemmas about assignments
     (`extend`, `extendOverList`, splitting indicators, `restrict_cast_*`).
   - `DSepSoundSkeleton/Factorizes` (1b): `jointUpTo` factorizes into a left and a right
     part when the two sides are separated by `Z` (`jointUpTo_factorizes`).
   - `DSepSoundSkeleton/AncestralReduction` (1c): the joint is a product of kernel factors
     `kfac`, and the marginal on an ancestral set is the joint of the restricted model
     (`marginal_eq_restricted_joint`).
2. `DSepSoundSkeleton/Moralisation`: the converse of the graph step. An open walk gives a
   walk in the moral graph of an ancestral set that avoids `Z` (`moral_walk_of_open`), so
   separation in the moral graph implies d-separation (`dsep_of_moral_sep`). The direction
   that soundness needs, from d-separation to moral separation, is
   `Lauritzen.moral_sep_of_dsep_lauritzen` (`Lauritzen.lean`); no other file uses this
   layer.
3. `DSepSoundSkeleton/Separator`: if `Z` separates `x` from `y` in an undirected graph,
   the vertices split as `L ∪ Z ∪ R`, the joint has the product form `f(L,Z) · g(R,Z)`
   (`joint_splits`), and the product form gives conditional independence
   (`condIndep_of_product_form`).

`CondIndep` is stated multiplicatively, `P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)`, so no layer
needs division or positivity.
-/
