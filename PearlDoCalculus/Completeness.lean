import PearlDoCalculus.Completeness.Trek
import PearlDoCalculus.Completeness.Chain
import PearlDoCalculus.Completeness.SingleRules
import PearlDoCalculus.Completeness.SetRules
import PearlDoCalculus.Completeness.Rule3ChainCopy
import PearlDoCalculus.Completeness.Rule3Full
import PearlDoCalculus.Completeness.Rule3SetFull

/-!
# Completeness of d-separation and of the do-rules

This file only collects the files of the `Completeness` folder, so that
`import PearlDoCalculus.Completeness` brings in the whole layer. The soundness results
(`DSepSound.dsep_sound`, the rules in `DoCalculus`, `Rule3Flag`) say that the graphical
conditions are sufficient; this folder proves that they are also necessary: whenever a
condition fails, some causal model on the graph violates the conclusion. So
d-separation and the three rules of the do-calculus are exact criteria
(`Completeness.dsep_iff`, `Completeness.dsepSet_iff`, `Completeness.rule1_iff_set`,
`Completeness.rule2_iff_set`, `Completeness.rule3_iff_set`).

The method throughout is to build explicit counter-models with Boolean values (copies,
ORs and XORs of parents) along the open path. The files, in order:

1. `Trek`: the collider-free case. A trek `x ← … ← s → … → y` outside `Z` gives a model
   in which `x` and `y` are dependent given `Z` (`trek_not_condIndep`).
2. `Chain`: the general case. A minimal open chain (a walk without repeated vertices)
   is extracted from a d-connecting walk, and XOR vertices along it make the endpoints
   dependent; this gives the completeness of d-separation (`dsep_complete`, `dsep_iff`,
   `dsepPath_iff`).
3. `SingleRules`: rules 1, 2 and 3 are complete for single vertices (section `RuleIff`);
   also the lifted models `liftSub` that later counter-models build on.
4. `SetRules`: the set versions, `dsepSet_iff`, `rule1_iff_set`, `rule2_iff_set`, and
   rule 3 for sets when no `z ∈ Z` is an ancestor of `W`.
5. `Rule3ChainCopy`: the chain-copy model for the case of rule 3 where the separating
   path needs a chain of vertices (`rule3_complete_chaincopy`).
6. `Rule3Full`: rule 3 for single vertices in all cases (`rule3_complete`, `rule3_iff`).
7. `Rule3SetFull`: rule 3 for sets in all cases (`rule3_complete_set`, `rule3_iff_set`).
-/
