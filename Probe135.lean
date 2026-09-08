import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {G : DAG V}
    {A Z : Finset V}
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    {x y : V} (hxZ : x ∉ Z) (hyZ : y ∉ Z) (p : (moralGraph G A).Walk x y)
    (hp : ∀ z ∈ Z, z ∉ p.support.tail.dropLast) :
    ∀ inc : DAG.Incoming, ∃ q : DAG.Walk G x y,
      ¬ DAG.Walk.blockedAux (G := G) Z inc q := by
  induction p with
  | nil =>
    intro inc
    refine ⟨DAG.Walk.nil _, ?_⟩
    cases inc <;> simp [DAG.Walk.blockedAux]
  | @cons u v w h q ih =>
    intro inc
    simp only [moralGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨hne, hcase⟩ := h
    rcases hcase with ⟨huA, hvA, hedge | ⟨c, hcA, hue, hve⟩⟩ | ⟨hvA, huA, hedge | ⟨c, hcA, hve, hue⟩⟩
    · have hvZ : v ∉ Z := by
        intro hvz
        cases q with
        | nil => exact hyZ hvz
        | cons h2 q2 => exact hp v hvz (by simp [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil, SimpleGraph.Walk.support_ne_nil])
      obtain ⟨q2, hq2⟩ := ih hvZ hyZ (by sorry) DAG.Incoming.fwd
      refine ⟨DAG.Walk.fwd hedge q2, ?_⟩
      cases inc
      · exact hq2
      · intro hb
        simp [DAG.Walk.blockedAux] at hb
        rcases hb with h1 | h1
        · exact hxZ h1
        · exact hq2 h1
      · intro hb
        simp [DAG.Walk.blockedAux] at hb
        rcases hb with h1 | h1
        · exact hxZ h1
        · exact hq2 h1
    · sorry
    · sorry
    · sorry
