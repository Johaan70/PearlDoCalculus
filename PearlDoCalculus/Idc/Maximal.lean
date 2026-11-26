/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Idc.Check
import PearlDoCalculus.Rule3

/-!
# The moved set does not depend on the order of the moves

The IDC check (`Idc/Check`) moves, in rounds, every conditioning variable that rule 2
allows into the intervention. The algorithm of Shpitser and Pearl moves them one at a
time, in any order. This file shows that both give the same set
(`docs/design-idc.md`, step 2): the moved set `M*` of the check is the largest set that
single moves reach from `(∅, W)`, and it is reached.

**The key lemma** (`Movable.after_move`). If `w` is movable from `(M, W')` and `w' ≠ w` is
another vertex of `W'`, then `w` is still movable after `w'` has been moved. The set that
rule 2 conditions on is the same before and after, `(X ∪ M) ∪ (W' ∖ {w})`, because `w'`
only goes from one part of it to the other. The graph loses the edges into `w'`, and
d-separation survives the removal of edges (`Rule3.dsepSet_mono`). So `w'` need not be
movable itself; the form where both are movable is `Movable.after_move_of_movable`.
Before this was proved, the statement was checked by exhaustive search on small graphs
with latent vertices (`verification/idc_monotone_check.py`).

**In the states that are reached** the rest is always `W' = W ∖ M` (`Reachable.eq_sdiff`),
so the conditioning set is `X ∪ (W ∖ {w})` for every `M`, and moving more vertices only
removes edges. Hence movability is monotone in `M` (`movable_mono`).

**The three facts.**

1. *Every reachable set lies in `M*`* (`Reachable.subset_movedSet`). By induction on the
   moves: if `M ⊆ M*` and `w` is movable from `M`, then `w` is movable from `M*` by
   monotonicity, so the round at `M*` would add it; but `M*` is a fixed point of the
   round (`moveRound_movedSet`), so `w ∈ M*`.
2. *`M*` is reached* (`reachable_movedSet`). Each round is a sequence of single moves:
   the vertices it adds stay movable while the others are moved, by monotonicity
   (`Reachable.moveRound`).
3. *Nothing more can be moved from `M*`* (`not_movable_movedSet`), since `M*` is a fixed
   point of the round.

**Main results.** `Movable.after_move`, `Movable.after_move_of_movable`,
`movable_mono`, `Reachable.subset_movedSet`, `reachable_movedSet`, `not_movable_movedSet`.
-/

open PearlDoCalculus DAG DoCalculus Classical

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {X Y W : Finset V}

/-! ## Monotonicity of a single move -/

/-- Intervening on more vertices removes more edges: `G_{\overline{A'}, \underline{w}}` is a
subgraph of `G_{\overline{A}, \underline{w}}` for `A ⊆ A'`. -/
lemma edge_cutOut_cutIn_mono {A A' : Finset V} (hA : A ⊆ A') (w : V) (u v : V)
    (h : (cutOut (cutIn G A') {w}).edge u v) : (cutOut (cutIn G A) {w}).edge u v :=
  ⟨⟨h.1.1, fun hv => h.1.2 (hA hv)⟩, h.2⟩

/-- **Monotonicity of a move.** If `w` is movable from `(M, W')` and `w' ≠ w` lies in `W'`,
then `w` is still movable after `w'` has been moved into the intervention. -/
theorem Movable.after_move {M W' : Finset V} {w w' : V} (hw : Movable G X Y M W' w)
    (hw' : w' ∈ W') (hne : w ≠ w') : Movable G X Y (insert w' M) (W'.erase w') w := by
  refine ⟨Finset.mem_erase.mpr ⟨hne, hw.1⟩, ?_⟩
  have hZ : (X ∪ insert w' M) ∪ (W'.erase w' \ {w}) = (X ∪ M) ∪ (W' \ {w}) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_singleton]
    constructor
    · rintro ((hX | rfl | hM) | ⟨⟨-, hW⟩, hvw⟩)
      · exact Or.inl (Or.inl hX)
      · exact Or.inr ⟨hw', fun h => hne h.symm⟩
      · exact Or.inl (Or.inr hM)
      · exact Or.inr ⟨hW, hvw⟩
    · rintro ((hX | hM) | ⟨hW, hvw⟩)
      · exact Or.inl (Or.inl hX)
      · exact Or.inl (Or.inr (Or.inr hM))
      · by_cases hv : v = w'
        · exact Or.inl (Or.inr (Or.inl hv))
        · exact Or.inr ⟨⟨hv, hW⟩, hvw⟩
  rw [hZ]
  exact Rule3.dsepSet_mono (edge_cutOut_cutIn_mono
    (Finset.union_subset_union (Finset.Subset.refl X) (Finset.subset_insert w' M)) w) hw.2

/-- **Monotonicity of a move**, in the form where both vertices are movable: if `w` and
`w'` are both movable from `(M, W')`, then `w` is still movable after moving `w'`. -/
theorem Movable.after_move_of_movable {M W' : Finset V} {w w' : V} (hw : Movable G X Y M W' w)
    (hw' : Movable G X Y M W' w') (hne : w ≠ w') :
    Movable G X Y (insert w' M) (W'.erase w') w :=
  hw.after_move hw'.1 hne

/-- **Movability is monotone in the moved set**, when the rest is `W ∖ M`: the
conditioning set is `X ∪ (W ∖ {w})` for every `M`, and the graph only loses edges. -/
theorem movable_mono {M M' : Finset V} {w : V} (hMM : M ⊆ M') (hM'W : M' ⊆ W) (hw : w ∉ M')
    (h : Movable G X Y M (W \ M) w) : Movable G X Y M' (W \ M') w := by
  have hwW : w ∈ W := (Finset.mem_sdiff.mp h.1).1
  refine ⟨Finset.mem_sdiff.mpr ⟨hwW, hw⟩, ?_⟩
  have hZ : ∀ N, N ⊆ W → w ∉ N → (X ∪ N) ∪ ((W \ N) \ {w}) = X ∪ (W \ {w}) := by
    intro N hNW hwN
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ((hX | hN) | ⟨⟨hW, -⟩, hvw⟩)
      · exact Or.inl hX
      · exact Or.inr ⟨hNW hN, fun h => hwN (h ▸ hN)⟩
      · exact Or.inr ⟨hW, hvw⟩
    · rintro (hX | ⟨hW, hvw⟩)
      · exact Or.inl (Or.inl hX)
      · by_cases hN : v ∈ N
        · exact Or.inl (Or.inr hN)
        · exact Or.inr ⟨⟨hW, hN⟩, hvw⟩
  have h2 := h.2
  rw [hZ M (hMM.trans hM'W) (fun h => hw (hMM h))] at h2
  rw [hZ M' hM'W hw]
  exact Rule3.dsepSet_mono
    (edge_cutOut_cutIn_mono (Finset.union_subset_union (Finset.Subset.refl X) hMM) w) h2

/-! ## The states that single moves reach -/

/-- **In a reached state the rest is `W ∖ M`**, and `M ⊆ W`. -/
theorem Reachable.eq_sdiff {s : Finset V × Finset V} (h : Reachable G X Y W s) :
    s.1 ⊆ W ∧ s.2 = W \ s.1 := by
  induction h with
  | refl => exact ⟨Finset.empty_subset W, Finset.sdiff_empty.symm⟩
  | tail _ hst ih =>
    obtain ⟨w, hw, rfl⟩ := hst
    obtain ⟨hMW, hrest⟩ := ih
    rw [hrest] at hw ⊢
    have hwW : w ∈ W := (Finset.mem_sdiff.mp hw.1).1
    exact ⟨Finset.insert_subset hwW hMW, (Finset.sdiff_insert W _ w).symm⟩

/-- A reached state is `(M, W ∖ M)`: a move from there gives `(insert w M, W ∖ insert w M)`. -/
lemma Reachable.move {M : Finset V} {w : V} (h : Reachable G X Y W (M, W \ M))
    (hw : Movable G X Y M (W \ M) w) : Reachable G X Y W (insert w M, W \ insert w M) := by
  refine Relation.ReflTransGen.tail h ⟨w, hw, ?_⟩
  rw [Finset.sdiff_insert]

/-- **Every reachable set lies in the moved set** `M*` of the check. -/
theorem Reachable.subset_movedSet {s : Finset V × Finset V} (h : Reachable G X Y W s) :
    s.1 ⊆ movedSet G X Y W := by
  induction h with
  | refl => exact Finset.empty_subset _
  | @tail s t hs hst ih =>
    obtain ⟨w, hw, rfl⟩ := hst
    obtain ⟨-, hrest⟩ := Reachable.eq_sdiff hs
    rw [hrest] at hw
    refine Finset.insert_subset ?_ ih
    by_contra hwM
    have hm := movable_mono ih (movedSet_subset G X Y W) hwM hw
    have hin : w ∈ moveRound G X Y W (movedSet G X Y W) :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm.1, hm⟩)
    rw [moveRound_movedSet] at hin
    exact hwM hin

/-- **One round is a sequence of single moves.** From a reached state `(M, W ∖ M)`, moving
any set `F` of vertices that are movable now, one at a time, reaches `(M ∪ F, W ∖ (M ∪ F))`;
each stays movable while the others are moved (`movable_mono`). -/
theorem Reachable.union_of_movable {M : Finset V} (h : Reachable G X Y W (M, W \ M)) :
    ∀ F : Finset V, (∀ w ∈ F, Movable G X Y M (W \ M) w) →
      Reachable G X Y W (M ∪ F, W \ (M ∪ F)) := by
  have hMW : M ⊆ W := h.eq_sdiff.1
  intro F
  induction F using Finset.induction_on with
  | empty => intro _; rwa [Finset.union_empty]
  | @insert a F haF ih =>
    intro hF
    have hF' := ih (fun w hw => hF w (Finset.mem_insert_of_mem hw))
    have ha := hF a (Finset.mem_insert_self a F)
    have haW : a ∈ W := (Finset.mem_sdiff.mp ha.1).1
    have haM : a ∉ M := (Finset.mem_sdiff.mp ha.1).2
    have hMF : M ∪ F ⊆ W := Finset.union_subset hMW fun w hw =>
      (Finset.mem_sdiff.mp (hF w (Finset.mem_insert_of_mem hw)).1).1
    have hm := movable_mono Finset.subset_union_left hMF
      (fun h => (Finset.mem_union.mp h).elim haM haF) ha
    have hr := hF'.move hm
    rwa [show insert a (M ∪ F) = M ∪ insert a F by
      rw [Finset.union_insert]] at hr

/-- **A round is reached** from a reached state. -/
theorem Reachable.moveRound {M : Finset V} (h : Reachable G X Y W (M, W \ M)) :
    Reachable G X Y W (moveRound G X Y W M, W \ moveRound G X Y W M) :=
  h.union_of_movable _ fun _ hw => (Finset.mem_filter.mp hw).2

/-- **The moved set is reached** by single moves from `(∅, W)`. -/
theorem reachable_movedSet :
    Reachable G X Y W (movedSet G X Y W, W \ movedSet G X Y W) := by
  have key : ∀ k, Reachable G X Y W ((moveRound G X Y W)^[k] ∅, W \ (moveRound G X Y W)^[k] ∅) := by
    intro k
    induction k with
    | zero =>
      show Reachable G X Y W (∅, W \ ∅)
      rw [Finset.sdiff_empty]
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.moveRound
  exact key W.card

/-- **Nothing more can be moved** from the moved set. -/
theorem not_movable_movedSet (w : V) :
    ¬ Movable G X Y (movedSet G X Y W) (W \ movedSet G X Y W) w := by
  intro hm
  have hin : w ∈ Idc.moveRound G X Y W (movedSet G X Y W) :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm.1, hm⟩)
  rw [moveRound_movedSet] at hin
  exact (Finset.mem_sdiff.mp hm.1).2 hin

end Idc
