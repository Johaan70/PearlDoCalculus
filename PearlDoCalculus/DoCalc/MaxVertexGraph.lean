/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.NonAncestors

/-!
# Graph lemmas for the block step: a vertex without children

Phase 4 of `docs/design-docalc-completeness.md` derives c-component factorization and the
`block` step of IDENTIFY by Tian's recursion: take a vertex `m` of `T ∖ U` of maximal rank,
split it off with the chain rule, and handle the two factors with rules 2 and 3. This file
proves the graph facts behind those two uses of the rules.

**Setting.** `U` are the latent vertices, all roots (`hroot`), and `O = Uᶜ`. `T` is a set
of vertices (it may contain latents), and `m ∈ T ∖ U` has no child in `T ∖ U` (`hmax`).
A vertex of maximal rank in `T ∖ U` has this property (`exists_childless`), since edges
increase the rank.

**Rule 3: `m` is not an ancestor** (`disjoint_ancestors_childless`). In `G` without the
edges into `X`, for any `X ⊇ O ∖ T`, `m` has no children at all: a child is not in `X`,
not latent (latents are roots), so it is in `T ∖ U`. Hence `m` is an ancestor of no set
that avoids `m`.

**Rule 2: the d-separation** (`dsepSet_rule2_block`). Let `S` be closed in `T` (no latent
edge into `T` crosses the boundary of `S`: the hypothesis `hcl` of
`IdentifyDerives.block`), with `m ∈ S`. Write `X = O ∖ T`, `A = (T ∖ U) ∖ S` and
`W = (T ∖ {m} ∩ S) ∖ U`. Then `{m}` and `A` are d-separated by `X ∪ W` in `G_{X̄ A̲}`
(`G` without the edges into `X` and out of `A`). This is the side condition of rule 2 that
turns `P(m | A, W, do X)` into `P(m | W, do(X ∪ A))`.

*How the proof goes.* Call `R = A ∪ (U ∖ S)`. In `G_{X̄ A̲}` the vertices of `A` have no
out-edges and the latents have no in-edges. A latent parent of a vertex of `A` is not in
`S`, and a latent outside `S` has all its children in `T` outside `S`, that is in `A`
(closedness). So every edge into `R` starts in `X`, in `W` or at `m`. Follow an open walk
backwards from its end in `A` (`open_walk_block`): it stays in `R` until it reaches the
vertex where it entered `R`. That vertex is the tail of the entering edge, so it is a
non-collider; it is not in the conditioning set `X ∪ W` only if it is the start `m`.
But `m` has no child in `A`.

**Main results.** `exists_childless`, `disjoint_ancestors_childless`, `open_walk_block`,
`dsepSet_rule2_block`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {U T : Finset V}

/-! ## A vertex of maximal rank has no child -/

/-- **A vertex without children.** A nonempty set `T ∖ U` has a vertex of maximal rank,
and it has no child in `T ∖ U`. -/
lemma exists_childless (G : DAG V) (h : (T \ U).Nonempty) :
    ∃ m ∈ T \ U, ∀ v ∈ T \ U, ¬ G.edge m v := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (T \ U) G.rank h
  exact ⟨m, hm, fun v hv e => absurd (hmax v hv) (not_le.mpr (G.rank_strict_mono m v e))⟩

/-! ## Rule 3: the childless vertex is not an ancestor -/

/-- **`m` is not an ancestor.** If the latents are roots and `m` has no child in `T ∖ U`,
then in `G` without the edges into `X ⊇ O ∖ T`, `m` is an ancestor of no set `B` that
avoids `m`. -/
lemma disjoint_ancestors_childless (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {m : V}
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) {X B : Finset V} (hX : Uᶜ \ T ⊆ X) (hmB : m ∉ B) :
    Disjoint {m} (ancestors (cutIn G X) B) := by
  rw [Finset.disjoint_singleton_left]
  intro hm
  obtain ⟨b, hb, hr⟩ := mem_ancestors_iff.mp hm
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨c, ⟨e, hcX⟩, -⟩
  · exact hmB hb
  · have hcU : c ∉ U := fun hcU => hroot c hcU m e
    have hcT : c ∈ T := by
      by_contra hcT
      exact hcX (hX (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hcU, hcT⟩))
    exact hmax c (Finset.mem_sdiff.mpr ⟨hcT, hcU⟩) e

/-! ## Rule 2: the d-separation of the block step -/

section Rule2

variable {S : Finset V} {m : V}

/-- **Open walks into `A`.** In `G_{X̄ A̲}`, with `X = O ∖ T` and `A = (T ∖ U) ∖ S`, let `q`
be a walk from `b` to a vertex of `A`, open given `X ∪ W` and entered with direction `inc`.
Then `b ∈ A`, or `b` is a latent outside `S`, or `q` starts at `b` (`inc = start`) and `b`
has a child in `A`. -/
lemma open_walk_block (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    ∀ {b a : V} (q : Walk (cutOut (cutIn G (Uᶜ \ T)) ((T \ U) \ S)) b a) (inc : Incoming),
      a ∈ (T \ U) \ S →
      ¬ Walk.blockedAux ((Uᶜ \ T) ∪ ((T.erase m ∩ S) \ U)) inc q →
      b ∈ (T \ U) \ S ∨ (b ∈ U ∧ b ∉ S) ∨ (inc = .start ∧ ∃ c ∈ (T \ U) \ S, G.edge b c) := by
  intro b a q
  induction q with
  | nil v => exact fun _ ha _ => Or.inl ha
  | @fwd x y z e rest ih =>
    -- the walk follows the edge `x → y`
    intro inc hz hq
    have hq' : ¬ Walk.blockedAux ((Uᶜ \ T) ∪ ((T.erase m ∩ S) \ U)) .fwd rest := by
      cases inc <;> simp only [Walk.blockedAux, not_or] at hq <;> tauto
    have hxA : x ∉ (T \ U) \ S := e.2
    replace e : G.edge x y := e.1.1
    -- `y` has a parent, so it is not latent: it lies in `A`
    have hyA : y ∈ (T \ U) \ S := by
      rcases ih .fwd hz hq' with h | ⟨hyU, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd e (hroot y hyU x)
      · exact nomatch h
    have hy := Finset.mem_sdiff.mp hyA
    by_cases hxU : x ∈ U
    · exact Or.inr (Or.inl ⟨hxU, fun hxS =>
        hy.2 ((hcl x hxU y (Finset.mem_sdiff.mp hy.1).1 e).mp hxS)⟩)
    · refine Or.inr (Or.inr ?_)
      cases inc
      · exact ⟨rfl, y, hyA, e⟩
      all_goals
        -- `x` is an interior non-collider, so it is not conditioned on
        exfalso
        simp only [Walk.blockedAux, not_or] at hq
        apply hq.1
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl, Finset.mem_inter,
          Finset.mem_erase]
        by_cases hxT : x ∈ T
        · have hxS : x ∈ S := by
            by_contra hxS
            exact hxA (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxT, hxU⟩, hxS⟩)
          by_cases hxm : x = m
          · subst hxm
            exact absurd e (hmax y hy.1)
          · exact Or.inr ⟨⟨⟨hxm, hxT⟩, hxS⟩, hxU⟩
        · exact Or.inl ⟨hxU, hxT⟩
  | @bwd x y z e rest ih =>
    -- the walk goes against the edge `y → x`
    intro inc hz hq
    have hq' : ¬ Walk.blockedAux ((Uᶜ \ T) ∪ ((T.erase m ∩ S) \ U)) .bwd rest := by
      cases inc <;> simp only [Walk.blockedAux, not_or] at hq <;> tauto
    obtain ⟨⟨e, hxX⟩, hyA⟩ := e
    rcases ih .bwd hz hq' with h | ⟨hyU, hyS⟩ | ⟨h, -⟩
    · exact absurd h hyA
    · -- `x` is a child of the latent `y ∉ S`, inside `T`: it lies in `A`
      have hxU : x ∉ U := fun hxU => hroot x hxU y e
      have hxT : x ∈ T := by
        by_contra hxT
        exact hxX (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hxU, hxT⟩)
      exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxT, hxU⟩,
        fun hxS => hyS ((hcl y hyU x hxT e).mpr hxS)⟩)
    · exact nomatch h

/-- **The side condition of rule 2 in the block step.** With the latents roots, `S` closed
in `T`, and `m ∈ S ∖ U` without children in `T ∖ U`: `{m}` and `A = (T ∖ U) ∖ S` are
d-separated by `X ∪ W` in `G_{X̄ A̲}`, where `X = O ∖ T` and `W = (T ∖ {m} ∩ S) ∖ U`. -/
theorem dsepSet_rule2_block (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hcl : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ S ↔ v ∈ S))
    (hmU : m ∉ U) (hmS : m ∈ S) (hmax : ∀ v ∈ T \ U, ¬ G.edge m v) :
    SetSound.DSeparatedSet (cutOut (cutIn G (Uᶜ \ T)) ((T \ U) \ S))
      ((Uᶜ \ T) ∪ ((T.erase m ∩ S) \ U)) {m} ((T \ U) \ S) := by
  intro y hy a ha p _
  obtain rfl := Finset.mem_singleton.mp hy
  by_contra hp
  rcases open_walk_block hroot hcl hmax p .start ha hp with h | ⟨h, -⟩ | ⟨-, c, hc, e⟩
  · exact (Finset.mem_sdiff.mp h).2 hmS
  · exact hmU h
  · exact hmax c (Finset.mem_sdiff.mp hc).1 e

end Rule2

end DoCalc
