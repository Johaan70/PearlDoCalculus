import PearlDoCalculus.DSepSoundSkeleton.Basic
/-!
# Moralisation: from open walks to moral walks

**What it proves.** An open walk in `G` gives a walk in the moral graph that avoids `Z`.
Let `A` be closed under parents and contain the walk. If a walk `q` from `x` to `y` is
not blocked by `Z`, there is a walk from `x` to `y` in `moralGraph G A` whose interior
vertices are all outside `Z` (`moral_walk_of_open`). As a consequence, if `Z` separates
`x` from `y` in the moral graph, and every walk from `x` to `y` in `G` stays inside `A`,
then `x` and `y` are d-separated by `Z` (`dsep_of_moral_sep`). A small companion fact:
a moral edge that is not an edge of `G` comes from a shared child
(`moral_edge_witness`).

**Why it is here, and who uses it.** This is the converse of the graph step of the
Lauritzen route (see `DSepSoundSkeleton.lean`), and it is not part of the proof of
soundness. Soundness needs the other direction, from d-separation to separation in the
moral graph of `ancestors G ({x, y} ∪ Z)`; that is `Lauritzen.moral_sep_of_dsep_lauritzen`
(`Lauritzen.lean`), proved with the Bayes ball. No other file uses the results of this
file; `verification/AxiomCheck.lean` prints their axioms. The hypothesis of
`dsep_of_moral_sep` that every walk from `x` to `y` stays inside `A` is strong, so the
result is mainly a check that open walks and moral walks correspond as expected.

**How the proof goes.** Strong induction on the length of the walk
(`DAG.Walk.strong_length_induction`), because the collider case consumes two steps at
once. A step `a → b` or `a ← b` of `G` is an edge of the moral graph. At a collider
`a → b ← d` the walk is open, and the moral graph has the marriage edge `a — d`, so the
collider `b` is skipped and drops out of the moral walk. Every other interior vertex is
a non-collider of an open walk, hence outside `Z`. `mem_support_tail_dropLast` and
`mem_support_interior` handle the bookkeeping of interior vertices
(`support.tail.dropLast`).

**Main results.** `moral_edge_witness`, `moral_walk_of_open` and `dsep_of_moral_sep`.
-/

set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel

/-! ## Marriage edges and colliders

A marriage edge `u — w` in `moralGraph G A` that is not an edge of `G` comes from a
shared child `c ∈ A`, i.e. `u → c ← w`, a collider. Marriage edges and colliders are
the same phenomenon, which is what links walks in `G` to walks in the moral graph.
In the direction from moral walks back to open walks (`Lauritzen.lean`) the choice
`A = ancestors G ({x, y} ∪ Z)` matters: there every collider of the moral walk reaches
`x`, `y` or `Z`, and for an arbitrary closed `A` the correspondence fails
(`Counterexample.lean`).
-/

/-- A moral edge absent from `G` arises from a shared child. -/
lemma moral_edge_witness {A : Finset V} {u w : V}
    (h : (moralGraph G A).Adj u w) (h1 : ¬ G.edge u w) (h2 : ¬ G.edge w u) :
    ∃ c ∈ A, G.edge u c ∧ G.edge w c := by
  simp only [moralGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, hr | hr⟩ := h
  · obtain ⟨-, -, he | ⟨c, hc, huc, hwc⟩⟩ := hr
    · exact absurd he h1
    · exact ⟨c, hc, huc, hwc⟩
  · obtain ⟨-, -, he | ⟨c, hc, hwc, huc⟩⟩ := hr
    · exact absurd he h2
    · exact ⟨c, hc, huc, hwc⟩

/-- Every vertex of an ancestral set reaches its seed. -/
lemma reaches_seed_of_mem_ancestors {S : Finset V} {v : V}
    (hv : v ∈ ancestors G S) : ∃ s ∈ S, G.Reaches v s := by
  exact mem_ancestors_iff.mp hv

/-! ## Open walks give moral walks -/

/-- Strong induction on the length of a walk. Needed because the collider case of the
moralisation skips two constructors, not one. -/
lemma DAG.Walk.strong_length_induction
    {P : ∀ {x y : V}, DAG.Walk G x y → Prop}
    (step : ∀ {x y : V} (q : DAG.Walk G x y),
      (∀ {u w : V} (r : DAG.Walk G u w), r.length < q.length → P r) → P q)
    {x y : V} (q : DAG.Walk G x y) : P q := by
  have H : ∀ n : ℕ, ∀ {u w : V} (r : DAG.Walk G u w), r.length ≤ n → P r := by
    intro n
    induction n with
    | zero => intro u w r hr; exact step r (fun s hs => absurd hs (by omega))
    | succ m ihm =>
      intro u w r hr
      exact step r (fun s hs => ihm s (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hs hr)))
  exact H q.length q le_rfl


/-- `l.tail.dropLast` is a sublist of `l.dropLast`. -/
lemma tail_dropLast_sublist_dropLast {α : Type*} (l : List α) :
    l.tail.dropLast.Sublist l.dropLast := by
  cases l with
  | nil => simp
  | cons hd tl =>
    simp only [List.tail_cons]
    cases tl with
    | nil => simp
    | cons h t =>
      simp only [List.dropLast]
      exact List.sublist_cons_self _ _
/-- If `z` is not the start vertex, membership in `dropLast` survives removing the
head. -/
lemma mem_support_tail_dropLast {H : SimpleGraph V} {b c : V}
    (p : H.Walk b c) (z : V) (hzb : z ≠ b)
    (hmem : z ∈ p.support.dropLast) : z ∈ p.support.tail.dropLast := by
  cases hl : p.support with
  | nil => simp [hl] at hmem
  | cons hd tl =>
    have hhd : hd = b := by
      have h := SimpleGraph.Walk.head_support p
      simp [hl] at h
      exact h
    subst hhd
    rw [hl] at hmem
    cases tl with
    | nil => simp at hmem
    | cons h2 t2 =>
      simp [List.dropLast] at hmem ⊢
      rcases hmem with rfl | h
      · exact absurd rfl hzb
      · exact h
/--
From an open walk in `G` to a moral walk avoiding `Z` internally.

This is the direction Lauritzen's proof actually takes. On an open walk
every non-collider lies outside `Z` (else the walk would be blocked), and
every collider `u → c ← w` becomes a marriage edge `u — w`, so `c` drops
out of the moral walk's support entirely. Minimality is not needed:
openness supplies what is required.

Note: walks may self-intersect. Lauritzen (1996) needs this, and
`SimpleGraph.Walk` allows it, so the representation is on the right side of
that subtlety.
-/
lemma moral_walk_of_open {A Z : Finset V} (inc : DAG.Incoming)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    {x y : V} (q : DAG.Walk G x y)
    (hq : ¬ DAG.Walk.blockedAux (G := G) Z inc q)
    (hsupp : ∀ v ∈ q.support, v ∈ A) :
    ∃ p : (moralGraph G A).Walk x y,
      ∀ z ∈ Z, z ∉ p.support.tail.dropLast := by
  induction q using DAG.Walk.strong_length_induction generalizing inc with
  | step q ihq =>
    match q, hq, hsupp with
    | .nil v, _, _ => exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | @DAG.Walk.fwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge a (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inl ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 a (by simp [DAG.Walk.support])
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.fwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.fwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        rename_i d
        rw [hr] at hrest
        simp [DAG.Walk.blockedAux] at hrest
        obtain ⟨hopen, hr2⟩ := hrest
        by_cases hneab : a = d
        · subst hneab
          exact ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
            (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
        · have hmarry : (moralGraph G A).Adj a d := by
            simp only [moralGraph, SimpleGraph.fromRel_adj]
            refine ⟨hneab, Or.inl ⟨hsupp2 a (by simp [DAG.Walk.support]), ?_, Or.inr ⟨b, ?_, e, e2⟩⟩⟩
            · exact hsupp2 d (by rw [hr]; cases r2 <;> simp [DAG.Walk.support])
            · exact hsupp2 b (by rw [hr]; simp [DAG.Walk.support])
          cases hr2c : r2 with
          | nil w =>
            refine ⟨SimpleGraph.Walk.cons hmarry SimpleGraph.Walk.nil, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
          | fwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
          | bwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
    | @DAG.Walk.bwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge b (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inr ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
        · exact hsupp2 a (by simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.bwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
/-! ## Moral separation implies d-separation

There is no converse here for an arbitrary set `A` closed under parents. The statements
`open_walk_of_moral` and `moral_sep_of_dsep` were false in that generality: see
`Counterexample.lean` (graph `0 → 2 ← 1`). The correct statement, with
`A = ancestors G ({x, y} ∪ Z)`, is `Lauritzen.moral_sep_of_dsep_lauritzen`. -/

/-- A vertex of the support that is neither the start nor the end is an interior
vertex. The last step (`hgl`) is the identity that the last element of the tail of the
support is the end vertex. -/
lemma mem_support_interior {H : SimpleGraph V} {x y : V}
    (p : H.Walk x y) (z : V) (hzx : z ≠ x) (hzy : z ≠ y)
    (hmem : z ∈ p.support) : z ∈ p.support.tail.dropLast := by
  have hc := SimpleGraph.Walk.cons_tail_support p
  rw [← hc] at hmem
  rw [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact absurd h hzx
  · have hne : p.support.tail ≠ [] := by
      intro he
      rw [he] at h
      simp at h
    refine List.mem_dropLast_of_mem_of_ne_getLast h ?_
    have hgl : p.support.tail.getLast hne = y := by
      simp
    rw [hgl]
    exact hzy

/--
**Moralisation.** Separation in the moral graph implies d-separation in `G`, when every
walk from `x` to `y` stays inside `A` and `x, y ∉ Z`.

By contradiction: an open walk gives a moral walk that avoids `Z` in its interior
(`moral_walk_of_open`), and the separator must meet it, which is only possible at `x`
or `y`. The converse, for `A = ancestors G ({x, y} ∪ Z)`, is
`Lauritzen.moral_sep_of_dsep_lauritzen`; that is the direction soundness uses.
-/
theorem dsep_of_moral_sep (Z : Finset V) (x y : V) (A : Finset V)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hsep : Separates (moralGraph G A) Z x y)
    (hxy : ∀ (q : DAG.Walk G x y), ∀ v ∈ q.support, v ∈ A)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    G.DSeparated Z x y := by
  intro q
  by_contra hopen
  obtain ⟨p, hp⟩ := moral_walk_of_open DAG.Incoming.start hclosed q hopen (hxy q)
  obtain ⟨z, hzZ, hzmem⟩ := hsep p
  by_cases hzx : z = x
  · exact hxZ (hzx ▸ hzZ)
  by_cases hzy : z = y
  · exact hyZ (hzy ▸ hzZ)
  exact hp z hzZ (mem_support_interior p z hzx hzy hzmem)


end PearlDoCalculus
