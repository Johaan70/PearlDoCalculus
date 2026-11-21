import PearlDoCalculus.Completeness.Rule3ChainCopy

/-!
# Completeness of rule 3 for single vertices

**What it proves.** Rule 3 of the do-calculus is exact for single vertices `y`, `z`: its
condition (d-separation of `y` and `z` given `X ∪ W` in `G_{X̄Z(W)̄}`) holds if and only if
its product form holds in every model on `G` and for all values (`rule3_iff`). The failure
direction is `rule3_complete`.

**Why it is needed.** With `rule1_iff` and `rule2_iff` (`Completeness/SingleRules.lean`)
this completes the do-calculus for single vertices. The chain lemmas of this file
(`rank_le_of_reach`, `Chain.mono`, `Chain.take`, `Chain.snoc`, `no_chain_of_dsep`) are
reused by the set version, `Completeness/Rule3SetFull.lean`.

**How the proof goes.** Three cases (`rule3_complete`).
1. `z` is not an ancestor of `W`: then `Z(W) = {z}` and `rule3_complete_nonanc` applies.
2. `z` is an ancestor of `W` (so `Z(W) = ∅`) and `y`, `z` are d-connected in `G_{X̄z̄}`:
   `z` can be made a root (`rule3_complete_root`).
3. The gap case (`rule3_complete_gap`): `y` and `z` are d-connected in `G_{X̄}` but
   d-separated in `G_{X̄z̄}`. Take a chain from `y` to `z` in `G_{X̄}` of minimal length,
   with distinct colliders. No source before the last reaches `z` (else a shorter chain
   would exist, `Chain.take`), and `z` does not reach `y` (else a trek from `z` would exist
   in `G_{X̄z̄}`). The first vertex `w1` of `X ∪ W` that `z` reaches lies in `W`. If `w1`
   were a collider `z_j`, cutting the chain after `s_j` and appending `z_j` and `z`
   (`Chain.snoc`) would give a chain that survives in `G_{X̄z̄}` (`Chain.cut`), a
   contradiction. So the chain-copy model of `Completeness/Rule3ChainCopy.lean` applies.

**Main results.** `rule3_iff`, `rule3_complete`, `rule3_complete_gap`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Chains in other graphs -/

section Rule3Full
open DoCalculus

/-- The rank does not decrease along a directed path. -/
lemma rank_le_of_reach {G : DAG V} {Z : Finset V} {s v : V} (h : ReachAvoid G Z s v) :
    G.rank s ≤ G.rank v := by
  have h' : Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) s v := h
  clear h
  induction h' with
  | refl => exact le_refl _
  | tail _ hbd ih => exact le_trans ih (le_of_lt (G.rank_strict_mono _ _ hbd.1))

/-- `ReachAvoid` passes to a graph with more edges. -/
lemma reach_mono {G1 G2 : DAG V} {Z : Finset V} {s v : V}
    (hE : ∀ a b, G1.edge a b → G2.edge a b) (h : ReachAvoid G1 Z s v) :
    ReachAvoid G2 Z s v :=
  Relation.ReflTransGen.mono (p := fun a b => G2.edge a b ∧ b ∉ Z)
    (fun a b hab => ⟨hE a b hab.1, hab.2⟩) h

/-- `RZ` passes to a graph with more edges. -/
lemma RZ_mono {G1 G2 : DAG V} {Z : Finset V} {s c : V}
    (hE : ∀ a b, G1.edge a b → G2.edge a b) (h : RZ G1 Z s c) : RZ G2 Z s c := by
  obtain ⟨p, hp, hr⟩ := h
  refine ⟨p, ?_, reach_mono hE hr⟩
  simp only [DAG.mem_parents] at hp ⊢
  exact hE _ _ hp

/-- A chain in a subgraph is a chain in the graph. -/
def Chain.mono {G1 G2 : DAG V} {Z : Finset V} {x y : V}
    (hE : ∀ a b, G1.edge a b → G2.edge a b) (C : Chain G1 Z x y) : Chain G2 Z x y where
  k := C.k
  s := C.s
  z := C.z
  hs := C.hs
  hz := C.hz
  hx := reach_mono hE C.hx
  hy := reach_mono hE C.hy
  hl := fun j => RZ_mono hE (C.hl j)
  hr := fun j => RZ_mono hE (C.hr j)

/-- A directed path whose start does not reach `c`, or is `c`, survives in `G_{c̄}`. -/
lemma reach_cut {H : DAG V} {Z : Finset V} {s c v : V}
    (hsrc : s = c ∨ ¬ ReachAvoid H Z s c) (h : ReachAvoid H Z s v) :
    ReachAvoid (cutIn H {c}) Z s v := by
  have h' : Relation.ReflTransGen (fun a b => H.edge a b ∧ b ∉ Z) s v := h
  clear h
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d hab hbd ih =>
    refine ih.tail ⟨(⟨hbd.1, ?_⟩ : H.edge b d ∧ d ∉ ({c} : Finset V)), hbd.2⟩
    intro hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    rcases hsrc with hsc | hn
    · have h1 : H.rank s ≤ H.rank b := rank_le_of_reach hab
      have h2 : H.rank b < H.rank d := H.rank_strict_mono b d hbd.1
      rw [hdc, ← hsc] at h2
      omega
    · exact hn (by rw [← hdc]; exact hab.tail hbd)

/-- `RZ` survives in `H_{c̄}` under the same condition, when `c ∉ Z` and the target lies in
`Z`. -/
lemma RZ_cut {H : DAG V} {Z : Finset V} {s c v : V} (hcZ : c ∉ Z) (hv : v ∈ Z)
    (hsrc : s = c ∨ ¬ ReachAvoid H Z s c) (h : RZ H Z s v) : RZ (cutIn H {c}) Z s v := by
  obtain ⟨p, hp, hr⟩ := h
  have hvc : v ∉ ({c} : Finset V) := by
    intro e
    rw [Finset.mem_singleton] at e
    rw [e] at hv
    exact hcZ hv
  exact ⟨p, mem_parents_cutIn.mpr ⟨hp, hvc⟩, reach_cut hsrc hr⟩

/-- A chain in which every source is `c` or does not reach `c` is a chain in `G_{c̄}`. -/
def Chain.cut {H : DAG V} {Z : Finset V} {x y c : V} (C : Chain H Z x y) (hcZ : c ∉ Z)
    (hsrc : ∀ i, C.s i = c ∨ ¬ ReachAvoid H Z (C.s i) c) : Chain (cutIn H {c}) Z x y where
  k := C.k
  s := C.s
  z := C.z
  hs := C.hs
  hz := C.hz
  hx := reach_cut (hsrc 0) C.hx
  hy := reach_cut (hsrc _) C.hy
  hl := fun j => RZ_cut hcZ (C.hz j) (hsrc _) (C.hl j)
  hr := fun j => RZ_cut hcZ (C.hz j) (hsrc _) (C.hr j)

/-- The start of a chain, up to and including source `m`. -/
def Chain.take {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y)
    (m : Fin (C.k + 1)) (h : ReachAvoid G Z (C.s m) y') : Chain G Z x y' where
  k := m.val
  s := fun i => C.s ⟨i.val, by have := i.2; have := m.2; omega⟩
  z := fun j => C.z ⟨j.val, by have := j.2; have := m.2; omega⟩
  hs := fun _ => C.hs _
  hz := fun _ => C.hz _
  hx := by
    have e : (⟨((0 : Fin (m.val + 1)) : ℕ), by simp⟩ : Fin (C.k + 1)) = 0 := Fin.ext (by simp)
    show ReachAvoid G Z (C.s ⟨((0 : Fin (m.val + 1)) : ℕ), _⟩) x
    rw [e]
    exact C.hx
  hy := by
    have e : (⟨((Fin.last m.val) : ℕ), m.2⟩ : Fin (C.k + 1)) = m := Fin.ext rfl
    show ReachAvoid G Z (C.s ⟨((Fin.last m.val) : ℕ), _⟩) y'
    rw [e]
    exact h
  hl := fun j => C.hl ⟨j.val, by have := j.2; have := m.2; omega⟩
  hr := fun j => C.hr ⟨j.val, by have := j.2; have := m.2; omega⟩

/-- The start of a chain with distinct colliders has distinct colliders. -/
lemma Chain.take_inj {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y)
    (m : Fin (C.k + 1)) (h : ReachAvoid G Z (C.s m) y') (hinj : Function.Injective C.z) :
    Function.Injective (C.take m h).z := by
  intro a b hab
  have e := hinj hab
  exact Fin.ext (Fin.mk.inj e)

/-- Append a new `Z` vertex `zc` and a new last source `s'` to a chain. -/
def Chain.snoc {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y) (zc s' : V)
    (hz : zc ∈ Z) (hs : s' ∉ Z) (hl : RZ G Z (C.s (Fin.last C.k)) zc) (hr : RZ G Z s' zc)
    (hy : ReachAvoid G Z s' y') : Chain G Z x y' where
  k := C.k + 1
  s := Fin.snoc (α := fun _ => V) C.s s'
  z := Fin.snoc (α := fun _ => V) C.z zc
  hs := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hs
    · simpa using C.hs j
  hz := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hz
    · simpa using C.hz j
  hx := by
    have e : (0 : Fin (C.k + 1 + 1)) = Fin.castSucc (0 : Fin (C.k + 1)) := Fin.ext (by simp)
    rw [e, Fin.snoc_castSucc]
    exact C.hx
  hy := by simpa using hy
  hl := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hl
    · simpa using C.hl j
  hr := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hr
    · simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
      exact C.hr j

/-- A property that holds for the sources of `C` and for `s'` holds for the sources of
`C.snoc`. -/
lemma Chain.snoc_src {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y) (zc s' : V)
    (hz : zc ∈ Z) (hs : s' ∉ Z) (hl : RZ G Z (C.s (Fin.last C.k)) zc) (hr : RZ G Z s' zc)
    (hy : ReachAvoid G Z s' y') (P : V → Prop) (hP : P s') (hC : ∀ i, P (C.s i)) :
    ∀ i, P ((C.snoc zc s' hz hs hl hr hy).s i) := by
  show ∀ i : Fin (C.k + 1 + 1), P (Fin.snoc (α := fun _ => V) C.s s' i)
  intro i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simpa using hP
  · simpa using hC i'

/-! ## The gap case -/

/-- A chain from `y` to `z` contradicts d-separation. -/
lemma no_chain_of_dsep {G' : DAG V} {Z : Finset V} {y z : V} (hyz : y ≠ z)
    (hsep : G'.DSeparated Z y z) (C : Chain G' Z y z) : False := by
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  exact chain_not_condIndep C' hinj hyz (DSepSound.dsep_sound (chainModel C') Z y z hsep)

/-- **The last case.** `z` is an ancestor of `W`, and `y` and `z` are d-connected in
`G_{X̄}` but d-separated in `G_{X̄z̄}`. Then a minimal chain and the first `W` vertex that `z`
reaches give the chain-copy model. -/
theorem rule3_complete_gap (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∈ ancestors (cutIn G X) W)
    (hcon : ¬ (cutIn (cutIn G X) ∅).DSeparated (X ∪ W) y z)
    (hsep : (cutIn (cutIn G X) {z}).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) ∅) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hcon (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C0⟩ := chain_of_open hy hz p hp
  have hE : ∀ a b, (cutIn (cutIn G X) ∅).edge a b → (cutIn G X).edge a b :=
    fun a b h => h.1
  obtain ⟨C1, hinj1⟩ := chain_injective _ (C0.mono hE) rfl
  have hP : ∃ n, ∃ C : Chain (cutIn G X) (X ∪ W) y z, C.k = n ∧ Function.Injective C.z :=
    ⟨C1.k, C1, rfl, hinj1⟩
  obtain ⟨C, hCk, hinj⟩ := Nat.find_spec hP
  -- no source before the last reaches z
  have hA : ∀ i : Fin (C.k + 1), i.val < C.k →
      ¬ ReachAvoid (cutIn G X) (X ∪ W) (C.s i) z := by
    intro i hi hr
    exact Nat.find_min hP (show i.val < Nat.find hP by omega)
      ⟨C.take i hr, rfl, C.take_inj i hr hinj⟩
  -- z does not reach y
  have hzy : ¬ ReachAvoid (cutIn G X) (X ∪ W) z y := by
    intro hr
    exact no_chain_of_dsep hyz hsep
      (Chain.trek z hz (reach_cut (Or.inl rfl) hr) Relation.ReflTransGen.refl)
  -- the first vertex of X ∪ W that z reaches lies in W
  obtain ⟨w, hwW, hzw0⟩ : ∃ w ∈ W, (cutIn G X).Reaches z w := by
    simpa [ancestors] using hanc
  obtain ⟨w1, hw1S, hzw⟩ := exists_first_Z hzw0 hz (Finset.mem_union_right X hwW)
  have hw1W : w1 ∈ W := by
    rcases Finset.mem_union.mp hw1S with h | h
    · exfalso
      obtain ⟨q, hq, _⟩ := hzw
      exact (mem_parents_cutIn.mp hq).2 h
    · exact h
  by_cases hc : ∃ j, C.z j = w1
  · -- w1 is a collider: cut the chain there and let z be the last source
    exfalso
    obtain ⟨j, hj⟩ := hc
    have hl : RZ (cutIn G X) (X ∪ W)
        ((C.take j.castSucc Relation.ReflTransGen.refl).s (Fin.last _)) (C.z j) := C.hl j
    have hr : RZ (cutIn G X) (X ∪ W) z (C.z j) := by
      rw [hj]
      exact hzw
    have hj2 := j.2
    exact no_chain_of_dsep hyz hsep (Chain.cut
      ((C.take j.castSucc Relation.ReflTransGen.refl).snoc (C.z j) z (C.hz j) hz hl hr
        Relation.ReflTransGen.refl) hz
      (Chain.snoc_src (C.take j.castSucc Relation.ReflTransGen.refl) (C.z j) z (C.hz j) hz hl hr
        Relation.ReflTransGen.refl (fun v => v = z ∨ ¬ ReachAvoid (cutIn G X) (X ∪ W) v z)
        (Or.inl rfl) (fun i => by
          have h1 : i.val < j.val + 1 := i.2
          exact Or.inr (hA ⟨i.val, by omega⟩ (show i.val < C.k by omega)))))
  · obtain ⟨M, x, t, hne⟩ := rule3_complete_chaincopy G X W y z w1 C hinj hyz hw1W
      (fun j e => hc ⟨j, e⟩) hzw hzy
    exact ⟨C.k, M, x, t, hne⟩

/-! ## Rule 3 for single vertices in all cases -/

/-- **Completeness of rule 3.** If the condition of `rule3_general` fails, there are a model
on `G` and values for which the product form of rule 3 fails. -/
theorem rule3_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  by_cases hanc : z ∈ ancestors (cutIn G X) W
  · have hZ2 : Rule3.Z2 (cutIn G X) {z} W = ∅ := by
      ext v
      simp only [Rule3.Z2, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hv⟩
        exact absurd hanc hv
      · intro hv
        simp at hv
    rw [hZ2] at h
    by_cases hroot : (cutIn (cutIn G X) {z}).DSeparated (X ∪ W) y z
    · exact rule3_complete_gap G X W y z hy hz hyz hanc h hroot
    · exact rule3_complete_root G X W y z hy hz hyz hroot
  · exact rule3_complete_nonanc G X W y z hy hz hyz hanc h

/-- **Rule 3 is exact.** For `y, z ∉ X ∪ W`, `y ≠ z`: the condition of rule 3 holds if and
only if the product form holds in every model on `G`. -/
theorem rule3_iff (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) :
    (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W))),
        (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M X x).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) {z} (t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x t
    exact Rule3Flag.rule3_general M X {y} {z} W x (Finset.disjoint_singleton.mpr hyz)
      (Finset.disjoint_singleton_right.mpr hz) (Finset.disjoint_singleton_left.mpr hy)
      (dsepSet_single h) t
  · intro H
    by_contra hn
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete G X W y z hy hz hyz hn
    exact hne (H k M x t)

end Rule3Full

end Completeness
