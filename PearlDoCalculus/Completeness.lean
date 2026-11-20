import PearlDoCalculus.Completeness.SetRules
import PearlDoCalculus.Completeness.Rule3Copy
import PearlDoCalculus.Completeness.Rule3ChainCopy

/-!
# Completeness of d-separation: the do-rules

The trek, chain, single-node rule and set rule parts live in
`Completeness/Trek.lean`, `Completeness/Chain.lean`,
`Completeness/SingleRules.lean`, `Completeness/SetRules.lean` and
`Completeness/Rule3Copy.lean` and `Completeness/Rule3ChainCopy.lean`; this file
continues with the full completeness of rule 3.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Regel 3: fullstendighet i alle tilfeller -/

section Rule3Full
open DoCalculus

lemma rank_le_of_reach {G : DAG V} {Z : Finset V} {s v : V} (h : ReachAvoid G Z s v) :
    G.rank s ≤ G.rank v := by
  have h' : Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) s v := h
  clear h
  induction h' with
  | refl => exact le_refl _
  | tail _ hbd ih => exact le_trans ih (le_of_lt (G.rank_strict_mono _ _ hbd.1))

lemma reach_mono {G1 G2 : DAG V} {Z : Finset V} {s v : V}
    (hE : ∀ a b, G1.edge a b → G2.edge a b) (h : ReachAvoid G1 Z s v) :
    ReachAvoid G2 Z s v :=
  Relation.ReflTransGen.mono (p := fun a b => G2.edge a b ∧ b ∉ Z)
    (fun a b hab => ⟨hE a b hab.1, hab.2⟩) h

lemma RZ_mono {G1 G2 : DAG V} {Z : Finset V} {s c : V}
    (hE : ∀ a b, G1.edge a b → G2.edge a b) (h : RZ G1 Z s c) : RZ G2 Z s c := by
  obtain ⟨p, hp, hr⟩ := h
  refine ⟨p, ?_, reach_mono hE hr⟩
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hE _ _ hp

/-- En kjede i en delgraf er en kjede i grafen. -/
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

/-- En rettet vei som ikke når `c`, eller som starter i `c`, overlever i `G_{c̄}`. -/
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

lemma RZ_cut {H : DAG V} {Z : Finset V} {s c v : V} (hcZ : c ∉ Z) (hv : v ∈ Z)
    (hsrc : s = c ∨ ¬ ReachAvoid H Z s c) (h : RZ H Z s v) : RZ (cutIn H {c}) Z s v := by
  obtain ⟨p, hp, hr⟩ := h
  have hvc : v ∉ ({c} : Finset V) := by
    intro e
    rw [Finset.mem_singleton] at e
    rw [e] at hv
    exact hcZ hv
  exact ⟨p, mem_parents_cutIn.mpr ⟨hp, hvc⟩, reach_cut hsrc hr⟩

/-- En kjede der hver kilde er `c` eller ikke når `c`, er en kjede i `G_{c̄}`. -/
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

/-- Starten av en kjede, til og med kilde `m`. -/
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

lemma Chain.take_inj {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y)
    (m : Fin (C.k + 1)) (h : ReachAvoid G Z (C.s m) y') (hinj : Function.Injective C.z) :
    Function.Injective (C.take m h).z := by
  intro a b hab
  have e := hinj hab
  exact Fin.ext (Fin.mk.inj e)

/-- Heng en ny Z-node `zc` og en ny siste kilde `s'` bak en kjede. -/
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

/-- En egenskap som holder for kildene i `C` og for `s'`, holder for kildene i `C.snoc`. -/
lemma Chain.snoc_src {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y) (zc s' : V)
    (hz : zc ∈ Z) (hs : s' ∉ Z) (hl : RZ G Z (C.s (Fin.last C.k)) zc) (hr : RZ G Z s' zc)
    (hy : ReachAvoid G Z s' y') (P : V → Prop) (hP : P s') (hC : ∀ i, P (C.s i)) :
    ∀ i, P ((C.snoc zc s' hz hs hl hr hy).s i) := by
  show ∀ i : Fin (C.k + 1 + 1), P (Fin.snoc (α := fun _ => V) C.s s' i)
  intro i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simpa using hP
  · simpa using hC i'

/-- En kjede fra `y` til `z` motsier d-separasjon. -/
lemma no_chain_of_dsep {G' : DAG V} {Z : Finset V} {y z : V} (hyz : y ≠ z)
    (hsep : G'.DSeparated Z y z) (C : Chain G' Z y z) : False := by
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  exact chain_not_condIndep C' hinj hyz (DSepSound.dsep_sound (chainModel C') Z y z hsep)

/-- **Det siste tilfellet.** `z` er forfar til `W`, `y` og `z` er d-forbundet i `G_{X̄}`,
men d-separert i `G_{X̄z̄}`. Da gir en minimal kjede og den første `W`-noden `z` når,
kjede-kopi-modellen. -/
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
  -- ingen kilde før den siste når z
  have hA : ∀ i : Fin (C.k + 1), i.val < C.k →
      ¬ ReachAvoid (cutIn G X) (X ∪ W) (C.s i) z := by
    intro i hi hr
    exact Nat.find_min hP (show i.val < Nat.find hP by omega)
      ⟨C.take i hr, rfl, C.take_inj i hr hinj⟩
  -- z når ikke y
  have hzy : ¬ ReachAvoid (cutIn G X) (X ∪ W) z y := by
    intro hr
    exact no_chain_of_dsep hyz hsep
      (Chain.trek z hz (reach_cut (Or.inl rfl) hr) Relation.ReflTransGen.refl)
  -- den første noden i X ∪ W som z når, ligger i W
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
  · -- w1 er en kollider: kutt kjeden der og la z være siste kilde
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

/-- **Fullstendighet for regel 3.** Svikter betingelsen i `rule3_general`, finnes en
modell på `G` og verdier der produktformen i regel 3 svikter. -/
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

/-- **Regel 3 er eksakt.** For `y, z ∉ X ∪ W`, `y ≠ z`: betingelsen i regel 3 holder
hvis og bare hvis produktformen holder i hver modell på `G`. -/
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

/-! ## Regel 3 for mengder: fullstendighet i alle tilfeller -/

section Rule3SetFull
open DoCalculus

lemma reach_avoid_mono {G : DAG V} {Z1 Z2 : Finset V} {s v : V} (h12 : Z1 ⊆ Z2)
    (h : ReachAvoid G Z2 s v) : ReachAvoid G Z1 s v :=
  Relation.ReflTransGen.mono (p := fun a b => G.edge a b ∧ b ∉ Z1)
    (fun a b hab => ⟨hab.1, fun hb => hab.2 (h12 hb)⟩) h

lemma RZ_avoid_mono {G : DAG V} {Z1 Z2 : Finset V} {s c : V} (h12 : Z1 ⊆ Z2)
    (h : RZ G Z2 s c) : RZ G Z1 s c := by
  obtain ⟨p, hp, hr⟩ := h
  exact ⟨p, hp, reach_avoid_mono h12 hr⟩

lemma reach_notin {G : DAG V} {A : Finset V} {s v : V} (h : ReachAvoid G A s v) :
    v = s ∨ v ∉ A := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨p, _, hpv⟩
  · exact Or.inl e
  · exact Or.inr hpv.2

lemma rank_lt_of_reach_ne {G : DAG V} {A : Finset V} {s v : V} (h : ReachAvoid G A s v)
    (hne : s ≠ v) : G.rank s < G.rank v := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨p, hp, hpv⟩
  · exact absurd e.symm hne
  · exact lt_of_le_of_lt (rank_le_of_reach hp) (G.rank_strict_mono _ _ hpv.1)

/-- Vitne under `do(D)`: `c` er sann, resten av `D` usann, alle bits 0. -/
noncomputable def uDS {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (c w1 : V)
    (D : Finset V) :
    Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V) :=
  fun v _ => if v.1 = c then true else if v.1 ∈ Z then decide (v.1 = w1)
    else if v.1 ∈ D then false else decide (ReachAvoid G (Z ∪ D) c v.1)

/-- Punktet for mengdeversjonen: `uDS` begrenset til `A`. -/
noncomputable def ptS {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (c w1 : V)
    (D A : Finset V) : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) A :=
  (uDS C c w1 D).restrict (Finset.subset_univ A)

lemma uDS_notZ {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {c w1 : V}
    {D : Finset V} : ∀ p, p ∉ Z → ∀ i,
      (uDS C c w1 D ⟨p, Finset.mem_univ p⟩ i = true ↔ ReachAvoid G (Z ∪ D) c p) := by
  intro p hp i
  by_cases hpc : p = c
  · subst hpc
    constructor
    · intro _
      exact Relation.ReflTransGen.refl
    · intro _
      simp [uDS]
  by_cases hpD : p ∈ D
  · constructor
    · intro h
      simp [uDS, hpc, hp, hpD] at h
    · intro h
      rcases reach_notin h with e | e
      · exact absurd e hpc
      · exact absurd (Finset.mem_union_right Z hpD) e
  · simp [uDS, hpc, hp, hpD]

lemma uDS_orpar {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {c w1 : V}
    {D : Finset V} (hcZ : c ∉ Z) (v : V)
    (pa : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool))
    (hpa : ∀ q, pa q = uDS C c w1 D ⟨q.1, Finset.mem_univ _⟩) (i : Fin (C.k + 1)) :
    orpar G Z v pa i = decide (RZ G (Z ∪ D) c v) := by
  unfold orpar
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨q, hq, hqu⟩
    rw [hpa q] at hqu
    exact ⟨q.1, q.2, (uDS_notZ C q.1 hq i).mp hqu⟩
  · rintro ⟨q, hq, hr⟩
    have hqZ : q ∉ Z := by
      rcases reach_notin hr with e | e
      · rw [e]
        exact hcZ
      · exact fun h => e (Finset.mem_union_left D h)
    refine ⟨⟨q, hq⟩, hqZ, ?_⟩
    rw [hpa]
    exact (uDS_notZ C q hqZ i).mpr hr

lemma uDS_kernel_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {c w1 : V}
    {D : Finset V} (hcZ : c ∉ Z) (hw1 : w1 ∈ Z) (hrz : RZ G (Z ∪ D) c w1) (hcD : c ∈ D)
    (v : V) (hvD : v ∉ D) (pa : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool))
    (hpa : ∀ q, pa q = uDS C c w1 D ⟨q.1, Finset.mem_univ _⟩) :
    (chainCopy C w1).kernel v pa (uDS C c w1 D ⟨v, Finset.mem_univ v⟩) ≠ 0 := by
  have hvc : v ≠ c := by
    rintro rfl
    exact hvD hcD
  have ho : ∀ i, orpar G Z v pa i = decide (RZ G (Z ∪ D) c v) := uDS_orpar C hcZ v pa hpa
  by_cases hvw : v = w1
  · subst hvw
    rw [cc_kernel_w1, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · funext i
      rw [ho]
      simp [uDS, hvc, hw1, hrz]
  rw [cc_kernel_ne C hvw]
  simp only [chainModel]
  by_cases hvZ : v ∈ Z
  · rw [if_pos hvZ]
    split_ifs with h
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext i
        rw [ho, ho]
        simp [uDS, hvc, hvZ, hvw]
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext i
        simp [uDS, hvc, hvZ, hvw]
  · rw [if_neg hvZ, map_unif_ne_zero]
    refine ⟨uDS C c w1 D ⟨v, Finset.mem_univ v⟩, ?_⟩
    funext i
    by_cases hsi : C.s i = v
    · simp [hsi]
    · simp only [hsi, ↓reduceIte]
      rw [ho]
      have hvZD : v ∉ Z ∪ D := by
        rw [Finset.mem_union]
        rintro (h | h)
        · exact hvZ h
        · exact hvD h
      simp [uDS, hvc, hvZ, hvD, RZ, reach_iff_parent hvZD hvc]

lemma uDS_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {c w1 : V}
    {D : Finset V} (hcZ : c ∉ Z) (hw1 : w1 ∈ Z) (hrz : RZ G (Z ∪ D) c w1) (hcD : c ∈ D)
    (t0 : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) D)
    (ht0 : ∀ v (hv : v ∈ D), t0 ⟨v, hv⟩ = uDS C c w1 D ⟨v, Finset.mem_univ v⟩) :
    ∀ v, kfac (doModel (chainCopy C w1) D t0) Finset.univ (uDS C c w1 D) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  by_cases hvD : v ∈ D
  · simp only [doModel, dif_pos hvD]
    rw [PMF.pure_apply, if_pos (ht0 v hvD).symm]
    exact one_ne_zero
  · simp only [doModel, dif_neg hvD]
    exact uDS_kernel_pos C hcZ hw1 hrz hcD v hvD _ (by intro q; rfl)

/-- **Kjede-kopi-modellen for mengder.** Som `rule3_complete_chaincopy`, men `do(Z)`
setter `z` til 1 og resten av `Z` til 0; da teller bare veier utenom `X ∪ W ∪ Z`. -/
theorem rule3_complete_chaincopy_set (G : DAG V) (X W Y Z : Finset V) (y z w1 : V)
    (C : Chain (cutIn G X) (X ∪ W) y z) (hinj : Function.Injective C.z)
    (hyY : y ∈ Y) (hzZ : z ∈ Z) (hYZ : Disjoint Y Z)
    (hw1 : w1 ∈ W) (hw1C : ∀ j, C.z j ≠ w1) (hzw : RZ (cutIn G X) (X ∪ W ∪ Z) z w1)
    (hzy : ¬ ReachAvoid (cutIn G X) (X ∪ W ∪ Z) z y) :
    ∃ M : G.CausalModel (fun _ : V => Fin (C.k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hy : y ∉ X ∪ W := reach_not_mem (C.hs 0) C.hx
  have hz : z ∉ X ∪ W := reach_not_mem (C.hs _) C.hy
  have hw1S : w1 ∈ X ∪ W := Finset.mem_union_right X hw1
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hyY (by rw [e]; exact hzZ)
  have hyZ : y ∉ Z := fun h => Finset.disjoint_left.mp hYZ hyY h
  have hsub : ∀ v, (cutIn G X).parents v ⊆ G.parents v := by
    intro v u hu
    exact (mem_parents_cutIn.mp hu).1
  have hXN : ∀ v (hv : v ∈ X) p, (chainCopy C w1).kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X) ⟨v, hv⟩) := by
    intro v hv p
    have hvw : v ≠ w1 := by
      rintro rfl
      obtain ⟨q, hq, _⟩ := hzw
      exact (mem_parents_cutIn.mp hq).2 hv
    rw [cc_kernel_ne C hvw]
    exact chain_noparent_false C v (Finset.mem_union_left W hv)
      (fun u he => (show G.edge u v ∧ v ∉ X from he).2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hrw : RZ (cutIn G X) (X ∪ W) (C.s (Fin.last C.k)) w1 :=
    RZ_of_reach C.hy (RZ_avoid_mono (by intro v hv; exact Finset.mem_union_left _ hv) hzw)
  -- (F1) observasjonelt er punktet med y = 0 umulig
  have F1 : (chainCopy C w1).marginal (Y ∪ (X ∪ W))
      ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict
        (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) = 0 := by
    refine Audit.marginal_eq_zero_of _ _ _ (fun u hu => ?_)
    by_contra hall
    have hall' : ∀ v, kfac (chainCopy C w1) Finset.univ u v ≠ 0 :=
      fun v hv => hall ⟨v, hv⟩
    have hpos : ∀ v, v ∉ X ∪ W → kfac (chainModel C) Finset.univ u v ≠ 0 := by
      intro v hv
      rw [← cc_kfac_ne C (show v ≠ w1 by rintro rfl; exact hv hw1S) u]
      exact hall' v
    have hval : ∀ v (hv : v ∈ Y ∪ (X ∪ W)) i, u ⟨v, Finset.mem_univ v⟩ i =
        uDS C z w1 Z ⟨v, Finset.mem_univ v⟩ i :=
      fun v hv i => congrFun (congrFun hu ⟨v, hv⟩) i
    have huy : u ⟨y, Finset.mem_univ y⟩ = fun _ => false := by
      funext i
      rw [hval y (Finset.mem_union_left _ hyY) i]
      simp only [uDS, if_neg hyz, if_neg hy, if_neg hyZ]
      simpa using hzy
    have huz : ∀ j, u ⟨C.z j, Finset.mem_univ _⟩ = fun _ => false := by
      intro j
      funext i
      have hzj : C.z j ≠ z := fun e => hz (e ▸ C.hz j)
      rw [hval (C.z j) (Finset.mem_union_right _ (C.hz j)) i]
      simp only [uDS, if_neg hzj, if_pos (C.hz j)]
      simpa using hw1C j
    have huw : u ⟨w1, Finset.mem_univ w1⟩ = fun _ => true := by
      funext i
      have hwz : w1 ≠ z := fun e => hz (e ▸ hw1S)
      rw [hval w1 (Finset.mem_union_right _ hw1S) i]
      simp only [uDS, if_neg hwz, if_pos hw1S]
      simp
    have hk := hall' w1
    rw [DoAudit.kfac_univ, cc_kernel_w1, PMF.pure_apply] at hk
    have hw1v : u ⟨w1, Finset.mem_univ w1⟩ = fun _ =>
        orpar (cutIn G X) (X ∪ W) w1 (u.restrict (Finset.subset_univ _)) (Fin.last C.k) := by
      by_contra hne
      exact hk (if_neg hne)
    have hbk : u ⟨C.s (Fin.last C.k), Finset.mem_univ _⟩ (Fin.last C.k) = true := by
      have e := congrFun hw1v 0
      rw [huw, orpar_eq' C u hpos hrw] at e
      exact e.symm
    have hb0 : u ⟨C.s 0, Finset.mem_univ _⟩ 0 = false := by
      have := congrFun huy 0
      rw [chain_support' C u hpos y hy 0] at this
      simpa [C.hx] using this
    have key : ∀ a b : Bool, false = xor a b → a = b := by
      intro a b
      cases a <;> cases b <;> simp
    have hstep : ∀ j : Fin C.k, u ⟨C.s j.castSucc, Finset.mem_univ _⟩ j.castSucc =
        u ⟨C.s j.succ, Finset.mem_univ _⟩ j.succ := by
      intro j
      have hzk : kfac (chainModel C) Finset.univ u (C.z j) ≠ 0 := by
        rw [← cc_kfac_ne C (hw1C j) u]
        exact hall' _
      have e := chain_z' C hinj u hpos j hzk
      rw [huz j] at e
      exact key _ _ (congrFun e 0)
    have hall2 : ∀ i : Fin (C.k + 1), u ⟨C.s i, Finset.mem_univ _⟩ i =
        u ⟨C.s 0, Finset.mem_univ _⟩ 0 := fun i =>
      Fin.induction (motive := fun i => u ⟨C.s i, Finset.mem_univ _⟩ i =
          u ⟨C.s 0, Finset.mem_univ _⟩ 0)
        rfl (fun j ih => (hstep j).symm.trans ih) i
    have := hall2 (Fin.last C.k)
    rw [hbk, hb0] at this
    exact Bool.noConfusion this
  -- (F2) observasjonelt er w-punktet mulig
  have F2 : (chainCopy C w1).marginal (X ∪ W)
      ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict
        (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ (u1W C w1) ?_ (u1W_pos C hw1S hrw)
    funext ⟨v, hv⟩
    have hvz : v ≠ z := fun e => hz (e ▸ hv)
    funext i
    by_cases hvw : v = w1
    · subst hvw
      simp only [Assignment.restrict, ptS, uDS, if_neg hvz, if_pos hv]
      simp [u1W]
    · simp only [Assignment.restrict, ptS, uDS, u1W, if_neg hvz, if_pos hv, if_neg hvw]
      rw [u1C_Z C ⟨v, Finset.mem_univ v⟩ hv]
      simp [hvw]
  -- (F3) under do(Z) er punktet mulig
  have F3 : (doModel (chainCopy C w1) Z
      ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict hzs)).marginal (Y ∪ (X ∪ W))
      ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict
        (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 :=
    Audit.marginal_ne_zero_of _ _ _ (uDS C z w1 Z) rfl
      (uDS_pos C hz hw1S hzw hzZ _ (fun v hv => rfl))
  refine ⟨liftSub hsub (chainCopy C w1), fun _ _ => false,
    ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W)), ?_⟩
  have hA : ∀ S', (doModel (liftSub hsub (chainCopy C w1)) X (fun _ _ => false)).marginal S' =
      (chainCopy C w1).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_kfac hsub _ _ hXN) S'
  have hB : ∀ S', (doModel (doModel (liftSub hsub (chainCopy C w1)) X (fun _ _ => false))
      Z ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict hzs)).marginal S' =
      (doModel (chainCopy C w1) Z
        ((ptS C z w1 Z (Y ∪ Z ∪ (X ∪ W))).restrict hzs)).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_do_kfac hsub _ _ _ hXN) S'
  rw [hB, hB, hA, hA, F1, zero_mul]
  exact mul_ne_zero F3 F2

/-- En vei i en delgraf, fra en kilde som ikke når andre `Zc`-noder, finnes i `H_{Z̄c}`. -/
lemma reach_cutset {G2 H : DAG V} {A Zc : Finset V} {s v : V}
    (hE : ∀ a b, G2.edge a b → H.edge a b)
    (hcl : ∀ c ∈ Zc, ReachAvoid G2 A s c → s = c) (h : ReachAvoid G2 A s v) :
    ReachAvoid (cutIn H Zc) A s v := by
  have h' : Relation.ReflTransGen (fun a b => G2.edge a b ∧ b ∉ A) s v := h
  clear h
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d hab hbd ih =>
    refine ih.tail ⟨(⟨hE b d hbd.1, ?_⟩ : H.edge b d ∧ d ∉ Zc), hbd.2⟩
    intro hd
    have hsd : s = d := hcl d hd (hab.tail hbd)
    have h1 : G2.rank s ≤ G2.rank b := rank_le_of_reach hab
    have h2 : G2.rank b < G2.rank d := G2.rank_strict_mono b d hbd.1
    rw [← hsd] at h2
    omega

lemma RZ_cutset {G2 H : DAG V} {A Zc : Finset V} {s v : V}
    (hE : ∀ a b, G2.edge a b → H.edge a b) (hv : v ∉ Zc)
    (hcl : ∀ c ∈ Zc, ReachAvoid G2 A s c → s = c) (h : RZ G2 A s v) :
    RZ (cutIn H Zc) A s v := by
  obtain ⟨p, hp, hr⟩ := h
  refine ⟨p, mem_parents_cutIn.mpr ⟨?_, hv⟩, reach_cutset hE hcl hr⟩
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hE _ _ hp

/-- En kjede der ingen kilde når en annen `Zc`-node, er en kjede i `H_{Z̄c}`. -/
def Chain.cutset {G2 H : DAG V} {A Zc : Finset V} {x y : V} (C : Chain G2 A x y)
    (hE : ∀ a b, G2.edge a b → H.edge a b) (hZA : ∀ v ∈ Zc, v ∉ A)
    (hcl : ∀ i, ∀ c ∈ Zc, ReachAvoid G2 A (C.s i) c → C.s i = c) :
    Chain (cutIn H Zc) A x y where
  k := C.k
  s := C.s
  z := C.z
  hs := C.hs
  hz := C.hz
  hx := reach_cutset hE (hcl 0) C.hx
  hy := reach_cutset hE (hcl _) C.hy
  hl := fun j => RZ_cutset hE (fun h => hZA _ h (C.hz j)) (hcl _) (C.hl j)
  hr := fun j => RZ_cutset hE (fun h => hZA _ h (C.hz j)) (hcl _) (C.hr j)

/-- Samme kjede med nytt endepunkt. -/
def Chain.withEnd {G : DAG V} {Z : Finset V} {x y y' : V} (C : Chain G Z x y)
    (h : ReachAvoid G Z (C.s (Fin.last C.k)) y') : Chain G Z x y' :=
  { C with hy := h }

/-- I `H_{B̄}` når bare `v` selv en node `v ∈ B`. -/
lemma reach_to_cut {H : DAG V} {A B : Finset V} {s v : V} (hv : v ∈ B)
    (h : ReachAvoid (cutIn H B) A s v) : s = v := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨p, _, hpv⟩
  · exact e.symm
  · exact absurd hv hpv.1.2

/-- En rettet vei inn i `W` går aldri gjennom `Z(W)`. -/
lemma reaches_cut_anc {H : DAG V} {Z W : Finset V} {a w : V} (h : H.Reaches a w)
    (hw : w ∈ W) : (cutIn H (Rule3.Z2 H Z W)).Reaches a w := by
  have h' : Relation.ReflTransGen H.edge a w := h
  clear h
  induction h' using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hbw ih =>
    refine Relation.ReflTransGen.head
      (⟨hab, ?_⟩ : H.edge a b ∧ b ∉ Rule3.Z2 H Z W) ih
    intro hb
    simp only [Rule3.Z2, Finset.mem_filter] at hb
    have hanc : b ∈ ancestors H W := by
      simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hw, hbw⟩
    exact hb.2 hanc

/-- Fra `G2` til `H` med `Zc` lagt til det som skal unngås. -/
lemma reach_H_of_clean {G2 H : DAG V} {A Zc : Finset V} {s v : V}
    (hE : ∀ a b, G2.edge a b → H.edge a b)
    (hcl : ∀ c ∈ Zc, c ≠ s → ¬ ReachAvoid G2 A s c) (h : ReachAvoid G2 A s v) :
    ReachAvoid H (A ∪ Zc) s v := by
  have h' : Relation.ReflTransGen (fun a b => G2.edge a b ∧ b ∉ A) s v := h
  clear h
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d hab hbd ih =>
    refine ih.tail ⟨hE b d hbd.1, ?_⟩
    rw [Finset.mem_union]
    rintro (hd | hd)
    · exact hbd.2 hd
    · by_cases hds : d = s
      · have h1 : G2.rank s ≤ G2.rank b := rank_le_of_reach hab
        have h2 : G2.rank b < G2.rank d := G2.rank_strict_mono b d hbd.1
        rw [hds] at h2
        omega
      · exact hcl d hd hds (hab.tail hbd)

lemma RZ_H_of_clean {G2 H : DAG V} {A Zc : Finset V} {s v : V}
    (hE : ∀ a b, G2.edge a b → H.edge a b)
    (hcl : ∀ c ∈ Zc, c ≠ s → ¬ ReachAvoid G2 A s c) (h : RZ G2 A s v) :
    RZ H (A ∪ Zc) s v := by
  obtain ⟨p, hp, hr⟩ := h
  refine ⟨p, ?_, reach_H_of_clean hE hcl hr⟩
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hE _ _ hp

/-- Fra `H` med `Zc` unngått til `H_{B̄}` når `B ⊆ Zc`. -/
lemma reach_cut_of_avoid {H : DAG V} {A Zc B : Finset V} {s v : V} (hB : B ⊆ Zc)
    (h : ReachAvoid H (A ∪ Zc) s v) : ReachAvoid (cutIn H B) A s v := by
  have h' : Relation.ReflTransGen (fun a b => H.edge a b ∧ b ∉ A ∪ Zc) s v := h
  clear h
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d hab hbd ih =>
    refine ih.tail ⟨(⟨hbd.1, fun hd => hbd.2 (Finset.mem_union_right A (hB hd))⟩ :
      H.edge b d ∧ d ∉ B), fun hd => hbd.2 (Finset.mem_union_left Zc hd)⟩

/-- **Kombinatorikken i mengdeversjonen.** Fra en kjede i `H_{Z(W)̄}` og ingen kjede i
`H_{Z̄}` får vi `y`, `z`, `w1` og en kjede som kjede-kopi-modellen kan bruke. -/
theorem set_gap_core {H : DAG V} {A W Y Z : Finset V} (hW : W ⊆ A)
    (hpar : ∀ v ∈ A, ∀ u, H.edge u v → v ∈ W) (hZA : ∀ v ∈ Z, v ∉ A)
    (y0 z0 : V) (hy0 : y0 ∈ Y) (hz0 : z0 ∈ Z) (C0 : Chain (cutIn H (Rule3.Z2 H Z W)) A y0 z0)
    (hsep : ∀ y ∈ Y, ∀ z ∈ Z, Chain (cutIn H Z) A y z → False) :
    ∃ y ∈ Y, ∃ z ∈ Z, ∃ w1 ∈ W, ∃ C : Chain H A y z, Function.Injective C.z ∧
      (∀ j, C.z j ≠ w1) ∧ RZ H (A ∪ Z) z w1 ∧ ¬ ReachAvoid H (A ∪ Z) z y := by
  have hE : ∀ a b, (cutIn H (Rule3.Z2 H Z W)).edge a b → H.edge a b := fun a b h => h.1
  obtain ⟨C1, hinj1⟩ := chain_injective C0.k C0 rfl
  have hP : ∃ n, ∃ y ∈ Y, ∃ z ∈ Z, ∃ C : Chain (cutIn H (Rule3.Z2 H Z W)) A y z,
      C.k = n ∧ Function.Injective C.z := ⟨C1.k, y0, hy0, z0, hz0, C1, rfl, hinj1⟩
  obtain ⟨y, hyY, z, hzZ, C, hCk, hinj⟩ := Nat.find_spec hP
  -- ingen kilde før den siste når en Z-node
  have hA : ∀ i : Fin (C.k + 1), i.val < C.k → ∀ c ∈ Z,
      ¬ ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C.s i) c := by
    intro i hi c hc hr
    exact Nat.find_min hP (show i.val < Nat.find hP by omega)
      ⟨y, hyY, c, hc, C.take i hr, rfl, C.take_inj i hr hinj⟩
  have hcl_i : ∀ i : Fin (C.k + 1), i.val < C.k → ∀ c ∈ Z,
      ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C.s i) c → C.s i = c :=
    fun i hi c hc hr => absurd hr (hA i hi c hc)
  -- z*: Z-noden med høyest rang som den siste kilden når
  obtain ⟨zs, hzsR, hzsmax⟩ := Finset.exists_max_image
    (Z.filter (fun c => ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C.s (Fin.last C.k)) c))
    (fun c => (cutIn H (Rule3.Z2 H Z W)).rank c) ⟨z, Finset.mem_filter.mpr ⟨hzZ, C.hy⟩⟩
  have hzsZ : zs ∈ Z := (Finset.mem_filter.mp hzsR).1
  have hkzs : ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C.s (Fin.last C.k)) zs :=
    (Finset.mem_filter.mp hzsR).2
  have hmax : ∀ c ∈ Z, c ≠ zs → ¬ ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A zs c := by
    intro c hc hne hr
    have h1 : (cutIn H (Rule3.Z2 H Z W)).rank c ≤ (cutIn H (Rule3.Z2 H Z W)).rank zs :=
      hzsmax c (Finset.mem_filter.mpr ⟨hc, hkzs.trans hr⟩)
    have h2 := rank_lt_of_reach_ne hr (Ne.symm hne)
    omega
  have hcl_zs : ∀ c ∈ Z, ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A zs c → zs = c := by
    intro c hc hr
    by_contra hne
    exact hmax c hc (Ne.symm hne) hr
  have hcut : ∀ C' : Chain (cutIn H (Rule3.Z2 H Z W)) A y zs,
      (∀ i, ∀ c ∈ Z, ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C'.s i) c → C'.s i = c) →
      False :=
    fun C' hcl => hsep y hyY zs hzsZ (C'.cutset hE hZA hcl)
  -- z* når ikke y
  have hzy : ¬ ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A zs y := by
    intro hr
    exact hcut (Chain.trek zs (hZA zs hzsZ) hr Relation.ReflTransGen.refl)
      (fun _ => hcl_zs)
  -- z* er forfar til W
  have hzs2 : zs ∉ Rule3.Z2 H Z W := by
    intro h2
    have hsk : C.s (Fin.last C.k) = zs := reach_to_cut h2 hkzs
    refine hcut (C.withEnd hkzs) (fun i c hc hr => ?_)
    show C.s i = c
    have hr' : ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A (C.s i) c := hr
    by_cases hi : i.val < C.k
    · exact hcl_i i hi c hc hr'
    · have hil : i = Fin.last C.k := Fin.ext (by rw [Fin.val_last]; have hi2 : i.val < C.k + 1 := i.2; omega)
      rw [hil, hsk] at hr' ⊢
      exact hcl_zs c hc hr'
  have hzsanc : zs ∈ ancestors H W := by
    by_contra hna
    apply hzs2
    simp only [Rule3.Z2, Finset.mem_filter]
    exact ⟨hzsZ, hna⟩
  obtain ⟨w, hwW, hzw0⟩ : ∃ w ∈ W, H.Reaches zs w := by
    simpa [ancestors] using hzsanc
  obtain ⟨w1, hw1A, hzw⟩ := exists_first_Z (reaches_cut_anc (Z := Z) hzw0 hwW)
    (hZA zs hzsZ) (hW hwW)
  have hw1W : w1 ∈ W := by
    obtain ⟨q, hq, _⟩ := hzw
    have hqH : q ∈ H.parents w1 := (mem_parents_cutIn.mp hq).1
    have hq' : H.edge q w1 := by simpa [DAG.parents] using hqH
    exact hpar w1 hw1A q hq'
  by_cases hc : ∃ j, C.z j = w1
  · -- w1 er en kollider: kutt kjeden der og la z* være siste kilde
    exfalso
    obtain ⟨j, hj⟩ := hc
    have hl : RZ (cutIn H (Rule3.Z2 H Z W)) A
        ((C.take j.castSucc Relation.ReflTransGen.refl).s (Fin.last _)) (C.z j) := C.hl j
    have hr : RZ (cutIn H (Rule3.Z2 H Z W)) A zs (C.z j) := by
      rw [hj]
      exact hzw
    have hj2 := j.2
    exact hcut ((C.take j.castSucc Relation.ReflTransGen.refl).snoc (C.z j) zs (C.hz j)
        (hZA zs hzsZ) hl hr Relation.ReflTransGen.refl)
      (Chain.snoc_src (C.take j.castSucc Relation.ReflTransGen.refl) (C.z j) zs (C.hz j)
        (hZA zs hzsZ) hl hr Relation.ReflTransGen.refl
        (fun v => ∀ c ∈ Z, ReachAvoid (cutIn H (Rule3.Z2 H Z W)) A v c → v = c)
        hcl_zs (fun i => by
          have h1 : i.val < j.val + 1 := i.2
          exact hcl_i ⟨i.val, by omega⟩ (show i.val < C.k by omega)))
  · refine ⟨y, hyY, zs, hzsZ, w1, hw1W, (C.withEnd hkzs).mono hE, hinj,
      fun j e => hc ⟨j, e⟩, RZ_H_of_clean hE hmax hzw, fun hr => hzy ?_⟩
    refine reach_cut_of_avoid ?_ hr
    intro v hv
    simp only [Rule3.Z2, Finset.mem_filter] at hv
    exact hv.1

/-- **Det siste tilfellet for mengder.** `Y` og `Z` er d-forbundet i `G_{X̄Z(W)̄}`,
men d-separert i `G_{X̄Z̄}`. -/
theorem rule3_complete_set_gap (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hcon : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z)
    (hsep : SetSound.DSeparatedSet (cutIn (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ : V => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  simp only [SetSound.DSeparatedSet, not_forall] at hcon
  obtain ⟨y0, hy0, z0, hz0, hn⟩ := hcon
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) y0 z0,
      ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C0⟩ := chain_of_open (Finset.disjoint_left.mp hY hy0)
    (Finset.disjoint_left.mp hZ hz0) p hp
  have hsep' : ∀ y ∈ Y, ∀ z ∈ Z, Chain (cutIn (cutIn G X) Z) (X ∪ W) y z → False := by
    intro y hy z hz C'
    have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
    exact no_chain_of_dsep hyz (dsep_of_dsepPath (hsep y hy z hz)) C'
  have hpar : ∀ v ∈ X ∪ W, ∀ u, (cutIn G X).edge u v → v ∈ W := by
    intro v hv u he
    rcases Finset.mem_union.mp hv with h | h
    · exact absurd h (show G.edge u v ∧ v ∉ X from he).2
    · exact h
  obtain ⟨y, hyY, zs, hzsZ, w1, hw1W, C, hinj, hw1C, hzw, hzy⟩ :=
    set_gap_core (H := cutIn G X) (A := X ∪ W) (W := W) (Y := Y) (Z := Z)
      (by intro v hv; exact Finset.mem_union_right X hv) hpar
      (fun v hv => Finset.disjoint_left.mp hZ hv) y0 z0 hy0 hz0 C0 hsep'
  obtain ⟨M, x, t, hne⟩ := rule3_complete_chaincopy_set G X W Y Z y zs w1 C hinj hyY hzsZ
    hYZ hw1W hw1C hzw hzy
  exact ⟨C.k, M, x, t, hne⟩

/-- **Fullstendighet for regel 3 med mengder.** -/
theorem rule3_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ : V => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  by_cases hroot : SetSound.DSeparatedSet (cutIn (cutIn G X) Z) (X ∪ W) Y Z
  · exact rule3_complete_set_gap G X W Y Z hY hZ hYZ h hroot
  · exact rule3_complete_set_root G X W Y Z hY hZ hYZ hroot

/-- **Regel 3 er eksakt for mengder.** For disjunkte `Y`, `Z` utenfor `X ∪ W`:
betingelsen i regel 3 holder hvis og bare hvis produktformen holder i hver modell. -/
theorem rule3_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ : V => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x t
    exact Rule3Flag.rule3_general M X Y Z W x hYZ hZ.symm hY h t
  · intro H
    by_contra hn
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_set G X W Y Z hY hZ hYZ hn
    exact hne (H k M x t)

end Rule3SetFull

end Completeness

#print axioms Completeness.support_iff
#print axioms Completeness.trek_not_condIndep
#print axioms Completeness.not_condIndep_of_colliderFree
#print axioms Completeness.dsep_complete_marginal
#print axioms Completeness.chain_support
#print axioms Completeness.chain_z
#print axioms Completeness.chain_not_condIndep
#print axioms Completeness.Chain.cons
#print axioms Completeness.exists_first_Z
#print axioms Completeness.chain_of_open
#print axioms Completeness.chain_injective
#print axioms Completeness.dsep_complete
#print axioms Completeness.dsep_iff
#print axioms Completeness.dsepPath_iff
#print axioms Completeness.collider_explaining_away
#print axioms Completeness.doModel_lift
#print axioms Completeness.rule1_complete
#print axioms Completeness.marginal_eq_of_kfac
#print axioms Completeness.rule2_complete
#print axioms Completeness.dsep_isolated
#print axioms Completeness.rule3_complete_nonanc
#print axioms Completeness.rule1_iff
#print axioms Completeness.rule2_iff
#print axioms Completeness.rule3_iff_nonanc

#print axioms Completeness.condIndep_single
#print axioms Completeness.dsepSet_iff
#print axioms Completeness.rule1_iff_set
#print axioms Completeness.rule2_complete_set
#print axioms Completeness.rule2_iff_set
#print axioms Completeness.rule3_complete_set_nonanc
#print axioms Completeness.rule3_iff_set_nonanc
#print axioms Completeness.rule3_complete_root
#print axioms Completeness.rule3_complete_set_root
#print axioms Completeness.copy_support
#print axioms Completeness.rule3_complete_copy
#print axioms Completeness.rule3_complete_chaincopy
#print axioms Completeness.rule3_complete
#print axioms Completeness.rule3_iff
#print axioms Completeness.rule3_complete_set
#print axioms Completeness.rule3_iff_set
