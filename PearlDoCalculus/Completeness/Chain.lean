import PearlDoCalculus.Completeness.Trek

/-!
# Completeness of d-separation: chains and the full theorem

Builds on the trek case (`Completeness/Trek.lean`). A chain is a walk without
repeated nodes; the chain model puts XOR nodes along it so that the two
endpoints are dependent exactly when the chain is open given `Z`. From a
d-connecting walk one extracts a minimal chain, which gives the completeness
direction.

Main results: `Completeness.dsep_complete` (if `x` and `y` are not d-separated
given `Z`, some model makes them dependent), `Completeness.dsep_iff`
(d-separation holds exactly when conditional independence holds in all models),
`Completeness.dsepPath_iff` (the same for the path-based definition), and the
explaining-away check `Completeness.collider_explaining_away`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Nivå 3a-3, runde 1: kjeder og kjedemodellen -/

/-- `s` når en forelder til `z` langs en rettet vei utenom `Z`. -/
def RZ (G : DAG V) (Z : Finset V) (s z : V) : Prop :=
  ∃ p ∈ G.parents z, ReachAvoid G Z s p

/-- En kjede fra `x` til `y` gitt `Z`: kilder `s₀, …, s_k ∉ Z` og noder
`z₁, …, z_k ∈ Z`, der `s₀` når `x`, `s_k` når `y`, og både `s_{j−1}` og `s_j` når
en forelder til `z_j`, alt utenom `Z`. -/
structure Chain (G : DAG V) (Z : Finset V) (x y : V) where
  k : ℕ
  s : Fin (k + 1) → V
  z : Fin k → V
  hs : ∀ i, s i ∉ Z
  hz : ∀ j, z j ∈ Z
  hx : ReachAvoid G Z (s 0) x
  hy : ReachAvoid G Z (s (Fin.last k)) y
  hl : ∀ j : Fin k, RZ G Z (s j.castSucc) (z j)
  hr : ∀ j : Fin k, RZ G Z (s j.succ) (z j)

/-- Komponent `i` av OR over foreldrene utenfor `Z`. -/
noncomputable def orpar (G : DAG V) (Z : Finset V) {k : ℕ} (v : V)
    (pa : {u // u ∈ G.parents v} → (Fin (k + 1) → Bool)) (i : Fin (k + 1)) : Bool :=
  decide (∃ p : {u // u ∈ G.parents v}, p.1 ∉ Z ∧ pa p i = true)

/-- **Kjedemodellen.** En node utenfor `Z` tar en uniform bit i komponent `i` hvis
den er `s_i`, ellers OR av komponent `i` hos foreldrene utenfor `Z`. `z_j` tar XOR av
komponent `j−1` og `j`; andre noder i `Z` er konstant `false`. -/
noncomputable def chainModel {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) :
    G.CausalModel (fun _ => Fin (C.k + 1) → Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v ∈ Z then
      if h : ∃ j, C.z j = v then
        PMF.pure (fun _ => xor (orpar G Z v pa (Classical.choose h).castSucc)
          (orpar G Z v pa (Classical.choose h).succ))
      else PMF.pure (fun _ => false)
    else PMF.map (fun u i => if C.s i = v then u i else orpar G Z v pa i)
      (PMF.uniformOfFintype (Fin (C.k + 1) → Bool))

/-- **Støtten til kjedemodellen, komponentvis.** Er alle kjernefaktorer ≠ 0, så er
komponent `i` av en node `v ∉ Z` lik biten til `s_i`, og bare hvis `s_i` når `v`
utenom `Z`. -/
lemma chain_support {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (chainModel C) Finset.univ u v ≠ 0) :
    ∀ v, v ∉ Z → ∀ i, u ⟨v, Finset.mem_univ v⟩ i =
      (u ⟨C.s i, Finset.mem_univ _⟩ i && decide (ReachAvoid G Z (C.s i) v)) := by
  suffices H : ∀ n, ∀ v, G.rank v = n → v ∉ Z → ∀ i, u ⟨v, Finset.mem_univ v⟩ i =
      (u ⟨C.s i, Finset.mem_univ _⟩ i && decide (ReachAvoid G Z (C.s i) v)) from
    fun v => H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hr hvZ i
  by_cases hsi : C.s i = v
  · subst hsi
    have hrefl : ReachAvoid G Z (C.s i) (C.s i) := Relation.ReflTransGen.refl
    simp [hrefl]
  have hk := hpos v
  rw [DoAudit.kfac_univ] at hk
  simp only [chainModel] at hk
  rw [if_neg hvZ, PMF.map_uniformOfFintype_apply_ne_zero_iff] at hk
  obtain ⟨w, hw⟩ := hk
  have hvi := congrFun hw i
  rw [if_neg hsi] at hvi
  rw [← hvi]
  unfold orpar
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff, Bool.and_eq_true]
  rw [reach_iff_parent hvZ (fun h => hsi h.symm)]
  constructor
  · rintro ⟨⟨p, hp⟩, hpZ, hpu⟩
    have hlt : G.rank p < n := by
      have := G.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    have hpu' : u ⟨p, Finset.mem_univ p⟩ i = true := hpu
    rw [ih _ hlt p rfl hpZ i] at hpu'
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hpu'
    exact ⟨hpu'.1, p, hp, hpu'.2⟩
  · rintro ⟨hb, p, hp, hrp⟩
    have hpZ : p ∉ Z := reach_not_mem (C.hs i) hrp
    have hlt : G.rank p < n := by
      have := G.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    refine ⟨⟨p, hp⟩, hpZ, ?_⟩
    show u ⟨p, Finset.mem_univ p⟩ i = true
    rw [ih _ hlt p rfl hpZ i]
    simp [hb, hrp]

/-! ## Nivå 3a-3, runde 2: XOR-nodene, vitnene og teoremet for en kjede -/

/-- Når `s_i` når en forelder til `v` utenom `Z`, er OR-komponent `i` i `v` lik
biten til `s_i`. -/
lemma orpar_eq_of_RZ {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (chainModel C) Finset.univ u v ≠ 0) {v : V} {i : Fin (C.k + 1)}
    (h : RZ G Z (C.s i) v) :
    orpar G Z v (u.restrict (Finset.subset_univ (G.parents v))) i =
      u ⟨C.s i, Finset.mem_univ _⟩ i := by
  unfold orpar
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨p, hp⟩, hpZ, hpu⟩
    have hpu' : u ⟨p, Finset.mem_univ p⟩ i = true := hpu
    rw [chain_support C u hpos p hpZ i] at hpu'
    simp only [Bool.and_eq_true] at hpu'
    exact hpu'.1
  · intro hb
    obtain ⟨p, hp, hrp⟩ := h
    have hpZ : p ∉ Z := reach_not_mem (C.hs i) hrp
    refine ⟨⟨p, hp⟩, hpZ, ?_⟩
    show u ⟨p, Finset.mem_univ p⟩ i = true
    rw [chain_support C u hpos p hpZ i]
    simp [hb, hrp]

/-- **XOR-nodene.** Med forskjellige `z` er `z_j = b_{j−1} ⊕ b_j`. -/
lemma chain_z {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (hinj : Function.Injective C.z)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (chainModel C) Finset.univ u v ≠ 0) (j : Fin C.k) :
    u ⟨C.z j, Finset.mem_univ _⟩ = fun _ =>
      xor (u ⟨C.s j.castSucc, Finset.mem_univ _⟩ j.castSucc)
        (u ⟨C.s j.succ, Finset.mem_univ _⟩ j.succ) := by
  have hk := hpos (C.z j)
  rw [DoAudit.kfac_univ] at hk
  simp only [chainModel] at hk
  have hex : ∃ j', C.z j' = C.z j := ⟨j, rfl⟩
  rw [if_pos (C.hz j), dif_pos hex, PMF.pure_apply] at hk
  have hch : Classical.choose hex = j := hinj (Classical.choose_spec hex)
  have huz : u ⟨C.z j, Finset.mem_univ _⟩ = fun _ =>
      xor (orpar G Z (C.z j) (u.restrict (Finset.subset_univ _)) (Classical.choose hex).castSucc)
        (orpar G Z (C.z j) (u.restrict (Finset.subset_univ _)) (Classical.choose hex).succ) := by
    by_contra h
    exact hk (if_neg h)
  rw [huz, hch, orpar_eq_of_RZ C u hpos (C.hl j), orpar_eq_of_RZ C u hpos (C.hr j)]

/-- Vitne A: alle bits 0. -/
def u0C {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) :
    Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V) :=
  fun _ _ => false

lemma u0_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) :
    ∀ v, kfac (chainModel C) Finset.univ (u0C C) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  simp only [chainModel]
  have hor : ∀ i, orpar G Z v ((u0C C).restrict (Finset.subset_univ _)) i = false := by
    intro i
    simp [orpar, u0C, Assignment.restrict]
  by_cases hvZ : v ∈ Z
  · rw [if_pos hvZ]
    split_ifs with h
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext _
        simp [hor, u0C]
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · rfl
  · rw [if_neg hvZ, PMF.map_uniformOfFintype_apply_ne_zero_iff]
    refine ⟨fun _ => false, ?_⟩
    funext i
    simp [hor, u0C]

/-- Vitne B: alle bits 1. -/
noncomputable def u1C {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) :
    Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 ∈ Z then (fun _ => false) else (fun i => decide (ReachAvoid G Z (C.s i) v.1))

lemma u1_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) :
    ∀ v, kfac (chainModel C) Finset.univ (u1C C) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  simp only [chainModel]
  have hor : ∀ i, orpar G Z v ((u1C C).restrict (Finset.subset_univ _)) i =
      decide (RZ G Z (C.s i) v) := by
    intro i
    unfold orpar
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    constructor
    · rintro ⟨⟨p, hp⟩, hpZ, hpu⟩
      have hpu' : u1C C ⟨p, Finset.mem_univ p⟩ i = true := hpu
      simp [u1C, hpZ] at hpu'
      exact ⟨p, hp, hpu'⟩
    · rintro ⟨p, hp, hrp⟩
      have hpZ : p ∉ Z := reach_not_mem (C.hs i) hrp
      refine ⟨⟨p, hp⟩, hpZ, ?_⟩
      show u1C C ⟨p, Finset.mem_univ p⟩ i = true
      simp [u1C, hpZ, hrp]
  by_cases hvZ : v ∈ Z
  · rw [if_pos hvZ]
    split_ifs with h
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext _
        have hj := Classical.choose_spec h
        have h1 : RZ G Z (C.s (Classical.choose h).castSucc) v := by
          have := C.hl (Classical.choose h)
          rwa [hj] at this
        have h2 : RZ G Z (C.s (Classical.choose h).succ) v := by
          have := C.hr (Classical.choose h)
          rwa [hj] at this
        rw [hor, hor]
        simp [u1C, hvZ, h1, h2]
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext _
        simp [u1C, hvZ]
  · rw [if_neg hvZ, PMF.map_uniformOfFintype_apply_ne_zero_iff]
    refine ⟨u1C C ⟨v, Finset.mem_univ v⟩, ?_⟩
    funext i
    by_cases hsi : C.s i = v
    · simp [hsi]
    · simp only [hsi, ↓reduceIte]
      rw [hor]
      simp [u1C, hvZ, RZ, reach_iff_parent hvZ (fun h => hsi h.symm)]

/-- Tilordningen `x = 0`, `y = [s_i når y]` komponentvis, og `Z = 0`. -/
noncomputable def wC {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (S : Finset V) : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) S :=
  fun v => if v.1 = y then (fun i => decide (ReachAvoid G Z (C.s i) y)) else (fun _ => false)

lemma wC_ne {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (S : Finset V)
    (v : {v // v ∈ S}) (hv : v.1 ≠ y) : wC C S v = fun _ => false := by
  simp [wC, hv]

lemma wC_eq {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (S : Finset V)
    (v : {v // v ∈ S}) (hv : v.1 = y) :
    wC C S v = fun i => decide (ReachAvoid G Z (C.s i) v.1) := by
  simp [wC, hv]

lemma u1C_notZ {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (v : {v // v ∈ (Finset.univ : Finset V)}) (hv : v.1 ∉ Z) :
    u1C C v = fun i => decide (ReachAvoid G Z (C.s i) v.1) := by
  simp [u1C, hv]

lemma u1C_Z {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (v : {v // v ∈ (Finset.univ : Finset V)}) (hv : v.1 ∈ Z) :
    u1C C v = fun _ => false := by
  simp [u1C, hv]

/-- **Teoremet for en kjede.** Har kjeden forskjellige `z`, og er `x ≠ y`, så
svikter `CondIndep {x} {y} Z` i kjedemodellen. -/
theorem chain_not_condIndep {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (hinj : Function.Injective C.z) (hxy : x ≠ y) :
    ¬ CondIndep (chainModel C) {x} {y} Z := by
  intro hci
  have hxZ : x ∉ Z := reach_not_mem (C.hs 0) C.hx
  have hyZ : y ∉ Z := reach_not_mem (C.hs _) C.hy
  have h := hci (wC C ({x} ∪ {y} ∪ Z))
  have hz : (chainModel C).marginal ({x} ∪ {y} ∪ Z) (wC C ({x} ∪ {y} ∪ Z)) = 0 := by
    refine Audit.marginal_eq_zero_of _ _ _ (fun u hu => ?_)
    by_contra hall
    have hall' : ∀ v, kfac (chainModel C) Finset.univ u v ≠ 0 :=
      fun v hv => hall ⟨v, hv⟩
    have hux : u ⟨x, Finset.mem_univ x⟩ = fun _ => false := by
      have := congrFun hu ⟨x, by simp⟩
      simpa [Assignment.restrict, wC, hxy] using this
    have huy : u ⟨y, Finset.mem_univ y⟩ = fun i => decide (ReachAvoid G Z (C.s i) y) := by
      have := congrFun hu ⟨y, by simp⟩
      simpa [Assignment.restrict, wC] using this
    have huz : ∀ j, u ⟨C.z j, Finset.mem_univ _⟩ = fun _ => false := by
      intro j
      have hzy : C.z j ≠ y := fun e => hyZ (e ▸ C.hz j)
      have := congrFun hu ⟨C.z j, by simp [C.hz j]⟩
      simpa [Assignment.restrict, wC, hzy] using this
    -- b₀ = false
    have hb0 : u ⟨C.s 0, Finset.mem_univ _⟩ 0 = false := by
      have := congrFun hux 0
      rw [chain_support C u hall' x hxZ 0] at this
      simpa [C.hx] using this
    -- b_k = true
    have hbk : u ⟨C.s (Fin.last C.k), Finset.mem_univ _⟩ (Fin.last C.k) = true := by
      have := congrFun huy (Fin.last C.k)
      rw [chain_support C u hall' y hyZ (Fin.last C.k)] at this
      simpa [C.hy] using this
    -- b_{j−1} = b_j
    have key : ∀ a b : Bool, false = xor a b → a = b := by
      intro a b
      cases a <;> cases b <;> simp
    have hstep : ∀ j : Fin C.k, u ⟨C.s j.castSucc, Finset.mem_univ _⟩ j.castSucc =
        u ⟨C.s j.succ, Finset.mem_univ _⟩ j.succ := by
      intro j
      have e := chain_z C hinj u hall' j
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
  rw [hz, zero_mul] at h
  refine (mul_ne_zero ?_ ?_) h.symm
  · refine Audit.marginal_ne_zero_of _ _ _ (u0C C) ?_ (u0_pos C)
    funext ⟨v, hv⟩
    have hvy : v ≠ y := by
      rcases Finset.mem_union.mp hv with h | h
      · rw [Finset.mem_singleton.mp h]
        exact hxy
      · exact fun e => hyZ (e ▸ h)
    have hv3 : v ∈ ({x} ∪ {y} ∪ Z : Finset V) := by
      simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
      tauto
    exact (wC_ne C _ ⟨v, hv3⟩ hvy).symm
  · refine Audit.marginal_ne_zero_of _ _ _ (u1C C) ?_ (u1_pos C)
    funext ⟨v, hv⟩
    have hv3 : v ∈ ({x} ∪ {y} ∪ Z : Finset V) := by
      simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
      tauto
    rcases Finset.mem_union.mp hv with h | h
    · have hv' : v = y := Finset.mem_singleton.mp h
      exact (u1C_notZ C ⟨v, Finset.mem_univ v⟩ (fun e => hyZ (hv' ▸ e))).trans
        (wC_eq C _ ⟨v, hv3⟩ hv').symm
    · have hvy : v ≠ y := fun e => hyZ (e ▸ h)
      exact (u1C_Z C ⟨v, Finset.mem_univ v⟩ h).trans (wC_ne C _ ⟨v, hv3⟩ hvy).symm

/-! ## Nivå 3a-3, runde 3a: byggeklosser for kjeder -/

/-- En trek er en kjede uten kollidere. -/
def Chain.trek {G : DAG V} {Z : Finset V} {x y : V} (s : V) (hs : s ∉ Z)
    (hx : ReachAvoid G Z s x) (hy : ReachAvoid G Z s y) : Chain G Z x y where
  k := 0
  s := fun _ => s
  z := Fin.elim0
  hs := fun _ => hs
  hz := fun j => j.elim0
  hx := hx
  hy := hy
  hl := fun j => j.elim0
  hr := fun j => j.elim0

/-- Samme kjede med nytt startpunkt. -/
def Chain.withStart {G : DAG V} {Z : Finset V} {x x' y : V} (C : Chain G Z x y)
    (h : ReachAvoid G Z (C.s 0) x') : Chain G Z x' y :=
  { C with hx := h }

/-- Skjøt en ny kilde `s` og en ny Z-node `zc` foran en kjede. -/
def Chain.cons {G : DAG V} {Z : Finset V} {x y : V} (s zc : V) (hs : s ∉ Z) (hz : zc ∈ Z)
    (hl : RZ G Z s zc) (C : Chain G Z x y) (hr : RZ G Z (C.s 0) zc) : Chain G Z s y where
  k := C.k + 1
  s := Fin.cons s C.s
  z := Fin.cons zc C.z
  hs := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hs
    · simpa using C.hs j
  hz := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hz
    · simpa using C.hz j
  hx := by
    simp only [Fin.cons_zero]
    exact Relation.ReflTransGen.refl
  hy := by
    rw [← Fin.succ_last, Fin.cons_succ]
    exact C.hy
  hl := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hl
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact C.hl j
  hr := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_succ, Fin.cons_zero]
      exact hr
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact C.hr j

/-- `RZ` forlenges bakover langs `ReachAvoid`. -/
lemma RZ_of_reach {G : DAG V} {Z : Finset V} {s c z : V}
    (h1 : ReachAvoid G Z s c) (h2 : RZ G Z c z) : RZ G Z s z := by
  obtain ⟨p, hp, hr⟩ := h2
  exact ⟨p, hp, h1.trans hr⟩

/-- Fra en rettet vei `c → … → b` med `c ∉ Z` og `b ∈ Z` finnes en første Z-node. -/
lemma exists_first_Z {G : DAG V} {Z : Finset V} {c b : V} (h : G.Reaches c b) :
    c ∉ Z → b ∈ Z → ∃ z ∈ Z, RZ G Z c z := by
  have h' : Relation.ReflTransGen G.edge c b := h
  clear h
  induction h' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hc hb
    exact absurd hb hc
  | @head a d had _ ih =>
    intro _ hb
    by_cases hd : d ∈ Z
    · exact ⟨d, hd, a, by simp [DAG.parents, had], Relation.ReflTransGen.refl⟩
    · obtain ⟨z, hz, p, hp, hr⟩ := ih hd hb
      exact ⟨z, hz, p, hp, Relation.ReflTransGen.head ⟨had, hd⟩ hr⟩

/-! ## Nivå 3a-3, runde 3b: kjede fra en åpen vandring -/

/-- To tilstander i én induksjon. **Oppover:** åpen i en tilstand som ikke er
`.fwd` gir en kjede fra `a`. **Nedover:** en kilde `s ∉ Z` som når en forelder til
`a`, og åpen i tilstanden `.fwd`, gir en kjede fra `s`. -/
lemma chain_aux {G : DAG V} {Z : Finset V} :
    ∀ {a b : V} (q : Walk G a b), b ∉ Z →
      (∀ inc : Incoming, inc ≠ .fwd → (inc = .start → a ∉ Z) →
        ¬ Walk.blockedAux Z inc q → Nonempty (Chain G Z a b)) ∧
      (∀ s, s ∉ Z → (∃ p, ReachAvoid G Z s p ∧ G.edge p a) →
        ¬ Walk.blockedAux Z .fwd q → Nonempty (Chain G Z s b)) := by
  intro a b q
  induction q with
  | nil v =>
    intro hb
    refine ⟨fun _ _ _ _ => ⟨Chain.trek v hb Relation.ReflTransGen.refl
      Relation.ReflTransGen.refl⟩, ?_⟩
    rintro s hs ⟨p, hp, e⟩ _
    exact ⟨Chain.trek s hs Relation.ReflTransGen.refl (hp.tail ⟨e, hb⟩)⟩
  | @fwd a a' _ e q ih =>
    intro hb
    obtain ⟨_, F'⟩ := ih hb
    constructor
    · intro inc hinc hst hZ
      have ha : a ∉ Z := by
        cases inc with
        | start => exact hst rfl
        | fwd => exact absurd rfl hinc
        | bwd => exact fun h => hZ (Or.inl h)
      have hZ' : ¬ Walk.blockedAux Z .fwd q := by
        cases inc with
        | start => exact hZ
        | fwd => exact absurd rfl hinc
        | bwd => exact fun h => hZ (Or.inr h)
      exact F' a ha ⟨a, Relation.ReflTransGen.refl, e⟩ hZ'
    · rintro s hs ⟨p, hp, e0⟩ hZ
      have ha : a ∉ Z := fun h => hZ (Or.inl h)
      exact F' s hs ⟨a, hp.tail ⟨e0, ha⟩, e⟩ (fun h => hZ (Or.inr h))
  | @bwd a a' _ e q ih =>
    intro hb
    obtain ⟨B', _⟩ := ih hb
    constructor
    · intro inc hinc hst hZ
      have ha : a ∉ Z := by
        cases inc with
        | start => exact hst rfl
        | fwd => exact absurd rfl hinc
        | bwd => exact fun h => hZ (Or.inl h)
      have hZ' : ¬ Walk.blockedAux Z .bwd q := by
        cases inc with
        | start => exact hZ
        | fwd => exact absurd rfl hinc
        | bwd => exact fun h => hZ (Or.inr h)
      obtain ⟨C⟩ := B' .bwd (by intro h; cases h) (by intro h; cases h) hZ'
      exact ⟨C.withStart (C.hx.tail ⟨e, ha⟩)⟩
    · rintro s hs ⟨p, hp, e0⟩ hZ
      -- a er en kollider: den har en etterkommer i Z.
      have hdesc : ∃ z ∈ Z, G.Reaches a z := by
        by_contra hc
        exact hZ (Or.inl (fun z hz hr => hc ⟨z, hz, hr⟩))
      have hZ' : ¬ Walk.blockedAux Z .bwd q := fun h => hZ (Or.inr h)
      obtain ⟨C⟩ := B' .bwd (by intro h; cases h) (by intro h; cases h) hZ'
      by_cases haZ : a ∈ Z
      · exact ⟨Chain.cons s a hs haZ ⟨p, by simp [DAG.parents, e0], hp⟩ C
          ⟨a', by simp [DAG.parents, e], C.hx⟩⟩
      · obtain ⟨z0, hz0, hr0⟩ := hdesc
        obtain ⟨zc, hzc, hrz⟩ := exists_first_Z hr0 haZ hz0
        have hsa : ReachAvoid G Z s a := hp.tail ⟨e0, haZ⟩
        have hca : ReachAvoid G Z (C.s 0) a := C.hx.tail ⟨e, haZ⟩
        exact ⟨Chain.cons s zc hs hzc (RZ_of_reach hsa hrz) C (RZ_of_reach hca hrz)⟩

/-- **Kjede fra en åpen vandring.** Er `x, y ∉ Z` og `p` åpen gitt `Z`, finnes en
kjede fra `x` til `y`. -/
theorem chain_of_open {G : DAG V} {Z : Finset V} {x y : V} (hxZ : x ∉ Z) (hyZ : y ∉ Z)
    (p : Walk G x y) (hp : ¬ Walk.Blocked Z p) : Nonempty (Chain G Z x y) :=
  (chain_aux p hyZ).1 .start (by intro h; cases h) (fun _ => hxZ) hp

/-! ## Nivå 3a-3, runde 4: minimal kjede og full fullstendighet -/

/-- Halen av en kjede fra indeks `m`. -/
def Chain.drop {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (m : Fin (C.k + 1)) : Chain G Z (C.s m) y where
  k := C.k - m.val
  s := fun i => C.s ⟨m.val + i.val, by have := i.2; have := m.2; omega⟩
  z := fun j => C.z ⟨m.val + j.val, by have := j.2; have := m.2; omega⟩
  hs := fun _ => C.hs _
  hz := fun _ => C.hz _
  hx := by
    have e : (⟨m.val + ((0 : Fin (C.k - m.val + 1)) : ℕ),
        by have := m.2; simp; omega⟩ : Fin (C.k + 1)) = m := Fin.ext (by simp)
    show ReachAvoid G Z (C.s ⟨m.val + ((0 : Fin (C.k - m.val + 1)) : ℕ), _⟩) (C.s m)
    rw [e]
    exact Relation.ReflTransGen.refl
  hy := by
    have e : (⟨m.val + ((Fin.last (C.k - m.val)) : ℕ),
        by have := m.2; simp; omega⟩ : Fin (C.k + 1)) = Fin.last C.k :=
      Fin.ext (by have := m.2; simp; omega)
    show ReachAvoid G Z (C.s ⟨m.val + ((Fin.last (C.k - m.val)) : ℕ), _⟩) y
    rw [e]
    exact C.hy
  hl := fun j => C.hl ⟨m.val + j.val, by have := j.2; have := m.2; omega⟩
  hr := fun j => C.hr ⟨m.val + j.val, by have := j.2; have := m.2; omega⟩

lemma Chain.drop_s0 {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (m : Fin (C.k + 1)) : (C.drop m).s 0 = C.s m := by
  show C.s ⟨m.val + ((0 : Fin (C.k - m.val + 1)) : ℕ), _⟩ = C.s m
  congr 1 <;> exact Fin.ext (by simp)

/-- **Minimal kjede.** Enhver kjede kan erstattes av en med forskjellige `z`. -/
theorem chain_injective {G : DAG V} {Z : Finset V} {y : V} :
    ∀ n, ∀ {x : V} (C : Chain G Z x y), C.k = n →
      ∃ C' : Chain G Z x y, Function.Injective C'.z := by
  intro n
  induction n with
  | zero =>
    intro x C hk
    exact ⟨C, fun i => absurd i.2 (by omega)⟩
  | succ n ih =>
    intro x C hk
    have h1 : 1 < C.k + 1 := by omega
    have h0 : 0 < C.k := by omega
    obtain ⟨T', hT'⟩ := ih (C.drop ⟨1, h1⟩) (by show C.k - 1 = n; omega)
    have hl0 : RZ G Z (C.s 0) (C.z ⟨0, h0⟩) := by
      have := C.hl ⟨0, h0⟩
      simpa using this
    have hr0 : RZ G Z (C.s ⟨1, h1⟩) (C.z ⟨0, h0⟩) := C.hr ⟨0, h0⟩
    have hr0' : RZ G Z (T'.s 0) (C.z ⟨0, h0⟩) := RZ_of_reach T'.hx hr0
    by_cases hA : C.z ⟨0, h0⟩ ∈ Set.range T'.z
    · obtain ⟨j, hj⟩ := hA
      have hDinj : Function.Injective (T'.drop j.succ).z := by
        intro a b hab
        have h2 : j.succ.val + a.val = j.succ.val + b.val := congrArg Fin.val (hT' hab)
        exact Fin.ext (by omega)
      have hDnot : C.z ⟨0, h0⟩ ∉ Set.range (T'.drop j.succ).z := by
        rintro ⟨i, hi⟩
        have h2 : j.succ.val + i.val = j.val := congrArg Fin.val (hT' (hi.trans hj.symm))
        rw [Fin.val_succ] at h2
        omega
      have hrD : RZ G Z ((T'.drop j.succ).s 0) (C.z ⟨0, h0⟩) := by
        rw [Chain.drop_s0, ← hj]
        exact T'.hr j
      exact ⟨(Chain.cons (C.s 0) (C.z ⟨0, h0⟩) (C.hs 0) (C.hz _) hl0 (T'.drop j.succ)
        hrD).withStart C.hx, Fin.cons_injective_iff.mpr ⟨hDnot, hDinj⟩⟩
    · exact ⟨(Chain.cons (C.s 0) (C.z ⟨0, h0⟩) (C.hs 0) (C.hz _) hl0 T' hr0').withStart
        C.hx, Fin.cons_injective_iff.mpr ⟨hA, hT'⟩⟩

/-- **Fullstendighet for d-separasjon.** Er `x, y ∉ Z`, `x ≠ y`, og `x` og `y` ikke
d-separert gitt `Z`, så finnes en kausalmodell på `G` der `x` og `y` ikke er
betinget uavhengige gitt `Z`. Sammen med `dsep_sound` er d-separasjon dermed
nøyaktig det grafiske kriteriet for betinget uavhengighet. -/
theorem dsep_complete (G : DAG V) (Z : Finset V) (x y : V)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hxy : x ≠ y) (h : ¬ G.DSeparated Z x y) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ¬ CondIndep M {x} {y} Z := by
  obtain ⟨p, hp⟩ : ∃ p : Walk G x y, ¬ Walk.Blocked Z p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hxZ hyZ p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  exact ⟨C'.k, chainModel C', chain_not_condIndep C' hinj hxy⟩

/-! ## d-separasjon er nøyaktig riktig kriterium -/

/-- **d-separasjon ⇔ uavhengighet i alle modeller.** For `x, y ∉ Z`, `x ≠ y`:
`x` og `y` er d-separert gitt `Z` hvis og bare hvis `CondIndep {x} {y} Z` holder i
hver kausalmodell på `G` (her med bitvektorer som verdier, som er nok). -/
theorem dsep_iff (G : DAG V) (Z : Finset V) (x y : V)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hxy : x ≠ y) :
    G.DSeparated Z x y ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool)), CondIndep M {x} {y} Z := by
  constructor
  · intro h k M
    exact DSepSound.dsep_sound M Z x y h
  · intro h
    by_contra hn
    obtain ⟨k, M, hM⟩ := dsep_complete G Z x y hxZ hyZ hxy hn
    exact hM (h k M)

/-- Samme påstand med den klassiske, stibaserte d-separasjonen. -/
theorem dsepPath_iff (G : DAG V) (Z : Finset V) (x y : V)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hxy : x ≠ y) :
    G.DSeparatedPath Z x y ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool)), CondIndep M {x} {y} Z :=
  dsepPath_iff_dsep.trans (dsep_iff G Z x y hxZ hyZ hxy)

/-- **Kontroll: «explaining away».** I kollideren `0 → 2 ← 1` er `0` og `1`
uavhengige i alle modeller, men det finnes en modell der de er avhengige gitt `2`. -/
theorem collider_explaining_away :
    (∀ (k : ℕ) (M : Counterexample.ceG.CausalModel (fun _ => Fin (k + 1) → Bool)),
      CondIndep M {0} {1} ∅) ∧
    ∃ k : ℕ, ∃ M : Counterexample.ceG.CausalModel (fun _ => Fin (k + 1) → Bool),
      ¬ CondIndep M {0} {1} {2} :=
  ⟨fun _ M => DSepSound.dsep_sound M ∅ 0 1 Audit.collider_dsep_empty,
   dsep_complete _ {2} 0 1 (by simp) (by simp) (by simp) Audit.collider_not_dsep_cond⟩

end Completeness
