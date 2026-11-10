import PearlDoCalculus.AdjAudit

/-!
# Nivå 3a-1: fullstendighet for d-separasjon, kolliderfritt tilfelle

Finnes det en node `s ∉ Z` med rettede veier til `x` og `y` der hver node etter
`s` ligger utenfor `Z`, så finnes en modell der `CondIndep M {x} {y} Z` svikter.

Modellen: noder i `Z` er konstant `false`, `s` er en uniform bit, og enhver annen
node er OR av foreldrene. Da er en node `true` nøyaktig når den kan nås fra `s`
utenom `Z` og `s` er `true`, så `x = y = s` mens `Z` er konstant.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Rettet vei fra `s` til `v` der hver node etter `s` ligger utenfor `Z`. -/
def ReachAvoid (G : DAG V) (Z : Finset V) (s v : V) : Prop :=
  Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) s v

/-- `Z` konstant `false`, `s` uniform, alle andre OR av foreldrene. -/
noncomputable def trekModel (G : DAG V) (Z : Finset V) (s : V) :
    G.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v ∈ Z then PMF.pure false
    else if v = s then PMF.uniformOfFintype Bool
    else PMF.pure (decide (∃ p : {u // u ∈ G.parents v}, pa p = true))

lemma reach_not_mem {G : DAG V} {Z : Finset V} {s v : V} (hs : s ∉ Z)
    (h : ReachAvoid G Z s v) : v ∉ Z := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, _, hpv⟩
  · exact hs
  · exact hpv.2

lemma reach_iff_parent {G : DAG V} {Z : Finset V} {s v : V} (hvZ : v ∉ Z) (hvs : v ≠ s) :
    ReachAvoid G Z s v ↔ ∃ p ∈ G.parents v, ReachAvoid G Z s p := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, hp, hpv⟩
    · exact absurd rfl hvs
    · exact ⟨p, by simp [DAG.parents, hpv.1], hp⟩
  · rintro ⟨p, hp, hr⟩
    exact hr.tail ⟨by simpa [DAG.parents] using hp, hvZ⟩

/-- **Støtten til `trekModel`.** I en tilordning der alle kjernefaktorer er ≠ 0,
er `v` sann nøyaktig når `v` kan nås fra `s` utenom `Z` og `s` er sann. -/
lemma support_iff (G : DAG V) (Z : Finset V) (s : V) (hs : s ∉ Z)
    (u : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (trekModel G Z s) Finset.univ u v ≠ 0) :
    ∀ v, (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachAvoid G Z s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) := by
  suffices H : ∀ n, ∀ v, G.rank v = n → (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachAvoid G Z s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) from fun v => H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hr
  have hk := hpos v
  rw [DoAudit.kfac_univ] at hk
  simp only [trekModel] at hk
  by_cases hvZ : v ∈ Z
  · rw [if_pos hvZ, PMF.pure_apply] at hk
    have huv : u ⟨v, Finset.mem_univ v⟩ = false := by
      by_contra h
      exact hk (if_neg h)
    constructor
    · intro h
      rw [huv] at h
      exact absurd h Bool.false_ne_true
    · rintro ⟨h, _⟩
      exact absurd hvZ (reach_not_mem hs h)
  by_cases hvs : v = s
  · subst hvs
    exact ⟨fun h => ⟨Relation.ReflTransGen.refl, h⟩, fun h => h.2⟩
  rw [if_neg hvZ, if_neg hvs, PMF.pure_apply] at hk
  have huv : u ⟨v, Finset.mem_univ v⟩ =
      decide (∃ p : {u // u ∈ G.parents v},
        (u.restrict (Finset.subset_univ _)) p = true) := by
    by_contra h
    exact hk (if_neg h)
  rw [huv, decide_eq_true_iff, reach_iff_parent hvZ hvs]
  constructor
  · rintro ⟨⟨p, hp⟩, hpu⟩
    have hlt : G.rank p < n := by
      have := G.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    obtain ⟨hrp, hs'⟩ := (ih _ hlt p rfl).mp hpu
    exact ⟨⟨p, hp, hrp⟩, hs'⟩
  · rintro ⟨⟨p, hp, hrp⟩, hs'⟩
    have hlt : G.rank p < n := by
      have := G.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    exact ⟨⟨p, hp⟩, (ih _ hlt p rfl).mpr ⟨hrp, hs'⟩⟩

/-- Vitnet: `v` sann nøyaktig når `v` kan nås fra `s` og `b` er sann. -/
noncomputable def uB (G : DAG V) (Z : Finset V) (s : V) (b : Bool) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => decide (ReachAvoid G Z s v.1) && b

lemma uB_pos {G : DAG V} {Z : Finset V} {s : V} (hs : s ∉ Z) (b : Bool) :
    ∀ v, kfac (trekModel G Z s) Finset.univ (uB G Z s b) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  simp only [trekModel]
  by_cases hvZ : v ∈ Z
  · have hnr : ¬ ReachAvoid G Z s v := fun h => reach_not_mem hs h hvZ
    rw [if_pos hvZ, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · simp [uB, hnr]
  by_cases hvs : v = s
  · subst hvs
    rw [if_neg hvZ, if_pos rfl]
    simp [PMF.uniformOfFintype_apply]
  rw [if_neg hvZ, if_neg hvs, PMF.pure_apply, if_pos]
  · exact one_ne_zero
  · rw [Bool.eq_iff_iff]
    simp only [uB, Assignment.restrict, Bool.and_eq_true, decide_eq_true_iff]
    rw [reach_iff_parent hvZ hvs]
    constructor
    · rintro ⟨⟨p, hp, hr⟩, hb⟩
      exact ⟨⟨p, hp⟩, hr, hb⟩
    · rintro ⟨⟨p, hp⟩, hr, hb⟩
      exact ⟨⟨p, hp, hr⟩, hb⟩

/-- Tilordningen `x = false`, `y = true`, `Z = false`. -/
def wXY (y : V) (S : Finset V) : Assignment (α := fun _ : V => Bool) S :=
  fun v => decide (v.1 = y)

/-- **Nivå 3a-1.** Kan `x` og `y` nås fra `s ∉ Z` langs rettede veier utenom `Z`,
og er `x ≠ y`, så svikter `CondIndep {x} {y} Z` i `trekModel`. -/
theorem trek_not_condIndep (G : DAG V) (Z : Finset V) (s x y : V) (hs : s ∉ Z)
    (hx : ReachAvoid G Z s x) (hy : ReachAvoid G Z s y) (hxy : x ≠ y) :
    ¬ CondIndep (trekModel G Z s) {x} {y} Z := by
  intro hci
  have hyZ : y ∉ Z := reach_not_mem hs hy
  have h := hci (wXY y ({x} ∪ {y} ∪ Z))
  have hz : (trekModel G Z s).marginal ({x} ∪ {y} ∪ Z) (wXY y ({x} ∪ {y} ∪ Z)) = 0 := by
    refine Audit.marginal_eq_zero_of _ _ _ (fun u hu => ?_)
    by_contra hall
    have hall' : ∀ v, kfac (trekModel G Z s) Finset.univ u v ≠ 0 :=
      fun v hv => hall ⟨v, hv⟩
    have hux : u ⟨x, Finset.mem_univ x⟩ = false := by
      have := congrFun hu ⟨x, by simp⟩
      simpa [Assignment.restrict, wXY, hxy] using this
    have huy : u ⟨y, Finset.mem_univ y⟩ = true := by
      have := congrFun hu ⟨y, by simp⟩
      simpa [Assignment.restrict, wXY] using this
    have hxt := (support_iff G Z s hs u hall' x).mpr
      ⟨hx, ((support_iff G Z s hs u hall' y).mp huy).2⟩
    rw [hux] at hxt
    exact absurd hxt Bool.false_ne_true
  rw [hz, zero_mul] at h
  refine (mul_ne_zero ?_ ?_) h.symm
  · refine Audit.marginal_ne_zero_of _ _ _ (uB G Z s false) ?_ (uB_pos hs false)
    funext ⟨v, hv⟩
    have hvy : v ≠ y := by
      rcases Finset.mem_union.mp hv with h | h
      · rw [Finset.mem_singleton.mp h]
        exact hxy
      · exact fun e => hyZ (e ▸ h)
    simp [uB, wXY, Assignment.restrict, hvy]
  · refine Audit.marginal_ne_zero_of _ _ _ (uB G Z s true) ?_ (uB_pos hs true)
    funext ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with h | h
    · have hv' := Finset.mem_singleton.mp h
      subst hv'
      simp [uB, wXY, Assignment.restrict, hy]
    · have hvy : v ≠ y := fun e => hyZ (e ▸ h)
      have hnr : ¬ ReachAvoid G Z s v := fun hr => reach_not_mem hs hr h
      simp [uB, wXY, Assignment.restrict, hvy, hnr]

/-! ## Nivå 3a-2: åpen, kolliderfri vandring ⇒ trek -/

/-- Foroverfasen: åpen for både `Z` og `∅` i tilstanden `.fwd` betyr bare
foroversteg, og hver node er utenfor `Z`. -/
lemma fwd_phase {G : DAG V} {Z : Finset V} :
    ∀ {c b : V} (q : Walk G c b), b ∉ Z →
      ¬ Walk.blockedAux Z .fwd q → ¬ Walk.blockedAux ∅ .fwd q →
      c ∉ Z ∧ ReachAvoid G Z c b := by
  intro c b q
  induction q with
  | nil v =>
    intro hb _ _
    exact ⟨hb, Relation.ReflTransGen.refl⟩
  | fwd e q ih =>
    intro hb hZ h0
    obtain ⟨hc', hr⟩ := ih hb (fun h => hZ (Or.inr h)) (fun h => h0 (Or.inr h))
    exact ⟨fun h => hZ (Or.inl h), Relation.ReflTransGen.head ⟨e, hc'⟩ hr⟩
  | bwd e q _ =>
    intro _ _ h0
    exact absurd (Or.inl (fun z hz => by simp at hz)) h0

/-- Bakoverfasen: vi fører med oss en rettet vei tilbake til `x` som unngår `Z`.
Ved første foroversteg er den nåværende noden kilden til en trek. -/
lemma trek_of_open {G : DAG V} {Z : Finset V} {x : V} :
    ∀ {a b : V} (q : Walk G a b) (inc : Incoming), inc ≠ .fwd →
      (inc = .start → a ∉ Z) → b ∉ Z →
      ¬ Walk.blockedAux Z inc q → ¬ Walk.blockedAux ∅ inc q →
      ReachAvoid G Z a x →
      ∃ s, s ∉ Z ∧ ReachAvoid G Z s x ∧ ReachAvoid G Z s b := by
  intro a b q
  induction q with
  | nil v =>
    intro _ _ _ hb _ _ acc
    exact ⟨v, hb, acc, Relation.ReflTransGen.refl⟩
  | @fwd a a' _ e q _ =>
    intro inc hinc hst hb hZ h0 acc
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
    have h0' : ¬ Walk.blockedAux ∅ .fwd q := by
      cases inc with
      | start => exact h0
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => h0 (Or.inr h)
    obtain ⟨ha', hr⟩ := fwd_phase q hb hZ' h0'
    exact ⟨a, ha, acc, Relation.ReflTransGen.head ⟨e, ha'⟩ hr⟩
  | @bwd a a' _ e q ih =>
    intro inc hinc hst hb hZ h0 acc
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
    have h0' : ¬ Walk.blockedAux ∅ .bwd q := by
      cases inc with
      | start => exact h0
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => h0 (Or.inr h)
    exact ih .bwd (by intro h; cases h) (by intro h; cases h) hb hZ' h0'
      (Relation.ReflTransGen.head ⟨e, ha⟩ acc)

/-- **Nivå 3a-2.** Finnes en vandring fra `x` til `y` som er åpen gitt `Z` og uten
kollidere (åpen gitt `∅`), så finnes en modell der `CondIndep {x} {y} Z` svikter. -/
theorem not_condIndep_of_colliderFree (G : DAG V) (Z : Finset V) (x y : V)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hxy : x ≠ y) (p : Walk G x y)
    (hZ : ¬ Walk.Blocked Z p) (h0 : ¬ Walk.Blocked ∅ p) :
    ∃ M : G.CausalModel (fun _ => Bool), ¬ CondIndep M {x} {y} Z := by
  obtain ⟨s, hs, hsx, hsy⟩ := trek_of_open p .start (by intro h; cases h)
    (fun _ => hxZ) hyZ hZ h0 Relation.ReflTransGen.refl
  exact ⟨trekModel G Z s, trek_not_condIndep G Z s x y hs hsx hsy hxy⟩

/-- **Fullstendighet for marginal uavhengighet.** Er `x` og `y` ikke d-separert
gitt `∅`, finnes en modell der de er avhengige. -/
theorem dsep_complete_marginal (G : DAG V) (x y : V) (hxy : x ≠ y)
    (h : ¬ G.DSeparated ∅ x y) :
    ∃ M : G.CausalModel (fun _ => Bool), ¬ CondIndep M {x} {y} ∅ := by
  obtain ⟨p, hp⟩ : ∃ p : Walk G x y, ¬ Walk.Blocked ∅ p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  exact not_condIndep_of_colliderFree G ∅ x y (by simp) (by simp) hxy p hp hp

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

lemma map_unif_ne_zero {β γ : Type*} [Fintype β] [Nonempty β] (f : β → γ) (a : γ) :
    (PMF.map f (PMF.uniformOfFintype β)) a ≠ 0 ↔ ∃ b, f b = a := by
  rw [← PMF.mem_support_iff, PMF.support_map, PMF.support_uniformOfFintype]
  simp

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
  rw [if_neg hvZ, map_unif_ne_zero] at hk
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
  · rw [if_neg hvZ, map_unif_ne_zero]
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
  · rw [if_neg hvZ, map_unif_ne_zero]
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

/-! ## Fullstendighet for regel 1 -/

section Rule1
open DoCalculus

lemma parents_cutIn_sub {G : DAG V} (X : Finset V) (v : V) :
    (cutIn G X).parents v ⊆ G.parents v := by
  intro u hu
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact hu.1

/-- En modell på `G_{X̄}` løftet til `G`: kjernene ignorerer foreldre i `X`-kanter. -/
noncomputable def liftModel {G : DAG V} {X : Finset V} {α : V → Type*}
    (N : (cutIn G X).CausalModel α) : G.CausalModel α where
  fin := N.fin
  deq := N.deq
  kernel := fun v pa => N.kernel v (fun u => pa ⟨u.1, parents_cutIn_sub X v u.2⟩)

/-- Er alle `X`-kjernene i `N` punktmasser i `x`, så er `do(X = x)` i den løftede
modellen lik `N`. -/
theorem doModel_lift {G : DAG V} {X : Finset V} {α : V → Type*}
    (N : (cutIn G X).CausalModel α) (x : Assignment (α := α) X)
    (hX : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩)) :
    doModel (liftModel N) X x = N := by
  obtain ⟨fin, deq, ker⟩ := N
  simp only [doModel, liftModel, CausalModel.mk.injEq, true_and]
  funext v p
  split_ifs with hv
  · exact (hX v hv p).symm
  · rfl

/-- I kjedemodellen på `G_{X̄}` med betinging på `X ∪ W` er `X`-nodene konstant
`false`: de har ingen foreldre, så de kan ikke være XOR-noder. -/
lemma chain_X_false {G : DAG V} {X W : Finset V} {y z : V}
    (C : Chain (cutIn G X) (X ∪ W) y z) :
    ∀ v (hv : v ∈ X) p, (chainModel C).kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X)
        ⟨v, hv⟩) := by
  intro v hv p
  simp only [chainModel]
  rw [if_pos (Finset.mem_union_left W hv), dif_neg]
  rintro ⟨j, hj⟩
  obtain ⟨q, hq, _⟩ := C.hl j
  rw [hj] at hq
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  exact hq.2 hv

/-- **Fullstendighet for regel 1.** Er `y` og `z` ikke d-separert gitt `X ∪ W` i
`G_{X̄}`, finnes en modell på `G` og en verdi `x` der
`P_x(y | z, x, w) = P_x(y | x, w)` svikter. -/
theorem rule1_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn G X).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) {y} {z} (X ∪ W) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn G X) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  refine ⟨C'.k, liftModel (chainModel C'), fun _ _ => false, ?_⟩
  rw [doModel_lift (chainModel C') (fun _ _ => false) (chain_X_false C')]
  exact chain_not_condIndep C' hinj hyz

end Rule1

/-! ## Fullstendighet for regel 2 -/

section Rule2
open DoCalculus

/-- Like kjernefaktorer gir like marginaler, også på forskjellige grafer. -/
lemma marginal_eq_of_kfac {G1 G2 : DAG V} {α : V → Type*}
    (M1 : G1.CausalModel α) (M2 : G2.CausalModel α)
    (h : ∀ (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V),
      kfac M1 Finset.univ u v = kfac M2 Finset.univ u v)
    (S : Finset V) : M1.marginal S = M2.marginal S := by
  have hj : M1.fullJoint = M2.fullJoint := PMF.ext fun u => by
    rw [fullJoint_apply_prod, fullJoint_apply_prod]
    exact Finset.prod_congr rfl (fun v _ => h u v)
  unfold CausalModel.marginal
  rw [hj]

/-- Løft fra en delgraf: kjernene ignorerer foreldre som bare finnes i `G`. -/
noncomputable def liftSub {G H : DAG V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α) : G.CausalModel α where
  fin := N.fin
  deq := N.deq
  kernel := fun v pa => N.kernel v (fun u => pa ⟨u.1, hsub v u.2⟩)

/-- En node i betingingsmengden uten foreldre er konstant `false` i kjedemodellen. -/
lemma chain_noparent_false {H : DAG V} {Z' : Finset V} {y z : V} (C : Chain H Z' y z)
    (v : V) (hvZ : v ∈ Z') (hnp : ∀ u, ¬ H.edge u v) :
    ∀ p, (chainModel C).kernel v p = PMF.pure (fun _ => false) := by
  intro p
  simp only [chainModel]
  rw [if_pos hvZ, dif_neg]
  rintro ⟨j, hj⟩
  obtain ⟨q, hq, _⟩ := C.hl j
  rw [hj] at hq
  simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  exact hnp q hq

/-- do(X = x) i den løftede modellen har samme kjernefaktorer som `N`. -/
lemma lift_do_kfac {G H : DAG V} {X : Finset V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α)
    (x : Assignment (α := α) X)
    (hXN : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩))
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (liftSub hsub N) X x) Finset.univ u v = kfac N Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
    rw [hXN v hx]
  · simp only [doModel, dif_neg hx, liftSub] <;> rfl

/-- do(X = x), do(Z = z₀) i den løftede modellen har samme kjernefaktorer som
do(Z = z₀) i `N`. -/
lemma lift_do_do_kfac {G H : DAG V} {X Zs : Finset V} {α : V → Type*}
    (hsub : ∀ v, H.parents v ⊆ G.parents v) (N : H.CausalModel α)
    (x : Assignment (α := α) X) (z₀ : Assignment (α := α) Zs)
    (hXN : ∀ v (hv : v ∈ X) p, N.kernel v p = PMF.pure (x ⟨v, hv⟩))
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (doModel (liftSub hsub N) X x) Zs z₀) Finset.univ u v =
      kfac (doModel N Zs z₀) Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hz : v ∈ Zs
  · simp only [doModel, dif_pos hz]
  · by_cases hx : v ∈ X
    · simp only [doModel, dif_neg hz, dif_pos hx]
      rw [hXN v hx]
    · simp only [doModel, dif_neg hz, dif_neg hx, liftSub] <;> rfl

/-- **Fullstendighet for regel 2.** Er `y` og `z` ikke d-separert gitt `X ∪ W` i
`G_{X̄Z̲}`, finnes en modell på `G` og verdier der produktformen i `rule2` svikter. -/
theorem rule2_complete (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutOut (cutIn G X) {z}).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) {z},
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
        t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ ∧
        (doModel M X x).marginal ({y} ∪ {z} ∪ (X ∪ W)) t *
          (doModel (doModel M X x) {z} z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel (doModel M X x) {z} z₀).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal ({z} ∪ (X ∪ W))
            (t.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutOut (cutIn G X) {z}) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hN := chain_not_condIndep C' hinj hyz
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutOut (cutIn G X) {z}).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w.restrict hzs, w, rfl, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN)
  have hB : ∀ S, z ∉ S → (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      {z} (w.restrict hzs)).marginal S = (chainModel C').marginal S := by
    intro S hS
    rw [marginal_eq_of_kfac _ (doModel (chainModel C') {z} (w.restrict hzs))
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN)]
    refine PMF.ext fun s => Rule3.doModel_marginal_of_sub (chainModel C') {z} _
      (Finset.univ.erase z) ?_ (by simp) S ?_ s
    · intro v _ w' e
      exact Finset.mem_erase.mpr ⟨fun hw' => e.2 (Finset.mem_singleton.mpr hw'), Finset.mem_univ _⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun e => hS (e ▸ hv), Finset.mem_univ v⟩
  have hz2 : z ∉ ({y} ∪ (X ∪ W) : Finset V) := fun hm =>
    (Finset.mem_union.mp hm).elim (fun e => hyz (Finset.mem_singleton.mp e).symm) hz
  rw [hB (X ∪ W) hz, hB ({y} ∪ (X ∪ W)) hz2, hA, hA]
  exact hw

end Rule2

/-! ## Fullstendighet for regel 3, tilfellet `z ∉ An(W)` -/

section Rule3C
open DoCalculus

/-- I en graf der `z` ikke har noen kanter, ender enhver vandring til `z` i `z`. -/
lemma walk_to_isolated {H : DAG V} {z : V}
    (hiso : ∀ u, ¬ H.edge u z ∧ ¬ H.edge z u) :
    ∀ {a b : V} (p : Walk H a b), b = z → a = z := by
  intro a b p
  induction p with
  | nil v =>
    intro h
    exact h
  | @fwd a b' _ e p ih =>
    intro hc
    have h1 := ih hc
    rw [h1] at e
    exact absurd e (hiso a).1
  | @bwd a b' _ e p ih =>
    intro hc
    have h1 := ih hc
    rw [h1] at e
    exact absurd e (hiso a).2

/-- Har `z` ingen foreldre i `H`, er `z` isolert i `H_{z̲}`, og dermed d-separert fra
enhver mengde uten `z`, gitt `∅`. -/
lemma dsep_isolated {H : DAG V} {z : V} (hnp : ∀ u, ¬ H.edge u z)
    (S : Finset V) (hS : z ∉ S) :
    SetSound.DSeparatedSet (cutOut H {z}) ∅ S {z} := by
  have hiso : ∀ u, ¬ (cutOut H {z}).edge u z ∧ ¬ (cutOut H {z}).edge z u :=
    fun u => ⟨fun e => hnp u e.1, fun e => e.2 (Finset.mem_singleton_self z)⟩
  intro s hs z' hz' p _
  exfalso
  have hs' : s = z := walk_to_isolated hiso p (Finset.mem_singleton.mp hz')
  exact hS (hs' ▸ hs)

/-- Er `z` ikke forfar til `W`, er `Z(W) = {z}`. -/
lemma Z2_singleton {H : DAG V} {z : V} {W : Finset V} (h : z ∉ ancestors H W) :
    Rule3.Z2 H {z} W = {z} := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun hv => hv.1
  · rintro rfl
    exact ⟨rfl, h⟩

/-- **Fullstendighet for regel 3 når `z` ikke er forfar til `W`.** Svikter
betingelsen i `rule3_general`, finnes en modell på `G` og verdier der produktformen
i regel 3 svikter. -/
theorem rule3_complete_nonanc (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∉ ancestors (cutIn G X) W)
    (h : ¬ (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
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
  rw [Z2_singleton hanc] at h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) {z}) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  obtain ⟨C⟩ := chain_of_open hy hz p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hN := chain_not_condIndep C' hinj hyz
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) {z}).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ u, ¬ (cutIn (cutIn G X) {z}).edge u z :=
    fun u e => e.2 (Finset.mem_singleton_self z)
  have hzy : z ∉ ({y} ∪ (X ∪ W) : Finset V) := fun hm =>
    (Finset.mem_union.mp hm).elim (fun e => hyz (Finset.mem_singleton.mp e).symm) hz
  -- z er en rot: å sette z er å betinge på z (FD1 med X := {z}).
  have fa : (chainModel C').marginal ({y} ∪ {z} ∪ (X ∪ W)) w =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal ({y} ∪ (X ∪ W))
        (w.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := {y} ∪ (X ∪ W) ∪ {z})
      (T := {y} ∪ {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} ({y} ∪ (X ∪ W))
      (Finset.disjoint_singleton_right.mpr hzy) (dsep_isolated hnp _ hzy) _
  have fd : (chainModel C').marginal ({z} ∪ (X ∪ W))
        (w.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal {z} (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := X ∪ W ∪ {z})
      (T := {z} ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') {z} (X ∪ W)
      (Finset.disjoint_singleton_right.mpr hz) (dsep_isolated hnp _ hz) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      {z} (w.restrict hzs)).marginal S =
      (doModel (chainModel C') {z} (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

end Rule3C

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
