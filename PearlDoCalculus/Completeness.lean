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

/-- **Regel 3 svikter når `y` og `z` er d-forbundet i `G_{X̄z̄}`**, uansett om `z`
er forfar til `W`. Da kan `z` gjøres til en rot. `rule3_complete_nonanc` er
spesialtilfellet der denne grafen er grafen i regel 3. -/
theorem rule3_complete_root (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (h : ¬ (cutIn (cutIn G X) {z}).DSeparated (X ∪ W) y z) :
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

/-! ## Reglene som ekvivalenser -/

section RuleIff
open DoCalculus

lemma dsepSet_single {H : DAG V} {S : Finset V} {y z : V} (h : H.DSeparated S y z) :
    SetSound.DSeparatedSet H S {y} {z} := by
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  subst ha
  subst hb
  exact dsepPath_of_dsep h

/-- **Regel 1 er eksakt.** Betingelsen i regel 1 holder hvis og bare hvis regelen
holder i alle modeller på `G` og for alle verdier `x`. -/
theorem rule1_iff (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) :
    (cutIn G X).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X),
        CondIndep (doModel M X x) {y} {z} (X ∪ W) := by
  constructor
  · intro h k M x
    exact rule1 M X W {y} {z} x (Finset.disjoint_singleton_left.mpr hy)
      (Finset.disjoint_singleton_left.mpr hz) (dsepSet_single h)
  · intro H
    by_contra hn
    obtain ⟨k, M, x, hM⟩ := rule1_complete G X W y z hy hz hyz hn
    exact hM (H k M x)

/-- **Regel 2 er eksakt.** -/
theorem rule2_iff (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) :
    (cutOut (cutIn G X) {z}).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) {z})
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W))),
        t.restrict (show ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ →
        (doModel M X x).marginal ({y} ∪ {z} ∪ (X ∪ W)) t *
          (doModel (doModel M X x) {z} z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel (doModel M X x) {z} z₀).marginal ({y} ∪ (X ∪ W))
            (t.restrict (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal ({z} ∪ (X ∪ W))
            (t.restrict (show {z} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x z₀ t ht
    exact rule2 M X {y} {z} W x z₀ (Finset.disjoint_singleton.mpr hyz)
      (Finset.disjoint_singleton_right.mpr hz) (Finset.disjoint_singleton_left.mpr hy)
      (dsepSet_single h) t ht
  · intro H
    by_contra hn
    obtain ⟨k, M, x, z₀, t, ht, hne⟩ := rule2_complete G X W y z hy hz hyz hn
    exact hne (H k M x z₀ t ht)

/-- **Regel 3 er eksakt når `z` ikke er forfar til `W`.** -/
theorem rule3_iff_nonanc (G : DAG V) (X W : Finset V) (y z : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z)
    (hanc : z ∉ ancestors (cutIn G X) W) :
    (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) {z} W)).DSeparated (X ∪ W) y z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W))),
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
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_nonanc G X W y z hy hz hyz hanc hn
    exact hne (H k M x t)

end RuleIff

/-! ## Dekomponering og mengdeversjonene -/

section SetVersions
open DoCalculus

/-- Enhver tilordning på `S ⊆ T` kan utvides til `T`. -/
lemma exists_restrict_eq {α : V → Type*} [∀ w, Nonempty (α w)] {S T : Finset V}
    (h : S ⊆ T) (b : Assignment (α := α) S) :
    ∃ a : Assignment (α := α) T, a.restrict h = b :=
  ⟨fun v => if hv : v.1 ∈ S then b ⟨v.1, hv⟩ else Classical.arbitrary _, by
    funext ⟨v, hv⟩
    simp [Assignment.restrict, hv]⟩

/-- **Symmetri.** -/
lemma condIndep_symm {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (h : CondIndep M X Y Z) : CondIndep M Y X Z := by
  intro w
  rw [Adjustment.marginal_eq_of_subset' M (S := X ∪ Y ∪ Z) (T := Y ∪ X ∪ Z)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto),
    mul_comm (M.marginal (Y ∪ Z) _)]
  exact h _

/-- **Dekomponering, høyre side.** Er `X ⊥ Y | Z` og `Y' ⊆ Y`, så er `X ⊥ Y' | Z`. -/
lemma condIndep_drop_right {G : DAG V} {α : V → Type*} (M : G.CausalModel α)
    [∀ w, Nonempty (α w)] {X Y Y' Z : Finset V}
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z) (hY' : Y' ⊆ Y) (h : CondIndep M X Y Z) :
    CondIndep M X Y' Z := by
  have h1 := Finset.disjoint_left.mp hXY
  have h2 := Finset.disjoint_left.mp hYZ
  have hBA : X ∪ Y' ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDA : Y \ Y' ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hBD : Disjoint (X ∪ Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with (hv | hv) | hv
    · exact h1 hv hv'.1
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB : X ∪ Y ∪ Z ⊆ X ∪ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hYZA : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDYZ : Y \ Y' ⊆ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hB2 : Y' ∪ Z ⊆ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hBD2 : Disjoint (Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with hv | hv
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB2 : Y ∪ Z ⊆ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hZD : Disjoint Z (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact h2 (Finset.mem_sdiff.mp hv').1 hv
  have hXZD : Disjoint (X ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h1 hv (Finset.mem_sdiff.mp hv').1
    · exact h2 (Finset.mem_sdiff.mp hv').1 hv
  intro b
  obtain ⟨a, rfl⟩ := exists_restrict_eq hBA b
  have e1 : M.marginal (X ∪ Y' ∪ Z) (a.restrict hBA) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (X ∪ Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d) :=
    (Rule3Flag.marginal_sum_Z M hDA hBA hBD hAB a).symm
  have e2 : M.marginal (Y' ∪ Z) ((a.restrict hBA).restrict
        (show Y' ∪ Z ⊆ X ∪ Y' ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (Y ∪ Z) (a.restrict hYZA) d) :=
    (Rule3Flag.marginal_sum_Z M hDYZ hB2 hBD2 hAB2 (a.restrict hYZA)).symm
  rw [e1, e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun d => ?_)
  have hci := h (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d)
  rw [Rule3Flag.setZ_restrict_disj _ hZD a d, Rule3Flag.setZ_restrict_disj _ hXZD a d] at hci
  exact hci

/-- **Dekomponering til enkeltnoder.** -/
lemma condIndep_single {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : CondIndep M X Y Z) {x y : V} (hx : x ∈ X) (hy : y ∈ Y) :
    CondIndep M {x} {y} Z := by
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have h1 := condIndep_drop_right M hXY hYZ (Finset.singleton_subset_iff.mpr hy) h
  have hyX : Disjoint ({y} : Finset V) X :=
    Finset.disjoint_singleton_left.mpr (fun hyX => Finset.disjoint_left.mp hXY hyX hy)
  exact condIndep_symm M (condIndep_drop_right M hyX hXZ
    (Finset.singleton_subset_iff.mpr hx) (condIndep_symm M h1))

/-- **d-separasjon av mengder ⇔ uavhengighet i alle modeller.** -/
theorem dsepSet_iff (G : DAG V) (Z X Y : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hXY : Disjoint X Y) :
    SetSound.DSeparatedSet G Z X Y ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool)), CondIndep M X Y Z := by
  constructor
  · intro h k M
    exact SetSound.dsep_sound_set M X Y Z hXZ hYZ h
  · intro H
    by_contra hn
    simp only [SetSound.DSeparatedSet, not_forall] at hn
    obtain ⟨x, hx, y, hy, hn⟩ := hn
    obtain ⟨k, M, hM⟩ := dsep_complete G Z x y (Finset.disjoint_left.mp hXZ hx)
      (Finset.disjoint_left.mp hYZ hy)
      (fun e => Finset.disjoint_left.mp hXY hx (by rw [e]; exact hy))
      (fun hd => hn (dsepPath_of_dsep hd))
    exact hM (condIndep_single M hXY hXZ hYZ (H k M) hx hy)

/-- **Fullstendighet for regel 1 med mengder.** -/
theorem rule1_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) Y Z (X ∪ W) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨k, M, x, hM⟩ := rule1_complete G X W y z (Finset.disjoint_left.mp hY hy)
    (Finset.disjoint_left.mp hZ hz)
    (fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz))
    (fun hd => hn (dsepPath_of_dsep hd))
  exact ⟨k, M, x, fun hci => hM (condIndep_single _ hYZ hY hZ hci hy hz)⟩

/-- **Regel 1 er eksakt, i nøyaktig den formen `rule1` har.** -/
theorem rule1_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X),
        CondIndep (doModel M X x) Y Z (X ∪ W) := by
  constructor
  · intro h k M x
    exact rule1 M X W Y Z x hY hZ h
  · intro H
    by_contra hn
    obtain ⟨k, M, x, hM⟩ := rule1_complete_set G X W Y Z hY hZ hYZ hn
    exact hM (H k M x)

end SetVersions

/-! ## Regel 2 for mengder -/

section Rule2Set
open DoCalculus

/-- **Fullstendighet for regel 2 med mengder.** -/
theorem rule2_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ ∧
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutOut (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutOut (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w.restrict hzs, w, rfl, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, Disjoint S Z →
      (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
        Z (w.restrict hzs)).marginal S = (chainModel C').marginal S := by
    intro S hS
    rw [marginal_eq_of_kfac _ (doModel (chainModel C') Z (w.restrict hzs))
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN)]
    refine PMF.ext fun s => Rule3.doModel_marginal_of_sub (chainModel C') Z _
      (Finset.univ \ Z) ?_ Finset.sdiff_disjoint S ?_ s
    · intro v _ w' e
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e.2⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, Finset.disjoint_left.mp hS hv⟩
  rw [hB (X ∪ W) hZ.symm, hB (Y ∪ (X ∪ W)) (Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩),
    hA, hA]
  exact hw

/-- **Regel 2 er eksakt, i nøyaktig den formen `rule2` har.** -/
theorem rule2_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ →
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x z₀ t ht
    exact rule2 M X Y Z W x z₀ hYZ hZ.symm hY h t ht
  · intro H
    by_contra hn
    obtain ⟨k, M, x, z₀, t, ht, hne⟩ := rule2_complete_set G X W Y Z hY hZ hYZ hn
    exact hne (H k M x z₀ t ht)

end Rule2Set

/-! ## Regel 3 for mengder, når ingen `z ∈ Z` er forfar til `W` -/

section Rule3Set
open DoCalculus

lemma walk_to_isolated_set {H : DAG V} {Z : Finset V}
    (hiso : ∀ z ∈ Z, ∀ u, ¬ H.edge u z ∧ ¬ H.edge z u) :
    ∀ {a b : V} (p : Walk H a b), b ∈ Z → a ∈ Z := by
  intro a b p
  induction p with
  | nil v =>
    intro h
    exact h
  | @fwd a b' _ e p ih =>
    intro hc
    exact absurd e (hiso b' (ih hc) a).1
  | @bwd a b' _ e p ih =>
    intro hc
    exact absurd e (hiso b' (ih hc) a).2

lemma dsep_isolated_set {H : DAG V} {Z : Finset V} (hnp : ∀ z ∈ Z, ∀ u, ¬ H.edge u z)
    (S : Finset V) (hS : Disjoint S Z) :
    SetSound.DSeparatedSet (cutOut H Z) ∅ S Z := by
  have hiso : ∀ z ∈ Z, ∀ u, ¬ (cutOut H Z).edge u z ∧ ¬ (cutOut H Z).edge z u :=
    fun z hz u => ⟨fun e => hnp z hz u e.1, fun e => e.2 hz⟩
  intro s hs z' hz' p _
  exfalso
  exact Finset.disjoint_left.mp hS hs (walk_to_isolated_set hiso p hz')

lemma Z2_all {H : DAG V} {Z W : Finset V} (h : ∀ z ∈ Z, z ∉ ancestors H W) :
    Rule3.Z2 H Z W = Z := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter]
  constructor
  · exact fun hv => hv.1
  · intro hv
    exact ⟨hv, h v hv⟩

/-- **Fullstendighet for regel 3 med mengder, når ingen `z ∈ Z` er forfar til `W`.** -/
theorem rule3_complete_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
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
  rw [Z2_all hanc] at h
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ z ∈ Z, ∀ u, ¬ (cutIn (cutIn G X) Z).edge u z :=
    fun z hz u e => e.2 hz
  have hYXWZ : Disjoint (Y ∪ (X ∪ W)) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩
  have fa : (chainModel C').marginal (Y ∪ Z ∪ (X ∪ W)) w =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (Y ∪ (X ∪ W))
        (w.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := Y ∪ (X ∪ W) ∪ Z)
      (T := Y ∪ Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (Y ∪ (X ∪ W)) hYXWZ
      (dsep_isolated_set hnp _ hYXWZ) _
  have fd : (chainModel C').marginal (Z ∪ (X ∪ W))
        (w.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := X ∪ W ∪ Z)
      (T := Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (X ∪ W) hZ.symm
      (dsep_isolated_set hnp _ hZ.symm) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      Z (w.restrict hzs)).marginal S =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

/-- **Regel 3 er eksakt for mengder når ingen `z ∈ Z` er forfar til `W`.** -/
theorem rule3_iff_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W) :
    SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
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
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_set_nonanc G X W Y Z hY hZ hYZ hanc hn
    exact hne (H k M x t)

/-- **Regel 3 svikter for mengder når `Y` og `Z` er d-forbundet i `G_{X̄Z̄}`.** -/
theorem rule3_complete_set_root (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
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
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨p, hp⟩ : ∃ p : Walk (cutIn (cutIn G X) Z) y z, ¬ Walk.Blocked (X ∪ W) p := by
    by_contra hc
    exact hn (dsepPath_of_dsep (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  obtain ⟨C⟩ := chain_of_open (Finset.disjoint_left.mp hY hy) (Finset.disjoint_left.mp hZ hz) p hp
  obtain ⟨C', hinj⟩ := chain_injective C.k C rfl
  have hyz : y ≠ z := fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz)
  have hN0 := chain_not_condIndep C' hinj hyz
  have hN : ¬ CondIndep (chainModel C') Y Z (X ∪ W) :=
    fun hc => hN0 (condIndep_single _ hYZ hY hZ hc hy hz)
  simp only [CausalModel.CondIndep, not_forall] at hN
  obtain ⟨w, hw⟩ := hN
  have hsub : ∀ v, (cutIn (cutIn G X) Z).parents v ⊆ G.parents v := by
    intro v u hu
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1.1
  have hXN : ∀ v (hv : v ∈ X) p, (chainModel C').kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C'.k + 1) → Bool) X)
        ⟨v, hv⟩) :=
    fun v hv p => chain_noparent_false C' v (Finset.mem_union_left W hv)
      (fun u e => e.1.2 hv) p
  have hzs : Z ⊆ Y ∪ Z ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hnp : ∀ z ∈ Z, ∀ u, ¬ (cutIn (cutIn G X) Z).edge u z :=
    fun z hz u e => e.2 hz
  have hYXWZ : Disjoint (Y ∪ (X ∪ W)) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hZ.symm⟩
  have fa : (chainModel C').marginal (Y ∪ Z ∪ (X ∪ W)) w =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (Y ∪ (X ∪ W))
        (w.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := Y ∪ (X ∪ W) ∪ Z)
      (T := Y ∪ Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (Y ∪ (X ∪ W)) hYXWZ
      (dsep_isolated_set hnp _ hYXWZ) _
  have fd : (chainModel C').marginal (Z ∪ (X ∪ W))
        (w.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal (X ∪ W)
        (w.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (chainModel C').marginal Z (w.restrict hzs) := by
    rw [Adjustment.marginal_eq_of_subset' (chainModel C') (S := X ∪ W ∪ Z)
      (T := Z ∪ (X ∪ W))
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)]
    exact Adjustment.frontdoor_step1 (chainModel C') Z (X ∪ W) hZ.symm
      (dsep_isolated_set hnp _ hZ.symm) _
  have key : ∀ A q b c B : ENNReal, A * b = c * B → A * q * b = c * (B * q) := by
    intro A q b c B e
    rw [mul_right_comm, e, mul_assoc]
  refine ⟨C'.k, liftSub hsub (chainModel C'), fun _ _ => false, w, ?_⟩
  have hA : ∀ S, (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false)).marginal S =
      (chainModel C').marginal S :=
    fun S => marginal_eq_of_kfac _ _ (lift_do_kfac hsub (chainModel C') _ hXN) S
  have hB : ∀ S, (doModel (doModel (liftSub hsub (chainModel C')) X (fun _ _ => false))
      Z (w.restrict hzs)).marginal S =
      (doModel (chainModel C') Z (w.restrict hzs)).marginal S :=
    fun S => marginal_eq_of_kfac _ _
      (lift_do_do_kfac hsub (chainModel C') _ (w.restrict hzs) hXN) S
  rw [hB, hB, hA, hA]
  intro heq
  apply hw
  rw [fa, fd]
  exact key _ _ _ _ _ heq

end Rule3Set

/-! ## Regel 3: kopi-modellen -/

section Rule3Copy
open DoCalculus

/-- Kopi-modellen: `s` er en uniform bit, noder utenfor `S` og `w1` er OR av
foreldrene utenfor `S`, andre noder i `S` er `false`. -/
noncomputable def copyNet (H : DAG V) (S : Finset V) (s w1 : V) :
    H.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = w1 then PMF.pure (decide (∃ p : {u // u ∈ H.parents v}, p.1 ∉ S ∧ pa p = true))
    else if v ∈ S then PMF.pure false
    else if v = s then PMF.uniformOfFintype Bool
    else PMF.pure (decide (∃ p : {u // u ∈ H.parents v}, p.1 ∉ S ∧ pa p = true))

lemma copy_kernel_w1 (H : DAG V) (S : Finset V) (s w1 : V)
    (pa : {u // u ∈ H.parents w1} → Bool) :
    (copyNet H S s w1).kernel w1 pa =
      PMF.pure (decide (∃ p : {u // u ∈ H.parents w1}, p.1 ∉ S ∧ pa p = true)) := by
  simp [copyNet]

lemma copy_kernel_S {H : DAG V} {S : Finset V} {s w1 v : V} (hv : v ∈ S) (hvw : v ≠ w1)
    (pa : {u // u ∈ H.parents v} → Bool) :
    (copyNet H S s w1).kernel v pa = PMF.pure false := by
  simp [copyNet, hv, hvw]

lemma copy_kernel_s {H : DAG V} {S : Finset V} {s w1 : V} (hs : s ∉ S) (hsw : s ≠ w1)
    (pa : {u // u ∈ H.parents s} → Bool) :
    (copyNet H S s w1).kernel s pa = PMF.uniformOfFintype Bool := by
  simp [copyNet, hs, hsw]

lemma copy_kernel_other {H : DAG V} {S : Finset V} {s w1 v : V} (hvS : v ∉ S) (hvs : v ≠ s)
    (hvw : v ≠ w1) (pa : {u // u ∈ H.parents v} → Bool) :
    (copyNet H S s w1).kernel v pa =
      PMF.pure (decide (∃ p : {u // u ∈ H.parents v}, p.1 ∉ S ∧ pa p = true)) := by
  simp [copyNet, hvS, hvs, hvw]

/-- **Støtten til kopi-modellen.** -/
lemma copy_support (H : DAG V) (S : Finset V) (s w1 : V) (hs : s ∉ S) (hw1 : w1 ∈ S)
    (u : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (copyNet H S s w1) Finset.univ u v ≠ 0) :
    ∀ v, v ∉ S → (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachAvoid H S s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) := by
  suffices Hn : ∀ n, ∀ v, H.rank v = n → v ∉ S → (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachAvoid H S s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) from fun v => Hn _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hr hvS
  by_cases hvs : v = s
  · subst hvs
    exact ⟨fun h => ⟨Relation.ReflTransGen.refl, h⟩, fun h => h.2⟩
  have hvw : v ≠ w1 := fun e => hvS (e ▸ hw1)
  have hk := hpos v
  rw [DoAudit.kfac_univ, copy_kernel_other hvS hvs hvw, PMF.pure_apply] at hk
  have huv : u ⟨v, Finset.mem_univ v⟩ = decide (∃ p : {u // u ∈ H.parents v},
      p.1 ∉ S ∧ (u.restrict (Finset.subset_univ _)) p = true) := by
    by_contra h
    exact hk (if_neg h)
  rw [huv, decide_eq_true_iff, reach_iff_parent hvS hvs]
  constructor
  · rintro ⟨⟨p, hp⟩, hpS, hpu⟩
    have hlt : H.rank p < n := by
      have := H.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    obtain ⟨hrp, hs'⟩ := (ih _ hlt p rfl hpS).mp hpu
    exact ⟨⟨p, hp, hrp⟩, hs'⟩
  · rintro ⟨⟨p, hp, hrp⟩, hs'⟩
    have hpS : p ∉ S := reach_not_mem hs hrp
    have hlt : H.rank p < n := by
      have := H.rank_strict_mono p v (by simpa [DAG.parents] using hp)
      omega
    exact ⟨⟨p, hp⟩, hpS, (ih _ hlt p rfl hpS).mpr ⟨hrp, hs'⟩⟩

/-- Observasjonelt vitne: biten er 1. -/
noncomputable def ubObs (H : DAG V) (S : Finset V) (s w1 : V) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 ∈ S then decide (v.1 = w1) else decide (ReachAvoid H S s v.1)

/-- Vitne under `do(z = 1)`: biten er 0, så bare det `z` når, er sant. -/
noncomputable def ubDo (H : DAG V) (S : Finset V) (z w1 : V) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 = z then true else if v.1 ∈ S then decide (v.1 = w1)
    else decide (ReachAvoid H S z v.1)

/-- Punktet: `z` og `w1` er sanne, alt annet usant. -/
def copyPt (z w1 : V) (A : Finset V) : Assignment (α := fun _ : V => Bool) A :=
  fun v => decide (v.1 = z ∨ v.1 = w1)

lemma ubObs_pos {H : DAG V} {S : Finset V} {s w1 : V} (hs : s ∉ S) (hw1 : w1 ∈ S)
    (hrz : RZ H S s w1) :
    ∀ v, kfac (copyNet H S s w1) Finset.univ (ubObs H S s w1) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  by_cases hvw : v = w1
  · subst hvw
    rw [copy_kernel_w1, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · obtain ⟨p, hp, hr⟩ := hrz
      have hpS : p ∉ S := reach_not_mem hs hr
      have e1 : ubObs H S s v ⟨v, Finset.mem_univ v⟩ = true := by simp [ubObs, hw1]
      rw [e1, eq_comm, decide_eq_true_iff]
      exact ⟨⟨p, hp⟩, hpS, by
        show ubObs H S s v ⟨p, Finset.mem_univ p⟩ = true
        simp [ubObs, hpS, hr]⟩
  by_cases hvS : v ∈ S
  · rw [copy_kernel_S hvS hvw, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · simp [ubObs, hvS, hvw]
  by_cases hvs : v = s
  · subst hvs
    rw [copy_kernel_s hs hvw]
    simp [PMF.uniformOfFintype_apply]
  rw [copy_kernel_other hvS hvs hvw, PMF.pure_apply, if_pos]
  · exact one_ne_zero
  · rw [Bool.eq_iff_iff, decide_eq_true_iff]
    have e : ubObs H S s w1 ⟨v, Finset.mem_univ v⟩ = true ↔ ReachAvoid H S s v := by
      simp [ubObs, hvS]
    rw [e, reach_iff_parent hvS hvs]
    constructor
    · rintro ⟨p, hp, hr⟩
      exact ⟨⟨p, hp⟩, reach_not_mem hs hr, by
        show ubObs H S s w1 ⟨p, Finset.mem_univ p⟩ = true
        simp [ubObs, reach_not_mem hs hr, hr]⟩
    · rintro ⟨⟨p, hp⟩, hpS, hpu⟩
      have hpu' : ubObs H S s w1 ⟨p, Finset.mem_univ p⟩ = true := hpu
      simp [ubObs, hpS] at hpu'
      exact ⟨p, hp, hpu'⟩

lemma ubDo_notS {H : DAG V} {S : Finset V} {z w1 : V} (hzS : z ∉ S) :
    ∀ p, p ∉ S → (ubDo H S z w1 ⟨p, Finset.mem_univ p⟩ = true ↔ ReachAvoid H S z p) := by
  intro p hp
  by_cases hpz : p = z
  · subst hpz
    constructor
    · intro _
      exact Relation.ReflTransGen.refl
    · intro _
      simp [ubDo]
  · simp [ubDo, hpz, hp]

lemma ubDo_pos {H : DAG V} {S : Finset V} {s z w1 : V} (hs : s ∉ S) (hzS : z ∉ S)
    (hw1 : w1 ∈ S) (hrz : RZ H S z w1) (z0 : Assignment (α := fun _ : V => Bool) {z})
    (hz0 : z0 ⟨z, Finset.mem_singleton_self z⟩ = true) :
    ∀ v, kfac (doModel (copyNet H S s w1) {z} z0) Finset.univ (ubDo H S z w1) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  by_cases hvz : v = z
  · have hvz' : v ∈ ({z} : Finset V) := Finset.mem_singleton.mpr hvz
    simp only [doModel, dif_pos hvz']
    rw [PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · subst hvz
      have e : z0 ⟨v, hvz'⟩ = true := hz0
      rw [e]
      simp [ubDo]
  have hvz' : v ∉ ({z} : Finset V) := fun h => hvz (Finset.mem_singleton.mp h)
  simp only [doModel, dif_neg hvz']
  by_cases hvw : v = w1
  · subst hvw
    rw [copy_kernel_w1, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · obtain ⟨p, hp, hr⟩ := hrz
      have hpS : p ∉ S := reach_not_mem hzS hr
      have e1 : ubDo H S z v ⟨v, Finset.mem_univ v⟩ = true := by simp [ubDo, hvz, hw1]
      rw [e1, eq_comm, decide_eq_true_iff]
      exact ⟨⟨p, hp⟩, hpS, (ubDo_notS hzS p hpS).mpr hr⟩
  by_cases hvS : v ∈ S
  · rw [copy_kernel_S hvS hvw, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · simp [ubDo, hvz, hvS, hvw]
  by_cases hvs : v = s
  · subst hvs
    rw [copy_kernel_s hs hvw]
    simp [PMF.uniformOfFintype_apply]
  rw [copy_kernel_other hvS hvs hvw, PMF.pure_apply, if_pos]
  · exact one_ne_zero
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, ubDo_notS hzS v hvS, reach_iff_parent hvS hvz]
    constructor
    · rintro ⟨p, hp, hr⟩
      exact ⟨⟨p, hp⟩, reach_not_mem hzS hr, (ubDo_notS hzS p (reach_not_mem hzS hr)).mpr hr⟩
    · rintro ⟨⟨p, hp⟩, hpS, hpu⟩
      exact ⟨p, hp, (ubDo_notS hzS p hpS).mp hpu⟩

/-- **Regel 3 svikter ved en trek gjennom `z`.** Finnes `s ∉ X ∪ W` med rettede veier
`s ⇝ y` og `s ⇝ z` utenom `X ∪ W` i `G_{X̄}`, når `z` en node `w1 ∈ W`, og når `z`
ikke `y`, så svikter produktformen i regel 3 i en modell på `G`. -/
theorem rule3_complete_copy (G : DAG V) (X W : Finset V) (y z s w1 : V)
    (hy : y ∉ X ∪ W) (hz : z ∉ X ∪ W) (hyz : y ≠ z) (hs : s ∉ X ∪ W)
    (hsy : ReachAvoid (cutIn G X) (X ∪ W) s y) (hsz : ReachAvoid (cutIn G X) (X ∪ W) s z)
    (hw1 : w1 ∈ W) (hzw : RZ (cutIn G X) (X ∪ W) z w1)
    (hzy : ¬ ReachAvoid (cutIn G X) (X ∪ W) z y) :
    ∃ M : G.CausalModel (fun _ => Bool),
      ∃ x : Assignment (α := fun _ : V => Bool) X,
      ∃ t : Assignment (α := fun _ : V => Bool) ({y} ∪ {z} ∪ (X ∪ W)),
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
  have hw1S : w1 ∈ X ∪ W := Finset.mem_union_right X hw1
  have hyw1 : y ≠ w1 := fun e => hy (e ▸ hw1S)
  have hw1X : w1 ∉ X := by
    obtain ⟨p, hp, _⟩ := hzw
    exact (mem_parents_cutIn.mp hp).2
  have hsub : ∀ v, (cutIn G X).parents v ⊆ G.parents v := by
    intro v u hu
    exact (mem_parents_cutIn.mp hu).1
  have hXN : ∀ v (hv : v ∈ X) p, (copyNet (cutIn G X) (X ∪ W) s w1).kernel v p =
      PMF.pure ((fun _ => false : Assignment (α := fun _ : V => Bool) X) ⟨v, hv⟩) :=
    fun v hv p => copy_kernel_S (Finset.mem_union_left W hv) (by rintro rfl; exact hw1X hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hz0 : ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)
      ⟨z, Finset.mem_singleton_self z⟩ = true := by
    simp [copyPt, Assignment.restrict]
  have hrzs : RZ (cutIn G X) (X ∪ W) s w1 := RZ_of_reach hsz hzw
  -- (F1) observasjonelt er (y = 0, w1 = 1) umulig
  have F1 : (copyNet (cutIn G X) (X ∪ W) s w1).marginal ({y} ∪ (X ∪ W))
      ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) = 0 := by
    refine Audit.marginal_eq_zero_of _ _ _ (fun u hu => ?_)
    by_contra hall
    have hall' : ∀ v, kfac (copyNet (cutIn G X) (X ∪ W) s w1) Finset.univ u v ≠ 0 :=
      fun v hv => hall ⟨v, hv⟩
    have huy : u ⟨y, Finset.mem_univ y⟩ = false := by
      have := congrFun hu ⟨y, by simp⟩
      simpa [Assignment.restrict, copyPt, hyz, hyw1] using this
    have huw : u ⟨w1, Finset.mem_univ w1⟩ = true := by
      have := congrFun hu ⟨w1, by simp [hw1]⟩
      simpa [Assignment.restrict, copyPt] using this
    have hk := hall' w1
    rw [DoAudit.kfac_univ, copy_kernel_w1, PMF.pure_apply] at hk
    have hw1v : u ⟨w1, Finset.mem_univ w1⟩ = decide (∃ p : {u // u ∈ (cutIn G X).parents w1},
        p.1 ∉ X ∪ W ∧ (u.restrict (Finset.subset_univ _)) p = true) := by
      by_contra hne
      exact hk (if_neg hne)
    rw [huw] at hw1v
    obtain ⟨⟨p, hp⟩, hpS, hpu⟩ := of_decide_eq_true hw1v.symm
    have hus := ((copy_support _ _ s w1 hs hw1S u hall' p hpS).mp hpu).2
    have huy' := (copy_support _ _ s w1 hs hw1S u hall' y hy).mpr ⟨hsy, hus⟩
    rw [huy] at huy'
    exact Bool.false_ne_true huy'
  -- (F2) observasjonelt er w-punktet mulig
  have F2 : (copyNet (cutIn G X) (X ∪ W) s w1).marginal (X ∪ W)
      ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ (ubObs (cutIn G X) (X ∪ W) s w1) ?_
      (ubObs_pos hs hw1S hrzs)
    funext ⟨v, hv⟩
    have hvz : v ≠ z := fun e => hz (e ▸ hv)
    simp only [Assignment.restrict, ubObs, copyPt, if_pos hv]
    simp [hvz]
  -- (F3) under do(z = 1) er (y = 0, w1 = 1) mulig
  have F3 : (doModel (copyNet (cutIn G X) (X ∪ W) s w1) {z}
      ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal ({y} ∪ (X ∪ W))
      ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ (ubDo (cutIn G X) (X ∪ W) z w1) ?_
      (ubDo_pos hs hz hw1S hzw _ hz0)
    funext ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with h | h
    · have hv' : v = y := Finset.mem_singleton.mp h
      subst hv'
      simp only [Assignment.restrict, ubDo, copyPt, if_neg hyz, if_neg hy]
      simp [hzy, hyz, hyw1]
    · have hvz : v ≠ z := fun e => hz (e ▸ h)
      simp only [Assignment.restrict, ubDo, copyPt, if_neg hvz, if_pos h]
      simp [hvz]
  refine ⟨liftSub hsub (copyNet (cutIn G X) (X ∪ W) s w1), fun _ => false,
    copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W)), ?_⟩
  have hA : ∀ S', (doModel (liftSub hsub (copyNet (cutIn G X) (X ∪ W) s w1)) X
      (fun _ => false)).marginal S' = (copyNet (cutIn G X) (X ∪ W) s w1).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_kfac hsub _ _ hXN) S'
  have hB : ∀ S', (doModel (doModel (liftSub hsub (copyNet (cutIn G X) (X ∪ W) s w1)) X
      (fun _ => false)) {z} ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal S' =
      (doModel (copyNet (cutIn G X) (X ∪ W) s w1) {z}
        ((copyPt z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_do_kfac hsub _ _ _ hXN) S'
  rw [hB, hB, hA, hA, F1, zero_mul]
  exact mul_ne_zero F3 F2

end Rule3Copy

/-! ## Regel 3: kjede-kopi-modellen -/

section Rule3ChainCopy
open DoCalculus

/-- Kjedemodellen, men `w1` kopierer komponent `k` fra foreldrene utenfor `Z`. -/
noncomputable def chainCopy {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (w1 : V) :
    G.CausalModel (fun _ => Fin (C.k + 1) → Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = w1 then PMF.pure (fun _ => orpar G Z v pa (Fin.last C.k))
    else (chainModel C).kernel v pa

lemma cc_kernel_w1 {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (w1 : V)
    (pa : {u // u ∈ G.parents w1} → (Fin (C.k + 1) → Bool)) :
    (chainCopy C w1).kernel w1 pa = PMF.pure (fun _ => orpar G Z w1 pa (Fin.last C.k)) := by
  simp [chainCopy]

lemma cc_kernel_ne {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {w1 v : V}
    (h : v ≠ w1) (pa : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool)) :
    (chainCopy C w1).kernel v pa = (chainModel C).kernel v pa := by
  simp [chainCopy, h]

lemma cc_kfac_ne {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {w1 v : V}
    (h : v ≠ w1)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V)) :
    kfac (chainCopy C w1) Finset.univ u v = kfac (chainModel C) Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ, cc_kernel_ne C h]

/-- `chain_support` med positivitet bare utenfor `Z`. -/
lemma chain_support' {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, v ∉ Z → kfac (chainModel C) Finset.univ u v ≠ 0) :
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
  have hk := hpos v hvZ
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

lemma orpar_eq' {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, v ∉ Z → kfac (chainModel C) Finset.univ u v ≠ 0) {v : V}
    {i : Fin (C.k + 1)} (h : RZ G Z (C.s i) v) :
    orpar G Z v (u.restrict (Finset.subset_univ (G.parents v))) i =
      u ⟨C.s i, Finset.mem_univ _⟩ i := by
  unfold orpar
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨p, hp⟩, hpZ, hpu⟩
    have hpu' : u ⟨p, Finset.mem_univ p⟩ i = true := hpu
    rw [chain_support' C u hpos p hpZ i] at hpu'
    simp only [Bool.and_eq_true] at hpu'
    exact hpu'.1
  · intro hb
    obtain ⟨p, hp, hrp⟩ := h
    have hpZ : p ∉ Z := reach_not_mem (C.hs i) hrp
    refine ⟨⟨p, hp⟩, hpZ, ?_⟩
    show u ⟨p, Finset.mem_univ p⟩ i = true
    rw [chain_support' C u hpos p hpZ i]
    simp [hb, hrp]

lemma chain_z' {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y)
    (hinj : Function.Injective C.z)
    (u : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, v ∉ Z → kfac (chainModel C) Finset.univ u v ≠ 0) (j : Fin C.k)
    (hzk : kfac (chainModel C) Finset.univ u (C.z j) ≠ 0) :
    u ⟨C.z j, Finset.mem_univ _⟩ = fun _ =>
      xor (u ⟨C.s j.castSucc, Finset.mem_univ _⟩ j.castSucc)
        (u ⟨C.s j.succ, Finset.mem_univ _⟩ j.succ) := by
  have hk := hzk
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
  rw [huz, hch, orpar_eq' C u hpos (C.hl j), orpar_eq' C u hpos (C.hr j)]

/-- Kjernen i kjedemodellen ser bare foreldre utenfor `Z`. -/
lemma chain_kernel_congr {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (v : V)
    (pa pa' : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool))
    (h : ∀ p : {u // u ∈ G.parents v}, p.1 ∉ Z → pa p = pa' p) :
    (chainModel C).kernel v pa = (chainModel C).kernel v pa' := by
  have ho : ∀ i, orpar G Z v pa i = orpar G Z v pa' i := by
    intro i
    unfold orpar
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    constructor
    · rintro ⟨p, hp, hpu⟩
      exact ⟨p, hp, by rw [← h p hp]; exact hpu⟩
    · rintro ⟨p, hp, hpu⟩
      exact ⟨p, hp, by rw [h p hp]; exact hpu⟩
  simp only [chainModel, ho]

lemma chain_kfac_congr {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {w1 v : V}
    (hw1 : w1 ∈ Z) (hv : v ≠ w1)
    (u u' : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V))
    (h : ∀ a, a ≠ w1 → u ⟨a, Finset.mem_univ a⟩ = u' ⟨a, Finset.mem_univ a⟩) :
    kfac (chainModel C) Finset.univ u v = kfac (chainModel C) Finset.univ u' v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ, h v hv,
    chain_kernel_congr C v (u.restrict (Finset.subset_univ _)) (u'.restrict (Finset.subset_univ _))
      (fun p hp => h p.1 (fun e => hp (by rw [e]; exact hw1)))]

/-- Observasjonelt vitne: alle bits 1, `w1` sann. -/
noncomputable def u1W {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (w1 : V) :
    Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V) :=
  fun v => if v.1 = w1 then (fun _ => true) else u1C C v

lemma u1W_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {w1 : V}
    (hw1 : w1 ∈ Z) (hr : RZ G Z (C.s (Fin.last C.k)) w1) :
    ∀ v, kfac (chainCopy C w1) Finset.univ (u1W C w1) v ≠ 0 := by
  intro v
  by_cases hv : v = w1
  · subst hv
    rw [DoAudit.kfac_univ, cc_kernel_w1, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · funext i
      have e1 : u1W C v ⟨v, Finset.mem_univ v⟩ i = true := by simp [u1W]
      rw [e1, eq_comm]
      unfold orpar
      rw [decide_eq_true_iff]
      obtain ⟨p, hp, hrp⟩ := hr
      have hpZ : p ∉ Z := reach_not_mem (C.hs _) hrp
      have hpv : p ≠ v := fun e => hpZ (by rw [e]; exact hw1)
      refine ⟨⟨p, hp⟩, hpZ, ?_⟩
      show u1W C v ⟨p, Finset.mem_univ p⟩ (Fin.last C.k) = true
      simp [u1W, u1C, hpv, hpZ, hrp]
  · rw [cc_kfac_ne C hv, chain_kfac_congr C hw1 hv (u1W C w1) (u1C C)
      (fun a ha => by simp [u1W, ha])]
    exact u1_pos C v

/-- Vitne under `do(z = 1)`: alle bits 0, så bare det `z` når, er sant. -/
noncomputable def uDC {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) (z w1 : V) :
    Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) (Finset.univ : Finset V) :=
  fun v _ => if v.1 = z then true else if v.1 ∈ Z then decide (v.1 = w1)
    else decide (ReachAvoid G Z z v.1)

lemma uDC_notZ {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {z w1 : V} :
    ∀ p, p ∉ Z → ∀ i, (uDC C z w1 ⟨p, Finset.mem_univ p⟩ i = true ↔ ReachAvoid G Z z p) := by
  intro p hp i
  by_cases hpz : p = z
  · subst hpz
    constructor
    · intro _
      exact Relation.ReflTransGen.refl
    · intro _
      simp [uDC]
  · simp [uDC, hpz, hp]

lemma uDC_orpar {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {z w1 : V}
    (hzZ : z ∉ Z) (v : V) (pa : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool))
    (hpa : ∀ q, pa q = uDC C z w1 ⟨q.1, Finset.mem_univ _⟩) (i : Fin (C.k + 1)) :
    orpar G Z v pa i = decide (RZ G Z z v) := by
  unfold orpar
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨q, hq, hqu⟩
    rw [hpa q] at hqu
    exact ⟨q.1, q.2, (uDC_notZ C q.1 hq i).mp hqu⟩
  · rintro ⟨q, hq, hr⟩
    have hqZ : q ∉ Z := reach_not_mem hzZ hr
    refine ⟨⟨q, hq⟩, hqZ, ?_⟩
    rw [hpa]
    exact (uDC_notZ C q hqZ i).mpr hr

lemma uDC_kernel_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {z w1 : V}
    (hzZ : z ∉ Z) (hw1 : w1 ∈ Z) (hrz : RZ G Z z w1) (v : V) (hvz : v ≠ z)
    (pa : {u // u ∈ G.parents v} → (Fin (C.k + 1) → Bool))
    (hpa : ∀ q, pa q = uDC C z w1 ⟨q.1, Finset.mem_univ _⟩) :
    (chainCopy C w1).kernel v pa (uDC C z w1 ⟨v, Finset.mem_univ v⟩) ≠ 0 := by
  have ho : ∀ i, orpar G Z v pa i = decide (RZ G Z z v) := uDC_orpar C hzZ v pa hpa
  by_cases hvw : v = w1
  · subst hvw
    rw [cc_kernel_w1, PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · funext i
      rw [ho]
      simp [uDC, hvz, hw1, hrz]
  rw [cc_kernel_ne C hvw]
  simp only [chainModel]
  by_cases hvZ : v ∈ Z
  · rw [if_pos hvZ]
    split_ifs with h
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext i
        rw [ho, ho]
        simp [uDC, hvz, hvZ, hvw]
    · rw [PMF.pure_apply, if_pos]
      · exact one_ne_zero
      · funext i
        simp [uDC, hvz, hvZ, hvw]
  · rw [if_neg hvZ, map_unif_ne_zero]
    refine ⟨uDC C z w1 ⟨v, Finset.mem_univ v⟩, ?_⟩
    funext i
    by_cases hsi : C.s i = v
    · simp [hsi]
    · simp only [hsi, ↓reduceIte]
      rw [ho]
      simp [uDC, hvz, hvZ, RZ, reach_iff_parent hvZ hvz]

lemma uDC_pos {G : DAG V} {Z : Finset V} {x y : V} (C : Chain G Z x y) {z w1 : V}
    (hzZ : z ∉ Z) (hw1 : w1 ∈ Z) (hrz : RZ G Z z w1)
    (z0 : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) {z})
    (hz0 : z0 ⟨z, Finset.mem_singleton_self z⟩ = fun _ => true) :
    ∀ v, kfac (doModel (chainCopy C w1) {z} z0) Finset.univ (uDC C z w1) v ≠ 0 := by
  intro v
  rw [DoAudit.kfac_univ]
  by_cases hvz : v = z
  · have hvz' : v ∈ ({z} : Finset V) := Finset.mem_singleton.mpr hvz
    simp only [doModel, dif_pos hvz']
    rw [PMF.pure_apply, if_pos]
    · exact one_ne_zero
    · subst hvz
      have e : z0 ⟨v, hvz'⟩ = fun _ => true := hz0
      rw [e]
      funext i
      simp [uDC]
  have hvz' : v ∉ ({z} : Finset V) := fun h => hvz (Finset.mem_singleton.mp h)
  simp only [doModel, dif_neg hvz']
  exact uDC_kernel_pos C hzZ hw1 hrz v hvz _ (by intro q; rfl)

/-- Punktet: `z` og `w1` er sanne (alle komponenter), alt annet usant. -/
def ccPt (k : ℕ) (z w1 : V) (A : Finset V) :
    Assignment (α := fun _ : V => Fin (k + 1) → Bool) A :=
  fun v _ => decide (v.1 = z ∨ v.1 = w1)

/-- **Regel 3 svikter ved en kjede inn i `z` og en kopi fra `z` inn i `W`.** Er `C` en
kjede fra `y` til `z` gitt `X ∪ W` i `G_{X̄}` med forskjellige `z_j`, når `z` en node
`w1 ∈ W` som ikke er blant `z_j`, og når `z` ikke `y`, så svikter produktformen i
regel 3 i en modell på `G`. -/
theorem rule3_complete_chaincopy (G : DAG V) (X W : Finset V) (y z w1 : V)
    (C : Chain (cutIn G X) (X ∪ W) y z) (hinj : Function.Injective C.z) (hyz : y ≠ z)
    (hw1 : w1 ∈ W) (hw1C : ∀ j, C.z j ≠ w1) (hzw : RZ (cutIn G X) (X ∪ W) z w1)
    (hzy : ¬ ReachAvoid (cutIn G X) (X ∪ W) z y) :
    ∃ M : G.CausalModel (fun _ => Fin (C.k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) ({y} ∪ {z} ∪ (X ∪ W)),
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
  have hy : y ∉ X ∪ W := reach_not_mem (C.hs 0) C.hx
  have hz : z ∉ X ∪ W := reach_not_mem (C.hs _) C.hy
  have hw1S : w1 ∈ X ∪ W := Finset.mem_union_right X hw1
  have hyw1 : y ≠ w1 := fun e => hy (e ▸ hw1S)
  have hsub : ∀ v, (cutIn G X).parents v ⊆ G.parents v := by
    intro v u hu
    exact (mem_parents_cutIn.mp hu).1
  have hXN : ∀ v (hv : v ∈ X) p, (chainCopy C w1).kernel v p =
      PMF.pure ((fun _ _ => false : Assignment (α := fun _ : V => Fin (C.k + 1) → Bool) X)
        ⟨v, hv⟩) := by
    intro v hv p
    have hvw : v ≠ w1 := by
      rintro rfl
      obtain ⟨q, hq, _⟩ := hzw
      exact (mem_parents_cutIn.mp hq).2 hv
    rw [cc_kernel_ne C hvw]
    exact chain_noparent_false C v (Finset.mem_union_left W hv)
      (fun u he => (show G.edge u v ∧ v ∉ X from he).2 hv) p
  have hzs : ({z} : Finset V) ⊆ {y} ∪ {z} ∪ (X ∪ W) := by
    intro v hv; simp only [Finset.mem_union]; tauto
  have hz0 : ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)
      ⟨z, Finset.mem_singleton_self z⟩ = fun _ => true := by
    funext i
    simp [ccPt, Assignment.restrict]
  have hrw : RZ (cutIn G X) (X ∪ W) (C.s (Fin.last C.k)) w1 := RZ_of_reach C.hy hzw
  -- (F1) observasjonelt er (y = 0, w = punktet) umulig
  have F1 : (chainCopy C w1).marginal ({y} ∪ (X ∪ W))
      ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) = 0 := by
    refine Audit.marginal_eq_zero_of _ _ _ (fun u hu => ?_)
    by_contra hall
    have hall' : ∀ v, kfac (chainCopy C w1) Finset.univ u v ≠ 0 :=
      fun v hv => hall ⟨v, hv⟩
    have hpos : ∀ v, v ∉ X ∪ W → kfac (chainModel C) Finset.univ u v ≠ 0 := by
      intro v hv
      rw [← cc_kfac_ne C (show v ≠ w1 by rintro rfl; exact hv hw1S) u]
      exact hall' v
    have huy : u ⟨y, Finset.mem_univ y⟩ = fun _ => false := by
      funext i
      have := congrFun (congrFun hu ⟨y, Finset.mem_union_left _ (Finset.mem_singleton_self y)⟩) i
      simpa [Assignment.restrict, ccPt, hyz, hyw1] using this
    have huz : ∀ j, u ⟨C.z j, Finset.mem_univ _⟩ = fun _ => false := by
      intro j
      have hzj : C.z j ≠ z := fun e => hz (e ▸ C.hz j)
      funext i
      have := congrFun (congrFun hu ⟨C.z j, Finset.mem_union_right _ (C.hz j)⟩) i
      simpa [Assignment.restrict, ccPt, hzj, hw1C j] using this
    have huw : u ⟨w1, Finset.mem_univ w1⟩ = fun _ => true := by
      funext i
      have := congrFun (congrFun hu ⟨w1, Finset.mem_union_right _ hw1S⟩) i
      simpa [Assignment.restrict, ccPt] using this
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
      ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show X ∪ W ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ (u1W C w1) ?_ (u1W_pos C hw1S hrw)
    funext ⟨v, hv⟩
    have hvz : v ≠ z := fun e => hz (e ▸ hv)
    funext i
    by_cases hvw : v = w1
    · subst hvw
      simp [Assignment.restrict, u1W, ccPt]
    · simp only [Assignment.restrict, u1W, ccPt, if_neg hvw]
      rw [u1C_Z C ⟨v, Finset.mem_univ v⟩ hv]
      simp [hvz, hvw]
  -- (F3) under do(z = 1) er (y = 0, w = punktet) mulig
  have F3 : (doModel (chainCopy C w1) {z}
      ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal ({y} ∪ (X ∪ W))
      ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict
        (show {y} ∪ (X ∪ W) ⊆ {y} ∪ {z} ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ (uDC C z w1) ?_ (uDC_pos C hz hw1S hzw _ hz0)
    funext ⟨v, hv⟩
    funext i
    rcases Finset.mem_union.mp hv with h | h
    · have hv' : v = y := Finset.mem_singleton.mp h
      simp only [Assignment.restrict, uDC, ccPt, hv', if_neg hyz, if_neg hy]
      simp [hzy, hyz, hyw1]
    · have hvz : v ≠ z := fun e => hz (e ▸ h)
      simp only [Assignment.restrict, uDC, ccPt, if_neg hvz, if_pos h]
      simp [hvz]
  refine ⟨liftSub hsub (chainCopy C w1), fun _ _ => false,
    ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W)), ?_⟩
  have hA : ∀ S', (doModel (liftSub hsub (chainCopy C w1)) X (fun _ _ => false)).marginal S' =
      (chainCopy C w1).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_kfac hsub _ _ hXN) S'
  have hB : ∀ S', (doModel (doModel (liftSub hsub (chainCopy C w1)) X (fun _ _ => false))
      {z} ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal S' =
      (doModel (chainCopy C w1) {z}
        ((ccPt C.k z w1 ({y} ∪ {z} ∪ (X ∪ W))).restrict hzs)).marginal S' :=
    fun S' => marginal_eq_of_kfac _ _ (lift_do_do_kfac hsub _ _ _ hXN) S'
  rw [hB, hB, hA, hA, F1, zero_mul]
  exact mul_ne_zero F3 F2

end Rule3ChainCopy

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
