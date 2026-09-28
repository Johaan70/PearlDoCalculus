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

end Completeness

#print axioms Completeness.support_iff
#print axioms Completeness.trek_not_condIndep
#print axioms Completeness.not_condIndep_of_colliderFree
#print axioms Completeness.dsep_complete_marginal
#print axioms Completeness.chain_support
