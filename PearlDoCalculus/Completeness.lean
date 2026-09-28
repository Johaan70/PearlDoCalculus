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

end Completeness

#print axioms Completeness.support_iff
#print axioms Completeness.trek_not_condIndep
