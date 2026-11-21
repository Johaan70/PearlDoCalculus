import PearlDoCalculus.Completeness.SingleRules

/-!
# Completeness of d-separation: the rule 3 copy model

The copy model used to show that rule 3 is complete when `X` and `Y` are
separated by a single node pair. It builds on the single-node rules
(`Completeness/SingleRules.lean`). The main result is `rule3_complete_copy`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

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
  rw [kfac_univ, copy_kernel_other hvS hvs hvw, PMF.pure_apply] at hk
  have huv : u ⟨v, Finset.mem_univ v⟩ = decide (∃ p : {u // u ∈ H.parents v},
      p.1 ∉ S ∧ (u.restrict (Finset.subset_univ _)) p = true) := by
    by_contra h
    exact hk (if_neg h)
  rw [huv, decide_eq_true_iff, reach_iff_parent hvS hvs]
  constructor
  · rintro ⟨⟨p, hp⟩, hpS, hpu⟩
    have hlt : H.rank p < n := by
      have := H.rank_strict_mono p v (DAG.mem_parents.mp hp)
      omega
    obtain ⟨hrp, hs'⟩ := (ih _ hlt p rfl hpS).mp hpu
    exact ⟨⟨p, hp, hrp⟩, hs'⟩
  · rintro ⟨⟨p, hp, hrp⟩, hs'⟩
    have hpS : p ∉ S := reach_not_mem hs hrp
    have hlt : H.rank p < n := by
      have := H.rank_strict_mono p v (DAG.mem_parents.mp hp)
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
  rw [kfac_univ]
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
  rw [kfac_univ]
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
    rw [kfac_univ, copy_kernel_w1, PMF.pure_apply] at hk
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

end Completeness
