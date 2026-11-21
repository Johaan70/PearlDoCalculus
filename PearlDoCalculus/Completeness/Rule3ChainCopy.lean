import PearlDoCalculus.Completeness.SingleRules

/-!
# Completeness of d-separation: the rule 3 chain copy model

The chain-copy model used to show that rule 3 is complete when the separating
path needs a chain of nodes. It builds on the single-node rules
(`Completeness/SingleRules.lean`). The main result is `rule3_complete_chaincopy`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

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
  · rw [if_neg hvZ, PMF.map_uniformOfFintype_apply_ne_zero_iff]
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

end Completeness
