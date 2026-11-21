import PearlDoCalculus.AdjAudit

/-!
# Completeness of d-separation: the collider-free case

The first step towards the completeness of d-separation (`Completeness.dsep_iff`). If
there is a vertex `s ∉ Z` with directed paths to `x` and to `y` on which every vertex
after `s` lies outside `Z` (`ReachesAvoiding`), and `x ≠ y`, then some model violates
`CondIndep M {x} {y} Z` (`trek_not_condIndep`).

**The model** (`trekModel`). Vertices in `Z` are constant `false`, `s` is a uniform bit,
and every other vertex is the OR of its parents. In every assignment of positive
probability a vertex is `true` exactly when it is reachable from `s` outside `Z` and `s`
is `true` (`support_iff`). So `x = y = s` while `Z` is constant, and `x` and `y` are
dependent given `Z`.

**From walks to treks.** A walk from `x` to `y` that is open given `Z` and has no
colliders (it is open given `∅`) contains such a source `s` (`trek_of_open`, which walks
backwards until the first forward step, and `fwd_phase` for the forward part). This gives
`not_condIndep_of_colliderFree`, and with `Z = ∅` the completeness of marginal
independence (`dsep_complete_marginal`).

**Why it is needed.** Soundness (`DSepSound.dsep_sound`) says that d-separation implies
conditional independence in every model; completeness is the converse. This file settles
the case without colliders. `Completeness/Chain.lean` generalises the model to walks with
colliders (several sources joined by XOR vertices in `Z`) and reuses `ReachesAvoiding`,
`reach_notMem` and `reach_iff_parent`. The theorems of this file are not used later, since
`Completeness.dsep_complete` covers them (a trek is a chain without colliders,
`Chain.trek`), but the trek case shows the argument in its simplest form.

**Main results.** `trek_not_condIndep`, `not_condIndep_of_colliderFree`,
`dsep_complete_marginal`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The trek model and its support -/

/-- A directed path from `s` to `v` on which every vertex after `s` lies outside `Z`. -/
def ReachesAvoiding (G : DAG V) (Z : Finset V) (s v : V) : Prop :=
  Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) s v

/-- The trek model: vertices in `Z` are constant `false`, `s` is a uniform bit, and every
other vertex is the OR of its parents. -/
noncomputable def trekModel (G : DAG V) (Z : Finset V) (s : V) :
    G.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v ∈ Z then PMF.pure false
    else if v = s then PMF.uniformOfFintype Bool
    else PMF.pure (decide (∃ p : {u // u ∈ G.parents v}, pa p = true))

/-- If the path starts outside `Z`, it ends outside `Z`. -/
lemma reach_notMem {G : DAG V} {Z : Finset V} {s v : V} (hs : s ∉ Z)
    (h : ReachesAvoiding G Z s v) : v ∉ Z := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, _, hpv⟩
  · exact hs
  · exact hpv.2

/-- One step back: a vertex `v ∉ Z` other than `s` is reached from `s` outside `Z` exactly
when one of its parents is. -/
lemma reach_iff_parent {G : DAG V} {Z : Finset V} {s v : V} (hvZ : v ∉ Z) (hvs : v ≠ s) :
    ReachesAvoiding G Z s v ↔ ∃ p ∈ G.parents v, ReachesAvoiding G Z s p := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, hp, hpv⟩
    · exact absurd rfl hvs
    · exact ⟨p, by simp [DAG.parents, hpv.1], hp⟩
  · rintro ⟨p, hp, hr⟩
    exact hr.tail ⟨by simpa [DAG.parents] using hp, hvZ⟩

/-- **The support of `trekModel`.** In an assignment where every kernel factor is nonzero,
`v` is `true` exactly when `v` is reached from `s` outside `Z` and `s` is `true`. The proof
is by induction on the rank of `v`. -/
lemma support_iff (G : DAG V) (Z : Finset V) (s : V) (hs : s ∉ Z)
    (u : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (hpos : ∀ v, kfac (trekModel G Z s) Finset.univ u v ≠ 0) :
    ∀ v, (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachesAvoiding G Z s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) := by
  suffices H : ∀ n, ∀ v, G.rank v = n → (u ⟨v, Finset.mem_univ v⟩ = true ↔
      ReachesAvoiding G Z s v ∧ u ⟨s, Finset.mem_univ s⟩ = true) from fun v => H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hr
  have hk := hpos v
  rw [kfac_univ] at hk
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
      exact absurd hvZ (reach_notMem hs h)
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

/-- The witness assignment: `v` is `true` exactly when `v` is reached from `s` outside `Z`
and `b` is `true`. -/
noncomputable def uB (G : DAG V) (Z : Finset V) (s : V) (b : Bool) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v => decide (ReachesAvoiding G Z s v.1) && b

/-- Every kernel factor of `trekModel` is nonzero at the witness `uB`, for both values of
`b`. -/
lemma uB_pos {G : DAG V} {Z : Finset V} {s : V} (hs : s ∉ Z) (b : Bool) :
    ∀ v, kfac (trekModel G Z s) Finset.univ (uB G Z s b) v ≠ 0 := by
  intro v
  rw [kfac_univ]
  simp only [trekModel]
  by_cases hvZ : v ∈ Z
  · have hnr : ¬ ReachesAvoiding G Z s v := fun h => reach_notMem hs h hvZ
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

/-- The assignment `x = false`, `y = true`, `Z = false` (only `y` is `true`). -/
def wXY (y : V) (S : Finset V) : Assignment (α := fun _ : V => Bool) S :=
  fun v => decide (v.1 = y)

/-- **A trek gives dependence.** If `x` and `y` are reached from `s ∉ Z` along directed
paths outside `Z`, and `x ≠ y`, then `CondIndep {x} {y} Z` fails in `trekModel`: the point
`x = false, y = true, Z = false` has probability zero (`x` and `y` both equal `s`), while
`x = false, Z = false` and `y = true, Z = false` both have positive probability. -/
theorem trek_not_condIndep (G : DAG V) (Z : Finset V) (s x y : V) (hs : s ∉ Z)
    (hx : ReachesAvoiding G Z s x) (hy : ReachesAvoiding G Z s y) (hxy : x ≠ y) :
    ¬ CondIndep (trekModel G Z s) {x} {y} Z := by
  intro hci
  have hyZ : y ∉ Z := reach_notMem hs hy
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
      have hnr : ¬ ReachesAvoiding G Z s v := fun hr => reach_notMem hs hr h
      simp [uB, wXY, Assignment.restrict, hvy, hnr]

/-! ## From an open collider-free walk to a trek -/

/-- The forward phase: a walk that is open for both `Z` and `∅` in the state `.fwd`
consists only of forward steps, and every vertex on it lies outside `Z`. -/
lemma fwd_phase {G : DAG V} {Z : Finset V} :
    ∀ {c b : V} (q : Walk G c b), b ∉ Z →
      ¬ Walk.blockedAux Z .fwd q → ¬ Walk.blockedAux ∅ .fwd q →
      c ∉ Z ∧ ReachesAvoiding G Z c b := by
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

/-- The backward phase: we carry along a directed path back to `x` that avoids `Z`. At
the first forward step the current vertex is the source of a trek. -/
lemma trek_of_open {G : DAG V} {Z : Finset V} {x : V} :
    ∀ {a b : V} (q : Walk G a b) (inc : Incoming), inc ≠ .fwd →
      (inc = .start → a ∉ Z) → b ∉ Z →
      ¬ Walk.blockedAux Z inc q → ¬ Walk.blockedAux ∅ inc q →
      ReachesAvoiding G Z a x →
      ∃ s, s ∉ Z ∧ ReachesAvoiding G Z s x ∧ ReachesAvoiding G Z s b := by
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

/-- **An open collider-free walk gives dependence.** If there is a walk from `x` to `y` that
is open given `Z` and has no colliders (it is open given `∅`), then some model violates
`CondIndep {x} {y} Z`. -/
theorem not_condIndep_of_colliderFree (G : DAG V) (Z : Finset V) (x y : V)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hxy : x ≠ y) (p : Walk G x y)
    (hZ : ¬ Walk.Blocked Z p) (h0 : ¬ Walk.Blocked ∅ p) :
    ∃ M : G.CausalModel (fun _ => Bool), ¬ CondIndep M {x} {y} Z := by
  obtain ⟨s, hs, hsx, hsy⟩ := trek_of_open p .start (by intro h; cases h)
    (fun _ => hxZ) hyZ hZ h0 Relation.ReflTransGen.refl
  exact ⟨trekModel G Z s, trek_not_condIndep G Z s x y hs hsx hsy hxy⟩

/-- **Completeness for marginal independence.** If `x` and `y` are not d-separated given
`∅`, some model makes them dependent. -/
theorem dsep_complete_marginal (G : DAG V) (x y : V) (hxy : x ≠ y)
    (h : ¬ G.DSeparated ∅ x y) :
    ∃ M : G.CausalModel (fun _ => Bool), ¬ CondIndep M {x} {y} ∅ := by
  obtain ⟨p, hp⟩ : ∃ p : Walk G x y, ¬ Walk.Blocked ∅ p := by
    by_contra hc
    exact h (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩)
  exact not_condIndep_of_colliderFree G ∅ x y (by simp) (by simp) hxy p hp hp

end Completeness
