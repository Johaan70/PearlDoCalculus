import PearlDoCalculus.WalkPath
import PearlDoCalculus.Lauritzen

/-!
# Soundness of d-separation for sets

For sets `X`, `Y`, `Z` with `X` and `Y` disjoint from `Z`: if every pair `x ∈ X`,
`y ∈ Y` is d-separated by `Z` in the classical (path-based) sense, then `X` and `Y` are
conditionally independent given `Z` (`dsep_sound_set`). The set version is what the
do-calculus and the adjustment formulas need, since their conditioning and outcome sets
are sets of vertices.

Pairwise conditional independence does *not* give independence of sets in general, so
the proof cannot be assembled from `dsep_sound_path` for each pair. Instead it repeats
the route of `DSepSound` for sets: separation in the moral graph of `An(X ∪ Y ∪ Z)`
(Lauritzen's theorem for sets, `moral_sep_of_dsep_set`, with the Bayes-ball argument of
`Lauritzen.lean` started from every `x ∈ X`), a partition `L ∪ Z ∪ R` of the vertices
with `X ⊆ L`, `Y ⊆ R` and no moral edge between `L` and `R`
(`separator_partition_set`), the product form of the joint distribution of the model
restricted to the ancestral set, and the transfer of conditional independence back to the
whole model.

**Main results.** `SetSound.moral_sep_of_dsep_set`, `SetSound.separator_partition_set`,
`SetSound.dsep_sound_set`.
-/

open PearlDoCalculus DAG DAG.CausalModel BayesBall

namespace SetSound

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- d-separation of sets: every pair is d-separated in the classical (path-based)
sense. -/
def DSeparatedSet (G : DAG V) (Z X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.DSeparatedPath Z x y

/-- Separation of sets in an undirected graph: every pair is separated by `Z`. -/
def SeparatesSet (H : SimpleGraph V) (Z X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, Separates H Z x y

/-- The Bayes ball reaches `v` from some `x ∈ X`. -/
def ReachS (G : DAG V) (Z X : Finset V) (v : V) : Prop :=
  ∃ x ∈ X, Lauritzen.Reach G Z x v

/-- Every vertex of `An(X ∪ Y ∪ Z)` is an ancestor of a vertex of `X`, of `Y` or of
`Z`. -/
lemma mem_A_cases_set {Z X Y : Finset V} {c : V}
    (hc : c ∈ ancestors G (X ∪ Y ∪ Z)) :
    (∃ x ∈ X, G.Reaches c x) ∨ (∃ y ∈ Y, G.Reaches c y) ∨ ∃ z ∈ Z, G.Reaches c z := by
  rw [mem_ancestors_iff] at hc
  obtain ⟨s, hs, hr⟩ := hc
  simp only [Finset.mem_union] at hs
  rcases hs with (hs | hs) | hs
  · exact Or.inl ⟨s, hs, hr⟩
  · exact Or.inr (Or.inl ⟨s, hs, hr⟩)
  · exact Or.inr (Or.inr ⟨s, hs, hr⟩)

/-- The heart, for sets. The ball came to the collider `c` from above, and `w → c`. Then
the ball reaches `w` (from some `x ∈ X`) or some `y ∈ Y`. If `c` is an ancestor of
another `x′ ∈ X`, the ball goes up from `x′`. -/
lemma up_at_collider_set {Z X Y : Finset V} {x₀ c w : V}
    (hXZ : ∀ x ∈ X, x ∉ Z) (hx₀ : x₀ ∈ X)
    (hc : c ∈ ancestors G (X ∪ Y ∪ Z)) (hcw : G.edge w c)
    (hreach : bbReachable G Z ⟨x₀, .fromChild⟩ ⟨c, .fromParent⟩) :
    ReachS G Z X w ∨ ∃ y ∈ Y, ReachS G Z X y := by
  classical
  by_cases hanc : ∃ z ∈ Z, G.Reaches c z
  · left
    exact ⟨x₀, hx₀, .fromChild, Relation.ReflTransGen.tail hreach
      (Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hanc⟩, hcw, rfl⟩)⟩
  · have hnz : Lauritzen.NotZAnc G Z c := hanc
    rcases mem_A_cases_set hc with ⟨x', hx', hcx⟩ | ⟨y', hy', hcy⟩ | hz
    · left
      exact ⟨x', hx', .fromChild, Relation.ReflTransGen.tail
        (Lauritzen.up_path (hXZ x' hx') hcx hnz)
        ⟨Lauritzen.notMem_of_notZAnc hnz, Or.inl ⟨hcw, rfl⟩⟩⟩
    · right
      obtain ⟨d', hd'⟩ := Lauritzen.down_path hcy hnz hreach
      exact ⟨y', hy', x₀, hx₀, d', hd'⟩
    · exact absurd hz hanc

/-- One step along a moral edge in `An(X ∪ Y ∪ Z)`, for sets. -/
lemma moral_step_set {Z X Y : Finset V} {v w : V}
    (hXZ : ∀ x ∈ X, x ∉ Z) (hv : v ∉ Z) (_hw : w ∉ Z)
    (hadj : (moralGraph G (ancestors G (X ∪ Y ∪ Z))).Adj v w)
    (hreach : ReachS G Z X v) : ReachS G Z X w ∨ ∃ y ∈ Y, ReachS G Z X y := by
  obtain ⟨x₀, hx₀, d, hd⟩ := hreach
  simp only [moralGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨_, hr⟩ := hadj
  rcases hr with ⟨_, _, hedge | ⟨c, hcA, hvc, hwc⟩⟩ | ⟨_, hvA, hedge | ⟨c, hcA, hwc, hvc⟩⟩
  · left
    exact ⟨x₀, hx₀, .fromParent, Lauritzen.step_down hd hv hedge⟩
  · exact up_at_collider_set hXZ hx₀ hcA hwc (Lauritzen.step_down hd hv hvc)
  · cases d with
    | fromChild =>
      left
      exact ⟨x₀, hx₀, .fromChild, Relation.ReflTransGen.tail hd ⟨hv, Or.inl ⟨hedge, rfl⟩⟩⟩
    | fromParent => exact up_at_collider_set hXZ hx₀ hvA hedge hd
  · exact up_at_collider_set hXZ hx₀ hcA hwc (Lauritzen.step_down hd hv hvc)

/-- Induction along a walk in an undirected graph, generic in a predicate `P` and a
goal `Q`. -/
lemma walk_reach_set {Z : Finset V} {H : SimpleGraph V} {P : V → Prop} {Q : Prop}
    (hstep : ∀ {v w : V}, v ∉ Z → w ∉ Z → H.Adj v w → P v → P w ∨ Q) :
    ∀ {v t : V} (p : H.Walk v t), (∀ u ∈ p.support, u ∉ Z) → P v → P t ∨ Q := by
  intro v t p
  induction p with
  | nil => intro _ h; exact Or.inl h
  | cons hadj rest ih =>
    intro hsupp hreach
    rcases hstep (hsupp _ (by simp)) (hsupp _ (by simp)) hadj hreach with h | h
    · exact ih (fun u hu => hsupp u (by simp [hu])) h
    · exact Or.inr h

/-- **Lauritzen's theorem for sets.** If `X` and `Y` are d-separated by `Z`, then `Z`
separates them in the moral graph of `An(X ∪ Y ∪ Z)`. -/
theorem moral_sep_of_dsep_set (X Y : Finset V) {Z : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (h : DSeparatedSet G Z X Y) :
    SeparatesSet (moralGraph G (ancestors G (X ∪ Y ∪ Z))) Z X Y := by
  intro x hx y hy p
  by_contra hno
  have hsupp : ∀ u ∈ p.support, u ∉ Z := fun u hu huZ => hno ⟨u, huZ, hu⟩
  have hXZ' : ∀ x ∈ X, x ∉ Z := fun x hx => Finset.disjoint_left.mp hXZ hx
  have hstart : ReachS G Z X x := ⟨x, hx, .fromChild, Relation.ReflTransGen.refl⟩
  rcases walk_reach_set (P := ReachS G Z X) (Q := ∃ y' ∈ Y, ReachS G Z X y')
      (fun hv hw hadj hr => moral_step_set hXZ' hv hw hadj hr) p hsupp hstart with hend | hQ
  · obtain ⟨x', hx', d, hd⟩ := hend
    exact not_bbReachable_of_dSeparated G Z x' y (dsep_of_dsepPath (h x' hx' y hy))
      .fromChild d hd
  · obtain ⟨y', hy', x', hx', d, hd⟩ := hQ
    exact not_bbReachable_of_dSeparated G Z x' y' (dsep_of_dsepPath (h x' hx' y' hy'))
      .fromChild d hd

/-- **Separator partition for sets.** If `Z` separates `X` from `Y` in `H`, the vertices
split as `L ∪ Z ∪ R` with `X ⊆ L`, `Y ⊆ R` and no edge between `L` and `R`; `L` is the
set of vertices reachable from `X` while avoiding `Z`. -/
lemma separator_partition_set {H : SimpleGraph V} {Z X Y : Finset V}
    (h : SeparatesSet H Z X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ∃ L R : Finset V,
      X ⊆ L ∧ Y ⊆ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  classical
  set L := Finset.univ.filter (fun v => v ∉ Z ∧ ∃ x ∈ X, ReachAvoiding H Z x v) with hLdef
  set R := Finset.univ \ (L ∪ Z) with hRdef
  have hmemL : ∀ v, v ∈ L ↔ v ∉ Z ∧ ∃ x ∈ X, ReachAvoiding H Z x v := by
    intro v
    simp [hLdef]
  have hmemR : ∀ v, v ∈ R ↔ v ∉ L ∧ v ∉ Z := by
    intro v
    simp [hRdef, not_or]
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxZ : x ∉ Z := Finset.disjoint_left.mp hXZ hx
    exact (hmemL x).mpr ⟨hxZ, x, hx, reachAvoiding_refl hxZ⟩
  · intro y hy
    have hyZ : y ∉ Z := Finset.disjoint_left.mp hYZ hy
    refine (hmemR y).mpr ⟨?_, hyZ⟩
    intro hyL
    obtain ⟨_, x, hx, p, hp⟩ := (hmemL y).mp hyL
    obtain ⟨z, hzZ, hzmem⟩ := h x hx y hy p
    exact hp z hzZ hzmem
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    exact ((hmemR v).mp hvR).1 hvL
  · rw [Finset.disjoint_left]
    intro v hvL hvZ
    exact ((hmemL v).mp hvL).1 hvZ
  · rw [Finset.disjoint_left]
    intro v hvR hvZ
    exact ((hmemR v).mp hvR).2 hvZ
  · ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvL : v ∈ L
    · exact Or.inl (Or.inl hvL)
    · by_cases hvZ : v ∈ Z
      · exact Or.inl (Or.inr hvZ)
      · exact Or.inr ((hmemR v).mpr ⟨hvL, hvZ⟩)
  · intro u huL w hwR hadj
    obtain ⟨_, x, hx, pu, hpu⟩ := (hmemL u).mp huL
    obtain ⟨hwL, hwZ⟩ := (hmemR w).mp hwR
    apply hwL
    refine (hmemL w).mpr ⟨hwZ, x, hx, pu.concat hadj, ?_⟩
    intro z hz hzmem
    rw [SimpleGraph.Walk.support_concat] at hzmem
    simp only [List.mem_append, List.mem_singleton] at hzmem
    rcases hzmem with h1 | h1
    · exact hpu z hz h1
    · subst h1
      exact hwZ hz

/-- **Soundness for sets.** Classical d-separation of sets gives conditional
independence. -/
theorem dsep_sound_set {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (h : DSeparatedSet G Z X Y) :
    M.CondIndep X Y Z := by
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have hA := DSepSound.A_closed (G := G) (X ∪ Y ∪ Z)
  have hsep := moral_sep_of_dsep_set X Y hXZ hYZ h
  obtain ⟨L, R, hXL, hYR, hLR, hLZ, hRZ, hcover, hnoadj⟩ :=
    separator_partition_set hsep hXZ hYZ
  obtain ⟨F, Gf, hF⟩ := joint_splits (CausalModel.restrictTo M _ hA) L Z R
    hLZ hLR hRZ.symm hcover (DSepSound.family_side hA hcover hnoadj)
  obtain ⟨F', Gf', hF'⟩ := DSepSound.product_form_mono (CausalModel.restrictTo M _ hA)
    hLR hLZ hRZ hXL hYR F Gf hF
  have hci' : CondIndep (CausalModel.restrictTo M _ hA) X Y Z :=
    DSepSound.condIndep_of_form _ X Y Z (Disjoint.mono hXL hYR hLR) hXZ hYZ F' Gf' hF'
  exact DSepSound.condIndep_transfer M _ hA hci' (subset_ancestors _)

end SetSound

#print axioms SetSound.separator_partition_set
#print axioms SetSound.moral_sep_of_dsep_set
#print axioms SetSound.dsep_sound_set
