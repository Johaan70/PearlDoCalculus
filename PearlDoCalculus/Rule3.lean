import PearlDoCalculus.DoCalculus
import PearlDoCalculus.Util.ENNReal

/-!
# Rule 3 of the do-calculus, with positivity

This file proves rule 3 of the do-calculus (removal of an action) in product form, under
a positivity assumption: `Rule3.rule3_pos` (without `X`) and `Rule3.rule3` (Pearl's form
`P_{x,z}(y | x, w) = P_x(y | x, w)` when `Y` and `Z` are d-separated by `X ∪ W` in
`G_{X̄, \overline{Z(W)}}`). The version without positivity is in `Rule3Flag.lean`.

**How.** Split `Z` into `Z₂ = Z(W)`, the nodes of `Z` that are not ancestors of `W`
(`Z2`), and the rest `Z₁` (`Z1`). The proof follows the chain
`P_z = P_{z₂,z₁} → P_{z₂} → P`:

1. *Subgraph monotonicity.* d-separation survives the removal of edges
   (`dsepPath_mono`, `dsepSet_mono`).
2. *Ancestral sets.* An intervention on `Z` does not change the marginal of an
   ancestral set disjoint from `Z` (`doModel_marginal_of_ancestral`,
   `doModel_marginal_of_subset`). Under the hypothesis of rule 3, `Z₂` is disjoint from the
   ancestors of `Y ∪ W` (`not_reaches_Y`, `disjoint_anc_Z2`), so `do(Z₂)` can be dropped.
3. *Composition.* `do(A)` inside `do(B)` is `do(A ∪ B)` for disjoint `A`, `B`
   (`doModel_comp`, `doModel_comp_marginal`).
4. *Step `do(Z₁)`.* In `do(Z₂)`, rule 2 exchanges the action on `Z₁` for an
   observation, and the soundness of d-separation gives the conditional independence;
   the two products are cancelled against each other with `ENNReal.cross_cancel`
   (`Util/ENNReal.lean`), using the positivity of `P(z₁, w)`.
5. *With `X`.* Rule 3 inside `do(X)`, through `G_{X̄}` (`Z2_cutIn_eq`, `Z1_cutIn_eq`).

**Main results.** `Rule3.dsepSet_mono`, `Rule3.doModel_marginal_of_ancestral`,
`Rule3.doModel_comp`, `Rule3.rule3_pos`, `Rule3.rule3`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical

namespace Rule3

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A walk in a graph with fewer edges is a walk in the larger graph. -/
def mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    {a b : V} → Walk H' a b → Walk H a b
  | _, _, .nil v => .nil v
  | _, _, .fwd e p => .fwd (hsub _ _ e) (mapSub hsub p)
  | _, _, .bwd e p => .bwd (hsub _ _ e) (mapSub hsub p)

/-- Moving a walk to a larger graph does not change its support. -/
lemma support_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    ∀ {a b : V} (p : Walk H' a b), (mapSub hsub p).support = p.support := by
  intro a b p
  induction p with
  | nil v => rfl
  | fwd e p ih => simp [mapSub, Walk.support, ih]
  | bwd e p ih => simp [mapSub, Walk.support, ih]

/-- A vertex reached in the smaller graph is reached in the larger one. -/
lemma reaches_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {u v : V} (h : H'.Reaches u v) : H.Reaches u v :=
  Relation.ReflTransGen.mono (fun a b hab => hsub a b hab) h

/-- Blocked in the larger graph gives blocked in the smaller one: non-colliders block in
the same way, and a collider has fewer descendants in the smaller graph. -/
lemma blocked_of_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} : ∀ (inc : Incoming) {a b : V} (p : Walk H' a b),
    Walk.blockedAux Z inc (mapSub hsub p) → Walk.blockedAux Z inc p := by
  intro inc a b p
  induction p generalizing inc with
  | nil v => intro h; simpa [mapSub, Walk.blockedAux] using h
  | fwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
  | bwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
      | exact Or.imp (fun h z hz hr => h z hz (reaches_mono hsub hr)) (ih _)

/-- **Subgraph monotonicity.** Path-based d-separation survives the removal of edges. -/
theorem dsepPath_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} {x y : V} (h : H.DSeparatedPath Z x y) :
    H'.DSeparatedPath Z x y := by
  intro p hp
  have hp' : (mapSub hsub p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hp
  exact blocked_of_mapSub hsub .start p (h (mapSub hsub p) hp')

/-- The set version of subgraph monotonicity. -/
theorem dsepSet_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z X Y : Finset V} (h : SetSound.DSeparatedSet H Z X Y) :
    SetSound.DSeparatedSet H' Z X Y :=
  fun x hx y hy => dsepPath_mono hsub (h x hx y hy)

variable {G : DAG V}

/-- For `v ∉ Z` the kernel factor of the intervened model is the same as in `M`, on
every set `S`. -/
lemma kfac_doModel_of_notMem {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z : Assignment (α := α) Z) (S : Finset V) (a : Assignment (α := α) S)
    {v : V} (hv : v ∉ Z) :
    kfac (doModel M Z z) S a v = kfac M S a v := by
  have hpar : (cutIn G Z).parents v = G.parents v := parents_cutIn_of_notMem hv
  unfold kfac
  by_cases hc : v ∈ S ∧ G.parents v ⊆ S
  · have hc' : v ∈ S ∧ (cutIn G Z).parents v ⊆ S := ⟨hc.1, by rw [hpar]; exact hc.2⟩
    rw [dif_pos hc', dif_pos hc]
    simp only [doModel, dif_neg hv]
    all_goals rfl
  · have hc' : ¬ (v ∈ S ∧ (cutIn G Z).parents v ⊆ S) :=
      fun h => hc ⟨h.1, by rw [← hpar]; exact h.2⟩
    rw [dif_neg hc', dif_neg hc]

/-- **B2.** An intervention on `Z` does not change the marginal of an ancestral set
disjoint from `Z`. -/
theorem doModel_marginal_of_ancestral {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (a : Assignment (α := α) A) :
    (doModel M Z z).marginal A a = M.marginal A a := by
  have hA' : ∀ v ∈ A, ∀ w, (cutIn G Z).edge w v → w ∈ A :=
    fun v hv w hw => hA v hv w hw.1
  rw [marginal_ancestral_apply (doModel M Z z) A hA' a, marginal_ancestral_apply M A hA a]
  exact Finset.prod_congr rfl
    (fun v hv => kfac_doModel_of_notMem M Z z A a (Finset.disjoint_left.mp hAZ hv))

/-- B2 for subsets of an ancestral set disjoint from `Z`. -/
theorem doModel_marginal_of_subset {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (S : Finset V) (hSA : S ⊆ A) (s : Assignment (α := α) S) :
    (doModel M Z z).marginal S s = M.marginal S s := by
  have hPMF : (doModel M Z z).marginal A = M.marginal A :=
    PMF.ext (doModel_marginal_of_ancestral M Z z A hA hAZ)
  rw [← marginal_restrict (doModel M Z z) hSA, ← marginal_restrict M hSA, hPMF]

/-- `Z(W)`: the vertices of `Z` that are not ancestors of any vertex of `W`. -/
noncomputable def Z2 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∉ ancestors G W)

/-- The rest of `Z`: the vertices that are ancestors of `W`. -/
noncomputable def Z1 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∈ ancestors G W)

/-- Blocked from the start gives blocked in state `.bwd`: `.bwd` only adds a condition at
the first vertex. -/
lemma blockedAux_bwd_of_start {H : DAG V} {Z : Finset V} {a b : V} (p : Walk H a b) :
    Walk.blockedAux Z .start p → Walk.blockedAux Z .bwd p := by
  cases p <;> simp [Walk.blockedAux] <;> tauto

/-- If `y` is reached from `z ∈ Z₂` in `G`, there is a last vertex `z′` of `Z₂` that
reaches `y` in `G_{\overline{Z₂}}`. -/
lemma reach_last {Z W : Finset V} {z y : V} (hz : z ∈ Z2 G Z W) (hr : G.Reaches z y) :
    ∃ z' ∈ Z2 G Z W, (cutIn G (Z2 G Z W)).Reaches z' y := by
  induction hr with
  | refl => exact ⟨z, hz, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨z', hz', hr'⟩ := ih
    by_cases hc : c ∈ Z2 G Z W
    · exact ⟨c, hc, Relation.ReflTransGen.refl⟩
    · exact ⟨z', hz', Relation.ReflTransGen.tail hr' ⟨hbc, hc⟩⟩

/-- If `c` is reached from `z′` in `cutIn G Z`, and no vertex that `z′` reaches lies in
`W`, there is a walk from `c` backwards to `z′` that is open in state `.bwd`. -/
lemma open_back {Z W : Finset V} {z' : V} (hnW : ∀ v, G.Reaches z' v → v ∉ W) :
    ∀ {c : V}, (cutIn G Z).Reaches z' c →
      ∃ p : Walk (cutIn G Z) c z', ¬ Walk.blockedAux W .bwd p := by
  intro c hr
  induction hr with
  | refl => exact ⟨Walk.nil _, by simp [Walk.blockedAux]⟩
  | @tail b c hab hbc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Walk.bwd hbc p, ?_⟩
    have hcW : c ∉ W :=
      hnW c (reaches_mono (H := G) (H' := cutIn G Z) (fun u v h => h.1)
        (Relation.ReflTransGen.tail hab hbc))
    simp only [Walk.blockedAux]
    tauto

/-- **B1 for `Y`.** Under the hypothesis of rule 3 no vertex of `Z₂` is an ancestor of
`Y`. -/
theorem not_reaches_Y {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    {z y : V} (hz : z ∈ Z2 G Z W) (hy : y ∈ Y) : ¬ G.Reaches z y := by
  intro hr
  obtain ⟨z', hz', hr'⟩ := reach_last hz hr
  have hz'Z : z' ∈ Z := (Finset.mem_filter.mp hz').1
  have hz'W : z' ∉ ancestors G W := (Finset.mem_filter.mp hz').2
  have hnW : ∀ v, G.Reaches z' v → v ∉ W :=
    fun v hv hvW => hz'W (mem_ancestors_iff.mpr ⟨v, hvW, hv⟩)
  obtain ⟨p, hp⟩ := open_back hnW hr'
  exact hp (blockedAux_bwd_of_start p (dsep_of_dsepPath (h y hy z' hz'Z) p))

/-- **B1.** `Z₂` is disjoint from `An(Y ∪ W)`. -/
theorem disjoint_anc_Z2 {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z) :
    Disjoint (ancestors G (Y ∪ W)) (Z2 G Z W) := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hv
  rcases Finset.mem_union.mp hs with hs | hs
  · exact not_reaches_Y h hvZ hs hr
  · exact (Finset.mem_filter.mp hvZ).2 (mem_ancestors_iff.mpr ⟨s, hs, hr⟩)

/-- **Composition.** `do(A)` inside `do(B)` has the same joint distribution as
`do(A ∪ B)`, for disjoint `A` and `B`. -/
theorem doModel_comp {α : V → Type*} (M : G.CausalModel α) (A B : Finset V)
    (hAB : Disjoint A B) (z : Assignment (α := α) (A ∪ B))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).fullJoint u =
      (doModel M (A ∪ B) z).fullJoint u := by
  rw [doModel_fullJoint, doModel_fullJoint]
  by_cases h : u.restrict (Finset.subset_univ (A ∪ B)) = z
  · have hA : u.restrict (Finset.subset_univ A) =
        z.restrict (Finset.subset_union_left : A ⊆ A ∪ B) := by
      funext ⟨v, hv⟩
      exact congrFun h ⟨v, Finset.mem_union_left _ hv⟩
    rw [if_pos hA, if_pos h, one_mul, one_mul]
    have hsub : (A ∪ B)ᶜ ⊆ Aᶜ := Finset.compl_subset_compl.mpr Finset.subset_union_left
    have hprod : ∏ v ∈ (A ∪ B)ᶜ, kfac (doModel M B
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) Finset.univ u v =
        ∏ v ∈ Aᶜ, kfac (doModel M B
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) Finset.univ u v := by
      refine Finset.prod_subset hsub (fun v hvA hvAB => ?_)
      have hvB : v ∈ B := by
        by_contra hvB
        exact hvAB (Finset.mem_compl.mpr (fun h' =>
          (Finset.mem_union.mp h').elim (Finset.mem_compl.mp hvA) hvB))
      rw [kfac_doModel, dif_pos hvB, if_pos]
      exact congrFun h ⟨v, Finset.mem_union_right _ hvB⟩
    rw [← hprod]
    exact Finset.prod_congr rfl (fun v hv => by
      have hvB : v ∉ B := fun hb => (Finset.mem_compl.mp hv) (Finset.mem_union_right _ hb)
      rw [kfac_doModel, dif_neg hvB])
  · rw [if_neg h, zero_mul]
    by_cases hA : u.restrict (Finset.subset_univ A) =
        z.restrict (Finset.subset_union_left : A ⊆ A ∪ B)
    · rw [if_pos hA, one_mul]
      have hex : ∃ v, ∃ hvB : v ∈ B,
          u ⟨v, Finset.mem_univ v⟩ ≠ z ⟨v, Finset.mem_union_right _ hvB⟩ := by
        by_contra hno
        push_neg at hno
        apply h
        funext ⟨v, hv⟩
        rcases Finset.mem_union.mp hv with hvA | hvB
        · exact congrFun hA ⟨v, hvA⟩
        · exact hno v hvB
      obtain ⟨v, hvB, hne⟩ := hex
      have hvA : v ∈ Aᶜ := Finset.mem_compl.mpr (Finset.disjoint_right.mp hAB hvB)
      refine Finset.prod_eq_zero hvA ?_
      rw [kfac_doModel, dif_pos hvB,
        if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ =
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B)) ⟨v, hvB⟩) from hne)]
    · rw [if_neg hA, zero_mul]

/-- Composition for marginals. -/
theorem doModel_comp_marginal {α : V → Type*} (M : G.CausalModel α) (A B : Finset V)
    (hAB : Disjoint A B) (z : Assignment (α := α) (A ∪ B)) (S : Finset V)
    (s : Assignment (α := α) S) :
    (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).marginal S s =
      (doModel M (A ∪ B) z).marginal S s := by
  have hF : (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).fullJoint =
      (doModel M (A ∪ B) z).fullJoint :=
    PMF.ext (doModel_comp M A B hAB z)
  unfold CausalModel.marginal
  rw [hF]

/-- Composition where the union is given as an equation `A ∪ B = C`. -/
theorem doModel_comp_marginal_of_union_eq {α : V → Type*} (M : G.CausalModel α) (A B C : Finset V)
    (hAB : Disjoint A B) (hC : A ∪ B = C) (z : Assignment (α := α) C) (S : Finset V)
    (s : Assignment (α := α) S) :
    (doModel (doModel M B (z.restrict (show B ⊆ C by rw [← hC]; exact Finset.subset_union_right)))
        A (z.restrict (show A ⊆ C by rw [← hC]; exact Finset.subset_union_left))).marginal S s =
      (doModel M C z).marginal S s := by
  subst hC
  exact doModel_comp_marginal M A B hAB z S s

/-- `Z₁` and `Z₂` together make up `Z`. -/
lemma Z1_union_Z2 (Z W : Finset V) : Z1 G Z W ∪ Z2 G Z W = Z := by
  ext v
  simp only [Z1, Z2, Finset.mem_union, Finset.mem_filter]
  tauto

/-- `Z₁` and `Z₂` are disjoint. -/
lemma disjoint_Z1_Z2 (Z W : Finset V) : Disjoint (Z1 G Z W) (Z2 G Z W) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

/-- **Rule 3 (deletion of actions), with positivity.** If `Y` and `Z` are d-separated by
`W` in `G_{\overline{Z(W)}}`, and `P(z₁, w) > 0` for the part `Z₁` of `Z` that consists
of ancestors of `W`, then `P_z(y | w) = P(y | w)`, in product form. -/
theorem rule3_pos {α : V → Type*} (M : G.CausalModel α) (Y Z W : Finset V)
    (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z) (hYW : Disjoint Y W)
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ W))
    (hpos : M.marginal (Z1 G Z W ∪ W) (t.restrict (show Z1 G Z W ∪ W ⊆ Y ∪ Z ∪ W by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.filter_subset _ _ hv))
      · exact Finset.mem_union_right _ hv)) ≠ 0) :
    (doModel M Z (t.restrict (show Z ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ W)
        (t.restrict (show Y ∪ W ⊆ Y ∪ Z ∪ W by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal W (t.restrict (show W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    M.marginal (Y ∪ W) (t.restrict (show Y ∪ W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel M Z (t.restrict (show Z ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal W
        (t.restrict (show W ⊆ Y ∪ Z ∪ W by
          intro v hv; simp only [Finset.mem_union]; tauto)) := by
  have sZ : Z ⊆ Y ∪ Z ∪ W := by intro v hv; simp only [Finset.mem_union]; tauto
  have hZ1Z : Z1 G Z W ⊆ Z := Finset.filter_subset _ _
  have hZ2Z : Z2 G Z W ⊆ Z := Finset.filter_subset _ _
  have sT1 : Y ∪ Z1 G Z W ∪ W ⊆ Y ∪ Z ∪ W := by
    intro v hv
    simp only [Finset.mem_union] at hv ⊢
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr (hZ1Z hv))
    · exact Or.inr hv
  have hdisj := disjoint_Z1_Z2 (G := G) Z W
  have hYZ1 : Disjoint Y (Z1 G Z W) := Finset.disjoint_of_subset_right hZ1Z hYZ
  have hWZ1 : Disjoint W (Z1 G Z W) := Finset.disjoint_of_subset_right hZ1Z hWZ
  have h1 : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y (Z1 G Z W) :=
    fun y hy z hz => h y hy z (hZ1Z hz)
  have h2 : SetSound.DSeparatedSet (cutOut (cutIn G (Z2 G Z W)) (Z1 G Z W)) W Y (Z1 G Z W) :=
    dsepSet_mono (H := cutIn G (Z2 G Z W))
      (H' := cutOut (cutIn G (Z2 G Z W)) (Z1 G Z W)) (fun u v huv => huv.1) h1
  -- Step A in M₂ = do(Z₂): rule 2 and conditional independence.
  have hr2 := rule2_core (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z))
    Y (Z1 G Z W) W ((t.restrict sZ).restrict hZ1Z) hYZ1 hWZ1 hYW h2 (t.restrict sT1) rfl
  have hci := SetSound.dsep_sound_set (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z))
    Y (Z1 G Z W) W hYW hWZ1.symm h1 (t.restrict sT1)
  -- B2: An(Y ∪ W) is ancestral and disjoint from Z₂.
  have hAcl := ancestors_closed (G := G) (Y ∪ W)
  have hAZ := disjoint_anc_Z2 h
  have hYW_A : Y ∪ W ⊆ ancestors G (Y ∪ W) := subset_ancestors _
  have hW_A : W ⊆ ancestors G (Y ∪ W) :=
    fun v hv => subset_ancestors _ (Finset.mem_union_right _ hv)
  have hZ1W_A : Z1 G Z W ∪ W ⊆ ancestors G (Y ∪ W) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp (Finset.mem_filter.mp hv).2
      exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩
    · exact hW_A hv
  -- Positivity in M₂ is positivity in M.
  have hd0 : (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z)).marginal (Z1 G Z W ∪ W)
      ((t.restrict sT1).restrict (show Z1 G Z W ∪ W ⊆ Y ∪ Z1 G Z W ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    rw [doModel_marginal_of_subset M (Z2 G Z W) _ _ hAcl hAZ _ hZ1W_A]
    exact hpos
  have hA := ENNReal.cross_cancel (PMF.apply_ne_top _ _) hr2.symm hci.symm
    (fun h => absurd h hd0)
  -- Back to do(Z) and M.
  rw [doModel_comp_marginal_of_union_eq M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) (Y ∪ W) _,
    doModel_comp_marginal_of_union_eq M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) W _,
    doModel_marginal_of_subset M (Z2 G Z W) _ _ hAcl hAZ (Y ∪ W) hYW_A _,
    doModel_marginal_of_subset M (Z2 G Z W) _ _ hAcl hAZ W hW_A _] at hA
  exact hA

/-- In `G_{X̄}` no vertex outside `X` reaches a vertex of `X`: the last edge into `x`
is removed. -/
lemma not_reaches_cutIn {X : Finset V} {z x : V} (hz : z ∉ X) (hx : x ∈ X) :
    ¬ (cutIn G X).Reaches z x := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, _, hc⟩
  · exact hz hx
  · exact hc.2 hx

/-- In `G_{X̄}`, `Z(X ∪ W) = Z(W)`: the vertices of `X` have no ancestors outside
`X`. -/
lemma Z2_cutIn_eq (X Z W : Finset V) (hZX : Disjoint Z X) :
    Z2 (cutIn G X) Z (X ∪ W) = Z2 (cutIn G X) Z W := by
  ext z
  simp only [Z2, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, fun hw => hn ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hw
    exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩
  · rintro ⟨hz, hn⟩
    refine ⟨hz, fun hxw => ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hxw
    rcases Finset.mem_union.mp hs with hs | hs
    · exact not_reaches_cutIn (Finset.disjoint_left.mp hZX hz) hs hr
    · exact hn (mem_ancestors_iff.mpr ⟨s, hs, hr⟩)

/-- The same for `Z₁`: the ancestors of `X ∪ W` in `Z` are the ancestors of `W`. -/
lemma Z1_cutIn_eq (X Z W : Finset V) (hZX : Disjoint Z X) :
    Z1 (cutIn G X) Z (X ∪ W) = Z1 (cutIn G X) Z W := by
  ext z
  simp only [Z1, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hxw⟩
    refine ⟨hz, ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hxw
    rcases Finset.mem_union.mp hs with hs | hs
    · exact absurd hr (not_reaches_cutIn (Finset.disjoint_left.mp hZX hz) hs)
    · exact mem_ancestors_iff.mpr ⟨s, hs, hr⟩
  · rintro ⟨hz, hw⟩
    refine ⟨hz, ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hw
    exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩

/-- **Rule 3 (Pearl), with positivity.** If `Y` and `Z` are d-separated by `X ∪ W` in
`G_{X̄, \overline{Z(W)}}`, where `Z(W)` is the set of vertices of `Z` that are not
ancestors of `W` in `G_{X̄}`, then `P_{x,z}(y | x, w) = P_x(y | x, w)`, in product form.

The positivity is `P_x(z₁, x, w) > 0` for the part `Z₁` of `Z` that consists of
ancestors of `X ∪ W` in `G_{X̄}`; by `Z1_cutIn_eq` these are the same vertices as the
ancestors of `W`. -/
theorem rule3 {α : V → Type*} (M : G.CausalModel α) (X Y Z W : Finset V)
    (x : Assignment (α := α) X)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutIn (cutIn G X) (Z2 (cutIn G X) Z W)) (X ∪ W) Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W)))
    (hpos : (doModel M X x).marginal (Z1 (cutIn G X) Z (X ∪ W) ∪ (X ∪ W))
      (t.restrict (show Z1 (cutIn G X) Z (X ∪ W) ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.filter_subset _ _ hv))
        · exact Finset.mem_union_right _ hv)) ≠ 0) :
    (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
        (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel M X x).marginal (X ∪ W) (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
    (doModel M X x).marginal (Y ∪ (X ∪ W))
        (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
        (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hZX : Disjoint Z X :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hXWZ.symm
  rw [← Z2_cutIn_eq X Z W hZX] at h
  exact rule3_pos (doModel M X x) Y Z (X ∪ W) hYZ hXWZ hYXW h t hpos

end Rule3

#print axioms Rule3.dsepPath_mono
#print axioms Rule3.dsepSet_mono
#print axioms Rule3.doModel_marginal_of_ancestral
#print axioms Rule3.doModel_marginal_of_subset
#print axioms Rule3.not_reaches_Y
#print axioms Rule3.disjoint_anc_Z2
#print axioms Rule3.doModel_comp
#print axioms Rule3.doModel_comp_marginal
#print axioms Rule3.rule3_pos
#print axioms Rule3.Z2_cutIn_eq
#print axioms Rule3.Z1_cutIn_eq
#print axioms Rule3.rule3
