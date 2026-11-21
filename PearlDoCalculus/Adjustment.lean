import PearlDoCalculus.Rule3Flag

/-!
# Adjustment formulas: back-door and front-door

Pearl's two classical adjustment formulas, derived for a general `CausalModel` from the
rules of the do-calculus (`DoCalculus`, `Rule3`, `Rule3Flag`).

**Back-door.** `Z` satisfies the back-door criterion for `(X, Y)` if (i) no vertex of `Z`
is a descendant of a vertex of `X`, and (ii) `Z` blocks every path between `X` and `Y`
that ends with an arrow into `X` (`BackdoorCriterion`). Pearl shows that, given (i),
(ii) is the same as `Y ⊥ X | Z` in `G_{X̲}` (`cutOut_dsep_of_backdoor`). Then
`P(y | do(x)) = Σ_z P(y, x, z) · P(z) / P(x, z)` (`backdoor_adjustment`,
`backdoor_adjustment_criterion`). The proof works stratum by stratum
(`backdoor_stratum`, without positivity) by rule 2 and rule 3, and divides at the end.

**Front-door.** `Z` satisfies the front-door criterion for `(X, Y)` if (i) every directed
path from `X` to `Y` meets `Z`, (ii) every back-door path from `Z` to `X` is blocked by
`∅`, and (iii) every back-door path from `Y` to `Z` is blocked by `X`
(`FrontdoorCriterion`). Then
`P(y | do(x)) = Σ_z [P(z, x) / P(x)] · Σ_{x'} P(y, z, x') · P(x') / P(z, x')`
(`frontdoor_adjustment`, `frontdoor_adjustment_criterion`). The proof follows Pearl's
derivation in three steps: `P(z, x) = P_x(z) · P(x)` (`frontdoor_step1`, rule 2),
`P_x(y, z) = P_{x,z}(y) · P_x(z)` (`frontdoor_step2`, rule 2) and
`P_{x,z}(y) = P_z(y)` (`frontdoor_step3`, rule 3), then combines them per stratum
(`frontdoor_stratum`) and sums (`frontdoor_product`). The lemmas `fd_h1` to `fd_h4`
translate the path conditions of the criterion into the d-separations that the three
steps need.

**Main results.** `Adjustment.backdoor_adjustment_criterion`,
`Adjustment.frontdoor_adjustment_criterion`, and the forms with d-separation
hypotheses `Adjustment.backdoor_adjustment`, `Adjustment.frontdoor_adjustment`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Adjustment

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- If no vertex of `Z` is a descendant of a vertex of `X`, then `An(Z)` is disjoint
from `X`. -/
lemma disjoint_anc_of_nondesc {X Z : Finset V}
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z) :
    Disjoint (ancestors G Z) X := by
  rw [Finset.disjoint_left]
  intro v hv hvX
  obtain ⟨z, hz, hr⟩ := mem_ancestors_iff.mp hv
  exact hdesc v hvX z hz hr

/-- **Back-door, stratum by stratum.** If `Z` satisfies the back-door criterion for
`(X, Y)`, then `P(y, x, z) · P(z) = P_x(y, z) · P(x, z)`, without positivity. -/
theorem backdoor_stratum {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z)
    (h : SetSound.DSeparatedSet (cutOut G X) Z Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    M.marginal (Y ∪ X ∪ Z) t *
      M.marginal Z (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ Z)
        (t.restrict (show Y ∪ Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal (X ∪ Z) (t.restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  -- Rule 2 with Z := X and W := Z.
  have hr := rule2_core M Y X Z (t.restrict sX) hYX hZX hYZ h t rfl
  -- B2: P_x(z) = P(z), because An(Z) is ancestral and disjoint from X.
  rw [doModel_marginal_of_subset M X (t.restrict sX) (ancestors G Z)
    (DSepSound.A_closed (G := G) Z) (disjoint_anc_of_nondesc hdesc) Z
    (subset_ancestors _) _] at hr
  exact hr

open Rule3Flag in
/-- **The back-door adjustment formula.** If `Z` satisfies the back-door criterion for
`(X, Y)`, and `P(x, z) > 0` for every `z`, then
`P(y | do(x)) = Σ_z P(y, x, z) · P(z) / P(x, z)`. -/
theorem backdoor_adjustment {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z)
    (h : SetSound.DSeparatedSet (cutOut G X) Z Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hpos : ∀ z : Assignment (α := α) Z,
      M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' z : Assignment (α := α) Z,
        M.marginal (Y ∪ X ∪ Z) (setZ Z (Y ∪ X ∪ Z) t z) *
          M.marginal Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show X ∪ Z ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hXZ : Disjoint X Z := hZX.symm
  -- 1. Summing out: P_x(y) = Σ_z P_x(y, z).
  refine (marginal_sum_Z (doModel M X (t.restrict sX))
    (Finset.subset_union_right : Z ⊆ Y ∪ Z) (Finset.subset_union_left : Y ⊆ Y ∪ Z)
    hYZ (Finset.Subset.refl _) (t.restrict sYZ)).symm.trans ?_
  refine tsum_congr (fun z => ?_)
  -- 2. Stratum by stratum, with the intervention value independent of z.
  have hb := backdoor_stratum M X Y Z hYX hZX hYZ hdesc h (setZ Z (Y ∪ X ∪ Z) t z)
  rw [setZ_restrict_disj _ hXZ] at hb
  -- 3. Solve for P_x(y, z) under positivity.
  rw [ENNReal.eq_div_iff (hpos z) (PMF.apply_ne_top _ _)]
  exact (mul_comm _ _).trans hb.symm

/-! ## Front-door, step 1: `P(z, x) = P_x(z) · P(x)` -/

/-- The marginal on `∅` is `1`: all assignments on `∅` are equal. -/
lemma marginal_empty {α : V → Type*} (M : G.CausalModel α)
    (a : Assignment (α := α) (∅ : Finset V)) : M.marginal ∅ a = 1 := by
  have hall : ∀ b c : Assignment (α := α) (∅ : Finset V), b = c :=
    fun b c => funext fun ⟨v, hv⟩ => by simp at hv
  rw [PMF.apply_eq_one_iff]
  ext b
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact hall b a
  · intro hb
    subst hb
    obtain ⟨c, hc⟩ := (M.marginal ∅).support_nonempty
    rwa [hall c b] at hc

/-- **FD1.** If `Z ⊥ X` in `G_{X̲}`, then `P(z, x) = P_x(z) · P(x)`. -/
theorem frontdoor_step1 {α : V → Type*} (M : G.CausalModel α) (X Z : Finset V)
    (hZX : Disjoint Z X) (h : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (t : Assignment (α := α) (Z ∪ X)) :
    M.marginal (Z ∪ X) t =
      (doModel M X (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right))).marginal Z
          (t.restrict (show Z ⊆ Z ∪ X from Finset.subset_union_left)) *
        M.marginal X (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right)) := by
  have s1 : Z ∪ X ∪ ∅ ⊆ Z ∪ X := by simp
  have hr := rule2_core M Z X ∅ (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right))
    hZX (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h (t.restrict s1) rfl
  rw [marginal_empty, mul_one,
    marginal_eq_restrict_of_subset_of_subset M (S := Z ∪ X) (T := Z ∪ X ∪ ∅) (by simp) s1,
    marginal_eq_restrict_of_subset_of_subset (doModel M X _) (S := Z) (T := Z ∪ ∅)
      (by simp) (by simp),
    marginal_eq_restrict_of_subset_of_subset M (S := X) (T := X ∪ ∅) (by simp) (by simp)] at hr
  exact hr

/-! ## Front-door, steps 2 and 3: `P_x(y, z) = P_{x,z}(y) · P_x(z)`, `P_{x,z}(y) = P_z(y)` -/

/-- **FD2.** If `Y ⊥ Z` in `G_{X̄Z̲}`, then `P_x(y, z) = P_{x,z}(y) · P_x(z)`. -/
theorem frontdoor_step2 {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (x : Assignment (α := α) X) (hYZ : Disjoint Y Z)
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (t : Assignment (α := α) (Y ∪ Z)) :
    (doModel M X x).marginal (Y ∪ Z) t =
      (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right))).marginal Y
          (t.restrict (show Y ⊆ Y ∪ Z from Finset.subset_union_left)) *
        (doModel M X x).marginal Z (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right)) := by
  have s1 : Y ∪ Z ∪ ∅ ⊆ Y ∪ Z := by simp
  have hr := rule2_core (doModel M X x) Y Z ∅
    (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right))
    hYZ (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h (t.restrict s1) rfl
  rw [marginal_empty, mul_one,
    marginal_eq_restrict_of_subset_of_subset (doModel M X x) (S := Y ∪ Z) (T := Y ∪ Z ∪ ∅)
      (by simp) s1,
    marginal_eq_restrict_of_subset_of_subset (doModel (doModel M X x) Z _) (S := Y) (T := Y ∪ ∅)
      (by simp) (by simp),
    marginal_eq_restrict_of_subset_of_subset (doModel M X x) (S := Z) (T := Z ∪ ∅)
      (by simp) (by simp)] at hr
  exact hr

/-- With `W = ∅` no vertex is an ancestor of `W`, so `Z(∅)` is the whole set. -/
lemma Z2_empty (H : DAG V) (X : Finset V) : Z2 H X ∅ = X := by
  ext v
  simp [Z2, mem_ancestors_iff]

/-- **FD3.** If `Y ⊥ X` in `G_{Z̄X̄}`, then `P_{x,z}(y) = P_z(y)`: the interventions
commute (both are `do(X ∪ Z)`), and rule 3 removes `do(x)` in the `do(z)` model. -/
theorem frontdoor_step3 {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hXZ : Disjoint X Z)
    (h : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    (doModel (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))) Z
        (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      (doModel M Z (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) := by
  have sXZ : X ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have sY : Y ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sZ : Z ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sT : Y ∪ X ∪ ∅ ⊆ Y ∪ X ∪ Z :=
    Finset.union_subset Finset.subset_union_left (Finset.empty_subset _)
  -- 1–2. Both orders are do(X ∪ Z).
  have e1 := doModel_comp_marginal' M Z X (X ∪ Z) hXZ.symm (Finset.union_comm Z X)
    (t.restrict sXZ) Y (t.restrict sY)
  have e2 := doModel_comp_marginal' M X Z (X ∪ Z) hXZ rfl (t.restrict sXZ) Y (t.restrict sY)
  -- 3. Rule 3 in the do(z) model, with W = ∅.
  have h' : SetSound.DSeparatedSet (cutIn (cutIn G Z) (Z2 (cutIn G Z) X ∅)) ∅ Y X := by
    rw [Z2_empty]
    exact h
  have hr := Rule3Flag.rule3_gen (doModel M Z (t.restrict sZ)) Y X ∅ hYX
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h' (t.restrict sT)
  rw [marginal_empty, marginal_empty, mul_one, mul_one,
    marginal_eq_restrict_of_subset_of_subset (doModel (doModel M Z (t.restrict sZ)) X _)
      (S := Y) (T := Y ∪ ∅)
      (by simp) (by simp),
    marginal_eq_restrict_of_subset_of_subset (doModel M Z (t.restrict sZ)) (S := Y) (T := Y ∪ ∅)
      (by simp) (by simp)] at hr
  exact e1.trans (e2.symm.trans hr)

/-! ## Front-door per stratum, and the sum -/

open Rule3Flag in
/-- **Front-door per stratum.** `P_x(y, z) · P(x) = P_z(y) · P(z, x)`, where `t_z` is
`t` with the `Z`-part replaced by `z`. -/
theorem frontdoor_stratum {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) (z : Assignment (α := α) Z) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ Z)
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ∪ Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have sZX : Z ∪ X ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hXZ : Disjoint X Z := hZX.symm
  -- FD2 at the point t_z|_{Y∪Z}.
  have f2 := frontdoor_step2 M X Y Z (t.restrict sX) hYZ h2
    ((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ)
  -- FD3 at the point t_z, with the intervention value on X rewritten as t|_X.
  have f3 := frontdoor_step3 M X Y Z hYX hXZ h3 (setZ Z (Y ∪ X ∪ Z) t z)
  rw [setZ_restrict_disj _ hXZ] at f3
  have f3' : (doModel (doModel M X (t.restrict sX)) Z
        (((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
          (show Z ⊆ Y ∪ Z from Finset.subset_union_right))).marginal Y
        (((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
          (show Y ⊆ Y ∪ Z from Finset.subset_union_left)) =
      (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) := f3
  -- FD1 at the point t_z|_{Z∪X}, with the intervention value on X rewritten as t|_X.
  have f1 := frontdoor_step1 M X Z hZX h1 ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX)
  have hx : ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX).restrict
      (show X ⊆ Z ∪ X from Finset.subset_union_right) = t.restrict sX :=
    setZ_restrict_disj sX hXZ t z
  rw [hx] at f1
  -- The Z-part is the same through Y ∪ Z and through Z ∪ X.
  have hzz : ((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
      (show Z ⊆ Y ∪ Z from Finset.subset_union_right) =
      ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX).restrict
      (show Z ⊆ Z ∪ X from Finset.subset_union_left) := rfl
  rw [hzz] at f2 f3'
  rw [f2, f1, f3']
  ring

open Rule3Flag in
/-- **Front-door in product form.** `P_x(y) · P(x) = Σ_z P_z(y) · P(z, x)`, without
positivity. -/
theorem frontdoor_product {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
          ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) *
        M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hs := marginal_sum_Z (doModel M X (t.restrict sX))
    (Finset.subset_union_right : Z ⊆ Y ∪ Z) (Finset.subset_union_left : Y ⊆ Y ∪ Z)
    hYZ (Finset.Subset.refl _) (t.restrict sYZ)
  calc _ = (∑' z : Assignment (α := α) Z,
          (doModel M X (t.restrict sX)).marginal (Y ∪ Z) (setZ Z (Y ∪ Z) (t.restrict sYZ) z)) *
          M.marginal X (t.restrict sX) := (congrArg (· * M.marginal X (t.restrict sX)) hs).symm
    _ = ∑' z : Assignment (α := α) Z,
          (doModel M X (t.restrict sX)).marginal (Y ∪ Z) (setZ Z (Y ∪ Z) (t.restrict sYZ) z) *
            M.marginal X (t.restrict sX) := ENNReal.tsum_mul_right.symm
    _ = _ := tsum_congr (fun z => frontdoor_stratum M X Y Z hZX hYX hYZ h1 h2 h3 t z)

/-! ## Front-door: the classical formula -/

open Rule3Flag in
/-- **The front-door adjustment formula.**
`P(y | do(x)) = Σ_z [P(z, x) / P(x)] · Σ_{x′} P(y, z, x′) · P(x′) / P(z, x′)`,
under the d-separation conditions of Pearl's derivation and `P(x) > 0`,
`P(z, x′) > 0`. -/
theorem frontdoor_adjustment {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (hdesc : ∀ z ∈ Z, ∀ x ∈ X, ¬ G.Reaches z x)
    (h4 : SetSound.DSeparatedSet (cutOut G Z) X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hx : M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) ≠ 0)
    (hpos : ∀ (z : Assignment (α := α) Z) (x' : Assignment (α := α) X),
      M.marginal (Z ∪ X)
        ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
          (show Z ∪ X ⊆ Y ∪ Z ∪ X by
            intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) /
        M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hXZ : Disjoint X Z := hZX.symm
  -- 1. Divide the product form by P(x).
  have hp := frontdoor_product M X Y Z hZX hYX hYZ h1 h2 h3 t
  have hdiv := (ENNReal.eq_div_iff hx (PMF.apply_ne_top _ _)).mpr ((mul_comm _ _).trans hp)
  rw [hdiv, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun z => ?_)
  -- 2. Back-door for P_z(y), with X as the adjustment set.
  have hb := backdoor_adjustment M Z Y X hYZ hXZ hYX hdesc h4
    ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
      intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) (hpos z)
  have hb' : (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := hb
  rw [hb', div_eq_mul_inv]
  ring

/-! ## The back-door criterion in terms of paths -/

/-- Is the walk empty? -/
def wIsNil {H : DAG V} : {a b : V} → Walk H a b → Bool
  | _, _, .nil _ => true
  | _, _, .fwd _ _ => false
  | _, _, .bwd _ _ => false

/-- The last step of the walk goes along an arrow *into* the end vertex. -/
def endsInto {H : DAG V} : {a b : V} → Walk H a b → Prop
  | _, _, .nil _ => False
  | _, _, .fwd _ p => wIsNil p = true ∨ endsInto p
  | _, _, .bwd _ p => wIsNil p = false ∧ endsInto p

/-- Moving a walk to a larger graph does not change whether it is empty. -/
lemma wIsNil_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    ∀ {a b : V} (p : Walk H' a b), wIsNil (mapSub hsub p) = wIsNil p := by
  intro a b p
  cases p <;> rfl

/-- A nonempty walk in `G_{X̲}` that ends at `x ∈ X` ends along an arrow into `x`: the
edges out of `x` are removed. -/
lemma endsInto_of_cutOut {X : Finset V} (hsub : ∀ u v, (cutOut G X).edge u v → G.edge u v) :
    ∀ {a b : V} (p : Walk (cutOut G X) a b), b ∈ X → wIsNil p = false →
      endsInto (mapSub hsub p) := by
  intro a b p
  induction p with
  | nil v =>
    intro _ h
    simp [wIsNil] at h
  | fwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    by_cases hp : wIsNil p = true
    · exact Or.inl hp
    · exact Or.inr (ih hb (by simpa using hp))
  | bwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    cases p with
    | nil v => exact absurd hb e.2
    | fwd e' p' => exact ⟨rfl, ih hb rfl⟩
    | bwd e' p' => exact ⟨rfl, ih hb rfl⟩

/-- **Criterion ⇒ d-separation.** If `Z` blocks every path in `G` from `y ∈ Y` to
`x ∈ X` that ends with an arrow into `x`, then `Y ⊥ X | Z` in `G_{X̲}`. -/
theorem cutOut_dsep_of_backdoor {X Y Z : Finset V} (hXY : Disjoint X Y)
    (hcrit : ∀ y ∈ Y, ∀ x ∈ X, ∀ p : Walk G y x, p.IsPath → endsInto p → Walk.Blocked Z p) :
    SetSound.DSeparatedSet (cutOut G X) Z Y X := by
  intro y hy x hx p hp
  have hsub : ∀ u v, (cutOut G X).edge u v → G.edge u v := fun u v h => h.1
  have hne : wIsNil p = false := by
    cases p with
    | nil v => exact absurd hx (Finset.disjoint_right.mp hXY hy)
    | fwd _ _ => rfl
    | bwd _ _ => rfl
  have hpath : (mapSub hsub p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hp
  exact blocked_of_mapSub hsub .start p
    (hcrit y hy x hx (mapSub hsub p) hpath (endsInto_of_cutOut hsub p hx hne))

/-- **Pearl's back-door criterion.** (i) No vertex of `Z` is a descendant of a vertex
of `X`. (ii) `Z` blocks every path between `x ∈ X` and `y ∈ Y` with an arrow into `x`,
here traversed from `y` to `x`. -/
def BackdoorCriterion (G : DAG V) (X Y Z : Finset V) : Prop :=
  (∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z) ∧
  ∀ y ∈ Y, ∀ x ∈ X, ∀ p : Walk G y x, p.IsPath → endsInto p → Walk.Blocked Z p

open Rule3Flag in
/-- **The back-door adjustment formula with Pearl's criterion.** If `Z` satisfies the
back-door criterion for `(X, Y)` and `P(x, z) > 0` for every `z`, then
`P(y | do(x)) = Σ_z P(y, x, z) · P(z) / P(x, z)`. -/
theorem backdoor_adjustment_criterion {α : V → Type*} (M : G.CausalModel α)
    (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hcrit : BackdoorCriterion G X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hpos : ∀ z : Assignment (α := α) Z,
      M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' z : Assignment (α := α) Z,
        M.marginal (Y ∪ X ∪ Z) (setZ Z (Y ∪ X ∪ Z) t z) *
          M.marginal Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show X ∪ Z ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) :=
  backdoor_adjustment M X Y Z hYX hZX hYZ hcrit.1
    (cutOut_dsep_of_backdoor hYX.symm hcrit.2) t hpos

/-! ## The front-door criterion in terms of paths: conditions (ii) and (iii) -/

/-- **Pearl's front-door criterion.** (i) Every directed path from `x ∈ X` to `y ∈ Y`
meets `Z` (there is no directed path on which every vertex after `x` lies outside `Z`).
(ii) Every path between `x ∈ X` and `z ∈ Z` with an arrow into `x` is blocked by `∅`,
here traversed from `z`. (iii) Every path between `z ∈ Z` and `y ∈ Y` with an arrow into
`z` is blocked by `X`, here traversed from `y`. -/
def FrontdoorCriterion (G : DAG V) (X Y Z : Finset V) : Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, ¬ Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) x y) ∧
  (∀ z ∈ Z, ∀ x ∈ X, ∀ p : Walk G z x, p.IsPath → endsInto p → Walk.Blocked ∅ p) ∧
  (∀ y ∈ Y, ∀ z ∈ Z, ∀ p : Walk G y z, p.IsPath → endsInto p → Walk.Blocked X p)

/-- **h1 from (ii):** `Z ⊥ X | ∅` in `G_{X̲}`. -/
lemma fd_h1 {X Y Z : Finset V} (hZX : Disjoint Z X) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut G X) ∅ Z X :=
  cutOut_dsep_of_backdoor hZX.symm hc.2.1

/-- **h4 from (iii):** `Y ⊥ Z | X` in `G_{Z̲}`. -/
lemma fd_h4 {X Y Z : Finset V} (hYZ : Disjoint Y Z) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut G Z) X Y Z :=
  cutOut_dsep_of_backdoor hYZ.symm hc.2.2

/-- From a directed path `a → … → b` with `a ∉ X` and `b ∈ X` there is a walk in
`G_{X̲}` from `a` to some `x′ ∈ X` with only forward steps; it is open given `∅`. -/
lemma exists_open_fwd {X : Finset V} {a b : V} (h : G.Reaches a b) :
    a ∉ X → b ∈ X → ∃ x' ∈ X, ∃ p : Walk (cutOut G X) a x',
      ¬ Walk.blockedAux ∅ .start p ∧ ¬ Walk.blockedAux ∅ .fwd p := by
  have h' : Relation.ReflTransGen G.edge a b := h
  clear h
  induction h' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro ha hb
    exact absurd hb ha
  | @head a c hac _ ih =>
    intro ha hb
    by_cases hc : c ∈ X
    · exact ⟨c, hc, Walk.fwd ⟨hac, ha⟩ (Walk.nil c),
        by simp [Walk.blockedAux], by simp [Walk.blockedAux]⟩
    · obtain ⟨x', hx', p, _, hp2⟩ := ih hc hb
      exact ⟨x', hx', Walk.fwd ⟨hac, ha⟩ p,
        by simp [Walk.blockedAux, hp2], by simp [Walk.blockedAux, hp2]⟩

/-- **hdesc from (ii), through h1:** no vertex of `X` is a descendant of a vertex of
`Z`. -/
lemma fd_hdesc {X Y Z : Finset V} (hZX : Disjoint Z X) (hc : FrontdoorCriterion G X Y Z) :
    ∀ z ∈ Z, ∀ x ∈ X, ¬ G.Reaches z x := by
  intro z hz x hx hr
  obtain ⟨x', hx', p, hp, _⟩ := exists_open_fwd hr (Finset.disjoint_left.mp hZX hz) hx
  exact hp (dsep_of_dsepPath (fd_h1 hZX hc z hz x' hx') p)

/-! ## The front-door criterion: h3 from condition (i) -/

/-- In a graph without edges into `X`: a walk that is open given `∅` in state `.fwd` and
ends in `X` starts in `X`. (A backward step gives a collider, which blocks; a forward
step goes into a vertex that is then not in `X`.) -/
lemma open_fwd_ends {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {c b : V} (q : Walk H c b), ¬ Walk.blockedAux ∅ .fwd q → b ∈ X → c ∈ X := by
  intro c b q
  induction q with
  | nil v =>
    intro _ hb
    exact hb
  | fwd e q ih =>
    intro hq hb
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := fun h => hq (Or.inr h)
    exact absurd (ih hq' hb) (hin _ _ e)
  | bwd e q _ =>
    intro hq _
    exact absurd (Or.inl (fun z hz => by simp at hz)) hq

/-- In a graph without edges into `X`: a walk from `a` to `b ∈ X` that is open given `∅`
in a state other than `.fwd` goes only backwards, and gives a directed path
`b → … → a`. -/
lemma open_nofwd_reach {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {a b : V} (q : Walk H a b) (inc : Incoming), inc ≠ .fwd →
      ¬ Walk.blockedAux ∅ inc q → b ∈ X → Relation.ReflTransGen H.edge b a := by
  intro a b q
  induction q with
  | nil v =>
    intro _ _ _ _
    exact Relation.ReflTransGen.refl
  | fwd e q _ =>
    intro inc hinc hq hb
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    exact absurd (open_fwd_ends hin q hq' hb) (hin _ _ e)
  | bwd e q ih =>
    intro inc hinc hq hb
    have hq' : ¬ Walk.blockedAux ∅ .bwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    exact (ih .bwd (by intro h; cases h) hq' hb).tail e

/-- **h3 from (i):** `Y ⊥ X | ∅` in `G_{Z̄X̄}`. An open walk from `y` to `x` would give
a directed path `x → … → y` that avoids `Z`. -/
lemma fd_h3 {X Y Z : Finset V} (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X := by
  intro y hy x hx p _
  by_contra hp
  have hin : ∀ u v, (cutIn (cutIn G Z) X).edge u v → v ∉ X := fun u v e => e.2
  have hr := open_nofwd_reach hin p .start (by intro h; cases h) hp hx
  exact hc.1 x hx y hy (Relation.ReflTransGen.mono (fun u v e => e.1) hr)

/-! ## The front-door criterion: h2, and the final theorem -/

/-- `endsInto_of_cutOut` for any graph without edges out of `S`. -/
lemma endsInto_of_noOut {H : DAG V} {S : Finset V} (hsub : ∀ u v, H.edge u v → G.edge u v)
    (hout : ∀ u v, H.edge u v → u ∉ S) :
    ∀ {a b : V} (p : Walk H a b), b ∈ S → wIsNil p = false → endsInto (mapSub hsub p) := by
  intro a b p
  induction p with
  | nil v =>
    intro _ h
    simp [wIsNil] at h
  | fwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    by_cases hp : wIsNil p = true
    · exact Or.inl hp
    · exact Or.inr (ih hb (by simpa using hp))
  | bwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    cases p with
    | nil v => exact absurd hb (hout _ _ e)
    | fwd e' p' => exact ⟨rfl, ih hb rfl⟩
    | bwd e' p' => exact ⟨rfl, ih hb rfl⟩

/-- Open given `∅` and with no vertices in `X` ⇒ open given `X` in the larger graph. -/
lemma open_mapSub_of_noX {H' : DAG V} {X : Finset V} (hsub : ∀ u v, H'.edge u v → G.edge u v) :
    ∀ {a b : V} (q : Walk H' a b) (inc : Incoming), (∀ v ∈ q.support, v ∉ X) →
      ¬ Walk.blockedAux ∅ inc q → ¬ Walk.blockedAux X inc (mapSub hsub q) := by
  intro a b q
  induction q with
  | nil v =>
    intro inc _ _ h
    cases inc <;> exact h
  | @fwd a a' _ e q ih =>
    intro inc hX hq
    have ha : a ∉ X := hX a (by simp [Walk.support])
    have hX' : ∀ v ∈ q.support, v ∉ X := fun v hv => hX v (by simp [Walk.support, hv])
    cases inc with
    | start => exact ih .fwd hX' hq
    | fwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .fwd hX' (fun h' => hq (Or.inr h')) h
    | bwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .fwd hX' (fun h' => hq (Or.inr h')) h
  | @bwd a a' _ e q ih =>
    intro inc hX hq
    have ha : a ∉ X := hX a (by simp [Walk.support])
    have hX' : ∀ v ∈ q.support, v ∉ X := fun v hv => hX v (by simp [Walk.support, hv])
    cases inc with
    | start => exact ih .bwd hX' hq
    | fwd => exact absurd (Or.inl (fun z hz => by simp at hz)) hq
    | bwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .bwd hX' (fun h' => hq (Or.inr h')) h

/-- The forward phase: in a graph without edges into `X`, no vertex of a walk that is
open (given `∅`, state `.fwd`) lies in `X`, as long as the start vertex does not. -/
lemma open_fwd_noX {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {c b : V} (q : Walk H c b), c ∉ X → ¬ Walk.blockedAux ∅ .fwd q →
      ∀ v ∈ q.support, v ∉ X := by
  intro c b q
  induction q with
  | nil v =>
    intro hc _ w hw
    simp [Walk.support] at hw
    subst hw
    exact hc
  | @fwd c c' _ e q ih =>
    intro hc hq w hw
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hc
    · exact ih (hin _ _ e) (fun h => hq (Or.inr h)) w hw
  | bwd e q _ =>
    intro _ hq
    exact absurd (Or.inl (fun z hz => by simp at hz)) hq

/-- The backward phase: we carry along a directed path back to `y` that avoids `Z`. If a
vertex lies in `X`, that path contradicts condition (i) of the criterion. -/
lemma open_bwd_noX {H : DAG V} {X Z : Finset V} {y : V}
    (hin : ∀ u v, H.edge u v → v ∉ X) (hout : ∀ u v, H.edge u v → u ∉ Z)
    (hG : ∀ u v, H.edge u v → G.edge u v)
    (hi : ∀ x ∈ X, ¬ Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) x y) :
    ∀ {a b : V} (q : Walk H a b) (inc : Incoming), inc ≠ .fwd →
      ¬ Walk.blockedAux ∅ inc q → a ∉ Z →
      Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) a y →
      ∀ v ∈ q.support, v ∉ X := by
  have key : ∀ a, Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) a y → a ∉ X :=
    fun a hr ha => hi a ha hr
  intro a b q
  induction q with
  | nil v =>
    intro _ _ _ _ hr w hw
    simp [Walk.support] at hw
    subst hw
    exact key _ hr
  | @fwd a a' _ e q _ =>
    intro inc hinc hq _ hr w hw
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact key _ hr
    · exact open_fwd_noX hin q (hin _ _ e) hq' w hw
  | @bwd a a' _ e q ih =>
    intro inc hinc hq ha hr w hw
    have hq' : ¬ Walk.blockedAux ∅ .bwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact key _ hr
    · exact ih .bwd (by intro h; cases h) hq' (hout _ _ e)
        (Relation.ReflTransGen.head ⟨hG _ _ e, ha⟩ hr) w hw

/-- **h2 from (i) and (iii):** `Y ⊥ Z | ∅` in `G_{X̄Z̲}`. -/
lemma fd_h2 {X Y Z : Finset V} (hYZ : Disjoint Y Z) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z := by
  intro y hy z hz p hpath
  by_contra hp
  have hin : ∀ u v, (cutOut (cutIn G X) Z).edge u v → v ∉ X := fun u v e => e.1.2
  have hout : ∀ u v, (cutOut (cutIn G X) Z).edge u v → u ∉ Z := fun u v e => e.2
  have hG : ∀ u v, (cutOut (cutIn G X) Z).edge u v → G.edge u v := fun u v e => e.1.1
  have hyZ : y ∉ Z := Finset.disjoint_left.mp hYZ hy
  -- No vertex of p lies in X (otherwise a directed path X -> Y that avoids Z).
  have hnoX := open_bwd_noX (y := y) hin hout hG (fun x hx hr => hc.1 x hx y hy hr)
    p .start (by intro h; cases h) hp hyZ Relation.ReflTransGen.refl
  -- Then p is an open back-door path from Z to Y in G, given X.
  have hne : wIsNil p = false := by
    cases p with
    | nil v => exact absurd hz hyZ
    | fwd _ _ => rfl
    | bwd _ _ => rfl
  have hpath' : (mapSub hG p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hpath
  exact open_mapSub_of_noX hG p .start hnoX hp
    (hc.2.2 y hy z hz (mapSub hG p) hpath' (endsInto_of_noOut hG hout p hz hne))

open Rule3Flag in
/-- **The front-door adjustment formula with Pearl's criterion.** If `Z` satisfies the
front-door criterion for `(X, Y)`, `P(x) > 0` and `P(z, x′) > 0`, then
`P(y | do(x)) = Σ_z [P(z, x) / P(x)] · Σ_{x′} P(y, z, x′) · P(x′) / P(z, x′)`. -/
theorem frontdoor_adjustment_criterion {α : V → Type*} (M : G.CausalModel α)
    (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (hc : FrontdoorCriterion G X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hx : M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) ≠ 0)
    (hpos : ∀ (z : Assignment (α := α) Z) (x' : Assignment (α := α) X),
      M.marginal (Z ∪ X)
        ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
          (show Z ∪ X ⊆ Y ∪ Z ∪ X by
            intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) /
        M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) :=
  frontdoor_adjustment M X Y Z hZX hYX hYZ (fd_h1 hZX hc) (fd_h2 hYZ hc) (fd_h3 hc)
    (fd_hdesc hZX hc) (fd_h4 hYZ hc) t hx hpos

end Adjustment

#print axioms Adjustment.backdoor_stratum
#print axioms Adjustment.backdoor_adjustment
#print axioms Adjustment.marginal_empty
#print axioms Adjustment.frontdoor_step1
#print axioms Adjustment.frontdoor_step2
#print axioms Adjustment.frontdoor_step3
#print axioms Adjustment.frontdoor_stratum
#print axioms Adjustment.frontdoor_product
#print axioms Adjustment.frontdoor_adjustment
#print axioms Adjustment.cutOut_dsep_of_backdoor
#print axioms Adjustment.backdoor_adjustment_criterion
#print axioms Adjustment.fd_h1
#print axioms Adjustment.fd_h4
#print axioms Adjustment.fd_hdesc
#print axioms Adjustment.fd_h3
#print axioms Adjustment.fd_h2
#print axioms Adjustment.frontdoor_adjustment_criterion
