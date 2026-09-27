import PearlDoCalculus.Rule3Flag

/-!
# Justeringsformler: back-door og front-door

Utledet for en generell `CausalModel` fra do-kalkulusens regler.

**Back-door-kriteriet** for `(X, Y)` med `Z`: (i) ingen node i `Z` er etterkommer
av en node i `X`; (ii) `Y ⊥ X | Z` i `G_{X̲}`. Pearl viser at (ii), gitt (i), er det
samme som at `Z` blokkerer hver sti mellom `X` og `Y` med en pil inn i `X`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Adjustment

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- Er ingen node i `Z` etterkommer av en node i `X`, er `An(Z)` disjunkt fra `X`. -/
lemma disjoint_anc_of_nondesc {X Z : Finset V}
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z) :
    Disjoint (ancestors G Z) X := by
  rw [Finset.disjoint_left]
  intro v hv hvX
  obtain ⟨z, hz, hr⟩ := mem_ancestors_iff.mp hv
  exact hdesc v hvX z hz hr

/-- **Back-door, stratum for stratum.** Oppfyller `Z` back-door-kriteriet for
`(X, Y)`, så er `P(y, x, z) · P(z) = P_x(y, z) · P(x, z)`, uten positivitet. -/
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
  -- Regel 2 med Z := X og W := Z.
  have hr := rule2_core M Y X Z (t.restrict sX) hYX hZX hYZ h t rfl
  -- B2: P_x(z) = P(z), fordi An(Z) er ancestral og disjunkt fra X.
  rw [doModel_marginal_of_sub M X (t.restrict sX) (ancestors G Z)
    (DSepSound.A_closed (G := G) Z) (disjoint_anc_of_nondesc hdesc) Z
    (subset_ancestors _) _] at hr
  exact hr

open Rule3Flag in
/-- **Back-door-justeringsformelen.** Oppfyller `Z` back-door-kriteriet for
`(X, Y)`, og er `P(x, z) > 0` for alle `z`, så er
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
  -- 1. Marginalisering: P_x(y) = Σ_z P_x(y, z).
  refine (marginal_sum_Z (doModel M X (t.restrict sX))
    (Finset.subset_union_right : Z ⊆ Y ∪ Z) (Finset.subset_union_left : Y ⊆ Y ∪ Z)
    hYZ (Finset.Subset.refl _) (t.restrict sYZ)).symm.trans ?_
  refine tsum_congr (fun z => ?_)
  -- 2. Stratum for stratum, med intervensjonsverdien uavhengig av z.
  have hb := backdoor_stratum M X Y Z hYX hZX hYZ hdesc h (setZ Z (Y ∪ X ∪ Z) t z)
  rw [setZ_restrict_disj _ hXZ] at hb
  -- 3. Løs ut P_x(y, z) under positivitet.
  rw [ENNReal.eq_div_iff (hpos z) (PMF.apply_ne_top _ _)]
  exact (mul_comm _ _).trans hb.symm

end Adjustment

#print axioms Adjustment.backdoor_stratum
#print axioms Adjustment.backdoor_adjustment
