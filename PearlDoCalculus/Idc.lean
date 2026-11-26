import PearlDoCalculus.IdAlgo
import PearlDoCalculus.DoCalc.Positivity

/-!
# IDC: identification of conditional effects `P(Y | do(X), Z, W)`

The ID algorithm decides whether an effect `P(Y | do(X))` is identifiable. Shpitser and
Pearl's IDC extends it to conditional effects: if rule 2 of the do-calculus lets `Z` be
moved into the intervention, then `P(Y | do(X), Z, W)` is identifiable whenever the
unconditional effect `P(Y, X, W | do(X ∪ Z))` is. This file proves that soundness
direction.

**Definition.** `IdentifiableCond G α O X Y Z W` says that `P(Y | do(X), Z, W)` is
determined by the positive distribution on the observed set `O`, in cross-multiplied
form, so that no division is needed:
`P₁,ₓ(y, z, w) · P₂,ₓ(z, w) = P₂,ₓ(y, z, w) · P₁,ₓ(z, w)`.

**How the proof goes.**

1. *Two interventions are one.* `do(X = x)` followed by `do(Z = z)` is the single
   intervention `do(X ∪ Z = x.join z)` for disjoint `X` and `Z`
   (`doModel_doModel_fullJoint`, `doModel_doModel_marginal`). Rule 2 in `DoCalculus` is
   stated with two nested interventions, the identification layer with one.
2. *Positivity.* If the observed distribution is positive, every interventional
   marginal is positive on assignments that agree with `x`
   (`DoCalc.doModel_marginal_ne_zero`, in `DoCalc/Positivity`), and zero on those that do
   not (`doModel_marginal_eq_zero`).
3. *Overlapping `X` and `Y`.* `Identifiable` speaks about `Y ∪ X`; `ident_marginal_eq`
   turns it into equality of the interventional marginals on `Y`, even when `Y` and `X`
   overlap.
4. *IDC.* `idc_sound` writes rule 2 in product form for both models, composes the
   interventions by step 1, uses identifiability for the two factors, and cancels the
   positive factor `P_{x,z}(w)` (`ENNReal.cross_cancel`).

**Main results.** `Idc.IdentifiableCond`, `Idc.idc_sound`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Classical

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Two interventions in a row are one**, at the level of the joint distribution. -/
theorem doModel_doModel_fullJoint (M : G.CausalModel α) (X Z : Finset V) (hXZ : Disjoint X Z)
    (x : Assignment (α := α) X) (z : Assignment (α := α) Z)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel (doModel M X x) Z z).fullJoint u =
      (doModel M (X ∪ Z) (x.join z)).fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [kfac_doModel (doModel M X x) Z z u v, kfac_doModel M X x u v,
    kfac_doModel M (X ∪ Z) (x.join z) u v]
  by_cases hz : v ∈ Z
  · have hx : v ∉ X := fun hx => Finset.disjoint_left.mp hXZ hx hz
    have hj : x.join z ⟨v, Finset.mem_union_right X hz⟩ = z ⟨v, hz⟩ := by
      simp only [Assignment.join, dif_neg hx]
    rw [dif_pos hz, dif_pos (Finset.mem_union_right X hz), hj]
  · rw [dif_neg hz]
    by_cases hx : v ∈ X
    · have hj : x.join z ⟨v, Finset.mem_union_left Z hx⟩ = x ⟨v, hx⟩ := by
        simp only [Assignment.join, dif_pos hx]
      rw [dif_pos hx, dif_pos (Finset.mem_union_left Z hx), hj]
    · rw [dif_neg hx, dif_neg (fun h => (Finset.mem_union.mp h).elim hx hz)]

/-- **Two interventions in a row are one**, for the marginals. -/
theorem doModel_doModel_marginal (M : G.CausalModel α) (X Z : Finset V) (hXZ : Disjoint X Z)
    (x : Assignment (α := α) X) (z : Assignment (α := α) Z) (S : Finset V) :
    (doModel (doModel M X x) Z z).marginal S =
      (doModel M (X ∪ Z) (x.join z)).marginal S := by
  unfold CausalModel.marginal
  rw [show (doModel (doModel M X x) Z z).fullJoint =
      (doModel M (X ∪ Z) (x.join z)).fullJoint from
    PMF.ext (fun u => doModel_doModel_fullJoint M X Z hXZ x z u)]

end Idc

/-! ## The IDC theorem

`IdentifiableCond` and its soundness, `idc_sound` (Shpitser and Pearl 2006, IDC). The
proof writes rule 2 in product form for both models, composes the interventions, and
cancels the positive factor `P_{x,z}(w)`. -/

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Under `do(X = x)` an assignment that differs from `x` has probability `0`. -/
theorem doModel_marginal_eq_zero (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) (S : Finset V) (s : Assignment (α := α) S) (v : V)
    (hvS : v ∈ S) (hvX : v ∈ X) (hne : s ⟨v, hvS⟩ ≠ x ⟨v, hvX⟩) :
    (doModel M X x).marginal S s = 0 := by
  by_contra h0
  unfold CausalModel.marginal at h0
  obtain ⟨u, hu, hus⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr h0)
  have hdo : (doModel M X x).fullJoint u ≠ 0 := (PMF.mem_support_iff _ _).mp hu
  rw [doModel_fullJoint] at hdo
  by_cases hux : u.restrict (Finset.subset_univ X) = x
  · apply hne
    rw [← hus, ← hux]
    rfl
  · exact hdo (by rw [if_neg hux, zero_mul])

/-- Identifiability gives equal interventional marginals, also when `Y` and `X`
overlap. -/
theorem ident_marginal_eq {O X Y : Finset V} (hid : Identifiable G α O X Y)
    (M₁ M₂ : G.CausalModel α) (hM : M₁.marginal O = M₂.marginal O)
    (hpos : ∀ a, M₁.marginal O a ≠ 0) (x : Assignment (α := α) X) :
    (doModel M₁ X x).marginal Y = (doModel M₂ X x).marginal Y := by
  ext s
  by_cases hc : ∀ v (hY : v ∈ Y) (hX : v ∈ X), s ⟨v, hY⟩ = x ⟨v, hX⟩
  · have e := hid M₁ M₂ hM hpos (s.join x)
    rw [Assignment.restrict_join_right s x hc, Assignment.restrict_join_left s x] at e
    exact e
  · simp only [not_forall] at hc
    obtain ⟨v, hY, hX, hne⟩ := hc
    rw [doModel_marginal_eq_zero M₁ X x Y s v hY hX hne,
      doModel_marginal_eq_zero M₂ X x Y s v hY hX hne]

/-- **Conditional identifiability** of `P(Y | do(X), Z, W)`. -/
def IdentifiableCond (G : DAG V) (α : V → Type*) (O X Y Z W : Finset V) : Prop :=
  ∀ M₁ M₂ : G.CausalModel α, M₁.marginal O = M₂.marginal O → (∀ a, M₁.marginal O a ≠ 0) →
    ∀ (x : Assignment (α := α) X) (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W))),
      (doModel M₁ X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel M₂ X x).marginal (Z ∪ (X ∪ W)) (t.restrict (show Z ∪ (X ∪ W) ⊆
            Y ∪ Z ∪ (X ∪ W) by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M₂ X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel M₁ X x).marginal (Z ∪ (X ∪ W)) (t.restrict (show Z ∪ (X ∪ W) ⊆
            Y ∪ Z ∪ (X ∪ W) by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto))

/-- **IDC is sound.** If `Y` and `Z` are d-separated by `X ∪ W` in `G_{X̄Z̲}` (rule 2)
and `P(Y, X, W | do(X ∪ Z))` is identifiable, then `P(Y | do(X), Z, W)` is
identifiable. -/
theorem idc_sound [∀ v, Nonempty (α v)] (U X Y Z W : Finset V)
    (hXO : X ⊆ Uᶜ) (hZO : Z ⊆ Uᶜ) (hWO : W ⊆ Uᶜ)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z)
    (hid : Identifiable G α Uᶜ (X ∪ Z) (Y ∪ (X ∪ W))) :
    IdentifiableCond G α Uᶜ X Y Z W := by
  intro M₁ M₂ hM hpos x t
  have hXZ : Disjoint X Z := Finset.disjoint_left.mpr (fun v hx hz =>
    Finset.disjoint_left.mp hXWZ (Finset.mem_union_left W hx) hz)
  have pX : X ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_left W hv)
  have pZ : Z ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right Y hv)
  have pXW : X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv => Finset.mem_union_right _ hv
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, t.restrict pZ = z₀ := ⟨_, rfl⟩
  by_cases hxt : ∀ v (hv : v ∈ X), t ⟨v, pX hv⟩ = x ⟨v, hv⟩
  · have r₁ := rule2 M₁ X Y Z W x z₀ hYZ hXWZ hYXW h t hz₀
    have r₂ := rule2 M₂ X Y Z W x z₀ hYZ hXWZ hYXW h t hz₀
    rw [doModel_doModel_marginal M₁ X Z hXZ x z₀, doModel_doModel_marginal M₁ X Z hXZ x z₀]
      at r₁
    rw [doModel_doModel_marginal M₂ X Z hXZ x z₀, doModel_doModel_marginal M₂ X Z hXZ x z₀]
      at r₂
    have hc := ident_marginal_eq hid M₁ M₂ hM hpos (x.join z₀)
    have hd : (doModel M₁ (X ∪ Z) (x.join z₀)).marginal (X ∪ W) =
        (doModel M₂ (X ∪ Z) (x.join z₀)).marginal (X ∪ W) := by
      rw [← marginal_restrict (doModel M₁ (X ∪ Z) (x.join z₀))
          (show X ∪ W ⊆ Y ∪ (X ∪ W) from Finset.subset_union_right),
        ← marginal_restrict (doModel M₂ (X ∪ Z) (x.join z₀))
          (show X ∪ W ⊆ Y ∪ (X ∪ W) from Finset.subset_union_right), hc]
    rw [hc, hd] at r₁
    have hpos₂ : ∀ a, M₂.marginal Uᶜ a ≠ 0 := fun a => by rw [← hM]; exact hpos a
    have hd0 : (doModel M₂ (X ∪ Z) (x.join z₀)).marginal (X ∪ W) (t.restrict pXW) ≠ 0 :=
      DoCalc.doModel_marginal_ne_zero M₂ U (X ∪ Z) (Finset.union_subset hXO hZO) hpos₂ _ (X ∪ W)
        (Finset.union_subset hXO hWO) _ (fun v hvS hvX => by
          by_cases hx : v ∈ X
          · simp only [Assignment.restrict, Assignment.join, dif_pos hx]
            exact hxt v hx
          · exfalso
            have hw : v ∈ W := (Finset.mem_union.mp hvS).resolve_left hx
            have hz : v ∈ Z := (Finset.mem_union.mp hvX).resolve_left hx
            exact Finset.disjoint_left.mp hXWZ (Finset.mem_union_right X hw) hz)
    exact ENNReal.cross_cancel (PMF.apply_ne_top _ _) r₁ r₂ (fun h => absurd h hd0)
  · simp only [not_forall] at hxt
    obtain ⟨v, hv, hne⟩ := hxt
    rw [doModel_marginal_eq_zero M₁ X x _ t v (pX hv) hv hne,
      doModel_marginal_eq_zero M₂ X x _ t v (pX hv) hv hne]
    simp

end Idc
