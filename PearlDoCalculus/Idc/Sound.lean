/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Idc.Maximal
import PearlDoCalculus.DoCalc.Soundness

/-!
# Soundness of the IDC check

If the IDC check (`Idc/Check`) says yes for `P(Y | do(X), W)`, the conditional effect is
identifiable, in the cross-multiplied sense of `IdentifiableCond` (`docs/design-idc.md`,
step 3; `idcCheck_sound`). No hypothesis on the latent vertices is needed.

**How the proof goes.** Write `M` for the moved set and `W' = W ∖ M`.

1. *The moves are one derivation* (`derives_of_reachable`). Each move of a vertex `w` is
   one step `Derives.rule2` with intervention `X ∪ M`, moved set `{w}` and rest
   `W' ∖ {w}`; its side condition is exactly `Movable`. Following the moves that reach
   the moved set (`reachable_movedSet`) gives `P(Y | W, do X) ⊢ P(Y | W', do(X ∪ M))`.
2. *A conditional is a ratio* (`derives_ratio`). The chain rule, the cancellation
   `(a · b) / b = a` and marginalization give
   `P(Y | W', do X') ⊢ P(Y ∪ W' | do X') / Σ_Y P(Y ∪ W' | do X')`.
   Together: `derives_frame`.
3. *The ratio is identified.* The ID check says yes for `P(Y ∪ W' | do(X ∪ M))`, so it is
   identifiable (`IdAlgo.idCheck_sound`), and two models with the same positive observed
   marginal give the ratio the same value. By soundness of derivations
   (`DoCalc.derives_sound`) they give `P(Y | W, do X)` the same value at every assignment.
4. *From values to `IdentifiableCond`* (`identifiableCond_of_eval`). The value of
   `prob Y W X` at an assignment `σ` is `P_x(y, w) / P_x(w)` with `x = σ_X`.
   `IdentifiableCond` instead compares the marginals on `Y ∪ (X ∪ W)` and on `X ∪ W`, at
   an assignment `t` and an intervention value `x` that may disagree on `X`. If they
   disagree, both marginals on `Y ∪ (X ∪ W)` are `0` (`doModel_marginal_eq_zero`). If they
   agree, `t` extends to a total assignment `σ` with `σ_X = x`; adding the intervened
   variables `X` does not change a marginal (`DoCalc.doProb_eq_of_union_eq`), and the
   denominators are positive and finite (`DoCalc.doProb_ne_zero`), so the equation of
   ratios cross-multiplies.

Step 4 is used again for derivations in `Idc/Derivation`.

**Main results.** `derives_of_reachable`, `derives_moved`, `derives_ratio`,
`derives_frame`, `identifiableCond_of_eval`, `idcCheck_sound`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification DoCalc Classical

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-! ## The moves as one derivation -/

section Moves

variable {U X Y W : Finset V} (hXO : X ⊆ Uᶜ) (hWO : W ⊆ Uᶜ) (hYX : Disjoint Y X)
  (hYW : Disjoint Y W) (hXW : Disjoint X W)
include hXO hWO hYX hYW hXW

/-- **The moves are one derivation.** If single moves reach `(M, W')` from `(∅, W)`, then
`P(Y | W, do X) ⊢ P(Y | W', do(X ∪ M))`: one step of rule 2 per move. -/
theorem derives_of_reachable {s : Finset V × Finset V} (h : Reachable G X Y W s) :
    Derives G U (.prob Y W X) (.prob Y s.2 (X ∪ s.1)) := by
  induction h with
  | refl =>
    show Derives G U (.prob Y W X) (.prob Y W (X ∪ ∅))
    rw [Finset.union_empty]
    exact Derives.refl _
  | @tail s t hs hst ih =>
    obtain ⟨w, hw, rfl⟩ := hst
    obtain ⟨hMW, hrest⟩ := Reachable.eq_sdiff hs
    have hwW' : w ∈ s.2 := hw.1
    rw [hrest] at hwW'
    have hwW : w ∈ W := (Finset.mem_sdiff.mp hwW').1
    have hwM : w ∉ s.1 := (Finset.mem_sdiff.mp hwW').2
    have hwX : w ∉ X := fun h => Finset.disjoint_left.mp hXW h hwW
    have hs2W : s.2 ⊆ W := hrest ▸ Finset.sdiff_subset
    have hYZ : Disjoint Y {w} :=
      Finset.disjoint_singleton_right.mpr fun h => Finset.disjoint_left.mp hYW h hwW
    have hXWZ : Disjoint ((X ∪ s.1) ∪ (s.2 \ {w})) {w} := by
      refine Finset.disjoint_singleton_right.mpr fun h => ?_
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at h
      tauto
    have hYXW : Disjoint Y ((X ∪ s.1) ∪ (s.2 \ {w})) := by
      refine Finset.disjoint_left.mpr fun v hvY hv => ?_
      simp only [Finset.mem_union, Finset.mem_sdiff] at hv
      rcases hv with (hvX | hvM) | ⟨hvW, -⟩
      · exact Finset.disjoint_left.mp hYX hvY hvX
      · exact Finset.disjoint_left.mp hYW hvY (hMW hvM)
      · exact Finset.disjoint_left.mp hYW hvY (hs2W hvW)
    have hO : {w} ∪ (s.2 \ {w}) ∪ (X ∪ s.1) ⊆ Uᶜ :=
      Finset.union_subset (Finset.union_subset (Finset.singleton_subset_iff.mpr (hWO hwW))
        (Finset.sdiff_subset.trans (hs2W.trans hWO))) (Finset.union_subset hXO (hMW.trans hWO))
    have r := Derives.rule2 (G := G) (U := U) (X ∪ s.1) Y {w} (s.2 \ {w}) hYZ hXWZ hYXW hO hw.2
    rw [Finset.union_sdiff_of_subset (Finset.singleton_subset_iff.mpr hw.1),
      show X ∪ s.1 ∪ {w} = X ∪ insert w s.1 by
        rw [Finset.union_insert, Finset.union_comm _ {w}, ← Finset.insert_eq],
      ← Finset.erase_eq] at r
    exact Derives.trans ih r

/-- **The moves of the check as one derivation**:
`P(Y | W, do X) ⊢ P(Y | W ∖ M, do(X ∪ M))` for the moved set `M`. -/
theorem derives_moved :
    Derives G U (.prob Y W X) (.prob Y (W \ movedSet G X Y W) (X ∪ movedSet G X Y W)) :=
  derives_of_reachable hXO hWO hYX hYW hXW reachable_movedSet

end Moves

/-- **A conditional is a ratio.** `P(Y | W', do X') ⊢ P(Y ∪ W' | do X') / Σ_Y P(Y ∪ W' | do X')`,
by the chain rule, the cancellation `(a · b) / b = a` and marginalization. -/
theorem derives_ratio {U Y W' X' : Finset V} (hO : W' ∪ X' ⊆ Uᶜ)
    (hY : Disjoint Y (W' ∪ X')) :
    Derives G U (.prob Y W' X')
      (.div (.query (Y ∪ W') X') (.sum Y (.query (Y ∪ W') X'))) := by
  have hb : (Expr.prob W' ∅ X').Positive U := by
    simpa only [Expr.Positive, Finset.union_empty] using hO
  have hc : Derives G U (.prob (Y ∪ W') ∅ X') (.mul (.prob Y W' X') (.prob W' ∅ X')) := by
    have h := Derives.chain (G := G) (U := U) Y W' ∅ X'
    rwa [Finset.union_empty] at h
  have hm : Derives G U (.prob W' ∅ X') (.sum Y (.prob (Y ∪ W') ∅ X')) := by
    have h := Derives.marg (G := G) (U := U) W' ∅ X' Y (by rwa [Finset.union_empty])
    rwa [Finset.union_comm W' Y] at h
  exact Derives.trans (Derives.symm (Derives.mul_div_cancel _ _ hb))
    (Derives.div (Derives.symm hc) hm)

/-- **The frame of IDC.** `P(Y | W, do X)` derives the ratio of the effect left by the
check: `P(Y ∪ W' | do(X ∪ M)) / Σ_Y P(Y ∪ W' | do(X ∪ M))`, with `M` the moved set and
`W' = W ∖ M`. No hypothesis on the latents is needed. -/
theorem derives_frame {U X Y W : Finset V} (hXO : X ⊆ Uᶜ) (hWO : W ⊆ Uᶜ)
    (hYX : Disjoint Y X) (hYW : Disjoint Y W) (hXW : Disjoint X W) :
    Derives G U (.prob Y W X)
      (.div (.query (Y ∪ (W \ movedSet G X Y W)) (X ∪ movedSet G X Y W))
        (.sum Y (.query (Y ∪ (W \ movedSet G X Y W)) (X ∪ movedSet G X Y W)))) := by
  have hMW := movedSet_subset G X Y W
  refine Derives.trans (derives_moved hXO hWO hYX hYW hXW) (derives_ratio ?_ ?_)
  · exact Finset.union_subset (Finset.sdiff_subset.trans hWO)
      (Finset.union_subset hXO (hMW.trans hWO))
  · refine Finset.disjoint_left.mpr fun v hvY hv => ?_
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv
    rcases hv with ⟨hvW, -⟩ | hvX | hvM
    · exact Finset.disjoint_left.mp hYW hvY hvW
    · exact Finset.disjoint_left.mp hYX hvY hvX
    · exact Finset.disjoint_left.mp hYW hvY (hMW hvM)

/-! ## From values to conditional identifiability -/

/-- **Equal values give conditional identifiability.** If any two models with the same
positive observed marginal give `prob Y W X` the same value at every assignment, then
`P(Y | do(X), W)` is identifiable in the sense of `IdentifiableCond`. -/
theorem identifiableCond_of_eval {α : V → Type*} {U X Y W : Finset V} (hXO : X ⊆ Uᶜ)
    (hWO : W ⊆ Uᶜ)
    (h : ∀ M₁ M₂ : G.CausalModel α, M₁.marginal Uᶜ = M₂.marginal Uᶜ →
      (∀ a, M₁.marginal Uᶜ a ≠ 0) → eval M₁ (.prob Y W X) = eval M₂ (.prob Y W X)) :
    IdentifiableCond G α Uᶜ X Y ∅ W := by
  intro M₁ M₂ hM hpos x t
  haveI : ∀ v, Nonempty (α v) := nonempty_of_model M₁
  have hpos₂ : ∀ a, M₂.marginal Uᶜ a ≠ 0 := fun a => hM ▸ hpos a
  have pX : X ⊆ Y ∪ ∅ ∪ (X ∪ W) := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_left W hv)
  by_cases hxt : ∀ v (hv : v ∈ X), t ⟨v, pX hv⟩ = x ⟨v, hv⟩
  · -- `t` extends to a total assignment `σ` with `σ_X = x`
    obtain ⟨σ, hσ⟩ : ∃ σ : ∀ v, α v, ∀ v (hv : v ∈ Y ∪ ∅ ∪ (X ∪ W)), σ v = t ⟨v, hv⟩ :=
      ⟨fun v => if hv : v ∈ Y ∪ ∅ ∪ (X ∪ W) then t ⟨v, hv⟩ else Classical.arbitrary _,
        fun v hv => dif_pos hv⟩
    have ht : valuesOn σ (Y ∪ ∅ ∪ (X ∪ W)) = t := funext fun ⟨v, hv⟩ => hσ v hv
    have hx : valuesOn σ X = x := funext fun ⟨v, hv⟩ => (hσ v (pX hv)).trans (hxt v hv)
    rw [← ht, ← hx, restrict_valuesOn]
    change doProb M₁ X _ σ * doProb M₂ X _ σ = doProb M₂ X _ σ * doProb M₁ X _ σ
    -- the variables of `X` can be dropped from both marginals
    have hn : ∀ M : G.CausalModel α, doProb M X (Y ∪ ∅ ∪ (X ∪ W)) σ = doProb M X (Y ∪ W) σ :=
      fun M => doProb_eq_of_union_eq M (Finset.Subset.refl X)
        (Finset.ext fun v => by simp only [Finset.mem_union, Finset.notMem_empty]; tauto) σ
    have hd : ∀ M : G.CausalModel α, doProb M X (∅ ∪ (X ∪ W)) σ = doProb M X W σ :=
      fun M => doProb_eq_of_union_eq M (Finset.Subset.refl X)
        (Finset.ext fun v => by simp only [Finset.mem_union, Finset.notMem_empty]; tauto) σ
    rw [hn, hn, hd, hd]
    have e := congrFun (h M₁ M₂ hM hpos) σ
    rw [eval_prob, eval_prob, ENNReal.div_eq_div_iff (doProb_ne_zero M₂ U hpos₂ hXO hWO σ)
      (doProb_ne_top M₂ X W σ) (doProb_ne_zero M₁ U hpos hXO hWO σ) (doProb_ne_top M₁ X W σ)]
      at e
    rw [mul_comm, e, mul_comm]
  · -- `t` disagrees with `x` on `X`: both sides are `0`
    simp only [not_forall] at hxt
    obtain ⟨v, hv, hne⟩ := hxt
    rw [doModel_marginal_eq_zero M₁ X x _ t v (pX hv) hv hne,
      doModel_marginal_eq_zero M₂ X x _ t v (pX hv) hv hne, zero_mul, zero_mul]

/-! ## Soundness -/

/-- **Soundness of the IDC check.** If `idcCheck G U X Y W = true`, with `X`, `Y`, `W`
observed and pairwise disjoint, then `P(Y | do(X), W)` is identifiable for every family of
value types. -/
theorem idcCheck_sound (G : DAG V) (U X Y W : Finset V) (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ)
    (hWO : W ⊆ Uᶜ) (hYX : Disjoint Y X) (hYW : Disjoint Y W) (hXW : Disjoint X W)
    (h : idcCheck G U X Y W = true) (α : V → Type*) :
    IdentifiableCond G α Uᶜ X Y ∅ W := by
  refine identifiableCond_of_eval hXO hWO fun M₁ M₂ hM hpos => ?_
  haveI : ∀ v, Nonempty (α v) := nonempty_of_model M₁
  have hpos₂ : ∀ a, M₂.marginal Uᶜ a ≠ 0 := fun a => hM ▸ hpos a
  have hMW := movedSet_subset G X Y W
  -- the effect left by the check is identifiable
  have hid : Identifiable G α Uᶜ (X ∪ movedSet G X Y W) (Y ∪ (W \ movedSet G X Y W)) :=
    IdAlgo.idCheck_sound G U _ _ (Finset.union_subset hXO (hMW.trans hWO))
      (Finset.union_subset hY (Finset.sdiff_subset.trans hWO)) h
  have hq : eval M₁ (.query (Y ∪ (W \ movedSet G X Y W)) (X ∪ movedSet G X Y W)) =
      eval M₂ (.query (Y ∪ (W \ movedSet G X Y W)) (X ∪ movedSet G X Y W)) := by
    funext σ
    rw [eval_query, eval_query]
    unfold doProb
    rw [ident_marginal_eq hid M₁ M₂ hM hpos]
  -- so is its ratio, and by soundness of derivations `P(Y | W, do X)`
  have hd := derives_frame (G := G) (U := U) hXO hWO hYX hYW hXW
  rw [derives_sound hd M₁ hpos, derives_sound hd M₂ hpos₂]
  funext σ
  simp only [eval_div, eval_sum, hq]

end Idc
