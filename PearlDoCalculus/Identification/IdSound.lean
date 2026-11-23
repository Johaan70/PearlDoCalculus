import PearlDoCalculus.Identification.Identify

/-!
# ID soundness for sets

This file proves that the ID algorithm is sound for sets: if the blocks of the
c-components of `G_{X̄}` can be reached from `V` by Tian's steps (`IdentifyDerives`), then
`P(Y | do(X))` is identifiable.

* `id_sound_blocks` and `id_sound` (ID lines 4, 6 and 7 put together), with `Q_lat` (a
  purely latent block has factor 1) and `ccomp_cutIn_X` (in `G_{X̄}` the c-component of
  `x ∈ X` is `{x}`).
* ID line 2, restriction to the ancestors of `Y`: `id_sound_anc`, `id_sound_anc_blocks`
  and `ccomp_ind_X`.

Why it is needed: `id_sound_anc` is the soundness theorem behind `IdAlgo.idCheck_sound`:
`IdAlgo` checks the hypotheses of `id_sound_anc` and derives the `IdentifyDerives` steps, so a
`true` answer of `idCheck` means identifiable. `ccomp_ind_X` is also used by
`Hedge/FromID` (a failing check gives a hedge).

How the proofs go: under `do(X = x)` the model lives on `G_{X̄}`, whose c-components are
the singletons of `X`, purely latent blocks, and blocks disjoint from `X`. The
intervention distribution is the product of the block factors (`marginal_prod`); the
first two kinds of blocks contribute the same factor in every model, and the factor of a
block disjoint from `X` is its factor in the original model (`Q_do_gen`), which is
determined by `P(O)` when it is reached by Tian's steps (`identifyDerives_ident`); the
three cases are `Q_do_eq`. With line 2, the marginal on an ancestral set `S ⊇ Y` is
`Q_X[S]` (`Q_marg`), which factors over the blocks closed inside `S` (`Q_prod_rel`, in
`Identification/CFactorSets`); summing fibre by fibre (`tsum_updX`, `fiber_eq`) passes
from equal sums over `O ∖ S` to equal marginals on `Y`.

Main results: `Identification.CFactor.id_sound`, `Identification.CFactor.id_sound_anc`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## The ID algorithm is sound for sets

Under `do(X = x)` the model lives on `G_{X̄}` (`cutIn G X`). Its c-components are `{x}`
for every `x ∈ X`, purely latent blocks, and blocks `D` outside `X`. Then

  `P_X(O) = ∏_D Q_X[D]`  and  `Q_X[D] = Q[D]`  for `D` disjoint from `X`

(`marginal_prod` for the intervention model, and `Q_do_gen`). If every such `D` can be
reached from `V` by Tian's steps (`IdentifyDerives`, `Identification/Identify`), every factor is
determined by the observed distribution (`identifyDerives_ident`), and so is all of `P_X`
(`id_sound`). These are lines 4, 6 and 7 of the ID algorithm put together; line 2
(cutting down to the ancestors of `Y`) is not included, so the hypothesis looks at all the
c-components, not only those that matter for `Y`.

* `Q_lat`: the factor of a purely latent block is 1.
* `Q_do_eq`: the factor under `do(X)` of a block of one of the three kinds is the same in
  two models with the same positive observed distribution.
* `id_sound_blocks`: the version with arbitrary blocks.
* `ccomp_cutIn_X`: in `G_{X̄}` the c-component of `x ∈ X` is just `{x}`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **A purely latent block has factor 1.** -/
lemma Q_lat [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V) (hT : T ⊆ U)
    (a : Assignment (α := α) Uᶜ) : Q M U T a = 1 := by
  unfold Q
  rw [← lat_one M U T a]
  refine tsum_congr (fun w => ?_)
  rw [Finset.inter_eq_right.mpr hT]

/-- **One block under `do(X)`.** If `C` lies in `X`, is purely latent, or is disjoint from
`X` and can be reached from `V`, then its factor in the intervention model is the same for
two models with the same positive observed distribution. -/
lemma Q_do_eq [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hM : M1.marginal Uᶜ = M2.marginal Uᶜ)
    (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0) (C : Finset V)
    (hC : C ⊆ X ∨ C ⊆ U ∨ (Disjoint C X ∧ IdentifyDerives G U Finset.univ C))
    (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M1 X xv) U C a = Q (doModel M2 X xv) U C a := by
  rcases hC with hsub | hlat | ⟨hdis, hRi⟩
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a]
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
  · rw [Q_lat (doModel M1 X xv) U C hlat a, Q_lat (doModel M2 X xv) U C hlat a]
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a,
      Finset.sdiff_eq_self_of_disjoint hdis]
    congr 1
    have h := identifyDerives_ident M1 M2 U C hRi hM hpos a
    unfold Q at h
    exact h

/-- **ID soundness with blocks.** The blocks are closed in `G_{X̄}`, pairwise disjoint and
cover all nodes. Every block lies in `X`, is purely latent, or is disjoint from `X` and can
be reached from `V`. Then `P(Y | do(X))` is identifiable. -/
theorem id_sound_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock (cutIn G X) U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i)
    (hblk : ∀ i ∈ I, B i ⊆ X ∨ B i ⊆ U ∨ (Disjoint (B i) X ∧ IdentifyDerives G U Finset.univ (B i)))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Uᶜ = (doModel M2 X xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [marginal_prod (doModel M1 X xv) U B I hcl hdisj hcov a,
      marginal_prod (doModel M2 X xv) U B I hcl hdisj hcov a]
    exact Finset.prod_congr rfl (fun i hi => Q_do_eq M1 M2 U X hXO hM hpos _ (hblk i hi) xv a)
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

/-- In `G_{X̄}`, `x ∈ X` has no latent neighbours: its c-component is `{x}`. -/
theorem ccomp_cutIn_X (G : DAG V) (U X : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (cutIn G X) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from e).2 (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **The ID algorithm is sound.** If every c-component of `G_{X̄}` that contains an
observed node outside `X` can be reached from `V` by Tian's steps, then `P(Y | do(X))` is
identifiable. -/
theorem id_sound [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (hR : ∀ y, y ∉ U → y ∉ X → IdentifyDerives G U Finset.univ (ccomp (cutIn G X) U y))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_blocks U X hXO id (Finset.univ.image (ccomp (cutIn G X) U)) ?_ ?_ ?_ ?_ Y hY
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (cutIn G X) U y
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v
    exact ⟨ccomp (cutIn G X) U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (cutIn G X) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl ((ccomp_cutIn_X G U X hXO hyX).trans (Finset.singleton_subset_iff.mpr hyX))
    · by_cases hU : ccomp (cutIn G X) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        have hdis : Disjoint (ccomp (cutIn G X) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (cutIn G X) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (cutIn G X) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_cutIn_X G U X hXO hzX hyz)]
            exact hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis hv h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvU hvX
        rw [ccomp_eq_of_mem hv] at hRv
        exact hRv

end CFactor
end Identification

/-! ## Line 2 of the ID algorithm: restriction to the ancestors of `Y`

The previous section required that *all* c-components of `G_{X̄}` can be reached. Line 2
of the ID algorithm (Shpitser–Pearl 2006; Tian & Pearl 2002) looks only at an ancestral
set `S ⊇ Y`:

  `Σ_{O ∖ S} P_X(O) = Q_X[S] = ∏_D Q_X[S ∩ D]`,

where `D` runs over the c-components of `G_{X̄}[S]` (`DAG.induce (cutIn G X) S`). The
first equality is `Q_marg` (`Identification/Identify`) in the intervention model, the
second the product theorem in which the blocks need only be closed inside `S`
(`Q_prod_rel`, in `Identification/CFactorSets`). If every `S ∩ D` that contains an observed node outside `X` can be reached
from `V` (`IdentifyDerives`), then `P(Y | do(X))` is identifiable (`id_sound_anc`). With `S = An(Y)`
in `G_{X̄}` these are lines 2, 4, 6 and 7.

The step from sums over `O ∖ S` to the marginal on `Y` is a recount
(`eq_updX_and_restrict_eq_iff` in `Identification/LatentSplit`, `tsum_updX`, `fiber_eq`):
two functions with equal sums over every fibre `{a[D := x'] : x'}` have equal marginals on
every `Y` outside `D`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **The sum over all assignments, fibre by fibre.** Every `a'` is `a[D := x']` for exactly
one `a` with the fixed value `c0` on `D` and one `x'`. -/
lemma tsum_updX (U D : Finset V) (hD : D ⊆ Uᶜ) (c0 : Assignment (α := α) D)
    (g : Assignment (α := α) Uᶜ → ENNReal) :
    ∑' a', g a' = ∑' a : Assignment (α := α) Uᶜ,
      (if a.restrict hD = c0 then ∑' x' : Assignment (α := α) D, g (updX U D a x') else 0) :=
  ENNReal.tsum_eq_tsum_ite_tsum_of_iff (updX U D) (fun a => a.restrict hD = c0)
    (fun a' => updX U D a' c0) (fun a' => a'.restrict hD)
    (fun a' a x' => eq_updX_and_restrict_eq_iff U D hD c0 x' a a') g

/-- **Equal fibre sums give equal marginals** on every `Y` outside `D`. -/
lemma fiber_eq [∀ v, Nonempty (α v)] (U D : Finset V) (hD : D ⊆ Uᶜ) (Y : Finset V)
    (hY : Y ⊆ Uᶜ) (hYD : ∀ v ∈ Y, v ∉ D) (P1 P2 : Assignment (α := α) Uᶜ → ENNReal)
    (h : ∀ a, ∑' x' : Assignment (α := α) D, P1 (updX U D a x') =
      ∑' x' : Assignment (α := α) D, P2 (updX U D a x'))
    (b : Assignment (α := α) Y) :
    ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0) =
      ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P2 a else 0) := by
  have c0 : Assignment (α := α) D := fun _ => Classical.arbitrary _
  have hr : ∀ (a : Assignment (α := α) Uᶜ) (x' : Assignment (α := α) D),
      (updX U D a x').restrict hY = a.restrict hY := fun a x' => by
    funext ⟨v, hv⟩
    simp only [Assignment.restrict, updX, dif_neg (hYD v hv)]
  calc ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0)
      = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P1 (updX U D a x') else 0) else 0) :=
        tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P1 a else 0)
    _ = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P2 (updX U D a x') else 0) else 0) := by
        refine tsum_congr (fun a => ?_)
        simp only [hr]
        by_cases hb : b = a.restrict hY
        · simp only [if_pos hb]
          rw [h a]
        · simp only [if_neg hb]
    _ = _ := (tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P2 a else 0)).symm

/-- **ID with restriction to an ancestral set, with blocks.** Let `S ⊇ Y` be ancestral in
`G_{X̄}`, and let the blocks be pairwise disjoint, closed inside `S` and cover `S`. If
every block, cut down to `S`, lies in `X`, is purely latent, or is disjoint from `X` and
can be reached from `V`, then `P(Y | do(X))` is identifiable. -/
theorem id_sound_anc_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (S : Finset V) (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, ∀ u ∈ U, ∀ v ∈ S, (cutIn G X).edge u v → (u ∈ B i ↔ v ∈ B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : S ⊆ I.biUnion B)
    (hblk : ∀ i ∈ I, S ∩ B i ⊆ X ∨ S ∩ B i ⊆ U ∨
      (Disjoint (S ∩ B i) X ∧ IdentifyDerives G U Finset.univ (S ∩ B i)))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hlat : IsLatClosed (cutIn G X) U Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  have hlatS : IsLatClosed (cutIn G X) U S := fun v hv u _ e => hS v hv u e
  have hS' : ∀ v ∈ Finset.univ ∩ S, ∀ p ∈ Finset.univ, (cutIn G X).edge p v → p ∈ S :=
    fun v hv p _ e => hS v (Finset.mem_inter.mp hv).2 p e
  have hDO : (Finset.univ ∩ Sᶜ) \ U ⊆ Uᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hYD : ∀ v ∈ Y, v ∉ (Finset.univ ∩ Sᶜ) \ U := fun v hv hvD =>
    Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvD).1).2 (hYS hv)
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Y = (doModel M2 X xv).marginal Y := by
    intro xv
    have hQS : ∀ a, Q (doModel M1 X xv) U S a = Q (doModel M2 X xv) U S a := fun a => by
      rw [Q_prod_rel (doModel M1 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a,
        Q_prod_rel (doModel M2 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a]
      exact Finset.prod_congr rfl (fun i hi => Q_do_eq M1 M2 U X hXO hM hpos _ (hblk i hi) xv a)
    have hfib : ∀ a, ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M1 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') =
        ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M2 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') := fun a => by
      rw [Q_marg (doModel M1 X xv) U Finset.univ S hlat hS' a,
        Q_marg (doModel M2 X xv) U Finset.univ S hlat hS' a, Finset.univ_inter S]
      exact hQS a
    ext b
    rw [← marginal_restrict (doModel M1 X xv) hY, ← marginal_restrict (doModel M2 X xv) hY,
      PMF.map_apply, PMF.map_apply]
    simp only [marginal_eq_Q]
    exact fiber_eq U ((Finset.univ ∩ Sᶜ) \ U) hDO Y hY hYD
      (Q (doModel M1 X xv) U Finset.univ) (Q (doModel M2 X xv) U Finset.univ) hfib b
  rw [hD]

/-- In `G_{X̄}[S]`, `x ∈ X` has no latent neighbours: its c-component is `{x}`. -/
theorem ccomp_ind_X (G : DAG V) (U X S : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (DAG.induce (cutIn G X) S) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from
        (show u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v from e).2.2).2
        (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **The ID algorithm with line 2.** Let `S ⊇ Y` be ancestral in `G_{X̄}` (for example
the ancestors of `Y`). If every c-component of `G_{X̄}[S]` with an observed node outside
`X` can be reached from `V` by Tian's steps, then `P(Y | do(X))` is identifiable. -/
theorem id_sound_anc [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ) (S : Finset V)
    (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    (hR : ∀ y ∈ S, y ∉ U → y ∉ X →
      IdentifyDerives G U Finset.univ (S ∩ ccomp (DAG.induce (cutIn G X) S) U y))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_anc_blocks U X hXO S hS id
    (Finset.univ.image (ccomp (DAG.induce (cutIn G X) S) U)) ?_ ?_ ?_ ?_ Y hYS hY
  · intro i hi u hu v hv e
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (DAG.induce (cutIn G X) S) U y u hu v
      (⟨hS v hv u e, hv, e⟩ : u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v)
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v _
    exact Finset.mem_biUnion.mpr ⟨ccomp (DAG.induce (cutIn G X) S) U v,
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (DAG.induce (cutIn G X) S) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl (fun z hz => (Finset.singleton_subset_iff.mpr hyX)
        (ccomp_ind_X G U X S hXO hyX (Finset.mem_inter.mp hz).2))
    · by_cases hU : S ∩ ccomp (DAG.induce (cutIn G X) S) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        obtain ⟨hvS, hvC⟩ := Finset.mem_inter.mp hv
        have hdis0 : Disjoint (ccomp (DAG.induce (cutIn G X) S) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (DAG.induce (cutIn G X) S) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (DAG.induce (cutIn G X) S) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_ind_X G U X S hXO hzX hyz)]
            exact hzX)
        have hdis : Disjoint (S ∩ ccomp (DAG.induce (cutIn G X) S) U y) X :=
          Finset.disjoint_left.mpr (fun z hz hzX =>
            Finset.disjoint_left.mp hdis0 (Finset.mem_inter.mp hz).2 hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis0 hvC h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvS hvU hvX
        rw [ccomp_eq_of_mem hvC] at hRv
        exact hRv

end CFactor
end Identification
