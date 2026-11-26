/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.BlockStep

/-!
# The c-components of the ID check

The ID check (`IdAlgo.idCheck`) for `P(Y | do(X))` works with the set
`S = An(Y)` in `G_{X̄}` (`IdAlgo.ancIn (cutIn G X) univ Y`; it may contain latents and
vertices of `X`) and, for each observed `y ∈ S` outside `X`, the c-component
`C_y = IdAlgo.ccIn (cutIn G X) U S {y}` of `y` in `G_{X̄}[S]`. It asks that IDENTIFY reaches
each `C_y` from `V` in `G` (`IdAlgo.identifyTop G U C_y`). The outer frame
(`DoCalc/OuterFrame`) writes the effect as a sum of `Q[D]` with `D = (S ∖ U) ∖ X`. This
file links the two: `Q[D]` is the product of the `Q[C_y]`, as a derivation.

**The graph does not matter for `Q`.** `qExpr U T` mentions only `U` and `T`, not the
graph. So `Q[C_y]` is literally the same expression whether `C_y` is seen as a
c-component of `G_{X̄}` or of `G`. What does depend on the graph is which sets are
c-components, and that is the content of this file.

**The c-components** (for `S` closed under parents in `G_{X̄}`, `X` observed, `y ∈ S ∖ X`):

* `C_y` contains no vertex of `X` (`disjoint_ccIn_cutIn`): a latent step in `G_{X̄}` never
  enters `X`, since latents are not in `X` and edges into `X` are cut.
* `C_y` is the c-component of `y` in `G[S ∖ X]` (`ccIn_cutIn_eq`, `ccIn_cutIn_eq_ccomp`),
  so the same set in `G` and in `G_{X̄}`.
* `C_y` is closed in `D`, for `G` (`ccIn_closed_in`): a latent parent `u` of `v ∈ D` lies in
  `S`, since `u → v` is an edge of `G_{X̄}`, so `u` and `v` are in `C_y` together.
* Two of them are equal or disjoint (`ccIn_eq_of_mem`, `ccIn_eq_or_disjoint`), and every
  `y` lies in its own (`IdAlgo.cc_sup`).
* `Q[D ∩ C_y] = Q[C_y]` (`qExpr_inter_ccIn`): the observed part of `C_y` lies in `D`.

**The factorization** (`Derives.qExpr_factor_ccIn`). With the latents roots,

  `Q[D] = ∏_{C ∈ {C_y : y ∈ D}} Q[C]`,

from `Derives.qExpr_factor_list` with the distinct blocks `C_y`, listed by
`Finset.toList`. Each block in the product is a `C_y` with `y ∈ D`, for which the ID check
runs IDENTIFY.

**What the ID check gives.** When `idCheck G U X Y = true`, IDENTIFY reaches every `C_y`
from `V` (`identifyDerives_of_idCheck`, from `IdAlgo.identifyTop_sound`).

**Main results.** `ancIn_cutIn_closed`, `disjoint_ccIn_cutIn`, `ccIn_cutIn_eq`,
`ccIn_cutIn_eq_ccomp`, `identifyDerives_of_idCheck`, `ccIn_closed_in`, `ccIn_eq_of_mem`, `ccIn_eq_or_disjoint`, `qExpr_inter_ccIn`,
`Derives.qExpr_factor_ccIn`.
-/

open PearlDoCalculus DAG DoCalculus IdAlgo

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {U X S : Finset V}

/-- The set of the ID check, `An(Y)` in `G_{X̄}`, is closed under parents in `G_{X̄}`. -/
lemma ancIn_cutIn_closed (G : DAG V) (X Y : Finset V) :
    ∀ v ∈ ancIn (cutIn G X) Finset.univ Y, ∀ p, (cutIn G X).edge p v →
      p ∈ ancIn (cutIn G X) Finset.univ Y := fun v hv p e =>
  anc_closed (cutIn G X) Finset.univ Y (Finset.subset_univ Y) p (Finset.mem_univ p) ⟨v, hv, e⟩

/-! ## The c-components in `G` and in `G_{X̄}` -/

/-- **`C_y` avoids `X`**, for observed `X` and `y ∉ X`. -/
lemma disjoint_ccIn_cutIn (hXO : X ⊆ Uᶜ) (T : Finset V) {y : V} (hy : y ∉ X) :
    Disjoint (ccIn (cutIn G X) U T {y}) X := by
  rw [← Finset.subset_compl_iff_disjoint_right]
  refine Finset.iterate_subset Xᶜ (ccStep (cutIn G X) U T) ?_ {y}
    (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hy)) T.card
  intro A hA w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact hA hw
  · obtain ⟨-, b, -, h⟩ := Finset.mem_filter.mp hw
    rcases h with ⟨-, -, hwX⟩ | ⟨hwU, -⟩
    · exact Finset.mem_compl.mpr hwX
    · exact Finset.mem_compl.mpr fun hwX => Finset.mem_compl.mp (hXO hwX) hwU

/-- **`C_y` is the c-component of `y` in `G[S ∖ X]`**, for observed `X` and `y ∈ S ∖ X`: the
c-components of `G_{X̄}[S]` and of `G[S ∖ X]` agree. -/
lemma ccIn_cutIn_eq (hXO : X ⊆ Uᶜ) {y : V} (hyS : y ∈ S) (hyX : y ∉ X) :
    ccIn (cutIn G X) U S {y} = ccIn G U (S \ X) {y} := by
  have hy : ({y} : Finset V) ⊆ S := Finset.singleton_subset_iff.mpr hyS
  have hy' : ({y} : Finset V) ⊆ S \ X :=
    Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hyS, hyX⟩)
  apply Finset.Subset.antisymm
  · refine Finset.iterate_subset _ (ccStep (cutIn G X) U S) ?_ {y} (cc_sup G U _ {y}) S.card
    intro A hA w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hA hw
    · obtain ⟨hwS, b, hb, h⟩ := Finset.mem_filter.mp hw
      have hwX : w ∉ X := by
        rcases h with ⟨-, -, hwX⟩ | ⟨hwU, -⟩
        · exact hwX
        · exact fun hwX => Finset.mem_compl.mp (hXO hwX) hwU
      refine cc_closed G U (S \ X) {y} hy' w (Finset.mem_sdiff.mpr ⟨hwS, hwX⟩) ⟨b, hA hb, ?_⟩
      rcases h with ⟨hbU, e, -⟩ | ⟨hwU, e, -⟩
      · exact Or.inl ⟨hbU, e⟩
      · exact Or.inr ⟨hwU, e⟩
  · refine Finset.iterate_subset _ (ccStep G U (S \ X)) ?_ {y}
      (cc_sup (cutIn G X) U _ {y}) (S \ X).card
    intro A hA w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hA hw
    · obtain ⟨hw', b, hb, h⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwS, hwX⟩ := Finset.mem_sdiff.mp hw'
      have hbX : b ∉ X := Finset.disjoint_left.mp (disjoint_ccIn_cutIn hXO S hyX) (hA hb)
      refine cc_closed (cutIn G X) U S {y} hy w hwS ⟨b, hA hb, ?_⟩
      rcases h with ⟨hbU, e⟩ | ⟨hwU, e⟩
      · exact Or.inl ⟨hbU, e, hwX⟩
      · exact Or.inr ⟨hwU, e, hbX⟩

/-- **`C_y` as a `ccomp`**: the c-component of `y` in the induced graph `G[S ∖ X]`. -/
lemma ccIn_cutIn_eq_ccomp (hXO : X ⊆ Uᶜ) {y : V} (hyS : y ∈ S) (hyX : y ∉ X) :
    ccIn (cutIn G X) U S {y} =
      (S \ X) ∩ Identification.CFactor.ccomp (DAG.induce G (S \ X)) U y := by
  rw [ccIn_cutIn_eq hXO hyS hyX, ccIn_eq G U (S \ X) y (Finset.mem_sdiff.mpr ⟨hyS, hyX⟩)]

/-- **What the ID check gives.** If `idCheck G U X Y = true`, then IDENTIFY reaches every
`C_y` from `V`, for `y` in `S = An(Y)` of `G_{X̄}` observed and outside `X`. -/
lemma identifyDerives_of_idCheck {Y : Finset V} (h : idCheck G U X Y = true) :
    ∀ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U → y ∉ X →
      Identification.CFactor.IdentifyDerives G U Finset.univ
        (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) := by
  intro y hy hyU hyX
  unfold idCheck at h
  exact identifyTop_sound G U _ (of_decide_eq_true h y hy hyU hyX)

/-! ## The blocks of the factorization -/

/-- **`C_y` is closed** in `S ∖ X` for `G`, when `S` is closed under parents in `G_{X̄}`: a
latent `u` with an edge into `v ∈ S ∖ X` is in `C_y` exactly when `v` is. -/
lemma ccIn_closed_in (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S) {y : V}
    (hyS : y ∈ S) :
    ∀ u ∈ U, ∀ v ∈ S \ X, G.edge u v →
      (u ∈ ccIn (cutIn G X) U S {y} ↔ v ∈ ccIn (cutIn G X) U S {y}) := by
  intro u hu v hv e
  obtain ⟨hvS, hvX⟩ := Finset.mem_sdiff.mp hv
  have e' : (cutIn G X).edge u v := ⟨e, hvX⟩
  have hy : ({y} : Finset V) ⊆ S := Finset.singleton_subset_iff.mpr hyS
  exact ⟨fun h => cc_closed (cutIn G X) U S {y} hy v hvS ⟨u, h, Or.inl ⟨hu, e'⟩⟩,
    fun h => cc_closed (cutIn G X) U S {y} hy u (hS v hvS u e') ⟨v, h, Or.inr ⟨hu, e'⟩⟩⟩

/-- **Two vertices in one c-component have the same c-component.** -/
lemma ccIn_eq_of_mem {H : DAG V} {T : Finset V} {y z : V} (hyT : y ∈ T)
    (hz : z ∈ ccIn H U T {y}) : ccIn H U T {z} = ccIn H U T {y} := by
  have hzT : z ∈ T := ccIn_subset H U T {y} (Finset.singleton_subset_iff.mpr hyT) hz
  rw [ccIn_eq H U T y hyT] at hz ⊢
  rw [ccIn_eq H U T z hzT,
    Identification.CFactor.ccomp_eq_of_mem (Finset.mem_inter.mp hz).2]

/-- **Two c-components are equal or disjoint.** -/
lemma ccIn_eq_or_disjoint {H : DAG V} {T : Finset V} {y z : V} (hyT : y ∈ T) (hzT : z ∈ T) :
    ccIn H U T {y} = ccIn H U T {z} ∨ Disjoint (ccIn H U T {y}) (ccIn H U T {z}) := by
  by_cases h : Disjoint (ccIn H U T {y}) (ccIn H U T {z})
  · exact Or.inr h
  · obtain ⟨w, hwy, hwz⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inl ((ccIn_eq_of_mem hyT hwy).symm.trans (ccIn_eq_of_mem hzT hwz))

/-- **`Q[D ∩ C_y] = Q[C_y]`** for `D = (S ∖ U) ∖ X`: the observed part of `C_y` lies in
`D`. -/
lemma qExpr_inter_ccIn (hXO : X ⊆ Uᶜ) {y : V} (hyS : y ∈ S) (hyX : y ∉ X) :
    qExpr U ((S \ U) \ X ∩ ccIn (cutIn G X) U S {y}) = qExpr U (ccIn (cutIn G X) U S {y}) := by
  have hsub := ccIn_subset (cutIn G X) U S {y} (Finset.singleton_subset_iff.mpr hyS)
  have hdis := disjoint_ccIn_cutIn (G := G) hXO S hyX
  have h : ((S \ U) \ X ∩ ccIn (cutIn G X) U S {y}) \ U = ccIn (cutIn G X) U S {y} \ U := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨⟨⟨hsub h.1, h.2⟩, Finset.disjoint_left.mp hdis h.1⟩, h.1⟩, h.2⟩
  rw [← qExpr_sdiff U ((S \ U) \ X ∩ _), h, qExpr_sdiff]

/-! ## The factorization of `Q[D]` -/

/-- **`Q[D]` is the product of the c-factors of the c-components.** For latents that are
roots, observed `X`, and `S` closed under parents in `G_{X̄}`, with `D = (S ∖ U) ∖ X` and
`C_y = ccIn (cutIn G X) U S {y}`: `Q[D] = ∏ Q[C]` over the distinct sets `C_y`, `y ∈ D`. -/
theorem Derives.qExpr_factor_ccIn (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXO : X ⊆ Uᶜ)
    (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S) :
    Derives G U (qExpr U ((S \ U) \ X))
      (prodExpr ((((S \ U) \ X).image (fun y => ccIn (cutIn G X) U S {y})).toList.map
        (qExpr U))) := by
  have hmem : ∀ {B}, B ∈ (((S \ U) \ X).image (fun y => ccIn (cutIn G X) U S {y})).toList →
      ∃ y, (y ∈ S ∧ y ∉ X) ∧ ccIn (cutIn G X) U S {y} = B := by
    intro B hB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hB)
    simp only [Finset.mem_sdiff] at hy
    exact ⟨y, ⟨hy.1.1, hy.2⟩, rfl⟩
  have h := Derives.qExpr_factor_list hroot
    (((S \ U) \ X).image (fun y => ccIn (cutIn G X) U S {y})).toList (T := (S \ U) \ X)
    (fun B hB u hu v hv e => by
      obtain ⟨y, ⟨hyS, -⟩, rfl⟩ := hmem hB
      simp only [Finset.mem_sdiff] at hv
      exact ccIn_closed_in hS hyS u hu v (Finset.mem_sdiff.mpr ⟨hv.1.1, hv.2⟩) e)
    ((Finset.nodup_toList _).imp_of_mem fun hB hB' hne => by
      obtain ⟨y, ⟨hyS, -⟩, rfl⟩ := hmem hB
      obtain ⟨z, ⟨hzS, -⟩, rfl⟩ := hmem hB'
      exact (ccIn_eq_or_disjoint hyS hzS).resolve_left hne)
    (fun v hv => ⟨ccIn (cutIn G X) U S {v},
      Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mp hv |>.1, rfl⟩),
      cc_sup _ U S {v} (Finset.mem_singleton_self v)⟩)
  refine trans h (of_eq (congrArg prodExpr (List.map_congr_left fun B hB => ?_)))
  obtain ⟨y, ⟨hyS, hyX⟩, rfl⟩ := hmem hB
  exact qExpr_inter_ccIn hXO hyS hyX

end DoCalc
