import PearlDoCalculus.Hedge.ProductBias

/-!
# Completeness of the ID algorithm (steps H4 and H5)

This file proves the completeness theorem `idCheck_iff`. Assume the latent nodes are
roots, `X` and `Y` are observed, and `X ∩ Y = ∅`. Then the ID check `idCheck G U X Y`
says yes exactly when `P(Y | do(X))` is identifiable for every choice of value types.
On the way it finishes step H4, `PM.hedge_not_ident_Y`: for every hedge for `P_X(Y)` the
effect on `Y` is not identifiable.

**Why.** Soundness of the ID check (`idCheck_sound`, in `IdAlgo`) gives one direction.
Completeness is the other: when the check fails, no method can identify the effect.

**How.**

1. *Not identifiable at `Y`, given the data* (`not_ident2`). `MP false` and `MP true` have
   the same observed distribution (`PM.marg2_eq`, in `Hedge/Product.lean`), and it is
   positive (`PM.pos2`). If the effect on `Y` were identifiable, the two models would give
   the same distribution of the parity `YbY` on `Y` under `do(x)` (`Yb_comp`). But `Yb` is
   a fair coin in `MP false` (`PM.Yb_half`) and biased in `MP true` (`PM.Yb_biased`, in
   `Hedge/ProductBias.lean`).
2. *Every hedge has the data* (`hedge_data`). This is the same construction as in
   `PM.hedge_not_ident` (`Hedge/Roots.lean`). The spanning tree from `hedge_spanning`
   gives `ρ` and `par`, and the `nxt` path from `ρ` gives the noisy root `r0`. Together
   with step 1 this gives `hedge_not_ident_Y` (H4).
3. *Completeness* (`idCheck_iff`, H5). The forward direction is `idCheck_sound`. For the
   converse, if `idCheck` says no, there is a hedge (`idCheck_false_hedge`, H2, in
   `Hedge/FromID.lean`), and then the effect is not identifiable with the value type
   `PM.Val2 U` (`hedge_not_ident_Y`).

**Main results.** `PM.not_ident2`, `PM.hedge_data`, `PM.hedge_not_ident_Y` (public),
`idCheck_iff` (public).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 86: H4 ferdig — `P(Y | do X)` er ikke identifiserbar for hver hedge

`YbY`: pariteten på en tilordning av `Y`; `Yb_comp`: `Yb = YbY ∘ restrict`. `not_ident2`: med
konstruksjonsdataene er `P(Y | do X)` ikke identifiserbar: `MP false` og `MP true` har samme
observerte fordeling (`marg2_eq`), `MP false` er positiv (`pos2`), men like marginaler på `Y`
under `do(x)` ville gitt like fordelinger for `Yb`, og `P(Yb = 1) = P(Yb = 0)` i `MP false`
(`Yb_half`) mens `P(Yb = 0) ≠ P(Yb = 1)` i `MP true` (`Yb_biased`). `hedge_data`:
konstruksjonsdataene finnes for hver hedge (fra `hedge_spanning`, som i `hedge_not_ident`).
`hedge_not_ident_Y`: **H4 — for hver hedge for `P(Y | do X)` er effekten ikke identifiserbar**
(latente er røtter, `X` og `Y` er observert, `X ∩ Y = ∅`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section final2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- Pariteten på en tilordning av `Y`. -/
def YbY (y : Assignment (α := Val2 U) Y) : ZMod 2 := ∑ r ∈ Y.attach, (y r).2

lemma Yb_comp : YbY U Y ∘ Assignment.restrict (Finset.subset_univ Y) = Yb U Y := by
  funext s
  exact Finset.sum_attach Y (fun r => (s ⟨r, Finset.mem_univ r⟩).2)

/-- **Ikke identifiserbar på `Y`**, gitt konstruksjonsdataene. -/
theorem not_ident2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X) {d d' : V → ℕ}
    (T : ParTree (OF U F) D.ρ D.par d) (T' : ParTree (OF U F') D.ρ D.par d')
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    ¬ Identifiable G (Val2 U) O X Y := by
  intro hid
  let x : Assignment (α := Val2 U) X := fun _ => (0, 0)
  have hmarg : (doModel (MP G U F F' D X Y false) X x).marginal Y =
      (doModel (MP G U F F' D X Y true) X x).marginal Y := by
    ext y
    let t : Assignment (α := Val2 U) (Y ∪ X) := fun v =>
      if hv : v.1 ∈ Y then y ⟨v.1, hv⟩ else x ⟨v.1, by
        rcases Finset.mem_union.mp v.2 with h | h
        · exact absurd h hv
        · exact h⟩
    have ht1 : ∀ h : X ⊆ Y ∪ X, t.restrict h = x := by
      intro h
      funext ⟨v, hv⟩
      exact dif_neg (fun h' => hYX v h' hv)
    have ht2 : ∀ h : Y ⊆ Y ∪ X, t.restrict h = y := by
      intro h
      funext ⟨v, hv⟩
      exact dif_pos hv
    have h' := hid (MP G U F F' D X Y false) (MP G U F F' D X Y true)
      (marg2_eq G U F F' D X Y hH hD hroot T hO) (fun a => pos2 G U F F' D X Y hH hD T' hO a) t
    rw [ht1, ht2] at h'
    exact h'
  have hq : (doModel (MP G U F F' D X Y false) X x).fullJoint.map (Yb U Y) =
      (doModel (MP G U F F' D X Y true) X x).fullJoint.map (Yb U Y) := by
    rw [← Yb_comp U Y, ← PMF.map_comp, ← PMF.map_comp]
    exact congrArg (fun q => q.map (YbY U Y)) hmarg
  have h1 := Yb_half G U F F' D X Y hH hD hroot hXU T' x
  have h2 := Yb_biased G U F F' D X Y hH hD hroot hYU hYX x
  rw [hq] at h1
  exact h2 h1.symm

end final2

section build2

variable (G : DAG V) (U : Finset V)

/-- **Konstruksjonsdataene finnes for hver hedge.** -/
theorem hedge_data {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) :
    ∃ (D : Data V) (d : V → ℕ), Good G U F F' D ∧ Nonempty (ParTree (OF U F) D.ρ D.par d) ∧
      Nonempty (ParTree (OF U F') D.ρ D.par d) := by
  obtain ⟨ρ, hρ, hρU, par, d, hpd⟩ := hedge_spanning hH hroot
  obtain ⟨n, hn⟩ := hedge_reaches_root hH ρ (hH.sub hρ)
  have hnU := iter_obs hH hroot (hH.sub hρ) hρU n
  have hGood : Good G U F F' (mkData G U ρ par ((nxt G F F')^[n] ρ)) :=
    { ρF := hρ
      ρU := hρU
      parF' := fun v hv hvU hvρ => by
        rw [mkData_par G U ρ par _ hvρ]
        have hs := (hpd v hv hvU hvρ).1
        exact ⟨hs.1, (sib_obs hroot hs).1⟩
      parF := fun v hvF hvU hvρ => by
        rw [mkData_par G U ρ par _ hvρ]
        exact ((hpd v (hH.sub hvF) hvU hvρ).2.2 hvF).1
      lat := fun v hv hvU hvρ => by
        obtain ⟨-, -, u, hu, -, e1, e2⟩ := (hpd v hv hvU hvρ).1
        obtain ⟨h1, h2, h3⟩ := mkData_lat G U ρ par ((nxt G F F')^[n] ρ) (v := v) ⟨u, hu, e1, e2⟩
        rw [mkData_par G U ρ par _ hvρ]
        exact ⟨h1, h3, h2⟩
      r0R := hn
      r0U := hnU }
  refine ⟨mkData G U ρ par ((nxt G F F')^[n] ρ), d, hGood, ⟨?_⟩, ⟨?_⟩⟩
  · exact
      { root := Finset.mem_filter.mpr ⟨hρ, hρU⟩
        fix := mkData_par_self G U ρ par _
        step := fun v hv hvρ => by
          obtain ⟨hvF, hvU⟩ := Finset.mem_filter.mp hv
          rw [mkData_par G U ρ par _ hvρ]
          obtain ⟨hs, hd, hsF⟩ := hpd v (hH.sub hvF) hvU hvρ
          exact ⟨Finset.mem_filter.mpr ⟨(hsF hvF).1, (sib_obs hroot hs).1⟩, hd⟩ }
  · exact
      { root := Finset.mem_filter.mpr ⟨hH.sub hρ, hρU⟩
        fix := mkData_par_self G U ρ par _
        step := fun v hv hvρ => by
          obtain ⟨hvF', hvU⟩ := Finset.mem_filter.mp hv
          rw [mkData_par G U ρ par _ hvρ]
          obtain ⟨hs, hd, -⟩ := hpd v hvF' hvU hvρ
          exact ⟨Finset.mem_filter.mpr ⟨hs.1, (sib_obs hroot hs).1⟩, hd⟩ }

/-- **H4: for hver hedge for `P(Y | do X)` er effekten ikke identifiserbar.** -/
theorem hedge_not_ident_Y {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X) :
    ¬ Identifiable G (Val2 U) Uᶜ X Y := by
  obtain ⟨D, d, hD, ⟨T⟩, ⟨T'⟩⟩ := hedge_data G U hH hroot
  exact not_ident2 G U F F' D X Y hH hD hroot hXU hYU hYX T T' (fun v hv => Finset.mem_compl.mp hv)

end build2

end PM
end Hedge

#print axioms Hedge.PM.not_ident2
#print axioms Hedge.PM.hedge_not_ident_Y

/-! ## Runde 87: H5 — ID-algoritmen er fullstendig

`idCheck_iff`: under standardantakelsene (latente er røtter, `X` og `Y` observert,
`X ∩ Y = ∅`) sier `idCheck` ja **nøyaktig** når `P(Y | do X)` er identifiserbar for alle
verdityper. `→` er sunnheten (`idCheck_sound`). `←`: sier `idCheck` nei, finnes en hedge
(`idCheck_false_hedge`, H2), og da er effekten ikke identifiserbar med verditypen `Val2 U`
(`hedge_not_ident_Y`, H3 og H4). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Fullstendigheten av ID-algoritmen.** -/
theorem idCheck_iff (G : DAG V) (U X Y : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (hXY : ∀ y ∈ Y, y ∉ X) :
    idCheck G U X Y = true ↔
      ∀ (α : V → Type) [∀ v, Nonempty (α v)], Identifiable G α Uᶜ X Y := by
  constructor
  · intro h α _
    exact idCheck_sound G U X Y hXO hY h
  · intro h
    cases hc : idCheck G U X Y with
    | true => rfl
    | false =>
      obtain ⟨F, F', hH⟩ := idCheck_false_hedge G U X Y hXO hc
      exact absurd (h (PM.Val2 U)) (PM.hedge_not_ident_Y G U hH hroot
        (fun v hv => Finset.mem_compl.mp (hXO hv)) (fun y hy => Finset.mem_compl.mp (hY hy)) hXY)

end Hedge

#print axioms Hedge.idCheck_iff
