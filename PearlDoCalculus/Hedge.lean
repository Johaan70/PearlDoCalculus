import PearlDoCalculus.Idc
import PearlDoCalculus.Hedge.FromID
import PearlDoCalculus.Hedge.Tree
import PearlDoCalculus.Hedge.Reduce
import PearlDoCalculus.Hedge.ParityModels
import PearlDoCalculus.Hedge.ObsEq
import PearlDoCalculus.Hedge.Positivity
import PearlDoCalculus.Hedge.DoGapM1
import PearlDoCalculus.Hedge.DoGapM2
import PearlDoCalculus.Hedge.Roots
import PearlDoCalculus.Hedge.Tails
import PearlDoCalculus.Hedge.Product
import PearlDoCalculus.Hedge.ProductBias

/-!
# Completeness of the ID algorithm: a hedge blocks identification (steps H4–H5)

The definitions `rootsIn`, `CConn` and `IsHedge` are in `PearlDoCalculus/Hedge/Defs.lean`.
Step H2, that a failing ID check gives a hedge (`idCheck_false_hedge`), is in
`PearlDoCalculus/Hedge/FromID.lean`. The forest into the roots of a hedge, its spanning
tree and the incidence lemmas on trees (`nxt`, `hedge_spanning`, `ParTree`, `inc`) are in
`PearlDoCalculus/Hedge/Tree.lean`. The reduction to the subgraph with only the forest and
tree edges (`not_ident_of_subα`, `keepDAG`, `hedgeKeep`) is in
`PearlDoCalculus/Hedge/Reduce.lean`. The parity models `M1`, `M2` and their kernel
factors (`PM.Data`, `PM.M`, `PM.Good`, `PM.sb_read`) are in
`PearlDoCalculus/Hedge/ParityModels.lean`, the proof that they have the same observed
distribution (`PM.phiS`, `PM.tele`, `PM.marg_eq`) is in `PearlDoCalculus/Hedge/ObsEq.lean`,
and its positivity (`PM.pos_M1`) is in `PearlDoCalculus/Hedge/Positivity.lean`. The
effect in `M1`, a fair root parity under `do(x)` (`nrI`, `PM.psiS`, `PM.parR_half`), is in
`PearlDoCalculus/Hedge/DoGapM1.lean`, and the effect in `M2`, a biased root parity
(`PM.cross_edge`, `PM.parR_three`), is in `PearlDoCalculus/Hedge/DoGapM2.lean`. Step H3,
that every hedge blocks identification at its observed roots (`PM.hedge_not_ident`), is
in `PearlDoCalculus/Hedge/Roots.lean`. The tails from the roots to `Y` (`tp`, `tI`) are
in `PearlDoCalculus/Hedge/Tails.lean`. The product models `MP`, their equal positive
observed distribution and the fair parity `Yb` in `MP false` (`PM.marg2_eq`, `PM.pos2`,
`PM.Yb_half`) are in `PearlDoCalculus/Hedge/Product.lean`, and the bias of `Yb` in
`MP true` (`bias_step`, `PM.Yb_biased`) is in `PearlDoCalculus/Hedge/ProductBias.lean`.

This file concludes H4, that `P(Y | do(X))` is not identifiable for every hedge
(`PM.hedge_not_ident_Y`), and ends with the completeness theorem `idCheck_iff` (H5). The
file is being split by topic; see `CLEANUP.md`.
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
