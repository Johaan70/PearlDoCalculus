import PearlDoCalculus.Hedge.DoGapM2

/-!
# A hedge blocks identification at its roots (step H3)

This file proves `PM.hedge_not_ident`, step H3 of the completeness proof. For every
hedge `(F, F')` for `P_X(Y)` (`IsHedge`, in `Hedge/Defs.lean`) with the latent nodes as
roots and `X` observed, the effect on the observed roots `RO` of `F` is not identifiable:
`¬ Identifiable G (Val U) Uᶜ X (RO G U F)`.

**Why.** Completeness of the ID algorithm says that a failing ID check means the effect
is not identifiable. A failing check gives a hedge (H2, `Hedge/FromID.lean`). This file
shows that the hedge blocks identification at its own roots. Step H4 then carries the
result from the roots to `Y` (`Hedge/Tails`, `Hedge/Product`, `Hedge/ProductBias`,
`Hedge/Complete`). `hedge_not_ident` is a public result in its own right; the final
theorem `idCheck_iff` does not call it, but step H4 runs the same parity models in the
first coordinate of its product models, takes its data from `PM.hedge_data` below and
repeats the argument of `not_ident_PM` with the parity on `Y` in place of the parity on
`RO`. `RO` is used there too.

**How.**

1. *The two parity models disagree* (`not_ident_PM`). Suppose the construction data
   satisfy `Good` and both trees, the one for `F` and the one for `F'`, are given. Then
   `M1` and `M2` have the same observed distribution (`PM.marg_eq`), and it is positive
   (`PM.pos_M1`). If the effect on `RO` were identifiable, the two models would have the
   same distribution of the parity `parY` of `RO` under `do(x)` (`parR_comp`). But that
   parity is a fair coin in `M1` (`PM.parR_half`, at the edge from `PM.cross_edge`) and
   biased `3 : 1` in `M2` (`PM.parR_three`). Since `q 0 + q 1 = 1`
   (`ZMod2.pmf_zero_add_one`), the two cannot agree (`ennreal_contra`).
2. *Every hedge has such data* (`mkData`, `hedge_data`). The spanning tree from
   `hedge_spanning` gives the root `ρ` and the parent pointer `par`. `lat v` is a common
   latent parent of `v` and `par v`. The noisy root `r0` is the root that the `nxt` path
   from `ρ` reaches (`hedge_reaches_root`), and it is observed (`iter_obs`). These data
   satisfy `Good`, and the tree gives the two `ParTree`s. With step 1 this gives
   `hedge_not_ident`.

**Main results.** `PM.not_ident_PM`, `PM.mkData`, `PM.hedge_data`, `PM.hedge_not_ident`
(public).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## The parity models give non-identifiability

`ZMod2.pmf_zero_add_one` (in `Util/ZMod2.lean`): `q 0 + q 1 = 1` for a distribution on
`ZMod 2`. `ennreal_contra`: `b = a`, `b = 3a` and `b + a = 1` cannot all hold. `RO`: the
observed roots; `parY`: the parity of an assignment to `RO`; `parR_comp`:
`parR = parY ∘ restrict`. `not_ident_PM`: with `Good` and the two trees, `P(RO | do X)` is
not identifiable: `M1` and `M2` have the same observed distribution (`marg_eq`), `M1` is
positive (`pos_M1`), but equal marginals on `RO` under `do(x)` would give equal parity
distributions, and these are `1/2` (`parR_half`, with `cross_edge`) against `1/4`
(`parR_three`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `b = a`, `b = 3 · a` and `b + a = 1` cannot all hold in `ENNReal`: they would give
`1 = 2`. -/
lemma ennreal_contra (a b : ENNReal) (h1 : b = a) (h2 : b = 3 * a) (h3 : b + a = 1) : False := by
  have e1 : a + a = 1 := by
    rw [h1] at h3
    exact h3
  have e2 : 3 * a + a = 1 := by
    rw [h2] at h3
    exact h3
  have e3 : (3 : ENNReal) * a + a = (a + a) + (a + a) := by ring
  rw [e3, e1, one_add_one_eq_two] at e2
  exact absurd e2 (ne_of_gt ENNReal.one_lt_two)

section final

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- The observed roots of `F`. -/
def RO : Finset V := (rootsIn G F).filter (fun r => r ∉ U)

/-- The parity of an assignment to `RO`. -/
def parY (y : Assignment (α := Val U) (RO G U F)) : ZMod 2 :=
  ∑ r ∈ (RO G U F).attach, rd (y r) 0

/-- The root parity of a full assignment is the parity of its restriction to `RO`. -/
lemma parR_comp :
    parY G U F ∘ Assignment.restrict (Finset.subset_univ (RO G U F)) = parR G U F := by
  funext s
  exact Finset.sum_attach (RO G U F) (fun r => ov U s r)

/-- **Not identifiable on the observed roots**, given construction data that satisfy
`Good` and the trees of `F` and `F'`. -/
theorem not_ident_PM {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) {d d' : V → ℕ}
    (T : ParTree (OF U F) D.ρ D.par d) (T' : ParTree (OF U F') D.ρ D.par d')
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    ¬ Identifiable G (Val U) O X (RO G U F) := by
  intro hid
  obtain ⟨c, hc, hcU, hcρ, hA⟩ := cross_edge G U F F' D X hH hD hXU T'
  have hYX : ∀ v ∈ RO G U F, v ∉ X := fun v hv =>
    hH.out v (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  let x : Assignment (α := Val U) X := fun _ => 0
  have hmarg : (doModel (M G U F F' D false) X x).marginal (RO G U F) =
      (doModel (M G U F F' D true) X x).marginal (RO G U F) := by
    ext y
    let t : Assignment (α := Val U) (RO G U F ∪ X) := fun v =>
      if hv : v.1 ∈ RO G U F then y ⟨v.1, hv⟩ else x ⟨v.1, by
        rcases Finset.mem_union.mp v.2 with h | h
        · exact absurd h hv
        · exact h⟩
    have ht1 : ∀ h : X ⊆ RO G U F ∪ X, t.restrict h = x := by
      intro h
      funext ⟨v, hv⟩
      exact dif_neg (fun h' => hYX v h' hv)
    have ht2 : ∀ h : RO G U F ⊆ RO G U F ∪ X, t.restrict h = y := by
      intro h
      funext ⟨v, hv⟩
      exact dif_pos hv
    have h' := hid (M G U F F' D false) (M G U F F' D true)
      (marg_eq G U F F' D hH hD hroot T hO) (fun a => pos_M1 G U F F' D hH hD T' hO a) t
    rw [ht1, ht2] at h'
    exact h'
  have hq : (doModel (M G U F F' D false) X x).fullJoint.map (parR G U F) =
      (doModel (M G U F F' D true) X x).fullJoint.map (parR G U F) := by
    rw [← parR_comp G U F, ← PMF.map_comp, ← PMF.map_comp]
    exact congrArg (fun q => q.map (parY G U F)) hmarg
  have h1 := parR_half G U F F' D X hH hD hroot hXU hc hcU hcρ hA x
  have h2 := parR_three G U F F' D hH hD hroot x
  rw [hq] at h1
  exact ennreal_contra _ _ h1.symm h2 (ZMod2.pmf_zero_add_one _)

end final

end PM
end Hedge

/-! ## Step H3 for every hedge

`mkData ρ par r0`: the construction data from `hedge_spanning` (`par ρ := ρ`; `lat v` is
a latent parent of both `v` and `par v`, chosen from `sib`). `hedge_data`: these data,
with `r0` the root that the `nxt` path from `ρ` reaches (`hedge_reaches_root`; it is
observed, `iter_obs`), satisfy `Good` and give both trees; step H4 uses them too.
`hedge_not_ident`: **for every hedge, `P(RO | do X)` is not identifiable**, where `RO`
are the observed roots of `F` (latent nodes are roots, `X` is observed). This is step
H3. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section build

variable (G : DAG V) (U : Finset V)

open Classical in
/-- The construction data built from a spanning tree: the root `ρ`, the parent pointer
`par` (made to fix `ρ`), for each `v` a common latent parent of `v` and `par v` when
there is one, and the noisy root `r0`. -/
noncomputable def mkData (ρ : V) (par : V → V) (r0 : V) : Data V where
  ρ := ρ
  par := fun v => if v = ρ then ρ else par v
  lat := fun v => if h : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v then Classical.choose h else v
  r0 := r0

/-- Away from `ρ`, the parent pointer of `mkData` is `par`. -/
lemma mkData_par (ρ : V) (par : V → V) (r0 : V) {v : V} (hv : v ≠ ρ) :
    (mkData G U ρ par r0).par v = par v :=
  if_neg hv

/-- The parent pointer of `mkData` fixes `ρ`. -/
lemma mkData_par_self (ρ : V) (par : V → V) (r0 : V) : (mkData G U ρ par r0).par ρ = ρ :=
  if_pos rfl

/-- When `v` and `par v` have a common latent parent, `lat v` is one. -/
lemma mkData_lat (ρ : V) (par : V → V) (r0 : V) {v : V}
    (hex : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v) :
    (mkData G U ρ par r0).lat v ∈ U ∧ G.edge ((mkData G U ρ par r0).lat v) (par v) ∧
      G.edge ((mkData G U ρ par r0).lat v) v := by
  have h : (mkData G U ρ par r0).lat v = Classical.choose hex := dif_pos hex
  rw [h]
  exact Classical.choose_spec hex

/-- **The construction data exist for every hedge**: `mkData` built from
`hedge_spanning` and the root reached from `ρ`, with `Good` and the two trees. -/
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

/-- **Step H3: a hedge blocks identification at its observed roots** (public). For a
hedge `(F, F')` for `P_X(Y)`, with the latent nodes as roots and `X` observed, the
effect of `X` on the observed roots `RO G U F` of `F` is not identifiable with the value
types `Val U`. -/
theorem hedge_not_ident {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) :
    ¬ Identifiable G (Val U) Uᶜ X (RO G U F) := by
  obtain ⟨D, d, hD, ⟨T⟩, ⟨T'⟩⟩ := hedge_data G U hH hroot
  exact not_ident_PM G U F F' D hH hD hroot hXU T T' (fun v hv => Finset.mem_compl.mp hv)

end build

end PM
end Hedge
