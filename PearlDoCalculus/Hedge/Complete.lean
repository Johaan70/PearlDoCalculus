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
This is the last file of the proof; `idCheck_iff` is the main public result of the
`Hedge` folder, checked by `verification/AuditV480.lean` and `verification/AuditFinal.lean` and described in
`EpistemicScope`. The steps H1 to H5 are laid out in section 2 of `HANDOFF.md`.

**How.**

1. *Not identifiable at `Y`, given the data* (`not_ident2`). `MP false` and `MP true` have
   the same observed distribution (`PM.marg2_eq`, in `Hedge/Product.lean`), and it is
   positive (`PM.pos2`). If the effect on `Y` were identifiable, the two models would give
   the same distribution of the parity `YbY` on `Y` under `do(x)` (`Yb_comp`). But `Yb` is
   a fair coin in `MP false` (`PM.Yb_half`) and biased in `MP true` (`PM.Yb_biased`, in
   `Hedge/ProductBias.lean`).
2. *Every hedge has the data* (`PM.hedge_data`, in `Hedge/Roots.lean`, where step H3
   uses it for `PM.hedge_not_ident`). The spanning tree from `hedge_spanning` gives `ρ`
   and `par`, and the `nxt` path from `ρ` gives the noisy root `r0`. Together with
   step 1 this gives `hedge_not_ident_Y` (H4).
3. *Completeness* (`idCheck_iff`, H5). The forward direction is `idCheck_sound`. For the
   converse, if `idCheck` says no, there is a hedge (`idCheck_false_hedge`, H2, in
   `Hedge/FromID.lean`), and then the effect is not identifiable with the value type
   `PM.Val2 U` (`hedge_not_ident_Y`).

**Main results.** `PM.not_ident2`, `PM.hedge_not_ident_Y` (public),
`idCheck_iff` (public).
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Step H4 finished: `P(Y | do X)` is not identifiable for any hedge

`YbY`: the parity of an assignment to `Y`; `Yb_comp`: `Yb = YbY ∘ restrict`. `not_ident2`:
given the construction data, `P(Y | do X)` is not identifiable: `MP false` and `MP true`
have the same observed distribution (`marg2_eq`), `MP false` is positive (`pos2`), but
equal marginals on `Y` under `do(x)` would give equal distributions of `Yb`, while
`P(Yb = 1) = P(Yb = 0)` in `MP false` (`Yb_half`) and `P(Yb = 0) ≠ P(Yb = 1)` in `MP true`
(`Yb_biased`). `hedge_not_ident_Y`, with the data of `hedge_data` (`Hedge/Roots`):
**step H4: for every hedge for `P(Y | do X)` the effect is not identifiable** (latent
nodes are roots, `X` and `Y` are observed, `X ∩ Y = ∅`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section final2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- The parity of the tail bits of an assignment to `Y`. -/
def YbY (y : Assignment (α := Val2 U) Y) : ZMod 2 := ∑ r ∈ Y.attach, (y r).2

/-- `Yb` of a full assignment is `YbY` of its restriction to `Y`. -/
lemma Yb_comp : YbY U Y ∘ Assignment.restrict (Finset.subset_univ Y) = Yb U Y := by
  funext s
  exact Finset.sum_attach Y (fun r => (s ⟨r, Finset.mem_univ r⟩).2)

/-- **Not identifiable on `Y`**, given construction data that satisfy `Good` and the
trees of `F` and `F'`. -/
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

/-- **Step H4: a hedge blocks identification at `Y`** (public). For every hedge
`(F, F')` for `P_X(Y)`, with the latent nodes as roots, `X` and `Y` observed and
`X ∩ Y = ∅`, the effect `P(Y | do X)` is not identifiable with the value types
`Val2 U`. -/
theorem hedge_not_ident_Y {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X) :
    ¬ Identifiable G (Val2 U) Uᶜ X Y := by
  obtain ⟨D, d, hD, ⟨T⟩, ⟨T'⟩⟩ := hedge_data G U hH hroot
  exact not_ident2 G U F F' D X Y hH hD hroot hXU hYU hYX T T' (fun v hv => Finset.mem_compl.mp hv)

end build2

end PM
end Hedge

/-! ## Step H5: the ID algorithm is complete

`idCheck_iff`: under the standard assumptions (latent nodes are roots, `X` and `Y`
observed, `X ∩ Y = ∅`), `idCheck` says yes **exactly** when `P(Y | do X)` is identifiable
for all value types. `→` is soundness (`idCheck_sound`). `←`: if `idCheck` says no, there
is a hedge (`idCheck_false_hedge`, H2), and then the effect is not identifiable with the
value type `Val2 U` (`hedge_not_ident_Y`, H3 and H4). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Completeness of the ID algorithm** (public; Shpitser and Pearl 2006, Huang and
Valtorta 2006). With the latent nodes `U` as roots, `X` and `Y` observed and
`X ∩ Y = ∅`, the ID check says yes exactly when `P(Y | do X)` is identifiable for every
choice of nonempty value types. For the direction `←` one witness type is enough, and
the proof uses `PM.Val2 U`. -/
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
