import PearlDoCalculus.Idc
import PearlDoCalculus.Hedge.FromID
import PearlDoCalculus.Hedge.Tree
import PearlDoCalculus.Hedge.Reduce
import PearlDoCalculus.Hedge.ParityModels
import PearlDoCalculus.Hedge.ObsEq
import PearlDoCalculus.Hedge.Positivity
import PearlDoCalculus.Hedge.DoGapM1

/-!
# Completeness of the ID algorithm: a hedge blocks identification (steps H3–H5)

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
`PearlDoCalculus/Hedge/DoGapM1.lean`.

This file shows that a hedge makes `P(Y | do(X))` non-identifiable, and ends with the
completeness theorem `idCheck_iff`. It computes the effect in `M2` and shows that the
parity models give different effects. The file is being split by topic; see `CLEANUP.md`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## Runde 72: den kryssende trekanten og et forholdslemma

`ParTree.iff_root`: har hver trekant `(c, par c)` samme sannhetsverdi for `P` i begge ender,
har hele treet sannhetsverdien til roten. `cross_edge`: i `F'`-treet finnes en trekant der
nøyaktig én ende når en rot uten å treffe `X` (røttene gjør det, en `x ∈ X ∩ F'` gjør det
ikke). `map_ratio`: en involusjon `τ` som snur `f` og ganger vekten med `k` når `f = 1`, gir
`P(f = 0) = k · P(f = 1)`; det brukes for `M2` med `k = noise 0 / noise 1`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Samme sannhetsverdi langs hver trekant ⇒ samme som roten. -/
theorem ParTree.iff_root {S : Finset V} {ρ : V} {par : V → V} {d : V → ℕ}
    (T : ParTree S ρ par d) (P : V → Prop) (h : ∀ c ∈ S, c ≠ ρ → (P c ↔ P (par c))) :
    ∀ v ∈ S, (P v ↔ P ρ) := by
  have key : ∀ n, ∀ v ∈ S, d v = n → (P v ↔ P ρ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hdn
      by_cases hvρ : v = ρ
      · rw [hvρ]
      · obtain ⟨hp, hlt⟩ := T.step v hv hvρ
        exact (h v hv hvρ).trans (ih (d (par v)) (by omega) (par v) hp rfl)
  exact fun v hv => key (d v) v hv rfl

lemma zmod2_s0 : ∀ a : ZMod 2, (0 = a + 1 ↔ 1 = a) := by decide

/-- **Forholdslemmaet.** -/
theorem map_ratio {β : Type*} (p : PMF β) (τ : β → β) (f : β → ZMod 2) (k : ENNReal)
    (hinv : ∀ s, τ (τ s) = s) (hf : ∀ s, f (τ s) = f s + 1)
    (hp : ∀ s, f s = 1 → p (τ s) = k * p s) :
    (p.map f) 0 = k * (p.map f) 1 := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm τ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  first
    | simp only [Function.Involutive.coe_toPerm, hf]
    | simp only [hf]
  by_cases h1 : 1 = f s
  · rw [if_pos ((zmod2_s0 (f s)).mpr h1), if_pos h1, hp s h1.symm]
  · rw [if_neg (fun h => h1 ((zmod2_s0 (f s)).mp h)), if_neg h1, mul_zero]

namespace PM

section cross

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- **Den kryssende trekanten.** -/
theorem cross_edge {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hXU : ∀ v ∈ X, v ∉ U) {d : V → ℕ} (T : ParTree (OF U F') D.ρ D.par d) :
    ∃ c, c ∈ F' ∧ c ∉ U ∧ c ≠ D.ρ ∧
      (((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
          ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
        ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
          ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r)) := by
  by_contra hno
  have hiff := T.iff_root (fun v => ∃ r ∈ rootsIn G F, nreach G X F F' v r) (fun c hc hcρ => by
    have hcF' := (Finset.mem_filter.mp hc).1
    have hcU := (Finset.mem_filter.mp hc).2
    by_cases h1 : ∃ r ∈ rootsIn G F, nreach G X F F' c r <;>
      by_cases h2 : ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact (hno ⟨c, hcF', hcU, hcρ, Or.inl ⟨h1, h2⟩⟩).elim
    · exact (hno ⟨c, hcF', hcU, hcρ, Or.inr ⟨h1, h2⟩⟩).elim
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩)
  have hr0F := (Finset.mem_filter.mp hD.r0R).1
  have hr0 : D.r0 ∈ OF U F' := Finset.mem_filter.mpr ⟨hH.sub hr0F, hD.r0U⟩
  have hP0 : ∃ r ∈ rootsIn G F, nreach G X F F' D.r0 r :=
    ⟨D.r0, hD.r0R, 0, rfl, fun j hj => by
      rw [Nat.le_zero.mp hj]
      exact hH.out _ hr0F⟩
  obtain ⟨x0, hx0X, hx0F'⟩ := hH.meet
  have hx0 : x0 ∈ OF U F' := Finset.mem_filter.mpr ⟨hx0F', hXU x0 hx0X⟩
  have hnP : ¬ ∃ r ∈ rootsIn G F, nreach G X F F' x0 r := by
    rintro ⟨r, -, k, -, hk⟩
    exact hk 0 (Nat.zero_le _) hx0X
  exact hnP ((hiff x0 hx0).mpr ((hiff D.r0 hr0).mp hP0))

end cross

end PM
end Hedge

#print axioms Hedge.ParTree.iff_root
#print axioms Hedge.map_ratio
#print axioms Hedge.PM.cross_edge

/-! ## Runde 73: `M2` under `do(x)`: pariteten er støyleddet

`noise_eq`, `noise_card`, `noise_ratio`: `noise 0 = 3 · noise 1`. `sum_sbV2`: summen av
`M2`-bitene over `OF` er summen av verdiene til ikke-røttene i `OF` (hver trebit i `F` telles to
ganger, hver `nxt`-verdi i `F` én gang). `parR_g`: for en tilordning med positiv sannsynlighet
under `do(x)` i `M2` holder ligningene i `OF` utenom `r0` (`F ∩ X = ∅`), så `parR s` er
`ov r0 + sbV true r0`, støyleddet i `r0`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma noise_eq (n : ZMod 2) :
    noise n = ∑ i : Fin 4,
      if n = (if i = 0 then (1 : ZMod 2) else 0) then (Fintype.card (Fin 4) : ENNReal)⁻¹ else 0 := by
  unfold noise
  rw [PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [PMF.uniformOfFintype_apply]
  by_cases h : n = if i = 0 then (1 : ZMod 2) else 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

lemma noise_card (n : ZMod 2) :
    noise n = ((Finset.univ.filter
      (fun i : Fin 4 => n = if i = 0 then (1 : ZMod 2) else 0)).card : ENNReal) *
        (Fintype.card (Fin 4) : ENNReal)⁻¹ := by
  rw [noise_eq, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- **`noise 0 = 3 · noise 1`.** -/
lemma noise_ratio : noise 0 = 3 * noise 1 := by
  rw [noise_card, noise_card]
  have h0 : (Finset.univ.filter
      (fun i : Fin 4 => (0 : ZMod 2) = if i = 0 then (1 : ZMod 2) else 0)).card = 3 := by decide
  have h1 : (Finset.univ.filter
      (fun i : Fin 4 => (1 : ZMod 2) = if i = 0 then (1 : ZMod 2) else 0)).card = 1 := by decide
  rw [h0, h1]
  push_cast
  ring

lemma zmod2_g : ∀ a b c : ZMod 2, a + c = b + c + (a + b) := by decide

section m2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- **Summen av `M2`-bitene over `OF`.** -/
theorem sum_sbV2 {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    ∑ v ∈ OF U F, sbV G U F F' D true s v =
      ∑ w ∈ (OF U F).filter (fun w => w ∉ rootsIn G F), ov U s w := by
  have hS : ∀ v ∈ OF U F, (CH U F' D v).filter (fun c => c ∈ F) =
      ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c = v) := by
    intro v _
    ext c
    simp only [CH, OF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hU, hρ, hp⟩, hF⟩
      exact ⟨⟨⟨hF, hU⟩, hρ⟩, hp⟩
    · rintro ⟨⟨⟨hF, hU⟩, hρ⟩, hp⟩
      exact ⟨⟨hH.sub hF, hU, hρ, hp⟩, hF⟩
  have hN : ∀ v ∈ OF U F, (NX G U F F' v).filter (fun w => w ∈ F) =
      ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter (fun w => nxt G F F' w = v) := by
    intro v _
    ext w
    simp only [NX, OF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hU, hR, hn⟩, hF⟩
      exact ⟨⟨⟨hF, hU⟩, hR⟩, hn⟩
    · rintro ⟨⟨⟨hF, hU⟩, hR⟩, hn⟩
      exact ⟨⟨hH.sub hF, hU, hR, hn⟩, hF⟩
  have hsplit : ∀ v ∈ OF U F, sbV G U F F' D true s v =
      (if v = D.ρ then 0 else lb U D s v) +
        ∑ c ∈ ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c = v), lb U D s c +
        ∑ w ∈ ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter (fun w => nxt G F F' w = v),
          ov U s w := by
    intro v hv
    unfold sbV
    rw [scope_true_in F (Finset.mem_filter.mp hv).1, hS v hv, hN v hv]
  have hS2 : ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c ∈ OF U F) =
      (OF U F).filter (fun c => c ≠ D.ρ) := by
    apply Finset.filter_true_of_mem
    intro c hc
    obtain ⟨hc1, hcρ⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF, hcU⟩ := Finset.mem_filter.mp hc1
    exact Finset.mem_filter.mpr ⟨hD.parF c hcF hcU hcρ, (hD.parF' c (hH.sub hcF) hcU hcρ).2⟩
  have hN2 : ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter
      (fun w => nxt G F F' w ∈ OF U F) = (OF U F).filter (fun w => w ∉ rootsIn G F) := by
    apply Finset.filter_true_of_mem
    intro w hw
    obtain ⟨hw1, hwR⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwF, -⟩ := Finset.mem_filter.mp hw1
    have h := hedge_nxt hH w (hH.sub hwF) hwR
    exact Finset.mem_filter.mpr ⟨h.1 hwF, fun hU => hroot _ hU _ h.2.2⟩
  have hown : ∑ v ∈ OF U F, (if v = D.ρ then 0 else lb U D s v) =
      ∑ c ∈ (OF U F).filter (fun c => c ≠ D.ρ), lb U D s c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v = D.ρ
    · rw [if_pos h, if_neg (not_not.mpr h)]
    · rw [if_neg h, if_pos (show v ≠ D.ρ from h)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    fiber_sum (OF U F) _ D.par (lb U D s), fiber_sum (OF U F) _ (nxt G F F') (ov U s),
    hS2, hN2, hown, zmod2_add_self, zero_add]

/-- **I `M2` under `do(x)` er pariteten støyleddet i `r0`** (på støtten). -/
theorem parR_g {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hs : (doModel (M G U F F' D true) X x).fullJoint s ≠ 0) :
    parR G U F s = ov U s D.r0 + sbV G U F F' D true s D.r0 := by
  rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff] at hs
  have hEq : ∀ v ∈ OF U F, v ≠ D.r0 → ov U s v = sbV G U F F' D true s v := by
    intro v hv hr
    obtain ⟨hvF, hvU⟩ := Finset.mem_filter.mp hv
    have h := hs v (Finset.mem_univ v)
    rw [kfac_doModel, dif_neg (hH.out v hvF), kfac_obs G U F F' D true _ hvU (hH.sub hvF) hr] at h
    rw [← sb_read G U F F' D true hH hD s (hH.sub hvF) hvU]
    by_contra hne
    exact h (if_neg hne)
  have hr0 : D.r0 ∈ OF U F := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hD.r0R).1, hD.r0U⟩
  have hsum : ∑ v ∈ OF U F, ov U s v = ∑ v ∈ OF U F, sbV G U F F' D true s v +
      (ov U s D.r0 + sbV G U F F' D true s D.r0) := by
    rw [← Finset.add_sum_erase (OF U F) (ov U s) hr0,
      ← Finset.add_sum_erase (OF U F) (sbV G U F F' D true s) hr0,
      Finset.sum_congr rfl (fun v hv => hEq v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv))]
    exact zmod2_g _ _ _
  rw [sum_sbV2 G U F F' D hH hD hroot s,
    ← Finset.sum_filter_add_sum_filter_not (OF U F) (fun w => w ∉ rootsIn G F) (ov U s)] at hsum
  have hR := add_left_cancel hsum
  unfold parR
  rw [← hR]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext r
  simp only [OF, Finset.mem_filter, not_not]
  constructor
  · rintro ⟨hr, hrU⟩
    exact ⟨⟨(Finset.mem_filter.mp hr).1, hrU⟩, hr⟩
  · rintro ⟨⟨-, hrU⟩, hr⟩
    exact ⟨hr, hrU⟩

end m2

end PM
end Hedge

#print axioms Hedge.PM.noise_ratio
#print axioms Hedge.PM.sum_sbV2
#print axioms Hedge.PM.parR_g

/-! ## Runde 74: `M2` under `do(x)`: `P(parR = 0) = 3 · P(parR = 1)`

`map_congr_supp`: like funksjoner på støtten gir lik bildefordeling. `tauS`: snu verdien i
`r0`. Ingen leser `r0` (røtter er ikke `nxt`-barn), så `sbV` er uendret (`sbV_tau`) og bare
faktoren i `r0` endres: når støyleddet `gS s = ov r0 + sbV true r0` er 1, går den fra
`noise 1` til `noise 0 = 3 · noise 1` (`joint_tau`). `parR_three`: med `parR_g` og
`map_ratio` er `P(parR = 0) = 3 · P(parR = 1)` under `do(x)` i `M2`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Like funksjoner på støtten gir lik bildefordeling. -/
theorem map_congr_supp {β : Type*} (p : PMF β) (f g : β → ZMod 2)
    (h : ∀ s, p s ≠ 0 → f s = g s) : p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro s
  by_cases hs : p s = 0
  · rw [hs, ite_self, ite_self]
  · rw [h s hs]

namespace PM

lemma zmod2_one : ∀ a b : ZMod 2, a + b = 1 → a + 1 + b = 0 := by decide

section tau

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- Indikatoren for `r`. -/
def ind0 (r w : V) : ZMod 2 := if w = r then 1 else 0

/-- Snu verdien i `r0`. -/
def tauS (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  flipO U (ind0 D.r0) s

/-- Støyleddet i `r0` i `M2`. -/
noncomputable def gS (s : Assignment (α := Val U) (Finset.univ : Finset V)) : ZMod 2 :=
  ov U s D.r0 + sbV G U F F' D true s D.r0

lemma tauS_invol (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    tauS U D (tauS U D s) = s := by
  funext u i
  simp only [tauS, flipO]
  rw [add_assoc, zmod2_add_self, add_zero]

lemma tau_ne (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ≠ D.r0) :
    tauS U D s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
  funext i
  show s ⟨v, Finset.mem_univ v⟩ i + (if v ∈ U then 0 else ind0 D.r0 v) = _
  unfold ind0
  rw [if_neg hv, ite_self, add_zero]

lemma ov_tau (hr0U : D.r0 ∉ U) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    ov U (tauS U D s) D.r0 = ov U s D.r0 + 1 := by
  unfold tauS
  rw [ov_flipO U _ _ hr0U]
  unfold ind0
  rw [if_pos rfl]

/-- **`sbV` leser ikke `r0`.** -/
lemma sbV_tau (hD : Good G U F F' D) (two : Bool)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D two (tauS U D s) v = sbV G U F F' D two s v := by
  unfold sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ]
        unfold tauS
        rw [lb_flipO U D _ _ (hD.lat v hvF' hvU hρ).1]
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
      unfold tauS
      exact lb_flipO U D _ _ (hD.lat c hcF' hcU hcρ).1
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, hwR, -⟩ := Finset.mem_filter.mp hw1
    have hwr : w ≠ D.r0 := fun h => hwR (by rw [h]; exact hD.r0R)
    unfold tauS
    rw [ov_flipO U _ _ hwU]
    unfold ind0
    rw [if_neg hwr, add_zero]

lemma gS_tau (hD : Good G U F F' D) (hr0F' : D.r0 ∈ F')
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    gS G U F F' D (tauS U D s) = gS G U F F' D s + 1 := by
  unfold gS
  rw [ov_tau U D hD.r0U s, sbV_tau G U F F' D hD true s hr0F' hD.r0U]
  ring

/-- Utenom `r0` er faktorene like. -/
lemma kfac_tau {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (x : Assignment (α := Val U) X) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    {v : V} (hv : v ≠ D.r0) :
    kfac (doModel (M G U F F' D true) X x) Finset.univ (tauS U D s) v =
      kfac (doModel (M G U F F' D true) X x) Finset.univ s v := by
  rw [kfac_doModel, kfac_doModel]
  by_cases hvX : v ∈ X
  · rw [dif_pos hvX, dif_pos hvX, tau_ne U D s hv]
  · rw [dif_neg hvX, dif_neg hvX]
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D true _ hvU, kfac_lat G U F F' D true _ hvU]
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D true _ hvU hvF', kfac_out G U F F' D true _ hvU hvF']
    rw [kfac_obs G U F F' D true _ hvU hvF' hv, kfac_obs G U F F' D true _ hvU hvF' hv,
      tau_ne U D s hv, sb_read G U F F' D true hH hD _ hvF' hvU,
      sb_read G U F F' D true hH hD _ hvF' hvU, sbV_tau G U F F' D hD true s hvF' hvU]

/-- **Vekten tredobles** når støyleddet er 1. -/
theorem joint_tau {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (x : Assignment (α := Val U) X) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hg : gS G U F F' D s = 1) :
    (doModel (M G U F F' D true) X x).fullJoint (tauS U D s) =
      3 * (doModel (M G U F F' D true) X x).fullJoint s := by
  have hr0F := (Finset.mem_filter.mp hD.r0R).1
  have hr0F' := hH.sub hr0F
  have hr0X := hH.out _ hr0F
  rw [fullJoint_apply_prod, fullJoint_apply_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    Finset.prod_congr rfl (fun v hv => kfac_tau G U F F' D hH hD x s (Finset.ne_of_mem_erase hv))]
  have h1 : kfac (doModel (M G U F F' D true) X x) Finset.univ (tauS U D s) D.r0 = noise 0 := by
    rw [kfac_doModel, dif_neg hr0X, kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl,
      sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    show ov U (tauS U D s) D.r0 + sbV G U F F' D true (tauS U D s) D.r0 = 0
    rw [ov_tau U D hD.r0U s, sbV_tau G U F F' D hD true s hr0F' hD.r0U]
    exact zmod2_one _ _ hg
  have h2 : kfac (doModel (M G U F F' D true) X x) Finset.univ s D.r0 = noise 1 := by
    rw [kfac_doModel, dif_neg hr0X, kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl,
      sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    try exact hg
  rw [h1, h2, noise_ratio, mul_assoc]

/-- **`P(parR = 0) = 3 · P(parR = 1)` under `do(x)` i `M2`.** -/
theorem parR_three {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (x : Assignment (α := Val U) X) :
    ((doModel (M G U F F' D true) X x).fullJoint.map (parR G U F)) 0 =
      3 * ((doModel (M G U F F' D true) X x).fullJoint.map (parR G U F)) 1 := by
  have hr0F' := hH.sub (Finset.mem_filter.mp hD.r0R).1
  rw [map_congr_supp _ (parR G U F) (gS G U F F' D)
    (fun s hs => parR_g G U F F' D hH hD hroot x s hs)]
  exact map_ratio _ (tauS U D) (gS G U F F' D) 3 (tauS_invol U D)
    (gS_tau G U F F' D hD hr0F') (fun s hg => joint_tau G U F F' D hH hD x s hg)

end tau

end PM
end Hedge

#print axioms Hedge.map_congr_supp
#print axioms Hedge.PM.joint_tau
#print axioms Hedge.PM.parR_three

/-! ## Runde 75: paritetsmodellene gir ikke-identifiserbarhet

`pmf_two`: `q 0 + q 1 = 1` for en fordeling på `ZMod 2`. `ennreal_contra`: `b = a`, `b = 3a` og
`b + a = 1` er umulig. `RO`: de observerte røttene; `parY`: pariteten på en tilordning av `RO`;
`parR_comp`: `parR = parY ∘ restrict`. `not_ident_PM`: med `Good` og de to trærne er
`P(RO | do X)` ikke identifiserbar: `M1` og `M2` har samme observerte fordeling (`marg_eq`),
`M1` er positiv (`pos_M1`), men like marginaler på `RO` under `do(x)` ville gitt like
paritetsfordelinger, og de er `1/2` (`parR_half`, med `cross_edge`) mot `1/4` (`parR_three`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma pmf_two (q : PMF (ZMod 2)) : q 0 + q 1 = 1 := by
  have h := q.tsum_coe
  rw [tsum_fintype] at h
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu, Finset.sum_pair (by decide)] at h
  exact h

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

/-- De observerte røttene. -/
def RO : Finset V := (rootsIn G F).filter (fun r => r ∉ U)

/-- Pariteten på en tilordning av `RO`. -/
def parY (y : Assignment (α := Val U) (RO G U F)) : ZMod 2 :=
  ∑ r ∈ (RO G U F).attach, rd (y r) 0

lemma parR_comp :
    parY G U F ∘ Assignment.restrict (Finset.subset_univ (RO G U F)) = parR G U F := by
  funext s
  exact Finset.sum_attach (RO G U F) (fun r => ov U s r)

/-- **Ikke identifiserbar på de observerte røttene**, gitt konstruksjonsdataene. -/
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
  exact ennreal_contra _ _ h1.symm h2 (pmf_two _)

end final

end PM
end Hedge

#print axioms Hedge.PM.not_ident_PM

/-! ## Runde 76: H3 for hver hedge

`mkData ρ par r0`: konstruksjonsdataene fra `hedge_spanning` (`par ρ := ρ`; `lat v` er en
latent forelder til både `v` og `par v`, valgt fra `sib`). `hedge_not_ident`: **for hver hedge
er `P(RO | do X)` ikke identifiserbar**, der `RO` er de observerte røttene i `F` (latente er
røtter, `X` er observert). `r0` er roten `nxt`-stien fra `ρ` når (`hedge_reaches_root`), og den
er observert (`iter_obs`). Dette er H3. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section build

variable (G : DAG V) (U : Finset V)

open Classical in
/-- Konstruksjonsdataene. -/
noncomputable def mkData (ρ : V) (par : V → V) (r0 : V) : Data V where
  ρ := ρ
  par := fun v => if v = ρ then ρ else par v
  lat := fun v => if h : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v then Classical.choose h else v
  r0 := r0

lemma mkData_par (ρ : V) (par : V → V) (r0 : V) {v : V} (hv : v ≠ ρ) :
    (mkData G U ρ par r0).par v = par v :=
  if_neg hv

lemma mkData_par_self (ρ : V) (par : V → V) (r0 : V) : (mkData G U ρ par r0).par ρ = ρ :=
  if_pos rfl

lemma mkData_lat (ρ : V) (par : V → V) (r0 : V) {v : V}
    (hex : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v) :
    (mkData G U ρ par r0).lat v ∈ U ∧ G.edge ((mkData G U ρ par r0).lat v) (par v) ∧
      G.edge ((mkData G U ρ par r0).lat v) v := by
  have h : (mkData G U ρ par r0).lat v = Classical.choose hex := dif_pos hex
  rw [h]
  exact Classical.choose_spec hex

/-- **H3: en hedge er ikke identifiserbar på de observerte røttene.** -/
theorem hedge_not_ident {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) :
    ¬ Identifiable G (Val U) Uᶜ X (RO G U F) := by
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
  have T : ParTree (OF U F) (mkData G U ρ par ((nxt G F F')^[n] ρ)).ρ
      (mkData G U ρ par ((nxt G F F')^[n] ρ)).par d :=
    { root := Finset.mem_filter.mpr ⟨hρ, hρU⟩
      fix := mkData_par_self G U ρ par _
      step := fun v hv hvρ => by
        obtain ⟨hvF, hvU⟩ := Finset.mem_filter.mp hv
        rw [mkData_par G U ρ par _ hvρ]
        obtain ⟨hs, hd, hsF⟩ := hpd v (hH.sub hvF) hvU hvρ
        exact ⟨Finset.mem_filter.mpr ⟨(hsF hvF).1, (sib_obs hroot hs).1⟩, hd⟩ }
  have T' : ParTree (OF U F') (mkData G U ρ par ((nxt G F F')^[n] ρ)).ρ
      (mkData G U ρ par ((nxt G F F')^[n] ρ)).par d :=
    { root := Finset.mem_filter.mpr ⟨hH.sub hρ, hρU⟩
      fix := mkData_par_self G U ρ par _
      step := fun v hv hvρ => by
        obtain ⟨hvF', hvU⟩ := Finset.mem_filter.mp hv
        rw [mkData_par G U ρ par _ hvρ]
        obtain ⟨hs, hd, -⟩ := hpd v hvF' hvU hvρ
        exact ⟨Finset.mem_filter.mpr ⟨hs.1, (sib_obs hroot hs).1⟩, hd⟩ }
  exact not_ident_PM G U F F' _ hH hGood hroot hXU T T' (fun v hv => Finset.mem_compl.mp hv)

end build

end PM
end Hedge

#print axioms Hedge.PM.hedge_not_ident

/-! ## Runde 78: H4, steg 1 — halepekeren `tp`

`anc_child_in`: en node i `ancIn G T C` er i `C` eller har et barn i `ancIn G T C`.
`AY` = forfedrene til `Y` i `G_{X̄}`. `tp v`: for `v ∈ AY \ Y` et barn i `AY` utenfor `X`
(`tp_spec`); i `Y` står `tp` stille. Langs `tp` vokser rangen (`tp_rank_iter`), stien holder
seg i `AY` og utenfor `X` (`tp_iter_mem`, `tp_iter_notX`), er observert når starten er det
(`tp_iter_obs`), og når `Y` (`tp_reaches`). `tI s w`: `w` ligger på `tp`-stien fra `s`.
`tI_rec`: `tI s v = [v = s] + Σ tI s w` over de observerte `w ∈ AY \ Y` med `tp w = v`.
`sum_tI_Y`: stien når nøyaktig én node i `Y`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En node i `ancIn G T C` er i `C` eller har et barn i `ancIn G T C`. -/
lemma anc_child_in (G : DAG V) (T C : Finset V) (hCT : C ⊆ T) :
    ∀ v ∈ ancIn G T C, v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w := by
  have h := ancIn_min G T C
    ((ancIn G T C).filter (fun v => v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w))
    (fun v hv => Finset.mem_filter.mpr ⟨anc_sup G T C hv, Or.inl hv⟩)
    (fun v hvT hex => by
      obtain ⟨w, hw, e⟩ := hex
      have hwA := (Finset.mem_filter.mp hw).1
      exact Finset.mem_filter.mpr ⟨anc_closed G T C hCT v hvT ⟨w, hwA, e⟩, Or.inr ⟨w, hwA, e⟩⟩)
  intro v hv
  exact (Finset.mem_filter.mp (h hv)).2

section tail

variable (G : DAG V) (X Y : Finset V)

/-- Forfedrene til `Y` i `G_{X̄}`. -/
def AY : Finset V := ancIn (cutIn G X) Finset.univ Y

open Classical in
/-- Halepekeren. -/
noncomputable def tp (v : V) : V :=
  if v ∈ Y then v else
    if h : ∃ w ∈ AY G X Y, (cutIn G X).edge v w then Classical.choose h else v

lemma tp_Y {v : V} (hv : v ∈ Y) : tp G X Y v = v := by
  unfold tp
  rw [if_pos hv]

lemma tp_spec {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    tp G X Y v ∈ AY G X Y ∧ G.edge v (tp G X Y v) ∧ tp G X Y v ∉ X := by
  have hex : ∃ w ∈ AY G X Y, (cutIn G X).edge v w := by
    rcases anc_child_in (cutIn G X) Finset.univ Y (Finset.subset_univ _) v hv with h | h
    · exact absurd h hvY
    · exact h
  have hdef : tp G X Y v = Classical.choose hex := by
    unfold tp
    rw [if_neg hvY, dif_pos hex]
  rw [hdef]
  obtain ⟨hA, e⟩ := Classical.choose_spec hex
  have e' : G.edge v (Classical.choose hex) ∧ Classical.choose hex ∉ X := e
  exact ⟨hA, e'.1, e'.2⟩

lemma iter_tpY {v : V} (hv : v ∈ Y) : ∀ m, (tp G X Y)^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, tp_Y G X Y hv]

lemma tp_iter_mem {v : V} (hv : v ∈ AY G X Y) : ∀ n, (tp G X Y)^[n] v ∈ AY G X Y := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y ih hY).1

lemma tp_iter_notX {v : V} (hv : v ∈ AY G X Y) (hvX : v ∉ X) :
    ∀ n, (tp G X Y)^[n] v ∉ X := by
  intro n
  induction n with
  | zero => exact hvX
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.2

lemma tp_iter_obs {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V}
    (hv : v ∈ AY G X Y) (hvU : v ∉ U) : ∀ n, (tp G X Y)^[n] v ∉ U := by
  intro n
  induction n with
  | zero => exact hvU
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · intro hU
      exact hroot _ hU _ (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.1

lemma tp_rank_iter {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    ∀ m, G.rank v < G.rank ((tp G X Y)^[m + 1] v) := by
  intro m
  induction m with
  | zero =>
    show G.rank v < G.rank (tp G X Y v)
    exact G.rank_strict_mono _ _ (tp_spec G X Y hv hvY).2.1
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases huY : (tp G X Y)^[m + 1] v ∈ Y
    · rw [tp_Y G X Y huY]
      exact ih
    · exact lt_trans ih
        (G.rank_strict_mono _ _ (tp_spec G X Y (tp_iter_mem G X Y hv (m + 1)) huY).2.1)

lemma tp_cycle {v : V} (hv : v ∈ AY G X Y) {m : ℕ} (h : (tp G X Y)^[m + 1] v = v) : v ∈ Y := by
  by_contra hY
  have hlt := tp_rank_iter G X Y hv hY m
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- **Halen når `Y`.** -/
theorem tp_reaches : ∀ v ∈ AY G X Y, ∃ n, (tp G X Y)^[n] v ∈ Y := by
  have key : ∀ k, ∀ v ∈ AY G X Y, (Finset.univ : Finset V).sup G.rank - G.rank v = k →
      ∃ n, (tp G X Y)^[n] v ∈ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hk
      by_cases hY : v ∈ Y
      · exact ⟨0, hY⟩
      · obtain ⟨hw, e, -⟩ := tp_spec G X Y hv hY
        have hlt := G.rank_strict_mono v _ e
        have hle : G.rank (tp G X Y v) ≤ (Finset.univ : Finset V).sup G.rank :=
          Finset.le_sup (Finset.mem_univ _)
        obtain ⟨n, hn⟩ := ih ((Finset.univ : Finset V).sup G.rank - G.rank (tp G X Y v))
          (by omega) _ hw rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  exact fun v hv => key _ v hv rfl

open Classical in
/-- `w` ligger på `tp`-stien fra `s`. -/
noncomputable def tI (s w : V) : ZMod 2 := if ∃ k, (tp G X Y)^[k] s = w then 1 else 0

lemma tp_pred_aux {s v w w' : V} (hs : s ∈ AY G X Y) {k k' : ℕ} (hk : k < k')
    (h1 : (tp G X Y)^[k] s = w) (h2 : (tp G X Y)^[k'] s = w')
    (hwv : tp G X Y w = v) (hw'v : tp G X Y w' = v) (hw' : w' ∉ Y) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hv : (tp G X Y)^[k + 1] s = v := by
    rw [Function.iterate_succ_apply', h1, hwv]
  have hw'm : (tp G X Y)^[m] v = w' := by
    rw [← hv, ← Function.iterate_add_apply, ← h2, show m + (k + 1) = k + m + 1 by omega]
  have hvA : v ∈ AY G X Y := by
    rw [← hv]
    exact tp_iter_mem G X Y hs (k + 1)
  have hcyc : (tp G X Y)^[m + 1] v = v := by
    rw [Function.iterate_succ_apply', hw'm, hw'v]
  have hY := tp_cycle G X Y hvA hcyc
  apply hw'
  rw [← hw'm, iter_tpY G X Y hY m]
  exact hY

/-- **Rekursjonen for `tI`.** -/
theorem tI_rec {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s v : V}
    (hs : s ∈ AY G X Y) (hsU : s ∉ U) :
    tI G X Y s v = (if v = s then 1 else 0) +
      ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v), tI G X Y s w := by
  classical
  have huniq : ∀ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      ∀ w' ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      (∃ k, (tp G X Y)^[k] s = w) → (∃ k, (tp G X Y)^[k] s = w') → w = w' := by
    intro w hw w' hw' h h'
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, -, hw'Y, hw'v⟩ := Finset.mem_filter.mp hw'
    obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := h'
    rcases lt_trichotomy k k' with hl | he | hl
    · exact (tp_pred_aux G X Y hs hl hk hk' hwv hw'v hw'Y).elim
    · subst he
      exact hk.symm.trans hk'
    · exact (tp_pred_aux G X Y hs hl hk' hk hw'v hwv hwY).elim
  by_cases hvs : v = s
  · have hr0 : ∃ k, (tp G X Y)^[k] s = v := ⟨0, hvs.symm⟩
    have h1 : tI G X Y s v = 1 := by
      unfold tI
      rw [if_pos hr0]
    rw [h1, if_pos hvs, Finset.sum_eq_zero, add_zero]
    intro w hw
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    have hcyc : (tp G X Y)^[k + 1] s = s := by
      rw [Function.iterate_succ_apply', hk, hwv, hvs]
    have hY := tp_cycle G X Y hs hcyc
    apply hwY
    rw [← hk, iter_tpY G X Y hY k]
    exact hY
  · rw [if_neg hvs, zero_add]
    by_cases hr : ∃ k, (tp G X Y)^[k] s = v
    · have hex : ∃ k, (tp G X Y)^[k] s = v := hr
      obtain ⟨k, hk⟩ := hr
      have hk0 := Nat.find_spec hex
      have hne0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0] at hk0
        exact hvs hk0.symm
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjv : (tp G X Y)^[j + 1] s = v := by
        rw [← hj]
        exact hk0
      have hwv : tp G X Y ((tp G X Y)^[j] s) = v := by
        have h' := hjv
        rw [Function.iterate_succ_apply'] at h'
        exact h'
      have hwY : (tp G X Y)^[j] s ∉ Y := by
        intro hY
        rw [tp_Y G X Y hY] at hwv
        exact Nat.find_min hex (show j < Nat.find hex by omega) hwv
      have hwmem : (tp G X Y)^[j] s ∈
          (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v) :=
        Finset.mem_filter.mpr ⟨tp_iter_mem G X Y hs j, tp_iter_obs G X Y hroot hs hsU j, hwY, hwv⟩
      have hwr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[j] s := ⟨j, rfl⟩
      unfold tI
      rw [if_pos hex, Finset.sum_eq_single ((tp G X Y)^[j] s)]
      · rw [if_pos hwr]
      · intro b hb hbw
        rw [if_neg]
        intro hbr
        exact hbw (huniq b hb _ hwmem hbr hwr)
      · intro hn
        exact absurd hwmem hn
    · unfold tI
      rw [if_neg hr, Finset.sum_eq_zero]
      intro w hw
      rw [if_neg]
      rintro ⟨k, hk⟩
      obtain ⟨-, -, -, hwv⟩ := Finset.mem_filter.mp hw
      apply hr
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hwv]⟩

/-- **Stien når nøyaktig én node i `Y`.** -/
theorem sum_tI_Y {s : V} (hs : s ∈ AY G X Y) : ∑ y ∈ Y, tI G X Y s y = 1 := by
  obtain ⟨n, hn⟩ := tp_reaches G X Y s hs
  have hr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[n] s := ⟨n, rfl⟩
  rw [Finset.sum_eq_single ((tp G X Y)^[n] s)]
  · unfold tI
    rw [if_pos hr]
  · intro b hb hbn
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    apply hbn
    rcases le_total k n with hl | hl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [add_comm, Function.iterate_add_apply, hk, iter_tpY G X Y hb m]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [← hk, add_comm, Function.iterate_add_apply, iter_tpY G X Y hn m]
  · intro hn'
    exact absurd hn hn'

end tail

end Hedge

#print axioms Hedge.tp_spec
#print axioms Hedge.tp_reaches
#print axioms Hedge.tI_rec
#print axioms Hedge.sum_tI_Y

/-! ## Runde 79: H4, steg 2 — produktmodellene

Verditypen `Val2 U v = Val U v × ZMod 2`. Første koordinat `a` følger paritetsmodellen
`M G U F F' D two` (kjernen leser bare foreldrenes `a`), andre koordinat er
`b_v = [v ∈ RO] a_v + Σ_{w ∈ TC v} b_w + η_v` med `η_v ~ noise`, der `TC v` er de observerte
`w ∈ AY \ Y` med `tp w = v`. `kern2_apply`: kjernen er `kern … a · noise (b + bIn)`.
`kfac2_eq`: faktoren i `MP` er faktoren i `M` på `fstA s` ganget med `noise (etaS s v)`;
`joint2_eq`: det samme for fellesfordelingen. `etaS_eq`: uten foreldrevakter (`TC v` er
foreldre til `v`, `tc_edge`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_bab : ∀ a b : ZMod 2, b + (a + b) = a := by decide

/-- Verditypen for produktmodellene. -/
abbrev Val2 (U : Finset V) (v : V) : Type := Val U v × ZMod 2

section prod

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V) (two : Bool)

/-- Haleforeldrene til `v`. -/
noncomputable def TC (v : V) : Finset V :=
  (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v)

lemma tc_edge {v w : V} (hw : w ∈ TC G U X Y v) : G.edge w v := by
  obtain ⟨hwA, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
  have h := (tp_spec G X Y hwA hwY).2.1
  rw [hwv] at h
  exact h

/-- Inngangen til `b` i `v`. -/
noncomputable def bIn (v : V) (a : Val U v) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) :
    ZMod 2 :=
  (if v ∈ RO G U F then rd a 0 else 0) +
    ∑ w ∈ TC G U X Y v, (if h : w ∈ G.parents v then (pa ⟨w, h⟩).2 else 0)

/-- Kjernen. -/
noncomputable def kern2 (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) :
    PMF (Val2 U v) :=
  (kern G U F F' D two v (fun u => (pa u).1)).bind
    (fun a => noise.map (fun η => (a, bIn G U F X Y v a pa + η)))

/-- **Produktmodellen.** -/
noncomputable def MP : G.CausalModel (Val2 U) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := kern2 G U F F' D X Y two

lemma kern2_apply (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) (z : Val2 U v) :
    kern2 G U F F' D X Y two v pa z =
      kern G U F F' D two v (fun u => (pa u).1) z.1 * noise (z.2 + bIn G U F X Y v z.1 pa) := by
  unfold kern2
  rw [PMF.bind_apply, tsum_eq_single z.1]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single (z.2 + bIn G U F X Y v z.1 pa)]
    · rw [if_pos]
      exact Prod.ext rfl (zmod2_bab _ _).symm
    · intro η hη
      rw [if_neg]
      intro h
      apply hη
      have h2 := congrArg Prod.snd h
      exact (zmod2_solve _ _ _).mp h2
  · intro a ha
    have h0 : (noise.map (fun η => (a, bIn G U F X Y v a pa + η))) z = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro η
      rw [if_neg]
      intro h
      exact ha (congrArg Prod.fst h).symm
    rw [h0, mul_zero]

/-- Første koordinat. -/
def fstA (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u => (s u).1

/-- Støyleddet i `v`. -/
noncomputable def etaS (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  (s ⟨v, Finset.mem_univ v⟩).2 +
    ((if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
      ∑ w ∈ TC G U X Y v,
        (if h : w ∈ G.parents v then (s ⟨w, Finset.mem_univ w⟩).2 else 0))

/-- **Faktoriseringen.** -/
theorem kfac2_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    kfac (MP G U F F' D X Y two) Finset.univ s v =
      kfac (M G U F F' D two) Finset.univ (fstA U s) v * noise (etaS G U F X Y s v) := by
  have h1 : kfac (MP G U F F' D X Y two) Finset.univ s v =
      kern2 G U F F' D X Y two v (s.restrict (Finset.subset_univ _)) (s ⟨v, Finset.mem_univ v⟩) :=
    DoAudit.kfac_univ _ _ _
  have h2 : kfac (M G U F F' D two) Finset.univ (fstA U s) v =
      kern G U F F' D two v ((fstA U s).restrict (Finset.subset_univ _))
        ((fstA U s) ⟨v, Finset.mem_univ v⟩) :=
    DoAudit.kfac_univ _ _ _
  rw [h1, h2, kern2_apply]
  rfl

theorem joint2_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (MP G U F F' D X Y two).fullJoint s =
      (M G U F F' D two).fullJoint (fstA U s) * ∏ v, noise (etaS G U F X Y s v) := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun v _ => kfac2_eq G U F F' D X Y two s v)

/-- `etaS` uten foreldrevakter. -/
lemma etaS_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y s v = (s ⟨v, Finset.mem_univ v⟩).2 +
      ((if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
        ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2) := by
  unfold etaS
  congr 2
  apply Finset.sum_congr rfl
  intro w hw
  rw [dif_pos (mem_parents_iff.mpr (tc_edge G U X Y hw))]

end prod

end PM
end Hedge

#print axioms Hedge.PM.kern2_apply
#print axioms Hedge.PM.kfac2_eq
#print axioms Hedge.PM.joint2_eq

/-! ## Runde 80: H4, steg 3 og 4 — lik observert fordeling og positivitet

`phiS2`: involusjonen fra H3 på første koordinat, andre koordinat uendret. Den holder de
observerte verdiene (`phiS2_restrict`) og endrer ikke støyleddene (`etaS_phiS2`: de leser
bare `b` og de observerte `a`-verdiene i `RO`), så `joint2_eq` og `joint_phiS` gir
`joint2_phiS2`, og `marg2_eq`: `MP false` og `MP true` har samme observerte fordeling.
`pos2`: hver observert tilordning har positiv sannsynlighet i `MP false` (første koordinat
fra `pos_M1`, og hver støyfaktor er positiv). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section obs2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

lemma phiS_obs (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (t : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U) :
    phiS G U F F' D t ⟨v, Finset.mem_univ v⟩ = t ⟨v, Finset.mem_univ v⟩ := by
  unfold phiS
  exact sh_obs G U F F' D hD hFF' _ t hv

/-- Involusjonen på produktmodellene. -/
noncomputable def phiS2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (phiS G U F F' D (fstA U s) u, (s u).2)

lemma fstA_phiS2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (phiS2 G U F F' D s) = phiS G U F F' D (fstA U s) := rfl

lemma phiS2_invol (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    phiS2 G U F F' D (phiS2 G U F F' D s) = s := by
  funext u
  show (phiS G U F F' D (fstA U (phiS2 G U F F' D s)) u, (s u).2) = s u
  rw [fstA_phiS2, phiS_invol G U F F' D hD hFF']
  rfl

lemma phiS2_restrict (hD : Good G U F F' D) (hFF' : F ⊆ F') {O : Finset V}
    (hO : ∀ v ∈ O, v ∉ U) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (phiS2 G U F F' D s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O) := by
  funext ⟨v, hv⟩
  show (phiS G U F F' D (fstA U s) ⟨v, Finset.mem_univ v⟩, (s ⟨v, Finset.mem_univ v⟩).2) =
    s ⟨v, Finset.mem_univ v⟩
  rw [phiS_obs G U F F' D hD hFF' _ (hO v hv)]
  rfl

lemma etaS_phiS2 (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y (phiS2 G U F F' D s) v = etaS G U F X Y s v := by
  have e1 : ∀ w, (phiS2 G U F F' D s ⟨w, Finset.mem_univ w⟩).2 = (s ⟨w, Finset.mem_univ w⟩).2 :=
    fun w => rfl
  have e2 : (if v ∈ RO G U F then rd (phiS2 G U F F' D s ⟨v, Finset.mem_univ v⟩).1 0 else 0) =
      (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) := by
    by_cases hv : v ∈ RO G U F
    · rw [if_pos hv, if_pos hv]
      show rd (phiS G U F F' D (fstA U s) ⟨v, Finset.mem_univ v⟩) 0 = _
      rw [phiS_obs G U F F' D hD hFF' _ (Finset.mem_filter.mp hv).2]
      rfl
    · rw [if_neg hv, if_neg hv]
  unfold etaS
  simp only [e1, e2]

/-- **Like fellesfordelinger etter involusjonen.** -/
theorem joint2_phiS2 {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (MP G U F F' D X Y true).fullJoint (phiS2 G U F F' D s) =
      (MP G U F F' D X Y false).fullJoint s := by
  rw [joint2_eq, joint2_eq, fstA_phiS2, joint_phiS G U F F' D hH hD hroot T]
  congr 1
  exact Finset.prod_congr rfl (fun v _ => by rw [etaS_phiS2 G U F F' D X Y hD hH.sub s v])

/-- **Steg 3: samme observerte fordeling.** -/
theorem marg2_eq {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    (MP G U F F' D X Y false).marginal O = (MP G U F F' D X Y true).marginal O :=
  marginal_eq_of_invol _ _ O (phiS2 G U F F' D) (phiS2_invol G U F F' D hD hH.sub)
    (phiS2_restrict G U F F' D hD hH.sub hO) (joint2_phiS2 G U F F' D X Y hH hD hroot T)

/-- **Steg 4: positivitet.** -/
theorem pos2 {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    {d : V → ℕ} (T' : ParTree (OF U F') D.ρ D.par d) {O : Finset V} (hO : ∀ v ∈ O, v ∉ U)
    (a : Assignment (α := Val2 U) O) :
    (MP G U F F' D X Y false).marginal O a ≠ 0 := by
  let aA : Assignment (α := Val U) O := fun v => (a v).1
  have hA := pos_M1 G U F F' D hH hD T' hO aA
  have hmem : aA ∈ ((M G U F F' D false).marginal O).support :=
    (PMF.mem_support_iff _ _).mpr hA
  unfold CausalModel.marginal at hmem
  rw [PMF.mem_support_map_iff] at hmem
  obtain ⟨sA, hsA, hres⟩ := hmem
  let s : Assignment (α := Val2 U) (Finset.univ : Finset V) :=
    fun u => (sA u, if h : u.1 ∈ O then (a ⟨u.1, h⟩).2 else 0)
  have hsupp : (MP G U F F' D X Y false).fullJoint s ≠ 0 := by
    rw [joint2_eq]
    refine mul_ne_zero ((PMF.mem_support_iff _ _).mp hsA) ?_
    rw [Finset.prod_ne_zero_iff]
    exact fun v _ => noise_pos _
  have hrs : s.restrict (Finset.subset_univ O) = a := by
    funext ⟨v, hv⟩
    have h1 : sA ⟨v, Finset.mem_univ v⟩ = (a ⟨v, hv⟩).1 := congrFun hres ⟨v, hv⟩
    show (sA ⟨v, Finset.mem_univ v⟩, if h : v ∈ O then (a ⟨v, h⟩).2 else 0) = a ⟨v, hv⟩
    rw [h1, dif_pos hv]
  intro h0
  have hmem2 : a ∈ ((MP G U F F' D X Y false).marginal O).support := by
    unfold CausalModel.marginal
    rw [PMF.mem_support_map_iff]
    exact ⟨s, (PMF.mem_support_iff _ _).mpr hsupp, hrs⟩
  exact (PMF.mem_support_iff _ _).mp hmem2 h0

end obs2

end PM
end Hedge

#print axioms Hedge.PM.marg2_eq
#print axioms Hedge.PM.pos2

/-! ## Runde 81: H4, steg 5 — `MP false` under `do(x)`: `P(Yb = 1) = P(Yb = 0)`

`betaC c w = Σ_{r ∈ RO} phiC c r · tI r w`: hvor ψ må snu `b` (langs halene fra røttene ψ snur).
`betaC_rec`: `betaC c v = [v ∈ RO] phiC c v + Σ_{TC v} betaC c w` (fra `tI_rec`); i latente og i
`X` er den 0. `psi2 c`: ψ på første koordinat, `b + betaC` på andre; involusjon. `etaS_psi2`:
støyleddene endres ikke. `kfac_psi2_do`, `joint_psi2`: fellesfordelingen under `do(x)` er
invariant. `Yb`: pariteten til `b` over `Y`; `Yb_psi2`: ψ2 snur `Yb` (hver hale når nøyaktig én
node i `Y`, og `Σ_{RO} phiC c = 1`). `Yb_half`: `P(Yb = 1) = P(Yb = 0)` under `do(x)` i `MP false`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_l5 : ∀ a b c d e : ZMod 2, a + (b + c) + (d + b + (e + c)) = a + (d + e) := by decide

lemma zmod2_l3 : ∀ a c e : ZMod 2, a + (0 + c) + (0 + (e + c)) = a + (0 + e) := by decide

section psi2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- Hvor ψ snur `b`. -/
noncomputable def betaC (c w : V) : ZMod 2 :=
  ∑ r ∈ RO G U F, phiC G F F' D X c r * tI G X Y r w

/-- **ψ på produktmodellene.** -/
noncomputable def psi2 (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (psiS G U F F' D X c (fstA U s) u, (s u).2 + betaC G U F F' D X Y c u.1)

lemma fstA_psi2 (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (psi2 G U F F' D X Y c s) = psiS G U F F' D X c (fstA U s) := rfl

lemma psi2_invol (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    psi2 G U F F' D X Y c (psi2 G U F F' D X Y c s) = s := by
  funext u
  show (psiS G U F F' D X c (fstA U (psi2 G U F F' D X Y c s)) u,
    (s u).2 + betaC G U F F' D X Y c u.1 + betaC G U F F' D X Y c u.1) = s u
  rw [fstA_psi2, psiS_invol, add_assoc, zmod2_add_self, add_zero]
  rfl

lemma betaC_rec (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (c v : V) :
    betaC G U F F' D X Y c v = (if v ∈ RO G U F then phiC G F F' D X c v else 0) +
      ∑ w ∈ TC G U X Y v, betaC G U F F' D X Y c w := by
  unfold betaC TC
  have hrw : ∀ r ∈ RO G U F, phiC G F F' D X c r * tI G X Y r v =
      (if v = r then phiC G F F' D X c r else 0) +
        ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
          phiC G F F' D X c r * tI G X Y r w := by
    intro r hr
    have hrA : r ∈ AY G X Y := hH.anc (Finset.mem_filter.mp hr).1
    rw [tI_rec G X Y hroot hrA (Finset.mem_filter.mp hr).2, mul_add, Finset.mul_sum]
    congr 1
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_comm]

lemma betaC_X (hH : IsHedge G U X Y F F') (c : V) {v : V} (hv : v ∈ X) :
    betaC G U F F' D X Y c v = 0 := by
  unfold betaC
  apply Finset.sum_eq_zero
  intro r hr
  have hrF := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hrA : r ∈ AY G X Y := hH.anc (Finset.mem_filter.mp hr).1
  have h0 : tI G X Y r v = 0 := by
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    apply tp_iter_notX G X Y hrA (hH.out r hrF) k
    rw [hk]
    exact hv
  rw [h0, mul_zero]

lemma psiS_X (hD : Good G U F F' D) (hXU : ∀ v ∈ X, v ∉ U) {c : V} (hc : c ∈ F') (hcU : c ∉ U)
    (hcρ : c ≠ D.ρ) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ X) :
    psiS G U F F' D X c t ⟨v, Finset.mem_univ v⟩ = t ⟨v, Finset.mem_univ v⟩ := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  have h0 : phiC G F F' D X c v = 0 := by
    unfold phiC
    rw [nrI_X G F F' X hv, nrI_X G F F' X hv, add_zero]
  unfold psiS
  rw [flipO_obs U _ _ (hXU v hv), obs_shE U D {c} hE _ t (hXU v hv), h0]
  funext i
  exact add_zero _

/-- **Støyleddene endres ikke av ψ2.** -/
theorem etaS_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y (psi2 G U F F' D X Y c s) v = etaS G U F X Y s v := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hb : ∀ w, (psi2 G U F F' D X Y c s ⟨w, Finset.mem_univ w⟩).2 =
      (s ⟨w, Finset.mem_univ w⟩).2 + betaC G U F F' D X Y c w := fun w => rfl
  rw [etaS_eq, etaS_eq]
  simp only [hb, Finset.sum_add_distrib]
  rw [betaC_rec G U F F' D X Y hH hroot c v]
  by_cases hvRO : v ∈ RO G U F
  · have ha : rd (psi2 G U F F' D X Y c s ⟨v, Finset.mem_univ v⟩).1 0 =
        rd (s ⟨v, Finset.mem_univ v⟩).1 0 + phiC G F F' D X c v :=
      ov_psi G U F F' D X c hcl (fstA U s) (Finset.mem_filter.mp hvRO).2
    simp only [if_pos hvRO]
    rw [ha]
    exact zmod2_l5 _ _ _ _ _
  · simp only [if_neg hvRO]
    exact zmod2_l3 _ _ _

/-- Hver faktor under `do(x)` bevares. -/
theorem kfac_psi2_do (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val2 U) X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (MP G U F F' D X Y false) X x) Finset.univ (psi2 G U F F' D X Y c s) v =
      kfac (doModel (MP G U F F' D X Y false) X x) Finset.univ s v := by
  rw [kfac_doModel, kfac_doModel]
  by_cases hv : v ∈ X
  · rw [dif_pos hv, dif_pos hv]
    have hpv : psi2 G U F F' D X Y c s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
      show (psiS G U F F' D X c (fstA U s) ⟨v, Finset.mem_univ v⟩,
        (s ⟨v, Finset.mem_univ v⟩).2 + betaC G U F F' D X Y c v) = s ⟨v, Finset.mem_univ v⟩
      rw [psiS_X G U F F' D X hD hXU hc hcU hcρ _ hv, betaC_X G U F F' D X Y hH c hv, add_zero]
      rfl
    rw [hpv]
  · rw [dif_neg hv, dif_neg hv, kfac2_eq, kfac2_eq, etaS_psi2 G U F F' D X Y hH hD hroot hc hcU hcρ]
    congr 1
    have h := kfac_psi_do G U F F' D X hH hD hroot hXU hc hcU hcρ (fun w => (x w).1) (fstA U s) v
    rw [kfac_doModel, kfac_doModel, dif_neg hv, dif_neg hv] at h
    exact h

theorem joint_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val2 U) X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (doModel (MP G U F F' D X Y false) X x).fullJoint (psi2 G U F F' D X Y c s) =
      (doModel (MP G U F F' D X Y false) X x).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  exact Finset.prod_congr rfl
    (fun v _ => kfac_psi2_do G U F F' D X Y hH hD hroot hXU hc hcU hcρ x s v)

/-- Pariteten til `b` over `Y`. -/
noncomputable def Yb (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) : ZMod 2 :=
  ∑ y ∈ Y, (s ⟨y, Finset.mem_univ y⟩).2

lemma sum_phiC_RO (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r)) :
    ∑ r ∈ RO G U F, phiC G F F' D X c r = 1 := by
  have hcl := (hD.lat c hc hcU hcρ).1
  let t : Assignment (α := Val U) (Finset.univ : Finset V) := fun _ => 0
  have h1 := parR_psi G U F F' D X hH hD hroot hc hcU hcρ hA t
  have h2 : parR G U F (psiS G U F F' D X c t) = parR G U F t + ∑ r ∈ RO G U F, phiC G F F' D X c r := by
    unfold parR RO
    rw [Finset.sum_congr rfl (fun r hr => ov_psi G U F F' D X c hcl t (Finset.mem_filter.mp hr).2),
      Finset.sum_add_distrib]
  rw [h2] at h1
  exact add_left_cancel h1

/-- **ψ2 snur `Yb`.** -/
theorem Yb_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (psi2 G U F F' D X Y c s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (psi2 G U F F' D X Y c s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + betaC G U F F' D X Y c y) from rfl,
    Finset.sum_add_distrib]
  congr 1
  unfold betaC
  rw [Finset.sum_comm,
    Finset.sum_congr rfl (fun r hr => by
      rw [← Finset.mul_sum, sum_tI_Y G X Y (hH.anc (Finset.mem_filter.mp hr).1), mul_one])]
  exact sum_phiC_RO G U F F' D X Y hH hD hroot hc hcU hcρ hA

/-- **Steg 5: `P(Yb = 1) = P(Yb = 0)` under `do(x)` i `MP false`.** -/
theorem Yb_half (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) {d : V → ℕ}
    (T' : ParTree (OF U F') D.ρ D.par d) (x : Assignment (α := Val2 U) X) :
    ((doModel (MP G U F F' D X Y false) X x).fullJoint.map (Yb U Y)) 1 =
      ((doModel (MP G U F F' D X Y false) X x).fullJoint.map (Yb U Y)) 0 := by
  obtain ⟨c, hc, hcU, hcρ, hA⟩ := cross_edge G U F F' D X hH hD hXU T'
  exact map_flip_eq _ (psi2 G U F F' D X Y c) (Yb U Y) (psi2_invol G U F F' D X Y c)
    (joint_psi2 G U F F' D X Y hH hD hroot hXU hc hcU hcρ x)
    (Yb_psi2 G U F F' D X Y hH hD hroot hc hcU hcρ hA)

end psi2

end PM
end Hedge

#print axioms Hedge.PM.etaS_psi2
#print axioms Hedge.PM.Yb_half

/-! ## Runde 82: H4, steg 6a — skjevhetslemmaet

`pair_ratio`: en involusjon σ som holder `f` fast, snur `e` og tredobler vekten der `e = 1`,
gir `P(f = a, e = 0) = 3 · P(f = a, e = 1)`. `map_fst0` … `map_add1`: fordelingene av `f` og
`f + e` uttrykt ved de fire verdiene `P(f = a, e = b)`. `bias_step`: er `P(f = 0) ≠ P(f = 1)`,
er også `P(f + e = 0) ≠ P(f + e = 1)` (regnet i `ℝ`: `3A + B = 3B + A` gir `A = B`).
`bias_base`: er `f` konstant på støtten, er `P(f = 0) ≠ P(f = 1)`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

lemma zmod2_01 : (0 : ZMod 2) ≠ 1 := by decide

lemma zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- **Forholdet for paret `(f, e)`.** -/
theorem pair_ratio {β : Type*} (p : PMF β) (σ : β → β) (f e : β → ZMod 2)
    (hinv : ∀ s, σ (σ s) = s) (hf : ∀ s, f (σ s) = f s) (he : ∀ s, e (σ s) = e s + 1)
    (hp : ∀ s, e s = 1 → p (σ s) = 3 * p s) (a : ZMod 2) :
    (p.map (fun s => (f s, e s))) (a, 0) = 3 * (p.map (fun s => (f s, e s))) (a, 1) := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm σ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  first
    | simp only [Function.Involutive.coe_toPerm, hf, he]
    | simp only [hf, he]
  by_cases h1 : (a, (1 : ZMod 2)) = (f s, e s)
  · have he1 : e s = 1 := (congrArg Prod.snd h1).symm
    have ha : a = f s := congrArg Prod.fst h1
    have h0 : (a, (0 : ZMod 2)) = (f s, e s + 1) :=
      Prod.ext ha (by show (0 : ZMod 2) = e s + 1; rw [he1]; decide)
    rw [if_pos h0, if_pos h1, hp s he1]
  · have h0 : ¬ (a, (0 : ZMod 2)) = (f s, e s + 1) := by
      intro h
      have ha : a = f s := congrArg Prod.fst h
      have hb : (0 : ZMod 2) = e s + 1 := congrArg Prod.snd h
      exact h1 (Prod.ext ha ((zmod2_s0 _).mp hb))
    rw [if_neg h0, if_neg h1, mul_zero]

lemma map_fst0 (q : PMF (ZMod 2 × ZMod 2)) : (q.map Prod.fst) 0 = q (0, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01, if_pos rfl, if_pos rfl,
    if_neg zmod2_01, if_neg zmod2_01]
  ring

lemma map_fst1 (q : PMF (ZMod 2 × ZMod 2)) : (q.map Prod.fst) 1 = q (1, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01, if_neg zmod2_01.symm,
    if_neg zmod2_01.symm, if_pos rfl, if_pos rfl]
  ring

lemma map_add0 (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 0 = q (0, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01,
    if_pos (by decide : (0 : ZMod 2) = 0 + 0), if_neg (by decide : ¬ (0 : ZMod 2) = 0 + 1),
    if_neg (by decide : ¬ (0 : ZMod 2) = 1 + 0), if_pos (by decide : (0 : ZMod 2) = 1 + 1)]
  ring

lemma map_add1 (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 1 = q (1, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01,
    if_neg (by decide : ¬ (1 : ZMod 2) = 0 + 0), if_pos (by decide : (1 : ZMod 2) = 0 + 1),
    if_pos (by decide : (1 : ZMod 2) = 1 + 0), if_neg (by decide : ¬ (1 : ZMod 2) = 1 + 1)]
  ring

/-- **Skjevhetslemmaet.** -/
theorem bias_step {β : Type*} (p : PMF β) (σ : β → β) (f e : β → ZMod 2)
    (hinv : ∀ s, σ (σ s) = s) (hf : ∀ s, f (σ s) = f s) (he : ∀ s, e (σ s) = e s + 1)
    (hp : ∀ s, e s = 1 → p (σ s) = 3 * p s) (hb : (p.map f) 0 ≠ (p.map f) 1) :
    (p.map (fun s => f s + e s)) 0 ≠ (p.map (fun s => f s + e s)) 1 := by
  have hmf : p.map f = (p.map (fun s => (f s, e s))).map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  have hms : p.map (fun s => f s + e s) =
      (p.map (fun s => (f s, e s))).map (fun z => z.1 + z.2) := by
    rw [PMF.map_comp]
    rfl
  have r0 := pair_ratio p σ f e hinv hf he hp 0
  have r1 := pair_ratio p σ f e hinv hf he hp 1
  rw [hmf, map_fst0, map_fst1, r0, r1] at hb
  rw [hms, map_add0, map_add1, r0, r1]
  have hA : (p.map (fun s => (f s, e s))) (0, 1) ≠ ⊤ := PMF.apply_ne_top _ _
  have hB : (p.map (fun s => (f s, e s))) (1, 1) ≠ ⊤ := PMF.apply_ne_top _ _
  have h3A : 3 * (p.map (fun s => (f s, e s))) (0, 1) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hA
  have h3B : 3 * (p.map (fun s => (f s, e s))) (1, 1) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
  intro h
  apply hb
  have hAB : (p.map (fun s => (f s, e s))) (0, 1) = (p.map (fun s => (f s, e s))) (1, 1) := by
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add h3A hB, ENNReal.toReal_add h3B hA, ENNReal.toReal_mul,
      ENNReal.toReal_mul] at h'
    have h'' : ENNReal.toReal ((p.map (fun s => (f s, e s))) (0, 1)) =
        ENNReal.toReal ((p.map (fun s => (f s, e s))) (1, 1)) := by
      have h3 : ENNReal.toReal (3 : ENNReal) = 3 := by simp
      rw [h3] at h'
      linarith
    first
      | exact (ENNReal.toReal_eq_toReal_iff' hA hB).mp h''
      | exact (ENNReal.toReal_eq_toReal hA hB).mp h''
  rw [hAB]

/-- **Grunntilfellet:** er `f` konstant på støtten, er `P(f = 0) ≠ P(f = 1)`. -/
theorem bias_base {β : Type*} (p : PMF β) (f : β → ZMod 2) (c : ZMod 2)
    (h : ∀ s, p s ≠ 0 → f s = c) : (p.map f) 0 ≠ (p.map f) 1 := by
  rw [map_congr_supp p f (fun _ => c) h]
  have hc : p.map (fun _ => c) = PMF.pure c := PMF.map_const p c
  rw [hc, PMF.pure_apply, PMF.pure_apply]
  rcases zmod2_cases c with rfl | rfl
  · rw [if_pos rfl, if_neg zmod2_01.symm]
    exact one_ne_zero
  · rw [if_neg zmod2_01, if_pos rfl]
    exact zero_ne_one

end Hedge

#print axioms Hedge.pair_ratio
#print axioms Hedge.bias_step
#print axioms Hedge.bias_base

/-! ## Runde 83: H4, steg 6b — teleskopering for `Yb`

`AO` = de observerte nodene i `AY` utenfor `X` (der støyen teller), `AXo` = de i `X`.
`Yb_tele`: for hver tilordning er `Yb = parR a + Σ_{AO} η + Σ_{AXo} b` (hver `w ∈ AY \ Y` er
halebarn av nøyaktig én node i `AO`, `fiber_sum`). `fS_const`: på støtten til `do(x)` i
`MP true` er `b` lik `x` i `X` og `parR = gS` (`parR_g`), så `Yb + gS + Σ_{AO} η` er en
konstant som bare avhenger av `x`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_tel : ∀ yb m p q : ZMod 2, yb = p + (yb + m + (p + (m + q))) + q := by decide

lemma zmod2_geq : ∀ g e q : ZMod 2, g + e + q + g + e = q := by decide

section tele3

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- De observerte nodene i `AY` utenfor `X`. -/
noncomputable def AO : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∉ X)

/-- De observerte nodene i `AY` i `X`. -/
noncomputable def AXo : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∈ X)

/-- **Teleskoperingsidentiteten for `Yb`.** -/
theorem Yb_tele (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y s = parR G U F (fstA U s) + ∑ v ∈ AO G U X Y, etaS G U F X Y s v +
      ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 := by
  have hTC : ∀ v, TC G U X Y v = ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter
      (fun w => tp G X Y w = v) := by
    intro v
    ext w
    simp only [TC, Finset.mem_filter]
    tauto
  have hS : ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter
      (fun w => tp G X Y w ∈ AO G U X Y) = (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y) := by
    apply Finset.filter_true_of_mem
    intro w hw
    obtain ⟨hwA, -, hwY⟩ := Finset.mem_filter.mp hw
    obtain ⟨h1, h2, h3⟩ := tp_spec G X Y hwA hwY
    exact Finset.mem_filter.mpr ⟨h1, fun hU => hroot _ hU _ h2, h3⟩
  have hRO : (AO G U X Y).filter (fun v => v ∈ RO G U F) = RO G U F := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hr
      have hrF := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      exact ⟨Finset.mem_filter.mpr ⟨hH.anc (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2,
        hH.out r hrF⟩, hr⟩
  have hYA : (AO G U X Y).filter (fun v => v ∈ Y) = Y := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hy
      exact ⟨Finset.mem_filter.mpr ⟨anc_sup (cutIn G X) Finset.univ Y hy, hYU y hy, hYX y hy⟩, hy⟩
  have hmid : (AO G U X Y).filter (fun v => v ∉ Y) =
      ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter (fun v => v ∉ X) := by
    ext v
    simp only [AO, Finset.mem_filter]
    tauto
  have hXo : ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter (fun v => ¬ v ∉ X) =
      AXo G U X Y := by
    ext v
    simp only [AXo, Finset.mem_filter, not_not]
    constructor
    · rintro ⟨⟨hA, hU, -⟩, hX⟩
      exact ⟨hA, hU, hX⟩
    · rintro ⟨hA, hU, hX⟩
      exact ⟨⟨hA, hU, fun hY => hYX v hY hX⟩, hX⟩
  have h1 : ∑ v ∈ AO G U X Y, etaS G U F X Y s v =
      ∑ v ∈ AO G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 +
        (∑ v ∈ AO G U X Y, (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
          ∑ v ∈ AO G U X Y, ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2) := by
    rw [Finset.sum_congr rfl (fun v _ => etaS_eq G U F X Y s v), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  have h2 : ∑ v ∈ AO G U X Y, (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) =
      parR G U F (fstA U s) := by
    rw [← Finset.sum_filter, hRO]
    rfl
  have h3 : ∑ v ∈ AO G U X Y, ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2 =
      ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y), (s ⟨w, Finset.mem_univ w⟩).2 := by
    simp only [hTC]
    rw [fiber_sum (AO G U X Y) _ (tp G X Y) (fun w => (s ⟨w, Finset.mem_univ w⟩).2), hS]
  have h4 : ∑ v ∈ AO G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 =
      ∑ v ∈ Y, (s ⟨v, Finset.mem_univ v⟩).2 +
        ∑ v ∈ (AO G U X Y).filter (fun v => v ∉ Y), (s ⟨v, Finset.mem_univ v⟩).2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (AO G U X Y) (fun v => v ∈ Y), hYA]
  have h5 : ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y), (s ⟨w, Finset.mem_univ w⟩).2 =
      ∑ v ∈ (AO G U X Y).filter (fun v => v ∉ Y), (s ⟨v, Finset.mem_univ v⟩).2 +
        ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 := by
    rw [← Finset.sum_filter_add_sum_filter_not ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y))
      (fun v => v ∉ X), ← hmid, hXo]
  rw [h1, h2, h3, h4, h5]
  unfold Yb
  exact zmod2_tel _ _ _ _

/-- **På støtten er `Yb + gS + Σ_{AO} η` konstant.** -/
theorem fS_const (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    (hs : (doModel (MP G U F F' D X Y true) X x).fullJoint s ≠ 0) :
    Yb U Y s + gS G U F F' D (fstA U s) + ∑ v ∈ AO G U X Y, etaS G U F X Y s v =
      ∑ v ∈ AXo G U X Y, (if h : v ∈ X then (x ⟨v, h⟩).2 else 0) := by
  rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff] at hs
  have hX : ∀ v (hv : v ∈ X), s ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩ := by
    intro v hv
    have h := hs v (Finset.mem_univ v)
    rw [kfac_doModel, dif_pos hv] at h
    by_contra hne
    exact h (if_neg hne)
  have hsA : (doModel (M G U F F' D true) X (fun w => (x w).1)).fullJoint (fstA U s) ≠ 0 := by
    rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff]
    intro v _
    rw [kfac_doModel]
    by_cases hv : v ∈ X
    · rw [dif_pos hv, if_pos]
      · exact one_ne_zero
      · exact congrArg Prod.fst (hX v hv)
    · rw [dif_neg hv]
      have h := hs v (Finset.mem_univ v)
      rw [kfac_doModel, dif_neg hv, kfac2_eq] at h
      exact left_ne_zero_of_mul h
  have hpar := parR_g G U F F' D hH hD hroot (fun w => (x w).1) (fstA U s) hsA
  have hq : ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 =
      ∑ v ∈ AXo G U X Y, (if h : v ∈ X then (x ⟨v, h⟩).2 else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvX := (Finset.mem_filter.mp hv).2.2
    rw [dif_pos hvX, hX v hvX]
  rw [Yb_tele G U F F' X Y hH hroot hYU hYX s, hpar, hq]
  exact zmod2_geq _ _ _

end tele3

end PM
end Hedge

#print axioms Hedge.PM.Yb_tele
#print axioms Hedge.PM.fS_const

/-! ## Runde 84: H4, steg 6b — involusjonene σ_v og τ′

`sig v`: snu `b` langs halen fra `v` (`v ∈ AO`). Etter `tI_rec` endrer det bare støyleddet i `v`
(`etaS_sig`), snur `Yb` (`Yb_sig`) og tredobler vekten under `do(x)` der `η_v = 1`
(`joint_sig`). `tau2`: snu `a` i `r0` (`tauS`) og `b` langs halen fra `r0`; støyleddene står
(`etaS_tau2`), `Yb` og `gS` snus, og vekten tredobles der `gS = 1` (`joint_tau2`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_s4 : ∀ a d c i e : ZMod 2, a + (d + c) + (i + (e + c)) = a + (i + e) + d := by decide

lemma zmod2_t1 : ∀ a c d e : ZMod 2, a + (1 + c) + (d + 1 + (e + c)) = a + (d + e) := by decide

lemma zmod2_t0 : ∀ a c i e : ZMod 2, a + (0 + c) + (i + (e + c)) = a + (i + e) := by decide

section sigtau

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

lemma tI_X {v : V} (hv : v ∈ AY G X Y) (hvX : v ∉ X) {u : V} (hu : u ∈ X) : tI G X Y v u = 0 := by
  unfold tI
  rw [if_neg]
  rintro ⟨k, hk⟩
  apply tp_iter_notX G X Y hv hvX k
  rw [hk]
  exact hu

/-- Snu `b` langs halen fra `v`. -/
noncomputable def sig (v : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => ((s u).1, (s u).2 + tI G X Y v u.1)

lemma sig_invol (v : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    sig G U X Y v (sig G U X Y v s) = s := by
  funext u
  exact Prod.ext rfl (by
    show (s u).2 + tI G X Y v u.1 + tI G X Y v u.1 = (s u).2
    rw [add_assoc, zmod2_add_self, add_zero])

lemma etaS_sig (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V} (hv : v ∈ AY G X Y) (hvU : v ∉ U)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (u : V) :
    etaS G U F X Y (sig G U X Y v s) u = etaS G U F X Y s u + (if u = v then 1 else 0) := by
  have ha : ∀ w, (sig G U X Y v s ⟨w, Finset.mem_univ w⟩).1 = (s ⟨w, Finset.mem_univ w⟩).1 :=
    fun w => rfl
  have hb : ∀ w, (sig G U X Y v s ⟨w, Finset.mem_univ w⟩).2 =
      (s ⟨w, Finset.mem_univ w⟩).2 + tI G X Y v w := fun w => rfl
  rw [etaS_eq, etaS_eq]
  simp only [ha, hb, Finset.sum_add_distrib]
  rw [tI_rec G X Y hroot (s := v) (v := u) hv hvU]
  unfold TC
  exact zmod2_s4 _ _ _ _ _

lemma Yb_sig {v : V} (hv : v ∈ AY G X Y) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (sig G U X Y v s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (sig G U X Y v s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + tI G X Y v y) from rfl,
    Finset.sum_add_distrib, sum_tI_Y G X Y hv]

lemma kfac_sig_ne (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V} (hv : v ∈ AO G U X Y)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    {u : V} (huv : u ≠ v) :
    kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ (sig G U X Y v s) u =
      kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ s u := by
  obtain ⟨hvA, hvU, hvX⟩ := Finset.mem_filter.mp hv
  rw [kfac_doModel, kfac_doModel]
  by_cases hu : u ∈ X
  · rw [dif_pos hu, dif_pos hu]
    have hsu : sig G U X Y v s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ :=
      Prod.ext rfl (by
        show (s ⟨u, Finset.mem_univ u⟩).2 + tI G X Y v u = _
        rw [tI_X G X Y hvA hvX hu, add_zero])
    rw [hsu]
  · rw [dif_neg hu, dif_neg hu, kfac2_eq, kfac2_eq, etaS_sig G U F X Y hroot hvA hvU, if_neg huv,
      add_zero]
    rfl

/-- **σ_v tredobler vekten der `η_v = 1`.** -/
theorem joint_sig (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V} (hv : v ∈ AO G U X Y)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    (he : etaS G U F X Y s v = 1) :
    (doModel (MP G U F F' D X Y true) X x).fullJoint (sig G U X Y v s) =
      3 * (doModel (MP G U F F' D X Y true) X x).fullJoint s := by
  obtain ⟨hvA, hvU, hvX⟩ := Finset.mem_filter.mp hv
  rw [fullJoint_apply_prod, fullJoint_apply_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), ← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    Finset.prod_congr rfl (fun u hu =>
      kfac_sig_ne G U F F' D X Y hroot hv x s (Finset.ne_of_mem_erase hu))]
  rw [kfac_doModel, kfac_doModel, dif_neg hvX, dif_neg hvX, kfac2_eq, kfac2_eq,
    etaS_sig G U F X Y hroot hvA hvU, if_pos rfl, he,
    show (1 : ZMod 2) + 1 = 0 from by decide, noise_ratio]
  show kfac (M G U F F' D true) Finset.univ (fstA U s) v * (3 * noise 1) * _ = _
  ring

/-- Snu `a` i `r0` og `b` langs halen fra `r0`. -/
noncomputable def tau2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (tauS U D (fstA U s) u, (s u).2 + tI G X Y D.r0 u.1)

lemma fstA_tau2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (tau2 G U D X Y s) = tauS U D (fstA U s) := rfl

lemma tau2_invol (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    tau2 G U D X Y (tau2 G U D X Y s) = s := by
  funext u
  refine Prod.ext ?_ ?_
  · show tauS U D (tauS U D (fstA U s)) u = (s u).1
    rw [tauS_invol]
    rfl
  · show (s u).2 + tI G X Y D.r0 u.1 + tI G X Y D.r0 u.1 = (s u).2
    rw [add_assoc, zmod2_add_self, add_zero]

lemma etaS_tau2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    (u : V) : etaS G U F X Y (tau2 G U D X Y s) u = etaS G U F X Y s u := by
  have hr0A : D.r0 ∈ AY G X Y := hH.anc hD.r0R
  have hb : ∀ w, (tau2 G U D X Y s ⟨w, Finset.mem_univ w⟩).2 =
      (s ⟨w, Finset.mem_univ w⟩).2 + tI G X Y D.r0 w := fun w => rfl
  rw [etaS_eq, etaS_eq]
  simp only [hb, Finset.sum_add_distrib]
  rw [tI_rec G X Y hroot (s := D.r0) (v := u) hr0A hD.r0U]
  unfold TC
  by_cases hu : u = D.r0
  · subst hu
    have hRO : D.r0 ∈ RO G U F := Finset.mem_filter.mpr ⟨hD.r0R, hD.r0U⟩
    have ha : rd (tau2 G U D X Y s ⟨D.r0, Finset.mem_univ D.r0⟩).1 0 =
        rd (s ⟨D.r0, Finset.mem_univ D.r0⟩).1 0 + 1 := ov_tau U D hD.r0U (fstA U s)
    rw [if_pos rfl]
    simp only [if_pos hRO]
    rw [ha]
    exact zmod2_t1 _ _ _ _
  · have ha : (tau2 G U D X Y s ⟨u, Finset.mem_univ u⟩).1 = (s ⟨u, Finset.mem_univ u⟩).1 :=
      tau_ne U D (fstA U s) hu
    rw [if_neg hu]
    simp only [ha]
    exact zmod2_t0 _ _ _ _

lemma Yb_tau2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (tau2 G U D X Y s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (tau2 G U D X Y s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + tI G X Y D.r0 y) from rfl,
    Finset.sum_add_distrib, sum_tI_Y G X Y (hH.anc hD.r0R)]

lemma kfac_tau2_ne (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    {u : V} (hu0 : u ≠ D.r0) :
    kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ (tau2 G U D X Y s) u =
      kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ s u := by
  have hr0A : D.r0 ∈ AY G X Y := hH.anc hD.r0R
  have hr0X : D.r0 ∉ X := hH.out _ (Finset.mem_filter.mp hD.r0R).1
  rw [kfac_doModel, kfac_doModel]
  by_cases hu : u ∈ X
  · rw [dif_pos hu, dif_pos hu]
    have hsu : tau2 G U D X Y s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ :=
      Prod.ext (tau_ne U D (fstA U s) hu0) (by
        show (s ⟨u, Finset.mem_univ u⟩).2 + tI G X Y D.r0 u = _
        rw [tI_X G X Y hr0A hr0X hu, add_zero])
    rw [hsu]
  · rw [dif_neg hu, dif_neg hu, kfac2_eq, kfac2_eq, etaS_tau2 G U F F' D X Y hH hD hroot]
    congr 1
    have h := kfac_tau G U F F' D hH hD (fun w => (x w).1) (fstA U s) hu0
    rw [kfac_doModel, kfac_doModel, dif_neg hu, dif_neg hu] at h
    exact h

/-- **τ′ tredobler vekten der `gS = 1`.** -/
theorem joint_tau2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    (hg : gS G U F F' D (fstA U s) = 1) :
    (doModel (MP G U F F' D X Y true) X x).fullJoint (tau2 G U D X Y s) =
      3 * (doModel (MP G U F F' D X Y true) X x).fullJoint s := by
  have hr0F := (Finset.mem_filter.mp hD.r0R).1
  have hr0F' := hH.sub hr0F
  have hr0X := hH.out _ hr0F
  have k1 : kfac (M G U F F' D true) Finset.univ (tauS U D (fstA U s)) D.r0 = noise 0 := by
    rw [kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl, sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    show ov U (tauS U D (fstA U s)) D.r0 + sbV G U F F' D true (tauS U D (fstA U s)) D.r0 = 0
    rw [ov_tau U D hD.r0U (fstA U s), sbV_tau G U F F' D hD true (fstA U s) hr0F' hD.r0U]
    exact zmod2_one _ _ hg
  have k2 : kfac (M G U F F' D true) Finset.univ (fstA U s) D.r0 = noise 1 := by
    rw [kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl, sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    try exact hg
  have e1 : kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ (tau2 G U D X Y s) D.r0 =
      noise 0 * noise (etaS G U F X Y s D.r0) := by
    rw [kfac_doModel, dif_neg hr0X, kfac2_eq, etaS_tau2 G U F F' D X Y hH hD hroot]
    congr 1
    try exact k1
  have e2 : kfac (doModel (MP G U F F' D X Y true) X x) Finset.univ s D.r0 =
      noise 1 * noise (etaS G U F X Y s D.r0) := by
    rw [kfac_doModel, dif_neg hr0X, kfac2_eq, k2]
  rw [fullJoint_apply_prod, fullJoint_apply_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    Finset.prod_congr rfl (fun u hu =>
      kfac_tau2_ne G U F F' D X Y hH hD hroot x s (Finset.ne_of_mem_erase hu)),
    e1, e2, noise_ratio]
  ring

end sigtau

end PM
end Hedge

#print axioms Hedge.PM.joint_sig
#print axioms Hedge.PM.etaS_tau2
#print axioms Hedge.PM.joint_tau2

/-! ## Runde 85: H4, steg 6b — induksjonen: `P(Yb = 1) ≠ ½` i `MP true` under `do(x)`

`fS S = Yb + gS + Σ_{v ∈ S} η_v`. For `S = AO` er den konstant på støtten (`fS_const`), så
`bias_base` gir skjevhet. Ta bort én `v` om gangen: σ_v holder `fS S` fast (`fS_sig`), snur
`η_v` og tredobler vekten der `η_v = 1`, så `bias_step` flytter skjevheten til
`fS (S \ {v}) = fS S + η_v`. Ved `S = ∅` gir τ′ (holder `Yb + gS` fast, snur `gS`) til slutt
skjevhet for `Yb` (`Yb_biased`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_ins : ∀ a b c e : ZMod 2, a + b + c = a + b + (e + c) + e := by decide

lemma zmod2_fin : ∀ y g : ZMod 2, y = y + g + 0 + g := by decide

lemma zmod2_fs : ∀ y g e : ZMod 2, y + 1 + g + (e + 1) = y + g + e := by decide

lemma zmod2_ft : ∀ y g e : ZMod 2, y + 1 + (g + 1) + e = y + g + e := by decide

section induct

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- `Yb + gS + Σ_{v ∈ S} η_v`. -/
noncomputable def fS (S : Finset V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    ZMod 2 :=
  Yb U Y s + gS G U F F' D (fstA U s) + ∑ v ∈ S, etaS G U F X Y s v

lemma fS_sig (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {S : Finset V} {v : V} (hv : v ∈ AO G U X Y)
    (hvS : v ∈ S) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fS G U F F' D X Y S (sig G U X Y v s) = fS G U F F' D X Y S s := by
  obtain ⟨hvA, hvU, -⟩ := Finset.mem_filter.mp hv
  unfold fS
  rw [Yb_sig G U X Y hvA,
    Finset.sum_congr rfl (fun u _ => etaS_sig G U F X Y hroot hvA hvU s u), Finset.sum_add_distrib]
  first
    | rw [Finset.sum_ite_eq']
    | rw [Finset.sum_ite_eq]
  rw [if_pos hvS]
  exact zmod2_fs _ _ _

lemma fS_tau2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (S : Finset V)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fS G U F F' D X Y S (tau2 G U D X Y s) = fS G U F F' D X Y S s := by
  have hr0F' := hH.sub (Finset.mem_filter.mp hD.r0R).1
  have hg : gS G U F F' D (fstA U (tau2 G U D X Y s)) = gS G U F F' D (fstA U s) + 1 :=
    gS_tau G U F F' D hD hr0F' (fstA U s)
  unfold fS
  rw [Yb_tau2 G U F F' D X Y hH hD, hg,
    Finset.sum_congr rfl (fun u _ => etaS_tau2 G U F F' D X Y hH hD hroot s u)]
  exact zmod2_ft _ _ _

/-- **Steg 6: skjevhet for `Yb` i `MP true` under `do(x)`.** -/
theorem Yb_biased (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X)
    (x : Assignment (α := Val2 U) X) :
    ((doModel (MP G U F F' D X Y true) X x).fullJoint.map (Yb U Y)) 0 ≠
      ((doModel (MP G U F F' D X Y true) X x).fullJoint.map (Yb U Y)) 1 := by
  have hbase : ((doModel (MP G U F F' D X Y true) X x).fullJoint.map
      (fS G U F F' D X Y (AO G U X Y))) 0 ≠
      ((doModel (MP G U F F' D X Y true) X x).fullJoint.map
        (fS G U F F' D X Y (AO G U X Y))) 1 :=
    bias_base _ _ _ (fun s hs => fS_const G U F F' D X Y hH hD hroot hYU hYX x s hs)
  have key : ∀ n, ∀ S ⊆ AO G U X Y, S.card + n = (AO G U X Y).card →
      ((doModel (MP G U F F' D X Y true) X x).fullJoint.map (fS G U F F' D X Y S)) 0 ≠
        ((doModel (MP G U F F' D X Y true) X x).fullJoint.map (fS G U F F' D X Y S)) 1 := by
    intro n
    induction n with
    | zero =>
      intro S hS hc
      have hSA : S = AO G U X Y := Finset.eq_of_subset_of_card_le hS (by omega)
      rw [hSA]
      exact hbase
    | succ n ih =>
      intro S hS hc
      obtain ⟨v, hvA, hvS⟩ : ∃ v ∈ AO G U X Y, v ∉ S := by
        by_contra hno
        push_neg at hno
        have hle := Finset.card_le_card hno
        omega
      have hins : insert v S ⊆ AO G U X Y := Finset.insert_subset_iff.mpr ⟨hvA, hS⟩
      have hcard : (insert v S).card + n = (AO G U X Y).card := by
        first
          | rw [Finset.card_insert_of_notMem hvS]
          | rw [Finset.card_insert_of_not_mem hvS]
        omega
      have ih' := ih (insert v S) hins hcard
      have heq : fS G U F F' D X Y S =
          fun s => fS G U F F' D X Y (insert v S) s + etaS G U F X Y s v := by
        funext s
        unfold fS
        rw [Finset.sum_insert hvS]
        exact zmod2_ins _ _ _ _
      rw [heq]
      exact bias_step _ (sig G U X Y v) (fS G U F F' D X Y (insert v S))
        (fun s => etaS G U F X Y s v) (sig_invol G U X Y v)
        (fun s => fS_sig G U F F' D X Y hroot hvA (Finset.mem_insert_self v S) s)
        (fun s => by
          show etaS G U F X Y (sig G U X Y v s) v = etaS G U F X Y s v + 1
          rw [etaS_sig G U F X Y hroot (Finset.mem_filter.mp hvA).1 (Finset.mem_filter.mp hvA).2.1,
            if_pos rfl])
        (fun s he => joint_sig G U F F' D X Y hroot hvA x s he) ih'
  have h0 := key (AO G U X Y).card ∅ (Finset.empty_subset _) (by simp)
  have hfin : (fun s => fS G U F F' D X Y ∅ s + gS G U F F' D (fstA U s)) = Yb U Y := by
    funext s
    unfold fS
    rw [Finset.sum_empty]
    exact (zmod2_fin _ _).symm
  rw [← hfin]
  have hr0F' := hH.sub (Finset.mem_filter.mp hD.r0R).1
  exact bias_step _ (tau2 G U D X Y) (fS G U F F' D X Y ∅) (fun s => gS G U F F' D (fstA U s))
    (tau2_invol G U D X Y) (fun s => fS_tau2 G U F F' D X Y hH hD hroot ∅ s)
    (fun s => gS_tau G U F F' D hD hr0F' (fstA U s))
    (fun s hg => joint_tau2 G U F F' D X Y hH hD hroot x s hg) h0

end induct

end PM
end Hedge

#print axioms Hedge.PM.Yb_biased

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
