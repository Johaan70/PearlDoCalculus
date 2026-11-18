import PearlDoCalculus.Hedge.DoGapM1

/-!
# The effect in `M2`: the root parity is biased under `do(x)` (step H3)

This file proves `PM.parR_three`: under an intervention `do(x)`, the parity model `M2`
(`PM.M` with `two = true`, from `Hedge/ParityModels.lean`) gives
`P(parR = 0) = 3 · P(parR = 1)` for the parity `parR` of the observed roots of the hedge.
It also proves `PM.cross_edge`: the spanning tree has an edge `(c, par c)` with exactly
one end that reaches a root along `nxt` without passing through `X`. That edge is the
hypothesis of `PM.parR_half`.

**Why.** In `M1` the root parity is a fair coin under `do(x)` (`PM.parR_half`, in
`Hedge/DoGapM1.lean`). In `M2` it is not. So the two models, which have the same
positive observed distribution, give different effects of `do(x)`, and the effect is
not identifiable.

**How.**

1. *The crossing edge.* If every edge `(c, par c)` of a tree has the same truth value for
   a property at both ends, the whole tree has the truth value of the root
   (`ParTree.iff_root`). The roots of `F` reach a root without passing through `X`, and a
   node of `X ∩ F'` does not. So some edge of the tree for `F'` crosses (`cross_edge`).
2. *The parity in `M2` is the noise term.* `noise 0 = 3 · noise 1` (`noise_ratio`). The
   bits of `M2` summed over the observed part `OF` of `F` equal the sum of the values of
   the non-roots in `OF`: every tree bit in `F` is counted twice, and every `nxt` value in
   `F` once (`sum_sbV2`). Since `F` avoids `X`, on every assignment of positive
   probability under `do(x)` the equations of `OF` hold except at the noisy root `r0`.
   So `parR` equals the noise term `ov r0 + sbV true r0` at `r0` (`parR_g`).
3. *The ratio.* `tauS` flips the value at `r0`. No node reads `r0`, because roots are not
   `nxt` children, so only the factor at `r0` changes (`sbV_tau`, `kfac_tau`). When the
   noise term `gS` is `1`, that factor goes from `noise 1` to `noise 0 = 3 · noise 1`
   (`joint_tau`). An involution that flips a bit and multiplies the weight by `k` where
   the bit is `1` gives `P(bit = 0) = k · P(bit = 1)` (`map_ratio`). Together with
   `parR_g` and `map_congr_supp`, this gives `parR_three`.

**Main results.** `ParTree.iff_root`, `map_ratio`, `PM.cross_edge`, `PM.noise_ratio`,
`PM.sum_sbV2`, `PM.parR_g`, `PM.joint_tau`, `PM.parR_three`.
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
