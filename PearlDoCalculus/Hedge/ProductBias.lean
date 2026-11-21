import PearlDoCalculus.Hedge.Product

/-!
# The product model `MP true` gives a biased parity on `Y` (step H4, third part)

This file proves `PM.Yb_biased`: under an intervention `do(x)`, the parity `Yb` of the
second bits on `Y` in the product model `MP true` (`PM.MP`, from `Hedge/Product.lean`)
is not a fair coin, that is `P(Yb = 0) ≠ P(Yb = 1)`.

**Why.** The two product models have the same positive observed distribution, and in
`MP false` the parity `Yb` is a fair coin under `do(x)` (`PM.Yb_half`, in
`Hedge/Product.lean`). If `Yb` is not fair in `MP true`, the two models give different
effects on `Y`, and `P(Y | do(X))` is not identifiable. The product construction
replaces the published treatment of the tails, which needs repair (see `HANDOFF.md`,
section 2). Because every tail node adds its own noise, `Yb` is not simply the root
parity, so the proof removes the noise terms one at a time. `Yb_biased` is used once, in
`PM.not_ident2` (`Hedge/Complete`), together with `PM.Yb_half`.

**How.**

1. *The bias lemma* (`pair_ratio`, `bias_step`, `bias_base`). If an involution σ keeps
   `f`, flips `e` and triples the weight where `e = 1`, then
   `P(f = a, e = 0) = 3 · P(f = a, e = 1)` (`pair_ratio`). Writing the distributions of
   `f` and `f + e` with the four values `P(f = a, e = b)` (`ZMod2.map_fst_zero` …
   `ZMod2.map_add_one`, from `Util/ZMod2.lean`), a bias in `f` gives a bias in `f + e`
   (`bias_step`, computed in `ℝ`). A function that is constant on the support is biased
   (`bias_base`).
2. *Telescoping for `Yb`* (`Yb_tele`, `fS_const`). Let `AO` be the observed nodes of `AY`
   outside `X`, where the noise counts, and `AXo` those in `X`. For every assignment,
   `Yb = parR a + Σ_{AO} η + Σ_{AXo} b`, because every `w ∈ AY \ Y` is a tail child of
   exactly one node of `AO` (`fiber_sum`). On the support of `do(x)` in `MP true`, `b`
   equals `x` on `X` and `parR = gS` (`parR_g`). So `Yb + gS + Σ_{AO} η` is a constant
   that depends only on `x`.
3. *The involutions σ_v and τ′* (`sig`, `tau2`). `sig v` flips `b` along the tail from
   `v ∈ AO`. By `tI_rec` this changes only the noise term at `v` (`etaS_sig`), flips `Yb`
   (`Yb_sig`), and triples the weight under `do(x)` where `η_v = 1` (`joint_sig`).
   `tau2` flips `a` at the noisy root `r0` (`tauS`) and `b` along the tail from `r0`. It
   keeps the noise terms (`etaS_tau2`), flips `Yb` and `gS`, and triples the weight where
   `gS = 1` (`joint_tau2`).
4. *The induction* (`fS`, `Yb_biased`). Let `fS S = Yb + gS + Σ_{v ∈ S} η_v`. For
   `S = AO` it is constant on the support, so `bias_base` gives a bias. Remove one `v` at
   a time: σ_v keeps `fS S` (`fS_sig`), flips `η_v` and triples the weight where
   `η_v = 1`, so `bias_step` moves the bias to `fS (S \ {v}) = fS S + η_v`. At `S = ∅`,
   τ′ keeps `Yb + gS` and flips `gS` (`fS_tau2`), and one more `bias_step` gives the bias
   for `Yb`.

**Main results.** `pair_ratio`, `bias_step`, `bias_base`, `PM.Yb_tele`, `PM.fS_const`,
`PM.joint_sig`, `PM.joint_tau2`, `PM.Yb_biased`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## The bias lemma

`pair_ratio`: an involution σ that keeps `f`, flips `e` and triples the weight where
`e = 1` gives `P(f = a, e = 0) = 3 · P(f = a, e = 1)`. `ZMod2.map_fst_zero` …
`ZMod2.map_add_one` (in `Util/ZMod2.lean`): the distributions of `f` and `f + e` in terms
of the four values `P(f = a, e = b)`. `bias_step`: if `P(f = 0) ≠ P(f = 1)`, then also
`P(f + e = 0) ≠ P(f + e = 1)` (computed in `ℝ`: `3A + B = 3B + A` gives `A = B`).
`bias_base`: if `f` is constant on the support, then `P(f = 0) ≠ P(f = 1)`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The ratio for the pair `(f, e)`**: `P(f = a, e = 0) = 3 · P(f = a, e = 1)`, by
reindexing the sum with σ. -/
theorem pair_ratio {β : Type*} (p : PMF β) (σ : β → β) (f e : β → ZMod 2)
    (hinv : ∀ s, σ (σ s) = s) (hf : ∀ s, f (σ s) = f s) (he : ∀ s, e (σ s) = e s + 1)
    (hp : ∀ s, e s = 1 → p (σ s) = 3 * p s) (a : ZMod 2) :
    (p.map (fun s => (f s, e s))) (a, 0) = 3 * (p.map (fun s => (f s, e s))) (a, 1) := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm σ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  simp only [Function.Involutive.coe_toPerm, hf, he]
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
      exact h1 (Prod.ext ha ((ZMod2.zero_eq_add_one_iff _).mp hb))
    rw [if_neg h0, if_neg h1, mul_zero]

/-- **The bias lemma**: under the hypotheses of `pair_ratio`, a bias of `f` gives a
bias of `f + e`. -/
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
  rw [hmf, ZMod2.map_fst_zero, ZMod2.map_fst_one, r0, r1] at hb
  rw [hms, ZMod2.map_add_zero, ZMod2.map_add_one, r0, r1]
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
    exact (ENNReal.toReal_eq_toReal_iff' hA hB).mp h''
  rw [hAB]

/-- **The base case:** if `f` is constant on the support, then `P(f = 0) ≠ P(f = 1)`. -/
theorem bias_base {β : Type*} (p : PMF β) (f : β → ZMod 2) (c : ZMod 2)
    (h : ∀ s, p s ≠ 0 → f s = c) : (p.map f) 0 ≠ (p.map f) 1 := by
  rw [PMF.map_congr_on_support p f (fun _ => c) h]
  have hc : p.map (fun _ => c) = PMF.pure c := PMF.map_const p c
  rw [hc, PMF.pure_apply, PMF.pure_apply]
  rcases ZMod2.eq_zero_or_eq_one c with rfl | rfl
  · rw [if_pos rfl, if_neg one_ne_zero]
    exact one_ne_zero
  · rw [if_neg zero_ne_one, if_pos rfl]
    exact zero_ne_one

end Hedge

#print axioms Hedge.pair_ratio
#print axioms Hedge.bias_step
#print axioms Hedge.bias_base

/-! ## Telescoping for `Yb`

`AO` = the observed nodes of `AY` outside `X` (where the noise counts), `AXo` = those in
`X`. `Yb_tele`: for every assignment, `Yb = parR a + Σ_{AO} η + Σ_{AXo} b` (every
`w ∈ AY \ Y` is a tail child of exactly one node of `AO`, `fiber_sum`). `fS_const`: on the
support of `do(x)` in `MP true`, `b` equals `x` on `X` and `parR = gS` (`parR_g`), so
`Yb + gS + Σ_{AO} η` is a constant that depends only on `x`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section tele3

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- The observed nodes of `AY` outside `X`. -/
noncomputable def AO : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∉ X)

/-- The observed nodes of `AY` in `X`. -/
noncomputable def AXo : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∈ X)

/-- **The telescoping identity for `Yb`.** -/
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
  exact ZMod2.self_eq_add_add_cancel _ _ _ _

/-- **On the support, `Yb + gS + Σ_{AO} η` is constant.** -/
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
  exact ZMod2.add_add_add_add_cancel_middle _ _ _

end tele3

end PM
end Hedge

#print axioms Hedge.PM.Yb_tele
#print axioms Hedge.PM.fS_const

/-! ## The involutions σ_v and τ′

`sig v`: flip `b` along the tail from `v` (`v ∈ AO`). By `tI_rec` this changes only the
noise term at `v` (`etaS_sig`), flips `Yb` (`Yb_sig`) and triples the weight under `do(x)`
where `η_v = 1` (`joint_sig`). `tau2`: flip `a` at `r0` (`tauS`) and `b` along the tail
from `r0`; the noise terms stay (`etaS_tau2`), `Yb` and `gS` flip, and the weight triples
where `gS = 1` (`joint_tau2`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section sigtau

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- The tail from a node of `AY` outside `X` does not meet `X`. -/
lemma tI_X {v : V} (hv : v ∈ AY G X Y) (hvX : v ∉ X) {u : V} (hu : u ∈ X) : tI G X Y v u = 0 := by
  unfold tI
  rw [if_neg]
  rintro ⟨k, hk⟩
  apply tp_iter_notX G X Y hv hvX k
  rw [hk]
  exact hu

/-- Flip `b` along the tail from `v`. -/
noncomputable def sig (v : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => ((s u).1, (s u).2 + tI G X Y v u.1)

/-- `sig v` is an involution. -/
lemma sig_invol (v : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    sig G U X Y v (sig G U X Y v s) = s := by
  funext u
  exact Prod.ext rfl (by
    show (s u).2 + tI G X Y v u.1 + tI G X Y v u.1 = (s u).2
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])

/-- `sig v` flips the noise term at `v` and no other. -/
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
  exact ZMod2.add_add_add_cancel_comm _ _ _ _ _

/-- `sig v` flips `Yb` (the tail from `v` meets `Y` once). -/
lemma Yb_sig {v : V} (hv : v ∈ AY G X Y) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (sig G U X Y v s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (sig G U X Y v s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + tI G X Y v y) from rfl,
    Finset.sum_add_distrib, sum_tI_Y G X Y hv]

/-- Away from `v`, `sig v` keeps every factor under `do(x)`. -/
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

/-- **σ_v triples the weight where `η_v = 1`.** -/
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
    CharTwo.add_self_eq_zero (1 : ZMod 2), noise_ratio]
  show kfac (M G U F F' D true) Finset.univ (fstA U s) v * (3 * noise 1) * _ = _
  ring

/-- Flip `a` at `r0` and `b` along the tail from `r0`. -/
noncomputable def tau2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (tauS U D (fstA U s) u, (s u).2 + tI G X Y D.r0 u.1)

/-- The first coordinate of `tau2 s` is `tauS` of the first coordinate of `s`. -/
lemma fstA_tau2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (tau2 G U D X Y s) = tauS U D (fstA U s) := rfl

/-- `tau2` is an involution. -/
lemma tau2_invol (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    tau2 G U D X Y (tau2 G U D X Y s) = s := by
  funext u
  refine Prod.ext ?_ ?_
  · show tauS U D (tauS U D (fstA U s)) u = (s u).1
    rw [tauS_invol]
    rfl
  · show (s u).2 + tI G X Y D.r0 u.1 + tI G X Y D.r0 u.1 = (s u).2
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- `tau2` keeps every noise term: at `r0` the flip of `a` and of `b` cancel, and along
the tail the flips of `b` cancel in pairs. -/
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
    exact ZMod2.add_add_add_cancel_pairs _ 1 _ _ _
  · have ha : (tau2 G U D X Y s ⟨u, Finset.mem_univ u⟩).1 = (s ⟨u, Finset.mem_univ u⟩).1 :=
      tau_ne U D (fstA U s) hu
    rw [if_neg hu]
    simp only [ha]
    exact ZMod2.add_add_add_cancel_comm_zero _ _ _ _

/-- `tau2` flips `Yb`. -/
lemma Yb_tau2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (tau2 G U D X Y s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (tau2 G U D X Y s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + tI G X Y D.r0 y) from rfl,
    Finset.sum_add_distrib, sum_tI_Y G X Y (hH.anc hD.r0R)]

/-- Away from `r0`, `tau2` keeps every factor under `do(x)`. -/
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

/-- **τ′ triples the weight where `gS = 1`.** -/
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
    exact ZMod2.add_one_add_eq_zero_of_add_eq_one _ _ hg
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

/-! ## The induction: `P(Yb = 1) ≠ ½` in `MP true` under `do(x)`

`fS S = Yb + gS + Σ_{v ∈ S} η_v`. For `S = AO` it is constant on the support (`fS_const`),
so `bias_base` gives a bias. Remove one `v` at a time: σ_v keeps `fS S` (`fS_sig`), flips
`η_v` and triples the weight where `η_v = 1`, so `bias_step` moves the bias to
`fS (S \ {v}) = fS S + η_v`. At `S = ∅`, τ′ (which keeps `Yb + gS` and flips `gS`) finally
gives the bias for `Yb` (`Yb_biased`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section induct

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- The function `Yb + gS + Σ_{v ∈ S} η_v` of the induction. -/
noncomputable def fS (S : Finset V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    ZMod 2 :=
  Yb U Y s + gS G U F F' D (fstA U s) + ∑ v ∈ S, etaS G U F X Y s v

/-- For `v ∈ S`, `sig v` keeps `fS S`: it flips both `Yb` and `η_v`. -/
lemma fS_sig (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {S : Finset V} {v : V} (hv : v ∈ AO G U X Y)
    (hvS : v ∈ S) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fS G U F F' D X Y S (sig G U X Y v s) = fS G U F F' D X Y S s := by
  obtain ⟨hvA, hvU, -⟩ := Finset.mem_filter.mp hv
  unfold fS
  rw [Yb_sig G U X Y hvA,
    Finset.sum_congr rfl (fun u _ => etaS_sig G U F X Y hroot hvA hvU s u), Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  rw [if_pos hvS]
  exact ZMod2.add_one_add_add_add_one _ _ _

/-- `tau2` keeps `fS S`: it flips both `Yb` and `gS`. -/
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
  exact ZMod2.add_one_add_add_one_add _ _ _

/-- **`Yb` is biased in `MP true` under `do(x)`**: `P(Yb = 0) ≠ P(Yb = 1)`. -/
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
        rw [Finset.card_insert_of_notMem hvS]
        omega
      have ih' := ih (insert v S) hins hcard
      have heq : fS G U F F' D X Y S =
          fun s => fS G U F F' D X Y (insert v S) s + etaS G U F X Y s v := by
        funext s
        unfold fS
        rw [Finset.sum_insert hvS]
        exact ZMod2.add_eq_add_add_add_cancel _ _ _ _
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
    exact (ZMod2.self_eq_add_add_zero_add _ _).symm
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
