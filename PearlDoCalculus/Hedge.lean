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
`PM.Yb_half`) are in `PearlDoCalculus/Hedge/Product.lean`.

This file shows that `Yb` is biased in `MP true` (the bias lemma and the induction),
concludes H4, and ends with the completeness theorem `idCheck_iff` (H5). The file is
being split by topic; see `CLEANUP.md`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

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
