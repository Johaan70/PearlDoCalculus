import PearlDoCalculus.Hedge.Roots
import PearlDoCalculus.Hedge.Tails

/-!
# The product models: carrying the root parity to `Y` (step H4, second part)

Step H3 (`Hedge/Roots.lean`) shows that a hedge blocks identification at its observed
roots `RO`. This file starts step H4, which carries the result down to `Y` along the
tails (`tp`, `Hedge/Tails.lean`). It defines the product models `MP`, shows that the two
of them have the same positive observed distribution, and proves the first half of the
effect gap: in `MP false` the parity `Yb` on `Y` is a fair coin under `do(x)`
(`PM.Yb_half`).

**Why.** The parity models of H3 differ only in the parity of the roots of the hedge,
and the roots need not lie in `Y`. The product models add a second bit to every node
that copies the root values down the tails, so the difference shows up at `Y`. The
second half, that `Yb` is biased in `MP true`, is proved in `Hedge/ProductBias.lean`.

**How.**

1. *The models* (`Val2`, `TC`, `bIn`, `kern2`, `MP`). A node has the value
   `(a, b) : Val U v × ZMod 2`. The first coordinate `a` follows the parity model
   `M G U F F' D two` and reads only the `a` of the parents. The second is
   `b_v = [v ∈ RO] a_v + Σ_{w ∈ TC v} b_w + η_v` with noise `η_v ~ noise`, where the tail
   parents `TC v` are the observed `w ∈ AY \ Y` with `tp w = v` (`tc_edge`). So each
   kernel factor of `MP` is the factor of `M` at the first coordinates times
   `noise (etaS s v)`, where `etaS` is the noise term (`kern2_apply`, `kfac2_eq`,
   `joint2_eq`, `etaS_eq`).
2. *Equal observed distribution and positivity* (`marg2_eq`, `pos2`). The involution
   `phiS` from H3 acts on the first coordinate and leaves `b` alone (`phiS2`). It keeps
   the observed values and the noise terms (`phiS2_restrict`, `etaS_phiS2`), so
   `joint_phiS` gives `joint2_phiS2` and equal marginals. Positivity comes from `pos_M1`
   and the positive noise factors.
3. *A fair `Yb` in `MP false`* (`Yb_half`). `betaC c w` sums `phiC c r · tI r w` over the
   roots `r`: where `b` must flip when ψ flips the root values (`betaC_rec`, and it is
   `0` on latents and on `X`, `betaC_X`). `psi2 c` applies ψ to the first coordinate and
   adds `betaC c` to the second. It is an involution that keeps every noise term
   (`etaS_psi2`), so it keeps the joint distribution under `do(x)` (`kfac_psi2_do`,
   `joint_psi2`). Each tail meets `Y` exactly once and `Σ_{RO} phiC c = 1`
   (`sum_phiC_RO`), so `psi2` flips `Yb` (`Yb_psi2`). Then `map_flip_eq`, at the edge from
   `cross_edge`, gives `Yb_half`.

**Main results.** `PM.MP`, `PM.kfac2_eq`, `PM.joint2_eq`, `PM.marg2_eq`, `PM.pos2`,
`PM.psi2_invol`, `PM.joint_psi2`, `PM.Yb_psi2`, `PM.Yb_half`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

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
