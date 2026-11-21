import PearlDoCalculus.Identification.LatentTree

/-!
# Root-path configurations and their models

This file sets up the c-forests with several roots used for the non-identifiability
results of `Identification/RootPath`.

* `MultiRoot.MR` (round 14): a latent tree over `x` and the nodes `nd₀, …, nd_{n+1}`
  with a directed forest pattern, together with the helpers `ext` and `chan_mix`.
* `RootPath.RP` (round 15): the same, but `x` may point into any root `nd_r`; the
  latent path from `u₀` to `u_r` is given by a parity condition. The file defines the
  graphs, the parity algebra, the bottom-up solution (as in round 9) and the three
  models A, B and C with their kernel products.

The file stops before the proof that A and C have the same joint distribution; that
and the bijection between A and B are in `Identification/RootPath`, which also proves
`rootPath_not_identifiable` and `multiRoot_not_identifiable`.
(The comments of the rounds below are still in Norwegian.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 14: c-skoger med flere røtter

Et latent tre over `x` og nodene `nd₀, …, nd_{n+1}` (med `x` som blad, festet til
`nd₀`), og et rettet skog-mønster: hver node peker på en forelder `dp k` eller er en
rot (`dp k = none`). `x → nd₀`, og `nd₀` er en rot. Da er `P(R | do(x))` ikke
identifiserbar, der `R` er mengden av røtter.

Her står bare konfigurasjonen `MR` og hjelpefunksjonene `ext` og `chan_mix`.
Beviset ble generalisert i runde 15 (`RootPath`), og teoremet
`multiRoot_not_identifiable` står etter runde 15, som korollar med `r = 0` og
stien `{u₀}`. -/

namespace Identification
namespace MultiRoot

open HedgeChain (ev xx xb chan_symm)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Verdien av en delvis tilordning, med `false` utenfor. -/
def ext {S : Finset V} (pa : Assignment (α := fun _ : V => Bool) S) (v : V) : Bool :=
  if h : v ∈ S then pa ⟨v, h⟩ else false

lemma ext_restrict (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    {S : Finset V} {v : V} (hv : v ∈ S) :
    ext (s.restrict (Finset.subset_univ S)) v = ev s v := by
  simp [ext, hv, Assignment.restrict, ev]

lemma chan_mix (a b c : Bool) : Bow.chan (xor a (xor b c)) b = Bow.chan c a := by
  rw [Bow.chan_apply, Bow.chan_apply]
  cases a <;> cases b <;> cases c <;> rfl

/-- Konfigurasjonen. -/
structure MR (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hdp0 : dp 0 = none
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd 0)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace MR

variable {G : DAG V} {n : ℕ} (P : MR G n)

/-- Røttene. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- Røttene som noder. -/
def Y : Finset V := P.Rt.image P.nd

lemma mem_Rt0 : (0 : Fin (n + 2)) ∈ P.Rt := by simp [Rt, P.hdp0]

lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

end MR

end MultiRoot
end Identification

/-! ## Runde 15: x kan peke inn i en hvilken som helst rot

Som runde 14, men `x → nd_r` for en vilkårlig rot `r`, ikke bare `nd₀`. Den latente
naboen til `x` er fortsatt `u₀`. En *sti* `pth` av latente fra `u₀` til `u_r` er gitt
ved paritetsvilkåret

  `pth k + #{barn j av k på stien} = [k = r]`   (mod 2),

dvs. hver node har et partall sti-latente inntil seg, unntatt `nd_r`, som har ett.

* Bijeksjonen flytter hele stien med `ΣR`. Pariteten endres da bare i `nd_r`.
* Modell B legger støykanalen på `nd_r` i stedet for `nd₀`; ellers er alt som i
  runde 14. Runde 13 (to røtter) og runde 14 er spesialtilfeller. -/

namespace Identification
namespace RootPath

open HedgeChain (ev xx xb chan_symm)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

open MultiRoot (ext ext_restrict chan_mix)

/-- Konfigurasjonen. -/
structure RP (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  r : Fin (n + 2)
  pth : Fin (n + 2) → Bool
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hr : dp r = none
  hp0 : pth 0 = true
  hpk : ∀ k, ofBool (pth k) + (∑ j, if bp j = some k then ofBool (pth j) else 0) =
    if k = r then 1 else 0
  hux : G.edge (u 0) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j k, dp j = some k → G.edge (nd j) (nd k)
  hxr : G.edge x (nd r)
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace RP

variable {G : DAG V} {n : ℕ} (P : RP G n)

/-- Røttene. -/
def Rt : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => P.dp k = none)
/-- Røttene som noder. -/
def Y : Finset V := P.Rt.image P.nd

lemma mem_Rtr : P.r ∈ P.Rt := by simp [Rt, P.hr]

lemma mem_Y {v : V} : v ∈ P.Y ↔ ∃ k, P.dp k = none ∧ P.nd k = v := by
  simp [Y, Rt]

/-! ### Grafene -/

noncomputable def gA : DAG V where
  edge a b := (a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hux
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)

noncomputable def gB : DAG V where
  edge a b := (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j k hd)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ P.hxr

noncomputable def gC : DAG V where
  edge a b := (∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨ (∃ k j, a = P.nd k ∧ b = P.u j)
  decEdge := fun _ _ => Classical.dec _
  rank := fun v => if ∃ k, P.nd k = v then 0 else 1
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨k, _, h1, h2⟩ | ⟨k, j, h1, h2⟩
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.x := fun ⟨k', e⟩ => P.hndx k' e
      simp [this]
    · rw [h1, h2]
      have : ¬ ∃ k', P.nd k' = P.u j := fun ⟨k', e⟩ => P.hund j k' e.symm
      simp [this]

lemma eA (a b : V) : P.gA.edge a b ↔ ((a = P.u 0 ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k)) := Iff.rfl
lemma eB (a b : V) : P.gB.edge a b ↔ ((∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j k, P.dp j = some k ∧ a = P.nd j ∧ b = P.nd k) ∨ (a = P.x ∧ b = P.nd P.r)) := Iff.rfl
lemma eC (a b : V) : P.gC.edge a b ↔ ((∃ k, P.dp k = none ∧ a = P.nd k ∧ b = P.x) ∨
    (∃ k j, a = P.nd k ∧ b = P.u j)) := Iff.rfl


lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.eA a v).mp ha with ⟨h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩
  · rw [h1, h2]; exact P.hux
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd

lemma hsB : ∀ v, P.gB.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.eB a v).mp ha with ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, k, hd, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j k hd
  · rw [h1, h2]; exact P.hxr

/-! ### Pariteten i en node -/

/-- Pariteten til foreldrene til `nd k` i A, lest av en verdifunksjon `g`. -/
def parZ (k : Fin (n + 2)) (g : V → Bool) : ZMod 2 :=
  ofBool (g (P.u k)) + (∑ j, if P.bp j = some k then ofBool (g (P.u j)) else 0) +
    ∑ j, if P.dp j = some k then ofBool (g (P.nd j)) else 0

lemma parZ_congr (k : Fin (n + 2)) {g h : V → Bool} (hu : ∀ j, g (P.u j) = h (P.u j))
    (hn : ∀ j, g (P.nd j) = h (P.nd j)) : P.parZ k g = P.parZ k h := by
  simp only [parZ, hu, hn]

lemma parZ_extA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gA.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩))))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

lemma parZ_extB (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (k : Fin (n + 2)) :
    P.parZ k (ext (s.restrict (Finset.subset_univ (P.gB.parents (P.nd k))))) =
      P.parZ k (ev s) := by
  unfold parZ
  rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inl ⟨k, rfl, rfl⟩)))]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))]
    · rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [ext_restrict s (DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩)))))]
    · rfl

/-! ### Løsningen nedenfra og opp (som i runde 9) -/

def solN (R : Fin (n + 2) → ZMod 2) : ℕ → Fin (n + 2) → ZMod 2
  | 0, k => R k
  | m + 1, k => R k + ∑ j, if P.bp j = some k then solN R m j else 0

def M : ℕ := Finset.univ.sup P.ht

lemma ht_le (k : Fin (n + 2)) : P.ht k ≤ P.M := Finset.le_sup (Finset.mem_univ k)

lemma stab (R : Fin (n + 2) → ZMod 2) :
    ∀ m k, P.ht k ≤ m → P.solN R (m + 1) k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then P.solN R 0 j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show R k + _ = R k
    rw [hz, add_zero]
  | succ m ih =>
    intro k hk
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma uniq (R ℓ : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) :
    ∀ m k, P.ht k ≤ m → ℓ k = P.solN R m k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hz : (∑ j, if P.bp j = some k then ℓ j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      split_ifs with h
      · exact absurd (P.hht j k h) (by omega)
      · rfl
    show ℓ k = R k
    rw [hE k, hz, add_zero]
  | succ m ih =>
    intro k hk
    rw [hE k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · exact ih j (by have := P.hht j k h; omega)
    · rfl

lemma sol_iff (R ℓ : Fin (n + 2) → ZMod 2) :
    (∀ k, ℓ k = R k + ∑ j, if P.bp j = some k then ℓ j else 0) ↔
      ∀ k, ℓ k = P.solN R (P.M + 1) k := by
  constructor
  · intro hE k
    exact P.uniq R ℓ hE (P.M + 1) k (by have := P.ht_le k; omega)
  · intro h k
    rw [h k]
    show R k + _ = R k + _
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rw [h j, P.stab R P.M j (P.ht_le j)]
    · rfl


/-! ### Algebraen -/


/-- **Residualidentiteten.** Summen av residualene over alle noder er
`Σ_{røtter} N + L₀`, uansett verdier. -/
lemma resid (L N : Fin (n + 2) → ZMod 2) :
    ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = (∑ k ∈ P.Rt, N k) + L 0 := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then L j else 0) = if j = 0 then 0 else L j := by
    intro j
    by_cases hj : j = 0
    · have hb : P.bp j = none := (P.hbp0 j).mpr hj
      rw [hb]
      simp [hj]
    · cases hb : P.bp j with
      | none => exact absurd ((P.hbp0 j).mp hb) hj
      | some k0 => simp [hj]
  have h2 : ∀ j, (∑ k, if P.dp j = some k then N j else 0) =
      if P.dp j = none then 0 else N j := by
    intro j
    cases hd : P.dp j <;> simp
  have hB : ∑ k, (∑ j, if P.bp j = some k then L j else 0) =
      ∑ j, (if j = 0 then 0 else L j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hD : ∑ k, (∑ j, if P.dp j = some k then N j else 0) =
      ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hL : ∑ j, L j = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
    calc ∑ j, L j = ∑ j, ((if j = 0 then L j else 0) + (if j = 0 then 0 else L j)) :=
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
      _ = L 0 + ∑ j, (if j = 0 then 0 else L j) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp
  have hN : ∑ j, N j = (∑ k ∈ P.Rt, N k) + ∑ j, (if P.dp j = none then 0 else N j) := by
    rw [Rt, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hsplit : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) =
      ∑ k, N k + ∑ k, L k + ∑ k, (∑ j, if P.bp j = some k then L j else 0) +
        ∑ k, (∑ j, if P.dp j = some k then N j else 0) := by
    simp only [Finset.sum_add_distrib]
    ring
  rw [hsplit, hB, hD, hL, hN]
  have t1 := CharTwo.add_self_eq_zero (∑ j, (if j = 0 then 0 else L j))
  have t2 := CharTwo.add_self_eq_zero (∑ j, (if P.dp j = none then 0 else N j))
  linear_combination t1 + t2

/-- Holder alle likningene, er `L₀` summen over røttene. -/
lemma eqs_sum (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k, (N k + (L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [← hE k]; exact CharTwo.add_self_eq_zero _)
  rw [hz] at h
  exact ZMod2.eq_of_zero_eq_add _ _ h

/-- Holder likningene utenfor `nd_r`, er likningen i `nd_r` ekvivalent med
`L₀ = Σ_{røtter} N`. -/
lemma eqr_iff (L N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, k ≠ P.r → N k = L k + (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0) :
    (N P.r = L P.r + (∑ j, if P.bp j = some P.r then L j else 0) +
      ∑ j, if P.dp j = some P.r then N j else 0) ↔ L 0 = ∑ k ∈ P.Rt, N k := by
  have h := P.resid L N
  have hz : ∑ k ∈ Finset.univ.erase P.r, (N k + (L k +
      (∑ j, if P.bp j = some k then L j else 0) +
      ∑ j, if P.dp j = some k then N j else 0)) = 0 :=
    Finset.sum_eq_zero (fun k hk => by
      rw [← hE k (Finset.ne_of_mem_erase hk)]; exact CharTwo.add_self_eq_zero _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P.r), hz, add_zero] at h
  exact ZMod2.eq_iff_eq_of_add_eq_add _ _ _ _ h

/-! ### C-modellens latente løsning -/

/-- `r_k = N_k + barna til k`, lest av `g`. -/
def Rg (g : V → Bool) (k : Fin (n + 2)) : ZMod 2 :=
  ofBool (g (P.nd k)) + ∑ j, if P.dp j = some k then ofBool (g (P.nd j)) else 0

lemma keyAC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (∀ k, ev s (P.nd k) = toBool (P.parZ k (ev s))) ↔
      ∀ j, ev s (P.u j) = toBool (P.solN (P.Rg (ev s)) (P.M + 1) j) := by
  have step : ∀ k, (ev s (P.nd k) = toBool (P.parZ k (ev s))) ↔
      (ofBool (ev s (P.u k)) = P.Rg (ev s) k +
        ∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0) := by
    intro k
    rw [eq_toBool_iff]
    exact ZMod2.eq_add_add_iff_eq_add_add _ _ _ _
  exact (forall_congr' step).trans ((P.sol_iff (P.Rg (ev s))
    (fun k => ofBool (ev s (P.u k)))).trans (forall_congr' fun j => (eq_toBool_iff _ _).symm))

/-! ### Modellene -/

lemma pAx : P.u 0 ∈ P.gA.parents P.x := DAG.mem_parents.mpr ((P.eA _ _).mpr (Or.inl ⟨rfl, rfl⟩))
lemma pBx : P.x ∈ P.gB.parents (P.nd P.r) :=
  DAG.mem_parents.mpr ((P.eB _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
lemma pCx (k : Fin (n + 2)) (hk : P.dp k = none) : P.nd k ∈ P.gC.parents P.x :=
  DAG.mem_parents.mpr ((P.eC _ _).mpr (Or.inl ⟨k, hk, rfl, rfl⟩))
lemma pCu (k j : Fin (n + 2)) : P.nd k ∈ P.gC.parents (P.u j) :=
  DAG.mem_parents.mpr ((P.eC _ _).mpr (Or.inr ⟨k, j, rfl, rfl⟩))

noncomputable def NA : P.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (ext pa (P.u 0))
    else if h : ∃ k, P.nd k = v then PMF.pure (toBool (P.parZ (Classical.choose h) (ext pa)))
    else PMF.uniformOfFintype Bool

noncomputable def NB : P.gB.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h : ∃ k, P.nd k = v then
      (if Classical.choose h = P.r then Bow.chan (xor (ext pa P.x) (toBool (P.parZ P.r (ext pa))))
       else PMF.pure (toBool (P.parZ (Classical.choose h) (ext pa))))
    else if v = P.u 0 then PMF.pure false
    else PMF.uniformOfFintype Bool

noncomputable def NC : P.gC.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if v = P.x then Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ext pa (P.nd k))))
    else if h : ∃ j, P.u j = v then
      PMF.pure (toBool (P.solN (P.Rg (ext pa)) (P.M + 1) (Classical.choose h)))
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) :
    P.NA.kernel P.x pa = Bow.chan (ext pa (P.u 0)) := by
  simp [NA]

lemma NA_nd (k : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) :
    P.NA.kernel (P.nd k) pa = PMF.pure (toBool (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NA, if_neg (P.hndx k), dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h)]

lemma NA_o {v : V} (hvx : v ≠ P.x) (hv : ∀ k, P.nd k ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents v)) :
    P.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NA, if_neg hvx, dif_neg h]

lemma NB_ndr (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd P.r))) :
    P.NB.kernel (P.nd P.r) pa = Bow.chan (xor (ext pa P.x) (toBool (P.parZ P.r (ext pa)))) := by
  have h : ∃ k', P.nd k' = P.nd P.r := ⟨P.r, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = P.r from P.ndinj (Classical.choose_spec h), if_pos rfl]

lemma NB_nd (k : Fin (n + 2)) (hk : k ≠ P.r)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.nd k))) :
    P.NB.kernel (P.nd k) pa = PMF.pure (toBool (P.parZ k (ext pa))) := by
  have h : ∃ k', P.nd k' = P.nd k := ⟨k, rfl⟩
  simp only [NB, dif_pos h]
  rw [show Classical.choose h = k from P.ndinj (Classical.choose_spec h), if_neg hk]

lemma NB_u0 (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents (P.u 0))) :
    P.NB.kernel (P.u 0) pa = PMF.pure false := by
  have h : ¬ ∃ k, P.nd k = P.u 0 := fun ⟨k, hk⟩ => P.hund 0 k hk.symm
  simp only [NB, dif_neg h]
  all_goals rfl

lemma NB_o {v : V} (hv : ∀ k, P.nd k ≠ v) (hv0 : v ≠ P.u 0)
    (pa : Assignment (α := fun _ : V => Bool) (P.gB.parents v)) :
    P.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ k, P.nd k = v := fun ⟨k, hk⟩ => hv k hk
  simp only [NB, dif_neg h, if_neg hv0]

lemma NC_x (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents P.x)) :
    P.NC.kernel P.x pa = Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ext pa (P.nd k)))) := by
  simp [NC]

lemma NC_u (j : Fin (n + 2)) (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents (P.u j))) :
    P.NC.kernel (P.u j) pa = PMF.pure (toBool (P.solN (P.Rg (ext pa)) (P.M + 1) j)) := by
  have h : ∃ j', P.u j' = P.u j := ⟨j, rfl⟩
  simp only [NC, if_neg (P.hux' j), dif_pos h]
  rw [show Classical.choose h = j from P.uinj (Classical.choose_spec h)]

lemma NC_o {v : V} (hvx : v ≠ P.x) (hv : ∀ j, P.u j ≠ v)
    (pa : Assignment (α := fun _ : V => Bool) (P.gC.parents v)) :
    P.NC.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, P.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [NC, if_neg hvx, dif_neg h]

noncomputable def mA : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsA P.NA
noncomputable def mB : G.CausalModel (fun _ => Bool) := Completeness.liftSub P.hsB P.NB

lemma Rg_ext (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    P.Rg (ext (s.restrict (Finset.subset_univ (P.gC.parents (P.u j))))) = P.Rg (ev s) := by
  funext k
  unfold Rg
  rw [ext_restrict s (P.pCu k j)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [ext_restrict s (P.pCu i j)]
  · rfl

/-! ### Produktene -/

/-- Resten av nodene. -/
def R5 : Finset V := (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd))ᶜ

lemma mem_R5 {v : V} : v ∈ P.R5 ↔ v ≠ P.x ∧ (∀ j, P.u j ≠ v) ∧ (∀ k, P.nd k ≠ v) := by
  simp [R5]

lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f P.x * ((∏ j, f (P.u j)) * ((∏ k, f (P.nd k)) * ∏ v ∈ P.R5, f v)) := by
  rw [← Finset.prod_mul_prod_compl (insert P.x (Finset.univ.image P.u ∪ Finset.univ.image P.nd)) f]
  have hx : P.x ∉ Finset.univ.image P.u ∪ Finset.univ.image P.nd := by
    simp [P.hux', P.hndx]
  have hd : Disjoint (Finset.univ.image P.u) (Finset.univ.image P.nd) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨k, hk⟩ := hb
    exact P.hund j k hk.symm
  rw [Finset.prod_insert hx, Finset.prod_union hd]
  rw [Finset.prod_image P.uinj.injOn, Finset.prod_image P.ndinj.injOn]
  simp only [R5, mul_assoc]

noncomputable abbrev c2 : ℝ≥0∞ := (Fintype.card Bool : ℝ≥0∞)⁻¹

lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NA Finset.univ s P.x = Bow.chan (ev s (P.u 0)) (ev s P.x) := by
  rw [DoAudit.kfac_univ, P.NA_x, ext_restrict s P.pAx]
  all_goals rfl

lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.u j) = c2 := by
  rw [DoAudit.kfac_univ, P.NA_o (P.hux' j) (fun k e => P.hund j k e.symm),
    PMF.uniformOfFintype_apply]

lemma A_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NA Finset.univ s (P.nd k) = PMF.pure (toBool (P.parZ k (ev s))) (ev s (P.nd k)) := by
  rw [DoAudit.kfac_univ, P.NA_nd, P.parZ_extA]
  all_goals rfl

lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NA Finset.univ s v = c2 := by
  obtain ⟨h1, _, h3⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NA_o h1 h3, PMF.uniformOfFintype_apply]

lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t P.x = c2 := by
  rw [DoAudit.kfac_univ, P.NB_o P.hndx (fun e => P.hux' 0 e.symm), PMF.uniformOfFintype_apply]

lemma B_u0 (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.u 0) = PMF.pure false (ev t (P.u 0)) := by
  rw [DoAudit.kfac_univ, P.NB_u0]
  all_goals rfl

lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2))
    (hj : j ≠ 0) : kfac P.NB Finset.univ t (P.u j) = c2 := by
  rw [DoAudit.kfac_univ, P.NB_o (fun k e => P.hund j k e.symm)
    (fun e => hj (P.uinj e)), PMF.uniformOfFintype_apply]

lemma B_ndr (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NB Finset.univ t (P.nd P.r) =
      Bow.chan (xor (ev t P.x) (toBool (P.parZ P.r (ev t)))) (ev t (P.nd P.r)) := by
  rw [DoAudit.kfac_univ, P.NB_ndr, P.parZ_extB, ext_restrict t P.pBx]
  all_goals rfl

lemma B_nd (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2))
    (hk : k ≠ P.r) :
    kfac P.NB Finset.univ t (P.nd k) = PMF.pure (toBool (P.parZ k (ev t))) (ev t (P.nd k)) := by
  rw [DoAudit.kfac_univ, P.NB_nd k hk, P.parZ_extB]
  all_goals rfl

lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NB Finset.univ t v = c2 := by
  obtain ⟨_, h2, h3⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NB_o h3 (fun e => h2 0 e.symm), PMF.uniformOfFintype_apply]

lemma C_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac P.NC Finset.univ s P.x =
      Bow.chan (toBool (∑ k ∈ P.Rt, ofBool (ev s (P.nd k)))) (ev s P.x) := by
  have hs : ∑ k ∈ P.Rt, ofBool (ext (s.restrict (Finset.subset_univ (P.gC.parents P.x))) (P.nd k)) =
      ∑ k ∈ P.Rt, ofBool (ev s (P.nd k)) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [ext_restrict s (P.pCx k (by simpa [Rt] using hk))])
  rw [DoAudit.kfac_univ, P.NC_x, hs]
  all_goals rfl

lemma C_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.u j) =
      PMF.pure (toBool (P.solN (P.Rg (ev s)) (P.M + 1) j)) (ev s (P.u j)) := by
  rw [DoAudit.kfac_univ, P.NC_u, P.Rg_ext]
  all_goals rfl

lemma C_nd (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    kfac P.NC Finset.univ s (P.nd k) = c2 := by
  rw [DoAudit.kfac_univ, P.NC_o (P.hndx k) (fun j => P.hund j k), PMF.uniformOfFintype_apply]

lemma C_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ P.R5) : kfac P.NC Finset.univ s v = c2 := by
  obtain ⟨h1, h2, _⟩ := P.mem_R5.mp hv
  rw [DoAudit.kfac_univ, P.NC_o h1 h2, PMF.uniformOfFintype_apply]

end RP
end RootPath
end Identification
