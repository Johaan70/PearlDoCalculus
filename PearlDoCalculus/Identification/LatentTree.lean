import PearlDoCalculus.Identification.HedgeTemplate

/-!
# Latent trees

Hedge counter-models for graphs whose latent connections form a tree over `x` and the
observed nodes, and whose directed edges form a tree towards `y`. Here `x` may have
several latent neighbours, and the intervention set `X` may contain further nodes outside
the hedge.

Why it is needed: it covers a large family of non-identifiable graphs. The later
two-root, multi-root, root-path and root-tree files reuse its definitions (`LT`).

How the proof goes: model A is the parity model. The equation system is solved from the
bottom up in the latent tree, and `u₀ = y` follows from a double count over both trees.
This gives an instance of `HedgeTmpl.Tm`. For sets `X` the extra nodes of `X` are uniform
noise without descendants, so intervening on them changes nothing.

Main results: `Identification.LatentTree.latentTree_not_identifiable`,
`Identification.latentTree_not_identifiable_set`,
`Identification.latentTree_not_identifiable_XY`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 9: latent tre

De latente forbindelsene danner et tre over `x` og de observerte nodene
`nd₀, …, nd_{n+1}` (med `y = nd_{n+1}`). Hver node `nd_k` har sin egen latente
`u_k` mot en forelder i treet, `bp k` (eller `x` når `k = 0`). De rettede kantene er
et tre mot `y`: hver `nd_j` (`j ≤ n`) peker på `nd_{dp j}`. Dette omfatter
stiene fra runde 8. Fra runde 10 kan `x` ha flere latente naboer: alle `u_j` med
`bp j = none` peker på `x`, og `x` er en støyende kopi av summen deres.

Modell A er paritetsmodellen. Likningssystemet løses nedenfra og opp i det latente
treet (`solN`, med en høydefunksjon `ht` som garanterer at barn ligger lavere), og
`u₀ = y` følger av en dobbelttelling over begge trærne (`dc`). -/

namespace Identification
namespace LatentTree

open HedgeChain (ev)
open ZMod2 (ofBool toBool eq_toBool_iff)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Et latent tre med et rettet tre mot `y`. -/
structure LT (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 1) → Fin (n + 2)
  hht : ∀ j k, bp j = some k → ht j < ht k
  hux : ∀ j, bp j = none → G.edge (u j) x
  hun : ∀ k, G.edge (u k) (nd k)
  hub : ∀ j k, bp j = some k → G.edge (u j) (nd k)
  hdp : ∀ j, G.edge (nd j.castSucc) (nd (dp j))
  hxy : G.edge x (nd (Fin.last (n + 1)))
  ndinj : Function.Injective nd
  uinj : Function.Injective u
  hund : ∀ j k, u j ≠ nd k
  hux' : ∀ j, u j ≠ x
  hndx : ∀ k, nd k ≠ x

namespace LT

variable {G : DAG V} {n : ℕ} (P : LT G n)

/-- Grafen for modell A. -/
noncomputable def gA : DAG V where
  edge a b := (∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨ (∃ k, a = P.u k ∧ b = P.nd k) ∨
    (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ | ⟨j, h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hux j0 h0)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hun k)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hub j k hb)
    · rw [h1, h2]; exact G.rank_strict_mono _ _ (P.hdp j)

lemma gA_edge (a b : V) : P.gA.edge a b ↔ ((∃ j, P.bp j = none ∧ a = P.u j ∧ b = P.x) ∨
    (∃ k, a = P.u k ∧ b = P.nd k) ∨ (∃ j k, P.bp j = some k ∧ a = P.u j ∧ b = P.nd k) ∨
    (∃ j, a = P.nd j.castSucc ∧ b = P.nd (P.dp j))) := Iff.rfl

lemma pxu (j : Fin (n + 2)) (h : P.bp j = none) : P.u j ∈ P.gA.parents P.x :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inl ⟨j, h, rfl, rfl⟩))
lemma pnu (k : Fin (n + 2)) : P.u k ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inl ⟨k, rfl, rfl⟩)))
lemma pnb (j k : Fin (n + 2)) (h : P.bp j = some k) : P.u j ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨j, k, h, rfl, rfl⟩))))
lemma pnd (j : Fin (n + 1)) (k : Fin (n + 2)) (h : P.dp j = k) :
    P.nd j.castSucc ∈ P.gA.parents (P.nd k) :=
  DAG.mem_parents.mpr ((P.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr ⟨j, rfl, by rw [h]⟩))))

lemma hsA : ∀ v, P.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (P.gA_edge a v).mp ha with ⟨j0, h0, h1, h2⟩ | ⟨k, h1, h2⟩ | ⟨j, k, hb, h1, h2⟩ |
      ⟨j, h1, h2⟩
  · rw [h1, h2]; exact P.hux j0 h0
  · rw [h1, h2]; exact P.hun k
  · rw [h1, h2]; exact P.hub j k hb
  · rw [h1, h2]; exact P.hdp j

lemma src : ∀ b, ∀ a ∈ P.gA.parents b,
    (∃ j, P.u j = a) ∨ (∃ i, P.nd (Fin.castSucc i) = a) := by
  intro b a ha
  rw [DAG.mem_parents] at ha
  rcases (P.gA_edge a b).mp ha with ⟨j0, _, h1, _⟩ | ⟨k, h1, _⟩ | ⟨j, k, _, h1, _⟩ | ⟨j, h1, _⟩
  · exact Or.inl ⟨j0, h1.symm⟩
  · exact Or.inl ⟨k, h1.symm⟩
  · exact Or.inl ⟨j, h1.symm⟩
  · exact Or.inr ⟨j, h1.symm⟩

/-! ### Kjernene -/

noncomputable def fn (k : Fin (n + 2))
    (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents (P.nd k))) : Bool :=
  toBool (ofBool (pa ⟨P.u k, P.pnu k⟩) +
    (∑ j, if h : P.bp j = some k then ofBool (pa ⟨P.u j, P.pnb j k h⟩) else 0) +
    ∑ j, if h : P.dp j = k then ofBool (pa ⟨P.nd j.castSucc, P.pnd j k h⟩) else 0)

lemma fn_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.fn k (s.restrict (Finset.subset_univ _)) =
      toBool (ofBool (ev s (P.u k)) +
        (∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0) +
        ∑ j, if P.dp j = k then ofBool (ev s (P.nd j.castSucc)) else 0) := by
  unfold fn
  congr 1

noncomputable def fx (pa : Assignment (α := fun _ : V => Bool) (P.gA.parents P.x)) : Bool :=
  toBool (∑ j, if h : P.bp j = none then ofBool (pa ⟨P.u j, P.pxu j h⟩) else 0)

lemma fx_s (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    P.fx (s.restrict (Finset.subset_univ _)) =
      toBool (∑ j, if P.bp j = none then ofBool (ev s (P.u j)) else 0) := by
  unfold fx
  congr 1

/-! ### Løsningen nedenfra og opp -/

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

/-! ### Dobbelttellingen -/

lemma dc (ℓ N : Fin (n + 2) → ZMod 2)
    (hE : ∀ k, ℓ k = (N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
      ∑ j, if P.bp j = some k then ℓ j else 0) :
    (∑ j, if P.bp j = none then ℓ j else 0) = N (Fin.last (n + 1)) := by
  have h1 : ∀ j, (∑ k, if P.bp j = some k then ℓ j else 0) =
      if P.bp j = none then 0 else ℓ j := by
    intro j
    cases hb : P.bp j with
    | none => simp
    | some k0 => simp
  have h2 : ∀ j : Fin (n + 1), (∑ k, if P.dp j = k then N j.castSucc else 0) = N j.castSucc := by
    intro j
    simp
  have hsplit : ∑ j, ℓ j = (∑ j, if P.bp j = none then ℓ j else 0) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hD : ∑ k, ∑ j, (if P.dp j = k then N j.castSucc else 0) = ∑ j, N (Fin.castSucc j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h2 j)
  have hB : ∑ k, ∑ j, (if P.bp j = some k then ℓ j else 0) =
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hsum : ∑ k, ℓ k = (∑ k, N k + ∑ j, N (Fin.castSucc j)) +
      ∑ j, (if P.bp j = none then 0 else ℓ j) := by
    calc ∑ k, ℓ k = ∑ k, ((N k + ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ j, if P.bp j = some k then ℓ j else 0) := Finset.sum_congr rfl (fun k _ => hE k)
      _ = (∑ k, N k + ∑ k, ∑ j, if P.dp j = k then N j.castSucc else 0) +
          ∑ k, ∑ j, if P.bp j = some k then ℓ j else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ k, N k + ∑ j, N (Fin.castSucc j)) + ∑ j, (if P.bp j = none then 0 else ℓ j) := by
        rw [hD, hB]
  have hN : ∑ k, N k + ∑ j, N (Fin.castSucc j) = N (Fin.last (n + 1)) := by
    rw [Fin.sum_univ_castSucc]
    have := CharTwo.add_self_eq_zero (∑ j : Fin (n + 1), N j.castSucc)
    linear_combination this
  have := hsplit.symm.trans hsum
  rw [hN] at this
  exact add_right_cancel this

/-! ### Likningene -/

def nz (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  ofBool (Fin.lastCases (motive := fun _ => Bool) c b k)

def rr (b : Fin (n + 1) → Bool) (c : Bool) (k : Fin (n + 2)) : ZMod 2 :=
  nz b c k + ∑ j, if P.dp j = k then nz b c j.castSucc else 0

def off (j : Fin (n + 2)) (b : Fin (n + 1) → Bool) (c : Bool) : Bool :=
  toBool (P.solN (P.rr b c) (P.M + 1) j)

lemma nz_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    nz (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      ofBool (ev s (P.nd k)) := by
  refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [nz]

lemma rr_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k =
      ofBool (ev s (P.nd k)) + ∑ j, if P.dp j = k then ofBool (ev s (P.nd j.castSucc)) else 0 := by
  simp only [rr, P.nz_eq]

lemma E_iff (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (k : Fin (n + 2)) :
    ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) ↔
      ofBool (ev s (P.u k)) =
        P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))) k +
          ∑ j, if P.bp j = some k then ofBool (ev s (P.u j)) else 0 := by
  rw [P.fn_s, eq_toBool_iff, P.rr_eq]
  exact ZMod2.eq_add_add_iff_eq_add_add _ _ _ _

lemma key (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
    ∀ j, ev s (P.u j) = P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1)))) := by
  have hall : ((∀ i, ev s (P.nd (Fin.castSucc i)) = P.fn (Fin.castSucc i) (s.restrict (Finset.subset_univ _))) ∧
      ev s (P.nd (Fin.last (n + 1))) = P.fn (Fin.last (n + 1)) (s.restrict (Finset.subset_univ _))) ↔
      ∀ k, ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _)) :=
    ⟨fun ⟨h1, h2⟩ k => Fin.lastCases (motive := fun k =>
        ev s (P.nd k) = P.fn k (s.restrict (Finset.subset_univ _))) h2 h1 k,
      fun h => ⟨fun i => h _, h _⟩⟩
  refine hall.trans ((forall_congr' fun k => P.E_iff s k).trans
    ((P.sol_iff (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1)))))
      (fun k => ofBool (ev s (P.u k)))).trans (forall_congr' fun j => ?_)))
  unfold off
  exact (eq_toBool_iff _ _).symm

lemma hfx (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V))
    (h : ∀ j, ev s (P.u j) =
      P.off j (fun i => ev s (P.nd (Fin.castSucc i))) (ev s (P.nd (Fin.last (n + 1))))) :
    P.fx (s.restrict (Finset.subset_univ _)) = ev s (P.nd (Fin.last (n + 1))) := by
  have h' : ∀ k, ofBool (ev s (P.u k)) =
      P.solN (P.rr (fun i => ev s (P.nd i.castSucc)) (ev s (P.nd (Fin.last (n + 1))))) (P.M + 1) k :=
    fun k => (eq_toBool_iff _ _).mp (h k)
  have hE := (P.sol_iff _ (fun k => ofBool (ev s (P.u k)))).mpr h'
  simp only [P.rr_eq] at hE
  have hd := P.dc (fun k => ofBool (ev s (P.u k))) (fun k => ofBool (ev s (P.nd k))) hE
  rw [P.fx_s]
  exact ((eq_toBool_iff _ _).mpr hd.symm).symm

/-- Konfigurasjonen som en mal. -/
noncomputable def toTm : HedgeTmpl.Tm G n where
  x := P.x
  y := P.nd (Fin.last (n + 1))
  w := fun i => P.nd (Fin.castSucc i)
  u := P.u
  gA := P.gA
  hsA := P.hsA
  fx := P.fx
  src := P.src
  fw := fun i => P.fn (Fin.castSucc i)
  fy := P.fn (Fin.last (n + 1))
  off := P.off
  hfx := P.hfx
  key := P.key
  hxy := P.hxy
  winj := fun a b h => Fin.castSucc_injective _ (P.ndinj h)
  uinj := P.uinj
  huw := fun j i => P.hund j _
  hux' := P.hux'
  huy' := fun j => P.hund j _
  hwx := fun i => P.hndx _
  hwy' := fun i h => (Fin.castSucc_lt_last i).ne (P.ndinj h)

end LT

/-- **Latent tre.** Danner de latente forbindelsene et tre over `x` og de observerte
nodene, og danner de rettede kantene et tre mot `y`, og er `x → y`,
så er `P(y | do(x))` ikke identifiserbar fra noen `O` som inneholder `x` og `y`, men
ingen latent. -/
theorem latentTree_not_identifiable {G : DAG V} {n : ℕ} (P : LT G n) (O : Finset V)
    (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} {P.nd (Fin.last (n + 1))} :=
  P.toTm.not_ident O hu hx hy

end LatentTree
end Identification

#print axioms Identification.LatentTree.latentTree_not_identifiable

namespace Identification

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Latent tre, mengdeversjon.** -/
theorem latentTree_not_identifiable_set {G : DAG V} {n : ℕ} (P : LatentTree.LT G n)
    (O Y : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O)
    (hyY : P.nd (Fin.last (n + 1)) ∈ Y) (hd : Disjoint Y {P.x}) :
    ¬ Identifiable G (fun _ => Bool) O {P.x} Y :=
  not_identifiable_of_mem (LatentTree.latentTree_not_identifiable P O hu hx hy) hyY hd

end Identification

#print axioms Identification.latentTree_not_identifiable_set

/-! ## Runde 12: mengder `X`

Inneholder `X` noden `x` og ellers bare noder utenfor hedgen (resten `R`), er
`P(y | do(X))` fortsatt ikke identifiserbar. I begge modellene er nodene i `R`
uniform støy uten etterkommere, så inngrep på dem endrer ingenting: i modell A gir
regel 3 (B2) det direkte, og i modell B skriver vi `do(X)` som `do(X ∖ {x})` etter
`do(x)` og bruker B2 på den indre modellen. -/

namespace Identification
namespace HedgeTmpl
namespace Tm

open HedgeChain (ev)

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : DAG V} {n : ℕ} (T : Tm G n)

/-- `do(X)` i modell A. -/
lemma doA_X (O X : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R)
    (x0 : Assignment (α := fun _ : V => Bool) X)
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mA X x0).marginal {T.y} y0 = T.mB.marginal {T.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel T.mA X x0) (doModel T.NA X x0)
    (BowGen.kfac_lift_doG T.hsA T.NA X x0) {T.y}]
  have hanc : ∀ v ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w), ∀ a,
      T.gA.edge a v → a ∈ insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w) := by
    intro v _ a ha
    have hp : a ∈ T.gA.parents v := DAG.mem_parents.mpr ha
    rcases T.src v a hp with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> simp
  have hdisj : Disjoint (insert T.y (Finset.univ.image T.u ∪ Finset.univ.image T.w)) X := by
    rw [Finset.disjoint_right]
    intro v hv
    rcases hX v hv with rfl | hR
    · simp [T.dxy, T.hux', T.hwx]
    · obtain ⟨_, h2, h3, h4⟩ := T.mem_R.mp hR
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, not_or, not_exists]
      exact ⟨h2, h3, h4⟩
  rw [Rule3.doModel_marginal_of_sub T.NA X x0 _ hanc hdisj {T.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac T.mA T.NA (BowGen.kfac_liftG T.hsA T.NA) {T.y},
    marginal_eq_of_subset (T.obsEq O hu) (show ({T.y} : Finset V) ⊆ O by simpa using hy)]

/-- `do(X)` i modell B er `do(x)`. -/
lemma doB_X (X : Finset V) (hxX : T.x ∈ X) (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R)
    (x0 : Assignment (α := fun _ : V => Bool) X)
    (y0 : Assignment (α := fun _ : V => Bool) {T.y}) :
    (doModel T.mB X x0).marginal {T.y} y0 =
      (doModel T.mB {T.x} (x0.restrict (Finset.singleton_subset_iff.mpr hxX))).marginal
        {T.y} y0 := by
  have hyX : T.y ∉ X := by
    intro hy
    rcases hX _ hy with h | h
    · exact T.dxy h.symm
    · exact (T.mem_R.mp h).2.1 rfl
  set x1 := x0.restrict (Finset.singleton_subset_iff.mpr hxX) with hx1
  set x2 := x0.restrict (Finset.erase_subset T.x X) with hx2
  rw [Completeness.marginal_eq_of_kfac (doModel T.mB X x0) (doModel T.NB X x0)
      (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB X x0) {T.y},
    Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} x1) (doModel T.NB {T.x} x1)
      (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB {T.x} x1) {T.y}]
  have hk : ∀ u v, kfac (doModel T.NB X x0) Finset.univ u v =
      kfac (doModel (doModel T.NB {T.x} x1) (X.erase T.x) x2) Finset.univ u v := by
    intro u v
    rw [kfac_doModel, kfac_doModel, kfac_doModel]
    by_cases h1 : v ∈ X.erase T.x
    · rw [dif_pos (Finset.mem_of_mem_erase h1), dif_pos h1]
      rfl
    · rw [dif_neg h1]
      by_cases h2 : v = T.x
      · subst h2
        rw [dif_pos hxX, dif_pos (Finset.mem_singleton_self _)]
        rfl
      · have h3 : v ∉ X := fun hv => h1 (Finset.mem_erase.mpr ⟨h2, hv⟩)
        rw [dif_neg h3, dif_neg (show v ∉ ({T.x} : Finset V) by simpa using h2)]
  rw [Completeness.marginal_eq_of_kfac (doModel T.NB X x0)
    (doModel (doModel T.NB {T.x} x1) (X.erase T.x) x2) hk {T.y}]
  have hA : ∀ v ∈ ({T.x, T.y} : Finset V), ∀ w,
      (cutIn (BowGen.g1 G T.x T.y T.hxy) {T.x}).edge w v → w ∈ ({T.x, T.y} : Finset V) := by
    intro v _ w hw
    have hw' : (w = T.x ∧ v = T.y) ∧ v ∉ ({T.x} : Finset V) := hw
    simp [hw'.1.1]
  have hAX : Disjoint ({T.x, T.y} : Finset V) (X.erase T.x) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (Finset.mem_erase.mp hv').1 rfl
    · exact hyX (Finset.mem_of_mem_erase hv')
  exact Rule3.doModel_marginal_of_sub (doModel T.NB {T.x} x1) (X.erase T.x) x2
    {T.x, T.y} hA hAX {T.y} (by simp) y0

/-- Selvmotsigelsen fra `do(x)`-likheten alene. -/
lemma contra (O : Finset V) (hu : ∀ j, T.u j ∉ O) (hy : T.y ∈ O)
    (hE : ∀ b : Bool, (doModel T.mA {T.x} (fun _ => b)).marginal {T.y} (fun _ => true) =
      (doModel T.mB {T.x} (fun _ => b)).marginal {T.y} (fun _ => true)) : False := by
  have hyx : T.y ≠ T.x := T.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G T.x T.y T.hxy).edge w T.x := by
    intro w hw
    have hw' : w = T.x ∧ T.x = T.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G T.x T.y T.hxy ({T.y} ∪ {T.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G T.x T.y T.hxy {T.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        T.mB.marginal {T.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ {T.x}) :=
      fun v => if v.1 = T.x then b else true
    have htx : t.restrict (show ({T.x} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = T.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ {T.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = T.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := hE b
    rw [T.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel T.mB {T.x} _)
        (doModel T.NB {T.x} _)
        (BowGen.kfac_lift_doG (BowGen.hsB G T.x T.y T.hxy) T.NB {T.x} _) {T.y}] at e
    have fd := Adjustment.frontdoor_step1 T.NB {T.x} {T.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {T.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({T.y} : Finset V) {T.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t T.y (by simp) (DAG.parents_subset_of_closed hS21 T.y (by simp)),
      BowGen.kfac_eqG _ _ t T.x (by simp) (DAG.parents_subset_of_closed hS21 T.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {T.x} hS1, Finset.prod_singleton,
      BowGen.kfac_eqG _ {T.x} _ T.x (by simp) (DAG.parents_subset_of_closed hS1 T.x (by simp))] at fd
    rw [T.NB_y, T.NB_o hyx.symm T.hux', T.NB_o hyx.symm T.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

/-- **Malen med en mengde `X`.** -/
theorem not_ident_X (O X : Finset V) (hu : ∀ j, T.u j ∉ O) (hx : T.x ∈ O) (hy : T.y ∈ O)
    (hxX : T.x ∈ X) (hX : ∀ v ∈ X, v = T.x ∨ v ∈ T.R) :
    ¬ Identifiable G (fun _ => Bool) O X {T.y} := by
  intro h
  have hyX : T.y ∉ X := by
    intro hy'
    rcases hX _ hy' with h' | h'
    · exact T.dxy h'.symm
    · exact (T.mem_R.mp h').2.1 rfl
  apply T.contra O hu hy
  intro b
  let t : Assignment (α := fun _ : V => Bool) ({T.y} ∪ X) :=
    fun v => if v.1 = T.y then true else b
  have htX : t.restrict (show X ⊆ {T.y} ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
    funext ⟨v, hv⟩
    have hvy : v ≠ T.y := fun e => hyX (e ▸ hv)
    simp [t, Assignment.restrict, hvy]
  have htY : t.restrict (show ({T.y} : Finset V) ⊆ {T.y} ∪ X by
      intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
    funext ⟨v, hv⟩
    have : v = T.y := Finset.mem_singleton.mp hv
    subst this
    simp [t, Assignment.restrict]
  have e := h T.mA T.mB (T.obsEq O hu) (T.posA O hu hx) t
  rw [htX, htY] at e
  calc (doModel T.mA {T.x} (fun _ => b)).marginal {T.y} (fun _ => true)
      = T.mB.marginal {T.y} (fun _ => true) := T.doA O hu hy _ _
    _ = (doModel T.mA X (fun _ => b)).marginal {T.y} (fun _ => true) :=
        (T.doA_X O X hu hy hX _ _).symm
    _ = (doModel T.mB X (fun _ => b)).marginal {T.y} (fun _ => true) := e
    _ = (doModel T.mB {T.x} (fun _ => b)).marginal {T.y} (fun _ => true) :=
        T.doB_X X hxX hX _ _

end Tm
end HedgeTmpl

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Latent tre med mengder `X` og `Y`.** -/
theorem latentTree_not_identifiable_XY {G : DAG V} {n : ℕ} (P : LatentTree.LT G n)
    (O X Y : Finset V) (hu : ∀ j, P.u j ∉ O) (hx : P.x ∈ O) (hy : P.nd (Fin.last (n + 1)) ∈ O)
    (hxX : P.x ∈ X) (hX : ∀ v ∈ X, v = P.x ∨ v ∈ P.toTm.R)
    (hyY : P.nd (Fin.last (n + 1)) ∈ Y) (hd : Disjoint Y X) :
    ¬ Identifiable G (fun _ => Bool) O X Y :=
  not_identifiable_of_mem (P.toTm.not_ident_X O X hu hx hy hxX hX) hyY hd

end Identification

#print axioms Identification.latentTree_not_identifiable_XY
