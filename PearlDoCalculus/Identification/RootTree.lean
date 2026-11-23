import PearlDoCalculus.Identification.RootPath

/-!
# Root trees and embedded hedges

This file shows that the root-path configurations of `Identification/RootPath` always
exist inside a c-forest, and that such a hedge only has to be embedded in the graph.

Why it is needed: `TianIff` proves the negative half of `tian_iff` by finding a
`RootTree` structure inside `G` and applying `embedded_not_identifiable` (except for the bow, which
`Identification/Bow` covers).

How the proof goes: the latent path that `RootPath` assumes is the chain
`r, bp r, bp (bp r), …` in the latent tree. The height grows strictly along the chain, so
the chain visits no node twice and reaches `0`, the only node without a parent
(`reach0`). Counting children on the chain gives the parity condition (`hpk`). For an
embedded structure, the models ignore every node, edge and latent they do not use, and
`Identifiable.mono_Y` passes from the roots to any larger `Y`.

Main results:
* `RootTree.not_identifiable`: for a `RootTree` structure the latent path required by
  `RootPath` is constructed, so `P(roots | do(x))` is not identifiable.
* `RootTree.embedded_not_identifiable`: a `RootTree` structure inside `G` with roots in `Y`
  makes `P(Y | do(x))` not identifiable.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## The latent path always exists

In `RootPath` the path of latents from `u₀` to `u_r` is an assumption. Here it is
constructed: `pth k` says that `k` lies on the chain `r, bp r, bp (bp r), …`. The height
grows strictly along the chain, so the chain is injective and ends in `0` (the only node
without a parent). The parity condition follows: a node on the chain (other than `r`) has
exactly one child on the chain, `r` has none, and a node off the chain has none. -/

namespace Identification

open ZMod2 (ofBool)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The root-path configuration `RootPath` without the path `pth` and its parity condition. -/
structure RootTree (G : DAG V) (n : ℕ) where
  x : V
  nd : Fin (n + 2) → V
  u : Fin (n + 2) → V
  bp : Fin (n + 2) → Option (Fin (n + 2))
  ht : Fin (n + 2) → ℕ
  dp : Fin (n + 2) → Option (Fin (n + 2))
  r : Fin (n + 2)
  hbp0 : ∀ j, bp j = none ↔ j = 0
  hht : ∀ j k, bp j = some k → ht j < ht k
  hr : dp r = none
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

namespace RootTree

variable {G : DAG V} {n : ℕ} (T : RootTree G n)

/-- The roots as nodes. -/
def Y : Finset V := (Finset.univ.filter (fun k => T.dp k = none)).image T.nd

/-- The chain `r, bp r, bp (bp r), …` (until it runs out). -/
def chain : ℕ → Option (Fin (n + 2))
  | 0 => some T.r
  | m + 1 => (chain m).bind T.bp

/-- One step of the chain. -/
lemma chain_succ (m : ℕ) : T.chain (m + 1) = (T.chain m).bind T.bp := rfl

/-- Along the chain the height grows at least by the number of steps. -/
lemma chain_ht (m d : ℕ) {a b : Fin (n + 2)} (ha : T.chain m = some a)
    (hb : T.chain (m + d) = some b) : T.ht a + d ≤ T.ht b := by
  induction d generalizing b with
  | zero =>
    have e : a = b := Option.some.inj (ha.symm.trans hb)
    subst e
    omega
  | succ d ih =>
    rw [← Nat.add_assoc, T.chain_succ] at hb
    cases hc : T.chain (m + d) with
    | none =>
      rw [hc] at hb
      simp at hb
    | some c =>
      rw [hc] at hb
      change T.bp c = some b at hb
      have h1 := ih (b := c) hc
      have h2 := T.hht c b hb
      omega

/-- The `m`-th node of the chain has height at least `m`. -/
lemma chain_le (m : ℕ) {a : Fin (n + 2)} (ha : T.chain m = some a) : m ≤ T.ht a := by
  have := T.chain_ht 0 m (a := T.r) (b := a) rfl (by simpa using ha)
  omega

/-- The chain visits no node twice. -/
lemma chain_inj {m m' : ℕ} {a : Fin (n + 2)} (h : T.chain m = some a)
    (h' : T.chain m' = some a) : m = m' := by
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have := T.chain_ht m (d + 1) h (by rw [← Nat.add_assoc]; exact h')
    omega
  · exact heq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have := T.chain_ht m' (d + 1) h' (by rw [← Nat.add_assoc]; exact h)
    omega

/-- As long as the chain has not reached `0`, it has not run out. -/
lemma chain_some (m : ℕ) (h0 : ∀ m' ≤ m, T.chain m' ≠ some 0) :
    ∃ a, T.chain m = some a := by
  induction m with
  | zero => exact ⟨T.r, rfl⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih (fun m' hm' => h0 m' (by omega))
    have ha0 : a ≠ 0 := fun e => h0 m (by omega) (by rw [ha, e])
    cases hb : T.bp a with
    | none => exact absurd ((T.hbp0 a).mp hb) ha0
    | some b => exact ⟨b, by rw [T.chain_succ, ha]; exact hb⟩

/-- The chain reaches `0`. -/
lemma reach0 : ∃ m, T.chain m = some 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha⟩ := T.chain_some (Finset.univ.sup T.ht + 1) (fun m' _ => hc m')
  have h1 := T.chain_le _ ha
  have h2 : T.ht a ≤ Finset.univ.sup T.ht := Finset.le_sup (Finset.mem_univ a)
  omega

/-- **The path:** `k` lies on the chain from `r`. -/
noncomputable def pth (k : Fin (n + 2)) : Bool :=
  decide (∃ m ∈ Finset.range (Finset.univ.sup T.ht + 1), T.chain m = some k)

/-- `k` is on the path exactly when the chain reaches it. -/
lemma pth_iff (k : Fin (n + 2)) : T.pth k = true ↔ ∃ m, T.chain m = some k := by
  unfold pth
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨m, _, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, Finset.mem_range.mpr ?_, hm⟩
    have h1 := T.chain_le m hm
    have h2 : T.ht k ≤ Finset.univ.sup T.ht := Finset.le_sup (Finset.mem_univ k)
    omega

/-- The parent of a node on the chain lies on the chain and is not `r`. -/
lemma child_on (j k : Fin (n + 2)) (hb : T.bp j = some k) (hj : T.pth j = true) :
    T.pth k = true ∧ k ≠ T.r := by
  obtain ⟨m, hm⟩ := (T.pth_iff j).mp hj
  have hk : T.chain (m + 1) = some k := by rw [T.chain_succ, hm]; exact hb
  refine ⟨(T.pth_iff k).mpr ⟨m + 1, hk⟩, fun e => ?_⟩
  rw [e] at hk
  have := T.chain_inj hk (rfl : T.chain 0 = some T.r)
  omega

/-- The number of children on the chain: one for a chain node other than `r`, otherwise zero. -/
lemma sum_children (k : Fin (n + 2)) :
    (∑ j, if T.bp j = some k then ofBool (T.pth j) else 0) =
      if T.pth k = true ∧ k ≠ T.r then 1 else 0 := by
  by_cases hk : T.pth k = true ∧ k ≠ T.r
  · rw [if_pos hk]
    obtain ⟨m', hm'⟩ := (T.pth_iff k).mp hk.1
    cases m' with
    | zero => exact absurd (Option.some.inj hm').symm hk.2
    | succ m =>
      rw [T.chain_succ] at hm'
      cases hc : T.chain m with
      | none =>
        rw [hc] at hm'
        simp at hm'
      | some j0 =>
        rw [hc] at hm'
        change T.bp j0 = some k at hm'
        rw [Finset.sum_eq_single j0]
        · rw [if_pos hm', (T.pth_iff j0).mpr ⟨m, hc⟩]
          all_goals rfl
        · intro j _ hj
          split_ifs with hb
          · cases hjp : T.pth j
            · rfl
            · exfalso
              obtain ⟨m2, hm2⟩ := (T.pth_iff j).mp hjp
              have e1 : T.chain (m2 + 1) = some k := by rw [T.chain_succ, hm2]; exact hb
              have e2 : T.chain (m + 1) = some k := by rw [T.chain_succ, hc]; exact hm'
              have e3 : m2 = m := by have := T.chain_inj e1 e2; omega
              rw [e3, hc] at hm2
              exact hj (Option.some.inj hm2).symm
          · rfl
        · intro h
          exact absurd (Finset.mem_univ j0) h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with hb
    · cases hjp : T.pth j
      · rfl
      · exact absurd (T.child_on j k hb hjp) hk
    · rfl

/-- **The parity condition of `RootPath` holds.** -/
lemma hpk (k : Fin (n + 2)) :
    ofBool (T.pth k) + (∑ j, if T.bp j = some k then ofBool (T.pth j) else 0) =
      if k = T.r then 1 else 0 := by
  rw [T.sum_children]
  by_cases hkr : k = T.r
  · subst hkr
    have hr : T.pth T.r = true := (T.pth_iff _).mpr ⟨0, rfl⟩
    simp [hr, ZMod2.ofBool]
  · rw [if_neg hkr]
    cases hp : T.pth k
    · rw [if_neg (fun h => Bool.false_ne_true h.1)]
      all_goals rfl
    · rw [if_pos ⟨rfl, hkr⟩]
      all_goals rfl

/-- The configuration with the constructed path. -/
noncomputable def toRootPath : RootPath G n where
  x := T.x
  nd := T.nd
  u := T.u
  bp := T.bp
  ht := T.ht
  dp := T.dp
  r := T.r
  pth := T.pth
  hbp0 := T.hbp0
  hht := T.hht
  hr := T.hr
  hp0 := (T.pth_iff 0).mpr T.reach0
  hpk := T.hpk
  hux := T.hux
  hun := T.hun
  hub := T.hub
  hdp := T.hdp
  hxr := T.hxr
  ndinj := T.ndinj
  uinj := T.uinj
  hund := T.hund
  hux' := T.hux'
  hndx := T.hndx

/-- **C-forests with several roots, without a path assumption.** A latent tree that binds
`x` (through `u₀`) to the nodes, a directed forest pattern among the nodes, and `x → nd_r`
for a root `r`. If the roots and `x` are observed and the latents are not, then
`P(roots | do(x))` is not identifiable. -/
theorem not_identifiable (O : Finset V) (hu : ∀ j, T.u j ∉ O)
    (hY : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} T.Y :=
  T.toRootPath.not_identifiable O hu hY hx

end RootTree
end Identification

/-! ## Embedded hedges

A `RootTree` structure only has to exist *inside* `G`: the graph may have more edges, more
latents and more nodes than the structure uses, and `Y` may be larger than the roots. The
models ignore what is left over (the kernels read only their own parents), and
`Identifiable.mono_Y` (`Identification/Basic`) lifts the result from the roots to `Y`.

In particular this covers an `x` with several latent neighbours. If `x` is an inner
point of the latent tree, then `F ∖ {x}` is disconnected, so `(F, F ∖ {x})` is not a
hedge. The right hedge is the branch that contains `nd_r`, with `x` as a leaf; it is an
`RootTree` structure inside `G`. The same holds for cycles among the latents: choose a spanning
tree in which `x` is a leaf. -/

namespace Identification
namespace RootTree

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Embedded hedge.** If `G` contains a `RootTree` structure with its roots in `Y`, then
`P(Y | do(x))` is not identifiable. -/
theorem embedded_not_identifiable {G : DAG V} {n : ℕ} (T : RootTree G n) (O Y : Finset V)
    (hu : ∀ j, T.u j ∉ O) (hR : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O)
    (hTY : T.Y ⊆ Y) (hd : Disjoint Y {T.x}) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} Y :=
  fun h => T.not_identifiable O hu hR hx (h.mono_Y hd hTY)

end RootTree
end Identification
