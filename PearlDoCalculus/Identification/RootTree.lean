import PearlDoCalculus.Identification.RootPath

/-!
# Root trees and embedded hedges

This file shows that the root-path configurations of `Identification/RootPath` always
exist inside a c-forest (round 16), and that a hedge only has to be embedded in the
graph (round 17).

Main results:
* `RootTree.rootTree_not_identifiable`: for an `RT` structure the latent path required by
  `RootPath` is constructed, so `P(roots | do(x))` is not identifiable.
* `RootTree.embedded_not_identifiable`: an `RT` structure inside `G` with roots in `Y`
  makes `P(Y | do(x))` not identifiable.

(The comments of the rounds below are still in Norwegian.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 16: stien finnes alltid

I runde 15 var stien av latente fra `u₀` til `u_r` en antakelse. Her konstrueres den:
`pth k` sier at `k` ligger på kjeden `r, bp r, bp (bp r), …`. Høyden vokser strengt
langs kjeden, så den er injektiv og ender i `0` (den eneste noden uten forelder).
Paritetsvilkåret følger: en node på kjeden (utenom `r`) har nøyaktig ett barn på
kjeden, `r` har ingen, og en node utenfor kjeden har ingen. -/

namespace Identification
namespace RootTree

open PathTree (b2z)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Konfigurasjonen fra runde 15, uten stien. -/
structure RT (G : DAG V) (n : ℕ) where
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

namespace RT

variable {G : DAG V} {n : ℕ} (T : RT G n)

/-- Røttene som noder. -/
def Y : Finset V := (Finset.univ.filter (fun k => T.dp k = none)).image T.nd

/-- Kjeden `r, bp r, bp (bp r), …` (til den går tom). -/
def chain : ℕ → Option (Fin (n + 2))
  | 0 => some T.r
  | m + 1 => (chain m).bind T.bp

lemma chain_succ (m : ℕ) : T.chain (m + 1) = (T.chain m).bind T.bp := rfl

/-- Langs kjeden vokser høyden minst med antall steg. -/
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

lemma chain_le (m : ℕ) {a : Fin (n + 2)} (ha : T.chain m = some a) : m ≤ T.ht a := by
  have := T.chain_ht 0 m (a := T.r) (b := a) rfl (by simpa using ha)
  omega

/-- Kjeden besøker ingen node to ganger. -/
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

/-- Kjeden når `0`. -/
lemma reach0 : ∃ m, T.chain m = some 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨a, ha⟩ := T.chain_some (Finset.univ.sup T.ht + 1) (fun m' _ => hc m')
  have h1 := T.chain_le _ ha
  have h2 : T.ht a ≤ Finset.univ.sup T.ht := Finset.le_sup (Finset.mem_univ a)
  omega

/-- **Stien:** `k` ligger på kjeden fra `r`. -/
noncomputable def pth (k : Fin (n + 2)) : Bool :=
  decide (∃ m ∈ Finset.range (Finset.univ.sup T.ht + 1), T.chain m = some k)

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

/-- Forelderen til en node på kjeden ligger på kjeden, og er ikke `r`. -/
lemma child_on (j k : Fin (n + 2)) (hb : T.bp j = some k) (hj : T.pth j = true) :
    T.pth k = true ∧ k ≠ T.r := by
  obtain ⟨m, hm⟩ := (T.pth_iff j).mp hj
  have hk : T.chain (m + 1) = some k := by rw [T.chain_succ, hm]; exact hb
  refine ⟨(T.pth_iff k).mpr ⟨m + 1, hk⟩, fun e => ?_⟩
  rw [e] at hk
  have := T.chain_inj hk (rfl : T.chain 0 = some T.r)
  omega

/-- Antall barn på kjeden: ett for en kjedenode utenom `r`, ellers null. -/
lemma sum_children (k : Fin (n + 2)) :
    (∑ j, if T.bp j = some k then b2z (T.pth j) else 0) =
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
          all_goals first | rfl | decide | simp [b2z]
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

/-- **Paritetsvilkåret fra runde 15 holder.** -/
lemma hpk (k : Fin (n + 2)) :
    b2z (T.pth k) + (∑ j, if T.bp j = some k then b2z (T.pth j) else 0) =
      if k = T.r then 1 else 0 := by
  rw [T.sum_children]
  by_cases hkr : k = T.r
  · subst hkr
    have hr : T.pth T.r = true := (T.pth_iff _).mpr ⟨0, rfl⟩
    simp [hr, b2z]
  · rw [if_neg hkr]
    cases hp : T.pth k
    · rw [if_neg (fun h => Bool.false_ne_true h.1)]
      all_goals first | rfl | decide | simp [b2z]
    · rw [if_pos ⟨rfl, hkr⟩]
      all_goals first | rfl | decide | simp [b2z]

/-- Konfigurasjonen med den konstruerte stien. -/
noncomputable def toRP : RootPath.RP G n where
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

end RT

/-- **c-skoger med flere røtter, uten stiantakelse.** Et latent tre som binder `x`
(gjennom `u₀`) til nodene, et rettet skog-mønster blant nodene, og `x → nd_r` for en
rot `r`. Er røttene og `x` observert og de latente ikke, er `P(røtter | do(x))` ikke
identifiserbar. -/
theorem rootTree_not_identifiable {G : DAG V} {n : ℕ} (T : RT G n) (O : Finset V)
    (hu : ∀ j, T.u j ∉ O) (hY : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} T.Y :=
  RootPath.rootPath_not_identifiable T.toRP O hu hY hx

end RootTree
end Identification

#print axioms Identification.RootTree.rootTree_not_identifiable

/-! ## Runde 17: innebygde hedger

En `RT`-struktur trenger bare å finnes *inne i* `G`: grafen kan ha flere kanter,
flere latente og flere noder enn strukturen bruker, og `Y` kan være større enn
røttene. Modellene ignorerer det overflødige (kjernene leser bare sine egne foreldre),
og `Identifiable.mono_Y` (runde 11) løfter resultatet fra røttene til `Y`.

Særlig dekker dette `x` med flere latente naboer. Er `x` et indre punkt i det latente
treet, er `F ∖ {x}` usammenhengende, så `(F, F ∖ {x})` er ingen hedge. Den riktige
hedgen er grenen som inneholder `nd_r`, med `x` som blad; den er en `RT`-struktur
inne i `G`. Det samme gjelder sykler blant de latente: velg et utspennende tre der
`x` er et blad. -/

namespace Identification
namespace RootTree

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Innebygd hedge.** Finnes en `RT`-struktur i `G` med røtter i `Y`, er
`P(Y | do(x))` ikke identifiserbar. -/
theorem embedded_not_identifiable {G : DAG V} {n : ℕ} (T : RT G n) (O Y : Finset V)
    (hu : ∀ j, T.u j ∉ O) (hR : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O)
    (hTY : T.Y ⊆ Y) (hd : Disjoint Y {T.x}) :
    ¬ Identifiable G (fun _ => Bool) O {T.x} Y :=
  fun h => rootTree_not_identifiable T O hu hR hx (h.mono_Y hd hTY)

end RootTree
end Identification

