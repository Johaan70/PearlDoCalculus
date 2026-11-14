import PearlDoCalculus.Identification

/-!
# Verma-begrensningen i det klassiske eksemplet

Noder: `0 = u` (latent), `1 = a`, `2 = b`, `3 = c`, `4 = d`.
Kanter: `a → b → c → d` og `b ↔ d` (`u → b`, `u → d`).

Ingen betinget uavhengighet mellom de observerte fanger denne grafen, men

  `Σ_b P(b | a) · P(d | a, b, c)`  avhenger ikke av `a`

(Verma & Pearl 1990). Her:

1. `verma_identify`: `P(a,b,c) · P(a) · Q[{u,b,d}] = P(a,b,c,d) · P(a,b)`, fra `anc_factor`
   på fire ancestrale mengder. Med positiv `P` er altså
   `Q[{u,b,d}] = P(a,b,c,d) P(a,b) / (P(a,b,c) P(a)) = P(b | a) P(d | a,b,c)`
   (`vermaF_eq_Q`).
2. `verma_Q`: summen av `Q[{u,b,d}]` over `b` avhenger bare av `c` og `d`
   (`verma_sum`: `{u, d}` er ancestral innenfor `{u, b, d}`, og foreldrene til `d` er `c`, `u`).
3. `verma_constraint`: for hver modell på grafen med positiv `P`, og hver verdi-type, er
   `Σ_b P(a,b,c,d) P(a,b) / (P(a,b,c) P(a))` den samme for to tilordninger som er like på
   `c` og `d`, uansett `a`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor

namespace Verma

/-- Verma-grafen: `a → b → c → d`, `u → b`, `u → d`. -/
def vG : DAG (Fin 5) where
  edge u v := (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 4))
  decEdge := fun u v => inferInstanceAs (Decidable
    ((u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 0 ∧ (v = 2 ∨ v = 4))))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide

variable {α : Fin 5 → Type*} [∀ v, Nonempty (α v)]

/-- **`Q[{u, b, d}]` uttrykt ved `P`**, uten divisjon. -/
theorem verma_identify (M : vG.CausalModel α) (a : Assignment (α := α) ({0} : Finset (Fin 5))ᶜ) :
    M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {0, 1, 2, 3}) (a.restrict (subO {0} {0, 1, 2, 3})) *
        M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {1}) (a.restrict (subO {0} {1})) *
        Q M {0} {0, 2, 4} a =
      M.marginal (({0} : Finset (Fin 5))ᶜ ∩ Finset.univ) (a.restrict (subO {0} Finset.univ)) *
        M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {0, 1, 2}) (a.restrict (subO {0} {0, 1, 2})) := by
  have hT : ∀ u ∈ ({0} : Finset (Fin 5)), ∀ v, vG.edge u v →
      (u ∈ ({0, 2, 4} : Finset (Fin 5)) ↔ v ∈ ({0, 2, 4} : Finset (Fin 5))) := by decide
  have E1 := anc_factor M {0} {0, 1, 2} {0, 2, 4} (by decide) hT a
  have E2 := anc_factor M {0} {0, 1, 2, 3} {0, 2, 4} (by decide) hT a
  have E3 := anc_factor M {0} {1} {0, 2, 4} (by decide) hT a
  have E4 := anc_factor M {0} Finset.univ {0, 2, 4} (by decide) hT a
  rw [show ({0, 1, 2} ∩ {0, 2, 4} : Finset (Fin 5)) = {0, 2} by decide,
    show ({0, 1, 2} ∩ ({0, 2, 4} : Finset (Fin 5))ᶜ : Finset (Fin 5)) = {1} by decide] at E1
  rw [show ({0, 1, 2, 3} ∩ {0, 2, 4} : Finset (Fin 5)) = {0, 2} by decide,
    show ({0, 1, 2, 3} ∩ ({0, 2, 4} : Finset (Fin 5))ᶜ : Finset (Fin 5)) = {1, 3} by decide] at E2
  rw [show ({1} ∩ {0, 2, 4} : Finset (Fin 5)) = ∅ by decide, Q_empty,
    show ({1} ∩ ({0, 2, 4} : Finset (Fin 5))ᶜ : Finset (Fin 5)) = {1} by decide] at E3
  rw [show (Finset.univ ∩ ({0, 2, 4} : Finset (Fin 5))ᶜ : Finset (Fin 5)) = {1, 3} by decide,
    show (Finset.univ ∩ {0, 2, 4} : Finset (Fin 5)) = {0, 2, 4} by decide] at E4
  rw [E1, E2, E3, E4]
  ring

/-- Den observerte funksjonen `P(a,b,c,d) P(a,b) / (P(a,b,c) P(a))`, altså
`P(b | a) · P(d | a, b, c)`. -/
noncomputable def vermaF (M : vG.CausalModel α)
    (a : Assignment (α := α) ({0} : Finset (Fin 5))ᶜ) : ENNReal :=
  M.marginal (({0} : Finset (Fin 5))ᶜ ∩ Finset.univ) (a.restrict (subO {0} Finset.univ)) *
      M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {0, 1, 2}) (a.restrict (subO {0} {0, 1, 2})) /
    (M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {0, 1, 2, 3}) (a.restrict (subO {0} {0, 1, 2, 3})) *
      M.marginal (({0} : Finset (Fin 5))ᶜ ∩ {1}) (a.restrict (subO {0} {1})))

/-- Med positiv `P` er den observerte funksjonen nøyaktig faktoren `Q[{u, b, d}]`. -/
theorem vermaF_eq_Q (M : vG.CausalModel α)
    (hpos : ∀ b, M.marginal ({0} : Finset (Fin 5))ᶜ b ≠ 0)
    (a : Assignment (α := α) ({0} : Finset (Fin 5))ᶜ) :
    vermaF M a = Q M {0} {0, 2, 4} a := by
  unfold vermaF
  have h1 := marginal_restrict_ne_zero M (subO {0} {0, 1, 2, 3}) a (hpos a)
  have h2 := marginal_restrict_ne_zero M (subO {0} {1}) a (hpos a)
  symm
  rw [ENNReal.eq_div_iff (mul_ne_zero h1 h2)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  exact verma_identify M a

/-- Summen av `Q[{u, b, d}]` over `b` avhenger bare av `c` og `d`. -/
theorem verma_Q (M : vG.CausalModel α) (a a' : Assignment (α := α) ({0} : Finset (Fin 5))ᶜ)
    (hc : a ⟨3, by decide⟩ = a' ⟨3, by decide⟩) (hd : a ⟨4, by decide⟩ = a' ⟨4, by decide⟩) :
    ∑' x' : Assignment (α := α) (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}),
        Q M {0} {0, 2, 4} (updX {0} (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}) a x') =
      ∑' x' : Assignment (α := α) (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}),
        Q M {0} {0, 2, 4} (updX {0} (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}) a' x') := by
  have key : ∀ z : Fin 5, z ∉ ({0} : Finset (Fin 5)) →
      (z ∈ ({0, 2, 4} : Finset (Fin 5)) ∩ {0, 4} ∨
        ∃ t ∈ ({0, 2, 4} : Finset (Fin 5)) ∩ {0, 4}, vG.edge z t) → z = 3 ∨ z = 4 := by
    decide
  refine verma_sum M {0} {0, 2, 4} {0, 4}
    (show ∀ v ∈ ({0, 2, 4} : Finset (Fin 5)), ∀ u ∈ ({0} : Finset (Fin 5)), vG.edge u v →
      u ∈ ({0, 2, 4} : Finset (Fin 5)) by decide)
    (by decide) a a' (fun z hz hz' => ?_)
  rcases key z hz hz' with rfl | rfl
  · exact hc
  · exact hd

/-- **Verma-begrensningen.** For hver modell på Verma-grafen med positiv `P` er
`Σ_b P(a,b,c,d) P(a,b) / (P(a,b,c) P(a))` den samme for to tilordninger som er like på
`c` og `d`; den avhenger altså ikke av `a`. -/
theorem verma_constraint (M : vG.CausalModel α)
    (hpos : ∀ b, M.marginal ({0} : Finset (Fin 5))ᶜ b ≠ 0)
    (a a' : Assignment (α := α) ({0} : Finset (Fin 5))ᶜ)
    (hc : a ⟨3, by decide⟩ = a' ⟨3, by decide⟩) (hd : a ⟨4, by decide⟩ = a' ⟨4, by decide⟩) :
    ∑' x' : Assignment (α := α) (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}),
        vermaF M (updX {0} (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}) a x') =
      ∑' x' : Assignment (α := α) (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}),
        vermaF M (updX {0} (({0, 2, 4} ∩ ({0, 4} : Finset (Fin 5))ᶜ) \ {0}) a' x') := by
  simp only [vermaF_eq_Q M hpos]
  exact verma_Q M a a' hc hd

end Verma

#print axioms Verma.verma_identify
#print axioms Verma.vermaF_eq_Q
#print axioms Verma.verma_constraint
