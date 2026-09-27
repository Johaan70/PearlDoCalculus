import PearlDoCalculus.DoCalculus

/-!
# Regel 3

Kjeden er `P_z = P_{z₂,z₁} → P_{z₂} → P`, der `Z₂` er nodene i `Z` som ikke er
forfedre til `W`. Fase 1 i denne fila: subgraf-monotonitet for d-separasjon.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical

namespace Rule3

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En vandring i en graf med færre kanter er en vandring i den større grafen. -/
def mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    {a b : V} → Walk H' a b → Walk H a b
  | _, _, .nil v => .nil v
  | _, _, .fwd e p => .fwd (hsub _ _ e) (mapSub hsub p)
  | _, _, .bwd e p => .bwd (hsub _ _ e) (mapSub hsub p)

lemma support_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    ∀ {a b : V} (p : Walk H' a b), (mapSub hsub p).support = p.support := by
  intro a b p
  induction p with
  | nil v => rfl
  | fwd e p ih => simp [mapSub, Walk.support, ih]
  | bwd e p ih => simp [mapSub, Walk.support, ih]

/-- Nås en node i den mindre grafen, nås den i den større. -/
lemma reaches_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {u v : V} (h : H'.Reaches u v) : H.Reaches u v :=
  Relation.ReflTransGen.mono (fun a b hab => hsub a b hab) h

/-- Blokkert i den større grafen gir blokkert i den mindre: ikke-kollidere
blokkerer likt, og en kollider har færre etterkommere i den mindre grafen. -/
lemma blocked_of_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} : ∀ (inc : Incoming) {a b : V} (p : Walk H' a b),
    Walk.blockedAux Z inc (mapSub hsub p) → Walk.blockedAux Z inc p := by
  intro inc a b p
  induction p generalizing inc with
  | nil v => intro h; simpa [mapSub, Walk.blockedAux] using h
  | fwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
  | bwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
      | exact Or.imp (fun h z hz hr => h z hz (reaches_mono hsub hr)) (ih _)

/-- **Subgraf-monotonitet.** Stibasert d-separasjon overlever at kanter fjernes. -/
theorem dsepPath_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} {x y : V} (h : H.DSeparatedPath Z x y) :
    H'.DSeparatedPath Z x y := by
  intro p hp
  have hp' : (mapSub hsub p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hp
  exact blocked_of_mapSub hsub .start p (h (mapSub hsub p) hp')

/-- Mengdeversjonen av subgraf-monotonitet. -/
theorem dsepSet_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z X Y : Finset V} (h : SetSound.DSeparatedSet H Z X Y) :
    SetSound.DSeparatedSet H' Z X Y :=
  fun x hx y hy => dsepPath_mono hsub (h x hx y hy)

end Rule3

#print axioms Rule3.dsepPath_mono
#print axioms Rule3.dsepSet_mono
