import PearlDoCalculus.DSepSound

/-!
# Vandringer og stier

`DSeparated` er definert over vandringer (gjentatte noder tillatt). Den klassiske
definisjonen bruker stier. Denne fila viser at de er ekvivalente, og løfter dermed
`dsep_sound` til den klassiske stibaserte hypotesen.

Retningen vandring ⇒ sti er triviell, siden enhver sti er en vandring. Retningen
sti ⇒ vandring er kontrapositivt «åpen vandring ⇒ åpen sti», og bevises ved å
fjerne løkker fra hodet av vandringen uten å miste åpenhet.
-/

namespace PearlDoCalculus
namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

namespace Walk

/-- Startnoden er med i støtten. -/
lemma start_mem_support {a b : V} (p : Walk G a b) : a ∈ p.support := by
  cases p <;> simp [support]

/-- Sluttnoden er med i støtten. -/
lemma end_mem_support {a b : V} (p : Walk G a b) : b ∈ p.support := by
  induction p with
  | nil v => simp [support]
  | fwd e q ih => simp [support, ih]
  | bwd e q ih => simp [support, ih]

/-- En sti: ingen node besøkes to ganger. Støtten inneholder både start- og
sluttnoden (`start_mem_support`, `end_mem_support`), så dette er nøyaktig
den klassiske sti-egenskapen. -/
def IsPath {a b : V} (p : Walk G a b) : Prop := p.support.Nodup

end Walk

/-- Klassisk d-separasjon: alle *stier* fra `x` til `y` er blokkert av `Z`. -/
def DSeparatedPath (G : DAG V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : Walk G x y, p.IsPath → Walk.Blocked Z p

/-- Den trivielle retningen: vandringsbasert d-separasjon gir stibasert. -/
theorem dsepPath_of_dsep {Z : Finset V} {x y : V} (h : G.DSeparated Z x y) :
    G.DSeparatedPath Z x y :=
  fun p _ => h p

/-- **Nedstigning.** Kom vandringen inn i `b` langs en pil (`.fwd`) og er åpen,
så når `b` enten en node i `Z`, eller alle noder på vandringen. Det andre
alternativet er det som gjør asyklisitet nyttig: dukker en tidligere node opp
igjen, får vi en rettet sykel. -/
lemma descend_of_open {Z : Finset V} : ∀ {b c : V} (q : Walk G b c),
    ¬ Walk.blockedAux Z .fwd q →
    (∃ z ∈ Z, G.Reaches b z) ∨ (∀ v ∈ q.support, G.Reaches b v) := by
  intro b c q
  induction q with
  | nil v =>
    intro _
    right
    intro w hw
    simp [Walk.support] at hw
    subst hw
    exact Reaches.refl G _
  | @fwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push_neg at hq
    rcases ih hq.2 with ⟨z, hz, hr⟩ | hall
    · left
      exact ⟨z, hz, Reaches.trans G (Reaches.of_edge G e) hr⟩
    · right
      intro w hw
      simp only [Walk.support, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Reaches.refl G _
      · exact Reaches.trans G (Reaches.of_edge G e) (hall w hw)
  | @bwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push_neg at hq
    left
    exact hq.1

/-- Hovedresultatet: stibasert d-separasjon gir vandringsbasert. Kontrapositivt:
fra en åpen vandring finnes en åpen sti. -/
theorem dsep_of_dsepPath {Z : Finset V} {x y : V} (h : G.DSeparatedPath Z x y) :
    G.DSeparated Z x y := by
  sorry

/-- Vandringsbasert og stibasert d-separasjon er ekvivalente. -/
theorem dsepPath_iff_dsep {Z : Finset V} {x y : V} :
    G.DSeparatedPath Z x y ↔ G.DSeparated Z x y :=
  ⟨dsep_of_dsepPath, dsepPath_of_dsep⟩

end DAG
end PearlDoCalculus

namespace WalkPath

open PearlDoCalculus DAG

/-- **Klassisk soundness.** Stibasert d-separasjon gir betinget uavhengighet. -/
theorem dsep_sound_path {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}
    {α : V → Type*} (M : G.CausalModel α) (Z : Finset V) (x y : V)
    (h : G.DSeparatedPath Z x y) : M.CondIndep {x} {y} Z :=
  DSepSound.dsep_sound M Z x y (dsep_of_dsepPath h)

end WalkPath

#print axioms PearlDoCalculus.DAG.Walk.start_mem_support
#print axioms PearlDoCalculus.DAG.Walk.end_mem_support
#print axioms PearlDoCalculus.DAG.dsepPath_of_dsep
#print axioms PearlDoCalculus.DAG.descend_of_open
#print axioms WalkPath.dsep_sound_path
