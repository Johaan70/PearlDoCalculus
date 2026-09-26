import PearlDoCalculus.WalkPath
import PearlDoCalculus.Lauritzen

/-!
# Mengdeversjonen av d-separasjonens soundness

For mengder `X`, `Y`, `Z` med `X` og `Y` disjunkte fra `Z`: er hvert par
`x ∈ X`, `y ∈ Y` d-separert av `Z` i klassisk (stibasert) forstand, så er
`X` og `Y` betinget uavhengige gitt `Z`.

Parvis betinget uavhengighet gir *ikke* mengde-uavhengighet i alminnelighet,
så beviset kan ikke settes sammen fra `dsep_sound_path` for hvert par. Det går
gjennom separasjon i moralgrafen til An(X ∪ Y ∪ Z), som i `DSepSound`, med
Lauritzen og separatorpartisjonen generalisert til mengder.
-/

open PearlDoCalculus DAG DAG.CausalModel

namespace SetSound

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- Mengde-d-separasjon: hvert par er d-separert i klassisk (stibasert) forstand. -/
def DSeparatedSet (G : DAG V) (Z X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, G.DSeparatedPath Z x y

/-- Mengde-separasjon i en urettet graf: hvert par er separert av `Z`. -/
def SeparatesSet (H : SimpleGraph V) (Z X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, Separates H Z x y

/-- **Lauritzen for mengder.** -/
theorem moral_sep_of_dsep_set (X Y : Finset V) {Z : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (h : DSeparatedSet G Z X Y) :
    SeparatesSet (moralGraph G (ancestors G (X ∪ Y ∪ Z))) Z X Y := by
  sorry

/-- **Separatorpartisjon for mengder.** -/
lemma separator_partition_set {H : SimpleGraph V} {Z X Y : Finset V}
    (h : SeparatesSet H Z X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ∃ L R : Finset V,
      X ⊆ L ∧ Y ⊆ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  sorry

/-- **Soundness for mengder.** Klassisk d-separasjon av mengder gir
betinget uavhengighet. -/
theorem dsep_sound_set {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (h : DSeparatedSet G Z X Y) :
    M.CondIndep X Y Z := by
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have hA := DSepSound.A_closed (G := G) (X ∪ Y ∪ Z)
  have hsep := moral_sep_of_dsep_set X Y hXZ hYZ h
  obtain ⟨L, R, hXL, hYR, hLR, hLZ, hRZ, hcover, hnoadj⟩ :=
    separator_partition_set hsep hXZ hYZ
  obtain ⟨F, Gf, hF⟩ := joint_splits (CausalModel.restrictTo M _ hA) L Z R
    hLZ hLR hRZ.symm hcover (DSepSound.family_side hA hcover hnoadj)
  obtain ⟨F', Gf', hF'⟩ := DSepSound.product_form_mono (CausalModel.restrictTo M _ hA)
    hLR hLZ hRZ hXL hYR F Gf hF
  have hci' : CondIndep (CausalModel.restrictTo M _ hA) X Y Z :=
    DSepSound.condIndep_of_form _ X Y Z (Disjoint.mono hXL hYR hLR) hXZ hYZ F' Gf' hF'
  exact DSepSound.condIndep_transfer M _ hA hci' (subset_ancestors _)

end SetSound

#print axioms SetSound.dsep_sound_set
