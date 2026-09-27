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

variable {G : DAG V}

/-- For `v ∉ Z` er kjernefaktoren i intervensjonsmodellen den samme som i `M`,
på enhver mengde `S`. -/
lemma kfac_doModel_of_not_mem {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z : Assignment (α := α) Z) (S : Finset V) (a : Assignment (α := α) S)
    {v : V} (hv : v ∉ Z) :
    kfac (doModel M Z z) S a v = kfac M S a v := by
  have hpar : (cutIn G Z).parents v = G.parents v := parents_cutIn_of_not_mem hv
  unfold kfac
  by_cases hc : v ∈ S ∧ G.parents v ⊆ S
  · have hc' : v ∈ S ∧ (cutIn G Z).parents v ⊆ S := ⟨hc.1, by rw [hpar]; exact hc.2⟩
    rw [dif_pos hc', dif_pos hc]
    simp only [doModel, dif_neg hv]
    all_goals rfl
  · have hc' : ¬ (v ∈ S ∧ (cutIn G Z).parents v ⊆ S) :=
      fun h => hc ⟨h.1, by rw [← hpar]; exact h.2⟩
    rw [dif_neg hc', dif_neg hc]

/-- **B2.** En intervensjon på `Z` endrer ikke marginalen på en ancestral mengde
disjunkt fra `Z`. -/
theorem doModel_marginal_of_ancestral {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (a : Assignment (α := α) A) :
    (doModel M Z z).marginal A a = M.marginal A a := by
  have hA' : ∀ v ∈ A, ∀ w, (cutIn G Z).edge w v → w ∈ A :=
    fun v hv w hw => hA v hv w hw.1
  rw [marginal_ancestral_apply (doModel M Z z) A hA' a, marginal_ancestral_apply M A hA a]
  exact Finset.prod_congr rfl
    (fun v hv => kfac_doModel_of_not_mem M Z z A a (Finset.disjoint_left.mp hAZ hv))

/-- B2 for delmengder av en ancestral mengde disjunkt fra `Z`. -/
theorem doModel_marginal_of_sub {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (S : Finset V) (hSA : S ⊆ A) (s : Assignment (α := α) S) :
    (doModel M Z z).marginal S s = M.marginal S s := by
  have hPMF : (doModel M Z z).marginal A = M.marginal A :=
    PMF.ext (doModel_marginal_of_ancestral M Z z A hA hAZ)
  rw [← marginal_restrict (doModel M Z z) hSA, ← marginal_restrict M hSA, hPMF]

/-- `Z(W)`: nodene i `Z` som ikke er forfedre til noen node i `W`. -/
noncomputable def Z2 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∉ ancestors G W)

/-- Resten av `Z`: nodene som er forfedre til `W`. -/
noncomputable def Z1 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∈ ancestors G W)

/-- Blokkert fra start gir blokkert i tilstand `.bwd`: `.bwd` legger bare til en
betingelse i første node. -/
lemma start_imp_bwd {H : DAG V} {Z : Finset V} {a b : V} (p : Walk H a b) :
    Walk.blockedAux Z .start p → Walk.blockedAux Z .bwd p := by
  cases p <;> simp [Walk.blockedAux] <;> tauto

/-- Nås `y` fra `z ∈ Z₂` i `G`, finnes en siste `Z₂`-node `z′` som når `y` i
`G_{\overline{Z₂}}`. -/
lemma reach_last {Z W : Finset V} {z y : V} (hz : z ∈ Z2 G Z W) (hr : G.Reaches z y) :
    ∃ z' ∈ Z2 G Z W, (cutIn G (Z2 G Z W)).Reaches z' y := by
  induction hr with
  | refl => exact ⟨z, hz, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨z', hz', hr'⟩ := ih
    by_cases hc : c ∈ Z2 G Z W
    · exact ⟨c, hc, Relation.ReflTransGen.refl⟩
    · exact ⟨z', hz', Relation.ReflTransGen.tail hr' ⟨hbc, hc⟩⟩

/-- Nås `c` fra `z′` i `cutIn G Z`, og ligger ingen node `z′` når i `W`, finnes en
vandring fra `c` bakover til `z′` som er åpen i tilstand `.bwd`. -/
lemma open_back {Z W : Finset V} {z' : V} (hnW : ∀ v, G.Reaches z' v → v ∉ W) :
    ∀ {c : V}, (cutIn G Z).Reaches z' c →
      ∃ p : Walk (cutIn G Z) c z', ¬ Walk.blockedAux W .bwd p := by
  intro c hr
  induction hr with
  | refl => exact ⟨Walk.nil _, by simp [Walk.blockedAux]⟩
  | @tail b c hab hbc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Walk.bwd hbc p, ?_⟩
    have hcW : c ∉ W :=
      hnW c (reaches_mono (H := G) (H' := cutIn G Z) (fun u v h => h.1)
        (Relation.ReflTransGen.tail hab hbc))
    simp only [Walk.blockedAux]
    tauto

/-- **B1 for `Y`.** Under hypotesen i regel 3 er ingen node i `Z₂` forfar til `Y`. -/
theorem not_reaches_Y {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    {z y : V} (hz : z ∈ Z2 G Z W) (hy : y ∈ Y) : ¬ G.Reaches z y := by
  intro hr
  obtain ⟨z', hz', hr'⟩ := reach_last hz hr
  have hz'Z : z' ∈ Z := (Finset.mem_filter.mp hz').1
  have hz'W : z' ∉ ancestors G W := (Finset.mem_filter.mp hz').2
  have hnW : ∀ v, G.Reaches z' v → v ∉ W :=
    fun v hv hvW => hz'W (mem_ancestors_iff.mpr ⟨v, hvW, hv⟩)
  obtain ⟨p, hp⟩ := open_back hnW hr'
  exact hp (start_imp_bwd p (dsep_of_dsepPath (h y hy z' hz'Z) p))

/-- **B1.** `Z₂` er disjunkt fra An(Y ∪ W). -/
theorem disjoint_anc_Z2 {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z) :
    Disjoint (ancestors G (Y ∪ W)) (Z2 G Z W) := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hv
  rcases Finset.mem_union.mp hs with hs | hs
  · exact not_reaches_Y h hvZ hs hr
  · exact (Finset.mem_filter.mp hvZ).2 (mem_ancestors_iff.mpr ⟨s, hs, hr⟩)

end Rule3

#print axioms Rule3.dsepPath_mono
#print axioms Rule3.dsepSet_mono
#print axioms Rule3.doModel_marginal_of_ancestral
#print axioms Rule3.doModel_marginal_of_sub
#print axioms Rule3.not_reaches_Y
#print axioms Rule3.disjoint_anc_Z2
