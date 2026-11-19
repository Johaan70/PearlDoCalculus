import PearlDoCalculus.Identification.Identify

/-!
# ID soundness for sets

This file proves that the ID algorithm is sound for sets: if the blocks of the
c-components of `G_{X̄}` can be reached from `V` by Tian's steps (`Reach`), then
`P(Y | do(X))` is identifiable.

* Round 33: `id_sound_blocks` and `id_sound` (ID lines 4, 6 and 7 put together), with
  `Q_lat` (a purely latent block has factor 1) and `ccomp_cutIn_X` (in `G_{X̄}` the
  c-component of `x ∈ X` is `{x}`).
* Round 34: ID line 2, restriction to the ancestors of `Y`: `id_sound_anc`,
  `id_sound_anc_blocks` and `ccomp_ind_X`.

The section comments below are in Norwegian, as written during the work rounds.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 33: ID-algoritmen er sunn for mengder

Under `do(X = x)` lever modellen på `G_{X̄}` (`cutIn G X`). Dens c-komponenter er `{x}`
for hver `x ∈ X`, rene latente blokker, og blokker `D` utenfor `X`. Da er

  `P_X(O) = ∏_D Q_X[D]`  og  `Q_X[D] = Q[D]`  for `D` disjunkt med `X`

(`marginal_prod` på intervensjonsmodellen og `Q_do_gen`). Kan hver slik `D` nås fra `V`
med Tians steg (`Reach`, runde 32), er hver faktor bestemt av den observerte fordelingen
(`reach_ident`), og dermed hele `P_X` (`id_sound`). Dette er ID-algoritmens linje 4, 6
og 7 satt sammen; linje 2 (å kutte til forfedrene til `Y`) er ikke tatt med, så
hypotesen ser på alle c-komponentene, ikke bare dem som teller for `Y`.

* `Q_lat`: faktoren for en rent latent blokk er 1.
* `id_sound_blocks`: versjonen med vilkårlige blokker.
* `ccomp_cutIn_X`: i `G_{X̄}` er c-komponenten til `x ∈ X` bare `{x}`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **En rent latent blokk har faktor 1.** -/
lemma Q_lat [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V) (hT : T ⊆ U)
    (a : Assignment (α := α) Uᶜ) : Q M U T a = 1 := by
  unfold Q
  rw [← lat_one M U T a]
  refine tsum_congr (fun w => ?_)
  rw [Finset.inter_eq_right.mpr hT]

/-- **ID-sunnhet med blokker.** Blokkene er lukkede i `G_{X̄}`, disjunkte og dekker alt.
Hver blokk ligger i `X`, er rent latent, eller er disjunkt med `X` og kan nås fra `V`. -/
theorem id_sound_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock (cutIn G X) U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i)
    (hblk : ∀ i ∈ I, B i ⊆ X ∨ B i ⊆ U ∨ (Disjoint (B i) X ∧ Reach G U Finset.univ (B i)))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Uᶜ = (doModel M2 X xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [marginal_prod (doModel M1 X xv) U B I hcl hdisj hcov a,
      marginal_prod (doModel M2 X xv) U B I hcl hdisj hcov a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rcases hblk i hi with hsub | hlat | ⟨hdis, hRi⟩
    · rw [Q_do_gen M1 U (B i) X hXO xv a, Q_do_gen M2 U (B i) X hXO xv a]
      simp only [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
    · rw [Q_lat (doModel M1 X xv) U (B i) hlat a, Q_lat (doModel M2 X xv) U (B i) hlat a]
    · rw [Q_do_gen M1 U (B i) X hXO xv a, Q_do_gen M2 U (B i) X hXO xv a,
        Finset.sdiff_eq_self_of_disjoint hdis]
      congr 1
      have h := reach_ident M1 M2 U (B i) hRi hM hpos a
      unfold Q at h
      exact h
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

/-- I `G_{X̄}` har `x ∈ X` ingen latente naboer: c-komponenten er `{x}`. -/
theorem ccomp_cutIn_X (G : DAG V) (U X : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (cutIn G X) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from e).2 (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **ID-algoritmen er sunn.** Kan hver c-komponent av `G_{X̄}` som inneholder en
observert node utenfor `X` nås fra `V` med Tians steg, er `P(Y | do(X))` identifiserbar. -/
theorem id_sound [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (hR : ∀ y, y ∉ U → y ∉ X → Reach G U Finset.univ (ccomp (cutIn G X) U y))
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_blocks U X hXO id (Finset.univ.image (ccomp (cutIn G X) U)) ?_ ?_ ?_ ?_ Y hY
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (cutIn G X) U y
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v
    exact ⟨ccomp (cutIn G X) U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (cutIn G X) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl ((ccomp_cutIn_X G U X hXO hyX).trans (Finset.singleton_subset_iff.mpr hyX))
    · by_cases hU : ccomp (cutIn G X) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        have hdis : Disjoint (ccomp (cutIn G X) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (cutIn G X) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (cutIn G X) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_cutIn_X G U X hXO hzX hyz)]
            exact hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis hv h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvU hvX
        rw [ccomp_eq_of_mem hv] at hRv
        exact hRv

end CFactor
end Identification

#print axioms Identification.CFactor.Q_lat
#print axioms Identification.CFactor.id_sound_blocks
#print axioms Identification.CFactor.id_sound

/-! ## Runde 34: ID-algoritmens linje 2, avgrensning til forfedrene til `Y`

Runde 33 krevde at *alle* c-komponentene i `G_{X̄}` kunne nås. Linje 2 i ID-algoritmen
(Shpitser–Pearl 2006; Tian & Pearl 2002) ser bare på en ancestral mengde `S ⊇ Y`:

  `Σ_{O ∖ S} P_X(O) = Q_X[S] = ∏_D Q_X[S ∩ D]`,

der `D` løper over c-komponentene til `G_{X̄}[S]` (`DAG.induce (cutIn G X) S`). Første
likhet er `Q_marg` (runde 30) i intervensjonsmodellen, den andre en ny produktsetning der
blokkene bare trenger å være lukket innenfor `S` (`Q_prod_rel`). Kan hver `S ∩ D` som
inneholder en observert node utenfor `X` nås fra `V` (`Reach`), er `P(Y | do(X))`
identifiserbar (`id_sound_anc`). Med `S = An(Y)` i `G_{X̄}` er dette linje 2, 4, 6 og 7.

Overgangen fra summer over `O ∖ S` til marginalen på `Y` går via en omtelling
(`upd_iff`, `tsum_updX`, `fiber_eq`): to funksjoner med like summer over hver fiber
`{a[D := x'] : x'}` har like marginaler på enhver `Y` utenfor `D`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Produkt over blokker som bare er lukket innenfor `T₀`.** -/
theorem Q_prod_rel [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι) (T0 : Finset V) :
    ∀ T : Finset V, T ⊆ T0 → IsLatClosed G U T →
      (∀ i ∈ I, ∀ u ∈ U, ∀ v ∈ T0, G.edge u v → (u ∈ B i ↔ v ∈ B i)) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k)) → T ⊆ I.biUnion B →
      ∀ a, Q M U T a = ∏ i ∈ I, Q M U (T ∩ B i) a := by
  induction I using Finset.induction_on with
  | empty =>
    intro T _ _ _ _ hTI a
    have hT0 : T = ∅ := by simpa using hTI
    rw [hT0, Finset.prod_empty, Q_empty]
  | insert j I' hj ih =>
    intro T hTT0 hT hcl hdisj hTI a
    have hclj : ∀ u ∈ U, ∀ v ∈ T, G.edge u v → (u ∈ B j ↔ v ∈ B j) :=
      fun u hu v hv e => hcl j (Finset.mem_insert_self j I') u hu v (hTT0 hv) e
    rw [Finset.prod_insert hj, Q_split_rel M U T (B j) hT hclj a]
    congr 1
    have hT' : IsLatClosed G U (T ∩ (B j)ᶜ) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        Finset.mem_compl.mpr (fun huB => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
          ((hclj u hu v (Finset.mem_inter.mp hv).1 e).mp huB))⟩
    have hTI' : T ∩ (B j)ᶜ ⊆ I'.biUnion B := by
      intro v hv
      obtain ⟨hvT, hvB⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hTI hvT)
      rcases Finset.mem_insert.mp hi with hij | hi'
      · rw [hij] at hvi
        exact absurd hvi (Finset.mem_compl.mp hvB)
      · exact Finset.mem_biUnion.mpr ⟨i, hi', hvi⟩
    rw [ih (T ∩ (B j)ᶜ) (fun v hv => hTT0 (Finset.mem_inter.mp hv).1) hT'
      (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
      (fun i hi k hk => hdisj i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
      hTI' a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hne : i ≠ j := fun e => hj (e ▸ hi)
    have hs : T ∩ (B j)ᶜ ∩ B i = T ∩ B i := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_compl]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, fun h2 => Finset.disjoint_left.mp
          (hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j I') hne) h3 h2⟩, h3⟩
    rw [hs]

/-- **Én blokk under `do(X)`.** Ligger `C` i `X`, er den rent latent, eller er den disjunkt
med `X` og kan nås fra `V`, er faktoren i intervensjonsmodellen den samme for to modeller
med samme positive observerte fordeling. -/
lemma Q_do_eq [∀ v, Nonempty (α v)] (M1 M2 : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hM : M1.marginal Uᶜ = M2.marginal Uᶜ)
    (hpos : ∀ a, M1.marginal Uᶜ a ≠ 0) (C : Finset V)
    (hC : C ⊆ X ∨ C ⊆ U ∨ (Disjoint C X ∧ Reach G U Finset.univ C))
    (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M1 X xv) U C a = Q (doModel M2 X xv) U C a := by
  rcases hC with hsub | hlat | ⟨hdis, hRi⟩
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a]
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
  · rw [Q_lat (doModel M1 X xv) U C hlat a, Q_lat (doModel M2 X xv) U C hlat a]
  · rw [Q_do_gen M1 U C X hXO xv a, Q_do_gen M2 U C X hXO xv a,
      Finset.sdiff_eq_self_of_disjoint hdis]
    congr 1
    have h := reach_ident M1 M2 U C hRi hM hpos a
    unfold Q at h
    exact h

/-- Omtelling: `a'` er `a` med `D` byttet ut, og `a` har en fast verdi `c₀` på `D`,
nøyaktig når `a` er `a'` med `D` satt til `c₀` og `x'` er `a'` på `D`. -/
lemma upd_iff (U D : Finset V) (hD : D ⊆ Uᶜ) (c0 x' : Assignment (α := α) D)
    (a a' : Assignment (α := α) Uᶜ) :
    (a' = updX U D a x' ∧ a.restrict hD = c0) ↔ (a = updX U D a' c0 ∧ x' = a'.restrict hD) := by
  constructor
  · rintro ⟨rfl, h2⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · have e := congrFun h2 ⟨v.1, hv⟩
        simp only [Assignment.restrict] at e
        simp only [updX, dif_pos hv]
        exact e
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · funext v
      by_cases hv : v.1 ∈ D
      · simp only [updX, dif_pos hv, Assignment.restrict]
      · simp only [updX, dif_neg hv]
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict, updX, dif_pos hv]

/-- **Summen over alle tilordninger, fiber for fiber.** -/
lemma tsum_updX (U D : Finset V) (hD : D ⊆ Uᶜ) (c0 : Assignment (α := α) D)
    (g : Assignment (α := α) Uᶜ → ENNReal) :
    ∑' a', g a' = ∑' a : Assignment (α := α) Uᶜ,
      (if a.restrict hD = c0 then ∑' x' : Assignment (α := α) D, g (updX U D a x') else 0) := by
  calc ∑' a', g a'
      = ∑' a' : Assignment (α := α) Uᶜ, ∑' a : Assignment (α := α) Uᶜ,
          ∑' x' : Assignment (α := α) D,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) := by
        refine tsum_congr (fun a' => ?_)
        rw [tsum_eq_single (updX U D a' c0)]
        · rw [tsum_eq_single (a'.restrict hD)]
          · rw [if_pos ((upd_iff U D hD c0 (a'.restrict hD) (updX U D a' c0) a').mpr
              ⟨rfl, rfl⟩)]
          · intro x' hx'
            rw [if_neg (fun h => hx' ((upd_iff U D hD c0 x' (updX U D a' c0) a').mp h).2)]
        · intro a ha
          exact ENNReal.tsum_eq_zero.mpr (fun x' =>
            if_neg (fun h => ha ((upd_iff U D hD c0 x' a a').mp h).1))
    _ = ∑' a : Assignment (α := α) Uᶜ, ∑' a' : Assignment (α := α) Uᶜ,
          ∑' x' : Assignment (α := α) D,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) := ENNReal.tsum_comm
    _ = ∑' a : Assignment (α := α) Uᶜ, ∑' x' : Assignment (α := α) D,
          ∑' a' : Assignment (α := α) Uᶜ,
            (if a' = updX U D a x' ∧ a.restrict hD = c0 then g a' else 0) :=
        tsum_congr (fun a => ENNReal.tsum_comm)
    _ = _ := by
        refine tsum_congr (fun a => ?_)
        by_cases hP : a.restrict hD = c0
        · rw [if_pos hP]
          refine tsum_congr (fun x' => ?_)
          rw [tsum_eq_single (updX U D a x')]
          · rw [if_pos ⟨rfl, hP⟩]
          · intro a'' h
            rw [if_neg (fun h' => h h'.1)]
        · rw [if_neg hP]
          exact ENNReal.tsum_eq_zero.mpr (fun x' => ENNReal.tsum_eq_zero.mpr (fun a'' =>
            if_neg (fun h => hP h.2)))

/-- **Like fibersummer gir like marginaler** på enhver `Y` utenfor `D`. -/
lemma fiber_eq [∀ v, Nonempty (α v)] (U D : Finset V) (hD : D ⊆ Uᶜ) (Y : Finset V)
    (hY : Y ⊆ Uᶜ) (hYD : ∀ v ∈ Y, v ∉ D) (P1 P2 : Assignment (α := α) Uᶜ → ENNReal)
    (h : ∀ a, ∑' x' : Assignment (α := α) D, P1 (updX U D a x') =
      ∑' x' : Assignment (α := α) D, P2 (updX U D a x'))
    (b : Assignment (α := α) Y) :
    ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0) =
      ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P2 a else 0) := by
  have c0 : Assignment (α := α) D := fun _ => Classical.arbitrary _
  have hr : ∀ (a : Assignment (α := α) Uᶜ) (x' : Assignment (α := α) D),
      (updX U D a x').restrict hY = a.restrict hY := fun a x' => by
    funext ⟨v, hv⟩
    simp only [Assignment.restrict, updX, dif_neg (hYD v hv)]
  calc ∑' a : Assignment (α := α) Uᶜ, (if b = a.restrict hY then P1 a else 0)
      = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P1 (updX U D a x') else 0) else 0) :=
        tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P1 a else 0)
    _ = ∑' a : Assignment (α := α) Uᶜ, (if a.restrict hD = c0 then
          ∑' x' : Assignment (α := α) D, (if b = (updX U D a x').restrict hY
            then P2 (updX U D a x') else 0) else 0) := by
        refine tsum_congr (fun a => ?_)
        simp only [hr]
        by_cases hb : b = a.restrict hY
        · simp only [if_pos hb]
          rw [h a]
        · simp only [if_neg hb]
    _ = _ := (tsum_updX U D hD c0 (fun a => if b = a.restrict hY then P2 a else 0)).symm

/-- **ID med avgrensning til en ancestral mengde, med blokker.** -/
theorem id_sound_anc_blocks [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ)
    (S : Finset V) (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    {ι : Type*} [DecidableEq ι] (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, ∀ u ∈ U, ∀ v ∈ S, (cutIn G X).edge u v → (u ∈ B i ↔ v ∈ B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : S ⊆ I.biUnion B)
    (hblk : ∀ i ∈ I, S ∩ B i ⊆ X ∨ S ∩ B i ⊆ U ∨
      (Disjoint (S ∩ B i) X ∧ Reach G U Finset.univ (S ∩ B i)))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hlat : IsLatClosed (cutIn G X) U Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  have hlatS : IsLatClosed (cutIn G X) U S := fun v hv u _ e => hS v hv u e
  have hS' : ∀ v ∈ Finset.univ ∩ S, ∀ p ∈ Finset.univ, (cutIn G X).edge p v → p ∈ S :=
    fun v hv p _ e => hS v (Finset.mem_inter.mp hv).2 p e
  have hDO : (Finset.univ ∩ Sᶜ) \ U ⊆ Uᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hYD : ∀ v ∈ Y, v ∉ (Finset.univ ∩ Sᶜ) \ U := fun v hv hvD =>
    Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvD).1).2 (hYS hv)
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Y = (doModel M2 X xv).marginal Y := by
    intro xv
    have hQS : ∀ a, Q (doModel M1 X xv) U S a = Q (doModel M2 X xv) U S a := fun a => by
      rw [Q_prod_rel (doModel M1 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a,
        Q_prod_rel (doModel M2 X xv) U B I S S (Finset.Subset.refl S) hlatS hcl hdisj hcov a]
      exact Finset.prod_congr rfl (fun i hi => Q_do_eq M1 M2 U X hXO hM hpos _ (hblk i hi) xv a)
    have hfib : ∀ a, ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M1 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') =
        ∑' x' : Assignment (α := α) ((Finset.univ ∩ Sᶜ) \ U),
        Q (doModel M2 X xv) U Finset.univ (updX U ((Finset.univ ∩ Sᶜ) \ U) a x') := fun a => by
      rw [Q_marg (doModel M1 X xv) U Finset.univ S hlat hS' a,
        Q_marg (doModel M2 X xv) U Finset.univ S hlat hS' a, Finset.univ_inter S]
      exact hQS a
    ext b
    rw [← marginal_restrict (doModel M1 X xv) hY, ← marginal_restrict (doModel M2 X xv) hY,
      PMF.map_apply, PMF.map_apply]
    simp only [marginal_eq_Q]
    exact fiber_eq U ((Finset.univ ∩ Sᶜ) \ U) hDO Y hY hYD
      (Q (doModel M1 X xv) U Finset.univ) (Q (doModel M2 X xv) U Finset.univ) hfib b
  rw [hD]

/-- I `G_{X̄}[S]` har `x ∈ X` ingen latente naboer: c-komponenten er `{x}`. -/
theorem ccomp_ind_X (G : DAG V) (U X S : Finset V) (hXO : X ⊆ Uᶜ) {x : V} (hx : x ∈ X) :
    ccomp (DAG.induce (cutIn G X) S) U x ⊆ {x} :=
  ccomp_subset (fun u hu v e => by
    have hux : u ≠ x := fun h =>
      Finset.mem_compl.mp (hXO (show u ∈ X by rw [h]; exact hx)) hu
    have hvx : v ≠ x := fun h =>
      (show G.edge u v ∧ v ∉ X from
        (show u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v from e).2.2).2
        (show v ∈ X by rw [h]; exact hx)
    simp [hux, hvx]) (Finset.mem_singleton_self x)

/-- **ID-algoritmen med linje 2.** La `S ⊇ Y` være ancestral i `G_{X̄}` (for eksempel
forfedrene til `Y`). Kan hver c-komponent av `G_{X̄}[S]` med en observert node utenfor `X`
nås fra `V` med Tians steg, er `P(Y | do(X))` identifiserbar. -/
theorem id_sound_anc [∀ v, Nonempty (α v)] (U X : Finset V) (hXO : X ⊆ Uᶜ) (S : Finset V)
    (hS : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S)
    (hR : ∀ y ∈ S, y ∉ U → y ∉ X →
      Reach G U Finset.univ (S ∩ ccomp (DAG.induce (cutIn G X) S) U y))
    (Y : Finset V) (hYS : Y ⊆ S) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine id_sound_anc_blocks U X hXO S hS id
    (Finset.univ.image (ccomp (DAG.induce (cutIn G X) S) U)) ?_ ?_ ?_ ?_ Y hYS hY
  · intro i hi u hu v hv e
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed (DAG.induce (cutIn G X) S) U y u hu v
      (⟨hS v hv u e, hv, e⟩ : u ∈ S ∧ v ∈ S ∧ (cutIn G X).edge u v)
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v _
    exact Finset.mem_biUnion.mpr ⟨ccomp (DAG.induce (cutIn G X) S) U v,
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
      self_mem_ccomp (DAG.induce (cutIn G X) S) U v⟩
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    by_cases hyX : y ∈ X
    · exact Or.inl (fun z hz => (Finset.singleton_subset_iff.mpr hyX)
        (ccomp_ind_X G U X S hXO hyX (Finset.mem_inter.mp hz).2))
    · by_cases hU : S ∩ ccomp (DAG.induce (cutIn G X) S) U y ⊆ U
      · exact Or.inr (Or.inl hU)
      · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hU
        obtain ⟨hvS, hvC⟩ := Finset.mem_inter.mp hv
        have hdis0 : Disjoint (ccomp (DAG.induce (cutIn G X) S) U y) X := by
          rw [Finset.disjoint_left]
          intro z hz hzX
          have hyz : y ∈ ccomp (DAG.induce (cutIn G X) S) U z := by
            rw [ccomp_eq_of_mem hz]
            exact self_mem_ccomp (DAG.induce (cutIn G X) S) U y
          exact hyX (by
            rw [Finset.mem_singleton.mp (ccomp_ind_X G U X S hXO hzX hyz)]
            exact hzX)
        have hdis : Disjoint (S ∩ ccomp (DAG.induce (cutIn G X) S) U y) X :=
          Finset.disjoint_left.mpr (fun z hz hzX =>
            Finset.disjoint_left.mp hdis0 (Finset.mem_inter.mp hz).2 hzX)
        have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis0 hvC h
        refine Or.inr (Or.inr ⟨hdis, ?_⟩)
        have hRv := hR v hvS hvU hvX
        rw [ccomp_eq_of_mem hvC] at hRv
        exact hRv

end CFactor
end Identification

#print axioms Identification.CFactor.Q_prod_rel
#print axioms Identification.CFactor.fiber_eq
#print axioms Identification.CFactor.id_sound_anc_blocks
#print axioms Identification.CFactor.id_sound_anc

