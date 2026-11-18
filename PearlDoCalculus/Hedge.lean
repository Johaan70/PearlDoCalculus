import PearlDoCalculus.Idc

/-!
# Mot fullstendighet: der ID står fast (steg H2 i HANDOFF avsnitt 7)

Runde 41: når IDENTIFY sier nei, står den fast ved en mengde `T` med

* `C ⊊ T`, og hele `T` er forfedre til `C` innenfor `G[T]` (`ancIn G T C = T`);
* `T` er latent-lukket, og er c-lukningen av `C` innenfor en større mengde.

Dette er Tians feiltilfelle `A = T`, og kandidaten til hedgen `(C, T)`. Drivstoffet i
`identifyTop` er nok: hvert steg krymper `T` strengt (`identifyN_false`). `idCheck_false`
gir et slikt vitne for en av blokkene når hele ID-sjekken sier nei.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **IDENTIFY står fast** ved `T` med målet `C`. -/
structure Stuck (G : DAG V) (U C T : Finset V) : Prop where
  sub : C ⊆ T
  ne : C ≠ T
  anc : ancIn G T C = T
  lat : IsLatClosed G U T
  cc : ∃ T', C ⊆ T' ∧ T ⊆ T' ∧ ccIn G U T' C = T

/-- **Når IDENTIFY sier nei, står den fast et sted** (med nok drivstoff). -/
theorem identifyN_false (G : DAG V) (U : Finset V) :
    ∀ n T C, C ⊆ T → IsLatClosed G U T → (∃ T', C ⊆ T' ∧ T ⊆ T' ∧ ccIn G U T' C = T) →
      T.card < n → identifyN G U n T C = false → ∃ T₀, Stuck G U C T₀ := by
  intro n
  induction n with
  | zero =>
    intro T C _ _ _ hn _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro T C hCT hT hcc hn h
    have hAT : ancIn G T C ⊆ T := anc_sub G T C hCT
    have hCA : C ⊆ ancIn G T C := anc_sup G T C
    simp only [identifyN] at h
    by_cases h1 : ancIn G T C = C
    · rw [if_pos h1] at h
      exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : ancIn G T C = T
      · exact ⟨T, ⟨hCT, fun e => h1 (h2.trans e.symm), h2, hT, hcc⟩⟩
      · rw [if_neg h2] at h
        have hA : IsLatClosed G U (ancIn G T C) := fun v hv u hu e =>
          anc_closed G T C hCT u (hT v (hAT hv) u hu e) ⟨v, hv, e⟩
        have hT'A : ccIn G U (ancIn G T C) C ⊆ ancIn G T C := cc_sub G U _ C hCA
        have hCT' : C ⊆ ccIn G U (ancIn G T C) C := cc_sup G U _ C
        have hT' : IsLatClosed G U (ccIn G U (ancIn G T C) C) := fun v hv u hu e =>
          cc_closed G U _ C hCA u (hA v (hT'A hv) u hu e) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
        have hss : ancIn G T C ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAT, h2⟩
        have hcard : (ccIn G U (ancIn G T C) C).card < n :=
          lt_of_le_of_lt (Finset.card_le_card hT'A)
            (lt_of_lt_of_le (Finset.card_lt_card hss) (Nat.lt_succ_iff.mp hn))
        exact ih _ C hCT' hT' ⟨ancIn G T C, hCA, hT'A, rfl⟩ hcard h

/-- **`identifyTop` sier nei ⇒ IDENTIFY står fast.** -/
theorem identifyTop_false (G : DAG V) (U D : Finset V) (h : identifyTop G U D = false) :
    ∃ T, Stuck G U D T := by
  have hD : D ⊆ ccIn G U Finset.univ D := cc_sup G U _ D
  have hlat : IsLatClosed G U (ccIn G U Finset.univ D) := fun v hv u hu e =>
    cc_closed G U _ D (Finset.subset_univ D) u (Finset.mem_univ u) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
  have hcard : (ccIn G U Finset.univ D).card < Fintype.card V + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_univ _)
  exact identifyN_false G U _ _ D hD hlat
    ⟨Finset.univ, Finset.subset_univ D, Finset.subset_univ _, rfl⟩ hcard h

/-- **Hele ID-sjekken sier nei ⇒ IDENTIFY står fast for én av blokkene.** -/
theorem idCheck_false (G : DAG V) (U X Y : Finset V) (h : idCheck G U X Y = false) :
    ∃ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U ∧ y ∉ X ∧
      ∃ T, Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T := by
  unfold idCheck at h
  have h' := of_decide_eq_false h
  simp only [not_forall] at h'
  obtain ⟨y, hy, hU, hX, hne⟩ := h'
  exact ⟨y, hy, hU, hX, identifyTop_false G U _ (by simpa using hne)⟩

/-- På buen står IDENTIFY fast. -/
theorem bow_stuck : ∃ T, Stuck Bow.bowG {0} {0, 2} T :=
  identifyTop_false _ _ _ bow_check

end Hedge

#print axioms Hedge.identifyN_false
#print axioms Hedge.idCheck_false
#print axioms Hedge.bow_stuck

/-! ## Runde 42: der ID står fast, treffer `T` mengden `X`

Planens punkt H2 (i). Er `D` en c-komponent av `G_{X̄}[S]` (`S` = forfedrene til `Y` i
`G_{X̄}`) og står IDENTIFY fast ved `T`, så møter `T` mengden `X`. Ellers ville hele `T`
ligge i `S` (alle noder er forfedre til `D` innenfor `T`, og ingen kant inn i `X` brukes),
og c-lukningen av `D` innenfor `T` ville holde seg inne i `D`; da er `T = D`, i strid med
`D ⊊ T`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
lemma iter_mono (f : Finset V → Finset V) (hinf : ∀ A, A ⊆ f A) (A0 : Finset V) (k : ℕ) :
    ∀ m, k ≤ m → f^[k] A0 ⊆ f^[m] A0 := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m _ ih =>
    rw [show f^[m + 1] A0 = f (f^[m] A0) from Function.iterate_succ_apply' f m A0]
    exact ih.trans (hinf _)

/-- **Der ID står fast, treffer `T` mengden `X`.** -/
theorem stuck_meets_X (G : DAG V) (U X Y : Finset V) (y : V)
    (hyS : y ∈ ancIn (cutIn G X) Finset.univ Y) {T : Finset V}
    (hst : Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T) :
    ∃ x ∈ X, x ∈ T := by
  by_contra hno
  have hTX : ∀ v ∈ T, v ∉ X := fun v hv hx => hno ⟨v, hx, hv⟩
  set S := ancIn (cutIn G X) Finset.univ Y
  have hyS' : ({y} : Finset V) ⊆ S := Finset.singleton_subset_iff.mpr hyS
  have hSanc : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S := fun v hv p e =>
    anc_closed (cutIn G X) Finset.univ Y (Finset.subset_univ Y) p (Finset.mem_univ p) ⟨v, hv, e⟩
  have hDS : ccIn (cutIn G X) U S {y} ⊆ S := cc_sub (cutIn G X) U S {y} hyS'
  -- Trinn 1: hele `T` ligger i `S`.
  have h1 : ∀ k, (ancStep G T)^[k] (ccIn (cutIn G X) U S {y}) ⊆ S ∩ T := by
    refine iter_sub (S ∩ T) (ancStep G T) ?_ _ ?_
    · intro A hA w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hA h
      · obtain ⟨hwT, a, ha, e⟩ := Finset.mem_filter.mp h
        have haS := (Finset.mem_inter.mp (hA ha)).1
        have haT := (Finset.mem_inter.mp (hA ha)).2
        exact Finset.mem_inter.mpr
          ⟨hSanc a haS w (⟨e, hTX a haT⟩ : G.edge w a ∧ a ∉ X), hwT⟩
    · intro v hv
      exact Finset.mem_inter.mpr ⟨hDS hv, hst.sub hv⟩
  have hTS : T ⊆ S := by
    intro v hv
    have hv' : v ∈ ancIn G T (ccIn (cutIn G X) U S {y}) := by rw [hst.anc]; exact hv
    exact (Finset.mem_inter.mp (h1 T.card hv')).1
  -- Trinn 2: c-lukningen holder seg inne i `D`.
  obtain ⟨T', _, _, hcc⟩ := hst.cc
  have hAT : ∀ j, j ≤ T'.card →
      (ccStep G U T')^[j] (ccIn (cutIn G X) U S {y}) ⊆ T := fun j hj v hv => by
    rw [← hcc]
    exact iter_mono (ccStep G U T') (fun _ => Finset.subset_union_left) _ j T'.card hj hv
  have key : ∀ k, k ≤ T'.card →
      (ccStep G U T')^[k] (ccIn (cutIn G X) U S {y}) ⊆ ccIn (cutIn G X) U S {y} := by
    intro k
    induction k with
    | zero => intro _; exact Finset.Subset.refl _
    | succ k ih =>
      intro hk
      have hAk := ih (Nat.le_of_succ_le hk)
      have hAkT := hAT k (Nat.le_of_succ_le hk)
      intro w hw
      have hwT := hAT (k + 1) hk hw
      rw [show (ccStep G U T')^[k + 1] (ccIn (cutIn G X) U S {y}) =
          ccStep G U T' ((ccStep G U T')^[k] (ccIn (cutIn G X) U S {y})) from
        Function.iterate_succ_apply' _ k _] at hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hAk h
      · obtain ⟨_, b, hb, hrel⟩ := Finset.mem_filter.mp h
        have hbT := hAkT hb
        refine cc_closed (cutIn G X) U S {y} hyS' w (hTS hwT) ⟨b, hAk hb, ?_⟩
        rcases hrel with ⟨hbU, e⟩ | ⟨hwU, e⟩
        · exact Or.inl ⟨hbU, (⟨e, hTX w hwT⟩ : G.edge b w ∧ w ∉ X)⟩
        · exact Or.inr ⟨hwU, (⟨e, hTX b hbT⟩ : G.edge w b ∧ b ∉ X)⟩
  have hTD : T ⊆ ccIn (cutIn G X) U S {y} := fun v hv => by
    rw [← hcc] at hv
    exact key T'.card le_rfl hv
  exact hst.ne (Finset.Subset.antisymm hst.sub hTD)

/-- **ID-sjekken sier nei ⇒ IDENTIFY står fast ved en `T` som møter `X`.** -/
theorem idCheck_false_meets (G : DAG V) (U X Y : Finset V) (h : idCheck G U X Y = false) :
    ∃ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U ∧ y ∉ X ∧
      ∃ T, Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T ∧
        ∃ x ∈ X, x ∈ T := by
  obtain ⟨y, hy, hU, hX, T, hst⟩ := idCheck_false G U X Y h
  exact ⟨y, hy, hU, hX, T, hst, stuck_meets_X G U X Y y hy hst⟩

end Hedge

#print axioms Hedge.stuck_meets_X
#print axioms Hedge.idCheck_false_meets

/-! ## Runde 43: røttene, og hedgen uten c-sammenheng

Planens punkt H2 (ii). Hos Shpitser og Pearl er en C-skog en *delgraf* der hver node
beholder høyst én barnekant, så røttene trenger ikke være barnløse i `G[F']`. Med
`R := rootsIn G D` (nodene i `D` uten barn i `D`) er både `D` og `T` `R`-rotet:

* `ancIn_roots`: hver node i `D` når en rot innenfor `D` (følg barn til det stopper;
  rangen vokser langs kantene, så det tar slutt);
* `stuck_rooted`: hver node i `T` når `D` innenfor `T`, og dermed `R`.

`stuck_hedge_pre` samler det som da gjelder for `(F, F') = (D, T)`: samme røtter,
`D` utenfor `X`, `T` møter `X`, røttene er forfedre til `Y` i `G_{X̄}`. Det som mangler
for en hedge i Shpitser–Pearls forstand, er c-sammenhengen i `D` og `T` (runde 44). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Nodene i `F` uten barn i `F`. -/
def rootsIn (G : DAG V) (F : Finset V) : Finset V := F.filter (fun v => ∀ w ∈ F, ¬ G.edge v w)

/-- `ancIn` er den minste mengden som inneholder `C` og er lukket under foreldre i `T`. -/
lemma ancIn_min (G : DAG V) (T C A : Finset V) (hCA : C ⊆ A)
    (hA : ∀ v ∈ T, (∃ a ∈ A, G.edge v a) → v ∈ A) : ancIn G T C ⊆ A :=
  iter_sub A (ancStep G T) (fun B hB w hw => by
    rcases Finset.mem_union.mp hw with h | h
    · exact hB h
    · obtain ⟨hwT, b, hb, e⟩ := Finset.mem_filter.mp h
      exact hA w hwT ⟨b, hB hb, e⟩) C hCA T.card

/-- **Hver node i `F` når en rot innenfor `F`.** -/
theorem ancIn_roots (G : DAG V) (F : Finset V) : ancIn G F (rootsIn G F) = F := by
  have hRF : rootsIn G F ⊆ F := Finset.filter_subset _ _
  apply Finset.Subset.antisymm (anc_sub G F _ hRF)
  by_contra hno
  have hne : (F \ ancIn G F (rootsIn G F)).Nonempty := Finset.sdiff_nonempty.mpr hno
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image _ G.rank hne
  obtain ⟨hvF, hvA⟩ := Finset.mem_sdiff.mp hv
  have hvR : ¬ ∀ w ∈ F, ¬ G.edge v w := fun h =>
    hvA (anc_sup G F _ (Finset.mem_filter.mpr ⟨hvF, h⟩))
  obtain ⟨w, hwF, e⟩ : ∃ w ∈ F, G.edge v w := by
    by_contra h'
    exact hvR (fun w hw e => h' ⟨w, hw, e⟩)
  by_cases hwA : w ∈ ancIn G F (rootsIn G F)
  · exact hvA (anc_closed G F _ hRF v hvF ⟨w, hwA, e⟩)
  · have hle := hmax w (Finset.mem_sdiff.mpr ⟨hwF, hwA⟩)
    exact absurd hle (not_le.mpr (G.rank_strict_mono v w e))

/-- `ancIn` vokser med `T`. -/
lemma ancIn_mono (G : DAG V) (D T C : Finset V) (hCD : C ⊆ D) (hDT : D ⊆ T) :
    ancIn G D C ⊆ ancIn G T C :=
  ancIn_min G D C (ancIn G T C) (anc_sup G T C)
    (fun v hv h => anc_closed G T C (hCD.trans hDT) v (hDT hv) h)

/-- **Der IDENTIFY står fast, er `T` rotet i røttene til målet.** -/
theorem stuck_rooted (G : DAG V) (U D T : Finset V) (hst : Stuck G U D T) :
    ancIn G T (rootsIn G D) = T := by
  have hRD : rootsIn G D ⊆ D := Finset.filter_subset _ _
  have hRT : rootsIn G D ⊆ T := hRD.trans hst.sub
  apply Finset.Subset.antisymm (anc_sub G T _ hRT)
  have hDA : D ⊆ ancIn G T (rootsIn G D) := by
    calc D = ancIn G D (rootsIn G D) := (ancIn_roots G D).symm
      _ ⊆ ancIn G T (rootsIn G D) := ancIn_mono G D T _ hRD hst.sub
  calc T = ancIn G T D := hst.anc.symm
    _ ⊆ ancIn G T (rootsIn G D) :=
      ancIn_min G T D _ hDA (fun v hv h => anc_closed G T _ hRT v hv h)

/-- **Hedgen uten c-sammenheng.** Der ID-sjekken står fast, har `(D, T)` samme røtter,
`D` ligger utenfor `X`, `T` møter `X`, og røttene er forfedre til `Y` i `G_{X̄}`. -/
theorem stuck_hedge_pre (G : DAG V) (U X Y : Finset V) (hXO : X ⊆ Uᶜ) (y : V)
    (hyS : y ∈ ancIn (cutIn G X) Finset.univ Y) (hyX : y ∉ X) {T : Finset V}
    (hst : Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T) :
    ancIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})
        (rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})) =
      ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y} ∧
    ancIn G T (rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})) = T ∧
    (∀ v ∈ ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}, v ∉ X) ∧
    (∃ x ∈ X, x ∈ T) ∧
    rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) ⊆
      ancIn (cutIn G X) Finset.univ Y := by
  have hyS' : ({y} : Finset V) ⊆ ancIn (cutIn G X) Finset.univ Y :=
    Finset.singleton_subset_iff.mpr hyS
  refine ⟨ancIn_roots G _, stuck_rooted G U _ T hst, ?_, stuck_meets_X G U X Y y hyS hst, ?_⟩
  · intro z hz hzX
    rw [ccIn_eq (cutIn G X) U _ y hyS] at hz
    have hzC := (Finset.mem_inter.mp hz).2
    have hyz : y ∈ ccomp (DAG.induce (cutIn G X) (ancIn (cutIn G X) Finset.univ Y)) U z := by
      rw [ccomp_eq_of_mem hzC]
      exact self_mem_ccomp _ U y
    have := ccomp_ind_X G U X _ hXO hzX hyz
    rw [Finset.mem_singleton.mp this] at hyX
    exact hyX hzX
  · exact (Finset.filter_subset _ _).trans (cc_sub (cutIn G X) U _ {y} hyS')

end Hedge

#print axioms Hedge.ancIn_roots
#print axioms Hedge.stuck_rooted
#print axioms Hedge.stuck_hedge_pre

/-! ## Runde 44: c-sammenheng, og hedgen

* `block_reach`: blokken `D` (c-komponenten av `y` i `G_{X̄}[S]`) er c-sammenhengende
  innenfor seg selv i `G`: hver sti i `G_{X̄}[S]` fra `y` går gjennom `D`.
* `stuck_reach`: `T` er c-lukningen av `D`, så hver node i `T` når `y` med latente steg
  innenfor `T`.
* `IsHedge`: Shpitser–Pearls hedge (Def. 5) på mengdeform: `F ⊊ F'`, begge
  c-sammenhengende, begge rotet i røttene til `F`, `F` utenfor `X`, `F'` møter `X`,
  røttene er forfedre til `Y` i `G_{X̄}`.
* `idCheck_false_hedge`: **sier ID-sjekken nei, finnes en hedge.** Steg H2 er dermed
  ferdig; `bow_hedge` er buen. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `F` er c-sammenhengende innenfor seg selv. -/
def CConn (G : DAG V) (U F : Finset V) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, b ∈ ccomp (DAG.induce G F) U a

lemma cconn_of_reach (G : DAG V) (U F : Finset V) (y : V)
    (h : ∀ b ∈ F, b ∈ ccomp (DAG.induce G F) U y) : CConn G U F :=
  fun a ha b hb => by
    rw [ccomp_eq_of_mem (h a ha)]
    exact h b hb

lemma latStep_induce_mono (G : DAG V) (U D T : Finset V) (hDT : D ⊆ T) (a b : V)
    (h : latStep (DAG.induce G D) U a b) : latStep (DAG.induce G T) U a b := by
  rcases h with ⟨hu, e⟩ | ⟨hu, e⟩
  · obtain ⟨ha, hb, e'⟩ := (show a ∈ D ∧ b ∈ D ∧ G.edge a b from e)
    exact Or.inl ⟨hu, (⟨hDT ha, hDT hb, e'⟩ : a ∈ T ∧ b ∈ T ∧ G.edge a b)⟩
  · obtain ⟨hb, ha, e'⟩ := (show b ∈ D ∧ a ∈ D ∧ G.edge b a from e)
    exact Or.inr ⟨hu, (⟨hDT hb, hDT ha, e'⟩ : b ∈ T ∧ a ∈ T ∧ G.edge b a)⟩

/-- **Blokken er c-sammenhengende i `G`.** -/
theorem block_reach (G : DAG V) (U X S : Finset V) (y : V) (hy : y ∈ S) :
    ∀ b ∈ ccIn (cutIn G X) U S {y},
      b ∈ ccomp (DAG.induce G (ccIn (cutIn G X) U S {y})) U y := by
  have hDeq := ccIn_eq (cutIn G X) U S y hy
  have hmem : ∀ c, c ∈ ccIn (cutIn G X) U S {y} ↔
      c ∈ S ∧ c ∈ ccomp (DAG.induce (cutIn G X) S) U y :=
    fun c => by rw [hDeq, Finset.mem_inter]
  have key : ∀ c, Relation.ReflTransGen (latStep (DAG.induce (cutIn G X) S) U) y c →
      c ∈ ccIn (cutIn G X) U S {y} ∧
      Relation.ReflTransGen (latStep (DAG.induce G (ccIn (cutIn G X) U S {y})) U) y c := by
    intro c hc
    induction hc with
    | refl => exact ⟨(hmem y).mpr ⟨hy, self_mem_ccomp _ U y⟩, Relation.ReflTransGen.refl⟩
    | @tail b' c hab hbc ih =>
      have hcD : c ∈ ccIn (cutIn G X) U S {y} := by
        refine (hmem c).mpr ⟨?_, mem_ccomp.mpr (hab.tail hbc)⟩
        rcases hbc with ⟨_, e⟩ | ⟨_, e⟩
        · exact (show b' ∈ S ∧ c ∈ S ∧ (cutIn G X).edge b' c from e).2.1
        · exact (show c ∈ S ∧ b' ∈ S ∧ (cutIn G X).edge c b' from e).1
      refine ⟨hcD, ih.2.tail ?_⟩
      rcases hbc with ⟨hu, e⟩ | ⟨hu, e⟩
      · have e' : G.edge b' c := (show G.edge b' c ∧ c ∉ X from
          (show b' ∈ S ∧ c ∈ S ∧ (cutIn G X).edge b' c from e).2.2).1
        exact Or.inl ⟨hu, (⟨ih.1, hcD, e'⟩ :
          b' ∈ ccIn (cutIn G X) U S {y} ∧ c ∈ ccIn (cutIn G X) U S {y} ∧ G.edge b' c)⟩
      · have e' : G.edge c b' := (show G.edge c b' ∧ b' ∉ X from
          (show c ∈ S ∧ b' ∈ S ∧ (cutIn G X).edge c b' from e).2.2).1
        exact Or.inr ⟨hu, (⟨hcD, ih.1, e'⟩ :
          c ∈ ccIn (cutIn G X) U S {y} ∧ b' ∈ ccIn (cutIn G X) U S {y} ∧ G.edge c b')⟩
  intro b hb
  exact mem_ccomp.mpr (key b (mem_ccomp.mp ((hmem b).mp hb).2)).2

/-- **Der IDENTIFY står fast, er `T` c-sammenhengende** (når målet er det). -/
theorem stuck_reach (G : DAG V) (U D T : Finset V) (y : V) (hst : Stuck G U D T)
    (hD : ∀ b ∈ D, b ∈ ccomp (DAG.induce G D) U y) :
    ∀ b ∈ T, b ∈ ccomp (DAG.induce G T) U y := by
  obtain ⟨T', _, _, hcc⟩ := hst.cc
  have hAT : ∀ j, j ≤ T'.card → (ccStep G U T')^[j] D ⊆ T := fun j hj v hv => by
    rw [← hcc]
    exact iter_mono (ccStep G U T') (fun _ => Finset.subset_union_left) _ j T'.card hj hv
  have key : ∀ k, k ≤ T'.card → ∀ b ∈ (ccStep G U T')^[k] D,
      b ∈ ccomp (DAG.induce G T) U y := by
    intro k
    induction k with
    | zero =>
      intro _ b hb
      exact mem_ccomp.mpr (Relation.ReflTransGen.mono (latStep_induce_mono G U D T hst.sub)
        (mem_ccomp.mp (hD b hb)))
    | succ k ih =>
      intro hk b hb
      have hbT := hAT (k + 1) hk hb
      rw [show (ccStep G U T')^[k + 1] D = ccStep G U T' ((ccStep G U T')^[k] D) from
        Function.iterate_succ_apply' _ k _] at hb
      rcases Finset.mem_union.mp hb with h | h
      · exact ih (Nat.le_of_succ_le hk) b h
      · obtain ⟨_, a, ha, hrel⟩ := Finset.mem_filter.mp h
        have haT := hAT k (Nat.le_of_succ_le hk) ha
        have hya := mem_ccomp.mp (ih (Nat.le_of_succ_le hk) a ha)
        refine mem_ccomp.mpr (hya.tail ?_)
        rcases hrel with ⟨hu, e⟩ | ⟨hu, e⟩
        · exact Or.inl ⟨hu, (⟨haT, hbT, e⟩ : a ∈ T ∧ b ∈ T ∧ G.edge a b)⟩
        · exact Or.inr ⟨hu, (⟨hbT, haT, e⟩ : b ∈ T ∧ a ∈ T ∧ G.edge b a)⟩
  intro b hb
  rw [← hcc] at hb
  exact key T'.card le_rfl b hb

/-- **Hedge for `P_X(Y)`** (Shpitser–Pearl Def. 5), på mengdeform. -/
structure IsHedge (G : DAG V) (U X Y F F' : Finset V) : Prop where
  sub : F ⊆ F'
  ne : F ≠ F'
  rootF : ancIn G F (rootsIn G F) = F
  rootF' : ancIn G F' (rootsIn G F) = F'
  out : ∀ v ∈ F, v ∉ X
  meet : ∃ x ∈ X, x ∈ F'
  anc : rootsIn G F ⊆ ancIn (cutIn G X) Finset.univ Y
  conn : CConn G U F
  conn' : CConn G U F'

/-- **Sier ID-sjekken nei, finnes en hedge.** -/
theorem idCheck_false_hedge (G : DAG V) (U X Y : Finset V) (hXO : X ⊆ Uᶜ)
    (h : idCheck G U X Y = false) : ∃ F F', IsHedge G U X Y F F' := by
  obtain ⟨y, hy, _, hyX, T, hst⟩ := idCheck_false G U X Y h
  obtain ⟨h1, h2, h3, h4, h5⟩ := stuck_hedge_pre G U X Y hXO y hy hyX hst
  have hDr := block_reach G U X (ancIn (cutIn G X) Finset.univ Y) y hy
  exact ⟨_, T, ⟨hst.sub, hst.ne, h1, h2, h3, h4, h5, cconn_of_reach G U _ y hDr,
    cconn_of_reach G U T y (stuck_reach G U _ T y hst hDr)⟩⟩

/-- Buen har en hedge for `P(y | do(x))`. -/
theorem bow_hedge : ∃ F F', IsHedge Bow.bowG {0} {1} {2} F F' :=
  idCheck_false_hedge _ _ _ _ (by decide) bow_idCheck

end Hedge

#print axioms Hedge.block_reach
#print axioms Hedge.stuck_reach
#print axioms Hedge.idCheck_false_hedge
#print axioms Hedge.bow_hedge

/-! ## Runde 45: H3, første steg — en skog inn i røttene

Konstruksjonen i Shpitser & Pearl (JMLR 2008, bevis for Thm 17) går på en C-skog: hver
node beholder høyst ett barn. Her velges det barnet (`nxt`) for hver node i `F'` som ikke
er en rot: inne i `F` for noder i `F`, ellers inne i `F'` (`hedge_nxt`). Rangen vokser
langs valgene, så hver node når en rot etter endelig mange steg (`hedge_reaches_root`). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Noder i `ancIn G T C` er i `C` eller har et barn i `T`. -/
lemma anc_has_child (G : DAG V) (T C : Finset V) (hCT : C ⊆ T) :
    ∀ v ∈ ancIn G T C, v ∈ C ∨ ∃ w ∈ T, G.edge v w := by
  have hbd : ∀ A, A ⊆ C ∪ T.filter (fun v => ∃ w ∈ T, G.edge v w) →
      ancStep G T A ⊆ C ∪ T.filter (fun v => ∃ w ∈ T, G.edge v w) := by
    intro A hA w hw
    rcases Finset.mem_union.mp hw with h1 | h1
    · exact hA h1
    · obtain ⟨hwT, a, ha, e⟩ := Finset.mem_filter.mp h1
      have haT : a ∈ T := by
        rcases Finset.mem_union.mp (hA ha) with h2 | h2
        · exact hCT h2
        · exact (Finset.mem_filter.mp h2).1
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwT, a, haT, e⟩)
  have h := iter_sub _ (ancStep G T) hbd C Finset.subset_union_left T.card
  intro v hv
  rcases Finset.mem_union.mp (h hv) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Finset.mem_filter.mp h1).2

/-- Det valgte barnet: inne i `F` for noder i `F`, ellers inne i `F'`. -/
noncomputable def nxt (G : DAG V) (F F' : Finset V) (v : V) : V :=
  if h : ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w then Classical.choose h else v

lemma nxt_spec (G : DAG V) (F F' : Finset V) (v : V)
    (h : ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w) :
    (v ∈ F → nxt G F F' v ∈ F) ∧ nxt G F F' v ∈ F' ∧ G.edge v (nxt G F F' v) := by
  unfold nxt
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **I en hedge har hver ikke-rot et valgt barn.** -/
theorem hedge_nxt {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') (v : V)
    (hv : v ∈ F') (hR : v ∉ rootsIn G F) :
    (v ∈ F → nxt G F F' v ∈ F) ∧ nxt G F F' v ∈ F' ∧ G.edge v (nxt G F F' v) := by
  apply nxt_spec
  by_cases hvF : v ∈ F
  · have hnot : ¬ ∀ w ∈ F, ¬ G.edge v w := fun h => hR (Finset.mem_filter.mpr ⟨hvF, h⟩)
    obtain ⟨w, hwF, e⟩ : ∃ w ∈ F, G.edge v w := by
      by_contra h'
      exact hnot (fun w hw e => h' ⟨w, hw, e⟩)
    exact ⟨w, fun _ => hwF, hH.sub hwF, e⟩
  · have hRF' : rootsIn G F ⊆ F' := (Finset.filter_subset _ _).trans hH.sub
    have hva : v ∈ ancIn G F' (rootsIn G F) := by rw [hH.rootF']; exact hv
    rcases anc_has_child G F' _ hRF' v hva with h | ⟨w, hw, e⟩
    · exact absurd h hR
    · exact ⟨w, fun h => absurd h hvF, hw, e⟩

/-- **Følger man de valgte barna, når man en rot.** -/
theorem hedge_reaches_root {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∀ v ∈ F', ∃ n, (nxt G F F')^[n] v ∈ rootsIn G F := by
  have key : ∀ k, ∀ v ∈ F', F'.sup G.rank - G.rank v = k →
      ∃ n, (nxt G F F')^[n] v ∈ rootsIn G F := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hk
      by_cases hR : v ∈ rootsIn G F
      · exact ⟨0, hR⟩
      · obtain ⟨_, hw, e⟩ := hedge_nxt hH v hv hR
        have hlt := G.rank_strict_mono v _ e
        have hle : G.rank (nxt G F F' v) ≤ F'.sup G.rank := Finset.le_sup hw
        obtain ⟨n, hn⟩ := ih (F'.sup G.rank - G.rank (nxt G F F' v)) (by omega) _ hw rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  exact fun v hv => key _ v hv rfl

end Hedge

#print axioms Hedge.hedge_nxt
#print axioms Hedge.hedge_reaches_root

/-! ## Runde 46: hver node har en rot

`nxt` står stille i røttene (`nxt_root`), og holder seg i `F` og `F'`
(`hedge_iter_memF`, `hedge_iter_mem`). Ett felles antall steg `N` fører hver node i `F'`
til en rot (`hedge_root_uniform`), så `r v := nxt^[N] v` er roten `v` mater inn i, og
`r` er konstant langs `nxt` (`hedge_rootOf`). Det er bokføringen paritetsmodellene i H3
trenger. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- I en rot står `nxt` stille. -/
lemma nxt_root (G : DAG V) (F F' : Finset V) (v : V) (hv : v ∈ rootsIn G F) :
    nxt G F F' v = v := by
  have hn : ¬ ∃ w, (v ∈ F → w ∈ F) ∧ w ∈ F' ∧ G.edge v w := by
    rintro ⟨w, hwF, _, e⟩
    have hvF : v ∈ F := (Finset.mem_filter.mp hv).1
    exact (Finset.mem_filter.mp hv).2 w (hwF hvF) e
  unfold nxt
  rw [dif_neg hn]

lemma iter_root (G : DAG V) (F F' : Finset V) (v : V) (hv : v ∈ rootsIn G F) :
    ∀ m, (nxt G F F')^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, nxt_root G F F' v hv]

/-- Følger man `nxt` fra `F'`, blir man i `F'`. -/
theorem hedge_iter_mem {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    {v : V} (hv : v ∈ F') : ∀ n, (nxt G F F')^[n] v ∈ F' := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]; exact ih
    · exact (hedge_nxt hH _ ih hR).2.1

/-- Følger man `nxt` fra `F`, blir man i `F`. -/
theorem hedge_iter_memF {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    {v : V} (hv : v ∈ F) : ∀ n, (nxt G F F')^[n] v ∈ F := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]; exact ih
    · exact (hedge_nxt hH _ (hH.sub ih) hR).1 ih

/-- **Ett antall steg holder for alle.** -/
theorem hedge_root_uniform {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∃ N, ∀ v ∈ F', (nxt G F F')^[N] v ∈ rootsIn G F := by
  choose! n hn using hedge_reaches_root hH
  refine ⟨F'.sup n, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hv)
  rw [hk, add_comm, Function.iterate_add_apply, iter_root G F F' _ (hn v hv) k]
  exact hn v hv

/-- **Rotkartet:** hver node i `F'` har en rot, og roten er den samme langs `nxt`. -/
theorem hedge_rootOf {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F') :
    ∃ r : V → V, (∀ v ∈ F', r v ∈ rootsIn G F) ∧ (∀ v ∈ F', r (nxt G F F' v) = r v) := by
  obtain ⟨N, hN⟩ := hedge_root_uniform hH
  refine ⟨fun v => (nxt G F F')^[N] v, fun v hv => hN v hv, fun v hv => ?_⟩
  show (nxt G F F')^[N] (nxt G F F' v) = (nxt G F F')^[N] v
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', nxt_root G F F' _ (hN v hv)]

end Hedge

#print axioms Hedge.nxt_root
#print axioms Hedge.hedge_iter_mem
#print axioms Hedge.hedge_iter_memF
#print axioms Hedge.hedge_root_uniform
#print axioms Hedge.hedge_rootOf

/-! ## Runde 47: utspent tre, steg 1 — søsken

Når de latente er røtter, går hver latent sti mellom to observerte noder i `F` via
felles latente foreldre. `sib G U F a b`: `a` og `b` er i `F` og har en felles latent
forelder i `F`. `cconn_sib`: i en c-sammenhengende `F` henger alle observerte noder
sammen gjennom en kjede av søsken. Det er grafen det utspente treet velges i. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `a` og `b` er søsken i `F`: begge i `F`, med en felles latent forelder i `F`. -/
def sib (G : DAG V) (U F : Finset V) (a b : V) : Prop :=
  a ∈ F ∧ b ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u a ∧ G.edge u b

lemma sib_symm {G : DAG V} {U F : Finset V} {a b : V} (h : sib G U F a b) : sib G U F b a := by
  obtain ⟨ha, hb, u, hu, huF, ea, eb⟩ := h
  exact (⟨hb, ha, u, hu, huF, eb, ea⟩ : b ∈ F ∧ a ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u b ∧ G.edge u a)

/-- **C-sammenheng gir søskenkjeder** (latente er røtter). -/
theorem cconn_sib (G : DAG V) (U F : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hF : CConn G U F) :
    ∀ a ∈ F, a ∉ U → ∀ b ∈ F, b ∉ U → Relation.ReflTransGen (sib G U F) a b := by
  intro a ha haU
  have key : ∀ x, Relation.ReflTransGen (latStep (DAG.induce G F) U) a x →
      (x ∉ U → Relation.ReflTransGen (sib G U F) a x) ∧
      (x ∈ U → ∃ c, c ∉ U ∧ c ∈ F ∧ x ∈ F ∧ G.edge x c ∧
        Relation.ReflTransGen (sib G U F) a c) := by
    intro x hx
    induction hx with
    | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => absurd h haU⟩
    | @tail b c _ hst ih =>
      rcases hst with ⟨hbU, e⟩ | ⟨hcU, e⟩
      · obtain ⟨hbF, hcF, ebc⟩ := (show b ∈ F ∧ c ∈ F ∧ G.edge b c from e)
        refine ⟨fun _ => ?_, fun hcU => absurd ebc (hroot c hcU b)⟩
        obtain ⟨d, _, hdF, _, ebd, hpath⟩ := ih.2 hbU
        exact hpath.tail (⟨hdF, hcF, b, hbU, hbF, ebd, ebc⟩ :
          d ∈ F ∧ c ∈ F ∧ ∃ u ∈ U, u ∈ F ∧ G.edge u d ∧ G.edge u c)
      · obtain ⟨hcF, hbF, ecb⟩ := (show c ∈ F ∧ b ∈ F ∧ G.edge c b from e)
        have hbU : b ∉ U := fun h => hroot b h c ecb
        exact ⟨fun h => absurd hcU h, fun _ => ⟨b, hbU, hbF, hcF, ecb, ih.1 hbU⟩⟩
  intro b hb hbU
  exact (key b (mem_ccomp.mp (hF a ha b hb))).1 hbU

end Hedge

#print axioms Hedge.sib_symm
#print axioms Hedge.cconn_sib

/-! ## Runde 48: utspent tre, steg 2–3 — lag og foreldrepeker

`lay G U F ρ n v`: `v` nås fra `ρ` med høyst `n` søskensteg. `lay_of_chain`: en søskenkjede
gir et lag. `sib_tree`: for en observert rot `ρ ∈ F` velger hver annen observert node i `F`
et søsken `par v` med strengt mindre avstand `d`. Det er et utspent tre av latente kanter:
å følge `par` minsker `d`, og bare `ρ` mangler forelder. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Lag: `v` nås fra `ρ` med høyst `n` søskensteg i `F`. -/
def lay (G : DAG V) (U F : Finset V) (ρ : V) : ℕ → V → Prop
  | 0, v => v = ρ
  | n + 1, v => lay G U F ρ n v ∨ ∃ w, lay G U F ρ n w ∧ sib G U F w v

lemma lay_of_chain (G : DAG V) (U F : Finset V) (ρ v : V)
    (h : Relation.ReflTransGen (sib G U F) ρ v) : ∃ n, lay G U F ρ n v := by
  induction h with
  | refl => exact ⟨0, by first | rfl | exact (rfl : ρ = ρ) | simp only [lay]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      first
        | exact (Or.inr ⟨b, hn, hbc⟩ : lay G U F ρ n c ∨ ∃ w, lay G U F ρ n w ∧ sib G U F w c)
        | (simp only [lay]; exact Or.inr ⟨b, hn, hbc⟩)⟩

/-- **Utspent tre:** hver observert `v ≠ ρ` i `F` har et søsken `par v` nærmere `ρ`. -/
theorem sib_tree (G : DAG V) (U F : Finset V) (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hF : CConn G U F) (ρ : V) (hρ : ρ ∈ F) (hρU : ρ ∉ U) :
    ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F, v ∉ U → v ≠ ρ →
      sib G U F (par v) v ∧ d (par v) < d v := by
  classical
  have hex : ∀ v ∈ F, v ∉ U → ∃ n, lay G U F ρ n v := fun v hv hvU =>
    lay_of_chain G U F ρ v (cconn_sib G U F hroot hF ρ hρ hρU v hv hvU)
  have step : ∀ v ∈ F, v ∉ U → v ≠ ρ → ∃ w, sib G U F w v ∧
      (if h : ∃ n, lay G U F ρ n w then Nat.find h else 0) <
      (if h : ∃ n, lay G U F ρ n v then Nat.find h else 0) := by
    intro v hv hvU hvρ
    have h := hex v hv hvU
    rw [dif_pos h]
    have hne : Nat.find h ≠ 0 := by
      intro h0
      apply hvρ
      have hs := Nat.find_spec h
      rw [h0] at hs
      first | exact hs | simpa only [lay] using hs
    obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := ⟨Nat.find h - 1, by omega⟩
    have hs := Nat.find_spec h
    rw [hj] at hs
    have hs' : lay G U F ρ j v ∨ ∃ w, lay G U F ρ j w ∧ sib G U F w v := by
      first | exact hs | simpa only [lay] using hs
    rcases hs' with hs' | ⟨w, hw, hsib⟩
    · exact absurd hs' (Nat.find_min h (by omega))
    · refine ⟨w, hsib, ?_⟩
      have hw' : ∃ n, lay G U F ρ n w := ⟨j, hw⟩
      rw [dif_pos hw', hj]
      have := Nat.find_min' hw' hw
      omega
  choose! par hpar using step
  exact ⟨par, fun v => if h : ∃ n, lay G U F ρ n v then Nat.find h else 0, hpar⟩

end Hedge

#print axioms Hedge.lay_of_chain
#print axioms Hedge.sib_tree

/-! ## Runde 49: utspent tre for hele hedgen

`hedge_tree`: med en observert rot `ρ ∈ F` får hver annen observert node i `F'` et søsken
`par v` i `F'` med strengt mindre `d`, og for noder i `F` ligger forelderen og den felles
latente forelderen i `F`. Treet i `F'` inneholder altså et utspent tre for `F`, slik
paritetsmodellene i H3 trenger. Avstanden er `d₁` (treet i `F`) inne i `F`, og
`max d₁ + 1 + d₂` (treet i `F'`) utenfor. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma sib_mono {G : DAG V} {U F F' : Finset V} (hFF' : F ⊆ F') {a b : V}
    (h : sib G U F a b) : sib G U F' a b := by
  obtain ⟨ha, hb, u, hu, huF, ea, eb⟩ := h
  exact (⟨hFF' ha, hFF' hb, u, hu, hFF' huF, ea, eb⟩ :
    a ∈ F' ∧ b ∈ F' ∧ ∃ u ∈ U, u ∈ F' ∧ G.edge u a ∧ G.edge u b)

/-- **Utspent tre for hedgen**, med treet for `F` inni. -/
theorem hedge_tree {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (ρ : V) (hρ : ρ ∈ F) (hρU : ρ ∉ U) :
    ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F', v ∉ U → v ≠ ρ →
      sib G U F' (par v) v ∧ d (par v) < d v ∧ (v ∈ F → sib G U F (par v) v) := by
  classical
  obtain ⟨p1, d1, h1⟩ := sib_tree G U F hroot hH.conn ρ hρ hρU
  obtain ⟨p2, d2, h2⟩ := sib_tree G U F' hroot hH.conn' ρ (hH.sub hρ) hρU
  refine ⟨fun v => if v ∈ F then p1 v else p2 v,
    fun v => if v ∈ F then d1 v else F.sup d1 + 1 + d2 v, fun v hv hvU hvρ => ?_⟩
  by_cases hvF : v ∈ F
  · obtain ⟨hs, hd⟩ := h1 v hvF hvU hvρ
    have hpF : p1 v ∈ F := by
      obtain ⟨h, _⟩ := hs
      exact h
    simp only [if_pos hvF, if_pos hpF]
    exact ⟨sib_mono hH.sub hs, hd, fun _ => hs⟩
  · obtain ⟨hs, hd⟩ := h2 v hv hvU hvρ
    simp only [if_neg hvF]
    refine ⟨hs, ?_, fun h => absurd h hvF⟩
    by_cases hpF : p2 v ∈ F
    · rw [if_pos hpF]
      have := Finset.le_sup (f := d1) hpF
      omega
    · rw [if_neg hpF]
      omega

end Hedge

#print axioms Hedge.sib_mono
#print axioms Hedge.hedge_tree

/-! ## Runde 50: treet uten ekstra antakelser

`hedge_obs`: når de latente er røtter, har `F` en observert node. Var hele `F` latent,
ville røttene ikke ha foreldre, så `F' = ancIn G F' (rootsIn G F) ⊆ F`, mot `F ≠ F'`.
`sib_obs`: søsken er observerte. `hedge_spanning`: hver hedge har en observert rot `ρ ∈ F`
og et utspent tre av latente kanter, uten andre antakelser enn at de latente er røtter. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Søsken er observerte (latente er røtter). -/
lemma sib_obs {G : DAG V} {U F : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {a b : V}
    (h : sib G U F a b) : a ∉ U ∧ b ∉ U := by
  obtain ⟨_, _, u, _, _, ea, eb⟩ := h
  exact ⟨fun h => hroot a h u ea, fun h => hroot b h u eb⟩

/-- **En hedge har en observert node i `F`** (latente er røtter). -/
theorem hedge_obs {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) : ∃ ρ ∈ F, ρ ∉ U := by
  by_contra hno
  have hall : ∀ v ∈ F, v ∈ U := fun v hv => by
    by_contra h
    exact hno ⟨v, hv, h⟩
  have hsub : ancIn G F' (rootsIn G F) ⊆ rootsIn G F :=
    ancIn_min G F' (rootsIn G F) (rootsIn G F) (Finset.Subset.refl _)
      (fun v _ hex => by
        obtain ⟨a, ha, e⟩ := hex
        exact absurd e (hroot a (hall a (Finset.mem_filter.mp ha).1) v))
  rw [hH.rootF'] at hsub
  exact hH.ne (Finset.Subset.antisymm hH.sub (hsub.trans (Finset.filter_subset _ _)))

/-- **Hver hedge har et utspent tre** med en observert rot i `F`. -/
theorem hedge_spanning {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) :
    ∃ ρ ∈ F, ρ ∉ U ∧ ∃ par : V → V, ∃ d : V → ℕ, ∀ v ∈ F', v ∉ U → v ≠ ρ →
      sib G U F' (par v) v ∧ d (par v) < d v ∧ (v ∈ F → sib G U F (par v) v) := by
  obtain ⟨ρ, hρ, hρU⟩ := hedge_obs hH hroot
  exact ⟨ρ, hρ, hρU, hedge_tree hH hroot ρ hρ hρU⟩

end Hedge

#print axioms Hedge.sib_obs
#print axioms Hedge.hedge_obs
#print axioms Hedge.hedge_spanning

/-! ## Runde 51: «flere kanter skader aldri» for alle verdityper

`Channel.not_ident_of_sub` er bevist for `Bool` på alle noder. Planen for H3 gir de latente
bit-vektorer (én bit per kant i det utspente treet), så her er samme resultat for vilkårlige
verdityper `α`: `not_ident_of_subα`. Beviset er det samme; det bruker ikke at verdiene er
`Bool`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma kfac_liftα {G H : DAG V} {α : V → Type*} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (Completeness.liftSub hsub N) Finset.univ w v = kfac N Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  rfl

lemma kfac_lift_doα {G H : DAG V} {α : V → Type*} (hsub : ∀ v, H.parents v ⊆ G.parents v)
    (N : H.CausalModel α) (X : Finset V) (x : Assignment (α := α) X)
    (w : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (Completeness.liftSub hsub N) X x) Finset.univ w v =
      kfac (doModel N X x) Finset.univ w v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hx : v ∈ X
  · simp only [doModel, dif_pos hx]
  · simp only [doModel, dif_neg hx, Completeness.liftSub] <;> rfl

/-- **Flere kanter skader aldri**, for vilkårlige verdityper. -/
theorem not_ident_of_subα {H G : DAG V} {α : V → Type*} (hsub : ∀ a b, H.edge a b → G.edge a b)
    {O X Y : Finset V} (h : ¬ Identifiable H α O X Y) : ¬ Identifiable G α O X Y := by
  intro hG
  apply h
  intro M1 M2 hM hpos t
  have hp : ∀ v, H.parents v ⊆ G.parents v := fun v a ha => by
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hsub _ _ ha
  have hm : ∀ (M : H.CausalModel α) (S : Finset V),
      (Completeness.liftSub hp M).marginal S = M.marginal S := fun M S =>
    Completeness.marginal_eq_of_kfac _ M (kfac_liftα hp M) S
  have hd : ∀ (M : H.CausalModel α) (x0 : Assignment (α := α) X)
      (S : Finset V), (doModel (Completeness.liftSub hp M) X x0).marginal S =
        (doModel M X x0).marginal S := fun M x0 S =>
    Completeness.marginal_eq_of_kfac _ _ (kfac_lift_doα hp M X x0) S
  have e := hG (Completeness.liftSub hp M1) (Completeness.liftSub hp M2)
    (by rw [hm, hm]; exact hM) (by intro a; rw [hm]; exact hpos a) t
  rw [hd, hd] at e
  exact e

end Hedge

#print axioms Hedge.not_ident_of_subα

/-! ## Runde 52: den reduserte grafen

`keepDAG G K`: delgrafen av `G` med bare kantene som oppfyller `K`. Den er en DAG med samme
rang, og `not_ident_keep`: ikke-identifiserbar i delgrafen gir ikke-identifiserbar i `G`
(for alle verdityper). `hedgeKeep`: kantene H3 beholder, nemlig `v → nxt v` (skogen inn i
røttene) og `u → v`, `u → par v` for latente `u` i `F'` (treet). `hedge_red_nxt` og
`hedge_red_lat`: disse kantene ligger i den reduserte grafen. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Delgrafen med bare kantene som oppfyller `K`. -/
noncomputable def keepDAG (G : DAG V) (K : V → V → Prop) : DAG V where
  edge a b := G.edge a b ∧ K a b
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := fun a b h => G.rank_strict_mono a b h.1

lemma keepDAG_edge {G : DAG V} {K : V → V → Prop} {a b : V} :
    (keepDAG G K).edge a b ↔ G.edge a b ∧ K a b := Iff.rfl

/-- **Ikke identifiserbar i delgrafen ⇒ ikke identifiserbar i `G`.** -/
theorem not_ident_keep {G : DAG V} {K : V → V → Prop} {α : V → Type*} {O X Y : Finset V}
    (h : ¬ Identifiable (keepDAG G K) α O X Y) : ¬ Identifiable G α O X Y :=
  not_ident_of_subα (fun a b (hab : (keepDAG G K).edge a b) => (keepDAG_edge.mp hab).1) h

/-- Kantene H3 beholder: skogen `v → nxt v`, og treets latente kanter `u → v`, `u → par v`. -/
def hedgeKeep (G : DAG V) (U F F' : Finset V) (par : V → V) (a b : V) : Prop :=
  (a ∈ F' ∧ b = nxt G F F' a) ∨
  (a ∈ U ∧ a ∈ F' ∧ ∃ v ∈ F', (b = v ∨ b = par v) ∧ G.edge a v ∧ G.edge a (par v))

/-- Skogkantene ligger i den reduserte grafen. -/
theorem hedge_red_nxt {G : DAG V} {U X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (par : V → V) {v : V} (hv : v ∈ F') (hR : v ∉ rootsIn G F) :
    (keepDAG G (hedgeKeep G U F F' par)).edge v (nxt G F F' v) :=
  keepDAG_edge.mpr ⟨(hedge_nxt hH v hv hR).2.2, by unfold hedgeKeep; exact Or.inl ⟨hv, rfl⟩⟩

/-- Treets latente kanter ligger i den reduserte grafen. -/
theorem hedge_red_lat (G : DAG V) (U F F' : Finset V) (par : V → V) {u v : V}
    (hu : u ∈ U) (huF : u ∈ F') (hv : v ∈ F') (e1 : G.edge u v) (e2 : G.edge u (par v)) :
    (keepDAG G (hedgeKeep G U F F' par)).edge u v ∧
      (keepDAG G (hedgeKeep G U F F' par)).edge u (par v) :=
  ⟨keepDAG_edge.mpr ⟨e1, by unfold hedgeKeep; exact Or.inr ⟨hu, huF, v, hv, Or.inl rfl, e1, e2⟩⟩,
   keepDAG_edge.mpr ⟨e2, by unfold hedgeKeep; exact Or.inr ⟨hu, huF, v, hv, Or.inr rfl, e1, e2⟩⟩⟩

end Hedge

#print axioms Hedge.not_ident_keep
#print axioms Hedge.hedge_red_nxt
#print axioms Hedge.hedge_red_lat

/-! ## Runde 53: trær med foreldrepeker, og etterkommere

Første del av trelemmaet over `ZMod 2` som paritetsmodellene trenger. `ParTree S ρ par d`:
`par` er en foreldrepeker på `S` med rot `ρ` (`par ρ = ρ`) og strengt minkende avstand `d`.
`desc par v w`: `w` ligger i deltreet under `v` (`par^[n] w = v`). Nøkkelen er
`desc_par_iff`: forelderen til `u` ligger under `v` hvis og bare hvis `u` gjør det og
`u ≠ v`. Det gir senere at hver kantbit er summen av innfallsverdiene i deltreet. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Et tre gitt ved foreldrepeker `par` på `S`, med rot `ρ` og minkende avstand `d`. -/
structure ParTree (S : Finset V) (ρ : V) (par : V → V) (d : V → ℕ) : Prop where
  root : ρ ∈ S
  fix : par ρ = ρ
  step : ∀ v ∈ S, v ≠ ρ → par v ∈ S ∧ d (par v) < d v

/-- `w` ligger i deltreet under `v`. -/
def desc (par : V → V) (v w : V) : Prop := ∃ n, par^[n] w = v

lemma desc_refl (par : V → V) (v : V) : desc par v v := ⟨0, rfl⟩

namespace ParTree

variable {S : Finset V} {ρ : V} {par : V → V} {d : V → ℕ}

lemma iter_mem (T : ParTree S ρ par d) {w : V} (hw : w ∈ S) : ∀ n, par^[n] w ∈ S := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : par^[n] w = ρ
    · rw [h, T.fix]; exact T.root
    · exact (T.step _ ih h).1

lemma iter_d_le (T : ParTree S ρ par d) {w : V} (hw : w ∈ S) : ∀ n, d (par^[n] w) ≤ d w := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : par^[n] w = ρ
    · rw [h, T.fix]
      rw [h] at ih
      exact ih
    · exact le_trans (le_of_lt (T.step _ (T.iter_mem hw n) h).2) ih

/-- **Forelderen ligger under `v` ⟺ `u` ligger under `v` og `u ≠ v`.** -/
theorem desc_par_iff (T : ParTree S ρ par d) {u v : V} (hu : u ∈ S) (hur : u ≠ ρ) :
    desc par v (par u) ↔ desc par v u ∧ u ≠ v := by
  constructor
  · rintro ⟨n, h⟩
    refine ⟨⟨n + 1, by rw [Function.iterate_succ_apply]; exact h⟩, ?_⟩
    intro huv
    subst huv
    have h1 := T.iter_d_le (T.step u hu hur).1 n
    rw [h] at h1
    exact absurd (lt_of_le_of_lt h1 (T.step u hu hur).2) (lt_irrefl _)
  · rintro ⟨⟨n, h⟩, hne⟩
    cases n with
    | zero => exact absurd h hne
    | succ m => exact ⟨m, by rw [Function.iterate_succ_apply] at h; exact h⟩

end ParTree

end Hedge

#print axioms Hedge.ParTree.iter_d_le
#print axioms Hedge.ParTree.desc_par_iff

/-! ## Runde 54: innfall i et tre er injektivt

`inc S ρ par c w`: innfallsverdien i `w`, altså biten på kanten over `w` (ingen for roten)
pluss bitene på kantene ned til barna. `ParTree.inc_inj`: er innfallsverdiene like i alle
noder utenom roten, er bitene like. Bevis ved induksjon fra bladene: barna har større `d`,
så bitene deres er like, og da er biten over `u` bestemt av innfallsverdien i `u`. Dette er
kjernen i at begge paritetsmodellene er injektive (planens punkt (i) og (ii)). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Innfallsverdien i `w`: kanten over `w` (ikke for roten) og kantene ned til barna. -/
def inc (S : Finset V) (ρ : V) (par : V → V) (c : V → ZMod 2) (w : V) : ZMod 2 :=
  (if w = ρ then 0 else c w) + ∑ u ∈ S.filter (fun u => u ≠ ρ ∧ par u = w), c u

namespace ParTree

variable {S : Finset V} {ρ : V} {par : V → V} {d : V → ℕ}

/-- **Innfall er injektivt**, med bare radene utenom roten. -/
theorem inc_inj (T : ParTree S ρ par d) {b b' : V → ZMod 2}
    (h : ∀ w ∈ S, w ≠ ρ → inc S ρ par b w = inc S ρ par b' w) :
    ∀ u ∈ S, u ≠ ρ → b u = b' u := by
  have key : ∀ k, ∀ u ∈ S, u ≠ ρ → S.sup d + 1 - d u = k → b u = b' u := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih u hu hur hk
    have hch : ∑ w ∈ S.filter (fun w => w ≠ ρ ∧ par w = u), b w =
        ∑ w ∈ S.filter (fun w => w ≠ ρ ∧ par w = u), b' w := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hwS, hwr, hpw⟩ := Finset.mem_filter.mp hw
      have hdlt : d u < d w := by
        rw [← hpw]
        exact (T.step w hwS hwr).2
      have hdw : d w ≤ S.sup d := Finset.le_sup (f := d) hwS
      exact ih (S.sup d + 1 - d w) (by omega) w hwS hwr rfl
    have e := h u hu hur
    unfold inc at e
    rw [if_neg hur, if_neg hur, hch] at e
    exact add_right_cancel e
  intro u hu hur
  exact key _ u hu hur rfl

end ParTree

end Hedge

#print axioms Hedge.ParTree.inc_inj

/-! ## Runde 55: innfall i et tre treffer alt med sum null

`inc_surj`: for et tre `S` og en vektor `τ` med `Σ_S τ = 0` finnes bitene `b` med
innfallsverdi `τ` i hver node. Bevis ved induksjon på `|S|`: et blad `ℓ` (største `d`)
har ingen barn; løs for `S \ {ℓ}` med `τ ℓ` flyttet over til forelderen, og sett biten
over `ℓ` til `τ ℓ`. Dette er det paritetsmodellene trenger for at `M1` og `M2` gir samme
observerte fordeling (en forskyvning av bitene i `F`-treet), og for positivitet. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by
  first
    | decide
    | (intro x; fin_cases x <;> rfl)

/-- **Innfall treffer alle vektorer med sum null.** -/
theorem inc_surj {ρ : V} {par : V → V} {d : V → ℕ} :
    ∀ (n : ℕ) (S : Finset V) (τ : V → ZMod 2), S.card = n → ParTree S ρ par d →
      ∑ w ∈ S, τ w = 0 → ∃ b : V → ZMod 2, ∀ w ∈ S, inc S ρ par b w = τ w := by
  intro n
  induction n with
  | zero =>
    intro S τ hc T _
    have := Finset.card_pos.mpr ⟨ρ, T.root⟩
    omega
  | succ n ih =>
    intro S τ hc T hsum
    by_cases hS : ∃ v ∈ S, v ≠ ρ
    · obtain ⟨ℓ, hℓf, hmax⟩ := Finset.exists_max_image (S.filter (fun v => v ≠ ρ)) d
        (by
          obtain ⟨v, hv, hvr⟩ := hS
          exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvr⟩⟩)
      obtain ⟨hℓS, hℓρ⟩ := Finset.mem_filter.mp hℓf
      have noch : ∀ u ∈ S, u ≠ ρ → par u ≠ ℓ := by
        intro u hu hur hpu
        have h1 := (T.step u hu hur).2
        rw [hpu] at h1
        have h2' := hmax u (Finset.mem_filter.mpr ⟨hu, hur⟩)
        omega
      have hpℓ : par ℓ ∈ S.erase ℓ := by
        refine Finset.mem_erase.mpr ⟨fun e => ?_, (T.step ℓ hℓS hℓρ).1⟩
        have h1 := (T.step ℓ hℓS hℓρ).2
        rw [e] at h1
        exact lt_irrefl _ h1
      have T' : ParTree (S.erase ℓ) ρ par d :=
        { root := Finset.mem_erase.mpr ⟨fun e => hℓρ e.symm, T.root⟩
          fix := T.fix
          step := fun v hv hvr => by
            have hvS := Finset.mem_of_mem_erase hv
            exact ⟨Finset.mem_erase.mpr ⟨noch v hvS hvr, (T.step v hvS hvr).1⟩,
              (T.step v hvS hvr).2⟩ }
      have hc' : (S.erase ℓ).card = n := by
        rw [Finset.card_erase_of_mem hℓS]
        omega
      have hsum' : ∑ w ∈ S.erase ℓ, (τ w + if w = par ℓ then τ ℓ else 0) = 0 := by
        rw [Finset.sum_add_distrib]
        have hite : ∑ w ∈ S.erase ℓ, (if w = par ℓ then τ ℓ else 0) = τ ℓ := by
          first
            | rw [Finset.sum_ite_eq' (S.erase ℓ) (par ℓ) (fun _ => τ ℓ), if_pos hpℓ]
            | simp [hpℓ]
        rw [hite, Finset.sum_erase_add S τ hℓS]
        exact hsum
      obtain ⟨b', hb'⟩ := ih (S.erase ℓ) (fun w => τ w + if w = par ℓ then τ ℓ else 0) hc' T' hsum'
      refine ⟨fun w => if w = ℓ then τ ℓ else b' w, fun w hw => ?_⟩
      have split : ∑ u ∈ S.filter (fun u => u ≠ ρ ∧ par u = w),
          (fun w => if w = ℓ then τ ℓ else b' w) u =
          ∑ u ∈ (S.erase ℓ).filter (fun u => u ≠ ρ ∧ par u = w), b' u +
            (if ℓ ≠ ρ ∧ par ℓ = w then τ ℓ else 0) := by
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_erase_add S _ hℓS]
        congr 1
        · apply Finset.sum_congr rfl
          intro u hu
          simp only [if_neg (Finset.ne_of_mem_erase hu)]
        · simp
      unfold inc
      rw [split]
      by_cases hwℓ : w = ℓ
      · subst hwℓ
        have hempty : ∑ u ∈ (S.erase w).filter (fun u => u ≠ ρ ∧ par u = w), b' u = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          obtain ⟨hu1, hu2, hu3⟩ := Finset.mem_filter.mp hu
          exact absurd hu3 (noch u (Finset.mem_of_mem_erase hu1) hu2)
        have hpw : ¬ (w ≠ ρ ∧ par w = w) := fun h => noch w hℓS hℓρ h.2
        rw [hempty, if_neg hpw, if_neg hℓρ]
        simp
      · have hwe : w ∈ S.erase ℓ := Finset.mem_erase.mpr ⟨hwℓ, hw⟩
        have e : (if w = ρ then 0 else b' w) +
            ∑ u ∈ (S.erase ℓ).filter (fun u => u ≠ ρ ∧ par u = w), b' u =
            τ w + (if w = par ℓ then τ ℓ else 0) := hb' w hwe
        have hbw : (if w = ρ then 0 else (fun w => if w = ℓ then τ ℓ else b' w) w) =
            (if w = ρ then 0 else b' w) := by
          simp only [if_neg hwℓ]
        rw [hbw, ← add_assoc, e]
        by_cases hpw : par ℓ = w
        · rw [if_pos hpw.symm, if_pos ⟨hℓρ, hpw⟩, add_assoc, zmod2_add_self, add_zero]
        · rw [if_neg (fun e => hpw e.symm), if_neg (fun h => hpw h.2), add_zero, add_zero]
    · refine ⟨fun _ => 0, fun w hw => ?_⟩
      have hSρ : S = {ρ} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨T.root, fun v hv => by
          by_contra h
          exact hS ⟨v, hv, h⟩⟩
      have hwρ : w = ρ := by
        rw [hSρ] at hw
        exact Finset.mem_singleton.mp hw
      rw [hSρ, Finset.sum_singleton] at hsum
      unfold inc
      simp only [ite_self, Finset.sum_const_zero, add_zero]
      rw [hwρ]
      exact hsum.symm

end Hedge

#print axioms Hedge.inc_surj

/-! ## Runde 56: generelle verktøy for paritetsmodellene

`marginal_eq_of_invol`: finnes en involusjon `φ` på hele tilordninger som bevarer verdiene
på `O` og flytter `M1`s sannsynlighet til `M2` (`M2.fullJoint (φ s) = M1.fullJoint s`), har
modellene samme marginal på `O`. Det er argumentet hedge-familiene i `Identification`
bruker hver for seg (`full_map`, `obsEq`), her én gang for alle grafer og verdityper.
`exists_ne_of_sum_ne`: er to summer ulike, er leddene ulike et sted; det gir til slutt en
`t` der `P(R = t | do x)` skiller modellene. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Samme marginal via en involusjon** som bevarer `O`. -/
theorem marginal_eq_of_invol {G1 G2 : DAG V} {α : V → Type*}
    (M1 : G1.CausalModel α) (M2 : G2.CausalModel α) (O : Finset V)
    (φ : Assignment (α := α) (Finset.univ : Finset V) → Assignment (α := α) (Finset.univ : Finset V))
    (hinv : ∀ s, φ (φ s) = s)
    (hO : ∀ s, (φ s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O))
    (hj : ∀ s, M2.fullJoint (φ s) = M1.fullJoint s) :
    M1.marginal O = M2.marginal O := by
  have hmap : M2.fullJoint = M1.fullJoint.map φ := by
    ext s
    rw [PMF.map_apply, tsum_eq_single (φ s)]
    · rw [if_pos (hinv s).symm, ← hj (φ s), hinv]
    · intro s' hs'
      rw [if_neg]
      intro hs
      apply hs'
      rw [hs, hinv]
  unfold CausalModel.marginal
  rw [hmap, PMF.map_comp]
  congr 1
  funext s
  exact (hO s).symm

/-- Ulike summer ⇒ ulike ledd et sted. -/
lemma exists_ne_of_sum_ne {ι β : Type*} [AddCommMonoid β] (s : Finset ι) (f g : ι → β)
    (h : ∑ i ∈ s, f i ≠ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≠ g i := by
  by_contra hno
  apply h
  apply Finset.sum_congr rfl
  intro i hi
  by_contra hne
  exact hno ⟨i, hi, hne⟩

end Hedge

#print axioms Hedge.marginal_eq_of_invol
#print axioms Hedge.exists_ne_of_sum_ne

/-! ## Runde 57: verdityper for paritetsmodellene

Alle noder får verditypen `Fin (kk U v) → ZMod 2`: `kk U v = |V|` for latente (én bit per
kant i treet, indeksert med kantens nedre node via `ix`) og `1` for observerte (én bit).
`rd x i` leser bit nummer `i` (og gir `0` utenfor rekkevidde), så kjernene kan lese
foreldre uten bevisforpliktelser. `obs_ext`: to observerte verdier er like nøyaktig når
biten er lik. `noise`: biten `1` med sannsynlighet `1/4`, til positivitet. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Antall biter: `|V|` for latente, `1` for observerte. -/
def kk (U : Finset V) (v : V) : ℕ := if v ∈ U then Fintype.card V else 1

/-- Verditypen. -/
abbrev Val (U : Finset V) (v : V) : Type := Fin (kk U v) → ZMod 2

/-- Bit nummer `i` (0 utenfor rekkevidde). -/
def rd {U : Finset V} {v : V} (x : Val U v) (i : ℕ) : ZMod 2 :=
  if h : i < kk U v then x ⟨i, h⟩ else 0

/-- Indeksen til kanten under `c` i en latent. -/
noncomputable def ix (c : V) : ℕ := (Fintype.equivFin V c).val

lemma kk_obs {U : Finset V} {v : V} (hv : v ∉ U) : kk U v = 1 := if_neg hv

lemma kk_lat {U : Finset V} {u : V} (hu : u ∈ U) : kk U u = Fintype.card V := if_pos hu

lemma ix_lt (c : V) : ix c < Fintype.card V := (Fintype.equivFin V c).isLt

lemma ix_inj {c c' : V} (h : ix c = ix c') : c = c' :=
  (Fintype.equivFin V).injective (Fin.ext h)

/-- En observert verdi med bit `b`. -/
def cst (U : Finset V) (v : V) (b : ZMod 2) : Val U v := fun _ => b

lemma rd_cst {U : Finset V} {v : V} (hv : v ∉ U) (b : ZMod 2) : rd (cst U v b) 0 = b := by
  have h0 : 0 < kk U v := by
    rw [kk_obs hv]
    omega
  simp only [rd, cst, dif_pos h0]

/-- **To observerte verdier er like nøyaktig når biten er lik.** -/
lemma obs_ext {U : Finset V} {v : V} (hv : v ∉ U) (x y : Val U v) :
    x = y ↔ rd x 0 = rd y 0 := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h0 : 0 < kk U v := by
      rw [kk_obs hv]
      omega
    unfold rd at h
    rw [dif_pos h0, dif_pos h0] at h
    funext i
    have hi : i.val = 0 := by
      have := i.isLt
      have h1 : kk U v = 1 := kk_obs hv
      omega
    have : i = ⟨0, h0⟩ := Fin.ext hi
    rw [this]
    exact h

lemma eq_cst {U : Finset V} {v : V} (hv : v ∉ U) (x : Val U v) : x = cst U v (rd x 0) :=
  (obs_ext hv x _).mpr (rd_cst hv _).symm

/-- Støy: `1` med sannsynlighet `1/4`. -/
noncomputable def noise : PMF (ZMod 2) :=
  PMF.map (fun i : Fin 4 => if i = 0 then (1 : ZMod 2) else 0) (PMF.uniformOfFintype (Fin 4))

end PM
end Hedge

#print axioms Hedge.PM.obs_ext
#print axioms Hedge.PM.eq_cst

/-! ## Runde 58: paritetsmodellene `M1` og `M2`

`Data`: roten `ρ` i `F`, foreldrepekeren `par`, den latente `lat c` bak trekanten
`(c, par c)`, og roten `r0` med støy. `CH v`: trebarna til `v` (observerte `c ≠ ρ` med
`par c = v`). `NX v`: `nxt`-barna til `v` (observerte ikke-røtter med `nxt w = v`).
`sb`: biten i `v` er egen trebit + trebarnas biter + `nxt`-barnas verdier; i `M2`
(`two = true`) teller en node i `F` bare barn i `F` (`scope`). Kjernen: uniform for latente
og for observerte utenfor `F'`; i `F'` er verdien `sb` (pluss `noise` i `r0`). Foreldre
leses med `rd`, beskyttet av `if h : w ∈ G.parents v`, så definisjonen har ingen
bevisforpliktelser. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Konstruksjonsdataene. -/
structure Data (W : Type*) where
  ρ : W
  par : W → W
  lat : W → W
  r0 : W

section models

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Hvilke barn en node teller: i `M2` teller noder i `F` bare barn i `F`. -/
def scope (v : V) : Finset V := if two = true ∧ v ∈ F then F else Finset.univ

/-- Trebarna til `v`. -/
def CH (v : V) : Finset V := F'.filter (fun c => c ∉ U ∧ c ≠ D.ρ ∧ D.par c = v)

/-- `nxt`-barna til `v`. -/
noncomputable def NX (v : V) : Finset V :=
  F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v)

/-- Biten i `v`, gitt en leser `g w i` for bit `i` hos forelder `w`. -/
noncomputable def sb (v : V) (g : V → ℕ → ZMod 2) : ZMod 2 :=
  (if v = D.ρ then 0 else g (D.lat v) (ix v)) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), g (D.lat c) (ix c) +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), g w 0

/-- Leseren for kjernen. -/
def rdp (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) (w : V) (i : ℕ) : ZMod 2 :=
  if h : w ∈ G.parents v then rd (pa ⟨w, h⟩) i else 0

/-- Kjernen. -/
noncomputable def kern (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) : PMF (Val U v) :=
  if v ∈ U then PMF.uniformOfFintype (Val U v)
  else if v ∈ F' then
    (if v = D.r0 then PMF.map (fun n => cst U v (sb G U F F' D two v (rdp G U v pa) + n)) noise
     else PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))))
  else PMF.uniformOfFintype (Val U v)

/-- **Modellen**: `M1` med `two = false`, `M2` med `two = true`. -/
noncomputable def M : G.CausalModel (Val U) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := kern G U F F' D two

lemma kern_lat {v : V} (hv : v ∈ U) (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_pos hv]

lemma kern_out {v : V} (hv : v ∉ U) (hF : v ∉ F') (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.uniformOfFintype (Val U v) := by
  unfold kern
  rw [if_neg hv, if_neg hF]

lemma kern_obs {v : V} (hv : v ∉ U) (hF : v ∈ F') (hr : v ≠ D.r0)
    (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa = PMF.pure (cst U v (sb G U F F' D two v (rdp G U v pa))) := by
  unfold kern
  rw [if_neg hv, if_pos hF, if_neg hr]

lemma kern_r0 {v : V} (hv : v ∉ U) (hF : v ∈ F') (hr : v = D.r0)
    (pa : ∀ u : {u // u ∈ G.parents v}, Val U u.1) :
    kern G U F F' D two v pa =
      PMF.map (fun n => cst U v (sb G U F F' D two v (rdp G U v pa) + n)) noise := by
  unfold kern
  rw [if_neg hv, if_pos hF, if_pos hr]

end models

end PM
end Hedge

#print axioms Hedge.PM.kern_obs
#print axioms Hedge.PM.kern_r0

/-! ## Runde 59: kjernefaktorene for en hel tilordning

For en hel tilordning `s`: `rdS s v w i` leser bit `i` hos `w` hvis `w` er forelder til
`v` (ellers `0`); `rdp_restrict`: kjernens leser er `rdS`. Faktorene (`kfac`) er
`1/|Val U v|` for latente og for observerte utenfor `F'` (`kfac_lat`, `kfac_out`), en
indikator på at biten er `sb` for observerte i `F'` (`kfac_obs`), og `noise` av
`bit + sb` i støyroten (`kfac_r0`; i `ZMod 2` er minus det samme som pluss). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_solve : ∀ r X n : ZMod 2, (r = X + n ↔ n = r + X) := by decide

section kfacs

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Leseren fra en hel tilordning. -/
def rdS (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v w : V) (i : ℕ) : ZMod 2 :=
  if w ∈ G.parents v then rd (s ⟨w, Finset.mem_univ w⟩) i else 0

lemma rdp_restrict (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    rdp G U v (s.restrict (Finset.subset_univ (G.parents v))) = rdS G U s v := by
  funext w i
  unfold rdp rdS
  split_ifs <;> rfl

lemma kfac_lat (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ U) :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [DoAudit.kfac_univ]
  first
    | show kern G U F F' D two v _ _ = _
    | simp only [M]
  rw [kern_lat G U F F' D two hv, PMF.uniformOfFintype_apply]

lemma kfac_out (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∉ F') :
    kfac (M G U F F' D two) Finset.univ s v = ((Fintype.card (Val U v) : ENNReal))⁻¹ := by
  rw [DoAudit.kfac_univ]
  first
    | show kern G U F F' D two v _ _ = _
    | simp only [M]
  rw [kern_out G U F F' D two hv hF, PMF.uniformOfFintype_apply]

/-- **Observerte i `F'`**: faktoren er 1 når biten er `sb`, ellers 0. -/
lemma kfac_obs (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∈ F') (hr : v ≠ D.r0) :
    kfac (M G U F F' D two) Finset.univ s v =
      if rd (s ⟨v, Finset.mem_univ v⟩) 0 = sb G U F F' D two v (rdS G U s v) then 1 else 0 := by
  rw [DoAudit.kfac_univ]
  first
    | show kern G U F F' D two v _ _ = _
    | simp only [M]
  rw [kern_obs G U F F' D two hv hF hr, rdp_restrict, PMF.pure_apply]
  simp only [obs_ext hv, rd_cst hv]

/-- **Støyroten**: faktoren er `noise (bit + sb)`. -/
lemma kfac_r0 (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U)
    (hF : v ∈ F') (hr : v = D.r0) :
    kfac (M G U F F' D two) Finset.univ s v =
      noise (rd (s ⟨v, Finset.mem_univ v⟩) 0 + sb G U F F' D two v (rdS G U s v)) := by
  rw [DoAudit.kfac_univ]
  first
    | show kern G U F F' D two v _ _ = _
    | simp only [M]
  rw [kern_r0 G U F F' D two hv hF hr, rdp_restrict, PMF.map_apply,
    tsum_eq_single (rd (s ⟨v, Finset.mem_univ v⟩) 0 + sb G U F F' D two v (rdS G U s v))]
  · rw [if_pos]
    exact (obs_ext hv _ _).mpr (by rw [rd_cst hv]; exact (zmod2_solve _ _ _).mpr rfl)
  · intro n hn
    rw [if_neg]
    intro h
    have h2 : rd (s ⟨v, Finset.mem_univ v⟩) 0 = sb G U F F' D two v (rdS G U s v) + n := by
      rw [h, rd_cst hv]
    exact hn ((zmod2_solve _ _ _).mp h2)

end kfacs

end PM
end Hedge

#print axioms Hedge.PM.kfac_obs
#print axioms Hedge.PM.kfac_r0

/-! ## Runde 60: `sb` uten vakter

`Good`: betingelsene konstruksjonsdataene oppfyller (fra `hedge_spanning`): `ρ` er en
observert node i `F`; for observerte `v ≠ ρ` i `F'` er `par v` observert i `F'` (i `F` når
`v ∈ F`), og `lat v` er latent med kanter til `v` og `par v`; `r0` er en observert rot.
`lb s c` er biten på trekanten `(c, par c)` og `ov s w` verdien til `w`, lest rett fra `s`.
`sb_read`: under `Good` og en hedge er `sb` bare summen av disse (vaktene i `rdS` holder:
`lat v → v`, `lat c → par c`, og `w → nxt w` fra `hedge_nxt`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Betingelsene på konstruksjonsdataene. -/
structure Good (G : DAG V) (U F F' : Finset V) (D : Data V) : Prop where
  ρF : D.ρ ∈ F
  ρU : D.ρ ∉ U
  parF' : ∀ v ∈ F', v ∉ U → v ≠ D.ρ → D.par v ∈ F' ∧ D.par v ∉ U
  parF : ∀ v ∈ F, v ∉ U → v ≠ D.ρ → D.par v ∈ F
  lat : ∀ v ∈ F', v ∉ U → v ≠ D.ρ →
    D.lat v ∈ U ∧ G.edge (D.lat v) v ∧ G.edge (D.lat v) (D.par v)
  r0R : D.r0 ∈ rootsIn G F
  r0U : D.r0 ∉ U

lemma mem_parents_iff {G : DAG V} {w v : V} : w ∈ G.parents v ↔ G.edge w v := by
  simp [DAG.parents]

section read

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (two : Bool)

/-- Biten på trekanten `(c, par c)`. -/
noncomputable def lb (s : Assignment (α := Val U) (Finset.univ : Finset V)) (c : V) : ZMod 2 :=
  rd (s ⟨D.lat c, Finset.mem_univ _⟩) (ix c)

/-- Verdien til en observert node. -/
def ov (s : Assignment (α := Val U) (Finset.univ : Finset V)) (w : V) : ZMod 2 :=
  rd (s ⟨w, Finset.mem_univ w⟩) 0

/-- `sb` lest rett fra tilordningen. -/
noncomputable def sbV (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  (if v = D.ρ then 0 else lb U D s v) +
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ scope F two v), lb U D s c +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ scope F two v), ov U s w

lemma rdS_edge (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v w : V}
    (h : G.edge w v) (i : ℕ) : rdS G U s v w i = rd (s ⟨w, Finset.mem_univ w⟩) i := by
  unfold rdS
  rw [if_pos (mem_parents_iff.mpr h)]

/-- **`sb` uten vakter.** -/
theorem sb_read {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∈ F') (hvU : v ∉ U) :
    sb G U F F' D two v (rdS G U s v) = sbV G U F F' D two s v := by
  unfold sb sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ]
        exact rdS_edge G U s (hD.lat v hvF hvU hρ).2.1 (ix v)
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF, hcU, hcρ, hpc⟩ := Finset.mem_filter.mp hc1
      have e := (hD.lat c hcF hcU hcρ).2.2
      rw [hpc] at e
      exact rdS_edge G U s e (ix c)
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwF, -, hwR, hnx⟩ := Finset.mem_filter.mp hw1
    have e := (hedge_nxt hH w hwF hwR).2.2
    rw [hnx] at e
    exact rdS_edge G U s e 0

end read

end PM
end Hedge

#print axioms Hedge.PM.sb_read

/-! ## Runde 61: forskyvningen av `F`-trebitene

`δ s v`: leddene `M1` har i `v` og `M2` ikke har (trebarn og `nxt`-barn utenfor `F`).
`sbV_split`: i `F` er `M1`-biten lik `M2`-biten pluss `δ`; `sbV_out`: utenfor `F` er de like.
`EF`: trekantene i `F` (observerte `c ≠ ρ` i `F`). `sh t s`: legger `t c` til biten på hver
trekant `c ∈ EF` (komponent `ix c` i den latente `lat c`). `sh_obs`: observerte verdier
endres ikke; `lb_sh`: trebiten øker med `t c` nøyaktig for `c ∈ EF`; `sh_sh`: `sh t` er
sin egen invers. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section shift

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

lemma scope_false (v : V) : scope F false v = Finset.univ := by simp [scope]

lemma scope_true_in {v : V} (hv : v ∈ F) : scope F true v = F := by simp [scope, hv]

lemma scope_true_out {v : V} (hv : v ∉ F) : scope F true v = Finset.univ := by simp [scope, hv]

/-- Leddene `M1` har og `M2` ikke har. -/
noncomputable def δ (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  ∑ c ∈ (CH U F' D v).filter (fun c => c ∉ F), lb U D s c +
  ∑ w ∈ (NX G U F F' v).filter (fun w => w ∉ F), ov U s w

lemma filter_univ (S : Finset V) : S.filter (fun c => c ∈ (Finset.univ : Finset V)) = S :=
  Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _)

/-- **I `F`: `M1`-biten = `M2`-biten + `δ`.** -/
theorem sbV_split (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ F) :
    sbV G U F F' D false s v = sbV G U F F' D true s v + δ G U F F' D s v := by
  unfold sbV δ
  first
    | rw [scope_false, scope_true_in F hv, filter_univ, filter_univ]
    | simp only [scope_false, scope_true_in F hv, Finset.mem_univ, Finset.filter_True]
  rw [← Finset.sum_filter_add_sum_filter_not (CH U F' D v) (fun c => c ∈ F),
    ← Finset.sum_filter_add_sum_filter_not (NX G U F F' v) (fun c => c ∈ F)]
  ring

/-- **Utenfor `F` er bitene like.** -/
theorem sbV_out (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ F) :
    sbV G U F F' D false s v = sbV G U F F' D true s v := by
  unfold sbV
  rw [scope_false, scope_true_out F hv]

/-- Trekantene i `F`. -/
def EF : Finset V := F.filter (fun c => c ∉ U ∧ c ≠ D.ρ)

/-- Forskyvningen av `F`-trebitene med `t`. -/
noncomputable def sh (t : V → ZMod 2) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u i => s u i + ∑ c ∈ (EF U F D).filter (fun c => D.lat c = u.1 ∧ ix c = i.val), t c

/-- **`sh t` er sin egen invers.** -/
lemma sh_sh (t : V → ZMod 2) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    sh U F D t (sh U F D t s) = s := by
  funext u i
  simp only [sh]
  rw [add_assoc, zmod2_add_self, add_zero]

/-- **Observerte verdier endres ikke.** -/
lemma sh_obs (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V} (hu : u ∉ U) :
    sh U F D t s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ := by
  funext i
  simp only [sh]
  rw [Finset.sum_eq_zero, add_zero]
  intro c hc
  exfalso
  obtain ⟨hcE, hlat, -⟩ := Finset.mem_filter.mp hc
  obtain ⟨hcF, hcU, hcρ⟩ := Finset.mem_filter.mp hcE
  have hl := (hD.lat c (hFF' hcF) hcU hcρ).1
  rw [hlat] at hl
  exact hu hl

/-- **Trebiten øker med `t c` nøyaktig for `c ∈ EF`.** -/
lemma lb_sh (hD : Good G U F F' D) (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {c : V} (hcF' : c ∈ F') (hcU : c ∉ U)
    (hcρ : c ≠ D.ρ) :
    lb U D (sh U F D t s) c = lb U D s c + (if c ∈ EF U F D then t c else 0) := by
  have hlU := (hD.lat c hcF' hcU hcρ).1
  have hk : ix c < kk U (D.lat c) := by
    rw [kk_lat hlU]
    exact ix_lt c
  unfold lb rd
  rw [dif_pos hk, dif_pos hk]
  simp only [sh]
  congr 1
  by_cases hc : c ∈ EF U F D
  · rw [if_pos hc]
    apply Finset.sum_eq_single c
    · intro b hb hbc
      exfalso
      obtain ⟨-, -, hix⟩ := Finset.mem_filter.mp hb
      exact hbc (ix_inj hix)
    · intro hn
      exfalso
      exact hn (Finset.mem_filter.mpr ⟨hc, rfl, rfl⟩)
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b hb
    exfalso
    obtain ⟨hbE, -, hix⟩ := Finset.mem_filter.mp hb
    have hbc : b = c := ix_inj hix
    rw [hbc] at hbE
    exact hc hbE

end shift

end PM
end Hedge

#print axioms Hedge.PM.sbV_split
#print axioms Hedge.PM.sh_obs
#print axioms Hedge.PM.lb_sh

/-! ## Runde 62: forskyvningen og bitene

`incF t v`: innfallsverdien til `t` i `F`-treet i `v` (kanten over `v` og kantene ned til
barna i `F`). `δ_sh`: forskyvningen endrer ikke `δ`, siden `δ` bare leser trekanter
utenfor `F` og observerte verdier. `sbV2_sh`: i `F` øker `M2`-biten med `incF t v`. Velges
`t` med `incF t = δ`, blir `M2`-biten av `sh t s` lik `M1`-biten av `s` i hele `F`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section shift2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- Innfallsverdien til `t` i `F`-treet. -/
noncomputable def incF (t : V → ZMod 2) (v : V) : ZMod 2 :=
  (if v = D.ρ then 0 else t v) + ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), t c

lemma ov_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V} (hw : w ∉ U) :
    ov U (sh U F D t s) w = ov U s w := by
  unfold ov
  rw [sh_obs G U F F' D hD hFF' t s hw]

/-- **Forskyvningen endrer ikke `δ`.** -/
theorem δ_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    δ G U F F' D (sh U F D t s) v = δ G U F F' D s v := by
  unfold δ
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcnF⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
    rw [lb_sh G U F F' D hD t s hcF' hcU hcρ,
      if_neg (show c ∉ EF U F D from fun h => hcnF (Finset.mem_filter.mp h).1), add_zero]
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU

/-- **I `F` øker `M2`-biten med `incF t v`.** -/
theorem sbV2_sh (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∈ F) (hvU : v ∉ U) :
    sbV G U F F' D true (sh U F D t s) v = sbV G U F F' D true s v + incF U F F' D t v := by
  have hvF' := hFF' hvF
  have hown : (if v = D.ρ then 0 else lb U D (sh U F D t s) v) =
      (if v = D.ρ then 0 else lb U D s v) + (if v = D.ρ then 0 else t v) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ, if_pos hρ, add_zero]
    · rw [if_neg hρ, if_neg hρ, if_neg hρ, lb_sh G U F F' D hD t s hvF' hvU hρ,
        if_pos (show v ∈ EF U F D from Finset.mem_filter.mpr ⟨hvF, hvU, hρ⟩)]
  have hch : ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), lb U D (sh U F D t s) c =
      ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), lb U D s c +
        ∑ c ∈ (CH U F' D v).filter (fun c => c ∈ F), t c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcF⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
    rw [lb_sh G U F F' D hD t s hcF' hcU hcρ, if_pos (show c ∈ EF U F D from Finset.mem_filter.mpr ⟨hcF, hcU, hcρ⟩)]
  have hnx : ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ F), ov U (sh U F D t s) w =
      ∑ w ∈ (NX G U F F' v).filter (fun w => w ∈ F), ov U s w := by
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU
  unfold sbV incF
  rw [scope_true_in F hvF]
  first
    | rw [hown, hch, hnx]
    | simp only [hown, hch, hnx]
  ring

end shift2

end PM
end Hedge

#print axioms Hedge.PM.δ_sh
#print axioms Hedge.PM.sbV2_sh

/-! ## Runde 63: involusjonen

`OF`: de observerte nodene i `F`. `incF_eq_inc`: `incF` er innfallsfunksjonen `inc` på `OF`
med rot `ρ`. `exists_shift`: er `F`-treet et `ParTree` og `Σ_{OF} τ = 0`, finnes `t` med
`incF t = τ` på `OF` (fra `inc_surj`). `tsel τ` velger en slik `t` (eller `0`), og
`phiS s = sh (tsel (δ s)) s`. `phiS_invol`: `phiS` er en involusjon, siden `δ` ikke endres av
forskyvningen og dermed velges samme `t` begge ganger. `phiS_restrict`: `phiS` endrer ingen
observerte verdier. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section invol

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- De observerte nodene i `F`. -/
def OF : Finset V := F.filter (fun v => v ∉ U)

lemma incF_eq_inc (hFF' : F ⊆ F') (t : V → ZMod 2) (v : V) :
    incF U F F' D t v = inc (OF U F) D.ρ D.par t v := by
  unfold incF inc
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [CH, OF, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, hU, hρ, hp⟩, hF⟩
    exact ⟨⟨hF, hU⟩, hρ, hp⟩
  · rintro ⟨⟨hF, hU⟩, hρ, hp⟩
    exact ⟨⟨hFF' hF, hU, hρ, hp⟩, hF⟩

/-- **Forskyvningen finnes** når `δ` summerer til null over `F`. -/
theorem exists_shift (hFF' : F ⊆ F') {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (τ : V → ZMod 2) (hτ : ∑ v ∈ OF U F, τ v = 0) :
    ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v := by
  obtain ⟨b, hb⟩ := inc_surj (OF U F).card (OF U F) τ rfl T hτ
  exact ⟨b, fun v hv => by rw [incF_eq_inc U F F' D hFF']; exact hb v hv⟩

open Classical in
/-- En forskyvning som løser `incF t = τ` på `OF`, når en finnes. -/
noncomputable def tsel (τ : V → ZMod 2) : V → ZMod 2 :=
  if h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v then Classical.choose h else 0

lemma tsel_spec (τ : V → ZMod 2)
    (h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = τ v) :
    ∀ v ∈ OF U F, incF U F F' D (tsel U F F' D τ) v = τ v := by
  unfold tsel
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Involusjonen.** -/
noncomputable def phiS (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  sh U F D (tsel U F F' D (δ G U F F' D s)) s

theorem phiS_invol (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    phiS G U F F' D (phiS G U F F' D s) = s := by
  unfold phiS
  have h : δ G U F F' D (sh U F D (tsel U F F' D (δ G U F F' D s)) s) = δ G U F F' D s :=
    funext (δ_sh G U F F' D hD hFF' _ s)
  rw [h, sh_sh]

theorem phiS_restrict (hD : Good G U F F' D) (hFF' : F ⊆ F') {O : Finset V}
    (hO : ∀ v ∈ O, v ∉ U) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (phiS G U F F' D s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O) := by
  funext ⟨v, hv⟩
  exact sh_obs G U F F' D hD hFF' _ s (hO v hv)

end invol

end PM
end Hedge

#print axioms Hedge.PM.exists_shift
#print axioms Hedge.PM.phiS_invol
#print axioms Hedge.PM.phiS_restrict

/-! ## Runde 64: like faktorer når forskyvningen finnes

`sbV1_sh_out`: utenfor `F` leser `M1`-biten ingenting forskyvningen endrer (et trebarn av en
node utenfor `F` ligger selv utenfor `F`, siden `par` holder `F`). `kfac_phiS`: når
`tsel (δ s)` løser `incF t = δ s` på `OF`, er hver kjernefaktor i `M2` på `phiS s` lik
faktoren i `M1` på `s`: uniforme faktorer er like; i `F` er `M2`-biten + `incF t` =
`M2`-biten + `δ` = `M1`-biten; utenfor `F` er bitene like; observerte verdier er uendret. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section factors

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

theorem sbV1_sh_out (hD : Good G U F F' D) (hFF' : F ⊆ F') (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF : v ∉ F) (hvF' : v ∈ F')
    (hvU : v ∉ U) :
    sbV G U F F' D false (sh U F D t s) v = sbV G U F F' D false s v := by
  unfold sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ, lb_sh G U F F' D hD t s hvF' hvU hρ,
          if_neg (show v ∉ EF U F D from fun h => hvF (Finset.mem_filter.mp h).1), add_zero]
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF', hcU, hcρ, hpc⟩ := Finset.mem_filter.mp hc1
      rw [lb_sh G U F F' D hD t s hcF' hcU hcρ,
        if_neg (show c ∉ EF U F D from fun h =>
          hvF (hpc ▸ hD.parF c (Finset.mem_filter.mp h).1 hcU hcρ)), add_zero]
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw1
    exact ov_sh G U F F' D hD hFF' t s hwU

/-- **Like faktorer** når forskyvningen løser `incF t = δ s`. -/
theorem kfac_phiS {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hsol : ∀ v ∈ OF U F, incF U F F' D (tsel U F F' D (δ G U F F' D s)) v = δ G U F F' D s v)
    (v : V) :
    kfac (M G U F F' D true) Finset.univ (phiS G U F F' D s) v =
      kfac (M G U F F' D false) Finset.univ s v := by
  have hFF' := hH.sub
  by_cases hvU : v ∈ U
  · rw [kfac_lat G U F F' D true _ hvU, kfac_lat G U F F' D false _ hvU]
  by_cases hvF' : v ∈ F'
  swap
  · rw [kfac_out G U F F' D true _ hvU hvF', kfac_out G U F F' D false _ hvU hvF']
  have hrd : rd (phiS G U F F' D s ⟨v, Finset.mem_univ v⟩) 0 = rd (s ⟨v, Finset.mem_univ v⟩) 0 := by
    unfold phiS
    rw [sh_obs G U F F' D hD hFF' _ s hvU]
  have hsb : sb G U F F' D true v (rdS G U (phiS G U F F' D s) v) =
      sb G U F F' D false v (rdS G U s v) := by
    rw [sb_read G U F F' D true hH hD _ hvF' hvU, sb_read G U F F' D false hH hD _ hvF' hvU]
    by_cases hvF : v ∈ F
    · unfold phiS
      rw [sbV2_sh G U F F' D hD hFF' _ s hvF hvU, hsol v (Finset.mem_filter.mpr ⟨hvF, hvU⟩),
        sbV_split G U F F' D s hvF]
    · rw [← sbV_out G U F F' D _ hvF]
      unfold phiS
      exact sbV1_sh_out G U F F' D hD hFF' _ s hvF hvF' hvU
  by_cases hr : v = D.r0
  · rw [kfac_r0 G U F F' D true _ hvU hvF' hr, kfac_r0 G U F F' D false _ hvU hvF' hr, hrd, hsb]
  · rw [kfac_obs G U F F' D true _ hvU hvF' hr, kfac_obs G U F F' D false _ hvU hvF' hr, hrd, hsb]

end factors

end PM
end Hedge

#print axioms Hedge.PM.sbV1_sh_out
#print axioms Hedge.PM.kfac_phiS

/-! ## Runde 65: verktøy for teleskoperingen

`Out`: de observerte nodene i `F' \ F`. `fiber_sum`: `Σ_{v ∈ T} Σ_{c ∈ S, p c = v} g c` er
`Σ_{c ∈ S, p c ∈ T} g c`. `part_sum`: dekker `A` og `B` (disjunkte) alle `p c`, deles en sum
over `S` etter om `p c ∈ A` eller `p c ∈ B`. `CH_out`, `NX_out`: barna utenfor `F` til en
node er nodene i `Out` med den som forelder (`par` eller `nxt`); `CH_in_out`, `NX_in_out`:
for en node utenfor `F` ligger alle barna i `Out`. `par_cover`, `nxt_cover`: forelderen til en
node i `Out` ligger i `OF` eller i `Out`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma fiber_sum (T S : Finset V) (p : V → V) (g : V → ZMod 2) :
    ∑ v ∈ T, ∑ c ∈ S.filter (fun c => p c = v), g c = ∑ c ∈ S.filter (fun c => p c ∈ T), g c := by
  calc ∑ v ∈ T, ∑ c ∈ S.filter (fun c => p c = v), g c
      = ∑ v ∈ T, ∑ c ∈ S, (if p c = v then g c else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_filter]
    _ = ∑ c ∈ S, ∑ v ∈ T, (if p c = v then g c else 0) := Finset.sum_comm
    _ = ∑ c ∈ S, (if p c ∈ T then g c else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_ite_eq]
    _ = ∑ c ∈ S.filter (fun c => p c ∈ T), g c := by rw [Finset.sum_filter]

lemma part_sum (S A B : Finset V) (p : V → V) (g : V → ZMod 2)
    (hcov : ∀ c ∈ S, p c ∈ A ∨ p c ∈ B) (hdis : ∀ x, x ∈ A → x ∉ B) :
    ∑ c ∈ S, g c = ∑ c ∈ S.filter (fun c => p c ∈ A), g c + ∑ c ∈ S.filter (fun c => p c ∈ B), g c := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun c => p c ∈ A) g]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro c hc
  constructor
  · intro h
    rcases hcov c hc with h' | h'
    · exact absurd h' h
    · exact h'
  · intro h h'
    exact hdis _ h' h

section tele

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- De observerte nodene i `F' \ F`. -/
def Out : Finset V := F'.filter (fun w => w ∉ U ∧ w ∉ F)

lemma OF_Out_dis : ∀ x, x ∈ OF U F → x ∉ Out U F F' :=
  fun _ h1 h2 => (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).1

lemma CH_out (hD : Good G U F F' D) (v : V) :
    (CH U F' D v).filter (fun c => c ∉ F) = (Out U F F').filter (fun c => D.par c = v) := by
  ext c
  simp only [CH, Out, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hF', hU, -, hp⟩, hnF⟩
    exact ⟨⟨hF', hU, hnF⟩, hp⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hp⟩
    exact ⟨⟨hF', hU, fun h => hnF (h ▸ hD.ρF), hp⟩, hnF⟩

lemma NX_out (v : V) :
    (NX G U F F' v).filter (fun c => c ∉ F) = (Out U F F').filter (fun c => nxt G F F' c = v) := by
  ext c
  simp only [NX, Out, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hF', hU, -, hn⟩, hnF⟩
    exact ⟨⟨hF', hU, hnF⟩, hn⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hn⟩
    exact ⟨⟨hF', hU, fun h => hnF (Finset.mem_filter.mp h).1, hn⟩, hnF⟩

lemma CH_in_out (hD : Good G U F F' D) {w : V} (hw : w ∉ F) :
    CH U F' D w = (Out U F F').filter (fun c => D.par c = w) := by
  ext c
  simp only [CH, Out, Finset.mem_filter]
  constructor
  · rintro ⟨hF', hU, hρ, hp⟩
    exact ⟨⟨hF', hU, fun hcF => hw (hp ▸ hD.parF c hcF hU hρ)⟩, hp⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hp⟩
    exact ⟨hF', hU, fun h => hnF (h ▸ hD.ρF), hp⟩

lemma NX_in_out {X Y : Finset V} (hH : IsHedge G U X Y F F') {w : V} (hw : w ∉ F) :
    NX G U F F' w = (Out U F F').filter (fun c => nxt G F F' c = w) := by
  ext c
  simp only [NX, Out, Finset.mem_filter]
  constructor
  · rintro ⟨hF', hU, hR, hn⟩
    exact ⟨⟨hF', hU, fun hcF => hw (hn ▸ (hedge_nxt hH c hF' hR).1 hcF)⟩, hn⟩
  · rintro ⟨⟨hF', hU, hnF⟩, hn⟩
    exact ⟨hF', hU, fun h => hnF (Finset.mem_filter.mp h).1, hn⟩

lemma par_cover (hD : Good G U F F' D) {c : V} (hc : c ∈ Out U F F') :
    D.par c ∈ OF U F ∨ D.par c ∈ Out U F F' := by
  obtain ⟨hF', hU, hnF⟩ := Finset.mem_filter.mp hc
  have hρ : c ≠ D.ρ := fun h => hnF (h ▸ hD.ρF)
  obtain ⟨hpF', hpU⟩ := hD.parF' c hF' hU hρ
  by_cases hpF : D.par c ∈ F
  · exact Or.inl (Finset.mem_filter.mpr ⟨hpF, hpU⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hpF', hpU, hpF⟩)

lemma nxt_cover {X Y : Finset V} (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {c : V} (hc : c ∈ Out U F F') :
    nxt G F F' c ∈ OF U F ∨ nxt G F F' c ∈ Out U F F' := by
  obtain ⟨hF', -, hnF⟩ := Finset.mem_filter.mp hc
  have hR : c ∉ rootsIn G F := fun h => hnF (Finset.mem_filter.mp h).1
  obtain ⟨-, hnF', he⟩ := hedge_nxt hH c hF' hR
  have hnU : nxt G F F' c ∉ U := fun h => hroot _ h c he
  by_cases hnF2 : nxt G F F' c ∈ F
  · exact Or.inl (Finset.mem_filter.mpr ⟨hnF2, hnU⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hnF', hnU, hnF2⟩)

end tele

end PM
end Hedge

#print axioms Hedge.PM.fiber_sum
#print axioms Hedge.PM.part_sum
#print axioms Hedge.PM.NX_in_out
#print axioms Hedge.PM.nxt_cover

/-! ## Runde 66: teleskoperingsidentiteten

`tele`: når hver observert node i `F' \ F` oppfyller sin ligning i `M1` (`ov w = sbV false w`),
summerer `δ` til null over `OF`. Bevis: `Σ_{OF} δ` er summen av trebitene og verdiene som går
fra `Out` inn i `F` (`hA`); summen av ligningene over `Out` (`hB`) og delingen etter om
forelderen ligger i `F` eller i `Out` (`part_sum`) gir `Σ_{OF} δ = 2 Σ_{Out} lb = 0`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_tele : ∀ a b c e : ZMod 2, c + e = a + b + b + e → a + c = 0 := by decide

section tele2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- **Teleskoperingsidentiteten.** -/
theorem tele {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hcons : ∀ w ∈ Out U F F', ov U s w = sbV G U F F' D false s w) :
    ∑ v ∈ OF U F, δ G U F F' D s v = 0 := by
  have hA : ∑ v ∈ OF U F, δ G U F F' D s v =
      ∑ c ∈ (Out U F F').filter (fun c => D.par c ∈ OF U F), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c ∈ OF U F), ov U s c := by
    unfold δ
    rw [Finset.sum_add_distrib]
    simp only [CH_out G U F F' D hD, NX_out G U F F']
    rw [fiber_sum (OF U F) (Out U F F') D.par (lb U D s),
      fiber_sum (OF U F) (Out U F F') (nxt G F F') (ov U s)]
  have hexp : ∀ w ∈ Out U F F', sbV G U F F' D false s w =
      lb U D s w + ∑ c ∈ (Out U F F').filter (fun c => D.par c = w), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c = w), ov U s c := by
    intro w hw
    obtain ⟨-, -, hwF⟩ := Finset.mem_filter.mp hw
    have hwρ : w ≠ D.ρ := fun h => hwF (h ▸ hD.ρF)
    unfold sbV
    first
      | rw [if_neg hwρ, scope_false, filter_univ, filter_univ, CH_in_out G U F F' D hD hwF,
          NX_in_out G U F F' hH hwF]
      | (simp only [if_neg hwρ, scope_false, Finset.mem_univ, Finset.filter_True]
         rw [CH_in_out G U F F' D hD hwF, NX_in_out G U F F' hH hwF])
  have hB : ∑ w ∈ Out U F F', ov U s w =
      ∑ w ∈ Out U F F', lb U D s w +
        ∑ c ∈ (Out U F F').filter (fun c => D.par c ∈ Out U F F'), lb U D s c +
        ∑ c ∈ (Out U F F').filter (fun c => nxt G F F' c ∈ Out U F F'), ov U s c := by
    rw [Finset.sum_congr rfl hcons, Finset.sum_congr rfl hexp, Finset.sum_add_distrib,
      Finset.sum_add_distrib, fiber_sum (Out U F F') (Out U F F') D.par (lb U D s),
      fiber_sum (Out U F F') (Out U F F') (nxt G F F') (ov U s)]
  have hP1 := part_sum (Out U F F') (OF U F) (Out U F F') D.par (lb U D s)
    (fun c hc => par_cover G U F F' D hD hc) (OF_Out_dis U F F')
  have hP2 := part_sum (Out U F F') (OF U F) (Out U F F') (nxt G F F') (ov U s)
    (fun c hc => nxt_cover G U F F' hH hroot hc) (OF_Out_dis U F F')
  rw [hP1, hP2] at hB
  rw [hA]
  exact zmod2_tele _ _ _ _ hB

end tele2

end PM
end Hedge

#print axioms Hedge.PM.tele

/-! ## Runde 67: felles-likheten og lik observert fordeling

`sh_zero`, `phiS_fix`: finnes ingen forskyvning, er `tsel = 0` og `phiS s = s`. `kfac_zero`:
bryter en node `w ∈ Out` sin ligning i `M1`, er faktoren hans 0 i begge modellene (utenfor `F`
er `M1`- og `M2`-biten like, og `w ≠ r0` siden `r0 ∈ F`). `joint_phiS`: `M2.fullJoint (phiS s)
= M1.fullJoint s`; finnes forskyvningen, er faktorene like (`kfac_phiS`); ellers er
`Σ_{OF} δ ≠ 0` (`exists_shift`), så etter `tele` bryter en `w ∈ Out` ligningen, og begge sider
er 0. `marg_eq`: `M1` og `M2` har samme fordeling på enhver mengde observerte noder. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section joint

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

lemma sh_zero (s : Assignment (α := Val U) (Finset.univ : Finset V)) : sh U F D 0 s = s := by
  funext u i
  simp only [sh, Pi.zero_apply, Finset.sum_const_zero, add_zero]

lemma phiS_fix (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (h : ¬ ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = δ G U F F' D s v) :
    phiS G U F F' D s = s := by
  have h0 : tsel U F F' D (δ G U F F' D s) = 0 := by
    unfold tsel
    exact dif_neg h
  unfold phiS
  rw [h0]
  exact sh_zero U F D s

/-- **En brutt ligning gir faktor 0** i begge modellene. -/
lemma kfac_zero {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D) (two : Bool)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V} (hw : w ∈ Out U F F')
    (hne : ov U s w ≠ sbV G U F F' D false s w) :
    kfac (M G U F F' D two) Finset.univ s w = 0 := by
  obtain ⟨hwF', hwU, hwF⟩ := Finset.mem_filter.mp hw
  have hr : w ≠ D.r0 := fun h => hwF (by rw [h]; exact (Finset.mem_filter.mp hD.r0R).1)
  have h2 : sbV G U F F' D two s w = sbV G U F F' D false s w := by
    cases two
    · rfl
    · exact (sbV_out G U F F' D s hwF).symm
  rw [kfac_obs G U F F' D two s hwU hwF' hr, sb_read G U F F' D two hH hD s hwF' hwU, if_neg]
  intro h
  exact hne (h.trans h2)

/-- **Felles-likheten.** -/
theorem joint_phiS {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (M G U F F' D true).fullJoint (phiS G U F F' D s) = (M G U F F' D false).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  by_cases h : ∃ t : V → ZMod 2, ∀ v ∈ OF U F, incF U F F' D t v = δ G U F F' D s v
  · exact Finset.prod_congr rfl
      (fun v _ => kfac_phiS G U F F' D hH hD s (tsel_spec U F F' D _ h) v)
  · have hsum : ∑ v ∈ OF U F, δ G U F F' D s v ≠ 0 :=
      fun h0 => h (exists_shift U F F' D hH.sub T _ h0)
    have hbad : ∃ w ∈ Out U F F', ov U s w ≠ sbV G U F F' D false s w := by
      by_contra hno
      push_neg at hno
      exact hsum (tele G U F F' D hH hD hroot s hno)
    obtain ⟨w, hw, hne⟩ := hbad
    rw [phiS_fix G U F F' D s h,
      Finset.prod_eq_zero (Finset.mem_univ w) (kfac_zero G U F F' D hH hD true s hw hne),
      Finset.prod_eq_zero (Finset.mem_univ w) (kfac_zero G U F F' D hH hD false s hw hne)]

/-- **Lik observert fordeling.** -/
theorem marg_eq {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    (M G U F F' D false).marginal O = (M G U F F' D true).marginal O :=
  marginal_eq_of_invol _ _ O (phiS G U F F' D) (phiS_invol G U F F' D hD hH.sub)
    (phiS_restrict G U F F' D hD hH.sub hO) (joint_phiS G U F F' D hH hD hroot T)

end joint

end PM
end Hedge

#print axioms Hedge.PM.joint_phiS
#print axioms Hedge.PM.marg_eq

/-! ## Runde 68: positivitet i `M1`

`noise_pos`: begge støyverdiene har positiv sannsynlighet. `lb_shE`, `obs_shE`: forskyvningen
`sh` med en vilkårlig kantmengde `E` (her hele `F'`-treet). `baseA a`: `a` på `O`, ellers 0.
`sbV_base`: på `sh U F' D b (baseA a)` er `M1`-biten for `v ∈ F'` lik `inc b v` pluss
`nxt`-barnas verdier. `pos_M1`: velg `τ v` = verdien til `v` pluss `nxt`-barnas verdier for
`v ≠ r0`, og `τ r0` slik at `Σ τ = 0`; `inc_surj` på `F'`-treet gir bitene `b`. Da holder alle
ligningene utenom i `r0`, og der tar støyen opp avviket; så har hver `a` positiv
sannsynlighet. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma noise_pos (n : ZMod 2) : noise n ≠ 0 := by
  rw [← PMF.mem_support_iff]
  unfold noise
  rw [PMF.support_map, PMF.support_uniformOfFintype]
  obtain ⟨i, hi⟩ := (show ∀ m : ZMod 2, ∃ i : Fin 4, (if i = 0 then (1 : ZMod 2) else 0) = m by
    decide) n
  exact ⟨i, Set.mem_univ _, hi⟩

section posM1

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

lemma lb_shE (E : Finset V) (t : V → ZMod 2) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    {c : V} (hl : D.lat c ∈ U) :
    lb U D (sh U E D t s) c = lb U D s c + (if c ∈ EF U E D then t c else 0) := by
  have hk : ix c < kk U (D.lat c) := by
    rw [kk_lat hl]
    exact ix_lt c
  unfold lb rd
  rw [dif_pos hk, dif_pos hk]
  simp only [sh]
  congr 1
  by_cases hc : c ∈ EF U E D
  · rw [if_pos hc]
    apply Finset.sum_eq_single c
    · intro b hb hbc
      exfalso
      obtain ⟨-, -, hix⟩ := Finset.mem_filter.mp hb
      exact hbc (ix_inj hix)
    · intro hn
      exfalso
      exact hn (Finset.mem_filter.mpr ⟨hc, rfl, rfl⟩)
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b hb
    exfalso
    obtain ⟨hbE, -, hix⟩ := Finset.mem_filter.mp hb
    have hbc : b = c := ix_inj hix
    rw [hbc] at hbE
    exact hc hbE

lemma obs_shE (E : Finset V) (hE : ∀ c ∈ EF U E D, D.lat c ∈ U) (t : V → ZMod 2)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V} (hu : u ∉ U) :
    sh U E D t s ⟨u, Finset.mem_univ u⟩ = s ⟨u, Finset.mem_univ u⟩ := by
  funext i
  simp only [sh]
  rw [Finset.sum_eq_zero, add_zero]
  intro c hc
  exfalso
  obtain ⟨hcE, hlat, -⟩ := Finset.mem_filter.mp hc
  have hl := hE c hcE
  rw [hlat] at hl
  exact hu hl

lemma EF_lat (hD : Good G U F F' D) : ∀ c ∈ EF U F' D, D.lat c ∈ U := fun c hc => by
  obtain ⟨hcF', hcU, hcρ⟩ := Finset.mem_filter.mp hc
  exact (hD.lat c hcF' hcU hcρ).1

/-- Grunntilordningen: `a` på `O`, ellers 0. -/
def baseA {O : Finset V} (a : Assignment (α := Val U) O) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u => if h : u.1 ∈ O then a ⟨u.1, h⟩ else 0

lemma lb_base {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) (a : Assignment (α := Val U) O) {c : V}
    (hl : D.lat c ∈ U) : lb U D (baseA U a) c = 0 := by
  have hn : D.lat c ∉ O := fun h => hO _ h hl
  have h0 : baseA U a ⟨D.lat c, Finset.mem_univ _⟩ = 0 := dif_neg hn
  unfold lb
  rw [h0]
  unfold rd
  split_ifs <;> rfl

theorem sbV_base (hD : Good G U F F' D) {O : Finset V} (hO : ∀ v ∈ O, v ∉ U)
    (a : Assignment (α := Val U) O) (b : V → ZMod 2) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D false (sh U F' D b (baseA U a)) v =
      inc (OF U F') D.ρ D.par b v + ∑ w ∈ NX G U F F' v, ov U (baseA U a) w := by
  have hE := EF_lat G U F F' D hD
  have hlb : ∀ c ∈ F', c ∉ U → c ≠ D.ρ → lb U D (sh U F' D b (baseA U a)) c = b c := by
    intro c hcF' hcU hcρ
    rw [lb_shE U D F' b _ (hD.lat c hcF' hcU hcρ).1, lb_base U D hO a (hD.lat c hcF' hcU hcρ).1,
      if_pos (show c ∈ EF U F' D from Finset.mem_filter.mpr ⟨hcF', hcU, hcρ⟩), zero_add]
  have hown : (if v = D.ρ then 0 else lb U D (sh U F' D b (baseA U a)) v) =
      (if v = D.ρ then 0 else b v) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ]
    · rw [if_neg hρ, if_neg hρ, hlb v hvF' hvU hρ]
  have hset : CH U F' D v = (OF U F').filter (fun c => c ≠ D.ρ ∧ D.par c = v) := by
    ext c
    simp only [CH, OF, Finset.mem_filter]
    tauto
  have hch : ∑ c ∈ CH U F' D v, lb U D (sh U F' D b (baseA U a)) c =
      ∑ c ∈ (OF U F').filter (fun c => c ≠ D.ρ ∧ D.par c = v), b c := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hc1, hcρ, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF', hcU⟩ := Finset.mem_filter.mp hc1
    exact hlb c hcF' hcU hcρ
  have hnx : ∑ w ∈ NX G U F F' v, ov U (sh U F' D b (baseA U a)) w =
      ∑ w ∈ NX G U F F' v, ov U (baseA U a) w := by
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw
    unfold ov
    rw [obs_shE U D F' hE b _ hwU]
  unfold sbV inc
  first
    | rw [scope_false, filter_univ, filter_univ, hown, hch, hnx]
    | (simp only [scope_false, Finset.mem_univ, Finset.filter_True]
       rw [hown, hch, hnx])

/-- Høyresiden i ligningene, uten `inc`. -/
noncomputable def sigA {O : Finset V} (a : Assignment (α := Val U) O) (v : V) : ZMod 2 :=
  ov U (baseA U a) v + ∑ w ∈ NX G U F F' v, ov U (baseA U a) w

/-- Målet for `inc_surj`: `sigA` utenom `r0`, og i `r0` det som gjør summen 0. -/
noncomputable def tauP {O : Finset V} (a : Assignment (α := Val U) O) (v : V) : ZMod 2 :=
  if v = D.r0 then ∑ u ∈ (OF U F').erase D.r0, sigA G U F F' a u else sigA G U F F' a v

lemma tauP_sum {O : Finset V} (a : Assignment (α := Val U) O) (hr : D.r0 ∈ OF U F') :
    ∑ v ∈ OF U F', tauP G U F F' D a v = 0 := by
  rw [← Finset.add_sum_erase (OF U F') (tauP G U F F' D a) hr]
  have h : ∑ v ∈ (OF U F').erase D.r0, tauP G U F F' D a v =
      ∑ v ∈ (OF U F').erase D.r0, sigA G U F F' a v := by
    apply Finset.sum_congr rfl
    intro v hv
    unfold tauP
    rw [if_neg (Finset.ne_of_mem_erase hv)]
  rw [h]
  unfold tauP
  rw [if_pos rfl, zmod2_add_self]

/-- **Positivitet**: hver observert tilordning har positiv sannsynlighet i `M1`. -/
theorem pos_M1 {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    {d : V → ℕ} (T : ParTree (OF U F') D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) (a : Assignment (α := Val U) O) :
    (M G U F F' D false).marginal O a ≠ 0 := by
  have hE := EF_lat G U F F' D hD
  have hr0 : D.r0 ∈ OF U F' :=
    Finset.mem_filter.mpr ⟨hH.sub (Finset.mem_filter.mp hD.r0R).1, hD.r0U⟩
  obtain ⟨b, hb⟩ := inc_surj (OF U F').card (OF U F') (tauP G U F F' D a) rfl T
    (tauP_sum G U F F' D a hr0)
  have hrestr : (sh U F' D b (baseA U a)).restrict (Finset.subset_univ O) = a := by
    funext ⟨v, hv⟩
    show sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩
    rw [obs_shE U D F' hE b _ (hO v hv)]
    exact dif_pos hv
  have hj : (M G U F F' D false).fullJoint (sh U F' D b (baseA U a)) ≠ 0 := by
    rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff]
    intro v _
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D false _ hvU]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D false _ hvU hvF']
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    by_cases hr : v = D.r0
    · rw [kfac_r0 G U F F' D false _ hvU hvF' hr]
      exact noise_pos _
    have hov : rd (sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩) 0 = ov U (baseA U a) v := by
      unfold ov
      rw [obs_shE U D F' hE b _ hvU]
    have heq : rd (sh U F' D b (baseA U a) ⟨v, Finset.mem_univ v⟩) 0 =
        sb G U F F' D false v (rdS G U (sh U F' D b (baseA U a)) v) := by
      rw [sb_read G U F F' D false hH hD _ hvF' hvU, sbV_base G U F F' D hD hO a b hvF' hvU,
        hb v (Finset.mem_filter.mpr ⟨hvF', hvU⟩), hov]
      unfold tauP sigA
      rw [if_neg hr, add_assoc, zmod2_add_self, add_zero]
    rw [kfac_obs G U F F' D false _ hvU hvF' hr, if_pos heq]
    exact one_ne_zero
  intro h0
  have hmem : a ∈ ((M G U F F' D false).marginal O).support := by
    unfold CausalModel.marginal
    rw [PMF.mem_support_map_iff]
    exact ⟨_, (PMF.mem_support_iff _ _).mpr hj, hrestr⟩
  exact (PMF.mem_support_iff _ _).mp hmem h0

end posM1

end PM
end Hedge

#print axioms Hedge.PM.noise_pos
#print axioms Hedge.PM.pos_M1

/-! ## Runde 69: stier langs `nxt` som unngår `X`

Forberedelse til do-forskjellen. `hedge_rank_iter`: fra en ikke-rot øker rangen langs `nxt`;
`hedge_cycle`: kommer `nxt` tilbake til `v`, er `v` en rot. `iter_obs`: fra en observert node
er hele `nxt`-stien observert (latente har ingen foreldre). `nreach s w`: `w` nås fra `s`
langs `nxt` uten å treffe `X` underveis (`w` selv og `s` medregnet); `nrI` er indikatoren i
`ZMod 2`. `nrI_rec`: for `v ∈ F' \ X` er `nrI s v = [v = s] + Σ_{w ∈ NX v} nrI s w` (høyst
én forgjenger på stien, `pred_aux`). `sum_nrI_roots`: en sti når høyst én rot. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

section nreach

variable {G : DAG V} {U X Y F F' : Finset V}

lemma hedge_rank_iter (hH : IsHedge G U X Y F F') {v : V} (hv : v ∈ F')
    (hR : v ∉ rootsIn G F) : ∀ m, G.rank v < G.rank ((nxt G F F')^[m + 1] v) := by
  intro m
  induction m with
  | zero =>
    show G.rank v < G.rank (nxt G F F' v)
    exact G.rank_strict_mono _ _ (hedge_nxt hH v hv hR).2.2
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases huR : (nxt G F F')^[m + 1] v ∈ rootsIn G F
    · rw [nxt_root G F F' _ huR]
      exact ih
    · exact lt_trans ih
        (G.rank_strict_mono _ _ (hedge_nxt hH _ (hedge_iter_mem hH hv (m + 1)) huR).2.2)

lemma hedge_cycle (hH : IsHedge G U X Y F F') {v : V} (hv : v ∈ F') {m : ℕ}
    (h : (nxt G F F')^[m + 1] v = v) : v ∈ rootsIn G F := by
  by_contra hR
  have hlt := hedge_rank_iter hH hv hR m
  rw [h] at hlt
  exact lt_irrefl _ hlt

lemma iter_obs (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s : V}
    (hs : s ∈ F') (hsU : s ∉ U) : ∀ n, (nxt G F F')^[n] s ∉ U := by
  intro n
  induction n with
  | zero => exact hsU
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hR : (nxt G F F')^[n] s ∈ rootsIn G F
    · rw [nxt_root G F F' _ hR]
      exact ih
    · intro hU
      exact hroot _ hU _ (hedge_nxt hH _ (hedge_iter_mem hH hs n) hR).2.2

/-- `w` nås fra `s` langs `nxt` uten å treffe `X`. -/
abbrev nreach (G : DAG V) (X F F' : Finset V) (s w : V) : Prop :=
  ∃ k, (nxt G F F')^[k] s = w ∧ ∀ j ≤ k, (nxt G F F')^[j] s ∉ X

open Classical in
/-- Indikatoren for `nreach` i `ZMod 2`. -/
noncomputable def nrI (G : DAG V) (X F F' : Finset V) (s w : V) : ZMod 2 :=
  if nreach G X F F' s w then 1 else 0

lemma pred_aux (hH : IsHedge G U X Y F F') {s v w w' : V} (hs : s ∈ F') {k k' : ℕ} (hk : k < k')
    (h1 : (nxt G F F')^[k] s = w) (h2 : (nxt G F F')^[k'] s = w')
    (hwv : nxt G F F' w = v) (hw'v : nxt G F F' w' = v) (hw' : w' ∉ rootsIn G F) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hv : (nxt G F F')^[k + 1] s = v := by
    rw [Function.iterate_succ_apply', h1, hwv]
  have hw'm : (nxt G F F')^[m] v = w' := by
    rw [← hv, ← Function.iterate_add_apply, ← h2, show m + (k + 1) = k + m + 1 by omega]
  have hvF : v ∈ F' := by
    rw [← hv]
    exact hedge_iter_mem hH hs (k + 1)
  have hcyc : (nxt G F F')^[m + 1] v = v := by
    rw [Function.iterate_succ_apply', hw'm, hw'v]
  have hR := hedge_cycle hH hvF hcyc
  apply hw'
  rw [← hw'm, iter_root G F F' v hR m]
  exact hR

/-- **Rekursjonen for `nrI`** langs `nxt`. -/
theorem nrI_rec (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s v : V}
    (hs : s ∈ F') (hsU : s ∉ U) (hv : v ∈ F') (hvX : v ∉ X) :
    nrI G X F F' s v = (if v = s then 1 else 0) +
      ∑ w ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v), nrI G X F F' s w := by
  classical
  have huniq : ∀ w ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v),
      ∀ w' ∈ F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v),
      nreach G X F F' s w → nreach G X F F' s w' → w = w' := by
    intro w hw w' hw' h h'
    obtain ⟨-, -, hwR, hwv⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, -, hw'R, hw'v⟩ := Finset.mem_filter.mp hw'
    obtain ⟨k, hk, -⟩ := h
    obtain ⟨k', hk', -⟩ := h'
    rcases lt_trichotomy k k' with hl | he | hl
    · exact (pred_aux hH hs hl hk hk' hwv hw'v hw'R).elim
    · subst he
      exact hk.symm.trans hk'
    · exact (pred_aux hH hs hl hk' hk hw'v hwv hwR).elim
  by_cases hvs : v = s
  · have hr0 : nreach G X F F' s v :=
      ⟨0, hvs.symm, fun j hj => by rw [Nat.le_zero.mp hj, ← hvs]; exact hvX⟩
    have h1 : nrI G X F F' s v = 1 := by
      unfold nrI
      rw [if_pos hr0]
    rw [h1, if_pos hvs, Finset.sum_eq_zero, add_zero]
    intro w hw
    unfold nrI
    rw [if_neg]
    rintro ⟨k, hk, -⟩
    obtain ⟨-, -, hwR, hwv⟩ := Finset.mem_filter.mp hw
    have hcyc : (nxt G F F')^[k + 1] s = s := by
      rw [Function.iterate_succ_apply', hk, hwv, hvs]
    have hR := hedge_cycle hH hs hcyc
    apply hwR
    rw [← hk, iter_root G F F' s hR k]
    exact hR
  · rw [if_neg hvs, zero_add]
    by_cases hr : nreach G X F F' s v
    · obtain ⟨k, hk, hkX⟩ := hr
      have hr' : nreach G X F F' s v := ⟨k, hk, hkX⟩
      have hex : ∃ k, (nxt G F F')^[k] s = v := ⟨k, hk⟩
      have hk0 := Nat.find_spec hex
      have hle : Nat.find hex ≤ k := Nat.find_min' hex hk
      have hne0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0] at hk0
        exact hvs hk0.symm
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjv : (nxt G F F')^[j + 1] s = v := by
        rw [← hj]
        exact hk0
      have hwv : nxt G F F' ((nxt G F F')^[j] s) = v := by
        have h' := hjv
        rw [Function.iterate_succ_apply'] at h'
        exact h'
      have hwR : (nxt G F F')^[j] s ∉ rootsIn G F := by
        intro hR
        rw [nxt_root G F F' _ hR] at hwv
        exact Nat.find_min hex (show j < Nat.find hex by omega) hwv
      have hwmem : (nxt G F F')^[j] s ∈
          F'.filter (fun w => w ∉ U ∧ w ∉ rootsIn G F ∧ nxt G F F' w = v) :=
        Finset.mem_filter.mpr ⟨hedge_iter_mem hH hs j, iter_obs hH hroot hs hsU j, hwR, hwv⟩
      have hwr : nreach G X F F' s ((nxt G F F')^[j] s) :=
        ⟨j, rfl, fun i hi => hkX i (by omega)⟩
      unfold nrI
      rw [if_pos hr', Finset.sum_eq_single ((nxt G F F')^[j] s)]
      · rw [if_pos hwr]
      · intro b hb hbw
        rw [if_neg]
        intro hbr
        exact hbw (huniq b hb _ hwmem hbr hwr)
      · intro hn
        exact absurd hwmem hn
    · unfold nrI
      rw [if_neg hr, Finset.sum_eq_zero]
      intro w hw
      rw [if_neg]
      rintro ⟨k, hk, hkX⟩
      obtain ⟨-, -, -, hwv⟩ := Finset.mem_filter.mp hw
      apply hr
      refine ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hwv], fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact hkX j (by omega)
      · rw [show j = k + 1 by omega, Function.iterate_succ_apply', hk, hwv]
        exact hvX

/-- Høyst én rot nås. -/
lemma nreach_root_unique {s r r' : V} (hr : r ∈ rootsIn G F) (hr' : r' ∈ rootsIn G F)
    (h : nreach G X F F' s r) (h' : nreach G X F F' s r') : r = r' := by
  obtain ⟨k, hk, -⟩ := h
  obtain ⟨k', hk', -⟩ := h'
  rcases le_total k k' with hl | hl
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, Function.iterate_add_apply, hk, iter_root G F F' r hr m] at hk'
    exact hk'
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, Function.iterate_add_apply, hk', iter_root G F F' r' hr' m] at hk
    exact hk.symm

open Classical in
/-- **Summen over røttene** er 1 nøyaktig når stien når en rot. -/
lemma sum_nrI_roots (s : V) :
    ∑ r ∈ rootsIn G F, nrI G X F F' s r =
      if ∃ r ∈ rootsIn G F, nreach G X F F' s r then 1 else 0 := by
  by_cases h : ∃ r ∈ rootsIn G F, nreach G X F F' s r
  · rw [if_pos h]
    obtain ⟨r, hr, hrr⟩ := h
    rw [Finset.sum_eq_single r]
    · unfold nrI
      rw [if_pos hrr]
    · intro b hb hbr
      unfold nrI
      rw [if_neg]
      intro hb'
      exact hbr (nreach_root_unique hb hr hb' hrr)
    · intro hn
      exact absurd hr hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro r hr
    unfold nrI
    rw [if_neg]
    intro hrr
    exact h ⟨r, hr, hrr⟩

end nreach

end Hedge

#print axioms Hedge.nrI_rec
#print axioms Hedge.sum_nrI_roots

/-! ## Runde 70: avbildningen ψ

`flipO Φ t`: legg `Φ w` til verdien til hver observert `w`. `phiC c w` = `nrI c w + nrI (par c) w`.
`psiS c s`: snu biten på trekanten `(c, par c)` (`sh` med `E = {c}`) og deretter verdiene der
`phiC c = 1`; ψ avhenger ikke av `s` og er en involusjon (`psiS_invol`). `ov_psi`, `lb_psi`:
virkningen på verdier og trebiter. `sbV_psi`: `M1`-biten til `v ∈ F'` endres med
`[v = c] + [v = par c] + Σ_{NX v} phiC`. `phiC_rec`: for `v ∈ F' \ X` er det nøyaktig
`phiC c v` (fra `nrI_rec`), så hver ligning utenfor `X` holder for `ψ s` når den holder for `s`.
`nrI_X`: ingen node i `X` nås. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_cc : ∀ a b c : ZMod 2, a + b + c + b + c = a := by decide

section psi

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- Legg `Φ` til verdiene til de observerte nodene. -/
def flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u i => t u i + (if u.1 ∈ U then 0 else Φ u.1)

lemma flipO_obs (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V}
    (hw : w ∉ U) :
    flipO U Φ t ⟨w, Finset.mem_univ w⟩ = fun i => t ⟨w, Finset.mem_univ w⟩ i + Φ w := by
  funext i
  show t ⟨w, Finset.mem_univ w⟩ i + (if w ∈ U then 0 else Φ w) = _
  rw [if_neg hw]

lemma flipO_lat (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {u : V}
    (hu : u ∈ U) : flipO U Φ t ⟨u, Finset.mem_univ u⟩ = t ⟨u, Finset.mem_univ u⟩ := by
  funext i
  show t ⟨u, Finset.mem_univ u⟩ i + (if u ∈ U then 0 else Φ u) = _
  rw [if_pos hu, add_zero]

lemma ov_flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {w : V}
    (hw : w ∉ U) : ov U (flipO U Φ t) w = ov U t w + Φ w := by
  have h0 : 0 < kk U w := by
    rw [kk_obs hw]
    omega
  unfold ov
  rw [flipO_obs U Φ t hw]
  unfold rd
  rw [dif_pos h0, dif_pos h0]

lemma lb_flipO (Φ : V → ZMod 2) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {c : V}
    (hl : D.lat c ∈ U) : lb U D (flipO U Φ t) c = lb U D t c := by
  unfold lb
  rw [flipO_lat U Φ t hl]

/-- Hvilke observerte verdier ψ snur. -/
noncomputable def phiC (c w : V) : ZMod 2 := nrI G X F F' c w + nrI G X F F' (D.par c) w

/-- **ψ**: snu biten på `(c, par c)` og verdiene der `phiC c = 1`. -/
noncomputable def psiS (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  flipO U (phiC G F F' D X c) (sh U {c} D (fun _ => 1) s)

theorem psiS_invol (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    psiS G U F F' D X c (psiS G U F F' D X c s) = s := by
  funext u i
  simp only [psiS, flipO, sh]
  exact zmod2_cc _ _ _

lemma lb_psi (c : V) (s : Assignment (α := Val U) (Finset.univ : Finset V)) {c' : V}
    (hl : D.lat c' ∈ U) (hc'U : c' ∉ U) (hc'ρ : c' ≠ D.ρ) :
    lb U D (psiS G U F F' D X c s) c' = lb U D s c' + (if c' = c then 1 else 0) := by
  unfold psiS
  rw [lb_flipO U D _ _ hl, lb_shE U D {c} _ s hl]
  by_cases h : c' = c
  · rw [if_pos (show c' ∈ EF U {c} D from
      Finset.mem_filter.mpr ⟨Finset.mem_singleton.mpr h, hc'U, hc'ρ⟩), if_pos h]
  · rw [if_neg (show c' ∉ EF U {c} D from
      fun hm => h (Finset.mem_singleton.mp (Finset.mem_filter.mp hm).1)), if_neg h]

lemma ov_psi (c : V) (hcl : D.lat c ∈ U) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    {w : V} (hw : w ∉ U) :
    ov U (psiS G U F F' D X c s) w = ov U s w + phiC G F F' D X c w := by
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  unfold psiS
  rw [ov_flipO U _ _ hw]
  unfold ov
  rw [obs_shE U D {c} hE _ s hw]

/-- **`M1`-biten under ψ.** -/
theorem sbV_psi (hD : Good G U F F' D) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D false (psiS G U F F' D X c s) v = sbV G U F F' D false s v +
      ((if v = c then 1 else 0) + (if v = D.par c then 1 else 0) +
        ∑ w ∈ NX G U F F' v, phiC G F F' D X c w) := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hown : (if v = D.ρ then 0 else lb U D (psiS G U F F' D X c s) v) =
      (if v = D.ρ then 0 else lb U D s v) + (if v = c then 1 else 0) := by
    by_cases hρ : v = D.ρ
    · rw [if_pos hρ, if_pos hρ, if_neg (fun h => hcρ (h.symm.trans hρ)), add_zero]
    · rw [if_neg hρ, if_neg hρ, lb_psi G U F F' D X c s (hD.lat v hvF' hvU hρ).1 hvU hρ]
  have hch : ∑ c' ∈ CH U F' D v, lb U D (psiS G U F F' D X c s) c' =
      ∑ c' ∈ CH U F' D v, lb U D s c' + (if v = D.par c then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun c' hc' => by
      obtain ⟨hF, hU, hρ', -⟩ := Finset.mem_filter.mp hc'
      exact lb_psi G U F F' D X c s (hD.lat c' hF hU hρ').1 hU hρ'),
      Finset.sum_add_distrib]
    first
      | rw [Finset.sum_ite_eq']
      | rw [Finset.sum_ite_eq]
    congr 1
    by_cases hp : v = D.par c
    · rw [if_pos hp, if_pos (show c ∈ CH U F' D v from
        Finset.mem_filter.mpr ⟨hc, hcU, hcρ, hp.symm⟩)]
    · rw [if_neg hp, if_neg (fun hm => hp (Finset.mem_filter.mp hm).2.2.2.symm)]
  have hnx : ∑ w ∈ NX G U F F' v, ov U (psiS G U F F' D X c s) w =
      ∑ w ∈ NX G U F F' v, ov U s w + ∑ w ∈ NX G U F F' v, phiC G F F' D X c w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨-, hwU, -, -⟩ := Finset.mem_filter.mp hw
    exact ov_psi G U F F' D X c hcl s hwU
  unfold sbV
  first
    | rw [scope_false, filter_univ, filter_univ, hown, hch, hnx]
    | (simp only [scope_false, Finset.mem_univ, Finset.filter_True]
       rw [hown, hch, hnx])
  ring

/-- **Rekursjonen for `phiC`** utenfor `X`. -/
theorem phiC_rec {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    {v : V} (hvF' : v ∈ F') (hvX : v ∉ X) :
    phiC G F F' D X c v = (if v = c then 1 else 0) + (if v = D.par c then 1 else 0) +
      ∑ w ∈ NX G U F F' v, phiC G F F' D X c w := by
  obtain ⟨hpc, hpcU⟩ := hD.parF' c hc hcU hcρ
  unfold phiC
  rw [nrI_rec hH hroot hc hcU hvF' hvX, nrI_rec hH hroot hpc hpcU hvF' hvX]
  unfold NX
  rw [Finset.sum_add_distrib]
  ring

lemma nrI_X {s v : V} (hv : v ∈ X) : nrI G X F F' s v = 0 := by
  unfold nrI
  rw [if_neg]
  rintro ⟨k, hk, hkX⟩
  apply hkX k le_rfl
  rw [hk]
  exact hv

end psi

end PM
end Hedge

#print axioms Hedge.PM.psiS_invol
#print axioms Hedge.PM.sbV_psi
#print axioms Hedge.PM.phiC_rec

/-! ## Runde 71: ψ under `do(x)` i `M1`: like sannsynligheter for odde og jevn paritet

`map_flip_eq`: en involusjon som bevarer vektene og snur `f` gir `P(f = 1) = P(f = 0)`.
`kfac_psi_do`: hver faktor i `doModel M1 X x` er den samme i `ψ s` og `s` (i `X` er verdien
uendret, `nrI_X`; utenfor `X` endres både verdien og `M1`-biten med `phiC c v`, `phiC_rec`).
`joint_psi`: fellesfordelingen er invariant. `parR`: pariteten til de observerte røttene.
`parR_psi`: når nøyaktig én av `c`, `par c` når en rot uten å treffe `X`, snur ψ `parR`.
`parR_half`: da er `P(parR = 1) = P(parR = 0)` under `do(x)` i `M1`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_shift1 : ∀ a : ZMod 2, (1 = a + 1 ↔ 0 = a) := by decide

/-- **Halv-halv** via en vektbevarende involusjon som snur `f`. -/
theorem map_flip_eq {β : Type*} (p : PMF β) (ψ : β → β) (f : β → ZMod 2)
    (hinv : ∀ s, ψ (ψ s) = s) (hp : ∀ s, p (ψ s) = p s) (hf : ∀ s, f (ψ s) = f s + 1) :
    (p.map f) 1 = (p.map f) 0 := by
  have hmap : p.map ψ = p := by
    ext s
    rw [PMF.map_apply, tsum_eq_single (ψ s)]
    · rw [if_pos (hinv s).symm, hp]
    · intro s' hs'
      rw [if_neg]
      intro h
      apply hs'
      rw [h, hinv]
  have hcomp : f ∘ ψ = fun s => f s + 1 := funext hf
  calc (p.map f) 1 = ((p.map ψ).map f) 1 := by rw [hmap]
    _ = (p.map (fun s => f s + 1)) 1 := by rw [PMF.map_comp, hcomp]
    _ = (p.map f) 0 := by
      rw [PMF.map_apply, PMF.map_apply]
      apply tsum_congr
      intro s
      by_cases h0 : 0 = f s
      · rw [if_pos ((zmod2_shift1 (f s)).mpr h0), if_pos h0]
      · rw [if_neg (fun h => h0 ((zmod2_shift1 (f s)).mp h)), if_neg h0]

namespace PM

lemma zmod2_pp : ∀ a b p : ZMod 2, a + p + (b + p) = a + b := by decide

section psido

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- **Hver faktor i `do(x)` bevares av ψ.** -/
theorem kfac_psi_do {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (M G U F F' D false) X x) Finset.univ (psiS G U F F' D X c s) v =
      kfac (doModel (M G U F F' D false) X x) Finset.univ s v := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  rw [kfac_doModel, kfac_doModel]
  by_cases hv : v ∈ X
  · rw [dif_pos hv, dif_pos hv]
    have h0 : phiC G F F' D X c v = 0 := by
      unfold phiC
      rw [nrI_X G F F' X hv, nrI_X G F F' X hv, add_zero]
    have hpv : psiS G U F F' D X c s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
      unfold psiS
      rw [flipO_obs U _ _ (hXU v hv), obs_shE U D {c} hE _ s (hXU v hv), h0]
      funext i
      exact add_zero _
    rw [hpv]
  · rw [dif_neg hv, dif_neg hv]
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D false _ hvU, kfac_lat G U F F' D false _ hvU]
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D false _ hvU hvF', kfac_out G U F F' D false _ hvU hvF']
    have hrd : rd (psiS G U F F' D X c s ⟨v, Finset.mem_univ v⟩) 0 =
        rd (s ⟨v, Finset.mem_univ v⟩) 0 + phiC G F F' D X c v :=
      ov_psi G U F F' D X c hcl s hvU
    have hsb : sb G U F F' D false v (rdS G U (psiS G U F F' D X c s) v) =
        sb G U F F' D false v (rdS G U s v) + phiC G F F' D X c v := by
      rw [sb_read G U F F' D false hH hD _ hvF' hvU, sb_read G U F F' D false hH hD _ hvF' hvU,
        sbV_psi G U F F' D X hD hc hcU hcρ s hvF' hvU,
        ← phiC_rec G U F F' D X hH hD hroot hc hcU hcρ hvF' hv]
    by_cases hr : v = D.r0
    · rw [kfac_r0 G U F F' D false _ hvU hvF' hr, kfac_r0 G U F F' D false _ hvU hvF' hr, hrd, hsb,
        zmod2_pp]
    · rw [kfac_obs G U F F' D false _ hvU hvF' hr, kfac_obs G U F F' D false _ hvU hvF' hr, hrd,
        hsb]
      simp only [add_left_inj]

/-- **Fellesfordelingen under `do(x)` er invariant under ψ.** -/
theorem joint_psi {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    (doModel (M G U F F' D false) X x).fullJoint (psiS G U F F' D X c s) =
      (doModel (M G U F F' D false) X x).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  exact Finset.prod_congr rfl
    (fun v _ => kfac_psi_do G U F F' D X hH hD hroot hXU hc hcU hcρ x s v)

/-- Pariteten til de observerte røttene. -/
noncomputable def parR (s : Assignment (α := Val U) (Finset.univ : Finset V)) : ZMod 2 :=
  ∑ r ∈ (rootsIn G F).filter (fun r => r ∉ U), ov U s r

lemma nrI_lat {Y : Finset V} (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {s r : V} (hs : s ∈ F') (hsU : s ∉ U) (hr : r ∈ U) : nrI G X F F' s r = 0 := by
  unfold nrI
  rw [if_neg]
  rintro ⟨k, hk, -⟩
  apply iter_obs hH hroot hs hsU k
  rw [hk]
  exact hr

/-- **ψ snur pariteten** når nøyaktig én av `c`, `par c` når en rot utenom `X`. -/
theorem parR_psi {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    parR G U F (psiS G U F F' D X c s) = parR G U F s + 1 := by
  have hcl := (hD.lat c hc hcU hcρ).1
  obtain ⟨hpc, hpcU⟩ := hD.parF' c hc hcU hcρ
  unfold parR
  rw [Finset.sum_congr rfl (fun r hr => ov_psi G U F F' D X c hcl s (Finset.mem_filter.mp hr).2),
    Finset.sum_add_distrib]
  congr 1
  have hz : ∀ r ∈ rootsIn G F, phiC G F F' D X c r ≠ 0 → r ∉ U := by
    intro r _ h hrU
    apply h
    unfold phiC
    rw [nrI_lat G U F F' X hH hroot hc hcU hrU, nrI_lat G U F F' X hH hroot hpc hpcU hrU, add_zero]
  rw [Finset.sum_filter_of_ne hz]
  unfold phiC
  rw [Finset.sum_add_distrib, sum_nrI_roots, sum_nrI_roots]
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

/-- **`P(parR = 1) = P(parR = 0)` under `do(x)` i `M1`.** -/
theorem parR_half {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (x : Assignment (α := Val U) X) :
    ((doModel (M G U F F' D false) X x).fullJoint.map (parR G U F)) 1 =
      ((doModel (M G U F F' D false) X x).fullJoint.map (parR G U F)) 0 :=
  map_flip_eq _ (psiS G U F F' D X c) (parR G U F) (psiS_invol G U F F' D X c)
    (joint_psi G U F F' D X hH hD hroot hXU hc hcU hcρ x)
    (parR_psi G U F F' D X hH hD hroot hc hcU hcρ hA)

end psido

end PM
end Hedge

#print axioms Hedge.map_flip_eq
#print axioms Hedge.PM.joint_psi
#print axioms Hedge.PM.parR_half

/-! ## Runde 72: den kryssende trekanten og et forholdslemma

`ParTree.iff_root`: har hver trekant `(c, par c)` samme sannhetsverdi for `P` i begge ender,
har hele treet sannhetsverdien til roten. `cross_edge`: i `F'`-treet finnes en trekant der
nøyaktig én ende når en rot uten å treffe `X` (røttene gjør det, en `x ∈ X ∩ F'` gjør det
ikke). `map_ratio`: en involusjon `τ` som snur `f` og ganger vekten med `k` når `f = 1`, gir
`P(f = 0) = k · P(f = 1)`; det brukes for `M2` med `k = noise 0 / noise 1`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Samme sannhetsverdi langs hver trekant ⇒ samme som roten. -/
theorem ParTree.iff_root {S : Finset V} {ρ : V} {par : V → V} {d : V → ℕ}
    (T : ParTree S ρ par d) (P : V → Prop) (h : ∀ c ∈ S, c ≠ ρ → (P c ↔ P (par c))) :
    ∀ v ∈ S, (P v ↔ P ρ) := by
  have key : ∀ n, ∀ v ∈ S, d v = n → (P v ↔ P ρ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hdn
      by_cases hvρ : v = ρ
      · rw [hvρ]
      · obtain ⟨hp, hlt⟩ := T.step v hv hvρ
        exact (h v hv hvρ).trans (ih (d (par v)) (by omega) (par v) hp rfl)
  exact fun v hv => key (d v) v hv rfl

lemma zmod2_s0 : ∀ a : ZMod 2, (0 = a + 1 ↔ 1 = a) := by decide

/-- **Forholdslemmaet.** -/
theorem map_ratio {β : Type*} (p : PMF β) (τ : β → β) (f : β → ZMod 2) (k : ENNReal)
    (hinv : ∀ s, τ (τ s) = s) (hf : ∀ s, f (τ s) = f s + 1)
    (hp : ∀ s, f s = 1 → p (τ s) = k * p s) :
    (p.map f) 0 = k * (p.map f) 1 := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm τ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  first
    | simp only [Function.Involutive.coe_toPerm, hf]
    | simp only [hf]
  by_cases h1 : 1 = f s
  · rw [if_pos ((zmod2_s0 (f s)).mpr h1), if_pos h1, hp s h1.symm]
  · rw [if_neg (fun h => h1 ((zmod2_s0 (f s)).mp h)), if_neg h1, mul_zero]

namespace PM

section cross

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X : Finset V)

/-- **Den kryssende trekanten.** -/
theorem cross_edge {Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hXU : ∀ v ∈ X, v ∉ U) {d : V → ℕ} (T : ParTree (OF U F') D.ρ D.par d) :
    ∃ c, c ∈ F' ∧ c ∉ U ∧ c ≠ D.ρ ∧
      (((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
          ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
        ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
          ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r)) := by
  by_contra hno
  have hiff := T.iff_root (fun v => ∃ r ∈ rootsIn G F, nreach G X F F' v r) (fun c hc hcρ => by
    have hcF' := (Finset.mem_filter.mp hc).1
    have hcU := (Finset.mem_filter.mp hc).2
    by_cases h1 : ∃ r ∈ rootsIn G F, nreach G X F F' c r <;>
      by_cases h2 : ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact (hno ⟨c, hcF', hcU, hcρ, Or.inl ⟨h1, h2⟩⟩).elim
    · exact (hno ⟨c, hcF', hcU, hcρ, Or.inr ⟨h1, h2⟩⟩).elim
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩)
  have hr0F := (Finset.mem_filter.mp hD.r0R).1
  have hr0 : D.r0 ∈ OF U F' := Finset.mem_filter.mpr ⟨hH.sub hr0F, hD.r0U⟩
  have hP0 : ∃ r ∈ rootsIn G F, nreach G X F F' D.r0 r :=
    ⟨D.r0, hD.r0R, 0, rfl, fun j hj => by
      rw [Nat.le_zero.mp hj]
      exact hH.out _ hr0F⟩
  obtain ⟨x0, hx0X, hx0F'⟩ := hH.meet
  have hx0 : x0 ∈ OF U F' := Finset.mem_filter.mpr ⟨hx0F', hXU x0 hx0X⟩
  have hnP : ¬ ∃ r ∈ rootsIn G F, nreach G X F F' x0 r := by
    rintro ⟨r, -, k, -, hk⟩
    exact hk 0 (Nat.zero_le _) hx0X
  exact hnP ((hiff x0 hx0).mpr ((hiff D.r0 hr0).mp hP0))

end cross

end PM
end Hedge

#print axioms Hedge.ParTree.iff_root
#print axioms Hedge.map_ratio
#print axioms Hedge.PM.cross_edge

/-! ## Runde 73: `M2` under `do(x)`: pariteten er støyleddet

`noise_eq`, `noise_card`, `noise_ratio`: `noise 0 = 3 · noise 1`. `sum_sbV2`: summen av
`M2`-bitene over `OF` er summen av verdiene til ikke-røttene i `OF` (hver trebit i `F` telles to
ganger, hver `nxt`-verdi i `F` én gang). `parR_g`: for en tilordning med positiv sannsynlighet
under `do(x)` i `M2` holder ligningene i `OF` utenom `r0` (`F ∩ X = ∅`), så `parR s` er
`ov r0 + sbV true r0`, støyleddet i `r0`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma noise_eq (n : ZMod 2) :
    noise n = ∑ i : Fin 4,
      if n = (if i = 0 then (1 : ZMod 2) else 0) then (Fintype.card (Fin 4) : ENNReal)⁻¹ else 0 := by
  unfold noise
  rw [PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [PMF.uniformOfFintype_apply]
  by_cases h : n = if i = 0 then (1 : ZMod 2) else 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

lemma noise_card (n : ZMod 2) :
    noise n = ((Finset.univ.filter
      (fun i : Fin 4 => n = if i = 0 then (1 : ZMod 2) else 0)).card : ENNReal) *
        (Fintype.card (Fin 4) : ENNReal)⁻¹ := by
  rw [noise_eq, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- **`noise 0 = 3 · noise 1`.** -/
lemma noise_ratio : noise 0 = 3 * noise 1 := by
  rw [noise_card, noise_card]
  have h0 : (Finset.univ.filter
      (fun i : Fin 4 => (0 : ZMod 2) = if i = 0 then (1 : ZMod 2) else 0)).card = 3 := by decide
  have h1 : (Finset.univ.filter
      (fun i : Fin 4 => (1 : ZMod 2) = if i = 0 then (1 : ZMod 2) else 0)).card = 1 := by decide
  rw [h0, h1]
  push_cast
  ring

lemma zmod2_g : ∀ a b c : ZMod 2, a + c = b + c + (a + b) := by decide

section m2

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- **Summen av `M2`-bitene over `OF`.** -/
theorem sum_sbV2 {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    ∑ v ∈ OF U F, sbV G U F F' D true s v =
      ∑ w ∈ (OF U F).filter (fun w => w ∉ rootsIn G F), ov U s w := by
  have hS : ∀ v ∈ OF U F, (CH U F' D v).filter (fun c => c ∈ F) =
      ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c = v) := by
    intro v _
    ext c
    simp only [CH, OF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hU, hρ, hp⟩, hF⟩
      exact ⟨⟨⟨hF, hU⟩, hρ⟩, hp⟩
    · rintro ⟨⟨⟨hF, hU⟩, hρ⟩, hp⟩
      exact ⟨⟨hH.sub hF, hU, hρ, hp⟩, hF⟩
  have hN : ∀ v ∈ OF U F, (NX G U F F' v).filter (fun w => w ∈ F) =
      ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter (fun w => nxt G F F' w = v) := by
    intro v _
    ext w
    simp only [NX, OF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hU, hR, hn⟩, hF⟩
      exact ⟨⟨⟨hF, hU⟩, hR⟩, hn⟩
    · rintro ⟨⟨⟨hF, hU⟩, hR⟩, hn⟩
      exact ⟨⟨hH.sub hF, hU, hR, hn⟩, hF⟩
  have hsplit : ∀ v ∈ OF U F, sbV G U F F' D true s v =
      (if v = D.ρ then 0 else lb U D s v) +
        ∑ c ∈ ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c = v), lb U D s c +
        ∑ w ∈ ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter (fun w => nxt G F F' w = v),
          ov U s w := by
    intro v hv
    unfold sbV
    rw [scope_true_in F (Finset.mem_filter.mp hv).1, hS v hv, hN v hv]
  have hS2 : ((OF U F).filter (fun c => c ≠ D.ρ)).filter (fun c => D.par c ∈ OF U F) =
      (OF U F).filter (fun c => c ≠ D.ρ) := by
    apply Finset.filter_true_of_mem
    intro c hc
    obtain ⟨hc1, hcρ⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcF, hcU⟩ := Finset.mem_filter.mp hc1
    exact Finset.mem_filter.mpr ⟨hD.parF c hcF hcU hcρ, (hD.parF' c (hH.sub hcF) hcU hcρ).2⟩
  have hN2 : ((OF U F).filter (fun w => w ∉ rootsIn G F)).filter
      (fun w => nxt G F F' w ∈ OF U F) = (OF U F).filter (fun w => w ∉ rootsIn G F) := by
    apply Finset.filter_true_of_mem
    intro w hw
    obtain ⟨hw1, hwR⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwF, -⟩ := Finset.mem_filter.mp hw1
    have h := hedge_nxt hH w (hH.sub hwF) hwR
    exact Finset.mem_filter.mpr ⟨h.1 hwF, fun hU => hroot _ hU _ h.2.2⟩
  have hown : ∑ v ∈ OF U F, (if v = D.ρ then 0 else lb U D s v) =
      ∑ c ∈ (OF U F).filter (fun c => c ≠ D.ρ), lb U D s c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v = D.ρ
    · rw [if_pos h, if_neg (not_not.mpr h)]
    · rw [if_neg h, if_pos (show v ≠ D.ρ from h)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    fiber_sum (OF U F) _ D.par (lb U D s), fiber_sum (OF U F) _ (nxt G F F') (ov U s),
    hS2, hN2, hown, zmod2_add_self, zero_add]

/-- **I `M2` under `do(x)` er pariteten støyleddet i `r0`** (på støtten). -/
theorem parR_g {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (x : Assignment (α := Val U) X)
    (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hs : (doModel (M G U F F' D true) X x).fullJoint s ≠ 0) :
    parR G U F s = ov U s D.r0 + sbV G U F F' D true s D.r0 := by
  rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff] at hs
  have hEq : ∀ v ∈ OF U F, v ≠ D.r0 → ov U s v = sbV G U F F' D true s v := by
    intro v hv hr
    obtain ⟨hvF, hvU⟩ := Finset.mem_filter.mp hv
    have h := hs v (Finset.mem_univ v)
    rw [kfac_doModel, dif_neg (hH.out v hvF), kfac_obs G U F F' D true _ hvU (hH.sub hvF) hr] at h
    rw [← sb_read G U F F' D true hH hD s (hH.sub hvF) hvU]
    by_contra hne
    exact h (if_neg hne)
  have hr0 : D.r0 ∈ OF U F := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hD.r0R).1, hD.r0U⟩
  have hsum : ∑ v ∈ OF U F, ov U s v = ∑ v ∈ OF U F, sbV G U F F' D true s v +
      (ov U s D.r0 + sbV G U F F' D true s D.r0) := by
    rw [← Finset.add_sum_erase (OF U F) (ov U s) hr0,
      ← Finset.add_sum_erase (OF U F) (sbV G U F F' D true s) hr0,
      Finset.sum_congr rfl (fun v hv => hEq v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv))]
    exact zmod2_g _ _ _
  rw [sum_sbV2 G U F F' D hH hD hroot s,
    ← Finset.sum_filter_add_sum_filter_not (OF U F) (fun w => w ∉ rootsIn G F) (ov U s)] at hsum
  have hR := add_left_cancel hsum
  unfold parR
  rw [← hR]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext r
  simp only [OF, Finset.mem_filter, not_not]
  constructor
  · rintro ⟨hr, hrU⟩
    exact ⟨⟨(Finset.mem_filter.mp hr).1, hrU⟩, hr⟩
  · rintro ⟨⟨-, hrU⟩, hr⟩
    exact ⟨hr, hrU⟩

end m2

end PM
end Hedge

#print axioms Hedge.PM.noise_ratio
#print axioms Hedge.PM.sum_sbV2
#print axioms Hedge.PM.parR_g

/-! ## Runde 74: `M2` under `do(x)`: `P(parR = 0) = 3 · P(parR = 1)`

`map_congr_supp`: like funksjoner på støtten gir lik bildefordeling. `tauS`: snu verdien i
`r0`. Ingen leser `r0` (røtter er ikke `nxt`-barn), så `sbV` er uendret (`sbV_tau`) og bare
faktoren i `r0` endres: når støyleddet `gS s = ov r0 + sbV true r0` er 1, går den fra
`noise 1` til `noise 0 = 3 · noise 1` (`joint_tau`). `parR_three`: med `parR_g` og
`map_ratio` er `P(parR = 0) = 3 · P(parR = 1)` under `do(x)` i `M2`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Like funksjoner på støtten gir lik bildefordeling. -/
theorem map_congr_supp {β : Type*} (p : PMF β) (f g : β → ZMod 2)
    (h : ∀ s, p s ≠ 0 → f s = g s) : p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro s
  by_cases hs : p s = 0
  · rw [hs, ite_self, ite_self]
  · rw [h s hs]

namespace PM

lemma zmod2_one : ∀ a b : ZMod 2, a + b = 1 → a + 1 + b = 0 := by decide

section tau

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- Indikatoren for `r`. -/
def ind0 (r w : V) : ZMod 2 := if w = r then 1 else 0

/-- Snu verdien i `r0`. -/
def tauS (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  flipO U (ind0 D.r0) s

/-- Støyleddet i `r0` i `M2`. -/
noncomputable def gS (s : Assignment (α := Val U) (Finset.univ : Finset V)) : ZMod 2 :=
  ov U s D.r0 + sbV G U F F' D true s D.r0

lemma tauS_invol (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    tauS U D (tauS U D s) = s := by
  funext u i
  simp only [tauS, flipO]
  rw [add_assoc, zmod2_add_self, add_zero]

lemma tau_ne (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ≠ D.r0) :
    tauS U D s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
  funext i
  show s ⟨v, Finset.mem_univ v⟩ i + (if v ∈ U then 0 else ind0 D.r0 v) = _
  unfold ind0
  rw [if_neg hv, ite_self, add_zero]

lemma ov_tau (hr0U : D.r0 ∉ U) (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    ov U (tauS U D s) D.r0 = ov U s D.r0 + 1 := by
  unfold tauS
  rw [ov_flipO U _ _ hr0U]
  unfold ind0
  rw [if_pos rfl]

/-- **`sbV` leser ikke `r0`.** -/
lemma sbV_tau (hD : Good G U F F' D) (two : Bool)
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hvF' : v ∈ F') (hvU : v ∉ U) :
    sbV G U F F' D two (tauS U D s) v = sbV G U F F' D two s v := by
  unfold sbV
  congr 1
  · congr 1
    · by_cases hρ : v = D.ρ
      · rw [if_pos hρ, if_pos hρ]
      · rw [if_neg hρ, if_neg hρ]
        unfold tauS
        rw [lb_flipO U D _ _ (hD.lat v hvF' hvU hρ).1]
    · apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨hcF', hcU, hcρ, -⟩ := Finset.mem_filter.mp hc1
      unfold tauS
      exact lb_flipO U D _ _ (hD.lat c hcF' hcU hcρ).1
  · apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hw1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hwU, hwR, -⟩ := Finset.mem_filter.mp hw1
    have hwr : w ≠ D.r0 := fun h => hwR (by rw [h]; exact hD.r0R)
    unfold tauS
    rw [ov_flipO U _ _ hwU]
    unfold ind0
    rw [if_neg hwr, add_zero]

lemma gS_tau (hD : Good G U F F' D) (hr0F' : D.r0 ∈ F')
    (s : Assignment (α := Val U) (Finset.univ : Finset V)) :
    gS G U F F' D (tauS U D s) = gS G U F F' D s + 1 := by
  unfold gS
  rw [ov_tau U D hD.r0U s, sbV_tau G U F F' D hD true s hr0F' hD.r0U]
  ring

/-- Utenom `r0` er faktorene like. -/
lemma kfac_tau {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (x : Assignment (α := Val U) X) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    {v : V} (hv : v ≠ D.r0) :
    kfac (doModel (M G U F F' D true) X x) Finset.univ (tauS U D s) v =
      kfac (doModel (M G U F F' D true) X x) Finset.univ s v := by
  rw [kfac_doModel, kfac_doModel]
  by_cases hvX : v ∈ X
  · rw [dif_pos hvX, dif_pos hvX, tau_ne U D s hv]
  · rw [dif_neg hvX, dif_neg hvX]
    by_cases hvU : v ∈ U
    · rw [kfac_lat G U F F' D true _ hvU, kfac_lat G U F F' D true _ hvU]
    by_cases hvF' : v ∈ F'
    swap
    · rw [kfac_out G U F F' D true _ hvU hvF', kfac_out G U F F' D true _ hvU hvF']
    rw [kfac_obs G U F F' D true _ hvU hvF' hv, kfac_obs G U F F' D true _ hvU hvF' hv,
      tau_ne U D s hv, sb_read G U F F' D true hH hD _ hvF' hvU,
      sb_read G U F F' D true hH hD _ hvF' hvU, sbV_tau G U F F' D hD true s hvF' hvU]

/-- **Vekten tredobles** når støyleddet er 1. -/
theorem joint_tau {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (x : Assignment (α := Val U) X) (s : Assignment (α := Val U) (Finset.univ : Finset V))
    (hg : gS G U F F' D s = 1) :
    (doModel (M G U F F' D true) X x).fullJoint (tauS U D s) =
      3 * (doModel (M G U F F' D true) X x).fullJoint s := by
  have hr0F := (Finset.mem_filter.mp hD.r0R).1
  have hr0F' := hH.sub hr0F
  have hr0X := hH.out _ hr0F
  rw [fullJoint_apply_prod, fullJoint_apply_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ D.r0),
    Finset.prod_congr rfl (fun v hv => kfac_tau G U F F' D hH hD x s (Finset.ne_of_mem_erase hv))]
  have h1 : kfac (doModel (M G U F F' D true) X x) Finset.univ (tauS U D s) D.r0 = noise 0 := by
    rw [kfac_doModel, dif_neg hr0X, kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl,
      sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    show ov U (tauS U D s) D.r0 + sbV G U F F' D true (tauS U D s) D.r0 = 0
    rw [ov_tau U D hD.r0U s, sbV_tau G U F F' D hD true s hr0F' hD.r0U]
    exact zmod2_one _ _ hg
  have h2 : kfac (doModel (M G U F F' D true) X x) Finset.univ s D.r0 = noise 1 := by
    rw [kfac_doModel, dif_neg hr0X, kfac_r0 G U F F' D true _ hD.r0U hr0F' rfl,
      sb_read G U F F' D true hH hD _ hr0F' hD.r0U]
    congr 1
    try exact hg
  rw [h1, h2, noise_ratio, mul_assoc]

/-- **`P(parR = 0) = 3 · P(parR = 1)` under `do(x)` i `M2`.** -/
theorem parR_three {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (x : Assignment (α := Val U) X) :
    ((doModel (M G U F F' D true) X x).fullJoint.map (parR G U F)) 0 =
      3 * ((doModel (M G U F F' D true) X x).fullJoint.map (parR G U F)) 1 := by
  have hr0F' := hH.sub (Finset.mem_filter.mp hD.r0R).1
  rw [map_congr_supp _ (parR G U F) (gS G U F F' D)
    (fun s hs => parR_g G U F F' D hH hD hroot x s hs)]
  exact map_ratio _ (tauS U D) (gS G U F F' D) 3 (tauS_invol U D)
    (gS_tau G U F F' D hD hr0F') (fun s hg => joint_tau G U F F' D hH hD x s hg)

end tau

end PM
end Hedge

#print axioms Hedge.map_congr_supp
#print axioms Hedge.PM.joint_tau
#print axioms Hedge.PM.parR_three

/-! ## Runde 75: paritetsmodellene gir ikke-identifiserbarhet

`pmf_two`: `q 0 + q 1 = 1` for en fordeling på `ZMod 2`. `ennreal_contra`: `b = a`, `b = 3a` og
`b + a = 1` er umulig. `RO`: de observerte røttene; `parY`: pariteten på en tilordning av `RO`;
`parR_comp`: `parR = parY ∘ restrict`. `not_ident_PM`: med `Good` og de to trærne er
`P(RO | do X)` ikke identifiserbar: `M1` og `M2` har samme observerte fordeling (`marg_eq`),
`M1` er positiv (`pos_M1`), men like marginaler på `RO` under `do(x)` ville gitt like
paritetsfordelinger, og de er `1/2` (`parR_half`, med `cross_edge`) mot `1/4` (`parR_three`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma pmf_two (q : PMF (ZMod 2)) : q 0 + q 1 = 1 := by
  have h := q.tsum_coe
  rw [tsum_fintype] at h
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu, Finset.sum_pair (by decide)] at h
  exact h

lemma ennreal_contra (a b : ENNReal) (h1 : b = a) (h2 : b = 3 * a) (h3 : b + a = 1) : False := by
  have e1 : a + a = 1 := by
    rw [h1] at h3
    exact h3
  have e2 : 3 * a + a = 1 := by
    rw [h2] at h3
    exact h3
  have e3 : (3 : ENNReal) * a + a = (a + a) + (a + a) := by ring
  rw [e3, e1, one_add_one_eq_two] at e2
  exact absurd e2 (ne_of_gt ENNReal.one_lt_two)

section final

variable (G : DAG V) (U F F' : Finset V) (D : Data V)

/-- De observerte røttene. -/
def RO : Finset V := (rootsIn G F).filter (fun r => r ∉ U)

/-- Pariteten på en tilordning av `RO`. -/
def parY (y : Assignment (α := Val U) (RO G U F)) : ZMod 2 :=
  ∑ r ∈ (RO G U F).attach, rd (y r) 0

lemma parR_comp :
    parY G U F ∘ Assignment.restrict (Finset.subset_univ (RO G U F)) = parR G U F := by
  funext s
  exact Finset.sum_attach (RO G U F) (fun r => ov U s r)

/-- **Ikke identifiserbar på de observerte røttene**, gitt konstruksjonsdataene. -/
theorem not_ident_PM {X Y : Finset V} (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) {d d' : V → ℕ}
    (T : ParTree (OF U F) D.ρ D.par d) (T' : ParTree (OF U F') D.ρ D.par d')
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    ¬ Identifiable G (Val U) O X (RO G U F) := by
  intro hid
  obtain ⟨c, hc, hcU, hcρ, hA⟩ := cross_edge G U F F' D X hH hD hXU T'
  have hYX : ∀ v ∈ RO G U F, v ∉ X := fun v hv =>
    hH.out v (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  let x : Assignment (α := Val U) X := fun _ => 0
  have hmarg : (doModel (M G U F F' D false) X x).marginal (RO G U F) =
      (doModel (M G U F F' D true) X x).marginal (RO G U F) := by
    ext y
    let t : Assignment (α := Val U) (RO G U F ∪ X) := fun v =>
      if hv : v.1 ∈ RO G U F then y ⟨v.1, hv⟩ else x ⟨v.1, by
        rcases Finset.mem_union.mp v.2 with h | h
        · exact absurd h hv
        · exact h⟩
    have ht1 : ∀ h : X ⊆ RO G U F ∪ X, t.restrict h = x := by
      intro h
      funext ⟨v, hv⟩
      exact dif_neg (fun h' => hYX v h' hv)
    have ht2 : ∀ h : RO G U F ⊆ RO G U F ∪ X, t.restrict h = y := by
      intro h
      funext ⟨v, hv⟩
      exact dif_pos hv
    have h' := hid (M G U F F' D false) (M G U F F' D true)
      (marg_eq G U F F' D hH hD hroot T hO) (fun a => pos_M1 G U F F' D hH hD T' hO a) t
    rw [ht1, ht2] at h'
    exact h'
  have hq : (doModel (M G U F F' D false) X x).fullJoint.map (parR G U F) =
      (doModel (M G U F F' D true) X x).fullJoint.map (parR G U F) := by
    rw [← parR_comp G U F, ← PMF.map_comp, ← PMF.map_comp]
    exact congrArg (fun q => q.map (parY G U F)) hmarg
  have h1 := parR_half G U F F' D X hH hD hroot hXU hc hcU hcρ hA x
  have h2 := parR_three G U F F' D hH hD hroot x
  rw [hq] at h1
  exact ennreal_contra _ _ h1.symm h2 (pmf_two _)

end final

end PM
end Hedge

#print axioms Hedge.PM.not_ident_PM

/-! ## Runde 76: H3 for hver hedge

`mkData ρ par r0`: konstruksjonsdataene fra `hedge_spanning` (`par ρ := ρ`; `lat v` er en
latent forelder til både `v` og `par v`, valgt fra `sib`). `hedge_not_ident`: **for hver hedge
er `P(RO | do X)` ikke identifiserbar**, der `RO` er de observerte røttene i `F` (latente er
røtter, `X` er observert). `r0` er roten `nxt`-stien fra `ρ` når (`hedge_reaches_root`), og den
er observert (`iter_obs`). Dette er H3. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section build

variable (G : DAG V) (U : Finset V)

open Classical in
/-- Konstruksjonsdataene. -/
noncomputable def mkData (ρ : V) (par : V → V) (r0 : V) : Data V where
  ρ := ρ
  par := fun v => if v = ρ then ρ else par v
  lat := fun v => if h : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v then Classical.choose h else v
  r0 := r0

lemma mkData_par (ρ : V) (par : V → V) (r0 : V) {v : V} (hv : v ≠ ρ) :
    (mkData G U ρ par r0).par v = par v :=
  if_neg hv

lemma mkData_par_self (ρ : V) (par : V → V) (r0 : V) : (mkData G U ρ par r0).par ρ = ρ :=
  if_pos rfl

lemma mkData_lat (ρ : V) (par : V → V) (r0 : V) {v : V}
    (hex : ∃ u ∈ U, G.edge u (par v) ∧ G.edge u v) :
    (mkData G U ρ par r0).lat v ∈ U ∧ G.edge ((mkData G U ρ par r0).lat v) (par v) ∧
      G.edge ((mkData G U ρ par r0).lat v) v := by
  have h : (mkData G U ρ par r0).lat v = Classical.choose hex := dif_pos hex
  rw [h]
  exact Classical.choose_spec hex

/-- **H3: en hedge er ikke identifiserbar på de observerte røttene.** -/
theorem hedge_not_ident {X Y F F' : Finset V} (hH : IsHedge G U X Y F F')
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) :
    ¬ Identifiable G (Val U) Uᶜ X (RO G U F) := by
  obtain ⟨ρ, hρ, hρU, par, d, hpd⟩ := hedge_spanning hH hroot
  obtain ⟨n, hn⟩ := hedge_reaches_root hH ρ (hH.sub hρ)
  have hnU := iter_obs hH hroot (hH.sub hρ) hρU n
  have hGood : Good G U F F' (mkData G U ρ par ((nxt G F F')^[n] ρ)) :=
    { ρF := hρ
      ρU := hρU
      parF' := fun v hv hvU hvρ => by
        rw [mkData_par G U ρ par _ hvρ]
        have hs := (hpd v hv hvU hvρ).1
        exact ⟨hs.1, (sib_obs hroot hs).1⟩
      parF := fun v hvF hvU hvρ => by
        rw [mkData_par G U ρ par _ hvρ]
        exact ((hpd v (hH.sub hvF) hvU hvρ).2.2 hvF).1
      lat := fun v hv hvU hvρ => by
        obtain ⟨-, -, u, hu, -, e1, e2⟩ := (hpd v hv hvU hvρ).1
        obtain ⟨h1, h2, h3⟩ := mkData_lat G U ρ par ((nxt G F F')^[n] ρ) (v := v) ⟨u, hu, e1, e2⟩
        rw [mkData_par G U ρ par _ hvρ]
        exact ⟨h1, h3, h2⟩
      r0R := hn
      r0U := hnU }
  have T : ParTree (OF U F) (mkData G U ρ par ((nxt G F F')^[n] ρ)).ρ
      (mkData G U ρ par ((nxt G F F')^[n] ρ)).par d :=
    { root := Finset.mem_filter.mpr ⟨hρ, hρU⟩
      fix := mkData_par_self G U ρ par _
      step := fun v hv hvρ => by
        obtain ⟨hvF, hvU⟩ := Finset.mem_filter.mp hv
        rw [mkData_par G U ρ par _ hvρ]
        obtain ⟨hs, hd, hsF⟩ := hpd v (hH.sub hvF) hvU hvρ
        exact ⟨Finset.mem_filter.mpr ⟨(hsF hvF).1, (sib_obs hroot hs).1⟩, hd⟩ }
  have T' : ParTree (OF U F') (mkData G U ρ par ((nxt G F F')^[n] ρ)).ρ
      (mkData G U ρ par ((nxt G F F')^[n] ρ)).par d :=
    { root := Finset.mem_filter.mpr ⟨hH.sub hρ, hρU⟩
      fix := mkData_par_self G U ρ par _
      step := fun v hv hvρ => by
        obtain ⟨hvF', hvU⟩ := Finset.mem_filter.mp hv
        rw [mkData_par G U ρ par _ hvρ]
        obtain ⟨hs, hd, -⟩ := hpd v hvF' hvU hvρ
        exact ⟨Finset.mem_filter.mpr ⟨hs.1, (sib_obs hroot hs).1⟩, hd⟩ }
  exact not_ident_PM G U F F' _ hH hGood hroot hXU T T' (fun v hv => Finset.mem_compl.mp hv)

end build

end PM
end Hedge

#print axioms Hedge.PM.hedge_not_ident

/-! ## Runde 78: H4, steg 1 — halepekeren `tp`

`anc_child_in`: en node i `ancIn G T C` er i `C` eller har et barn i `ancIn G T C`.
`AY` = forfedrene til `Y` i `G_{X̄}`. `tp v`: for `v ∈ AY \ Y` et barn i `AY` utenfor `X`
(`tp_spec`); i `Y` står `tp` stille. Langs `tp` vokser rangen (`tp_rank_iter`), stien holder
seg i `AY` og utenfor `X` (`tp_iter_mem`, `tp_iter_notX`), er observert når starten er det
(`tp_iter_obs`), og når `Y` (`tp_reaches`). `tI s w`: `w` ligger på `tp`-stien fra `s`.
`tI_rec`: `tI s v = [v = s] + Σ tI s w` over de observerte `w ∈ AY \ Y` med `tp w = v`.
`sum_tI_Y`: stien når nøyaktig én node i `Y`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En node i `ancIn G T C` er i `C` eller har et barn i `ancIn G T C`. -/
lemma anc_child_in (G : DAG V) (T C : Finset V) (hCT : C ⊆ T) :
    ∀ v ∈ ancIn G T C, v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w := by
  have h := ancIn_min G T C
    ((ancIn G T C).filter (fun v => v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w))
    (fun v hv => Finset.mem_filter.mpr ⟨anc_sup G T C hv, Or.inl hv⟩)
    (fun v hvT hex => by
      obtain ⟨w, hw, e⟩ := hex
      have hwA := (Finset.mem_filter.mp hw).1
      exact Finset.mem_filter.mpr ⟨anc_closed G T C hCT v hvT ⟨w, hwA, e⟩, Or.inr ⟨w, hwA, e⟩⟩)
  intro v hv
  exact (Finset.mem_filter.mp (h hv)).2

section tail

variable (G : DAG V) (X Y : Finset V)

/-- Forfedrene til `Y` i `G_{X̄}`. -/
def AY : Finset V := ancIn (cutIn G X) Finset.univ Y

open Classical in
/-- Halepekeren. -/
noncomputable def tp (v : V) : V :=
  if v ∈ Y then v else
    if h : ∃ w ∈ AY G X Y, (cutIn G X).edge v w then Classical.choose h else v

lemma tp_Y {v : V} (hv : v ∈ Y) : tp G X Y v = v := by
  unfold tp
  rw [if_pos hv]

lemma tp_spec {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    tp G X Y v ∈ AY G X Y ∧ G.edge v (tp G X Y v) ∧ tp G X Y v ∉ X := by
  have hex : ∃ w ∈ AY G X Y, (cutIn G X).edge v w := by
    rcases anc_child_in (cutIn G X) Finset.univ Y (Finset.subset_univ _) v hv with h | h
    · exact absurd h hvY
    · exact h
  have hdef : tp G X Y v = Classical.choose hex := by
    unfold tp
    rw [if_neg hvY, dif_pos hex]
  rw [hdef]
  obtain ⟨hA, e⟩ := Classical.choose_spec hex
  have e' : G.edge v (Classical.choose hex) ∧ Classical.choose hex ∉ X := e
  exact ⟨hA, e'.1, e'.2⟩

lemma iter_tpY {v : V} (hv : v ∈ Y) : ∀ m, (tp G X Y)^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, tp_Y G X Y hv]

lemma tp_iter_mem {v : V} (hv : v ∈ AY G X Y) : ∀ n, (tp G X Y)^[n] v ∈ AY G X Y := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y ih hY).1

lemma tp_iter_notX {v : V} (hv : v ∈ AY G X Y) (hvX : v ∉ X) :
    ∀ n, (tp G X Y)^[n] v ∉ X := by
  intro n
  induction n with
  | zero => exact hvX
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.2

lemma tp_iter_obs {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V}
    (hv : v ∈ AY G X Y) (hvU : v ∉ U) : ∀ n, (tp G X Y)^[n] v ∉ U := by
  intro n
  induction n with
  | zero => exact hvU
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · intro hU
      exact hroot _ hU _ (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.1

lemma tp_rank_iter {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    ∀ m, G.rank v < G.rank ((tp G X Y)^[m + 1] v) := by
  intro m
  induction m with
  | zero =>
    show G.rank v < G.rank (tp G X Y v)
    exact G.rank_strict_mono _ _ (tp_spec G X Y hv hvY).2.1
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases huY : (tp G X Y)^[m + 1] v ∈ Y
    · rw [tp_Y G X Y huY]
      exact ih
    · exact lt_trans ih
        (G.rank_strict_mono _ _ (tp_spec G X Y (tp_iter_mem G X Y hv (m + 1)) huY).2.1)

lemma tp_cycle {v : V} (hv : v ∈ AY G X Y) {m : ℕ} (h : (tp G X Y)^[m + 1] v = v) : v ∈ Y := by
  by_contra hY
  have hlt := tp_rank_iter G X Y hv hY m
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- **Halen når `Y`.** -/
theorem tp_reaches : ∀ v ∈ AY G X Y, ∃ n, (tp G X Y)^[n] v ∈ Y := by
  have key : ∀ k, ∀ v ∈ AY G X Y, (Finset.univ : Finset V).sup G.rank - G.rank v = k →
      ∃ n, (tp G X Y)^[n] v ∈ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hk
      by_cases hY : v ∈ Y
      · exact ⟨0, hY⟩
      · obtain ⟨hw, e, -⟩ := tp_spec G X Y hv hY
        have hlt := G.rank_strict_mono v _ e
        have hle : G.rank (tp G X Y v) ≤ (Finset.univ : Finset V).sup G.rank :=
          Finset.le_sup (Finset.mem_univ _)
        obtain ⟨n, hn⟩ := ih ((Finset.univ : Finset V).sup G.rank - G.rank (tp G X Y v))
          (by omega) _ hw rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  exact fun v hv => key _ v hv rfl

open Classical in
/-- `w` ligger på `tp`-stien fra `s`. -/
noncomputable def tI (s w : V) : ZMod 2 := if ∃ k, (tp G X Y)^[k] s = w then 1 else 0

lemma tp_pred_aux {s v w w' : V} (hs : s ∈ AY G X Y) {k k' : ℕ} (hk : k < k')
    (h1 : (tp G X Y)^[k] s = w) (h2 : (tp G X Y)^[k'] s = w')
    (hwv : tp G X Y w = v) (hw'v : tp G X Y w' = v) (hw' : w' ∉ Y) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hv : (tp G X Y)^[k + 1] s = v := by
    rw [Function.iterate_succ_apply', h1, hwv]
  have hw'm : (tp G X Y)^[m] v = w' := by
    rw [← hv, ← Function.iterate_add_apply, ← h2, show m + (k + 1) = k + m + 1 by omega]
  have hvA : v ∈ AY G X Y := by
    rw [← hv]
    exact tp_iter_mem G X Y hs (k + 1)
  have hcyc : (tp G X Y)^[m + 1] v = v := by
    rw [Function.iterate_succ_apply', hw'm, hw'v]
  have hY := tp_cycle G X Y hvA hcyc
  apply hw'
  rw [← hw'm, iter_tpY G X Y hY m]
  exact hY

/-- **Rekursjonen for `tI`.** -/
theorem tI_rec {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s v : V}
    (hs : s ∈ AY G X Y) (hsU : s ∉ U) :
    tI G X Y s v = (if v = s then 1 else 0) +
      ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v), tI G X Y s w := by
  classical
  have huniq : ∀ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      ∀ w' ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      (∃ k, (tp G X Y)^[k] s = w) → (∃ k, (tp G X Y)^[k] s = w') → w = w' := by
    intro w hw w' hw' h h'
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, -, hw'Y, hw'v⟩ := Finset.mem_filter.mp hw'
    obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := h'
    rcases lt_trichotomy k k' with hl | he | hl
    · exact (tp_pred_aux G X Y hs hl hk hk' hwv hw'v hw'Y).elim
    · subst he
      exact hk.symm.trans hk'
    · exact (tp_pred_aux G X Y hs hl hk' hk hw'v hwv hwY).elim
  by_cases hvs : v = s
  · have hr0 : ∃ k, (tp G X Y)^[k] s = v := ⟨0, hvs.symm⟩
    have h1 : tI G X Y s v = 1 := by
      unfold tI
      rw [if_pos hr0]
    rw [h1, if_pos hvs, Finset.sum_eq_zero, add_zero]
    intro w hw
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    have hcyc : (tp G X Y)^[k + 1] s = s := by
      rw [Function.iterate_succ_apply', hk, hwv, hvs]
    have hY := tp_cycle G X Y hs hcyc
    apply hwY
    rw [← hk, iter_tpY G X Y hY k]
    exact hY
  · rw [if_neg hvs, zero_add]
    by_cases hr : ∃ k, (tp G X Y)^[k] s = v
    · have hex : ∃ k, (tp G X Y)^[k] s = v := hr
      obtain ⟨k, hk⟩ := hr
      have hk0 := Nat.find_spec hex
      have hne0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0] at hk0
        exact hvs hk0.symm
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjv : (tp G X Y)^[j + 1] s = v := by
        rw [← hj]
        exact hk0
      have hwv : tp G X Y ((tp G X Y)^[j] s) = v := by
        have h' := hjv
        rw [Function.iterate_succ_apply'] at h'
        exact h'
      have hwY : (tp G X Y)^[j] s ∉ Y := by
        intro hY
        rw [tp_Y G X Y hY] at hwv
        exact Nat.find_min hex (show j < Nat.find hex by omega) hwv
      have hwmem : (tp G X Y)^[j] s ∈
          (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v) :=
        Finset.mem_filter.mpr ⟨tp_iter_mem G X Y hs j, tp_iter_obs G X Y hroot hs hsU j, hwY, hwv⟩
      have hwr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[j] s := ⟨j, rfl⟩
      unfold tI
      rw [if_pos hex, Finset.sum_eq_single ((tp G X Y)^[j] s)]
      · rw [if_pos hwr]
      · intro b hb hbw
        rw [if_neg]
        intro hbr
        exact hbw (huniq b hb _ hwmem hbr hwr)
      · intro hn
        exact absurd hwmem hn
    · unfold tI
      rw [if_neg hr, Finset.sum_eq_zero]
      intro w hw
      rw [if_neg]
      rintro ⟨k, hk⟩
      obtain ⟨-, -, -, hwv⟩ := Finset.mem_filter.mp hw
      apply hr
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hwv]⟩

/-- **Stien når nøyaktig én node i `Y`.** -/
theorem sum_tI_Y {s : V} (hs : s ∈ AY G X Y) : ∑ y ∈ Y, tI G X Y s y = 1 := by
  obtain ⟨n, hn⟩ := tp_reaches G X Y s hs
  have hr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[n] s := ⟨n, rfl⟩
  rw [Finset.sum_eq_single ((tp G X Y)^[n] s)]
  · unfold tI
    rw [if_pos hr]
  · intro b hb hbn
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    apply hbn
    rcases le_total k n with hl | hl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [add_comm, Function.iterate_add_apply, hk, iter_tpY G X Y hb m]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [← hk, add_comm, Function.iterate_add_apply, iter_tpY G X Y hn m]
  · intro hn'
    exact absurd hn hn'

end tail

end Hedge

#print axioms Hedge.tp_spec
#print axioms Hedge.tp_reaches
#print axioms Hedge.tI_rec
#print axioms Hedge.sum_tI_Y

/-! ## Runde 79: H4, steg 2 — produktmodellene

Verditypen `Val2 U v = Val U v × ZMod 2`. Første koordinat `a` følger paritetsmodellen
`M G U F F' D two` (kjernen leser bare foreldrenes `a`), andre koordinat er
`b_v = [v ∈ RO] a_v + Σ_{w ∈ TC v} b_w + η_v` med `η_v ~ noise`, der `TC v` er de observerte
`w ∈ AY \ Y` med `tp w = v`. `kern2_apply`: kjernen er `kern … a · noise (b + bIn)`.
`kfac2_eq`: faktoren i `MP` er faktoren i `M` på `fstA s` ganget med `noise (etaS s v)`;
`joint2_eq`: det samme for fellesfordelingen. `etaS_eq`: uten foreldrevakter (`TC v` er
foreldre til `v`, `tc_edge`). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_bab : ∀ a b : ZMod 2, b + (a + b) = a := by decide

/-- Verditypen for produktmodellene. -/
abbrev Val2 (U : Finset V) (v : V) : Type := Val U v × ZMod 2

section prod

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V) (two : Bool)

/-- Haleforeldrene til `v`. -/
noncomputable def TC (v : V) : Finset V :=
  (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v)

lemma tc_edge {v w : V} (hw : w ∈ TC G U X Y v) : G.edge w v := by
  obtain ⟨hwA, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
  have h := (tp_spec G X Y hwA hwY).2.1
  rw [hwv] at h
  exact h

/-- Inngangen til `b` i `v`. -/
noncomputable def bIn (v : V) (a : Val U v) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) :
    ZMod 2 :=
  (if v ∈ RO G U F then rd a 0 else 0) +
    ∑ w ∈ TC G U X Y v, (if h : w ∈ G.parents v then (pa ⟨w, h⟩).2 else 0)

/-- Kjernen. -/
noncomputable def kern2 (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) :
    PMF (Val2 U v) :=
  (kern G U F F' D two v (fun u => (pa u).1)).bind
    (fun a => noise.map (fun η => (a, bIn G U F X Y v a pa + η)))

/-- **Produktmodellen.** -/
noncomputable def MP : G.CausalModel (Val2 U) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := kern2 G U F F' D X Y two

lemma kern2_apply (v : V) (pa : ∀ u : {u // u ∈ G.parents v}, Val2 U u.1) (z : Val2 U v) :
    kern2 G U F F' D X Y two v pa z =
      kern G U F F' D two v (fun u => (pa u).1) z.1 * noise (z.2 + bIn G U F X Y v z.1 pa) := by
  unfold kern2
  rw [PMF.bind_apply, tsum_eq_single z.1]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single (z.2 + bIn G U F X Y v z.1 pa)]
    · rw [if_pos]
      exact Prod.ext rfl (zmod2_bab _ _).symm
    · intro η hη
      rw [if_neg]
      intro h
      apply hη
      have h2 := congrArg Prod.snd h
      exact (zmod2_solve _ _ _).mp h2
  · intro a ha
    have h0 : (noise.map (fun η => (a, bIn G U F X Y v a pa + η))) z = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro η
      rw [if_neg]
      intro h
      exact ha (congrArg Prod.fst h).symm
    rw [h0, mul_zero]

/-- Første koordinat. -/
def fstA (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val U) (Finset.univ : Finset V) :=
  fun u => (s u).1

/-- Støyleddet i `v`. -/
noncomputable def etaS (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) : ZMod 2 :=
  (s ⟨v, Finset.mem_univ v⟩).2 +
    ((if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
      ∑ w ∈ TC G U X Y v,
        (if h : w ∈ G.parents v then (s ⟨w, Finset.mem_univ w⟩).2 else 0))

/-- **Faktoriseringen.** -/
theorem kfac2_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    kfac (MP G U F F' D X Y two) Finset.univ s v =
      kfac (M G U F F' D two) Finset.univ (fstA U s) v * noise (etaS G U F X Y s v) := by
  have h1 : kfac (MP G U F F' D X Y two) Finset.univ s v =
      kern2 G U F F' D X Y two v (s.restrict (Finset.subset_univ _)) (s ⟨v, Finset.mem_univ v⟩) :=
    DoAudit.kfac_univ _ _ _
  have h2 : kfac (M G U F F' D two) Finset.univ (fstA U s) v =
      kern G U F F' D two v ((fstA U s).restrict (Finset.subset_univ _))
        ((fstA U s) ⟨v, Finset.mem_univ v⟩) :=
    DoAudit.kfac_univ _ _ _
  rw [h1, h2, kern2_apply]
  rfl

theorem joint2_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (MP G U F F' D X Y two).fullJoint s =
      (M G U F F' D two).fullJoint (fstA U s) * ∏ v, noise (etaS G U F X Y s v) := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun v _ => kfac2_eq G U F F' D X Y two s v)

/-- `etaS` uten foreldrevakter. -/
lemma etaS_eq (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y s v = (s ⟨v, Finset.mem_univ v⟩).2 +
      ((if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
        ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2) := by
  unfold etaS
  congr 2
  apply Finset.sum_congr rfl
  intro w hw
  rw [dif_pos (mem_parents_iff.mpr (tc_edge G U X Y hw))]

end prod

end PM
end Hedge

#print axioms Hedge.PM.kern2_apply
#print axioms Hedge.PM.kfac2_eq
#print axioms Hedge.PM.joint2_eq

/-! ## Runde 80: H4, steg 3 og 4 — lik observert fordeling og positivitet

`phiS2`: involusjonen fra H3 på første koordinat, andre koordinat uendret. Den holder de
observerte verdiene (`phiS2_restrict`) og endrer ikke støyleddene (`etaS_phiS2`: de leser
bare `b` og de observerte `a`-verdiene i `RO`), så `joint2_eq` og `joint_phiS` gir
`joint2_phiS2`, og `marg2_eq`: `MP false` og `MP true` har samme observerte fordeling.
`pos2`: hver observert tilordning har positiv sannsynlighet i `MP false` (første koordinat
fra `pos_M1`, og hver støyfaktor er positiv). -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

section obs2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

lemma phiS_obs (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (t : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∉ U) :
    phiS G U F F' D t ⟨v, Finset.mem_univ v⟩ = t ⟨v, Finset.mem_univ v⟩ := by
  unfold phiS
  exact sh_obs G U F F' D hD hFF' _ t hv

/-- Involusjonen på produktmodellene. -/
noncomputable def phiS2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (phiS G U F F' D (fstA U s) u, (s u).2)

lemma fstA_phiS2 (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (phiS2 G U F F' D s) = phiS G U F F' D (fstA U s) := rfl

lemma phiS2_invol (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    phiS2 G U F F' D (phiS2 G U F F' D s) = s := by
  funext u
  show (phiS G U F F' D (fstA U (phiS2 G U F F' D s)) u, (s u).2) = s u
  rw [fstA_phiS2, phiS_invol G U F F' D hD hFF']
  rfl

lemma phiS2_restrict (hD : Good G U F F' D) (hFF' : F ⊆ F') {O : Finset V}
    (hO : ∀ v ∈ O, v ∉ U) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (phiS2 G U F F' D s).restrict (Finset.subset_univ O) = s.restrict (Finset.subset_univ O) := by
  funext ⟨v, hv⟩
  show (phiS G U F F' D (fstA U s) ⟨v, Finset.mem_univ v⟩, (s ⟨v, Finset.mem_univ v⟩).2) =
    s ⟨v, Finset.mem_univ v⟩
  rw [phiS_obs G U F F' D hD hFF' _ (hO v hv)]
  rfl

lemma etaS_phiS2 (hD : Good G U F F' D) (hFF' : F ⊆ F')
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y (phiS2 G U F F' D s) v = etaS G U F X Y s v := by
  have e1 : ∀ w, (phiS2 G U F F' D s ⟨w, Finset.mem_univ w⟩).2 = (s ⟨w, Finset.mem_univ w⟩).2 :=
    fun w => rfl
  have e2 : (if v ∈ RO G U F then rd (phiS2 G U F F' D s ⟨v, Finset.mem_univ v⟩).1 0 else 0) =
      (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) := by
    by_cases hv : v ∈ RO G U F
    · rw [if_pos hv, if_pos hv]
      show rd (phiS G U F F' D (fstA U s) ⟨v, Finset.mem_univ v⟩) 0 = _
      rw [phiS_obs G U F F' D hD hFF' _ (Finset.mem_filter.mp hv).2]
      rfl
    · rw [if_neg hv, if_neg hv]
  unfold etaS
  simp only [e1, e2]

/-- **Like fellesfordelinger etter involusjonen.** -/
theorem joint2_phiS2 {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (MP G U F F' D X Y true).fullJoint (phiS2 G U F F' D s) =
      (MP G U F F' D X Y false).fullJoint s := by
  rw [joint2_eq, joint2_eq, fstA_phiS2, joint_phiS G U F F' D hH hD hroot T]
  congr 1
  exact Finset.prod_congr rfl (fun v _ => by rw [etaS_phiS2 G U F F' D X Y hD hH.sub s v])

/-- **Steg 3: samme observerte fordeling.** -/
theorem marg2_eq {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {d : V → ℕ} (T : ParTree (OF U F) D.ρ D.par d)
    {O : Finset V} (hO : ∀ v ∈ O, v ∉ U) :
    (MP G U F F' D X Y false).marginal O = (MP G U F F' D X Y true).marginal O :=
  marginal_eq_of_invol _ _ O (phiS2 G U F F' D) (phiS2_invol G U F F' D hD hH.sub)
    (phiS2_restrict G U F F' D hD hH.sub hO) (joint2_phiS2 G U F F' D X Y hH hD hroot T)

/-- **Steg 4: positivitet.** -/
theorem pos2 {X0 Y0 : Finset V} (hH : IsHedge G U X0 Y0 F F') (hD : Good G U F F' D)
    {d : V → ℕ} (T' : ParTree (OF U F') D.ρ D.par d) {O : Finset V} (hO : ∀ v ∈ O, v ∉ U)
    (a : Assignment (α := Val2 U) O) :
    (MP G U F F' D X Y false).marginal O a ≠ 0 := by
  let aA : Assignment (α := Val U) O := fun v => (a v).1
  have hA := pos_M1 G U F F' D hH hD T' hO aA
  have hmem : aA ∈ ((M G U F F' D false).marginal O).support :=
    (PMF.mem_support_iff _ _).mpr hA
  unfold CausalModel.marginal at hmem
  rw [PMF.mem_support_map_iff] at hmem
  obtain ⟨sA, hsA, hres⟩ := hmem
  let s : Assignment (α := Val2 U) (Finset.univ : Finset V) :=
    fun u => (sA u, if h : u.1 ∈ O then (a ⟨u.1, h⟩).2 else 0)
  have hsupp : (MP G U F F' D X Y false).fullJoint s ≠ 0 := by
    rw [joint2_eq]
    refine mul_ne_zero ((PMF.mem_support_iff _ _).mp hsA) ?_
    rw [Finset.prod_ne_zero_iff]
    exact fun v _ => noise_pos _
  have hrs : s.restrict (Finset.subset_univ O) = a := by
    funext ⟨v, hv⟩
    have h1 : sA ⟨v, Finset.mem_univ v⟩ = (a ⟨v, hv⟩).1 := congrFun hres ⟨v, hv⟩
    show (sA ⟨v, Finset.mem_univ v⟩, if h : v ∈ O then (a ⟨v, h⟩).2 else 0) = a ⟨v, hv⟩
    rw [h1, dif_pos hv]
  intro h0
  have hmem2 : a ∈ ((MP G U F F' D X Y false).marginal O).support := by
    unfold CausalModel.marginal
    rw [PMF.mem_support_map_iff]
    exact ⟨s, (PMF.mem_support_iff _ _).mpr hsupp, hrs⟩
  exact (PMF.mem_support_iff _ _).mp hmem2 h0

end obs2

end PM
end Hedge

#print axioms Hedge.PM.marg2_eq
#print axioms Hedge.PM.pos2

/-! ## Runde 81: H4, steg 5 — `MP false` under `do(x)`: `P(Yb = 1) = P(Yb = 0)`

`betaC c w = Σ_{r ∈ RO} phiC c r · tI r w`: hvor ψ må snu `b` (langs halene fra røttene ψ snur).
`betaC_rec`: `betaC c v = [v ∈ RO] phiC c v + Σ_{TC v} betaC c w` (fra `tI_rec`); i latente og i
`X` er den 0. `psi2 c`: ψ på første koordinat, `b + betaC` på andre; involusjon. `etaS_psi2`:
støyleddene endres ikke. `kfac_psi2_do`, `joint_psi2`: fellesfordelingen under `do(x)` er
invariant. `Yb`: pariteten til `b` over `Y`; `Yb_psi2`: ψ2 snur `Yb` (hver hale når nøyaktig én
node i `Y`, og `Σ_{RO} phiC c = 1`). `Yb_half`: `P(Yb = 1) = P(Yb = 0)` under `do(x)` i `MP false`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_l5 : ∀ a b c d e : ZMod 2, a + (b + c) + (d + b + (e + c)) = a + (d + e) := by decide

lemma zmod2_l3 : ∀ a c e : ZMod 2, a + (0 + c) + (0 + (e + c)) = a + (0 + e) := by decide

section psi2

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- Hvor ψ snur `b`. -/
noncomputable def betaC (c w : V) : ZMod 2 :=
  ∑ r ∈ RO G U F, phiC G F F' D X c r * tI G X Y r w

/-- **ψ på produktmodellene.** -/
noncomputable def psi2 (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Assignment (α := Val2 U) (Finset.univ : Finset V) :=
  fun u => (psiS G U F F' D X c (fstA U s) u, (s u).2 + betaC G U F F' D X Y c u.1)

lemma fstA_psi2 (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    fstA U (psi2 G U F F' D X Y c s) = psiS G U F F' D X c (fstA U s) := rfl

lemma psi2_invol (c : V) (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    psi2 G U F F' D X Y c (psi2 G U F F' D X Y c s) = s := by
  funext u
  show (psiS G U F F' D X c (fstA U (psi2 G U F F' D X Y c s)) u,
    (s u).2 + betaC G U F F' D X Y c u.1 + betaC G U F F' D X Y c u.1) = s u
  rw [fstA_psi2, psiS_invol, add_assoc, zmod2_add_self, add_zero]
  rfl

lemma betaC_rec (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (c v : V) :
    betaC G U F F' D X Y c v = (if v ∈ RO G U F then phiC G F F' D X c v else 0) +
      ∑ w ∈ TC G U X Y v, betaC G U F F' D X Y c w := by
  unfold betaC TC
  have hrw : ∀ r ∈ RO G U F, phiC G F F' D X c r * tI G X Y r v =
      (if v = r then phiC G F F' D X c r else 0) +
        ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
          phiC G F F' D X c r * tI G X Y r w := by
    intro r hr
    have hrA : r ∈ AY G X Y := hH.anc (Finset.mem_filter.mp hr).1
    rw [tI_rec G X Y hroot hrA (Finset.mem_filter.mp hr).2, mul_add, Finset.mul_sum]
    congr 1
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_comm]

lemma betaC_X (hH : IsHedge G U X Y F F') (c : V) {v : V} (hv : v ∈ X) :
    betaC G U F F' D X Y c v = 0 := by
  unfold betaC
  apply Finset.sum_eq_zero
  intro r hr
  have hrF := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hrA : r ∈ AY G X Y := hH.anc (Finset.mem_filter.mp hr).1
  have h0 : tI G X Y r v = 0 := by
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    apply tp_iter_notX G X Y hrA (hH.out r hrF) k
    rw [hk]
    exact hv
  rw [h0, mul_zero]

lemma psiS_X (hD : Good G U F F' D) (hXU : ∀ v ∈ X, v ∉ U) {c : V} (hc : c ∈ F') (hcU : c ∉ U)
    (hcρ : c ≠ D.ρ) (t : Assignment (α := Val U) (Finset.univ : Finset V)) {v : V} (hv : v ∈ X) :
    psiS G U F F' D X c t ⟨v, Finset.mem_univ v⟩ = t ⟨v, Finset.mem_univ v⟩ := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hE : ∀ c' ∈ EF U {c} D, D.lat c' ∈ U := fun c' hc' => by
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hc').1]
    exact hcl
  have h0 : phiC G F F' D X c v = 0 := by
    unfold phiC
    rw [nrI_X G F F' X hv, nrI_X G F F' X hv, add_zero]
  unfold psiS
  rw [flipO_obs U _ _ (hXU v hv), obs_shE U D {c} hE _ t (hXU v hv), h0]
  funext i
  exact add_zero _

/-- **Støyleddene endres ikke av ψ2.** -/
theorem etaS_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    etaS G U F X Y (psi2 G U F F' D X Y c s) v = etaS G U F X Y s v := by
  have hcl := (hD.lat c hc hcU hcρ).1
  have hb : ∀ w, (psi2 G U F F' D X Y c s ⟨w, Finset.mem_univ w⟩).2 =
      (s ⟨w, Finset.mem_univ w⟩).2 + betaC G U F F' D X Y c w := fun w => rfl
  rw [etaS_eq, etaS_eq]
  simp only [hb, Finset.sum_add_distrib]
  rw [betaC_rec G U F F' D X Y hH hroot c v]
  by_cases hvRO : v ∈ RO G U F
  · have ha : rd (psi2 G U F F' D X Y c s ⟨v, Finset.mem_univ v⟩).1 0 =
        rd (s ⟨v, Finset.mem_univ v⟩).1 0 + phiC G F F' D X c v :=
      ov_psi G U F F' D X c hcl (fstA U s) (Finset.mem_filter.mp hvRO).2
    simp only [if_pos hvRO]
    rw [ha]
    exact zmod2_l5 _ _ _ _ _
  · simp only [if_neg hvRO]
    exact zmod2_l3 _ _ _

/-- Hver faktor under `do(x)` bevares. -/
theorem kfac_psi2_do (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val2 U) X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel (MP G U F F' D X Y false) X x) Finset.univ (psi2 G U F F' D X Y c s) v =
      kfac (doModel (MP G U F F' D X Y false) X x) Finset.univ s v := by
  rw [kfac_doModel, kfac_doModel]
  by_cases hv : v ∈ X
  · rw [dif_pos hv, dif_pos hv]
    have hpv : psi2 G U F F' D X Y c s ⟨v, Finset.mem_univ v⟩ = s ⟨v, Finset.mem_univ v⟩ := by
      show (psiS G U F F' D X c (fstA U s) ⟨v, Finset.mem_univ v⟩,
        (s ⟨v, Finset.mem_univ v⟩).2 + betaC G U F F' D X Y c v) = s ⟨v, Finset.mem_univ v⟩
      rw [psiS_X G U F F' D X hD hXU hc hcU hcρ _ hv, betaC_X G U F F' D X Y hH c hv, add_zero]
      rfl
    rw [hpv]
  · rw [dif_neg hv, dif_neg hv, kfac2_eq, kfac2_eq, etaS_psi2 G U F F' D X Y hH hD hroot hc hcU hcρ]
    congr 1
    have h := kfac_psi_do G U F F' D X hH hD hroot hXU hc hcU hcρ (fun w => (x w).1) (fstA U s) v
    rw [kfac_doModel, kfac_doModel, dif_neg hv, dif_neg hv] at h
    exact h

theorem joint_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U)
    {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ) (x : Assignment (α := Val2 U) X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    (doModel (MP G U F F' D X Y false) X x).fullJoint (psi2 G U F F' D X Y c s) =
      (doModel (MP G U F F' D X Y false) X x).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  exact Finset.prod_congr rfl
    (fun v _ => kfac_psi2_do G U F F' D X Y hH hD hroot hXU hc hcU hcρ x s v)

/-- Pariteten til `b` over `Y`. -/
noncomputable def Yb (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) : ZMod 2 :=
  ∑ y ∈ Y, (s ⟨y, Finset.mem_univ y⟩).2

lemma sum_phiC_RO (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r)) :
    ∑ r ∈ RO G U F, phiC G F F' D X c r = 1 := by
  have hcl := (hD.lat c hc hcU hcρ).1
  let t : Assignment (α := Val U) (Finset.univ : Finset V) := fun _ => 0
  have h1 := parR_psi G U F F' D X hH hD hroot hc hcU hcρ hA t
  have h2 : parR G U F (psiS G U F F' D X c t) = parR G U F t + ∑ r ∈ RO G U F, phiC G F F' D X c r := by
    unfold parR RO
    rw [Finset.sum_congr rfl (fun r hr => ov_psi G U F F' D X c hcl t (Finset.mem_filter.mp hr).2),
      Finset.sum_add_distrib]
  rw [h2] at h1
  exact add_left_cancel h1

/-- **ψ2 snur `Yb`.** -/
theorem Yb_psi2 (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {c : V} (hc : c ∈ F') (hcU : c ∉ U) (hcρ : c ≠ D.ρ)
    (hA : ((∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ¬ ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r) ∨
      ((¬ ∃ r ∈ rootsIn G F, nreach G X F F' c r) ∧
        ∃ r ∈ rootsIn G F, nreach G X F F' (D.par c) r))
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y (psi2 G U F F' D X Y c s) = Yb U Y s + 1 := by
  unfold Yb
  rw [show (∑ y ∈ Y, (psi2 G U F F' D X Y c s ⟨y, Finset.mem_univ y⟩).2) =
      ∑ y ∈ Y, ((s ⟨y, Finset.mem_univ y⟩).2 + betaC G U F F' D X Y c y) from rfl,
    Finset.sum_add_distrib]
  congr 1
  unfold betaC
  rw [Finset.sum_comm,
    Finset.sum_congr rfl (fun r hr => by
      rw [← Finset.mul_sum, sum_tI_Y G X Y (hH.anc (Finset.mem_filter.mp hr).1), mul_one])]
  exact sum_phiC_RO G U F F' D X Y hH hD hroot hc hcU hcρ hA

/-- **Steg 5: `P(Yb = 1) = P(Yb = 0)` under `do(x)` i `MP false`.** -/
theorem Yb_half (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hXU : ∀ v ∈ X, v ∉ U) {d : V → ℕ}
    (T' : ParTree (OF U F') D.ρ D.par d) (x : Assignment (α := Val2 U) X) :
    ((doModel (MP G U F F' D X Y false) X x).fullJoint.map (Yb U Y)) 1 =
      ((doModel (MP G U F F' D X Y false) X x).fullJoint.map (Yb U Y)) 0 := by
  obtain ⟨c, hc, hcU, hcρ, hA⟩ := cross_edge G U F F' D X hH hD hXU T'
  exact map_flip_eq _ (psi2 G U F F' D X Y c) (Yb U Y) (psi2_invol G U F F' D X Y c)
    (joint_psi2 G U F F' D X Y hH hD hroot hXU hc hcU hcρ x)
    (Yb_psi2 G U F F' D X Y hH hD hroot hc hcU hcρ hA)

end psi2

end PM
end Hedge

#print axioms Hedge.PM.etaS_psi2
#print axioms Hedge.PM.Yb_half

/-! ## Runde 82: H4, steg 6a — skjevhetslemmaet

`pair_ratio`: en involusjon σ som holder `f` fast, snur `e` og tredobler vekten der `e = 1`,
gir `P(f = a, e = 0) = 3 · P(f = a, e = 1)`. `map_fst0` … `map_add1`: fordelingene av `f` og
`f + e` uttrykt ved de fire verdiene `P(f = a, e = b)`. `bias_step`: er `P(f = 0) ≠ P(f = 1)`,
er også `P(f + e = 0) ≠ P(f + e = 1)` (regnet i `ℝ`: `3A + B = 3B + A` gir `A = B`).
`bias_base`: er `f` konstant på støtten, er `P(f = 0) ≠ P(f = 1)`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

lemma zmod2_01 : (0 : ZMod 2) ≠ 1 := by decide

lemma zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- **Forholdet for paret `(f, e)`.** -/
theorem pair_ratio {β : Type*} (p : PMF β) (σ : β → β) (f e : β → ZMod 2)
    (hinv : ∀ s, σ (σ s) = s) (hf : ∀ s, f (σ s) = f s) (he : ∀ s, e (σ s) = e s + 1)
    (hp : ∀ s, e s = 1 → p (σ s) = 3 * p s) (a : ZMod 2) :
    (p.map (fun s => (f s, e s))) (a, 0) = 3 * (p.map (fun s => (f s, e s))) (a, 1) := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine ((Function.Involutive.toPerm σ hinv).tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro s
  first
    | simp only [Function.Involutive.coe_toPerm, hf, he]
    | simp only [hf, he]
  by_cases h1 : (a, (1 : ZMod 2)) = (f s, e s)
  · have he1 : e s = 1 := (congrArg Prod.snd h1).symm
    have ha : a = f s := congrArg Prod.fst h1
    have h0 : (a, (0 : ZMod 2)) = (f s, e s + 1) :=
      Prod.ext ha (by show (0 : ZMod 2) = e s + 1; rw [he1]; decide)
    rw [if_pos h0, if_pos h1, hp s he1]
  · have h0 : ¬ (a, (0 : ZMod 2)) = (f s, e s + 1) := by
      intro h
      have ha : a = f s := congrArg Prod.fst h
      have hb : (0 : ZMod 2) = e s + 1 := congrArg Prod.snd h
      exact h1 (Prod.ext ha ((zmod2_s0 _).mp hb))
    rw [if_neg h0, if_neg h1, mul_zero]

lemma map_fst0 (q : PMF (ZMod 2 × ZMod 2)) : (q.map Prod.fst) 0 = q (0, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01, if_pos rfl, if_pos rfl,
    if_neg zmod2_01, if_neg zmod2_01]
  ring

lemma map_fst1 (q : PMF (ZMod 2 × ZMod 2)) : (q.map Prod.fst) 1 = q (1, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01, if_neg zmod2_01.symm,
    if_neg zmod2_01.symm, if_pos rfl, if_pos rfl]
  ring

lemma map_add0 (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 0 = q (0, 0) + q (1, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01,
    if_pos (by decide : (0 : ZMod 2) = 0 + 0), if_neg (by decide : ¬ (0 : ZMod 2) = 0 + 1),
    if_neg (by decide : ¬ (0 : ZMod 2) = 1 + 0), if_pos (by decide : (0 : ZMod 2) = 1 + 1)]
  ring

lemma map_add1 (q : PMF (ZMod 2 × ZMod 2)) :
    (q.map (fun z => z.1 + z.2)) 1 = q (1, 0) + q (0, 1) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, zmod2_univ, Finset.sum_pair zmod2_01,
    Finset.sum_pair zmod2_01, Finset.sum_pair zmod2_01,
    if_neg (by decide : ¬ (1 : ZMod 2) = 0 + 0), if_pos (by decide : (1 : ZMod 2) = 0 + 1),
    if_pos (by decide : (1 : ZMod 2) = 1 + 0), if_neg (by decide : ¬ (1 : ZMod 2) = 1 + 1)]
  ring

/-- **Skjevhetslemmaet.** -/
theorem bias_step {β : Type*} (p : PMF β) (σ : β → β) (f e : β → ZMod 2)
    (hinv : ∀ s, σ (σ s) = s) (hf : ∀ s, f (σ s) = f s) (he : ∀ s, e (σ s) = e s + 1)
    (hp : ∀ s, e s = 1 → p (σ s) = 3 * p s) (hb : (p.map f) 0 ≠ (p.map f) 1) :
    (p.map (fun s => f s + e s)) 0 ≠ (p.map (fun s => f s + e s)) 1 := by
  have hmf : p.map f = (p.map (fun s => (f s, e s))).map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  have hms : p.map (fun s => f s + e s) =
      (p.map (fun s => (f s, e s))).map (fun z => z.1 + z.2) := by
    rw [PMF.map_comp]
    rfl
  have r0 := pair_ratio p σ f e hinv hf he hp 0
  have r1 := pair_ratio p σ f e hinv hf he hp 1
  rw [hmf, map_fst0, map_fst1, r0, r1] at hb
  rw [hms, map_add0, map_add1, r0, r1]
  have hA : (p.map (fun s => (f s, e s))) (0, 1) ≠ ⊤ := PMF.apply_ne_top _ _
  have hB : (p.map (fun s => (f s, e s))) (1, 1) ≠ ⊤ := PMF.apply_ne_top _ _
  have h3A : 3 * (p.map (fun s => (f s, e s))) (0, 1) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hA
  have h3B : 3 * (p.map (fun s => (f s, e s))) (1, 1) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
  intro h
  apply hb
  have hAB : (p.map (fun s => (f s, e s))) (0, 1) = (p.map (fun s => (f s, e s))) (1, 1) := by
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add h3A hB, ENNReal.toReal_add h3B hA, ENNReal.toReal_mul,
      ENNReal.toReal_mul] at h'
    have h'' : ENNReal.toReal ((p.map (fun s => (f s, e s))) (0, 1)) =
        ENNReal.toReal ((p.map (fun s => (f s, e s))) (1, 1)) := by
      have h3 : ENNReal.toReal (3 : ENNReal) = 3 := by simp
      rw [h3] at h'
      linarith
    first
      | exact (ENNReal.toReal_eq_toReal_iff' hA hB).mp h''
      | exact (ENNReal.toReal_eq_toReal hA hB).mp h''
  rw [hAB]

/-- **Grunntilfellet:** er `f` konstant på støtten, er `P(f = 0) ≠ P(f = 1)`. -/
theorem bias_base {β : Type*} (p : PMF β) (f : β → ZMod 2) (c : ZMod 2)
    (h : ∀ s, p s ≠ 0 → f s = c) : (p.map f) 0 ≠ (p.map f) 1 := by
  rw [map_congr_supp p f (fun _ => c) h]
  have hc : p.map (fun _ => c) = PMF.pure c := PMF.map_const p c
  rw [hc, PMF.pure_apply, PMF.pure_apply]
  rcases zmod2_cases c with rfl | rfl
  · rw [if_pos rfl, if_neg zmod2_01.symm]
    exact one_ne_zero
  · rw [if_neg zmod2_01, if_pos rfl]
    exact zero_ne_one

end Hedge

#print axioms Hedge.pair_ratio
#print axioms Hedge.bias_step
#print axioms Hedge.bias_base

/-! ## Runde 83: H4, steg 6b — teleskopering for `Yb`

`AO` = de observerte nodene i `AY` utenfor `X` (der støyen teller), `AXo` = de i `X`.
`Yb_tele`: for hver tilordning er `Yb = parR a + Σ_{AO} η + Σ_{AXo} b` (hver `w ∈ AY \ Y` er
halebarn av nøyaktig én node i `AO`, `fiber_sum`). `fS_const`: på støtten til `do(x)` i
`MP true` er `b` lik `x` i `X` og `parR = gS` (`parR_g`), så `Yb + gS + Σ_{AO} η` er en
konstant som bare avhenger av `x`. -/

namespace Hedge
namespace PM

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma zmod2_tel : ∀ yb m p q : ZMod 2, yb = p + (yb + m + (p + (m + q))) + q := by decide

lemma zmod2_geq : ∀ g e q : ZMod 2, g + e + q + g + e = q := by decide

section tele3

variable (G : DAG V) (U F F' : Finset V) (D : Data V) (X Y : Finset V)

/-- De observerte nodene i `AY` utenfor `X`. -/
noncomputable def AO : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∉ X)

/-- De observerte nodene i `AY` i `X`. -/
noncomputable def AXo : Finset V := (AY G X Y).filter (fun v => v ∉ U ∧ v ∈ X)

/-- **Teleskoperingsidentiteten for `Yb`.** -/
theorem Yb_tele (hH : IsHedge G U X Y F F') (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X)
    (s : Assignment (α := Val2 U) (Finset.univ : Finset V)) :
    Yb U Y s = parR G U F (fstA U s) + ∑ v ∈ AO G U X Y, etaS G U F X Y s v +
      ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 := by
  have hTC : ∀ v, TC G U X Y v = ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter
      (fun w => tp G X Y w = v) := by
    intro v
    ext w
    simp only [TC, Finset.mem_filter]
    tauto
  have hS : ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter
      (fun w => tp G X Y w ∈ AO G U X Y) = (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y) := by
    apply Finset.filter_true_of_mem
    intro w hw
    obtain ⟨hwA, -, hwY⟩ := Finset.mem_filter.mp hw
    obtain ⟨h1, h2, h3⟩ := tp_spec G X Y hwA hwY
    exact Finset.mem_filter.mpr ⟨h1, fun hU => hroot _ hU _ h2, h3⟩
  have hRO : (AO G U X Y).filter (fun v => v ∈ RO G U F) = RO G U F := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hr
      have hrF := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      exact ⟨Finset.mem_filter.mpr ⟨hH.anc (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2,
        hH.out r hrF⟩, hr⟩
  have hYA : (AO G U X Y).filter (fun v => v ∈ Y) = Y := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hy
      exact ⟨Finset.mem_filter.mpr ⟨anc_sup (cutIn G X) Finset.univ Y hy, hYU y hy, hYX y hy⟩, hy⟩
  have hmid : (AO G U X Y).filter (fun v => v ∉ Y) =
      ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter (fun v => v ∉ X) := by
    ext v
    simp only [AO, Finset.mem_filter]
    tauto
  have hXo : ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y)).filter (fun v => ¬ v ∉ X) =
      AXo G U X Y := by
    ext v
    simp only [AXo, Finset.mem_filter, not_not]
    constructor
    · rintro ⟨⟨hA, hU, -⟩, hX⟩
      exact ⟨hA, hU, hX⟩
    · rintro ⟨hA, hU, hX⟩
      exact ⟨⟨hA, hU, fun hY => hYX v hY hX⟩, hX⟩
  have h1 : ∑ v ∈ AO G U X Y, etaS G U F X Y s v =
      ∑ v ∈ AO G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 +
        (∑ v ∈ AO G U X Y, (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) +
          ∑ v ∈ AO G U X Y, ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2) := by
    rw [Finset.sum_congr rfl (fun v _ => etaS_eq G U F X Y s v), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  have h2 : ∑ v ∈ AO G U X Y, (if v ∈ RO G U F then rd (s ⟨v, Finset.mem_univ v⟩).1 0 else 0) =
      parR G U F (fstA U s) := by
    rw [← Finset.sum_filter, hRO]
    rfl
  have h3 : ∑ v ∈ AO G U X Y, ∑ w ∈ TC G U X Y v, (s ⟨w, Finset.mem_univ w⟩).2 =
      ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y), (s ⟨w, Finset.mem_univ w⟩).2 := by
    simp only [hTC]
    rw [fiber_sum (AO G U X Y) _ (tp G X Y) (fun w => (s ⟨w, Finset.mem_univ w⟩).2), hS]
  have h4 : ∑ v ∈ AO G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 =
      ∑ v ∈ Y, (s ⟨v, Finset.mem_univ v⟩).2 +
        ∑ v ∈ (AO G U X Y).filter (fun v => v ∉ Y), (s ⟨v, Finset.mem_univ v⟩).2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (AO G U X Y) (fun v => v ∈ Y), hYA]
  have h5 : ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y), (s ⟨w, Finset.mem_univ w⟩).2 =
      ∑ v ∈ (AO G U X Y).filter (fun v => v ∉ Y), (s ⟨v, Finset.mem_univ v⟩).2 +
        ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 := by
    rw [← Finset.sum_filter_add_sum_filter_not ((AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y))
      (fun v => v ∉ X), ← hmid, hXo]
  rw [h1, h2, h3, h4, h5]
  unfold Yb
  exact zmod2_tel _ _ _ _

/-- **På støtten er `Yb + gS + Σ_{AO} η` konstant.** -/
theorem fS_const (hH : IsHedge G U X Y F F') (hD : Good G U F F' D)
    (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) (hYU : ∀ y ∈ Y, y ∉ U) (hYX : ∀ y ∈ Y, y ∉ X)
    (x : Assignment (α := Val2 U) X) (s : Assignment (α := Val2 U) (Finset.univ : Finset V))
    (hs : (doModel (MP G U F F' D X Y true) X x).fullJoint s ≠ 0) :
    Yb U Y s + gS G U F F' D (fstA U s) + ∑ v ∈ AO G U X Y, etaS G U F X Y s v =
      ∑ v ∈ AXo G U X Y, (if h : v ∈ X then (x ⟨v, h⟩).2 else 0) := by
  rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff] at hs
  have hX : ∀ v (hv : v ∈ X), s ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩ := by
    intro v hv
    have h := hs v (Finset.mem_univ v)
    rw [kfac_doModel, dif_pos hv] at h
    by_contra hne
    exact h (if_neg hne)
  have hsA : (doModel (M G U F F' D true) X (fun w => (x w).1)).fullJoint (fstA U s) ≠ 0 := by
    rw [fullJoint_apply_prod, Finset.prod_ne_zero_iff]
    intro v _
    rw [kfac_doModel]
    by_cases hv : v ∈ X
    · rw [dif_pos hv, if_pos]
      · exact one_ne_zero
      · exact congrArg Prod.fst (hX v hv)
    · rw [dif_neg hv]
      have h := hs v (Finset.mem_univ v)
      rw [kfac_doModel, dif_neg hv, kfac2_eq] at h
      exact left_ne_zero_of_mul h
  have hpar := parR_g G U F F' D hH hD hroot (fun w => (x w).1) (fstA U s) hsA
  have hq : ∑ v ∈ AXo G U X Y, (s ⟨v, Finset.mem_univ v⟩).2 =
      ∑ v ∈ AXo G U X Y, (if h : v ∈ X then (x ⟨v, h⟩).2 else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvX := (Finset.mem_filter.mp hv).2.2
    rw [dif_pos hvX, hX v hvX]
  rw [Yb_tele G U F F' X Y hH hroot hYU hYX s, hpar, hq]
  exact zmod2_geq _ _ _

end tele3

end PM
end Hedge

#print axioms Hedge.PM.Yb_tele
#print axioms Hedge.PM.fS_const
