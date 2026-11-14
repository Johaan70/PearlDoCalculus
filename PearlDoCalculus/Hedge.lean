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
