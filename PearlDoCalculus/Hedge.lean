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
