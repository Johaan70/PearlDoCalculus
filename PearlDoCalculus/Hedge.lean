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
