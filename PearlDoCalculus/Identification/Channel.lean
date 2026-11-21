import PearlDoCalculus.Identification.RootTree

/-!
# The channel step and whole directed paths

Shpitser and Pearl only require the roots of a hedge to be ancestors of `Y`. This file
moves a non-identifiable effect one step along a directed edge `ρ → y` (round 18), and
then along a whole directed path (round 19).

How the proof goes: the models of the smaller graph are kept, the new node `y` gets a
noisy channel from `ρ`, and the channel is invertible, so equal answers after the step
give equal answers before it.

Main results:
* `Channel.channel_step`: the effect on `Y ∖ {ρ} ∪ {y}` is not identifiable.
* `Channel.not_ident_of_sub`: more edges never make an effect identifiable.
* `Channel.path_not_identifiable`: the step repeated along a directed path.
* `Channel.rootTree_tail`: a hedge together with tails at its roots.

(The comments of the rounds below are still in Norwegian.)
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 18: kanalsteget

Shpitser og Pearl krever bare at røttene i en hedge er *forfedre* til `Y`. Dette
steget fører en ikke-identifiserbar effekt ett ledd videre langs en rettet kant
`ρ → y`: står `y` isolert i en delgraf `G'` der effekten på `Y ∋ ρ` ikke er
identifiserbar, så er effekten på `Y ∖ {ρ} ∪ {y}` ikke identifiserbar i `G`, når
`y` observeres gjennom en støyende kanal fra `ρ`.

* Modellene fra `G'` beholdes, og `y` får kjernen `chan(ρ)`. Siden ingen leser `y`,
  er fellesfordelingen den gamle marginalen uten `y`, utvidet med kanalen
  (`joint_ins`). Marginalene får samme form (`marg_ins`).
* Like observasjoner og positivitet går derfor rett over.
* Kanalen er inverterbar: fra fordelingen på `(Y ∖ {ρ}, y)` kan fordelingen på `Y`
  regnes tilbake (`Φ_inj`, et 2 × 2-likningssystem). Like svar etter steget gir
  like svar før steget, i strid med antakelsen. -/

namespace Identification
namespace Channel

open HedgeChain (ev)
open MultiRoot (ext ext_restrict)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Å utvide en tilordning med én node -/

/-- `b` på `T`, utvidet med verdien `c` i `w`, som tilordning på `U ⊆ insert w T`. -/
def ins (w : V) {T U : Finset V} (hU : U ⊆ insert w T)
    (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    Assignment (α := fun _ : V => Bool) U :=
  fun v => if h : v.1 = w then c else b ⟨v.1, (Finset.mem_insert.mp (hU v.2)).resolve_left h⟩

lemma ins_eq_iff (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool)
    (s : Assignment (α := fun _ : V => Bool) U) :
    ins w hU b c = s ↔ b = s.restrict hTU ∧ c = s ⟨w, hw⟩ := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      have hvw : v ≠ w := fun e => hwT (e ▸ hv)
      simp [ins, Assignment.restrict, hvw]
    · simp [ins]
  · rintro ⟨rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases h : v = w
    · subst h
      simp [ins]
    · simp [ins, Assignment.restrict, h]

lemma ins_restrict (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (s : Assignment (α := fun _ : V => Bool) U) :
    ins w hU (s.restrict hTU) (s ⟨w, hw⟩) = s :=
  (ins_eq_iff w hU hTU hw hwT _ _ s).mpr ⟨rfl, rfl⟩

lemma ins_restrict_T (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    (ins w hU b c).restrict hTU = b :=
  ((ins_eq_iff w hU hTU hw hwT b c _).mp rfl).1.symm

lemma ins_at (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hw : w ∈ U)
    (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) : (ins w hU b c) ⟨w, hw⟩ = c := by
  simp [ins]

lemma ins_inj (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) {b b' : Assignment (α := fun _ : V => Bool) T} {c c' : Bool}
    (h : ins w hU b c = ins w hU b' c') : b = b' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := (ins_eq_iff w hU hTU hw hwT b c _).mp h
  rw [ins_restrict_T w hU hTU hw hwT] at h1
  rw [ins_at w hU hw] at h2
  exact ⟨h1, h2⟩

lemma restrict_ins (w : V) {T U T' U' : Finset V} (hU : U ⊆ insert w T) (hU' : U' ⊆ insert w T')
    (hUU : U' ⊆ U) (hT : T' ⊆ T) (b : Assignment (α := fun _ : V => Bool) T) (c : Bool) :
    (ins w hU b c).restrict hUU = ins w hU' (b.restrict hT) c := by
  funext ⟨v, hv⟩
  by_cases h : v = w
  · subst h
    simp [ins, Assignment.restrict]
  · simp [ins, Assignment.restrict, h]

/-- Summen over tilordninger av formen `ins w b c` faller sammen til ett ledd. -/
lemma tsum_ins (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (f : Assignment (α := fun _ : V => Bool) T → Bool → ℝ≥0∞)
    (s : Assignment (α := fun _ : V => Bool) U) :
    (∑' b, ∑' c, if s = ins w hU b c then f b c else 0) = f (s.restrict hTU) (s ⟨w, hw⟩) := by
  have key : ∀ b c, s = ins w hU b c ↔ b = s.restrict hTU ∧ c = s ⟨w, hw⟩ := fun b c =>
    eq_comm.trans (ins_eq_iff w hU hTU hw hwT b c s)
  rw [tsum_eq_single (s.restrict hTU)]
  · rw [tsum_eq_single (s ⟨w, hw⟩)]
    · rw [if_pos ((key _ _).mpr ⟨rfl, rfl⟩)]
    · intro c hc
      rw [if_neg (fun h => hc ((key _ _).mp h).2)]
  · intro b hb
    exact ENNReal.tsum_eq_zero.mpr (fun c => if_neg (fun h => hb ((key _ _).mp h).1))

/-- Bytte av summasjonsvariabel: en tilordning på `U` er det samme som en på `T`
pluss en verdi i `w`. -/
lemma tsum_reindex (w : V) {T U : Finset V} (hU : U ⊆ insert w T) (hTU : T ⊆ U) (hw : w ∈ U)
    (hwT : w ∉ T) (g : Assignment (α := fun _ : V => Bool) U → ℝ≥0∞) :
    (∑' s, g s) = ∑' b, ∑' c, g (ins w hU b c) := by
  calc (∑' s, g s) = ∑' s, ∑' b, ∑' c, (if s = ins w hU b c then g (ins w hU b c) else 0) := by
        refine tsum_congr (fun s => ?_)
        rw [tsum_ins w hU hTU hw hwT (fun b c => g (ins w hU b c)) s]
        exact (congrArg g (ins_restrict w hU hTU hw hwT s)).symm
    _ = ∑' b, ∑' c, ∑' s, (if s = ins w hU b c then g (ins w hU b c) else 0) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr (fun b => ?_)
        rw [ENNReal.tsum_comm]
    _ = ∑' b, ∑' c, g (ins w hU b c) := by
        refine tsum_congr (fun b => tsum_congr (fun c => ?_))
        rw [tsum_eq_single (ins w hU b c)]
        · rw [if_pos rfl]
        · intro s hs
          rw [if_neg hs]

/-! ### Et blad med kanal -/

/-- Alle noder unntatt `y`. -/
abbrev Ay (y : V) : Finset V := Finset.univ.erase y

lemma memA {ρ y : V} (h : ρ ≠ y) : ρ ∈ Ay y := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩

lemma univ_sub (y : V) : (Finset.univ : Finset V) ⊆ insert y (Ay y) := by
  intro v _
  by_cases h : v = y
  · rw [h]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (memA h)

lemma notA (y : V) : y ∉ Ay y := fun h => (Finset.mem_erase.mp h).1 rfl

section Leaf

variable {H H1 : DAG V} (K : H.CausalModel (fun _ => Bool)) (K1 : H1.CausalModel (fun _ => Bool))

/-- **Fellesfordelingen med bladet.** Leser ingen `y`, og har `y` kjernen `chan(ρ)`,
er fellesfordelingen marginalen uten `y`, utvidet med kanalen. -/
lemma joint_ins {ρ y : V} (hρy : ρ ≠ y)
    (hanc : ∀ v ∈ Ay y, ∀ a, H.edge a v → a ∈ Ay y)
    (hoff : ∀ s v, v ≠ y → kfac K1 Finset.univ s v = kfac K Finset.univ s v)
    (hyk : ∀ s, kfac K1 Finset.univ s y = Bow.chan (ev s ρ) (ev s y)) :
    K1.fullJoint = (K.marginal (Ay y)).bind (fun b =>
      (Bow.chan (b ⟨ρ, memA hρy⟩)).map (ins y (univ_sub y) b)) := by
  ext s
  rw [fullJoint_apply_prod, PMF.bind_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ y), hyk]
  have hp : ∏ v ∈ Ay y, kfac K1 Finset.univ s v =
      K.marginal (Ay y) (s.restrict (Finset.subset_univ _)) := by
    rw [marginal_ancestral_apply K (Ay y) hanc]
    refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [hoff s v (Finset.mem_erase.mp hv).1,
      kfac_restrict K (Finset.subset_univ _) s hv (DAG.parents_subset_of_closed hanc v hv)]
  rw [hp]
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_ins y (univ_sub y) (Finset.subset_univ _) (Finset.mem_univ y) (notA y)
    (fun b c => K.marginal (Ay y) b * Bow.chan (b ⟨ρ, memA hρy⟩) c) s]
  exact mul_comm _ _

/-- **Marginalene med bladet.** For `ρ ∈ S` og `y ∉ S`. -/
lemma marg_ins {ρ y : V} (hρy : ρ ≠ y)
    (hanc : ∀ v ∈ Ay y, ∀ a, H.edge a v → a ∈ Ay y)
    (hoff : ∀ s v, v ≠ y → kfac K1 Finset.univ s v = kfac K Finset.univ s v)
    (hyk : ∀ s, kfac K1 Finset.univ s y = Bow.chan (ev s ρ) (ev s y))
    (S : Finset V) (hρS : ρ ∈ S) (hyS : y ∉ S) :
    K1.marginal (insert y S) = (K.marginal S).bind (fun a =>
      (Bow.chan (a ⟨ρ, hρS⟩)).map (ins y (Finset.Subset.refl (insert y S)) a)) := by
  have hSA : S ⊆ Ay y := fun v hv =>
    Finset.mem_erase.mpr ⟨fun e => hyS (e ▸ hv), Finset.mem_univ _⟩
  show K1.fullJoint.map (Assignment.restrict (Finset.subset_univ _)) = _
  rw [joint_ins K K1 hρy hanc hoff hyk, PMF.map_bind]
  have hcomp : ∀ b : Assignment (α := fun _ : V => Bool) (Ay y),
      ((Bow.chan (b ⟨ρ, memA hρy⟩)).map (ins y (univ_sub y) b)).map
          (Assignment.restrict (Finset.subset_univ (insert y S))) =
        (Bow.chan ((b.restrict hSA) ⟨ρ, hρS⟩)).map
          (ins y (Finset.Subset.refl (insert y S)) (b.restrict hSA)) := by
    intro b
    rw [PMF.map_comp]
    congr 1
  simp only [hcomp]
  rw [← marginal_restrict K hSA, PMF.bind_map]
  all_goals rfl

end Leaf

/-- Verdien av utvidelsen i ett punkt. -/
lemma bind_ins_apply {ρ y : V} {S : Finset V} (hρS : ρ ∈ S) (hyS : y ∉ S)
    (P : PMF (Assignment (α := fun _ : V => Bool) S))
    (s : Assignment (α := fun _ : V => Bool) (insert y S)) :
    (P.bind (fun a => (Bow.chan (a ⟨ρ, hρS⟩)).map (ins y (Finset.Subset.refl (insert y S)) a))) s =
      P (s.restrict (Finset.subset_insert y S)) *
        Bow.chan (s ⟨ρ, Finset.mem_insert_of_mem hρS⟩) (s ⟨y, Finset.mem_insert_self y S⟩) := by
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_ins y (Finset.Subset.refl _) (Finset.subset_insert y S) (Finset.mem_insert_self y S)
    hyS (fun a c => P a * Bow.chan (a ⟨ρ, hρS⟩) c) s]
  all_goals rfl

/-! ### Kanalen er inverterbar -/

/-- Fordelingen på `Y` sendt gjennom kanalen `ρ ↦ y`, med `ρ` summert ut. -/
noncomputable def Φ {ρ : V} {Y : Finset V} (hρY : ρ ∈ Y) (y : V)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y)) :
    PMF (Assignment (α := fun _ : V => Bool) (insert y (Y.erase ρ))) :=
  P.bind (fun a => (Bow.chan (a ⟨ρ, hρY⟩)).map
    (ins y (Finset.Subset.refl _) (a.restrict (Finset.erase_subset ρ Y))))

lemma hYW {ρ : V} {Y : Finset V} (hρY : ρ ∈ Y) : Y ⊆ insert ρ (Y.erase ρ) := fun v hv => by
  rw [Finset.insert_erase hρY]
  exact hv

lemma hρW (ρ : V) (Y : Finset V) : ρ ∉ Y.erase ρ := fun h => (Finset.mem_erase.mp h).1 rfl

lemma map_bind_ins {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y)) :
    (P.bind (fun a => (Bow.chan (a ⟨ρ, hρY⟩)).map (ins y (Finset.Subset.refl (insert y Y)) a))).map
        (Assignment.restrict (Finset.insert_subset_insert y (Finset.erase_subset ρ Y))) =
      Φ hρY y P := by
  rw [PMF.map_bind]
  unfold Φ
  congr 1
  funext a
  rw [PMF.map_comp]
  congr 1

lemma Φ_apply {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y) (hyY : y ∉ Y)
    (P : PMF (Assignment (α := fun _ : V => Bool) Y))
    (w : Assignment (α := fun _ : V => Bool) (Y.erase ρ)) (c : Bool) :
    Φ hρY y P (ins y (Finset.Subset.refl _) w c) =
      P (ins ρ (hYW hρY) w false) * Bow.chan false c +
        P (ins ρ (hYW hρY) w true) * Bow.chan true c := by
  have hyW : y ∉ Y.erase ρ := fun h => hyY (Finset.mem_of_mem_erase h)
  have inner : ∀ a : Assignment (α := fun _ : V => Bool) Y,
      (∑' d, if ins y (Finset.Subset.refl _) w c =
          ins y (Finset.Subset.refl _) (a.restrict (Finset.erase_subset ρ Y)) d
        then Bow.chan (a ⟨ρ, hρY⟩) d else 0) =
      if w = a.restrict (Finset.erase_subset ρ Y) then Bow.chan (a ⟨ρ, hρY⟩) c else 0 := by
    intro a
    rw [tsum_eq_single c]
    · by_cases hw : w = a.restrict (Finset.erase_subset ρ Y)
      · subst hw
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun e => hw (ins_inj y (Finset.Subset.refl _) (Finset.subset_insert y _)
          (Finset.mem_insert_self y _) hyW e).1), if_neg hw]
    · intro d hd
      exact if_neg (fun e => hd (ins_inj y (Finset.Subset.refl _) (Finset.subset_insert y _)
        (Finset.mem_insert_self y _) hyW e).2.symm)
  unfold Φ
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, inner]
  rw [tsum_reindex ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y)]
  simp only [ins_restrict_T ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y),
    ins_at ρ (hYW hρY) hρY]
  rw [tsum_eq_single w]
  · have hs : ∀ r : Bool, (P (ins ρ (hYW hρY) w r) * if w = w then Bow.chan r c else 0) =
        P (ins ρ (hYW hρY) w r) * Bow.chan r c := fun r => by rw [if_pos rfl]
    simp only [hs]
    rw [tsum_fintype, Fintype.sum_bool]
    simp
    exact add_comm _ _
  · intro w' hw'
    exact ENNReal.tsum_eq_zero.mpr (fun r => by rw [if_neg (Ne.symm hw'), mul_zero])

/-- To likninger med kanalens koeffisienter bestemmer de to ukjente. -/
lemma lin2 {p q p' q' : ℝ≥0∞} (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp' : p' ≠ ⊤) (hq' : q' ≠ ⊤)
    (h1 : p * (3 / 4) + q * (1 / 4) = p' * (3 / 4) + q' * (1 / 4))
    (h2 : p * (1 / 4) + q * (3 / 4) = p' * (1 / 4) + q' * (3 / 4)) : p = p' ∧ q = q' := by
  have k1 : (1 / 4 : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp) (by simp)
  have k3 : (3 / 4 : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp) (by simp)
  have r1 : (1 / 4 : ℝ≥0∞).toReal = 1 / 4 := by
    norm_num [ENNReal.toReal_div]
  have r3 : (3 / 4 : ℝ≥0∞).toReal = 3 / 4 := by
    norm_num [ENNReal.toReal_div]
  have e1 := congrArg ENNReal.toReal h1
  have e2 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp k3) (ENNReal.mul_ne_top hq k1),
    ENNReal.toReal_add (ENNReal.mul_ne_top hp' k3) (ENNReal.mul_ne_top hq' k1),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, r1, r3] at e1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp k1) (ENNReal.mul_ne_top hq k3),
    ENNReal.toReal_add (ENNReal.mul_ne_top hp' k1) (ENNReal.mul_ne_top hq' k3),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, r1, r3] at e2
  have ep : p.toReal = p'.toReal := by linarith
  have eq : q.toReal = q'.toReal := by linarith
  constructor
  · exact (ENNReal.toReal_eq_toReal_iff' hp hp').mp ep
  · exact (ENNReal.toReal_eq_toReal_iff' hq hq').mp eq

/-- **Kanalen er inverterbar.** -/
lemma Φ_inj {ρ y : V} {Y : Finset V} (hρY : ρ ∈ Y) (hyY : y ∉ Y)
    (P1 P2 : PMF (Assignment (α := fun _ : V => Bool) Y)) (h : Φ hρY y P1 = Φ hρY y P2) :
    P1 = P2 := by
  ext a
  have key : ∀ c, P1 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) false) * Bow.chan false c +
      P1 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) true) * Bow.chan true c =
      P2 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) false) * Bow.chan false c +
      P2 (ins ρ (hYW hρY) (a.restrict (Finset.erase_subset ρ Y)) true) * Bow.chan true c :=
    fun c => by rw [← Φ_apply hρY hyY, ← Φ_apply hρY hyY, h]
  have k0 := key false
  have k1 := key true
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show false = false from rfl),
    if_neg (show ¬ (false = true) by decide)] at k0
  rw [Bow.chan_apply, Bow.chan_apply, if_neg (show ¬ (true = false) by decide),
    if_pos (show true = true from rfl)] at k1
  have hl := lin2 (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _) k0 k1
  have ha := (ins_restrict ρ (hYW hρY) (Finset.erase_subset ρ Y) hρY (hρW ρ Y) a).symm
  rw [ha]
  cases hr : a ⟨ρ, hρY⟩
  · exact hl.1
  · exact hl.2

/-! ### Grafen og modellene -/

/-- Ett kanalsteg: `y` står isolert i `G'`, og `ρ → y` er en kant i `G`. -/
structure Step (G' G : DAG V) where
  ρ : V
  y : V
  hsub : ∀ a b, G'.edge a b → G.edge a b
  hρy : G.edge ρ y
  hiso : ∀ a, ¬ G'.edge a y ∧ ¬ G'.edge y a

namespace Step

variable {G' G : DAG V} (D : Step G' G)

lemma hne : D.ρ ≠ D.y := BowGen.ne_of_edge D.hρy

/-- `G'` med kanten `ρ → y`; rangen lånes fra `G`. -/
noncomputable def G1 : DAG V where
  edge a b := G'.edge a b ∨ (a = D.ρ ∧ b = D.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro a b h
    rcases h with h | ⟨h1, h2⟩
    · exact G.rank_strict_mono _ _ (D.hsub _ _ h)
    · rw [h1, h2]
      exact G.rank_strict_mono _ _ D.hρy

lemma edge1 {a b : V} : D.G1.edge a b ↔ G'.edge a b ∨ (a = D.ρ ∧ b = D.y) := Iff.rfl

lemma par'_sub {u v : V} (h : u ∈ G'.parents v) : u ∈ D.G1.parents v :=
  DAG.mem_parents.mpr (D.edge1.mpr (Or.inl (DAG.mem_parents.mp h)))

lemma sub1 : ∀ v, D.G1.parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.mem_parents]
  rcases (D.edge1.mp (DAG.mem_parents.mp ha)) with h | ⟨h1, h2⟩
  · exact D.hsub _ _ h
  · rw [h1, h2]
    exact D.hρy

lemma hρpar : D.ρ ∈ D.G1.parents D.y := DAG.mem_parents.mpr (D.edge1.mpr (Or.inr ⟨rfl, rfl⟩))

/-- Den gamle modellen, med kanalen `chan(ρ)` i `y`. -/
noncomputable def N (M : G'.CausalModel (fun _ => Bool)) : D.G1.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa => if v = D.y then Bow.chan (ext pa D.ρ)
    else M.kernel v (fun u => pa ⟨u.1, D.par'_sub u.2⟩)

lemma N_y (M : G'.CausalModel (fun _ => Bool))
    (pa : Assignment (α := fun _ : V => Bool) (D.G1.parents D.y)) :
    (D.N M).kernel D.y pa = Bow.chan (ext pa D.ρ) := by
  simp [N]

lemma N_o (M : G'.CausalModel (fun _ => Bool)) {v : V} (hv : v ≠ D.y)
    (pa : Assignment (α := fun _ : V => Bool) (D.G1.parents v)) :
    (D.N M).kernel v pa = M.kernel v (fun u => pa ⟨u.1, D.par'_sub u.2⟩) := by
  simp [N, hv]

lemma ancG' : ∀ v ∈ Ay D.y, ∀ a, G'.edge a v → a ∈ Ay D.y := by
  intro v _ a ha
  exact Finset.mem_erase.mpr ⟨fun e => (D.hiso v).2 (e ▸ ha), Finset.mem_univ _⟩

lemma ancCut (X : Finset V) : ∀ v ∈ Ay D.y, ∀ a, (cutIn G' X).edge a v → a ∈ Ay D.y :=
  fun v hv a ha => D.ancG' v hv a (show G'.edge a v ∧ v ∉ X from ha).1

lemma hoff (M : G'.CausalModel (fun _ => Bool)) :
    ∀ s v, v ≠ D.y → kfac (D.N M) Finset.univ s v = kfac M Finset.univ s v := by
  intro s v hv
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ, D.N_o M hv]
  all_goals rfl

lemma hyk (M : G'.CausalModel (fun _ => Bool)) :
    ∀ s, kfac (D.N M) Finset.univ s D.y = Bow.chan (ev s D.ρ) (ev s D.y) := by
  intro s
  rw [DoAudit.kfac_univ, D.N_y M, ext_restrict s D.hρpar]
  all_goals rfl

lemma hoff_do (M : G'.CausalModel (fun _ => Bool)) (X : Finset V)
    (x0 : Assignment (α := fun _ : V => Bool) X) :
    ∀ s v, v ≠ D.y → kfac (doModel (D.N M) X x0) Finset.univ s v =
      kfac (doModel M X x0) Finset.univ s v := by
  intro s v hv
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hvX : v ∈ X
  · simp only [doModel, dif_pos hvX]
  · simp only [doModel, dif_neg hvX]
    rw [D.N_o M hv]
    all_goals rfl

lemma hyk_do (M : G'.CausalModel (fun _ => Bool)) (X : Finset V) (hyX : D.y ∉ X)
    (x0 : Assignment (α := fun _ : V => Bool) X) :
    ∀ s, kfac (doModel (D.N M) X x0) Finset.univ s D.y = Bow.chan (ev s D.ρ) (ev s D.y) := by
  intro s
  rw [DoAudit.kfac_univ]
  simp only [doModel, dif_neg hyX]
  rw [D.N_y M]
  simp [MultiRoot.ext, D.hρpar, Assignment.restrict, ev]

end Step

/-! ### Kanalsteget -/

/-- **Kanalsteget.** Er effekten på `Y ∋ ρ` ikke identifiserbar i `G'`, der `y` står
isolert, så er effekten på `Y ∖ {ρ} ∪ {y}` ikke identifiserbar i `G`, med `y` observert. -/
theorem channel_step {G' G : DAG V} (D : Step G' G) {O X Y : Finset V}
    (hρO : D.ρ ∈ O) (hyO : D.y ∉ O) (hρY : D.ρ ∈ Y) (hyY : D.y ∉ Y) (hyX : D.y ∉ X)
    (hYX : Disjoint Y X) (h : ¬ Identifiable G' (fun _ => Bool) O X Y) :
    ¬ Identifiable G (fun _ => Bool) (insert D.y O) X (insert D.y (Y.erase D.ρ)) := by
  intro hI
  apply h
  intro M1 M2 hM hpos t
  -- Observasjonene
  have hL : ∀ M : G'.CausalModel (fun _ => Bool),
      (Completeness.liftSub D.sub1 (D.N M)).marginal (insert D.y O) =
        (M.marginal O).bind (fun a =>
          (Bow.chan (a ⟨D.ρ, hρO⟩)).map (ins D.y (Finset.Subset.refl (insert D.y O)) a)) := by
    intro M
    rw [Completeness.marginal_eq_of_kfac _ (D.N M) (BowGen.kfac_liftG D.sub1 (D.N M))
      (insert D.y O)]
    exact marg_ins M (D.N M) D.hne D.ancG' (D.hoff M) (D.hyk M) O hρO hyO
  have hobs : (Completeness.liftSub D.sub1 (D.N M1)).marginal (insert D.y O) =
      (Completeness.liftSub D.sub1 (D.N M2)).marginal (insert D.y O) := by
    rw [hL M1, hL M2, hM]
  have hpos' : ∀ a, (Completeness.liftSub D.sub1 (D.N M1)).marginal (insert D.y O) a ≠ 0 := by
    intro a
    rw [hL M1, bind_ins_apply hρO hyO]
    exact mul_ne_zero (hpos _) (Bow.chan_ne_zero _ _)
  -- Intervensjonene
  have hd' : Disjoint (insert D.y (Y.erase D.ρ)) X := by
    rw [Finset.disjoint_insert_left]
    exact ⟨hyX, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYX⟩
  have hdo : ∀ x0 : Assignment (α := fun _ : V => Bool) X,
      (doModel (Completeness.liftSub D.sub1 (D.N M1)) X x0).marginal (insert D.y (Y.erase D.ρ)) =
        (doModel (Completeness.liftSub D.sub1 (D.N M2)) X x0).marginal
          (insert D.y (Y.erase D.ρ)) := by
    intro x0
    ext a
    have e := hI _ _ hobs hpos' (a.join x0)
    rw [Assignment.restrict_join_right a x0
        (fun v hY hX => (Finset.disjoint_left.mp hd' hY hX).elim),
      Assignment.restrict_join_left] at e
    exact e
  have hT : ∀ (M : G'.CausalModel (fun _ => Bool)) (x0 : Assignment (α := fun _ : V => Bool) X),
      (doModel (Completeness.liftSub D.sub1 (D.N M)) X x0).marginal (insert D.y (Y.erase D.ρ)) =
        Φ hρY D.y ((doModel M X x0).marginal Y) := by
    intro M x0
    rw [Completeness.marginal_eq_of_kfac _ (doModel (D.N M) X x0)
        (BowGen.kfac_lift_doG D.sub1 (D.N M) X x0) _,
      ← marginal_restrict (doModel (D.N M) X x0)
        (Finset.insert_subset_insert D.y (Finset.erase_subset D.ρ Y)),
      marg_ins (doModel M X x0) (doModel (D.N M) X x0) D.hne (D.ancCut X) (D.hoff_do M X x0)
        (D.hyk_do M X hyX x0) Y hρY hyY]
    exact map_bind_ins hρY _
  have hx := hdo (t.restrict (show X ⊆ Y ∪ X by intro v hv; simp only [Finset.mem_union]; tauto))
  rw [hT M1, hT M2] at hx
  have e := Φ_inj hρY hyY _ _ hx
  exact congrArg (fun P : PMF (Assignment (α := fun _ : V => Bool) Y) =>
    P (t.restrict (show Y ⊆ Y ∪ X by intro v hv; simp only [Finset.mem_union]; tauto))) e

end Channel
end Identification

#print axioms Identification.Channel.channel_step

/-! ## Runde 19: en hel sti

Kanalsteget fra runde 18 gjentas langs en rettet sti `ρ → p₁ → … → p_m`. Før stien
legges på, står stinodene isolert (`isoSet`). Hvert steg legger på én kant, og til slutt
løftes resultatet til hele `G` (`not_ident_of_sub`: flere kanter gjør aldri en effekt
identifiserbar). Resultat: `ρ` i `Y` kan byttes ut med stiens endepunkt.

Flere disjunkte stier fra ulike røtter håndteres ved å bruke teoremet én gang per sti,
med grafen der de andre stiene ennå er isolert. Stier som møtes, er ikke dekket. -/

namespace Identification
namespace Channel

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Flere kanter skader aldri.** Er effekten ikke identifiserbar i en delgraf, er den
heller ikke identifiserbar i hele grafen. -/
theorem not_ident_of_sub {H G : DAG V} (hsub : ∀ a b, H.edge a b → G.edge a b)
    {O X Y : Finset V} (h : ¬ Identifiable H (fun _ => Bool) O X Y) :
    ¬ Identifiable G (fun _ => Bool) O X Y := by
  intro hG
  apply h
  intro M1 M2 hM hpos t
  have hp : ∀ v, H.parents v ⊆ G.parents v := fun v a ha => by
    simp only [DAG.mem_parents] at ha ⊢
    exact hsub _ _ ha
  have hm : ∀ (M : H.CausalModel (fun _ => Bool)) (S : Finset V),
      (Completeness.liftSub hp M).marginal S = M.marginal S := fun M S =>
    Completeness.marginal_eq_of_kfac _ M (BowGen.kfac_liftG hp M) S
  have hd : ∀ (M : H.CausalModel (fun _ => Bool)) (x0 : Assignment (α := fun _ : V => Bool) X)
      (S : Finset V), (doModel (Completeness.liftSub hp M) X x0).marginal S =
        (doModel M X x0).marginal S := fun M x0 S =>
    Completeness.marginal_eq_of_kfac _ _ (BowGen.kfac_lift_doG hp M X x0) S
  have e := hG (Completeness.liftSub hp M1) (Completeness.liftSub hp M2)
    (by rw [hm, hm]; exact hM) (by intro a; rw [hm]; exact hpos a) t
  rw [hd, hd] at e
  exact e

/-- `G` uten kanter som berører `S`. -/
noncomputable def isoSet (G : DAG V) (S : Finset V) : DAG V where
  edge a b := G.edge a b ∧ a ∉ S ∧ b ∉ S
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := fun a b h => G.rank_strict_mono a b h.1

lemma isoSet_edge {G : DAG V} {S : Finset V} {a b : V} :
    (isoSet G S).edge a b ↔ G.edge a b ∧ a ∉ S ∧ b ∉ S := Iff.rfl

/-- `ρ → p₁ → … → p_m` er en rettet sti i `G`. -/
def IsPath (G : DAG V) : V → List V → Prop
  | _, [] => True
  | ρ, p :: rest => G.edge ρ p ∧ IsPath G p rest

/-- Stiens endepunkt. -/
def lastOf : V → List V → V
  | ρ, [] => ρ
  | _, p :: rest => lastOf p rest

/-- **En hel sti.** Er effekten på `Y ∋ ρ` ikke identifiserbar når stien `ρ → p₁ → … → p_m`
er fjernet, så er effekten på `Y ∖ {ρ} ∪ {p_m}` ikke identifiserbar i `G`, med stinodene
observert. -/
theorem path_not_identifiable {G : DAG V} {X : Finset V} (ps : List V) :
    ∀ (ρ : V) (O Y : Finset V), IsPath G ρ ps → (ρ :: ps).Nodup → ρ ∈ O → ρ ∈ Y →
      (∀ p ∈ ps, p ∉ O ∧ p ∉ Y ∧ p ∉ X) → Disjoint Y X →
      ¬ Identifiable (isoSet G ps.toFinset) (fun _ => Bool) O X Y →
      ¬ Identifiable G (fun _ => Bool) (O ∪ ps.toFinset) X (insert (lastOf ρ ps) (Y.erase ρ)) := by
  induction ps with
  | nil =>
    intro ρ O Y _ _ _ hρY _ _ h
    simp only [lastOf, List.toFinset_nil, Finset.union_empty, Finset.insert_erase hρY]
    exact not_ident_of_sub (fun a b hab => (isoSet_edge.mp hab).1) h
  | cons p1 rest ih =>
    intro ρ O Y hP hnd hρO hρY hps hYX h
    obtain ⟨hρp, hP'⟩ := hP
    have hnd' : (p1 :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have hρnot : ρ ∉ p1 :: rest := (List.nodup_cons.mp hnd).1
    have hp1rest : p1 ∉ rest := (List.nodup_cons.mp hnd').1
    obtain ⟨hp1O, hp1Y, hp1X⟩ := hps p1 (by simp)
    have hp1S : p1 ∈ (p1 :: rest).toFinset := by simp
    -- Ett kanalsteg: p₁ legges på
    let D : Step (isoSet G (p1 :: rest).toFinset) (isoSet G rest.toFinset) :=
      { ρ := ρ
        y := p1
        hsub := fun a b hab => by
          obtain ⟨h1, h2, h3⟩ := isoSet_edge.mp hab
          refine isoSet_edge.mpr ⟨h1, fun ha => h2 ?_, fun hb => h3 ?_⟩
          · simp only [List.mem_toFinset, List.mem_cons] at ha ⊢
            exact Or.inr ha
          · simp only [List.mem_toFinset, List.mem_cons] at hb ⊢
            exact Or.inr hb
        hρy := isoSet_edge.mpr ⟨hρp,
          fun h => hρnot (List.mem_cons_of_mem _ (List.mem_toFinset.mp h)),
          fun h => hp1rest (List.mem_toFinset.mp h)⟩
        hiso := fun a => ⟨fun hab => (isoSet_edge.mp hab).2.2 hp1S,
          fun hab => (isoSet_edge.mp hab).2.1 hp1S⟩ }
    have hs1 : ¬ Identifiable (isoSet G rest.toFinset) (fun _ => Bool) (insert p1 O) X
        (insert p1 (Y.erase ρ)) :=
      channel_step D hρO hp1O hρY hp1Y hp1X hYX h
    -- Resten av stien
    have hps' : ∀ p ∈ rest, p ∉ insert p1 O ∧ p ∉ insert p1 (Y.erase ρ) ∧ p ∉ X := by
      intro p hp
      obtain ⟨hO, hY, hX⟩ := hps p (List.mem_cons_of_mem _ hp)
      have hne : p ≠ p1 := fun e => hp1rest (e ▸ hp)
      refine ⟨?_, ?_, hX⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hO⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨hne, fun h => hY (Finset.mem_of_mem_erase h)⟩
    have hYX' : Disjoint (insert p1 (Y.erase ρ)) X :=
      Finset.disjoint_insert_left.mpr
        ⟨hp1X, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYX⟩
    have hrest := ih p1 (insert p1 O) (insert p1 (Y.erase ρ)) hP' hnd'
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) hps' hYX' hs1
    -- Mengdene på riktig form
    have e1 : O ∪ (p1 :: rest).toFinset = insert p1 O ∪ rest.toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    have e2 : (insert p1 (Y.erase ρ)).erase p1 = Y.erase ρ :=
      Finset.erase_insert (fun h => hp1Y (Finset.mem_of_mem_erase h))
    rw [e1]
    show ¬ Identifiable G (fun _ => Bool) (insert p1 O ∪ rest.toFinset) X
      (insert (lastOf p1 rest) (Y.erase ρ))
    rw [← e2]
    exact hrest

/-- **Hedge med hale.** En `RT`-hedge i grafen uten stien, og en rettet sti fra en av
røttene: røtten kan byttes ut med stiens endepunkt i `Y`. -/
theorem rootTree_tail {G : DAG V} {n : ℕ} (ps : List V)
    (T : RootTree.RT (isoSet G ps.toFinset) n) (O : Finset V) (ρ : V)
    (hu : ∀ j, T.u j ∉ O) (hR : ∀ k, T.dp k = none → T.nd k ∈ O) (hx : T.x ∈ O)
    (hρ : ρ ∈ T.Y) (hP : IsPath G ρ ps) (hnd : (ρ :: ps).Nodup)
    (hps : ∀ p ∈ ps, p ∉ O ∧ p ∉ T.Y ∧ p ≠ T.x) :
    ¬ Identifiable G (fun _ => Bool) (O ∪ ps.toFinset) {T.x}
      (insert (lastOf ρ ps) (T.Y.erase ρ)) := by
  have hYX : Disjoint T.Y {T.x} := by
    rw [Finset.disjoint_singleton_right]
    intro hm
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact T.hndx k hk
  have hρO : ρ ∈ O := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hρ
    exact hR k (Finset.mem_filter.mp hk).2
  exact path_not_identifiable ps ρ O T.Y hP hnd hρO hρ
    (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1, by
      rw [Finset.mem_singleton]; exact (hps p hp).2.2⟩) hYX
    (RootTree.rootTree_not_identifiable T O hu hR hx)

end Channel
end Identification

#print axioms Identification.Channel.path_not_identifiable
#print axioms Identification.Channel.rootTree_tail
