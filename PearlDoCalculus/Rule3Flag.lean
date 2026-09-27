import PearlDoCalculus.Rule3
import PearlDoCalculus.DoAudit

/-!
# Regel 3 uten positivitet: flaggmodellen

Pearls utvidede graf legger til en intervensjonsnode `F_z → z` per `z ∈ Z`.
Siden `F_z` bare har ett barn, legges flagget her inn i verdien til `z`:
flaggmodellen har verdier i `Option (α v)`, der `none` på en `Z`-node betyr
«intervenert til `z₀`». Den inneholder både `P` (alle `some`) og `P_{z₀}`
(`Z`-nodene `none`), på samme graf, så `dsep_sound_set` gjelder direkte.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Rule3Flag

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Avbildning med `some` bevarer sannsynligheten i `some a`. -/
lemma map_some_apply {β : Type*} (p : PMF β) (a : β) : (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- Avbildning med `some` gir ingen masse i `none`. -/
lemma map_some_none {β : Type*} (p : PMF β) : (p.map some) none = 0 := by
  rw [PMF.map_apply]
  simp

/-- Hvordan et barn leser en forelder: `some a` er `a`, `none` er `z₀` på `Z`
(og en vilkårlig verdi utenfor `Z`, der `none` aldri har positiv sannsynlighet). -/
noncomputable def readVal [∀ w, Nonempty (α w)] (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : V) (o : Option (α u)) : α u :=
  o.elim (if hu : u ∈ Z then z₀ ⟨u, hu⟩ else Classical.arbitrary _) id

/-- **Flaggmodellen.** For `v ∈ Z`: med sannsynlighet ½ `none`, ellers `some` av
en verdi fra `M`. For `v ∉ Z`: `some` av en verdi fra `M`. Foreldre leses med
`readVal`. -/
noncomputable def flagModel [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) : G.CausalModel (fun v => Option (α v)) where
  fin := fun v => by haveI := M.fin v; infer_instance
  deq := fun v => by haveI := M.deq v; infer_instance
  kernel := fun v p =>
    if v ∈ Z then
      (PMF.uniformOfFintype Bool).bind (fun b =>
        if b then PMF.pure none
        else (M.kernel v (fun u => readVal Z z₀ u.1 (p u))).map some)
    else (M.kernel v (fun u => readVal Z z₀ u.1 (p u))).map some

/-- Observasjon: alle noder `some`. -/
def obs (u : Assignment (α := α) (Finset.univ : Finset V)) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => some (u v)

/-- Intervensjon: `Z`-nodene `none`, de andre `some`. -/
def intv (Z : Finset V) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => if v.1 ∈ Z then none else some (u v)

/-- Flaggkjernen på `Z` i `some a`: ½ ganger `M` sin. -/
lemma flag_kernel_some [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∈ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) (a : α v) :
    (flagModel M Z z₀).kernel v p (some a) =
      2⁻¹ * M.kernel v (fun u => readVal Z z₀ u.1 (p u)) a := by
  simp only [flagModel, if_pos hv]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply]
  congr 1
  refine (tsum_eq_single a ?_).trans ?_
  · intro b hb
    simp [Ne.symm hb]
  · simp

/-- Flaggkjernen på `Z` i `none`: ½. -/
lemma flag_kernel_none_mem [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∈ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) :
    (flagModel M Z z₀).kernel v p none = 2⁻¹ := by
  simp only [flagModel, if_pos hv]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply, map_some_none]

/-- Flaggkjernen utenfor `Z` i `some a`: `M` sin. -/
lemma flag_kernel_some_not_mem [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∉ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) (a : α v) :
    (flagModel M Z z₀).kernel v p (some a) =
      M.kernel v (fun u => readVal Z z₀ u.1 (p u)) a := by
  simp only [flagModel, if_neg hv]
  exact map_some_apply _ _

/-- **Punkt 1.** Kjernefaktorene i en observasjon: ½ ganger `M` sin på `Z`,
`M` sin utenfor. -/
lemma kfac_flag_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (flagModel M Z z₀) Finset.univ (obs u) v =
      (if v ∈ Z then 2⁻¹ else 1) * kfac M Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hv : v ∈ Z
  · rw [if_pos hv]
    exact flag_kernel_some M Z z₀ hv _ _
  · rw [if_neg hv, one_mul]
    exact flag_kernel_some_not_mem M Z z₀ hv _ _

/-- **Punkt 2.** Kjernefaktorene i en intervensjon: ½ på `Z`, og utenfor `Z`
`M` sin faktor i tilordningen med `Z` satt til `z₀`. -/
lemma kfac_flag_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (flagModel M Z z₀) Finset.univ (intv Z u) v =
      if v ∈ Z then 2⁻¹
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v := by
  rw [DoAudit.kfac_univ]
  by_cases hv : v ∈ Z
  · have hval : (intv Z u) ⟨v, Finset.mem_univ v⟩ = none := by simp [intv, hv]
    rw [if_pos hv, hval]
    exact flag_kernel_none_mem M Z z₀ hv _
  · have hval : (intv Z u) ⟨v, Finset.mem_univ v⟩ = some (u ⟨v, Finset.mem_univ v⟩) := by
      simp [intv, hv]
    rw [if_neg hv, DoAudit.kfac_univ, hval, flag_kernel_some_not_mem M Z z₀ hv]
    refine congrArg₂ (fun p x => M.kernel v p x) ?_ ?_
    · funext w
      by_cases hw : w.1 ∈ Z
      · simp [readVal, intv, combineZ, Assignment.restrict, hw]
      · simp [readVal, intv, combineZ, Assignment.restrict, hw]
    · simp [combineZ, Assignment.restrict, hv]

/-- **Fellesfordelingen i en observasjon:** `P⁺(obs u) = (½)^|Z| · P(u)`. -/
lemma flag_fullJoint_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (flagModel M Z z₀).fullJoint (obs u) = (2⁻¹ : ENNReal) ^ Z.card * M.fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp_rw [kfac_flag_obs]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **Fellesfordelingen i en intervensjon:** `P⁺(intv u) = (½)^|Z| · P_{z₀}(ũ)`,
der `ũ` er `u` utenfor `Z` og `z₀` på `Z`. -/
lemma flag_fullJoint_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (flagModel M Z z₀).fullJoint (intv Z u) =
      (2⁻¹ : ENNReal) ^ Z.card *
        (doModel M Z z₀).fullJoint (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) := by
  rw [fullJoint_apply_prod, doModel_fullJoint, if_pos (combine_restrict_Z Z z₀ _), one_mul]
  simp_rw [kfac_flag_int]
  rw [← Finset.prod_mul_prod_compl Z]
  have h1 : ∏ v ∈ Z, (if v ∈ Z then (2⁻¹ : ENNReal)
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v) =
      ∏ _v ∈ Z, (2⁻¹ : ENNReal) :=
    Finset.prod_congr rfl (fun v hv => if_pos hv)
  have h2 : ∏ v ∈ Zᶜ, (if v ∈ Z then (2⁻¹ : ENNReal)
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v) =
      ∏ v ∈ Zᶜ, kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v :=
    Finset.prod_congr rfl (fun v hv => if_neg (Finset.mem_compl.mp hv))
  rw [h1, h2, Finset.prod_const]

/-- **Null utenfor `Z`:** er en node utenfor `Z` `none`, er `P⁺ = 0`. -/
lemma flag_fullJoint_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    {v : V} (hv : v ∉ Z) (hnone : u ⟨v, Finset.mem_univ v⟩ = none) :
    (flagModel M Z z₀).fullJoint u = 0 := by
  rw [fullJoint_apply_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  rw [DoAudit.kfac_univ, hnone]
  simp only [flagModel, if_neg hv]
  exact map_some_none _

/-! ## Fase 4, runde 1: injektivitet og støtte -/

lemma obs_injective : Function.Injective (obs (V := V) (α := α)) := by
  intro u u' h
  funext v
  have := congrFun h v
  simpa [obs] using this

/-- Intervensjon indeksert av tilordninger utenfor `Z`: `none` på `Z`,
`some (a v)` utenfor. -/
def intC (Z : Finset V) (a : Assignment (α := α) Zᶜ) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => if h : v.1 ∈ Z then none else some (a ⟨v.1, Finset.mem_compl.mpr h⟩)

lemma intC_injective (Z : Finset V) : Function.Injective (intC (α := α) Z) := by
  intro a a' h
  funext ⟨v, hv⟩
  have hvZ : v ∉ Z := Finset.mem_compl.mp hv
  have := congrFun h ⟨v, Finset.mem_univ v⟩
  simpa [intC, hvZ] using this

lemma intC_eq_intv (Z : Finset V) (z₀ : Assignment (α := α) Z)
    (a : Assignment (α := α) Zᶜ) : intC Z a = intv Z (combineZ Z z₀ a) := by
  funext ⟨v, hv⟩
  by_cases hvZ : v ∈ Z
  · simp [intC, intv, hvZ]
  · simp [intC, intv, combineZ, hvZ]

/-- **Steg 1 i (M1).** Positiv masse og ingen `none` på `Z` gir en observasjon. -/
lemma exists_obs_of_ne_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    (h : (flagModel M Z z₀).fullJoint u ≠ 0)
    (hZ : ∀ v ∈ Z, u ⟨v, Finset.mem_univ v⟩ ≠ none) :
    ∃ u₀ : Assignment (α := α) (Finset.univ : Finset V), obs u₀ = u := by
  have hsome : ∀ v : {v // v ∈ (Finset.univ : Finset V)}, ∃ a, u v = some a := by
    intro ⟨v, hv⟩
    by_cases hvZ : v ∈ Z
    · exact Option.ne_none_iff_exists'.mp (hZ v hvZ)
    · by_contra hno
      push_neg at hno
      exact h (flag_fullJoint_zero M Z z₀ u hvZ (Option.eq_none_iff_forall_ne_some.mpr hno))
  choose u₀ hu₀ using hsome
  exact ⟨u₀, funext fun v => (hu₀ v).symm⟩

/-- **Steg 1 i (M2).** Positiv masse og `none` på hele `Z` gir en intervensjon. -/
lemma exists_intC_of_ne_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    (h : (flagModel M Z z₀).fullJoint u ≠ 0)
    (hZ : ∀ v ∈ Z, u ⟨v, Finset.mem_univ v⟩ = none) :
    ∃ a : Assignment (α := α) Zᶜ, intC Z a = u := by
  have hsome : ∀ v : {v // v ∈ (Zᶜ : Finset V)}, ∃ x, u ⟨v.1, Finset.mem_univ _⟩ = some x := by
    intro ⟨v, hv⟩
    have hvZ : v ∉ Z := Finset.mem_compl.mp hv
    by_contra hno
    push_neg at hno
    exact h (flag_fullJoint_zero M Z z₀ u hvZ (Option.eq_none_iff_forall_ne_some.mpr hno))
  choose a ha using hsome
  refine ⟨a, funext fun ⟨v, hv⟩ => ?_⟩
  by_cases hvZ : v ∈ Z
  · simp only [intC, dif_pos hvZ]
    exact (hZ v hvZ).symm
  · simp only [intC, dif_neg hvZ]
    exact (ha ⟨v, Finset.mem_compl.mpr hvZ⟩).symm

end Rule3Flag

#print axioms Rule3Flag.map_some_apply
#print axioms Rule3Flag.map_some_none
#print axioms Rule3Flag.kfac_flag_obs
#print axioms Rule3Flag.kfac_flag_int
#print axioms Rule3Flag.flag_fullJoint_obs
#print axioms Rule3Flag.flag_fullJoint_int
#print axioms Rule3Flag.flag_fullJoint_zero
#print axioms Rule3Flag.intC_eq_intv
#print axioms Rule3Flag.exists_obs_of_ne_zero
#print axioms Rule3Flag.exists_intC_of_ne_zero
