import PearlDoCalculus.IdAlgo

/-!
# IDC: betingede effekter `P(Y | do(X), Z)` (runde 39–40)

Runde 39 legger grunnmuren:

* `doModel_doModel_marginal`: to intervensjoner etter hverandre, `do(X = x)` og så
  `do(Z = z)`, er det samme som én intervensjon `do(X ∪ Z = (x, z))` (for disjunkte `X`, `Z`).
  Regel 2 i `DoCalculus` er formulert med to nøstede intervensjoner; ID-laget med én.
* `doModel_marginal_ne_zero`: er den observerte fordelingen positiv, er alle
  intervensjonsmarginaler positive på tilordninger som stemmer med `x`. Dette trengs for å
  forkorte i den betingede formen.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Classical

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `x` på `X` og `z` på `Z`, slått sammen til en tilordning på `X ∪ Z`. -/
def joinXZ (X Z : Finset V) (x : Assignment (α := α) X) (z : Assignment (α := α) Z) :
    Assignment (α := α) (X ∪ Z) :=
  fun v => if h : v.1 ∈ X then x ⟨v.1, h⟩
    else z ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩

/-- **To intervensjoner etter hverandre er én**, på nivå av fellesfordelingen. -/
theorem doModel_doModel_fullJoint (M : G.CausalModel α) (X Z : Finset V) (hXZ : Disjoint X Z)
    (x : Assignment (α := α) X) (z : Assignment (α := α) Z)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel (doModel M X x) Z z).fullJoint u =
      (doModel M (X ∪ Z) (joinXZ X Z x z)).fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [kfac_doModel (doModel M X x) Z z u v, kfac_doModel M X x u v,
    kfac_doModel M (X ∪ Z) (joinXZ X Z x z) u v]
  by_cases hz : v ∈ Z
  · have hx : v ∉ X := fun hx => Finset.disjoint_left.mp hXZ hx hz
    have hj : joinXZ X Z x z ⟨v, Finset.mem_union_right X hz⟩ = z ⟨v, hz⟩ := by
      simp only [joinXZ, dif_neg hx]
    rw [dif_pos hz, dif_pos (Finset.mem_union_right X hz), hj]
  · rw [dif_neg hz]
    by_cases hx : v ∈ X
    · have hj : joinXZ X Z x z ⟨v, Finset.mem_union_left Z hx⟩ = x ⟨v, hx⟩ := by
        simp only [joinXZ, dif_pos hx]
      rw [dif_pos hx, dif_pos (Finset.mem_union_left Z hx), hj]
    · rw [dif_neg hx, dif_neg (fun h => (Finset.mem_union.mp h).elim hx hz)]

/-- **To intervensjoner etter hverandre er én**, for marginalene. -/
theorem doModel_doModel_marginal (M : G.CausalModel α) (X Z : Finset V) (hXZ : Disjoint X Z)
    (x : Assignment (α := α) X) (z : Assignment (α := α) Z) (S : Finset V) :
    (doModel (doModel M X x) Z z).marginal S =
      (doModel M (X ∪ Z) (joinXZ X Z x z)).marginal S := by
  unfold CausalModel.marginal
  rw [show (doModel (doModel M X x) Z z).fullJoint =
      (doModel M (X ∪ Z) (joinXZ X Z x z)).fullJoint from
    PMF.ext (fun u => doModel_doModel_fullJoint M X Z hXZ x z u)]

/-- En tilordning på de observerte som er `s` på `S` og `x` på `X`. -/
noncomputable def extSX [∀ v, Nonempty (α v)] (U S X : Finset V) (s : Assignment (α := α) S)
    (x : Assignment (α := α) X) : Assignment (α := α) Uᶜ :=
  fun v => if h : v.1 ∈ S then s ⟨v.1, h⟩
    else if h' : v.1 ∈ X then x ⟨v.1, h'⟩ else Classical.arbitrary _

/-- **Positive intervensjonsmarginaler.** -/
theorem doModel_marginal_ne_zero [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U X : Finset V)
    (hXO : X ⊆ Uᶜ) (hpos : ∀ a, M.marginal Uᶜ a ≠ 0) (x : Assignment (α := α) X)
    (S : Finset V) (hS : S ⊆ Uᶜ) (s : Assignment (α := α) S)
    (hsx : ∀ v (hvS : v ∈ S) (hvX : v ∈ X), s ⟨v, hvS⟩ = x ⟨v, hvX⟩) :
    (doModel M X x).marginal S s ≠ 0 := by
  have h0 := hpos (extSX U S X s x)
  unfold CausalModel.marginal at h0
  obtain ⟨u, hu, hua⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr h0)
  have hval : ∀ v (hv : v ∈ Uᶜ),
      u ⟨v, Finset.mem_univ v⟩ = extSX U S X s x ⟨v, hv⟩ := fun v hv => congrFun hua ⟨v, hv⟩
  have hux : u.restrict (Finset.subset_univ X) = x := by
    funext w
    obtain ⟨v, hv⟩ := w
    show u ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩
    rw [hval v (hXO hv)]
    by_cases hvS : v ∈ S
    · simp only [extSX, dif_pos hvS]
      exact hsx v hvS hv
    · simp only [extSX, dif_neg hvS, dif_pos hv]
  have hus : u.restrict (Finset.subset_univ S) = s := by
    funext w
    obtain ⟨v, hv⟩ := w
    show u ⟨v, Finset.mem_univ v⟩ = s ⟨v, hv⟩
    rw [hval v (hS hv)]
    simp only [extSX, dif_pos hv]
  have hM : M.fullJoint u ≠ 0 := (PMF.mem_support_iff _ _).mp hu
  rw [fullJoint_apply_prod] at hM
  have hk := Finset.prod_ne_zero_iff.mp hM
  have hdo : (doModel M X x).fullJoint u ≠ 0 := by
    rw [doModel_fullJoint, if_pos hux, one_mul]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => hk v (Finset.mem_univ v))
  unfold CausalModel.marginal
  exact (PMF.mem_support_iff _ _).mp
    ((PMF.mem_support_map_iff _ _ _).mpr ⟨u, (PMF.mem_support_iff _ _).mpr hdo, hus⟩)

end Idc

#print axioms Idc.doModel_doModel_marginal
#print axioms Idc.doModel_marginal_ne_zero

/-! ## Runde 40: IDC-setningen

`IdentifiableCond G α O X Y Z W`: `P(Y | do(X), Z, W)` er bestemt av `P(O)`, på
kryssmultiplisert form (like der den betingede fordelingen er definert):

  `P₁,ₓ(y, z, w) · P₂,ₓ(z, w) = P₂,ₓ(y, z, w) · P₁,ₓ(z, w)`.

`idc_sound` (Shpitser & Pearl 2006, IDC): tillater regel 2 å flytte `Z` inn i
intervensjonen (`Y ⊥ Z | X, W` i `G_{X̄ Z̲}`), og er `P(Y, X, W | do(X ∪ Z))`
identifiserbar (for eksempel med `IdAlgo.idCheck`), så er `P(Y | do(X), Z, W)`
identifiserbar. Beviset: regel 2 på produktform for begge modellene, komposisjon av
intervensjonene, og forkorting med den positive faktoren `P_{x,z}(w)`. -/

namespace Idc

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

omit [Fintype V] in
lemma joinXZ_left (A B : Finset V) (a : Assignment (α := α) A) (b : Assignment (α := α) B) :
    (joinXZ A B a b).restrict Finset.subset_union_left = a := by
  funext w
  obtain ⟨v, hv⟩ := w
  simp only [Assignment.restrict, joinXZ, dif_pos hv]

omit [Fintype V] in
lemma joinXZ_right (A B : Finset V) (a : Assignment (α := α) A) (b : Assignment (α := α) B)
    (hab : ∀ v (ha : v ∈ A) (hb : v ∈ B), a ⟨v, ha⟩ = b ⟨v, hb⟩) :
    (joinXZ A B a b).restrict Finset.subset_union_right = b := by
  funext w
  obtain ⟨v, hv⟩ := w
  by_cases ha : v ∈ A
  · simp only [Assignment.restrict, joinXZ, dif_pos ha]
    exact hab v ha hv
  · simp only [Assignment.restrict, joinXZ, dif_neg ha]

/-- Under `do(X = x)` har en tilordning som avviker fra `x` sannsynlighet 0. -/
theorem doModel_marginal_eq_zero (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) (S : Finset V) (s : Assignment (α := α) S) (v : V)
    (hvS : v ∈ S) (hvX : v ∈ X) (hne : s ⟨v, hvS⟩ ≠ x ⟨v, hvX⟩) :
    (doModel M X x).marginal S s = 0 := by
  by_contra h0
  unfold CausalModel.marginal at h0
  obtain ⟨u, hu, hus⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr h0)
  have hdo : (doModel M X x).fullJoint u ≠ 0 := (PMF.mem_support_iff _ _).mp hu
  rw [doModel_fullJoint] at hdo
  by_cases hux : u.restrict (Finset.subset_univ X) = x
  · apply hne
    rw [← hus, ← hux]
    rfl
  · exact hdo (by rw [if_neg hux, zero_mul])

/-- Identifiserbarhet gir like intervensjonsmarginaler, også når `Y` og `X` overlapper. -/
theorem ident_marginal_eq {O X Y : Finset V} (hid : Identifiable G α O X Y)
    (M₁ M₂ : G.CausalModel α) (hM : M₁.marginal O = M₂.marginal O)
    (hpos : ∀ a, M₁.marginal O a ≠ 0) (x : Assignment (α := α) X) :
    (doModel M₁ X x).marginal Y = (doModel M₂ X x).marginal Y := by
  ext s
  by_cases hc : ∀ v (hY : v ∈ Y) (hX : v ∈ X), s ⟨v, hY⟩ = x ⟨v, hX⟩
  · have e := hid M₁ M₂ hM hpos (joinXZ Y X s x)
    rw [joinXZ_right Y X s x hc, joinXZ_left Y X s x] at e
    exact e
  · simp only [not_forall] at hc
    obtain ⟨v, hY, hX, hne⟩ := hc
    rw [doModel_marginal_eq_zero M₁ X x Y s v hY hX hne,
      doModel_marginal_eq_zero M₂ X x Y s v hY hX hne]

/-- Forkorting i kryssmultiplisert form. -/
lemma cross_cancel {a₁ a₂ b₁ b₂ c d : ENNReal} (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (r₁ : a₁ * d = c * b₁) (r₂ : a₂ * d = c * b₂) : a₁ * b₂ = a₂ * b₁ := by
  apply (ENNReal.mul_right_inj hd0 hdt).mp
  calc d * (a₁ * b₂) = (a₁ * d) * b₂ := by ring
    _ = (c * b₁) * b₂ := by rw [r₁]
    _ = (a₂ * d) * b₁ := by rw [r₂]; ring
    _ = d * (a₂ * b₁) := by ring

/-- **Betinget identifiserbarhet** av `P(Y | do(X), Z, W)`. -/
def IdentifiableCond (G : DAG V) (α : V → Type*) (O X Y Z W : Finset V) : Prop :=
  ∀ M₁ M₂ : G.CausalModel α, M₁.marginal O = M₂.marginal O → (∀ a, M₁.marginal O a ≠ 0) →
    ∀ (x : Assignment (α := α) X) (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W))),
      (doModel M₁ X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel M₂ X x).marginal (Z ∪ (X ∪ W)) (t.restrict (show Z ∪ (X ∪ W) ⊆
            Y ∪ Z ∪ (X ∪ W) by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M₂ X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel M₁ X x).marginal (Z ∪ (X ∪ W)) (t.restrict (show Z ∪ (X ∪ W) ⊆
            Y ∪ Z ∪ (X ∪ W) by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto))

/-- **IDC er sunn.** -/
theorem idc_sound [∀ v, Nonempty (α v)] (U X Y Z W : Finset V)
    (hXO : X ⊆ Uᶜ) (hZO : Z ⊆ Uᶜ) (hWO : W ⊆ Uᶜ)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z)
    (hid : Identifiable G α Uᶜ (X ∪ Z) (Y ∪ (X ∪ W))) :
    IdentifiableCond G α Uᶜ X Y Z W := by
  intro M₁ M₂ hM hpos x t
  have hXZ : Disjoint X Z := Finset.disjoint_left.mpr (fun v hx hz =>
    Finset.disjoint_left.mp hXWZ (Finset.mem_union_left W hx) hz)
  have pX : X ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_left W hv)
  have pZ : Z ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right Y hv)
  have pXW : X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) := fun v hv => Finset.mem_union_right _ hv
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, t.restrict pZ = z₀ := ⟨_, rfl⟩
  by_cases hxt : ∀ v (hv : v ∈ X), t ⟨v, pX hv⟩ = x ⟨v, hv⟩
  · have r₁ := rule2 M₁ X Y Z W x z₀ hYZ hXWZ hYXW h t hz₀
    have r₂ := rule2 M₂ X Y Z W x z₀ hYZ hXWZ hYXW h t hz₀
    rw [doModel_doModel_marginal M₁ X Z hXZ x z₀, doModel_doModel_marginal M₁ X Z hXZ x z₀]
      at r₁
    rw [doModel_doModel_marginal M₂ X Z hXZ x z₀, doModel_doModel_marginal M₂ X Z hXZ x z₀]
      at r₂
    have hc := ident_marginal_eq hid M₁ M₂ hM hpos (joinXZ X Z x z₀)
    have hd : (doModel M₁ (X ∪ Z) (joinXZ X Z x z₀)).marginal (X ∪ W) =
        (doModel M₂ (X ∪ Z) (joinXZ X Z x z₀)).marginal (X ∪ W) := by
      rw [← marginal_restrict (doModel M₁ (X ∪ Z) (joinXZ X Z x z₀))
          (show X ∪ W ⊆ Y ∪ (X ∪ W) from Finset.subset_union_right),
        ← marginal_restrict (doModel M₂ (X ∪ Z) (joinXZ X Z x z₀))
          (show X ∪ W ⊆ Y ∪ (X ∪ W) from Finset.subset_union_right), hc]
    rw [hc, hd] at r₁
    have hpos₂ : ∀ a, M₂.marginal Uᶜ a ≠ 0 := fun a => by rw [← hM]; exact hpos a
    have hd0 : (doModel M₂ (X ∪ Z) (joinXZ X Z x z₀)).marginal (X ∪ W) (t.restrict pXW) ≠ 0 :=
      doModel_marginal_ne_zero M₂ U (X ∪ Z) (Finset.union_subset hXO hZO) hpos₂ _ (X ∪ W)
        (Finset.union_subset hXO hWO) _ (fun v hvS hvX => by
          by_cases hx : v ∈ X
          · simp only [Assignment.restrict, joinXZ, dif_pos hx]
            exact hxt v hx
          · exfalso
            have hw : v ∈ W := (Finset.mem_union.mp hvS).resolve_left hx
            have hz : v ∈ Z := (Finset.mem_union.mp hvX).resolve_left hx
            exact Finset.disjoint_left.mp hXWZ (Finset.mem_union_right X hw) hz)
    exact cross_cancel hd0 (PMF.apply_ne_top _ _) r₁ r₂
  · simp only [not_forall] at hxt
    obtain ⟨v, hv, hne⟩ := hxt
    rw [doModel_marginal_eq_zero M₁ X x _ t v (pX hv) hv hne,
      doModel_marginal_eq_zero M₂ X x _ t v (pX hv) hv hne]
    simp

end Idc

#print axioms Idc.ident_marginal_eq
#print axioms Idc.idc_sound
