import PearlDoCalculus.Identification.CFactor

/-!
# Tian's theorem for sets, factorization over many blocks, and `Q[S]` as a causal effect

This file extends Tian's identification theorem from one node `x` to a set `X` of observed
nodes inside a closed block `S`. The proof is the one of `Identification/CFactor`, with a
sum over all values of `X` instead of over one value `x`. It then factorizes the
distribution over many blocks (line 4 of the ID algorithm), gives Tian's theorem with one
sum per c-component, shows that each factor is a causal effect
(`Q[S] = P_{do(O ∖ S)}`), and finally derives the first theorem again as a corollary.

Main results: `Identification.CFactor.tian_identifiableX` and
`Identification.CFactor.tian_identifiable_ccompX`, besides the factorization lemmas used
by `Identification.lean`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## Runde 25: Tians teorem for en mengde `X`

Samme bevis som runde 22, med en sum over alle verdiene til `X` i stedet for over `x`.
La `X ⊆ S` være observert, `S` en lukket blokk, og la ingen node i `X` ha et barn i `S`.
Da er

  `P_X(a) = [a_X = x] · (Σ_{x'} Q[S](a[X := x'])) · Q[Sᶜ](a)`,

og effekten av `X` er identifiserbar. (Runde 29: teoremene står nå etter runde 27, som
korollarer av `tian_identifiable_sets`; her står bare hjelpelemmaene.)

Nytt er bare `sum_assign_prod`: summen over alle tilordninger på `X` av et produkt av
kjerner er produktet av summene (`Fintype.prod_sum`), altså 1. Med c-komponenter: velg
`S` som unionen av c-komponentene til nodene i `X`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `a` med verdiene på `X` byttet ut med `x'`. -/
noncomputable def updX (U X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) : Assignment (α := α) Uᶜ :=
  fun v => if h : v.1 ∈ X then x' ⟨v.1, h⟩ else a v

/-- `updX` is `Rule3Flag.setZ` on the observed set `Uᶜ`. The two definitions are equal;
both are kept because both occur in the statements of public results (`setZ` in the
back-door and front-door adjustment formulas, `updX` in Verma's constraint). -/
lemma updX_eq_setZ (U X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) : updX U X a x' = Rule3Flag.setZ X Uᶜ a x' :=
  rfl

lemma fill_updX_out [∀ v, Nonempty (α v)] (U T X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∉ X) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = fill U T a w ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · simp [fill, h0]
  · simp [fill, h0, updX, hz]

lemma fill_updX_in [∀ v, Nonempty (α v)] (U T X : Finset V) (a : Assignment (α := α) Uᶜ)
    (x' : Assignment (α := α) X) (w : Assignment (α := α) (U ∩ T)) (z : V) (hz : z ∈ X)
    (hzU : z ∉ U) :
    fill U T (updX U X a x') w ⟨z, Finset.mem_univ z⟩ = x' ⟨z, hz⟩ := by
  simp [fill, hzU, updX, hz]

/-- **Produktet av summene.** Summert over alle tilordninger på `X` er et produkt av
sannsynlighetsfordelinger lik 1. -/
lemma sum_assign_prod (M : G.CausalModel α) (X : Finset V)
    (K : ∀ v : {v // v ∈ X}, PMF (α v.1)) :
    ∑' x' : Assignment (α := α) X, ∏ v : {v // v ∈ X}, K v (x' v) = 1 := by
  haveI : ∀ v, Fintype (α v) := M.fin
  show ∑' x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v) = 1
  calc ∑' x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v)
      = ∑ x' : (∀ v : {v // v ∈ X}, α v.1), ∏ v : {v // v ∈ X}, K v (x' v) := tsum_fintype _
    _ = ∏ v : {v // v ∈ X}, ∑ t : α v.1, K v t := (Fintype.prod_sum (fun v t => K v t)).symm
    _ = 1 := Finset.prod_eq_one (fun v _ => by
        calc ∑ t : α v.1, K v t = ∑' t : α v.1, K v t := (tsum_fintype _).symm
          _ = 1 := (K v).tsum_coe)

/-- **`X` summeres bort.** -/
theorem sum_Q_updX [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S X : Finset V)
    (hXO : X ⊆ Uᶜ) (hXS : X ⊆ S) (hch : ∀ x ∈ X, ∀ v ∈ S, ¬ G.edge x v)
    (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) X, Q M U S (updX U X a x') =
      ∑' w : Assignment (α := α) (U ∩ S), ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := by
  unfold Q
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun w => ?_)
  have hrest : ∀ x' : Assignment (α := α) X,
      ∏ v ∈ S \ X, kfac M Finset.univ (fill U S (updX U X a x') w) v =
        ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := fun x' =>
    Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
      (fill_updX_out U S X a x' w v (Finset.mem_sdiff.mp hv).2)
      (fun u hu => fill_updX_out U S X a x' w u
        (fun huX => hch u huX v (Finset.mem_sdiff.mp hv).1 (DAG.mem_parents.mp hu))))
  have hxk : ∀ x' : Assignment (α := α) X,
      ∏ v ∈ X, kfac M Finset.univ (fill U S (updX U X a x') w) v =
        ∏ v : {v // v ∈ X}, M.kernel v.1
          ((fill U S a w).restrict (Finset.subset_univ _)) (x' v) := by
    intro x'
    rw [← Finset.prod_coe_sort X]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    have hr : (fill U S (updX U X a x') w).restrict (Finset.subset_univ (G.parents v.1)) =
        (fill U S a w).restrict (Finset.subset_univ (G.parents v.1)) := by
      funext ⟨u, hu⟩
      exact fill_updX_out U S X a x' w u
        (fun huX => hch u huX v.1 (hXS v.2) (DAG.mem_parents.mp hu))
    rw [kfac_univ, hr,
      fill_updX_in U S X a x' w v.1 v.2 (Finset.mem_compl.mp (hXO v.2))]
  have hSX : S ∩ X = X := Finset.inter_eq_right.mpr hXS
  calc ∑' x' : Assignment (α := α) X, ∏ v ∈ S, kfac M Finset.univ (fill U S (updX U X a x') w) v
      = ∑' x' : Assignment (α := α) X,
          (∏ v : {v // v ∈ X}, M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _)) (x' v)) *
            ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v :=
        tsum_congr (fun x' => by
          rw [← Finset.prod_inter_mul_prod_diff S X, hSX, hxk x', hrest x'])
    _ = (∑' x' : Assignment (α := α) X,
          ∏ v : {v // v ∈ X}, M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _)) (x' v)) *
            ∏ v ∈ S \ X, kfac M Finset.univ (fill U S a w) v := ENNReal.tsum_mul_right
    _ = _ := by
        rw [sum_assign_prod M X
          (fun v => M.kernel v.1 ((fill U S a w).restrict (Finset.subset_univ _))), one_mul]

end CFactor
end Identification

/-! ## Runde 26: faktorisering over mange blokker (ID-algoritmens linje 4)

Runde 20–21 delte i to blokker, `S` og `Sᶜ`. ID-algoritmen trenger en faktor per
c-komponent. Her:

1. `Q_split`: for en mengde `T` som inneholder sine latente foreldre (`IsLatClosed`) og
   en lukket blokk `S`, er `Q[T] = Q[T ∩ S] · Q[T ∩ Sᶜ]`. Ren algebra: summen over de
   latente i `T` deles i to (`tsum_join2`), og produktet over `T` likeså.
2. `marginal_eq_Q`: `P(O) = Q[V]`.
3. `Q_prod`: for parvis disjunkte lukkede blokker `B i`, `i ∈ I`, som dekker `T`, er
   `Q[T] = ∏_{i ∈ I} Q[T ∩ B i]`. Induksjon over `I` med `Q_split`.
4. `marginal_prod`: `P(O) = ∏_i Q[B i]` når blokkene dekker alle noder. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- `T` inneholder alle sine latente foreldre. -/
def IsLatClosed (G : DAG V) (U T : Finset V) : Prop :=
  ∀ v ∈ T, ∀ u ∈ U, G.edge u v → u ∈ T

/-- Faktoren for den tomme mengden er 1. -/
lemma Q_empty [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : Q M U ∅ a = 1 := by
  unfold Q
  simp only [Finset.prod_empty]
  have w0 : Assignment (α := α) (U ∩ ∅) := fun v => absurd v.2 (by simp)
  have hw : ∀ w w' : Assignment (α := α) (U ∩ ∅), w = w' :=
    fun w w' => funext (fun v => absurd v.2 (by simp))
  exact tsum_eq_single w0 (fun w hw' => absurd (hw w w0) hw')

lemma subT1 (U T S : Finset V) : U ∩ (T ∩ S) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

lemma subT2 (U T S : Finset V) : U ∩ (T ∩ Sᶜ) ⊆ U ∩ T := fun v hv => by
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr ⟨h0, (Finset.mem_inter.mp h1).1⟩

/-- De latente i `T`, satt sammen av delene i `T ∩ S` og `T ∩ Sᶜ`. -/
noncomputable def join2 (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) : Assignment (α := α) (U ∩ T) :=
  fun v => if h : v.1 ∈ S then
      w1 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, h⟩⟩⟩
    else w2 ⟨v.1, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp v.2).2, Finset.mem_compl.mpr h⟩⟩⟩

lemma join2_iff (U T S : Finset V) (w1 : Assignment (α := α) (U ∩ (T ∩ S)))
    (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ))) (w : Assignment (α := α) (U ∩ T)) :
    w = join2 U T S w1 w2 ↔ w1 = w.restrict (subT1 U T S) ∧ w2 = w.restrict (subT2 U T S) := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      have hS : v ∈ S := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [join2, Assignment.restrict, hS]
    · funext ⟨v, hv⟩
      have hS : v ∉ S := Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2
      simp [join2, Assignment.restrict, hS]
  · rintro ⟨rfl, rfl⟩
    funext ⟨v, hv⟩
    by_cases hS : v ∈ S
    · simp [join2, Assignment.restrict, hS]
    · simp [join2, Assignment.restrict, hS]

/-- **Summen over de latente i `T` deler seg i to.** -/
lemma tsum_join2 (U T S : Finset V) (F : Assignment (α := α) (U ∩ T) → ENNReal) :
    ∑' w, F w = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
      ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)), F (join2 U T S w1 w2) := by
  calc ∑' w, F w
      = ∑' w, ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
            (if w = join2 U T S w1 w2 then F w else 0) := by
        refine tsum_congr (fun w => ?_)
        rw [tsum_eq_single (w.restrict (subT1 U T S))]
        · rw [tsum_eq_single (w.restrict (subT2 U T S))]
          · rw [if_pos ((join2_iff U T S _ _ w).mpr ⟨rfl, rfl⟩)]
          · intro w2 hw2
            rw [if_neg (fun h => hw2 ((join2_iff U T S _ _ w).mp h).2)]
        · intro w1 hw1
          exact ENNReal.tsum_eq_zero.mpr (fun w2 =>
            if_neg (fun h => hw1 ((join2_iff U T S _ _ w).mp h).1))
    _ = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)), ∑' w,
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)),
            (if w = join2 U T S w1 w2 then F w else 0) := ENNReal.tsum_comm
    _ = ∑' w1 : Assignment (α := α) (U ∩ (T ∩ S)),
          ∑' w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)), ∑' w,
            (if w = join2 U T S w1 w2 then F w else 0) :=
        tsum_congr (fun w1 => ENNReal.tsum_comm)
    _ = _ := by
        refine tsum_congr (fun w1 => tsum_congr (fun w2 => ?_))
        rw [tsum_eq_single (join2 U T S w1 w2)]
        · simp
        · intro w hw
          rw [if_neg hw]

lemma fill_join1 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ S) :
    fill U T a (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ S) a w1 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    simp [fill, join2, h0, hT, hS]
  · simp [fill, h0]

lemma fill_join2 [∀ v, Nonempty (α v)] (U T S : Finset V) (a : Assignment (α := α) Uᶜ)
    (w1 : Assignment (α := α) (U ∩ (T ∩ S))) (w2 : Assignment (α := α) (U ∩ (T ∩ Sᶜ)))
    (z : V) (hz : z ∈ U → z ∈ T ∩ Sᶜ) :
    fill U T a (join2 U T S w1 w2) ⟨z, Finset.mem_univ z⟩ =
      fill U (T ∩ Sᶜ) a w2 ⟨z, Finset.mem_univ z⟩ := by
  by_cases h0 : z ∈ U
  · obtain ⟨hT, hS⟩ := Finset.mem_inter.mp (hz h0)
    have hS' : z ∉ S := Finset.mem_compl.mp hS
    simp [fill, join2, h0, hT, hS']
  · simp [fill, h0]

/-- **To blokker innenfor `T`.** -/
theorem Q_split [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T S : Finset V)
    (hT : IsLatClosed G U T) (hcl : IsClosedBlock G U S) (a : Assignment (α := α) Uᶜ) :
    Q M U T a = Q M U (T ∩ S) a * Q M U (T ∩ Sᶜ) a := by
  have h2 : ∀ w1 w2, ∏ v ∈ T, kfac M Finset.univ (fill U T a (join2 U T S w1 w2)) v =
      (∏ v ∈ T ∩ S, kfac M Finset.univ (fill U (T ∩ S) a w1) v) *
        ∏ v ∈ T ∩ Sᶜ, kfac M Finset.univ (fill U (T ∩ Sᶜ) a w2) v := by
    intro w1 w2
    rw [← Finset.prod_inter_mul_prod_diff T S, Finset.sdiff_eq_inter_compl]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join1 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join1 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (DAG.mem_parents.mp hu),
              (hcl u hu0 v (DAG.mem_parents.mp hu)).mpr (Finset.mem_inter.mp hv).2⟩)))
    · refine Finset.prod_congr rfl (fun v hv => kfac_congr M _ _ v
        (fill_join2 U T S a w1 w2 v (fun _ => hv)) (fun u hu => fill_join2 U T S a w1 w2 u
          (fun hu0 => Finset.mem_inter.mpr
            ⟨hT v (Finset.mem_inter.mp hv).1 u hu0 (DAG.mem_parents.mp hu),
              Finset.mem_compl.mpr (fun hus => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
                ((hcl u hu0 v (DAG.mem_parents.mp hu)).mp hus))⟩)))
  unfold Q
  rw [tsum_join2 U T S]
  simp only [h2]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun w1 => ?_)
  rw [ENNReal.tsum_mul_left]

/-- `P(O) = Q[V]`. -/
theorem marginal_eq_Q [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U : Finset V)
    (a : Assignment (α := α) Uᶜ) : M.marginal Uᶜ a = Q M U Finset.univ a := by
  rw [marginal_factor M U Finset.univ (fun _ _ _ _ => by simp) a, Finset.compl_univ,
    Q_empty, mul_one]

/-- **Faktorisering over mange blokker.** -/
theorem Q_prod [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι) :
    ∀ T : Finset V, IsLatClosed G U T → (∀ i ∈ I, IsClosedBlock G U (B i)) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k)) → T ⊆ I.biUnion B →
      ∀ a, Q M U T a = ∏ i ∈ I, Q M U (T ∩ B i) a := by
  induction I using Finset.induction_on with
  | empty =>
    intro T _ _ _ hTI a
    have hT0 : T = ∅ := by simpa using hTI
    rw [hT0, Finset.prod_empty, Q_empty]
  | insert j I' hj ih =>
    intro T hT hcl hdisj hTI a
    have hclj : IsClosedBlock G U (B j) := hcl j (Finset.mem_insert_self j I')
    rw [Finset.prod_insert hj, Q_split M U T (B j) hT hclj a]
    congr 1
    have hT' : IsLatClosed G U (T ∩ (B j)ᶜ) := fun v hv u hu e =>
      Finset.mem_inter.mpr ⟨hT v (Finset.mem_inter.mp hv).1 u hu e,
        Finset.mem_compl.mpr (fun huB => (Finset.mem_compl.mp (Finset.mem_inter.mp hv).2)
          ((hclj u hu v e).mp huB))⟩
    have hTI' : T ∩ (B j)ᶜ ⊆ I'.biUnion B := by
      intro v hv
      obtain ⟨hvT, hvB⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hTI hvT)
      rcases Finset.mem_insert.mp hi with hij | hi'
      · rw [hij] at hvi
        exact absurd hvi (Finset.mem_compl.mp hvB)
      · exact Finset.mem_biUnion.mpr ⟨i, hi', hvi⟩
    rw [ih (T ∩ (B j)ᶜ) hT' (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
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

/-- **`P(O)` er produktet av blokkfaktorene.** -/
theorem marginal_prod [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι] (M : G.CausalModel α)
    (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (a : Assignment (α := α) Uᶜ) :
    M.marginal Uᶜ a = ∏ i ∈ I, Q M U (B i) a := by
  rw [marginal_eq_Q, Q_prod M U B I Finset.univ (fun _ _ _ _ _ => Finset.mem_univ _) hcl hdisj
    (fun v _ => Finset.mem_biUnion.mpr (hcov v)) a]
  simp only [Finset.univ_inter]

end CFactor
end Identification

#print axioms Identification.CFactor.Q_split
#print axioms Identification.CFactor.Q_prod
#print axioms Identification.CFactor.marginal_prod

/-! ## Runde 27: Tians teorem for mengder, én sum per c-komponent

Runde 25 krevde at ingen node i `X` hadde barn i *unionen* av c-komponentene til `X`.
Det er for strengt: i `x₁ → z ↔ x₂` med `X = {x₁, x₂}` har `x₁` et barn i c-komponenten
til `x₂`, men effekten er identifiserbar. Her får hver blokk sin egen sum:

  `P_X(a) = ∏_i [a_{X ∩ Bᵢ} = x] · Σ_{x'} Q[Bᵢ](a[X ∩ Bᵢ := x'])`   (`tian_formula_blocks`).

Kjerner i `Bᵢ` som leser noder i `X` utenfor `Bᵢ`, ser bare de faste verdiene. Kravet er
derfor bare at ingen `x ∈ X` har et barn i *sin egen* c-komponent
(`tian_identifiable_sets`). For én `x` er dette nøyaktig `tian_iff`. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Faktoren for en blokk `T` i intervensjonsmodellen, for vilkårlig `X`. -/
theorem Q_do_gen [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T X : Finset V)
    (hXO : X ⊆ Uᶜ) (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    Q (doModel M X xv) U T a =
      (∏ v : {v // v ∈ T ∩ X}, if a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
        xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) *
      ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T \ X, kfac M Finset.univ (fill U T a w) v := by
  unfold Q
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun w => ?_)
  rw [← Finset.prod_inter_mul_prod_diff T X]
  congr 1
  · rw [← Finset.prod_coe_sort (T ∩ X)]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [kfac_doModel, dif_pos (Finset.mem_inter.mp v.2).2]
    have hf := fill_x U T (Finset.mem_compl.mp (hXO (Finset.mem_inter.mp v.2).2)) a w
    by_cases h : a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
        xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ <;> simp [hf, h]
  · exact Finset.prod_congr rfl (fun v hv => by
      rw [kfac_doModel, dif_neg (Finset.mem_sdiff.mp hv).2])

/-- Summen over verdiene til `X ∩ T` fjerner kjernene til `X ∩ T` fra `Q[T]`. -/
lemma sum_block [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T X : Finset V)
    (hXO : X ⊆ Uᶜ) (hch : ∀ x ∈ T ∩ X, ∀ v ∈ T, ¬ G.edge x v) (a : Assignment (α := α) Uᶜ) :
    ∑' x' : Assignment (α := α) (T ∩ X), Q M U T (updX U (T ∩ X) a x') =
      ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ T \ X, kfac M Finset.univ (fill U T a w) v := by
  rw [sum_Q_updX M U T (T ∩ X) (fun v hv => hXO (Finset.mem_inter.mp hv).2)
    Finset.inter_subset_left hch a, Finset.sdiff_inter_self_left]

/-- **Formelen med én sum per blokk.** -/
theorem tian_formula_blocks [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι]
    (M : G.CausalModel α) (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (X : Finset V) (hXO : X ⊆ Uᶜ)
    (hch : ∀ i ∈ I, ∀ x ∈ B i ∩ X, ∀ v ∈ B i, ¬ G.edge x v)
    (xv : Assignment (α := α) X) (a : Assignment (α := α) Uᶜ) :
    (doModel M X xv).marginal Uᶜ a =
      ∏ i ∈ I, ((∏ v : {v // v ∈ B i ∩ X}, if a ⟨v.1, hXO (Finset.mem_inter.mp v.2).2⟩ =
          xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) *
        ∑' x' : Assignment (α := α) (B i ∩ X), Q M U (B i) (updX U (B i ∩ X) a x')) := by
  rw [marginal_prod (doModel M X xv) U B I
    (fun i hi => by
      intro u hu v e
      exact hcl i hi u hu v (show G.edge u v ∧ v ∉ X from e).1) hdisj hcov a]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Q_do_gen M U (B i) X hXO xv a, sum_block M U (B i) X hXO (hch i hi) a]

/-- **Identifiserbarhet med blokker.** -/
theorem tian_identifiable_blocks [∀ v, Nonempty (α v)] {ι : Type*} [DecidableEq ι]
    (U : Finset V) (B : ι → Finset V) (I : Finset ι)
    (hcl : ∀ i ∈ I, IsClosedBlock G U (B i))
    (hdisj : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (B i) (B k))
    (hcov : ∀ v, ∃ i ∈ I, v ∈ B i) (X : Finset V) (hXO : X ⊆ Uᶜ)
    (hch : ∀ i ∈ I, ∀ x ∈ B i ∩ X, ∀ v ∈ B i, ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  unfold Identifiable
  intro M1 M2 hM hpos t
  have hQ : ∀ i ∈ I, ∀ b, Q M1 U (B i) b = Q M2 U (B i) b := fun i hi b =>
    (Q_identifiable M1 M2 U (B i) (hcl i hi) hM hpos b).1
  have hD : ∀ xv : Assignment (α := α) X,
      (doModel M1 X xv).marginal Uᶜ = (doModel M2 X xv).marginal Uᶜ := by
    intro xv
    ext a
    rw [tian_formula_blocks M1 U B I hcl hdisj hcov X hXO hch xv a,
      tian_formula_blocks M2 U B I hcl hdisj hcov X hXO hch xv a]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [hQ i hi]
  rw [← marginal_restrict _ hY, ← marginal_restrict _ hY, hD]

lemma latStep_symm {U : Finset V} {a b : V} (h : latStep G U a b) : latStep G U b a :=
  Or.symm h

/-- To noder i samme c-komponent har samme c-komponent. -/
lemma ccomp_eq_of_mem {U : Finset V} {x v : V} (h : v ∈ ccomp G U x) :
    ccomp G U v = ccomp G U x := by
  have hsymm : Symmetric (Relation.ReflTransGen (latStep G U)) :=
    Relation.ReflTransGen.symmetric (fun _ _ h => latStep_symm h)
  have hxv := mem_ccomp.mp h
  ext w
  rw [mem_ccomp, mem_ccomp]
  exact ⟨fun hvw => hxv.trans hvw, fun hxw => (hsymm hxv).trans hxw⟩

/-- **Tians teorem for mengder.** Har ingen `x ∈ X` et barn i sin egen c-komponent, er
effekten av `X` på enhver mengde observerte `Y` identifiserbar. -/
theorem tian_identifiable_sets [∀ v, Nonempty (α v)] (U X : Finset V)
    (hX : ∀ x ∈ X, x ∉ U) (hch : ∀ x ∈ X, ∀ v ∈ ccomp G U x, ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y := by
  refine tian_identifiable_blocks U id (Finset.univ.image (ccomp G U)) ?_ ?_ ?_ X
    (fun x hx => Finset.mem_compl.mpr (hX x hx)) ?_ Y hY
  · intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    exact ccomp_closed G U y
  · intro i hi k hk hik
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.disjoint_left]
    intro v hvy hvz
    exact hik ((ccomp_eq_of_mem hvy).symm.trans (ccomp_eq_of_mem hvz))
  · intro v
    exact ⟨ccomp G U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, self_mem_ccomp G U v⟩
  · intro i hi x hx v hv
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hi
    have hxy : x ∈ ccomp G U y := (Finset.mem_inter.mp hx).1
    exact hch x (Finset.mem_inter.mp hx).2 v (by rw [ccomp_eq_of_mem hxy]; exact hv)

end CFactor
end Identification

#print axioms Identification.CFactor.tian_formula_blocks
#print axioms Identification.CFactor.tian_identifiable_blocks
#print axioms Identification.CFactor.tian_identifiable_sets

/-! ## Runde 28: hver faktor er en kausal effekt (`Q[S] = P_{do(O ∖ S)}`)

ID-algoritmens linje 4 og 7 kaller seg selv på faktorene `Q[Sᵢ]`. Det gir bare mening fordi
hver faktor er en kausal effekt: fastholdes alle observerte utenfor en lukket blokk `S`,
er fordelingen på de observerte nettopp `Q[S]` (`Q_causal`):

  `P_{do(X = x)}(O = a) = [a_X = x] · Q[S](a)`,   `X = Sᶜ ∖ U`.

1. `lat_one`: summert over de latente i en mengde er produktet av deres kjerner 1. Det
   følger direkte av `sum_compl_kfac_eq_one` (kjedeegenskapen) ved å telle om
   (`fill_iff`).
2. I intervensjonsmodellen er faktoren for `S` uendret, og faktoren for `Sᶜ` er
   indikatoren for `X` ganger kjernene til de latente i `Sᶜ`, som summerer til 1. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

lemma fill_out [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w w' : Assignment (α := α) (U ∩ T)) (v : V) (hv : v ∉ U ∩ T) :
    fill U T a w ⟨v, Finset.mem_univ v⟩ = fill U T a w' ⟨v, Finset.mem_univ v⟩ := by
  by_cases h0 : v ∈ U
  · have hT : v ∉ T := fun h => hv (Finset.mem_inter.mpr ⟨h0, h⟩)
    simp [fill, h0, hT]
  · simp [fill, h0]

/-- En full tilordning er en `fill` nøyaktig når den stemmer med `fill` utenfor de latente
i `T`; da er `w` dens restriksjon. -/
lemma fill_iff [∀ v, Nonempty (α v)] (U T : Finset V) (a : Assignment (α := α) Uᶜ)
    (w0 w : Assignment (α := α) (U ∩ T)) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    u = fill U T a w ↔
      u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
        (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ) ∧
      w = u.restrict (Finset.subset_univ (U ∩ T)) := by
  constructor
  · rintro rfl
    constructor
    · funext ⟨v, hv⟩
      simp only [Assignment.restrict]
      exact fill_out U T a w w0 v (Finset.mem_compl.mp hv)
    · funext ⟨v, hv⟩
      obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      simp [fill, Assignment.restrict, h0, h1]
  · rintro ⟨hb, rfl⟩
    funext ⟨v, _⟩
    by_cases hv : v ∈ U ∩ T
    · obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
      simp [fill, Assignment.restrict, h0, h1]
    · have e := congrFun hb ⟨v, Finset.mem_compl.mpr hv⟩
      simp only [Assignment.restrict] at e
      rw [e]
      exact fill_out U T a w0 _ v hv

/-- **De latente summerer til 1.** -/
theorem lat_one [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U T : Finset V)
    (a : Assignment (α := α) Uᶜ) :
    ∑' w : Assignment (α := α) (U ∩ T), ∏ v ∈ U ∩ T, kfac M Finset.univ (fill U T a w) v = 1 := by
  have w0 : Assignment (α := α) (U ∩ T) := fun _ => Classical.arbitrary _
  have key := sum_compl_kfac_eq_one M (U ∩ T)ᶜ
    ((fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ))
  rw [compl_compl] at key
  refine Eq.trans ?_ key
  symm
  calc ∑' u : Assignment (α := α) (Finset.univ : Finset V),
        (if u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
          (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ) then (1 : ENNReal) else 0) *
          ∏ v ∈ U ∩ T, kfac M Finset.univ u v
      = ∑' u : Assignment (α := α) (Finset.univ : Finset V),
          ∑' w : Assignment (α := α) (U ∩ T),
            (if u = fill U T a w then ∏ v ∈ U ∩ T, kfac M Finset.univ u v else 0) := by
        refine tsum_congr (fun u => ?_)
        by_cases hu : u.restrict (Finset.subset_univ (U ∩ T)ᶜ) =
            (fill U T a w0).restrict (Finset.subset_univ (U ∩ T)ᶜ)
        · rw [if_pos hu, one_mul, tsum_eq_single (u.restrict (Finset.subset_univ (U ∩ T)))]
          · rw [if_pos ((fill_iff U T a w0 _ u).mpr ⟨hu, rfl⟩)]
          · intro w hw
            rw [if_neg (fun h => hw ((fill_iff U T a w0 w u).mp h).2)]
        · rw [if_neg hu, zero_mul]
          symm
          exact ENNReal.tsum_eq_zero.mpr (fun w =>
            if_neg (fun h => hu ((fill_iff U T a w0 w u).mp h).1))
    _ = ∑' w : Assignment (α := α) (U ∩ T),
          ∑' u : Assignment (α := α) (Finset.univ : Finset V),
            (if u = fill U T a w then ∏ v ∈ U ∩ T, kfac M Finset.univ u v else 0) :=
        ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr (fun w => ?_)
        rw [tsum_eq_single (fill U T a w)]
        · simp
        · intro u hu
          rw [if_neg hu]

/-- **Hver faktor er en kausal effekt.** Fastholdes de observerte utenfor en lukket blokk
`S`, er fordelingen på de observerte indikatoren ganger `Q[S]`. -/
theorem Q_causal [∀ v, Nonempty (α v)] (M : G.CausalModel α) (U S : Finset V)
    (hcl : IsClosedBlock G U S) (xv : Assignment (α := α) (Sᶜ \ U))
    (a : Assignment (α := α) Uᶜ) :
    (doModel M (Sᶜ \ U) xv).marginal Uᶜ a =
      (∏ v : {v // v ∈ Sᶜ ∩ (Sᶜ \ U)},
        if a ⟨v.1, (show Sᶜ \ U ⊆ Uᶜ from fun _ hz =>
            Finset.mem_compl.mpr (Finset.mem_sdiff.mp hz).2) (Finset.mem_inter.mp v.2).2⟩ =
          xv ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ then (1 : ENNReal) else 0) * Q M U S a := by
  have hXO : Sᶜ \ U ⊆ Uᶜ := fun _ hz => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hz).2
  have hcl' : IsClosedBlock (cutIn G (Sᶜ \ U)) U S := by
    intro u hu v e
    exact hcl u hu v (show G.edge u v ∧ v ∉ Sᶜ \ U from e).1
  have h1 : Q (doModel M (Sᶜ \ U) xv) U S a = Q M U S a := by
    unfold Q
    refine tsum_congr (fun w => Finset.prod_congr rfl (fun v hv => ?_))
    have hvX : v ∉ Sᶜ \ U := fun h =>
      (Finset.mem_compl.mp (Finset.mem_sdiff.mp h).1) hv
    rw [kfac_doModel, dif_neg hvX]
  have hset : Sᶜ \ (Sᶜ \ U) = U ∩ Sᶜ := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [marginal_factor (doModel M (Sᶜ \ U) xv) U S hcl' a, h1,
    Q_do_gen M U Sᶜ (Sᶜ \ U) hXO xv a, hset, lat_one, mul_one, mul_comm]

end CFactor
end Identification

#print axioms Identification.CFactor.lat_one
#print axioms Identification.CFactor.Q_causal

/-! ## Runde 29: rydding — runde 25 som korollarer

`tian_identifiable_sets` (runde 27) er det generelle teoremet for mengder. Teoremene fra
runde 25 følger av det: en lukket blokk `S ⊇ X` inneholder c-komponenten til hver `x ∈ X`
(`ccomp_subset`), og unionen av c-komponentene inneholder hver av dem. `tian_formulaX` og
`Q_doX` er fjernet; `tian_formula_blocks` og `Q_do_gen` dekker dem. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- **Tians teorem for en mengde `X` i en lukket blokk.** -/
theorem tian_identifiableX [∀ v, Nonempty (α v)] (U S X : Finset V)
    (hXO : X ⊆ Uᶜ) (hXS : X ⊆ S) (hch : ∀ x ∈ X, ∀ v ∈ S, ¬ G.edge x v)
    (hcl : ∀ u ∈ U, ∀ v, G.edge u v → (u ∈ S ↔ v ∈ S)) (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X (fun _ hx => Finset.mem_compl.mp (hXO hx))
    (fun x hx v hv => hch x hx v (ccomp_subset hcl (hXS hx) hv)) Y hY

/-- **Med unionen av c-komponentene.** -/
theorem tian_identifiable_ccompX [∀ v, Nonempty (α v)] (U X : Finset V)
    (hX : ∀ x ∈ X, x ∉ U) (hch : ∀ x ∈ X, ∀ v ∈ X.biUnion (ccomp G U), ¬ G.edge x v)
    (Y : Finset V) (hY : Y ⊆ Uᶜ) :
    Identifiable G α Uᶜ X Y :=
  tian_identifiable_sets U X hX
    (fun x hx v hv => hch x hx v (Finset.mem_biUnion.mpr ⟨x, hx, hv⟩)) Y hY

end CFactor
end Identification

#print axioms Identification.CFactor.tian_identifiableX
#print axioms Identification.CFactor.tian_identifiable_ccompX
