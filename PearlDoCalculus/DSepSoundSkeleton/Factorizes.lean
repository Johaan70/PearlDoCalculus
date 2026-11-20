import PearlDoCalculus.DSepSoundSkeleton.AssignmentCasts
/-!
# Factorisation of `jointUpTo` along a separator

Layer 1b of the Lauritzen route to soundness of d-separation (`DSepSound.dsep_sound`).
It proves that the partial joint `jointUpTo` factorises into a left part and a right part
when the two sides are separated by a set `Z`. The lemmas are: the `nil` case of the
strengthened factorisation for `extendOverList`, the vanishing of `extendOverList` on
assignments that do not extend the base, the collapse of the `bind` sum in
`jointUpTo (n+1)` to a single term, the factorisation for `extendOverList` over a list,
the factorisation `jointUpTo_factorizes` itself (by induction on the rank level), and the
explicit product form `extendOverList_apply_prod`.
-/

set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel

/-- `nil`-tilfellet av den styrkede faktoriseringen, med `base` som
eksplisitt argument til `F` og `Gf`.

Koblingen mellom `indicator_splits` (som lever helt over `B`) og
`extendOverList_nil` (der `a` lever på `B ∪ [].toFinset`). `convert ... using 2`
gir tre delmål: en `Iff` for indikatorbetingelsen, og to `Eq ENNReal` for
`F0`- og `Gf0`-anvendelsene. -/
lemma extendOverList_factorizes_nil (M : CausalModel G α) (L R B : Finset V)
    (hLR : B ∪ ([] : List V).toFinset ⊆ L ∪ R)
    (hpar : ∀ w ∈ ([] : List V), G.parents w ⊆ B) :
    ∃ (F : Assignment (α := α) (L ∩ B) →
           Assignment (α := α) (L ∩ (B ∪ ([] : List V).toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) →
            Assignment (α := α) (R ∩ (B ∪ ([] : List V).toFinset)) → ENNReal),
      ∀ (base : Assignment (α := α) B)
        (a : Assignment (α := α) (B ∪ ([] : List V).toFinset)),
        (extendOverList M B base [] hpar) a =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  have hB : B ⊆ L ∪ R := fun x hx => hLR (Finset.mem_union_left _ hx)
  obtain ⟨F0, Gf0, hF0⟩ := indicator_splits (α := α) L R B hB
  refine ⟨fun bp p => F0 bp (cast (by simp) p),
          fun bq q => Gf0 bq (cast (by simp) q), ?_⟩
  intro base a
  rw [extendOverList_nil]
  have hx := hF0 base (cast (by simp) a)
  simp only [eq_comm] at hx ⊢
  convert hx using 2
  · rw [eq_comm, cast_eq_iff_eq_cast_symm, eq_comm]
  · exact congrArg (F0 _) (restrict_cast_comm L (B ∪ ([] : List V).toFinset) B (by simp) (by simp) (by simp) a).symm
  · exact congrArg (Gf0 _) (restrict_cast_comm R (B ∪ ([] : List V).toFinset) B (by simp) (by simp) (by simp) a).symm



/-- `extendOverList` er null når tilordningen ikke utvider `base`.

Dette er brikken som får `bind`-summen i `jointUpTo_factorizes` sitt
`succ`-steg til å kollapse: bare den ene mellomtilstanden som stemmer med
`a` bidrar. Uten den går summen også over `Z`-delen, og faktoriseringen
ødelegges.

Merk plasseringen: lemmaet bruker både `extendOverList_cons'` og
`restrict_cast_eq`, så det må stå etter begge. -/
lemma extendOverList_eq_zero_of_ne (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (l : List V)
    (hpar : ∀ w ∈ l, G.parents w ⊆ B)
    (hnodup : l.Nodup)
    (hdisj : ∀ w ∈ l, w ∉ B)
    (a : Assignment (α := α) (B ∪ l.toFinset))
    (hne : a.restrict Finset.subset_union_left ≠ base) :
    (extendOverList M B base l hpar) a = 0 := by
  induction l with
  | nil =>
    rw [extendOverList_nil]
    rw [if_neg]
    intro heq
    apply hne
    subst heq
    have hB : B ∪ ([] : List V).toFinset = B := by simp
    rw [restrict_cast_eq]
    · rfl
    · exact hB
    · exact Finset.Subset.refl B
  | cons v vs ih =>
    have hv : v ∉ B ∪ vs.toFinset := by
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact hdisj v List.mem_cons_self h
      · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
    have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
        = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
      congr 1
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    have hab : a = cast htype (cast htype.symm a) := by simp
    rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a)]
    have hzero : (M.extendOverList B base vs
        (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        ((cast htype.symm a).restrict (Finset.subset_insert v (B ∪ vs.toFinset))) = 0 := by
      apply ih
      · exact (List.nodup_cons.mp hnodup).2
      · exact fun w hw => hdisj w (List.mem_cons_of_mem v hw)
      · rw [Assignment.restrict_restrict, restrict_cast_eq]
        · exact hne
        · simp
    rw [hzero, zero_mul]
/-- Spesialisering av `extendOverList_eq_zero_of_ne` til rangnivåene i
`jointUpTo`. Hypotesene om duplikatfrihet og disjunkthet er utledet fra
`newAtRank`, så kallstedet slipper å gjenta argumentet. -/
lemma extendOverList_level_eq_zero_of_ne (M : CausalModel G α) (n : ℕ)
    (b : Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset))
    (a1 : Assignment (α := α) (G.verticesUpTo n))
    (hne : a1 ≠ b.restrict Finset.subset_union_left) :
    (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
      (jointUpTo._proof_6 n)) b = 0 := by
  apply extendOverList_eq_zero_of_ne
  · exact Finset.nodup_toList _
  · intro w hw
    have hw2 : w ∈ G.newAtRank (n + 1) := by simpa using hw
    simp only [newAtRank, Finset.mem_filter] at hw2
    simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · exact fun h => hne h.symm
/-- `bind`-summen i `jointUpTo (n+1)` kollapser til ett ledd: bare den
mellomtilstanden som stemmer med `b` bidrar. -/
lemma jointUpTo_bind_collapse (M : CausalModel G α) (n : ℕ)
    (b : Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset)) :
    (∑' a1 : Assignment (α := α) (G.verticesUpTo n),
      (M.jointUpTo n) a1 *
        (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n)) b)
    = (M.jointUpTo n) (b.restrict Finset.subset_union_left) *
        (M.extendOverList (G.verticesUpTo n) (b.restrict Finset.subset_union_left)
          (G.newAtRank (n + 1)).toList (jointUpTo._proof_6 n)) b := by
  have step : ∀ a1 : Assignment (α := α) (G.verticesUpTo n),
      (M.jointUpTo n) a1 *
        (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n)) b
      = if a1 = b.restrict Finset.subset_union_left then
          (M.jointUpTo n) a1 *
            (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
              (jointUpTo._proof_6 n)) b
        else 0 := by
    intro a1
    by_cases h : a1 = b.restrict Finset.subset_union_left
    · rw [if_pos h]
    · rw [if_neg h, extendOverList_level_eq_zero_of_ne M n b a1 h, mul_zero]
  rw [tsum_congr step]
  rw [tsum_ite_eq]



lemma extendOverList_factorizes' (M : CausalModel G α) (L R B : Finset V) (l : List V)
    (hpar : ∀ w ∈ l, G.parents w ⊆ B)
    (hLR : B ∪ l.toFinset ⊆ L ∪ R)
    (hnodup : l.Nodup)
    (hdisj : ∀ w ∈ l, w ∉ B)
    (hclique : ∀ w ∈ l, (insert w (G.parents w) ⊆ L) ∨ (insert w (G.parents w) ⊆ R)) :
    ∃ (F : Assignment (α := α) (L ∩ B) →
           Assignment (α := α) (L ∩ (B ∪ l.toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) →
            Assignment (α := α) (R ∩ (B ∪ l.toFinset)) → ENNReal),
      ∀ (base : Assignment (α := α) B) (a : Assignment (α := α) (B ∪ l.toFinset)),
        (extendOverList M B base l hpar) a =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  induction l with
  | nil => exact extendOverList_factorizes_nil M L R B hLR hpar
  | cons v vs ih =>
    have hpar2 : ∀ w ∈ vs, G.parents w ⊆ B := fun w hw => hpar w (List.mem_cons_of_mem v hw)
    have hsub : B ∪ vs.toFinset ⊆ B ∪ (v :: vs).toFinset := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (by simp at h ⊢; tauto)
    have hLR2 : B ∪ vs.toFinset ⊆ L ∪ R := fun x hx => hLR (hsub hx)
    have hnodup2 : vs.Nodup := (List.nodup_cons.mp hnodup).2
    have hdisj2 : ∀ w ∈ vs, w ∉ B := fun w hw => hdisj w (List.mem_cons_of_mem v hw)
    have hclique2 : ∀ w ∈ vs, insert w (G.parents w) ⊆ L ∨ insert w (G.parents w) ⊆ R :=
      fun w hw => hclique w (List.mem_cons_of_mem v hw)
    obtain ⟨F0, Gf0, hF0⟩ := ih hpar2 hLR2 hnodup2 hdisj2 hclique2
    rcases hclique v List.mem_cons_self with hcl | hcl
    · refine ⟨fun bp p => F0 bp (p.restrict (inter_mono_cons L B v vs)) *
        (M.kernel v (p.restrict (parents_subset_inter L B v vs (hpar v List.mem_cons_self) hcl)))
          (p ⟨v, self_mem_inter L B v vs hcl⟩),
        fun bq q => Gf0 bq (q.restrict (inter_mono_cons R B v vs)), ?_⟩
      intro base a
      have hv : v ∉ B ∪ vs.toFinset := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hdisj v List.mem_cons_self h
        · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
      have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
          = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
        congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      have hab : a = cast htype (cast htype.symm a) := by simp
      rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a), hF0]
      simp only [Assignment.restrict_restrict]
      simp only [cast_cast, cast_eq]
      simp only [Assignment.restrict]
      rw [restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (intro x hx; simp at hx ⊢; tauto)
        | skip
      rw [cast_apply_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | ring
        | simp
    · refine ⟨fun bp p => F0 bp (p.restrict (inter_mono_cons L B v vs)),
        fun bq q => Gf0 bq (q.restrict (inter_mono_cons R B v vs)) *
          (M.kernel v (q.restrict (parents_subset_inter R B v vs (hpar v List.mem_cons_self) hcl)))
            (q ⟨v, self_mem_inter R B v vs hcl⟩), ?_⟩
      intro base a
      have hv : v ∉ B ∪ vs.toFinset := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hdisj v List.mem_cons_self h
        · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
      have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
          = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
        congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      have hab : a = cast htype (cast htype.symm a) := by simp
      rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a), hF0]
      simp only [Assignment.restrict_restrict]
      simp only [cast_cast, cast_eq]
      simp only [Assignment.restrict]
      rw [restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (intro x hx; simp at hx ⊢; tauto)
        | skip
      rw [cast_apply_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | ring
        | simp
/-- `jointUpTo` faktoriserer langs en separator: en `L`-del og en `R`-del,
begge med `Z` som felles argument.
Tre formuleringer ble prøvd. Todelt med `L ∩ ...` og `R ∩ ...` uten `Z`:
`bind` splitter ikke, siden delene overlapper på separatoren. Tredelt med
faste `L`, `Z`, `R` og `hcover : verticesUpTo n = L ∪ R ∪ Z`:
induksjonshypotesen blir ubrukelig, fordi den krever at nivå `n` dekker
samme mengder som `n+1`.

Denne formen virker: `L`, `Z`, `R` er globale og dekker `univ`, snittene med
`verticesUpTo n` vokser med `n`, og `hclique` er uavhengig av `n`. Da kommer
`ih` uten betingelser — verifisert.

Merk om `succ`-steget: `hclique` deler ikke nodene på nivå `n+1` disjunkt i
en `L`-liste og en `R`-liste. En node i `Z` oppfyller begge disjunkter, så
plasseringen må velges konsistent i faktoriseringen. Det er ikke en
teknikalitet — det er der separatoren faktisk gjør arbeid. -/
lemma jointUpTo_factorizes (M : CausalModel G α) (L Z R : Finset V) (n : ℕ)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) (L ∩ G.verticesUpTo n) →
           Assignment (α := α) (Z ∩ G.verticesUpTo n) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ G.verticesUpTo n) →
            Assignment (α := α) (Z ∩ G.verticesUpTo n) → ENNReal),
      ∀ a : Assignment (α := α) (G.verticesUpTo n),
        (jointUpTo M n) a =
          F (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) *
          Gf (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) := by
  induction n with
  | zero =>
    have hLR2 : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
      intro x _
      have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    obtain ⟨F0, Gf0, hF0⟩ := extendOverList_factorizes' M (L ∪ Z) (R ∪ Z) ∅
      (G.verticesUpTo 0).toList jointUpTo._proof_4 hLR2 (Finset.nodup_toList _)
      (fun w _ => by simp) (fun w _ => hclique w)
    refine ⟨fun p q => F0 (fun v => absurd v.2 (by simp))
        (joinInter L Z _ (by simpa using p) (by simpa using q)),
      fun p q => Gf0 (fun v => absurd v.2 (by simp))
        (joinInter R Z _ (by simpa using p) (by simpa using q)), ?_⟩
    intro a
    rw [jointUpTo_zero_apply]
    have hx := hF0 (fun v => absurd v.2 (Finset.notMem_empty _)) (cast (by simp) a)
    rw [hx]
    congr 1
    all_goals congr 1
    all_goals first
      | (funext u; exact absurd (Finset.mem_inter.mp u.2).2 (Finset.notMem_empty _))
      | simp [← joinInter_restrict, restrict_cast_eq, cast_restrict_eq]
  | succ n ih =>
    obtain ⟨F0, Gf0, hF0⟩ := ih
    have hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        = G.verticesUpTo (n + 1) := by
      rw [G.verticesUpTo_succ n]
      simp
    have htype2 : Assignment (α := α) (G.verticesUpTo (n + 1))
        = Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) := by
      rw [hset]
    have hLR2 : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
      intro x _
      have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    have hdisjN : ∀ w ∈ (G.newAtRank (n + 1)).toList, w ∉ G.verticesUpTo n := by
      intro w hw
      have hw2 : w ∈ G.newAtRank (n + 1) := by simpa using hw
      simp only [newAtRank, Finset.mem_filter] at hw2
      simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    obtain ⟨F1, Gf1, hF1⟩ := extendOverList_factorizes' M (L ∪ Z) (R ∪ Z)
      (G.verticesUpTo n) (G.newAtRank (n + 1)).toList (jointUpTo._proof_6 n) hLR2
      (Finset.nodup_toList _) hdisjN (fun w _ => hclique w)
    refine ⟨fun p q =>
        F0 (p.restrict (inter_verticesUpTo_mono_succ L n))
          (q.restrict (inter_verticesUpTo_mono_succ Z n)) *
        F1 ((joinInter L Z (G.verticesUpTo (n + 1)) p q).restrict
            (inter_verticesUpTo_mono_succ (L ∪ Z) n))
          ((joinInter L Z (G.verticesUpTo (n + 1)) p q).restrict (by rw [hset])),
      fun p q =>
        Gf0 (p.restrict (inter_verticesUpTo_mono_succ R n))
          (q.restrict (inter_verticesUpTo_mono_succ Z n)) *
        Gf1 ((joinInter R Z (G.verticesUpTo (n + 1)) p q).restrict
            (inter_verticesUpTo_mono_succ (R ∪ Z) n))
          ((joinInter R Z (G.verticesUpTo (n + 1)) p q).restrict (by rw [hset])), ?_⟩
    case _ =>
      intro a
      rw [jointUpTo_succ_apply M n hset htype2, PMF.bind_apply, jointUpTo_bind_collapse]
      have hx0 := hF0 ((cast htype2 a).restrict Finset.subset_union_left)
      have hx1 := hF1 ((cast htype2 a).restrict Finset.subset_union_left) (cast htype2 a)
      rw [hx0, hx1]
      simp only [Assignment.restrict_restrict]
      rw [joinInter_restrict L Z (G.verticesUpTo (n + 1)) a,
        joinInter_restrict R Z (G.verticesUpTo (n + 1)) a]
      simp only [Assignment.restrict_restrict]
      rw [restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1))]
      all_goals first
        | exact hset
        | (intro x hx; rw [← hset]; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
        | (intro x hx; rw [← hset]; exact (Finset.mem_inter.mp hx).2)
        | skip
      ring



/-- Eksplisitt produktform for `extendOverList`: indikator på basen
ganger kjernene til de nye nodene, som listeprodukt så induksjonen følger
`extendOverList_cons'`. Alle foreldre ligger i `B`, så kjerne-input er
`base` restriktert. -/
lemma extendOverList_apply_prod (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) :
    ∀ (l : List V) (hpar : ∀ v ∈ l, G.parents v ⊆ B),
      l.Nodup → (∀ v ∈ l, v ∉ B) →
      ∀ b : Assignment (α := α) (B ∪ l.toFinset),
        (extendOverList M B base l hpar) b =
          (if b.restrict Finset.subset_union_left = base then 1 else 0) *
          (l.attach.map (fun w => M.kernel w.1 (base.restrict (hpar w.1 w.2))
              (b ⟨w.1, Finset.mem_union_right B (List.mem_toFinset.mpr w.2)⟩))).prod := by
  intro l
  induction l with
  | nil =>
    intro hpar _ _ b
    have hB : B ∪ ([] : List V).toFinset = B := by simp
    rw [extendOverList_nil]
    simp only [List.attach_nil, List.map_nil, List.prod_nil, mul_one]
    by_cases hb : b.restrict Finset.subset_union_left = base
    · rw [if_pos hb, if_pos]
      funext ⟨x, hx⟩
      rw [cast_apply_eq _ _ hB _ base x hx (by simpa using hx)]
      exact congrFun hb ⟨x, _⟩
    · rw [if_neg hb, if_neg]
      intro h
      apply hb
      funext ⟨x, hx⟩
      rw [h]
      exact cast_apply_eq _ _ hB _ base x _ hx
  | cons v vs ih =>
    intro hpar hnd hdisj b
    have hnd' := List.nodup_cons.mp hnd
    have hv : v ∉ B ∪ vs.toFinset := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hdisj v List.mem_cons_self h
      · exact hnd'.1 (List.mem_toFinset.mp h)
    have hset : insert v (B ∪ vs.toFinset) = B ∪ (v :: vs).toFinset := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_cons]
      tauto
    have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
        = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by rw [hset]
    obtain ⟨b', rfl⟩ : ∃ b', b = cast htype b' := ⟨cast htype.symm b, by simp⟩
    have hBsub : B ⊆ insert v (B ∪ vs.toFinset) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    have hev : ∀ (x : V) (hx : x ∈ B ∪ (v :: vs).toFinset),
        (cast htype b') ⟨x, hx⟩ = b' ⟨x, by rw [hset]; exact hx⟩ :=
      fun x hx => cast_apply_eq _ _ hset.symm htype b' x hx _
    rw [extendOverList_cons' M B base v vs hpar hv htype b',
      ih _ hnd'.2 (fun w hw => hdisj w (List.mem_cons_of_mem v hw)),
      restrict_cast_eq _ _ _ hset.symm htype b' Finset.subset_union_left hBsub]
    have hcond : (b'.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
        Finset.subset_union_left = b'.restrict hBsub := rfl
    rw [hcond]
    simp only [List.attach_cons, List.map_cons, List.map_map, List.prod_cons, hev]
    by_cases hc : b'.restrict hBsub = base
    · have hk : (b'.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))
          = base.restrict (hpar v List.mem_cons_self) := by
        subst hc; rfl
      rw [hk]
      simp only [if_pos hc, one_mul]
      rw [mul_comm]
      congr 1
    · simp only [if_neg hc, zero_mul]

end PearlDoCalculus
