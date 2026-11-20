import PearlDoCalculus.DSepSoundSkeleton.Basic
/-!
# Casts and splits of assignments

Layer 1a of the Lauritzen route to soundness of d-separation (`DSepSound.dsep_sound`).
It collects the bookkeeping lemmas about assignments that later layers need: the
parents of an induced vertex, `extend` as a characterisation of equal assignments, the
`nil` and `cons` unfoldings of `extendOverList`, the splitting of indicators, the
`jointUpTo` and `fullJoint` evaluation lemmas, and the `restrict_cast_*` family, which says
that restriction commutes with transport along equalities of finsets.
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
/-! ## Layer 1 — ancestral reduction

Marginalising the joint onto an ancestrally closed set yields the joint of
the induced model.

**Use `G.rank`.** `rank_le_of_reaches` gives strong induction on the
maximum rank among non-ancestors without constructing a topological order.

Sketch: let `v` be a non-ancestor of maximal rank. No vertex of `A` has
`v` as a parent — otherwise `v` would be an ancestor. So `v` occurs in
exactly one factor, `P(v | parents v)`, which sums to 1 over `α v`. Sum it
out and recurse. `PMF.bind`, `Finset.sum_comm` and `tsum_eq_sum` do the
work.
-/
/-- For noder i en ancestralt lukket mengde er foreldrene uendret av `induce`. -/
lemma DAG.induce_parents_eq (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (v : V) (hv : v ∈ A) :
    (DAG.induce G A).parents v = G.parents v := by
  ext u
  simp [DAG.parents, DAG.induce]
  constructor
  · exact fun h => h.2.2
  · exact fun he => ⟨hA v hv u he, hv, he⟩
/-- Indikatoren `b = extend asg x` bestemmer både `asg` og `x` entydig.
Nøkkelen til å kollapse dobbeltsummen i `extendOverList`. -/
lemma extend_eq_iff (S : Finset V) (v : V) (hvS : v ∉ S)
    (b : Assignment (α := α) (insert v S))
    (asg : Assignment (α := α) S) (x : α v) :
    (Assignment.extend asg x = b) ↔
      (asg = b.restrict (Finset.subset_insert v S) ∧
       x = b ⟨v, Finset.mem_insert_self v S⟩) := by
  constructor
  · intro hb
    subst hb
    constructor
    · funext u
      simp [Assignment.extend, Assignment.restrict]
      intro hu
      exact absurd (hu ▸ u.2) hvS
    · simp [Assignment.extend]
  · rintro ⟨h1, h2⟩
    subst h1
    subst h2
    funext u
    by_cases hv : u.1 = v
    · have : u = ⟨v, Finset.mem_insert_self v S⟩ := Subtype.ext hv
      subst this
      simp [Assignment.extend]
    · have huS : u.1 ∈ S := by
        rcases Finset.mem_insert.mp u.2 with h | h
        · exact absurd h hv
        · exact h
      simp [Assignment.extend, Assignment.restrict, hv, huS]

/-- `extendOverList` på tom liste er punktmassen på `base`.

Merk teknikken for `cast`: `rw! (castMode := .all)` flytter mengden, og
`simp [eqRec_eq_cast, cast_cast]` opphever transportene. Den kombinasjonen
er nøkkelen til alt arbeid med `extendOverList` og `jointUpTo`. -/
lemma extendOverList_nil (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B)
    (hpar : ∀ v ∈ ([] : List V), G.parents v ⊆ B)
    (a : Assignment (α := α) (B ∪ ([] : List V).toFinset)) :
    (extendOverList M B base [] hpar) a = if a = cast (by simp) base then 1 else 0 := by
  have hB : B ∪ ([] : List V).toFinset = B := by simp
  rw! (castMode := .all) [hB]
  simp [extendOverList, eqRec_eq_cast, cast_cast, PMF.pure_apply]
/-- Flytter en `cast` fra den ene siden av en likhet til den andre. -/
lemma cast_eq_iff_eq_cast_symm {A B : Sort _} (h : A = B) (b : A) (a : B) :
    (cast h b = a) ↔ (b = cast h.symm a) := by
  subst h
  simp

/-- `extendOverList` på en ikke-tom liste faktoriserer: halens fordeling
ganger kjernen for hodet. Kjeden av `cast`-omskrivinger er den samme som i
`extendOverList_nil`, med `extend_eq_iff` for kollapsen. -/
lemma extendOverList_cons (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hv : v ∉ B ∪ vs.toFinset)
    (htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
      = Assignment (α := α) (B ∪ (v :: vs).toFinset))
    (a : Assignment (α := α) (B ∪ (v :: vs).toFinset)) :
    (extendOverList M B base (v :: vs) hpar) a =
      (extendOverList M B base vs (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        ((cast htype.symm a).restrict (Finset.subset_insert v (B ∪ vs.toFinset))) *
      (M.kernel v (((cast htype.symm a).restrict
          (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        ((cast htype.symm a) ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  simp only [extendOverList, PMF.bind_apply, PMF.map_apply, eq_comm (a := a)]
  simp only [cast_eq_iff_heq]
  simp only [← cast_eq_iff_heq (e := htype)]
  simp only [cast_eq_iff_eq_cast_symm]
  simp only [extend_eq_iff _ v hv]
  simp only [and_comm, ite_and, tsum_ite_eq]
  simp only [mul_ite, mul_zero, tsum_ite_eq]
/-- `extendOverList_cons` uttrykt med tilordningen på `insert`-formen.
Flytter transporten til kallstedet, så høyresiden er fri for `cast`. -/
lemma extendOverList_cons' (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hv : v ∉ B ∪ vs.toFinset)
    (htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
      = Assignment (α := α) (B ∪ (v :: vs).toFinset))
    (b : Assignment (α := α) (insert v (B ∪ vs.toFinset))) :
    (extendOverList M B base (v :: vs) hpar) (cast htype b) =
      (extendOverList M B base vs (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        (b.restrict (Finset.subset_insert v (B ∪ vs.toFinset))) *
      (M.kernel v ((b.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        (b ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  have h := extendOverList_cons M B base v vs hpar hv htype (cast htype b)
  simpa using h


/-- Likhet mellom tilordninger splitter i `L`- og `R`-delene når `L ∪ R`
dekker mengden. Grunnlaget for `nil`-tilfellet i faktoriseringen. -/
lemma assignment_eq_iff_inter (L R B : Finset V) (hLR : B ⊆ L ∪ R)
    (base b : Assignment (α := α) B) :
    (b = base) ↔
      (b.restrict (Finset.inter_subset_right (s₁ := L)) =
         base.restrict (Finset.inter_subset_right (s₁ := L)) ∧
       b.restrict (Finset.inter_subset_right (s₁ := R)) =
         base.restrict (Finset.inter_subset_right (s₁ := R))) := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext u
    rcases Finset.mem_union.mp (hLR u.2) with hu | hu
    · exact congrFun h1 ⟨u.1, Finset.mem_inter.mpr ⟨hu, u.2⟩⟩
    · exact congrFun h2 ⟨u.1, Finset.mem_inter.mpr ⟨hu, u.2⟩⟩
/-- Kjernen av `nil`-tilfellet for den styrkede faktoriseringen: indikatoren
på likhet splitter i et produkt av `L`- og `R`-indikatorer, med `base` som
eksplisitt argument.

Formulert helt over `B`, uten `B ∪ [].toFinset`, så ingen transport oppstår.
Koblingen til `extendOverList_nil` gjøres separat. -/
lemma indicator_splits (L R B : Finset V) (hLR : B ⊆ L ∪ R) :
    ∃ (F : Assignment (α := α) (L ∩ B) → Assignment (α := α) (L ∩ B) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) → Assignment (α := α) (R ∩ B) → ENNReal),
      ∀ (base a : Assignment (α := α) B),
        (if a = base then (1 : ENNReal) else 0) =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  refine ⟨fun bp p => if p = bp then 1 else 0,
          fun bq q => if q = bq then 1 else 0, ?_⟩
  intro base a
  rw [assignment_eq_iff_inter L R B hLR base a]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← ite_and]
  congr 1
  exact propext and_comm


/-- Foreldrene til `v` ligger i `L`-snittet når familieklikken gjør det. -/
lemma parents_subset_inter (L B : Finset V) (v : V) (vs : List V)
    (hparv : G.parents v ⊆ B) (hcl : insert v (G.parents v) ⊆ L) :
    G.parents v ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact hcl (Finset.mem_insert_of_mem hx)
  · exact Finset.mem_union_left _ (hparv hx)

/-- `v` selv ligger i `L`-snittet når familieklikken gjør det. -/
lemma self_mem_inter (L B : Finset V) (v : V) (vs : List V)
    (hcl : insert v (G.parents v) ⊆ L) :
    v ∈ L ∩ (B ∪ (v :: vs).toFinset) := by
  refine Finset.mem_inter.mpr ⟨hcl (Finset.mem_insert_self _ _), ?_⟩
  simp

/-- Snittet vokser når listen vokser. -/
lemma inter_mono_cons (L B : Finset V) (v : V) (vs : List V) :
    L ∩ (B ∪ vs.toFinset) ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hL, hBvs⟩
  refine Finset.mem_inter.mpr ⟨hL, ?_⟩
  rcases Finset.mem_union.mp hBvs with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simp at h ⊢; tauto)
/-- Verteksmengden vokser med rangnivået. -/
lemma verticesUpTo_mono_succ (n : ℕ) :
    G.verticesUpTo n ⊆ G.verticesUpTo (n + 1) := by
  intro x hx
  simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

/-- Snittet med en fast mengde vokser tilsvarende. -/
lemma inter_verticesUpTo_mono_succ (S : Finset V) (n : ℕ) :
    S ∩ G.verticesUpTo n ⊆ S ∩ G.verticesUpTo (n + 1) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨h1, h2⟩
  exact Finset.mem_inter.mpr ⟨h1, verticesUpTo_mono_succ n h2⟩

/-- Snitt distribuerer over union. -/
lemma union_inter_distrib (L Z S : Finset V) :
    (L ∪ Z) ∩ S = (L ∩ S) ∪ (Z ∩ S) := by
  ext x
  simp [Finset.mem_inter, Finset.mem_union]
  tauto

/-- Disjunkthet bevares under snitt. -/
lemma disjoint_inter_of_disjoint (L Z S : Finset V) (hLZ : Disjoint L Z) :
    Disjoint (L ∩ S) (Z ∩ S) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left hLZ)
/-- Tilordninger over en disjunkt union splitter i et produkt. -/
def assignmentSplit (s t : Finset V) (h : Disjoint s t) :
    Assignment (α := α) (s ∪ t) ≃ Assignment (α := α) s × Assignment (α := α) t := by
  unfold Assignment
  exact (Equiv.piCongrLeft _ (Equiv.Finset.union s t h)).symm.trans
    (Equiv.sumPiEquivProdPi _)

/-- Sett sammen en `L`-del og en `Z`-del til en tilordning på `(L ∪ Z) ∩ S`. -/
noncomputable def joinInter (L Z S : Finset V)
    (p : Assignment (α := α) (L ∩ S)) (q : Assignment (α := α) (Z ∩ S)) :
    Assignment (α := α) ((L ∪ Z) ∩ S) :=
  fun u =>
    if h : u.1 ∈ L then
      p ⟨u.1, Finset.mem_inter.mpr ⟨h, (Finset.mem_inter.mp u.2).2⟩⟩
    else
      q ⟨u.1, Finset.mem_inter.mpr ⟨by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp u.2).1 with hL | hZ
        · exact absurd hL h
        · exact hZ, (Finset.mem_inter.mp u.2).2⟩⟩
/-- `joinInter` av de to restriksjonene er restriksjonen til `(L ∪ Z) ∩ S`.
Dette er koblingen `jointUpTo_factorizes` trenger. -/
lemma joinInter_restrict (L Z S : Finset V) (a : Assignment (α := α) S) :
    joinInter L Z S (a.restrict Finset.inter_subset_right)
      (a.restrict Finset.inter_subset_right)
      = a.restrict (Finset.inter_subset_right (s₁ := L ∪ Z)) := by
  funext u
  unfold joinInter Assignment.restrict
  by_cases h : u.1 ∈ L <;> simp [h]
/-- Å anvende en transportert `PMF` er å anvende originalen på det
tilbaketransporterte argumentet. -/
lemma cast_pmf_apply (S T : Finset V) (hset : S = T)
    (htype : PMF (Assignment (α := α) S) = PMF (Assignment (α := α) T))
    (htype2 : Assignment (α := α) T = Assignment (α := α) S)
    (p : PMF (Assignment (α := α) S)) (a : Assignment (α := α) T) :
    (cast htype p) a = p (cast htype2 a) := by
  subst hset
  simp
/-- En produktfaktorisering overlever transport langs en mengdelikhet.
Samler transporten på ett sted framfor å spre den utover beviset. -/
lemma transport_factorization (S T A B : Finset V) (hS : S = T)
    (F0 : Assignment (α := α) A → ENNReal)
    (Gf0 : Assignment (α := α) B → ENNReal)
    (rA : Assignment (α := α) S → Assignment (α := α) A)
    (rB : Assignment (α := α) S → Assignment (α := α) B)
    (p : PMF (Assignment (α := α) S))
    (h : ∀ x : Assignment (α := α) S, p x = F0 (rA x) * Gf0 (rB x)) :
    ∀ y : Assignment (α := α) T,
      (hS ▸ p) y = F0 ((hS ▸ rA) y) * Gf0 ((hS ▸ rB) y) := by
  subst hS
  simpa using h
/-- `cast` på en funksjon flyttes til argumentet. -/
lemma cast_fun_apply (S T A : Finset V) (hS : S = T)
    (htype : (Assignment (α := α) S → Assignment (α := α) A)
      = (Assignment (α := α) T → Assignment (α := α) A))
    (h2 : Assignment (α := α) T = Assignment (α := α) S)
    (f : Assignment (α := α) S → Assignment (α := α) A)
    (y : Assignment (α := α) T) :
    (cast htype f) y = f (cast h2 y) := by
  subst hS
  simp
/-- `jointUpTo` på nivå 0, med transporten skjult.

Eksponerer `extendOverList` direkte, slik at klientbevis slipper å håndtere
`cast`. Dette er mønsteret Mathlib bruker: `cast` i implementasjonen, rent
API utenpå. Å kjede sammen transportlemmaer i hvert klientbevis kostet flere
økter uten å lykkes; å samle transporten her gikk på første forsøk. -/
lemma jointUpTo_zero_apply (M : CausalModel G α)
    (a : Assignment (α := α) (G.verticesUpTo 0)) :
    (jointUpTo M 0) a =
      (M.extendOverList ∅ (fun v => absurd (jointUpTo._proof_2 v) (jointUpTo._proof_3 v))
        (G.verticesUpTo 0).toList jointUpTo._proof_4)
        (cast (by simp) a) := by
  unfold jointUpTo
  rw [cast_pmf_apply _ _ (by simp)]
/-- `jointUpTo` på nivå `n+1`, med transporten skjult.

Merk `conv_lhs`: et vanlig `unfold jointUpTo` ruller også ut `jointUpTo M n`
på høyresiden, og da matcher sidene aldri. Ni forsøk gikk med til å lete
etter feil i transporten før det viste seg å være dette. -/
lemma jointUpTo_succ_apply (M : CausalModel G α) (n : ℕ)
    (hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset = G.verticesUpTo (n + 1))
    (htype2 : Assignment (α := α) (G.verticesUpTo (n + 1))
      = Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset))
    (a : Assignment (α := α) (G.verticesUpTo (n + 1))) :
    (jointUpTo M (n + 1)) a =
      ((M.jointUpTo n).bind fun asg =>
        M.extendOverList (G.verticesUpTo n) asg (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n))
        (cast htype2 a) := by
  conv_lhs => unfold jointUpTo
  rw [cast_pmf_apply _ _ hset _ htype2]
/-- `fullJoint` med transporten skjult. Samme mønster som
`jointUpTo_zero_apply` og `jointUpTo_succ_apply`. -/
lemma fullJoint_apply (M : CausalModel G α)
    (htype2 : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank))
    (a : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) a = (jointUpTo M G.maxRank) (cast htype2 a) := by
  unfold fullJoint
  rw [cast_pmf_apply _ _ G.verticesUpTo_maxRank _ htype2]




/-- Restriksjon av en transportert tilordning er restriksjon av originalen,
når transporten kommer fra en mengdelikhet. -/
lemma restrict_cast_eq (S T U : Finset V) (hset : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (h1 : U ⊆ S) (h2 : U ⊆ T) :
    (cast htype a).restrict h1 = a.restrict h2 := by
  subst hset
  simp
/-- Oppslag i en transportert tilordning er oppslag i originalen.
Motstykket til `restrict_cast_eq` for direkte oppslag framfor restriksjon. -/
lemma cast_apply_eq (S T : Finset V) (hST : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) (h1 : v ∈ S) (h2 : v ∈ T) :
    (cast htype a) ⟨v, h1⟩ = a ⟨v, h2⟩ := by
  subst hST
  simp

/-- `cast` på en restriksjon flyttes ut når mengdene er like.
Motstykket til `restrict_cast_eq` — sammen dekker de begge retninger. -/
lemma cast_restrict_eq (S A B : Finset V) (hAB : A = B)
    (htype : Assignment (α := α) A = Assignment (α := α) B)
    (h1 : A ⊆ S) (h2 : B ⊆ S)
    (a : Assignment (α := α) S) :
    cast htype (a.restrict h1) = a.restrict h2 := by
  subst hAB
  simp
/-- Restriksjon og transport kommuterer når mengdene er like.
Formulert med `S` og `T` som separate variabler så `subst` er mulig —
`B ∪ [] = B` har `B` på begge sider og lar seg ikke substituere direkte. -/
lemma restrict_cast_comm (L S T : Finset V) (hST : S = T)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) (L ∩ S) = Assignment (α := α) (L ∩ T))
    (base : Assignment (α := α) S) :
    (cast h1 base).restrict (Finset.inter_subset_right (s₁ := L))
      = cast h2 (base.restrict (Finset.inter_subset_right (s₁ := L))) := by
  subst hST
  simp
/-- Når mengden er hele `univ`, er restriksjon og transport inverse.
Lar indikatoren snus så `tsum_ite_eq` kan kollapse summen i `joint_splits`. -/
lemma eq_restrict_iff_eq_cast (S : Finset V) (hS : S = Finset.univ)
    (htypeA : Assignment (α := α) S = Assignment (α := α) (Finset.univ : Finset V))
    (a : Assignment (α := α) S) (a1 : Assignment (α := α) (Finset.univ : Finset V)) :
    (a = a1.restrict (by rw [hS])) ↔ (a1 = cast htypeA a) := by
  subst hS
  constructor
  · intro h
    subst h
    rfl
  · intro h
    subst h
    rfl
/-- Restriksjon og transport kommuterer, generelt: fire mengder, to
mengdelikheter. Generaliseringen av `restrict_cast_comm` som `joint_splits`
trenger, der `U` og `W` ikke er avledet fra `S` og `T`. -/
lemma restrict_cast_gen (S T U W : Finset V) (hST : S = T) (hUW : U = W)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) U = Assignment (α := α) W)
    (a : Assignment (α := α) S) (hu : U ⊆ S) (hw : W ⊆ T) :
    (cast h1 a).restrict hw = cast h2 (a.restrict hu) := by
  subst hST
  subst hUW
  simp

end PearlDoCalculus
