import PearlDoCalculus.Soundness.Basic
/-!
# Casts and splits of assignments

**What it proves.** Bookkeeping lemmas about assignments and about the way a causal
model builds its joint distribution. The joint is built rank level by rank level
(`CausalModel.jointUpTo`): each level extends the assignment on the lower levels by
the new vertices one at a time (`CausalModel.extendOverList`), and `fullJoint` is the
last level. Each step changes the index set of the assignments, so the definitions are
full of `cast`s along equalities of finsets. This file proves:
- in an induced subgraph on a set closed under parents, a vertex has the same parents as
  in `G` (`DAG.induce_parents_eq`);
- `extendOverList` on the empty list is the point mass on the base
  (`extendOverList_nil`), and on `v :: vs` it is the value on `vs` times the kernel of `v`
  (`extendOverList_cons`, `extendOverList_cons_insert`);
- an indicator `[a = base]` splits into a product of an indicator on `L ∩ B` and one on
  `R ∩ B` (`indicator_splits`);
- small set facts that the factorisation needs (`parents_subset_inter`, `self_mem_inter`,
  `inter_mono_cons`, `inter_verticesUpTo_mono_succ`), the split of assignments on a
  disjoint union (`assignmentSplit`) and the join of an `L`-part and a `Z`-part
  (`joinInter`);
- the evaluation of `jointUpTo` and `fullJoint` at a point, with the casts moved into the
  lemma (`jointUpTo_zero_apply`, `jointUpTo_succ_apply`, `fullJoint_apply`);
- restriction and evaluation commute with transport along an equality of finsets
  (`restrict_cast_eq`, `cast_apply_eq`, `cast_restrict_eq`, `restrict_cast_comm`,
  `restrict_cast_gen`, `eq_restrict_iff_eq_cast`).

**Why it is needed.** This is layer 1a of the Lauritzen route to the soundness of
d-separation (see `Soundness.lean`). The factorisation along a separator
(`Soundness/Factorizes`), the product form of the joint
(`Soundness/AncestralReduction`) and the split of the joint
(`Soundness/Separator`) all compute with `jointUpTo` and `extendOverList` at a
point, and they use these lemmas to do so without handling the casts themselves.
`DAG.induce_parents_eq` is also used by `CausalModel.restrictTo` and by
`Soundness/DSepSound`.

**How the proofs go.** Almost every cast lemma is proved by `subst` on the equality of
finsets, after which both sides agree and `simp` closes the goal; the lemmas are stated
with two separate finsets `S` and `T` so that `subst` applies. The unfoldings of
`extendOverList` use `rw! (castMode := .all)` to move the index set, and
`simp [eqRec_eq_cast, cast_cast]` to cancel the transports; in the `cons` case,
`extend_eq_iff` collapses the double sum of the `bind` to a single term.

**Main results.** `extendOverList_nil`, `extendOverList_cons_insert`, `indicator_splits`,
`jointUpTo_zero_apply`, `jointUpTo_succ_apply`, `fullJoint_apply`, `restrict_cast_eq`
and `cast_apply_eq`.
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
/-! ## Parents in an induced subgraph -/

/-- For a vertex of a set closed under parents, `induce` does not change its parents. -/
lemma DAG.induce_parents_eq (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (v : V) (hv : v ∈ A) :
    (DAG.induce G A).parents v = G.parents v := by
  ext u
  simp [DAG.mem_parents, DAG.induce]
  constructor
  · exact fun h => h.2.2
  · exact fun he => ⟨hA v hv u he, hv, he⟩
/-! ## Unfolding `extendOverList` -/

omit [Fintype V] in
/-- The indicator `extend asg x = b` determines both `asg` and `x` uniquely.
This is what collapses the double sum in `extendOverList`. -/
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
      simp [Assignment.extend, Assignment.restrict, hv]

/-- `extendOverList` on the empty list is the point mass on `base`.

Note the technique for `cast`: `rw! (castMode := .all)` moves the index set, and
`simp [eqRec_eq_cast, cast_cast]` cancels the transports. This combination is the key
to all work with `extendOverList` and `jointUpTo`. -/
lemma extendOverList_nil (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B)
    (hpar : ∀ v ∈ ([] : List V), G.parents v ⊆ B)
    (a : Assignment (α := α) (B ∪ ([] : List V).toFinset)) :
    (extendOverList M B base [] hpar) a = if a = cast (by simp) base then 1 else 0 := by
  have hB : B ∪ ([] : List V).toFinset = B := by simp
  rw! (castMode := .all) [hB]
  simp [extendOverList, eqRec_eq_cast, cast_cast, PMF.pure_apply]
/-- Moves a `cast` from one side of an equation to the other. -/
lemma cast_eq_iff_eq_cast_symm {A B : Sort _} (h : A = B) (b : A) (a : B) :
    (cast h b = a) ↔ (b = cast h.symm a) := by
  subst h
  simp

/-- `extendOverList` on a non-empty list factorises: the distribution of the tail times
the kernel of the head. The chain of `cast` rewrites is the same as in
`extendOverList_nil`, with `extend_eq_iff` for the collapse. -/
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
          (fun _ hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        ((cast htype.symm a) ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  simp only [extendOverList, PMF.bind_apply, PMF.map_apply, eq_comm (a := a)]
  simp only [cast_eq_iff_heq]
  simp only [← cast_eq_iff_heq (e := htype)]
  simp only [cast_eq_iff_eq_cast_symm]
  simp only [extend_eq_iff _ v hv]
  simp only [and_comm, ite_and, tsum_ite_eq]
  simp only [mul_ite, mul_zero, tsum_ite_eq]
/-- `extendOverList_cons` stated for an assignment on the `insert` form of the set.
This moves the transport to the call site, so the right-hand side is free of `cast`. -/
lemma extendOverList_cons_insert (M : CausalModel G α) (B : Finset V)
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
          (fun _ hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        (b ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  have h := extendOverList_cons M B base v vs hpar hv htype (cast htype b)
  simpa using h


/-! ## Splitting an indicator along `L` and `R` -/

omit [Fintype V] in
/-- Equality of assignments splits into the `L` part and the `R` part when `L ∪ R`
covers the set. This is the basis of the `nil` case of the factorisation. -/
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

omit [Fintype V] in
/-- The core of the `nil` case of the strengthened factorisation: the indicator of
equality splits into a product of an `L` indicator and an `R` indicator, with `base` as
an explicit argument.

Stated entirely over `B`, without `B ∪ [].toFinset`, so no transport arises. The link
to `extendOverList_nil` is made separately (`extendOverList_factorizes_nil`). -/
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


/-! ## Set facts for the factorisation -/

/-- The parents of `v` lie in the `L` intersection when the family clique does. -/
lemma parents_subset_inter (L B : Finset V) (v : V) (vs : List V)
    (hparv : G.parents v ⊆ B) (hcl : insert v (G.parents v) ⊆ L) :
    G.parents v ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact hcl (Finset.mem_insert_of_mem hx)
  · exact Finset.mem_union_left _ (hparv hx)

/-- `v` itself lies in the `L` intersection when the family clique does. -/
lemma self_mem_inter (L B : Finset V) (v : V) (vs : List V)
    (hcl : insert v (G.parents v) ⊆ L) :
    v ∈ L ∩ (B ∪ (v :: vs).toFinset) := by
  refine Finset.mem_inter.mpr ⟨hcl (Finset.mem_insert_self _ _), ?_⟩
  simp

omit [Fintype V] in
/-- The intersection grows when the list grows. -/
lemma inter_mono_cons (L B : Finset V) (v : V) (vs : List V) :
    L ∩ (B ∪ vs.toFinset) ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hL, hBvs⟩
  refine Finset.mem_inter.mpr ⟨hL, ?_⟩
  rcases Finset.mem_union.mp hBvs with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simp at h ⊢; tauto)
/-- The set of vertices up to a rank grows with the rank. -/
lemma verticesUpTo_mono_succ (n : ℕ) :
    G.verticesUpTo n ⊆ G.verticesUpTo (n + 1) := by
  intro x hx
  simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

/-- So does its intersection with a fixed set. -/
lemma inter_verticesUpTo_mono_succ (S : Finset V) (n : ℕ) :
    S ∩ G.verticesUpTo n ⊆ S ∩ G.verticesUpTo (n + 1) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨h1, h2⟩
  exact Finset.mem_inter.mpr ⟨h1, verticesUpTo_mono_succ n h2⟩

/-! ## Splitting and joining assignments -/

/-- Assignments on a disjoint union split into a pair. -/
def assignmentSplit (s t : Finset V) (h : Disjoint s t) :
    Assignment (α := α) (s ∪ t) ≃ Assignment (α := α) s × Assignment (α := α) t := by
  unfold Assignment
  exact (Equiv.piCongrLeft _ (Equiv.Finset.union s t h)).symm.trans
    (Equiv.sumPiEquivProdPi _)

/-- Joins an `L` part and a `Z` part into an assignment on `(L ∪ Z) ∩ S`. -/
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

omit [Fintype V] in
/-- `joinInter` of the two restrictions is the restriction to `(L ∪ Z) ∩ S`.
This is the link that `jointUpTo_factorizes` needs. -/
lemma joinInter_restrict (L Z S : Finset V) (a : Assignment (α := α) S) :
    joinInter L Z S (a.restrict Finset.inter_subset_right)
      (a.restrict Finset.inter_subset_right)
      = a.restrict (Finset.inter_subset_right (s₁ := L ∪ Z)) := by
  funext u
  unfold joinInter Assignment.restrict
  by_cases h : u.1 ∈ L <;> simp [h]
/-! ## Evaluating the joint without casts -/

omit [DecidableEq V] [Fintype V] in
/-- Applying a transported `PMF` is applying the original to the argument transported
back. -/
lemma cast_pmf_apply (S T : Finset V) (hset : S = T)
    (htype : PMF (Assignment (α := α) S) = PMF (Assignment (α := α) T))
    (htype2 : Assignment (α := α) T = Assignment (α := α) S)
    (p : PMF (Assignment (α := α) S)) (a : Assignment (α := α) T) :
    (cast htype p) a = p (cast htype2 a) := by
  subst hset
  simp
/-- `jointUpTo` at level 0, with the transport hidden.

It exposes `extendOverList` directly, so client proofs need not handle `cast`. This is
the pattern Mathlib uses: `cast` in the implementation, a clean API outside. Chaining
transport lemmas inside every client proof does not work well; collecting the
transport here does. -/
lemma jointUpTo_zero_apply (M : CausalModel G α)
    (a : Assignment (α := α) (G.verticesUpTo 0)) :
    (jointUpTo M 0) a =
      (M.extendOverList ∅ (fun v => absurd (jointUpTo._proof_2 v) (jointUpTo._proof_3 v))
        (G.verticesUpTo 0).toList jointUpTo._proof_4)
        (cast (by simp) a) := by
  unfold jointUpTo
  rw [cast_pmf_apply _ _ (by simp)]
/-- `jointUpTo` at level `n+1`, with the transport hidden.

Note `conv_lhs`: a plain `unfold jointUpTo` also unfolds `jointUpTo M n` on the
right-hand side, and then the two sides never match. The failure looks like a problem
with the transport, but it is this. -/
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
/-- `fullJoint` with the transport hidden. Same pattern as
`jointUpTo_zero_apply` and `jointUpTo_succ_apply`. -/
lemma fullJoint_apply (M : CausalModel G α)
    (htype2 : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank))
    (a : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) a = (jointUpTo M G.maxRank) (cast htype2 a) := by
  unfold fullJoint
  rw [cast_pmf_apply _ _ G.verticesUpTo_maxRank _ htype2]




/-! ## Restriction and evaluation commute with casts -/

omit [DecidableEq V] [Fintype V] in
/-- Restricting a transported assignment is restricting the original, when the
transport comes from an equality of finsets. -/
lemma restrict_cast_eq (S T U : Finset V) (hset : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (h1 : U ⊆ S) (h2 : U ⊆ T) :
    (cast htype a).restrict h1 = a.restrict h2 := by
  subst hset
  simp

omit [DecidableEq V] [Fintype V] in
/-- Evaluating a transported assignment is evaluating the original.
The counterpart of `restrict_cast_eq` for evaluation at a vertex instead of
restriction. -/
lemma cast_apply_eq (S T : Finset V) (hST : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) (h1 : v ∈ S) (h2 : v ∈ T) :
    (cast htype a) ⟨v, h1⟩ = a ⟨v, h2⟩ := by
  subst hST
  simp

omit [DecidableEq V] [Fintype V] in
/-- A `cast` of a restriction is again a restriction when the finsets are equal.
The counterpart of `restrict_cast_eq`; together they cover both directions. -/
lemma cast_restrict_eq (S A B : Finset V) (hAB : A = B)
    (htype : Assignment (α := α) A = Assignment (α := α) B)
    (h1 : A ⊆ S) (h2 : B ⊆ S)
    (a : Assignment (α := α) S) :
    cast htype (a.restrict h1) = a.restrict h2 := by
  subst hAB
  simp

omit [Fintype V] in
/-- Restriction and transport commute when the finsets are equal.
Stated with `S` and `T` as separate variables so that `subst` applies: `B ∪ [] = B`
has `B` on both sides and cannot be substituted directly. -/
lemma restrict_cast_comm (L S T : Finset V) (hST : S = T)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) (L ∩ S) = Assignment (α := α) (L ∩ T))
    (base : Assignment (α := α) S) :
    (cast h1 base).restrict (Finset.inter_subset_right (s₁ := L))
      = cast h2 (base.restrict (Finset.inter_subset_right (s₁ := L))) := by
  subst hST
  simp

omit [DecidableEq V] in
/-- When the set is all of `univ`, restriction and transport are inverse.
This turns the indicator around so that `tsum_ite_eq` can collapse the sum in
`joint_splits`. -/
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

omit [DecidableEq V] [Fintype V] in
/-- Restriction and transport commute, in general: four finsets, two equalities.
The generalisation of `restrict_cast_comm` that `joint_splits` needs, where `U` and `W`
are not derived from `S` and `T`. -/
lemma restrict_cast_gen (S T U W : Finset V) (hST : S = T) (hUW : U = W)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) U = Assignment (α := α) W)
    (a : Assignment (α := α) S) (hu : U ⊆ S) (hw : W ⊆ T) :
    (cast h1 a).restrict hw = cast h2 (a.restrict hu) := by
  subst hST
  subst hUW
  simp

end PearlDoCalculus
