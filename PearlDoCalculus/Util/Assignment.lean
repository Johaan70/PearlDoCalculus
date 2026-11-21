/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.CausalModel

/-!
# Joining, extending and restricting assignments

An `Assignment S` gives a value to every vertex of a finite set `S`, and
`Assignment.restrict` forgets the values outside a subset (`CausalModel`). Several
unrelated files need the same three facts about these maps: the soundness of
d-separation (`DSepSound`), the completeness of the do-rules (`Completeness/SetRules`),
the identification layer (`Identification/Basic`) and IDC (`Idc`), and through
`Util/Marginal` many more. They are stated here once. Each proof unfolds the
definitions of `join` and `restrict` and compares the two sides pointwise.

**Contents.**

1. *Joining two assignments.* `Assignment.join a b` puts an assignment `a` on `A` and
   an assignment `b` on `B` together into one assignment on `A ∪ B`. Where `A` and `B`
   overlap it takes the value of `a`. Restricting the join to `A` gives back `a`
   (`restrict_join_left`). Restricting it to `B` gives back `b` provided `a` and `b`
   agree on the overlap (`restrict_join_right`); this holds in particular when `A` and
   `B` are disjoint.
2. *Every assignment on a subset extends.* If `S ⊆ T` and every value type is
   nonempty, every assignment on `S` is the restriction of one on `T`
   (`restrict_surjective`): fill the values outside `S` with arbitrary elements.
3. *Restriction between equal sets.* If `T ⊆ S` and `S ⊆ T`, the restriction from `S`
   to `T` loses nothing (`restrict_injective_of_subset`). This is used when the same
   set is written in two ways, such as `X ∪ Y ∪ Z` and `Y ∪ X ∪ Z`.

**Main results.** `Assignment.join`, `Assignment.restrict_join_left`,
`Assignment.restrict_join_right`, `Assignment.restrict_surjective`,
`Assignment.restrict_injective_of_subset`.
-/

namespace PearlDoCalculus.DAG.CausalModel

variable {V : Type*} [DecidableEq V] {α : V → Type*}

/-! ## Joining two assignments -/

/-- `a` on `A` and `b` on `B`, joined into one assignment on `A ∪ B`. On the overlap the
value of `a` wins. -/
def Assignment.join {A B : Finset V} (a : Assignment (α := α) A)
    (b : Assignment (α := α) B) : Assignment (α := α) (A ∪ B) :=
  fun v => if h : v.1 ∈ A then a ⟨v.1, h⟩
    else b ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩

/-- Restricting a join to the left set gives back the left assignment. -/
lemma Assignment.restrict_join_left {A B : Finset V} (a : Assignment (α := α) A)
    (b : Assignment (α := α) B) :
    (a.join b).restrict Finset.subset_union_left = a := by
  funext w
  obtain ⟨v, hv⟩ := w
  simp only [Assignment.restrict, Assignment.join, dif_pos hv]

/-- Restricting a join to the right set gives back the right assignment, if the two
assignments agree where their sets overlap. -/
lemma Assignment.restrict_join_right {A B : Finset V} (a : Assignment (α := α) A)
    (b : Assignment (α := α) B) (hab : ∀ v (ha : v ∈ A) (hb : v ∈ B), a ⟨v, ha⟩ = b ⟨v, hb⟩) :
    (a.join b).restrict Finset.subset_union_right = b := by
  funext w
  obtain ⟨v, hv⟩ := w
  by_cases ha : v ∈ A
  · simp only [Assignment.restrict, Assignment.join, dif_pos ha]
    exact hab v ha hv
  · simp only [Assignment.restrict, Assignment.join, dif_neg ha]

/-! ## Every assignment on a subset extends -/

/-- Every assignment on `S ⊆ T` is the restriction of an assignment on `T`. -/
lemma Assignment.restrict_surjective [∀ w, Nonempty (α w)] {S T : Finset V} (h : S ⊆ T) :
    Function.Surjective (Assignment.restrict (α := α) h) := fun b =>
  ⟨fun v => if hv : v.1 ∈ S then b ⟨v.1, hv⟩ else Classical.arbitrary _, by
    funext ⟨v, hv⟩
    simp [Assignment.restrict, hv]⟩

/-! ## Restriction between equal sets -/

omit [DecidableEq V] in
/-- If `T ⊆ S ⊆ T`, restriction from `S` to `T` loses nothing. -/
lemma Assignment.restrict_injective_of_subset {S T : Finset V} (h : T ⊆ S) (h' : S ⊆ T) :
    Function.Injective (Assignment.restrict (α := α) h) := by
  intro a b e
  funext v
  exact congrFun e ⟨v.1, h' v.2⟩

end PearlDoCalculus.DAG.CausalModel
