/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DoCalc.Derives
import PearlDoCalculus.Completeness.SetRules

/-!
# Rule 3 for non-ancestors, and small derived steps

The completeness proof (`docs/design-docalc-completeness.md`, phase 3) uses rule 3 of the
do-calculus in one special form, over and over: an intervention on variables that are not
ancestors of the query can be dropped. This file derives that form from the `rule3`
constructor of `Derives`, together with a few small steps composed from the other
constructors. `Derives` itself is not changed.

**Derived steps.** `Derives.of_eq` turns an equality of expressions into a derivation; it
is how the sets of a `prob` term are rewritten (for example `Y ∪ (D ∖ Y)` into `D`).
`Derives.mul_one` is the right unit law of `mul`, from `mul_comm` and `one_mul`.
`Derives.marg_superset` is marginalization onto a given superset `D ⊇ Y`:
`P(Y | Z, do X) = Σ_{D ∖ Y} P(D | Z, do X)`.

**Rule 3 for non-ancestors.** Let `Z` contain no ancestor of `Y ∪ W` in `G_{X̄}`. Then
`P(Y | W, do(X ∪ Z)) = P(Y | W, do(X))` (`Derives.rule3_nonanc`); without `W` this is
`P(Y | do(X ∪ Z)) = P(Y | do(X))` (`Derives.query_rule3_nonanc`). The side condition of
`rule3` is d-separation of `Y` and `Z` by `X ∪ W` in `G_{X̄, Z(W)̄}`. Here no vertex of `Z`
is an ancestor of `W`, so `Z(W) = Z` (`Completeness.Z2_all`), and the d-separation is a
graph lemma (`dsepSet_rule3_nonanc`). No hypothesis on the latent vertices is needed.

**How the graph lemma goes.** Let `H` be a graph without edges into `X` and into `Z`
(here `G_{X̄Z̄}`), and take a walk from `y ∈ Y` to `z ∈ Z` that is open given `X ∪ W`.
Read it backwards from `z` (`open_walk_to_root`). Since `z` has no parents, the walk
leaves `z` along an out-edge. As long as it keeps following edges forwards, every vertex
is a descendant of `z`. If it ever turns, the turning vertex is a collider, and an open
collider has a descendant in `X ∪ W`. It cannot be a descendant in `X`: a vertex of `X`
has no parents in `H`, so it is its own only ancestor, and the collider has a parent on
the walk. So the collider, and with it `z`, is an ancestor of `W`. Otherwise the walk is
directed from `z` to `y`, and `z` is an ancestor of `y`. Either way `z` is an ancestor of
`Y ∪ W` in `H`, hence in `G_{X̄}`.

**Main results.** `Derives.of_eq`, `Derives.mul_one`, `Derives.marg_superset`,
`open_walk_to_root`, `dsepSet_of_noParents`, `dsepSet_rule3_nonanc`,
`Derives.rule3_nonanc`, `Derives.query_rule3_nonanc`.
-/

open PearlDoCalculus DAG DoCalculus

namespace DoCalc

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Derived steps -/

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- Equal expressions derive each other. This is how the sets of a `prob` term are
rewritten. -/
lemma of_eq {e₁ e₂ : Expr V} (h : e₁ = e₂) : Derives G U e₁ e₂ :=
  h ▸ refl e₁

/-- `one` is a right unit for `mul`. -/
lemma mul_one (a : Expr V) : Derives G U (.mul a .one) a :=
  trans (mul_comm a .one) (one_mul a)

/-- **Marginalization onto a superset.** `P(Y | Z, do X) = Σ_{D ∖ Y} P(D | Z, do X)` for
`Y ⊆ D` and `D` disjoint from `Z ∪ X`. -/
lemma marg_superset (Y D Z X : Finset V) (hYD : Y ⊆ D) (hD : Disjoint D (Z ∪ X)) :
    Derives G U (.prob Y Z X) (.sum (D \ Y) (.prob D Z X)) := by
  have h : Disjoint (D \ Y) (Y ∪ Z ∪ X) := by
    rw [Finset.union_assoc]
    exact Finset.disjoint_union_right.mpr ⟨Finset.sdiff_disjoint,
      Finset.disjoint_of_subset_left Finset.sdiff_subset hD⟩
  have hm := marg (G := G) (U := U) Y Z X (D \ Y) h
  rwa [Finset.union_sdiff_of_subset hYD] at hm

end Derives

/-! ## d-separation from non-ancestors -/

section Graph

variable {H : DAG V} {X W Z : Finset V}

/-- **An open walk into a vertex without parents.** Let `H` have no edges into `X` and
into `Z`, and let `q` be a walk from `a` to `b ∈ Z` that is open given `X ∪ W`, entered with
direction `inc`. Then `b` is an ancestor of a vertex of `W`, or `b` is an ancestor of `a`;
in the second case, if `q` is entered along an arrow into `a`, then `q` is empty. -/
lemma open_walk_to_root (hX : ∀ u v, H.edge u v → v ∉ X) (hZ : ∀ u v, H.edge u v → v ∉ Z) :
    ∀ {a b : V} (q : Walk H a b) (inc : Incoming), b ∈ Z →
      ¬ Walk.blockedAux (X ∪ W) inc q →
      (∃ w ∈ W, H.Reaches b w) ∨ (H.Reaches b a ∧ (inc = .fwd → a = b)) := by
  intro a b q
  induction q with
  | nil v => exact fun _ _ _ => Or.inr ⟨Reaches.refl H v, fun _ => rfl⟩
  | @fwd a a' b e rest ih =>
    -- the walk follows the edge `a → a'`; the rest is entered along an arrow
    intro inc hb hq
    have hq' : ¬ Walk.blockedAux (X ∪ W) .fwd rest := by
      cases inc <;> simp only [Walk.blockedAux, not_or] at hq <;> tauto
    rcases ih .fwd hb hq' with hW | ⟨-, h⟩
    · exact Or.inl hW
    · -- the rest is empty, so `a → b` would be an edge into `Z`
      obtain rfl := h rfl
      exact absurd hb (hZ _ _ e)
  | @bwd a a' b e rest ih =>
    -- the walk goes against the edge `a' → a`
    intro inc hb hq
    have hq' : ¬ Walk.blockedAux (X ∪ W) .bwd rest := by
      cases inc <;> simp only [Walk.blockedAux, not_or] at hq <;> tauto
    rcases ih .bwd hb hq' with hW | ⟨hr, -⟩
    · exact Or.inl hW
    have hr' : H.Reaches b a := Relation.ReflTransGen.tail hr e
    cases inc with
    | start => exact Or.inr ⟨hr', fun h => nomatch h⟩
    | bwd => exact Or.inr ⟨hr', fun h => nomatch h⟩
    | fwd =>
      -- `a` is a collider, open, so it has a descendant `x ∈ X ∪ W`
      simp only [Walk.blockedAux, not_or, not_forall, not_not] at hq
      obtain ⟨⟨x, hx, hax⟩, -⟩ := hq
      rcases Finset.mem_union.mp hx with hxX | hxW
      · -- `x ∈ X` has no parents, so `x = a`; but `a` has the parent `a'`
        rcases Relation.ReflTransGen.cases_tail hax with rfl | ⟨c, -, hc⟩
        · exact absurd hxX (hX _ _ e)
        · exact absurd hxX (hX _ _ hc)
      · exact Or.inl ⟨x, hxW, Relation.ReflTransGen.trans hr' hax⟩

/-- **d-separation from non-ancestors.** In a graph without edges into `X` and into `Z`,
`Y` and `Z` are d-separated by `X ∪ W` when no vertex of `Z` is an ancestor of `Y ∪ W`. -/
lemma dsepSet_of_noParents {Y : Finset V} (hX : ∀ u v, H.edge u v → v ∉ X)
    (hZ : ∀ u v, H.edge u v → v ∉ Z) (h : ∀ z ∈ Z, z ∉ ancestors H (Y ∪ W)) :
    SetSound.DSeparatedSet H (X ∪ W) Y Z := by
  intro y hy z hz p _
  by_contra hp
  apply h z hz
  rw [mem_ancestors_iff]
  rcases open_walk_to_root hX hZ p .start hz hp with ⟨w, hw, hr⟩ | ⟨hr, -⟩
  · exact ⟨w, Finset.mem_union_right _ hw, hr⟩
  · exact ⟨y, Finset.mem_union_left _ hy, hr⟩

/-- **The side condition of rule 3 for non-ancestors.** If no vertex of `Z` is an
ancestor of `Y ∪ W` in `G_{X̄}`, then `Z(W) = Z`, and `Y` and `Z` are d-separated by
`X ∪ W` in `G_{X̄, Z(W)̄}`. -/
theorem dsepSet_rule3_nonanc (G : DAG V) {X Y Z W : Finset V}
    (hZ : Disjoint Z (ancestors (cutIn G X) (Y ∪ W))) :
    SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z := by
  have hZW : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W := by
    intro z hz hzW
    obtain ⟨w, hw, hr⟩ := mem_ancestors_iff.mp hzW
    exact Finset.disjoint_left.mp hZ hz
      (mem_ancestors_iff.mpr ⟨w, Finset.mem_union_right _ hw, hr⟩)
  rw [Completeness.Z2_all hZW]
  refine dsepSet_of_noParents (fun u v e => e.1.2) (fun u v e => e.2) (fun z hz hzA => ?_)
  obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hzA
  exact Finset.disjoint_left.mp hZ hz
    (mem_ancestors_iff.mpr ⟨s, hs, Rule3.reaches_mono (H := cutIn G X)
      (H' := cutIn (cutIn G X) Z) (fun u v e => e.1) hr⟩)

end Graph

/-! ## Rule 3 for non-ancestors -/

namespace Derives

variable {G : DAG V} {U : Finset V}

/-- **Rule 3 for non-ancestors.** `P(Y | W, do(X ∪ Z)) = P(Y | W, do(X))` when no vertex
of `Z` is an ancestor of `Y ∪ W` in `G_{X̄}`, for observed `X`, `Z`, `W`, with `Z` disjoint
from `X` and `Y` disjoint from `X ∪ W`. -/
theorem rule3_nonanc (X Y Z W : Finset V) (hXZ : Disjoint X Z) (hYXW : Disjoint Y (X ∪ W))
    (hO : Z ∪ W ∪ X ⊆ Uᶜ) (hZ : Disjoint Z (ancestors (cutIn G X) (Y ∪ W))) :
    Derives G U (.prob Y W (X ∪ Z)) (.prob Y W X) := by
  have hYWZ : Disjoint (Y ∪ W) Z :=
    Finset.disjoint_of_subset_left (subset_ancestors (G := cutIn G X) _) hZ.symm
  have hYZ : Disjoint Y Z := Finset.disjoint_of_subset_left Finset.subset_union_left hYWZ
  have hWZ : Disjoint W Z := Finset.disjoint_of_subset_left Finset.subset_union_right hYWZ
  exact rule3 X Y Z W hYZ (Finset.disjoint_union_left.mpr ⟨hXZ, hWZ⟩) hYXW hO
    (dsepSet_rule3_nonanc G hZ)

/-- **Rule 3 for non-ancestors, without conditioning.** `P(Y | do(X ∪ Z)) = P(Y | do(X))`
when no vertex of `Z` is an ancestor of `Y` in `G_{X̄}`, for observed `X` and `Z`, with
`Z` disjoint from `X` and `Y` disjoint from `X`. -/
theorem query_rule3_nonanc (X Y Z : Finset V) (hXZ : Disjoint X Z) (hYX : Disjoint Y X)
    (hO : Z ∪ X ⊆ Uᶜ) (hZ : Disjoint Z (ancestors (cutIn G X) Y)) :
    Derives G U (Expr.query Y (X ∪ Z)) (Expr.query Y X) :=
  rule3_nonanc X Y Z ∅ hXZ (by rwa [Finset.union_empty]) (by rwa [Finset.union_empty])
    (by rwa [Finset.union_empty])

end Derives

end DoCalc
