import PearlDoCalculus.Completeness.SingleRules

/-!
# Completeness of d-separation and of the do-rules for sets

**What it proves.** d-separation of sets is exact: `X` and `Y` are d-separated given `Z` if
and only if `CondIndep M X Y Z` holds in every model (`dsepSet_iff`). Rules 1 and 2 for sets
are exact, in exactly the form that `rule1` and `rule2` have (`rule1_iff_set`,
`rule2_iff_set`). Rule 3 for sets is exact when no `z ∈ Z` is an ancestor of `W`
(`rule3_iff_set_nonanc`), and it fails whenever `Y` and `Z` are d-connected in `G_{X̄Z̄}`
(`rule3_complete_set_root`).

**Why it is needed.** `dsepSet_iff`, `rule1_iff_set` and `rule2_iff_set` are public
results. `rule3_complete_set_root` is one of the two cases of the general rule 3 for sets,
`Completeness/Rule3SetIff.lean`, which proves the other case.

**How the proof goes.** d-separation of sets means that every pair `y ∈ Y`, `z ∈ Z` is
d-separated. If one pair is d-connected, the chain model between them
(`Completeness/Chain.lean`) makes `y` and `z` dependent, and then `Y` and `Z` are dependent
too, since conditional independence of sets implies it for their members
(`exists_chain_not_condIndep_set`). This decomposition (`condIndep_symm`,
`condIndep_drop_right`, `condIndep_single`) sums out `Y ∖ Y'` with `Rule3Flag.marginal_sum_Z`.
For rules 2 and 3 the counter-models of `Completeness/SingleRules.lean` are already stated
for sets (`rule2_fails_of_chain`, `rule3_fails_of_chain`): under `do(Z)` the marginals
without `Z` are unchanged in `G_{X̄Z̲}`, and in `G_{X̄Z̄}` the vertices of `Z` are roots, so
setting them is conditioning on them. The proofs here only supply the chain.

**Main results.** `dsepSet_iff`, `rule1_iff_set`, `rule2_iff_set` (all public),
`rule3_iff_set_nonanc`, `rule3_complete_set_root`, the decomposition `condIndep_single` and
`exists_chain_not_condIndep_set`.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace Completeness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Decomposition, d-separation of sets, and rule 1 for sets -/

section SetVersions
open DoCalculus

/-- **Symmetry** of conditional independence. -/
lemma condIndep_symm {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (h : CondIndep M X Y Z) : CondIndep M Y X Z := by
  intro w
  rw [marginal_eq_restrict_of_subset_of_subset M (S := X ∪ Y ∪ Z) (T := Y ∪ X ∪ Z)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)
      (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto),
    mul_comm (M.marginal (Y ∪ Z) _)]
  exact h _

/-- **Decomposition, right-hand side.** If `X ⊥ Y | Z` and `Y' ⊆ Y`, then `X ⊥ Y' | Z`.
Both marginals with `Y'` are sums over `Y ∖ Y'` of the marginals with `Y`. -/
lemma condIndep_drop_right {G : DAG V} {α : V → Type*} (M : G.CausalModel α)
    [∀ w, Nonempty (α w)] {X Y Y' Z : Finset V}
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z) (hY' : Y' ⊆ Y) (h : CondIndep M X Y Z) :
    CondIndep M X Y' Z := by
  have h1 := Finset.disjoint_left.mp hXY
  have h2 := Finset.disjoint_left.mp hYZ
  have hBA : X ∪ Y' ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDA : Y \ Y' ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hBD : Disjoint (X ∪ Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with (hv | hv) | hv
    · exact h1 hv hv'.1
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB : X ∪ Y ∪ Z ⊆ X ∪ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hYZA : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hDYZ : Y \ Y' ⊆ Y ∪ Z := by
    intro v hv; simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢; tauto
  have hB2 : Y' ∪ Z ⊆ Y ∪ Z := by
    intro v hv; have := @hY' v; simp only [Finset.mem_union] at hv ⊢; tauto
  have hBD2 : Disjoint (Y' ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv hv'
    rcases hv with hv | hv
    · exact hv'.2 hv
    · exact h2 hv'.1 hv
  have hAB2 : Y ∪ Z ⊆ Y' ∪ Z ∪ (Y \ Y') := by
    intro v hv
    by_cases hv' : v ∈ Y' <;> simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢ <;> tauto
  have hZD : Disjoint Z (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact h2 (Finset.mem_sdiff.mp hv').1 hv
  have hXZD : Disjoint (X ∪ Z) (Y \ Y') := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h1 hv (Finset.mem_sdiff.mp hv').1
    · exact h2 (Finset.mem_sdiff.mp hv').1 hv
  intro b
  obtain ⟨a, rfl⟩ := Assignment.restrict_surjective hBA b
  have e1 : M.marginal (X ∪ Y' ∪ Z) (a.restrict hBA) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (X ∪ Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d) :=
    (Rule3Flag.marginal_sum_Z M hDA hBA hBD hAB a).symm
  have e2 : M.marginal (Y' ∪ Z) ((a.restrict hBA).restrict
        (show Y' ∪ Z ⊆ X ∪ Y' ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
      ∑' d : Assignment (α := α) (Y \ Y'),
        M.marginal (Y ∪ Z) (Rule3Flag.setZ (Y \ Y') (Y ∪ Z) (a.restrict hYZA) d) :=
    (Rule3Flag.marginal_sum_Z M hDYZ hB2 hBD2 hAB2 (a.restrict hYZA)).symm
  rw [e1, e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun d => ?_)
  have hci := h (Rule3Flag.setZ (Y \ Y') (X ∪ Y ∪ Z) a d)
  rw [Rule3Flag.setZ_restrict_disj _ hZD a d, Rule3Flag.setZ_restrict_disj _ hXZD a d] at hci
  exact hci

/-- **Decomposition to single vertices.** If `X ⊥ Y | Z`, then `x ⊥ y | Z` for all
`x ∈ X` and `y ∈ Y`. -/
lemma condIndep_single {G : DAG V} {α : V → Type*} (M : G.CausalModel α) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : CondIndep M X Y Z) {x y : V} (hx : x ∈ X) (hy : y ∈ Y) :
    CondIndep M {x} {y} Z := by
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have h1 := condIndep_drop_right M hXY hYZ (Finset.singleton_subset_iff.mpr hy) h
  have hyX : Disjoint ({y} : Finset V) X :=
    Finset.disjoint_singleton_left.mpr (fun hyX => Finset.disjoint_left.mp hXY hyX hy)
  exact condIndep_symm M (condIndep_drop_right M hyX hXZ
    (Finset.singleton_subset_iff.mpr hx) (condIndep_symm M h1))

/-- **A chain that makes two sets dependent.** If `Y` and `Z` are not d-separated given
`S`, some `y ∈ Y` and `z ∈ Z` are d-connected; the chain model between them
(`exists_chain_not_condIndep`) makes `y` and `z` dependent, and hence also `Y` and `Z`
(`condIndep_single`). -/
lemma exists_chain_not_condIndep_set {H : DAG V} {S Y Z : Finset V}
    (hY : Disjoint Y S) (hZ : Disjoint Z S) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet H S Y Z) :
    ∃ y z, ∃ C : Chain H S y z, ¬ CondIndep (chainModel C) Y Z S := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨C, hC⟩ := exists_chain_not_condIndep (Finset.disjoint_left.mp hY hy)
    (Finset.disjoint_left.mp hZ hz) (fun e => Finset.disjoint_left.mp hYZ hy (e ▸ hz))
    (fun hd => hn (dsepPath_of_dsep hd))
  exact ⟨y, z, C, fun hc => hC (condIndep_single _ hYZ hY hZ hc hy hz)⟩

/-- **d-separation of sets ⇔ independence in all models.** For pairwise disjoint `X`, `Y`
and `Z`: `X` and `Y` are d-separated given `Z` if and only if `CondIndep M X Y Z` holds in
every causal model on `G` with bit vectors as values. -/
theorem dsepSet_iff (G : DAG V) (Z X Y : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hXY : Disjoint X Y) :
    SetSound.DSeparatedSet G Z X Y ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool)), CondIndep M X Y Z := by
  constructor
  · intro h k M
    exact SetSound.dsep_sound_set M X Y Z hXZ hYZ h
  · intro H
    by_contra hn
    obtain ⟨x, y, C, hC⟩ := exists_chain_not_condIndep_set hXZ hYZ hXY hn
    exact hC (H C.k (chainModel C))

/-- **Completeness of rule 1 for sets.** If `Y` and `Z` are not d-separated given `X ∪ W`
in `G_{X̄}`, there are a model on `G` and a value `x` for which
`CondIndep (do(X = x)) Y Z (X ∪ W)` fails. -/
theorem rule1_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
        ¬ CondIndep (doModel M X x) Y Z (X ∪ W) := by
  simp only [SetSound.DSeparatedSet, not_forall] at h
  obtain ⟨y, hy, z, hz, hn⟩ := h
  obtain ⟨k, M, x, hM⟩ := rule1_complete G X W y z (Finset.disjoint_left.mp hY hy)
    (Finset.disjoint_left.mp hZ hz)
    (fun e => Finset.disjoint_left.mp hYZ hy (by rw [e]; exact hz))
    (fun hd => hn (dsepPath_of_dsep hd))
  exact ⟨k, M, x, fun hci => hM (condIndep_single _ hYZ hY hZ hci hy hz)⟩

/-- **Rule 1 is exact, in exactly the form that `rule1` has.** The condition of rule 1
holds if and only if the rule holds in every model on `G` and for every value `x`. -/
theorem rule1_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X),
        CondIndep (doModel M X x) Y Z (X ∪ W) := by
  constructor
  · intro h k M x
    exact rule1 M X W Y Z x hY hZ h
  · intro H
    by_contra hn
    obtain ⟨k, M, x, hM⟩ := rule1_complete_set G X W Y Z hY hZ hYZ hn
    exact hM (H k M x)

end SetVersions

/-! ## Rule 2 for sets -/

section Rule2Set
open DoCalculus

/-- **Completeness of rule 2 for sets.** If `Y` and `Z` are not d-separated given `X ∪ W`
in `G_{X̄Z̲}`, there are a model on `G` and values for which the product form of `rule2`
fails. -/
theorem rule2_complete_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ ∧
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨y, z, C, hC⟩ := exists_chain_not_condIndep_set hY hZ hYZ h
  exact ⟨C.k, rule2_fails_of_chain C hYZ hZ hC⟩

/-- **Rule 2 is exact, in exactly the form that `rule2` has.** The condition of rule 2
holds if and only if its product form holds in every model on `G` and for all values. -/
theorem rule2_iff_set (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z) :
    SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (z₀ : Assignment (α := fun _ : V => Fin (k + 1) → Bool) Z)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union]; tauto) = z₀ →
        (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
          (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (Z ∪ (X ∪ W))
            (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x z₀ t ht
    exact rule2 M X Y Z W x z₀ hYZ hZ.symm hY h t ht
  · intro H
    by_contra hn
    obtain ⟨k, M, x, z₀, t, ht, hne⟩ := rule2_complete_set G X W Y Z hY hZ hYZ hn
    exact hne (H k M x z₀ t ht)

end Rule2Set

/-! ## Rule 3 for sets when the vertices of `Z` can be made roots

This covers the case where no `z ∈ Z` is an ancestor of `W` and, more generally, every case
where `Y` and `Z` are d-connected in `G_{X̄Z̄}`. -/

section Rule3Set
open DoCalculus

/-- If no `z ∈ Z` is an ancestor of `W`, then `Z(W) = Z`. -/
lemma Z2_all {H : DAG V} {Z W : Finset V} (h : ∀ z ∈ Z, z ∉ ancestors H W) :
    Rule3.Z2 H Z W = Z := by
  ext v
  simp only [Rule3.Z2, Finset.mem_filter]
  constructor
  · exact fun hv => hv.1
  · intro hv
    exact ⟨hv, h v hv⟩

/-- **Completeness of rule 3 for sets when no `z ∈ Z` is an ancestor of `W`.** If the
condition of `rule3_general` fails, there are a model on `G` and values for which the
product form of rule 3 fails. -/
theorem rule3_complete_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  rw [Z2_all hanc] at h
  obtain ⟨y, z, C, hC⟩ := exists_chain_not_condIndep_set hY hZ hYZ h
  exact ⟨C.k, rule3_fails_of_chain C hYZ hZ hC⟩

/-- **Rule 3 for sets is exact when no `z ∈ Z` is an ancestor of `W`.** The condition of
rule 3 holds if and only if its product form holds in every model on `G` and for all
values. -/
theorem rule3_iff_set_nonanc (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (hanc : ∀ z ∈ Z, z ∉ ancestors (cutIn G X) W) :
    SetSound.DSeparatedSet (cutIn (cutIn G X) (Rule3.Z2 (cutIn G X) Z W)) (X ∪ W) Y Z ↔
      ∀ (k : ℕ) (M : G.CausalModel (fun _ => Fin (k + 1) → Bool))
        (x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X)
        (t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W))),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  constructor
  · intro h k M x t
    exact Rule3Flag.rule3_general M X Y Z W x hYZ hZ.symm hY h t
  · intro H
    by_contra hn
    obtain ⟨k, M, x, t, hne⟩ := rule3_complete_set_nonanc G X W Y Z hY hZ hYZ hanc hn
    exact hne (H k M x t)

/-- **Rule 3 for sets fails when `Y` and `Z` are d-connected in `G_{X̄Z̄}`**, whether or
not the vertices of `Z` are ancestors of `W`. Then the vertices of `Z` can be made roots. -/
theorem rule3_complete_set_root (G : DAG V) (X W Y Z : Finset V)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W)) (hYZ : Disjoint Y Z)
    (h : ¬ SetSound.DSeparatedSet (cutIn (cutIn G X) Z) (X ∪ W) Y Z) :
    ∃ k : ℕ, ∃ M : G.CausalModel (fun _ => Fin (k + 1) → Bool),
      ∃ x : Assignment (α := fun _ : V => Fin (k + 1) → Bool) X,
      ∃ t : Assignment (α := fun _ : V => Fin (k + 1) → Bool) (Y ∪ Z ∪ (X ∪ W)),
        (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel M X x).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠
        (doModel M X x).marginal (Y ∪ (X ∪ W))
            (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
          (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
            intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
            (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  obtain ⟨y, z, C, hC⟩ := exists_chain_not_condIndep_set hY hZ hYZ h
  exact ⟨C.k, rule3_fails_of_chain C hYZ hZ hC⟩

end Rule3Set

end Completeness
