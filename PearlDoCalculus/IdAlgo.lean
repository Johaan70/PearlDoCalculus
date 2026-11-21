import PearlDoCalculus.IdAudit

/-!
# The ID algorithm as a computable check (step H1)

This file turns Tian's IDENTIFY and the whole ID check for `P(Y | do(X))` into functions
to `Bool` and proves them sound: when the check says yes, the effect is identifiable.
Because the functions compute, `decide` runs them on concrete graphs.

**Why.** The completeness theorem `Hedge.idCheck_iff` is a statement about this check:
it says yes exactly when there is no hedge. The inductive predicate `Reach` (in
`Identification/Identify.lean`) describes the successful runs of IDENTIFY but cannot be
evaluated; the functions here can, and soundness links the two.

**How.**

1. *Fixed points.* An inflationary map on subsets of `T` stands still after `|T|` steps
   (`iter_fix`): each step that changes the set adds an element, and there are at most
   `|T|` of them. The iterates grow (Mathlib's `Function.id_le_iterate_of_id_le`) and
   stay inside `T` (`Finset.iterate_subset`, in `Util/Finset.lean`).
2. *Closures inside `T`.* `ancIn G T C` is the set of ancestors of `C` inside `G[T]` and
   `ccIn G U T C` the closure of `C` under latent edges inside `T`, both computed by
   iterating one step `|T|` times. They contain `C`, stay inside `T` and are closed
   (`anc_sup`, `ancIn_subset`, `anc_closed`, `cc_sup`, `ccIn_subset`, `cc_closed`).
3. *IDENTIFY.* `identifyN G U n T C` sets `A := ancIn G T C`; if `A = C` it succeeds, if
   `A = T` it fails (a hedge stands here), and otherwise it continues with
   `ccIn G U A C`. The number `n` is fuel, and `identifyTop` gives enough. A run that
   says `true` gives a `Reach` witness (`identifyN_sound`, `identifyTop_sound`).
4. *The whole check.* `idCheck G U X Y` takes the ancestors `S` of `Y` in `G_{X̄}` and
   asks IDENTIFY to succeed for the c-component of every observed `y ∈ S ∖ X`. The
   computed closure is that c-component (`ccIn_eq`), so `id_sound_anc` gives
   identifiability (`idCheck_sound`).
5. *Concrete graphs.* On `IdAudit.idG` the check says yes, which recovers
   `IdAudit.id_audit` with no hand work (`id_audit'`); on the bow it says no
   (`bow_check`, `bow_idCheck`).

**Main results.** `IdAlgo.ancIn`, `IdAlgo.ccIn`, `IdAlgo.identifyTop`,
`IdAlgo.identifyTop_sound`, `IdAlgo.ccIn_eq`, `IdAlgo.idCheck`, `IdAlgo.idCheck_sound`.
-/

open PearlDoCalculus DAG DoCalculus Identification Identification.CFactor

namespace IdAlgo

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Fixed points of an inflationary map -/

omit [DecidableEq V] [Fintype V] in
/-- After `|T|` steps an inflationary map inside `T` stands still. -/
theorem iter_fix (T : Finset V) (f : Finset V → Finset V) (hinf : ∀ A, A ⊆ f A)
    (hbd : ∀ A, A ⊆ T → f A ⊆ T) (A0 : Finset V) (h0 : A0 ⊆ T) :
    f (f^[T.card] A0) = f^[T.card] A0 := by
  have hsub := Finset.iterate_subset T f hbd A0 h0
  have key : ∀ k, f (f^[k] A0) = f^[k] A0 ∨ k ≤ (f^[k] A0).card := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k ih =>
      rw [show f^[k + 1] A0 = f (f^[k] A0) from Function.iterate_succ_apply' f k A0]
      by_cases hfix : f (f^[k] A0) = f^[k] A0
      · left
        rw [hfix, hfix]
      · right
        rcases ih with h | hk
        · exact absurd h hfix
        · have hss : f^[k] A0 ⊂ f (f^[k] A0) :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hinf _, fun e => hfix e.symm⟩
          have := Finset.card_lt_card hss
          omega
  rcases key T.card with hfix | hk
  · exact hfix
  · have heq : f^[T.card] A0 = T := Finset.eq_of_subset_of_card_le (hsub _) hk
    apply Finset.Subset.antisymm _ (hinf _)
    rw [heq]
    exact hbd T (Finset.Subset.refl T)

/-! ### Ancestors and c-closure inside `T` -/

/-- One step towards the ancestors of `A` inside `T`. -/
def ancStep (G : DAG V) (T A : Finset V) : Finset V :=
  A ∪ T.filter (fun v => ∃ a ∈ A, G.edge v a)

/-- The ancestors of `C` inside `G[T]`. -/
def ancIn (G : DAG V) (T C : Finset V) : Finset V := (ancStep G T)^[T.card] C

/-- One latent step inside `T`. -/
def ccStep (G : DAG V) (U T B : Finset V) : Finset V :=
  B ∪ T.filter (fun w => ∃ b ∈ B, (b ∈ U ∧ G.edge b w) ∨ (w ∈ U ∧ G.edge w b))

/-- The closure of `C` under latent steps inside `T`. -/
def ccIn (G : DAG V) (U T C : Finset V) : Finset V := (ccStep G U T)^[T.card] C

/-- `ancIn G T C` contains `C`. -/
lemma anc_sup (G : DAG V) (T C : Finset V) : C ⊆ ancIn G T C :=
  Function.id_le_iterate_of_id_le (f := ancStep G T) (fun _ => Finset.subset_union_left) T.card C

/-- `ancIn G T C` lies inside `T`. -/
lemma ancIn_subset (G : DAG V) (T C : Finset V) (hC : C ⊆ T) : ancIn G T C ⊆ T :=
  Finset.iterate_subset T (ancStep G T)
    (fun _ h => Finset.union_subset h (Finset.filter_subset _ _)) C hC T.card

/-- `ancIn G T C` is closed under parents inside `T`. -/
lemma anc_closed (G : DAG V) (T C : Finset V) (hC : C ⊆ T) :
    ∀ v ∈ T, (∃ a ∈ ancIn G T C, G.edge v a) → v ∈ ancIn G T C := by
  intro v hv h
  have hfix : ancStep G T (ancIn G T C) = ancIn G T C :=
    iter_fix T (ancStep G T) (fun _ => Finset.subset_union_left)
      (fun _ h => Finset.union_subset h (Finset.filter_subset _ _)) C hC
  rw [← hfix]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, h⟩)

/-- `ccIn G U T C` contains `C`. -/
lemma cc_sup (G : DAG V) (U T C : Finset V) : C ⊆ ccIn G U T C :=
  Function.id_le_iterate_of_id_le (f := ccStep G U T) (fun _ => Finset.subset_union_left) T.card C

/-- `ccIn G U T C` lies inside `T`. -/
lemma ccIn_subset (G : DAG V) (U T C : Finset V) (hC : C ⊆ T) : ccIn G U T C ⊆ T :=
  Finset.iterate_subset T (ccStep G U T)
    (fun _ h => Finset.union_subset h (Finset.filter_subset _ _)) C hC T.card

/-- `ccIn G U T C` is closed under latent steps inside `T`. -/
lemma cc_closed (G : DAG V) (U T C : Finset V) (hC : C ⊆ T) :
    ∀ w ∈ T, (∃ b ∈ ccIn G U T C, (b ∈ U ∧ G.edge b w) ∨ (w ∈ U ∧ G.edge w b)) →
      w ∈ ccIn G U T C := by
  intro w hw h
  have hfix : ccStep G U T (ccIn G U T C) = ccIn G U T C :=
    iter_fix T (ccStep G U T) (fun _ => Finset.subset_union_left)
      (fun _ h => Finset.union_subset h (Finset.filter_subset _ _)) C hC
  rw [← hfix]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, h⟩)

/-! ### IDENTIFY -/

/-- **Tian's IDENTIFY**, with fuel `n`. -/
def identifyN (G : DAG V) (U : Finset V) : ℕ → Finset V → Finset V → Bool
  | 0, _, _ => false
  | n + 1, T, C =>
    if ancIn G T C = C then true
    else if ancIn G T C = T then false
    else identifyN G U n (ccIn G U (ancIn G T C) C) C

/-- **Soundness:** `true` gives a `Reach` witness. -/
theorem identifyN_sound (G : DAG V) (U : Finset V) :
    ∀ n T C, C ⊆ T → IsLatClosed G U T → identifyN G U n T C = true → Reach G U T C := by
  intro n
  induction n with
  | zero =>
    intro T C _ _ h
    simp [identifyN] at h
  | succ n ih =>
    intro T C hCT hT h
    have hAT : ancIn G T C ⊆ T := ancIn_subset G T C hCT
    have hCA : C ⊆ ancIn G T C := anc_sup G T C
    have hanc : ∀ v ∈ T ∩ ancIn G T C, ∀ p ∈ T, G.edge p v → p ∈ ancIn G T C :=
      fun v hv p hp e => anc_closed G T C hCT p hp ⟨v, (Finset.mem_inter.mp hv).2, e⟩
    have hTA : T ∩ ancIn G T C = ancIn G T C := Finset.inter_eq_right.mpr hAT
    simp only [identifyN] at h
    by_cases h1 : ancIn G T C = C
    · refine Reach.anc T (ancIn G T C) C hanc ?_
      rw [hTA, h1]
      exact Reach.refl C
    · rw [if_neg h1] at h
      by_cases h2 : ancIn G T C = T
      · rw [if_pos h2] at h
        exact absurd h Bool.false_ne_true
      · rw [if_neg h2] at h
        have hA : IsLatClosed G U (ancIn G T C) := fun v hv u hu e =>
          anc_closed G T C hCT u (hT v (hAT hv) u hu e) ⟨v, hv, e⟩
        have hT'A : ccIn G U (ancIn G T C) C ⊆ ancIn G T C := ccIn_subset G U _ C hCA
        have hCT' : C ⊆ ccIn G U (ancIn G T C) C := cc_sup G U _ C
        have hT' : IsLatClosed G U (ccIn G U (ancIn G T C) C) := fun v hv u hu e =>
          cc_closed G U _ C hCA u (hA v (hT'A hv) u hu e) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
        have hcl : ∀ u ∈ U, ∀ v ∈ ancIn G T C, G.edge u v →
            (u ∈ ccIn G U (ancIn G T C) C ↔ v ∈ ccIn G U (ancIn G T C) C) :=
          fun u hu v hv e =>
            ⟨fun hu' => cc_closed G U _ C hCA v hv ⟨u, hu', Or.inl ⟨hu, e⟩⟩,
              fun hv' => cc_closed G U _ C hCA u (hA v hv u hu e) ⟨v, hv', Or.inr ⟨hu, e⟩⟩⟩
        refine Reach.anc T (ancIn G T C) C hanc ?_
        rw [hTA]
        refine Reach.block (ancIn G T C) (ccIn G U (ancIn G T C) C) C hcl ?_
        rw [Finset.inter_eq_right.mpr hT'A]
        exact ih _ C hCT' hT' h

/-- IDENTIFY started from the c-closure of `D` in the whole graph, with enough fuel. -/
def identifyTop (G : DAG V) (U D : Finset V) : Bool :=
  identifyN G U (Fintype.card V + 1) (ccIn G U Finset.univ D) D

/-- **Soundness:** `identifyTop … = true` gives `Reach G U V D`. -/
theorem identifyTop_sound (G : DAG V) (U D : Finset V) (h : identifyTop G U D = true) :
    Reach G U Finset.univ D := by
  have hD : D ⊆ ccIn G U Finset.univ D := cc_sup G U _ D
  have hcl : ∀ u ∈ U, ∀ v ∈ (Finset.univ : Finset V), G.edge u v →
      (u ∈ ccIn G U Finset.univ D ↔ v ∈ ccIn G U Finset.univ D) := fun u hu v _ e =>
    ⟨fun hu' => cc_closed G U _ D (Finset.subset_univ D) v (Finset.mem_univ v)
        ⟨u, hu', Or.inl ⟨hu, e⟩⟩,
      fun hv' => cc_closed G U _ D (Finset.subset_univ D) u (Finset.mem_univ u)
        ⟨v, hv', Or.inr ⟨hu, e⟩⟩⟩
  have hlat : IsLatClosed G U (ccIn G U Finset.univ D) := fun v hv u hu e =>
    cc_closed G U _ D (Finset.subset_univ D) u (Finset.mem_univ u) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
  refine Reach.block Finset.univ (ccIn G U Finset.univ D) D hcl ?_
  rw [Finset.univ_inter]
  exact identifyN_sound G U _ _ D hD hlat h

/-! ### Checks on concrete graphs -/

/-- On `IdAudit.idG`, IDENTIFY succeeds for the block `{u₂, y}`. -/
theorem idAudit_check : identifyTop IdAudit.idG {0, 1} {1, 4} = true := by decide

/-- On the bow, IDENTIFY fails for the block `{u, y}`: here stands the hedge. -/
theorem bow_check : identifyTop Bow.bowG {0} {0, 2} = false := by decide

/-- `IdAudit.reach_y` again, now computed instead of written by hand. -/
theorem reach_y' : Reach IdAudit.idG {0, 1} Finset.univ {1, 4} :=
  identifyTop_sound _ _ _ idAudit_check

end IdAlgo

#print axioms IdAlgo.identifyN_sound
#print axioms IdAlgo.identifyTop_sound
#print axioms IdAlgo.idAudit_check
#print axioms IdAlgo.bow_check
#print axioms IdAlgo.reach_y'

/-! ## The whole ID check for `P(Y | do(X))`

* `ccIn_eq`: for `y ∈ T` the computed closure `ccIn G U T {y}` equals
  `T ∩ ccomp (G[T]) y`, the c-component as `id_sound_anc` uses it.
* `idCheck G U X Y`: `S := ancIn (cutIn G X) V Y` (the ancestors of `Y` in `G_{X̄}`), and
  for every observed `y ∈ S ∖ X`, IDENTIFY must succeed for the block
  `ccIn (G_{X̄}) U S {y}`.
* `idCheck_sound`: `idCheck = true` gives identifiability (through `id_sound_anc`).

With this, `decide` checks a whole effect: `id_audit'` recovers `IdAudit.id_audit` with
no hand work, and on the bow the check says no. -/

namespace IdAlgo

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The computed closure is the c-component** in `G[T]`. -/
theorem ccIn_eq (G : DAG V) (U T : Finset V) (y : V) (hy : y ∈ T) :
    ccIn G U T {y} = T ∩ ccomp (DAG.induce G T) U y := by
  have hyT : ({y} : Finset V) ⊆ T := Finset.singleton_subset_iff.mpr hy
  apply Finset.Subset.antisymm
  · refine Finset.iterate_subset (T ∩ ccomp (DAG.induce G T) U y) (ccStep G U T) ?_ {y} ?_ T.card
    · intro A hA w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hA h
      · obtain ⟨hwT, b, hb, hrel⟩ := Finset.mem_filter.mp h
        have hbT := (Finset.mem_inter.mp (hA hb)).1
        have hbC := (Finset.mem_inter.mp (hA hb)).2
        refine Finset.mem_inter.mpr ⟨hwT, ?_⟩
        have step : latStep (DAG.induce G T) U b w := by
          rcases hrel with ⟨hbU, e⟩ | ⟨hwU, e⟩
          · exact Or.inl ⟨hbU, (⟨hbT, hwT, e⟩ : b ∈ T ∧ w ∈ T ∧ G.edge b w)⟩
          · exact Or.inr ⟨hwU, (⟨hwT, hbT, e⟩ : w ∈ T ∧ b ∈ T ∧ G.edge w b)⟩
        exact mem_ccomp.mpr ((mem_ccomp.mp hbC).tail step)
    · intro z hz
      rw [Finset.mem_singleton.mp hz]
      exact Finset.mem_inter.mpr ⟨hy, self_mem_ccomp _ U y⟩
  · intro z hz
    have hr := mem_ccomp.mp (Finset.mem_inter.mp hz).2
    clear hz
    induction hr with
    | refl => exact cc_sup G U T {y} (Finset.mem_singleton_self y)
    | @tail b c _ hbc ih =>
      have hcT : c ∈ T := by
        rcases hbc with ⟨_, e⟩ | ⟨_, e⟩
        · exact (show b ∈ T ∧ c ∈ T ∧ G.edge b c from e).2.1
        · exact (show c ∈ T ∧ b ∈ T ∧ G.edge c b from e).1
      refine cc_closed G U T {y} hyT c hcT ⟨b, ih, ?_⟩
      rcases hbc with ⟨hbU, e⟩ | ⟨hcU, e⟩
      · exact Or.inl ⟨hbU, (show b ∈ T ∧ c ∈ T ∧ G.edge b c from e).2.2⟩
      · exact Or.inr ⟨hcU, (show c ∈ T ∧ b ∈ T ∧ G.edge c b from e).2.2⟩

/-- **The whole ID check** for `P(Y | do(X))`. -/
def idCheck (G : DAG V) (U X Y : Finset V) : Bool :=
  decide (∀ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U → y ∉ X →
    identifyTop G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) = true)

/-- **Soundness:** `idCheck = true` gives identifiability. -/
theorem idCheck_sound {α : V → Type*} [∀ v, Nonempty (α v)] (G : DAG V) (U X Y : Finset V)
    (hXO : X ⊆ Uᶜ) (hY : Y ⊆ Uᶜ) (h : idCheck G U X Y = true) :
    Identifiable G α Uᶜ X Y := by
  have hS : ∀ v ∈ ancIn (cutIn G X) Finset.univ Y, ∀ p, (cutIn G X).edge p v →
      p ∈ ancIn (cutIn G X) Finset.univ Y := fun v hv p e =>
    anc_closed (cutIn G X) Finset.univ Y (Finset.subset_univ Y) p (Finset.mem_univ p) ⟨v, hv, e⟩
  unfold idCheck at h
  have hc := of_decide_eq_true h
  refine id_sound_anc U X hXO (ancIn (cutIn G X) Finset.univ Y) hS (fun y hyS hyU hyX => ?_) Y
    (anc_sup (cutIn G X) Finset.univ Y) hY
  rw [← ccIn_eq (cutIn G X) U _ y hyS]
  exact identifyTop_sound G U _ (hc y hyS hyU hyX)

/-- On `IdAudit.idG` the ID check says yes for `P(y | do(x))`. -/
theorem idAudit_idCheck : idCheck IdAudit.idG {0, 1} {2} {4} = true := by decide

/-- `IdAudit.id_audit` again, fully automatically. -/
theorem id_audit' :
    Identifiable IdAudit.idG (fun _ => Bool) ({0, 1} : Finset (Fin 5))ᶜ {2} {4} :=
  idCheck_sound _ _ _ _ (by decide) (by decide) idAudit_idCheck

/-- On the bow the ID check says no for `P(y | do(x))`. -/
theorem bow_idCheck : idCheck Bow.bowG {0} {1} {2} = false := by decide

end IdAlgo

#print axioms IdAlgo.ccIn_eq
#print axioms IdAlgo.idCheck_sound
#print axioms IdAlgo.id_audit'
#print axioms IdAlgo.bow_idCheck
