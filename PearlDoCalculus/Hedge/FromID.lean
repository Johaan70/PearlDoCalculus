import PearlDoCalculus.Hedge.Defs

/-!
# From a failing ID check to a hedge (step H2)

This file proves `idCheck_false_hedge`: if the ID check `idCheck G U X Y` says no, and `X`
is observed, then the graph contains a hedge for `P_X(Y)` (`IsHedge`, defined in
`Hedge/Defs.lean`). It is the easy half of the completeness theorem `Hedge.idCheck_iff`;
the other half shows that a hedge blocks identification.

**Why.** Completeness says that whenever ID fails, the effect is not identifiable. The
proof goes through a hedge: ID failure gives a hedge (this file), and a hedge gives two
models with the same observed distribution but different effects (the later files).
`idCheck_false_hedge` is used once, in the final assembly `idCheck_iff`
(`Hedge/Complete`); the small closure lemma `ancIn_min` is also used in `Hedge/Tree`
and `Hedge/Tails`.

**How.** The proof follows the recursion of IDENTIFY (in `IdAlgo`).

1. *Where ID gets stuck.* When IDENTIFY answers no it is stuck at a set `T` that strictly
   contains the target `D`, consists of ancestors of `D` inside `G[T]`, and is the
   c-closure of `D` inside a larger set (`Stuck`, `identifyN_false`). The fuel in
   `identifyTop` is enough, since every step shrinks `T` strictly. If the whole check
   says no, this happens for the block `D` of some `y` (`idCheck_false`).
2. *`T` meets `X`.* Otherwise all of `T` would lie among the ancestors of `Y` in `G_{X̄}`,
   the c-closure of `D` would stay inside `D`, and `T = D` (`stuck_meets_X`).
3. *Rooted.* With `R := rootsIn G D`, every node of `D` reaches `R` inside `D`
   (`ancIn_roots`), and every node of `T` reaches `R` inside `T` (`stuck_rooted`);
   `stuck_hedge_pre` collects these facts for the pair `(D, T)`.
4. *C-connected.* `D` is c-connected inside itself in `G` (`block_reach`), and so is
   `T`, its c-closure (`stuck_reach`). Then `(D, T)` is a hedge.

**Main results.** `identifyN_false`, `idCheck_false`, `stuck_meets_X`,
`idCheck_false_meets`, `ancIn_roots`, `stuck_rooted`, `stuck_hedge_pre`, `block_reach`,
`stuck_reach`, `idCheck_false_hedge` (public), and the bow examples `bow_stuck`,
`bow_hedge`.
-/

/-! ## Where IDENTIFY gets stuck

When IDENTIFY says no, it is stuck at a set `T` with

* `C ⊊ T`, and all of `T` consists of ancestors of `C` inside `G[T]` (`ancIn G T C = T`);
* `T` is latent-closed, and is the c-closure of `C` inside a larger set.

This is Tian's failure case `A = T`, and the candidate for the hedge `(C, T)`. The fuel
in `identifyTop` is enough: each step shrinks `T` strictly (`identifyN_false`).
`idCheck_false` gives such a witness for one of the blocks when the whole ID check says no.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **IDENTIFY is stuck** at `T` with target `C`: `C ⊊ T`, every node of `T` is an
ancestor of `C` inside `G[T]`, `T` is latent-closed, and `T` is the c-closure of `C`
inside some larger set `T'`. This is Tian's failure case `A = T`. -/
structure Stuck (G : DAG V) (U C T : Finset V) : Prop where
  sub : C ⊆ T
  ne : C ≠ T
  anc : ancIn G T C = T
  lat : IsLatClosed G U T
  cc : ∃ T', C ⊆ T' ∧ T ⊆ T' ∧ ccIn G U T' C = T

/-- **When IDENTIFY says no, it is stuck somewhere**, provided the fuel `n` exceeds
`|T|`. By induction on the fuel: each recursive call replaces `T` by the c-closure of
`C` inside `ancIn G T C`, a strictly smaller set. -/
theorem identifyN_false (G : DAG V) (U : Finset V) :
    ∀ n T C, C ⊆ T → IsLatClosed G U T → (∃ T', C ⊆ T' ∧ T ⊆ T' ∧ ccIn G U T' C = T) →
      T.card < n → identifyN G U n T C = false → ∃ T₀, Stuck G U C T₀ := by
  intro n
  induction n with
  | zero =>
    intro T C _ _ _ hn _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro T C hCT hT hcc hn h
    have hAT : ancIn G T C ⊆ T := ancIn_subset G T C hCT
    have hCA : C ⊆ ancIn G T C := anc_sup G T C
    simp only [identifyN] at h
    by_cases h1 : ancIn G T C = C
    · rw [if_pos h1] at h
      exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : ancIn G T C = T
      · exact ⟨T, ⟨hCT, fun e => h1 (h2.trans e.symm), h2, hT, hcc⟩⟩
      · rw [if_neg h2] at h
        have hA : IsLatClosed G U (ancIn G T C) := fun v hv u hu e =>
          anc_closed G T C hCT u (hT v (hAT hv) u hu e) ⟨v, hv, e⟩
        have hT'A : ccIn G U (ancIn G T C) C ⊆ ancIn G T C := ccIn_subset G U _ C hCA
        have hCT' : C ⊆ ccIn G U (ancIn G T C) C := cc_sup G U _ C
        have hT' : IsLatClosed G U (ccIn G U (ancIn G T C) C) := fun v hv u hu e =>
          cc_closed G U _ C hCA u (hA v (hT'A hv) u hu e) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
        have hss : ancIn G T C ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAT, h2⟩
        have hcard : (ccIn G U (ancIn G T C) C).card < n :=
          lt_of_le_of_lt (Finset.card_le_card hT'A)
            (lt_of_lt_of_le (Finset.card_lt_card hss) (Nat.lt_succ_iff.mp hn))
        exact ih _ C hCT' hT' ⟨ancIn G T C, hCA, hT'A, rfl⟩ hcard h

/-- **If `identifyTop` says no, IDENTIFY is stuck.** The fuel `|V| + 1` of `identifyTop`
exceeds the size of the starting set, so `identifyN_false` applies. -/
theorem identifyTop_false (G : DAG V) (U D : Finset V) (h : identifyTop G U D = false) :
    ∃ T, Stuck G U D T := by
  have hD : D ⊆ ccIn G U Finset.univ D := cc_sup G U _ D
  have hlat : IsLatClosed G U (ccIn G U Finset.univ D) := fun v hv u hu e =>
    cc_closed G U _ D (Finset.subset_univ D) u (Finset.mem_univ u) ⟨v, hv, Or.inr ⟨hu, e⟩⟩
  have hcard : (ccIn G U Finset.univ D).card < Fintype.card V + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_univ _)
  exact identifyN_false G U _ _ D hD hlat
    ⟨Finset.univ, Finset.subset_univ D, Finset.subset_univ _, rfl⟩ hcard h

/-- **If the whole ID check says no, IDENTIFY is stuck for one of the blocks**: the
c-component `D` of some observed `y ∉ X` inside `G_{X̄}[An(Y)]`. -/
theorem idCheck_false (G : DAG V) (U X Y : Finset V) (h : idCheck G U X Y = false) :
    ∃ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U ∧ y ∉ X ∧
      ∃ T, Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T := by
  unfold idCheck at h
  have h' := of_decide_eq_false h
  simp only [not_forall] at h'
  obtain ⟨y, hy, hU, hX, hne⟩ := h'
  exact ⟨y, hy, hU, hX, identifyTop_false G U _ (by simpa using hne)⟩

/-- On the bow graph, IDENTIFY gets stuck. -/
theorem bow_stuck : ∃ T, Stuck Bow.bowG {0} {0, 2} T :=
  identifyTop_false _ _ _ bow_check

end Hedge

/-! ## Where ID gets stuck, `T` meets `X`

If `D` is a c-component of `G_{X̄}[S]` (`S` = the ancestors of `Y` in `G_{X̄}`) and
IDENTIFY is stuck at `T`, then `T` meets `X`. Otherwise all of `T` would lie in `S` (every
node is an ancestor of `D` inside `T`, and no edge into `X` is used), and the c-closure
of `D` inside `T` would stay inside `D`; then `T = D`, contradicting `D ⊊ T`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Where ID gets stuck, `T` meets `X`.** -/
theorem stuck_meets_X (G : DAG V) (U X Y : Finset V) (y : V)
    (hyS : y ∈ ancIn (cutIn G X) Finset.univ Y) {T : Finset V}
    (hst : Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T) :
    ∃ x ∈ X, x ∈ T := by
  by_contra hno
  have hTX : ∀ v ∈ T, v ∉ X := fun v hv hx => hno ⟨v, hx, hv⟩
  set S := ancIn (cutIn G X) Finset.univ Y
  have hyS' : ({y} : Finset V) ⊆ S := Finset.singleton_subset_iff.mpr hyS
  have hSanc : ∀ v ∈ S, ∀ p, (cutIn G X).edge p v → p ∈ S := fun v hv p e =>
    anc_closed (cutIn G X) Finset.univ Y (Finset.subset_univ Y) p (Finset.mem_univ p) ⟨v, hv, e⟩
  have hDS : ccIn (cutIn G X) U S {y} ⊆ S := ccIn_subset (cutIn G X) U S {y} hyS'
  -- Step 1: all of `T` lies in `S`.
  have h1 : ∀ k, (ancStep G T)^[k] (ccIn (cutIn G X) U S {y}) ⊆ S ∩ T := by
    refine Finset.iterate_subset (S ∩ T) (ancStep G T) ?_ _ ?_
    · intro A hA w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hA h
      · obtain ⟨hwT, a, ha, e⟩ := Finset.mem_filter.mp h
        have haS := (Finset.mem_inter.mp (hA ha)).1
        have haT := (Finset.mem_inter.mp (hA ha)).2
        exact Finset.mem_inter.mpr
          ⟨hSanc a haS w (⟨e, hTX a haT⟩ : G.edge w a ∧ a ∉ X), hwT⟩
    · intro v hv
      exact Finset.mem_inter.mpr ⟨hDS hv, hst.sub hv⟩
  have hTS : T ⊆ S := by
    intro v hv
    have hv' : v ∈ ancIn G T (ccIn (cutIn G X) U S {y}) := by rw [hst.anc]; exact hv
    exact (Finset.mem_inter.mp (h1 T.card hv')).1
  -- Step 2: the c-closure stays inside `D`.
  obtain ⟨T', _, _, hcc⟩ := hst.cc
  have hAT : ∀ j, j ≤ T'.card →
      (ccStep G U T')^[j] (ccIn (cutIn G X) U S {y}) ⊆ T := fun j hj v hv => by
    rw [← hcc]
    exact Function.monotone_iterate_of_id_le (f := ccStep G U T')
      (fun _ => Finset.subset_union_left) hj _ hv
  have key : ∀ k, k ≤ T'.card →
      (ccStep G U T')^[k] (ccIn (cutIn G X) U S {y}) ⊆ ccIn (cutIn G X) U S {y} := by
    intro k
    induction k with
    | zero => intro _; exact Finset.Subset.refl _
    | succ k ih =>
      intro hk
      have hAk := ih (Nat.le_of_succ_le hk)
      have hAkT := hAT k (Nat.le_of_succ_le hk)
      intro w hw
      have hwT := hAT (k + 1) hk hw
      rw [show (ccStep G U T')^[k + 1] (ccIn (cutIn G X) U S {y}) =
          ccStep G U T' ((ccStep G U T')^[k] (ccIn (cutIn G X) U S {y})) from
        Function.iterate_succ_apply' _ k _] at hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hAk h
      · obtain ⟨_, b, hb, hrel⟩ := Finset.mem_filter.mp h
        have hbT := hAkT hb
        refine cc_closed (cutIn G X) U S {y} hyS' w (hTS hwT) ⟨b, hAk hb, ?_⟩
        rcases hrel with ⟨hbU, e⟩ | ⟨hwU, e⟩
        · exact Or.inl ⟨hbU, (⟨e, hTX w hwT⟩ : G.edge b w ∧ w ∉ X)⟩
        · exact Or.inr ⟨hwU, (⟨e, hTX b hbT⟩ : G.edge w b ∧ b ∉ X)⟩
  have hTD : T ⊆ ccIn (cutIn G X) U S {y} := fun v hv => by
    rw [← hcc] at hv
    exact key T'.card le_rfl hv
  exact hst.ne (Finset.Subset.antisymm hst.sub hTD)

/-- **If the ID check says no, IDENTIFY is stuck at a `T` that meets `X`.** -/
theorem idCheck_false_meets (G : DAG V) (U X Y : Finset V) (h : idCheck G U X Y = false) :
    ∃ y ∈ ancIn (cutIn G X) Finset.univ Y, y ∉ U ∧ y ∉ X ∧
      ∃ T, Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T ∧
        ∃ x ∈ X, x ∈ T := by
  obtain ⟨y, hy, hU, hX, T, hst⟩ := idCheck_false G U X Y h
  exact ⟨y, hy, hU, hX, T, hst, stuck_meets_X G U X Y y hy hst⟩

end Hedge

/-! ## The roots, and the hedge without c-connectedness

In Shpitser and Pearl a C-forest is a *subgraph* in which each node keeps at most one
child edge, so the roots need not be childless in `G[F']`. With `R := rootsIn G D` (the
nodes of `D` without a child in `D`) both `D` and `T` are `R`-rooted:

* `ancIn_roots`: every node of `D` reaches a root inside `D` (follow children until it
  stops; the rank grows along edges, so it ends);
* `stuck_rooted`: every node of `T` reaches `D` inside `T`, and hence `R`.

`stuck_hedge_pre` collects what then holds for `(F, F') = (D, T)`: the same roots, `D`
outside `X`, `T` meets `X`, the roots are ancestors of `Y` in `G_{X̄}`. What is missing
for a hedge is the c-connectedness of `D` and `T` (next section). -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `ancIn G T C` is the smallest set that contains `C` and is closed under taking
parents inside `T`. -/
lemma ancIn_min (G : DAG V) (T C A : Finset V) (hCA : C ⊆ A)
    (hA : ∀ v ∈ T, (∃ a ∈ A, G.edge v a) → v ∈ A) : ancIn G T C ⊆ A :=
  Finset.iterate_subset A (ancStep G T) (fun B hB w hw => by
    rcases Finset.mem_union.mp hw with h | h
    · exact hB h
    · obtain ⟨hwT, b, hb, e⟩ := Finset.mem_filter.mp h
      exact hA w hwT ⟨b, hB hb, e⟩) C hCA T.card

/-- **Every node of `F` reaches a root of `F` inside `F`.** A node of maximal rank
outside the ancestors of the roots would have a child in `F` of larger rank. -/
theorem ancIn_roots (G : DAG V) (F : Finset V) : ancIn G F (rootsIn G F) = F := by
  have hRF : rootsIn G F ⊆ F := Finset.filter_subset _ _
  apply Finset.Subset.antisymm (ancIn_subset G F _ hRF)
  by_contra hno
  have hne : (F \ ancIn G F (rootsIn G F)).Nonempty := Finset.sdiff_nonempty.mpr hno
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image _ G.rank hne
  obtain ⟨hvF, hvA⟩ := Finset.mem_sdiff.mp hv
  have hvR : ¬ ∀ w ∈ F, ¬ G.edge v w := fun h =>
    hvA (anc_sup G F _ (Finset.mem_filter.mpr ⟨hvF, h⟩))
  obtain ⟨w, hwF, e⟩ : ∃ w ∈ F, G.edge v w := by
    by_contra h'
    exact hvR (fun w hw e => h' ⟨w, hw, e⟩)
  by_cases hwA : w ∈ ancIn G F (rootsIn G F)
  · exact hvA (anc_closed G F _ hRF v hvF ⟨w, hwA, e⟩)
  · have hle := hmax w (Finset.mem_sdiff.mpr ⟨hwF, hwA⟩)
    exact absurd hle (not_le.mpr (G.rank_strict_mono v w e))

/-- `ancIn` grows with the ambient set: `D ⊆ T` gives `ancIn G D C ⊆ ancIn G T C`. -/
lemma ancIn_mono (G : DAG V) (D T C : Finset V) (hCD : C ⊆ D) (hDT : D ⊆ T) :
    ancIn G D C ⊆ ancIn G T C :=
  ancIn_min G D C (ancIn G T C) (anc_sup G T C)
    (fun v hv h => anc_closed G T C (hCD.trans hDT) v (hDT hv) h)

/-- **Where IDENTIFY is stuck, `T` is rooted in the roots of the target `D`.** -/
theorem stuck_rooted (G : DAG V) (U D T : Finset V) (hst : Stuck G U D T) :
    ancIn G T (rootsIn G D) = T := by
  have hRD : rootsIn G D ⊆ D := Finset.filter_subset _ _
  have hRT : rootsIn G D ⊆ T := hRD.trans hst.sub
  apply Finset.Subset.antisymm (ancIn_subset G T _ hRT)
  have hDA : D ⊆ ancIn G T (rootsIn G D) := by
    calc D = ancIn G D (rootsIn G D) := (ancIn_roots G D).symm
      _ ⊆ ancIn G T (rootsIn G D) := ancIn_mono G D T _ hRD hst.sub
  calc T = ancIn G T D := hst.anc.symm
    _ ⊆ ancIn G T (rootsIn G D) :=
      ancIn_min G T D _ hDA (fun v hv h => anc_closed G T _ hRT v hv h)

/-- **The hedge without c-connectedness.** Where the ID check gets stuck, `D` and `T`
are both rooted in the roots of `D`, `D` lies outside `X`, `T` meets `X`, and the roots
are ancestors of `Y` in `G_{X̄}`. -/
theorem stuck_hedge_pre (G : DAG V) (U X Y : Finset V) (hXO : X ⊆ Uᶜ) (y : V)
    (hyS : y ∈ ancIn (cutIn G X) Finset.univ Y) (hyX : y ∉ X) {T : Finset V}
    (hst : Stuck G U (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) T) :
    ancIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})
        (rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})) =
      ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y} ∧
    ancIn G T (rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y})) = T ∧
    (∀ v ∈ ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}, v ∉ X) ∧
    (∃ x ∈ X, x ∈ T) ∧
    rootsIn G (ccIn (cutIn G X) U (ancIn (cutIn G X) Finset.univ Y) {y}) ⊆
      ancIn (cutIn G X) Finset.univ Y := by
  have hyS' : ({y} : Finset V) ⊆ ancIn (cutIn G X) Finset.univ Y :=
    Finset.singleton_subset_iff.mpr hyS
  refine ⟨ancIn_roots G _, stuck_rooted G U _ T hst, ?_, stuck_meets_X G U X Y y hyS hst, ?_⟩
  · intro z hz hzX
    rw [ccIn_eq (cutIn G X) U _ y hyS] at hz
    have hzC := (Finset.mem_inter.mp hz).2
    have hyz : y ∈ ccomp (DAG.induce (cutIn G X) (ancIn (cutIn G X) Finset.univ Y)) U z := by
      rw [ccomp_eq_of_mem hzC]
      exact self_mem_ccomp _ U y
    have := ccomp_ind_X G U X _ hXO hzX hyz
    rw [Finset.mem_singleton.mp this] at hyX
    exact hyX hzX
  · exact (Finset.filter_subset _ _).trans (ccIn_subset (cutIn G X) U _ {y} hyS')

end Hedge

/-! ## C-connectedness, and the hedge

* `block_reach`: the block `D` (the c-component of `y` in `G_{X̄}[S]`) is c-connected
  inside itself in `G`: every latent path in `G_{X̄}[S]` from `y` stays in `D`.
* `stuck_reach`: `T` is the c-closure of `D`, so every node of `T` reaches `y` by latent
  steps inside `T`.
* `idCheck_false_hedge`: **if the ID check says no, there is a hedge** (`IsHedge`, in
  `Hedge/Defs`). This finishes step H2; `bow_hedge` is the bow graph. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A set whose nodes all lie in the c-component of one node `y` (inside `G[F]`) is
c-connected. -/
lemma cconn_of_reach (G : DAG V) (U F : Finset V) (y : V)
    (h : ∀ b ∈ F, b ∈ ccomp (DAG.induce G F) U y) : CConn G U F :=
  fun a ha b hb => by
    rw [ccomp_eq_of_mem (h a ha)]
    exact h b hb

/-- A latent step inside `G[D]` is also a latent step inside `G[T]` when `D ⊆ T`. -/
lemma latStep_induce_mono (G : DAG V) (U D T : Finset V) (hDT : D ⊆ T) (a b : V)
    (h : latStep (DAG.induce G D) U a b) : latStep (DAG.induce G T) U a b := by
  rcases h with ⟨hu, e⟩ | ⟨hu, e⟩
  · obtain ⟨ha, hb, e'⟩ := (show a ∈ D ∧ b ∈ D ∧ G.edge a b from e)
    exact Or.inl ⟨hu, (⟨hDT ha, hDT hb, e'⟩ : a ∈ T ∧ b ∈ T ∧ G.edge a b)⟩
  · obtain ⟨hb, ha, e'⟩ := (show b ∈ D ∧ a ∈ D ∧ G.edge b a from e)
    exact Or.inr ⟨hu, (⟨hDT hb, hDT ha, e'⟩ : b ∈ T ∧ a ∈ T ∧ G.edge b a)⟩

/-- **The block is c-connected in `G`.** Every node of the block `D` (the c-component
of `y` in `G_{X̄}[S]`) is reached from `y` by latent steps inside `G[D]`: by induction
along a latent path in `G_{X̄}[S]`, every node on it lies in `D`, and each step is also a
step of `G[D]`. -/
theorem block_reach (G : DAG V) (U X S : Finset V) (y : V) (hy : y ∈ S) :
    ∀ b ∈ ccIn (cutIn G X) U S {y},
      b ∈ ccomp (DAG.induce G (ccIn (cutIn G X) U S {y})) U y := by
  have hDeq := ccIn_eq (cutIn G X) U S y hy
  have hmem : ∀ c, c ∈ ccIn (cutIn G X) U S {y} ↔
      c ∈ S ∧ c ∈ ccomp (DAG.induce (cutIn G X) S) U y :=
    fun c => by rw [hDeq, Finset.mem_inter]
  have key : ∀ c, Relation.ReflTransGen (latStep (DAG.induce (cutIn G X) S) U) y c →
      c ∈ ccIn (cutIn G X) U S {y} ∧
      Relation.ReflTransGen (latStep (DAG.induce G (ccIn (cutIn G X) U S {y})) U) y c := by
    intro c hc
    induction hc with
    | refl => exact ⟨(hmem y).mpr ⟨hy, self_mem_ccomp _ U y⟩, Relation.ReflTransGen.refl⟩
    | @tail b' c hab hbc ih =>
      have hcD : c ∈ ccIn (cutIn G X) U S {y} := by
        refine (hmem c).mpr ⟨?_, mem_ccomp.mpr (hab.tail hbc)⟩
        rcases hbc with ⟨_, e⟩ | ⟨_, e⟩
        · exact (show b' ∈ S ∧ c ∈ S ∧ (cutIn G X).edge b' c from e).2.1
        · exact (show c ∈ S ∧ b' ∈ S ∧ (cutIn G X).edge c b' from e).1
      refine ⟨hcD, ih.2.tail ?_⟩
      rcases hbc with ⟨hu, e⟩ | ⟨hu, e⟩
      · have e' : G.edge b' c := (show G.edge b' c ∧ c ∉ X from
          (show b' ∈ S ∧ c ∈ S ∧ (cutIn G X).edge b' c from e).2.2).1
        exact Or.inl ⟨hu, (⟨ih.1, hcD, e'⟩ :
          b' ∈ ccIn (cutIn G X) U S {y} ∧ c ∈ ccIn (cutIn G X) U S {y} ∧ G.edge b' c)⟩
      · have e' : G.edge c b' := (show G.edge c b' ∧ b' ∉ X from
          (show c ∈ S ∧ b' ∈ S ∧ (cutIn G X).edge c b' from e).2.2).1
        exact Or.inr ⟨hu, (⟨hcD, ih.1, e'⟩ :
          c ∈ ccIn (cutIn G X) U S {y} ∧ b' ∈ ccIn (cutIn G X) U S {y} ∧ G.edge c b')⟩
  intro b hb
  exact mem_ccomp.mpr (key b (mem_ccomp.mp ((hmem b).mp hb).2)).2

/-- **Where IDENTIFY is stuck, `T` is c-connected** (when the target `D` is): `T` is
the c-closure of `D`, so by induction on the closure steps every node of `T` is reached
from `y` by latent steps inside `T`. -/
theorem stuck_reach (G : DAG V) (U D T : Finset V) (y : V) (hst : Stuck G U D T)
    (hD : ∀ b ∈ D, b ∈ ccomp (DAG.induce G D) U y) :
    ∀ b ∈ T, b ∈ ccomp (DAG.induce G T) U y := by
  obtain ⟨T', _, _, hcc⟩ := hst.cc
  have hAT : ∀ j, j ≤ T'.card → (ccStep G U T')^[j] D ⊆ T := fun j hj v hv => by
    rw [← hcc]
    exact Function.monotone_iterate_of_id_le (f := ccStep G U T')
      (fun _ => Finset.subset_union_left) hj _ hv
  have key : ∀ k, k ≤ T'.card → ∀ b ∈ (ccStep G U T')^[k] D,
      b ∈ ccomp (DAG.induce G T) U y := by
    intro k
    induction k with
    | zero =>
      intro _ b hb
      exact mem_ccomp.mpr (Relation.ReflTransGen.mono (latStep_induce_mono G U D T hst.sub)
        (mem_ccomp.mp (hD b hb)))
    | succ k ih =>
      intro hk b hb
      have hbT := hAT (k + 1) hk hb
      rw [show (ccStep G U T')^[k + 1] D = ccStep G U T' ((ccStep G U T')^[k] D) from
        Function.iterate_succ_apply' _ k _] at hb
      rcases Finset.mem_union.mp hb with h | h
      · exact ih (Nat.le_of_succ_le hk) b h
      · obtain ⟨_, a, ha, hrel⟩ := Finset.mem_filter.mp h
        have haT := hAT k (Nat.le_of_succ_le hk) ha
        have hya := mem_ccomp.mp (ih (Nat.le_of_succ_le hk) a ha)
        refine mem_ccomp.mpr (hya.tail ?_)
        rcases hrel with ⟨hu, e⟩ | ⟨hu, e⟩
        · exact Or.inl ⟨hu, (⟨haT, hbT, e⟩ : a ∈ T ∧ b ∈ T ∧ G.edge a b)⟩
        · exact Or.inr ⟨hu, (⟨hbT, haT, e⟩ : b ∈ T ∧ a ∈ T ∧ G.edge b a)⟩
  intro b hb
  rw [← hcc] at hb
  exact key T'.card le_rfl b hb

/-- **Step H2: if the ID check says no, there is a hedge** (public). With `X` observed,
`F` is the block `D` of some `y ∈ An(Y)` in `G_{X̄}` and `F'` is the set `T` at which
IDENTIFY gets stuck. -/
theorem idCheck_false_hedge (G : DAG V) (U X Y : Finset V) (hXO : X ⊆ Uᶜ)
    (h : idCheck G U X Y = false) : ∃ F F', IsHedge G U X Y F F' := by
  obtain ⟨y, hy, _, hyX, T, hst⟩ := idCheck_false G U X Y h
  obtain ⟨h1, h2, h3, h4, h5⟩ := stuck_hedge_pre G U X Y hXO y hy hyX hst
  have hDr := block_reach G U X (ancIn (cutIn G X) Finset.univ Y) y hy
  exact ⟨_, T, ⟨hst.sub, hst.ne, h1, h2, h3, h4, h5, cconn_of_reach G U _ y hDr,
    cconn_of_reach G U T y (stuck_reach G U _ T y hst hDr)⟩⟩

/-- The bow graph has a hedge for `P(y | do(x))`. -/
theorem bow_hedge : ∃ F F', IsHedge Bow.bowG {0} {1} {2} F F' :=
  idCheck_false_hedge _ _ _ _ (by decide) bow_idCheck

end Hedge
