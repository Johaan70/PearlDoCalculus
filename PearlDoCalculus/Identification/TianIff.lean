import PearlDoCalculus.Identification.RootTree
import PearlDoCalculus.Identification.CFactor

/-!
# The dividing line for a single `x` (`tian_iff`)

This file is the only bridge between the hedge side (the counter-models of the
non-identifiability results) and the c-factor side (Tian's identification theorem).
When the latent nodes are roots and all variables are `Bool`, the effect of one node `x`
is identifiable if and only if no child of `x` lies in the c-component of `x`. The
direction from right to left is Tian's theorem (`tian_identifiable_ccomp`); the other
direction builds a hedge from a child of `x` in the c-component
(`not_ident_of_child`), using the embedded hedges of `Identification/RootTree`.

Why it is needed: `tian_iff` is one of the public results. It is the single-node case
of the hedge criterion, proved before and independently of `Hedge/*`, and the only file
outside the hedge families that uses their counter-models.

How the proof goes: a child `c` of `x` in the c-component is reached from `x` by latent
steps. A shortest such chain to any child of `x` repeats no node, since a repetition could
be cut out. When the latents are roots, every latent step joins a latent and an observed
node, so the chain alternates: `x ← u₀ → o₀ ← u₁ → ⋯ → o_p`, with `x → o_p`. For `p = 0`
this is the bow; otherwise it is a `RootTree` structure (a latent path, every `o_k` a root),
and the embedded hedge gives non-identifiability. The steps are listed in the section
below.

Main results: `Identification.CFactor.tian_iff` (public) and
`Identification.CFactor.not_ident_of_child`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## The dividing line for one `x` as one theorem

When the latents are roots (Tian's standard setting) and the variables are Boolean,

  `P(O ∖ {x} | do(x))` identifiable  ⟺  no child of `x` in the c-component of `x`
  (`tian_iff`).

`⟸` is Tian's theorem (`Identification/CFactor`). `⟹` is the other half of the bridge
(`not_ident_of_child`): a child `c` of `x` in the c-component gives a hedge.

1. `rtg_chain`: latent steps from `x` to `c` give a chain `f 0 = x, …, f m = c`.
2. Take a shortest chain from `x` to a child of `x` (`Nat.find`). It has no repeated
   nodes: a repetition could be cut out (`chain_cut`), and the chain would be shorter.
3. When the latents are roots, every step alternates between observed and latent
   (`chain_parity`), so the chain is `x ← u₀ → o₀ ← u₁ → o₁ ← ⋯ → o_p` with `x → o_p`.
4. `p = 0` (`m = 2`) is the bow (`bow_not_identifiable_general`). For `p ≥ 1` the chain is
   exactly a `RootTree` structure with a latent path as its tree and every `o_k` a root, and
   the embedded hedges of `Identification/RootTree` (`embedded_not_identifiable`) do the
   rest. -/

namespace Identification
namespace CFactor

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- Steps of a relation from `x` to `v` give a chain indexed by `ℕ`. -/
lemma rtg_chain {r : V → V → Prop} {x v : V} (h : Relation.ReflTransGen r x v) :
    ∃ m : ℕ, ∃ f : ℕ → V, f 0 = x ∧ f m = v ∧ ∀ i < m, r (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨m, f, h0, hm, hs⟩ := ih
    refine ⟨m + 1, fun i => if i ≤ m then f i else c, ?_, ?_, ?_⟩
    · show (if 0 ≤ m then f 0 else c) = x
      rw [if_pos (Nat.zero_le m), h0]
    · show (if m + 1 ≤ m then f (m + 1) else c) = c
      rw [if_neg (show ¬ (m + 1 ≤ m) by omega)]
    · intro i hi
      show r (if i ≤ m then f i else c) (if i + 1 ≤ m then f (i + 1) else c)
      by_cases hlt : i + 1 ≤ m
      · rw [if_pos (show i ≤ m by omega), if_pos hlt]
        exact hs i (by omega)
      · rw [if_pos (show i ≤ m by omega), if_neg hlt, show i = m by omega, hm]
        exact hbc

omit [DecidableEq V] [Fintype V] in
/-- **Cut.** If `f i = f j` with `i < j ≤ m`, there is a chain with the same ends that is
`j - i` shorter. -/
lemma chain_cut {r : V → V → Prop} {m i j : ℕ} {f : ℕ → V}
    (hs : ∀ k < m, r (f k) (f (k + 1))) (hij : i < j) (hjm : j ≤ m) (he : f i = f j) :
    ∃ g : ℕ → V, g 0 = f 0 ∧ g (m - (j - i)) = f m ∧
      ∀ k < m - (j - i), r (g k) (g (k + 1)) := by
  refine ⟨fun k => if k ≤ i then f k else f (k + (j - i)), ?_, ?_, ?_⟩
  · show (if 0 ≤ i then f 0 else f (0 + (j - i))) = f 0
    rw [if_pos (Nat.zero_le i)]
  · show (if m - (j - i) ≤ i then f (m - (j - i)) else f (m - (j - i) + (j - i))) = f m
    by_cases hle : m - (j - i) ≤ i
    · rw [if_pos hle, show m - (j - i) = i by omega, he, show j = m by omega]
    · rw [if_neg hle, show m - (j - i) + (j - i) = m by omega]
  · intro k hk
    show r (if k ≤ i then f k else f (k + (j - i)))
      (if k + 1 ≤ i then f (k + 1) else f (k + 1 + (j - i)))
    by_cases h1 : k + 1 ≤ i
    · rw [if_pos (show k ≤ i by omega), if_pos h1]
      exact hs k (by omega)
    · by_cases h2 : k ≤ i
      · rw [if_pos h2, if_neg h1, show k = i by omega, he,
          show i + 1 + (j - i) = j + 1 by omega]
        exact hs j (by omega)
      · rw [if_neg h2, if_neg h1, show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hs (k + (j - i)) (by omega)

/-- When the latents are roots, a latent step joins a latent and an observed node, along an
edge from the latent one. -/
lemma latStep_edges {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {a b : V} (h : latStep G U a b) :
    (a ∈ U → G.edge a b ∧ b ∉ U) ∧ (b ∈ U → G.edge b a ∧ a ∉ U) := by
  rcases h with ⟨_, e⟩ | ⟨_, e⟩
  · exact ⟨fun _ => ⟨e, fun hb => hroot b hb a e⟩, fun hb => absurd e (hroot b hb a)⟩
  · exact ⟨fun ha => absurd e (hroot a ha b), fun _ => ⟨e, fun ha => hroot a ha b e⟩⟩

/-- **Parity.** If the chain starts at an observed node, exactly the odd positions are
latent. -/
lemma chain_parity {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {f : ℕ → V} {m : ℕ} (hf0 : f 0 ∉ U) (hs : ∀ i < m, latStep G U (f i) (f (i + 1))) :
    ∀ i ≤ m, (f i ∈ U ↔ i % 2 = 1) := by
  intro i
  induction i with
  | zero => intro _; simp [hf0]
  | succ i ih =>
    intro hi
    have h := hs i (by omega)
    have e := latStep_edges hroot h
    have ih' := ih (by omega)
    have hU : f i ∈ U ∨ f (i + 1) ∈ U := by
      rcases h with ⟨ha, _⟩ | ⟨hb, _⟩
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hU with ha | hb
    · have hb := (e.1 ha).2
      have hi1 : i % 2 = 1 := ih'.mp ha
      exact ⟨fun h' => absurd h' hb, fun h' => absurd h' (by omega)⟩
    · have ha := (e.2 hb).2
      have hi0 : i % 2 ≠ 1 := fun h' => ha (ih'.mpr h')
      exact ⟨fun _ => by omega, fun _ => hb⟩

/-- **The other half of the bridge.** If the latents are roots and a child of `x` lies in
the c-component of `x`, then `P(O ∖ {x} | do(x))` is not identifiable. -/
theorem not_ident_of_child {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {x c : V} (hx : x ∉ U) (hcc : c ∈ ccomp G U x) (hxc : G.edge x c) :
    ¬ Identifiable G (fun _ => Bool) Uᶜ {x} (Uᶜ.erase x) := by
  -- 1. A shortest chain from `x` to a child of `x`
  have hex : ∃ m, ∃ f : ℕ → V, f 0 = x ∧ G.edge x (f m) ∧
      ∀ i < m, latStep G U (f i) (f (i + 1)) := by
    obtain ⟨m, f, h0, hm, hs⟩ := rtg_chain (mem_ccomp.mp hcc)
    exact ⟨m, f, h0, by rw [hm]; exact hxc, hs⟩
  have hmin : ∀ k, (∃ g : ℕ → V, g 0 = x ∧ G.edge x (g k) ∧
      ∀ i < k, latStep G U (g i) (g (i + 1))) → Nat.find hex ≤ k :=
    fun k hk => Nat.find_min' hex hk
  obtain ⟨f, hf0, hfm, hs⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  -- 2. No repeated nodes
  have hsimp : ∀ i j, i < j → j ≤ m → f i ≠ f j := by
    intro i j hij hjm he
    obtain ⟨g, hg0, hgm, hgs⟩ := chain_cut hs hij hjm he
    have := hmin (m - (j - i)) ⟨g, hg0.trans hf0, by rw [hgm]; exact hfm, hgs⟩
    omega
  -- 3. Parity and edges
  have hpar := chain_parity hroot (by rw [hf0]; exact hx) hs
  have hfmU : f m ∉ U := fun h => hroot _ h x hfm
  have hmeven : m % 2 = 0 := by
    by_contra h
    exact hfmU ((hpar m le_rfl).mpr (by omega))
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, hf0] at hfm
    exact DAG.not_self_edge G x hfm
  have hU1 : ∀ k, 2 * k + 1 ≤ m → f (2 * k + 1) ∈ U := fun k hk => (hpar _ hk).mpr (by omega)
  have hO2 : ∀ k, 2 * k + 2 ≤ m → f (2 * k + 2) ∉ U := fun k hk h => by
    have := (hpar _ hk).mp h
    omega
  have hE1 : ∀ k, 2 * k + 2 ≤ m → G.edge (f (2 * k + 1)) (f (2 * k + 2)) := fun k hk =>
    ((latStep_edges hroot (hs (2 * k + 1) (by omega))).1 (hU1 k (by omega))).1
  have hE0 : ∀ k, 2 * k + 2 ≤ m → G.edge (f (2 * k + 1)) (f (2 * k)) := fun k hk =>
    ((latStep_edges hroot (hs (2 * k) (by omega))).2 (hU1 k (by omega))).1
  have hx2 : ∀ k, 2 * k + 2 ≤ m → f (2 * k + 2) ≠ x := fun k hk e =>
    hsimp 0 (2 * k + 2) (by omega) hk (hf0.trans e.symm)
  -- 4. The bow or a `RootTree` structure
  intro hid
  have hxO : x ∈ Uᶜ := Finset.mem_compl.mpr hx
  have hd : Disjoint (Uᶜ.erase x) {x} :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase x _)
  by_cases hm2 : m = 2
  · have e0 := hE0 0 (by omega)
    have e1 := hE1 0 (by omega)
    have o2 := hO2 0 (by omega)
    have x2 := hx2 0 (by omega)
    have u1 := hU1 0 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add] at e0 e1 o2 x2 u1
    rw [hf0] at e0
    have hb := BowEmbedded.bow_not_identifiable_general G Uᶜ (f 1) x (f 2) e0 e1
      (by rw [hm2] at hfm; exact hfm) (fun h => (Finset.mem_compl.mp h) u1) hxO
      (Finset.mem_compl.mpr o2)
    apply hb
    refine hid.mono_Y hd ?_
    intro v hv
    rw [Finset.mem_singleton] at hv
    rw [hv]
    exact Finset.mem_erase.mpr ⟨x2, Finset.mem_compl.mpr o2⟩
  · obtain ⟨n, hn⟩ : ∃ n, m = 2 * (n + 2) := ⟨m / 2 - 2, by omega⟩
    let T : RootTree G n :=
      { x := x
        nd := fun k => f (2 * k.val + 2)
        u := fun k => f (2 * k.val + 1)
        bp := fun j => if h : j.val = 0 then none else some ⟨j.val - 1, by have := j.isLt; omega⟩
        ht := fun j => n + 1 - j.val
        dp := fun _ => none
        r := Fin.last (n + 1)
        hbp0 := fun j => by
          by_cases h : j.val = 0
          · have hj : j = 0 := Fin.ext (by simp [h])
            simp [hj]
          · have hj : j ≠ 0 := fun e => h (by simp [e])
            simp [h, hj]
        hht := fun j k hjk => by
          by_cases h : j.val = 0
          · simp [h] at hjk
          · simp only [dif_neg h, Option.some.injEq] at hjk
            subst hjk
            have := j.isLt
            show n + 1 - j.val < n + 1 - (j.val - 1)
            omega
        hr := rfl
        hux := by
          have e := hE0 0 (by omega)
          simp only [Nat.mul_zero, Nat.zero_add] at e
          rw [hf0] at e
          show G.edge (f (2 * (0 : Fin (n + 2)).val + 1)) x
          simpa using e
        hun := fun k => hE1 k.val (by have := k.isLt; omega)
        hub := fun j k hjk => by
          by_cases h : j.val = 0
          · simp [h] at hjk
          · simp only [dif_neg h, Option.some.injEq] at hjk
            subst hjk
            have := j.isLt
            have e := hE0 j.val (by omega)
            show G.edge (f (2 * j.val + 1)) (f (2 * (j.val - 1) + 2))
            rw [show 2 * (j.val - 1) + 2 = 2 * j.val by omega]
            exact e
        hdp := fun j k h => ((Option.some_ne_none k).symm h).elim
        hxr := by
          show G.edge x (f (2 * (Fin.last (n + 1)).val + 2))
          rw [Fin.val_last, show 2 * (n + 1) + 2 = m by omega]
          exact hfm
        ndinj := fun a b hab => by
          have e : f (2 * a.val + 2) = f (2 * b.val + 2) := hab
          have ha := a.isLt
          have hb := b.isLt
          by_contra hne
          have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
          rcases Nat.lt_or_gt_of_ne hv with h | h
          · exact hsimp _ _ (show 2 * a.val + 2 < 2 * b.val + 2 by omega) (by omega) e
          · exact hsimp _ _ (show 2 * b.val + 2 < 2 * a.val + 2 by omega) (by omega) e.symm
        uinj := fun a b hab => by
          have e : f (2 * a.val + 1) = f (2 * b.val + 1) := hab
          have ha := a.isLt
          have hb := b.isLt
          by_contra hne
          have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
          rcases Nat.lt_or_gt_of_ne hv with h | h
          · exact hsimp _ _ (show 2 * a.val + 1 < 2 * b.val + 1 by omega) (by omega) e
          · exact hsimp _ _ (show 2 * b.val + 1 < 2 * a.val + 1 by omega) (by omega) e.symm
        hund := fun j k e => by
          have e' : f (2 * j.val + 1) = f (2 * k.val + 2) := e
          have := j.isLt
          have := k.isLt
          exact hO2 k.val (by omega) (by rw [← e']; exact hU1 j.val (by omega))
        hux' := fun j e => by
          have e' : f (2 * j.val + 1) = x := e
          have := j.isLt
          exact hx (by rw [← e']; exact hU1 j.val (by omega))
        hndx := fun k e => by
          have e' : f (2 * k.val + 2) = x := e
          have := k.isLt
          exact hx2 k.val (by omega) e' }
    refine RootTree.embedded_not_identifiable T Uᶜ (Uᶜ.erase x) ?_ ?_ hxO ?_ hd hid
    · intro j h
      have := j.isLt
      exact (Finset.mem_compl.mp h) (hU1 j.val (by omega))
    · intro k _
      have := k.isLt
      exact Finset.mem_compl.mpr (hO2 k.val (by omega))
    · intro v hv
      obtain ⟨k, -, hkv⟩ := Finset.mem_image.mp hv
      rw [← hkv]
      have := k.isLt
      exact Finset.mem_erase.mpr ⟨hx2 k.val (by omega), Finset.mem_compl.mpr (hO2 k.val (by omega))⟩

/-- **The dividing line for one `x`.** With latent roots and Boolean variables,
`P(O ∖ {x} | do(x))` is identifiable if and only if no child of `x` lies in the
c-component of `x`. -/
theorem tian_iff {G : DAG V} {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u)
    {x : V} (hx : x ∉ U) :
    Identifiable G (fun _ => Bool) Uᶜ {x} (Uᶜ.erase x) ↔ ∀ v ∈ ccomp G U x, ¬ G.edge x v := by
  constructor
  · intro hid v hv hxv
    exact not_ident_of_child hroot hx hv hxv hid
  · intro h
    exact tian_identifiable_ccomp U hx h (Uᶜ.erase x) (Finset.erase_subset x _)

end CFactor
end Identification
