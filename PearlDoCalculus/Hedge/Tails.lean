import PearlDoCalculus.Hedge.FromID

/-!
# Tails from the roots of a hedge to `Y` (step H4, first part)

Step H3 (`Hedge/Roots.lean`) shows that a hedge blocks identification at its observed
roots. Step H4 carries this to `Y`. Every root of the hedge is an ancestor of `Y` in
`G_{X̄}`, the graph with the edges into `X` cut. This file fixes, for every such ancestor,
one path down to `Y` that avoids `X`: the tail. It also gives the parity bookkeeping
along tails that the product models of H4 need. Nothing here mentions probability.

**Why.** In the product models of H4 the root parity of the hedge is passed down to `Y`.
Each node carries a second bit, and that bit flows along the tail pointer: a node adds
up the second bits of the observed nodes whose tail pointer points to it, as the forest
`nxt` does inside the hedge (`Hedge/Tree.lean`). To see what reaches `Y`, one needs to
know which nodes lie on the tail from a given start, and that each tail ends in exactly
one node of `Y`. The product models (`Hedge/Product`) are built on `AY`, `tp` and `tI`;
`tI_rec` drives the flips along tails there and in `Hedge/ProductBias`, and `sum_tI_Y`
shows that each flip of a root changes the parity on `Y` once. The file needs only
`Hedge/FromID` (for `ancIn_min`), so it is independent of the parity models.

**How.**

1. *A child that stays ancestral.* A node of `ancIn G T C` is in `C` or has a child in
   `ancIn G T C` (`anc_child_in`).
2. *The tail pointer.* `AY` is the set of ancestors of `Y` in `G_{X̄}`. For `v ∈ AY \ Y`,
   `tp v` is a child of `v` in `AY` outside `X` (`tp_spec`); on `Y`, `tp` stays put
   (`tp_Y`). Along `tp` the rank grows (`tp_rank_iter`), so `tp` has no cycles except on
   `Y` (`tp_cycle`). The path stays in `AY` and outside `X` (`tp_iter_mem`,
   `tp_iter_notX`), stays observed when it starts observed (`tp_iter_obs`), and reaches
   `Y` (`tp_reaches`).
3. *Indicators along a tail.* `tI s w` is `1` in `ZMod 2` when `w` lies on the tail from
   `s`. It satisfies `tI s v = [v = s] + Σ tI s w` over the observed `w ∈ AY \ Y` with
   `tp w = v` (`tI_rec`), because a node has at most one predecessor on the tail
   (`tp_pred_aux`). A tail meets `Y` in exactly one node (`sum_tI_Y`).

**Main results.** `anc_child_in`, `tp_spec`, `tp_reaches`, `tI_rec`, `sum_tI_Y`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Identification Identification.CFactor
open IdAlgo

/-! ## The tail pointer `tp`

`anc_child_in`: a node of `ancIn G T C` is in `C` or has a child in `ancIn G T C`. `AY` =
the ancestors of `Y` in `G_{X̄}`. `tp v`: for `v ∈ AY \ Y` a child in `AY` outside `X`
(`tp_spec`); on `Y`, `tp` stands still. Along `tp` the rank grows (`tp_rank_iter`), the
path stays in `AY` and outside `X` (`tp_iter_mem`, `tp_iter_notX`), is observed when the
start is (`tp_iter_obs`), and reaches `Y` (`tp_reaches`). `tI s w`: `w` lies on the `tp`
path from `s`. `tI_rec`: `tI s v = [v = s] + Σ tI s w` over the observed `w ∈ AY \ Y` with
`tp w = v`. `sum_tI_Y`: the path reaches exactly one node of `Y`. -/

namespace Hedge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A node of `ancIn G T C` is in `C` or has a child in `ancIn G T C`. -/
lemma anc_child_in (G : DAG V) (T C : Finset V) (hCT : C ⊆ T) :
    ∀ v ∈ ancIn G T C, v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w := by
  have h := ancIn_min G T C
    ((ancIn G T C).filter (fun v => v ∈ C ∨ ∃ w ∈ ancIn G T C, G.edge v w))
    (fun v hv => Finset.mem_filter.mpr ⟨anc_sup G T C hv, Or.inl hv⟩)
    (fun v hvT hex => by
      obtain ⟨w, hw, e⟩ := hex
      have hwA := (Finset.mem_filter.mp hw).1
      exact Finset.mem_filter.mpr ⟨anc_closed G T C hCT v hvT ⟨w, hwA, e⟩, Or.inr ⟨w, hwA, e⟩⟩)
  intro v hv
  exact (Finset.mem_filter.mp (h hv)).2

section tail

variable (G : DAG V) (X Y : Finset V)

/-- The ancestors of `Y` in `G_{X̄}` (the graph with the edges into `X` cut). -/
def AY : Finset V := ancIn (cutIn G X) Finset.univ Y

open Classical in
/-- The tail pointer: for `v ∈ AY \ Y` a chosen child in `AY` along an edge of `G_{X̄}`
(so the child is not in `X`); `v` itself on `Y` and outside `AY`. -/
noncomputable def tp (v : V) : V :=
  if v ∈ Y then v else
    if h : ∃ w ∈ AY G X Y, (cutIn G X).edge v w then Classical.choose h else v

/-- On `Y`, the tail pointer stands still. -/
lemma tp_Y {v : V} (hv : v ∈ Y) : tp G X Y v = v := by
  unfold tp
  rw [if_pos hv]

/-- For `v ∈ AY \ Y`, `tp v` is a child of `v` in `AY` and outside `X`. -/
lemma tp_spec {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    tp G X Y v ∈ AY G X Y ∧ G.edge v (tp G X Y v) ∧ tp G X Y v ∉ X := by
  have hex : ∃ w ∈ AY G X Y, (cutIn G X).edge v w := by
    rcases anc_child_in (cutIn G X) Finset.univ Y (Finset.subset_univ _) v hv with h | h
    · exact absurd h hvY
    · exact h
  have hdef : tp G X Y v = Classical.choose hex := by
    unfold tp
    rw [if_neg hvY, dif_pos hex]
  rw [hdef]
  obtain ⟨hA, e⟩ := Classical.choose_spec hex
  have e' : G.edge v (Classical.choose hex) ∧ Classical.choose hex ∉ X := e
  exact ⟨hA, e'.1, e'.2⟩

/-- On `Y`, every iterate of the tail pointer stands still. -/
lemma iter_tpY {v : V} (hv : v ∈ Y) : ∀ m, (tp G X Y)^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, tp_Y G X Y hv]

/-- The tail from a node of `AY` stays in `AY`. -/
lemma tp_iter_mem {v : V} (hv : v ∈ AY G X Y) : ∀ n, (tp G X Y)^[n] v ∈ AY G X Y := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y ih hY).1

/-- The tail from a node of `AY` outside `X` stays outside `X`. -/
lemma tp_iter_notX {v : V} (hv : v ∈ AY G X Y) (hvX : v ∉ X) :
    ∀ n, (tp G X Y)^[n] v ∉ X := by
  intro n
  induction n with
  | zero => exact hvX
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · exact (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.2

/-- The tail from an observed node stays observed (latent nodes are roots). -/
lemma tp_iter_obs {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {v : V}
    (hv : v ∈ AY G X Y) (hvU : v ∉ U) : ∀ n, (tp G X Y)^[n] v ∉ U := by
  intro n
  induction n with
  | zero => exact hvU
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hY : (tp G X Y)^[n] v ∈ Y
    · rw [tp_Y G X Y hY]
      exact ih
    · intro hU
      exact hroot _ hU _ (tp_spec G X Y (tp_iter_mem G X Y hv n) hY).2.1

/-- From a node of `AY \ Y`, the rank grows strictly along the tail. -/
lemma tp_rank_iter {v : V} (hv : v ∈ AY G X Y) (hvY : v ∉ Y) :
    ∀ m, G.rank v < G.rank ((tp G X Y)^[m + 1] v) := by
  intro m
  induction m with
  | zero =>
    show G.rank v < G.rank (tp G X Y v)
    exact G.rank_strict_mono _ _ (tp_spec G X Y hv hvY).2.1
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases huY : (tp G X Y)^[m + 1] v ∈ Y
    · rw [tp_Y G X Y huY]
      exact ih
    · exact lt_trans ih
        (G.rank_strict_mono _ _ (tp_spec G X Y (tp_iter_mem G X Y hv (m + 1)) huY).2.1)

/-- If the tail comes back to `v`, then `v ∈ Y`. -/
lemma tp_cycle {v : V} (hv : v ∈ AY G X Y) {m : ℕ} (h : (tp G X Y)^[m + 1] v = v) : v ∈ Y := by
  by_contra hY
  have hlt := tp_rank_iter G X Y hv hY m
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- **The tail reaches `Y`.** By strong induction on the rank gap to the largest rank. -/
theorem tp_reaches : ∀ v ∈ AY G X Y, ∃ n, (tp G X Y)^[n] v ∈ Y := by
  have key : ∀ k, ∀ v ∈ AY G X Y, (Finset.univ : Finset V).sup G.rank - G.rank v = k →
      ∃ n, (tp G X Y)^[n] v ∈ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hk
      by_cases hY : v ∈ Y
      · exact ⟨0, hY⟩
      · obtain ⟨hw, e, -⟩ := tp_spec G X Y hv hY
        have hlt := G.rank_strict_mono v _ e
        have hle : G.rank (tp G X Y v) ≤ (Finset.univ : Finset V).sup G.rank :=
          Finset.le_sup (Finset.mem_univ _)
        obtain ⟨n, hn⟩ := ih ((Finset.univ : Finset V).sup G.rank - G.rank (tp G X Y v))
          (by omega) _ hw rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  exact fun v hv => key _ v hv rfl

open Classical in
/-- The indicator in `ZMod 2` that `w` lies on the tail from `s`. -/
noncomputable def tI (s w : V) : ZMod 2 := if ∃ k, (tp G X Y)^[k] s = w then 1 else 0

/-- A node has at most one predecessor outside `Y` on the tail from `s`. -/
lemma tp_pred_aux {s v w w' : V} (hs : s ∈ AY G X Y) {k k' : ℕ} (hk : k < k')
    (h1 : (tp G X Y)^[k] s = w) (h2 : (tp G X Y)^[k'] s = w')
    (hwv : tp G X Y w = v) (hw'v : tp G X Y w' = v) (hw' : w' ∉ Y) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hv : (tp G X Y)^[k + 1] s = v := by
    rw [Function.iterate_succ_apply', h1, hwv]
  have hw'm : (tp G X Y)^[m] v = w' := by
    rw [← hv, ← Function.iterate_add_apply, ← h2, show m + (k + 1) = k + m + 1 by omega]
  have hvA : v ∈ AY G X Y := by
    rw [← hv]
    exact tp_iter_mem G X Y hs (k + 1)
  have hcyc : (tp G X Y)^[m + 1] v = v := by
    rw [Function.iterate_succ_apply', hw'm, hw'v]
  have hY := tp_cycle G X Y hvA hcyc
  apply hw'
  rw [← hw'm, iter_tpY G X Y hY m]
  exact hY

/-- **The recursion for `tI`**: `v` lies on the tail from `s` iff `v = s` or exactly
one observed `w ∈ AY \ Y` with `tp w = v` does. -/
theorem tI_rec {U : Finset V} (hroot : ∀ u ∈ U, ∀ w, ¬ G.edge w u) {s v : V}
    (hs : s ∈ AY G X Y) (hsU : s ∉ U) :
    tI G X Y s v = (if v = s then 1 else 0) +
      ∑ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v), tI G X Y s w := by
  classical
  have huniq : ∀ w ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      ∀ w' ∈ (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v),
      (∃ k, (tp G X Y)^[k] s = w) → (∃ k, (tp G X Y)^[k] s = w') → w = w' := by
    intro w hw w' hw' h h'
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, -, hw'Y, hw'v⟩ := Finset.mem_filter.mp hw'
    obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := h'
    rcases lt_trichotomy k k' with hl | he | hl
    · exact (tp_pred_aux G X Y hs hl hk hk' hwv hw'v hw'Y).elim
    · subst he
      exact hk.symm.trans hk'
    · exact (tp_pred_aux G X Y hs hl hk' hk hw'v hwv hwY).elim
  by_cases hvs : v = s
  · have hr0 : ∃ k, (tp G X Y)^[k] s = v := ⟨0, hvs.symm⟩
    have h1 : tI G X Y s v = 1 := by
      unfold tI
      rw [if_pos hr0]
    rw [h1, if_pos hvs, Finset.sum_eq_zero, add_zero]
    intro w hw
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    obtain ⟨-, -, hwY, hwv⟩ := Finset.mem_filter.mp hw
    have hcyc : (tp G X Y)^[k + 1] s = s := by
      rw [Function.iterate_succ_apply', hk, hwv, hvs]
    have hY := tp_cycle G X Y hs hcyc
    apply hwY
    rw [← hk, iter_tpY G X Y hY k]
    exact hY
  · rw [if_neg hvs, zero_add]
    by_cases hr : ∃ k, (tp G X Y)^[k] s = v
    · have hex : ∃ k, (tp G X Y)^[k] s = v := hr
      obtain ⟨k, hk⟩ := hr
      have hk0 := Nat.find_spec hex
      have hne0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0] at hk0
        exact hvs hk0.symm
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjv : (tp G X Y)^[j + 1] s = v := by
        rw [← hj]
        exact hk0
      have hwv : tp G X Y ((tp G X Y)^[j] s) = v := by
        have h' := hjv
        rw [Function.iterate_succ_apply'] at h'
        exact h'
      have hwY : (tp G X Y)^[j] s ∉ Y := by
        intro hY
        rw [tp_Y G X Y hY] at hwv
        exact Nat.find_min hex (show j < Nat.find hex by omega) hwv
      have hwmem : (tp G X Y)^[j] s ∈
          (AY G X Y).filter (fun w => w ∉ U ∧ w ∉ Y ∧ tp G X Y w = v) :=
        Finset.mem_filter.mpr ⟨tp_iter_mem G X Y hs j, tp_iter_obs G X Y hroot hs hsU j, hwY, hwv⟩
      have hwr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[j] s := ⟨j, rfl⟩
      unfold tI
      rw [if_pos hex, Finset.sum_eq_single ((tp G X Y)^[j] s)]
      · rw [if_pos hwr]
      · intro b hb hbw
        rw [if_neg]
        intro hbr
        exact hbw (huniq b hb _ hwmem hbr hwr)
      · intro hn
        exact absurd hwmem hn
    · unfold tI
      rw [if_neg hr, Finset.sum_eq_zero]
      intro w hw
      rw [if_neg]
      rintro ⟨k, hk⟩
      obtain ⟨-, -, -, hwv⟩ := Finset.mem_filter.mp hw
      apply hr
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hwv]⟩

/-- **The tail reaches exactly one node of `Y`.** -/
theorem sum_tI_Y {s : V} (hs : s ∈ AY G X Y) : ∑ y ∈ Y, tI G X Y s y = 1 := by
  obtain ⟨n, hn⟩ := tp_reaches G X Y s hs
  have hr : ∃ k, (tp G X Y)^[k] s = (tp G X Y)^[n] s := ⟨n, rfl⟩
  rw [Finset.sum_eq_single ((tp G X Y)^[n] s)]
  · unfold tI
    rw [if_pos hr]
  · intro b hb hbn
    unfold tI
    rw [if_neg]
    rintro ⟨k, hk⟩
    apply hbn
    rcases le_total k n with hl | hl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [add_comm, Function.iterate_add_apply, hk, iter_tpY G X Y hb m]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [← hk, add_comm, Function.iterate_add_apply, iter_tpY G X Y hn m]
  · intro hn'
    exact absurd hn hn'

end tail

end Hedge
