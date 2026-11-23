import PearlDoCalculus.Soundness.DSepSound

/-!
# Walks and paths

`DSeparated` is defined over walks (repeated vertices allowed). The classical definition
uses paths. This file shows that the two are equivalent (`dsepPath_iff_dsep`), and so
lifts `dsep_sound` to the classical path-based hypothesis (`WalkPath.dsep_sound_path`).
It is needed to state d-separation in the form found in the literature; the completeness
side (`Completeness.dsepPath_iff`) uses it too.

**Proof.** The direction walk ⇒ path is trivial, since every path is a walk. The
direction path ⇒ walk is, contrapositively, "open walk ⇒ open path", proved by removing
loops from the head of the walk without losing openness. Given an open walk from `a`,
jump to the last occurrence of `a` (`exists_fromLast`); the start vertex keeps its
incoming edge but gets a new outgoing one, and a case analysis shows that the walk stays
open (`exists_jump`). The one hard case, a new collider at `a`, is settled with
`descend_of_open` and acyclicity: if the walk came into `a` along an arrow and stays open,
it reaches `Z` or comes back to `a` by a directed path, which would be a cycle. Then take
one step and clean the rest, by strong induction on the length (`exists_open_path`).

**Main results.** `DAG.dsepPath_iff_dsep`, `WalkPath.dsep_sound_path`.
-/

namespace PearlDoCalculus
namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

namespace Walk

/-- The start vertex is in the support. -/
lemma start_mem_support {a b : V} (p : Walk G a b) : a ∈ p.support := by
  cases p <;> simp [support]

/-- The end vertex is in the support. -/
lemma end_mem_support {a b : V} (p : Walk G a b) : b ∈ p.support := by
  induction p with
  | nil v => simp [support]
  | fwd e q ih => simp [support, ih]
  | bwd e q ih => simp [support, ih]

/-- A path: no vertex is visited twice. The support contains both the start and the end
vertex (`start_mem_support`, `end_mem_support`), so this is exactly the classical
property of a path. -/
def IsPath {a b : V} (p : Walk G a b) : Prop := p.support.Nodup

end Walk

/-- Classical d-separation: every *path* from `x` to `y` is blocked by `Z`. -/
def DSeparatedPath (G : DAG V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : Walk G x y, p.IsPath → Walk.Blocked Z p

/-- The trivial direction: walk-based d-separation gives path-based d-separation. -/
theorem dsepPath_of_dsep {Z : Finset V} {x y : V} (h : G.DSeparated Z x y) :
    G.DSeparatedPath Z x y :=
  fun p _ => h p

/-- **Descent.** If the walk came into `b` along an arrow (`.fwd`) and is open, then `b`
reaches either a vertex of `Z` or every vertex of the walk. The second alternative is
what makes acyclicity useful: if an earlier vertex turns up again, we get a directed
cycle. -/
lemma descend_of_open {Z : Finset V} : ∀ {b c : V} (q : Walk G b c),
    ¬ Walk.blockedAux Z .fwd q →
    (∃ z ∈ Z, G.Reaches b z) ∨ (∀ v ∈ q.support, G.Reaches b v) := by
  intro b c q
  induction q with
  | nil v =>
    intro _
    right
    intro w hw
    simp [Walk.support] at hw
    subst hw
    exact Reaches.refl G _
  | @fwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push Not at hq
    rcases ih hq.2 with ⟨z, hz, hr⟩ | hall
    · left
      exact ⟨z, hz, Reaches.trans G (Reaches.of_edge G e) hr⟩
    · right
      intro w hw
      simp only [Walk.support, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Reaches.refl G _
      · exact Reaches.trans G (Reaches.of_edge G e) (hall w hw)
  | @bwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push Not at hq
    left
    exact hq.1

/-- If the walk is open, the rest after a `fwd` step is open in state `.fwd`. -/
lemma open_tail_fwd {Z : Finset V} {inc : Incoming} {a a₁ b : V}
    (e : G.edge a a₁) (rest : Walk G a₁ b)
    (h : ¬ Walk.blockedAux Z inc (Walk.fwd e rest)) :
    ¬ Walk.blockedAux Z .fwd rest := by
  intro hr
  apply h
  cases inc <;> simp [Walk.blockedAux, hr]

/-- If the walk is open, the rest after a `bwd` step is open in state `.bwd`. -/
lemma open_tail_bwd {Z : Finset V} {inc : Incoming} {a a₁ b : V}
    (e : G.edge a₁ a) (rest : Walk G a₁ b)
    (h : ¬ Walk.blockedAux Z inc (Walk.bwd e rest)) :
    ¬ Walk.blockedAux Z .bwd rest := by
  intro hr
  apply h
  cases inc <;> simp [Walk.blockedAux, hr]

/-- **Jump to the last occurrence.** For a vertex `x` on an open walk there is a suffix
that starts at the last occurrence of `x`, with the state there. Either the state is
unchanged, or the jump came from an interior position, and `x` lay in the tail of the
original walk. -/
lemma exists_fromLast {Z : Finset V} (x : V) : ∀ {a b : V} (p : Walk G a b)
    (inc : Incoming), x ∈ p.support → ¬ Walk.blockedAux Z inc p →
    ∃ (inc' : Incoming) (q : Walk G x b),
      q.support ⊆ p.support ∧ x ∉ q.support.tail ∧ q.length ≤ p.length ∧
      ¬ Walk.blockedAux Z inc' q ∧
      (inc' = inc ∨ (inc' ≠ .start ∧ x ∈ p.support.tail)) := by
  intro a b p
  induction p with
  | nil v =>
    intro inc hx hp
    simp [Walk.support] at hx
    subst hx
    exact ⟨inc, Walk.nil _, List.Subset.refl _, by simp [Walk.support], le_refl _, hp,
      Or.inl rfl⟩
  | @fwd a a₁ b e rest ih =>
    intro inc hx hp
    have hrest := open_tail_fwd e rest hp
    by_cases hxr : x ∈ rest.support
    · obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ := ih .fwd hxr hrest
      refine ⟨inc', q, ?_, hnot, ?_, hopen, Or.inr ⟨?_, ?_⟩⟩
      · intro w hw
        simp only [Walk.support, List.mem_cons]
        exact Or.inr (hsub hw)
      · simp only [Walk.length]
        omega
      · rcases hcase with rfl | ⟨h, _⟩
        · intro h; cases h
        · exact h
      · simpa [Walk.support] using hxr
    · have hxa : x = a := by
        simp only [Walk.support, List.mem_cons] at hx
        rcases hx with h | h
        · exact h
        · exact absurd h hxr
      subst hxa
      exact ⟨inc, Walk.fwd e rest, List.Subset.refl _, by simpa [Walk.support] using hxr,
        le_refl _, hp, Or.inl rfl⟩
  | @bwd a a₁ b e rest ih =>
    intro inc hx hp
    have hrest := open_tail_bwd e rest hp
    by_cases hxr : x ∈ rest.support
    · obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ := ih .bwd hxr hrest
      refine ⟨inc', q, ?_, hnot, ?_, hopen, Or.inr ⟨?_, ?_⟩⟩
      · intro w hw
        simp only [Walk.support, List.mem_cons]
        exact Or.inr (hsub hw)
      · simp only [Walk.length]
        omega
      · rcases hcase with rfl | ⟨h, _⟩
        · intro h; cases h
        · exact h
      · simpa [Walk.support] using hxr
    · have hxa : x = a := by
        simp only [Walk.support, List.mem_cons] at hx
        rcases hx with h | h
        · exact h
        · exact absurd h hxr
      subst hxa
      exact ⟨inc, Walk.bwd e rest, List.Subset.refl _, by simpa [Walk.support] using hxr,
        le_refl _, hp, Or.inl rfl⟩

/-- **The jump keeps the walk open.** From an open walk there is a suffix from the last
occurrence of the start vertex that is open in the *original* state. The start vertex
keeps its incoming edge but gets a new outgoing edge; the case analysis shows that the
walk stays open. A new collider at `a` is handled with `descend_of_open` and
acyclicity. -/
lemma exists_jump {Z : Finset V} (inc : Incoming) {a b : V} (p : Walk G a b)
    (hp : ¬ Walk.blockedAux Z inc p) :
    ∃ q : Walk G a b, q.support ⊆ p.support ∧ a ∉ q.support.tail ∧
      q.length ≤ p.length ∧ ¬ Walk.blockedAux Z inc q := by
  obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ :=
    exists_fromLast a p inc (Walk.start_mem_support p) hp
  refine ⟨q, hsub, hnot, hlen, ?_⟩
  rcases hcase with rfl | ⟨hstart, ha⟩
  · exact hopen
  · cases q with
    | nil => simp [Walk.blockedAux]
    | fwd e' r =>
      have hr := open_tail_fwd e' r hopen
      have haZ : a ∉ Z := by
        intro haZ
        apply hopen
        cases inc' with
        | start => exact absurd rfl hstart
        | fwd => simp [Walk.blockedAux, haZ]
        | bwd => simp [Walk.blockedAux, haZ]
      cases inc <;> simp [Walk.blockedAux, haZ, hr]
    | bwd e' r =>
      have hr := open_tail_bwd e' r hopen
      cases inc with
      | start => simp [Walk.blockedAux, hr]
      | bwd =>
        have haZ : a ∉ Z := by
          cases p with
          | nil => simp [Walk.support] at ha
          | fwd e rest => intro haZ; apply hp; simp [Walk.blockedAux, haZ]
          | bwd e rest => intro haZ; apply hp; simp [Walk.blockedAux, haZ]
        simp [Walk.blockedAux, haZ, hr]
      | fwd =>
        have hz : ∃ z ∈ Z, G.Reaches a z := by
          cases p with
          | nil => simp [Walk.support] at ha
          | @fwd _ a₁ _ e rest =>
            have hrest := open_tail_fwd e rest hp
            have ha' : a ∈ rest.support := by simpa [Walk.support] using ha
            rcases descend_of_open rest hrest with ⟨z, hz, hreach⟩ | hall
            · exact ⟨z, hz, Reaches.trans G (Reaches.of_edge G e) hreach⟩
            · exfalso
              have h1 := G.rank_strict_mono _ _ e
              have h2 := G.rank_le_of_reaches (hall a ha')
              omega
          | bwd e rest =>
            by_contra hno
            apply hp
            simp only [Walk.blockedAux]
            left
            intro z hz hreach
            exact hno ⟨z, hz, hreach⟩
        intro hb
        simp only [Walk.blockedAux] at hb
        rcases hb with hb | hb
        · obtain ⟨z, hz', hreach⟩ := hz
          exact hb z hz' hreach
        · exact hr hb

/-- **Loop removal.** From an open walk there is an open path with the same endpoints,
the same incoming state, and support inside the original one. Strong induction on the
length: jump to the last occurrence of the start vertex (`exists_jump`), take one step,
and clean the rest recursively. -/
lemma exists_open_path {Z : Finset V} : ∀ (n : ℕ) {a b : V} (p : Walk G a b),
    p.length ≤ n → ∀ inc : Incoming, ¬ Walk.blockedAux Z inc p →
    ∃ q : Walk G a b, q.IsPath ∧ q.support ⊆ p.support ∧ ¬ Walk.blockedAux Z inc q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p hlen inc hp
    obtain ⟨q, hsub, hnot, hqlen, hq⟩ := exists_jump inc p hp
    cases q with
    | nil =>
      exact ⟨Walk.nil _, by simp [Walk.IsPath, Walk.support], hsub, hq⟩
    | @fwd _ a₁ _ e r =>
      have hr := open_tail_fwd e r hq
      have hrlen : r.length < n := by
        simp only [Walk.length] at hqlen
        omega
      obtain ⟨r', hr'path, hr'sub, hr'open⟩ := ih r.length hrlen r le_rfl .fwd hr
      refine ⟨Walk.fwd e r', ?_, ?_, ?_⟩
      · simp only [Walk.IsPath, Walk.support, List.nodup_cons]
        refine ⟨fun ha => hnot ?_, hr'path⟩
        simp only [Walk.support, List.tail_cons]
        exact hr'sub ha
      · intro w hw
        simp only [Walk.support, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Walk.start_mem_support p
        · exact hsub (by simp only [Walk.support, List.mem_cons]; exact Or.inr (hr'sub hw))
      · cases inc <;> simp only [Walk.blockedAux] at hq ⊢ <;>
          first
          | exact hr'open
          | exact fun h => h.elim (fun h1 => hq (Or.inl h1)) hr'open
    | @bwd _ a₁ _ e r =>
      have hr := open_tail_bwd e r hq
      have hrlen : r.length < n := by
        simp only [Walk.length] at hqlen
        omega
      obtain ⟨r', hr'path, hr'sub, hr'open⟩ := ih r.length hrlen r le_rfl .bwd hr
      refine ⟨Walk.bwd e r', ?_, ?_, ?_⟩
      · simp only [Walk.IsPath, Walk.support, List.nodup_cons]
        refine ⟨fun ha => hnot ?_, hr'path⟩
        simp only [Walk.support, List.tail_cons]
        exact hr'sub ha
      · intro w hw
        simp only [Walk.support, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Walk.start_mem_support p
        · exact hsub (by simp only [Walk.support, List.mem_cons]; exact Or.inr (hr'sub hw))
      · cases inc <;> simp only [Walk.blockedAux] at hq ⊢ <;>
          first
          | exact hr'open
          | exact fun h => h.elim (fun h1 => hq (Or.inl h1)) hr'open

/-- The main result: path-based d-separation gives walk-based d-separation.
Contrapositively: from an open walk there is an open path. -/
theorem dsep_of_dsepPath {Z : Finset V} {x y : V} (h : G.DSeparatedPath Z x y) :
    G.DSeparated Z x y := by
  intro p
  by_contra hp
  obtain ⟨q, hq, _, hqo⟩ := exists_open_path p.length p le_rfl .start hp
  exact hqo (h q hq)

/-- Walk-based and path-based d-separation are equivalent. -/
theorem dsepPath_iff_dsep {Z : Finset V} {x y : V} :
    G.DSeparatedPath Z x y ↔ G.DSeparated Z x y :=
  ⟨dsep_of_dsepPath, dsepPath_of_dsep⟩

end DAG
end PearlDoCalculus

namespace WalkPath

open PearlDoCalculus DAG

/-- **Classical soundness.** Path-based d-separation gives conditional independence. -/
theorem dsep_sound_path {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}
    {α : V → Type*} (M : G.CausalModel α) (Z : Finset V) (x y : V)
    (h : G.DSeparatedPath Z x y) : M.CondIndep {x} {y} Z :=
  DSepSound.dsep_sound M Z x y (dsep_of_dsepPath h)

end WalkPath

#print axioms PearlDoCalculus.DAG.Walk.start_mem_support
#print axioms PearlDoCalculus.DAG.Walk.end_mem_support
#print axioms PearlDoCalculus.DAG.dsepPath_of_dsep
#print axioms PearlDoCalculus.DAG.descend_of_open
#print axioms PearlDoCalculus.DAG.exists_fromLast
#print axioms PearlDoCalculus.DAG.exists_jump
#print axioms PearlDoCalculus.DAG.exists_open_path
#print axioms PearlDoCalculus.DAG.dsep_of_dsepPath
#print axioms PearlDoCalculus.DAG.dsepPath_iff_dsep
#print axioms WalkPath.dsep_sound_path
