import PearlDoCalculus.BayesBall

/-!
# Lauritzen's theorem via Bayes-Ball

Corrected form of `moral_sep_of_dsep` (which is false as stated, see
`Counterexample.lean`): take `A = ancestors G ({x, y} ∪ Z)`.

Proof: contrapositive. A moral walk from `x` to `y` avoiding `Z` lets the
Bayes ball travel from `⟨x, fromChild⟩` to `y`, giving an open walk.
-/

open PearlDoCalculus DAG Classical

namespace Lauritzen

variable {V : Type} [DecidableEq V] [Fintype V] {G : DAG V} {Z : Finset V}

/-- `v` is not an ancestor of any element of `Z`. -/
def NotZAnc (G : DAG V) (Z : Finset V) (v : V) : Prop :=
  ¬ ∃ z ∈ Z, G.Reaches v z

/-- The ball starting at `⟨x, fromChild⟩` can reach `v` in some direction. -/
def Reach (G : DAG V) (Z : Finset V) (x v : V) : Prop :=
  ∃ d : BallDir, bbReachable G Z ⟨x, .fromChild⟩ ⟨v, d⟩

/-- H1: a non-ancestor of `Z` is not in `Z` (by `Reaches.refl`). -/
lemma not_mem_of_notZAnc {v : V} (h : NotZAnc G Z v) : v ∉ Z := by
  sorry

/-- L1: going up. If `v →* x` and `v` is not an ancestor of `Z`, the ball
    reaches `⟨v, fromChild⟩` from `⟨x, fromChild⟩`. -/
lemma up_path {x v : V} (hx : x ∉ Z) (hr : G.Reaches v x) (hv : NotZAnc G Z v) :
    bbReachable G Z ⟨x, .fromChild⟩ ⟨v, .fromChild⟩ := by
  sorry

/-- L2: going down. If the ball reaches `v`, and `v →* y` with `v` not an
    ancestor of `Z`, the ball reaches `y`. -/
lemma down_path {s : BallState V} {v y : V} {d : BallDir}
    (hr : G.Reaches v y) (hv : NotZAnc G Z v)
    (hs : bbReachable G Z s ⟨v, d⟩) : ∃ d', bbReachable G Z s ⟨y, d'⟩ := by
  sorry

/-- L3: one step along a moral edge inside `A = ancestors({x, y} ∪ Z)`. -/
lemma moral_step {x y v w : V} (hx : x ∉ Z) (hv : v ∉ Z) (hw : w ∉ Z)
    (hadj : (moralGraph G (ancestors G (insert x (insert y Z)))).Adj v w)
    (hreach : Reach G Z x v) : Reach G Z x w ∨ Reach G Z x y := by
  sorry

/-- L4: induction along a walk in any graph `H` satisfying the step property.
    The graph is kept separate from the walk's endpoint `t`, so induction can
    generalise `t` without changing `H`. -/
lemma walk_reach {x y : V} {H : SimpleGraph V}
    (hstep : ∀ {v w : V}, v ∉ Z → w ∉ Z → H.Adj v w →
      Reach G Z x v → Reach G Z x w ∨ Reach G Z x y) :
    ∀ {v t : V} (p : H.Walk v t), (∀ u ∈ p.support, u ∉ Z) →
      Reach G Z x v → Reach G Z x t ∨ Reach G Z x y := by
  intro v t p
  induction p with
  | nil => intro _ h; exact Or.inl h
  | cons hadj rest ih =>
    intro hsupp hreach
    rcases hstep (hsupp _ (by simp)) (hsupp _ (by simp)) hadj hreach with h | h
    · exact ih (fun u hu => hsupp u (by simp [hu])) h
    · exact Or.inr h

/-- L5 (main): Lauritzen's theorem, the corrected `moral_sep_of_dsep`. -/
theorem moral_sep_of_dsep_lauritzen (x y : V) (hdsep : G.DSeparated Z x y) :
    Separates (moralGraph G (ancestors G (insert x (insert y Z)))) Z x y := by
  intro p
  by_contra hno
  have hsupp : ∀ u ∈ p.support, u ∉ Z := fun u hu huZ => hno ⟨u, huZ, hu⟩
  have hx : x ∉ Z := hsupp x (SimpleGraph.Walk.start_mem_support p)
  obtain ⟨d, hd⟩ := (walk_reach (fun hv hw hadj hr => moral_step hx hv hw hadj hr)
    p hsupp ⟨.fromChild, Relation.ReflTransGen.refl⟩).elim id id
  exact DSeparated_imp_not_bbReachable G Z x y hdsep .fromChild d hd

end Lauritzen

#print axioms Lauritzen.moral_sep_of_dsep_lauritzen
