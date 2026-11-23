import PearlDoCalculus.Soundness.AncestralReduction
import PearlDoCalculus.Soundness.Separator

/-!
# Bayes-ball reachability gives open walks

The Bayes-ball algorithm decides d-separation by passing a ball between vertices. The
state of the ball is a vertex together with the direction it came from (`BallDir`: from
a child or from a parent), and `bbNext` is one move: a ball that comes from a child
passes on through a vertex outside `Z` to its parents and children; a ball that comes
from a parent passes on to the children if the vertex is outside `Z`, and bounces back
to the parents if the vertex is an ancestor of `Z` (an open collider).

This file proves one direction of the correctness of Bayes-ball: every path of moves
from `x` to `y` traces an open walk from `x` to `y` (`exists_open_walk_of_bbReachable`). So
if `x` and `y` are d-separated given `Z`, the ball cannot get from `x` to `y`
(`not_bbReachable_of_dSeparated`). It connects the walk-based definition of
d-separation (`Blocking.lean`) to the usual algorithmic one.

**Proof.** Induction on the reflexive-transitive closure, from the head: each move
prepends one edge to the open walk built so far, with the direction of the move as the
`Incoming` state of `blockedAux`.

**Main results** (namespace `BayesBall`, opened by `Soundness/Lauritzen` and `Soundness/SetSound`).
`not_blocked_of_bbReachable`, `exists_open_walk_of_bbReachable`,
`not_bbReachable_of_dSeparated`.
-/

open PearlDoCalculus DAG Classical

namespace BayesBall

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The direction a Bayes ball comes from: from a child or from a parent. -/
inductive BallDir where
  | fromChild  : BallDir
  | fromParent : BallDir
  deriving DecidableEq, Repr, Fintype

/-- The state of a Bayes ball: the vertex it is at and the direction it came from. -/
structure BallState (V : Type*) where
  node : V
  dir  : BallDir
  deriving DecidableEq

/-- One move of the Bayes ball, given the conditioning set `Z` and the set `anc` of
ancestors of `Z`. From a child it passes through a vertex outside `Z` to a parent or a
child; from a parent it passes through a vertex outside `Z` to a child, or bounces at an
ancestor of `Z` (an open collider) back to a parent. -/
def bbNext (G : DAG V) (Z anc : Finset V) (s t : BallState V) : Prop :=
  match s.dir with
  | .fromChild =>
    s.node ∉ Z ∧ (
      (G.edge t.node s.node ∧ t.dir = .fromChild) ∨
      (G.edge s.node t.node ∧ t.dir = .fromParent)
    )
  | .fromParent =>
    (s.node ∉ Z ∧ G.edge s.node t.node ∧ t.dir = .fromParent) ∨
    (s.node ∈ anc ∧ G.edge t.node s.node ∧ t.dir = .fromChild)

/-- The ball can get from state `s` to state `t` in finitely many moves. -/
def bbReachable (G : DAG V) (Z : Finset V) (s t : BallState V) : Prop :=
  let anc := Finset.univ.filter (fun v => ∃ z ∈ Z, G.Reaches v z)
  Relation.ReflTransGen (bbNext G Z anc) s t


/-- The `Incoming` state of `blockedAux` that matches the direction of the ball: coming
from a parent is a forward step, coming from a child a backward step. -/
def incomingOfDir : BallDir → DAG.Incoming
  | .fromParent => .fwd
  | .fromChild  => .bwd

/-- A walk with no blocking vertex from any incoming state is open: the start vertex is
not interior, so `blockedAux` from `start` is weaker. -/
lemma open_of_not_blockedAux (G : DAG V) (Z : Finset V) (inc : DAG.Incoming)
    {x y : V} (p : Walk G x y)
    (h : ¬ Walk.blockedAux (G := G) Z inc p) :
    Walk.Open Z p := by
  unfold Walk.Open Walk.Blocked
  cases p with
  | nil v => simp [Walk.blockedAux] at h ⊢
  | fwd e rest =>
    cases inc <;> simp [Walk.blockedAux] at h ⊢ <;> tauto
  | bwd e rest =>
    cases inc <;> simp [Walk.blockedAux] at h ⊢ <;> tauto

/-- If the ball can get from `x` to `y`, there is a walk from `x` to `y` with no blocking
vertex, read with the incoming direction of the first state. This is the core of the
correspondence between Bayes-ball and d-separation. -/
theorem not_blocked_of_bbReachable (G : DAG V) (Z : Finset V) (x y : V)
    (d1 d2 : BallDir)
    (hreach : bbReachable G Z {node := x, dir := d1} {node := y, dir := d2}) :
    exists p : Walk G x y, Not (Walk.blockedAux (G := G) Z (incomingOfDir d1) p) := by
  unfold bbReachable at hreach
  apply Relation.ReflTransGen.head_induction_on
    (motive := fun s _ => exists p : Walk G s.node y,
      Not (Walk.blockedAux (G := G) Z (incomingOfDir s.dir) p))
    hreach
  · exact ⟨Walk.nil _, by cases d2 <;> simp [Walk.blockedAux]⟩
  · intro ⟨c_node, c_dir⟩ _ hstep _ ih
    obtain ⟨p_ih, hp_ih⟩ := ih
    cases c_dir with
    | fromChild =>
      obtain ⟨hxZ, hcase⟩ := hstep
      rcases hcase with ⟨hedge, hdir⟩ | ⟨hedge, hdir⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.bwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.fwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
    | fromParent =>
      rcases hstep with ⟨hxZ, hedge, hdir⟩ | ⟨hxanc, hedge, hdir⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.fwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        simp only [Finset.mem_filter] at hxanc
        obtain ⟨_, z, hzZ, hreach⟩ := hxanc
        exact ⟨Walk.bwd hedge p_ih, by
          simp only [Walk.blockedAux]
          intro h
          rcases h with h1 | h2
          · exact h1 z hzZ hreach
          · exact hp_ih h2⟩

/-- If the ball can get from `x` to `y`, there is an open walk from `x` to `y`. -/
theorem exists_open_walk_of_bbReachable (G : DAG V) (Z : Finset V) (x y : V)
    (d1 d2 : BallDir)
    (hreach : bbReachable G Z {node := x, dir := d1} {node := y, dir := d2}) :
    exists p : Walk G x y, Walk.Open Z p :=
  let ⟨p, hp⟩ := not_blocked_of_bbReachable G Z x y d1 d2 hreach
  ⟨p, open_of_not_blockedAux G Z (incomingOfDir d1) p hp⟩

/-- The corollary: if `x` and `y` are d-separated given `Z`, the ball cannot get from `x`
to `y`, whatever the directions. -/
theorem not_bbReachable_of_dSeparated (G : DAG V) (Z : Finset V) (x y : V)
    (hsep : G.DSeparated Z x y) :
    ∀ d1 d2 : BallDir, ¬ bbReachable G Z ⟨x, d1⟩ ⟨y, d2⟩ := by
  intro d1 d2 hreach
  have ⟨p, hp⟩ := exists_open_walk_of_bbReachable G Z x y d1 d2 hreach
  exact hp (hsep p)

#check @exists_open_walk_of_bbReachable

end BayesBall
