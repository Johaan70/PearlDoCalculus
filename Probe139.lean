import PearlDoCalculus
open PearlDoCalculus DAG Classical

variable {V : Type} [DecidableEq V] [Fintype V]

inductive BallDir where
  | fromChild  : BallDir
  | fromParent : BallDir
  deriving DecidableEq, Repr, Fintype

structure BallState (V : Type) where
  node : V
  dir  : BallDir
  deriving DecidableEq

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

def bbReachable (G : DAG V) (Z : Finset V) (s t : BallState V) : Prop :=
  let anc := Finset.univ.filter (fun v => ∃ z ∈ Z, G.Reaches v z)
  Relation.ReflTransGen (bbNext G Z anc) s t

-- Kontrapositivt: om det finnes en bbReachable-sti, finnes en åpen Walk
-- Dette er kjernen i ekvivalensen
theorem bbReachable_imp_open_walk (G : DAG V) (Z : Finset V) (x y : V)
    (d1 d2 : BallDir)
    (hreach : bbReachable G Z ⟨x, d1⟩ ⟨y, d2⟩) :
    ∃ p : Walk G x y, Walk.Open Z p := by
  sorry

-- Korollaret vi vil ha
theorem DSeparated_imp_not_bbReachable (G : DAG V) (Z : Finset V) (x y : V)
    (hsep : G.DSeparated Z x y) :
    ∀ d1 d2 : BallDir, ¬ bbReachable G Z ⟨x, d1⟩ ⟨y, d2⟩ := by
  intro d1 d2 hreach
  have ⟨p, hp⟩ := bbReachable_imp_open_walk G Z x y d1 d2 hreach
  exact hp (hsep p)

#check @bbReachable_imp_open_walk
