import PearlDoCalculus
open PearlDoCalculus DAG Classical
variable {V : Type} [DecidableEq V] [Fintype V] {G : DAG V}

inductive BallDir where
  | fromChild : BallDir | fromParent : BallDir
  deriving DecidableEq, Repr, Fintype

def outgoingDir (d : BallDir) : ∀ {x y : V}, Walk G x y → BallDir
  | _, _, .nil _   => d
  | _, _, .fwd _ q => outgoingDir .fromParent q
  | _, _, .bwd _ q => outgoingDir .fromChild q

example {a b c : V} (d : BallDir) (e : G.edge a b) (q : Walk G b c) :
    outgoingDir d (Walk.fwd e q) = outgoingDir .fromParent q := by
  simp [outgoingDir]
