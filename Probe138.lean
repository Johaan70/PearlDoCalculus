import PearlDoCalculus
open PearlDoCalculus DAG Classical

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Retningen ballen reiser. -/
inductive BallDir where
  | fromChild  : BallDir  -- ballen kom fra et barn (reiser oppover)
  | fromParent : BallDir  -- ballen kom fra en forelder (reiser nedover)
  deriving DecidableEq, Repr, Fintype

/-- En balltilstand: hvilken node og hvilken retning. -/
structure BallState (V : Type) where
  node : V
  dir  : BallDir
  deriving DecidableEq

instance [Fintype V] : Fintype (BallState V) :=
  Fintype.ofEquiv (V × BallDir)
    ⟨fun p => ⟨p.1, p.2⟩, fun s => ⟨s.node, s.dir⟩,
     fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- Ett steg i Bayes-Ball-algoritmen.
`anc` er `bbZAncestors Z` — forhåndsberegnet én gang. -/
def bbNext (G : DAG V) (Z anc : Finset V) (s t : BallState V) : Prop :=
  match s.dir with
  | .fromChild =>
    -- Ikke i Z: ballen passerer gjennom
    s.node ∉ Z ∧ (
      (G.edge t.node s.node ∧ t.dir = .fromChild)  ∨  -- opp til forelder
      (G.edge s.node t.node ∧ t.dir = .fromParent)    -- ned til barn
    )
  | .fromParent =>
    -- Ned til barn om ikke i Z
    (s.node ∉ Z ∧ G.edge s.node t.node ∧ t.dir = .fromParent) ∨
    -- Kollider-sprett: opp til forelder om node er forfader av Z
    (s.node ∈ anc ∧ G.edge t.node s.node ∧ t.dir = .fromChild)

instance (G : DAG V) (Z anc : Finset V) :
    DecidableRel (bbNext G Z anc) := by
  intro s t
  unfold bbNext
  cases s.dir <;> simp only [] <;> infer_instance

/-- Bayes-Ball-reachability: transitiv lukning av `bbNext`. -/
def bbReachable (G : DAG V) (Z : Finset V) (s t : BallState V) : Prop :=
  let anc := Finset.univ.filter (fun v => ∃ z ∈ Z, G.Reaches v z)
  Relation.ReflTransGen (bbNext G Z anc) s t

/-- D-separasjon via Bayes-Ball.
`X` og `Y` er d-separert av `Z` om ingen ball som starter i `X`
(i begge retninger) når en node i `Y`. -/
def dSepBB (G : DAG V) (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y,
    ¬ bbReachable G Z ⟨x, .fromChild⟩  ⟨y, .fromChild⟩  ∧
    ¬ bbReachable G Z ⟨x, .fromChild⟩  ⟨y, .fromParent⟩ ∧
    ¬ bbReachable G Z ⟨x, .fromParent⟩ ⟨y, .fromChild⟩  ∧
    ¬ bbReachable G Z ⟨x, .fromParent⟩ ⟨y, .fromParent⟩

/-- Målet: Bayes-Ball-d-separasjon er ekvivalent med vår eksisterende `DSeparated`.
Merk at `DSeparated` tar enkeltvariabler, ikke Finset. -/
theorem dSepBB_iff_DSeparated (G : DAG V) (Z : Finset V) (x y : V) :
    (∀ d1 d2 : BallDir, ¬ bbReachable G Z ⟨x, d1⟩ ⟨y, d2⟩) ↔
    G.DSeparated Z x y := by
  sorry

#check @dSepBB_iff_DSeparated
