import PearlDoCalculus.Identification.Bow

/-!
# Hedge chains of any length are not identifiable

A chain `x ↔ w₀ ↔ w₁ ↔ … ↔ w_n ↔ y` of confounded nodes, with latent variables
`u₀, …, u_{n+1}` and the edge `x → y`, has `P(y | do(x))` not identifiable from the
observed nodes (`Identification.HedgeChain.chain_not_identifiable`), whether or not the
`w_i` are observed. For `n = 0` this is the hedge with two latent variables.

Why it is needed: this is the first hedge family of unbounded size, and the pattern for
the later ones: `HedgeTemplate` generalizes the chain to any shape of the `w`s, and
`LatentTree`, `RootPathModels` and `RootPath` follow the same plan. The helpers `ev` (the
value of a full assignment at a node), `xx`, `xb` and `chan_symm` are reused by those
files. The theorem itself is a special case of the hedge criterion (`Hedge/*`) and has
no users.

How the proof goes: two models with the same positive distribution on the observed
nodes and different `P(y | do(x))`, related by a bijection `φ` that changes only latent
nodes. In model A, `y` is a function of the latent variables alone, so `do(x)` does not
change it; in model B, `y` is a noisy copy of `x`. Model B gives `φ s` the probability
that model A gives `s`, because the defining equations of the two models are equivalent
(`condA_iff`, by induction along the chain). The end of the proof is the same as for the
bow: positivity, `P(y | do(x))` in model A, and the front-door step in model B. The two
models are described in the first section below.

Main result: `Identification.HedgeChain.chain_not_identifiable`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

/-! ## The chain and its two models

Latent `u₀, …, u_{n+1}` and nodes `w₀, …, w_n` form the chain
`x ↔ w₀ ↔ w₁ ↔ … ↔ w_n ↔ y`: `u₀ → x`, `u_i → w_i`, `u_{i+1} → w_i`,
`w_i → w_{i+1}`, `w_n → y`, `u_{n+1} → y`, and `x → y`. Then `P(y | do(x))` is not
identifiable, whether the `w`s are observed or not.

Model A: the `u`s uniform, `x` a noisy copy of `u₀`,
`w₀ = u₀ xor u₁`, `w_{i+1} = w_i xor u_{i+1} xor u_{i+2}`, `y = w_n xor u_{n+1}`.
By induction `w_i = u₀ xor u_{i+1}` and `y = u₀`, so `y` is not affected by `x`.
Model B: all `u = 0`, `x` and the `w`s uniform, `y` a noisy copy of `x`.
The bijection `u₀ ↦ u₀ xor y`, `u_{i+1} ↦ u_{i+1} xor w_i xor y` carries one joint
distribution to the other; the two systems of equations are equivalent
(`condA_iff`, proved by induction along the chain). -/

namespace Identification
namespace HedgeChain

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Boolean algebra along the chain -/

/-- Solving `r = p xor q` for `q`. -/
lemma bx2 {p q r : Bool} (h : r = xor p q) : q = xor r p := by
  rw [h]; cases p <;> cases q <;> rfl
/-- One induction step along the chain: from `q = p xor t` and `r = p xor q xor s`, get `s = r
xor t`. -/
lemma bx3 {p q r s t : Bool} (h1 : q = xor p t) (h2 : r = xor p (xor q s)) :
    s = xor r t := by
  rw [h2, h1]; cases p <;> cases s <;> cases t <;> rfl
/-- The end of the chain: from `c = p xor q` and `q = p xor t`, get `t = c`. -/
lemma bx4 {p q c t : Bool} (h1 : c = xor p q) (h2 : q = xor p t) : t = c := by
  rw [h1, h2]; cases p <;> cases t <;> rfl
/-- The first equation of model A, recovered from the equations of model B. -/
lemma bx5 {a0 a1 b0 c : Bool} (h0 : a0 = c) (h1 : a1 = xor b0 c) : b0 = xor a0 a1 := by
  rw [h0, h1]; cases b0 <;> cases c <;> rfl
/-- An inner equation of model A, recovered from the equations of model B. -/
lemma bx6 {bi bj A B c : Bool} (hA : A = xor bi c) (hB : B = xor bj c) :
    bj = xor bi (xor A B) := by
  rw [hA, hB]; cases bi <;> cases bj <;> cases c <;> rfl
/-- The last equation of model A, recovered from the equations of model B. -/
lemma bx7 {bl al c : Bool} (h : al = xor bl c) : c = xor bl al := by
  rw [h]; cases bl <;> cases c <;> rfl
/-- Adding the same bit twice changes nothing. -/
lemma xx (a k : Bool) : xor (xor a k) k = a := by cases a <;> cases k <;> rfl
/-- If `a xor k = false`, then `a = k`. -/
lemma xb (a k : Bool) (h : xor a k = false) : a = k := by
  cases a <;> cases k <;> simp_all

/-- The shift in the bijection: `0` for `u₀`, `w_i` for `u_{i+1}`. -/
def offB {n : ℕ} (b : Fin (n + 1) → Bool) (j : Fin (n + 2)) : Bool :=
  Fin.cases (motive := fun _ => Bool) false b j

/-- The shift of `u₀` is `false`. -/
lemma offB_zero {n : ℕ} (b : Fin (n + 1) → Bool) : offB b 0 = false := by simp [offB]
/-- The shift of `u_{i+1}` is `w_i`. -/
lemma offB_succ {n : ℕ} (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    offB b i.succ = b i := by simp [offB]

/-- The equations of model A: `w₀ = u₀ xor u₁`, `w_{i+1} = w_i xor u_{i+1} xor u_{i+2}` and
`y = w_n xor u_{n+1}` (with `a` the values of the `u`s, `b` those of the `w`s, `c` that of
`y`). -/
abbrev condA {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) : Prop :=
  b 0 = xor (a 0) (a (Fin.succ 0)) ∧
  (∀ i : Fin n, b i.succ = xor (b i.castSucc) (xor (a i.succ.castSucc) (a i.succ.succ))) ∧
  c = xor (b (Fin.last n)) (a (Fin.last (n + 1)))

/-- The equations of model B after the bijection: `u_j = shift_j xor y` for every `j`. -/
abbrev condB {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) : Prop :=
  ∀ j, a j = xor (offB b j) c

/-- The equations of the `w`s in model A give `u_{i+1} = w_i xor u₀` for every `i`, by induction
along the chain. -/
lemma chain_aux {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool)
    (h1 : b 0 = xor (a 0) (a (Fin.succ 0)))
    (h2 : ∀ i : Fin n, b i.succ = xor (b i.castSucc) (xor (a i.succ.castSucc) (a i.succ.succ))) :
    ∀ i : Fin (n + 1), a i.succ = xor (b i) (a 0) := by
  intro i
  induction i using Fin.induction with
  | zero => exact bx2 h1
  | succ i ih =>
    have ee : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    have e : a i.succ.castSucc = xor (b i.castSucc) (a 0) := by rw [ee]; exact ih
    exact bx3 e (h2 i)

/-- **The two systems of equations are equivalent**, by induction along the chain. -/
lemma condA_iff {n : ℕ} (a : Fin (n + 2) → Bool) (b : Fin (n + 1) → Bool) (c : Bool) :
    condA a b c ↔ condB a b c := by
  have eel : Fin.last (n + 1) = (Fin.last n).succ := Fin.ext rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have aux := chain_aux a b h1 h2
    have hl : a (Fin.last (n + 1)) = xor (b (Fin.last n)) (a 0) := by rw [eel]; exact aux _
    have hc : a 0 = c := bx4 h3 hl
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [offB_zero]; simpa using hc
    · rw [offB_succ, aux i, hc]
  · intro h
    have h0 : a 0 = c := by simpa [offB_zero] using h 0
    have hs : ∀ i : Fin (n + 1), a i.succ = xor (b i) c := by
      intro i
      have := h i.succ
      rwa [offB_succ] at this
    refine ⟨bx5 h0 (hs 0), fun i => bx6 ?_ (hs i.succ), bx7 ?_⟩
    · have ee : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [ee]; exact hs i.castSucc
    · rw [eel]; exact hs _

/-- The noisy channel is symmetric in its input and output. -/
lemma chan_symm (a b : Bool) : Bow.chan a b = Bow.chan b a := by
  rw [Bow.chan_apply, Bow.chan_apply]
  cases a <;> cases b <;> rfl

/-- The value of a full assignment at a node. -/
def ev (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V) : Bool :=
  s ⟨v, Finset.mem_univ v⟩

/-! ### The chain inside `G` -/

/-- A hedge chain in `G` with `n + 1` inner nodes: the nodes `x`, `y`, `w₀, …, w_n` and the
latent `u₀, …, u_{n+1}`, the edges of the chain together with `x → y`, and the facts that
all these nodes are different. -/
structure Chain (G : DAG V) (n : ℕ) where
  x : V
  y : V
  w : Fin (n + 1) → V
  u : Fin (n + 2) → V
  hux : G.edge (u 0) x
  huw1 : ∀ i, G.edge (u i.castSucc) (w i)
  huw2 : ∀ i, G.edge (u i.succ) (w i)
  hww : ∀ i : Fin n, G.edge (w i.castSucc) (w i.succ)
  hwy : G.edge (w (Fin.last n)) y
  huy : G.edge (u (Fin.last (n + 1))) y
  hxy : G.edge x y
  winj : Function.Injective w
  uinj : Function.Injective u
  huw : ∀ j i, u j ≠ w i
  hux' : ∀ j, u j ≠ x
  huy' : ∀ j, u j ≠ y
  hwx : ∀ i, w i ≠ x
  hwy' : ∀ i, w i ≠ y

namespace Chain

variable {G : DAG V} {n : ℕ} (H : Chain G n)

/-- `x` and `y` are different. -/
lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy

/-- The graph of model A: the edges of the chain, without `x → y`. -/
noncomputable def gA : DAG V where
  edge s t := (s = H.u 0 ∧ t = H.x) ∨ (∃ i, s = H.u i.castSucc ∧ t = H.w i) ∨
    (∃ i, s = H.u i.succ ∧ t = H.w i) ∨ (∃ i : Fin n, s = H.w i.castSucc ∧ t = H.w i.succ) ∨
    (s = H.w (Fin.last n) ∧ t = H.y) ∨ (s = H.u (Fin.last (n + 1)) ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> apply G.rank_strict_mono <;>
      first | exact H.hux | exact H.huw1 _ | exact H.huw2 _ | exact H.hww _ | exact H.hwy | exact H.huy

/-- The edges of the graph of model A. -/
lemma gA_edge (s t : V) : H.gA.edge s t ↔ ((s = H.u 0 ∧ t = H.x) ∨
    (∃ i, s = H.u i.castSucc ∧ t = H.w i) ∨ (∃ i, s = H.u i.succ ∧ t = H.w i) ∨
    (∃ i : Fin n, s = H.w i.castSucc ∧ t = H.w i.succ) ∨
    (s = H.w (Fin.last n) ∧ t = H.y) ∨ (s = H.u (Fin.last (n + 1)) ∧ t = H.y)) := Iff.rfl

/-- `u₀` is a parent of `x` in the graph of model A. -/
lemma pA_x : H.u 0 ∈ H.gA.parents H.x :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inl ⟨rfl, rfl⟩))
/-- `u_i` is a parent of `w_i` in the graph of model A. -/
lemma pA_w1 (i : Fin (n + 1)) : H.u i.castSucc ∈ H.gA.parents (H.w i) :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))
/-- `u_{i+1}` is a parent of `w_i` in the graph of model A. -/
lemma pA_w2 (i : Fin (n + 1)) : H.u i.succ ∈ H.gA.parents (H.w i) :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))))
/-- `w_i` is a parent of `w_{i+1}` in the graph of model A. -/
lemma pA_ww (i : Fin n) : H.w i.castSucc ∈ H.gA.parents (H.w i.succ) :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))))
/-- `w_n` is a parent of `y` in the graph of model A. -/
lemma pA_yw : H.w (Fin.last n) ∈ H.gA.parents H.y :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
/-- `u_{n+1}` is a parent of `y` in the graph of model A. -/
lemma pA_yu : H.u (Fin.last (n + 1)) ∈ H.gA.parents H.y :=
  DAG.mem_parents.mpr ((H.gA_edge _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
/-- `u₀` is a parent of `w₀` in the graph of model A. -/
lemma pA_w0 : H.u 0 ∈ H.gA.parents (H.w 0) := by simpa using H.pA_w1 0

/-- Transport a parent along an equality of children. -/
lemma mem_cast {a b c : V} (e : b = c) (h : a ∈ H.gA.parents b) : a ∈ H.gA.parents c := by
  rw [← e]; exact h

/-- The kernel of `w_j` in model A: `w₀ = u₀ xor u₁`, `w_{i+1} = w_i xor u_{i+1} xor u_{i+2}`. -/
noncomputable def kw (j : Fin (n + 1)) : ({v // v ∈ H.gA.parents (H.w j)} → Bool) → PMF Bool :=
  Fin.cases (motive := fun j : Fin (n + 1) => ({v // v ∈ H.gA.parents (H.w j)} → Bool) → PMF Bool)
    (fun pa => PMF.pure (xor (pa ⟨H.u 0, H.pA_w0⟩) (pa ⟨H.u (Fin.succ 0), H.pA_w2 0⟩)))
    (fun i pa => PMF.pure (xor (pa ⟨H.w i.castSucc, H.pA_ww i⟩)
      (xor (pa ⟨H.u i.succ.castSucc, H.pA_w1 i.succ⟩) (pa ⟨H.u i.succ.succ, H.pA_w2 i.succ⟩)))) j

/-- The kernel of `w₀` in model A. -/
lemma kw_zero (pa : {v // v ∈ H.gA.parents (H.w 0)} → Bool) :
    H.kw 0 pa = PMF.pure (xor (pa ⟨H.u 0, H.pA_w0⟩) (pa ⟨H.u (Fin.succ 0), H.pA_w2 0⟩)) := by
  rfl

/-- The kernel of `w_{i+1}` in model A. -/
lemma kw_succ (i : Fin n) (pa : {v // v ∈ H.gA.parents (H.w i.succ)} → Bool) :
    H.kw i.succ pa = PMF.pure (xor (pa ⟨H.w i.castSucc, H.pA_ww i⟩)
      (xor (pa ⟨H.u i.succ.castSucc, H.pA_w1 i.succ⟩) (pa ⟨H.u i.succ.succ, H.pA_w2 i.succ⟩))) := by
  rfl

/-- Model A: `x` a noisy copy of `u₀`, the `w`s and `y` given by the equations `condA`, every
other node uniform. -/
noncomputable def NA : H.gA.CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u 0, by rw [hvx]; exact H.pA_x⟩)
    else if hvy : v = H.y then
      PMF.pure (xor (pa ⟨H.w (Fin.last n), by rw [hvy]; exact H.pA_yw⟩)
        (pa ⟨H.u (Fin.last (n + 1)), by rw [hvy]; exact H.pA_yu⟩))
    else if h : ∃ j, H.w j = v then
      H.kw (Classical.choose h)
        (fun p => pa ⟨p.1, H.mem_cast (Classical.choose_spec h) p.2⟩)
    else PMF.uniformOfFintype Bool

/-- Model B, on the graph with only `x → y`: `y` a noisy copy of `x`, the `u`s fixed to `false`,
every other node uniform. -/
noncomputable def NB : (BowGen.g1 G H.x H.y H.hxy).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then Bow.chan (pa ⟨H.x, by rw [hvy]; exact BowGen.p1 G H.x H.y H.hxy⟩)
    else if ∃ j, H.u j = v then PMF.pure false
    else PMF.uniformOfFintype Bool

/-- The kernel of `x` in model A. -/
lemma NA_x (pa : {v // v ∈ H.gA.parents H.x} → Bool) :
    H.NA.kernel H.x pa = Bow.chan (pa ⟨H.u 0, H.pA_x⟩) := by
  simp [NA]

/-- The kernel of `y` in model A. -/
lemma NA_y (pa : {v // v ∈ H.gA.parents H.y} → Bool) :
    H.NA.kernel H.y pa = PMF.pure (xor (pa ⟨H.w (Fin.last n), H.pA_yw⟩)
      (pa ⟨H.u (Fin.last (n + 1)), H.pA_yu⟩)) := by
  simp [NA, H.dxy.symm]

/-- The kernel of `w_j` in model A. -/
lemma NA_w (j : Fin (n + 1)) (pa : {v // v ∈ H.gA.parents (H.w j)} → Bool) :
    H.NA.kernel (H.w j) pa = H.kw j pa := by
  have h : ∃ j', H.w j' = H.w j := ⟨j, rfl⟩
  have key : ∀ (j' : Fin (n + 1)) (e : H.w j' = H.w j),
      H.kw j' (fun p => pa ⟨p.1, H.mem_cast e p.2⟩) = H.kw j pa := by
    intro j' e
    obtain rfl := H.winj e
    rfl
  simp only [NA, dif_neg (H.hwx j), dif_neg (H.hwy' j), dif_pos h]
  exact key _ (Classical.choose_spec h)

/-- The kernel of any other node in model A is uniform. -/
lemma NA_o {v : V} (hvx : v ≠ H.x) (hvy : v ≠ H.y) (hw : ∀ i, H.w i ≠ v)
    (pa : {w // w ∈ H.gA.parents v} → Bool) :
    H.NA.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, H.w j = v := fun ⟨j, hj⟩ => hw j hj
  simp only [NA, dif_neg hvx, dif_neg hvy, dif_neg h]

/-- The kernel of `y` in model B. -/
lemma NB_y (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents H.y} → Bool) :
    H.NB.kernel H.y pa = Bow.chan (pa ⟨H.x, BowGen.p1 G H.x H.y H.hxy⟩) := by
  simp [NB]

/-- The kernel of `u_j` in model B. -/
lemma NB_u (j : Fin (n + 2)) (pa : {v // v ∈ (BowGen.g1 G H.x H.y H.hxy).parents (H.u j)} → Bool) :
    H.NB.kernel (H.u j) pa = PMF.pure false := by
  have h : ∃ j', H.u j' = H.u j := ⟨j, rfl⟩
  simp only [NB, dif_neg (H.huy' j), if_pos h]

/-- The kernel of any other node in model B is uniform. -/
lemma NB_o {v : V} (hvy : v ≠ H.y) (hu : ∀ j, H.u j ≠ v)
    (pa : {w // w ∈ (BowGen.g1 G H.x H.y H.hxy).parents v} → Bool) :
    H.NB.kernel v pa = PMF.uniformOfFintype Bool := by
  have h : ¬ ∃ j, H.u j = v := fun ⟨j, hj⟩ => hu j hj
  simp only [NB, dif_neg hvy, if_neg h]

/-- The graph of model A is a subgraph of `G`. -/
lemma hsA : ∀ v, H.gA.parents v ⊆ G.parents v := by
  intro v a ha
  rw [DAG.mem_parents] at ha
  simp only [DAG.mem_parents]
  rcases (H.gA_edge a v).mp ha with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;>
    first | exact H.hux | exact H.huw1 _ | exact H.huw2 _ | exact H.hww _ | exact H.hwy | exact H.huy

/-- Model A as a model on `G`. -/
noncomputable def mA : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub H.hsA H.NA
/-- Model B as a model on `G`. -/
noncomputable def mB : G.CausalModel (fun _ => Bool) :=
  Completeness.liftSub (BowGen.hsB G H.x H.y H.hxy) H.NB

/-- The bijection of full assignments: it changes only the `u`s, `u_j ↦ u_j xor shift_j xor y`. -/
noncomputable def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if h : ∃ j, H.u j = v.1 then
      xor (s v) (xor (offB (fun i => ev s (H.w i)) (Classical.choose h)) (ev s H.y))
    else s v

/-- The value of `φ s` at `u_j`. -/
lemma φ_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    ev (H.φ s) (H.u j) = xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) := by
  have h : ∃ j', H.u j' = H.u j := ⟨j, rfl⟩
  have hc : Classical.choose h = j := H.uinj (Classical.choose_spec h)
  simp only [ev, φ]
  rw [dif_pos h, hc]

/-- `φ` does not change the nodes outside the `u`s. -/
lemma φ_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) {v : V}
    (hv : ∀ j, H.u j ≠ v) : ev (H.φ s) v = ev s v := by
  have h : ¬ ∃ j, H.u j = v := fun ⟨j, hj⟩ => hv j hj
  simp only [ev, φ]
  rw [dif_neg h]

/-- `φ` is an involution. -/
lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    H.φ (H.φ s) = s := by
  funext ⟨v, hv⟩
  show ev (H.φ (H.φ s)) v = ev s v
  by_cases h : ∃ j, H.u j = v
  · obtain ⟨j, rfl⟩ := h
    have hw : ∀ i, ev (H.φ s) (H.w i) = ev s (H.w i) := fun i => H.φ_o s (fun j => H.huw j i)
    have hy : ev (H.φ s) H.y = ev s H.y := H.φ_o s H.huy'
    rw [H.φ_u (H.φ s) j]
    simp only [hw, hy]
    rw [H.φ_u s j]
    exact xx _ _
  · have hv' : ∀ j, H.u j ≠ v := fun j hj => h ⟨j, hj⟩
    rw [H.φ_o _ hv', H.φ_o _ hv']

/-- The remaining nodes: all except `x`, `y`, the `u`s and the `w`s. -/
def R : Finset V :=
  (insert H.x (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w)))ᶜ

/-- Membership in the remaining nodes. -/
lemma mem_R {v : V} : v ∈ H.R ↔
    v ≠ H.x ∧ v ≠ H.y ∧ (∀ j, H.u j ≠ v) ∧ (∀ i, H.w i ≠ v) := by
  simp [R]

/-- A product over all nodes splits into the factors at `x`, `y`, the `u`s, the `w`s and the
remaining nodes. -/
lemma prod_split (f : V → ℝ≥0∞) :
    ∏ v, f v = f H.x * f H.y * (∏ j, f (H.u j)) * (∏ i, f (H.w i)) * ∏ v ∈ H.R, f v := by
  rw [← Finset.prod_mul_prod_compl
    (insert H.x (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w))) f]
  have hx : H.x ∉ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w) := by
    simp [H.dxy, H.hux', H.hwx]
  have hy : H.y ∉ Finset.univ.image H.u ∪ Finset.univ.image H.w := by
    simp [H.huy', H.hwy']
  have hd : Disjoint (Finset.univ.image H.u) (Finset.univ.image H.w) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨i, hi⟩ := hb
    exact H.huw j i hi.symm
  rw [Finset.prod_insert hx, Finset.prod_insert hy, Finset.prod_union hd]
  rw [Finset.prod_image H.uinj.injOn, Finset.prod_image H.winj.injOn]
  simp only [R, mul_assoc]

/-! ### The kernel factors of the two models -/

/-- The factor of `x` in model A. -/
lemma A_x (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s H.x = Bow.chan (ev s (H.u 0)) (ev s H.x) := by
  rw [kfac_univ, H.NA_x]
  all_goals rfl

/-- The factor of `y` in model A. -/
lemma A_y (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s H.y =
      PMF.pure (xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))) (ev s H.y) := by
  rw [kfac_univ, H.NA_y]
  all_goals rfl

/-- The factor of `u_j` in model A is `1/2`. -/
lemma A_u (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac H.NA Finset.univ s (H.u j) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, H.NA_o (H.hux' j) (H.huy' j) (fun i => (H.huw j i).symm),
    PMF.uniformOfFintype_apply]

/-- The factor of `w₀` in model A. -/
lemma A_w0 (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NA Finset.univ s (H.w 0) =
      PMF.pure (xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0)))) (ev s (H.w 0)) := by
  rw [kfac_univ, H.NA_w, H.kw_zero]
  all_goals rfl

/-- The factor of `w_{i+1}` in model A. -/
lemma A_ws (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin n) :
    kfac H.NA Finset.univ s (H.w i.succ) =
      PMF.pure (xor (ev s (H.w i.castSucc)) (xor (ev s (H.u i.succ.castSucc))
        (ev s (H.u i.succ.succ)))) (ev s (H.w i.succ)) := by
  rw [kfac_univ, H.NA_w, H.kw_succ]
  all_goals rfl

/-- The factor of a remaining node in model A is `1/2`. -/
lemma A_o (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ H.R) : kfac H.NA Finset.univ s v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨h1, h2, _, h4⟩ := H.mem_R.mp hv
  rw [kfac_univ, H.NA_o h1 h2 h4, PMF.uniformOfFintype_apply]

/-- The factor of `x` in model B is `1/2`. -/
lemma B_x (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NB Finset.univ t H.x = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, H.NB_o H.dxy H.hux', PMF.uniformOfFintype_apply]

/-- The factor of `y` in model B. -/
lemma B_y (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    kfac H.NB Finset.univ t H.y = Bow.chan (ev t H.x) (ev t H.y) := by
  rw [kfac_univ, H.NB_y]
  all_goals rfl

/-- The factor of `u_j` in model B. -/
lemma B_u (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (j : Fin (n + 2)) :
    kfac H.NB Finset.univ t (H.u j) = PMF.pure false (ev t (H.u j)) := by
  rw [kfac_univ, H.NB_u]
  all_goals rfl

/-- The factor of `w_i` in model B is `1/2`. -/
lemma B_w (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (i : Fin (n + 1)) :
    kfac H.NB Finset.univ t (H.w i) = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  rw [kfac_univ, H.NB_o (H.hwy' i) (fun j => H.huw j i), PMF.uniformOfFintype_apply]

/-- The factor of a remaining node in model B is `1/2`. -/
lemma B_o (t : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) (v : V)
    (hv : v ∈ H.R) : kfac H.NB Finset.univ t v = (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  obtain ⟨_, h2, h3, _⟩ := H.mem_R.mp hv
  rw [kfac_univ, H.NB_o h2 h3, PMF.uniformOfFintype_apply]

/-! ### The joint distributions and the end of the proof -/

/-- Model B gives `φ s` the probability that model A gives `s`: both are zero unless the
equations hold, and then they are equal. -/
lemma joint_eq (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    H.mB.fullJoint (H.φ s) = H.mA.fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, Completeness.kfac_liftSub]
  rw [H.prod_split, H.prod_split]
  have hR : ∏ v ∈ H.R, kfac H.NB Finset.univ (H.φ s) v =
      ∏ v ∈ H.R, kfac H.NA Finset.univ s v :=
    Finset.prod_congr rfl (fun v hv => by rw [H.B_o _ v hv, H.A_o s v hv])
  have hx' : ev (H.φ s) H.x = ev s H.x := H.φ_o s H.hux'
  have hy' : ev (H.φ s) H.y = ev s H.y := H.φ_o s H.huy'
  rw [hR, H.A_x, H.A_y, H.B_x, H.B_y, hx', hy']
  by_cases hC : condA (fun j => ev s (H.u j)) (fun i => ev s (H.w i)) (ev s H.y)
  · have hB := (condA_iff _ _ _).mp hC
    obtain ⟨h1, h2, h3⟩ := hC
    have h1' : ev s (H.w 0) = xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0))) := h1
    have h2' : ∀ k : Fin n, ev s (H.w k.succ) = xor (ev s (H.w k.castSucc))
        (xor (ev s (H.u k.succ.castSucc)) (ev s (H.u k.succ.succ))) := h2
    have h3' : ev s H.y = xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1)))) := h3
    have hU : ∏ j, kfac H.NB Finset.univ (H.φ s) (H.u j) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hj : ev s (H.u j) = xor (offB (fun i => ev s (H.w i)) j) (ev s H.y) := hB j
      have hcond : xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) =
          false := by
        rw [hj]; exact Bool.xor_self _
      rw [H.B_u, H.φ_u, PMF.pure_apply, if_pos hcond]
    have hW : ∏ i, kfac H.NA Finset.univ s (H.w i) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [H.A_w0, PMF.pure_apply, if_pos h1']
      · rw [H.A_ws, PMF.pure_apply, if_pos (h2' k)]
    have h0 : ev s (H.u 0) = ev s H.y := by
      have hj0 : ev s (H.u 0) = xor (offB (fun i => ev s (H.w i)) 0) (ev s H.y) := hB 0
      rw [offB_zero] at hj0
      simpa using hj0
    rw [hU, hW]
    simp only [H.A_u, H.B_w, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [PMF.pure_apply, if_pos h3', h0, chan_symm (ev s H.y)]
    ring
  · have hB : ¬ ∀ j, ev s (H.u j) = xor (offB (fun i => ev s (H.w i)) j) (ev s H.y) :=
      fun h => hC ((condA_iff _ _ _).mpr h)
    have hU : ∏ j, kfac H.NB Finset.univ (H.φ s) (H.u j) = 0 := by
      push_neg at hB
      obtain ⟨j, hj⟩ := hB
      have hnc : ¬ (xor (ev s (H.u j)) (xor (offB (fun i => ev s (H.w i)) j) (ev s H.y)) =
          false) := fun hf => hj (xb _ _ hf)
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [H.B_u, H.φ_u, PMF.pure_apply, if_neg hnc]
    have hA : PMF.pure (xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))) (ev s H.y)
        = 0 ∨ ∏ i, kfac H.NA Finset.univ s (H.w i) = 0 := by
      by_cases h3 : ev s H.y = xor (ev s (H.w (Fin.last n))) (ev s (H.u (Fin.last (n + 1))))
      · right
        by_cases h1 : ev s (H.w 0) = xor (ev s (H.u 0)) (ev s (H.u (Fin.succ 0)))
        · have h2 : ¬ ∀ k : Fin n, ev s (H.w k.succ) = xor (ev s (H.w k.castSucc))
              (xor (ev s (H.u k.succ.castSucc)) (ev s (H.u k.succ.succ))) :=
            fun h2 => hC ⟨h1, h2, h3⟩
          push_neg at h2
          obtain ⟨k, hk⟩ := h2
          exact Finset.prod_eq_zero (Finset.mem_univ k.succ)
            (by rw [H.A_ws, PMF.pure_apply, if_neg hk])
        · exact Finset.prod_eq_zero (Finset.mem_univ 0)
            (by rw [H.A_w0, PMF.pure_apply, if_neg h1])
      · left
        rw [PMF.pure_apply, if_neg h3]
    rcases hA with h | h
    · rw [hU, h]; simp
    · rw [hU, h]; simp

/-- The joint distribution of model B is that of model A pushed forward along `φ`. -/
lemma full_map : H.mB.fullJoint = H.mA.fullJoint.map H.φ := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (H.φ s)]
  · rw [if_pos (H.φ_invol s).symm, ← H.joint_eq (H.φ s), H.φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, H.φ_invol]

/-- Models A and B agree on every `O` that contains no `u`. -/
lemma obsEq (O : Finset V) (hu : ∀ j, H.u j ∉ O) :
    H.mA.marginal O = H.mB.marginal O := by
  unfold CausalModel.marginal
  rw [H.full_map, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ∀ j, H.u j ≠ v := fun j e => hu j (e ▸ hv)
  show ev s v = ev (H.φ s) v
  exact (H.φ_o s hv').symm

/-- The observed distribution of model A on `O` is positive when `x ∈ O` and no `u` is in `O`. -/
lemma posA (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) :
    ∀ a, H.mA.marginal O a ≠ 0 := by
  intro a
  rw [H.obsEq O hu, show H.mB.marginal O = H.NB.marginal O from
    Completeness.marginal_eq_of_kfac _ _
      (Completeness.kfac_liftSub (BowGen.hsB G H.x H.y H.hxy) H.NB) O]
  have hS := BowGen.ancB G H.x H.y H.hxy O (Or.inl hx)
  rw [marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [kfac_of_mem _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  by_cases hvy : v = H.y
  · subst hvy
    rw [H.NB_y]
    exact Bow.chan_ne_zero _ _
  · rw [H.NB_o hvy (fun j e => hu j (e ▸ hv))]
    simp [PMF.uniformOfFintype_apply]

/-- In model A, `P_x(y)` is the observed `P(y)` of model B: after the intervention `x` no longer
reaches `y`. -/
lemma doA (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hy : H.y ∈ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y}) :
    (doModel H.mA {H.x} x0).marginal {H.y} y0 = H.mB.marginal {H.y} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel H.mA {H.x} x0)
    (doModel H.NA {H.x} x0)
    (Completeness.kfac_doModel_liftSub H.hsA H.NA {H.x} x0) {H.y}]
  have hanc : ∀ v ∈ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w), ∀ a,
      H.gA.edge a v → a ∈ insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w) := by
    intro v _ a ha
    rcases (H.gA_edge a v).mp ha with ⟨h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> simp
  have hdisj : Disjoint (insert H.y (Finset.univ.image H.u ∪ Finset.univ.image H.w)) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.dxy, H.hux', H.hwx]
  rw [Rule3.doModel_marginal_of_subset H.NA {H.x} x0 _ hanc hdisj {H.y} (by simp) y0,
    ← Completeness.marginal_eq_of_kfac H.mA H.NA (Completeness.kfac_liftSub H.hsA H.NA) {H.y},
    marginal_eq_of_subset (H.obsEq O hu) (show ({H.y} : Finset V) ⊆ O by simpa using hy)]

/-- **The hedge chain is not identifiable.** For a chain `x ↔ w₀ ↔ … ↔ w_n ↔ y` with
latent `u`s, `w_i → w_{i+1}`, `w_n → y` and `x → y`, `P(y | do(x))` is not identifiable
from any `O` that contains `x` and `y` but no `u`. -/
theorem not_ident (O : Finset V) (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} := by
  intro h
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hnp : ∀ w, ¬ (BowGen.g1 G H.x H.y H.hxy).edge w H.x := by
    intro w hw
    have hw' : w = H.x ∧ H.x = H.y := hw
    exact hyx hw'.2.symm
  have hS21 := BowGen.ancB G H.x H.y H.hxy ({H.y} ∪ {H.x}) (Or.inl (by simp))
  have hS1 := BowGen.ancB G H.x H.y H.hxy {H.x} (Or.inr (by simp [hyx]))
  have key : ∀ b : Bool,
      Bow.chan b true * (Fintype.card Bool : ℝ≥0∞)⁻¹ =
        H.mB.marginal {H.y} (fun _ => true) * (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else true
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    have hty : t.restrict (show ({H.y} : Finset V) ⊆ {H.y} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => true := by
      funext ⟨v, hv⟩
      have : v = H.y := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict, hyx]
    have e := h H.mA H.mB (H.obsEq O hu) (H.posA O hu hx) t
    rw [htx, hty, H.doA O hu hy,
      Completeness.marginal_eq_of_kfac (doModel H.mB {H.x} _)
        (doModel H.NB {H.x} _)
        (Completeness.kfac_doModel_liftSub (BowGen.hsB G H.x H.y H.hxy) H.NB {H.x} _) {H.y}] at e
    have fd := Adjustment.frontdoor_step1 H.NB {H.x} {H.y}
      (Finset.disjoint_singleton.mpr hyx)
      (Completeness.dsep_isolated hnp {H.y} (by simp [hyx.symm])) t
    rw [htx, hty, ← e] at fd
    rw [marginal_ancestral_apply _ _ hS21 t,
      Finset.prod_union (show Disjoint ({H.y} : Finset V) {H.x} from
        Finset.disjoint_singleton.mpr hyx),
      Finset.prod_singleton, Finset.prod_singleton,
      kfac_of_mem _ _ t H.y (by simp) (DAG.parents_subset_of_closed hS21 H.y (by simp)),
      kfac_of_mem _ _ t H.x (by simp) (DAG.parents_subset_of_closed hS21 H.x (by simp))] at fd
    rw [marginal_ancestral_apply _ {H.x} hS1, Finset.prod_singleton,
      kfac_of_mem _ {H.x} _ H.x (by simp) (DAG.parents_subset_of_closed hS1 H.x (by simp))] at fd
    rw [H.NB_y, H.NB_o hyx.symm H.hux', H.NB_o hyx.symm H.hux'] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, mul_comm, hyx] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hc : Bow.chan true true = Bow.chan false true := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (true = false) by decide)] at hc
  exact Bow.q_ne hc

end Chain

/-- **The hedge chain is not identifiable**, as a standalone theorem. -/
theorem chain_not_identifiable {G : DAG V} {n : ℕ} (H : Chain G n) (O : Finset V)
    (hu : ∀ j, H.u j ∉ O) (hx : H.x ∈ O) (hy : H.y ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y} :=
  H.not_ident O hu hx hy

end HedgeChain
end Identification

#print axioms Identification.HedgeChain.chain_not_identifiable
