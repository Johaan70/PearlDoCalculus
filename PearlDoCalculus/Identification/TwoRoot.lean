import PearlDoCalculus.Identification.Bow

/-!
# A c-forest with two roots

The graph has the edges `u₁ → x`, `u₁ → w`, `u₂ → w`, `u₂ → y` and `x → y`, with `u₁, u₂`
latent. Here `P(y | do(x))` alone is identifiable (`w` is a collider on the only back-door
path), but `P(y, w | do(x))` is not: `F = {x, y, w}` and `F' = {y, w}` with the roots `y`
and `w`. This is the smallest case that needs several roots.

How the proof goes: in model A, `x = chan(u₁)`, `w = u₁ xor u₂` and `y = u₂`, so
`y xor w = u₁` and `do(x)` changes nothing. In model B, `u₁ = 0`, `w = u₂` and
`y = chan(x) xor u₂`. Model B uses a latent variable itself; with only the edge `x → y`
it would be impossible. The observed distributions agree. To compute the marginals we use
a third model C with the same joint distribution as A, in which `{y, w, x}` is closed
under ancestors (`y, w` uniform, `x = chan(y xor w)`, `u₁ = y xor w`, `u₂ = y`).

Main result: `Identification.TwoRoot.twoRoot_not_identifiable`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

open scoped ENNReal

namespace Identification
namespace TwoRoot

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Konfigurasjonen inne i `G`: `y` er roten med `x → y`, `w` er den andre roten. -/
structure Data (G : DAG V) where
  u1 : V
  u2 : V
  x : V
  w : V
  y : V
  h1x : G.edge u1 x
  h1w : G.edge u1 w
  h2w : G.edge u2 w
  h2y : G.edge u2 y
  hxy : G.edge x y
  h12 : u1 ≠ u2
  h2x : u2 ≠ x
  hxw : x ≠ w
  hwy : w ≠ y

namespace Data

variable {G : DAG V} (H : Data G)

lemma d1x : H.u1 ≠ H.x := BowGen.ne_of_edge H.h1x
lemma d1w : H.u1 ≠ H.w := BowGen.ne_of_edge H.h1w
lemma d2w : H.u2 ≠ H.w := BowGen.ne_of_edge H.h2w
lemma d2y : H.u2 ≠ H.y := BowGen.ne_of_edge H.h2y
lemma dxy : H.x ≠ H.y := BowGen.ne_of_edge H.hxy
lemma d1y : H.u1 ≠ H.y := by
  intro e
  have a := G.rank_strict_mono _ _ H.h1x
  have b := G.rank_strict_mono _ _ H.hxy
  rw [e] at a
  omega

/-! ### De tre grafene -/

noncomputable def gA : DAG V where
  edge s t := (s = H.u1 ∧ t = H.x) ∨ (s = H.u1 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.w) ∨
    (s = H.u2 ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h1x
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h1w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2y

noncomputable def gB : DAG V where
  edge s t := (s = H.u2 ∧ t = H.w) ∨ (s = H.u2 ∧ t = H.y) ∨ (s = H.x ∧ t = H.y)
  decEdge := fun _ _ => Classical.dec _
  rank := G.rank
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2w
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.h2y
    · rw [h1, h2]; exact G.rank_strict_mono _ _ H.hxy

noncomputable def gC : DAG V where
  edge s t := (s = H.y ∧ t = H.x) ∨ (s = H.w ∧ t = H.x) ∨ (s = H.y ∧ t = H.u1) ∨
    (s = H.w ∧ t = H.u1) ∨ (s = H.y ∧ t = H.u2)
  decEdge := fun _ _ => Classical.dec _
  rank := fun v => if v = H.y ∨ v = H.w then 0 else 1
  rank_strict_mono := by
    intro s t h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      simp [H.dxy, H.hxw, H.d1y, H.d1w, H.d2y, H.d2w, H.hwy, H.hwy.symm]

lemma pAx : H.u1 ∈ (gA H).parents H.x := by simp [DAG.parents, gA]
lemma pAw1 : H.u1 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAw2 : H.u2 ∈ (gA H).parents H.w := by simp [DAG.parents, gA]
lemma pAy : H.u2 ∈ (gA H).parents H.y := by simp [DAG.parents, gA]
lemma pBw : H.u2 ∈ (gB H).parents H.w := by simp [DAG.parents, gB]
lemma pBy2 : H.u2 ∈ (gB H).parents H.y := by simp [DAG.parents, gB]
lemma pByx : H.x ∈ (gB H).parents H.y := by simp [DAG.parents, gB]
lemma pCxy : H.y ∈ (gC H).parents H.x := by simp [DAG.parents, gC]
lemma pCxw : H.w ∈ (gC H).parents H.x := by simp [DAG.parents, gC]
lemma pC1y : H.y ∈ (gC H).parents H.u1 := by simp [DAG.parents, gC]
lemma pC1w : H.w ∈ (gC H).parents H.u1 := by simp [DAG.parents, gC]
lemma pC2y : H.y ∈ (gC H).parents H.u2 := by simp [DAG.parents, gC]

/-! ### Modellene -/

noncomputable def NA : (gA H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then Bow.chan (pa ⟨H.u1, by rw [hvx]; exact pAx H⟩)
    else if hvw : v = H.w then
      PMF.pure (xor (pa ⟨H.u1, by rw [hvw]; exact pAw1 H⟩) (pa ⟨H.u2, by rw [hvw]; exact pAw2 H⟩))
    else if hvy : v = H.y then PMF.pure (pa ⟨H.u2, by rw [hvy]; exact pAy H⟩)
    else PMF.uniformOfFintype Bool

noncomputable def NB : (gB H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvy : v = H.y then
      Bow.chan (xor (pa ⟨H.x, by rw [hvy]; exact pByx H⟩) (pa ⟨H.u2, by rw [hvy]; exact pBy2 H⟩))
    else if hvw : v = H.w then PMF.pure (pa ⟨H.u2, by rw [hvw]; exact pBw H⟩)
    else if v = H.u1 then PMF.pure false
    else PMF.uniformOfFintype Bool

noncomputable def NC : (gC H).CausalModel (fun _ => Bool) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hvx : v = H.x then
      Bow.chan (xor (pa ⟨H.y, by rw [hvx]; exact pCxy H⟩) (pa ⟨H.w, by rw [hvx]; exact pCxw H⟩))
    else if hv1 : v = H.u1 then
      PMF.pure (xor (pa ⟨H.y, by rw [hv1]; exact pC1y H⟩) (pa ⟨H.w, by rw [hv1]; exact pC1w H⟩))
    else if hv2 : v = H.u2 then PMF.pure (pa ⟨H.y, by rw [hv2]; exact pC2y H⟩)
    else PMF.uniformOfFintype Bool

lemma NA_x (pa : {v // v ∈ (gA H).parents H.x} → Bool) :
    (NA H).kernel H.x pa = Bow.chan (pa ⟨H.u1, pAx H⟩) := by simp [NA]
lemma NA_w (pa : {v // v ∈ (gA H).parents H.w} → Bool) :
    (NA H).kernel H.w pa = PMF.pure (xor (pa ⟨H.u1, pAw1 H⟩) (pa ⟨H.u2, pAw2 H⟩)) := by
  simp [NA, H.hxw.symm]
lemma NA_y (pa : {v // v ∈ (gA H).parents H.y} → Bool) :
    (NA H).kernel H.y pa = PMF.pure (pa ⟨H.u2, pAy H⟩) := by
  simp [NA, H.dxy.symm, H.hwy.symm]
lemma NA_o {v : V} (hvx : v ≠ H.x) (hvw : v ≠ H.w) (hvy : v ≠ H.y)
    (pa : {w // w ∈ (gA H).parents v} → Bool) :
    (NA H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NA, hvx, hvw, hvy]

lemma NB_y (pa : {v // v ∈ (gB H).parents H.y} → Bool) :
    (NB H).kernel H.y pa = Bow.chan (xor (pa ⟨H.x, pByx H⟩) (pa ⟨H.u2, pBy2 H⟩)) := by
  simp [NB]
lemma NB_w (pa : {v // v ∈ (gB H).parents H.w} → Bool) :
    (NB H).kernel H.w pa = PMF.pure (pa ⟨H.u2, pBw H⟩) := by simp [NB, H.hwy]
lemma NB_u1 (pa : {v // v ∈ (gB H).parents H.u1} → Bool) :
    (NB H).kernel H.u1 pa = PMF.pure false := by simp [NB, H.d1y, H.d1w]
lemma NB_o {v : V} (hvy : v ≠ H.y) (hvw : v ≠ H.w) (hv1 : v ≠ H.u1)
    (pa : {w // w ∈ (gB H).parents v} → Bool) :
    (NB H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NB, hvy, hvw, hv1]

lemma NC_x (pa : {v // v ∈ (gC H).parents H.x} → Bool) :
    (NC H).kernel H.x pa = Bow.chan (xor (pa ⟨H.y, pCxy H⟩) (pa ⟨H.w, pCxw H⟩)) := by
  simp [NC]
lemma NC_u1 (pa : {v // v ∈ (gC H).parents H.u1} → Bool) :
    (NC H).kernel H.u1 pa = PMF.pure (xor (pa ⟨H.y, pC1y H⟩) (pa ⟨H.w, pC1w H⟩)) := by
  simp [NC, H.d1x]
lemma NC_u2 (pa : {v // v ∈ (gC H).parents H.u2} → Bool) :
    (NC H).kernel H.u2 pa = PMF.pure (pa ⟨H.y, pC2y H⟩) := by
  simp [NC, H.h2x, H.h12.symm]
lemma NC_o {v : V} (hvx : v ≠ H.x) (hv1 : v ≠ H.u1) (hv2 : v ≠ H.u2)
    (pa : {w // w ∈ (gC H).parents v} → Bool) :
    (NC H).kernel v pa = PMF.uniformOfFintype Bool := by simp [NC, hvx, hv1, hv2]

lemma hsA : ∀ v, (gA H).parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.mem_parents] at ha ⊢
  have ha' : (a = H.u1 ∧ v = H.x) ∨ (a = H.u1 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.w) ∨
      (a = H.u2 ∧ v = H.y) := ha
  rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact H.h1x
  · rw [h1, h2]; exact H.h1w
  · rw [h1, h2]; exact H.h2w
  · rw [h1, h2]; exact H.h2y

lemma hsB : ∀ v, (gB H).parents v ⊆ G.parents v := by
  intro v a ha
  simp only [DAG.mem_parents] at ha ⊢
  have ha' : (a = H.u2 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.y) ∨ (a = H.x ∧ v = H.y) := ha
  rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact H.h2w
  · rw [h1, h2]; exact H.h2y
  · rw [h1, h2]; exact H.hxy

noncomputable def mA : G.CausalModel (fun _ => Bool) := Completeness.liftSub (hsA H) (NA H)
noncomputable def mB : G.CausalModel (fun _ => Bool) := Completeness.liftSub (hsB H) (NB H)

/-! ### Fellesfordelingene -/

/-- Bijeksjonen: `u₁ ↦ u₁ xor y xor w`, `u₂ ↦ u₂ xor y xor w`. -/
def φ (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V) :=
  fun v =>
    if v.1 = H.u1 ∨ v.1 = H.u2 then
      xor (s v) (xor (s ⟨H.y, Finset.mem_univ _⟩) (s ⟨H.w, Finset.mem_univ _⟩))
    else s v

lemma φ_invol (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    φ H (φ H s) = s := by
  funext ⟨v, hv⟩
  by_cases h : v = H.u1 ∨ v = H.u2
  · have hy : ¬ (H.y = H.u1 ∨ H.y = H.u2) := by
      rintro (e | e)
      · exact H.d1y e.symm
      · exact H.d2y e.symm
    have hw : ¬ (H.w = H.u1 ∨ H.w = H.u2) := by
      rintro (e | e)
      · exact H.d1w e.symm
      · exact H.d2w e.symm
    rcases Bool.eq_false_or_eq_true (s ⟨v, hv⟩) with a | a <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with b | b <;>
    rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with c | c <;>
    simp [φ, h, hy, hw, a, b, c]
  · simp [φ, h]

/-- Produktet over alle noder, delt opp i de fem spesielle og resten. -/
lemma split5 (f : V → ℝ≥0∞) :
    ∏ v, f v = f H.u1 * (f H.u2 * (f H.x * (f H.w * (f H.y *
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y, f v)))) := by
  have m2 : H.u2 ∈ Finset.univ.erase H.u1 := by simp [H.h12.symm]
  have mx : H.x ∈ (Finset.univ.erase H.u1).erase H.u2 := by
    simp [H.d1x.symm, H.h2x.symm]
  have mw : H.w ∈ ((Finset.univ.erase H.u1).erase H.u2).erase H.x := by
    simp [H.d1w.symm, H.d2w.symm, H.hxw.symm]
  have my : H.y ∈ (((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w := by
    simp [H.d1y.symm, H.d2y.symm, H.dxy.symm, H.hwy.symm]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H.u1),
    ← Finset.mul_prod_erase _ _ m2, ← Finset.mul_prod_erase _ _ mx,
    ← Finset.mul_prod_erase _ _ mw, ← Finset.mul_prod_erase _ _ my]

lemma mem_rest {v : V}
    (hv : v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y) :
    v ≠ H.y ∧ v ≠ H.w ∧ v ≠ H.x ∧ v ≠ H.u2 ∧ v ≠ H.u1 := by
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

lemma joint_AC (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (NC H).fullJoint s = (mA H).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, BowGen.kfac_liftG]
  rw [split5 H, split5 H]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NC H) Finset.univ s v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hy, hw, hx, h2, h1⟩ := H.mem_rest hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NC_o H hx h1 h2, NA_o H hx hw hy]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NA_o, Data.NC_x, Data.NC_u1,
    Data.NC_u2, Data.NC_o, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.hwy, H.hwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma joint_BA (s : Assignment (α := fun _ : V => Bool) (Finset.univ : Finset V)) :
    (mB H).fullJoint (φ H s) = (mA H).fullJoint s := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp only [mA, mB, BowGen.kfac_liftG]
  rw [split5 H, split5 H]
  have hR : ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NB H) Finset.univ (φ H s) v =
      ∏ v ∈ ((((Finset.univ.erase H.u1).erase H.u2).erase H.x).erase H.w).erase H.y,
        kfac (NA H) Finset.univ s v := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hy, hw, hx, h2, h1⟩ := H.mem_rest hv
    rw [DoAudit.kfac_univ, DoAudit.kfac_univ, NB_o H hy hw h1, NA_o H hx hw hy]
    simp [PMF.uniformOfFintype_apply]
  rw [hR]
  rcases Bool.eq_false_or_eq_true (s ⟨H.u1, Finset.mem_univ _⟩) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.u2, Finset.mem_univ _⟩) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.x, Finset.mem_univ _⟩) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.w, Finset.mem_univ _⟩) with h3 | h3 <;>
  rcases Bool.eq_false_or_eq_true (s ⟨H.y, Finset.mem_univ _⟩) with h4 | h4 <;>
  simp [DoAudit.kfac_univ, Data.NA_x, Data.NA_w, Data.NA_y, Data.NA_o, Data.NB_y, Data.NB_w,
    Data.NB_u1, Data.NB_o, φ, Assignment.restrict,
    PMF.pure_apply, Bow.chan_apply, PMF.uniformOfFintype_apply, h0, h1, h2, h3, h4,
    H.d1x, H.d1x.symm, H.d1w, H.d1w.symm, H.d2w, H.d2w.symm, H.d2y, H.d2y.symm,
    H.hwy, H.hwy.symm, H.dxy, H.dxy.symm, H.d1y, H.d1y.symm, H.h12, H.h12.symm,
    H.h2x, H.h2x.symm, H.hxw, H.hxw.symm, mul_comm, mul_left_comm, mul_assoc]

lemma full_map : (mB H).fullJoint = (mA H).fullJoint.map (φ H) := by
  ext s
  rw [PMF.map_apply, tsum_eq_single (φ H s)]
  · rw [if_pos (φ_invol H s).symm, ← joint_BA H (φ H s), φ_invol]
  · intro s' hs'
    rw [if_neg]
    intro hs
    apply hs'
    rw [hs, φ_invol]

lemma obsEq (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) :
    (mA H).marginal O = (mB H).marginal O := by
  unfold CausalModel.marginal
  rw [full_map H, PMF.map_comp]
  congr 1
  funext s
  funext ⟨v, hv⟩
  have hv' : ¬ (v = H.u1 ∨ v = H.u2) := by
    rintro (e | e)
    · exact hu1 (e ▸ hv)
    · exact hu2 (e ▸ hv)
  simp [Function.comp, Assignment.restrict, φ, hv']

lemma margAC (T : Finset V) : (mA H).marginal T = (NC H).marginal T := by
  have hj : (NC H).fullJoint = (mA H).fullJoint := PMF.ext (joint_AC H)
  unfold CausalModel.marginal
  rw [hj]

/-! ### Utregninger i C og B -/

lemma ancC (S : Finset V) (hyS : H.y ∈ S) (hwS : H.w ∈ S) (h1 : H.u1 ∉ S) (h2 : H.u2 ∉ S) :
    ∀ v ∈ S, ∀ a, (gC H).edge a v → a ∈ S := by
  intro v hv a ha
  have ha' : (a = H.y ∧ v = H.x) ∨ (a = H.w ∧ v = H.x) ∨ (a = H.y ∧ v = H.u1) ∨
      (a = H.w ∧ v = H.u1) ∨ (a = H.y ∧ v = H.u2) := ha
  rcases ha' with ⟨e1, _⟩ | ⟨e1, _⟩ | ⟨_, e2⟩ | ⟨_, e2⟩ | ⟨_, e2⟩
  · rw [e1]; exact hyS
  · rw [e1]; exact hwS
  · exact absurd (e2 ▸ hv) h1
  · exact absurd (e2 ▸ hv) h1
  · exact absurd (e2 ▸ hv) h2

lemma posA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O) (hy : H.y ∈ O) (hw : H.w ∈ O) :
    ∀ a, (mA H).marginal O a ≠ 0 := by
  intro a
  have hS := H.ancC O hy hw hu1 hu2
  rw [margAC H O, marginal_ancestral_apply _ O hS a]
  refine Finset.prod_ne_zero_iff.mpr (fun v hv => ?_)
  rw [BowGen.kfac_eqG _ O a v hv (DAG.parents_subset_of_closed hS v hv)]
  have hv1 : v ≠ H.u1 := fun e => hu1 (e ▸ hv)
  have hv2 : v ≠ H.u2 := fun e => hu2 (e ▸ hv)
  by_cases hvx : v = H.x
  · subst hvx
    rw [NC_x]
    exact Bow.chan_ne_zero _ _
  · rw [NC_o H hvx hv1 hv2]
    simp [PMF.uniformOfFintype_apply]

lemma doA (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (x0 : Assignment (α := fun _ : V => Bool) {H.x})
    (y0 : Assignment (α := fun _ : V => Bool) {H.y, H.w}) :
    (doModel (mA H) {H.x} x0).marginal {H.y, H.w} y0 = (mA H).marginal {H.y, H.w} y0 := by
  rw [Completeness.marginal_eq_of_kfac (doModel (mA H) {H.x} x0) (doModel (NA H) {H.x} x0)
    (BowGen.kfac_lift_doG (hsA H) (NA H) {H.x} x0) {H.y, H.w}]
  have hanc : ∀ v ∈ ({H.u1, H.u2, H.w, H.y} : Finset V), ∀ a, (gA H).edge a v →
      a ∈ ({H.u1, H.u2, H.w, H.y} : Finset V) := by
    intro v _ a ha
    have ha' : (a = H.u1 ∧ v = H.x) ∨ (a = H.u1 ∧ v = H.w) ∨ (a = H.u2 ∧ v = H.w) ∨
        (a = H.u2 ∧ v = H.y) := ha
    rcases ha' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdisj : Disjoint ({H.u1, H.u2, H.w, H.y} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.d1x.symm, H.h2x.symm, H.hxw, H.dxy]
  rw [Rule3.doModel_marginal_of_sub (NA H) {H.x} x0 {H.u1, H.u2, H.w, H.y} hanc hdisj
      {H.y, H.w} (by intro v hv; simp at hv ⊢; tauto) y0,
    ← Completeness.marginal_eq_of_kfac (mA H) (NA H) (BowGen.kfac_liftG (hsA H) (NA H))
      {H.y, H.w}]

/-- **To røtter: `P(y, w | do(x))` er ikke identifiserbar.** -/
theorem not_ident (O : Finset V) (hu1 : H.u1 ∉ O) (hu2 : H.u2 ∉ O)
    (hy : H.y ∈ O) (hw : H.w ∈ O) (hx : H.x ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {H.x} {H.y, H.w} := by
  intro h
  have hyx : H.y ≠ H.x := H.dxy.symm
  have hwx : H.w ≠ H.x := H.hxw.symm
  have hYX : Disjoint ({H.y, H.w} : Finset V) {H.x} := by
    rw [Finset.disjoint_singleton_right]
    simp [H.dxy, H.hxw]
  have hnp : ∀ a, ¬ (gB H).edge a H.x := by
    intro a ha
    have ha' : (a = H.u2 ∧ H.x = H.w) ∨ (a = H.u2 ∧ H.x = H.y) ∨ (a = H.x ∧ H.x = H.y) := ha
    rcases ha' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
    · exact H.hxw e
    · exact H.dxy e
    · exact H.dxy e
  have hSx : ∀ v ∈ ({H.x} : Finset V), ∀ a, (gB H).edge a v → a ∈ ({H.x} : Finset V) := by
    intro v hv a ha
    rw [Finset.mem_singleton] at hv
    subst hv
    exact absurd ha (hnp a)
  have hOY : ({H.y, H.w} : Finset V) ∪ {H.x} ⊆ O := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with (rfl | rfl) | rfl
    · exact hy
    · exact hw
    · exact hx
  have hC1 := H.ancC ({H.y, H.w} ∪ {H.x}) (by simp) (by simp)
    (by simp [H.d1y, H.d1w, H.d1x]) (by simp [H.d2y, H.d2w, H.h2x])
  have hC2 := H.ancC ({H.y, H.w} : Finset V) (by simp) (by simp)
    (by simp [H.d1y, H.d1w]) (by simp [H.d2y, H.d2w])
  have key : ∀ b : Bool,
      Bow.chan true b * ((Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹) =
        ((Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹) *
          (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
    intro b
    let t : Assignment (α := fun _ : V => Bool) ({H.y, H.w} ∪ {H.x}) :=
      fun v => if v.1 = H.x then b else if v.1 = H.y then true else false
    have htx : t.restrict (show ({H.x} : Finset V) ⊆ {H.y, H.w} ∪ {H.x} by
        intro v hv; simp only [Finset.mem_union]; tauto) = fun _ => b := by
      funext ⟨v, hv⟩
      have : v = H.x := Finset.mem_singleton.mp hv
      subst this
      simp [t, Assignment.restrict]
    -- Identifiserbarheten
    have e := h (mA H) (mB H) (obsEq H O hu1 hu2) (posA H O hu1 hu2 hy hw) t
    rw [htx, doA H O hu1 hu2,
      Completeness.marginal_eq_of_kfac (doModel (mB H) {H.x} _) (doModel (NB H) {H.x} _)
        (BowGen.kfac_lift_doG (hsB H) (NB H) {H.x} _) {H.y, H.w}] at e
    -- FD1 i modell B
    have fd := Adjustment.frontdoor_step1 (NB H) {H.x} {H.y, H.w} hYX
      (Completeness.dsep_isolated hnp {H.y, H.w} (by simp [H.dxy, H.hxw])) t
    rw [htx, ← e] at fd
    -- P_B(y, w, x) = P_C(y, w, x)
    rw [show (NB H).marginal ({H.y, H.w} ∪ {H.x}) = (NC H).marginal ({H.y, H.w} ∪ {H.x}) from by
      rw [← Completeness.marginal_eq_of_kfac (mB H) (NB H) (BowGen.kfac_liftG (hsB H) (NB H)),
        ← marginal_eq_of_sub (obsEq H O hu1 hu2) hOY, margAC]] at fd
    rw [margAC H] at fd
    -- Produktene
    have hyw : H.y ∉ ({H.w} : Finset V) := by simp [H.hwy.symm]
    rw [marginal_ancestral_apply _ _ hC1 t, Finset.prod_union hYX, Finset.prod_insert hyw,
      Finset.prod_singleton, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ t H.y (by simp) (DAG.parents_subset_of_closed hC1 H.y (by simp)),
      BowGen.kfac_eqG _ _ t H.w (by simp) (DAG.parents_subset_of_closed hC1 H.w (by simp)),
      BowGen.kfac_eqG _ _ t H.x (by simp) (DAG.parents_subset_of_closed hC1 H.x (by simp)),
      NC_o H hyx H.d1y.symm H.d2y.symm, NC_o H hwx H.d1w.symm H.d2w.symm, NC_x] at fd
    rw [marginal_ancestral_apply _ _ hC2, Finset.prod_insert hyw, Finset.prod_singleton,
      BowGen.kfac_eqG _ _ _ H.y (by simp) (DAG.parents_subset_of_closed hC2 H.y (by simp)),
      BowGen.kfac_eqG _ _ _ H.w (by simp) (DAG.parents_subset_of_closed hC2 H.w (by simp)),
      NC_o H hyx H.d1y.symm H.d2y.symm, NC_o H hwx H.d1w.symm H.d2w.symm] at fd
    rw [marginal_ancestral_apply _ {H.x} hSx, Finset.prod_singleton,
      BowGen.kfac_eqG _ {H.x} _ H.x (by simp) (DAG.parents_subset_of_closed hSx H.x (by simp)),
      NB_o H hyx.symm H.hxw H.d1x.symm] at fd
    simpa [PMF.uniformOfFintype_apply, Assignment.restrict, t, hyx, hwx, H.hwy,
      mul_comm, mul_left_comm, mul_assoc] using fd
  have k := (key true).trans (key false).symm
  have hQ0 : (Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hQT : (Fintype.card Bool : ℝ≥0∞)⁻¹ * (Fintype.card Bool : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  have hc : Bow.chan true true = Bow.chan true false := by
    exact (ENNReal.mul_left_inj hQ0 hQT).mp k
  rw [Bow.chan_apply, Bow.chan_apply, if_pos (show true = true from rfl),
    if_neg (show ¬ (false = true) by decide)] at hc
  exact Bow.q_ne hc

end Data

/-- **c-skog med to røtter.** -/
theorem twoRoot_not_identifiable (G : DAG V) (O : Finset V) (u1 u2 x w y : V)
    (h1x : G.edge u1 x) (h1w : G.edge u1 w) (h2w : G.edge u2 w) (h2y : G.edge u2 y)
    (hxy : G.edge x y) (h12 : u1 ≠ u2) (hxw : x ≠ w) (hwy : w ≠ y)
    (hu1 : u1 ∉ O) (hu2 : u2 ∉ O) (hx : x ∈ O) (hy : y ∈ O) (hw : w ∈ O) :
    ¬ Identifiable G (fun _ => Bool) O {x} {y, w} :=
  Data.not_ident ⟨u1, u2, x, w, y, h1x, h1w, h2w, h2y, hxy, h12,
    fun e => hu2 (e ▸ hx), hxw, hwy⟩ O hu1 hu2 hy hw hx

end TwoRoot
end Identification

#print axioms Identification.TwoRoot.twoRoot_not_identifiable
