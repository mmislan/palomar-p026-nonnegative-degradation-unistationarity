import proofs.MixedDegradation.TypeVReduced
import proofs.MixedDegradation.PassiveChain

namespace MixedDegradation.TypeV

/-- A Type V pair is either an identified endpoint or a literal reversible
unit path ending at a fork source with its own nonnegative loss. -/
inductive Sector where
  | collapsed
  | linked (chain : MixedDegradation.UnitChain) (loss : ℝ) (loss_nonneg : 0 ≤ loss)

def Sector.Aux : Sector → Type
  | .collapsed => PUnit
  | .linked q _ _ => ℝ × q.State

def Sector.tip : (q : Sector) → ℝ → q.Aux → ℝ
  | .collapsed, X, _ => X
  | .linked _ _ _, _, z => z.1

def Sector.current (q : Sector) (f g X P : ℝ) (z : q.Aux) : ℝ :=
  f * q.tip X z - g * P

/-- The full local species balances, including every internal chain species.
P is the product of the other two base concentrations and T their fork-current sum. -/
def Sector.Steady : (q : Sector) → ℝ → ℝ → ℝ → ℝ → ℝ → q.Aux → ℝ → Prop
  | .collapsed, f, g, d, X, P, z, T =>
      T - Sector.current .collapsed f g X P z - d * X = 0
  | .linked q loss hl, f, g, d, X, P, z, T =>
      ∃ jL jR, MixedDegradation.ChainFlux q z.2 X z.1 jL jR ∧
        jR - Sector.current (.linked q loss hl) f g X P z - loss * z.1 = 0 ∧
        T - jL - d * X = 0

structure Response where
  alpha : ℝ
  beta : ℝ
  lossLinear : ℝ
  lossProduct : ℝ
  tipLinear : ℝ
  tipProduct : ℝ
  beta_pos : 0 < beta
  lossLinear_nonneg : 0 ≤ lossLinear
  lossProduct_nonneg : 0 ≤ lossProduct

noncomputable def Sector.response (q : Sector) (f g d : ℝ)
    (hf : 0 < f) (hg : 0 < g) (hd : 0 ≤ d) : Response :=
  match q with
  | .collapsed => ⟨f,g,d,0,1,0,hg,hd,le_rfl⟩
  | .linked chain loss hl => by
      let s := chain.summary
      let H := loss + s.leakR
      let D := s.beta + f + H
      have hH : 0 ≤ H := add_nonneg hl s.leakR_nonneg
      have hD : 0 < D := add_pos_of_pos_of_nonneg (add_pos s.beta_pos hf) hH
      exact ⟨f*s.c/D, g*(s.beta+H)/D,
        d+s.leakL+H*s.c/D, H*g/D, s.c/D, g/D,
        div_pos (mul_pos hg (add_pos_of_pos_of_nonneg s.beta_pos hH)) hD,
        add_nonneg (add_nonneg hd s.leakL_nonneg)
          (div_nonneg (mul_nonneg hH s.c_pos.le) hD.le),
        div_nonneg (mul_nonneg hH hg.le) hD.le⟩

theorem Sector.reduce (q : Sector) (f g d : ℝ)
    (hf : 0 < f) (hg : 0 < g) (hd : 0 ≤ d)
    (X P T : ℝ) (z : q.Aux) (hz : q.Steady f g d X P z T) :
    let R := q.response f g d hf hg hd
    q.current f g X P z = R.alpha*X - R.beta*P ∧
    T - q.current f g X P z = R.lossLinear*X + R.lossProduct*P ∧
    q.tip X z = R.tipLinear*X + R.tipProduct*P := by
  cases q with
  | collapsed =>
      dsimp [response, current, tip, Steady] at hz ⊢
      constructor
      · rfl
      constructor
      · linarith
      · ring
  | linked chain loss hl =>
      rcases hz with ⟨jL,jR,hflux,hS,hU⟩
      obtain ⟨hL,hR⟩ := MixedDegradation.chain_flux_compress chain z.2 hflux
      let s := chain.summary
      let H := loss + s.leakR
      let D := s.beta + f + H
      have hH : 0 ≤ H := add_nonneg hl s.leakR_nonneg
      have hD : 0 < D := add_pos_of_pos_of_nonneg (add_pos s.beta_pos hf) hH
      have htip : z.1 = (s.c*X+g*P)/D := by
        apply (eq_div_iff (ne_of_gt hD)).2
        dsimp [current, tip] at hS
        rw [hR] at hS
        dsimp [D,H,s]
        linear_combination -hS
      have htotal : T - Sector.current (.linked chain loss hl) f g X P z =
          (d+s.leakL)*X + H*z.1 := by
        rw [hL] at hU
        rw [hR] at hS
        dsimp [H,s]
        linear_combination hU + hS
      change f*z.1-g*P = f*s.c/D*X - g*(s.beta+H)/D*P ∧
        T-(f*z.1-g*P) = (d+s.leakL+H*s.c/D)*X + H*g/D*P ∧
        z.1 = s.c/D*X + g/D*P
      constructor
      · rw [htip]
        field_simp [ne_of_gt hD]
        dsimp [D,H]
        ring
      constructor
      · change T-Sector.current (.linked chain loss hl) f g X P z = _
        rw [htotal,htip]
        field_simp [ne_of_gt hD]
        ring
      · rw [htip]
        ring

theorem Sector.aux_unique (q : Sector) (f g d : ℝ)
    (hf : 0 < f) (hg : 0 < g) (hd : 0 ≤ d)
    (X P T W : ℝ) (z w : q.Aux)
    (hz : q.Steady f g d X P z T) (hw : q.Steady f g d X P w W) : z = w := by
  have htip : q.tip X z = q.tip X w :=
    (q.reduce f g d hf hg hd X P T z hz).2.2.trans
      (q.reduce f g d hf hg hd X P W w hw).2.2.symm
  cases q with
  | collapsed => cases z; cases w; rfl
  | linked chain loss hl =>
      rcases z with ⟨Z,z⟩
      rcases w with ⟨W,w⟩
      change Z = W at htip
      subst W
      rcases hz with ⟨jL,jR,hz,_,_⟩
      rcases hw with ⟨kL,kR,hw,_,_⟩
      have heq := MixedDegradation.chain_state_unique chain z w hz hw
      cases heq
      rfl

structure Network where
  sector : Fin 3 → Sector
  forward : Fin 3 → ℝ
  reverse : Fin 3 → ℝ
  loss : Fin 3 → ℝ
  forward_pos : ∀ i, 0 < forward i
  reverse_pos : ∀ i, 0 < reverse i
  loss_nonneg : ∀ i, 0 ≤ loss i

@[ext] structure State (N : Network) where
  base : Fin 3 → ℝ
  aux : ∀ i, (N.sector i).Aux

def current (N : Network) (x : State N) (i : Fin 3) : ℝ :=
  (N.sector i).current (N.forward i) (N.reverse i) (x.base i)
    (x.base (i+1)*x.base (i+2)) (x.aux i)

def Stationary (N : Network) (x : State N) : Prop :=
  ∀ i, (N.sector i).Steady (N.forward i) (N.reverse i) (N.loss i)
    (x.base i) (x.base (i+1)*x.base (i+2)) (x.aux i)
    (current N x (i+1)+current N x (i+2))

noncomputable def response (N : Network) (i : Fin 3) : Response :=
  (N.sector i).response (N.forward i) (N.reverse i) (N.loss i)
    (N.forward_pos i) (N.reverse_pos i) (N.loss_nonneg i)

noncomputable def reducedParams (N : Network) : ReducedParams where
  a i := (response N i).alpha
  b i := (response N i).beta
  c i := (response N (i+1)).lossLinear/2
  d i := (response N (i+2)).lossLinear/2
  h i := (response N (i+1)).lossProduct/2
  k i := (response N (i+2)).lossProduct/2
  b_pos i := (response N i).beta_pos
  c_nonneg i := div_nonneg (response N (i+1)).lossLinear_nonneg (by norm_num)
  d_nonneg i := div_nonneg (response N (i+2)).lossLinear_nonneg (by norm_num)
  h_nonneg i := div_nonneg (response N (i+1)).lossProduct_nonneg (by norm_num)
  k_nonneg i := div_nonneg (response N (i+2)).lossProduct_nonneg (by norm_num)

private theorem idx11 (i : Fin 3) : i+1+1=i+2 := by fin_cases i <;> rfl
private theorem idx12 (i : Fin 3) : i+1+2=i := by fin_cases i <;> rfl
private theorem idx21 (i : Fin 3) : i+2+1=i := by fin_cases i <;> rfl
private theorem idx22 (i : Fin 3) : i+2+2=i+1 := by fin_cases i <;> rfl

theorem stationary_reduces (N : Network) (x : State N) (hx : Stationary N x) :
    ReducedStationary (reducedParams N) x.base := by
  have hred (i : Fin 3) := (N.sector i).reduce (N.forward i) (N.reverse i)
    (N.loss i) (N.forward_pos i) (N.reverse_pos i) (N.loss_nonneg i)
    (x.base i) (x.base (i+1)*x.base (i+2))
    (current N x (i+1)+current N x (i+2)) (x.aux i) (hx i)
  intro i
  have hi := (hred i).1
  have hj := (hred (i+1)).2.1
  have hk := (hred (i+2)).2.1
  change current N x i = (response N i).alpha*x.base i -
    (response N i).beta*(x.base (i+1)*x.base (i+2)) at hi
  change current N x (i+1+1)+current N x (i+1+2)-current N x (i+1) =
    (response N (i+1)).lossLinear*x.base (i+1) +
    (response N (i+1)).lossProduct*(x.base (i+1+1)*x.base (i+1+2)) at hj
  change current N x (i+2+1)+current N x (i+2+2)-current N x (i+2) =
    (response N (i+2)).lossLinear*x.base (i+2) +
    (response N (i+2)).lossProduct*(x.base (i+2+1)*x.base (i+2+2)) at hk
  rw [idx11,idx12] at hj
  rw [idx21,idx22] at hk
  change (response N i).alpha*x.base i =
    (response N i).beta*x.base (i+1)*x.base (i+2) +
    (response N (i+1)).lossLinear/2*x.base (i+1) +
    (response N (i+2)).lossLinear/2*x.base (i+2) +
    (response N (i+1)).lossProduct/2*x.base i*x.base (i+2) +
    (response N (i+2)).lossProduct/2*x.base i*x.base (i+1)
  linear_combination -hi + hj/2 + hk/2

/-- At most one literal stationary state with positive base concentrations,
for all eight pair identifications and arbitrary finite reversible unit paths.
Every endpoint and internal concentration is included in the equality. -/
theorem type_v_unistationarity (N : Network) (x y : State N)
    (hx : ∀ i, 0 < x.base i) (hy : ∀ i, 0 < y.base i)
    (hxs : Stationary N x) (hys : Stationary N y) : x = y := by
  have hb : x.base = y.base := reduced_unistationarity (reducedParams N)
    x.base y.base hx hy (stationary_reduces N x hxs) (stationary_reduces N y hys)
  apply State.ext hb
  funext i
  apply (N.sector i).aux_unique (N.forward i) (N.reverse i) (N.loss i)
    (N.forward_pos i) (N.reverse_pos i) (N.loss_nonneg i)
    (x.base i) (x.base (i+1)*x.base (i+2))
    (current N x (i+1)+current N x (i+2))
    (current N y (i+1)+current N y (i+2)) (x.aux i) (y.aux i)
  · exact hxs i
  · simpa only [hb] using hys i

def chainPositive : (q : MixedDegradation.UnitChain) → q.State → Prop
  | .direct _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _, z => chainPositive q z.1 ∧ 0 < z.2

def Sector.positiveAux : (q : Sector) → q.Aux → Prop
  | .collapsed, _ => True
  | .linked q _ _, z => 0 < z.1 ∧ chainPositive q z.2

/-- Strict positivity of every literal species, including source endpoints
and all internal path concentrations. Collapsed endpoints are counted once. -/
def PositiveState (N : Network) (x : State N) : Prop :=
  (∀ i, 0 < x.base i) ∧ ∀ i, (N.sector i).positiveAux (x.aux i)

/-- Source-normal Type V unistationarity with nonnegative degradation,
hence in particular with mixed support. The model contains the literal unit
paths and endpoint identifications of Theorem 3.1(v); no contracted equation,
determinant certificate, or continuation premise occurs in this interface. -/
theorem paper_type_v_unistationarity (N : Network) (x y : State N)
    (hx : PositiveState N x) (hy : PositiveState N y)
    (hxs : Stationary N x) (hys : Stationary N y) : x = y :=
  type_v_unistationarity N x y hx.1 hy.1 hxs hys

end MixedDegradation.TypeV
