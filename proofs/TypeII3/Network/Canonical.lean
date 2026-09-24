import Mathlib

namespace TypeII3

structure ArcRates where
  c : ℝ
  beta : ℝ
  gamma : ℝ
  eta : ℝ
  dR : ℝ
  dP : ℝ
  dQ : ℝ
  c_pos : 0 < c
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma
  eta_pos : 0 < eta
  dR_pos : 0 < dR
  dP_pos : 0 < dP
  dQ_pos : 0 < dQ

structure ForkRates where
  plus : ℝ
  minus : ℝ
  m : ℕ
  plus_pos : 0 < plus
  minus_pos : 0 < minus
  m_pos : 0 < m

structure CanonicalParams where
  arc0 : ArcRates
  arc1 : ArcRates
  arc2 : ArcRates
  fork0 : ForkRates
  fork1 : ForkRates
  fork2 : ForkRates

@[ext] structure CanonicalState where
  P0 : ℝ
  Q0 : ℝ
  R0 : ℝ
  P1 : ℝ
  Q1 : ℝ
  R1 : ℝ
  P2 : ℝ
  Q2 : ℝ
  R2 : ℝ

def PositiveCanonicalState (x : CanonicalState) : Prop :=
  0 < x.P0 ∧ 0 < x.Q0 ∧ 0 < x.R0 ∧
  0 < x.P1 ∧ 0 < x.Q1 ∧ 0 < x.R1 ∧
  0 < x.P2 ∧ 0 < x.Q2 ∧ 0 < x.R2

def forkCurrent (f : ForkRates) (Q P R : ℝ) : ℝ :=
  f.plus * Q - f.minus * P * R ^ f.m

def ArcSteady (a : ArcRates) (m : ℕ)
    (delta deltaNext R P Q : ℝ) : Prop :=
  m * delta - (a.c + a.dR) * R + a.beta * P = 0 ∧
  a.c * R - (a.beta + a.gamma + a.dP) * P + a.eta * Q + deltaNext = 0 ∧
  a.gamma * P - (a.eta + a.dQ) * Q - deltaNext = 0

/-- `arc0` is the sector `(R2,P0,Q0)`, then indices rotate. -/
def IsCanonicalStationary (p : CanonicalParams) (x : CanonicalState) : Prop :=
  let d0 := forkCurrent p.fork0 x.Q0 x.P0 x.R0
  let d1 := forkCurrent p.fork1 x.Q1 x.P1 x.R1
  let d2 := forkCurrent p.fork2 x.Q2 x.P2 x.R2
  ArcSteady p.arc0 p.fork2.m d2 d0 x.R2 x.P0 x.Q0 ∧
  ArcSteady p.arc1 p.fork0.m d0 d1 x.R0 x.P1 x.Q1 ∧
  ArcSteady p.arc2 p.fork1.m d1 d2 x.R1 x.P2 x.Q2

end TypeII3
