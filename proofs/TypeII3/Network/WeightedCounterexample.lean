import Mathlib
import proofs.TypeII3.Network.TwoRootKernel

namespace TypeII3

/-- Stoichiometric matrix of a six-species Type-II-shaped network with gap word
`111` and cycle weights `(2,2,1,3,1,3)`.  It is not a minimal autocatalytic
core; `SourceMembership.lean` records the proper-core obstruction.  Its fork columns are
`X0 -> 2 X1 + X5`, `X2 -> X3 + X1`, and `X4 -> X5 + X3`. -/
def weightedCounterexampleN : Fin 6 → Fin 6 → ℝ := ![
  ![-1, 0, 0, 0, 0, 3],
  ![ 2,-1, 1, 0, 0, 0],
  ![ 0, 2,-1, 0, 0, 0],
  ![ 0, 0, 1,-1, 1, 0],
  ![ 0, 0, 0, 3,-1, 0],
  ![ 1, 0, 0, 0, 1,-1]]

def weightedCounterexampleReactant (r : Fin 6) (z : Fin 6 → ℝ) : ℝ := z r

def weightedCounterexampleProduct (r : Fin 6) (z : Fin 6 → ℝ) : ℝ :=
  ![z 1 ^ 2 * z 5, z 2 ^ 2, z 3 * z 1,
    z 4 ^ 3, z 5 * z 3, z 0 ^ 3] r

def weightedCounterexampleY : Fin 6 → ℝ := fun _ => 1

noncomputable def weightedCounterexampleX : Fin 6 → ℝ :=
  fun i => match i.1 with
    | 0 => (31 : ℝ) / 50
    | 1 => (57 : ℝ) / 50
    | 2 => (22 : ℝ) / 25
    | 3 => (3 : ℝ) / 5
    | 4 => (14 : ℝ) / 25
    | _ => (3 : ℝ) / 5

@[simp] theorem weightedCounterexampleX_zero :
    weightedCounterexampleX 0 = (31 : ℝ) / 50 := rfl
@[simp] theorem weightedCounterexampleX_one :
    weightedCounterexampleX 1 = (57 : ℝ) / 50 := rfl
@[simp] theorem weightedCounterexampleX_two :
    weightedCounterexampleX 2 = (22 : ℝ) / 25 := rfl
@[simp] theorem weightedCounterexampleX_three :
    weightedCounterexampleX 3 = (3 : ℝ) / 5 := rfl
@[simp] theorem weightedCounterexampleX_four :
    weightedCounterexampleX 4 = (14 : ℝ) / 25 := rfl
@[simp] theorem weightedCounterexampleX_five :
    weightedCounterexampleX 5 = (3 : ℝ) / 5 := rfl

def weightedCounterexampleP : Fin 6 → ℝ := ![
  704180941994460, 619799798320080, 1064148026967810,
  1379889114510795, 5001118197194658, 1928841702241720]

def weightedCounterexampleQ : Fin 6 → ℝ := ![
  18981846318750, 1952234297034000, 3747998870714400,
  18981846318750, 937378238937273, 98424792637500]

def weightedCounterexampleE : Fin 6 → ℝ := ![
  4806051633136950, 18981846318750, 18981846318750,
  18981846318750, 18981846318750, 2918522144328875]

/-- Exact multistationarity benchmark for the broader nonminimal
Type-II-shaped class.  The displayed strictly positive common rates and
degradations make both the all-one state and the distinct rational state
stationary.  This theorem does not refute source-core unistationarity. -/
theorem weighted_typeII3_multistationary :
    (∀ i, 0 < weightedCounterexampleX i) ∧
    (∀ i, 0 < weightedCounterexampleY i) ∧
    (∀ r, 0 < weightedCounterexampleP r) ∧
    (∀ r, 0 < weightedCounterexampleQ r) ∧
    (∀ i, 0 < weightedCounterexampleE i) ∧
    FluxStationary weightedCounterexampleN weightedCounterexampleReactant
      weightedCounterexampleProduct weightedCounterexampleP weightedCounterexampleQ
      weightedCounterexampleE (fun z i => z i) weightedCounterexampleY ∧
    FluxStationary weightedCounterexampleN weightedCounterexampleReactant
      weightedCounterexampleProduct weightedCounterexampleP weightedCounterexampleQ
      weightedCounterexampleE (fun z i => z i) weightedCounterexampleX ∧
    weightedCounterexampleX ≠ weightedCounterexampleY := by
  constructor
  · intro i
    fin_cases i <;> norm_num [weightedCounterexampleX]
  constructor
  · intro i
    fin_cases i <;> norm_num [weightedCounterexampleY]
  constructor
  · intro r
    fin_cases r <;> norm_num [weightedCounterexampleP]
  constructor
  · intro r
    fin_cases r <;> norm_num [weightedCounterexampleQ]
  constructor
  · intro i
    fin_cases i <;> norm_num [weightedCounterexampleE]
  constructor
  · intro i
    fin_cases i <;>
      norm_num [FluxStationary, weightedCounterexampleN,
        weightedCounterexampleReactant, weightedCounterexampleProduct,
        weightedCounterexampleP, weightedCounterexampleQ,
        weightedCounterexampleE, weightedCounterexampleY, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
  constructor
  · intro i
    fin_cases i <;>
      norm_num [FluxStationary, weightedCounterexampleN,
        weightedCounterexampleReactant, weightedCounterexampleProduct,
        weightedCounterexampleP, weightedCounterexampleQ,
        weightedCounterexampleE, weightedCounterexampleX, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
  · intro h
    have h0 := congrFun h 0
    norm_num [weightedCounterexampleX, weightedCounterexampleY] at h0

end TypeII3
