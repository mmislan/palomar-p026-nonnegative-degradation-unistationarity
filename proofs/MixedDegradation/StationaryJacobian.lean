import Mathlib

namespace MixedDegradation
open scoped BigOperators Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scaled mass-action Jacobian expressed in stationary flows. All
degradation values occur algebraically, without division. -/
def scaledJacobian (N P : Matrix ι ι ℝ) (p q e : ι → ℝ) : Matrix ι ι ℝ :=
  N * Matrix.diagonal p - N * Matrix.diagonal q * P.transpose - Matrix.diagonal e

theorem scaledJacobian_stationary_identity
    (N : Matrix ι ι ℝ) (q J e : ι → ℝ) :
    scaledJacobian N (1 + N) (q + J) q e =
      -N * Matrix.diagonal q * N.transpose +
        N * Matrix.diagonal J - Matrix.diagonal e := by
  unfold scaledJacobian
  have hdiag : Matrix.diagonal (q + J) = Matrix.diagonal q + Matrix.diagonal J := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [hdiag, Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring

def stationaryB (V : Matrix ι ι ℝ) (J e : ι → ℝ) : Matrix ι ι ℝ :=
  (Matrix.diagonal J - V * Matrix.diagonal e) * V.transpose

theorem stationary_factorization
    (N V : Matrix ι ι ℝ) (hNV : N * V = 1) (q J e : ι → ℝ) :
    -scaledJacobian N (1 + N) (q + J) q e =
      N * (Matrix.diagonal q - stationaryB V J e) * N.transpose := by
  have ht : V.transpose * N.transpose = 1 := by
    rw [← Matrix.transpose_mul, hNV, Matrix.transpose_one]
  rw [scaledJacobian_stationary_identity]
  unfold stationaryB
  calc
    -(-N * Matrix.diagonal q * N.transpose + N * Matrix.diagonal J -
        Matrix.diagonal e) =
        N * Matrix.diagonal q * N.transpose - N * Matrix.diagonal J +
          Matrix.diagonal e := by noncomm_ring
    _ = N * Matrix.diagonal q * N.transpose -
        N * Matrix.diagonal J * (V.transpose * N.transpose) +
        (N * V) * Matrix.diagonal e * (V.transpose * N.transpose) := by
      rw [ht, hNV]
      simp
    _ = _ := by noncomm_ring

/-- The signed determinant transport. Stationarity identifies J with V e
when N is invertible; that substitution is kept separate from this algebra. -/
theorem stationary_signed_determinant
    (N V : Matrix ι ι ℝ) (hNV : N * V = 1) (q J e : ι → ℝ) :
    (-1 : ℝ) ^ Fintype.card ι *
        (scaledJacobian N (1 + N) (q + J) q e).det =
      N.det ^ 2 * (Matrix.diagonal q - stationaryB V J e).det := by
  rw [← Matrix.det_neg, stationary_factorization N V hNV q J e,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end MixedDegradation
