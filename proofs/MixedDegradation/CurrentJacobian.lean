import proofs.MixedDegradation.StationaryJacobian
import proofs.TypeIIL.GenericCurrentSecantKernel

namespace MixedDegradation
open TypeIIL
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem current_kernel_matrix_factor
    (C N : Matrix ι ι ℝ) (p q e : ι → ℝ) :
    currentSecantKernelMatrixWith C N p q e =
      1 - (Matrix.diagonal p - Matrix.diagonal q * C) *
        Matrix.diagonal (fun i => (e i)⁻¹) * N := by
  let R := Matrix.diagonal p - Matrix.diagonal q * C
  let D := Matrix.diagonal (fun i => (e i)⁻¹)
  have hentry : ∀ r i, (R * D) r i = currentResponseCoeffWith C p q r i / e i := by
    intro r i
    change ((Matrix.diagonal p - Matrix.diagonal q * C) *
      Matrix.diagonal (fun i => (e i)⁻¹)) r i = _
    rw [Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
    simp [Matrix.diagonal,currentResponseCoeffWith,div_eq_mul_inv]
  ext r k
  change (if r=k then 1 else 0) -
      ∑ i, currentResponseCoeffWith C p q r i / e i * N i k =
    (if r=k then 1 else 0) - ∑ i, (R*D) r i * N i k
  simp_rw [hentry]

/-- Positive-loss current-kernel exclusion supplies stationary Jacobian
nondegeneracy. This is purely a change of coordinates, not a second-root argument. -/
theorem scaledJacobian_nonsingular_of_current_kernel
    (N P : Matrix ι ι ℝ) (p q e : ι → ℝ)
    (he : ∀ i, e i ≠ 0)
    (hker : (currentSecantKernelMatrixWith P.transpose N p q e).det ≠ 0) :
    (scaledJacobian N P p q e).det ≠ 0 := by
  let R := Matrix.diagonal p - Matrix.diagonal q * P.transpose
  let E := Matrix.diagonal e
  let D := Matrix.diagonal (fun i => (e i)⁻¹)
  have hED : E * D = 1 := by
    change Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    simp [he]
  have hfactor : 1 - N*(R*D) = (E-N*R)*D := by
    calc
      1 - N*(R*D) = E*D - (N*R)*D := by rw [hED]; noncomm_ring
      _ = (E-N*R)*D := (sub_mul E (N*R) D).symm
  have hneg : E-N*R = -scaledJacobian N P p q e := by
    dsimp [E,R,scaledJacobian]
    noncomm_ring
  intro hz
  apply hker
  rw [current_kernel_matrix_factor]
  change (1-(R*D)*N).det = 0
  rw [Matrix.det_one_sub_mul_comm,hfactor,Matrix.det_mul,hneg,Matrix.det_neg,hz]
  simp

end MixedDegradation
