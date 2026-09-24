import proofs.TypeIIL.GenericCurrentSecantKernel
import proofs.TypeIIL.OrderedMonomialSecantMatrix

namespace TypeIIL

open scoped BigOperators

/-- Exact nonlinear-to-linear current-kernel equation using the canonical
coordinate-ordered telescoping secant.  This is the representation whose
source Schur complement has the one-wrap sign pattern. -/
theorem ordered_current_secant_kernel_row
    {n : ℕ} (P : Fin n → Fin n → ℕ) (N : Matrix (Fin n) (Fin n) ℝ)
    {p q e rho : Fin n → ℝ}
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ r, N i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, N i r *
        (rho r * p r - monomialRatio P rho r * q r) = rho i * e i)
    (r : Fin n) :
    ∑ k,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix P rho) N p q e r k *
          twoRootCurrentDelta P p q rho k = 0 := by
  apply current_secant_kernel_row_with P
    (orderedMonomialSecantMatrix P rho) N
  · intro row
    exact orderedMonomialSecantMatrix_mul_ratio_sub_one P row
  · exact he
  · exact hbase
  · exact hratio

/-- Source-shaped strict base-current certificate for the ordered kernel.
Each product row has a first positive exponent `a r`, no earlier support,
and a distinct later positive exponent `b r`. -/
theorem ordered_current_kernel_baseCurrent_pos_of_two_support
    {n : ℕ} (P : Fin n → Fin n → ℕ) (N : Matrix (Fin n) (Fin n) ℝ)
    {p q e rho : Fin n → ℝ}
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (hrho : ∀ i, 0 < rho i) (hq : ∀ r, 0 < q r)
    (a b : Fin n → Fin n)
    (hab : ∀ r, a r ≠ b r)
    (hbefore : ∀ r j, j.val < (a r).val → P j r = 0)
    (ha : ∀ r, 0 < P (a r) r)
    (hb : ∀ r, 0 < P (b r) r)
    (r : Fin n) :
    0 < ∑ k,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix P rho) N p q e r k *
          (p k - q k) := by
  apply currentSecantKernelMatrixWith_mul_baseCurrent_pos
    (orderedMonomialSecantMatrix P rho) N he hbase hq
  intro row
  exact one_lt_orderedMonomialSecantMatrix_row_sum_of_two_support
    P hrho row (a row) (b row) (hab row) (hbefore row) (ha row) (hb row)

end TypeIIL
