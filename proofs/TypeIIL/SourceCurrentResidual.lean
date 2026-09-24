import proofs.TypeIIL.GenericCurrentSecantKernel
import proofs.TypeIIL.SourceOrderedProduct

namespace TypeIIL

open scoped BigOperators

/-- Every literal weighted source row acts nonnegatively on the positive base
current.  Unit nonfork rows may attain zero; a fork or a nonfork weight above
one supplies strict gain. -/
theorem source_ordered_current_base_residual_nonneg
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (N : Matrix (Fin n) (Fin n) ℝ)
    {p q e rho : Fin n → ℝ}
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (hrho : ∀ i, 0 < rho i) (hq : ∀ r, 0 ≤ q r)
    (hweight : ∀ r, 0 < weight r)
    (hbackDistinct : ∀ r z, back r = some z → z ≠ next r)
    (r : Fin n) :
    0 ≤ ∑ k,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            N p q e r k * (p k - q k) := by
  rw [currentSecantKernelMatrixWith_mul_baseCurrent
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho) N he hbase r]
  apply mul_nonneg (hq r)
  apply sub_nonneg.mpr
  cases h : back r with
  | none =>
      exact one_le_source_nonfork_ordered_row_sum next weight back hrho h
        (hweight r)
  | some z =>
      exact le_of_lt (one_lt_source_fork_ordered_row_sum next weight back hrho
        h (hweight r) (hbackDistinct r z h))

/-- Fork rows have a strictly positive source residual because the product
contains both a positive successor power and the coefficient-one back target. -/
theorem source_ordered_current_fork_base_residual_pos
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (N : Matrix (Fin n) (Fin n) ℝ)
    {p q e rho : Fin n → ℝ}
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (hrho : ∀ i, 0 < rho i) (hq : ∀ r, 0 < q r)
    {r z : Fin n} (hr : back r = some z)
    (hw : 0 < weight r) (hz : z ≠ next r) :
    0 < ∑ k,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            N p q e r k * (p k - q k) := by
  rw [currentSecantKernelMatrixWith_mul_baseCurrent
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho) N he hbase r]
  exact mul_pos (hq r) (sub_pos.mpr
    (one_lt_source_fork_ordered_row_sum next weight back hrho hr hw hz))

end TypeIIL
