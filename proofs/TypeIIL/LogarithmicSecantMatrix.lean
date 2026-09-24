import proofs.TypeIIL.LogarithmicSecant

namespace TypeIIL

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι]

/-- Product-complex ratio associated with a nonnegative integer product
stoichiometry matrix. -/
def monomialRatio (P : ι → κ → ℕ) (rho : ι → ℝ) (r : κ) : ℝ :=
  ∏ i, rho i ^ P i r

theorem monomialRatio_pos (P : ι → κ → ℕ) {rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (r : κ) :
    0 < monomialRatio P rho r := by
  unfold monomialRatio
  exact Finset.prod_pos fun i _ => pow_pos (hrho i) _

theorem log_monomialRatio (P : ι → κ → ℕ) {rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (r : κ) :
    Real.log (monomialRatio P rho r) =
      ∑ i, (P i r : ℝ) * Real.log (rho i) := by
  unfold monomialRatio
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    exact Real.log_pow (rho i) (P i r)
  · intro i _
    exact pow_ne_zero _ (hrho i).ne'

/-- The logarithmic two-point secant matrix.  It factors as a positive row
diagonal, the transpose product stoichiometry, and a positive column diagonal. -/
noncomputable def logarithmicSecantMatrix
    (P : ι → κ → ℕ) (rho : ι → ℝ) : κ → ι → ℝ :=
  fun r i => logSecant (monomialRatio P rho r) * (P i r : ℝ) /
    logSecant (rho i)

theorem logarithmicSecantMatrix_nonneg
    (P : ι → κ → ℕ) {rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (r : κ) (i : ι) :
    0 ≤ logarithmicSecantMatrix P rho r i := by
  unfold logarithmicSecantMatrix
  exact div_nonneg
    (mul_nonneg (le_of_lt (logSecant_pos (monomialRatio_pos P hrho r)))
      (Nat.cast_nonneg _))
    (le_of_lt (logSecant_pos (hrho i)))

theorem div_logSecant_mul_sub_one {x : ℝ} (hx : 0 < x) :
    (x - 1) / logSecant x = Real.log x := by
  have hL : logSecant x ≠ 0 := ne_of_gt (logSecant_pos hx)
  apply (div_eq_iff hL).2
  simpa [mul_comm] using (logSecant_mul_log hx).symm

/-- Matrix-level exact secant identity.  This is the source-faithful
replacement for coordinate-order-dependent telescoping coefficients. -/
theorem logarithmicSecantMatrix_mul_ratio_sub_one
    (P : ι → κ → ℕ) {rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (r : κ) :
    ∑ i, logarithmicSecantMatrix P rho r i * (rho i - 1) =
      monomialRatio P rho r - 1 := by
  have hmon : 0 < monomialRatio P rho r := monomialRatio_pos P hrho r
  calc
    ∑ i, logarithmicSecantMatrix P rho r i * (rho i - 1) =
        logSecant (monomialRatio P rho r) *
          ∑ i, (P i r : ℝ) * Real.log (rho i) := by
      unfold logarithmicSecantMatrix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        logSecant (monomialRatio P rho r) * (P i r : ℝ) /
              logSecant (rho i) * (rho i - 1) =
            logSecant (monomialRatio P rho r) * (P i r : ℝ) *
              ((rho i - 1) / logSecant (rho i)) := by ring
        _ = logSecant (monomialRatio P rho r) *
              ((P i r : ℝ) * Real.log (rho i)) := by
            rw [div_logSecant_mul_sub_one (hrho i)]
            ring
    _ = logSecant (monomialRatio P rho r) *
          Real.log (monomialRatio P rho r) := by
      rw [log_monomialRatio P hrho r]
    _ = monomialRatio P rho r - 1 := logSecant_mul_log hmon

end TypeIIL
