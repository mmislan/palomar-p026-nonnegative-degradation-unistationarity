import proofs.TypeIIL.LogarithmicSecantMatrix

namespace TypeIIL

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Difference of a reversible reaction current between two states, written
using one-way flows at the base state and the concentration ratio. -/
noncomputable def twoRootCurrentDelta
    (P : ι → ι → ℕ) (p q rho : ι → ℝ) (r : ι) : ℝ :=
  p r * (rho r - 1) - q r * (monomialRatio P rho r - 1)

/-- Exact linear response of reaction `r` to the species ratio differences. -/
noncomputable def currentResponseCoeff
    (P : ι → ι → ℕ) (p q rho : ι → ℝ) (r i : ι) : ℝ :=
  (if r = i then p r else 0) -
    q r * logarithmicSecantMatrix P rho r i

/-- Current-coordinate two-root kernel matrix. -/
noncomputable def currentSecantKernelMatrix
    (P : ι → ι → ℕ) (N : Matrix ι ι ℝ)
    (p q e rho : ι → ℝ) : Matrix ι ι ℝ :=
  fun r k => (if r = k then 1 else 0) -
    ∑ i, currentResponseCoeff P p q rho r i / e i * N i k

theorem twoRootCurrentDelta_response
    (P : ι → ι → ℕ) {p q rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (r : ι) :
    twoRootCurrentDelta P p q rho r =
      ∑ i, currentResponseCoeff P p q rho r i * (rho i - 1) := by
  unfold twoRootCurrentDelta
  rw [show monomialRatio P rho r - 1 =
      ∑ i, logarithmicSecantMatrix P rho r i * (rho i - 1) by
    symm
    exact logarithmicSecantMatrix_mul_ratio_sub_one P hrho r]
  unfold currentResponseCoeff
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i, (if r = i then p r else 0) * (rho i - 1)) =
      p r * (rho r - 1) by simp]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Subtracting two source stationary systems and eliminating the species
ratio differences puts the reaction-current difference in the exact current
secant kernel. -/
theorem current_secant_kernel_row
    (P : ι → ι → ℕ) (N : Matrix ι ι ℝ)
    {p q e rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i) (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ r, N i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, N i r *
        (rho r * p r - monomialRatio P rho r * q r) = rho i * e i)
    (r : ι) :
    ∑ k, currentSecantKernelMatrix P N p q e rho r k *
        twoRootCurrentDelta P p q rho k = 0 := by
  have hdelta : ∀ i,
      ∑ k, N i k * twoRootCurrentDelta P p q rho k =
        e i * (rho i - 1) := by
    intro i
    calc
      ∑ k, N i k * twoRootCurrentDelta P p q rho k =
          (∑ k, N i k *
            (rho k * p k - monomialRatio P rho k * q k)) -
            ∑ k, N i k * (p k - q k) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        unfold twoRootCurrentDelta
        ring
      _ = rho i * e i - e i := by rw [hratio i, hbase i]
      _ = e i * (rho i - 1) := by ring
  have hratioDifference : ∀ i,
      rho i - 1 =
        (∑ k, N i k * twoRootCurrentDelta P p q rho k) / e i := by
    intro i
    apply (eq_div_iff (he i)).2
    rw [hdelta i]
    ring
  have hdouble :
      ∑ k, (∑ i, currentResponseCoeff P p q rho r i / e i * N i k) *
          twoRootCurrentDelta P p q rho k =
        ∑ i, currentResponseCoeff P p q rho r i / e i *
          (∑ k, N i k * twoRootCurrentDelta P p q rho k) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    ∑ k, currentSecantKernelMatrix P N p q e rho r k *
          twoRootCurrentDelta P p q rho k =
        twoRootCurrentDelta P p q rho r -
          ∑ i, currentResponseCoeff P p q rho r i / e i *
            (∑ k, N i k * twoRootCurrentDelta P p q rho k) := by
      unfold currentSecantKernelMatrix
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul]
      rw [hdouble]
      simp
    _ = twoRootCurrentDelta P p q rho r -
          ∑ i, currentResponseCoeff P p q rho r i * (rho i - 1) := by
      apply congrArg (twoRootCurrentDelta P p q rho r - ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [hratioDifference i]
      ring
    _ = 0 := by
      rw [← twoRootCurrentDelta_response P hrho r]
      ring

/-- Once the two-root current difference vanishes, the stationary balance
difference and nonzero degradation force every concentration ratio to be one.
This is the final generic reconstruction step after current-kernel exclusion. -/
theorem ratios_eq_one_of_twoRootCurrentDelta_eq_zero
    {κ : Type*} [Fintype κ]
    (P : κ → κ → ℕ) (N : Matrix κ κ ℝ)
    {p q e rho : κ → ℝ}
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ r, N i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, N i r *
        (rho r * p r - monomialRatio P rho r * q r) = rho i * e i)
    (hdelta : ∀ r, twoRootCurrentDelta P p q rho r = 0) :
    ∀ i, rho i = 1 := by
  intro i
  have hbalance :
      ∑ r, N i r * twoRootCurrentDelta P p q rho r =
        e i * (rho i - 1) := by
    calc
      ∑ r, N i r * twoRootCurrentDelta P p q rho r =
          (∑ r, N i r *
            (rho r * p r - monomialRatio P rho r * q r)) -
            ∑ r, N i r * (p r - q r) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _
        unfold twoRootCurrentDelta
        ring
      _ = rho i * e i - e i := by rw [hratio i, hbase i]
      _ = e i * (rho i - 1) := by ring
  have hzero : e i * (rho i - 1) = 0 := by
    have hsumzero :
        ∑ r, N i r * twoRootCurrentDelta P p q rho r = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [hdelta r, mul_zero]
    exact hbalance.symm.trans hsumzero
  have hz : rho i - 1 = 0 := (mul_eq_zero.mp hzero).resolve_left (he i)
  linarith

/-- The secant matrix has an explicit action on the positive base-current
vector.  For a source balance `N (p-q)=e`, the result in reaction row `r` is
`q_r` times the excess of the product-monomial secant row sum over one. -/
theorem currentSecantKernelMatrix_mul_baseCurrent
    (P : ι → ι → ℕ) (N : Matrix ι ι ℝ)
    {p q e rho : ι → ℝ} (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (r : ι) :
    ∑ k, currentSecantKernelMatrix P N p q e rho r k * (p k - q k) =
      q r * (∑ i, logarithmicSecantMatrix P rho r i - 1) := by
  have hdouble :
      ∑ k, (∑ i, currentResponseCoeff P p q rho r i / e i * N i k) *
          (p k - q k) =
        ∑ i, currentResponseCoeff P p q rho r i / e i *
          (∑ k, N i k * (p k - q k)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    ∑ k, currentSecantKernelMatrix P N p q e rho r k * (p k - q k) =
        (p r - q r) -
          ∑ i, currentResponseCoeff P p q rho r i / e i *
            (∑ k, N i k * (p k - q k)) := by
      unfold currentSecantKernelMatrix
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul]
      rw [hdouble]
      simp
    _ = (p r - q r) - ∑ i, currentResponseCoeff P p q rho r i := by
      apply congrArg ((p r - q r) - ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [hbase i]
      field_simp [he i]
    _ = q r * (∑ i, logarithmicSecantMatrix P rho r i - 1) := by
      unfold currentResponseCoeff
      rw [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      simp
      ring

/-- A product row with strict logarithmic-secant gain acts positively on the
positive base-current vector. -/
theorem currentSecantKernelMatrix_mul_baseCurrent_pos
    (P : ι → ι → ℕ) (N : Matrix ι ι ℝ)
    {p q e rho : ι → ℝ} (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (r : ι) (hq : 0 < q r)
    (hrow : 1 < ∑ i, logarithmicSecantMatrix P rho r i) :
    0 < ∑ k, currentSecantKernelMatrix P N p q e rho r k *
      (p k - q k) := by
  rw [currentSecantKernelMatrix_mul_baseCurrent P N he hbase r]
  exact mul_pos hq (sub_pos.mpr hrow)

end TypeIIL
