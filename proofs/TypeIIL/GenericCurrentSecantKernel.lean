import proofs.TypeIIL.CurrentSecantKernel

namespace TypeIIL

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Current response for any exact positive monomial secant representation. -/
noncomputable def currentResponseCoeffWith
    (C : Matrix ι ι ℝ) (p q : ι → ℝ) (r i : ι) : ℝ :=
  (if r = i then p r else 0) - q r * C r i

noncomputable def currentSecantKernelMatrixWith
    (C : Matrix ι ι ℝ) (N : Matrix ι ι ℝ)
    (p q e : ι → ℝ) : Matrix ι ι ℝ :=
  fun r k => (if r = k then 1 else 0) -
    ∑ i, currentResponseCoeffWith C p q r i / e i * N i k

theorem twoRootCurrentDelta_response_with
    (P : ι → ι → ℕ) (C : Matrix ι ι ℝ) {p q rho : ι → ℝ}
    (hsecant : ∀ r, ∑ i, C r i * (rho i - 1) =
      monomialRatio P rho r - 1) (r : ι) :
    twoRootCurrentDelta P p q rho r =
      ∑ i, currentResponseCoeffWith C p q r i * (rho i - 1) := by
  unfold twoRootCurrentDelta
  rw [← hsecant r]
  unfold currentResponseCoeffWith
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i, (if r = i then p r else 0) * (rho i - 1)) =
      p r * (rho r - 1) by simp]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Generic exact nonlinear-to-current-kernel adapter. -/
theorem current_secant_kernel_row_with
    (P : ι → ι → ℕ) (C : Matrix ι ι ℝ) (N : Matrix ι ι ℝ)
    {p q e rho : ι → ℝ}
    (hsecant : ∀ r, ∑ i, C r i * (rho i - 1) =
      monomialRatio P rho r - 1)
    (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ r, N i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, N i r *
        (rho r * p r - monomialRatio P rho r * q r) = rho i * e i)
    (r : ι) :
    ∑ k, currentSecantKernelMatrixWith C N p q e r k *
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
      ∑ k, (∑ i, currentResponseCoeffWith C p q r i / e i * N i k) *
          twoRootCurrentDelta P p q rho k =
        ∑ i, currentResponseCoeffWith C p q r i / e i *
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
    ∑ k, currentSecantKernelMatrixWith C N p q e r k *
          twoRootCurrentDelta P p q rho k =
        twoRootCurrentDelta P p q rho r -
          ∑ i, currentResponseCoeffWith C p q r i / e i *
            (∑ k, N i k * twoRootCurrentDelta P p q rho k) := by
      unfold currentSecantKernelMatrixWith
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul]
      rw [hdouble]
      simp
    _ = twoRootCurrentDelta P p q rho r -
          ∑ i, currentResponseCoeffWith C p q r i * (rho i - 1) := by
      apply congrArg (twoRootCurrentDelta P p q rho r - ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [hratioDifference i]
      ring
    _ = 0 := by
      rw [← twoRootCurrentDelta_response_with P C hsecant r]
      ring

/-- The base-current action depends only on the chosen secant row sum. -/
theorem currentSecantKernelMatrixWith_mul_baseCurrent
    (C : Matrix ι ι ℝ) (N : Matrix ι ι ℝ)
    {p q e : ι → ℝ} (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (r : ι) :
    ∑ k, currentSecantKernelMatrixWith C N p q e r k * (p k - q k) =
      q r * (∑ i, C r i - 1) := by
  have hdouble :
      ∑ k, (∑ i, currentResponseCoeffWith C p q r i / e i * N i k) *
          (p k - q k) =
        ∑ i, currentResponseCoeffWith C p q r i / e i *
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
    ∑ k, currentSecantKernelMatrixWith C N p q e r k * (p k - q k) =
        (p r - q r) -
          ∑ i, currentResponseCoeffWith C p q r i / e i *
            (∑ k, N i k * (p k - q k)) := by
      unfold currentSecantKernelMatrixWith
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul]
      rw [hdouble]
      simp
    _ = (p r - q r) - ∑ i, currentResponseCoeffWith C p q r i := by
      apply congrArg ((p r - q r) - ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [hbase i]
      field_simp [he i]
    _ = q r * (∑ i, C r i - 1) := by
      unfold currentResponseCoeffWith
      rw [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      simp
      ring

/-- A positive base current and a secant row of gain greater than one give a
strictly positive row action for the generic current kernel. -/
theorem currentSecantKernelMatrixWith_mul_baseCurrent_pos
    (C : Matrix ι ι ℝ) (N : Matrix ι ι ℝ)
    {p q e : ι → ℝ} (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (hq : ∀ r, 0 < q r) (hgain : ∀ r, 1 < ∑ i, C r i)
    (r : ι) :
    0 < ∑ k, currentSecantKernelMatrixWith C N p q e r k *
        (p k - q k) := by
  rw [currentSecantKernelMatrixWith_mul_baseCurrent C N he hbase r]
  exact mul_pos (hq r) (sub_pos.mpr (hgain r))

/-- Weak form used on nonfork source rows; unit product molecularity gives
equality, while larger nonfork weights give a strict residual. -/
theorem currentSecantKernelMatrixWith_mul_baseCurrent_nonneg
    (C : Matrix ι ι ℝ) (N : Matrix ι ι ℝ)
    {p q e : ι → ℝ} (he : ∀ i, e i ≠ 0)
    (hbase : ∀ i, ∑ k, N i k * (p k - q k) = e i)
    (hq : ∀ r, 0 ≤ q r) (hgain : ∀ r, 1 ≤ ∑ i, C r i)
    (r : ι) :
    0 ≤ ∑ k, currentSecantKernelMatrixWith C N p q e r k *
        (p k - q k) := by
  rw [currentSecantKernelMatrixWith_mul_baseCurrent C N he hbase r]
  exact mul_nonneg (hq r) (sub_nonneg.mpr (hgain r))

end TypeIIL
