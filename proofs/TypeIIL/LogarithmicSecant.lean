import Mathlib

namespace TypeIIL

/-- The logarithmic mean of `x` and `1`, continuously completed at `x = 1`.
It is the positive diagonal factor which changes concentration differences
into log-concentration differences. -/
noncomputable def logSecant (x : ℝ) : ℝ :=
  if x = 1 then 1 else (x - 1) / Real.log x

theorem logSecant_mul_log {x : ℝ} (hx : 0 < x) :
    logSecant x * Real.log x = x - 1 := by
  by_cases h : x = 1
  · simp [logSecant, h]
  · rw [logSecant, ite_eq_right h]
    have hlog : Real.log x ≠ 0 := by
      intro hz
      exact h (Real.eq_one_of_pos_of_log_eq_zero hx hz)
    field_simp

theorem logSecant_pos {x : ℝ} (hx : 0 < x) : 0 < logSecant x := by
  by_cases h : x = 1
  · simp [logSecant, h]
  · rw [logSecant, ite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hlt) (Real.log_neg hx hlt)
    · exact div_pos (sub_pos.mpr hgt) (Real.log_pos hgt)

theorem positive_ratio_log_ne_zero {x : ℝ} (hx : 0 < x) (h : x ≠ 1) :
    Real.log x ≠ 0 := by
  intro hz
  exact h (Real.eq_one_of_pos_of_log_eq_zero hx hz)

/-- Exact logarithmic secant for a weighted product.  Unlike a coordinatewise
telescoping secant, this exposes a single positive row factor and the linear
stoichiometric action on log-ratios. -/
theorem weighted_fork_log_secant
    {P R : ℝ} (hP : 0 < P) (hR : 0 < R) (m : ℕ) :
    P * R ^ m - 1 =
      logSecant (P * R ^ m) *
        (Real.log P + (m : ℝ) * Real.log R) := by
  have hprod : 0 < P * R ^ m := mul_pos hP (pow_pos hR m)
  rw [← Real.log_pow]
  rw [← Real.log_mul hP.ne' (pow_ne_zero m hR.ne')]
  symm
  exact logSecant_mul_log hprod

/-- The one-product specialization used on every weighted nonfork step. -/
theorem weighted_edge_log_secant {R : ℝ} (hR : 0 < R) (m : ℕ) :
    R ^ m - 1 =
      logSecant (R ^ m) * ((m : ℝ) * Real.log R) := by
  have hpow : 0 < R ^ m := pow_pos hR m
  rw [← Real.log_pow]
  symm
  exact logSecant_mul_log hpow

end TypeIIL
