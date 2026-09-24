import Mathlib

namespace TypeII3

/-- Recursive geometric secant polynomial.  This indexing avoids truncated
natural-number subtraction in the formal factorization. -/
def secantPoly (r s : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => r ^ n + s * secantPoly r s n

theorem pow_sub_pow_eq_mul_secantPoly (r s : ℝ) (n : ℕ) :
    r ^ n - s ^ n = (r - s) * secantPoly r s n := by
  induction n with
  | zero => simp [secantPoly]
  | succ n ih =>
      simp only [secantPoly, pow_succ]
      linear_combination s * ih

theorem secantPoly_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    0 ≤ secantPoly r s n := by
  induction n with
  | zero => simp [secantPoly]
  | succ n ih =>
      simp only [secantPoly]
      exact add_nonneg (le_of_lt (pow_pos hr n)) (mul_nonneg (le_of_lt hs) ih)

theorem secantPoly_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {n : ℕ} (hn : 0 < n) : 0 < secantPoly r s n := by
  cases n with
  | zero => simp at hn
  | succ n =>
      simp only [secantPoly]
      have hpow : 0 < r ^ n := pow_pos hr n
      have htail : 0 ≤ s * secantPoly r s n :=
        mul_nonneg (le_of_lt hs) (secantPoly_nonneg hr hs n)
      linarith

end TypeII3
