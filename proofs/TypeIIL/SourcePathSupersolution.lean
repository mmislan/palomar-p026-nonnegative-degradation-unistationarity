import Mathlib

namespace TypeIIL

/-- Interior cancellation for the cumulative stoichiometric scaling.  The
source tridiagonal row has diagonal `1+A+c*sNext`, predecessor magnitude
`A*sPrev`, and successor magnitude `c`.  Scaling consecutive coordinates by
the intervening source weights cancels both transport terms and leaves the
strict margin `w`. -/
theorem source_path_interior_scaling
    {A c sPrev sNext wPrev w wNext : ℝ}
    (hprev : w = sPrev * wPrev) (hnext : wNext = sNext * w) :
    (1 + A + c * sNext) * w - (A * sPrev) * wPrev - c * wNext = w := by
  rw [hnext, hprev]
  ring

/-- The left cut deletes the predecessor term, adding the positive margin
`A*w` to the universal interior margin. -/
theorem source_path_left_scaling
    {A c sNext w wNext : ℝ}
    (hnext : wNext = sNext * w) :
    (1 + A + c * sNext) * w - c * wNext = (1 + A) * w := by
  rw [hnext]
  ring

/-- The right cut deletes the successor term, adding the positive margin
`c*sNext*w` to the universal interior margin. -/
theorem source_path_right_scaling
    {A c sPrev sNext wPrev w : ℝ}
    (hprev : w = sPrev * wPrev) :
    (1 + A + c * sNext) * w - (A * sPrev) * wPrev =
      (1 + c * sNext) * w := by
  rw [hprev]
  ring

theorem source_path_interior_scaling_pos
    {A c sPrev sNext wPrev w wNext : ℝ}
    (hw : 0 < w)
    (hprev : w = sPrev * wPrev) (hnext : wNext = sNext * w) :
    0 < (1 + A + c * sNext) * w - (A * sPrev) * wPrev - c * wNext := by
  rw [source_path_interior_scaling hprev hnext]
  exact hw

theorem source_path_left_scaling_pos
    {A c sNext w wNext : ℝ}
    (hA : 0 ≤ A) (hw : 0 < w) (hnext : wNext = sNext * w) :
    0 < (1 + A + c * sNext) * w - c * wNext := by
  rw [source_path_left_scaling hnext]
  exact mul_pos (by linarith) hw

theorem source_path_right_scaling_pos
    {A c sPrev sNext wPrev w : ℝ}
    (hc : 0 ≤ c) (hsNext : 0 ≤ sNext) (hw : 0 < w)
    (hprev : w = sPrev * wPrev) :
    0 < (1 + A + c * sNext) * w - (A * sPrev) * wPrev := by
  rw [source_path_right_scaling hprev]
  exact mul_pos (by positivity) hw

/-- A one-coordinate path has both cut margins. -/
theorem source_path_singleton_scaling_pos
    {A c sNext w : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hsNext : 0 ≤ sNext) (hw : 0 < w) :
    0 < (1 + A + c * sNext) * w := by
  have : 0 < 1 + A + c * sNext := by positivity
  exact mul_pos this hw

end TypeIIL
