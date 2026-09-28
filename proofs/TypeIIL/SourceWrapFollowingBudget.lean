module

public import proofs.TypeIIL.SourceWrapRightDiagonal
public import proofs.TypeIIL.SourceWrapPrecedingBudget

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- Positive forcing at the left boundary together with one unit at the
terminal boundary.  This is the forcing obtained from the two literal Schur
responses after shifting the mixed response by the terminal basis vector. -/
def finiteSourcePathLeftTerminalUnitForcing {m : ℕ}
    (A : Fin (m + 1) → ℝ) (scale : ℝ) : Fin (m + 1) → ℝ :=
  fun i => (if i.val = 0 then A i * scale else 0) +
    (if i.val = m then 1 else 0)

/-- The cumulative source weight dominates the response to positive left
forcing plus a terminal unit.  Only the value at the first coordinate is
needed for the following-gap Schur budget. -/
theorem finiteSourcePath_left_terminal_unit_response_le_scale
    {m : ℕ} {A c s u : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale)
    (hu : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * u j =
      finiteSourcePathLeftTerminalUnitForcing A scale i) :
    u 0 ≤ scale := by
  have hbound : ∀ i, u i ≤ scale * finiteSourcePathWeight s i := by
    apply zmatrix_solution_le_supersolution
      (finiteSourcePathMatrix A c s)
      (fun i => scale * finiteSourcePathWeight s i) u
      (finiteSourcePathLeftTerminalUnitForcing A scale)
    · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
        (fun i => le_trans zero_le_one (hs i))
    · intro i
      exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
        (finiteSourcePathWeight_pos
          (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
    · intro i
      have hfactor :
          (∑ j, finiteSourcePathMatrix A c s i j *
              (scale * finiteSourcePathWeight s j)) =
            scale * (∑ j, finiteSourcePathMatrix A c s i j *
              finiteSourcePathWeight s j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hfactor]
      exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
        (finiteSourcePathMatrix_mul_weight_pos hA hc
          (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
    · exact hu
    · intro i
      have hw : 1 ≤ finiteSourcePathWeight s i :=
        finiteSourcePathWeight_one_le hs i
      have hscale0 : 0 ≤ scale := le_trans zero_le_one hscale
      have hA0 : 0 ≤ A i := hA i
      have hc0 : 0 ≤ c i := hc i
      have hs0 : 0 ≤ s i := le_trans zero_le_one (hs i)
      have hw0 : 0 ≤ finiteSourcePathWeight s i :=
        le_trans zero_le_one hw
      have hAw : A i * scale ≤
          scale * (A i * finiteSourcePathWeight s i) := by
        nlinarith [mul_nonneg hA0 hscale0,
          mul_nonneg (mul_nonneg hA0 hscale0) hw0]
      have hone : 1 ≤ scale * finiteSourcePathWeight s i :=
        one_le_mul_of_one_le_of_one_le hscale hw
      have hfactor :
          (∑ j, finiteSourcePathMatrix A c s i j *
              (scale * finiteSourcePathWeight s j)) =
            scale * (∑ j, finiteSourcePathMatrix A c s i j *
              finiteSourcePathWeight s j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hfactor, finiteSourcePathMatrix_mul_weight_exact_boundary]
      unfold finiteSourcePathLeftTerminalUnitForcing
      split_ifs <;>
        nlinarith [mul_nonneg hscale0 hw0,
          mul_nonneg hscale0 (mul_nonneg hA0 hw0),
          mul_nonneg hscale0 (mul_nonneg (mul_nonneg hc0 hs0) hw0)]
  have hzero : finiteSourcePathWeight s (0 : Fin (m + 1)) = 1 := by
    unfold finiteSourcePathWeight
    have hempty : Finset.Iio (0 : Fin (m + 1)) = ∅ := by
      ext j
      simp
    rw [hempty]
    simp
  simpa [hzero] using hbound 0

/-- The two actual literal responses leave a nonnegative following-gap
budget.  The mixed response is shifted by the terminal basis vector before
the maximum principle is applied; at coordinate zero the shift is invisible. -/
theorem finiteSourcePath_literal_following_budget_nonneg
    {m : ℕ} (hm : 0 < m) (A c s : Fin (m + 1) → ℝ)
    {scale k : ℝ} (xf yw : Fin (m + 1) → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale) (hk : 0 ≤ k)
    (hunit : s (Fin.last m) = 1)
    (hxf : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * xf j =
      sourceWrapForwardForcing A c i)
    (hyw : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * yw j =
      sourceWrapLeftForcing A scale i) :
    0 ≤ k * (scale + yw 0 - xf 0) := by
  let last : Fin (m + 1) := Fin.last m
  let u : Fin (m + 1) → ℝ := fun i =>
    -yw i + xf i + if i = last then 1 else 0
  have hshift := finiteSourcePath_forward_add_terminal_solve hm A c s xf
    hunit hxf
  have hu : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * u j =
      finiteSourcePathLeftTerminalUnitForcing A scale i := by
    intro i
    have hy := hyw i
    have hx := hshift i
    dsimp [u]
    calc
      (∑ j, finiteSourcePathMatrix A c s i j *
          (-yw j + xf j + if j = last then 1 else 0)) =
          -(∑ j, finiteSourcePathMatrix A c s i j * yw j) +
            ∑ j, finiteSourcePathMatrix A c s i j *
              (xf j + if j = last then 1 else 0) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -sourceWrapLeftForcing A scale i +
          (if i = Fin.last m then 1 else 0) := by
        rw [hy]
        simpa [last] using congrArg
          (fun z => -sourceWrapLeftForcing A scale i + z) hx
      _ = finiteSourcePathLeftTerminalUnitForcing A scale i := by
        unfold sourceWrapLeftForcing finiteSourcePathLeftTerminalUnitForcing
        have hm0 : m ≠ 0 := Nat.ne_of_gt hm
        by_cases hi0 : i.val = 0 <;> by_cases him : i.val = m <;>
          simp [hi0, him, Fin.ext_iff, hm0]
  have hu0 := finiteSourcePath_left_terminal_unit_response_le_scale
    hA hc hs hscale hu
  have hzeroLast : (0 : Fin (m + 1)) ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    simp [last] at hv
    omega
  dsimp [u] at hu0
  rw [ite_eq_right hzeroLast] at hu0
  exact mul_nonneg hk (by linarith)

end TypeIIL
