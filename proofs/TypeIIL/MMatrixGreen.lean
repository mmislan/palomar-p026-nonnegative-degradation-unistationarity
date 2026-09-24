import Mathlib

namespace TypeIIL

open scoped BigOperators

/-- Finite Z-matrix maximum principle.  A positive vector on which `D` acts
strictly positively is enough to make every solution with nonnegative forcing
nonnegative.  This is the Green-function sign needed for nonfork Schur
elimination; no diagonal-dominance normalization is assumed. -/
theorem zmatrix_solution_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℝ) (w x b : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hDw : ∀ i, 0 < ∑ j, D i j * w j)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i, ∑ j, D i j * x j = b i) :
    ∀ i, 0 ≤ x i := by
  classical
  by_contra hnot
  push Not at hnot
  let ratio : ι → ℝ := fun i => x i / w i
  obtain ⟨k, hk_mem, hkmin⟩ := Finset.exists_min_image Finset.univ ratio
    (Finset.univ_nonempty)
  obtain ⟨i, hi⟩ := hnot
  have hrneg : ratio k < 0 := by
    have hri : ratio i < 0 := div_neg_of_neg_of_pos hi (hw i)
    exact lt_of_le_of_lt (hkmin i (Finset.mem_univ i)) hri
  have hxk : x k = ratio k * w k := by
    dsimp [ratio]
    field_simp [ne_of_gt (hw k)]
  have hterm : ∀ j, D k j * x j ≤ ratio k * (D k j * w j) := by
    intro j
    by_cases hj : j = k
    · subst j
      rw [hxk]
      ring_nf
      exact le_rfl
    · have hratio : ratio k ≤ ratio j := hkmin j (Finset.mem_univ j)
      have hxj : ratio k * w j ≤ x j := by
        dsimp [ratio] at hratio
        exact (le_div_iff₀ (hw j)).mp hratio
      have hD := hoff k j (Ne.symm hj)
      have hmul := mul_le_mul_of_nonpos_left hxj hD
      nlinarith
  have hsum :
      ∑ j, D k j * x j ≤ ratio k * ∑ j, D k j * w j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  have hnegative : ratio k * ∑ j, D k j * w j < 0 :=
    mul_neg_of_neg_of_pos hrneg (hDw k)
  rw [hsolve k] at hsum
  exact (not_lt_of_ge (hb k)) (lt_of_le_of_lt hsum hnegative)

/-- A Z-matrix with a positive strict supersolution has trivial kernel. -/
theorem zmatrix_kernel_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℝ) (w x : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hDw : ∀ i, 0 < ∑ j, D i j * w j)
    (hker : ∀ i, ∑ j, D i j * x j = 0) :
    ∀ i, x i = 0 := by
  have hx := zmatrix_solution_nonneg D w x (fun _ => 0) hoff hw hDw
    (fun _ => le_rfl) hker
  have hnegker : ∀ i, ∑ j, D i j * (-x j) = 0 := by
    intro i
    rw [← neg_eq_zero]
    simpa [Finset.mul_sum] using congrArg Neg.neg (hker i)
  have hnx := zmatrix_solution_nonneg D w (fun i => -x i) (fun _ => 0)
    hoff hw hDw (fun _ => le_rfl) hnegker
  intro i
  exact le_antisymm (by linarith [hnx i]) (hx i)

/-- Order comparison for the same finite Green kernel.  If `D y = b` and the
forcing lies below the action of a supersolution `w`, then `y ≤ w`
coordinatewise. -/
theorem zmatrix_solution_le_supersolution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℝ) (w y b : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hDw : ∀ i, 0 < ∑ j, D i j * w j)
    (hsolve : ∀ i, ∑ j, D i j * y j = b i)
    (hbelow : ∀ i, b i ≤ ∑ j, D i j * w j) :
    ∀ i, y i ≤ w i := by
  let gap : ι → ℝ := fun i => w i - y i
  let residual : ι → ℝ := fun i =>
    (∑ j, D i j * w j) - b i
  have hresidual : ∀ i, 0 ≤ residual i := by
    intro i
    exact sub_nonneg.mpr (hbelow i)
  have hgapSolve : ∀ i, ∑ j, D i j * gap j = residual i := by
    intro i
    dsimp [gap, residual]
    simp_rw [mul_sub, Finset.sum_sub_distrib, hsolve]
  have hgap := zmatrix_solution_nonneg D w gap residual hoff hw hDw
    hresidual hgapSolve
  intro i
  dsimp [gap] at hgap
  linarith [hgap i]

/-- Dual Green certificate for a Schur boundary correction.  If a nonnegative
row `z` satisfies `zᵀ D = -B`, then the boundary functional `B` is nonpositive
on every solution of `D y = b` with nonnegative forcing. -/
theorem boundary_functional_nonpos_of_dual_certificate
    {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℝ) (B z y b : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hb : ∀ i, 0 ≤ b i)
    (hdual : ∀ j, ∑ i, z i * D i j = -B j)
    (hsolve : ∀ i, ∑ j, D i j * y j = b i) :
    ∑ j, B j * y j ≤ 0 := by
  have htranspose :
      ∑ j, (∑ i, z i * D i j) * y j =
        ∑ i, z i * (∑ j, D i j * y j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnonneg : 0 ≤ ∑ i, z i * b i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (hb i)
  have hleft :
      ∑ j, (∑ i, z i * D i j) * y j = -(∑ j, B j * y j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdual j]
    ring
  rw [hleft] at htranspose
  simp_rw [hsolve] at htranspose
  linarith

end TypeIIL
