import proofs.TypeIIL.CyclicClosureBound
import Mathlib.LinearAlgebra.Matrix.Gershgorin

namespace MixedDegradation
open TypeIIL
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiaffinity prevents a nonnegative diagonal-shift determinant from
vanishing inside the positive orthant. The hypothesis will be obtained by
continuity from strictly positive degradation; it is not a source assumption. -/
theorem det_pos_of_nonnegative_diagonal_shifts
    (A : Matrix ι ι ℝ)
    (hnonneg : ∀ r : ι → ℝ, (∀ i, 0 < r i) →
      0 ≤ (A + Matrix.diagonal r).det)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    0 < (A + Matrix.diagonal q).det := by
  classical
  let off : ι → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, ‖A i j‖
  have hoff : ∀ i, 0 ≤ off i := fun i =>
    Finset.sum_nonneg fun j _ => norm_nonneg _
  let b : ι → ℝ := fun i => q i + ‖A i i‖ + off i + 1
  let a : ι → ℝ := fun i => q i / 2
  have hbq : ∀ i, q i < b i := by
    intro i
    dsimp [b]
    linarith [abs_nonneg (A i i), hoff i]
  have hb : ∀ i, 0 < b i := fun i => (hq i).trans (hbq i)
  have ha : ∀ i, 0 < a i := fun i => div_pos (hq i) (by norm_num)
  have haq : ∀ i, a i < q i := by
    intro i
    dsimp [a]
    linarith [hq i]
  have hba : ∀ i, 0 < b i - a i := by
    intro i
    linarith [hbq i, haq i]
  have hdiag : ∀ i, off i < A i i + b i := by
    intro i
    have habs : -|A i i| ≤ A i i := neg_abs_le (A i i)
    dsimp [b]
    linarith [hq i]
  have hne : (A + Matrix.diagonal b).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have heq : (∑ j ∈ Finset.univ.erase i,
        ‖(A + Matrix.diagonal b) i j‖) = off i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Matrix.add_apply, Matrix.diagonal, Ne.symm hji]
    rw [heq]
    have hpos : 0 < A i i + b i := (hoff i).trans_lt (hdiag i)
    simpa [Matrix.add_apply, Real.norm_eq_abs, abs_of_pos hpos] using hdiag i
  have hbdet : 0 < (A + Matrix.diagonal b).det :=
    lt_of_le_of_ne (hnonneg b hb) (Ne.symm hne)
  let t : ι → ℝ := fun i => (b i - q i) / (b i - a i)
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    exact (div_pos (sub_pos.mpr (hbq i)) (hba i)).le
  have ht1 : ∀ i, t i < 1 := by
    intro i
    exact (div_lt_one (hba i)).mpr (by linarith [haq i])
  have hinterp : columnBoxMatrix (A + Matrix.diagonal b)
      (A + Matrix.diagonal a) t = A + Matrix.diagonal q := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp only [columnBoxMatrix, Matrix.add_apply, Matrix.diagonal_apply_eq]
      dsimp [t]
      field_simp [ne_of_gt (hba i)]
      ring
    · simp only [columnBoxMatrix, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij,
        add_zero]
      ring
  rw [← hinterp, det_columnBoxMatrix_eq_boxInterpolation]
  apply boxInterpolation_pos ht0 ht1
  · intro s _
    have hv : columnVertexMatrix (A + Matrix.diagonal b)
        (A + Matrix.diagonal a) s =
        A + Matrix.diagonal (fun i => if i ∈ s then a i else b i) := by
      funext i j
      by_cases h : j ∈ s <;> by_cases hij : i = j <;>
        simp [columnVertexMatrix, Matrix.add_apply, Matrix.diagonal, h, hij]
    rw [hv]
    apply hnonneg
    intro i
    split_ifs <;> first | exact ha i | exact hb i
  · simpa [columnVertexMatrix] using hbdet

open Filter Set
open scoped Topology

/-- The one-sided limit of nonnegative real values is nonnegative. -/
theorem nonneg_at_zero_of_pos_side {f : ℝ → ℝ}
    (hf : ContinuousAt f 0) (h : ∀ t, 0 < t → 0 ≤ f t) : 0 ≤ f 0 := by
  apply ge_of_tendsto (hf.mono_left nhdsWithin_le_nhds :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h t ht

/-- A continuous family with nonnegative positive-parameter diagonal-shift
determinants retains strict positivity at parameter zero. -/
theorem det_pos_at_zero_of_diagonal_family
    (A : ℝ → Matrix ι ι ℝ) (hA : ContinuousAt A 0)
    (h : ∀ ε, 0 < ε → ∀ q : ι → ℝ, (∀ i, 0 < q i) →
      0 ≤ (A ε + Matrix.diagonal q).det)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    0 < (A 0 + Matrix.diagonal q).det := by
  apply det_pos_of_nonnegative_diagonal_shifts (A 0) _ q hq
  intro r hr
  apply nonneg_at_zero_of_pos_side (f := fun ε => (A ε + Matrix.diagonal r).det)
  · exact continuous_id.matrix_det.continuousAt.comp
      (hA.add continuousAt_const)
  · intro ε hε
    exact h ε hε r hr

end MixedDegradation
