import proofs.MixedDegradation.DiagonalBoundary

namespace MixedDegradation
open Filter Set
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_endpoint_of_continuous_nonsingular
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (h0 : 0 < f 0) (hne : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) : 0 < f 1 := by
  by_contra h
  have h1 : f 1 ≤ 0 := le_of_not_gt h
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hf ⟨h1,h0.le⟩
  exact hne t ht hft

theorem exists_positive_diagonal_shift (A : Matrix ι ι ℝ) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ 0 < (A + Matrix.diagonal b).det := by
  let f : ℝ → ℝ := fun t => (1 + t • A).det
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < f t := by
    apply hf.continuousAt
    exact isOpen_Ioi.mem_nhds (by simp [f])
  have hp' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 0 < f t := by
    filter_upwards [self_mem_nhdsWithin, hp.filter_mono nhdsWithin_le_nhds] with t ht hft
    exact ⟨ht,hft⟩
  obtain ⟨t,ht,hft⟩ := hp'.exists
  refine ⟨fun _ => t⁻¹, fun _ => inv_pos.mpr ht, ?_⟩
  have hdiag : Matrix.diagonal (fun _ : ι => t⁻¹) = t⁻¹ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  have hmatrix : A + Matrix.diagonal (fun _ : ι => t⁻¹) = t⁻¹ • (1+t•A) := by
    rw [hdiag,smul_add,smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]
    exact add_comm _ _
  rw [hmatrix,Matrix.det_smul]
  exact mul_pos (pow_pos (inv_pos.mpr ht) _) hft

/-- For a fixed matrix, nonsingularity for every positive diagonal shift
forces the positive determinant orientation. -/
theorem det_pos_of_nonsingular_diagonal_shifts
    (A : Matrix ι ι ℝ)
    (hne : ∀ r : ι → ℝ, (∀ i, 0 < r i) → (A+Matrix.diagonal r).det ≠ 0)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) : 0 < (A+Matrix.diagonal q).det := by
  obtain ⟨b,hb,hbdet⟩ := exists_positive_diagonal_shift A
  let r : ℝ → ι → ℝ := fun t i => (1-t)*b i+t*q i
  let f : ℝ → ℝ := fun t => (A+Matrix.diagonal (r t)).det
  have hf : Continuous f := by
    apply Continuous.matrix_det
    apply Continuous.add continuous_const
    apply continuous_matrix
    intro i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij,r] <;> fun_prop
  have h0 : 0 < f 0 := by simpa [f,r] using hbdet
  have hn : ∀ t ∈ Icc (0:ℝ) 1, f t ≠ 0 := by
    intro t ht
    apply hne
    intro i
    dsimp [r]
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hlt) (hb i)) (mul_nonneg ht.1 (hq i).le)
    · simpa using hq i
  simpa [f,r] using positive_endpoint_of_continuous_nonsingular f hf.continuousOn h0 hn

/-- Interior nonsingularity on the entire positive diagonal-shift domain
extends to the parameter boundary. This is the uniform replacement for
degradation-support determinant enumeration. -/
theorem det_pos_at_boundary_of_nonsingular_inside
    (A : ℝ → Matrix ι ι ℝ) (hA : ContinuousAt A 0)
    (hne : ∀ ε, 0 < ε → ∀ q : ι → ℝ, (∀ i, 0 < q i) →
      (A ε+Matrix.diagonal q).det ≠ 0)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    0 < (A 0+Matrix.diagonal q).det := by
  apply det_pos_at_zero_of_diagonal_family A hA _ q hq
  intro ε hε r hr
  exact (det_pos_of_nonsingular_diagonal_shifts (A ε) (hne ε hε) r hr).le

end MixedDegradation
