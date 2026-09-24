import proofs.MixedDegradation.StationaryJacobian
import proofs.MixedDegradation.InteriorBoundary

namespace MixedDegradation
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The admissibility shift keeps both stationary reaction flows strictly
positive, including when some stationary currents are negative. -/
def admissibilityShift (J : ι → ℝ) : ι → ℝ := fun i => max 0 (-J i)

theorem stationary_boundary_nonsingular
    (N V : Matrix ι ι ℝ) (hNV : N * V = 1)
    (hinterior : ∀ p q e : ι → ℝ,
      (∀ i, 0 < p i) → (∀ i, 0 < q i) → (∀ i, 0 < e i) →
      N.mulVec (p-q) = e →
      (scaledJacobian N (1+N) p q e).det ≠ 0)
    (p q e : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (he : ∀ i, 0 ≤ e i) (hbase : N.mulVec (p-q) = e) :
    (scaledJacobian N (1+N) p q e).det ≠ 0 := by
  have hVN : V * N = 1 := mul_eq_one_comm.mp hNV
  have hN : N.det ≠ 0 := by
    have h := congrArg Matrix.det hNV
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro hz
    rw [hz, zero_mul] at h
    norm_num at h
  have hJ : V.mulVec e = p-q := by
    rw [← hbase, Matrix.mulVec_mulVec, hVN, Matrix.one_mulVec]
  let ee : ℝ → ι → ℝ := fun ε i => e i + ε
  let J : ℝ → ι → ℝ := fun ε => V.mulVec (ee ε)
  let s : ℝ → ι → ℝ := fun ε => admissibilityShift (J ε)
  let A : ℝ → Matrix ι ι ℝ := fun ε => Matrix.diagonal (s ε) - stationaryB V (J ε) (ee ε)
  have hA : ContinuousAt A 0 := by
    have hdiag : ∀ f : ℝ → ι → ℝ, Continuous f →
        Continuous (fun ε => Matrix.diagonal (f ε)) := by
      intro f hf
      apply continuous_matrix
      intro i j
      by_cases hij : i=j
      · simpa [Matrix.diagonal,hij] using (continuous_apply i).comp hf
      · simpa [Matrix.diagonal,hij] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    have hec : Continuous ee := by dsimp [ee]; fun_prop
    have hjc : Continuous J := by dsimp [J, Matrix.mulVec, dotProduct]; fun_prop
    have hsc : Continuous s := by
      apply continuous_pi
      intro i
      exact continuous_const.max (((continuous_apply i).comp hjc).neg)
    exact ((hdiag s hsc).sub (((hdiag J hjc).sub
      (continuous_const.mul (hdiag ee hec))).mul continuous_const)).continuousAt
  have hd : ∀ ε, 0 < ε → ∀ t : ι → ℝ, (∀ i, 0 < t i) →
      (A ε + Matrix.diagonal t).det ≠ 0 := by
    intro ε hε t ht
    let qq := s ε + t
    let pp := qq + J ε
    have hqq : ∀ i, 0 < qq i := by
      intro i
      exact add_pos_of_nonneg_of_pos (le_max_left _ _) (ht i)
    have hpp : ∀ i, 0 < pp i := by
      intro i
      have hb : -J ε i ≤ s ε i := le_max_right _ _
      have hh := ht i
      change 0 < s ε i + t i + J ε i
      linarith
    have hbal : N.mulVec (pp-qq) = ee ε := by
      have heq : pp-qq = J ε := by dsimp [pp]; abel
      rw [heq]
      dsimp [J]
      rw [Matrix.mulVec_mulVec, hNV, Matrix.one_mulVec]
    have hi := hinterior pp qq (ee ε) hpp hqq (fun i => add_pos_of_nonneg_of_pos (he i) hε) hbal
    have hm : Matrix.diagonal qq - stationaryB V (J ε) (ee ε) = A ε + Matrix.diagonal t := by
      dsimp [qq, A]
      have hdiag : Matrix.diagonal (s ε+t) = Matrix.diagonal (s ε) + Matrix.diagonal t := by
        ext i j
        by_cases hij : i=j <;> simp [Matrix.diagonal, hij]
      rw [hdiag]
      abel
    have hf := stationary_signed_determinant N V hNV qq (J ε) (ee ε)
    rw [hm] at hf
    intro hz
    rw [hz, mul_zero] at hf
    exact hi ((mul_eq_zero.mp hf).resolve_left (pow_ne_zero _ (by norm_num)))
  let t : ι → ℝ := q - s 0
  have ht : ∀ i, 0 < t i := by
    intro i
    have hj : J 0 i = p i-q i := by simpa [J, ee] using congrFun hJ i
    dsimp [t, s, admissibilityShift]
    rw [sub_pos, max_lt_iff]
    constructor
    · exact hq i
    · rw [hj]
      linarith [hp i]
  have hd0 := det_pos_at_boundary_of_nonsingular_inside A hA hd t ht
  have hm : A 0 + Matrix.diagonal t = Matrix.diagonal q - stationaryB V (p-q) e := by
    have hJ0 : J 0 = p-q := by simpa [J, ee] using hJ
    dsimp [A, t]
    rw [hJ0]
    have hdg : Matrix.diagonal (q-s 0) = Matrix.diagonal q - Matrix.diagonal (s 0) := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
    rw [hdg]
    have he0 : ee 0 = e := by funext i; simp [ee]
    rw [he0]
    abel
  rw [hm] at hd0
  have hf := stationary_signed_determinant N V hNV q (p-q) e
  have hpq : q + (p-q) = p := by abel
  rw [hpq] at hf
  intro hz
  rw [hz, mul_zero] at hf
  exact (ne_of_gt (mul_pos (sq_pos_of_ne_zero hN) hd0)) hf.symm

end MixedDegradation
