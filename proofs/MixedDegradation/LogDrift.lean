import proofs.MixedDegradation.StationaryJacobian
import proofs.MixedDegradation.BoundaryUniqueness

namespace MixedDegradation
open Filter Set
open scoped Matrix BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixCLM (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp] theorem matrixCLM_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixCLM A x = A.mulVec x := rfl

theorem matrixCLM_invertible (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (matrixCLM A).IsInvertible := by
  have hi : Function.Injective (matrixCLM A) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA))
  exact ⟨ContinuousLinearEquiv.ofBijective (matrixCLM A)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hi)), rfl⟩

def logForward (a z : ι → ℝ) : ι → ℝ := fun i => a i * Real.exp (z i)
def logReverse (P : Matrix ι ι ℝ) (b z : ι → ℝ) : ι → ℝ :=
  fun i => b i * Real.exp (P.transpose.mulVec z i)

def logDrift (N P : Matrix ι ι ℝ) (a b d : ι → ℝ)
    (v : ℝ × (ι → ℝ)) : ι → ℝ :=
  N.mulVec (logForward a v.2 - logReverse P b v.2) -
    (fun i => (d i+v.1) * Real.exp (v.2 i))

def logDriftDerivative (N P : Matrix ι ι ℝ) (a b d : ι → ℝ)
    (v : ℝ × (ι → ℝ)) : (ℝ × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  (matrixCLM (scaledJacobian N P (logForward a v.2) (logReverse P b v.2)
    (fun i => (d i+v.1)*Real.exp (v.2 i)))).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)) -
  ContinuousLinearMap.pi (fun i => Real.exp (v.2 i) • (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)))

theorem logDrift_hasStrictFDerivAt (N P : Matrix ι ι ℝ) (a b d : ι → ℝ)
    (v : ℝ × (ι → ℝ)) :
    HasStrictFDerivAt (logDrift N P a b d) (logDriftDerivative N P a b d v) v := by
  let sndL := ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)
  let fstL := ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)
  let R := Matrix.diagonal (logForward a v.2) - Matrix.diagonal (logReverse P b v.2)*P.transpose
  have hc : HasStrictFDerivAt (fun w : ℝ × (ι → ℝ) => logForward a w.2 - logReverse P b w.2)
      ((matrixCLM R).comp sndL) v := by
    rw [hasStrictFDerivAt_pi']
    intro i
    let Li := (ContinuousLinearMap.proj i).comp sndL
    let Lp := (ContinuousLinearMap.proj i).comp ((matrixCLM P.transpose).comp sndL)
    have hf := ((Real.hasStrictDerivAt_exp (v.2 i)).comp_hasStrictFDerivAt v Li.hasStrictFDerivAt).const_mul (a i)
    have hr := ((Real.hasStrictDerivAt_exp (P.transpose.mulVec v.2 i)).comp_hasStrictFDerivAt v Lp.hasStrictFDerivAt).const_mul (b i)
    have hL : (ContinuousLinearMap.proj i).comp ((matrixCLM R).comp sndL) =
        a i • Real.exp (v.2 i) • Li - b i • Real.exp (P.transpose.mulVec v.2 i) • Lp := by
      apply ContinuousLinearMap.ext
      intro w
      simp [R, Li, Lp, logForward, logReverse, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      ring
    rw [hL]
    exact hf.sub hr
  have hd : HasStrictFDerivAt (fun w : ℝ × (ι → ℝ) => fun i => (d i+w.1)*Real.exp (w.2 i))
      (ContinuousLinearMap.pi (fun i =>
        Real.exp (v.2 i) • fstL +
        ((d i+v.1)*Real.exp (v.2 i)) • ((ContinuousLinearMap.proj i).comp sndL))) v := by
    rw [hasStrictFDerivAt_pi']
    intro i
    let Li := (ContinuousLinearMap.proj i).comp sndL
    have hf := (fstL.hasStrictFDerivAt (x := v)).const_add (d i)
    have he := (Real.hasStrictDerivAt_exp (v.2 i)).comp_hasStrictFDerivAt v Li.hasStrictFDerivAt
    have hL : (ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.pi (fun j => Real.exp (v.2 j) • fstL +
          ((d j+v.1)*Real.exp (v.2 j)) • ((ContinuousLinearMap.proj j).comp sndL))) =
        (d i+fstL v) • Real.exp (v.2 i) • Li + Real.exp (Li v) • fstL := by
      apply ContinuousLinearMap.ext
      intro w
      simp [fstL, Li, sndL]
      ring
    rw [hL]
    exact hf.mul he
  have hh := ((matrixCLM N).hasStrictFDerivAt.comp v hc).sub hd
  have hL : logDriftDerivative N P a b d v =
      (matrixCLM N).comp ((matrixCLM R).comp sndL) -
      ContinuousLinearMap.pi (fun i => Real.exp (v.2 i) • fstL +
        ((d i+v.1)*Real.exp (v.2 i)) • ((ContinuousLinearMap.proj i).comp sndL)) := by
    apply ContinuousLinearMap.ext
    intro w
    funext i
    simp [logDriftDerivative, scaledJacobian, R, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.mulVec_sub, sndL, fstL]
    ring
  rw [hL]
  exact hh

theorem logDrift_partial (N P : Matrix ι ι ℝ) (a b d z : ι → ℝ) :
    (logDriftDerivative N P a b d (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)) =
      matrixCLM (scaledJacobian N P (logForward a z) (logReverse P b z)
        (fun i => d i*Real.exp (z i))) := by
  ext w i
  simp [logDriftDerivative]

/-- The source-specific work is precisely interior uniqueness and boundary
nonsingularity. Smoothness and the two-branch argument are supplied here. -/
theorem logDrift_boundary_uniqueness (N P : Matrix ι ι ℝ)
    (a b d : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hd : ∀ i, 0 ≤ d i)
    (hi : ∀ ε, 0 < ε → ∀ x y : ι → ℝ,
      logDrift N P a b d (ε,x) = 0 → logDrift N P a b d (ε,y) = 0 → x=y)
    (hn : ∀ p q e : ι → ℝ, (∀ i, 0 < p i) → (∀ i, 0 < q i) →
      (∀ i, 0 ≤ e i) → N.mulVec (p-q) = e →
      (scaledJacobian N P p q e).det ≠ 0)
    (x y : ι → ℝ) (hx : logDrift N P a b d (0,x) = 0)
    (hy : logDrift N P a b d (0,y) = 0) : x=y := by
  apply boundary_uniqueness_of_nondegenerate (logDrift N P a b d) Set.univ isOpen_univ
    _ _ x y (Set.mem_univ _) (Set.mem_univ _) hx hy
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    intro u _ v _ hu hv
    exact hi ε hε u v hu hv
  · intro z _ hz
    refine ⟨logDriftDerivative N P a b d (0,z), logDrift_hasStrictFDerivAt N P a b d (0,z), ?_⟩
    rw [logDrift_partial]
    apply matrixCLM_invertible
    apply hn
    · intro i
      exact mul_pos (ha i) (Real.exp_pos _)
    · intro i
      exact mul_pos (hb i) (Real.exp_pos _)
    · intro i
      exact mul_nonneg (hd i) (Real.exp_pos _).le
    · simpa [logDrift] using sub_eq_zero.mp hz

end
end MixedDegradation
