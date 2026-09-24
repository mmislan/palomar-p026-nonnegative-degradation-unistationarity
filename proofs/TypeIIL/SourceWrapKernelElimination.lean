import proofs.TypeIIL.SourceWrapLiteralColumns

namespace TypeIIL

open scoped BigOperators

/-- Once a global kernel row has been split into a long gap and its two
adjacent fork columns, invertibility of the literal gap block reconstructs
every internal coordinate from the two source-defined Schur responses. -/
theorem SourceWrapForkGap.internal_coordinates_eq_negative_responses
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (x : Fin n → ℝ) (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      sourceWrapForwardForcing (G.gapA p e)
        (G.gapC weight q e rho) i)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      sourceWrapLeftForcing (G.gapA p e) (weight left) i)
    (hrows : ∀ i,
      (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x (G.idx j)) +
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e (G.idx i) left * x left +
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e (G.idx i) right * x right = 0) :
    ∀ i, x (G.idx i) = -(yw i * x left + xf i * x right) := by
  let z : Fin (m + 1) → ℝ := fun i =>
    x (G.idx i) + yw i * x left + xf i * x right
  have hzero : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j = 0 := by
    intro i
    have hr := hrows i
    rw [P.internal_left_column_eq_forcing weight p q e rho i,
      P.internal_right_column_eq_forcing (by omega) weight p q e rho hunit i] at hr
    calc
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j =
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x (G.idx j)) +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j) * x left +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j) * x right := by
            dsimp [z]
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp only [← mul_assoc]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = 0 := by rw [hyw i, hxf i]; linarith
  have hz := G.restrictedCurrentMatrix_kernel_eq_zero weight p q e rho
    hp hq he hrho hw z hzero
  intro i
  have hi := hz i
  dsimp [z] at hi
  linarith

end TypeIIL
