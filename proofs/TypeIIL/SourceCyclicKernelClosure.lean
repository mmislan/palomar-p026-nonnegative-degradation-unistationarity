import proofs.TypeIIL.SourceCyclicRawClosure

namespace TypeIIL

/-- Complementary sign branch.  If `W ≤ 0`, the signed wrap coefficient
`-W/B` is nonnegative.  The correction estimate then contributes a
nonnegative term, while `whole ≥ 1` and the forward cycle is strictly below
one.  No exceptional two-edge comparison is needed in this branch. -/
theorem nonpositive_raw_wrap_cyclic_closure_pos
    (n : ℕ)
    {whole middle B F Bprev Fprev W rest correction : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F)
    (hBprev : 0 < Bprev) (hFprev : 0 ≤ Fprev)
    (hFprev_le : Fprev ≤ Bprev) (hW : W ≤ 0)
    (hrest₀ : 0 ≤ rest) (hrest₁ : rest ≤ 1)
    (hcorrection : correction ≤ (Fprev / Bprev) * middle) :
    let r := F / B
    let edge := Fprev / Bprev
    let cycle := r * edge * rest
    let wrap := -(W / B)
    0 < whole + (-1 : ℝ) ^ n * cycle +
      wrap * edge * middle - wrap * correction := by
  dsimp only
  have hr := forward_ratio_mem_unitInterval hB hF hgap
  have hedge₀ : 0 ≤ Fprev / Bprev :=
    div_nonneg hFprev (le_of_lt hBprev)
  have hedge₁ : Fprev / Bprev ≤ 1 :=
    (div_le_one hBprev).2 hFprev_le
  have hcycle₀ : 0 ≤ F / B * (Fprev / Bprev) * rest :=
    mul_nonneg (mul_nonneg hr.1 hedge₀) hrest₀
  have hcycle₁ : F / B * (Fprev / Bprev) * rest < 1 :=
    forward_cycle_product_lt_one_of_local hr.1 hr.2 hedge₁ hrest₀ hrest₁
  have hwrap₀ : 0 ≤ -(W / B) :=
    neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hW (le_of_lt hB))
  have hcorrTerm : 0 ≤ -(W / B) *
      ((Fprev / Bprev) * middle - correction) :=
    mul_nonneg hwrap₀ (sub_nonneg.mpr hcorrection)
  have hsignsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    simp
  have hsign : -1 ≤ (-1 : ℝ) ^ n := by
    nlinarith [sq_nonneg (((-1 : ℝ) ^ n) + 1)]
  have hparity : -(F / B * (Fprev / Bprev) * rest) ≤
      (-1 : ℝ) ^ n * (F / B * (Fprev / Bprev) * rest) := by
    simpa using mul_le_mul_of_nonneg_right hsign hcycle₀
  have hwhole₁ : 1 ≤ whole := le_trans hmiddle hwhole
  nlinarith

/-- End-to-end kernel exclusion in the nonpositive raw-wrap branch. -/
theorem nonpositive_raw_source_schur_cyclic_transfer_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale correction B F Bprev Fprev W rest x₀ x₁ : ℝ}
    (hmiddle : ∀ w ∈ middleWeights, 0 ≤ w)
    (hfirst : 0 ≤ first) (hlast : 0 ≤ last)
    (hscale : 0 < scale)
    (hcycle :
      F / B * (Fprev / Bprev) * rest = scale * (Fprev / Bprev))
    (hcorrectionIdentity :
      scale * correction = first * last * middleWeights.prod)
    (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F)
    (hBprev : 0 < Bprev) (hFprev : 0 ≤ Fprev)
    (hFprev_le : Fprev ≤ Bprev) (hW : W ≤ 0)
    (hrest₀ : 0 ≤ rest) (hrest₁ : rest ≤ 1)
    (hcorrection :
      correction ≤ (Fprev / Bprev) * pathContinuant middleWeights)
    (hend :
      (pathTransfer (first :: (middleWeights ++ [last])) x₀ x₁).2 =
        (F / B * (Fprev / Bprev) * rest) * x₀)
    (hwrap :
      -(W / B) *
          (pathTransfer (first :: (middleWeights ++ [last])) x₀ x₁).1 =
        scale * (x₀ + x₁)) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hmidOne : 1 ≤ pathContinuant middleWeights :=
    one_le_pathContinuant hmiddle
  have hmidWhole : pathContinuant middleWeights ≤
      pathContinuant (first :: (middleWeights ++ [last])) :=
    pathContinuant_middle_le hfirst hlast hmiddle
  have hclosure := nonpositive_raw_wrap_cyclic_closure_pos
    middleWeights.length hmidOne hmidWhole hB hF hgap hBprev hFprev
      hFprev_le hW hrest₀ hrest₁ hcorrection
  exact cyclic_transfer_kernel_eq_zero middleWeights hscale hcycle
    hcorrectionIdentity hclosure hend hwrap

/-- Sign-free cyclic landing theorem.  The raw coupled minor is consumed when
`W > 0`; when `W ≤ 0`, the signed wrap is already nonnegative and the same
continuant correction bound closes the determinant directly. -/
theorem raw_source_schur_cyclic_transfer_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale B F Bprev Fprev W rest correction x₀ x₁ : ℝ}
    (hfirst : 0 ≤ first) (hlast : 0 ≤ last)
    (hmiddleWeights : ∀ w ∈ middleWeights, 0 ≤ w)
    (hscale : 0 < scale) (hscaleEq : scale = (F / B) * rest)
    (hcorrectionEq :
      scale * correction = first * last * middleWeights.prod)
    (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F)
    (hBprev : 0 < Bprev) (hFprev : 0 ≤ Fprev)
    (hFprev_le : Fprev ≤ Bprev)
    (hrest₀ : 0 ≤ rest) (hrest₁ : rest ≤ 1)
    (hlocal : W * Fprev < (B - F) * Bprev)
    (hcorrection₀ : 0 ≤ correction)
    (hcorrection : correction ≤
      (Fprev / Bprev) * pathContinuant middleWeights)
    (hend :
      (pathTransfer (first :: (middleWeights ++ [last])) x₀ x₁).2 =
        ((F / B) * (Fprev / Bprev) * rest) * x₀)
    (hwrap :
      (-(W / B)) *
          (pathTransfer (first :: (middleWeights ++ [last])) x₀ x₁).1 =
        scale * (x₀ + x₁)) :
    x₀ = 0 ∧ x₁ = 0 := by
  by_cases hW : 0 < W
  · exact raw_two_edge_margin_implies_cyclic_transfer_kernel_eq_zero
      middleWeights hfirst hlast hmiddleWeights hscale hscaleEq
      hcorrectionEq hB hF hgap hBprev hFprev hFprev_le hW
      hrest₀ hrest₁ hlocal hcorrection₀ hcorrection hend hwrap
  · have hcycle :
        F / B * (Fprev / Bprev) * rest =
          scale * (Fprev / Bprev) := by
      rw [hscaleEq]
      ring
    exact nonpositive_raw_source_schur_cyclic_transfer_kernel_eq_zero
      middleWeights hmiddleWeights hfirst hlast hscale hcycle
      hcorrectionEq hB hF hgap hBprev hFprev hFprev_le
      (le_of_not_gt hW) hrest₀ hrest₁ hcorrection hend hwrap

end TypeIIL
