import proofs.TypeIIL.SourceWrapLiteralResponse
import proofs.TypeIIL.CyclicClosureBound

namespace TypeIIL

/-- The complete scalar normalization chain for the exceptional source wrap.
A positive raw two-edge margin implies the global signed-wrap closure formula
after the remaining forward ratios are known to lie in the unit interval.
This is the exact consumer of the literal response theorem before the two
boundary equations are reconstructed. -/
theorem raw_two_edge_margin_implies_cyclic_closure_pos
    (n : ℕ)
    {whole middle B F Bprev Fprev W rest correction : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F)
    (hBprev : 0 < Bprev) (hFprev : 0 ≤ Fprev)
    (hFprev_le : Fprev ≤ Bprev)
    (hW : 0 < W)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : W * Fprev < (B - F) * Bprev)
    (hcorrection0 : 0 ≤ correction)
    (hcorrection : correction ≤ (Fprev / Bprev) * middle) :
    let r₀ := F / B
    let edge := Fprev / Bprev
    let cycle := r₀ * edge * rest
    let wrap := -(W / B)
    0 < whole + (-1 : ℝ) ^ n * cycle +
      wrap * edge * middle - wrap * correction := by
  dsimp only
  have hr₀ := forward_ratio_mem_unitInterval hB hF hgap
  have hedge0 : 0 ≤ Fprev / Bprev :=
    div_nonneg hFprev (le_of_lt hBprev)
  have hedge1 : Fprev / Bprev ≤ 1 :=
    (div_le_one hBprev).2 hFprev_le
  have hcycle0 : 0 ≤ (F / B) * (Fprev / Bprev) * rest :=
    mul_nonneg (mul_nonneg hr₀.1 hedge0) hrest0
  have hwrap : -(W / B) < 0 := by
    exact neg_lt_zero.mpr (div_pos hW hB)
  have hnormalized := raw_two_edge_margin_implies_normalized_wrap
    hB hBprev hlocal
  have hglobal :
      (-(-(W / B))) * (Fprev / Bprev) <
        1 - (F / B) * (Fprev / Bprev) * rest := by
    apply local_wrap_bound_implies_global hr₀.1 hedge1 hrest0 hrest1
    simpa only [neg_neg] using hnormalized
  exact negative_wrap_formula_pos n hmiddle hwhole hcycle0 hwrap hglobal
    hcorrection0 hcorrection

/-- End-to-end zero-kernel theorem for a cut normalized source cycle.  The
interior recurrence is represented by `pathTransfer`; the exceptional local
minor supplies its strict boundary determinant. -/
theorem raw_two_edge_margin_implies_cyclic_transfer_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale B F Bprev Fprev W rest correction x₀ x₁ : ℝ}
    (hfirst : 0 ≤ first) (hlast : 0 ≤ last)
    (hmiddleWeights : ∀ w ∈ middleWeights, 0 ≤ w)
    (hscale : 0 < scale)
    (hscaleEq : scale = (F / B) * rest)
    (hcorrectionEq :
      scale * correction = first * last * middleWeights.prod)
    (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F)
    (hBprev : 0 < Bprev) (hFprev : 0 ≤ Fprev)
    (hFprev_le : Fprev ≤ Bprev)
    (hW : 0 < W)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : W * Fprev < (B - F) * Bprev)
    (hcorrection0 : 0 ≤ correction)
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
  have hmiddle : 1 ≤ pathContinuant middleWeights :=
    one_le_pathContinuant hmiddleWeights
  have hwhole : pathContinuant middleWeights ≤
      pathContinuant (first :: (middleWeights ++ [last])) :=
    pathContinuant_middle_le hfirst hlast hmiddleWeights
  have hclosure := raw_two_edge_margin_implies_cyclic_closure_pos
    middleWeights.length hmiddle hwhole hB hF hgap hBprev hFprev
      hFprev_le hW hrest0 hrest1 hlocal hcorrection0 hcorrection
  apply cyclic_transfer_kernel_eq_zero middleWeights hscale
    (edge := Fprev / Bprev) (correction := correction)
    (wrap := -(W / B))
  · rw [hscaleEq]
  · exact hcorrectionEq
  · convert hclosure using 1
    all_goals ring
  · convert hend using 1
    all_goals ring
  · exact hwrap

end TypeIIL
