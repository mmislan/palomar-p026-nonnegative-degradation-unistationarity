import proofs.TypeIIL.SourceCyclicKernelClosure

namespace TypeIIL

/-- Indexed three-term fork rows assemble to the cut-path transfer.  This is
the bookkeeping bridge from literal normalized Schur rows to the transfer
object used by cyclic kernel exclusion. -/
theorem pathTransfer_eq_of_indexed_recurrence
    (weights : List ℝ) (x : ℕ → ℝ)
    (hrow : ∀ i (hi : i < weights.length),
      x (i + 2) = weights[i] * x i - x (i + 1)) :
    pathTransfer weights (x 0) (x 1) =
      (x weights.length, x (weights.length + 1)) := by
  induction weights generalizing x with
  | nil => simp [pathTransfer]
  | cons w weights ih =>
      have hzero : x 2 = w * x 0 - x 1 := by
        exact hrow 0 (by simp)
      have htail : ∀ i (hi : i < weights.length),
          x (i + 3) = weights[i] * x (i + 1) - x (i + 2) := by
        intro i hi
        have h := hrow (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc] using h
      simp only [pathTransfer]
      rw [← hzero]
      have hrec := ih (fun i => x (i + 1)) (by
        intro i hi
        simpa [Nat.add_assoc] using htail i hi)
      simpa [Nat.add_assoc] using hrec

/-- Sign-free cyclic kernel exclusion stated directly in terms of the
normalized indexed fork rows.  The transfer endpoint identities are derived
from those rows, leaving the source adapter only the literal Schur
normalization and the two cut-boundary equations. -/
theorem raw_source_schur_cyclic_indexed_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale B F Bprev Fprev W rest correction : ℝ}
    (x : ℕ → ℝ)
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
    (hrow : ∀ i
      (hi : i < (first :: (middleWeights ++ [last])).length),
      x (i + 2) = (first :: (middleWeights ++ [last]))[i] * x i -
        x (i + 1))
    (hend :
      x ((first :: (middleWeights ++ [last])).length + 1) =
        ((F / B) * (Fprev / Bprev) * rest) * x 0)
    (hwrap :
      (-(W / B)) * x (first :: (middleWeights ++ [last])).length =
        scale * (x 0 + x 1)) :
    x 0 = 0 ∧ x 1 = 0 := by
  let weights := first :: (middleWeights ++ [last])
  have htransfer : pathTransfer weights (x 0) (x 1) =
      (x weights.length, x (weights.length + 1)) :=
    pathTransfer_eq_of_indexed_recurrence weights x hrow
  apply raw_source_schur_cyclic_transfer_kernel_eq_zero
    middleWeights hfirst hlast hmiddleWeights hscale hscaleEq
      hcorrectionEq hB hF hgap hBprev hFprev hFprev_le
      hrest₀ hrest₁ hlocal hcorrection₀ hcorrection
  · rw [htransfer]
    exact hend
  · rw [htransfer]
    exact hwrap

end TypeIIL
