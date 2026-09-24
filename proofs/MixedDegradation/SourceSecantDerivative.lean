import proofs.TypeIIL.SourceBackFirstSecant

namespace MixedDegradation
open TypeIIL

theorem secantPoly_one_one (m : ℕ) : TypeII3.secantPoly 1 1 m = (m : ℝ) := by
  induction m with
  | zero => simp [TypeII3.secantPoly]
  | succ m ih => simp [TypeII3.secantPoly, ih]; ring

theorem source_secant_at_one {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ) (back : Fin n → Option (Fin n))
    (hd : ∀ r z, back r = some z → z ≠ next r) :
    sourceBackFirstSecantMatrix next weight back (fun _ => 1) =
      Matrix.transpose (fun i r => (sourceProductExponent next weight back i r : ℝ)) := by
  ext r i
  cases hr : back r with
  | none =>
    simp [sourceBackFirstSecantMatrix, sourceProductExponent, hr, secantPoly_one_one]
  | some z =>
    have hz := hd r z hr
    by_cases hi : i = z
    · subst i
      simp [sourceBackFirstSecantMatrix, sourceProductExponent, hr, hz]
    · by_cases hn : i = next r
      · subst i
        simp [sourceBackFirstSecantMatrix, sourceProductExponent, hr, hz.symm,
          secantPoly_one_one]
      · simp [sourceBackFirstSecantMatrix, sourceProductExponent, hr, hi, hn]

end MixedDegradation
