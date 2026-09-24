import proofs.TypeIIL.OrderedMonomialSecant
import proofs.TypeIIL.LogarithmicSecantMatrix

namespace TypeIIL

open TypeII3
open scoped BigOperators

def finLift {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x ⟨j, h⟩ else 1

def orderedPrefix {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j ∈ Finset.range i.val, finLift x j

theorem orderedPrefix_pos {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (i : Fin n) : 0 < orderedPrefix x i := by
  unfold orderedPrefix
  apply Finset.prod_pos
  intro j _
  unfold finLift
  split_ifs with hj
  · exact hx ⟨j, hj⟩
  · norm_num

theorem ordered_product_sub_one_range (x : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, x j) * (x i - 1) =
      (∏ i ∈ Finset.range n, x i) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ih]
      ring

theorem finLift_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    finLift x i.val = x i := by
  simp [finLift, i.isLt]

theorem ordered_product_sub_one_fin {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, orderedPrefix x i * (x i - 1) = (∏ i, x i) - 1 := by
  have h := ordered_product_sub_one_range (finLift x) n
  rw [Finset.sum_range] at h
  have hprod : (∏ j ∈ Finset.range n, finLift x j) = ∏ i, x i := by
    rw [Finset.prod_range]
    simp [finLift_apply]
  rw [hprod] at h
  simpa [orderedPrefix, finLift_apply] using h

/-- Coordinate-ordered telescoping secant matrix on the canonical `Fin n`
order. -/
noncomputable def orderedMonomialSecantMatrix
    {n : ℕ} (P : Fin n → Fin n → ℕ) (rho : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r i => orderedPrefix (fun j => rho j ^ P j r) i *
    secantPoly (rho i) 1 (P i r)

theorem orderedMonomialSecantMatrix_nonneg
    {n : ℕ} (P : Fin n → Fin n → ℕ) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) (r i : Fin n) :
    0 ≤ orderedMonomialSecantMatrix P rho r i := by
  unfold orderedMonomialSecantMatrix orderedPrefix
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j hj => by
      unfold finLift
      split_ifs with h
      · exact le_of_lt (pow_pos (hrho ⟨j, h⟩) _)
      · norm_num
  · exact secantPoly_nonneg (hrho i) (by norm_num) _

/-- Exact finite-matrix version of the ordered telescoping identity. -/
theorem orderedMonomialSecantMatrix_mul_ratio_sub_one
    {n : ℕ} (P : Fin n → Fin n → ℕ) {rho : Fin n → ℝ}
    (r : Fin n) :
    ∑ i, orderedMonomialSecantMatrix P rho r i * (rho i - 1) =
      monomialRatio P rho r - 1 := by
  let factor : Fin n → ℝ := fun i => rho i ^ P i r
  have hpow : ∀ i, factor i - 1 =
      (rho i - 1) * secantPoly (rho i) 1 (P i r) := by
    intro i
    dsimp [factor]
    simpa using pow_sub_pow_eq_mul_secantPoly (rho i) 1 (P i r)
  calc
    ∑ i, orderedMonomialSecantMatrix P rho r i * (rho i - 1) =
        ∑ i, orderedPrefix factor i * (factor i - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hpow i]
      unfold orderedMonomialSecantMatrix
      dsimp [factor]
      ring
    _ = (∏ i, factor i) - 1 := ordered_product_sub_one_fin factor
    _ = monomialRatio P rho r - 1 := by rfl

/-- A source fork has strict ordered-secant row gain once its first two
positive exponents are identified.  Coordinates before `a` are absent, so
the `a`-coefficient already contributes at least one; the later
`b`-coefficient is strictly positive. -/
theorem one_lt_orderedMonomialSecantMatrix_row_sum_of_two_support
    {n : ℕ} (P : Fin n → Fin n → ℕ) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) (r a b : Fin n)
    (hab : a ≠ b)
    (hbefore : ∀ j : Fin n, j.val < a.val → P j r = 0)
    (ha : 0 < P a r) (hb : 0 < P b r) :
    1 < ∑ i, orderedMonomialSecantMatrix P rho r i := by
  have hprefixA : orderedPrefix (fun j => rho j ^ P j r) a = 1 := by
    unfold orderedPrefix
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_range] at hj
    unfold finLift
    split_ifs with hn
    · dsimp
      rw [hbefore ⟨j, hn⟩ hj]
      simp
    · omega
  have hA : 1 ≤ orderedMonomialSecantMatrix P rho r a := by
    unfold orderedMonomialSecantMatrix
    rw [hprefixA, one_mul]
    exact one_le_secantPoly_one (hrho a) ha
  have hB : 0 < orderedMonomialSecantMatrix P rho r b := by
    unfold orderedMonomialSecantMatrix orderedPrefix
    apply mul_pos
    · exact Finset.prod_pos fun j hj => by
        unfold finLift
        split_ifs with hn
        · exact pow_pos (hrho ⟨j, hn⟩) _
        · norm_num
    · exact secantPoly_pos (hrho b) (by norm_num) hb
  have hpair :
      orderedMonomialSecantMatrix P rho r a +
          orderedMonomialSecantMatrix P rho r b ≤
        ∑ i, orderedMonomialSecantMatrix P rho r i := by
    let s : Finset (Fin n) := {a, b}
    calc
      orderedMonomialSecantMatrix P rho r a +
          orderedMonomialSecantMatrix P rho r b =
          ∑ i ∈ s, orderedMonomialSecantMatrix P rho r i := by
            simp [s, hab]
      _ ≤ ∑ i, orderedMonomialSecantMatrix P rho r i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ s
        · intro i hi _
          exact orderedMonomialSecantMatrix_nonneg P hrho r i
  linarith

end TypeIIL
