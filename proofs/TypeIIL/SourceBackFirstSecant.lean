import proofs.TypeIIL.SourceCurrentMatrix

namespace TypeIIL

open scoped BigOperators
open TypeII3

/-! A source-adapted exact monomial secant.

The telescoping order of a product is a gauge choice.  For every fork row we
expand the coefficient-one back factor first and the weighted successor factor
second.  Thus all fork rows enjoy the same local order, independently of the
ambient numbering of `Fin n`; the artificial cyclic coordinate seam disappears.
-/

noncomputable def sourceBackFirstSecantMatrix {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r i =>
    match back r with
    | none =>
        if i = next r then secantPoly (rho i) 1 (weight r) else 0
    | some z =>
        if i = z then 1
        else if i = next r then rho z * secantPoly (rho i) 1 (weight r)
        else 0

theorem sourceBackFirstSecantMatrix_nonfork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r : Fin n} (hr : back r = none) (i : Fin n) :
    sourceBackFirstSecantMatrix next weight back rho r i =
      if i = next r then secantPoly (rho i) 1 (weight r) else 0 := by
  rw [sourceBackFirstSecantMatrix]
  simp [hr]

theorem sourceBackFirstSecantMatrix_fork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z) (i : Fin n) :
    sourceBackFirstSecantMatrix next weight back rho r i =
      if i = z then 1
      else if i = next r then rho z * secantPoly (rho i) 1 (weight r)
      else 0 := by
  rw [sourceBackFirstSecantMatrix]
  simp [hr]

theorem monomialRatio_source_nonfork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r : Fin n} (hr : back r = none) :
    monomialRatio (sourceProductExponent next weight back) rho r =
      rho (next r) ^ weight r := by
  classical
  unfold monomialRatio
  simp_rw [sourceProductExponent_nonfork next weight back hr]
  simp

theorem monomialRatio_source_fork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z) :
    monomialRatio (sourceProductExponent next weight back) rho r =
      rho z * rho (next r) ^ weight r := by
  classical
  unfold monomialRatio
  simp_rw [sourceProductExponent_fork next weight back hr]
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]
  simp
  ring

/-- Exact secant identity, with a rowwise telescoping gauge that always puts
the back target first. -/
theorem sourceBackFirstSecantMatrix_mul_ratio_sub_one {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    (hbackDistinct : ∀ r z, back r = some z → z ≠ next r)
    (r : Fin n) :
    ∑ i, sourceBackFirstSecantMatrix next weight back rho r i *
        (rho i - 1) =
      monomialRatio (sourceProductExponent next weight back) rho r - 1 := by
  classical
  cases h : back r with
  | none =>
      rw [monomialRatio_source_nonfork next weight back rho h]
      rw [show (∑ i, sourceBackFirstSecantMatrix next weight back rho r i *
          (rho i - 1)) =
          secantPoly (rho (next r)) 1 (weight r) *
            (rho (next r) - 1) by
        rw [Fintype.sum_eq_single (next r)]
        · rw [sourceBackFirstSecantMatrix_nonfork next weight back rho h]
          simp
        · intro i hi
          rw [sourceBackFirstSecantMatrix_nonfork next weight back rho h]
          simp [hi]
        ]
      simpa [one_pow, mul_comm] using
        (pow_sub_pow_eq_mul_secantPoly (rho (next r)) 1 (weight r)).symm
  | some z =>
      by_cases hz : z = next r
      · exact False.elim ((hbackDistinct r z h) hz)
      · rw [monomialRatio_source_fork next weight back rho h]
        rw [show (∑ i, sourceBackFirstSecantMatrix next weight back rho r i *
            (rho i - 1)) =
            (rho z - 1) +
              (rho z * secantPoly (rho (next r)) 1 (weight r)) *
                (rho (next r) - 1) by
          have hpoint : ∀ i,
              sourceBackFirstSecantMatrix next weight back rho r i *
                  (rho i - 1) =
                (if i = z then rho z - 1 else 0) +
                (if i = next r then
                    (rho z * secantPoly (rho (next r)) 1 (weight r)) *
                      (rho (next r) - 1)
                  else 0) := by
            intro i
            rw [sourceBackFirstSecantMatrix_fork next weight back rho h]
            by_cases hiz : i = z
            · subst i
              simp [hz]
            · by_cases hin : i = next r
              · subst i
                simp [Ne.symm hz]
              · simp [hiz, hin]
          simp_rw [hpoint, Finset.sum_add_distrib]
          simp]
        have hp := pow_sub_pow_eq_mul_secantPoly
          (rho (next r)) 1 (weight r)
        simp only [one_pow] at hp
        calc
          rho z - 1 +
                rho z * secantPoly (rho (next r)) 1 (weight r) *
                  (rho (next r) - 1) =
              rho z *
                  (1 + (rho (next r) - 1) *
                    secantPoly (rho (next r)) 1 (weight r)) - 1 := by ring
          _ = rho z * rho (next r) ^ weight r - 1 := by rw [← hp]; ring

theorem sourceBackFirstSecantMatrix_nonneg {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) (r i : Fin n) :
    0 ≤ sourceBackFirstSecantMatrix next weight back rho r i := by
  cases h : back r with
  | none =>
      rw [sourceBackFirstSecantMatrix_nonfork next weight back rho h]
      split
      · exact secantPoly_nonneg (hrho i) (by norm_num) _
      · exact le_rfl
  | some z =>
      by_cases hz : z = next r
      · subst z
        by_cases hi : i = next r
        · subst i
          simp [sourceBackFirstSecantMatrix, h]
        · simp [sourceBackFirstSecantMatrix, h, hi]
      · rw [sourceBackFirstSecantMatrix_fork next weight back rho h]
        split
        · norm_num
        · split
          · exact mul_nonneg (le_of_lt (hrho _))
              (secantPoly_nonneg (hrho _) (by norm_num) _)
          · exact le_rfl

theorem sourceBackFirstSecantMatrix_row_gain_nonfork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) {r : Fin n}
    (hr : back r = none) (hw : 0 < weight r) :
    1 ≤ ∑ i, sourceBackFirstSecantMatrix next weight back rho r i := by
  rw [show (∑ i, sourceBackFirstSecantMatrix next weight back rho r i) =
      secantPoly (rho (next r)) 1 (weight r) by
    rw [Fintype.sum_eq_single (next r)]
    · rw [sourceBackFirstSecantMatrix_nonfork next weight back rho hr]
      simp
    · intro i hi
      rw [sourceBackFirstSecantMatrix_nonfork next weight back rho hr]
      simp [hi]
    ]
  exact one_le_secantPoly_one (hrho _) hw

theorem sourceBackFirstSecantMatrix_row_gain_fork {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) {r z : Fin n}
    (hr : back r = some z) (hz : z ≠ next r) (hw : 0 < weight r) :
    1 < ∑ i, sourceBackFirstSecantMatrix next weight back rho r i := by
  have hnext : 0 < sourceBackFirstSecantMatrix next weight back rho r (next r) := by
    rw [sourceBackFirstSecantMatrix_fork next weight back rho hr]
    simp [Ne.symm hz]
    exact mul_pos (hrho z) (secantPoly_pos (hrho _) (by norm_num) hw)
  have hzentry : sourceBackFirstSecantMatrix next weight back rho r z = 1 := by
    rw [sourceBackFirstSecantMatrix_fork next weight back rho hr]
    simp
  calc
    1 < sourceBackFirstSecantMatrix next weight back rho r z +
        sourceBackFirstSecantMatrix next weight back rho r (next r) := by
          rw [hzentry]
          linarith
    _ ≤ ∑ i, sourceBackFirstSecantMatrix next weight back rho r i := by
      let s : Finset (Fin n) := {z, next r}
      rw [show sourceBackFirstSecantMatrix next weight back rho r z +
          sourceBackFirstSecantMatrix next weight back rho r (next r) =
          ∑ i ∈ s, sourceBackFirstSecantMatrix next weight back rho r i by
        simp [s, hz]]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro i hi _
      exact sourceBackFirstSecantMatrix_nonneg next weight back hrho r i

end TypeIIL
