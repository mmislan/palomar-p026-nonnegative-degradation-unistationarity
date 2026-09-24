import proofs.TypeIIL.OrderedMonomialSecantMatrix

namespace TypeIIL

open scoped BigOperators
open TypeII3

/-- Literal product-complex exponent matrix for a source cycle reaction.
Every reaction produces a positive integer number of copies of its successor;
a fork additionally produces one copy of its back target. -/
def sourceProductExponent {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) : Fin n → Fin n → ℕ :=
  fun i r => (if i = next r then weight r else 0) +
    match back r with
    | none => 0
    | some z => if i = z then 1 else 0

theorem sourceProductExponent_nonfork
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {r : Fin n}
    (hr : back r = none) (i : Fin n) :
    sourceProductExponent next weight back i r =
      if i = next r then weight r else 0 := by
  simp [sourceProductExponent, hr]

theorem sourceProductExponent_fork
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {r z i : Fin n}
    (hr : back r = some z) :
    sourceProductExponent next weight back i r =
      (if i = next r then weight r else 0) + (if i = z then 1 else 0) := by
  simp [sourceProductExponent, hr]

/-- A weighted nonfork product has ordered secant row sum at least one.  The
only active coordinate is the successor, so all earlier prefix factors are
one. -/
theorem one_le_source_nonfork_ordered_row_sum
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) {r : Fin n}
    (hr : back r = none) (hw : 0 < weight r) :
    1 ≤ ∑ i, orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho r i := by
  let s := next r
  have hprefix : orderedPrefix
      (fun j => rho j ^ sourceProductExponent next weight back j r) s = 1 := by
    unfold orderedPrefix
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_range] at hj
    unfold finLift
    split_ifs with hn
    · dsimp
      rw [sourceProductExponent_nonfork next weight back hr]
      rw [ite_eq_right]
      · simp
      · intro heq
        have := congrArg Fin.val heq
        dsimp [s] at hj this
        omega
    · omega
  have hs : 1 ≤ orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho r s := by
    unfold orderedMonomialSecantMatrix
    rw [hprefix, one_mul]
    rw [sourceProductExponent_nonfork next weight back hr]
    simpa [s] using one_le_secantPoly_one (hrho s) hw
  calc
    1 ≤ orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho r s := hs
    _ ≤ ∑ i, orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho r i := by
      apply Finset.single_le_sum
      intro i _
      exact orderedMonomialSecantMatrix_nonneg _ hrho r i
      simp

/-- Exact sparse row of a literal nonfork product. -/
theorem source_nonfork_ordered_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    {r : Fin n} (hr : back r = none) (i : Fin n) :
    orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho r i =
      if i = next r then secantPoly (rho i) 1 (weight r) else 0 := by
  by_cases hi : i = next r
  · subst i
    have hprefix : orderedPrefix
        (fun j => rho j ^ sourceProductExponent next weight back j r)
        (next r) = 1 := by
      unfold orderedPrefix
      apply Finset.prod_eq_one
      intro j hj
      simp only [Finset.mem_range] at hj
      unfold finLift
      split_ifs with hn
      · dsimp
        rw [sourceProductExponent_nonfork next weight back hr]
        rw [ite_eq_right]
        · simp
        · intro heq
          have hval : j = (next r).val := congrArg Fin.val heq
          omega
      · omega
    unfold orderedMonomialSecantMatrix
    rw [hprefix, one_mul]
    rw [sourceProductExponent_nonfork next weight back hr]
    simp
  · unfold orderedMonomialSecantMatrix
    rw [sourceProductExponent_nonfork next weight back hr]
    simp [hi, secantPoly]

/-- Minimality forces the terminal pre-fork source weight to one, so its sole
ordered coefficient is exactly one. -/
theorem source_nonfork_unit_ordered_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    {r : Fin n} (hr : back r = none) (hw : weight r = 1) (i : Fin n) :
    orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho r i =
      if i = next r then 1 else 0 := by
  rw [source_nonfork_ordered_entry next weight back hr]
  by_cases hi : i = next r <;> simp [hi, hw, secantPoly]

/-- Exact sparse ordered-secant row of a literal fork.  Keeping the two
ordered-prefix factors explicit records which coupling crosses the unique
coordinate-order wrap. -/
theorem source_fork_ordered_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    {r z i : Fin n} (hr : back r = some z) (hz : z ≠ next r) :
    orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho r i =
      if i = next r then
        orderedPrefix
            (fun j => rho j ^ sourceProductExponent next weight back j r) i *
          secantPoly (rho i) 1 (weight r)
      else if i = z then
        orderedPrefix
            (fun j => rho j ^ sourceProductExponent next weight back j r) i
      else 0 := by
  unfold orderedMonomialSecantMatrix
  rw [sourceProductExponent_fork next weight back hr]
  by_cases hin : i = next r
  · subst i
    simp [hz.symm]
  · rw [ite_eq_right hin]
    by_cases hiz : i = z
    · subst i
      simp [hz, secantPoly]
    · rw [ite_eq_right hiz]
      simp [hin, hiz, secantPoly]

/-- Every literal source fork has strict ordered-secant row gain: its
successor exponent is positive and its distinct back target has coefficient
one.  The proof chooses whichever of those coordinates occurs first in the
canonical paper order. -/
theorem one_lt_source_fork_ordered_row_sum
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) {r z : Fin n}
    (hr : back r = some z) (hw : 0 < weight r)
    (hz : z ≠ next r) :
    1 < ∑ i, orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho r i := by
  by_cases horder : z.val < (next r).val
  · apply one_lt_orderedMonomialSecantMatrix_row_sum_of_two_support
      (sourceProductExponent next weight back) hrho r z (next r) hz
    · intro j hj
      rw [sourceProductExponent_fork next weight back hr]
      have hjz : j ≠ z := by
        intro h
        have := congrArg Fin.val h
        omega
      have hjn : j ≠ next r := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hjz, hjn]
    · rw [sourceProductExponent_fork next weight back hr]
      simp [hz]
    · rw [sourceProductExponent_fork next weight back hr]
      simp [hw]
  · have hnz : (next r).val < z.val := by
      have hne : (next r).val ≠ z.val := by
        intro h
        apply hz
        exact Fin.ext h.symm
      omega
    apply one_lt_orderedMonomialSecantMatrix_row_sum_of_two_support
      (sourceProductExponent next weight back) hrho r (next r) z hz.symm
    · intro j hj
      rw [sourceProductExponent_fork next weight back hr]
      have hjn : j ≠ next r := by
        intro h
        have := congrArg Fin.val h
        omega
      have hjz : j ≠ z := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hjz, hjn]
    · rw [sourceProductExponent_fork next weight back hr]
      simp [hw]
    · rw [sourceProductExponent_fork next weight back hr]
      simp [hz]

end TypeIIL
