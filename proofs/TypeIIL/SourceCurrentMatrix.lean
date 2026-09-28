module

public import proofs.TypeIIL.SourceCurrentResidual

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- Literal square stoichiometric matrix of the source cycle: consume one
copy of reaction `k`'s source species and produce its declared successor/back
complex. -/
def sourceStoich {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => (sourceProductExponent next weight back i k : ℝ) -
    if i = k then 1 else 0

theorem sourceStoich_apply
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (i k : Fin n) :
    sourceStoich next weight back i k =
      (sourceProductExponent next weight back i k : ℝ) -
        if i = k then 1 else 0 := rfl

theorem sourceStoich_eq_zero_of_off_support
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {i k : Fin n}
    (hik : i ≠ k) (hinext : i ≠ next k)
    (hiback : ∀ z, back k = some z → i ≠ z) :
    sourceStoich next weight back i k = 0 := by
  unfold sourceStoich sourceProductExponent
  cases h : back k with
  | none => simp [hik, hinext]
  | some z =>
      have hiz : i ≠ z := hiback z h
      simp [hik, hinext, hiz]

theorem sourceStoich_source_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {k : Fin n}
    (hnext : k ≠ next k)
    (hback : ∀ z, back k = some z → k ≠ z) :
    sourceStoich next weight back k k = -1 := by
  unfold sourceStoich sourceProductExponent
  cases h : back k with
  | none => simp [hnext]
  | some z =>
      have hkz : k ≠ z := hback z h
      simp [hnext, hkz]

theorem sourceStoich_successor_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {k : Fin n}
    (hnext : next k ≠ k)
    (hback : ∀ z, back k = some z → next k ≠ z) :
    sourceStoich next weight back (next k) k = weight k := by
  unfold sourceStoich sourceProductExponent
  cases h : back k with
  | none => simp [hnext]
  | some z =>
      have hnz : next k ≠ z := hback z h
      simp [hnext, hnz]

theorem sourceStoich_back_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {k z : Fin n}
    (h : back k = some z) (hsource : z ≠ k) (hnext : z ≠ next k) :
    sourceStoich next weight back z k = 1 := by
  unfold sourceStoich sourceProductExponent
  simp [h, hsource, hnext]

/-- Entrywise expansion of the generic current kernel.  The first term is
the direct source-current response; the second is the positive ordered
product-secant correction.  This is the starting formula for the literal
nonfork tridiagonal and fork boundary calculations. -/
theorem currentSecantKernelMatrixWith_entry_expansion
    {n : ℕ} (C N : Matrix (Fin n) (Fin n) ℝ)
    {p q e : Fin n → ℝ} (r k : Fin n) :
    currentSecantKernelMatrixWith C N p q e r k =
      (if r = k then 1 else 0) - (p r / e r) * N r k +
        q r * ∑ i, (C r i / e i) * N i k := by
  classical
  unfold currentSecantKernelMatrixWith currentResponseCoeffWith
  have hdiag :
      (∑ i, ((if r = i then p r else 0) / e i) * N i k) =
        (p r / e r) * N r k := by
    calc
      (∑ i, ((if r = i then p r else 0) / e i) * N i k) =
          ((if r = r then p r else 0) / e r) * N r k := by
        apply Fintype.sum_eq_single r
        intro b hb
        simp [Ne.symm hb]
      _ = (p r / e r) * N r k := by simp
  simp_rw [sub_div, sub_mul]
  rw [Finset.sum_sub_distrib, hdiag, Finset.mul_sum]
  ring_nf

/-- Source-specialized form of the entry expansion. -/
theorem sourceOrderedCurrentMatrix_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} (r k : Fin n) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r k =
      (if r = k then 1 else 0) -
        (p r / e r) * sourceStoich next weight back r k +
        q r * ∑ i,
          (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho r i / e i) *
            sourceStoich next weight back i k := by
  exact currentSecantKernelMatrixWith_entry_expansion _ _ r k

/-- A literal nonfork row of the source current matrix depends only on its
source stoichiometric row and the stoichiometric row of its successor.  This
is the exact two-row adapter from the paper object to the path-block
calculation. -/
theorem sourceOrderedCurrentMatrix_nonfork_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r : Fin n}
    (hr : back r = none) (k : Fin n) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r k =
      (if r = k then 1 else 0) -
        (p r / e r) * sourceStoich next weight back r k +
        q r *
          ((TypeII3.secantPoly (rho (next r)) 1 (weight r) / e (next r)) *
            sourceStoich next weight back (next r) k) := by
  classical
  rw [sourceOrderedCurrentMatrix_entry]
  congr 1
  rw [Finset.sum_eq_single (next r)]
  · rw [source_nonfork_ordered_entry next weight back hr]
    simp
  · intro i hi hne
    rw [source_nonfork_ordered_entry next weight back hr]
    simp [hne]
  · simp

theorem sourceOrderedCurrentMatrix_nonfork_diagonal
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r : Fin n}
    (hr : back r = none) (hnext : r ≠ next r) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r r =
      1 + p r / e r +
        q r * (TypeII3.secantPoly (rho (next r)) 1 (weight r) /
          e (next r)) * weight r := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back hr]
  rw [sourceStoich_source_entry next weight back hnext (by simp [hr])]
  rw [sourceStoich_successor_entry next weight back hnext.symm (by simp [hr])]
  simp
  ring

theorem sourceOrderedCurrentMatrix_nonfork_successor
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r : Fin n}
    (hr : back r = none) (hrn : r ≠ next r)
    (hrr : r ≠ next (next r))
    (hn : back (next r) = none)
    (hnn : next r ≠ next (next r)) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r (next r) =
      -(q r * (TypeII3.secantPoly (rho (next r)) 1 (weight r) /
        e (next r))) := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back hr]
  rw [sourceStoich_eq_zero_of_off_support next weight back hrn hrr (by simp [hn])]
  rw [sourceStoich_source_entry next weight back hnn (by simp [hn])]
  simp [hrn]

theorem sourceOrderedCurrentMatrix_nonfork_predecessor
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {prev r : Fin n}
    (hr : back r = none) (hp : back prev = none)
    (hpr : next prev = r) (hne : prev ≠ r) (hpn : prev ≠ next r)
    (hrn : r ≠ next r) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r prev =
      -(p r / e r * weight prev) := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back hr]
  have hsource : sourceStoich next weight back r prev = weight prev := by
    rw [← hpr]
    exact sourceStoich_successor_entry next weight back
      (by simpa [hpr] using hne.symm) (by simp [hp])
  rw [hsource]
  rw [sourceStoich_eq_zero_of_off_support next weight back hpn.symm
    (by simpa [hpr] using hrn.symm) (by simp [hp])]
  simp [hne.symm]

theorem sourceOrderedCurrentMatrix_nonfork_off_support
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r k : Fin n}
    (hr : back r = none) (hk : back k = none)
    (hkr : k ≠ r) (hnkr : next k ≠ r)
    (hkn : k ≠ next r) (hnkn : next k ≠ next r) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r k = 0 := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back hr]
  rw [sourceStoich_eq_zero_of_off_support next weight back hkr.symm
    hnkr.symm (by simp [hk])]
  rw [sourceStoich_eq_zero_of_off_support next weight back hkn.symm
    hnkn.symm (by simp [hk])]
  simp [hkr.symm]

noncomputable def sourceForkNextCoeff
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    (r : Fin n) : ℝ :=
  orderedPrefix
      (fun j => rho j ^ sourceProductExponent next weight back j r) (next r) *
    TypeII3.secantPoly (rho (next r)) 1 (weight r)

noncomputable def sourceForkBackCoeff
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    (r z : Fin n) : ℝ :=
  orderedPrefix
    (fun j => rho j ^ sourceProductExponent next weight back j r) z

theorem sourceForkNextCoeff_pos
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) (hw : ∀ i, 0 < weight i) (r : Fin n) :
    0 < sourceForkNextCoeff next weight back rho r := by
  unfold sourceForkNextCoeff
  exact mul_pos
    (orderedPrefix_pos (fun j => pow_pos (hrho j) _) (next r))
    (TypeII3.secantPoly_pos (hrho (next r)) (by norm_num) (hw r))

theorem sourceForkBackCoeff_pos
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) {rho : Fin n → ℝ}
    (hrho : ∀ i, 0 < rho i) (r z : Fin n) :
    0 < sourceForkBackCoeff next weight back rho r z := by
  unfold sourceForkBackCoeff
  exact orderedPrefix_pos (fun j => pow_pos (hrho j) _) z

/-- Away from the unique coordinate-order wrap, the back target is the first
active product coordinate, so its ordered secant coefficient is exactly one. -/
theorem sourceForkBackCoeff_eq_one_of_back_lt_next
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z)
    (horder : z.val < (next r).val) :
    sourceForkBackCoeff next weight back rho r z = 1 := by
  unfold sourceForkBackCoeff orderedPrefix
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_range] at hj
  unfold finLift
  split_ifs with hjn
  · let x : Fin n := ⟨j, hjn⟩
    have hxz : x ≠ z := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [x] at hv
      omega
    have hxn : x ≠ next r := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [x] at hv
      omega
    change rho x ^ sourceProductExponent next weight back x r = 1
    rw [sourceProductExponent_fork next weight back hr]
    simp [hxz, hxn]
  · omega

/-- At the sole coordinate-order wrap, the successor is the first active
product coordinate, so its prefix is one. -/
theorem sourceForkNextCoeff_eq_secant_of_next_lt_back
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z)
    (horder : (next r).val < z.val) :
    sourceForkNextCoeff next weight back rho r =
      TypeII3.secantPoly (rho (next r)) 1 (weight r) := by
  unfold sourceForkNextCoeff
  have hprefix : orderedPrefix
      (fun j => rho j ^ sourceProductExponent next weight back j r) (next r) = 1 := by
    unfold orderedPrefix
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_range] at hj
    unfold finLift
    split_ifs with hjn
    · let x : Fin n := ⟨j, hjn⟩
      have hxn : x ≠ next r := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [x] at hv
        omega
      have hxz : x ≠ z := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [x] at hv
        omega
      change rho x ^ sourceProductExponent next weight back x r = 1
      rw [sourceProductExponent_fork next weight back hr]
      simp [hxn, hxz]
    · omega
  rw [hprefix, one_mul]

/-- Off the wrap, the back coordinate contributes its ratio before the
successor secant is taken. -/
theorem sourceForkNextCoeff_eq_back_mul_secant_of_back_lt_next
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z) (hz : z ≠ next r)
    (horder : z.val < (next r).val) :
    sourceForkNextCoeff next weight back rho r =
      rho z * TypeII3.secantPoly (rho (next r)) 1 (weight r) := by
  unfold sourceForkNextCoeff
  have hprefix : orderedPrefix
      (fun j => rho j ^ sourceProductExponent next weight back j r) (next r) =
      rho z := by
    unfold orderedPrefix
    rw [Finset.prod_eq_ite z.val]
    · rw [ite_eq_left (Finset.mem_range.mpr horder)]
      unfold finLift
      rw [dite_eq_left z.isLt]
      change rho z ^ sourceProductExponent next weight back z r = rho z
      rw [sourceProductExponent_fork next weight back hr]
      simp [hz]
    · intro j hj hjz
      simp only [Finset.mem_range] at hj
      unfold finLift
      split_ifs with hjn
      · let x : Fin n := ⟨j, hjn⟩
        have hxz : x ≠ z := by
          intro h
          apply hjz
          exact congrArg Fin.val h
        have hxn : x ≠ next r := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [x] at hv
          omega
        change rho x ^ sourceProductExponent next weight back x r = 1
        rw [sourceProductExponent_fork next weight back hr]
        simp [hxz, hxn]
      · omega
  rw [hprefix]

/-- At the wrap, the successor monomial is the entire prefix seen by the
later back coordinate. -/
theorem sourceForkBackCoeff_eq_next_pow_of_next_lt_back
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z) (hz : z ≠ next r)
    (horder : (next r).val < z.val) :
    sourceForkBackCoeff next weight back rho r z =
      rho (next r) ^ weight r := by
  unfold sourceForkBackCoeff orderedPrefix
  rw [Finset.prod_eq_ite (next r).val]
  · rw [ite_eq_left (Finset.mem_range.mpr horder)]
    unfold finLift
    rw [dite_eq_left (next r).isLt]
    change rho (next r) ^ sourceProductExponent next weight back (next r) r =
      rho (next r) ^ weight r
    rw [sourceProductExponent_fork next weight back hr]
    simp [hz.symm]
  · intro j hj hjnval
    simp only [Finset.mem_range] at hj
    unfold finLift
    split_ifs with hjn
    · let x : Fin n := ⟨j, hjn⟩
      have hxn : x ≠ next r := by
        intro h
        apply hjnval
        exact congrArg Fin.val h
      have hxz : x ≠ z := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [x] at hv
        omega
      change rho x ^ sourceProductExponent next weight back x r = 1
      rw [sourceProductExponent_fork next weight back hr]
      simp [hxn, hxz]
    · omega

/-- A literal fork current row is supported through exactly the source,
successor, and back-target stoichiometric rows. -/
theorem sourceOrderedCurrentMatrix_fork_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r z : Fin n}
    (hr : back r = some z) (hz : z ≠ next r) (k : Fin n) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r k =
      (if r = k then 1 else 0) -
        (p r / e r) * sourceStoich next weight back r k +
        q r *
          ((sourceForkNextCoeff next weight back rho r / e (next r)) *
              sourceStoich next weight back (next r) k +
            (sourceForkBackCoeff next weight back rho r z / e z) *
              sourceStoich next weight back z k) := by
  rw [sourceOrderedCurrentMatrix_entry]
  congr 1
  apply congrArg (q r * ·)
  classical
  calc
    ∑ x,
        (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho r x / e x) *
          sourceStoich next weight back x k =
        ∑ x, if next r = x then
          (sourceForkNextCoeff next weight back rho r / e (next r)) *
            sourceStoich next weight back (next r) k
        else if z = x then
          (sourceForkBackCoeff next weight back rho r z / e z) *
            sourceStoich next weight back z k
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [source_fork_ordered_entry next weight back hr hz]
      by_cases hx : x = next r
      · subst x
        simp [sourceForkNextCoeff]
      · rw [ite_eq_right hx]
        by_cases hxz : x = z
        · subst x
          have hnz : next r ≠ z := hz.symm
          simp [hnz, sourceForkBackCoeff]
        · rw [ite_eq_right hxz]
          have hnx : next r ≠ x := Ne.symm hx
          have hzx : z ≠ x := Ne.symm hxz
          simp [hnx, hzx]
    _ =
        (sourceForkNextCoeff next weight back rho r / e (next r)) *
            sourceStoich next weight back (next r) k +
          (sourceForkBackCoeff next weight back rho r z / e z) *
            sourceStoich next weight back z k := by
      let A := (sourceForkNextCoeff next weight back rho r / e (next r)) *
        sourceStoich next weight back (next r) k
      let B := (sourceForkBackCoeff next weight back rho r z / e z) *
        sourceStoich next weight back z k
      have hsplit : ∀ x : Fin n,
          (if next r = x then A else if z = x then B else 0) =
            (if next r = x then A else 0) + (if z = x then B else 0) := by
        intro x
        by_cases hn : next r = x
        · subst x
          simp [hz]
        · by_cases hz' : z = x <;> simp [hn, hz']
      calc
        ∑ x, (if next r = x then A else if z = x then B else 0) =
            ∑ x, ((if next r = x then A else 0) +
              (if z = x then B else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hsplit x
        _ = (∑ x, if next r = x then A else 0) +
              ∑ x, if z = x then B else 0 := Finset.sum_add_distrib
        _ = A + B := by simp
        _ = _ := by rfl

/-- Exact diagonal coefficient of a literal fork row.  Both product supports
contribute positively to the diagonal through the source stoichiometric
column; this is the uneliminated source of the Schur diagonal margin. -/
theorem sourceOrderedCurrentMatrix_fork_diagonal
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r z : Fin n}
    (hr : back r = some z) (hz : z ≠ next r)
    (hrn : r ≠ next r) (hzr : z ≠ r) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r r =
      1 + p r / e r + q r *
        (sourceForkNextCoeff next weight back rho r / e (next r) * weight r +
          sourceForkBackCoeff next weight back rho r z / e z) := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back hr hz]
  rw [sourceStoich_source_entry next weight back hrn (by
    intro x hx
    rw [hr] at hx
    injection hx with hxz
    simpa [hxz] using hzr.symm)]
  rw [sourceStoich_successor_entry next weight back hrn.symm (by
    intro x hx
    rw [hr] at hx
    injection hx with hxz
    simpa [hxz] using hz.symm)]
  rw [sourceStoich_back_entry next weight back hr hzr hz]
  simp

theorem one_lt_sourceOrderedCurrentMatrix_fork_diagonal
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r z : Fin n}
    (hr : back r = some z) (hz : z ≠ next r)
    (hrn : r ≠ next r) (hzr : z ≠ r)
    (hp : 0 ≤ p r) (hq : 0 < q r)
    (he : ∀ i, 0 < e i) (hrho : ∀ i, 0 < rho i)
    (hw : ∀ i, 0 < weight i) :
    1 < currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r r := by
  rw [sourceOrderedCurrentMatrix_fork_diagonal next weight back hr hz hrn hzr]
  have hnext : 0 < sourceForkNextCoeff next weight back rho r :=
    sourceForkNextCoeff_pos next weight back hrho hw r
  have hback : 0 < sourceForkBackCoeff next weight back rho r z :=
    sourceForkBackCoeff_pos next weight back hrho r z
  have hwreal : 0 < (weight r : ℝ) := by exact_mod_cast hw r
  have hpdiv : 0 ≤ p r / e r := div_nonneg hp (le_of_lt (he r))
  have htermNext : 0 <
      sourceForkNextCoeff next weight back rho r / e (next r) * weight r :=
    mul_pos (div_pos hnext (he (next r))) hwreal
  have htermBack : 0 <
      sourceForkBackCoeff next weight back rho r z / e z :=
    div_pos hback (he z)
  have hinside : 0 <
      sourceForkNextCoeff next weight back rho r / e (next r) * weight r +
        sourceForkBackCoeff next weight back rho r z / e z := by
    exact add_pos htermNext htermBack
  nlinarith [mul_pos hq hinside]

end TypeIIL
