import proofs.TypeIIL.SourceForkGapAdapter

namespace TypeIIL

open scoped BigOperators

/-- Forcing produced at the first internal reaction by the left endpoint
fork, with the endpoint current scaled by `scale`. -/
def finiteSourcePathLeftForcing {m : ℕ}
    (A : Fin (m + 1) → ℝ) (scale : ℝ) : Fin (m + 1) → ℝ :=
  fun i => if i.val = 0 then A i * scale else 0

/-- Auxiliary nonnegative forcing concentrated at the last path coordinate.
For a literal right fork this is only the positive part of its boundary
column; a nonsingleton source gap also has a negative penultimate term. -/
def finiteSourcePathRightForcing {m : ℕ}
    (A c : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun i => if i.val = m then A i + c i else 0

/-- A response to only the left endpoint forcing is bounded by the same
cumulative supersolution as the two-ended physical response. -/
theorem finiteSourcePathLeftResponse_le_weight {m : ℕ}
    {A c s y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathLeftForcing A scale i) :
    ∀ i, y i ≤ scale * finiteSourcePathWeight s i := by
  apply zmatrix_solution_le_supersolution
    (finiteSourcePathMatrix A c s)
    (fun i => scale * finiteSourcePathWeight s i) y
    (finiteSourcePathLeftForcing A scale)
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_trans zero_le_one (hs i))
  · intro i
    exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      (finiteSourcePathWeight_pos
        (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
  · intro i
    have hfactor :
        (∑ j, finiteSourcePathMatrix A c s i j *
            (scale * finiteSourcePathWeight s j)) =
          scale * (∑ j, finiteSourcePathMatrix A c s i j *
            finiteSourcePathWeight s j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      (finiteSourcePathMatrix_mul_weight_pos hA hc
        (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
  · exact hsolve
  · intro i
    have hfull := finiteSourcePathBoundaryForcing_le_mul_weight
      hA hc hs hscale i
    have hsub : finiteSourcePathLeftForcing A scale i ≤
        finiteSourcePathBoundaryForcing A c scale i := by
      unfold finiteSourcePathLeftForcing finiteSourcePathBoundaryForcing
      split_ifs <;> linarith [hc i]
    exact le_trans hsub hfull

/-- The auxiliary one-sided endpoint responses are nonnegative. -/
theorem finiteSourcePathLeftResponse_nonneg {m : ℕ}
    {A c s y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathLeftForcing A scale i) :
    ∀ i, 0 ≤ y i := by
  apply zmatrix_solution_nonneg
    (finiteSourcePathMatrix A c s) (finiteSourcePathWeight s) y
    (finiteSourcePathLeftForcing A scale)
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_of_lt (hs i))
  · exact finiteSourcePathWeight_pos hs
  · exact finiteSourcePathMatrix_mul_weight_pos hA hc hs
  · intro i
    unfold finiteSourcePathLeftForcing
    split_ifs
    · exact mul_nonneg (hA i) hscale
    · exact le_rfl
  · exact hsolve

theorem finiteSourcePathRightResponse_nonneg {m : ℕ}
    {A c s y : Fin (m + 1) → ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathRightForcing A c i) :
    ∀ i, 0 ≤ y i := by
  apply zmatrix_solution_nonneg
    (finiteSourcePathMatrix A c s) (finiteSourcePathWeight s) y
    (finiteSourcePathRightForcing A c)
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_of_lt (hs i))
  · exact finiteSourcePathWeight_pos hs
  · exact finiteSourcePathMatrix_mul_weight_pos hA hc hs
  · intro i
    unfold finiteSourcePathRightForcing
    split_ifs
    · exact add_nonneg (hA i) (hc i)
    · exact le_rfl
  · exact hsolve

/-- Auxiliary following-gap response budget.  The left response can consume
at most the direct successor weight, while a nonnegative terminal response
has the compensating sign.  Literal nonsingleton docking additionally needs
the penultimate term in the right-fork column. -/
theorem finiteSourcePath_following_budget_nonneg {m : ℕ}
    {A c s x y : Fin (m + 1) → ℝ}
    {scale h : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale) (hh : 0 ≤ h)
    (hx : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * x j =
        finiteSourcePathLeftForcing A scale i)
    (hy : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathRightForcing A c i) :
    0 ≤ h * (scale - x 0 + y 0) := by
  have hx0 := finiteSourcePathLeftResponse_le_weight hA hc hs hscale hx 0
  have hy0 := finiteSourcePathRightResponse_nonneg hA hc
    (fun i => lt_of_lt_of_le zero_lt_one (hs i)) hy 0
  have hw0 : finiteSourcePathWeight s (0 : Fin (m + 1)) = 1 := by
    unfold finiteSourcePathWeight
    have hempty : Finset.Iio (0 : Fin (m + 1)) = ∅ := by
      ext j
      simp
    rw [hempty]
    simp
  rw [hw0, mul_one] at hx0
  exact mul_nonneg hh (by linarith)

/-- Positive numerator obtained by eliminating a two-reaction literal source
gap with its true mixed right-fork column.  `ER` is the degradation current
at the right fork.  The only subtraction groups as
`ER * k * q₀ * (s₀*sL - 1)`, so positive integer source weights close it.
This is the length-two seed for the arbitrary-gap continuant induction. -/
theorem two_reaction_source_gap_budget_numerator_pos
    {sL s₀ ER J₀ JR q₀ q₁ k : ℝ}
    (hsL : 1 ≤ sL) (hs₀ : 1 ≤ s₀)
    (hER : 0 < ER) (hJ₀ : 0 < J₀) (hJR : 0 < JR)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hk : 0 < k) :
    0 < ER * J₀ * s₀ * sL + ER * JR * sL +
        ER * k * q₀ * s₀ * sL - ER * k * q₀ +
        J₀ * q₁ * s₀ * sL + k * q₀ * q₁ * s₀ * sL := by
  have hw : 0 ≤ s₀ * sL - 1 := by
    exact sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hs₀ hsL)
  have hid :
      ER * J₀ * s₀ * sL + ER * JR * sL +
          ER * k * q₀ * s₀ * sL - ER * k * q₀ +
          J₀ * q₁ * s₀ * sL + k * q₀ * q₁ * s₀ * sL =
        ER * J₀ * s₀ * sL + ER * JR * sL +
          ER * k * q₀ * (s₀ * sL - 1) +
          J₀ * q₁ * s₀ * sL + k * q₀ * q₁ * s₀ * sL := by
    ring
  rw [hid]
  positivity

/-- Every product of source successor weights is at least one. -/
theorem one_le_source_weight_product
    {ws : List ℝ} (hws : ∀ w ∈ ws, 1 ≤ w) : 1 ≤ ws.prod := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      have hw : 1 ≤ w := hws w (by simp)
      have htail : ∀ x ∈ ws, 1 ≤ x := by
        intro x hx
        exact hws x (by simp [hx])
      simpa using one_le_mul_of_one_le_of_one_le hw (ih htail)

/-- The sole signed term exposed by the exact length-two and length-three
mixed-boundary eliminations is harmless for an arbitrary source path: it is
a nonnegative coefficient times the cumulative-weight defect. -/
theorem source_weight_defect_term_nonneg
    {ws : List ℝ} {coefficient : ℝ}
    (hws : ∀ w ∈ ws, 1 ≤ w) (hc : 0 ≤ coefficient) :
    0 ≤ coefficient * (ws.prod - 1) := by
  exact mul_nonneg hc (sub_nonneg.mpr (one_le_source_weight_product hws))

/-- The singleton coupled-wrap numerator remains strictly positive when a
compressed gap has an additional nonnegative diagonal killing margin.  Thus
arbitrary-gap reduction only needs to preserve `1 + A + c ≤ d`, not an
exact singleton normal form. -/
theorem compressed_wrap_core_margin_pos
    {A c g h k s d : ℝ}
    (hd : 1 + A + c ≤ d)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hs : 0 < s) :
    0 < (d + g + h) * (d + k * s * (1 + c)) -
      s * (h * (1 + c) - g * A) * k := by
  let d₀ := 1 + A + c
  have hd₀ : d₀ = 1 + A + c := rfl
  have hcore := singleton_wrap_core_margin_pos hd₀ hA hc hg hh hk hs
  have hd₀0 : 0 ≤ d₀ := by dsimp [d₀]; positivity
  have hleft₀ : 0 ≤ d₀ + g + h := by positivity
  have hright₀ : 0 ≤ d₀ + k * s * (1 + c) := by positivity
  have hleft : d₀ + g + h ≤ d + g + h := by dsimp [d₀] at hd ⊢; linarith
  have hright : d₀ + k * s * (1 + c) ≤
      d + k * s * (1 + c) := by dsimp [d₀] at hd ⊢; linarith
  have hprod :
      (d₀ + g + h) * (d₀ + k * s * (1 + c)) ≤
        (d + g + h) * (d + k * s * (1 + c)) := by
    exact mul_le_mul hleft hright hright₀
      (le_trans hd₀0 (by linarith [hg, hh]))
  linarith

end TypeIIL
