import proofs.TypeIIL.SourceWrapTwoNode
import proofs.TypeIIL.SourceWrapGapAdapter

namespace TypeIIL

/-- Prefix state after eliminating coordinates `0,...,r-1` of an abstract
source path represented by natural-indexed coefficient functions. -/
noncomputable def natWrapPrefixState
    (A c s : ℕ → ℝ) (scale k : ℝ) : ℕ → WrapPrefixState
  | 0 => { A := A 0, scale := scale, k := k }
  | r + 1 => wrapPrefixStep (natWrapPrefixState A c s scale k r)
      (A (r + 1)) (c r) (s r)

/-- Natural-indexed list of the first `r` pivot triples. -/
noncomputable def natWrapPrefixSteps
    (A c s : ℕ → ℝ) (r : ℕ) : List (ℝ × ℝ × ℝ) :=
  (List.range r).map fun i => (A (i + 1), c i, s i)

/-- The recursive natural-indexed state is exactly the existing list fold,
so equation induction and the coupled-margin theorem use the same object. -/
theorem natWrapPrefixState_eq_fold
    (A c s : ℕ → ℝ) (scale k : ℝ) : ∀ r,
    natWrapPrefixState A c s scale k r =
      wrapPrefixFold (natWrapPrefixState A c s scale k 0)
        (natWrapPrefixSteps A c s r) := by
  intro r
  induction r with
  | zero => simp [natWrapPrefixSteps, wrapPrefixFold]
  | succ r ih =>
      change wrapPrefixStep (natWrapPrefixState A c s scale k r)
        (A (r + 1)) (c r) (s r) = _
      rw [ih]
      simp [natWrapPrefixSteps, List.range_succ, wrapPrefixFold,
        List.foldl_append, wrapPrefixStep]

/-- Positive source coefficients keep every natural-indexed prefix state
strictly positive. -/
theorem natWrapPrefixState_pos
    (A c s : ℕ → ℝ) {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k) :
    ∀ r, (natWrapPrefixState A c s scale k r).StrictlyPositive := by
  intro r
  induction r with
  | zero => exact ⟨hA 0, hscale, hk⟩
  | succ r ih =>
      exact wrapPrefixStep_pos ih (hA (r + 1)) (hc r) (hs r)

/-- Arbitrary-length inverse-free Gaussian induction.  Starting from the
first boundary equation and the raw tridiagonal rows, this constructs the
exact condensed front equation after `r` pivots. -/
theorem natWrapPrefixEquationDerivation
    (A c s x : ℕ → ℝ) {scale k L : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation (natWrapPrefixState A c s scale k 0)
        (c 0) (s 0) L (x 0) (x 1))
    (hrows : ∀ i < r,
      (-A (i + 1) * s i) * x i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
          c (i + 1) * x (i + 2) = 0) :
    WrapPrefixEquationDerivation L
      (natWrapPrefixState A c s scale k r)
      (c r) (s r) (x r) (x (r + 1)) := by
  induction r with
  | zero => exact .base hfirst
  | succ r ih =>
      have hprior := ih (fun i hi => hrows i (Nat.lt_succ_of_lt hi))
      have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
      apply WrapPrefixEquationDerivation.step hprior
      · exact ne_of_gt (wrapPrefixPivot_pos (le_of_lt hpos.1)
          (le_of_lt (hc r)) (le_of_lt (hs r)))
      · linarith [hpos.1]
      · exact hrows r (Nat.lt_succ_self r)

/-- Usable equation extracted from the arbitrary natural-indexed
derivation. -/
theorem natWrapPrefixEquation
    (A c s x : ℕ → ℝ) {scale k L : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation (natWrapPrefixState A c s scale k 0)
        (c 0) (s 0) L (x 0) (x 1))
    (hrows : ∀ i < r,
      (-A (i + 1) * s i) * x i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
          c (i + 1) * x (i + 2) = 0) :
    wrapFrontEquation (natWrapPrefixState A c s scale k r)
      (c r) (s r) L (x r) (x (r + 1)) := by
  exact (natWrapPrefixEquationDerivation A c s x r hA hc hs hscale hk
    hfirst hrows).equation

/-- The forward boundary flux is invariant under prefix condensation.  To
transport from coordinate `0` to coordinate `r`, only rows strictly before
`r` are needed; in particular a forcing at the reserved terminal row does
not enter this identity. -/
theorem natWrapForwardTransport
    (A c s x : ℕ → ℝ) {scale k : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation (natWrapPrefixState A c s scale k 0)
        (c 0) (s 0) 0 (x 0) (x 1))
    (hrows : ∀ i, i + 1 < r →
      (-A (i + 1) * s i) * x i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
          c (i + 1) * x (i + 2) = 0) :
    k * x 0 = (natWrapPrefixState A c s scale k r).k * x r := by
  induction r with
  | zero => simp [natWrapPrefixState]
  | succ r ih =>
      have hprior : ∀ i, i + 1 < r →
          (-A (i + 1) * s i) * x i +
            (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
              c (i + 1) * x (i + 2) = 0 := by
        intro i hi
        exact hrows i (by omega)
      have hi := ih hprior
      have hfront := natWrapPrefixEquation A c s x r hA hc hs hscale hk
        hfirst (by
          intro i hi
          exact hrows i (by omega))
      have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
      have hpiv : 0 < wrapPrefixPivot
          (natWrapPrefixState A c s scale k r).A (c r) (s r) :=
        wrapPrefixPivot_pos (le_of_lt hpos.1) (le_of_lt (hc r))
          (le_of_lt (hs r))
      change
        wrapPrefixPivot (natWrapPrefixState A c s scale k r).A
            (c r) (s r) * x r - c r * x (r + 1) -
          (natWrapPrefixState A c s scale k r).A *
            (natWrapPrefixState A c s scale k r).scale * 0 = 0 at hfront
      change k * x 0 =
        (wrapPrefixStep (natWrapPrefixState A c s scale k r)
          (A (r + 1)) (c r) (s r)).k * x (r + 1)
      dsimp only [wrapPrefixStep]
      unfold wrapCondensedK
      have hfront' :
          wrapPrefixPivot (natWrapPrefixState A c s scale k r).A
              (c r) (s r) * x r = c r * x (r + 1) := by
        linarith [hfront]
      have hmul :
          k * x 0 * wrapPrefixPivot
              (natWrapPrefixState A c s scale k r).A (c r) (s r) =
            (natWrapPrefixState A c s scale k r).k * c r * x (r + 1) := by
        calc
          k * x 0 * wrapPrefixPivot
                (natWrapPrefixState A c s scale k r).A (c r) (s r) =
              ((natWrapPrefixState A c s scale k r).k * x r) *
                wrapPrefixPivot
                  (natWrapPrefixState A c s scale k r).A (c r) (s r) := by
                    rw [hi]
          _ = (natWrapPrefixState A c s scale k r).k *
                (wrapPrefixPivot
                  (natWrapPrefixState A c s scale k r).A (c r) (s r) * x r) := by
                    ring
          _ = (natWrapPrefixState A c s scale k r).k *
                (c r * x (r + 1)) := by rw [hfront']
          _ = _ := by ring
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff (ne_of_gt hpiv)).2 hmul

/-- Total natural-number access to a finite path, clamped only outside the
range used by a prefix proof. -/
def finitePathClamp (m i : ℕ) : Fin (m + 1) :=
  ⟨min i m, by omega⟩

@[simp] theorem finitePathClamp_val_of_le {m i : ℕ} (hi : i ≤ m) :
    (finitePathClamp m i).val = i := by
  simp [finitePathClamp, min_eq_left hi]

/-- The abstract natural recurrence instantiated with literal `Fin (m+1)`
path coefficients.  Only rows `1,...,r` are consumed, so `r < m` leaves the
last edge and terminal row for the exact two-node condensation. -/
theorem finiteSourcePath_prefix_equation_of_rows
    {m : ℕ} (A c s x : Fin (m + 1) → ℝ)
    {scale k L : ℝ} (r : ℕ) (hr : r < m)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation
        { A := A ⟨0, by omega⟩, scale := scale, k := k }
        (c ⟨0, by omega⟩) (s ⟨0, by omega⟩) L
        (x ⟨0, by omega⟩) (x ⟨1, by omega⟩))
    (hrows : ∀ i (hi : i < r),
      (-A ⟨i + 1, by omega⟩ * s ⟨i, by omega⟩) *
          x ⟨i, by omega⟩ +
        (1 + A ⟨i + 1, by omega⟩ +
            c ⟨i + 1, by omega⟩ * s ⟨i + 1, by omega⟩) *
          x ⟨i + 1, by omega⟩ -
        c ⟨i + 1, by omega⟩ * x ⟨i + 2, by omega⟩ = 0) :
    wrapFrontEquation
      (natWrapPrefixState
        (fun i => A (finitePathClamp m i))
        (fun i => c (finitePathClamp m i))
        (fun i => s (finitePathClamp m i)) scale k r)
      (c (finitePathClamp m r)) (s (finitePathClamp m r)) L
      (x (finitePathClamp m r)) (x (finitePathClamp m (r + 1))) := by
  apply natWrapPrefixEquation _ _ _ _ r
  · exact fun i => hA _
  · exact fun i => hc _
  · exact fun i => hs _
  · exact hscale
  · exact hk
  · have hm1 : 1 ≤ m := by omega
    simpa [natWrapPrefixState, finitePathClamp, min_eq_left hm1] using hfirst
  · intro i hi
    have hi0 : i ≤ m := by omega
    have hi1 : i + 1 ≤ m := by omega
    have hi2 : i + 2 ≤ m := by omega
    simpa [finitePathClamp, min_eq_left hi0, min_eq_left hi1,
      min_eq_left hi2] using hrows i hi

/-- Accumulated adjacent-fork diagonal correction after eliminating a
natural-indexed prefix. -/
noncomputable def natWrapForkDiagonal
    (A c s : ℕ → ℝ) (scale k : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
      let st := natWrapPrefixState A c s scale k r
      natWrapForkDiagonal A c s scale k r +
        st.k * st.A * st.scale / wrapPrefixPivot st.A (c r) (s r)

/-- The adjacent fork row is transported in lockstep with the condensed
front equation.  This supplies the exact diagonal budget accumulated by an
arbitrary prefix without introducing a matrix inverse. -/
theorem natWrapForkEquation
    (A c s x : ℕ → ℝ) {scale k L forkRest : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation (natWrapPrefixState A c s scale k 0)
        (c 0) (s 0) L (x 0) (x 1))
    (hrows : ∀ i < r,
      (-A (i + 1) * s i) * x i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
          c (i + 1) * x (i + 2) = 0)
    (hfork : forkRest - k * x 0 = 0) :
    forkRest - natWrapForkDiagonal A c s scale k r * L -
        (natWrapPrefixState A c s scale k r).k * x r = 0 := by
  induction r with
  | zero => simpa [natWrapForkDiagonal, natWrapPrefixState] using hfork
  | succ r ih =>
      have hpriorRows : ∀ i < r,
          (-A (i + 1) * s i) * x i +
            (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
              c (i + 1) * x (i + 2) = 0 :=
        fun i hi => hrows i (Nat.lt_succ_of_lt hi)
      have hfront := natWrapPrefixEquation A c s x r hA hc hs hscale hk
        hfirst hpriorRows
      have ih' := ih hpriorRows
      have ih'' :
          (forkRest - natWrapForkDiagonal A c s scale k r * L) -
            (natWrapPrefixState A c s scale k r).k * x r = 0 := by
        linarith [ih']
      have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
      have hpiv : wrapPrefixPivot
          (natWrapPrefixState A c s scale k r).A (c r) (s r) ≠ 0 :=
        ne_of_gt (wrapPrefixPivot_pos (le_of_lt hpos.1)
          (le_of_lt (hc r)) (le_of_lt (hs r)))
      have hstep := wrap_prefix_fork_equation_step hpiv hfront ih''
      change forkRest -
          (natWrapForkDiagonal A c s scale k r +
            (natWrapPrefixState A c s scale k r).k *
              (natWrapPrefixState A c s scale k r).A *
              (natWrapPrefixState A c s scale k r).scale /
                wrapPrefixPivot (natWrapPrefixState A c s scale k r).A
                  (c r) (s r)) * L -
          (wrapPrefixStep (natWrapPrefixState A c s scale k r)
            (A (r + 1)) (c r) (s r)).k * x (r + 1) = 0
      dsimp [wrapPrefixStep] at hstep ⊢
      ring_nf at hstep ⊢
      exact hstep

/-- Affine version of the last prefix pivot.  When all earlier forcing has
already been condensed into the front equation, a forcing applied in the
new row is preserved as the right-hand side of the new front equation. -/
theorem wrap_prefix_internal_equation_step_rhs
    {A₀ A₁ c₀ c₁ s₀ s₁ scale L x₀ x₁ x₂ rhs : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0)
    (hone : 1 + A₀ ≠ 0)
    (h₀ : wrapPrefixPivot A₀ c₀ s₀ * x₀ - c₀ * x₁ -
        A₀ * scale * L = 0)
    (h₁ : (-A₁ * s₀) * x₀ + (1 + A₁ + c₁ * s₁) * x₁ -
        c₁ * x₂ = rhs) :
    (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ * s₁) * x₁ -
        c₁ * x₂ -
        wrapCondensedA A₀ A₁ c₀ s₀ *
          wrapCondensedScale A₀ s₀ scale * L = rhs := by
  have hx₀ : x₀ = (c₀ * x₁ + A₀ * scale * L) /
      wrapPrefixPivot A₀ c₀ s₀ := by
    apply (eq_div_iff hpiv).2
    linarith
  rw [hx₀] at h₁
  have hleft :
      wrapCondensedA A₀ A₁ c₀ s₀ *
          wrapCondensedScale A₀ s₀ scale =
        A₁ * s₀ * A₀ * scale / wrapPrefixPivot A₀ c₀ s₀ := by
    unfold wrapCondensedA wrapCondensedScale
    field_simp [hpiv, hone]
  rw [hleft]
  unfold wrapCondensedA
  field_simp [hpiv] at h₁ ⊢
  unfold wrapPrefixPivot at h₁ ⊢
  ring_nf at h₁ ⊢
  exact h₁

/-- A homogeneous prefix followed by one forced row.  This is the exact
shape of the mixed penultimate/terminal exceptional source column. -/
theorem natWrapPrefixEquation_final_rhs
    (A c s x : ℕ → ℝ) {scale k L rhs : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      wrapFrontEquation (natWrapPrefixState A c s scale k 0)
        (c 0) (s 0) L (x 0) (x 1))
    (hrows : ∀ i < r,
      (-A (i + 1) * s i) * x i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * x (i + 1) -
          c (i + 1) * x (i + 2) = 0)
    (hfinal :
      (-A (r + 1) * s r) * x r +
        (1 + A (r + 1) + c (r + 1) * s (r + 1)) * x (r + 1) -
          c (r + 1) * x (r + 2) = rhs) :
    (1 + (natWrapPrefixState A c s scale k (r + 1)).A +
        c (r + 1) * s (r + 1)) * x (r + 1) -
      c (r + 1) * x (r + 2) -
      (natWrapPrefixState A c s scale k (r + 1)).A *
        (natWrapPrefixState A c s scale k (r + 1)).scale * L = rhs := by
  have hfront := natWrapPrefixEquation A c s x r hA hc hs hscale hk
    hfirst hrows
  have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
  have hpiv : wrapPrefixPivot
      (natWrapPrefixState A c s scale k r).A (c r) (s r) ≠ 0 :=
    ne_of_gt (wrapPrefixPivot_pos (le_of_lt hpos.1)
      (le_of_lt (hc r)) (le_of_lt (hs r)))
  have hone : 1 + (natWrapPrefixState A c s scale k r).A ≠ 0 := by
    linarith [hpos.1]
  change (1 +
      (wrapPrefixStep (natWrapPrefixState A c s scale k r)
        (A (r + 1)) (c r) (s r)).A + c (r + 1) * s (r + 1)) *
        x (r + 1) - c (r + 1) * x (r + 2) -
      (wrapPrefixStep (natWrapPrefixState A c s scale k r)
        (A (r + 1)) (c r) (s r)).A *
        (wrapPrefixStep (natWrapPrefixState A c s scale k r)
          (A (r + 1)) (c r) (s r)).scale * L = rhs
  simpa [wrapPrefixStep] using
    (wrap_prefix_internal_equation_step_rhs hpiv hone hfront hfinal)

/-- Every accumulated fork diagonal correction is nonnegative under
positive source coefficients. -/
theorem natWrapForkDiagonal_nonneg
    (A c s : ℕ → ℝ) {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k) :
    ∀ r, 0 ≤ natWrapForkDiagonal A c s scale k r := by
  intro r
  induction r with
  | zero => simp [natWrapForkDiagonal]
  | succ r ih =>
      have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
      have hpiv := wrapPrefixPivot_pos (le_of_lt hpos.1)
        (le_of_lt (hc r)) (le_of_lt (hs r))
      simp only [natWrapForkDiagonal]
      exact add_nonneg ih (div_nonneg
        (mul_nonneg (mul_nonneg (le_of_lt hpos.2.2) (le_of_lt hpos.1))
          (le_of_lt hpos.2.1)) (le_of_lt hpiv))

/-- Prefix elimination cannot consume more of the adjacent-fork diagonal
budget than the initial boundary product `k * scale`.  More precisely, the
unconsumed terminal product and the accumulated correction remain below that
initial budget.  The one-step loss is exactly `st.k * st.scale / (1 + st.A)`.
This is the grouped invariant needed for the literal `Bprev` estimate; no
sign is assigned to the mixed response by itself. -/
theorem natWrapForkDiagonal_add_terminal_le_initial
    (A c s : ℕ → ℝ) {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 < scale) (hk : 0 < k) :
    ∀ r,
      natWrapForkDiagonal A c s scale k r +
          (natWrapPrefixState A c s scale k r).k *
            (natWrapPrefixState A c s scale k r).scale ≤
        k * scale := by
  intro r
  induction r with
  | zero => simp [natWrapForkDiagonal, natWrapPrefixState]
  | succ r ih =>
      let st := natWrapPrefixState A c s scale k r
      have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
      have hpiv : 0 < wrapPrefixPivot st.A (c r) (s r) :=
        wrapPrefixPivot_pos (le_of_lt hpos.1) (le_of_lt (hc r))
          (le_of_lt (hs r))
      have hone : 0 < 1 + st.A := by linarith [hpos.1]
      have hid :
          st.k * st.scale -
              (st.k * st.A * st.scale /
                  wrapPrefixPivot st.A (c r) (s r) +
                (wrapPrefixStep st (A (r + 1)) (c r) (s r)).k *
                  (wrapPrefixStep st (A (r + 1)) (c r) (s r)).scale) =
            st.k * st.scale / (1 + st.A) := by
        dsimp [wrapPrefixStep]
        unfold wrapCondensedK wrapCondensedScale
        field_simp [ne_of_gt hpiv, ne_of_gt hone]
        unfold wrapPrefixPivot
        ring
      have hloss : 0 ≤ st.k * st.scale / (1 + st.A) :=
        div_nonneg (mul_nonneg (le_of_lt hpos.2.2) (le_of_lt hpos.2.1))
          (le_of_lt hone)
      have hstep :
          natWrapForkDiagonal A c s scale k (r + 1) +
              (natWrapPrefixState A c s scale k (r + 1)).k *
                (natWrapPrefixState A c s scale k (r + 1)).scale ≤
            natWrapForkDiagonal A c s scale k r + st.k * st.scale := by
        simp only [natWrapForkDiagonal, natWrapPrefixState]
        change natWrapForkDiagonal A c s scale k r +
              st.k * st.A * st.scale /
                wrapPrefixPivot st.A (c r) (s r) +
              (wrapPrefixStep st (A (r + 1)) (c r) (s r)).k *
                (wrapPrefixStep st (A (r + 1)) (c r) (s r)).scale ≤
            natWrapForkDiagonal A c s scale k r + st.k * st.scale
        linarith [hid, hloss]
      exact le_trans hstep ih

end TypeIIL
