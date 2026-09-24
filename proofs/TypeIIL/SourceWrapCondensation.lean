import proofs.TypeIIL.SourceGapBudget

namespace TypeIIL

/-- Pivot of the first reaction in a weighted source path. -/
def wrapPrefixPivot (A c s : ℝ) : ℝ := 1 + A + c * s

/-- Effective predecessor coefficient after eliminating the first path
reaction. -/
noncomputable def wrapCondensedA (A₀ A₁ c₀ s₀ : ℝ) : ℝ :=
  A₁ * (1 + A₀) / wrapPrefixPivot A₀ c₀ s₀

/-- Effective left endpoint scale after the same elimination. -/
noncomputable def wrapCondensedScale (A₀ s₀ scale : ℝ) : ℝ :=
  scale * s₀ * A₀ / (1 + A₀)

/-- Effective following-fork row coefficient. -/
noncomputable def wrapCondensedK (A₀ c₀ s₀ k : ℝ) : ℝ :=
  k * c₀ / wrapPrefixPivot A₀ c₀ s₀

/-- Effective exceptional-row coefficient in the final two-node
condensation step. -/
noncomputable def wrapCondensedH (A₀ c₀ s₀ h : ℝ) : ℝ :=
  h * (1 + A₀) / wrapPrefixPivot A₀ c₀ s₀

theorem wrapPrefixPivot_pos
    {A c s : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    0 < wrapPrefixPivot A c s := by
  unfold wrapPrefixPivot
  have : 0 ≤ c * s := mul_nonneg hc hs
  nlinarith

/-- Eliminating the first path coordinate preserves the source-path
diagonal form at the new first coordinate. -/
theorem wrap_prefix_diagonal_step
    {A₀ A₁ c₀ c₁ s₀ : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0) :
    (1 + A₁ + c₁) -
        (-A₁ * s₀) * (-c₀) / wrapPrefixPivot A₀ c₀ s₀ =
      1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ := by
  unfold wrapCondensedA
  field_simp [wrapPrefixPivot, hpiv]
  unfold wrapPrefixPivot
  ring

/-- The condensed left column again has the form `-A * scale`. -/
theorem wrap_prefix_left_column_step
    {A₀ A₁ c₀ s₀ scale : ℝ}
    (hA₀ : 1 + A₀ ≠ 0) :
    0 - (-A₁ * s₀) * (-A₀ * scale) /
        wrapPrefixPivot A₀ c₀ s₀ =
      -(wrapCondensedA A₀ A₁ c₀ s₀ *
        wrapCondensedScale A₀ s₀ scale) := by
  unfold wrapCondensedA wrapCondensedScale
  field_simp [hA₀]
  ring

/-- The following-fork row propagates with a nonnegative effective
coefficient. -/
theorem wrap_prefix_left_row_step
    {A₀ c₀ s₀ k : ℝ} :
    0 - (-k) * (-c₀) / wrapPrefixPivot A₀ c₀ s₀ =
      -wrapCondensedK A₀ c₀ s₀ k := by
  unfold wrapCondensedK
  ring

/-- Equation-level form of one prefix elimination.  It is the induction step
needed to transport a literal tridiagonal path equation, rather than merely
its individual matrix entries. -/
theorem wrap_prefix_internal_equation_step
    {A₀ A₁ c₀ c₁ s₀ s₁ scale L x₀ x₁ x₂ : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0)
    (hone : 1 + A₀ ≠ 0)
    (h₀ : wrapPrefixPivot A₀ c₀ s₀ * x₀ - c₀ * x₁ -
        A₀ * scale * L = 0)
    (h₁ : (-A₁ * s₀) * x₀ + (1 + A₁ + c₁ * s₁) * x₁ -
        c₁ * x₂ = 0) :
    (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ * s₁) * x₁ -
        c₁ * x₂ -
        wrapCondensedA A₀ A₁ c₀ s₀ *
          wrapCondensedScale A₀ s₀ scale * L = 0 := by
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

/-- The adjacent fork row is transported by the same pivot.  The displayed
last term is the accumulated diagonal correction, deliberately kept
separate from the nonnegative diagonal budget. -/
theorem wrap_prefix_fork_equation_step
    {A₀ c₀ s₀ scale k L x₀ x₁ forkRest : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0)
    (h₀ : wrapPrefixPivot A₀ c₀ s₀ * x₀ - c₀ * x₁ -
        A₀ * scale * L = 0)
    (hfork : forkRest - k * x₀ = 0) :
    forkRest - wrapCondensedK A₀ c₀ s₀ k * x₁ -
        (k * A₀ * scale / wrapPrefixPivot A₀ c₀ s₀) * L = 0 := by
  unfold wrapCondensedK
  field_simp [hpiv]
  linear_combination
    wrapPrefixPivot A₀ c₀ s₀ * hfork + k * h₀

/-- In the final two-node step, the right boundary column becomes
`-(A' + c₁)`. -/
theorem wrap_final_right_column_step
    {A₀ A₁ c₀ c₁ s₀ : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0) :
    (-(A₁ + c₁)) -
        (-A₁ * s₀) * c₀ / wrapPrefixPivot A₀ c₀ s₀ =
      -(wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
  unfold wrapCondensedA
  field_simp [wrapPrefixPivot, hpiv]
  unfold wrapPrefixPivot
  ring

/-- In the final two-node step, the exceptional fork row becomes
`-(g + h')`. -/
theorem wrap_final_right_row_step
    {A₀ c₀ s₀ g h : ℝ}
    (hpiv : wrapPrefixPivot A₀ c₀ s₀ ≠ 0) :
    (-(g + h)) - h * s₀ * (-c₀) /
        wrapPrefixPivot A₀ c₀ s₀ =
      -(g + wrapCondensedH A₀ c₀ s₀ h) := by
  unfold wrapCondensedH
  field_simp [wrapPrefixPivot, hpiv]
  unfold wrapPrefixPivot
  ring

/-- The two direct fork edges created in the final condensation are exactly
the singleton-template coefficients. -/
theorem wrap_final_direct_edges
    {A₀ c₀ s₀ scale k h : ℝ}
    (hA₀ : 1 + A₀ ≠ 0) :
    (0 - (-k) * c₀ / wrapPrefixPivot A₀ c₀ s₀ =
        wrapCondensedK A₀ c₀ s₀ k) ∧
      (0 - h * s₀ * (-A₀ * scale) /
          wrapPrefixPivot A₀ c₀ s₀ =
        wrapCondensedH A₀ c₀ s₀ h *
          wrapCondensedScale A₀ s₀ scale) := by
  constructor
  · unfold wrapCondensedK
    ring
  · unfold wrapCondensedH wrapCondensedScale
    field_simp [hA₀]
    ring

/-- All effective parameters needed by the singleton wrap factorization
remain nonnegative (strictly positive under strict source data). -/
theorem wrap_condensed_parameters_pos
    {A₀ A₁ c₀ s₀ scale k h : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hc₀ : 0 < c₀)
    (hs₀ : 0 < s₀) (hscale : 0 < scale)
    (hk : 0 < k) (hh : 0 < h) :
    0 < wrapCondensedA A₀ A₁ c₀ s₀ ∧
      0 < wrapCondensedScale A₀ s₀ scale ∧
      0 < wrapCondensedK A₀ c₀ s₀ k ∧
      0 < wrapCondensedH A₀ c₀ s₀ h := by
  have hpiv := wrapPrefixPivot_pos (le_of_lt hA₀) (le_of_lt hc₀)
    (le_of_lt hs₀)
  have hone : 0 < 1 + A₀ := by linarith
  unfold wrapCondensedA wrapCondensedScale wrapCondensedK wrapCondensedH
  exact ⟨div_pos (mul_pos hA₁ hone) hpiv,
    div_pos (mul_pos (mul_pos hscale hs₀) hA₀) hone,
    div_pos (mul_pos hk hc₀) hpiv,
    div_pos (mul_pos hh hone) hpiv⟩

/-- The three left-to-right parameters propagated while a prefix of the
wrap gap is eliminated. -/
structure WrapPrefixState where
  A : ℝ
  scale : ℝ
  k : ℝ

def WrapPrefixState.StrictlyPositive (st : WrapPrefixState) : Prop :=
  0 < st.A ∧ 0 < st.scale ∧ 0 < st.k

noncomputable def wrapPrefixStep
    (st : WrapPrefixState) (nextA c s : ℝ) : WrapPrefixState where
  A := wrapCondensedA st.A nextA c s
  scale := wrapCondensedScale st.A s st.scale
  k := wrapCondensedK st.A c s st.k

/-- The current first path equation summarized by a condensation state. -/
def wrapFrontEquation
    (st : WrapPrefixState) (c s L x xNext : ℝ) : Prop :=
  wrapPrefixPivot st.A c s * x - c * xNext -
    st.A * st.scale * L = 0

/-- A proof object recording successive exact eliminations of a path prefix.
Its state is definitionally updated by `wrapPrefixStep`, so it can be used
without introducing a matrix inverse. -/
inductive WrapPrefixEquationDerivation (L : ℝ) :
    WrapPrefixState → ℝ → ℝ → ℝ → ℝ → Prop
  | base {st c s x xNext}
      (h : wrapFrontEquation st c s L x xNext) :
      WrapPrefixEquationDerivation L st c s x xNext
  | step {st nextA c s nextC nextS x xNext xAfter}
      (prior : WrapPrefixEquationDerivation L st c s x xNext)
      (hpiv : wrapPrefixPivot st.A c s ≠ 0)
      (hone : 1 + st.A ≠ 0)
      (hrow : (-nextA * s) * x +
        (1 + nextA + nextC * nextS) * xNext -
          nextC * xAfter = 0) :
      WrapPrefixEquationDerivation L
        (wrapPrefixStep st nextA c s) nextC nextS xNext xAfter

/-- Every iterated derivation really satisfies its displayed condensed front
equation. -/
theorem WrapPrefixEquationDerivation.equation
    {L : ℝ} {st : WrapPrefixState} {c s x xNext : ℝ}
    (H : WrapPrefixEquationDerivation L st c s x xNext) :
    wrapFrontEquation st c s L x xNext := by
  induction H with
  | base h => exact h
  | @step st nextA c s nextC nextS x xNext xAfter prior hpiv hone hrow ih =>
      unfold wrapFrontEquation at ih ⊢
      change
        (1 + (wrapPrefixStep st nextA c s).A + nextC * nextS) * xNext -
          nextC * xAfter -
          (wrapPrefixStep st nextA c s).A *
            (wrapPrefixStep st nextA c s).scale * L = 0
      simpa [wrapPrefixStep, wrapPrefixPivot] using
        (wrap_prefix_internal_equation_step hpiv hone ih hrow)

theorem wrapPrefixStep_pos
    {st : WrapPrefixState} {nextA c s : ℝ}
    (hst : st.StrictlyPositive) (hnextA : 0 < nextA)
    (hc : 0 < c) (hs : 0 < s) :
    (wrapPrefixStep st nextA c s).StrictlyPositive := by
  rcases hst with ⟨hA, hscale, hk⟩
  have hpiv := wrapPrefixPivot_pos (le_of_lt hA) (le_of_lt hc) (le_of_lt hs)
  have hone : 0 < 1 + st.A := by linarith
  constructor
  · exact div_pos (mul_pos hnextA hone) hpiv
  constructor
  · exact div_pos (mul_pos (mul_pos hscale hs) hA) hone
  · exact div_pos (mul_pos hk hc) hpiv

noncomputable def wrapPrefixFold
    (st : WrapPrefixState) (steps : List (ℝ × ℝ × ℝ)) :
    WrapPrefixState :=
  steps.foldl (fun acc step =>
    wrapPrefixStep acc step.1 step.2.1 step.2.2) st

/-- Arbitrarily many prefix eliminations preserve strict positivity. -/
theorem wrapPrefixFold_pos
    (steps : List (ℝ × ℝ × ℝ)) (st : WrapPrefixState)
    (hst : st.StrictlyPositive)
    (hsteps : ∀ step ∈ steps,
      0 < step.1 ∧ 0 < step.2.1 ∧ 0 < step.2.2) :
    (wrapPrefixFold st steps).StrictlyPositive := by
  induction steps generalizing st with
  | nil => simpa [wrapPrefixFold] using hst
  | cons step steps ih =>
      have hstep := hsteps step (by simp)
      have htail : ∀ x ∈ steps,
          0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
        intro x hx
        exact hsteps x (by simp [hx])
      unfold wrapPrefixFold
      simp only [List.foldl_cons]
      apply ih (wrapPrefixStep st step.1 step.2.1 step.2.2)
      · exact wrapPrefixStep_pos hst hstep.1 hstep.2.1 hstep.2.2
      · exact htail

/-- After an arbitrary positive prefix, the last two-node elimination has
all positive singleton-template parameters. -/
theorem wrapPrefixFold_final_parameters_pos
    (steps : List (ℝ × ℝ × ℝ)) (st : WrapPrefixState)
    (hst : st.StrictlyPositive)
    (hsteps : ∀ step ∈ steps,
      0 < step.1 ∧ 0 < step.2.1 ∧ 0 < step.2.2)
    {nextA edgeC edgeS h : ℝ}
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hh : 0 < h) :
    let eff := wrapPrefixFold st steps
    0 < wrapCondensedA eff.A nextA edgeC edgeS ∧
      0 < wrapCondensedScale eff.A edgeS eff.scale ∧
      0 < wrapCondensedK eff.A edgeC edgeS eff.k ∧
      0 < wrapCondensedH eff.A edgeC edgeS h := by
  have heff := wrapPrefixFold_pos steps st hst hsteps
  exact wrap_condensed_parameters_pos heff.1 hnextA hedgeC hedgeS heff.2.1
    heff.2.2 hh

/-- Once staged elimination supplies the four displayed effective Schur
quantities, an arbitrary positive prefix inherits the singleton coupled-wrap
margin.  This is the exact abstract docking point for the literal path
condensation proof. -/
theorem wrapPrefixFold_raw_two_edge_margin
    (steps : List (ℝ × ℝ × ℝ)) (st : WrapPrefixState)
    (hst : st.StrictlyPositive)
    (hsteps : ∀ step ∈ steps,
      0 < step.1 ∧ 0 < step.2.1 ∧ 0 < step.2.2)
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W : ℝ}
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hX :
      let eff := wrapPrefixFold st steps
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heff := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      (d + g + heff) / d ≤ X)
    (hBprev :
      let eff := wrapPrefixFold st steps
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      (d + keff * seff * (1 + terminalC)) / d ≤ Bprev)
    (hFprev :
      let eff := wrapPrefixFold st steps
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      Fprev = keff / d)
    (hW :
      let eff := wrapPrefixFold st steps
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keffH := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      W = seff * (keffH * (1 + terminalC) - g * Aeff) / d) :
    W * Fprev < X * Bprev := by
  have hparams := wrapPrefixFold_final_parameters_pos steps st hst hsteps
    hnextA hedgeC hedgeS hh
  dsimp only at hparams hX hBprev hFprev hW
  exact singleton_wrap_raw_two_edge_margin rfl
    (le_of_lt hparams.1) (le_of_lt hterminalC) hg
    (le_of_lt hparams.2.2.2)
    (le_of_lt hparams.2.2.1) hparams.2.1 hX hBprev hFprev hW

/-- Literal initial state for eliminating a nonempty source gap from left
to right.  `scale` is the left endpoint multiplicity and `k` is the
following fork-row coefficient incident to the first internal reaction. -/
noncomputable def literalWrapPrefixState
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (p e : Fin n → ℝ)
    (scale k : ℝ) : WrapPrefixState where
  A := G.gapA p e 0
  scale := scale
  k := k

/-- The exact coefficient triples consumed by successive source-gap pivot
steps.  Step `i` introduces reaction `i+1` and eliminates the edge carrying
`c_i,s_i`. -/
noncomputable def literalWrapPrefixSteps
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    List (ℝ × ℝ × ℝ) :=
  List.ofFn fun i : Fin m =>
    (G.gapA p e i.succ,
      G.gapC weight q e rho i.castSucc,
      G.gapS weight i.castSucc)

/-- For a gap with at least two internal reactions, reserve the final edge
for the terminal two-node condensation and fold only the earlier edges.  If
the gap has exactly two reactions this list is empty. -/
noncomputable def literalWrapProperPrefixSteps
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    List (ℝ × ℝ × ℝ) :=
  List.ofFn fun i : Fin (m - 1) =>
    let current : Fin (m + 1) := ⟨i.val, by omega⟩
    let following : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    (G.gapA p e following,
      G.gapC weight q e rho current,
      G.gapS weight current)

/-- Index of the reaction immediately preceding the terminal reaction in a
gap with at least two reactions. -/
def finitePathPenultimate (m : ℕ) (hm : 0 < m) : Fin (m + 1) :=
  ⟨m - 1, by omega⟩

/-- Source positivity discharges every sign condition in the arbitrary
prefix fold.  This is the literal coefficient-level docking of a
`SourceGapEmbedding` to `WrapPrefixState`; the remaining matrix-level task is
to identify the four final Schur entries with the folded expressions. -/
theorem literalWrapPrefixFold_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k) :
    (wrapPrefixFold (literalWrapPrefixState G p e scale k)
      (literalWrapPrefixSteps G weight p q e rho)).StrictlyPositive := by
  apply wrapPrefixFold_pos
  · exact ⟨div_pos (hp _) (he _), hscale, hk⟩
  · intro step hstep
    unfold literalWrapPrefixSteps at hstep
    rw [List.mem_ofFn'] at hstep
    obtain ⟨i, rfl⟩ := hstep
    refine ⟨div_pos (hp _) (he _), ?_, G.gapS_pos hw i.castSucc⟩
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))

/-- The initial state used by a literal post-fork gap is strictly positive:
its scale is the fork successor multiplicity and its row coefficient is the
ordered fork-next secant coefficient. -/
theorem sourceFork_literalWrapPrefixFold_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} (fork : Fin n)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) :
    (wrapPrefixFold
      (literalWrapPrefixState G p e (weight fork)
        (q fork *
          (sourceForkNextCoeff next weight back rho fork / e (next fork))))
      (literalWrapPrefixSteps G weight p q e rho)).StrictlyPositive := by
  apply literalWrapPrefixFold_pos G weight p q e rho hp hq he hrho hw
  · exact_mod_cast hw fork
  · exact mul_pos (hq fork) (div_pos
      (sourceForkNextCoeff_pos next weight back hrho hw fork) (he _))

/-- Source positivity also discharges the correctly split proper-prefix
fold, leaving the last path edge for `wrapPrefixFold_final_parameters_pos`. -/
theorem literalWrapProperPrefixFold_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k) :
    (wrapPrefixFold (literalWrapPrefixState G p e scale k)
      (literalWrapProperPrefixSteps G hm weight p q e rho)).StrictlyPositive := by
  apply wrapPrefixFold_pos
  · exact ⟨div_pos (hp _) (he _), hscale, hk⟩
  · intro step hstep
    unfold literalWrapProperPrefixSteps at hstep
    rw [List.mem_ofFn'] at hstep
    obtain ⟨i, rfl⟩ := hstep
    dsimp only
    refine ⟨div_pos (hp _) (he _), ?_, G.gapS_pos hw _⟩
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))

/-- After the proper prefix is eliminated, the literal terminal edge supplies
strictly positive effective singleton parameters. -/
theorem literalWrapFinalParameters_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k h : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hscale : 0 < scale) (hk : 0 < k) (hh : 0 < h) :
    let st := literalWrapPrefixState G p e scale k
    let steps := literalWrapProperPrefixSteps G hm weight p q e rho
    let eff := wrapPrefixFold st steps
    let penultimate := finitePathPenultimate m hm
    let terminal := Fin.last m
    0 < wrapCondensedA eff.A (G.gapA p e terminal)
          (G.gapC weight q e rho penultimate) (G.gapS weight penultimate) ∧
      0 < wrapCondensedScale eff.A (G.gapS weight penultimate) eff.scale ∧
      0 < wrapCondensedK eff.A (G.gapC weight q e rho penultimate)
          (G.gapS weight penultimate) eff.k ∧
      0 < wrapCondensedH eff.A (G.gapC weight q e rho penultimate)
          (G.gapS weight penultimate) h := by
  dsimp only
  apply wrap_condensed_parameters_pos
  · exact (literalWrapProperPrefixFold_pos G hm weight p q e rho
      hp hq he hrho hw hscale hk).1
  · exact div_pos (hp _) (he _)
  · unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw _
  · exact (literalWrapProperPrefixFold_pos G hm weight p q e rho
      hp hq he hrho hw hscale hk).2.1
  · exact (literalWrapProperPrefixFold_pos G hm weight p q e rho
      hp hq he hrho hw hscale hk).2.2
  · exact hh

end TypeIIL
