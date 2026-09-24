import proofs.TypeIIL.SourceWrapFiniteInduction

namespace TypeIIL

/-- The raw two-node determinant exposed after a positive prefix is
strictly positive. -/
theorem wrap_two_node_raw_det_pos
    {A₀ A₁ c₀ c₁ s₀ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hs₀ : 0 < s₀) :
    0 < wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
      A₁ * s₀ * c₀ := by
  have hp := wrapPrefixPivot_pos (le_of_lt hA₀) (le_of_lt hc₀)
    (le_of_lt hs₀)
  have hd := (two_reaction_condensation_denominators_pos
    hA₀ hA₁ hc₀ hc₁ hs₀).2
  have hid :
      wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) - A₁ * s₀ * c₀ =
        wrapPrefixPivot A₀ c₀ s₀ *
          (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
    unfold wrapCondensedA
    field_simp [ne_of_gt hp]
    unfold wrapPrefixPivot
    ring
  rw [hid]
  exact mul_pos hp hd

/-- Equation-level coupled-wrap theorem.  A positive condensed prefix state,
the literal final two path equations, and the two endpoint diagonal lower
bounds imply the strict raw minor used by cyclic closure.  The forward and
wrap Schur entries are derived here rather than assumed. -/
theorem wrapPrefixState_response_raw_two_edge_margin
    {eff : WrapPrefixState}
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W
      xf₀ xf₁ yw₀ yw₁ : ℝ}
    (heff : eff.StrictlyPositive)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hX :
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heffR := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      (d + g + heffR) / d ≤ X)
    (hBprev :
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      (d + keff * seff * (1 + terminalC)) / d ≤ Bprev)
    (hforward₀ :
      wrapPrefixPivot eff.A edgeC edgeS * xf₀ - edgeC * xf₁ = edgeC)
    (hforward₁ :
      -(nextA * edgeS) * xf₀ + (1 + nextA + terminalC) * xf₁ =
        -(nextA + terminalC))
    (hFprev : Fprev = eff.k * xf₀)
    (hwrap₀ :
      wrapPrefixPivot eff.A edgeC edgeS * yw₀ - edgeC * yw₁ =
        -(eff.A * eff.scale))
    (hwrap₁ :
      -(nextA * edgeS) * yw₀ + (1 + nextA + terminalC) * yw₁ = 0)
    (hW : W = -(h * edgeS * yw₀ - (g + h) * yw₁)) :
    W * Fprev < X * Bprev := by
  have hparams := wrap_condensed_parameters_pos heff.1 hnextA hedgeC
    hedgeS heff.2.1 heff.2.2 hh
  have hdetPos := wrap_two_node_raw_det_pos heff.1 hnextA hedgeC
    hterminalC hedgeS
  have hdet :
      wrapPrefixPivot eff.A edgeC edgeS * (1 + nextA + terminalC) -
        nextA * edgeS * edgeC ≠ 0 := ne_of_gt hdetPos
  have hfRaw := two_reaction_forward_response_eq (k := eff.k) hdet
    hforward₀ hforward₁
  have hfCond := two_reaction_forward_condensation_eq
    (A₁ := nextA) (c₁ := terminalC) (k := eff.k)
    (ne_of_gt (wrapPrefixPivot_pos (le_of_lt heff.1)
      (le_of_lt hedgeC) (le_of_lt hedgeS)))
  have hFexact :
      Fprev = wrapCondensedK eff.A edgeC edgeS eff.k /
        (1 + wrapCondensedA eff.A nextA edgeC edgeS + terminalC) := by
    rw [hFprev, hfRaw, hfCond]
  have hwRaw := two_reaction_wrap_response_eq
    (scale := eff.scale) (h := h) (g := g) hdet hwrap₀ hwrap₁
  have hwCond := two_reaction_wrap_condensation_eq
    (A₁ := nextA) (c₁ := terminalC)
    (scale := eff.scale) (h := h) (g := g)
    (by linarith [heff.1])
    (ne_of_gt (wrapPrefixPivot_pos (le_of_lt heff.1)
      (le_of_lt hedgeC) (le_of_lt hedgeS)))
  have hWexact :
      W = wrapCondensedScale eff.A edgeS eff.scale *
        (wrapCondensedH eff.A edgeC edgeS h * (1 + terminalC) -
          g * wrapCondensedA eff.A nextA edgeC edgeS) /
        (1 + wrapCondensedA eff.A nextA edgeC edgeS + terminalC) := by
    rw [hW, hwRaw, hwCond]
  dsimp only at hX hBprev
  exact singleton_wrap_raw_two_edge_margin rfl
    (le_of_lt hparams.1) (le_of_lt hterminalC) hg
    (le_of_lt hparams.2.2.2) (le_of_lt hparams.2.2.1)
    hparams.2.1 hX hBprev hFexact hWexact

/-- The forward port of a positive condensed prefix is exactly `keff / d`.
This is the sign interface needed by the cyclic transfer normalization. -/
theorem wrapPrefixState_forward_flux_eq
    {eff : WrapPrefixState}
    {nextA edgeC edgeS terminalC xf₀ xf₁ : ℝ}
    (heff : eff.StrictlyPositive)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hforward₀ :
      wrapPrefixPivot eff.A edgeC edgeS * xf₀ - edgeC * xf₁ = edgeC)
    (hforward₁ :
      -(nextA * edgeS) * xf₀ + (1 + nextA + terminalC) * xf₁ =
        -(nextA + terminalC)) :
    eff.k * xf₀ =
      wrapCondensedK eff.A edgeC edgeS eff.k /
        (1 + wrapCondensedA eff.A nextA edgeC edgeS + terminalC) := by
  have hdetPos := wrap_two_node_raw_det_pos heff.1 hnextA hedgeC
    hterminalC hedgeS
  have hdet :
      wrapPrefixPivot eff.A edgeC edgeS * (1 + nextA + terminalC) -
        nextA * edgeS * edgeC ≠ 0 := ne_of_gt hdetPos
  have hfRaw := two_reaction_forward_response_eq (k := eff.k) hdet
    hforward₀ hforward₁
  have hfCond := two_reaction_forward_condensation_eq
    (A₁ := nextA) (c₁ := terminalC) (k := eff.k)
    (ne_of_gt (wrapPrefixPivot_pos (le_of_lt heff.1)
      (le_of_lt hedgeC) (le_of_lt hedgeS)))
  rw [hfRaw, hfCond]

/-- Arbitrary-length corollary: positivity of the original natural-indexed
source coefficients supplies the positive condensed state automatically. -/
theorem natWrapPrefix_response_raw_two_edge_margin
    (A c s : ℕ → ℝ) {scale k : ℝ} (r : ℕ)
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W
      xf₀ xf₁ yw₀ yw₁ : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hX :
      let eff := natWrapPrefixState A c s scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heffR := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      (d + g + heffR) / d ≤ X)
    (hBprev :
      let eff := natWrapPrefixState A c s scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      (d + keff * seff * (1 + terminalC)) / d ≤ Bprev)
    (hforward₀ :
      let eff := natWrapPrefixState A c s scale k r
      wrapPrefixPivot eff.A edgeC edgeS * xf₀ - edgeC * xf₁ = edgeC)
    (hforward₁ :
      -(nextA * edgeS) * xf₀ + (1 + nextA + terminalC) * xf₁ =
        -(nextA + terminalC))
    (hFprev :
      let eff := natWrapPrefixState A c s scale k r
      Fprev = eff.k * xf₀)
    (hwrap₀ :
      let eff := natWrapPrefixState A c s scale k r
      wrapPrefixPivot eff.A edgeC edgeS * yw₀ - edgeC * yw₁ =
        -(eff.A * eff.scale))
    (hwrap₁ :
      -(nextA * edgeS) * yw₀ + (1 + nextA + terminalC) * yw₁ = 0)
    (hW : W = -(h * edgeS * yw₀ - (g + h) * yw₁)) :
    W * Fprev < X * Bprev := by
  exact wrapPrefixState_response_raw_two_edge_margin
    (natWrapPrefixState_pos A c s hA hc hs hscale hk r)
    hnextA hedgeC hedgeS hterminalC hh hg hX hBprev hforward₀
    hforward₁ hFprev hwrap₀ hwrap₁ hW

/-- The complete left-fork contribution of an arbitrary positive gap
dominates the endpoint core used by the coupled margin.  Mixed responses are
grouped with the direct boundary product before any estimate is taken. -/
theorem natWrapPrefix_left_diagonal_core_le
    (A c s y : ℕ → ℝ) {scale k : ℝ} (r : ℕ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hfirst : wrapFrontEquation
      (natWrapPrefixState A c s scale k 0) (c 0) (s 0) (-1) (y 0) (y 1))
    (hrows : ∀ i < r,
      (-A (i + 1) * s i) * y i +
        (1 + A (i + 1) + c (i + 1) * s (i + 1)) * y (i + 1) -
          c (i + 1) * y (i + 2) = 0)
    (hterminal :
      -(A (r + 1) * s r) * y r +
        (1 + A (r + 1) + c (r + 1)) * y (r + 1) = 0) :
    let eff := natWrapPrefixState A c s scale k r
    let Aeff := wrapCondensedA eff.A (A (r + 1)) (c r) (s r)
    let seff := wrapCondensedScale eff.A (s r) eff.scale
    let keff := wrapCondensedK eff.A (c r) (s r) eff.k
    let d := 1 + Aeff + c (r + 1)
    (d + keff * seff * (1 + c (r + 1))) / d ≤
      1 + k * scale + k * y 0 := by
  let eff := natWrapPrefixState A c s scale k r
  have hpos := natWrapPrefixState_pos A c s hA hc hs hscale hk r
  have hfront := natWrapPrefixEquation A c s y r hA hc hs hscale hk
    hfirst hrows
  have hrow₀ :
      wrapPrefixPivot eff.A (c r) (s r) * y r - c r * y (r + 1) =
        -(eff.A * eff.scale) := by
    change wrapFrontEquation eff (c r) (s r) (-1) (y r) (y (r + 1)) at hfront
    unfold wrapFrontEquation at hfront
    linarith
  have htwo := two_reaction_left_diagonal_budget_eq
    hpos.1 (hA (r + 1)) (hc r) (hc (r + 1)) (hs r) hrow₀ hterminal
    (scale := eff.scale) (k := eff.k)
  have hfork := natWrapForkEquation A c s y r hA hc hs hscale hk
    hfirst hrows (forkRest := k * y 0) (by ring)
  have hbudget := natWrapForkDiagonal_add_terminal_le_initial
    A c s hA hc hs hscale hk r
  have hrem : 0 ≤ eff.k * eff.scale / (1 + eff.A) := by
    exact div_nonneg
      (mul_nonneg (le_of_lt hpos.2.2) (le_of_lt hpos.2.1))
      (by linarith [hpos.1])
  dsimp only at htwo ⊢
  change k * y 0 -
      natWrapForkDiagonal A c s scale k r * (-1) - eff.k * y r = 0 at hfork
  change natWrapForkDiagonal A c s scale k r + eff.k * eff.scale ≤
    k * scale at hbudget
  linarith

end TypeIIL
