import proofs.TypeIIL.SourceWrapCoupledMargin

namespace TypeIIL

/-- The two endpoint budgets needed by the coupled wrap determinant have the
literal Schur signs: the following gap adds a nonnegative amount to `B-F`,
while the preceding gap subtracts a nonpositive correction from `Bprev`.
This packages those signs directly, so no independent bound on the exceptional
wrap entry is introduced. -/
theorem wrapPrefixState_response_raw_two_edge_margin_of_endpoint_budgets
    {eff : WrapPrefixState}
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W
      xf₀ xf₁ yw₀ yw₁ followingBudget precedingCorrection : ℝ}
    (heff : eff.StrictlyPositive)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heffR := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      Bprev = (d + keff * seff * (1 + terminalC)) / d -
        precedingCorrection)
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
  apply wrapPrefixState_response_raw_two_edge_margin heff hnextA hedgeC
    hedgeS hterminalC hh hg
  · dsimp only at hX ⊢
    rw [hX]
    linarith
  · dsimp only at hBprev ⊢
    rw [hBprev]
    linarith
  · exact hforward₀
  · exact hforward₁
  · exact hFprev
  · exact hwrap₀
  · exact hwrap₁
  · exact hW

/-- Natural-indexed arbitrary-prefix version of the endpoint-budget theorem.
It is the direct consumer for literal finite-gap equation induction. -/
theorem natWrapPrefix_response_raw_two_edge_margin_of_endpoint_budgets
    (A c s : ℕ → ℝ) {scale k : ℝ} (r : ℕ)
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W
      xf₀ xf₁ yw₀ yw₁ followingBudget precedingCorrection : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let eff := natWrapPrefixState A c s scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heffR := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let eff := natWrapPrefixState A c s scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      Bprev = (d + keff * seff * (1 + terminalC)) / d -
        precedingCorrection)
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
  exact wrapPrefixState_response_raw_two_edge_margin_of_endpoint_budgets
    (natWrapPrefixState_pos A c s hA hc hs hscale hk r)
    hnextA hedgeC hedgeS hterminalC hh hg hfollowing hpreceding hX hBprev
    hforward₀ hforward₁ hFprev hwrap₀ hwrap₁ hW

end TypeIIL
