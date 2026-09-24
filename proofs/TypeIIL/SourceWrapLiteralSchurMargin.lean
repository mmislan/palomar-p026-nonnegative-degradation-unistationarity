import proofs.TypeIIL.SourceWrapKernelElimination

namespace TypeIIL

open scoped BigOperators

/-- The long-gap coupled margin with every boundary parameter specialized to
its literal source-current coefficient.  The two responses solve the actual
adjacent fork columns, not abstract forcing vectors. -/
theorem SourceWrapForkGap.exists_literal_responses_and_raw_margin
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {X Bprev followingBudget precedingCorrection : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let k := q left *
        (sourceForkNextCoeff next weight back rho left / e (next left))
      let h := q right *
        (sourceForkBackCoeff next weight back rho right
          (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))
      let g := p right / e right
      let eff := G.properWrapState weight p q e rho (weight left) k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1))
      let heffR := wrapCondensedH eff.A
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1)) h
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let k := q left *
        (sourceForkNextCoeff next weight back rho left / e (next left))
      let eff := G.properWrapState weight p q e rho (weight left) k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1))
      let seff := wrapCondensedScale eff.A
        (finitePathNatLift (G.gapS weight) (m - 1)) eff.scale
      let keff := wrapCondensedK eff.A
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1)) eff.k
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
      Bprev = (d + keff * seff *
        (1 + finitePathNatLift (G.gapC weight q e rho) m)) / d -
          precedingCorrection) :
    ∃ xf yw : Fin (m + 1) → ℝ,
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right) ∧
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) ∧
      let k := q left *
        (sourceForkNextCoeff next weight back rho left / e (next left))
      let h := q right *
        (sourceForkBackCoeff next weight back rho right
          (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))
      let g := p right / e right
      let eff := G.properWrapState weight p q e rho (weight left) k
      let Fprev := eff.k * finitePathNatLift xf (m - 1)
      let W := -(h * finitePathNatLift (G.gapS weight) (m - 1) *
          finitePathNatLift yw (m - 1) -
        (g + h) * finitePathNatLift yw m)
      W * Fprev < X * Bprev := by
  let k := q left *
    (sourceForkNextCoeff next weight back rho left / e (next left))
  let h := q right *
    (sourceForkBackCoeff next weight back rho right
      (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))
  let g := p right / e right
  have hscale : 0 < (weight left : ℝ) := by exact_mod_cast hw left
  have hk : 0 < k := mul_pos (hq left)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw left)
      (he (next left)))
  have hh : 0 < h := mul_pos (hq right)
    (div_pos (sourceForkBackCoeff_pos next weight back hrho right
      (G.idx (Fin.last m))) (he (G.idx (Fin.last m))))
  have hg : 0 ≤ g := le_of_lt (div_pos (hp right) (he right))
  have hgapunit : G.gapS weight (Fin.last m) = 1 := by
    simp [SourceGapEmbedding.gapS, hunit]
  by_cases hm1 : m = 1
  · subst m
    obtain ⟨xf, yw, hxf, hyw, hmargin⟩ :=
      G.exists_two_coordinate_responses_and_raw_margin
        weight p q e rho hp hq he hrho hw hscale hk hgapunit hh hg
        hfollowing hpreceding (by simpa [k, h, g] using hX)
          (by simpa [k] using hBprev)
    refine ⟨xf, yw, ?_, ?_, ?_⟩
    · intro i
      rw [P.internal_right_column_eq_forcing (by omega)
        weight p q e rho hunit i]
      exact hxf i
    · intro i
      rw [P.internal_left_column_eq_forcing weight p q e rho i]
      exact hyw i
    · simpa [k, h, g] using hmargin
  · have hmlong : 1 < m := by omega
    obtain ⟨xf, yw, hxf, hyw, hmargin⟩ :=
      G.exists_responses_and_raw_two_edge_margin hmlong
        weight p q e rho hp hq he hrho hw hscale hk hgapunit hh hg
        hfollowing hpreceding (by simpa [k, h, g] using hX)
          (by simpa [k] using hBprev)
    refine ⟨xf, yw, ?_, ?_, ?_⟩
    · intro i
      rw [P.internal_right_column_eq_forcing hm weight p q e rho hunit i]
      exact hxf i
    · intro i
      rw [P.internal_left_column_eq_forcing weight p q e rho i]
      exact hyw i
    · simpa [k, h, g] using hmargin

end TypeIIL
