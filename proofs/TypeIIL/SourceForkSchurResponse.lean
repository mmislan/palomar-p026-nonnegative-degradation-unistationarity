import proofs.TypeIIL.SourceForkRowAssembly

namespace TypeIIL

open scoped BigOperators

theorem sum_mul_negative_two_response
    {α : Type*} [Fintype α]
    (c yw xf : α → ℝ) (u v : ℝ) :
    (∑ i, c i * -(yw i * u + xf i * v)) =
      -(∑ i, c i * yw i) * u - (∑ i, c i * xf i) * v := by
  have hy : (∑ i, c i * yw i) * u = ∑ i, c i * (yw i * u) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hx : (∑ i, c i * xf i) * v = ∑ i, c i * (xf i * v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [mul_neg, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  rw [← hy, ← hx]
  ring

/-- Normalize a raw three-term Schur row by a positive reference current.
The predecessor sign is reversed so that ordinary source rows have a
nonnegative coefficient `alpha`. -/
theorem raw_three_term_to_normalized_sector
    {P D F Jprev J Jnext zprev z znext : ℝ}
    (hD : 0 < D) (hJ : 0 < J)
    (hrow :
      P * (Jprev * zprev) + D * (J * z) + F * (Jnext * znext) = 0) :
    let alpha := -(P * Jprev) / (D * J)
    let gamma := F * Jnext / (D * J)
    (-alpha) * zprev + z + gamma * znext = 0 := by
  dsimp only
  have hden : D * J ≠ 0 := ne_of_gt (mul_pos hD hJ)
  field_simp [hden]
  linear_combination hrow

/-- The signs of a raw cyclic Schur row pass through positive-current
normalization. -/
theorem normalized_sector_coefficients_nonneg
    {P D F Jprev J Jnext : ℝ}
    (hP : P ≤ 0) (hF : 0 ≤ F)
    (hD : 0 < D) (hJprev : 0 < Jprev)
    (hJ : 0 < J) (hJnext : 0 < Jnext) :
    0 ≤ -(P * Jprev) / (D * J) ∧
      0 ≤ F * Jnext / (D * J) := by
  have hden : 0 < D * J := mul_pos hD hJ
  constructor
  · exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      hP (le_of_lt hJprev))) (le_of_lt hden)
  · exact div_nonneg (mul_nonneg hF (le_of_lt hJnext)) (le_of_lt hden)

/-- A strictly positive raw Schur residual on the positive reference current
is exactly the strict sector inequality after normalization. -/
theorem normalized_sector_bound_of_residual
    {P D F Jprev J Jnext : ℝ}
    (hD : 0 < D) (hJ : 0 < J)
    (hresidual : 0 < P * Jprev + D * J + F * Jnext) :
    -(P * Jprev) / (D * J) <
      1 + F * Jnext / (D * J) := by
  have hden : 0 < D * J := mul_pos hD hJ
  apply (div_lt_iff₀ hden).2
  field_simp [ne_of_gt hden]
  nlinarith

/-- Positive column gauges turn neighboring normalized sector rows into the
denominator-free continuant recurrence used by `pathTransfer`.  If
`c = gammaPrev * cprev` and `cnext = gamma * c`, then the new edge weight is
the local product `alpha * gammaPrev`. -/
theorem normalized_sector_row_to_continuant_step
    {alpha gammaPrev gamma cprev c cnext zprev z znext : ℝ}
    (hprev : c = gammaPrev * cprev)
    (hnext : cnext = gamma * c)
    (hrow : (-alpha) * zprev + z + gamma * znext = 0) :
    cnext * znext =
      (alpha * gammaPrev) * (cprev * zprev) - c * z := by
  rw [hnext, hprev]
  linear_combination (gammaPrev * cprev) * hrow

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

noncomputable def forkSchurPrevCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let pred := S.step.symm j
  M (S.fork j) (S.fork pred) -
    ∑ i, M (S.fork j) ((S.gap pred).idx i) * yw pred i

noncomputable def forkSchurSelfCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let pred := S.step.symm j
  M (S.fork j) (S.fork j) -
    (∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i) -
    ∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i

noncomputable def forkSchurNextCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  M (S.fork j) (S.fork (S.step j)) -
    ∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i

/-- Across a nonsingleton literal gap, the successor Schur coefficient is
exactly the positive left-fork boundary functional applied to the right-fork
response.  This is the first of the three coefficient identities needed to
dock the fork cycle to the continuant closure. -/
theorem forkSchurNextCoefficient_eq_boundary_response
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j) :
    S.forkSchurNextCoefficient weight p q e rho xf j =
      (q (S.fork j) *
        (sourceForkNextCoeff next weight back rho (S.fork j) /
          e (next (S.fork j)))) * xf j 0 := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  have hdirect := (S.wrap j).left_right_entry_zero hm weight p q e rho
  have hgap := (S.wrap j).post.fork_postGap_mul
    weight p q e rho (xf j)
  change M (S.fork j) (S.fork (S.step j)) = 0 at hdirect
  change (∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i) = _ at hgap
  simp only [forkSchurNextCoefficient]
  change M (S.fork j) (S.fork (S.step j)) -
    (∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i) = _
  rw [hdirect, hgap]
  ring

/-- At the right endpoint of a nonsingleton literal gap, the predecessor
Schur coefficient is exactly the signed terminal Green functional.  This is
the exceptional quantity denoted `W` in the coupled two-edge margin. -/
theorem forkSchurPrevCoefficient_step_eq_terminal_response
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) =
      -((q (S.fork (S.step j)) *
          (sourceForkBackCoeff next weight back rho
            (S.fork (S.step j))
            ((S.gap j).idx (Fin.last (S.gapLength j))) /
              e ((S.gap j).idx (Fin.last (S.gapLength j))))) *
          weight ((S.gap j).idx
            (finitePathPrev (Fin.last (S.gapLength j)) (by simpa using hm))) *
          yw j (finitePathPrev (Fin.last (S.gapLength j)) (by simpa using hm)) -
        (p (S.fork (S.step j)) / e (S.fork (S.step j)) +
          q (S.fork (S.step j)) *
            (sourceForkBackCoeff next weight back rho
              (S.fork (S.step j))
              ((S.gap j).idx (Fin.last (S.gapLength j))) /
                e ((S.gap j).idx (Fin.last (S.gapLength j))))) *
          yw j (Fin.last (S.gapLength j))) := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  have hdirect := (S.wrap j).right_left_entry_zero hm weight p q e rho
  have hgap := (S.wrap j).pre.fork_preGap_mul hm
    weight p q e rho hunit (yw j)
  change M (S.fork (S.step j)) (S.fork j) = 0 at hdirect
  change (∑ i, M (S.fork (S.step j)) ((S.gap j).idx i) * yw j i) = _ at hgap
  simp only [forkSchurPrevCoefficient]
  rw [S.step.symm_apply_apply]
  change M (S.fork (S.step j)) (S.fork j) -
    (∑ i, M (S.fork (S.step j)) ((S.gap j).idx i) * yw j i) = _
  rw [hdirect, hgap]
  ring

/-- The literal successor Schur coefficient is the condensed forward
quantity `Fprev` used by the coupled two-edge margin. -/
theorem forkSchurNextCoefficient_eq_condensed_response
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hxf : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i) :
    S.forkSchurNextCoefficient weight p q e rho xf j =
      let k := q (S.fork j) *
        (sourceForkNextCoeff next weight back rho (S.fork j) /
          e (next (S.fork j)))
      let eff := (S.gap j).properWrapState weight p q e rho
        (weight (S.fork j)) k
      eff.k * finitePathNatLift (xf j) (S.gapLength j - 1) := by
  let m := S.gapLength j
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  have hscale : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hk : 0 < k := mul_pos (hq (S.fork j))
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw (S.fork j))
      (he (next (S.fork j))))
  have hboundary := S.forkSchurNextCoefficient_eq_boundary_response
    weight p q e rho xf j hm
  change S.forkSchurNextCoefficient weight p q e rho xf j =
    ((S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) k).k * finitePathNatLift (xf j) (m - 1)
  rw [hboundary]
  change k * xf j 0 = _
  by_cases hm1 : S.gapLength j = 1
  · have hmdef : m = 1 := by simpa [m] using hm1
    have heff :
        ((S.gap j).properWrapState weight p q e rho
          (weight (S.fork j)) k).k = k := by
      simp [SourceGapEmbedding.properWrapState, natWrapPrefixState, hm1]
    have hlift : finitePathNatLift (xf j) (m - 1) = xf j 0 := by
      rw [hmdef]
      simp [finitePathNatLift_of_lt]
    rw [heff, hlift]
  · have hm2 : 1 < S.gapLength j := by omega
    apply (S.gap j).restricted_forward_boundary_transport hm weight p q e rho
      (xf j) hp hq he hrho hw hscale hk
    · have hx := hxf (0 : Fin (m + 1))
      have h0m1 : (0 : ℕ) ≠ S.gapLength j - 1 := by omega
      have h0m : (0 : ℕ) ≠ S.gapLength j := by omega
      simpa [sourceWrapForwardForcing, h0m1, h0m] using hx
    · intro i hi him
      have hi1 : i.val ≠ S.gapLength j - 1 := by omega
      have him' : i.val ≠ S.gapLength j := by omega
      simpa [sourceWrapForwardForcing, hi1, him'] using hxf i

/-- Every genuine successor Schur coefficient across a positive literal gap
is strictly positive. -/
theorem forkSchurNextCoefficient_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i) :
    0 < S.forkSchurNextCoefficient weight p q e rho xf j := by
  let m := S.gapLength j
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) k
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) m)
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
  let keff := wrapCondensedK eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) eff.k
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) m
  have hboundary := S.forkSchurNextCoefficient_eq_condensed_response
    weight p q e rho xf j hm hp hq he hrho hw hxf
  have hscale : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hk : 0 < k := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hflux := (S.gap j).literal_forward_flux_eq hm
    weight p q e rho (xf j) hp hq he hrho hw hscale hk
    (by simpa [SourceGapEmbedding.gapS, m] using hunit)
    (by intro i; simpa [sourceWrapForwardForcing, m] using hxf i)
  let An := finitePathNatLift ((S.gap j).gapA p e)
  let cn := finitePathNatLift ((S.gap j).gapC weight q e rho)
  let sn := finitePathNatLift ((S.gap j).gapS weight)
  have hAn : ∀ i, 0 < An i := fun i => div_pos (hp _) (he _)
  have hcn : ∀ i, 0 < cn i := by
    intro i
    unfold cn finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hsn : ∀ i, 0 < sn i := fun i => (S.gap j).gapS_pos hw _
  have heff : eff.StrictlyPositive := by
    simpa [eff, SourceGapEmbedding.properWrapState, An, cn, sn, m] using
      (natWrapPrefixState_pos An cn sn hAn hcn hsn hscale hk (m - 1))
  have hparams := wrap_condensed_parameters_pos heff.1 (hAn m) (hcn (m - 1))
    (hsn (m - 1)) heff.2.1 heff.2.2 (show (0 : ℝ) < 1 by norm_num)
  have hd : 0 < d := by
    dsimp [d, Aeff, m, cn] at hparams ⊢
    linarith [hparams.1, hcn (S.gapLength j)]
  have hkeff : 0 < keff := by
    simpa [keff, eff, m, cn, sn] using hparams.2.2.1
  dsimp [m, k, eff, Aeff, keff, d] at hboundary hflux ⊢
  rw [hboundary, hflux]
  exact div_pos hkeff hd

/-- Exact two-port assembly: after internal reconstruction, the literal fork
row is a three-term Schur equation on predecessor, self, and successor fork
coordinates. -/
theorem fork_schur_three_term_of_reconstruction
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hrec : ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))))
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∀ j : Fin l,
      S.forkSchurPrevCoefficient weight p q e rho yw j *
          x (S.fork (S.step.symm j)) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw j *
          x (S.fork j) +
        S.forkSchurNextCoefficient weight p q e rho xf j *
          x (S.fork (S.step j)) = 0 := by
  intro j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let pred := S.step.symm j
  have hpre := sum_mul_negative_two_response
    (fun i => M (S.fork j) ((S.gap pred).idx i))
    (yw pred) (xf pred) (x (S.fork pred)) (x (S.fork j))
  have hpost := sum_mul_negative_two_response
    (fun i => M (S.fork j) ((S.gap j).idx i))
    (yw j) (xf j) (x (S.fork j)) (x (S.fork (S.step j)))
  have hsplit := S.fork_kernel_row_split hprevnext
    weight p q e rho x hker j
  simp_rw [hrec] at hsplit
  simp only [S.step.apply_symm_apply] at hsplit
  change
    (∑ i, M (S.fork j) ((S.gap pred).idx i) *
      -(yw pred i * x (S.fork pred) + xf pred i * x (S.fork j))) = _ at hpre
  change
    (∑ i, M (S.fork j) ((S.gap j).idx i) *
      -(yw j i * x (S.fork j) + xf j i * x (S.fork (S.step j)))) = _ at hpost
  rw [hpre, hpost] at hsplit
  change
    (M (S.fork j) (S.fork pred) -
        ∑ i, M (S.fork j) ((S.gap pred).idx i) * yw pred i) *
          x (S.fork pred) +
      (M (S.fork j) (S.fork j) -
          (∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i) -
          ∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i) *
          x (S.fork j) +
      (M (S.fork j) (S.fork (S.step j)) -
          ∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i) *
          x (S.fork (S.step j)) = 0
  simpa only [forkSchurPrevCoefficient, forkSchurSelfCoefficient,
    forkSchurNextCoefficient, M, pred] using (by
      linear_combination hsplit)

end SourceCyclicNonemptyGapSystem

end TypeIIL
