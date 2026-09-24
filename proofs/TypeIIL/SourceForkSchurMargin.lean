import proofs.TypeIIL.SourceForkSchurDiagonal
import proofs.TypeIIL.SourceWrapLiteralSchurMargin

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- The abstract literal response margin docks to the genuine cyclic Schur
coefficients.  The only analytic inputs are lower bounds for the right core
`B-F` and the preceding diagonal `Bprev`; response uniqueness identifies the
local witnesses with the globally chosen Schur responses. -/
theorem forkSchurPrev_mul_next_lt_of_core_bounds
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i)
    (hyw : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        sourceWrapLeftForcing ((S.gap j).gapA p e)
          (weight (S.fork j)) i)
    {X Bprev : ℝ}
    (hXcore :
      let k := q (S.fork j) *
        (sourceForkNextCoeff next weight back rho (S.fork j) /
          e (next (S.fork j)))
      let h := q (S.fork (S.step j)) *
        (sourceForkBackCoeff next weight back rho (S.fork (S.step j))
          ((S.gap j).idx (Fin.last (S.gapLength j))) /
            e ((S.gap j).idx (Fin.last (S.gapLength j))))
      let g := p (S.fork (S.step j)) / e (S.fork (S.step j))
      let eff := (S.gap j).properWrapState weight p q e rho
        (weight (S.fork j)) k
      let Aeff := wrapCondensedA eff.A
        (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
        (finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j - 1))
        (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
      let heff := wrapCondensedH eff.A
        (finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j - 1))
        (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) h
      let d := 1 + Aeff +
        finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
      (d + g + heff) / d ≤ X)
    (hBcore :
      let k := q (S.fork j) *
        (sourceForkNextCoeff next weight back rho (S.fork j) /
          e (next (S.fork j)))
      let eff := (S.gap j).properWrapState weight p q e rho
        (weight (S.fork j)) k
      let Aeff := wrapCondensedA eff.A
        (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
        (finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j - 1))
        (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
      let seff := wrapCondensedScale eff.A
        (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.scale
      let keff := wrapCondensedK eff.A
        (finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j - 1))
        (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.k
      let d := 1 + Aeff +
        finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
      (d + keff * seff *
        (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j))) / d ≤ Bprev) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j < X * Bprev := by
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let h := q (S.fork (S.step j)) *
    (sourceForkBackCoeff next weight back rho (S.fork (S.step j))
      ((S.gap j).idx (Fin.last (S.gapLength j))) /
        e ((S.gap j).idx (Fin.last (S.gapLength j))))
  let g := p (S.fork (S.step j)) / e (S.fork (S.step j))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) k
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
    (finitePathNatLift ((S.gap j).gapC weight q e rho)
      (S.gapLength j - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
  let heff := wrapCondensedH eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho)
      (S.gapLength j - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) h
  let seff := wrapCondensedScale eff.A
    (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.scale
  let keff := wrapCondensedK eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho)
      (S.gapLength j - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.k
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
  let followingBudget := X - (d + g + heff) / d
  let precedingCorrection :=
    (d + keff * seff *
      (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j))) / d - Bprev
  have hfollowing : 0 ≤ followingBudget := by
    dsimp [followingBudget]
    dsimp [k, h, g, eff, Aeff, heff, d] at hXcore
    linarith
  have hpreceding : precedingCorrection ≤ 0 := by
    dsimp [precedingCorrection]
    dsimp [k, eff, Aeff, seff, keff, d] at hBcore
    linarith
  have hXeq : X = (d + g + heff) / d + followingBudget := by
    dsimp [followingBudget]
    ring
  have hBeq : Bprev =
      (d + keff * seff *
        (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
          (S.gapLength j))) / d - precedingCorrection := by
    dsimp [precedingCorrection]
    ring
  obtain ⟨xf', yw', hxf', hyw', hmargin⟩ :=
    (S.wrap j).exists_literal_responses_and_raw_margin hm
      weight p q e rho hp hq he hrho hw hunit
      hfollowing hpreceding
      (by simpa [k, h, g, eff, Aeff, heff, d] using hXeq)
      (by simpa [k, eff, Aeff, seff, keff, d] using hBeq)
  have hxfActual : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          ((S.gap j).idx i) (S.fork (S.step j)) := by
    intro i
    rw [(S.wrap j).internal_right_column_eq_forcing hm
      weight p q e rho hunit i]
    exact hxf i
  have hywActual : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          ((S.gap j).idx i) (S.fork j) := by
    intro i
    rw [(S.wrap j).internal_left_column_eq_forcing weight p q e rho i]
    exact hyw i
  have hxfEq : xf' = xf j := (S.gap j).restricted_response_unique
    weight p q e rho (fun a => le_of_lt (hp a)) (fun a => le_of_lt (hq a))
    he hrho hw _ xf' (xf j) hxf' hxfActual
  have hywEq : yw' = yw j := (S.gap j).restricted_response_unique
    weight p q e rho (fun a => le_of_lt (hp a)) (fun a => le_of_lt (hq a))
    he hrho hw _ yw' (yw j) hyw' hywActual
  subst xf'
  subst yw'
  have hF := S.forkSchurNextCoefficient_eq_condensed_response
    weight p q e rho xf j hm hp hq he hrho hw hxf
  have hW := S.forkSchurPrevCoefficient_step_eq_terminal_response
    weight p q e rho yw j hm hunit
  dsimp [k, h, g, eff] at hmargin hF hW
  have hprevEq :
      (⟨S.gapLength j - 1, by omega⟩ : Fin (S.gapLength j + 1)) =
        finitePathPrev (Fin.last (S.gapLength j)) (by simpa using hm) := by
    apply Fin.ext
    simp [finitePathPrev]
  have hlastEq :
      (⟨S.gapLength j, by omega⟩ : Fin (S.gapLength j + 1)) =
        Fin.last (S.gapLength j) := by
    apply Fin.ext
    simp
  have hsLift :
      finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1) =
        (weight ((S.gap j).idx
          (finitePathPrev (Fin.last (S.gapLength j))
            (by simpa using hm))) : ℝ) := by
    rw [finitePathNatLift_of_lt (i := S.gapLength j - 1)
      ((S.gap j).gapS weight) (by omega), hprevEq]
    rfl
  have hyPrevLift :
      finitePathNatLift (yw j) (S.gapLength j - 1) =
        yw j (finitePathPrev (Fin.last (S.gapLength j))
          (by simpa using hm)) := by
    rw [finitePathNatLift_of_lt (i := S.gapLength j - 1) (yw j) (by omega),
      hprevEq]
  have hyLastLift :
      finitePathNatLift (yw j) (S.gapLength j) =
        yw j (Fin.last (S.gapLength j)) := by
    rw [finitePathNatLift_of_lt (i := S.gapLength j) (yw j) (by omega),
      hlastEq]
  rw [hsLift, hyPrevLift, hyLastLift] at hmargin
  rw [hF, hW]
  exact hmargin

/-- A long literal gap supplies the strict adjacent-product margin needed by
the cyclic tridiagonal closure.  Both diagonal bounds are consequences of the
source balance identities: the following response is absorbed on the right,
and the preceding terminal-basis shift is absorbed on the left. -/
theorem forkSchurPrev_mul_next_lt_self_sub_next_mul_self_of_long_gap
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 1 < S.gapLength j)
    (hnext : 0 < S.gapLength (S.step j))
    (hpred : 0 < S.gapLength (S.step.symm j))
    (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hnextUnit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hpredUnit : weight ((S.gap (S.step.symm j)).idx
      (Fin.last (S.gapLength (S.step.symm j)))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j <
      (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
          S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  apply S.forkSchurPrev_mul_next_lt_of_core_bounds weight p q e rho xf yw j
    (Nat.zero_lt_of_lt hm) hp hq he hrho hw hunit (hxf j) (hyw j)
  · exact S.right_core_le_forkSchurSelf_sub_next weight p q e rho xf yw j
      hm hnext hp hq he hrho hw hunit hnextUnit hxf hyw
  · exact S.literal_positive_preceding_left_core_le_forkSchurSelf
      weight p q e rho xf yw j (Nat.zero_lt_of_lt hm) hpred JFork
      hp hq he hrho hw hJFork hunit hpredUnit horder hpFork hpLast
      hxf (hyw j)

/-- Uniform strict adjacent-product margin for every positive literal gap.
The only length split is internal to the right-core identity; the cyclic
closure sees one invariant statement. -/
theorem forkSchurPrev_mul_next_lt_self_sub_next_mul_self_of_positive_gap
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hnext : 0 < S.gapLength (S.step j))
    (hpred : 0 < S.gapLength (S.step.symm j))
    (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hnextUnit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hpredUnit : weight ((S.gap (S.step.symm j)).idx
      (Fin.last (S.gapLength (S.step.symm j)))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j <
      (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
          S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  apply S.forkSchurPrev_mul_next_lt_of_core_bounds weight p q e rho xf yw j
    hm hp hq he hrho hw hunit (hxf j) (hyw j)
  · by_cases hm1 : S.gapLength j = 1
    · exact S.two_coordinate_right_core_le_forkSchurSelf_sub_next
        weight p q e rho xf yw j hm1 hnext hp hq he hrho hw
        hunit hnextUnit hxf hyw
    · exact S.right_core_le_forkSchurSelf_sub_next weight p q e rho xf yw j
        (by omega) hnext hp hq he hrho hw hunit hnextUnit hxf hyw
  · exact S.literal_positive_preceding_left_core_le_forkSchurSelf
      weight p q e rho xf yw j hm hpred JFork hp hq he hrho hw hJFork
      hunit hpredUnit horder hpFork hpLast hxf (hyw j)

/-- Uniform sign package for the genuine cyclic Schur row.  Positive literal
gaps and unit terminal weights force a positive successor port, a strictly
positive diagonal gap, hence a positive diagonal dominating that port. -/
theorem forkSchur_cyclic_signs
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    0 < S.forkSchurNextCoefficient weight p q e rho xf j ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j -
        S.forkSchurNextCoefficient weight p q e rho xf j ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j ∧
      S.forkSchurNextCoefficient weight p q e rho xf j ≤
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  have hnext := S.forkSchurNextCoefficient_pos weight p q e rho xf j
    (hgap j) hp hq he hrho hw (hunit j) (hxf j)
  have hstep : S.step (S.step.symm j) = j := S.step.apply_symm_apply j
  have hdiag := S.forkSchurSelf_sub_next_pos weight p q e rho xf yw
    (S.step.symm j) (hgap (S.step.symm j))
    (by simpa using hgap j) hp hq he hrho hw (hunit (S.step.symm j))
    (by rw [hstep]; exact hunit j) hxf hyw
  have hdiag' :
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j -
        S.forkSchurNextCoefficient weight p q e rho xf j := by
    simpa [hstep] using hdiag
  constructor
  · exact hnext
  constructor
  · exact hdiag'
  constructor <;> linarith

end SourceCyclicNonemptyGapSystem

end TypeIIL
