import proofs.TypeIIL.SourceBackFirstWeakClosure

namespace MixedDegradation
open TypeIIL
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators

/-- The inherited analytic proof excludes every current-kernel vector using
one base stationary state. A second stationary state is not required. -/
theorem typeII_interior_current_kernel_nonsingular
    {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hbase : TypeII3.BaseFluxBalance (sourceStoich next weight back) p q e) :
    (S.backFirstCurrentMatrix weight p q e rho).det ≠ 0 := by
  letI : NeZero l := ⟨by omega⟩
  obtain ⟨xf, yw, hxf, hyw⟩ := S.exists_actual_fork_column_responses
    weight p q e rho (fun r => (hp r).le) (fun r => (hq r).le) he hrho hw
  let seam : Fin l := ⟨0, by omega⟩
  have hdet := S.backFirstActualForkSectorMatrix_det_pos hl hprevnext
    weight p q e rho xf yw hbase hp hq he hrho hw hunit hxf hyw seam
  have hself : ∀ a,
      0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a := by
    intro a
    have hnext := S.backFirstActualForkNextCoefficient_pos
      weight p q e rho xf a hp hq he hrho hw (hunit a) (hxf a)
    have hmargin := S.backFirstActualForkSelf_sub_next_ge_one
      weight p q e rho xf yw hbase hp hq he hrho hw hunit hxf hyw a
    linarith
  apply det_ne_zero_of_mulVec_kernel_eq_zero
  intro x hx
  exact S.backFirstActualGlobalCurrentSecantKernel_eq_zero_of_sector_det hprevnext
    weight p q e rho (fun r => (hp r).le) (fun r => (hq r).le) he hrho hw
    xf yw hxf hyw hself hdet x (fun r => congrFun hx r)

end MixedDegradation
