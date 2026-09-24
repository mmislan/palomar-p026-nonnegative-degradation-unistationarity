import proofs.MixedDegradation.TypeIIInterior
import proofs.MixedDegradation.CurrentJacobian
import proofs.MixedDegradation.SourceSecantDerivative

namespace MixedDegradation
open TypeIIL
open TypeIIL.SourceCyclicNonemptyGapSystem

theorem typeII_interior_jacobian_nonsingular
    {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r) (he : ∀ r, 0 < e r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a, weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hbase : TypeII3.BaseFluxBalance (sourceStoich next weight back) p q e) :
    (scaledJacobian (sourceStoich next weight back)
      (fun i r => (sourceProductExponent next weight back i r : ℝ)) p q e).det ≠ 0 := by
  have hd : ∀ r z, back r = some z → z ≠ next r := by
    intro r z hr
    rcases S.cover r with ⟨a, rfl⟩ | ⟨a, i, rfl⟩
    · rw [S.back_fork a] at hr
      injection hr with hz
      subst z
      simpa using (S.wrap a).post.back_ne_next
    · rw [(S.gap a).nonfork i] at hr
      contradiction
  apply scaledJacobian_nonsingular_of_current_kernel _ _ p q e (fun i => ne_of_gt (he i))
  have hk := typeII_interior_current_kernel_nonsingular S hl hprevnext weight
    p q e (fun _ => 1) hp hq he (by intro i; norm_num) hw hunit hbase
  simpa [backFirstCurrentMatrix, source_secant_at_one next weight back hd] using hk

end MixedDegradation
