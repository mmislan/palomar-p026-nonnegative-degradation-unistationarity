import proofs.MixedDegradation.SourceJacobian
import proofs.MixedDegradation.SourceInvertible
import proofs.MixedDegradation.StationaryBoundary

namespace MixedDegradation
open TypeIIL
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators

theorem source_product_eq_one_add {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ) (back : Fin n → Option (Fin n)) :
    (fun i r => (sourceProductExponent next weight back i r : ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) + sourceStoich next weight back := by
  ext i j
  change (sourceProductExponent next weight back i j : ℝ) =
    (if i=j then 1 else 0) + ((sourceProductExponent next weight back i j : ℝ) -
      (if i=j then 1 else 0))
  ring

theorem typeII_boundary_jacobian_nonsingular
    {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a, weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (p q e : Fin n → ℝ) (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 ≤ e r)
    (hbase : TypeII3.BaseFluxBalance (sourceStoich next weight back) p q e) :
    (scaledJacobian (sourceStoich next weight back)
      (fun i r => (sourceProductExponent next weight back i r : ℝ)) p q e).det ≠ 0 := by
  let N := sourceStoich next weight back
  have hN : N.det ≠ 0 := typeII_source_stoich_nonsingular S weight hw hunit
  rw [source_product_eq_one_add]
  apply stationary_boundary_nonsingular N N⁻¹
    (Matrix.mul_nonsing_inv N (isUnit_iff_ne_zero.mpr hN))
  · intro pp qq ee hpp hqq hee hb
    rw [← source_product_eq_one_add]
    apply typeII_interior_jacobian_nonsingular S hl hprevnext weight pp qq ee
      hpp hqq hee hw hunit
    intro i
    exact congrFun hb i
  · exact hp
  · exact hq
  · exact he
  · funext i
    exact hbase i

end MixedDegradation
