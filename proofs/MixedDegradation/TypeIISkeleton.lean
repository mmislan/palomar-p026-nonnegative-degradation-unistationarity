import proofs.MixedDegradation.SourceBoundary
import proofs.MixedDegradation.LogDrift
import proofs.TypeIIL.PaperFullClosure

namespace MixedDegradation
open TypeIIL TypeII3
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators
noncomputable section

def massActionDrift {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (P : Fin n → Fin n → ℕ) (a b d x : Fin n → ℝ) : Fin n → ℝ :=
  N.mulVec (fun r => a r*x r-b r*paperSourceProductMonomial P r x) -
    (fun i => d i*x i)

theorem exp_product_exponent {n : ℕ} (P : Fin n → Fin n → ℕ)
    (z : Fin n → ℝ) (r : Fin n) :
    Real.exp ((Matrix.transpose (fun i r => (P i r : ℝ))).mulVec z r) =
      paperSourceProductMonomial P r (fun i => Real.exp (z i)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Real.exp_sum, Real.exp_nat_mul, paperSourceProductMonomial]

theorem logDrift_eq_massAction {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (P : Fin n → Fin n → ℕ) (a b d z : Fin n → ℝ) (ε : ℝ) :
    logDrift N (fun i r => (P i r : ℝ)) a b d (ε,z) =
      massActionDrift N P a b (fun i => d i+ε) (fun i => Real.exp (z i)) := by
  unfold logDrift massActionDrift
  congr 1
  congr 1
  funext r
  simp [logForward, logReverse, exp_product_exponent]

theorem typeII_skeleton_unistationarity
    {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a, weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (a b d : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hd : ∀ i, 0 ≤ d i)
    (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxs : massActionDrift (sourceStoich next weight back)
      (sourceProductExponent next weight back) a b d x = 0)
    (hys : massActionDrift (sourceStoich next weight back)
      (sourceProductExponent next weight back) a b d y = 0) : x=y := by
  let N := sourceStoich next weight back
  let P := sourceProductExponent next weight back
  have huni : ∀ ε, 0 < ε → ∀ u v : Fin n → ℝ,
      logDrift N (fun i r => (P i r : ℝ)) a b d (ε,u) = 0 →
      logDrift N (fun i r => (P i r : ℝ)) a b d (ε,v) = 0 → u=v := by
    intro ε hε u v hu hv
    let rates : PaperSourceRates n :=
      { plus := a, minus := b, degrade := fun i => d i+ε,
        plus_pos := ha, minus_pos := hb,
        degrade_pos := fun i => add_pos_of_nonneg_of_pos (hd i) hε }
    rw [logDrift_eq_massAction] at hu hv
    have hsu : IsPaperSourceStationary next weight back rates (fun i => Real.exp (u i)) := by
      intro i
      have hh := congrFun (sub_eq_zero.mp hu) i
      exact hh
    have hsv : IsPaperSourceStationary next weight back rates (fun i => Real.exp (v i)) := by
      intro i
      have hh := congrFun (sub_eq_zero.mp hv) i
      exact hh
    have heq := S.paper_source_typeII_l_weak_gap_unistationarity hl hprevnext weight
      hw hunit rates (fun i => Real.exp (u i)) (fun i => Real.exp (v i))
      (fun i => Real.exp_pos _) (fun i => Real.exp_pos _) hsu hsv
    funext i
    exact Real.exp_injective (congrFun heq i)
  have hn : ∀ p q e : Fin n → ℝ, (∀ i, 0 < p i) → (∀ i, 0 < q i) →
      (∀ i, 0 ≤ e i) → N.mulVec (p-q) = e →
      (scaledJacobian N (fun i r => (P i r : ℝ)) p q e).det ≠ 0 := by
    intro p q e hp hq he hbase
    exact typeII_boundary_jacobian_nonsingular S hl hprevnext weight hw hunit
      p q e hp hq he (fun i => congrFun hbase i)
  have hlogx : logDrift N (fun i r => (P i r : ℝ)) a b d
      (0,fun i => Real.log (x i)) = 0 := by
    rw [logDrift_eq_massAction]
    have hex : (fun i => Real.exp (Real.log (x i))) = x := funext (fun i => Real.exp_log (hx i))
    rw [hex]
    simpa only [add_zero] using hxs
  have hlogy : logDrift N (fun i r => (P i r : ℝ)) a b d
      (0,fun i => Real.log (y i)) = 0 := by
    rw [logDrift_eq_massAction]
    have hey : (fun i => Real.exp (Real.log (y i))) = y := funext (fun i => Real.exp_log (hy i))
    rw [hey]
    simpa only [add_zero] using hys
  have heq := logDrift_boundary_uniqueness N (fun i r => (P i r : ℝ))
    a b d ha hb hd huni hn _ _ hlogx hlogy
  funext i
  have hh := congrArg Real.exp (congrFun heq i)
  simpa [Real.exp_log (hx i), Real.exp_log (hy i)] using hh

end
end MixedDegradation
