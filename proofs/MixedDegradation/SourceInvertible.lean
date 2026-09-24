import proofs.TypeIIL.SourceBaseCurrentTransport
import proofs.TypeIIL.CyclicCombinedCone

namespace MixedDegradation
open TypeIIL
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators

theorem fin_weighted_stem_zero (m : ℕ) (s J : Fin (m+1) → ℝ)
    (hs : ∀ i, s i ≠ 0)
    (hstep : ∀ i : Fin m, s i.castSucc * J i.castSucc = J i.succ)
    (hlast : J (Fin.last m) = 0) : ∀ i, J i = 0 := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact hlast
  | cast i ih =>
    exact (mul_eq_zero.mp ((hstep i).trans ih)).resolve_left (hs i.castSucc)

theorem typeII_source_stoich_nonsingular
    {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a, weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1) :
    (sourceStoich next weight back).det ≠ 0 := by
  apply det_ne_zero_of_mulVec_kernel_eq_zero
  intro x hx
  have hb : TypeII3.BaseFluxBalance (sourceStoich next weight back) x 0 0 := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hx i
  have hin : ∀ a i, x (S.gapIncomingReaction a i) = 0 := by
    intro a
    let s : Fin (S.gapLength a + 1) → ℝ := fun i => (weight (S.gapIncomingReaction a i) : ℝ)
    let J : Fin (S.gapLength a + 1) → ℝ := fun i => x (S.gapIncomingReaction a i)
    have hs : ∀ i, s i ≠ 0 := by
      intro i
      exact ne_of_gt (Nat.cast_pos.mpr (hw _))
    apply fin_weighted_stem_zero (S.gapLength a) s J hs
    · intro i
      have hg := S.base_gap_current_balance weight x 0 0 hb a i.castSucc
      have hne : i.castSucc ≠ Fin.last (S.gapLength a) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      rw [if_neg hne] at hg
      dsimp [s, J]
      rw [S.gapIncomingReaction_succ]
      simp only [Pi.zero_apply, sub_zero, add_zero] at hg
      linarith only [hg]
    · have hg := S.base_gap_current_balance weight x 0 0 hb a (Fin.last (S.gapLength a))
      have hu : weight ((S.gap (S.step.symm (S.step a))).idx
          (Fin.last (S.gapLength (S.step.symm (S.step a))))) = 1 := by
        rw [S.step.symm_apply_apply]
        exact hunit a
      have hf := S.base_fork_current_balance weight x 0 0 hb (S.step a) hu
      rw [S.step.symm_apply_apply] at hf
      simp only [Pi.zero_apply, sub_zero, if_true] at hg hf
      have hp : s (Fin.last (S.gapLength a)) * J (Fin.last (S.gapLength a)) = 0 := by
        dsimp [s, J]
        linarith
      exact (mul_eq_zero.mp hp).resolve_left (hs _)
  have hf : ∀ a, x (S.fork a) = 0 := by
    intro a
    simpa using hin a 0
  funext r
  change x r = 0
  rcases S.cover r with ⟨a, rfl⟩ | ⟨a, i, rfl⟩
  · exact hf a
  · have hg := S.base_gap_current_balance weight x 0 0 hb a i
    rw [hin a i] at hg
    simp only [Pi.zero_apply, sub_zero, mul_zero] at hg
    split_ifs at hg with hi
    · rw [hf] at hg
      linarith
    · linarith

end MixedDegradation
