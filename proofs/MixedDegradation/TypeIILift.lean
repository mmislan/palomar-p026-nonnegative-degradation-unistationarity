import proofs.MixedDegradation.TypeIISkeleton
import proofs.MixedDegradation.PassiveChain
import proofs.TypeIIL.PaperSourceLift

namespace MixedDegradation.TypeII
open TypeIIL TypeII3
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators
noncomputable section
variable {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}

structure Rates (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) where
  tailDepth : Fin l → ℕ
  tailDepth_pos : ∀ j, 1 ≤ tailDepth j
  tailCycleWeight : ∀ j, Fin (tailDepth j+1) → ℕ
  tailCycleWeight_pos : ∀ j k, 0 < tailCycleWeight j k
  terminal_cycle_weight : ∀ j, weight (S.paperTailTerminal j) = tailCycleWeight j 0
  chain : Fin l → MixedDegradation.UnitChain
  plus : Fin n → ℝ
  minus : Fin n → ℝ
  degrade : Fin n → ℝ
  plus_pos : ∀ r, 0 < plus r
  minus_pos : ∀ r, 0 < minus r
  degrade_nonneg : ∀ i, 0 ≤ degrade i
  terminal_plus : ∀ j, plus (S.paperTailTerminal j) = (chain j).summary.c
  terminal_minus : ∀ j, minus (S.paperTailTerminal j) = (chain j).summary.beta

def ReturnMinimal {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) : Prop :=
  ∀ j, EveryPaperTailRotationPassesMinimality (rates.tailCycleWeight j)

@[ext] structure State (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rates : Rates S weight) where
  core : Fin n → ℝ
  tail : ∀ j, (rates.chain j).State

def positiveTail : (q : MixedDegradation.UnitChain) → q.State → Prop
  | .direct _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _, z => positiveTail q z.1 ∧ 0 < z.2

def Positive {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} {rates : Rates S weight} (x : State S weight rates) : Prop :=
  (∀ i, 0 < x.core i) ∧ ∀ j, positiveTail (rates.chain j) (x.tail j)

def current {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  rates.plus r*x r-rates.minus r*paperSourceProductMonomial (sourceProductExponent next weight back) r x

def Stationary {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (x : State S weight rates) : Prop :=
  ∃ jL jR : Fin l → ℝ,
    (∀ j, MixedDegradation.ChainFlux (rates.chain j) (x.tail j)
      (x.core (S.paperTailTerminal j)) (x.core (S.fork j)) (jL j) (jR j)) ∧
    ∀ i, (∑ r, sourceStoich next weight back i r*current rates x.core r) -
      (∑ j, sourceStoich next weight back i (S.paperTailTerminal j)*current rates x.core (S.paperTailTerminal j)) +
      (∑ j, paperTailBoundaryContribution S i j (jL j) (jR j)) = rates.degrade i*x.core i

def leak {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (i : Fin n) (j : Fin l) : ℝ :=
  (if i=S.paperTailTerminal j then (rates.chain j).summary.leakL else 0) +
    (if i=S.fork j then (rates.chain j).summary.leakR else 0)

def effectiveLoss {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (i : Fin n) : ℝ :=
  rates.degrade i + ∑ j, leak rates i j

theorem effectiveLoss_nonneg {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (i : Fin n) : 0 ≤ effectiveLoss rates i := by
  apply add_nonneg (rates.degrade_nonneg i)
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · split_ifs <;> first | exact (rates.chain j).summary.leakL_nonneg | exact le_rfl
  · split_ifs <;> first | exact (rates.chain j).summary.leakR_nonneg | exact le_rfl

theorem terminal_unit {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (hm : ReturnMinimal rates) (j : Fin l) :
    weight (S.paperTailTerminal j) = 1 := by
  rw [rates.terminal_cycle_weight]
  exact paper_tail_all_weights_eq_one_of_minimality (rates.tailDepth_pos j)
    (rates.tailCycleWeight j) (rates.tailCycleWeight_pos j) (hm j) 0

theorem boundary_compress {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (hm : ReturnMinimal rates)
    (x : State S weight rates) (j : Fin l) {jL jR : ℝ}
    (hflux : MixedDegradation.ChainFlux (rates.chain j) (x.tail j)
      (x.core (S.paperTailTerminal j)) (x.core (S.fork j)) jL jR) (i : Fin n) :
    paperTailBoundaryContribution S i j jL jR =
      sourceStoich next weight back i (S.paperTailTerminal j)*current rates x.core (S.paperTailTerminal j) -
        leak rates i j*x.core i := by
  have hu := terminal_unit rates hm j
  have hmon : paperSourceProductMonomial (sourceProductExponent next weight back)
      (S.paperTailTerminal j) x.core = x.core (S.fork j) :=
    S.monomialRatio_paperTailTerminal weight x.core j hu
  obtain ⟨hL,hR⟩ := MixedDegradation.chain_flux_compress (rates.chain j) (x.tail j) hflux
  rw [S.sourceStoich_paperTailTerminal weight j hu i]
  unfold current
  rw [hmon, rates.terminal_plus, rates.terminal_minus]
  have hne := S.paperTailTerminal_ne_fork j
  unfold paperTailBoundaryContribution leak
  by_cases hiT : i=S.paperTailTerminal j
  · subst i
    simp [hne]
    linarith
  · by_cases hiF : i=S.fork j
    · subst i
      simp [hiT]
      linarith
    · simp [hiT,hiF]

theorem stationary_compress {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (hm : ReturnMinimal rates)
    (x : State S weight rates) (hx : Stationary rates x) :
    massActionDrift (sourceStoich next weight back) (sourceProductExponent next weight back)
      rates.plus rates.minus (effectiveLoss rates) x.core = 0 := by
  obtain ⟨jL,jR,hchain,hrows⟩ := hx
  funext i
  have hr := hrows i
  simp_rw [boundary_compress rates hm x _ (hchain _) i] at hr
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hr
  change (∑ r, sourceStoich next weight back i r*current rates x.core r) -
    effectiveLoss rates i*x.core i = 0
  dsimp [effectiveLoss]
  linarith

theorem separated_unistationarity
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (hl : 3 ≤ l)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (rates : Rates S weight) (hm : ReturnMinimal rates)
    (x y : State S weight rates) (hx : Positive x) (hy : Positive y)
    (hxs : Stationary rates x) (hys : Stationary rates y) : x=y := by
  have hu : ∀ a, weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1 := by
    intro a
    have ht := terminal_unit rates hm (S.step a)
    change weight ((S.gap (S.step.symm (S.step a))).idx
      (Fin.last (S.gapLength (S.step.symm (S.step a))))) = 1 at ht
    rw [S.step.symm_apply_apply] at ht
    exact ht
  have hc := typeII_skeleton_unistationarity S hl (S.prev_ne_next_of_three_le hl)
    weight hw hu rates.plus rates.minus (effectiveLoss rates) rates.plus_pos rates.minus_pos
    (effectiveLoss_nonneg rates) x.core y.core hx.1 hy.1
    (stationary_compress rates hm x hxs) (stationary_compress rates hm y hys)
  apply State.ext hc
  obtain ⟨jL,jR,hchain,_⟩ := hxs
  obtain ⟨kL,kR,kchain,_⟩ := hys
  funext j
  apply MixedDegradation.chain_state_unique (rates.chain j) (x.tail j) (y.tail j) (hchain j)
  simpa only [hc] using kchain j

end
end MixedDegradation.TypeII
