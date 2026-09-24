import proofs.TypeIIL.PaperFullClosure
import proofs.TypeII3.Network.QuotientAllZero

namespace TypeIIL

open TypeII3
open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

noncomputable section

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- Positivity of every internal concentration in a literal unit return
tail.  The existing analytic theorem only needs endpoint positivity, but the
paper theorem quantifies over positive concentrations on all species. -/
def PositiveUnitChainState : (q : UnitChain) → q.State → Prop
  | .direct _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _, z => PositiveUnitChainState q z.1 ∧ 0 < z.2

/-- Literal kinetic data for the strictly separated paper Type `II_l`
normal form.  The terminal reactions of `S` are bookkeeping placeholders for
the return paths: their effective rate constants are required to be the
boundary transfer coefficients of the displayed literal chains. -/
structure PaperSeparatedRates
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) where
  tailDepth : Fin l → ℕ
  tailDepth_pos : ∀ j, 1 ≤ tailDepth j
  tailCycleWeight : ∀ j, Fin (tailDepth j + 1) → ℕ
  tailCycleWeight_pos : ∀ j k, 0 < tailCycleWeight j k
  terminal_cycle_weight : ∀ j,
    weight (S.paperTailTerminal j) = tailCycleWeight j 0
  chain : Fin l → UnitChain
  plus : Fin n → ℝ
  minus : Fin n → ℝ
  degrade : Fin n → ℝ
  plus_pos : ∀ r, 0 < plus r
  minus_pos : ∀ r, 0 < minus r
  degrade_pos : ∀ i, 0 < degrade i
  terminal_plus : ∀ j,
    plus (S.paperTailTerminal j) = (chain j).summary.c
  terminal_minus : ∀ j,
    minus (S.paperTailTerminal j) = (chain j).summary.beta

/-- A concentration state on every retained source species and every
internal return-tail species. -/
@[ext] structure PaperSeparatedState
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rates : PaperSeparatedRates S weight) where
  core : Fin n → ℝ
  tail : ∀ j, (rates.chain j).State

def PositivePaperSeparatedState
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} {rates : PaperSeparatedRates S weight}
    (x : PaperSeparatedState S weight rates) : Prop :=
  (∀ i, 0 < x.core i) ∧
    ∀ j, PositiveUnitChainState (rates.chain j) (x.tail j)

/-- Literal mass-action forward flow on a retained reaction. -/
def paperSeparatedForward
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight)
    (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  rates.plus r * x r

/-- Literal mass-action reverse flow on a retained reaction. -/
def paperSeparatedReverse
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight)
    (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  rates.minus r *
    paperSourceProductMonomial (sourceProductExponent next weight back) r x

/-- The raw stationary equations before tail contraction.  The full retained
reaction sum has its synthetic terminal columns removed, and the literal
left/right currents of the return chains are inserted at their endpoints.
This is simply the finite species balance of the uncontracted paper network. -/
def IsPaperSeparatedStationary
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight)
    (x : PaperSeparatedState S weight rates) : Prop :=
  ∃ jL jR : Fin l → ℝ,
    (∀ j, ChainFlux (rates.chain j) (x.tail j)
      (x.core (S.paperTailTerminal j)) (x.core (S.fork j))
      (jL j) (jR j)) ∧
    ∀ i,
      (∑ r, sourceStoich next weight back i r *
        (paperSeparatedForward rates x.core r -
          paperSeparatedReverse rates x.core r)) -
        (∑ j, sourceStoich next weight back i (S.paperTailTerminal j) *
          (paperSeparatedForward rates x.core (S.paperTailTerminal j) -
            paperSeparatedReverse rates x.core (S.paperTailTerminal j))) +
        (∑ j, paperTailBoundaryContribution S i j (jL j) (jR j)) =
      rates.degrade i * x.core i

/-- Source minimality, restricted to the literal return subcycles, is the
exact consequence of global paper minimality used by the kinetic proof.  A
separate source-exhaustion theorem below derives this field from the raw
restriction predicate. -/
def PaperReturnRestrictionsMinimal
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight) : Prop :=
  ∀ j, EveryPaperTailRotationPassesMinimality (rates.tailCycleWeight j)

/-- A cyclic fork enumeration of length at least three has distinct
predecessor and successor.  This discharges the former public `hprevnext`
assumption from the source data itself. -/
theorem prev_ne_next_of_three_le
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (j : Fin l) : S.step.symm j ≠ S.step j := by
  let _ : NeZero l := ⟨by omega⟩
  intro h
  have hidx : S.cyclicIndexFrom j (l - 1) = S.cyclicIndexFrom j 1 := by
    calc
      S.cyclicIndexFrom j (l - 1) = S.step.symm j :=
        S.cyclicIndexFrom_pred_length (by omega) j
      _ = S.step j := h
      _ = S.cyclicIndexFrom j 1 := by
        rw [← S.step_cyclicIndexFrom j 0, S.cyclicIndexFrom_zero]
  unfold cyclicIndexFrom at hidx
  have hfin : Fin.ofNat l (l - 1) = Fin.ofNat l 1 :=
    (S.cyclicOrderFrom j).injective hidx
  have hv := congrArg Fin.val hfin
  simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : l - 1 < l),
    Nat.mod_eq_of_lt (by omega : 1 < l)] at hv
  omega

theorem paperSeparatedForward_ratio
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight)
    (x y : Fin n → ℝ) (hy : ∀ i, 0 < y i) (r : Fin n) :
    paperSeparatedForward rates x r =
      (x r / y r) * paperSeparatedForward rates y r := by
  calc
    paperSeparatedForward rates x r = rates.plus r * x r := rfl
    _ = rates.plus r * ((x r / y r) * y r) := by
      rw [div_mul_cancel₀ (x r) (ne_of_gt (hy r))]
    _ = (x r / y r) * paperSeparatedForward rates y r := by
      unfold paperSeparatedForward
      ring

theorem paperSeparatedReverse_ratio
    {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : PaperSeparatedRates S weight)
    (x y : Fin n → ℝ) (hy : ∀ i, 0 < y i) (r : Fin n) :
    paperSeparatedReverse rates x r =
      monomialRatio (sourceProductExponent next weight back)
          (fun i => x i / y i) r *
        paperSeparatedReverse rates y r := by
  unfold paperSeparatedReverse
  rw [paperSourceProductMonomial_ratio
    (sourceProductExponent next weight back) hy r]
  ring

/-- The constructed witness together with the four definitional projections
needed to reconstruct the original raw state. -/
structure PaperSeparatedTwoRootLift
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rates : PaperSeparatedRates S weight)
    (x y : PaperSeparatedState S weight rates) where
  witness : PaperTailExpandedTwoRoot S weight
  reconstruct :
    (∀ i, witness.rho i * witness.y i = witness.y i) →
      witness.z0 = witness.z1 → x = y

/-- Construct the analytic two-root witness from literal common rates and two
raw stationary states.  None of the tail currents or stationary balance
fields of `PaperTailExpandedTwoRoot` are public assumptions. -/
noncomputable def paperSeparatedTwoRoot_of_literal_states
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ)
    (rates : PaperSeparatedRates S weight)
    (hminimal : PaperReturnRestrictionsMinimal rates)
    (x y : PaperSeparatedState S weight rates)
    (hx : PositivePaperSeparatedState x)
    (hy : PositivePaperSeparatedState y)
    (hxs : IsPaperSeparatedStationary rates x)
    (hys : IsPaperSeparatedStationary rates y) :
    PaperSeparatedTwoRootLift S weight rates x y := by
  have hxcore := hx.1
  have hycore := hy.1
  let jL1 := Classical.choose hxs
  have hxs1 := Classical.choose_spec hxs
  let jR1 := Classical.choose hxs1
  have hxs2 := Classical.choose_spec hxs1
  let jL0 := Classical.choose hys
  have hys1 := Classical.choose_spec hys
  let jR0 := Classical.choose hys1
  have hys2 := Classical.choose_spec hys1
  have hchain1raw := hxs2.1
  have hstat1 := hxs2.2
  have hchain0 := hys2.1
  have hstat0 := hys2.2
  let P := sourceProductExponent next weight back
  let rho : Fin n → ℝ := fun i => x.core i / y.core i
  let p : Fin n → ℝ := fun r => paperSeparatedForward rates y.core r
  let q : Fin n → ℝ := fun r => paperSeparatedReverse rates y.core r
  have hrho : ∀ i, 0 < rho i := fun i => div_pos (hxcore i) (hycore i)
  have hp : ∀ r, 0 < p r := fun r =>
    mul_pos (rates.plus_pos r) (hycore r)
  have hq : ∀ r, 0 < q r := fun r =>
    mul_pos (rates.minus_pos r)
      (paperSourceProductMonomial_pos P hycore r)
  have hterminalUnit : ∀ j, weight (S.paperTailTerminal j) = 1 := by
    intro j
    have hall := paper_tail_all_weights_eq_one_of_minimality
      (rates.tailDepth_pos j) (rates.tailCycleWeight j)
      (rates.tailCycleWeight_pos j) (hminimal j)
    exact (rates.terminal_cycle_weight j).trans (hall 0)
  have hcoreRatio : ∀ i, x.core i = rho i * y.core i := by
    intro i
    exact (div_mul_cancel₀ (x.core i) (ne_of_gt (hycore i))).symm
  have hchain1 : ∀ j, ChainFlux (rates.chain j) (x.tail j)
      (rho (S.paperTailTerminal j) * y.core (S.paperTailTerminal j))
      (rho (S.fork j) * y.core (S.fork j)) (jL1 j) (jR1 j) := by
    intro j
    simpa only [← hcoreRatio] using hchain1raw j
  have hterminalForward : ∀ j,
      p (S.paperTailTerminal j) =
        (rates.chain j).summary.c * y.core (S.paperTailTerminal j) := by
    intro j
    simp only [p, paperSeparatedForward, rates.terminal_plus]
  have hterminalReverse : ∀ j,
      q (S.paperTailTerminal j) =
        (rates.chain j).summary.beta * y.core (S.fork j) := by
    intro j
    calc
      q (S.paperTailTerminal j) =
          rates.minus (S.paperTailTerminal j) *
            paperSourceProductMonomial P (S.paperTailTerminal j) y.core := rfl
      _ = (rates.chain j).summary.beta *
            paperSourceProductMonomial P (S.paperTailTerminal j) y.core := by
          rw [rates.terminal_minus j]
      _ = (rates.chain j).summary.beta * y.core (S.fork j) := by
          congr 1
          unfold paperSourceProductMonomial
          dsimp [P]
          classical
          rw [Finset.prod_eq_single (S.fork j)]
          · rw [sourceProductExponent_nonfork next weight back
              (S.paperTailTerminal_back j) (S.fork j)]
            rw [S.paperTailTerminal_next, hterminalUnit j]
            simp
          · intro b _ hb
            rw [sourceProductExponent_nonfork next weight back
              (S.paperTailTerminal_back j) b]
            rw [S.paperTailTerminal_next]
            simp [hb]
          · simp
  have hratioStat : ∀ i,
      (∑ r, sourceStoich next weight back i r *
        (rho r * p r - monomialRatio P rho r * q r)) -
        (∑ j, sourceStoich next weight back i (S.paperTailTerminal j) *
          (rho (S.paperTailTerminal j) * p (S.paperTailTerminal j) -
            monomialRatio P rho (S.paperTailTerminal j) *
              q (S.paperTailTerminal j))) +
        (∑ j, paperTailBoundaryContribution S i j (jL1 j) (jR1 j)) =
      rates.degrade i * (rho i * y.core i) := by
    intro i
    have hf : ∀ r, paperSeparatedForward rates x.core r = rho r * p r := by
      intro r
      simpa only [rho, p] using
        paperSeparatedForward_ratio rates x.core y.core hycore r
    have hr : ∀ r, paperSeparatedReverse rates x.core r =
        monomialRatio P rho r * q r := by
      intro r
      simpa only [P, rho, q] using
        paperSeparatedReverse_ratio rates x.core y.core hycore r
    have hs := hstat1 i
    simp_rw [hf, hr] at hs
    rw [hcoreRatio i] at hs
    exact hs
  let W : PaperTailExpandedTwoRoot S weight :=
    { tailDepth := rates.tailDepth
      tailDepth_pos := rates.tailDepth_pos
      tailCycleWeight := rates.tailCycleWeight
      tailCycleWeight_pos := rates.tailCycleWeight_pos
      tailMinimal := hminimal
      terminal_cycle_weight := rates.terminal_cycle_weight
      chain := rates.chain
      y := y.core
      rho := rho
      p := p
      q := q
      degrade := rates.degrade
      y_pos := hycore
      rho_pos := hrho
      p_pos := hp
      q_pos := hq
      degrade_pos := rates.degrade_pos
      z0 := y.tail
      z1 := x.tail
      jL0 := jL0
      jR0 := jR0
      jL1 := jL1
      jR1 := jR1
      chain0 := hchain0
      chain1 := hchain1
      terminal_forward := hterminalForward
      terminal_reverse := hterminalReverse
      base_stationary := hstat0
      ratio_stationary := hratioStat }
  exact
    { witness := W
      reconstruct := by
        intro hcore htail
        apply PaperSeparatedState.ext
        · funext i
          have hi := hcore i
          change (x.core i / y.core i) * y.core i = y.core i at hi
          calc
            x.core i = (x.core i / y.core i) * y.core i :=
              (div_mul_cancel₀ (x.core i) (ne_of_gt (hycore i))).symm
            _ = y.core i := hi
        · change y.tail = x.tail at htail
          exact htail.symm }

/-- Literal separated-source theorem.  Former public hypotheses
`PaperTailExpandedTwoRoot` and `hprevnext` are now constructed internally
from common rates, raw stationary equations, source-tail minimality, and the
cyclic order. -/
theorem paper_separated_typeII_l_states_equal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (rates : PaperSeparatedRates S weight)
    (hminimal : PaperReturnRestrictionsMinimal rates)
    (x y : PaperSeparatedState S weight rates)
    (hx : PositivePaperSeparatedState x)
    (hy : PositivePaperSeparatedState y)
    (hxs : IsPaperSeparatedStationary rates x)
    (hys : IsPaperSeparatedStationary rates y) : x = y := by
  let L := paperSeparatedTwoRoot_of_literal_states S weight rates hminimal
    x y hx hy hxs hys
  let W := L.witness
  obtain ⟨hcore, htail⟩ := S.paper_source_typeII_l_full_states_equal hl
    (S.prev_ne_next_of_three_le hl) weight hw W
  exact L.reconstruct hcore htail

end

end SourceCyclicNonemptyGapSystem

end TypeIIL
