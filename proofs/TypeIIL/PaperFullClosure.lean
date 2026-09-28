module

public import proofs.TypeIIL.SourceBackFirstWeakClosure
public import proofs.TypeIIL.PaperMassActionAdapter
public import proofs.TypeIIL.PaperTailContraction

@[expose] public section

namespace TypeIIL

open TypeII3
open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

noncomputable section

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- The retained left endpoint of the paper return tail ending at fork `j`.
In the terminal-back contraction this is the last nonfork source before that
fork. -/
def paperTailTerminal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (j : Fin l) :
    Fin n :=
  (S.gap (S.step.symm j)).idx
    (Fin.last (S.gapLength (S.step.symm j)))

set_option warning.simp.varHead false in
@[simp] theorem paperTailTerminal_back
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (j : Fin l) :
    back (S.paperTailTerminal j) = none := by
  exact (S.gap (S.step.symm j)).nonfork _

@[simp] theorem paperTailTerminal_next
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (j : Fin l) :
    next (S.paperTailTerminal j) = S.fork j := by
  simpa [paperTailTerminal] using
    (S.wrap (S.step.symm j)).pre.terminal_next

theorem paperTailTerminal_ne_fork
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (j : Fin l) :
    S.paperTailTerminal j ≠ S.fork j := by
  exact S.gap_point_ne_fork j (S.step.symm j) _

/-- A unit terminal column is precisely the boundary incidence of the
corresponding return tail. -/
theorem sourceStoich_paperTailTerminal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (j : Fin l)
    (hunit : weight (S.paperTailTerminal j) = 1) (i : Fin n) :
    sourceStoich next weight back i (S.paperTailTerminal j) =
      (if i = S.fork j then 1 else 0) -
        (if i = S.paperTailTerminal j then 1 else 0) := by
  unfold sourceStoich
  rw [sourceProductExponent_nonfork next weight back
    (S.paperTailTerminal_back j)]
  rw [S.paperTailTerminal_next, hunit]
  push_cast
  ring

/-- The product ratio of a unit paper-tail terminal reaction is the ratio at
the fork endpoint. -/
theorem monomialRatio_paperTailTerminal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rho : Fin n → ℝ) (j : Fin l)
    (hunit : weight (S.paperTailTerminal j) = 1) :
    monomialRatio (sourceProductExponent next weight back) rho
        (S.paperTailTerminal j) = rho (S.fork j) := by
  rw [monomialRatio_source_nonfork next weight back rho
    (S.paperTailTerminal_back j)]
  rw [S.paperTailTerminal_next, hunit]
  simp

/-- Signed contribution of one uncontracted return tail to a retained core
species: current leaves its terminal endpoint and enters its fork endpoint. -/
def paperTailBoundaryContribution
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (i : Fin n) (j : Fin l) (jL jR : ℝ) : ℝ :=
  (if i = S.paperTailTerminal j then -jL else 0) +
    (if i = S.fork j then jR else 0)

/-- Endpoint leakage contributed by the passive two-port obtained by
contracting one return tail. -/
noncomputable def paperTailEndpointLeak
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (q : UnitChain) (y : Fin n → ℝ) (i : Fin n) (j : Fin l) : ℝ :=
  (if i = S.paperTailTerminal j then q.summary.leakL * y i else 0) +
    (if i = S.fork j then q.summary.leakR * y i else 0)

/-- Generating contraction identity for a literal return tail.  Its entire
boundary action is the unit terminal reaction column, minus nonnegative
endpoint leakage. -/
theorem paperTailBoundaryContribution_compress
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (q : UnitChain) (z : q.State)
    (y : Fin n → ℝ) (j : Fin l) {jL jR : ℝ}
    (hunit : weight (S.paperTailTerminal j) = 1)
    (hflux : ChainFlux q z (y (S.paperTailTerminal j))
      (y (S.fork j)) jL jR) (i : Fin n) :
    paperTailBoundaryContribution S i j jL jR =
      sourceStoich next weight back i (S.paperTailTerminal j) *
          (q.summary.c * y (S.paperTailTerminal j) -
            q.summary.beta * y (S.fork j)) -
        paperTailEndpointLeak S q y i j := by
  obtain ⟨hL, hR⟩ := chain_flux_compress q z hflux
  rw [S.sourceStoich_paperTailTerminal weight j hunit i]
  have hne := S.paperTailTerminal_ne_fork j
  unfold paperTailBoundaryContribution paperTailEndpointLeak
  by_cases hiT : i = S.paperTailTerminal j
  · subst i
    simp [hne]
    linarith
  · by_cases hiF : i = S.fork j
    · subst i
      simp [hiT]
      linarith
    · simp [hiT, hiF]

theorem paperTailEndpointLeak_ratio_mul
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (q : UnitChain) (rho y : Fin n → ℝ) (i : Fin n) (j : Fin l) :
    paperTailEndpointLeak S q (fun k => rho k * y k) i j =
      rho i * paperTailEndpointLeak S q y i j := by
  have hne := S.paperTailTerminal_ne_fork j
  unfold paperTailEndpointLeak
  by_cases hiT : i = S.paperTailTerminal j <;>
    by_cases hiF : i = S.fork j <;>
      simp [hiT, hiF, hne, hne.symm] <;> ring

/-- Exact two-root current presentation of the literal paper model before
return-tail contraction.  The core sums omit the terminal reactions and the
four boundary-current families insert the actual unit return chains.  Thus
the stationary equations below are the uncontracted equations, not an
assumption that the contracted model is stationary. -/
structure PaperTailExpandedTwoRoot
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) where
  /-- The return-tail subcycle has `tailDepth + 1` reactions. -/
  tailDepth : Fin l → ℕ
  tailDepth_pos : ∀ j, 1 ≤ tailDepth j
  tailCycleWeight : ∀ j, Fin (tailDepth j + 1) → ℕ
  tailCycleWeight_pos : ∀ j k, 0 < tailCycleWeight j k
  tailMinimal : ∀ j,
    EveryPaperTailRotationPassesMinimality (tailCycleWeight j)
  terminal_cycle_weight : ∀ j,
    weight (S.paperTailTerminal j) = tailCycleWeight j 0
  chain : Fin l → UnitChain
  y : Fin n → ℝ
  rho : Fin n → ℝ
  p : Fin n → ℝ
  q : Fin n → ℝ
  degrade : Fin n → ℝ
  y_pos : ∀ i, 0 < y i
  rho_pos : ∀ i, 0 < rho i
  p_pos : ∀ r, 0 < p r
  q_pos : ∀ r, 0 < q r
  degrade_pos : ∀ i, 0 < degrade i
  z0 : ∀ j, (chain j).State
  z1 : ∀ j, (chain j).State
  jL0 : Fin l → ℝ
  jR0 : Fin l → ℝ
  jL1 : Fin l → ℝ
  jR1 : Fin l → ℝ
  chain0 : ∀ j, ChainFlux (chain j) (z0 j)
    (y (S.paperTailTerminal j)) (y (S.fork j)) (jL0 j) (jR0 j)
  chain1 : ∀ j, ChainFlux (chain j) (z1 j)
    (rho (S.paperTailTerminal j) * y (S.paperTailTerminal j))
    (rho (S.fork j) * y (S.fork j)) (jL1 j) (jR1 j)
  /-- Common rates identify the contracted forward and reverse terminal
  currents with the two-port transfer coefficients. -/
  terminal_forward : ∀ j,
    p (S.paperTailTerminal j) =
      (chain j).summary.c * y (S.paperTailTerminal j)
  terminal_reverse : ∀ j,
    q (S.paperTailTerminal j) =
      (chain j).summary.beta * y (S.fork j)
  base_stationary : ∀ i,
    (∑ r, sourceStoich next weight back i r * (p r - q r)) -
        (∑ j, sourceStoich next weight back i (S.paperTailTerminal j) *
          (p (S.paperTailTerminal j) - q (S.paperTailTerminal j))) +
        (∑ j, paperTailBoundaryContribution S i j (jL0 j) (jR0 j)) =
      degrade i * y i
  ratio_stationary : ∀ i,
    (∑ r, sourceStoich next weight back i r *
      (rho r * p r -
        monomialRatio (sourceProductExponent next weight back) rho r * q r)) -
        (∑ j, sourceStoich next weight back i (S.paperTailTerminal j) *
          (rho (S.paperTailTerminal j) * p (S.paperTailTerminal j) -
            monomialRatio (sourceProductExponent next weight back) rho
              (S.paperTailTerminal j) * q (S.paperTailTerminal j))) +
        (∑ j, paperTailBoundaryContribution S i j (jL1 j) (jR1 j)) =
      degrade i * (rho i * y i)

/-- Full literal paper Type `II_l` closure.  Source minimality first forces
every return-tail multiplier to one.  Simultaneous passive-chain contraction
then produces the terminal-back positive-current system, whose ratio kernel
is trivial; unique chain reconstruction recovers all eliminated species. -/
theorem paper_source_typeII_l_full_unistationarity
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (W : PaperTailExpandedTwoRoot S weight) :
    (∀ i, W.rho i = 1) ∧ W.z0 = W.z1 := by
  have hterminalUnit : ∀ j, weight (S.paperTailTerminal j) = 1 := by
    intro j
    have hall := paper_tail_all_weights_eq_one_of_minimality
      (W.tailDepth_pos j) (W.tailCycleWeight j)
      (W.tailCycleWeight_pos j) (W.tailMinimal j)
    calc
      weight (S.paperTailTerminal j) = W.tailCycleWeight j 0 :=
        W.terminal_cycle_weight j
      _ = 1 := hall 0
  have hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1 := by
    intro a
    have ht := hterminalUnit (S.step a)
    change weight ((S.gap (S.step.symm (S.step a))).idx
      (Fin.last (S.gapLength (S.step.symm (S.step a))))) = 1 at ht
    rw [S.step.symm_apply_apply] at ht
    exact ht
  let e : Fin n → ℝ := fun i =>
    W.degrade i * W.y i +
      ∑ j, paperTailEndpointLeak S (W.chain j) W.y i j
  have hleakNonneg : ∀ i j,
      0 ≤ paperTailEndpointLeak S (W.chain j) W.y i j := by
    intro i j
    unfold paperTailEndpointLeak
    apply add_nonneg
    · split_ifs
      · exact mul_nonneg (W.chain j).summary.leakL_nonneg
          (le_of_lt (W.y_pos i))
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (W.chain j).summary.leakR_nonneg
          (le_of_lt (W.y_pos i))
      · exact le_rfl
  have he : ∀ i, 0 < e i := by
    intro i
    exact add_pos_of_pos_of_nonneg
      (mul_pos (W.degrade_pos i) (W.y_pos i))
      (Finset.sum_nonneg fun j _ => hleakNonneg i j)
  have hbase : BaseFluxBalance (sourceStoich next weight back) W.p W.q e := by
    intro i
    have hboundary :
        (∑ j, paperTailBoundaryContribution S i j (W.jL0 j) (W.jR0 j)) =
          ∑ j, (sourceStoich next weight back i (S.paperTailTerminal j) *
              (W.p (S.paperTailTerminal j) -
                W.q (S.paperTailTerminal j)) -
            paperTailEndpointLeak S (W.chain j) W.y i j) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        paperTailBoundaryContribution S i j (W.jL0 j) (W.jR0 j) =
            sourceStoich next weight back i (S.paperTailTerminal j) *
                ((W.chain j).summary.c * W.y (S.paperTailTerminal j) -
                  (W.chain j).summary.beta * W.y (S.fork j)) -
              paperTailEndpointLeak S (W.chain j) W.y i j :=
          S.paperTailBoundaryContribution_compress weight (W.chain j)
            (W.z0 j) W.y j (hterminalUnit j) (W.chain0 j) i
        _ = sourceStoich next weight back i (S.paperTailTerminal j) *
              (W.p (S.paperTailTerminal j) -
                W.q (S.paperTailTerminal j)) -
            paperTailEndpointLeak S (W.chain j) W.y i j := by
          rw [W.terminal_forward j, W.terminal_reverse j]
    have hb := W.base_stationary i
    rw [hboundary, Finset.sum_sub_distrib] at hb
    dsimp [BaseFluxBalance, e]
    linear_combination hb
  have hratio : RatioFluxBalance (sourceStoich next weight back)
      W.rho (monomialRatio (sourceProductExponent next weight back) W.rho)
      W.rho W.p W.q e := by
    intro i
    have hterminalCurrent : ∀ j,
        (W.chain j).summary.c *
              (W.rho (S.paperTailTerminal j) *
                W.y (S.paperTailTerminal j)) -
            (W.chain j).summary.beta *
              (W.rho (S.fork j) * W.y (S.fork j)) =
          W.rho (S.paperTailTerminal j) *
              W.p (S.paperTailTerminal j) -
            monomialRatio (sourceProductExponent next weight back) W.rho
                (S.paperTailTerminal j) *
              W.q (S.paperTailTerminal j) := by
      intro j
      rw [S.monomialRatio_paperTailTerminal weight W.rho j
        (hterminalUnit j)]
      rw [W.terminal_forward j, W.terminal_reverse j]
      ring
    have hboundary :
        (∑ j, paperTailBoundaryContribution S i j (W.jL1 j) (W.jR1 j)) =
          ∑ j, (sourceStoich next weight back i (S.paperTailTerminal j) *
              (W.rho (S.paperTailTerminal j) *
                  W.p (S.paperTailTerminal j) -
                monomialRatio (sourceProductExponent next weight back) W.rho
                    (S.paperTailTerminal j) *
                  W.q (S.paperTailTerminal j)) -
            paperTailEndpointLeak S (W.chain j)
              (fun k => W.rho k * W.y k) i j) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        paperTailBoundaryContribution S i j (W.jL1 j) (W.jR1 j) =
            sourceStoich next weight back i (S.paperTailTerminal j) *
                ((W.chain j).summary.c *
                    (W.rho (S.paperTailTerminal j) *
                      W.y (S.paperTailTerminal j)) -
                  (W.chain j).summary.beta *
                    (W.rho (S.fork j) * W.y (S.fork j))) -
              paperTailEndpointLeak S (W.chain j)
                (fun k => W.rho k * W.y k) i j :=
          S.paperTailBoundaryContribution_compress weight (W.chain j)
            (W.z1 j) (fun k => W.rho k * W.y k) j
            (hterminalUnit j) (W.chain1 j) i
        _ = sourceStoich next weight back i (S.paperTailTerminal j) *
              (W.rho (S.paperTailTerminal j) *
                  W.p (S.paperTailTerminal j) -
                monomialRatio (sourceProductExponent next weight back) W.rho
                    (S.paperTailTerminal j) *
                  W.q (S.paperTailTerminal j)) -
            paperTailEndpointLeak S (W.chain j)
              (fun k => W.rho k * W.y k) i j := by
          rw [hterminalCurrent j]
    have hleakScale :
        (∑ j, paperTailEndpointLeak S (W.chain j)
            (fun k => W.rho k * W.y k) i j) =
          W.rho i *
            ∑ j, paperTailEndpointLeak S (W.chain j) W.y i j := by
      calc
        (∑ j, paperTailEndpointLeak S (W.chain j)
            (fun k => W.rho k * W.y k) i j) =
            ∑ j, W.rho i *
              paperTailEndpointLeak S (W.chain j) W.y i j := by
          apply Finset.sum_congr rfl
          intro j _
          exact S.paperTailEndpointLeak_ratio_mul
            (W.chain j) W.rho W.y i j
        _ = W.rho i *
            ∑ j, paperTailEndpointLeak S (W.chain j) W.y i j := by
          rw [Finset.mul_sum]
    have hr := W.ratio_stationary i
    rw [hboundary, Finset.sum_sub_distrib, hleakScale] at hr
    dsimp [RatioFluxBalance, e]
    linear_combination hr
  have hall := S.ratios_eq_one_of_backFirst_weak_gap_generated
    hl hprevnext weight W.p W.q e W.rho W.p_pos W.q_pos he W.rho_pos
      hw hunit hbase hratio
  refine ⟨hall, ?_⟩
  funext j
  apply chain_state_unique (W.chain j) (W.z0 j) (W.z1 j) (W.chain0 j)
  simpa [hall] using W.chain1 j

/-- Concentration form of the full theorem: the two positive stationary
states agree on every retained paper species and on every return-tail
internal species. -/
theorem paper_source_typeII_l_full_states_equal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (W : PaperTailExpandedTwoRoot S weight) :
    (∀ i, W.rho i * W.y i = W.y i) ∧ W.z0 = W.z1 := by
  obtain ⟨hall, htail⟩ :=
    S.paper_source_typeII_l_full_unistationarity hl hprevnext weight hw W
  exact ⟨fun i => by rw [hall i, one_mul], htail⟩

/-- Concentration-level paper theorem for the terminal-back source normal
form.  This is the nonlinear docking theorem: two literal positive
mass-action stationary states are equal for every `l ≥ 3` and every
paper-legal gap length. -/
theorem paper_source_typeII_l_weak_gap_unistationarity
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (rates : PaperSourceRates n)
    (x y : PaperSourceState n)
    (hx : PositivePaperSourceState x) (hy : PositivePaperSourceState y)
    (hxs : IsPaperSourceStationary next weight back rates x)
    (hys : IsPaperSourceStationary next weight back rates y) :
    x = y := by
  let P := sourceProductExponent next weight back
  let p : Fin n → ℝ := fun r => rates.plus r * y r
  let q : Fin n → ℝ := fun r =>
    rates.minus r * paperSourceProductMonomial P r y
  let e : Fin n → ℝ := fun i => rates.degrade i * y i
  let rho : Fin n → ℝ := fun i => x i / y i
  obtain ⟨hp, hq, he, hrho, hbase, hratio⟩ :=
    paper_two_stationary_to_current_data next weight back rates x y
      hx hy hxs hys
  have hall := S.ratios_eq_one_of_backFirst_weak_gap_generated
    hl hprevnext weight p q e rho hp hq he hrho hw hunit hbase hratio
  funext i
  have hi : x i / y i = 1 := by simpa [rho] using hall i
  calc
    x i = (x i / y i) * y i :=
      (div_mul_cancel₀ (x i) (ne_of_gt (hy i))).symm
    _ = y i := by rw [hi]; ring

end

end SourceCyclicNonemptyGapSystem

end TypeIIL
