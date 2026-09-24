import proofs.TypeIIL.PaperTailMinimality
import proofs.TypeII3.Network.ChainCompression

namespace TypeIIL

open TypeII3

/-!
Exact contraction of the unit return tails forced by paper source minimality.
The statement is deliberately at the stationary boundary interface: a whole
tail becomes one reversible edge, and its killed internal transport appears
only as nonnegative extra degradation at the two retained endpoints.
-/

/-- Contracting one unit return tail preserves both endpoint stationary
balances. -/
theorem paper_tail_boundary_balance_compress
    (q : UnitChain) (z : q.State)
    {X Y jL jR extL extR dL dR : ℝ}
    (hflux : ChainFlux q z X Y jL jR)
    (hleft : extL - jL - dL * X = 0)
    (hright : jR + extR - dR * Y = 0) :
    let jEff := q.summary.c * X - q.summary.beta * Y
    extL - jEff - (dL + q.summary.leakL) * X = 0 ∧
      jEff + extR - (dR + q.summary.leakR) * Y = 0 := by
  dsimp
  obtain ⟨hjL, hjR⟩ := chain_flux_compress q z hflux
  rw [hjL] at hleft
  rw [hjR] at hright
  constructor <;> linarith

/-- The effective endpoint degradations remain strictly positive. -/
theorem paper_tail_effective_degradation_pos
    (q : UnitChain) {dL dR : ℝ} (hdL : 0 < dL) (hdR : 0 < dR) :
    0 < dL + q.summary.leakL ∧ 0 < dR + q.summary.leakR := by
  exact ⟨add_pos_of_pos_of_nonneg hdL q.summary.leakL_nonneg,
    add_pos_of_pos_of_nonneg hdR q.summary.leakR_nonneg⟩

/-- All paper return tails contract simultaneously because their interiors
are disjoint.  No ordering or length case is used: the theorem is pointwise
over the fork family. -/
theorem paper_tail_family_boundary_balance_compress
    {l : ℕ} (q : Fin l → UnitChain)
    (z : ∀ j, (q j).State)
    (X Y jL jR extL extR dL dR : Fin l → ℝ)
    (hflux : ∀ j, ChainFlux (q j) (z j) (X j) (Y j) (jL j) (jR j))
    (hleft : ∀ j, extL j - jL j - dL j * X j = 0)
    (hright : ∀ j, jR j + extR j - dR j * Y j = 0) :
    ∀ j,
      let jEff := (q j).summary.c * X j - (q j).summary.beta * Y j
      extL j - jEff - (dL j + (q j).summary.leakL) * X j = 0 ∧
        jEff + extR j - (dR j + (q j).summary.leakR) * Y j = 0 := by
  intro j
  exact paper_tail_boundary_balance_compress (q j) (z j)
    (hflux j) (hleft j) (hright j)

/-- Once the contracted endpoint concentrations agree, every eliminated tail
concentration agrees.  This is the reconstruction half of the same
contraction principle. -/
theorem paper_tail_family_state_unique
    {l : ℕ} (q : Fin l → UnitChain)
    (z w : ∀ j, (q j).State)
    (X Y jLz jRz jLw jRw : Fin l → ℝ)
    (hz : ∀ j,
      ChainFlux (q j) (z j) (X j) (Y j) (jLz j) (jRz j))
    (hw : ∀ j,
      ChainFlux (q j) (w j) (X j) (Y j) (jLw j) (jRw j)) :
    z = w := by
  funext j
  exact chain_state_unique (q j) (z j) (w j) (hz j) (hw j)

end TypeIIL
