import Mathlib
import proofs.TypeII3.Network.WeightedCounterexample

namespace TypeII3

/-- Exact positive-production definition used by the source's stoichiometric
autocatalysis test. -/
def StoichiometricallyAutocatalytic {n r : ℕ}
    (S : Fin n → Fin r → ℝ) : Prop :=
  ∃ v : Fin r → ℝ, (∀ j, 0 < v j) ∧
    ∀ i, 0 < ∑ j, S i j * v j

/-- The proper `{X₁,X₂}` restriction of the nonminimal weighted benchmark,
in reaction order `X₁ → 2X₂`, `X₂ → X₁` after chemostatting `X₃`. -/
def weightedCounterexampleRestriction12 : Fin 2 → Fin 2 → ℝ := ![
  ![-1, 1],
  ![ 2,-1]]

def weightedCounterexampleRestrictionWitness : Fin 2 → ℝ := ![2, 3]

/-- The proper restriction has the exact positive-production witness
`S₁₂ (2,3)ᵀ = (1,1)ᵀ`. -/
theorem weighted_counterexample_restriction12_autocatalytic :
    StoichiometricallyAutocatalytic weightedCounterexampleRestriction12 := by
  refine ⟨weightedCounterexampleRestrictionWitness, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [weightedCounterexampleRestrictionWitness]
  · intro i
    fin_cases i <;>
      norm_num [weightedCounterexampleRestriction12,
        weightedCounterexampleRestrictionWitness, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- Regression predicate required before treating the weighted benchmark as a
source-minimal core.  It fails because the displayed proper restriction is
autocatalytic. -/
def WeightedCounterexamplePassesMinimalityRegression : Prop :=
  ¬ StoichiometricallyAutocatalytic weightedCounterexampleRestriction12

theorem weighted_counterexample_not_source_minimal :
    ¬ WeightedCounterexamplePassesMinimalityRegression := by
  intro h
  exact h weighted_counterexample_restriction12_autocatalytic

end TypeII3
