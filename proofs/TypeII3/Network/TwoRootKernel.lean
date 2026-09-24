import Mathlib

namespace TypeII3

section CommonRateKernel

variable {Species Reaction State : Type*}
variable [Fintype Reaction]

/-- A mass-action system written only in terms of its reactant and product
monomials.  This deliberately does not assume that net reaction currents are
positive. -/
def FluxStationary
    (N : Species → Reaction → ℝ)
    (reactant product : Reaction → State → ℝ)
    (kplus kminus : Reaction → ℝ) (degradation : Species → ℝ)
    (concentration : State → Species → ℝ) (x : State) : Prop :=
  ∀ i, ∑ r, N i r *
      (kplus r * reactant r x - kminus r * product r x) =
    degradation i * concentration x i

/-- The first block of the common-rate two-root positive-kernel system. -/
def BaseFluxBalance
    (N : Species → Reaction → ℝ)
    (p q : Reaction → ℝ) (e : Species → ℝ) : Prop :=
  ∀ i, ∑ r, N i r * (p r - q r) = e i

/-- The second block of the common-rate two-root positive-kernel system. -/
def RatioFluxBalance
    (N : Species → Reaction → ℝ)
    (alpha beta : Reaction → ℝ) (rho : Species → ℝ)
    (p q : Reaction → ℝ) (e : Species → ℝ) : Prop :=
  ∀ i, ∑ r, N i r * (alpha r * p r - beta r * q r) = rho i * e i

/-- Exact common-rate two-root equivalence.  The hypotheses say that `alpha`,
`beta`, and `rho` are respectively the reactant-complex, product-complex, and
species ratios between `x` and `y`. -/
theorem two_stationary_iff_flux_kernel
    (N : Species → Reaction → ℝ)
    (reactant product : Reaction → State → ℝ)
    (kplus kminus : Reaction → ℝ) (degradation : Species → ℝ)
    (concentration : State → Species → ℝ) (x y : State)
    (alpha beta : Reaction → ℝ) (rho : Species → ℝ)
    (halpha : ∀ r, reactant r x = alpha r * reactant r y)
    (hbeta : ∀ r, product r x = beta r * product r y)
    (hrho : ∀ i, concentration x i = rho i * concentration y i) :
    (FluxStationary N reactant product kplus kminus degradation concentration y ∧
      FluxStationary N reactant product kplus kminus degradation concentration x) ↔
    (BaseFluxBalance N
        (fun r => kplus r * reactant r y)
        (fun r => kminus r * product r y)
        (fun i => degradation i * concentration y i) ∧
      RatioFluxBalance N alpha beta rho
        (fun r => kplus r * reactant r y)
        (fun r => kminus r * product r y)
        (fun i => degradation i * concentration y i)) := by
  constructor
  · rintro ⟨hy, hx⟩
    constructor
    · intro i
      simpa [FluxStationary, BaseFluxBalance] using hy i
    · intro i
      have hxi := hx i
      simp only [halpha, hbeta, hrho] at hxi
      simpa [RatioFluxBalance, mul_assoc, mul_left_comm, mul_comm] using hxi
  · rintro ⟨hy, hx⟩
    constructor
    · intro i
      simpa [FluxStationary, BaseFluxBalance] using hy i
    · intro i
      have hxi := hx i
      simp only [halpha, hbeta, hrho]
      simpa [RatioFluxBalance, mul_assoc, mul_left_comm, mul_comm] using hxi

omit [Fintype Reaction] in
theorem positive_base_fluxes
    (reactant product : Reaction → State → ℝ)
    (kplus kminus : Reaction → ℝ) (degradation : Species → ℝ)
    (concentration : State → Species → ℝ) (y : State)
    (hkplus : ∀ r, 0 < kplus r) (hkminus : ∀ r, 0 < kminus r)
    (hreactant : ∀ r, 0 < reactant r y) (hproduct : ∀ r, 0 < product r y)
    (hdegradation : ∀ i, 0 < degradation i)
    (hconcentration : ∀ i, 0 < concentration y i) :
    (∀ r, 0 < kplus r * reactant r y) ∧
    (∀ r, 0 < kminus r * product r y) ∧
    (∀ i, 0 < degradation i * concentration y i) := by
  exact ⟨fun r => mul_pos (hkplus r) (hreactant r),
    fun r => mul_pos (hkminus r) (hproduct r),
    fun i => mul_pos (hdegradation i) (hconcentration i)⟩

omit [Fintype Reaction] in
/-- Positive one-way flows reconstruct positive common rate constants at any
positive reference state. -/
theorem reconstructed_rates_positive
    (reactant product : Reaction → State → ℝ)
    (concentration : State → Species → ℝ) (y : State)
    (p q : Reaction → ℝ) (e : Species → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r) (he : ∀ i, 0 < e i)
    (hreactant : ∀ r, 0 < reactant r y) (hproduct : ∀ r, 0 < product r y)
    (hconcentration : ∀ i, 0 < concentration y i) :
    (∀ r, 0 < p r / reactant r y) ∧
    (∀ r, 0 < q r / product r y) ∧
    (∀ i, 0 < e i / concentration y i) := by
  exact ⟨fun r => div_pos (hp r) (hreactant r),
    fun r => div_pos (hq r) (hproduct r),
    fun i => div_pos (he i) (hconcentration i)⟩

omit [Fintype Reaction] in
theorem reconstructed_forward_flux
    (reactant : Reaction → State → ℝ) (y : State) (p : Reaction → ℝ)
    (hreactant : ∀ r, 0 < reactant r y) :
    ∀ r, (p r / reactant r y) * reactant r y = p r := by
  intro r
  exact div_mul_cancel₀ (p r) (ne_of_gt (hreactant r))

omit [Fintype Reaction] in
theorem reconstructed_reverse_flux
    (product : Reaction → State → ℝ) (y : State) (q : Reaction → ℝ)
    (hproduct : ∀ r, 0 < product r y) :
    ∀ r, (q r / product r y) * product r y = q r := by
  intro r
  exact div_mul_cancel₀ (q r) (ne_of_gt (hproduct r))

omit [Fintype Reaction] in
theorem reconstructed_degradation_flux
    (concentration : State → Species → ℝ) (y : State) (e : Species → ℝ)
    (hconcentration : ∀ i, 0 < concentration y i) :
    ∀ i, (e i / concentration y i) * concentration y i = e i := by
  intro i
  exact div_mul_cancel₀ (e i) (ne_of_gt (hconcentration i))

/-- Exact converse to the common-rate two-root reduction.  Positive kernel
data, together with the displayed complex/species ratio identities, reconstruct
strictly positive common rates and make both supplied states stationary. -/
theorem positive_flux_kernel_reconstructs_common_rates
    (N : Species → Reaction → ℝ)
    (reactant product : Reaction → State → ℝ)
    (concentration : State → Species → ℝ) (x y : State)
    (alpha beta : Reaction → ℝ) (rho : Species → ℝ)
    (p q : Reaction → ℝ) (e : Species → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r) (he : ∀ i, 0 < e i)
    (hreactant : ∀ r, 0 < reactant r y)
    (hproduct : ∀ r, 0 < product r y)
    (hconcentration : ∀ i, 0 < concentration y i)
    (halpha : ∀ r, reactant r x = alpha r * reactant r y)
    (hbeta : ∀ r, product r x = beta r * product r y)
    (hrho : ∀ i, concentration x i = rho i * concentration y i)
    (hB : BaseFluxBalance N p q e)
    (hR : RatioFluxBalance N alpha beta rho p q e) :
    ∃ kplus kminus : Reaction → ℝ, ∃ degradation : Species → ℝ,
      (∀ r, 0 < kplus r) ∧ (∀ r, 0 < kminus r) ∧
      (∀ i, 0 < degradation i) ∧
      FluxStationary N reactant product kplus kminus degradation concentration y ∧
      FluxStationary N reactant product kplus kminus degradation concentration x := by
  let kplus : Reaction → ℝ := fun r => p r / reactant r y
  let kminus : Reaction → ℝ := fun r => q r / product r y
  let degradation : Species → ℝ := fun i => e i / concentration y i
  have hpos := reconstructed_rates_positive reactant product concentration y p q e
    hp hq he hreactant hproduct hconcentration
  have hpf := reconstructed_forward_flux reactant y p hreactant
  have hqf := reconstructed_reverse_flux product y q hproduct
  have hef := reconstructed_degradation_flux concentration y e hconcentration
  have hkernel :
      BaseFluxBalance N
          (fun r => kplus r * reactant r y)
          (fun r => kminus r * product r y)
          (fun i => degradation i * concentration y i) ∧
        RatioFluxBalance N alpha beta rho
          (fun r => kplus r * reactant r y)
          (fun r => kminus r * product r y)
          (fun i => degradation i * concentration y i) := by
    constructor
    · intro i
      simpa [kplus, kminus, degradation, hpf, hqf, hef] using hB i
    · intro i
      simpa [kplus, kminus, degradation, hpf, hqf, hef] using hR i
  have hstat := (two_stationary_iff_flux_kernel N reactant product
    kplus kminus degradation concentration x y alpha beta rho
    halpha hbeta hrho).mpr hkernel
  exact ⟨kplus, kminus, degradation, hpos.1, hpos.2.1, hpos.2.2,
    hstat.1, hstat.2⟩

end CommonRateKernel

end TypeII3
