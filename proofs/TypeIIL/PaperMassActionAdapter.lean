import proofs.TypeIIL.SourceCurrentMatrix
import proofs.TypeII3.Network.TwoRootKernel

namespace TypeIIL

open TypeII3
open scoped BigOperators

/-- Literal positive rates for a reversible fully open paper source network. -/
structure PaperSourceRates (n : ℕ) where
  plus : Fin n → ℝ
  minus : Fin n → ℝ
  degrade : Fin n → ℝ
  plus_pos : ∀ r, 0 < plus r
  minus_pos : ∀ r, 0 < minus r
  degrade_pos : ∀ i, 0 < degrade i

abbrev PaperSourceState (n : ℕ) := Fin n → ℝ

def PositivePaperSourceState {n : ℕ} (x : PaperSourceState n) : Prop :=
  ∀ i, 0 < x i

/-- Every paper reaction consumes its same-index source species. -/
def paperSourceReactantMonomial {n : ℕ}
    (r : Fin n) (x : PaperSourceState n) : ℝ := x r

/-- Literal product-complex mass-action monomial. -/
def paperSourceProductMonomial {n : ℕ}
    (P : Fin n → Fin n → ℕ) (r : Fin n)
    (x : PaperSourceState n) : ℝ :=
  ∏ i, x i ^ P i r

def IsPaperSourceStationary {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rates : PaperSourceRates n)
    (x : PaperSourceState n) : Prop :=
  FluxStationary (sourceStoich next weight back)
    paperSourceReactantMonomial
    (paperSourceProductMonomial (sourceProductExponent next weight back))
    rates.plus rates.minus rates.degrade id x

theorem paperSourceProductMonomial_pos
    {n : ℕ} (P : Fin n → Fin n → ℕ)
    {x : PaperSourceState n} (hx : PositivePaperSourceState x) (r : Fin n) :
    0 < paperSourceProductMonomial P r x := by
  unfold paperSourceProductMonomial
  exact Finset.prod_pos fun i _ => pow_pos (hx i) _

/-- Product monomials transform by the exact monomial ratio between two
positive concentration states. -/
theorem paperSourceProductMonomial_ratio
    {n : ℕ} (P : Fin n → Fin n → ℕ)
    {x y : PaperSourceState n} (hy : PositivePaperSourceState y)
    (r : Fin n) :
    paperSourceProductMonomial P r x =
      monomialRatio P (fun i => x i / y i) r *
        paperSourceProductMonomial P r y := by
  have hxy : ∀ i, x i = (x i / y i) * y i := by
    intro i
    exact (div_mul_cancel₀ (x i) (ne_of_gt (hy i))).symm
  unfold paperSourceProductMonomial monomialRatio
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [hxy i, mul_pow]

/-- Literal two-stationary-state kinetics generate exactly the positive
current data consumed by the ordered-secant source theorem. -/
theorem paper_two_stationary_to_current_data
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (rates : PaperSourceRates n)
    (x y : PaperSourceState n)
    (hx : PositivePaperSourceState x) (hy : PositivePaperSourceState y)
    (hxs : IsPaperSourceStationary next weight back rates x)
    (hys : IsPaperSourceStationary next weight back rates y) :
    let P := sourceProductExponent next weight back
    let p : Fin n → ℝ := fun r => rates.plus r * y r
    let q : Fin n → ℝ := fun r =>
      rates.minus r * paperSourceProductMonomial P r y
    let e : Fin n → ℝ := fun i => rates.degrade i * y i
    let rho : Fin n → ℝ := fun i => x i / y i
    (∀ r, 0 < p r) ∧ (∀ r, 0 < q r) ∧ (∀ i, 0 < e i) ∧
      (∀ i, 0 < rho i) ∧
      BaseFluxBalance (sourceStoich next weight back) p q e ∧
      RatioFluxBalance (sourceStoich next weight back)
        rho (monomialRatio P rho) rho p q e := by
  dsimp
  let P := sourceProductExponent next weight back
  let rho : Fin n → ℝ := fun i => x i / y i
  have hrho : ∀ i, 0 < rho i := fun i => div_pos (hx i) (hy i)
  have hreactantX : ∀ r,
      paperSourceReactantMonomial r x =
        rho r * paperSourceReactantMonomial r y := by
    intro r
    exact (div_mul_cancel₀ (x r) (ne_of_gt (hy r))).symm
  have hproductX : ∀ r,
      paperSourceProductMonomial P r x =
        monomialRatio P rho r * paperSourceProductMonomial P r y := by
    intro r
    exact paperSourceProductMonomial_ratio P hy r
  have hkernel :=
    (two_stationary_iff_flux_kernel
      (sourceStoich next weight back)
      paperSourceReactantMonomial (paperSourceProductMonomial P)
      rates.plus rates.minus rates.degrade id x y
      rho (monomialRatio P rho) rho
      hreactantX hproductX (fun i => hreactantX i)).mp ⟨hys, hxs⟩
  have hpos := positive_base_fluxes
    paperSourceReactantMonomial (paperSourceProductMonomial P)
    rates.plus rates.minus rates.degrade id y
    rates.plus_pos rates.minus_pos (fun r => hy r)
    (paperSourceProductMonomial_pos P hy) rates.degrade_pos hy
  exact ⟨hpos.1, hpos.2.1, hpos.2.2, hrho, hkernel.1, hkernel.2⟩

end TypeIIL
