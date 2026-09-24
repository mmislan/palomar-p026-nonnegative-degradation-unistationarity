import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Topology.Order.DenselyOrdered

namespace MixedDegradation
open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Boundary uniqueness from local nondegeneracy and uniqueness for nearby
positive parameters. The two implicit branches agree on the same one-sided
parameter filter, so uniqueness of their limits identifies the boundary roots. -/
theorem boundary_uniqueness_of_nondegenerate
    (F : ℝ × E → E) (U : Set E) (hU : IsOpen U)
    (hinterior : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ x ∈ U, ∀ y ∈ U, F (ε, x) = 0 → F (ε, y) = 0 → x = y)
    (hregular : ∀ z ∈ U, F (0, z) = 0 →
      ∃ L : (ℝ × E) →L[ℝ] E,
        HasStrictFDerivAt F L (0, z) ∧
        (L.comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible)
    (x y : E) (hx : x ∈ U) (hy : y ∈ U)
    (hxzero : F (0, x) = 0) (hyzero : F (0, y) = 0) : x = y := by
  obtain ⟨Lx, hLx, hix⟩ := hregular x hx hxzero
  obtain ⟨Ly, hLy, hiy⟩ := hregular y hy hyzero
  let ψx := hLx.implicitFunctionOfProdDomain hix
  let ψy := hLy.implicitFunctionOfProdDomain hiy
  have htx : Tendsto ψx (𝓝 (0 : ℝ)) (𝓝 x) :=
    hLx.tendsto_implicitFunctionOfProdDomain hix
  have hty : Tendsto ψy (𝓝 (0 : ℝ)) (𝓝 y) :=
    hLy.tendsto_implicitFunctionOfProdDomain hiy
  have hUx : ∀ᶠ ε in 𝓝 (0 : ℝ), ψx ε ∈ U := htx (hU.mem_nhds hx)
  have hUy : ∀ᶠ ε in 𝓝 (0 : ℝ), ψy ε ∈ U := hty (hU.mem_nhds hy)
  have hFx : ∀ᶠ ε in 𝓝 (0 : ℝ), F (ε, ψx ε) = 0 := by
    simpa [ψx, hxzero] using hLx.eventually_apply_implicitFunctionOfProdDomain hix
  have hFy : ∀ᶠ ε in 𝓝 (0 : ℝ), F (ε, ψy ε) = 0 := by
    simpa [ψy, hyzero] using hLy.eventually_apply_implicitFunctionOfProdDomain hiy
  have heq : ψx =ᶠ[𝓝[>] (0 : ℝ)] ψy := by
    filter_upwards [hinterior, hUx.filter_mono nhdsWithin_le_nhds,
      hUy.filter_mono nhdsWithin_le_nhds, hFx.filter_mono nhdsWithin_le_nhds,
      hFy.filter_mono nhdsWithin_le_nhds] with ε huni hux huy hfx hfy
    exact huni (ψx ε) hux (ψy ε) huy hfx hfy
  exact tendsto_nhds_unique_of_eventuallyEq
    (htx.mono_left nhdsWithin_le_nhds) (hty.mono_left nhdsWithin_le_nhds) heq

end MixedDegradation
