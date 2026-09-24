import proofs.TypeIIL.SourceGapAdapter

namespace TypeIIL

open scoped BigOperators

/-- A square real matrix with trivial kernel solves every forcing equation.
This is the finite-dimensional existence half needed to define literal Schur
responses from the already proved source-gap kernel exclusion. -/
theorem matrix_solve_exists_of_kernel_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hker : ∀ x : ι → ℝ,
      (∀ i, ∑ j, M i j * x j = 0) → ∀ i, x i = 0)
    (b : ι → ℝ) :
    ∃ x : ι → ℝ, ∀ i, ∑ j, M i j * x j = b i := by
  have hinjective : Function.Injective M.mulVecLin := by
    intro x y hxy
    have hzero : ∀ i, ∑ j, M i j * (x - y) j = 0 := by
      intro i
      have hi := congrFun hxy i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at hi
      simp only [Pi.sub_apply]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      linarith
    have hxy0 := hker (x - y) hzero
    funext i
    have hi := hxy0 i
    simp only [Pi.sub_apply, sub_eq_zero] at hi
    exact hi
  have hsurjective : Function.Surjective M.mulVecLin :=
    LinearMap.injective_iff_surjective.mp hinjective
  rcases hsurjective b with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro i
  have hi := congrFun hx i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using hi

/-- Every literal positive source gap has a response to an arbitrary forcing.
Together with `restrictedCurrentMatrix_kernel_eq_zero`, this makes its Schur
responses genuine consequences of the source matrix rather than witnesses
that must be postulated. -/
theorem SourceGapEmbedding.restricted_response_exists
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (b : Fin (m + 1) → ℝ) :
    ∃ x : Fin (m + 1) → ℝ, ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = b i := by
  apply matrix_solve_exists_of_kernel_eq_zero
  intro x hx
  exact G.restrictedCurrentMatrix_kernel_eq_zero weight p q e rho
    hp hq he hrho hw x hx

/-- Literal source-gap responses to the same forcing are unique.  This is the
interface needed to identify independently constructed local Schur witnesses
with the responses used by the global kernel reconstruction. -/
theorem SourceGapEmbedding.restricted_response_unique
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (b x y : Fin (m + 1) → ℝ)
    (hx : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = b i)
    (hy : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    x = y := by
  have hzero : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * (x - y) j = 0 := by
    intro i
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hx i, hy i]
    ring
  have hz := G.restrictedCurrentMatrix_kernel_eq_zero weight p q e rho
    hp hq he hrho hw (x - y) hzero
  funext i
  have hi := hz i
  simpa only [Pi.sub_apply, sub_eq_zero] using hi

end TypeIIL
