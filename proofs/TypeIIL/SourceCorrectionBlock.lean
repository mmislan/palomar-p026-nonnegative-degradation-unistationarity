import proofs.TypeIIL.MMatrixGreen

namespace TypeIIL

/-- Algebraic two-node Green calculation.  The boundary row has one positive
coefficient `h*s` followed by the negative coefficient `-(g+h)`.  The two
displayed transport inequalities are exactly what makes its product with the
positive tridiagonal Green kernel entrywise nonpositive. -/
theorem two_node_mixed_boundary_correction_nonpos
    {d₁ d₂ a c h g s det : ℝ}
    (hdet : 0 < det)
    (hleft : h * s * d₂ ≤ (g + h) * a)
    (hright : h * s * c ≤ (g + h) * d₁) :
    (h * s * d₂ - (g + h) * a) / det ≤ 0 ∧
      (h * s * c - (g + h) * d₁) / det ≤ 0 := by
  constructor
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hleft) (le_of_lt hdet)
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hright) (le_of_lt hdet)

/-- Source-equilibrium inequality at the first genuinely weighted two-node
block.  Here `J₂=e₃+J₃` and `J₃=e₄+e₅`; after clearing denominators the gap is
`J₃ * (q₂ + e₃ + q₃ + J₃)`.  This is the exact cancellation found by the
symbolic `(2,1,1)` experiment when the terminal edge and back branch have
unit stoichiometry. -/
theorem source_two_node_left_transport
    {e₂ e₃ e₄ e₅ q₂ q₃ : ℝ}
    (he₂ : 0 < e₂) (he₃ : 0 < e₃)
    (he₄ : 0 < e₄) (he₅ : 0 < e₅)
    (hq₂ : 0 < q₂) (hq₃ : 0 < q₃) :
    let J₃ := e₄ + e₅
    let J₂ := e₃ + J₃
    let h := q₃ / e₂
    let g := (q₃ + J₃) / e₃
    let u := (q₂ + J₂) / e₂
    let d₂ := 1 + u + q₂ / e₃
    h * 2 * d₂ ≤ (g + h) * (2 * u) := by
  dsimp only
  have he₂ne : e₂ ≠ 0 := ne_of_gt he₂
  have he₃ne : e₃ ≠ 0 := ne_of_gt he₃
  have hrem : 0 ≤ (e₄ + e₅) *
      (q₂ + e₃ + q₃ + (e₄ + e₅)) := by positivity
  field_simp [he₂ne, he₃ne]
  nlinarith

/-- The second two-node transport inequality is purely passive: the diagonal
contains the boundary coupling `s*c` plus an additional positive term. -/
theorem source_two_node_right_transport
    {dExtra c h g s : ℝ}
    (hdExtra : 0 ≤ dExtra) (hc : 0 ≤ c)
    (hh : 0 ≤ h) (hg : 0 ≤ g) (hs : 0 ≤ s) :
    h * s * c ≤ (g + h) * (dExtra + s * c) := by
  nlinarith [mul_nonneg hg hdExtra, mul_nonneg hh hdExtra,
    mul_nonneg hg (mul_nonneg hs hc)]

/-- Every column of an inverse tridiagonal Green kernel satisfies this same
terminal estimate.  No inverse formula or path-length induction is needed:
the last row and nonnegativity of the solution contain the whole argument. -/
theorem terminal_mixed_boundary_nonpos
    {a d h g s yPrev y b : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hrow : d * y - a * yPrev = b)
    (htransport : h * s * d ≤ (g + h) * a) :
    h * s * yPrev - (g + h) * y ≤ 0 := by
  have hlast : a * yPrev ≤ d * y := by linarith
  have hscale : 0 ≤ h * s := mul_nonneg hh hs
  have h₁ : (h * s) * (a * yPrev) ≤ (h * s) * (d * y) :=
    mul_le_mul_of_nonneg_left hlast hscale
  have h₂ : (h * s * d) * y ≤ ((g + h) * a) * y :=
    mul_le_mul_of_nonneg_right htransport hy
  have ha0 : 0 ≤ a := le_of_lt ha
  have hcancel : a * (h * s * yPrev) ≤
      a * ((g + h) * y) := by
    nlinarith [h₁, h₂]
  exact sub_nonpos.mpr
    (le_of_mul_le_mul_left (by simpa [mul_assoc] using hcancel) ha)

/-- Uniform source-boundary transport inequality.  The terminal cycle current
is `JLast=eFork+JFork`; after clearing denominators the unused margin is
`JFork * (qLast + eFork + qFork + JFork)`. -/
theorem source_terminal_transport
    {eBack eFork qLast qFork JFork s : ℝ}
    (heBack : 0 < eBack) (heFork : 0 < eFork)
    (hqLast : 0 < qLast) (hqFork : 0 < qFork)
    (hJFork : 0 < JFork) (hs : 0 ≤ s) :
    let h := qFork / eBack
    let g := (qFork + JFork) / eFork
    let u := (qLast + eFork + JFork) / eBack
    let d := 1 + u + qLast / eFork
    h * s * d ≤ (g + h) * (s * u) := by
  dsimp only
  have heBackNe : eBack ≠ 0 := ne_of_gt heBack
  have heForkNe : eFork ≠ 0 := ne_of_gt heFork
  have hrem : 0 ≤ JFork * (qLast + eFork + qFork + JFork) := by positivity
  have hbase :
      (qFork / eBack) *
          (1 + (qLast + eFork + JFork) / eBack + qLast / eFork) ≤
        ((qFork + JFork) / eFork + qFork / eBack) *
          ((qLast + eFork + JFork) / eBack) := by
    field_simp [heBackNe, heForkNe]
    nlinarith
  calc
    (qFork / eBack) * s *
        (1 + (qLast + eFork + JFork) / eBack + qLast / eFork) =
      s * ((qFork / eBack) *
        (1 + (qLast + eFork + JFork) / eBack + qLast / eFork)) := by ring
    _ ≤ s * (((qFork + JFork) / eFork + qFork / eBack) *
        ((qLast + eFork + JFork) / eBack)) :=
      mul_le_mul_of_nonneg_left hbase hs
    _ = ((qFork + JFork) / eFork + qFork / eBack) *
        (s * ((qLast + eFork + JFork) / eBack)) := by ring

/-- Arbitrary-length weighted-path correction theorem.  The Z-matrix maximum
principle makes the response to every nonnegative internal forcing
nonnegative.  The terminal row then reduces the mixed fork boundary
functional to `terminal_mixed_boundary_nonpos`; no formula for `D⁻¹` and no
path-length induction are required. -/
theorem zmatrix_terminal_mixed_boundary_nonpos
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℝ) (w y b : ι → ℝ) (prev last : ι)
    {a d h g s : ℝ}
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hDw : ∀ i, 0 < ∑ j, D i j * w j)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i, ∑ j, D i j * y j = b i)
    (ha : 0 < a) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hterminal : d * y last - a * y prev = b last)
    (htransport : h * s * d ≤ (g + h) * a) :
    h * s * y prev - (g + h) * y last ≤ 0 := by
  have hy := zmatrix_solution_nonneg D w y b hoff hw hDw hb hsolve
  exact terminal_mixed_boundary_nonpos ha hh hs (hy last) (hb last)
    hterminal htransport

end TypeIIL
