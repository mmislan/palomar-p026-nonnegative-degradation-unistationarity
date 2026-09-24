import Mathlib

namespace TypeIIL

open scoped BigOperators

/-- A row-sum-zero matrix has zero determinant.  This authenticates the
all-upper vertex in the nonnegative-wrap interpolation argument. -/
theorem det_eq_zero_of_row_sums_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hrows : ∀ i, ∑ j, M i j = 0) :
    M.det = 0 := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := fun _ => 1) (i := i)
  · funext r
    simp [Matrix.mulVec, dotProduct, hrows r]
  · simp

/-- Matching continuant of a path whose edge weights are listed in order. -/
def pathContinuant : List ℝ → ℝ
  | [] => 1
  | [w] => 1 + w
  | w :: v :: ws => pathContinuant (v :: ws) + w * pathContinuant ws

/-- The continuant recurrence may equally be run from the right endpoint. -/
theorem pathContinuant_append_two (ws : List ℝ) (u v : ℝ) :
    pathContinuant (ws ++ [u, v]) =
      pathContinuant (ws ++ [u]) + v * pathContinuant ws := by
  induction ws using List.twoStepInduction with
  | nil => simp [pathContinuant]; ring
  | singleton w => simp [pathContinuant]; ring
  | cons_cons w x ws ih₁ ih₂ =>
      simp only [List.cons_append, pathContinuant]
      have hx := ih₂ x
      simp only [List.cons_append] at hx
      rw [hx, ih₁]
      ring

/-- Matching continuants do not depend on which endpoint of the path is
chosen first. -/
theorem pathContinuant_reverse (ws : List ℝ) :
    pathContinuant ws.reverse = pathContinuant ws := by
  induction ws using List.twoStepInduction with
  | nil => simp [pathContinuant]
  | singleton w => simp [pathContinuant]
  | cons_cons w v ws ih₁ ih₂ =>
      simp only [List.reverse_cons, List.append_assoc]
      change pathContinuant (ws.reverse ++ [v, w]) =
        pathContinuant (w :: v :: ws)
      rw [pathContinuant_append_two]
      have hv := ih₂ v
      simp only [List.reverse_cons] at hv
      rw [hv, ih₁]
      simp only [pathContinuant]

/-- Transfer through the cut path for the denominator-free recurrence
`x_{k+1} = w_k x_{k-1} - x_k`. -/
def pathTransfer : List ℝ → ℝ → ℝ → ℝ × ℝ
  | [], x₀, x₁ => (x₀, x₁)
  | w :: ws, x₀, x₁ => pathTransfer ws x₁ (w * x₀ - x₁)

theorem pathTransfer_append (left right : List ℝ) (x₀ x₁ : ℝ) :
    pathTransfer (left ++ right) x₀ x₁ =
      pathTransfer right (pathTransfer left x₀ x₁).1
        (pathTransfer left x₀ x₁).2 := by
  induction left generalizing x₀ x₁ with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.cons_append, pathTransfer]
      exact ih x₁ (w * x₀ - x₁)

/-- The transfer is exactly linear in its two endpoint data.  This is the
formal bridge used when interior source equations are eliminated. -/
theorem pathTransfer_linear (ws : List ℝ) (x₀ x₁ : ℝ) :
    pathTransfer ws x₀ x₁ =
      (x₀ * (pathTransfer ws 1 0).1 +
          x₁ * (pathTransfer ws 0 1).1,
        x₀ * (pathTransfer ws 1 0).2 +
          x₁ * (pathTransfer ws 0 1).2) := by
  induction ws generalizing x₀ x₁ with
  | nil => simp [pathTransfer]
  | cons w ws ih =>
      simp only [pathTransfer]
      rw [ih x₁ (w * x₀ - x₁)]
      norm_num
      rw [ih 0 w, ih 1 (-1)]
      constructor <;> simp <;> ring

theorem pathContinuant_cons_formula (w : ℝ) (ws : List ℝ) :
    pathContinuant (w :: ws) =
      pathContinuant ws + w * pathContinuant ws.tail := by
  cases ws <;> simp [pathContinuant]

/-- Closed form for the endpoint produced by forward elimination.  The two
coefficients are precisely the whole and middle matching continuants that
occur in the cyclic determinant formula. -/
theorem pathTransfer_cons_snd (w : ℝ) (ws : List ℝ) (x₀ x₁ : ℝ) :
    (pathTransfer (w :: ws) x₀ x₁).2 =
      (-1 : ℝ) ^ (ws.length + 1) * pathContinuant ws * x₁ +
        (-1 : ℝ) ^ ws.length * w * pathContinuant ws.tail * x₀ := by
  induction ws generalizing w x₀ x₁ with
  | nil => simp [pathTransfer, pathContinuant]; ring
  | cons v ws ih =>
      change (pathTransfer (v :: ws) x₁ (w * x₀ - x₁)).2 = _
      rw [ih v x₁ (w * x₀ - x₁)]
      rw [pathContinuant_cons_formula]
      simp only [List.length_cons, List.tail_cons, pow_succ]
      ring

/-- Discrete Wronskian (Cassini identity) for path continuants.  This is the
term that becomes the product of all predecessor coefficients when the two
cyclic boundary equations are combined. -/
theorem pathContinuant_append_wronskian (ws : List ℝ) (v : ℝ) :
    pathContinuant (ws ++ [v]) * pathContinuant ws.tail -
        pathContinuant (ws ++ [v]).tail * pathContinuant ws =
      (-1 : ℝ) ^ ws.length * v * ws.prod := by
  induction ws with
  | nil => simp [pathContinuant]
  | cons w ws ih =>
      simp only [List.cons_append, List.tail_cons, List.length_cons,
        List.prod_cons, pow_succ]
      rw [pathContinuant_cons_formula, pathContinuant_cons_formula]
      linear_combination -w * ih

/-- Exact determinant of the two boundary equations left after eliminating a
cut cyclic path.  `scale` is the product of all forward coefficients except
the wrap edge, `cycle = scale * edge`, and
`scale * correction = first * last * middle.prod`. -/
theorem cyclic_boundary_determinant_identity
    (middle : List ℝ)
    {first last scale cycle edge correction wrap : ℝ}
    (hcycle : cycle = scale * edge)
    (hcorrection : scale * correction = first * last * middle.prod) :
    let s := (-1 : ℝ) ^ middle.length
    let whole := pathContinuant (first :: (middle ++ [last]))
    let mid := pathContinuant middle
    let near := first * pathContinuant middle.tail
    let far := pathContinuant (middle ++ [last])
    let farNear := first * pathContinuant (middle ++ [last]).tail
    ((-s * farNear - cycle) * (-wrap * s * mid - scale) -
        (s * far) * (wrap * s * near - scale)) =
      s * scale *
        (whole + s * cycle + wrap * edge * mid - wrap * correction) := by
  dsimp only
  have hW := pathContinuant_append_wronskian middle last
  have hwhole := pathContinuant_cons_formula first (middle ++ [last])
  have hs : ((-1 : ℝ) ^ middle.length) *
      ((-1 : ℝ) ^ middle.length) = 1 := by
    rw [← pow_add]
    simp
  rw [hwhole, hcycle]
  linear_combination
    -wrap * first * hW +
      ((-1 : ℝ) ^ middle.length) * wrap * hcorrection -
        scale ^ 2 * edge * hs -
      first * wrap *
        (pathContinuant (middle ++ [last]) * pathContinuant middle.tail -
          pathContinuant (middle ++ [last]).tail * pathContinuant middle) * hs

theorem two_equation_kernel_eq_zero
    {a b c d x y : ℝ}
    (hdet : a * d - b * c ≠ 0)
    (h₁ : a * x + b * y = 0)
    (h₂ : c * x + d * y = 0) : x = 0 ∧ y = 0 := by
  have hx : (a * d - b * c) * x = 0 := by
    linear_combination d * h₁ - b * h₂
  have hy : (a * d - b * c) * y = 0 := by
    linear_combination a * h₂ - c * h₁
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet,
    (mul_eq_zero.mp hy).resolve_left hdet⟩

/-- Zero-kernel theorem for the two boundary equations.  All interior
elimination and parity have been absorbed into the four displayed
coefficients; strict positivity of the scalar closure formula is enough. -/
theorem cyclic_boundary_kernel_eq_zero
    (middle : List ℝ)
    {first last scale cycle edge correction wrap x₀ x₁ : ℝ}
    (hscale : 0 < scale)
    (hcycle : cycle = scale * edge)
    (hcorrection : scale * correction = first * last * middle.prod)
    (hclosure : 0 <
      pathContinuant (first :: (middle ++ [last])) +
        (-1 : ℝ) ^ middle.length * cycle +
        wrap * edge * pathContinuant middle - wrap * correction)
    (h₁ :
      (-((-1 : ℝ) ^ middle.length) *
          (first * pathContinuant (middle ++ [last]).tail) - cycle) * x₀ +
        (((-1 : ℝ) ^ middle.length) *
          pathContinuant (middle ++ [last])) * x₁ = 0)
    (h₂ :
      (wrap * ((-1 : ℝ) ^ middle.length) *
          (first * pathContinuant middle.tail) - scale) * x₀ +
        (-wrap * ((-1 : ℝ) ^ middle.length) *
          pathContinuant middle - scale) * x₁ = 0) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hid := cyclic_boundary_determinant_identity middle (wrap := wrap)
    hcycle hcorrection
  have hsne : (-1 : ℝ) ^ middle.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscalene : scale ≠ 0 := ne_of_gt hscale
  have hclosurene :
      pathContinuant (first :: (middle ++ [last])) +
          (-1 : ℝ) ^ middle.length * cycle +
          wrap * edge * pathContinuant middle - wrap * correction ≠ 0 :=
    ne_of_gt hclosure
  apply two_equation_kernel_eq_zero
    (a := -((-1 : ℝ) ^ middle.length) *
      (first * pathContinuant (middle ++ [last]).tail) - cycle)
    (b := ((-1 : ℝ) ^ middle.length) *
      pathContinuant (middle ++ [last]))
    (c := wrap * ((-1 : ℝ) ^ middle.length) *
      (first * pathContinuant middle.tail) - scale)
    (d := -wrap * ((-1 : ℝ) ^ middle.length) *
      pathContinuant middle - scale)
  · rw [hid]
    exact mul_ne_zero (mul_ne_zero hsne hscalene) hclosurene
  · exact h₁
  · exact h₂

/-- The two natural endpoint closure equations for `pathTransfer` imply the
coefficient-form equations consumed by `cyclic_boundary_kernel_eq_zero`. -/
theorem cyclic_transfer_boundary_equations
    (middle : List ℝ)
    {first last scale cycle wrap x₀ x₁ : ℝ}
    (hend :
      (pathTransfer (first :: (middle ++ [last])) x₀ x₁).2 = cycle * x₀)
    (hwrap :
      wrap * (pathTransfer (first :: (middle ++ [last])) x₀ x₁).1 =
        scale * (x₀ + x₁)) :
    ((-((-1 : ℝ) ^ middle.length) *
          (first * pathContinuant (middle ++ [last]).tail) - cycle) * x₀ +
        (((-1 : ℝ) ^ middle.length) *
          pathContinuant (middle ++ [last])) * x₁ = 0) ∧
    ((wrap * ((-1 : ℝ) ^ middle.length) *
          (first * pathContinuant middle.tail) - scale) * x₀ +
        (-wrap * ((-1 : ℝ) ^ middle.length) *
          pathContinuant middle - scale) * x₁ = 0) := by
  have hfull := pathTransfer_cons_snd first (middle ++ [last]) x₀ x₁
  simp only [List.length_append, List.length_singleton, pow_succ] at hfull
  have happ := pathTransfer_append (first :: middle) [last] x₀ x₁
  have hfirst :
      (pathTransfer (first :: (middle ++ [last])) x₀ x₁).1 =
        (pathTransfer (first :: middle) x₀ x₁).2 := by
    have hp := congrArg Prod.fst happ
    simpa [pathTransfer] using hp
  have hpre := pathTransfer_cons_snd first middle x₀ x₁
  simp only [pow_succ] at hpre
  rw [hfirst, hpre] at hwrap
  constructor
  · linear_combination hend - hfull
  · linear_combination hwrap

/-- End-to-end zero-kernel theorem for the cut-path transfer model. -/
theorem cyclic_transfer_kernel_eq_zero
    (middle : List ℝ)
    {first last scale cycle edge correction wrap x₀ x₁ : ℝ}
    (hscale : 0 < scale)
    (hcycle : cycle = scale * edge)
    (hcorrection : scale * correction = first * last * middle.prod)
    (hclosure : 0 <
      pathContinuant (first :: (middle ++ [last])) +
        (-1 : ℝ) ^ middle.length * cycle +
        wrap * edge * pathContinuant middle - wrap * correction)
    (hend :
      (pathTransfer (first :: (middle ++ [last])) x₀ x₁).2 = cycle * x₀)
    (hwrap :
      wrap * (pathTransfer (first :: (middle ++ [last])) x₀ x₁).1 =
        scale * (x₀ + x₁)) :
    x₀ = 0 ∧ x₁ = 0 := by
  rcases cyclic_transfer_boundary_equations middle hend hwrap with ⟨h₁, h₂⟩
  exact cyclic_boundary_kernel_eq_zero middle hscale hcycle hcorrection
    hclosure h₁ h₂

theorem one_le_pathContinuant {ws : List ℝ}
    (hws : ∀ w ∈ ws, 0 ≤ w) : 1 ≤ pathContinuant ws := by
  induction ws using List.twoStepInduction with
  | nil => simp [pathContinuant]
  | singleton w =>
      have hw : 0 ≤ w := hws w (by simp)
      simp [pathContinuant, hw]
  | cons_cons w v ws ih₁ ih₂ =>
      have hw : 0 ≤ w := hws w (by simp)
      have htail : ∀ x ∈ v :: ws, 0 ≤ x := by
        intro x hx
        exact hws x (by simp [hx])
      have hrest : ∀ x ∈ ws, 0 ≤ x := by
        intro x hx
        exact hws x (by simp [hx])
      have hnonneg : 0 ≤ pathContinuant ws :=
        le_trans (by norm_num) (ih₁ hrest)
      simp only [pathContinuant]
      exact le_trans (ih₂ v htail)
        (le_add_of_nonneg_right (mul_nonneg hw hnonneg))

/-- Adding a nonnegative edge at the left can only increase the path
continuant. -/
theorem pathContinuant_le_cons {w : ℝ} {ws : List ℝ}
    (hw : 0 ≤ w) (hws : ∀ x ∈ ws, 0 ≤ x) :
    pathContinuant ws ≤ pathContinuant (w :: ws) := by
  cases ws with
  | nil => simp [pathContinuant, hw]
  | cons v vs =>
      have hnonneg : 0 ≤ pathContinuant vs :=
        le_trans (by norm_num) (one_le_pathContinuant (by
          intro x hx
          exact hws x (by simp [hx])))
      simp only [pathContinuant]
      exact le_add_of_nonneg_right (mul_nonneg hw hnonneg)

/-- Adding a nonnegative edge at the right can only increase the path
continuant. -/
theorem pathContinuant_le_append_singleton {w : ℝ} {ws : List ℝ}
    (hw : 0 ≤ w) (hws : ∀ x ∈ ws, 0 ≤ x) :
    pathContinuant ws ≤ pathContinuant (ws ++ [w]) := by
  induction ws using List.twoStepInduction with
  | nil => simp [pathContinuant, hw]
  | singleton v =>
      simp [pathContinuant, hw, add_comm, add_left_comm]
  | cons_cons u v ws ih₁ ih₂ =>
      have hu : 0 ≤ u := hws u (by simp)
      have htail : ∀ x ∈ v :: ws, 0 ≤ x := by
        intro x hx
        exact hws x (by simp [hx])
      have hrest : ∀ x ∈ ws, 0 ≤ x := by
        intro x hx
        exact hws x (by simp [hx])
      simp only [List.cons_append, pathContinuant]
      exact add_le_add (ih₂ v htail) (mul_le_mul_of_nonneg_left (ih₁ hrest) hu)

theorem pathContinuant_middle_le
    {left right : ℝ} {middle : List ℝ}
    (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hmiddle : ∀ x ∈ middle, 0 ≤ x) :
    pathContinuant middle ≤
      pathContinuant (left :: (middle ++ [right])) := by
  exact le_trans (pathContinuant_le_append_singleton hright hmiddle)
    (pathContinuant_le_cons hleft (by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hmiddle x hx
      · rcases List.mem_singleton.mp hx with rfl
        exact hright))

section BoxInterpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Barycentric weight of a vertex of the unit box. -/
def boxVertexWeight (t : ι → ℝ) (s : Finset ι) : ℝ :=
  (∏ i ∈ s, t i) * ∏ i ∈ Finset.univ \ s, (1 - t i)

/-- Multiaffine interpolation from values on all vertices of a finite box. -/
def boxInterpolation (vertex : Finset ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.powerset, boxVertexWeight t s * vertex s

/-- A matrix obtained by independently interpolating each column. -/
def columnBoxMatrix (lo hi : Matrix ι ι ℝ) (t : ι → ℝ) : Matrix ι ι ℝ :=
  fun r c => t c * hi r c + (1 - t c) * lo r c

/-- Vertex matrix associated with a subset of upper columns. -/
def columnVertexMatrix
    (lo hi : Matrix ι ι ℝ) (s : Finset ι) : Matrix ι ι ℝ :=
  fun r c => if c ∈ s then hi r c else lo r c

/-- The determinant of a columnwise affine matrix is its exact box
interpolation from the vertex determinants. -/
theorem det_columnBoxMatrix_eq_boxInterpolation
    (lo hi : Matrix ι ι ℝ) (t : ι → ℝ) :
    (columnBoxMatrix lo hi t).det =
      boxInterpolation (fun s => (columnVertexMatrix lo hi s).det) t := by
  classical
  unfold boxInterpolation boxVertexWeight
  rw [Matrix.det_apply']
  simp_rw [columnBoxMatrix, Finset.prod_add]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_powerset] at hs
  rw [Matrix.det_apply']
  simp_rw [Finset.mul_sum]
  congr 1
  funext σ
  unfold columnVertexMatrix
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.filter_mem_eq_inter]
  simp [Finset.sdiff_eq_filter]
  ring

theorem boxVertexWeight_nonneg {t : ι → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (s : Finset ι) :
    0 ≤ boxVertexWeight t s := by
  unfold boxVertexWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ => ht0 i
  · exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (ht1 i)

/-- If all vertex values are nonnegative, the empty vertex is positive, and
every coordinate is strictly below its upper endpoint, then the multiaffine
interpolation is strictly positive. -/
theorem boxInterpolation_pos
    {vertex : Finset ι → ℝ} {t : ι → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1)
    (hvertex : ∀ s ⊆ Finset.univ, 0 ≤ vertex s)
    (hempty : 0 < vertex ∅) :
    0 < boxInterpolation vertex t := by
  unfold boxInterpolation
  apply Finset.sum_pos'
  · intro s hs
    rw [Finset.mem_powerset] at hs
    exact mul_nonneg
      (boxVertexWeight_nonneg ht0 (fun i => le_of_lt (ht1 i)) s)
      (hvertex s hs)
  · refine ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
    have hprod : 0 < ∏ i : ι, (1 - t i) := by
      exact Finset.prod_pos fun i _ => sub_pos.mpr (ht1 i)
    simpa [boxVertexWeight] using mul_pos hprod hempty

/-- A convenient boundary-certificate form of `boxInterpolation_pos`.  For
the cyclic determinant application every proper box vertex has a uniform
positive margin, while the all-upper vertex is allowed to vanish. -/
theorem boxInterpolation_pos_of_proper_vertex_margin
    {vertex : Finset ι → ℝ} {t : ι → ℝ} {margin : ℝ}
    [Nonempty ι]
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1)
    (hmargin : 0 < margin)
    (hproper : ∀ s ⊆ Finset.univ, s ≠ Finset.univ → margin ≤ vertex s)
    (hall : 0 ≤ vertex Finset.univ) :
    0 < boxInterpolation vertex t := by
  apply boxInterpolation_pos ht0 ht1
  · intro s hs
    by_cases hsu : s = Finset.univ
    · simpa [hsu] using hall
    · exact le_trans (le_of_lt hmargin) (hproper s hs hsu)
  · have hempty_ne : (∅ : Finset ι) ≠ Finset.univ := by
      intro h
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
      rw [← h] at hi
      exact Finset.notMem_empty i hi
    exact lt_of_lt_of_le hmargin
      (hproper ∅ (Finset.empty_subset _) hempty_ne)

/-- Matrix form of the proper-vertex interpolation criterion. -/
theorem det_columnBoxMatrix_pos_of_proper_vertex_margin
    [Nonempty ι]
    {lo hi : Matrix ι ι ℝ} {t : ι → ℝ} {margin : ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1)
    (hmargin : 0 < margin)
    (hproper : ∀ s ⊆ Finset.univ, s ≠ Finset.univ →
      margin ≤ (columnVertexMatrix lo hi s).det)
    (hall : 0 ≤ (columnVertexMatrix lo hi Finset.univ).det) :
    0 < (columnBoxMatrix lo hi t).det := by
  rw [det_columnBoxMatrix_eq_boxInterpolation]
  exact boxInterpolation_pos_of_proper_vertex_margin ht0 ht1 hmargin
    hproper hall

end BoxInterpolation

/-- The scalar inequality behind the sole-negative-wrap case of the cyclic
Schur determinant.  `whole` and `middle` are the positive matching
continuants of the cut path, `cycle` is the forward cycle product, `wrap` is
the magnitude of the negative predecessor coefficient, and `edge` is the
forward coefficient paired with that wrap edge. -/
theorem negative_wrap_closure_pos
    {whole middle cycle wrap edge correction : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hcycle0 : 0 ≤ cycle) (hwrap : 0 ≤ wrap)
    (hcomparison : wrap * edge < 1 - cycle)
    (hcorrection : correction ≤ edge * middle) :
    0 < whole - cycle - wrap * correction := by
  have hmiddlePos : 0 < middle := lt_of_lt_of_le zero_lt_one hmiddle
  have hscaled : wrap * edge * middle < (1 - cycle) * middle :=
    mul_lt_mul_of_pos_right hcomparison hmiddlePos
  have hcorr : wrap * correction ≤ wrap * (edge * middle) :=
    mul_le_mul_of_nonneg_left hcorrection hwrap
  have hassoc : wrap * (edge * middle) = wrap * edge * middle := by ring
  have hpath : (1 - cycle) * middle ≤ whole - cycle := by
    nlinarith [mul_nonneg hcycle0 (sub_nonneg.mpr hmiddle)]
  rw [hassoc] at hcorr
  exact sub_pos.mpr (lt_of_le_of_lt hcorr (lt_of_lt_of_le hscaled hpath))

/-- Odd cyclic orientation has an additional positive forward-cycle term, so
the same comparison estimate is stronger than needed. -/
theorem negative_wrap_closure_pos_odd
    {whole middle cycle wrap edge correction : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hcycle0 : 0 ≤ cycle) (hwrap : 0 ≤ wrap)
    (hcomparison : wrap * edge < 1 - cycle)
    (hcorrection : correction ≤ edge * middle) :
    0 < whole + cycle - wrap * correction := by
  have heven := negative_wrap_closure_pos hmiddle hwhole hcycle0 hwrap
    hcomparison hcorrection
  nlinarith

/-- Parity-free form of the sole-negative-wrap estimate in the exact cyclic
closure formula.  Since `(-1)^n * cycle ≥ -cycle`, the even orientation is
the worst case. -/
theorem negative_wrap_formula_pos
    (n : ℕ) {whole middle cycle wrap edge correction : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hcycle0 : 0 ≤ cycle) (hwrap : wrap < 0)
    (hcomparison : (-wrap) * edge < 1 - cycle)
    (hcorrection0 : 0 ≤ correction)
    (hcorrection : correction ≤ edge * middle) :
    0 < whole + (-1 : ℝ) ^ n * cycle +
      wrap * edge * middle - wrap * correction := by
  have hsignsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    simp
  have hsign : -1 ≤ (-1 : ℝ) ^ n := by
    nlinarith [sq_nonneg (((-1 : ℝ) ^ n) + 1)]
  have hparity : -cycle ≤ (-1 : ℝ) ^ n * cycle := by
    simpa using (mul_le_mul_of_nonneg_right hsign hcycle0 :
      (-1 : ℝ) * cycle ≤ (-1 : ℝ) ^ n * cycle)
  have hgap : edge * middle - correction ≤ edge * middle := by
    linarith
  have hgap0 : 0 ≤ edge * middle - correction := sub_nonneg.mpr hcorrection
  have hbase := negative_wrap_closure_pos hmiddle hwhole hcycle0
    (neg_nonneg.mpr (le_of_lt hwrap)) hcomparison hgap
  nlinarith [hgap0]

/-- At every proper nonnegative-wrap box vertex, some predecessor coefficient
vanishes.  Hence the product correction is zero and the fixed-cut closure has
the uniform margin `1 - cycle`, without rotating the cycle. -/
theorem nonnegative_wrap_zero_correction_margin
    (n : ℕ) {whole middle cycle wrap edge correction : ℝ}
    (hwhole : 1 ≤ whole)
    (hcycle0 : 0 ≤ cycle) (hcycle1 : cycle < 1)
    (hwrap : 0 ≤ wrap) (hedge : 0 ≤ edge) (hmiddle : 0 ≤ middle)
    (hcorrection : correction = 0) :
    1 - cycle ≤ whole + (-1 : ℝ) ^ n * cycle +
        wrap * edge * middle - wrap * correction ∧
      0 < whole + (-1 : ℝ) ^ n * cycle +
        wrap * edge * middle - wrap * correction := by
  have hsignsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    simp
  have hsign : -1 ≤ (-1 : ℝ) ^ n := by
    nlinarith [sq_nonneg (((-1 : ℝ) ^ n) + 1)]
  have hparity : -cycle ≤ (-1 : ℝ) ^ n * cycle := by
    simpa using (mul_le_mul_of_nonneg_right hsign hcycle0 :
      (-1 : ℝ) * cycle ≤ (-1 : ℝ) ^ n * cycle)
  have hpositiveTerm : 0 ≤ wrap * edge * middle :=
    mul_nonneg (mul_nonneg hwrap hedge) hmiddle
  rw [hcorrection, mul_zero]
  constructor <;> linarith

/-- A local two-edge exceptional-wrap estimate implies the global comparison
used by `negative_wrap_formula_pos`.  The remaining forward ratios enter only
through a factor in `[0,1]`. -/
theorem local_wrap_bound_implies_global
    {r₀ rPrev rest wrap : ℝ}
    (hr₀0 : 0 ≤ r₀) (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : wrap * rPrev < 1 - r₀) :
    wrap * rPrev < 1 - r₀ * rPrev * rest := by
  have hrProd : rPrev * rest ≤ 1 :=
    calc
      rPrev * rest ≤ 1 * rest := mul_le_mul_of_nonneg_right hrPrev1 hrest0
      _ ≤ 1 := by simpa only [one_mul] using hrest1
  have hcycle : r₀ * rPrev * rest ≤ r₀ := by
    calc
      r₀ * rPrev * rest = r₀ * (rPrev * rest) := by ring
      _ ≤ r₀ * 1 := mul_le_mul_of_nonneg_left hrProd hr₀0
      _ = r₀ := by ring
  linarith

/-- The same local bounds force the complete forward cycle product below
one. -/
theorem forward_cycle_product_lt_one_of_local
    {r₀ rPrev rest : ℝ}
    (hr₀0 : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1) :
    r₀ * rPrev * rest < 1 := by
  have hrProd : rPrev * rest ≤ 1 :=
    calc
      rPrev * rest ≤ 1 * rest := mul_le_mul_of_nonneg_right hrPrev1 hrest0
      _ ≤ 1 := by simpa only [one_mul] using hrest1
  have hcycle : r₀ * rPrev * rest ≤ r₀ := by
    calc
      r₀ * rPrev * rest = r₀ * (rPrev * rest) := by ring
      _ ≤ r₀ * 1 := mul_le_mul_of_nonneg_left hrProd hr₀0
      _ = r₀ := by ring
  exact lt_of_le_of_lt hcycle hr₀1

/-- A positive raw diagonal-forward gap produces a forward ratio in `[0,1)`.
This is the normalization used for source Schur rows. -/
theorem forward_ratio_mem_unitInterval
    {B F : ℝ} (hB : 0 < B) (hF : 0 ≤ F) (hgap : 0 < B - F) :
    0 ≤ F / B ∧ F / B < 1 := by
  constructor
  · exact div_nonneg hF (le_of_lt hB)
  · exact (div_lt_one hB).2 (by linarith)

/-- The unnormalized two-edge source margin is exactly the local exceptional
wrap comparison after dividing the two adjacent Schur rows by their positive
diagonals. -/
theorem raw_two_edge_margin_implies_normalized_wrap
    {B F Bprev Fprev W : ℝ}
    (hB : 0 < B) (hBprev : 0 < Bprev)
    (hlocal : W * Fprev < (B - F) * Bprev) :
    (W / B) * (Fprev / Bprev) < 1 - F / B := by
  have hden : 0 < B * Bprev := mul_pos hB hBprev
  calc
    (W / B) * (Fprev / Bprev) =
        (W * Fprev) / (B * Bprev) := by field_simp
    _ < ((B - F) * Bprev) / (B * Bprev) :=
      (div_lt_div_iff_of_pos_right hden).2 hlocal
    _ = 1 - F / B := by field_simp

end TypeIIL
