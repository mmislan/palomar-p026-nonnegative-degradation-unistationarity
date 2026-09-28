module

public import proofs.TypeIIL.CyclicClosureBound

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- Choosing no upper columns leaves the lower matrix unchanged. -/
theorem columnVertexMatrix_empty {ι : Type*} [DecidableEq ι]
    (lo hi : Matrix ι ι ℝ) : columnVertexMatrix lo hi ∅ = lo := by
  ext i j
  simp [columnVertexMatrix]

/-- Normalized cyclic three-term matrix.  The additive definition remains
correct even in the small collision quotients where predecessor and successor
coordinates coincide. -/
def cyclicSectorMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (alpha gamma : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    (if j = i then 1 else 0) +
      (if j = next.symm i then -alpha i else 0) +
      (if j = next i then gamma i else 0)

/-- The additive matrix definition evaluates to the intended three-term row,
including small quotients where predecessor, self, or successor columns
coincide. -/
theorem cyclicSectorMatrix_mulVec_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (alpha gamma z : ι → ℝ) (i : ι) :
    Matrix.mulVec (cyclicSectorMatrix next alpha gamma) z i =
      (-alpha i) * z (next.symm i) + z i + gamma i * z (next i) := by
  simp only [Matrix.mulVec, dotProduct, cyclicSectorMatrix]
  simp_rw [add_mul]
  simp only [Finset.sum_add_distrib]
  simp
  ring

/-- The predecessor coefficient for which the normalized row annihilates a
given positive comparison vector. -/
noncomputable def cyclicSectorUpper
    {ι : Type*} (next : ι ≃ ι) (gamma v : ι → ℝ) (i : ι) : ℝ :=
  (v i + gamma i * v (next i)) / v (next.symm i)

/-- Varying the predecessor coefficient in row `next j` is exactly a
columnwise affine variation in column `j`.  This is the bridge from the
source-current residual box to the already compiled determinant
interpolation theorem. -/
theorem cyclicSectorMatrix_eq_columnBoxMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (alpha gamma v : ι → ℝ)
    (hupper : ∀ i, cyclicSectorUpper next gamma v i ≠ 0) :
    cyclicSectorMatrix next alpha gamma =
      columnBoxMatrix
        (cyclicSectorMatrix next (fun _ => 0) gamma)
        (cyclicSectorMatrix next (cyclicSectorUpper next gamma v) gamma)
        (fun j => alpha (next j) /
          cyclicSectorUpper next gamma v (next j)) := by
  funext i j
  by_cases hpred : j = next.symm i
  · subst j
    simp only [columnBoxMatrix, cyclicSectorMatrix, next.apply_symm_apply,
      ite_true]
    field_simp [hupper i]
    ring
  · simp only [columnBoxMatrix, cyclicSectorMatrix, hpred, ite_false]
    ring

/-- Endpoint-free form of the column-box identity.  It permits selected
predecessor coefficients (in particular the unique signed seam) to be held
fixed by taking equal lower and upper endpoints. -/
theorem cyclicSectorMatrix_eq_columnBoxMatrix_of_alpha_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (alpha gamma loAlpha hiAlpha t : ι → ℝ)
    (halpha : ∀ j, alpha (next j) =
      t j * hiAlpha (next j) + (1 - t j) * loAlpha (next j)) :
    cyclicSectorMatrix next alpha gamma =
      columnBoxMatrix
        (cyclicSectorMatrix next loAlpha gamma)
        (cyclicSectorMatrix next hiAlpha gamma) t := by
  funext i j
  by_cases hpred : j = next.symm i
  · subst j
    simp only [columnBoxMatrix, cyclicSectorMatrix, ite_true]
    have ha := halpha (next.symm i)
    simp only [next.apply_symm_apply] at ha
    rw [ha]
    ring
  · simp only [columnBoxMatrix, cyclicSectorMatrix, hpred, ite_false]
    ring

/-- A column vertex of two cyclic matrices is again a cyclic matrix; the
predecessor coefficient in row `r` is selected by the membership of its
predecessor column `next.symm r`. -/
theorem columnVertexMatrix_cyclicSectorMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (loAlpha hiAlpha gamma : ι → ℝ) (s : Finset ι) :
    columnVertexMatrix (cyclicSectorMatrix next loAlpha gamma)
        (cyclicSectorMatrix next hiAlpha gamma) s =
      cyclicSectorMatrix next
        (fun r => if next.symm r ∈ s then hiAlpha r else loAlpha r) gamma := by
  ext r c
  by_cases hc : c ∈ s
  · by_cases hpred : c = next.symm r
    · subst c
      simp [columnVertexMatrix, cyclicSectorMatrix, hc]
    · simp [columnVertexMatrix, cyclicSectorMatrix, hc, hpred]
  · by_cases hpred : c = next.symm r
    · subst c
      simp [columnVertexMatrix, cyclicSectorMatrix, hc]
    · simp [columnVertexMatrix, cyclicSectorMatrix, hc, hpred]

/-- Interpolating one still-lower predecessor column of a cyclic vertex is
again a cyclic matrix with exactly one interpolated row coefficient. -/
theorem columnVertexMatrix_updateCol_cyclicSectorMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (loAlpha hiAlpha gamma : ι → ℝ)
    (s : Finset ι) (i : ι) (t : ℝ) :
    (columnVertexMatrix (cyclicSectorMatrix next loAlpha gamma)
        (cyclicSectorMatrix next hiAlpha gamma) s).updateCol i
      (t • (fun r => cyclicSectorMatrix next hiAlpha gamma r i) +
        (1 - t) • (fun r => cyclicSectorMatrix next loAlpha gamma r i)) =
      cyclicSectorMatrix next
        (fun r => if r = next i then
          t * hiAlpha r + (1 - t) * loAlpha r
        else if next.symm r ∈ s then hiAlpha r else loAlpha r) gamma := by
  ext r c
  by_cases hci : c = i
  · subst c
    by_cases hpred : i = next.symm r
    · have hr : r = next i := by
        rw [hpred, next.apply_symm_apply]
      simp [cyclicSectorMatrix, hr]
      ring
    · have hr : r ≠ next i := by
        intro hr
        subst r
        exact hpred (next.symm_apply_apply i).symm
      simp [cyclicSectorMatrix, hpred]
      ring
  · rw [Matrix.updateCol_ne hci]
    rw [columnVertexMatrix_cyclicSectorMatrix]
    by_cases hr : r = next i
    · subst r
      have hpred : c ≠ i := hci
      simp [cyclicSectorMatrix, hpred]
    · simp [cyclicSectorMatrix, hr]

/-- Frozen-coordinate determinant interpolation.  Once every box vertex is
nonnegative and the lower vertex is positive, strict upper slack in every
actually interpolated coordinate forces a positive determinant.  Coordinates
held fixed have `t = 0`, so they satisfy the same criterion automatically. -/
theorem det_cyclicSectorMatrix_pos_of_frozen_vertex_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (alpha gamma loAlpha hiAlpha t : ι → ℝ)
    (halpha : ∀ j, alpha (next j) =
      t j * hiAlpha (next j) + (1 - t j) * loAlpha (next j))
    (ht0 : ∀ j, 0 ≤ t j) (ht1 : ∀ j, t j < 1)
    (hvertex : ∀ s ⊆ Finset.univ,
      0 ≤ (columnVertexMatrix
        (cyclicSectorMatrix next loAlpha gamma)
        (cyclicSectorMatrix next hiAlpha gamma) s).det)
    (hlower : 0 < (cyclicSectorMatrix next loAlpha gamma).det) :
    0 < (cyclicSectorMatrix next alpha gamma).det := by
  rw [cyclicSectorMatrix_eq_columnBoxMatrix_of_alpha_eq next alpha gamma
    loAlpha hiAlpha t halpha]
  rw [det_columnBoxMatrix_eq_boxInterpolation]
  apply boxInterpolation_pos ht0 ht1 hvertex
  simpa only [columnVertexMatrix_empty] using hlower

/-- At the all-upper box vertex the comparison vector is an exact null
vector.  This authenticates the distinguished boundary vertex without any
determinant expansion. -/
theorem cyclicSectorMatrix_upper_mulVec_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : ι ≃ ι) (gamma v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) :
    Matrix.mulVec
      (cyclicSectorMatrix next (cyclicSectorUpper next gamma v) gamma) v = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, cyclicSectorMatrix, Pi.zero_apply]
  simp_rw [add_mul]
  simp only [Finset.sum_add_distrib]
  simp
  rw [cyclicSectorUpper]
  field_simp [hv (next.symm i)]
  ring

/-- Positivity of the comparison vector and nonnegativity of the forward
coefficient put every row-null predecessor coefficient strictly above zero. -/
theorem cyclicSectorUpper_pos
    {ι : Type*} (next : ι ≃ ι) (gamma v : ι → ℝ)
    (hgamma : ∀ i, 0 ≤ gamma i) (hv : ∀ i, 0 < v i) (i : ι) :
    0 < cyclicSectorUpper next gamma v i := by
  unfold cyclicSectorUpper
  exact div_pos (add_pos_of_pos_of_nonneg (hv i)
    (mul_nonneg (hgamma i) (le_of_lt (hv (next i)))))
    (hv (next.symm i))

/-- Determinant interpolation reduces the normalized positive-current cone
to its proper column vertices.  The all-upper vertex is singular for the
explicit positive comparison vector, while every actual predecessor
coefficient lies strictly inside its column interval. -/
theorem det_cyclicSectorMatrix_pos_of_proper_vertex_margin
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (next : ι ≃ ι) (alpha gamma v : ι → ℝ) (margin : ℝ)
    (hgamma : ∀ i, 0 ≤ gamma i) (hv : ∀ i, 0 < v i)
    (halpha0 : ∀ i, 0 ≤ alpha i)
    (halphaUpper : ∀ i, alpha i < cyclicSectorUpper next gamma v i)
    (hmargin : 0 < margin)
    (hproper : ∀ s ⊆ Finset.univ, s ≠ Finset.univ →
      margin ≤
        (columnVertexMatrix
          (cyclicSectorMatrix next (fun _ => 0) gamma)
          (cyclicSectorMatrix next (cyclicSectorUpper next gamma v) gamma)
          s).det) :
    0 < (cyclicSectorMatrix next alpha gamma).det := by
  let upper := cyclicSectorUpper next gamma v
  let lo := cyclicSectorMatrix next (fun _ => 0) gamma
  let hi := cyclicSectorMatrix next upper gamma
  let t : ι → ℝ := fun j => alpha (next j) / upper (next j)
  have hupperPos : ∀ i, 0 < upper i := fun i =>
    cyclicSectorUpper_pos next gamma v hgamma hv i
  have hmatrix : cyclicSectorMatrix next alpha gamma =
      columnBoxMatrix lo hi t := by
    exact cyclicSectorMatrix_eq_columnBoxMatrix next alpha gamma v
      (fun i => ne_of_gt (hupperPos i))
  rw [hmatrix]
  apply det_columnBoxMatrix_pos_of_proper_vertex_margin
      (margin := margin)
  · intro j
    exact div_nonneg (halpha0 (next j)) (le_of_lt (hupperPos (next j)))
  · intro j
    exact (div_lt_one (hupperPos (next j))).mpr (halphaUpper (next j))
  · exact hmargin
  · simpa [lo, hi, upper] using hproper
  · have hmul : Matrix.mulVec hi v = 0 := by
      exact cyclicSectorMatrix_upper_mulVec_eq_zero next gamma v
        (fun i => ne_of_gt (hv i))
    have hdet : hi.det = 0 := by
      let i : ι := Classical.choice (inferInstance : Nonempty ι)
      apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
        (v := v) (i := i)
      · exact hmul
      · exact mem_nonZeroDivisors_iff_ne_zero.mpr (ne_of_gt (hv i))
    have hallEq : columnVertexMatrix lo hi Finset.univ = hi := by
      ext r c
      simp [columnVertexMatrix]
    rw [hallEq, hdet]

/-- Scalar closure at every proper box vertex.  The three forward factors
are in the unit interval.  If the exceptional predecessor coefficient is
negative, its local two-edge minor implies the required global comparison;
if it is nonnegative, deleting an ordinary predecessor edge removes the
cycle correction and positivity is immediate.  The statement is independent
of cycle parity. -/
theorem proper_vertex_signed_seam_closure_pos
    (n : ℕ) {whole middle r₀ rPrev rest wrap : ℝ}
    (hmiddle : 1 ≤ middle) (hwhole : middle ≤ whole)
    (hr₀0 : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hrPrev0 : 0 ≤ rPrev) (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : (-wrap) * rPrev < 1 - r₀) :
    0 < whole + (-1 : ℝ) ^ n * (r₀ * rPrev * rest) +
      wrap * rPrev * middle := by
  have hcycle0 : 0 ≤ r₀ * rPrev * rest :=
    mul_nonneg (mul_nonneg hr₀0 hrPrev0) hrest0
  have hcycle1 : r₀ * rPrev * rest < 1 :=
    forward_cycle_product_lt_one_of_local hr₀0 hr₀1 hrPrev1 hrest0 hrest1
  by_cases hwrap : wrap < 0
  · have hglobal : (-wrap) * rPrev < 1 - r₀ * rPrev * rest :=
      local_wrap_bound_implies_global hr₀0 hrPrev1 hrest0 hrest1 hlocal
    have hcorr : (0 : ℝ) ≤ rPrev * middle :=
      mul_nonneg hrPrev0 (le_trans zero_le_one hmiddle)
    simpa using negative_wrap_formula_pos n hmiddle hwhole hcycle0 hwrap
      hglobal (le_refl 0) hcorr
  · have hwrap0 : 0 ≤ wrap := le_of_not_gt hwrap
    have hwhole1 : 1 ≤ whole := le_trans hmiddle hwhole
    have h := nonnegative_wrap_zero_correction_margin n hwhole1 hcycle0
      hcycle1 hwrap0 hrPrev0 (le_trans zero_le_one hmiddle) (by rfl)
    simpa using h.2

/-- Cut-path kernel exclusion on every proper interpolation edge.  A missing
ordinary predecessor makes the cyclic correction product exactly zero, so
the local seam minor and the unit-interval forward ratios are sufficient;
the globally false correction estimate is absent. -/
theorem proper_vertex_signed_seam_cyclic_transfer_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale r₀ rPrev rest wrap x₀ x₁ : ℝ}
    (hfirst : 0 ≤ first) (hlast : 0 ≤ last)
    (hmiddleWeights : ∀ w ∈ middleWeights, 0 ≤ w)
    (hscale : 0 < scale) (hscaleEq : scale = r₀ * rest)
    (hzeroCorrection : first * last * middleWeights.prod = 0)
    (hr₀0 : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hrPrev0 : 0 ≤ rPrev) (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : (-wrap) * rPrev < 1 - r₀)
    (hend :
      (pathTransfer (first :: (middleWeights ++ [last])) x₀ x₁).2 =
        (r₀ * rPrev * rest) * x₀)
    (hwrap :
      wrap * (pathTransfer
        (first :: (middleWeights ++ [last])) x₀ x₁).1 =
          scale * (x₀ + x₁)) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hmiddle : 1 ≤ pathContinuant middleWeights :=
    one_le_pathContinuant hmiddleWeights
  have hwhole : pathContinuant middleWeights ≤
      pathContinuant (first :: (middleWeights ++ [last])) :=
    pathContinuant_middle_le hfirst hlast hmiddleWeights
  have hclosure := proper_vertex_signed_seam_closure_pos
    middleWeights.length hmiddle hwhole hr₀0 hr₀1 hrPrev0 hrPrev1
      hrest0 hrest1 hlocal
  apply cyclic_transfer_kernel_eq_zero middleWeights hscale
      (edge := rPrev) (cycle := r₀ * rPrev * rest)
      (correction := 0) (wrap := wrap)
  · rw [hscaleEq]
    ring
  · simpa using hzeroCorrection.symm
  · simpa using hclosure
  · exact hend
  · exact hwrap

/-- A real affine segment which starts positive and never vanishes cannot end
nonpositive.  This elementary sign-continuation lemma replaces any appeal to
topological connectedness when signs are propagated across cube edges. -/
theorem affine_endpoint_pos_of_ne_zero
    {a b : ℝ} (ha : 0 < a)
    (hne : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * b + (1 - t) * a ≠ 0) :
    0 < b := by
  by_contra hb
  have hb0 : b ≤ 0 := le_of_not_gt hb
  have hden : 0 < a - b := by linarith
  let t := a / (a - b)
  have ht0 : 0 ≤ t := le_of_lt (div_pos ha hden)
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hz := hne t ht0 ht1
  apply hz
  dsimp [t]
  field_simp [ne_of_gt hden]
  ring

/-- Exact one-column affinity of the determinant, stated in the form used to
walk from the empty vertex to every proper vertex. -/
theorem det_updateCol_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i : ι) (u : ι → ℝ) (t : ℝ) :
    (A.updateCol i
      (t • u + (1 - t) • (fun r => A r i))).det =
      t * (A.updateCol i u).det + (1 - t) * A.det := by
  rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul]
  simp

/-- The exceptional signed seam can be recovered from the zero-seam cut by
one-column affinity.  At the row-null upper value the comparison vector makes
the matrix singular; consequently every seam coefficient strictly below that
value has the same positive determinant sign as the zero-seam cut.  No lower
bound on the seam coefficient is needed. -/
theorem det_cyclicSectorMatrix_update_seam_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (next : ι ≃ ι) (gamma v : ι → ℝ) (seam : ι) (a : ℝ)
    (hv : ∀ i, 0 < v i)
    (hupper : 0 < cyclicSectorUpper next gamma v seam)
    (ha : a < cyclicSectorUpper next gamma v seam)
    (hzero : 0 <
      (cyclicSectorMatrix next
        (Function.update (cyclicSectorUpper next gamma v) seam 0) gamma).det) :
    0 <
      (cyclicSectorMatrix next
        (Function.update (cyclicSectorUpper next gamma v) seam a) gamma).det := by
  let upper := cyclicSectorUpper next gamma v
  let zeroAlpha := Function.update upper seam 0
  let actualAlpha := Function.update upper seam a
  let Mzero := cyclicSectorMatrix next zeroAlpha gamma
  let Mupper := cyclicSectorMatrix next upper gamma
  let col := next.symm seam
  let t := a / upper seam
  have hupperDet : Mupper.det = 0 := by
    have hmul : Matrix.mulVec Mupper v = 0 := by
      exact cyclicSectorMatrix_upper_mulVec_eq_zero next gamma v
        (fun i => ne_of_gt (hv i))
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      hmul (mem_nonZeroDivisors_iff_ne_zero.mpr (ne_of_gt (hv i)))
  have hmatrix :
      cyclicSectorMatrix next actualAlpha gamma =
        Mzero.updateCol col
          (t • (fun r => Mupper r col) +
            (1 - t) • (fun r => Mzero r col)) := by
    ext r c
    by_cases hc : c = col
    · subst c
      rw [Matrix.updateCol_self]
      dsimp [Mzero, Mupper, zeroAlpha, actualAlpha, col, t, upper]
      by_cases hrs : r = seam
      · subst r
        simp [cyclicSectorMatrix]
        field_simp [hupper.ne']
        ring
      · have hpred : next.symm seam ≠ next.symm r := by
          exact fun h => hrs (next.symm.injective h.symm)
        simp [cyclicSectorMatrix, hpred]
        ring
    · rw [Matrix.updateCol_ne hc]
      dsimp [Mzero, actualAlpha, zeroAlpha, col, upper]
      by_cases hrs : r = seam
      · subst r
        have hpred : c ≠ next.symm seam := hc
        simp [cyclicSectorMatrix, hpred]
      · simp [cyclicSectorMatrix, Function.update, hrs]
  have hupperMatrix :
      Mzero.updateCol col (fun r => Mupper r col) = Mupper := by
    ext r c
    by_cases hc : c = col
    · subst c
      rw [Matrix.updateCol_self]
    · rw [Matrix.updateCol_ne hc]
      dsimp [Mzero, Mupper, zeroAlpha, col, upper]
      by_cases hrs : r = seam
      · subst r
        have hpred : c ≠ next.symm seam := hc
        simp [cyclicSectorMatrix, hpred]
      · simp [cyclicSectorMatrix, Function.update, hrs]
  have hdetAffine := det_updateCol_affine Mzero col
    (fun r => Mupper r col) t
  rw [← hmatrix] at hdetAffine
  have ht : t < 1 := (div_lt_one hupper).mpr ha
  rw [hdetAffine, hupperMatrix, hupperDet]
  dsimp [Mzero, zeroAlpha] at hzero ⊢
  nlinarith

/-- Positivity propagates across a column edge whenever every intermediate
matrix is nonsingular.  Proper cyclic vertices have exactly this property:
one still-missing predecessor edge keeps the correction product zero along
the whole edge. -/
theorem det_updateCol_pos_of_segment_nonsingular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i : ι) (u : ι → ℝ)
    (hA : 0 < A.det)
    (hne : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (A.updateCol i
        (t • u + (1 - t) • (fun r => A r i))).det ≠ 0) :
    0 < (A.updateCol i u).det := by
  apply affine_endpoint_pos_of_ne_zero hA
  intro t ht0 ht1
  rw [← det_updateCol_affine A i u t]
  exact hne t ht0 ht1

/-- Every proper vertex of a column box is positive if the empty vertex is
positive and each edge that remains in the proper cube is nonsingular along
its full segment.  This is the exact combinatorial replacement for an
explicit signed permutation expansion of every cyclic determinant. -/
theorem columnVertexMatrix_det_pos_of_proper_edge_nonsingular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lo hi : Matrix ι ι ℝ)
    (hempty : 0 < lo.det)
    (hedge : ∀ (s : Finset ι) (i : ι), i ∉ s →
      insert i s ≠ Finset.univ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0) :
    ∀ s ⊆ Finset.univ, s ≠ Finset.univ →
      0 < (columnVertexMatrix lo hi s).det := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simpa only [columnVertexMatrix_empty] using hempty
  | @insert i s his ih =>
      intro _ hproper
      have hsproper : s ≠ Finset.univ := by
        intro hs
        apply hproper
        simp [hs]
      have hbase : 0 < (columnVertexMatrix lo hi s).det :=
        ih (Finset.subset_univ s) hsproper
      have hstep := det_updateCol_pos_of_segment_nonsingular
        (columnVertexMatrix lo hi s) i (fun r => hi r i) hbase (by
          intro t ht0 ht1
          have hne := hedge s i his hproper t ht0 ht1
          simpa [columnVertexMatrix, his] using hne)
      have hmatrix :
          (columnVertexMatrix lo hi s).updateCol i (fun r => hi r i) =
            columnVertexMatrix lo hi (insert i s) := by
        ext r c
        by_cases hci : c = i
        · subst c
          simp [columnVertexMatrix]
        · simp [columnVertexMatrix, Matrix.updateCol, hci]
      rw [hmatrix] at hstep
      exact hstep

/-- Full-cube version of determinant sign propagation.  When every edge
segment is nonsingular, positivity at the empty vertex reaches every vertex,
including the all-upper endpoint. -/
theorem columnVertexMatrix_det_pos_of_edge_nonsingular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : Matrix ι ι ℝ)
    (hempty : 0 < lo.det)
    (hedge : ∀ (s : Finset ι) (i : ι), i ∉ s →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0) :
    ∀ s ⊆ Finset.univ, 0 < (columnVertexMatrix lo hi s).det := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [columnVertexMatrix_empty] using hempty
  | @insert i s his ih =>
      intro _
      have hbase : 0 < (columnVertexMatrix lo hi s).det :=
        ih (Finset.subset_univ s)
      have hstep := det_updateCol_pos_of_segment_nonsingular
        (columnVertexMatrix lo hi s) i (fun r => hi r i) hbase (by
          intro t ht0 ht1
          simpa [columnVertexMatrix, his] using hedge s i his t ht0 ht1)
      have hmatrix :
          (columnVertexMatrix lo hi s).updateCol i (fun r => hi r i) =
            columnVertexMatrix lo hi (insert i s) := by
        ext r c
        by_cases hci : c = i
        · subst c
          simp [columnVertexMatrix]
        · simp [columnVertexMatrix, Matrix.updateCol, hci]
      rw [hmatrix] at hstep
      exact hstep

/-- Sign propagation in a cube with one frozen column.  Vertices which have
all genuinely varying columns upper are the same matrix as the all-upper
endpoint; every other induction edge retains a genuinely missing column. -/
theorem columnVertexMatrix_det_pos_of_frozen_edge_nonsingular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : Matrix ι ι ℝ) (frozen : ι)
    (hfrozen : ∀ r, lo r frozen = hi r frozen)
    (hempty : 0 < lo.det) (hall : 0 < hi.det)
    (hedge : ∀ (s : Finset ι) (i : ι), i ∉ s →
      (∃ c, c ≠ frozen ∧ c ∉ insert i s) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0) :
    ∀ s ⊆ Finset.univ, 0 < (columnVertexMatrix lo hi s).det := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [columnVertexMatrix_empty] using hempty
  | @insert i s his ih =>
      intro _
      by_cases heffective : ∀ c, c ≠ frozen → c ∈ insert i s
      · have hmatrix : columnVertexMatrix lo hi (insert i s) = hi := by
          ext r c
          by_cases hcf : c = frozen
          · subst c
            simp [columnVertexMatrix, hfrozen]
          · simp [columnVertexMatrix, heffective c hcf]
        rw [hmatrix]
        exact hall
      · push Not at heffective
        obtain ⟨c, hcf, hcmiss⟩ := heffective
        have hbase : 0 < (columnVertexMatrix lo hi s).det :=
          ih (Finset.subset_univ s)
        have hstep := det_updateCol_pos_of_segment_nonsingular
          (columnVertexMatrix lo hi s) i (fun r => hi r i) hbase (by
            intro t ht0 ht1
            simpa [columnVertexMatrix, his] using
              hedge s i his ⟨c, hcf, hcmiss⟩ t ht0 ht1)
        have hmatrix :
            (columnVertexMatrix lo hi s).updateCol i (fun r => hi r i) =
              columnVertexMatrix lo hi (insert i s) := by
          ext r d
          by_cases hdi : d = i
          · subst d
            simp [columnVertexMatrix]
          · simp [columnVertexMatrix, Matrix.updateCol, hdi]
        rw [hmatrix] at hstep
        exact hstep

/-- Final box criterion using edgewise kernel exclusion rather than explicit
vertex margins.  All proper signs are propagated from the empty vertex; only
the all-upper boundary value is supplied separately. -/
theorem det_columnBoxMatrix_pos_of_proper_edge_nonsingular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lo hi : Matrix ι ι ℝ) (t : ι → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1)
    (hempty : 0 < lo.det)
    (hedge : ∀ (s : Finset ι) (i : ι), i ∉ s →
      insert i s ≠ Finset.univ → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (u • (fun r => hi r i) +
          (1 - u) • (fun r => lo r i))).det ≠ 0)
    (hall : 0 ≤ hi.det) :
    0 < (columnBoxMatrix lo hi t).det := by
  rw [det_columnBoxMatrix_eq_boxInterpolation]
  apply boxInterpolation_pos ht0 ht1
  · intro s hs
    by_cases hsu : s = Finset.univ
    · subst s
      have hallEq : columnVertexMatrix lo hi Finset.univ = hi := by
        ext r c
        simp [columnVertexMatrix]
      rw [hallEq]
      exact hall
    · exact le_of_lt
        (columnVertexMatrix_det_pos_of_proper_edge_nonsingular lo hi
          hempty hedge s hs hsu)
  · simpa only [columnVertexMatrix_empty] using hempty

/-- Kernel form of determinant nonsingularity over the reals.  This is the
bridge by which the already compiled cut-path transfer theorem can discharge
every edge hypothesis in the proper-cube sign argument. -/
theorem det_ne_zero_of_mulVec_kernel_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hkernel : ∀ z : ι → ℝ, Matrix.mulVec M z = 0 → z = 0) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hMz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hz (hkernel z hMz)

/-- With every predecessor port cut, strict forward contraction excludes a
kernel by maximum modulus: a largest nonzero coordinate would have to be
strictly smaller than its successor. -/
theorem cyclicSectorMatrix_zero_alpha_kernel_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (next : ι ≃ ι) (gamma z : ι → ℝ)
    (hgamma0 : ∀ i, 0 ≤ gamma i) (hgamma1 : ∀ i, gamma i < 1)
    (hkernel : Matrix.mulVec
      (cyclicSectorMatrix next (fun _ => 0) gamma) z = 0) :
    z = 0 := by
  obtain ⟨k, _, hkmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => |z i|) Finset.univ_nonempty
  have hkrow := congrFun hkernel k
  rw [cyclicSectorMatrix_mulVec_apply] at hkrow
  simp only [Pi.zero_apply, neg_zero, zero_mul, zero_add] at hkrow
  have hnextLe : |z (next k)| ≤ |z k| := hkmax (next k) (Finset.mem_univ _)
  have habs : |z k| = gamma k * |z (next k)| := by
    calc
      |z k| = |(-(gamma k * z (next k)))| := by
        rw [eq_neg_of_add_eq_zero_left hkrow]
      _ = |gamma k * z (next k)| := abs_neg _
      _ = gamma k * |z (next k)| := by
        rw [abs_mul, abs_of_nonneg (hgamma0 k)]
  have hkzero : z k = 0 := by
    by_contra hkne
    have hkpos : 0 < |z k| := abs_pos.mpr hkne
    have hnpos : 0 < |z (next k)| := by
      by_contra hn
      have hnzero : |z (next k)| = 0 := le_antisymm (le_of_not_gt hn) (abs_nonneg _)
      rw [hnzero, mul_zero] at habs
      linarith
    have hstrict : gamma k * |z (next k)| < |z (next k)| := by
      calc
        gamma k * |z (next k)| < 1 * |z (next k)| :=
          mul_lt_mul_of_pos_right (hgamma1 k) hnpos
        _ = |z (next k)| := one_mul _
    linarith
  funext i
  have hile : |z i| ≤ |z k| := hkmax i (Finset.mem_univ _)
  rw [hkzero, abs_zero] at hile
  exact abs_eq_zero.mp (le_antisymm hile (abs_nonneg _))

/-- The all-cut cyclic matrix has positive determinant.  Switch on the
strictly contractive forward rows one at a time; maximum-modulus kernel
exclusion keeps every column edge of the transposed cube nonsingular. -/
theorem det_cyclicSectorMatrix_zero_alpha_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (next : ι ≃ ι) (gamma : ι → ℝ)
    (hnext : ∀ i, i ≠ next i)
    (hgamma0 : ∀ i, 0 ≤ gamma i) (hgamma1 : ∀ i, gamma i < 1) :
    0 < (cyclicSectorMatrix next (fun _ => 0) gamma).det := by
  let lo := (cyclicSectorMatrix next (fun _ => 0) (fun _ => 0)).transpose
  let hi := (cyclicSectorMatrix next (fun _ => 0) gamma).transpose
  have hlo : lo = 1 := by
    ext r c
    simp [lo, cyclicSectorMatrix, Matrix.one_apply]
  have hempty : 0 < lo.det := by
    rw [hlo]
    simp
  have hedge : ∀ (s : Finset ι) (i : ι), i ∉ s →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0 := by
    intro s i his t ht0 ht1
    let g : ι → ℝ := fun j =>
      if j = i then t * gamma j else if j ∈ s then gamma j else 0
    let E := (columnVertexMatrix lo hi s).updateCol i
      (t • (fun r => hi r i) + (1 - t) • (fun r => lo r i))
    have hmatrix : E = (cyclicSectorMatrix next (fun _ => 0) g).transpose := by
      ext r c
      by_cases hci : c = i
      · subst c
        have hnext' : next i ≠ i := fun h => hnext i h.symm
        by_cases hri : r = i <;> by_cases hrn : r = next i <;>
          simp [E, g, lo, hi, cyclicSectorMatrix, hnext i, hnext', hri, hrn]
      · by_cases hcs : c ∈ s
        · simp [E, g, lo, hi, columnVertexMatrix, cyclicSectorMatrix,
            hci, hcs]
        · simp [E, g, lo, hi, columnVertexMatrix, cyclicSectorMatrix,
            hci, hcs]
    have hg0 : ∀ j, 0 ≤ g j := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [g, ite_eq_left rfl]
        exact mul_nonneg ht0 (hgamma0 i)
      · by_cases hjs : j ∈ s
        · simp [g, hji, hjs, hgamma0 j]
        · simp [g, hji, hjs]
    have hg1 : ∀ j, g j < 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        have htg : t * gamma i ≤ gamma i :=
          mul_le_of_le_one_left (hgamma0 i) ht1
        simp only [g, ite_eq_left rfl]
        exact lt_of_le_of_lt htg (hgamma1 i)
      · by_cases hjs : j ∈ s
        · simp [g, hji, hjs, hgamma1 j]
        · simp [g, hji, hjs]
    change E.det ≠ 0
    rw [hmatrix, Matrix.det_transpose]
    exact det_ne_zero_of_mulVec_kernel_eq_zero
      (cyclicSectorMatrix next (fun _ => 0) g)
      (fun z hz => cyclicSectorMatrix_zero_alpha_kernel_eq_zero
        next g z hg0 hg1 hz)
  have hall := columnVertexMatrix_det_pos_of_edge_nonsingular lo hi
    hempty hedge Finset.univ (Finset.subset_univ _)
  have hallEq : columnVertexMatrix lo hi Finset.univ = hi := by
    ext r c
    simp [columnVertexMatrix]
  rw [hallEq] at hall
  simpa [hi, Matrix.det_transpose] using hall

end TypeIIL
