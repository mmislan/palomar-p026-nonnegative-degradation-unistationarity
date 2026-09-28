module

public import proofs.TypeIIL.CyclicCombinedCone
public import proofs.TypeIIL.OrderedCurrentSecantKernel
public import proofs.TypeIIL.SourceCyclicRowAssembly
public import proofs.TypeIIL.SourceForkSchurMargin

@[expose] public section

namespace TypeIIL

/-- Positive column gauge accumulated along an indexed cyclic path. -/
def cyclicPrefixScale (gamma : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => gamma k * cyclicPrefixScale gamma k

/-- Peeling the first factor from a cyclic prefix product. -/
theorem cyclicPrefixScale_succ_shift (gamma : ℕ → ℝ) (k : ℕ) :
    cyclicPrefixScale gamma (k + 1) =
      gamma 0 * cyclicPrefixScale (fun i => gamma (i + 1)) k := by
  induction k with
  | zero => simp [cyclicPrefixScale]
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega]
      simp only [cyclicPrefixScale]
      have ih' := ih
      simp only [cyclicPrefixScale] at ih'
      rw [ih']
      ring

theorem cyclicPrefixScale_pos (gamma : ℕ → ℝ)
    (hgamma : ∀ i, 0 < gamma i) :
    ∀ k, 0 < cyclicPrefixScale gamma k := by
  intro k
  induction k with
  | zero => simp [cyclicPrefixScale]
  | succ k ih =>
      simp only [cyclicPrefixScale]
      exact mul_pos (hgamma k) ih

theorem cyclicPrefixScale_nonneg (gamma : ℕ → ℝ)
    (hgamma : ∀ i, 0 ≤ gamma i) :
    ∀ k, 0 ≤ cyclicPrefixScale gamma k := by
  intro k
  induction k with
  | zero => simp [cyclicPrefixScale]
  | succ k ih =>
      simp only [cyclicPrefixScale]
      exact mul_nonneg (hgamma k) ih

theorem cyclicPrefixScale_le_one (gamma : ℕ → ℝ)
    (hgamma0 : ∀ i, 0 ≤ gamma i) (hgamma1 : ∀ i, gamma i ≤ 1) :
    ∀ k, cyclicPrefixScale gamma k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [cyclicPrefixScale]
  | succ k ih =>
      simp only [cyclicPrefixScale]
      simpa using (mul_le_mul (hgamma1 k) ih
        (cyclicPrefixScale_nonneg gamma hgamma0 k) (by norm_num))

/-- Natural continuant weights on the path obtained by cutting the seam row
from a cyclic three-term system. -/
def cyclicCutWeights (alpha gamma : ℕ → ℝ) (l : ℕ) : List ℝ :=
  List.ofFn (fun i : Fin (l - 1) => alpha (i + 1) * gamma i)

@[simp] theorem cyclicCutWeights_length (alpha gamma : ℕ → ℝ) (l : ℕ) :
    (cyclicCutWeights alpha gamma l).length = l - 1 := by
  simp [cyclicCutWeights]

theorem cyclicCutWeights_getElem (alpha gamma : ℕ → ℝ) (l i : ℕ)
    (hi : i < (cyclicCutWeights alpha gamma l).length) :
    (cyclicCutWeights alpha gamma l)[i] = alpha (i + 1) * gamma i := by
  simp [cyclicCutWeights]

/-- Prefix-product gauging turns a normalized three-term row into the exact
denominator-free continuant recurrence. -/
theorem cyclic_sector_row_to_indexed_recurrence
    (alpha gamma z : ℕ → ℝ) (k : ℕ)
    (hrow : (-alpha (k + 1)) * z k + z (k + 1) +
      gamma (k + 1) * z (k + 2) = 0) :
    cyclicPrefixScale gamma (k + 2) * z (k + 2) =
      (alpha (k + 1) * gamma k) *
          (cyclicPrefixScale gamma k * z k) -
        cyclicPrefixScale gamma (k + 1) * z (k + 1) := by
  apply normalized_sector_row_to_continuant_step
    (alpha := alpha (k + 1)) (gammaPrev := gamma k)
    (gamma := gamma (k + 1))
  · rfl
  · rfl
  · exact hrow

/-- Once the first two entries of an indexed second-order recurrence vanish,
every entry through the represented cut path vanishes. -/
theorem indexed_recurrence_zero_of_initial
    (weights : List ℝ) (x : ℕ → ℝ)
    (hrow : ∀ i (hi : i < weights.length),
      x (i + 2) = weights[i] * x i - x (i + 1))
    (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    ∀ i, i ≤ weights.length + 1 → x i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      by_cases hi0 : i = 0
      · simpa [hi0] using hx0
      by_cases hi1 : i = 1
      · simpa [hi1] using hx1
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := by
        use i - 2
        omega
      have hk : k < weights.length := by omega
      have hk0 : x k = 0 := ih k (by omega) (by omega)
      have hk1 : x (k + 1) = 0 := ih (k + 1) (by omega) (by omega)
      rw [hrow k hk, hk0, hk1]
      ring

/-- Indexed proper-edge landing theorem.  It is the zero-correction analogue
of `raw_source_schur_cyclic_indexed_kernel_eq_zero`: the transfer endpoint
equations and the local seam minor kill the first two coordinates, and the
row recurrence then kills the entire enumerated cycle. -/
theorem proper_vertex_signed_seam_cyclic_indexed_kernel_eq_zero
    (middleWeights : List ℝ)
    {first last scale r₀ rPrev rest wrap : ℝ}
    (x : ℕ → ℝ)
    (hfirst : 0 ≤ first) (hlast : 0 ≤ last)
    (hmiddleWeights : ∀ w ∈ middleWeights, 0 ≤ w)
    (hscale : 0 < scale) (hscaleEq : scale = r₀ * rest)
    (hzeroCorrection : first * last * middleWeights.prod = 0)
    (hr₀0 : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hrPrev0 : 0 ≤ rPrev) (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : (-wrap) * rPrev < 1 - r₀)
    (hrow : ∀ i
      (hi : i < (first :: (middleWeights ++ [last])).length),
      x (i + 2) = (first :: (middleWeights ++ [last]))[i] * x i -
        x (i + 1))
    (hend :
      x ((first :: (middleWeights ++ [last])).length + 1) =
        (r₀ * rPrev * rest) * x 0)
    (hwrap :
      wrap * x (first :: (middleWeights ++ [last])).length =
        scale * (x 0 + x 1)) :
    ∀ i, i ≤ (first :: (middleWeights ++ [last])).length + 1 → x i = 0 := by
  let weights := first :: (middleWeights ++ [last])
  have htransfer : pathTransfer weights (x 0) (x 1) =
      (x weights.length, x (weights.length + 1)) :=
    pathTransfer_eq_of_indexed_recurrence weights x hrow
  have hinitial : x 0 = 0 ∧ x 1 = 0 := by
    apply proper_vertex_signed_seam_cyclic_transfer_kernel_eq_zero
      middleWeights hfirst hlast hmiddleWeights hscale hscaleEq
        hzeroCorrection hr₀0 hr₀1 hrPrev0 hrPrev1 hrest0 hrest1 hlocal
    · rw [htransfer]
      exact hend
    · rw [htransfer]
      exact hwrap
  exact indexed_recurrence_zero_of_initial weights x hrow
    hinitial.1 hinitial.2

/-- List-shaped wrapper for the indexed proper-cut theorem.  It removes the
artificial choice of first/middle/last from source adapters: any weight list of
length at least two with zero product is split canonically at its endpoints. -/
theorem proper_vertex_signed_seam_cyclic_list_kernel_eq_zero
    (weights : List ℝ)
    {scale r₀ rPrev rest wrap : ℝ}
    (x : ℕ → ℝ)
    (hlen : 2 ≤ weights.length)
    (hweights : ∀ w ∈ weights, 0 ≤ w)
    (hscale : 0 < scale) (hscaleEq : scale = r₀ * rest)
    (hzeroCorrection : weights.prod = 0)
    (hr₀0 : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hrPrev0 : 0 ≤ rPrev) (hrPrev1 : rPrev ≤ 1)
    (hrest0 : 0 ≤ rest) (hrest1 : rest ≤ 1)
    (hlocal : (-wrap) * rPrev < 1 - r₀)
    (hrow : ∀ i (hi : i < weights.length),
      x (i + 2) = weights[i] * x i - x (i + 1))
    (hend : x (weights.length + 1) =
      (r₀ * rPrev * rest) * x 0)
    (hwrap : wrap * x weights.length = scale * (x 0 + x 1)) :
    ∀ i, i ≤ weights.length + 1 → x i = 0 := by
  cases weights with
  | nil => simp at hlen
  | cons first tail =>
      have htail : tail ≠ [] := by
        intro ht
        subst tail
        simp at hlen
      let middle := tail.dropLast
      let last := tail.getLast htail
      have htailEq : tail = middle ++ [last] := by
        exact (List.dropLast_append_getLast htail).symm
      rw [htailEq] at hweights hzeroCorrection hrow hend hwrap ⊢
      have hfirst : 0 ≤ first := hweights first (by simp)
      have hlast : 0 ≤ last := hweights last (by simp)
      have hmiddle : ∀ w ∈ middle, 0 ≤ w := by
        intro w hw
        exact hweights w (by simp [hw])
      have hzero : first * last * middle.prod = 0 := by
        have hz := hzeroCorrection
        simp only [List.prod_cons, List.prod_append, List.prod_nil, mul_one] at hz
        calc
          first * last * middle.prod = first * (middle.prod * last) := by ring
          _ = 0 := hz
      exact proper_vertex_signed_seam_cyclic_indexed_kernel_eq_zero middle
        x hfirst hlast hmiddle hscale hscaleEq hzero hr₀0 hr₀1
        hrPrev0 hrPrev1 hrest0 hrest1 hlocal hrow hend hwrap

/-- Exact natural-index adapter for a proper cyclic vertex.  Cutting at the
signed seam leaves a path whose first continuant weight vanishes; the cyclic
return and seam row are then precisely the two transfer endpoints. -/
theorem proper_cut_indexed_cyclic_kernel_eq_zero
    (l : ℕ) (hl : 3 ≤ l) (alpha gamma z : ℕ → ℝ)
    (hgamma0 : ∀ i, 0 < gamma i)
    (hgamma1 : ∀ i, gamma i < 1)
    (halpha : ∀ i, 1 ≤ i → i < l → 0 ≤ alpha i)
    (hmissing : ∃ m, 1 ≤ m ∧ m < l ∧ alpha m = 0)
    (hlocal : (-alpha 0) * gamma (l - 1) < 1 - gamma 0)
    (hrow : ∀ k, k < l - 1 →
      (-alpha (k + 1)) * z k + z (k + 1) +
        gamma (k + 1) * z (k + 2) = 0)
    (hreturn : z l = z 0)
    (hseam : (-alpha 0) * z (l - 1) + z 0 + gamma 0 * z 1 = 0) :
    ∀ i, i ≤ l → z i = 0 := by
  let weights := cyclicCutWeights alpha gamma l
  let x : ℕ → ℝ := fun i => cyclicPrefixScale gamma i * z i
  let scale := cyclicPrefixScale gamma (l - 1)
  let rest := cyclicPrefixScale (fun i => gamma (i + 1)) (l - 2)
  obtain ⟨m, hm1, hml, hm0⟩ := hmissing
  have hlen : 2 ≤ weights.length := by
    simp [weights]
    omega
  have hweights : ∀ w ∈ weights, 0 ≤ w := by
    intro w hw
    rcases List.mem_ofFn.mp hw with ⟨i, rfl⟩
    exact mul_nonneg (halpha (i + 1) (by omega) (by omega))
      (le_of_lt (hgamma0 i))
  have hscale : 0 < scale := cyclicPrefixScale_pos gamma hgamma0 (l - 1)
  have hscaleEq : scale = gamma 0 * rest := by
    dsimp only [scale, rest]
    rw [show l - 1 = (l - 2) + 1 by omega]
    exact cyclicPrefixScale_succ_shift gamma (l - 2)
  have hzero : weights.prod = 0 := by
    apply List.prod_eq_zero
    apply List.mem_ofFn.mpr
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    change alpha (m - 1 + 1) * gamma (m - 1) = 0
    rw [show m - 1 + 1 = m by omega, hm0, zero_mul]
  have hrest0 : 0 ≤ rest := cyclicPrefixScale_nonneg _
    (fun i => le_of_lt (hgamma0 (i + 1))) (l - 2)
  have hrest1 : rest ≤ 1 := cyclicPrefixScale_le_one _
    (fun i => le_of_lt (hgamma0 (i + 1)))
    (fun i => le_of_lt (hgamma1 (i + 1))) (l - 2)
  have hxrow : ∀ i (hi : i < weights.length),
      x (i + 2) = weights[i] * x i - x (i + 1) := by
    intro i hi
    rw [cyclicCutWeights_getElem alpha gamma l i hi]
    exact cyclic_sector_row_to_indexed_recurrence alpha gamma z i
      (hrow i (by simpa [weights] using hi))
  have hcycleScale : cyclicPrefixScale gamma l =
      (gamma 0 * gamma (l - 1) * rest) := by
    rw [show l = (l - 1) + 1 by omega]
    simp only [cyclicPrefixScale]
    rw [show l - 1 + 1 - 1 = l - 1 by omega]
    change gamma (l - 1) * scale = gamma 0 * gamma (l - 1) * rest
    rw [hscaleEq]
    ring
  have hxend : x (weights.length + 1) =
      (gamma 0 * gamma (l - 1) * rest) * x 0 := by
    have hindex : weights.length + 1 = l := by simp [weights]; omega
    rw [hindex]
    dsimp only [x]
    rw [hreturn, hcycleScale]
    simp [cyclicPrefixScale]
  have hxwrap : alpha 0 * x weights.length = scale * (x 0 + x 1) := by
    have hindex : weights.length = l - 1 := by simp [weights]
    rw [hindex]
    dsimp only [x]
    simp only [cyclicPrefixScale]
    dsimp only [scale]
    linear_combination
      -cyclicPrefixScale gamma (l - 1) * hseam
  have hxzero := proper_vertex_signed_seam_cyclic_list_kernel_eq_zero
    weights x hlen hweights hscale hscaleEq hzero
    (le_of_lt (hgamma0 0)) (hgamma1 0)
    (le_of_lt (hgamma0 (l - 1))) (le_of_lt (hgamma1 (l - 1)))
    hrest0 hrest1 hlocal hxrow hxend hxwrap
  intro i hi
  have hbound : i ≤ weights.length + 1 := by
    have hindex : weights.length + 1 = l := by simp [weights]; omega
    rw [hindex]
    exact hi
  have hxi := hxzero i hbound
  dsimp only [x] at hxi
  exact (mul_eq_zero.mp hxi).resolve_left
    (ne_of_gt (cyclicPrefixScale_pos gamma hgamma0 i))

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- Row-normalized predecessor coefficient used by the determinant box. -/
noncomputable def forkSectorAlpha
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  -S.forkSchurPrevCoefficient weight p q e rho yw j /
    S.forkSchurSelfCoefficient weight p q e rho xf yw j

/-- Row-normalized forward ratio; the compiled diagonal gap puts it in
`[0,1)`. -/
noncomputable def forkSectorGamma
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  S.forkSchurNextCoefficient weight p q e rho xf j /
    S.forkSchurSelfCoefficient weight p q e rho xf yw j

noncomputable def forkSectorMatrix
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ) :
    Matrix (Fin l) (Fin l) ℝ :=
  cyclicSectorMatrix S.step
    (S.forkSectorAlpha weight p q e rho xf yw)
    (S.forkSectorGamma weight p q e rho xf yw)

/-- A kernel row read in any rotated paper order has literal predecessor and
successor indices `k` and `k+2`. -/
theorem forkSectorMatrix_indexed_row [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (start : Fin l) (z : Fin l → ℝ)
    (hkernel : Matrix.mulVec
      (S.forkSectorMatrix weight p q e rho xf yw) z = 0)
    (k : ℕ) :
    (-S.forkSectorAlpha weight p q e rho xf yw
          (S.cyclicIndexFrom start (k + 1))) *
        z (S.cyclicIndexFrom start k) +
      z (S.cyclicIndexFrom start (k + 1)) +
      S.forkSectorGamma weight p q e rho xf yw
          (S.cyclicIndexFrom start (k + 1)) *
        z (S.cyclicIndexFrom start (k + 2)) = 0 := by
  have hr := congrFun hkernel (S.cyclicIndexFrom start (k + 1))
  change Matrix.mulVec
    (cyclicSectorMatrix S.step
      (S.forkSectorAlpha weight p q e rho xf yw)
      (S.forkSectorGamma weight p q e rho xf yw)) z
        (S.cyclicIndexFrom start (k + 1)) = 0 at hr
  rw [cyclicSectorMatrix_mulVec_apply] at hr
  have hprev :
      S.step.symm (S.cyclicIndexFrom start (k + 1)) =
        S.cyclicIndexFrom start k := by
    rw [← S.step_cyclicIndexFrom start k, S.step.symm_apply_apply]
  have hnext :
      S.step (S.cyclicIndexFrom start (k + 1)) =
        S.cyclicIndexFrom start (k + 2) := by
    simpa [Nat.add_assoc] using S.step_cyclicIndexFrom start (k + 1)
  simpa [hprev, hnext] using hr

/-- The literal cyclic-sector kernel therefore produces the exact scaled
continuant recurrence along every rotated paper enumeration. -/
theorem forkSectorMatrix_indexed_recurrence [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (start : Fin l) (z : Fin l → ℝ)
    (hkernel : Matrix.mulVec
      (S.forkSectorMatrix weight p q e rho xf yw) z = 0)
    (k : ℕ) :
    let idx := S.cyclicIndexFrom start
    let alpha : ℕ → ℝ := fun i =>
      S.forkSectorAlpha weight p q e rho xf yw (idx i)
    let gamma : ℕ → ℝ := fun i =>
      S.forkSectorGamma weight p q e rho xf yw (idx i)
    let x : ℕ → ℝ := fun i => cyclicPrefixScale gamma i * z (idx i)
    x (k + 2) = (alpha (k + 1) * gamma k) * x k - x (k + 1) := by
  dsimp only
  exact cyclic_sector_row_to_indexed_recurrence
    (fun i => S.forkSectorAlpha weight p q e rho xf yw
      (S.cyclicIndexFrom start i))
    (fun i => S.forkSectorGamma weight p q e rho xf yw
      (S.cyclicIndexFrom start i))
    (fun i => z (S.cyclicIndexFrom start i)) k
    (S.forkSectorMatrix_indexed_row weight p q e rho xf yw start z hkernel k)

/-- Cyclic-order wrapper of the natural proper-cut theorem for arbitrary
three-term coefficients.  This is used for determinant-box edge matrices,
whose predecessor coefficients are vertex/interpolation values rather than
the final source coefficients. -/
theorem cyclicSectorMatrix_kernel_eq_zero_of_proper_cut [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (alpha gamma : Fin l → ℝ)
    (seam : Fin l) (missingIndex : ℕ)
    (hmissingIndex0 : 1 ≤ missingIndex)
    (hmissingIndex1 : missingIndex < l)
    (hgamma : ∀ a, 0 < gamma a ∧ gamma a < 1)
    (halphaOrdinary : ∀ a, a ≠ seam → 0 ≤ alpha a)
    (hmissing : alpha (S.cyclicIndexFrom seam missingIndex) = 0)
    (hlocal : (-alpha seam) * gamma (S.cyclicIndexFrom seam (l - 1)) <
      1 - gamma seam)
    (z : Fin l → ℝ)
    (hkernel : Matrix.mulVec (cyclicSectorMatrix S.step alpha gamma) z = 0) :
    z = 0 := by
  let idx := S.cyclicIndexFrom seam
  let an : ℕ → ℝ := fun i => alpha (idx i)
  let gn : ℕ → ℝ := fun i => gamma (idx i)
  let zn : ℕ → ℝ := fun i => z (idx i)
  have hidxl : idx l = seam := S.cyclicIndexFrom_length seam
  have hidxplus : idx (l + 1) = idx 1 := by
    calc
      idx (l + 1) = S.step (idx l) :=
        (S.step_cyclicIndexFrom seam l).symm
      _ = S.step seam := by rw [hidxl]
      _ = idx 1 := by simpa using S.step_cyclicIndexFrom seam 0
  have han : ∀ i, 1 ≤ i → i < l → 0 ≤ an i := by
    intro i hi0 hi1
    apply halphaOrdinary
    intro heq
    have hfin : Fin.ofNat l i = 0 := by
      apply (S.cyclicOrderFrom seam).injective
      simpa [idx, cyclicIndexFrom] using heq
    have hv := congrArg Fin.val hfin
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi1] at hv
    omega
  have hrow : ∀ k, k < l - 1 →
      (-an (k + 1)) * zn k + zn (k + 1) + gn (k + 1) * zn (k + 2) = 0 := by
    intro k hk
    have hr := congrFun hkernel (idx (k + 1))
    rw [cyclicSectorMatrix_mulVec_apply] at hr
    have hprev : S.step.symm (idx (k + 1)) = idx k := by
      dsimp only [idx]
      rw [← S.step_cyclicIndexFrom seam k, S.step.symm_apply_apply]
    have hnext : S.step (idx (k + 1)) = idx (k + 2) := by
      dsimp only [idx]
      simpa [Nat.add_assoc] using S.step_cyclicIndexFrom seam (k + 1)
    simpa [an, gn, zn, hprev, hnext] using hr
  have hreturn : zn l = zn 0 := by
    dsimp only [zn, idx]
    rw [S.cyclicIndexFrom_length, S.cyclicIndexFrom_zero]
  have hseam : (-an 0) * zn (l - 1) + zn 0 + gn 0 * zn 1 = 0 := by
    have hr := congrFun hkernel seam
    rw [cyclicSectorMatrix_mulVec_apply] at hr
    have hpred : S.step.symm seam = idx (l - 1) := by
      have hs : S.step (idx (l - 1)) = seam := by
        dsimp only [idx]
        rw [S.step_cyclicIndexFrom, show l - 1 + 1 = l by omega,
          S.cyclicIndexFrom_length]
      rw [← hs, S.step.symm_apply_apply]
    have hnext : S.step seam = idx 1 := by
      dsimp only [idx]
      simpa using S.step_cyclicIndexFrom seam 0
    simpa [an, gn, zn, idx, hpred, hnext] using hr
  have hlocal' : (-an 0) * gn (l - 1) < 1 - gn 0 := by
    simpa [an, gn, idx] using hlocal
  have hzn := proper_cut_indexed_cyclic_kernel_eq_zero l hl an gn zn
    (fun i => (hgamma (idx i)).1) (fun i => (hgamma (idx i)).2)
    han ⟨missingIndex, hmissingIndex0, hmissingIndex1, hmissing⟩
    hlocal' hrow hreturn hseam
  funext a
  let i : Fin l := (S.cyclicOrderFrom seam).symm a
  have hidx : idx i.val = a := by
    dsimp only [idx, cyclicIndexFrom]
    have hfin : Fin.ofNat l i.val = i := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [hfin]
    exact (S.cyclicOrderFrom seam).apply_symm_apply a
  have hz := hzn i.val (Nat.le_of_lt i.isLt)
  simpa [zn, hidx] using hz

/-- The comparison-vector upper matrix with the signed seam cut to zero has
positive determinant.  Along the full ordinary-column cube the cut seam is a
fixed missing port; choosing the next row as an artificial seam makes every
remaining predecessor coefficient nonnegative and the local inequality
automatic. -/
theorem cyclicSectorMatrix_upper_update_seam_zero_pos [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (gamma v : Fin l → ℝ) (seam : Fin l)
    (hgamma : ∀ a, 0 < gamma a ∧ gamma a < 1)
    (hv : ∀ a, 0 < v a) :
    0 < (cyclicSectorMatrix S.step
      (Function.update (cyclicSectorUpper S.step gamma v) seam 0) gamma).det := by
  let upper := cyclicSectorUpper S.step gamma v
  let hiAlpha := Function.update upper seam 0
  let lo := cyclicSectorMatrix S.step (fun _ => 0) gamma
  let hi := cyclicSectorMatrix S.step hiAlpha gamma
  let artificialSeam := S.step seam
  have hstep : ∀ a, a ≠ S.step a := S.ne_step_of_two_le (by omega)
  have hupper0 : ∀ a, 0 ≤ upper a := fun a => le_of_lt
    (cyclicSectorUpper_pos S.step gamma v
      (fun i => le_of_lt (hgamma i).1) hv a)
  have hhi0 : ∀ a, 0 ≤ hiAlpha a := by
    intro a
    by_cases ha : a = seam
    · simp [hiAlpha, ha]
    · simp [hiAlpha, ha, hupper0 a]
  have hbase : 0 < lo.det := by
    exact det_cyclicSectorMatrix_zero_alpha_pos S.step gamma hstep
      (fun a => le_of_lt (hgamma a).1) (fun a => (hgamma a).2)
  have hseamNe : seam ≠ artificialSeam := S.ne_step_of_two_le (by omega) seam
  obtain ⟨missingIndex, hmissing0, hmissing1, hmissingEq⟩ :=
    S.exists_cyclicIndexFrom_eq_of_ne artificialSeam seam hseamNe
  have hedge : ∀ (s : Finset (Fin l)) (i : Fin l), i ∉ s →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0 := by
    intro s i his t ht0 ht1
    let edgeAlpha : Fin l → ℝ := fun r => if r = S.step i then
      t * hiAlpha r
    else if S.step.symm r ∈ s then hiAlpha r else 0
    have hmatrix :
        (columnVertexMatrix lo hi s).updateCol i
          (t • (fun r => hi r i) +
            (1 - t) • (fun r => lo r i)) =
          cyclicSectorMatrix S.step edgeAlpha gamma := by
      dsimp only [lo, hi]
      rw [columnVertexMatrix_updateCol_cyclicSectorMatrix]
      congr 1
      funext r
      simp [edgeAlpha]
    have hedgeAlpha0 : ∀ a, 0 ≤ edgeAlpha a := by
      intro a
      by_cases hai : a = S.step i
      · dsimp only [edgeAlpha]
        rw [ite_eq_left hai]
        exact mul_nonneg ht0 (hhi0 _)
      · by_cases has : S.step.symm a ∈ s
        · simp [edgeAlpha, hai, has, hhi0 a]
        · simp [edgeAlpha, hai, has]
    have hmissing : edgeAlpha
        (S.cyclicIndexFrom artificialSeam missingIndex) = 0 := by
      rw [hmissingEq]
      simp [edgeAlpha, hiAlpha]
    have hlocal : (-edgeAlpha artificialSeam) *
          gamma (S.cyclicIndexFrom artificialSeam (l - 1)) <
        1 - gamma artificialSeam := by
      have hp : 0 ≤ edgeAlpha artificialSeam *
          gamma (S.cyclicIndexFrom artificialSeam (l - 1)) :=
        mul_nonneg (hedgeAlpha0 artificialSeam)
          (le_of_lt (hgamma _).1)
      nlinarith [(hgamma artificialSeam).2]
    rw [hmatrix]
    exact det_ne_zero_of_mulVec_kernel_eq_zero _ (fun z hz =>
      S.cyclicSectorMatrix_kernel_eq_zero_of_proper_cut hl edgeAlpha gamma
        artificialSeam missingIndex hmissing0 hmissing1 hgamma
        (fun a _ => hedgeAlpha0 a) hmissing hlocal z hz)
  have hall := columnVertexMatrix_det_pos_of_edge_nonsingular lo hi
    hbase hedge Finset.univ (Finset.subset_univ _)
  have hallEq : columnVertexMatrix lo hi Finset.univ = hi := by
    ext r c
    simp [columnVertexMatrix]
  rw [hallEq] at hall
  simpa [hi, hiAlpha, upper] using hall

/-- A single possibly signed predecessor coefficient can be switched on from
the all-cut matrix as long as its local two-edge minor stays positive.  The
next predecessor port remains cut throughout the homotopy, so the natural
proper-cut continuant excludes a kernel on the whole segment. -/
theorem cyclicSectorMatrix_single_signed_seam_pos [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (gamma : Fin l → ℝ) (seam : Fin l) (a : ℝ)
    (hgamma : ∀ r, 0 < gamma r ∧ gamma r < 1)
    (hlocal : (-a) * gamma (S.cyclicIndexFrom seam (l - 1)) <
      1 - gamma seam) :
    0 < (cyclicSectorMatrix S.step
      (Function.update (fun _ => 0) seam a) gamma).det := by
  let zeroAlpha : Fin l → ℝ := fun _ => 0
  let oneAlpha := Function.update zeroAlpha seam a
  let Mzero := cyclicSectorMatrix S.step zeroAlpha gamma
  let Mone := cyclicSectorMatrix S.step oneAlpha gamma
  let frozen := S.step.symm seam
  have hstep : seam ≠ S.step seam := S.ne_step_of_two_le (by omega) seam
  have hbase : 0 < Mzero.det := by
    exact det_cyclicSectorMatrix_zero_alpha_pos S.step gamma
      (S.ne_step_of_two_le (by omega))
      (fun r => le_of_lt (hgamma r).1) (fun r => (hgamma r).2)
  have hsegment : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (Mzero.updateCol frozen
        (t • (fun r => Mone r frozen) +
          (1 - t) • (fun r => Mzero r frozen))).det ≠ 0 := by
    intro t ht0 ht1
    let edgeAlpha : Fin l → ℝ := fun r =>
      if r = seam then t * oneAlpha r else 0
    have hmatrix : Mzero.updateCol frozen
          (t • (fun r => Mone r frozen) +
            (1 - t) • (fun r => Mzero r frozen)) =
        cyclicSectorMatrix S.step edgeAlpha gamma := by
      have h := columnVertexMatrix_updateCol_cyclicSectorMatrix S.step
        zeroAlpha oneAlpha gamma (∅ : Finset (Fin l)) frozen t
      have hvtx : columnVertexMatrix
          (cyclicSectorMatrix S.step zeroAlpha gamma)
          (cyclicSectorMatrix S.step oneAlpha gamma) ∅ =
          cyclicSectorMatrix S.step zeroAlpha gamma := by
        ext r c
        simp [columnVertexMatrix]
      rw [hvtx] at h
      simpa [Mzero, Mone, frozen, zeroAlpha, edgeAlpha] using h
    have hedge0 : ∀ r, r ≠ seam → 0 ≤ edgeAlpha r := by
      intro r hr
      simp [edgeAlpha, hr]
    have hmissing : edgeAlpha (S.cyclicIndexFrom seam 1) = 0 := by
      have hidx : S.cyclicIndexFrom seam 1 = S.step seam := by
        simpa using (S.step_cyclicIndexFrom seam 0).symm
      rw [hidx]
      simp [edgeAlpha, Ne.symm hstep]
    have hlocalT : (-edgeAlpha seam) *
          gamma (S.cyclicIndexFrom seam (l - 1)) < 1 - gamma seam := by
      have hgprev := (hgamma (S.cyclicIndexFrom seam (l - 1))).1
      have hgseam := (hgamma seam).2
      simp only [edgeAlpha, ite_eq_left rfl, oneAlpha, Function.update_self]
      by_cases ha0 : 0 ≤ a
      · have : (-t * a) * gamma (S.cyclicIndexFrom seam (l - 1)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hgprev)
        nlinarith
      · have hat : -t * a ≤ -a := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hat (le_of_lt hgprev)]
    rw [hmatrix]
    exact det_ne_zero_of_mulVec_kernel_eq_zero _ (fun z hz =>
      S.cyclicSectorMatrix_kernel_eq_zero_of_proper_cut hl edgeAlpha gamma
        seam 1 (by omega) (by omega) hgamma hedge0 hmissing hlocalT z hz)
  have hone : 0 < (Mzero.updateCol frozen (fun r => Mone r frozen)).det :=
    det_updateCol_pos_of_segment_nonsingular Mzero frozen
      (fun r => Mone r frozen) hbase hsegment
  have hupdate : Mzero.updateCol frozen (fun r => Mone r frozen) = Mone := by
    ext r c
    by_cases hc : c = frozen
    · subst c
      simp
    · rw [Matrix.updateCol_ne hc]
      by_cases hpred : c = S.step.symm r
      · have hrs : r ≠ seam := by
          intro hrs
          subst r
          apply hc
          simpa [frozen] using hpred
        simp [Mzero, Mone, cyclicSectorMatrix, oneAlpha, zeroAlpha,
          hpred, hrs]
      · simp [Mzero, Mone, cyclicSectorMatrix, hpred]
  rw [hupdate] at hone
  simpa [Mone, oneAlpha, zeroAlpha] using hone

/-- Full signed-seam determinant criterion.  The exceptional coefficient is
first installed along the one-column proper-cut homotopy.  It is then frozen
while all ordinary columns traverse their comparison box; every nonterminal
edge retains another missing ordinary column, so the same continuant theorem
propagates the positive sign to every frozen-box vertex. -/
theorem cyclicSectorMatrix_signed_seam_pos [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (alpha gamma v : Fin l → ℝ) (seam : Fin l)
    (hgamma : ∀ r, 0 < gamma r ∧ gamma r < 1)
    (hv : ∀ r, 0 < v r)
    (halphaOrdinary : ∀ r, r ≠ seam → 0 ≤ alpha r)
    (halphaUpper : ∀ r,
      alpha r < cyclicSectorUpper S.step gamma v r)
    (hlocal : (-alpha seam) *
        gamma (S.cyclicIndexFrom seam (l - 1)) < 1 - gamma seam) :
    0 < (cyclicSectorMatrix S.step alpha gamma).det := by
  let upper := cyclicSectorUpper S.step gamma v
  let loAlpha := Function.update (fun _ : Fin l => (0 : ℝ)) seam (alpha seam)
  let hiAlpha := Function.update upper seam (alpha seam)
  let lo := cyclicSectorMatrix S.step loAlpha gamma
  let hi := cyclicSectorMatrix S.step hiAlpha gamma
  let frozen := S.step.symm seam
  have hupperPos : ∀ r, 0 < upper r := fun r =>
    cyclicSectorUpper_pos S.step gamma v
      (fun i => le_of_lt (hgamma i).1) hv r
  have hempty : 0 < lo.det := by
    exact S.cyclicSectorMatrix_single_signed_seam_pos hl gamma seam
      (alpha seam) hgamma hlocal
  have hzero := S.cyclicSectorMatrix_upper_update_seam_zero_pos hl gamma v
    seam hgamma hv
  have hall : 0 < hi.det := by
    have h := det_cyclicSectorMatrix_update_seam_pos S.step gamma v seam
      (alpha seam) hv (hupperPos seam) (halphaUpper seam) hzero
    simpa [hi, hiAlpha, upper] using h
  have hfrozen : ∀ r, lo r frozen = hi r frozen := by
    intro r
    by_cases hrs : r = seam
    · subst r
      simp [lo, hi, loAlpha, hiAlpha, frozen, cyclicSectorMatrix]
    · have hpred : frozen ≠ S.step.symm r := by
        intro h
        apply hrs
        exact S.step.symm.injective h.symm
      simp [lo, hi, loAlpha, hiAlpha, frozen, cyclicSectorMatrix, hpred]
  have hedge : ∀ (s : Finset (Fin l)) (i : Fin l), i ∉ s →
      (∃ c, c ≠ frozen ∧ c ∉ insert i s) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((columnVertexMatrix lo hi s).updateCol i
        (t • (fun r => hi r i) +
          (1 - t) • (fun r => lo r i))).det ≠ 0 := by
    intro s i his hmissingColumn t ht0 ht1
    let edgeAlpha : Fin l → ℝ := fun r => if r = S.step i then
      t * hiAlpha r + (1 - t) * loAlpha r
    else if S.step.symm r ∈ s then hiAlpha r else loAlpha r
    have hmatrix :
        (columnVertexMatrix lo hi s).updateCol i
          (t • (fun r => hi r i) +
            (1 - t) • (fun r => lo r i)) =
          cyclicSectorMatrix S.step edgeAlpha gamma := by
      dsimp only [lo, hi]
      rw [columnVertexMatrix_updateCol_cyclicSectorMatrix]
    have hedge0 : ∀ r, r ≠ seam → 0 ≤ edgeAlpha r := by
      intro r hrs
      have hu0 : 0 ≤ upper r := le_of_lt (hupperPos r)
      by_cases hri : r = S.step i
      · subst r
        simp only [edgeAlpha, ite_eq_left rfl, hiAlpha, loAlpha,
          Function.update_of_ne hrs, mul_zero, add_zero]
        exact mul_nonneg ht0 hu0
      · by_cases hrsMem : S.step.symm r ∈ s
        · simp [edgeAlpha, hri, hrsMem, hiAlpha, hrs, hu0]
        · simp [edgeAlpha, hri, hrsMem, loAlpha, hrs]
    obtain ⟨c, hcfrozen, hcinsert⟩ := hmissingColumn
    have hci : c ≠ i := by
      simpa using (fun h : c = i => hcinsert (by simp [h]))
    have hcs : c ∉ s := by
      exact fun h => hcinsert (by simp [h])
    have htarget : S.step c ≠ seam := by
      intro h
      apply hcfrozen
      apply S.step.injective
      simpa [frozen] using h
    obtain ⟨missingIndex, hmissing0, hmissing1, hmissingEq⟩ :=
      S.exists_cyclicIndexFrom_eq_of_ne seam (S.step c) htarget
    have hmissing : edgeAlpha
        (S.cyclicIndexFrom seam missingIndex) = 0 := by
      rw [hmissingEq]
      have hnext : S.step c ≠ S.step i := fun h => hci (S.step.injective h)
      simp [edgeAlpha, hnext, hcs, loAlpha, htarget]
    have hedgeSeam : edgeAlpha seam = alpha seam := by
      by_cases hri : seam = S.step i
      · simp [edgeAlpha, hri, hiAlpha, loAlpha]
        ring
      · by_cases hmem : S.step.symm seam ∈ s
        · simp [edgeAlpha, hri, hmem, hiAlpha]
        · simp [edgeAlpha, hri, hmem, loAlpha]
    have hlocalEdge : (-edgeAlpha seam) *
          gamma (S.cyclicIndexFrom seam (l - 1)) < 1 - gamma seam := by
      rw [hedgeSeam]
      exact hlocal
    rw [hmatrix]
    exact det_ne_zero_of_mulVec_kernel_eq_zero _ (fun z hz =>
      S.cyclicSectorMatrix_kernel_eq_zero_of_proper_cut hl edgeAlpha gamma
        seam missingIndex hmissing0 hmissing1 hgamma hedge0 hmissing
        hlocalEdge z hz)
  have hvertices := columnVertexMatrix_det_pos_of_frozen_edge_nonsingular
    lo hi frozen hfrozen hempty hall hedge
  let coord : Fin l → ℝ := fun j => if j = frozen then 0 else
    alpha (S.step j) / upper (S.step j)
  have hcoord0 : ∀ j, 0 ≤ coord j := by
    intro j
    by_cases hj : j = frozen
    · simp [coord, hj]
    · have hrow : S.step j ≠ seam := by
        intro h
        apply hj
        apply S.step.injective
        simpa [frozen] using h
      simp [coord, hj]
      exact div_nonneg (halphaOrdinary (S.step j) hrow)
        (le_of_lt (hupperPos (S.step j)))
  have hcoord1 : ∀ j, coord j < 1 := by
    intro j
    by_cases hj : j = frozen
    · simp [coord, hj]
    · simp [coord, hj]
      exact (div_lt_one (hupperPos (S.step j))).mpr
        (halphaUpper (S.step j))
  have halpha : ∀ j, alpha (S.step j) =
      coord j * hiAlpha (S.step j) +
        (1 - coord j) * loAlpha (S.step j) := by
    intro j
    by_cases hj : j = frozen
    · subst j
      simp [coord, frozen, hiAlpha, loAlpha]
    · have hrow : S.step j ≠ seam := by
        intro h
        apply hj
        apply S.step.injective
        simpa [frozen] using h
      simp [coord, hj, hiAlpha, loAlpha, hrow]
      field_simp [ne_of_gt (hupperPos (S.step j))]
  apply det_cyclicSectorMatrix_pos_of_frozen_vertex_certificate S.step
    alpha gamma loAlpha hiAlpha coord halpha hcoord0 hcoord1
  · intro s hs
    exact le_of_lt (hvertices s hs)
  · exact hempty

/-- Source-matrix instantiation of the proper-cut continuant theorem.  The
only exceptional predecessor row is chosen as `seam`; any vanished ordinary
predecessor port supplies the zero correction somewhere on the complementary
path. -/
theorem forkSectorMatrix_kernel_eq_zero_of_proper_cut [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (seam : Fin l) (missingIndex : ℕ)
    (hmissingIndex0 : 1 ≤ missingIndex)
    (hmissingIndex1 : missingIndex < l)
    (hgamma : ∀ a,
      0 < S.forkSectorGamma weight p q e rho xf yw a ∧
      S.forkSectorGamma weight p q e rho xf yw a < 1)
    (halphaOrdinary : ∀ a, a ≠ seam →
      0 ≤ S.forkSectorAlpha weight p q e rho xf yw a)
    (hmissing : S.forkSectorAlpha weight p q e rho xf yw
      (S.cyclicIndexFrom seam missingIndex) = 0)
    (hlocal :
      (-S.forkSectorAlpha weight p q e rho xf yw seam) *
          S.forkSectorGamma weight p q e rho xf yw
            (S.cyclicIndexFrom seam (l - 1)) <
        1 - S.forkSectorGamma weight p q e rho xf yw seam)
    (z : Fin l → ℝ)
    (hkernel : Matrix.mulVec
      (S.forkSectorMatrix weight p q e rho xf yw) z = 0) :
    z = 0 := by
  let idx := S.cyclicIndexFrom seam
  let alpha : ℕ → ℝ := fun i =>
    S.forkSectorAlpha weight p q e rho xf yw (idx i)
  let gamma : ℕ → ℝ := fun i =>
    S.forkSectorGamma weight p q e rho xf yw (idx i)
  let zn : ℕ → ℝ := fun i => z (idx i)
  have hidxl : idx l = seam := S.cyclicIndexFrom_length seam
  have hidxplus : idx (l + 1) = idx 1 := by
    calc
      idx (l + 1) = S.step (idx l) := by
        exact (S.step_cyclicIndexFrom seam l).symm
      _ = S.step seam := by rw [hidxl]
      _ = idx 1 := by
        simpa using S.step_cyclicIndexFrom seam 0
  have halpha : ∀ i, 1 ≤ i → i < l → 0 ≤ alpha i := by
    intro i hi0 hi1
    apply halphaOrdinary
    intro heq
    have hfin : Fin.ofNat l i = 0 := by
      apply (S.cyclicOrderFrom seam).injective
      simpa [idx, cyclicIndexFrom] using heq
    have hv := congrArg Fin.val hfin
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi1] at hv
    omega
  have hrow : ∀ k, k < l - 1 →
      (-alpha (k + 1)) * zn k + zn (k + 1) +
        gamma (k + 1) * zn (k + 2) = 0 := by
    intro k hk
    exact S.forkSectorMatrix_indexed_row weight p q e rho xf yw
      seam z hkernel k
  have hreturn : zn l = zn 0 := by
    dsimp only [zn, idx]
    rw [S.cyclicIndexFrom_length, S.cyclicIndexFrom_zero]
  have hseam : (-alpha 0) * zn (l - 1) + zn 0 + gamma 0 * zn 1 = 0 := by
    have hr := S.forkSectorMatrix_indexed_row weight p q e rho xf yw
      seam z hkernel (l - 1)
    have hidxplus' : S.cyclicIndexFrom seam (l + 1) =
        S.cyclicIndexFrom seam 1 := hidxplus
    dsimp only [alpha, gamma, zn, idx]
    rw [show l - 1 + 1 = l by omega,
      show l - 1 + 2 = l + 1 by omega,
      S.cyclicIndexFrom_length seam, hidxplus'] at hr
    simpa using hr
  have hlocal' : (-alpha 0) * gamma (l - 1) < 1 - gamma 0 := by
    simpa [alpha, gamma, idx] using hlocal
  have hzn := proper_cut_indexed_cyclic_kernel_eq_zero l hl alpha gamma zn
    (fun i => (hgamma (idx i)).1) (fun i => (hgamma (idx i)).2)
    halpha ⟨missingIndex, hmissingIndex0, hmissingIndex1, hmissing⟩
    hlocal' hrow hreturn hseam
  funext a
  let i : Fin l := (S.cyclicOrderFrom seam).symm a
  have hidx : idx i.val = a := by
    dsimp only [idx, cyclicIndexFrom]
    have hfin : Fin.ofNat l i.val = i := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [hfin]
    exact (S.cyclicOrderFrom seam).apply_symm_apply a
  have hz := hzn i.val (Nat.le_of_lt i.isLt)
  simpa [zn, hidx] using hz

theorem fork_sector_row
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (z : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hrow :
      S.forkSchurPrevCoefficient weight p q e rho yw j *
          z (S.step.symm j) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw j * z j +
        S.forkSchurNextCoefficient weight p q e rho xf j *
          z (S.step j) = 0) :
    (-S.forkSectorAlpha weight p q e rho xf yw j) *
          z (S.step.symm j) + z j +
        S.forkSectorGamma weight p q e rho xf yw j * z (S.step j) = 0 := by
  unfold forkSectorAlpha forkSectorGamma
  have hne : S.forkSchurSelfCoefficient weight p q e rho xf yw j ≠ 0 :=
    ne_of_gt hself
  field_simp [hne]
  linear_combination hrow

theorem forkSectorGamma_mem_unitInterval
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hnext : 0 ≤ S.forkSchurNextCoefficient weight p q e rho xf j)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hgap : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j -
      S.forkSchurNextCoefficient weight p q e rho xf j) :
    0 ≤ S.forkSectorGamma weight p q e rho xf yw j ∧
      S.forkSectorGamma weight p q e rho xf yw j < 1 := by
  exact forward_ratio_mem_unitInterval hself hnext hgap

theorem forkSectorAlpha_nonneg
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hprev : S.forkSchurPrevCoefficient weight p q e rho yw j ≤ 0)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j) :
    0 ≤ S.forkSectorAlpha weight p q e rho xf yw j := by
  unfold forkSectorAlpha
  exact div_nonneg (neg_nonneg.mpr hprev) (le_of_lt hself)

/-- A strict Schur residual on the positive source current places the raw
row-normalized predecessor coefficient strictly below the comparison-vector
upper endpoint used by `cyclicSectorUpper`. -/
theorem forkSectorAlpha_lt_upper
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hJprev : 0 < J (S.step.symm j))
    (hresidual : 0 <
      S.forkSchurPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw j * J j +
        S.forkSchurNextCoefficient weight p q e rho xf j * J (S.step j)) :
    S.forkSectorAlpha weight p q e rho xf yw j <
      cyclicSectorUpper S.step
        (S.forkSectorGamma weight p q e rho xf yw) J j := by
  unfold forkSectorAlpha forkSectorGamma cyclicSectorUpper
  apply (lt_div_iff₀ hJprev).2
  calc
    (-S.forkSchurPrevCoefficient weight p q e rho yw j /
          S.forkSchurSelfCoefficient weight p q e rho xf yw j) *
        J (S.step.symm j) =
        (-S.forkSchurPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j)) /
            S.forkSchurSelfCoefficient weight p q e rho xf yw j := by ring
    _ < J j +
        (S.forkSchurNextCoefficient weight p q e rho xf j /
          S.forkSchurSelfCoefficient weight p q e rho xf yw j) *
            J (S.step j) := by
      apply (div_lt_iff₀ hself).2
      have hcancel :
          (J j +
              (S.forkSchurNextCoefficient weight p q e rho xf j /
                S.forkSchurSelfCoefficient weight p q e rho xf yw j) *
                  J (S.step j)) *
              S.forkSchurSelfCoefficient weight p q e rho xf yw j =
            S.forkSchurSelfCoefficient weight p q e rho xf yw j * J j +
              S.forkSchurNextCoefficient weight p q e rho xf j *
                J (S.step j) := by
        field_simp [ne_of_gt hself]
      rw [hcancel]
      nlinarith

/-- Positive-current normalization of the genuine predecessor Schur port. -/
noncomputable def forkNormalizedAlpha
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l) : ℝ :=
  -(S.forkSchurPrevCoefficient weight p q e rho yw j *
      J (S.step.symm j)) /
    (S.forkSchurSelfCoefficient weight p q e rho xf yw j * J j)

/-- Positive-current normalization of the genuine successor Schur port. -/
noncomputable def forkNormalizedGamma
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l) : ℝ :=
  (S.forkSchurNextCoefficient weight p q e rho xf j * J (S.step j)) /
    (S.forkSchurSelfCoefficient weight p q e rho xf yw j * J j)

noncomputable def forkNormalizedSectorMatrix
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  cyclicSectorMatrix S.step
    (S.forkNormalizedAlpha weight p q e rho xf yw J)
    (S.forkNormalizedGamma weight p q e rho xf yw J)

/-- A literal reconstructed fork Schur row is exactly the corresponding row
of the normalized cyclic-sector matrix after gauging by the positive source
current. -/
theorem fork_normalized_sector_row
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J z : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hJ : 0 < J j)
    (hrow :
      S.forkSchurPrevCoefficient weight p q e rho yw j *
          (J (S.step.symm j) * z (S.step.symm j)) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw j *
          (J j * z j) +
        S.forkSchurNextCoefficient weight p q e rho xf j *
          (J (S.step j) * z (S.step j)) = 0) :
    (-S.forkNormalizedAlpha weight p q e rho xf yw J j) *
          z (S.step.symm j) + z j +
        S.forkNormalizedGamma weight p q e rho xf yw J j *
          z (S.step j) = 0 := by
  exact raw_three_term_to_normalized_sector hself hJ hrow

/-- Rowwise normalized Schur equations assemble exactly into one matrix
kernel equation. -/
theorem forkNormalizedSectorMatrix_mulVec_eq_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J z : Fin l → ℝ)
    (hrow : ∀ j,
      (-S.forkNormalizedAlpha weight p q e rho xf yw J j) *
            z (S.step.symm j) + z j +
          S.forkNormalizedGamma weight p q e rho xf yw J j *
            z (S.step j) = 0) :
    Matrix.mulVec
      (S.forkNormalizedSectorMatrix weight p q e rho xf yw J) z = 0 := by
  funext j
  change Matrix.mulVec
    (cyclicSectorMatrix S.step
      (S.forkNormalizedAlpha weight p q e rho xf yw J)
      (S.forkNormalizedGamma weight p q e rho xf yw J)) z j = 0
  rw [cyclicSectorMatrix_mulVec_apply]
  exact hrow j

/-- The literal positive-current residual is precisely the strict upper-box
inequality for the normalized predecessor coefficient. -/
theorem forkNormalizedAlpha_lt_upper
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hJ : 0 < J j)
    (hresidual : 0 <
      S.forkSchurPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw j * J j +
        S.forkSchurNextCoefficient weight p q e rho xf j * J (S.step j)) :
    S.forkNormalizedAlpha weight p q e rho xf yw J j <
      1 + S.forkNormalizedGamma weight p q e rho xf yw J j := by
  exact normalized_sector_bound_of_residual hself hJ hresidual

theorem forkNormalizedAlpha_nonneg
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hprev : S.forkSchurPrevCoefficient weight p q e rho yw j ≤ 0)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hJprev : 0 < J (S.step.symm j)) (hJ : 0 < J j) :
    0 ≤ S.forkNormalizedAlpha weight p q e rho xf yw J j := by
  exact (normalized_sector_coefficients_nonneg hprev (le_refl 0)
    hself hJprev hJ hJ).1

theorem forkNormalizedGamma_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hnext : 0 < S.forkSchurNextCoefficient weight p q e rho xf j)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hJ : 0 < J j) (hJnext : 0 < J (S.step j)) :
    0 < S.forkNormalizedGamma weight p q e rho xf yw J j := by
  unfold forkNormalizedGamma
  exact div_pos (mul_pos hnext hJnext) (mul_pos hself hJ)

/-- The genuine neighboring-fork minor is exactly the normalized seam
comparison used by the parity-free proper-edge closure. -/
theorem forkSchur_local_margin_normalized
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hself : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw
      (S.step j))
    (hselfPrev : 0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j)
    (hlocal :
      S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
          S.forkSchurNextCoefficient weight p q e rho xf j <
        (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
            S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
          S.forkSchurSelfCoefficient weight p q e rho xf yw j) :
    (S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) /
        S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j)) *
      (S.forkSchurNextCoefficient weight p q e rho xf j /
        S.forkSchurSelfCoefficient weight p q e rho xf yw j) <
      1 - S.forkSchurNextCoefficient weight p q e rho xf (S.step j) /
        S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) := by
  exact raw_two_edge_margin_implies_normalized_wrap hself hselfPrev hlocal

/-- The literal cyclic Schur rows satisfy the exact combined cone isolated by
the numerical falsifier ladder.  All ordinary predecessor ports are
nonnegative after row normalization, every predecessor port (including the
unique signed seam) lies strictly below its comparison-vector upper value,
the forward ratios lie in `[0,1)`, and the genuine neighboring-fork minor is
precisely the normalized seam inequality. -/
theorem forkSector_combined_cone
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hJ : ∀ a, 0 < J a)
    (hprevOrdinary : ∀ a, a ≠ S.step seamPred →
      S.forkSchurPrevCoefficient weight p q e rho yw a ≤ 0)
    (hresidual : ∀ a, 0 <
      S.forkSchurPrevCoefficient weight p q e rho yw a *
          J (S.step.symm a) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw a * J a +
        S.forkSchurNextCoefficient weight p q e rho xf a * J (S.step a))
    (hlocal :
      S.forkSchurPrevCoefficient weight p q e rho yw (S.step seamPred) *
          S.forkSchurNextCoefficient weight p q e rho xf seamPred <
        (S.forkSchurSelfCoefficient weight p q e rho xf yw
              (S.step seamPred) -
            S.forkSchurNextCoefficient weight p q e rho xf
              (S.step seamPred)) *
          S.forkSchurSelfCoefficient weight p q e rho xf yw seamPred) :
    (∀ a, 0 ≤ S.forkSectorGamma weight p q e rho xf yw a ∧
      S.forkSectorGamma weight p q e rho xf yw a < 1) ∧
    (∀ a, a ≠ S.step seamPred →
      0 ≤ S.forkSectorAlpha weight p q e rho xf yw a) ∧
    (∀ a, S.forkSectorAlpha weight p q e rho xf yw a <
      cyclicSectorUpper S.step
        (S.forkSectorGamma weight p q e rho xf yw) J a) ∧
    (-S.forkSectorAlpha weight p q e rho xf yw (S.step seamPred)) *
        S.forkSectorGamma weight p q e rho xf yw seamPred <
      1 - S.forkSectorGamma weight p q e rho xf yw (S.step seamPred) := by
  have hsigns : ∀ a,
      0 < S.forkSchurNextCoefficient weight p q e rho xf a ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a -
        S.forkSchurNextCoefficient weight p q e rho xf a ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a ∧
      S.forkSchurNextCoefficient weight p q e rho xf a ≤
        S.forkSchurSelfCoefficient weight p q e rho xf yw a := fun a =>
    S.forkSchur_cyclic_signs weight p q e rho xf yw a hgap hp hq he hrho
      hw hunit hxf hyw
  constructor
  · intro a
    exact S.forkSectorGamma_mem_unitInterval weight p q e rho xf yw a
      (le_of_lt (hsigns a).1) (hsigns a).2.2.1 (hsigns a).2.1
  constructor
  · intro a ha
    exact S.forkSectorAlpha_nonneg weight p q e rho xf yw a
      (hprevOrdinary a ha) (hsigns a).2.2.1
  constructor
  · intro a
    exact S.forkSectorAlpha_lt_upper weight p q e rho xf yw J a
      (hsigns a).2.2.1 (hJ (S.step.symm a)) (hresidual a)
  · have hm := S.forkSchur_local_margin_normalized weight p q e rho xf yw
      seamPred (hsigns (S.step seamPred)).2.2.1
        (hsigns seamPred).2.2.1 hlocal
    unfold forkSectorAlpha forkSectorGamma
    convert hm using 1
    · ring

/-- The literal source fork-sector Schur matrix has positive determinant.
This is the source-faithful docking theorem for the signed-seam frozen-cube
criterion above. -/
theorem forkSectorMatrix_det_pos [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hJ : ∀ a, 0 < J a)
    (hprevOrdinary : ∀ a, a ≠ S.step seamPred →
      S.forkSchurPrevCoefficient weight p q e rho yw a ≤ 0)
    (hresidual : ∀ a, 0 <
      S.forkSchurPrevCoefficient weight p q e rho yw a *
          J (S.step.symm a) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw a * J a +
        S.forkSchurNextCoefficient weight p q e rho xf a * J (S.step a))
    (hlocal :
      S.forkSchurPrevCoefficient weight p q e rho yw (S.step seamPred) *
          S.forkSchurNextCoefficient weight p q e rho xf seamPred <
        (S.forkSchurSelfCoefficient weight p q e rho xf yw
              (S.step seamPred) -
            S.forkSchurNextCoefficient weight p q e rho xf
              (S.step seamPred)) *
          S.forkSchurSelfCoefficient weight p q e rho xf yw seamPred) :
    0 < (S.forkSectorMatrix weight p q e rho xf yw).det := by
  obtain ⟨hgamma0, halphaOrdinary, halphaUpper, hlocalNormalized⟩ :=
    S.forkSector_combined_cone weight p q e rho xf yw J seamPred
      hgap hp hq he hrho hw hunit hxf hyw hJ hprevOrdinary hresidual hlocal
  have hsigns : ∀ a,
      0 < S.forkSchurNextCoefficient weight p q e rho xf a ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a -
        S.forkSchurNextCoefficient weight p q e rho xf a ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a ∧
      S.forkSchurNextCoefficient weight p q e rho xf a ≤
        S.forkSchurSelfCoefficient weight p q e rho xf yw a := fun a =>
    S.forkSchur_cyclic_signs weight p q e rho xf yw a hgap hp hq he hrho
      hw hunit hxf hyw
  have hgamma : ∀ a,
      0 < S.forkSectorGamma weight p q e rho xf yw a ∧
      S.forkSectorGamma weight p q e rho xf yw a < 1 := by
    intro a
    constructor
    · unfold forkSectorGamma
      exact div_pos (hsigns a).1 (hsigns a).2.2.1
    · exact (hgamma0 a).2
  have hlocalCyclic :
      (-S.forkSectorAlpha weight p q e rho xf yw (S.step seamPred)) *
          S.forkSectorGamma weight p q e rho xf yw
            (S.cyclicIndexFrom (S.step seamPred) (l - 1)) <
        1 - S.forkSectorGamma weight p q e rho xf yw
          (S.step seamPred) := by
    rw [S.cyclicIndexFrom_pred_length (by omega), S.step.symm_apply_apply]
    exact hlocalNormalized
  simpa [forkSectorMatrix] using
    S.cyclicSectorMatrix_signed_seam_pos hl
      (S.forkSectorAlpha weight p q e rho xf yw)
      (S.forkSectorGamma weight p q e rho xf yw) J (S.step seamPred)
      hgamma hJ halphaOrdinary halphaUpper hlocalCyclic

/-- A nonsingular literal fork-sector Schur matrix kills every global current
secant kernel vector: gap rows reconstruct from the two boundary fork values,
the fork rows reduce to the sector matrix, and the killed fork values then
force every internal gap coordinate to vanish. -/
theorem globalCurrentSecantKernel_eq_zero_of_forkSector_det [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hself : ∀ a,
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a)
    (hdet : 0 < (S.forkSectorMatrix weight p q e rho xf yw).det)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    x = 0 := by
  have hrec : ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))) := by
    intro a i
    exact SourceWrapGlobalColumnClosed.internal_coordinates_eq_negative_responses_of_kernel
      (S.globalColumnClosed a) (hgap a) weight p q e rho hp hq he hrho hw
        (hunit a) x (xf a) (yw a) (hxf a) (hyw a) hker i
  have hraw := S.fork_schur_three_term_of_reconstruction hprevnext
    weight p q e rho x xf yw hrec hker
  let z : Fin l → ℝ := fun a => x (S.fork a)
  have hsector : Matrix.mulVec
      (S.forkSectorMatrix weight p q e rho xf yw) z = 0 := by
    funext a
    simpa [forkSectorMatrix, cyclicSectorMatrix_mulVec_apply] using
      S.fork_sector_row weight p q e rho xf yw z a (hself a) (hraw a)
  have hz : z = 0 := Matrix.eq_zero_of_mulVec_eq_zero (ne_of_gt hdet) hsector
  have hfork : ∀ a : Fin l, x (S.fork a) = 0 := by
    intro a
    exact congrFun hz a
  exact S.kernel_eq_zero_of_fork_coordinates_eq_zero weight p q e rho
    hp hq he hrho hw x hker hfork

/-- The strict-gap source branch is unistationary once its single signed seam
is controlled by the neighboring two-edge minor.  This theorem composes the
positive fork-sector determinant, global current-kernel reconstruction, and
the final stationary-balance recovery of concentration ratios. -/
theorem ratios_eq_one_of_strict_gap_combined_cone [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hbase : ∀ i,
      ∑ r, sourceStoich next weight back i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, sourceStoich next weight back i r *
          (rho r * p r -
            monomialRatio (sourceProductExponent next weight back) rho r * q r) =
        rho i * e i)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hJ : ∀ a, 0 < J a)
    (hprevOrdinary : ∀ a, a ≠ S.step seamPred →
      S.forkSchurPrevCoefficient weight p q e rho yw a ≤ 0)
    (hresidual : ∀ a, 0 <
      S.forkSchurPrevCoefficient weight p q e rho yw a *
          J (S.step.symm a) +
        S.forkSchurSelfCoefficient weight p q e rho xf yw a * J a +
        S.forkSchurNextCoefficient weight p q e rho xf a * J (S.step a))
    (hlocal :
      S.forkSchurPrevCoefficient weight p q e rho yw (S.step seamPred) *
          S.forkSchurNextCoefficient weight p q e rho xf seamPred <
        (S.forkSchurSelfCoefficient weight p q e rho xf yw
              (S.step seamPred) -
            S.forkSchurNextCoefficient weight p q e rho xf
              (S.step seamPred)) *
          S.forkSchurSelfCoefficient weight p q e rho xf yw seamPred) :
    ∀ i, rho i = 1 := by
  have hdet : 0 < (S.forkSectorMatrix weight p q e rho xf yw).det :=
    S.forkSectorMatrix_det_pos hl weight p q e rho xf yw J seamPred
      hgap hp hq he hrho hw hunit hxf hyw hJ hprevOrdinary hresidual hlocal
  have hself : ∀ a,
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a := fun a =>
    (S.forkSchur_cyclic_signs weight p q e rho xf yw a hgap hp hq he hrho
      hw hunit hxf hyw).2.2.1
  let x : Fin n → ℝ :=
    twoRootCurrentDelta (sourceProductExponent next weight back) p q rho
  have hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0 := by
    intro r
    exact ordered_current_secant_kernel_row
      (sourceProductExponent next weight back) (sourceStoich next weight back)
      (fun i => ne_of_gt (he i)) hbase hratio r
  have hx : x = 0 :=
    S.globalCurrentSecantKernel_eq_zero_of_forkSector_det hprevnext
      weight p q e rho (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r))
      he hrho hw hgap hunit xf yw hxf hyw hself hdet x hker
  apply ratios_eq_one_of_twoRootCurrentDelta_eq_zero
    (sourceProductExponent next weight back) (sourceStoich next weight back)
    (fun i => ne_of_gt (he i)) hbase hratio
  intro r
  exact congrFun hx r

end SourceCyclicNonemptyGapSystem

end TypeIIL
