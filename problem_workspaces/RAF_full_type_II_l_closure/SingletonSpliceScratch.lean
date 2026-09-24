import proofs.TypeIIL.SourceCyclicCombinedCone

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- A zero-length cyclic gap is exactly the scalar singleton two-port. -/
noncomputable def singletonForkGap
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (j : Fin l) (hm : S.gapLength j = 0) :
    {G : SourceGapEmbedding next back 0 //
      SourceSingletonForkGap G (S.fork j) (S.fork (S.step j))
        ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j))))} := by
  let Pack (m : ℕ) := {G : SourceGapEmbedding next back m //
    SourceWrapForkGap G (S.fork j) (S.fork (S.step j))
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j))))}
  let Q : Pack 0 := hm ▸ (⟨S.gap j, S.wrap j⟩ : Pack (S.gapLength j))
  let G := Q.1
  let P := Q.2
  exact
    ⟨G,
      { pre := P.pre
        post := P.post
        right_successor_ne_left := P.right_successor_ne_left
        right_successor_ne_leftBack := P.right_successor_ne_leftBack }⟩

end SourceCyclicNonemptyGapSystem

/-- Reconstruction from the literal fork columns is uniform in the gap
length.  In particular, unlike `sourceWrapForwardForcing`, this interface
does not change meaning when the internal block is a singleton. -/
theorem SourceWrapGlobalColumnClosed.internal_coordinates_eq_negative_actual_responses_of_kernel
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    {P : SourceWrapForkGap G left right leftBack}
    (H : SourceWrapGlobalColumnClosed P)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (x : Fin n → ℝ) (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∀ i, x (G.idx i) = -(yw i * x left + xf i * x right) := by
  let z : Fin (m + 1) → ℝ := fun i =>
    x (G.idx i) + yw i * x left + xf i * x right
  have hzero : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j = 0 := by
    intro i
    have hr := H.kernel_row_split weight p q e rho x hker i
    calc
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j =
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x (G.idx j)) +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j) * x left +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j) * x right := by
            dsimp [z]
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp only [← mul_assoc]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = 0 := by rw [hyw i, hxf i]; exact hr
  have hz := G.restrictedCurrentMatrix_kernel_eq_zero weight p q e rho
    hp hq he hrho hw z hzero
  intro i
  have hi := hz i
  dsimp [z] at hi
  linarith

/-- Forward boundary port of a literal gap after its interior is eliminated
against the actual right-fork column. -/
noncomputable def SourceWrapForkGap.forwardPort
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right : Fin n}
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : Fin (m + 1) → ℝ) : ℝ :=
  currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e left right -
    ∑ i, currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e left (G.idx i) * xf i

/-- Reverse/wrap boundary port of the same eliminated literal gap. -/
noncomputable def SourceWrapForkGap.wrapPort
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right : Fin n}
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : Fin (m + 1) → ℝ) : ℝ :=
  currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e right left -
    ∑ i, currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e right (G.idx i) * yw i

/-- The literal successor Schur coefficient across a singleton internal
block is `k / (1 + A + c)`, hence positive.  The response is taken against
the actual right-fork column, which is the uniform forcing convention. -/
theorem SourceWrapForkGap.singleton_actual_schur_next_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right) :
    0 < currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e left right -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e left (G.idx i) * xf i := by
  subst m
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let k := q left *
    (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
  have hA : 0 < A := div_pos (hp _) (he _)
  have hc : 0 < c := div_pos (hq _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hk : 0 < k := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hsolve := hxf (0 : Fin 1)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] at hsolve
  rw [PS.internal_diagonal weight p q e rho hunit,
    PS.internal_right_entry weight p q e rho hunit] at hsolve
  have hxf0 : xf 0 = -(A + c) / d := by
    dsimp [A, c, d] at hsolve ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith
  have hdirect := PS.left_right_entry weight p q e rho
  have hgap := P.post.fork_postGap_mul weight p q e rho xf
  rw [hdirect, hgap, hxf0]
  rw [P.post.first_eq.symm]
  change 0 < k - (-k) * (-(A + c) / d)
  rw [singleton_schur_forward_eq rfl (ne_of_gt hd)]
  exact div_pos hk hd

/-- Exact coordinates of the two literal column responses of a singleton
block. -/
theorem SourceSingletonForkGap.actual_response_coordinates
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back 0} {left right leftBack : Fin n}
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r)
    (hunit : weight (G.idx 0) = 1)
    (xf yw : Fin 1 → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    xf 0 = -(p (G.idx 0) / e (G.idx 0) + q (G.idx 0) / e right) /
        (1 + p (G.idx 0) / e (G.idx 0) + q (G.idx 0) / e right) ∧
      yw 0 = -(p (G.idx 0) / e (G.idx 0) * weight left) /
        (1 + p (G.idx 0) / e (G.idx 0) + q (G.idx 0) / e right) := by
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  have hd : 0 < d := by
    have hA : 0 < A := div_pos (hp _) (he _)
    have hc : 0 < c := div_pos (hq _) (he _)
    dsimp [d]
    linarith
  have hx := hxf 0
  have hy := hyw 0
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] at hx hy
  rw [P.internal_diagonal weight p q e rho hunit,
    P.internal_right_entry weight p q e rho hunit] at hx
  rw [P.internal_diagonal weight p q e rho hunit,
    P.internal_left_entry weight p q e rho] at hy
  constructor
  · dsimp [A, c, d] at hd ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith
  · dsimp [A, c, d] at hd ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith

/-- A singleton following gap contributes strictly positive diagonal slack.
The `-1` is the direct fork-to-fork edge that is absent for longer gaps. -/
theorem SourceSingletonForkGap.following_budget_pos
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back 0} {left right leftBack : Fin n}
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx 0) = 1)
    (xf yw : Fin 1 → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    0 < (weight left : ℝ) - 1 + yw 0 - xf 0 := by
  obtain ⟨hx, hy⟩ := P.actual_response_coordinates
    weight p q e rho hp hq he hunit xf yw hxf hyw
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let s : ℝ := weight left
  have hA : 0 < A := div_pos (hp _) (he _)
  have hc : 0 < c := div_pos (hq _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hs : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast hw left
  have hnum : 0 < s * (1 + c) - 1 := by
    nlinarith [mul_pos (lt_of_lt_of_le (by norm_num) hs) (by linarith : 0 < 1 + c)]
  rw [hx, hy]
  change 0 < s - 1 + (-(A * s) / d) - (-(A + c) / d)
  have hid : s - 1 + (-(A * s) / d) - (-(A + c) / d) =
      (s * (1 + c) - 1) / d := by
    field_simp
    dsimp [d]
    ring
  rw [hid]
  exact div_pos hnum hd

/-- Length-uniform following-port slack.  The Kronecker term is the direct
fork-to-fork feedthrough: it is present exactly for the identity-length
(singleton) two-port and absent after one or more path-composition steps. -/
theorem SourceWrapForkGap.actual_following_budget_nonneg
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left)
    {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ k * ((weight left : ℝ) - (if m = 0 then 1 else 0) + yw 0 - xf 0) := by
  by_cases hm : m = 0
  · subst m
    let PS : SourceSingletonForkGap G left right leftBack :=
      { pre := P.pre
        post := P.post
        right_successor_ne_left := P.right_successor_ne_left
        right_successor_ne_leftBack := P.right_successor_ne_leftBack }
    have hs := PS.following_budget_pos weight p q e rho hp hq he hw
      hunit xf yw hxf hyw
    simpa using mul_nonneg hk (le_of_lt hs)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA : ∀ i, 0 ≤ G.gapA p e i :=
      G.gapA_nonneg (fun r => le_of_lt (hp r)) he
    have hc : ∀ i, 0 ≤ G.gapC weight q e rho i :=
      G.gapC_nonneg (fun r => le_of_lt (hq r)) he hrho hw
    have hs : ∀ i, 1 ≤ G.gapS weight i := G.gapS_one_le hw
    have hscale : 1 ≤ (weight left : ℝ) := by
      exact_mod_cast hw left
    have hxf' : ∀ i, ∑ j,
        finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
            (G.gapS weight) i j * xf j =
          sourceWrapForwardForcing (G.gapA p e) (G.gapC weight q e rho) i := by
      intro i
      rw [← G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
      rw [← P.internal_right_column_eq_forcing hmpos
        weight p q e rho hunit i]
      exact hxf i
    have hyw' : ∀ i, ∑ j,
        finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
            (G.gapS weight) i j * yw j =
          sourceWrapLeftForcing (G.gapA p e) (weight left) i := by
      intro i
      rw [← G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
      rw [← P.internal_left_column_eq_forcing weight p q e rho i]
      exact hyw i
    have hbudget := finiteSourcePath_literal_following_budget_nonneg hmpos
      (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight) xf yw
      hA hc hs hscale hk (by simpa [SourceGapEmbedding.gapS] using hunit)
      hxf' hyw'
    simpa [hm] using hbudget

/-- Direct feedthrough of a literal boundary trace.  It is the next-edge
coefficient for the singleton base and vanishes after every nontrivial path
extension. -/
theorem SourceWrapForkGap.left_right_entry_eq_directFeedthrough
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e left right =
      (if m = 0 then
        q left * (sourceForkNextCoeff next weight back rho left /
          e (next left)) else 0) := by
  by_cases hm : m = 0
  · subst m
    let PS : SourceSingletonForkGap G left right leftBack :=
      { pre := P.pre
        post := P.post
        right_successor_ne_left := P.right_successor_ne_left
        right_successor_ne_leftBack := P.right_successor_ne_leftBack }
    rw [ite_eq_left rfl, PS.left_right_entry weight p q e rho,
      P.post.first_eq]
  · rw [ite_eq_right hm]
    exact P.left_right_entry_zero (Nat.pos_of_ne_zero hm) weight p q e rho

/-- Coordinate-free following contribution to the fork diagonal.  This is
the generated trace law actually consumed by Schur closure; the response
coordinates and the singleton direct edge have disappeared into one
nonnegative scalar. -/
theorem SourceWrapForkGap.actual_following_contribution_nonneg
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let k := q left *
      (sourceForkNextCoeff next weight back rho left / e (next left))
    0 ≤ k * weight left - (∑ i, M left (G.idx i) * yw i) - M left right +
      ∑ i, M left (G.idx i) * xf i := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let k := q left *
    (sourceForkNextCoeff next weight back rho left / e (next left))
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _)))
  have hb := P.actual_following_budget_nonneg weight p q e rho hp hq he hrho
    hw hunit xf yw hxf hyw hk
  have hfeed := P.left_right_entry_eq_directFeedthrough weight p q e rho
  have hx := P.post.fork_postGap_mul weight p q e rho xf
  have hy := P.post.fork_postGap_mul weight p q e rho yw
  change M left right = _ at hfeed
  change (∑ i, M left (G.idx i) * xf i) = _ at hx
  change (∑ i, M left (G.idx i) * yw i) = _ at hy
  change 0 ≤ k * weight left - (∑ i, M left (G.idx i) * yw i) -
    M left right + ∑ i, M left (G.idx i) * xf i
  rw [hx, hy, hfeed]
  dsimp [k] at hb ⊢
  by_cases hm : m = 0 <;> simp [hm] at hb ⊢ <;>
    ring_nf at hb ⊢ <;> linarith

/-- Generating singleton two-port theorem in literal matrix coordinates.
The four boundary coefficients are not estimated separately: their oriented
`2×2` minor is transported as one invariant. -/
theorem SourceSingletonForkGap.actual_raw_two_edge_margin
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back 0} {left right leftBack : Fin n}
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx 0) = 1)
    (xf yw : Fin 1 → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left)
    {X Bprev : ℝ}
    (hX :
      let A := p (G.idx 0) / e (G.idx 0)
      let c := q (G.idx 0) / e right
      let d := 1 + A + c
      let g := p right / e right
      let h := q right *
        (sourceForkBackCoeff next weight back rho right (G.idx 0) /
          e (G.idx 0))
      (d + g + h) / d ≤ X)
    (hBprev :
      let A := p (G.idx 0) / e (G.idx 0)
      let c := q (G.idx 0) / e right
      let d := 1 + A + c
      let k := q left *
        (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
      let s : ℝ := weight left
      (d + k * s * (1 + c)) / d ≤ Bprev) :
    (currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e right left -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e right (G.idx i) * yw i) *
      (currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e left right -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e left (G.idx i) * xf i) <
      X * Bprev := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let g := p right / e right
  let h := q right *
    (sourceForkBackCoeff next weight back rho right (G.idx 0) /
      e (G.idx 0))
  let k := q left *
    (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
  let s : ℝ := weight left
  have hA : 0 ≤ A := le_of_lt (div_pos (hp _) (he _))
  have hc : 0 ≤ c := le_of_lt (div_pos (hq _) (he _))
  have hg : 0 ≤ g := le_of_lt (div_pos (hp _) (he _))
  have hh : 0 ≤ h := le_of_lt (mul_pos (hq _)
    (div_pos (sourceForkBackCoeff_pos next weight back hrho _ _) (he _)))
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _)))
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast hw left
  obtain ⟨hxf0, hyw0⟩ := P.actual_response_coordinates
    weight p q e rho hp hq he hunit xf yw hxf hyw
  have hF : M left right - (∑ i, M left (G.idx i) * xf i) = k / d := by
    dsimp [M]
    rw [P.left_right_entry weight p q e rho,
      P.post.fork_postGap_mul weight p q e rho xf, hxf0]
    rw [P.post.first_eq.symm]
    change k - (-k) * (-(A + c) / d) = k / d
    exact singleton_schur_forward_eq rfl
      (ne_of_gt (by dsimp [d]; linarith))
  have hW : M right left - (∑ i, M right (G.idx i) * yw i) =
      s * (h * (1 + c) - g * A) / d := by
    dsimp [M]
    rw [Fin.sum_univ_one, P.right_left_entry weight p q e rho,
      P.pre.fork_singletonGap_entry weight p q e rho hunit, hyw0]
    change h * s - (-(g + h)) * (-(A * s) / d) = _
    exact singleton_schur_wrap_eq rfl
      (ne_of_gt (by dsimp [d]; linarith))
  change (M right left - (∑ i, M right (G.idx i) * yw i)) *
      (M left right - (∑ i, M left (G.idx i) * xf i)) < X * Bprev
  apply singleton_wrap_raw_two_edge_margin (A := A) (c := c) (g := g)
    (h := h) (k := k) (s := s) (d := d) rfl hA hc hg hh hk hs
  · simpa [A, c, d, g, h] using hX
  · simpa [A, c, d, k, s] using hBprev
  · exact hF
  · exact hW

/-- Two adjacent singleton gaps already give the complete strict `B-F`
inequality at their common fork.  This is the smallest mixed-gap Schur row
and the base case hidden by the former positive-`m` interface. -/
theorem adjacent_singleton_schur_self_sub_next_pos
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {Gprev Gnext : SourceGapEmbedding next back 0}
    {left center right leftBack : Fin n}
    (Pprev : SourceSingletonForkGap Gprev left center leftBack)
    (Pnext : SourceSingletonForkGap Gnext center right (Gprev.idx 0))
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hprevUnit : weight (Gprev.idx 0) = 1)
    (hnextUnit : weight (Gnext.idx 0) = 1)
    (xp yp xn yn : Fin 1 → ℝ)
    (hxp : ∀ i, ∑ j,
      Gprev.restrictedCurrentMatrix weight p q e rho i j * xp j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (Gprev.idx i) center)
    (hyp : ∀ i, ∑ j,
      Gprev.restrictedCurrentMatrix weight p q e rho i j * yp j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (Gprev.idx i) left)
    (hxn : ∀ i, ∑ j,
      Gnext.restrictedCurrentMatrix weight p q e rho i j * xn j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (Gnext.idx i) right)
    (hyn : ∀ i, ∑ j,
      Gnext.restrictedCurrentMatrix weight p q e rho i j * yn j =
        currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (Gnext.idx i) center) :
    0 <
      (currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e center center -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e center (Gprev.idx i) * xp i -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e center (Gnext.idx i) * yn i) -
      (currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e center right -
        ∑ i, currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e center (Gnext.idx i) * xn i) := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let A := p (Gprev.idx 0) / e (Gprev.idx 0)
  let c := q (Gprev.idx 0) / e center
  let d := 1 + A + c
  let g := p center / e center
  let h := q center *
    (sourceForkBackCoeff next weight back rho center (Gprev.idx 0) /
      e (Gprev.idx 0))
  let k := q center *
    (sourceForkNextCoeff next weight back rho center / e (Gnext.idx 0))
  let s : ℝ := weight center
  have hd : 0 < d := by
    have hA : 0 < A := div_pos (hp _) (he _)
    have hc : 0 < c := div_pos (hq _) (he _)
    dsimp [d]
    linarith
  have hg : 0 < g := div_pos (hp _) (he _)
  have hh : 0 < h := mul_pos (hq _)
    (div_pos (sourceForkBackCoeff_pos next weight back hrho _ _) (he _))
  have hk : 0 < k := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hxp0 :=
    (Pprev.actual_response_coordinates
      weight p q e rho hp hq he hprevUnit xp yp hxp hyp).1
  have hfollow :=
    Pnext.following_budget_pos
      weight p q e rho hp hq he hw hnextUnit xn yn hxn hyn
  have hdiag := sourceOrderedCurrentMatrix_fork_diagonal
    next weight back (p := p) (q := q) (e := e) (rho := rho)
    (r := center) (z := Gprev.idx 0)
    Pnext.post.fork_back
    (by simpa [Pnext.post.first_eq] using Pnext.post.back_outside 0)
    (by simpa [Pnext.post.first_eq] using Pnext.post.fork_outside 0)
    Pprev.pre.terminal_ne_fork
  have hpre := Pprev.pre.fork_singletonGap_entry
    weight p q e rho hprevUnit
  have hpostY := Pnext.post.fork_postGap_mul weight p q e rho yn
  have hpostX := Pnext.post.fork_postGap_mul weight p q e rho xn
  have hdirect := Pnext.left_right_entry weight p q e rho
  change M center center = _ at hdiag
  change M center (Gprev.idx 0) = _ at hpre
  change (∑ i, M center (Gnext.idx i) * yn i) = _ at hpostY
  change (∑ i, M center (Gnext.idx i) * xn i) = _ at hpostX
  change M center right = _ at hdirect
  change 0 < (M center center -
      (∑ i, M center (Gprev.idx i) * xp i) -
      (∑ i, M center (Gnext.idx i) * yn i)) -
    (M center right - ∑ i, M center (Gnext.idx i) * xn i)
  rw [Fin.sum_univ_one, hdiag, hpre, hpostY, hpostX, hdirect, hxp0]
  rw [Pnext.post.first_eq.symm]
  have hcore : 0 < (d + g + h) / d := by
    exact div_pos (by linarith) hd
  have hcore' : 0 <
      1 + g + h - (-(g + h)) * (-(A + c) / d) := by
    rw [singleton_schur_right_diagonal_core_eq rfl (ne_of_gt hd)]
    exact hcore
  have hbudget : 0 < k * (s - 1 + yn 0 - xn 0) := mul_pos hk hfollow
  dsimp [A, c, d, g, h, k, s] at hcore' hbudget ⊢
  nlinarith

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- Every cyclic gap, including a singleton block, has unique responses to
its two literal adjacent-fork columns. -/
theorem exists_actual_fork_column_responses
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) :
    ∃ xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ,
      (∀ a i, ∑ t,
        (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
          currentSecantKernelMatrixWith
              (orderedMonomialSecantMatrix
                (sourceProductExponent next weight back) rho)
              (sourceStoich next weight back) p q e
              ((S.gap a).idx i) (S.fork (S.step a))) ∧
      (∀ a i, ∑ t,
        (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
          currentSecantKernelMatrixWith
              (orderedMonomialSecantMatrix
                (sourceProductExponent next weight back) rho)
              (sourceStoich next weight back) p q e
              ((S.gap a).idx i) (S.fork a)) := by
  classical
  choose xf hxf using fun a =>
    (S.gap a).restricted_response_exists weight p q e rho
      hp hq he hrho hw (fun i =>
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
  choose yw hyw using fun a =>
    (S.gap a).restricted_response_exists weight p q e rho
      hp hq he hrho hw (fun i =>
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
  exact ⟨xf, yw, hxf, hyw⟩

/-- Positivity of the genuine successor Schur port is uniform over all paper
gap lengths.  Long gaps reduce to the existing continuant response theorem;
the formerly omitted singleton gap reduces to the scalar two-port identity. -/
theorem forkSchurNextCoefficient_pos_of_actual_response
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork (S.step j))) :
    0 < S.forkSchurNextCoefficient weight p q e rho xf j := by
  by_cases hm : S.gapLength j = 0
  · unfold forkSchurNextCoefficient
    exact (S.wrap j).singleton_actual_schur_next_pos hm weight p q e rho
      hp hq he hrho hw hunit (xf j) hxf
  · apply S.forkSchurNextCoefficient_pos weight p q e rho xf j
      (Nat.pos_of_ne_zero hm) hp hq he hrho hw hunit
    intro i
    rw [← (S.wrap j).internal_right_column_eq_forcing
      (Nat.pos_of_ne_zero hm) weight p q e rho hunit i]
    exact hxf i

/-- On a nonsingleton block, the uniform actual right-column response agrees
with the historical synthetic forcing interface. -/
theorem actual_right_response_eq_forward_forcing
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork (S.step j))) :
    ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i := by
  intro i
  rw [← (S.wrap j).internal_right_column_eq_forcing hm
    weight p q e rho hunit i]
  exact hxf i

/-- The actual left-fork column is represented by the historical left
forcing for every gap length, including a singleton. -/
theorem actual_left_response_eq_left_forcing
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hyw : ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork j)) :
    ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        sourceWrapLeftForcing ((S.gap j).gapA p e)
          (weight (S.fork j)) i := by
  intro i
  rw [← (S.wrap j).internal_left_column_eq_forcing weight p q e rho i]
  exact hyw i

/-- The cyclic forward Schur coefficient is exactly the forward port of its
literal gap boundary trace. -/
theorem forkSchurNextCoefficient_eq_forwardPort
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    S.forkSchurNextCoefficient weight p q e rho xf j =
      SourceWrapForkGap.forwardPort (G := S.gap j)
        (left := S.fork j) (right := S.fork (S.step j))
        weight p q e rho (xf j) := by
  rfl

/-- The successor row's predecessor Schur coefficient is exactly the reverse
port of the intervening literal gap boundary trace. -/
theorem forkSchurPrevCoefficient_step_eq_wrapPort
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) =
      SourceWrapForkGap.wrapPort (G := S.gap j)
        (left := S.fork j) (right := S.fork (S.step j))
        weight p q e rho (yw j) := by
  simp only [forkSchurPrevCoefficient, SourceWrapForkGap.wrapPort]
  rw [S.step.symm_apply_apply]

/-- Generating fork-row decomposition.  The diagonal-minus-forward port is
the sum of the core transported from the preceding two-port and the
coordinate-free contribution of the following trace.  No gap length enters
this identity. -/
theorem forkSchurSelf_sub_next_eq_precedingCore_add_followingTrace
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    let r := S.step j
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let k := q (S.fork r) *
      (sourceForkNextCoeff next weight back rho (S.fork r) /
        e (next (S.fork r)))
    S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r =
      (M (S.fork r) (S.fork r) - k * weight (S.fork r) -
        ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i) +
      (k * weight (S.fork r) -
          (∑ i, M (S.fork r) ((S.gap r).idx i) * yw r i) -
        M (S.fork r) (S.fork (S.step r)) +
          ∑ i, M (S.fork r) ((S.gap r).idx i) * xf r i) := by
  simp only [forkSchurSelfCoefficient, forkSchurNextCoefficient]
  rw [S.step.symm_apply_apply]
  ring

/-- Exact boundary conservation for the identity trace.  The following gap
appears only to identify the literal fork diagonal; its length and response do
not enter the scalar identity. -/
theorem SourceWrapForkGap.singleton_precedingCore_eq
    {n m mnext : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m}
    {Gnext : SourceGapEmbedding next back mnext}
    {left right rightNext leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (Pnext : SourceWrapForkGap Gnext right rightNext (G.idx (Fin.last m)))
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : Fin (m + 1) → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hxf : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * xf t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * yw t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let A := p (G.idx 0) / e (G.idx 0)
    let c := q (G.idx 0) / e right
    let d := 1 + A + c
    let g := p right / e right
    let h := q right *
      (sourceForkBackCoeff next weight back rho right (G.idx 0) / e (G.idx 0))
    let k := q right *
      (sourceForkNextCoeff next weight back rho right / e (next right))
    M right right - k * weight right -
        ∑ i, M right (G.idx i) * xf i =
      (d + g + h) / d := by
  subst m
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let g := p right / e right
  let h := q right *
    (sourceForkBackCoeff next weight back rho right (G.idx 0) / e (G.idx 0))
  let k := q right *
    (sourceForkNextCoeff next weight back rho right / e (next right))
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  have hd : 0 < d := by
    have hA : 0 < A := div_pos (hp _) (he _)
    have hc : 0 < c := div_pos (hq _) (he _)
    dsimp [d]
    linarith
  have hx0 := (PS.actual_response_coordinates weight p q e rho hp hq he
    hunit xf yw hxf hyw).1
  have hdiag := sourceOrderedCurrentMatrix_fork_diagonal
    next weight back (p := p) (q := q) (e := e) (rho := rho)
    (r := right) (z := G.idx 0)
    P.pre.fork_back
    (by simpa [Pnext.post.first_eq] using Pnext.post.back_outside 0)
    (by simpa [Pnext.post.first_eq] using Pnext.post.fork_outside 0)
    P.pre.terminal_ne_fork
  have hpre := PS.pre.fork_singletonGap_entry weight p q e rho hunit
  change M right right = _ at hdiag
  change M right (G.idx 0) = _ at hpre
  change M right right - k * weight right -
      ∑ i, M right (G.idx i) * xf i = (d + g + h) / d
  rw [Fin.sum_univ_one, hdiag, hpre, hx0]
  have hid : 1 + g + h - (-(g + h)) * (-(A + c) / d) =
      (d + g + h) / d :=
    singleton_schur_right_diagonal_core_eq rfl (ne_of_gt hd)
  dsimp [A, c, d, g, h, k] at hid ⊢
  nlinarith [hid]

/-- Positivity of the identity transported core is a corollary of its exact
conservation law. -/
theorem SourceWrapForkGap.singleton_precedingCore_pos
    {n m mnext : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m}
    {Gnext : SourceGapEmbedding next back mnext}
    {left right rightNext leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (Pnext : SourceWrapForkGap Gnext right rightNext (G.idx (Fin.last m)))
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : Fin (m + 1) → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hxf : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * xf t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * yw t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let k := q right *
      (sourceForkNextCoeff next weight back rho right / e (next right))
    0 < M right right - k * weight right -
      ∑ i, M right (G.idx i) * xf i := by
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let g := p right / e right
  let h := q right *
    (sourceForkBackCoeff next weight back rho right (G.idx 0) / e (G.idx 0))
  have hEq := SourceWrapForkGap.singleton_precedingCore_eq
    (P := P) hm (Pnext := Pnext) weight p q e rho xf yw
      hp hq he hunit hxf hyw
  have hd : 0 < d := by
    have hA : 0 < A := div_pos (hp _) (he _)
    have hc : 0 < c := div_pos (hq _) (he _)
    dsimp [d]
    linarith
  have hg : 0 < g := div_pos (hp _) (he _)
  have hh : 0 < h := mul_pos (hq _) (div_pos
    (sourceForkBackCoeff_pos next weight back hrho _ _) (he _))
  have hquot : 0 < (d + g + h) / d := div_pos (by linarith) hd
  dsimp [A, c, d, g, h] at hEq hquot ⊢
  nlinarith

/-- The left Schur group of the identity trace is its exact fractional-linear
boundary core.  This is the identity element of the same two-port composition
law used for positive paths. -/
theorem SourceWrapForkGap.singleton_actual_left_group_eq
    {n m : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m}
    {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * xf t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * yw t =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    let A := p (G.idx 0) / e (G.idx 0)
    let c := q (G.idx 0) / e right
    let d := 1 + A + c
    let k := q left *
      (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
    let s : ℝ := weight left
    1 + k * s + k * yw 0 = (d + k * s * (1 + c)) / d := by
  subst m
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let k := q left *
    (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
  let s : ℝ := weight left
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  have hd : 0 < d := by
    have hA : 0 < A := div_pos (hp _) (he _)
    have hc : 0 < c := div_pos (hq _) (he _)
    dsimp [d]
    linarith
  have hy0 := (PS.actual_response_coordinates weight p q e rho hp hq he
    hunit xf yw hxf hyw).2
  have hcore := singleton_schur_left_diagonal_core_eq
    (A := A) (c := c) (k := k) (s := s) (d := d)
      rfl (ne_of_gt hd)
  dsimp [A, c, d, k, s] at hy0 hcore ⊢
  rw [hy0]
  nlinarith [hcore]

/-- Identity-trace determinant law stated solely through its two boundary
ports.  The proof is the scalar singleton minor; the statement is already in
the composition interface used by an arbitrary cyclic network. -/
theorem SourceWrapForkGap.singleton_actual_port_minor
    {n m : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m}
    {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left)
    {X Bprev : ℝ}
    (hX :
      let A := p (G.idx 0) / e (G.idx 0)
      let c := q (G.idx 0) / e right
      let d := 1 + A + c
      let g := p right / e right
      let h := q right *
        (sourceForkBackCoeff next weight back rho right (G.idx 0) /
          e (G.idx 0))
      (d + g + h) / d ≤ X)
    (hBprev :
      let A := p (G.idx 0) / e (G.idx 0)
      let c := q (G.idx 0) / e right
      let d := 1 + A + c
      let k := q left *
        (sourceForkNextCoeff next weight back rho left / e (G.idx 0))
      let s : ℝ := weight left
      (d + k * s * (1 + c)) / d ≤ Bprev) :
    SourceWrapForkGap.wrapPort (G := G) (left := left) (right := right)
        weight p q e rho yw *
      SourceWrapForkGap.forwardPort (G := G) (left := left) (right := right)
        weight p q e rho xf < X * Bprev := by
  subst m
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  simpa [SourceWrapForkGap.wrapPort, SourceWrapForkGap.forwardPort] using
    PS.actual_raw_two_edge_margin weight p q e rho hp hq he hrho hw
      hunit xf yw hxf hyw hX hBprev

/-- The singleton base obeys the same terminal-basis preceding-budget law as
a nontrivial positive path. -/
theorem SourceWrapForkGap.singleton_actual_forward_correction_le_direct
    {n m : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m}
    {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (xf : Fin (m + 1) → ℝ)
    (hxf : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e (G.idx i) right) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e right (G.idx j) * xf j ≤
      p right / e right + q right *
        (sourceForkBackCoeff next weight back rho right
          (G.idx (Fin.last m)) / e (G.idx (Fin.last m))) := by
  subst m
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  have hunit0 : weight (G.idx 0) = 1 := by simpa using hunit
  have hrow :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j =
        -(G.gapA p e 0 + G.gapC weight q e rho 0) := by
    rw [hxf 0, PS.internal_right_entry weight p q e rho hunit]
    unfold SourceGapEmbedding.gapA SourceGapEmbedding.gapC
    rw [show next (G.idx 0) = right by simpa using PS.pre.terminal_next,
      hunit0]
    simp [TypeII3.secantPoly]
    ring
  exact PS.pre.singleton_forward_correction_le_direct
    weight p q e rho hunit hp hq he hrho xf hrow

/-- Boundary-trace form of the preceding-gap budget.  The proof has one
identity trace (`gapLength = 0`) and one positive-path composition theorem;
there is no case split on a neighbouring length pattern. -/
theorem actual_preceding_correction_le_direct
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxfActual : ∀ i,
      ∑ t,
        (S.gap (S.step.symm j)).restrictedCurrentMatrix
            weight p q e rho i t * xf (S.step.symm j) t =
          currentSecantKernelMatrixWith
              (orderedMonomialSecantMatrix
                (sourceProductExponent next weight back) rho)
              (sourceStoich next weight back) p q e
              ((S.gap (S.step.symm j)).idx i) (S.fork j)) :
    let pred := S.step.symm j
    let last := Fin.last (S.gapLength pred)
    ∑ i,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          (S.fork j) ((S.gap pred).idx i) * xf pred i ≤
        p (S.fork j) / e (S.fork j) +
          q (S.fork j) *
            (sourceForkBackCoeff next weight back rho (S.fork j)
              ((S.gap pred).idx last) / e ((S.gap pred).idx last)) := by
  let pred := S.step.symm j
  by_cases hm : S.gapLength pred = 0
  · have hsingle :=
      SourceWrapForkGap.singleton_actual_forward_correction_le_direct
        (P := S.wrap pred) hm weight p q e rho (hunit pred)
        hp hq he hrho (xf pred) (by
          intro i
          simpa only [pred, Equiv.apply_symm_apply] using hxfActual i)
    simpa only [pred, Equiv.apply_symm_apply] using hsingle
  · have hmpos : 0 < S.gapLength pred := Nat.pos_of_ne_zero hm
    have hsynth := S.actual_right_response_eq_forward_forcing
      weight p q e rho xf pred hmpos (hunit pred) (by
        intro i
        simpa only [pred, Equiv.apply_symm_apply] using hxfActual i)
    have hpositive :=
      (S.wrap pred).pre.forward_correction_le_direct_of_nonwrap
        hmpos weight p q e rho JFork (hunit pred)
        (by simpa only [pred, Equiv.apply_symm_apply] using horder)
        (by simpa only [pred, Equiv.apply_symm_apply] using hpFork)
        (by simpa only [pred, Equiv.apply_symm_apply] using hpLast)
        hp hq he hrho hw hJFork (xf pred) hsynth
    simpa only [pred, Equiv.apply_symm_apply] using hpositive

/-- The positive-gap left core is bounded by the genuine Schur diagonal for
an arbitrary predecessor trace.  Length has disappeared from the seam
interface: only the preceding two-port budget is used. -/
theorem actual_positive_left_core_le_forkSchurSelf
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxfActual : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hywActual : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork j)) :
    let k := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) k
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let seff := wrapCondensedScale eff.A
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.scale
    let keff := wrapCondensedK eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.k
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + keff * seff *
      (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j))) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  have hpreceding := S.actual_preceding_correction_le_direct
    weight p q e rho xf j JFork hp hq he hrho hw hJFork hunit
      horder hpFork hpLast (by
        intro i
        simpa only [Equiv.apply_symm_apply] using
          hxfActual (S.step.symm j) i)
  have hyw := S.actual_left_response_eq_left_forcing
    weight p q e rho yw j hywActual
  exact S.left_core_le_forkSchurSelf weight p q e rho xf yw j hm
    hp hq he hrho hw (hunit j) hyw hpreceding

/-- Exact boundary conservation law for a positive path: the literal Schur
core at the right port is the condensed Möbius core.  The apparent `m = 1`
branch below only docks the endpoint-collision representation to the common
formula; it is not a distinct neighboring-gap case. -/
theorem positive_precedingCore_eq
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxfActual : ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork (S.step j))) :
    let r := S.step j
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let m := S.gapLength j
    let kLeft := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
    let k := q (S.fork r) *
      (sourceForkNextCoeff next weight back rho (S.fork r) /
        e (next (S.fork r)))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) kLeft
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) m)
      (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) h
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) m
    M (S.fork r) (S.fork r) - k * weight (S.fork r) -
        ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i =
      (d + g + heff) / d := by
  let r := S.step j
  let m := S.gapLength j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) kLeft
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) m)
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
  let heff := wrapCondensedH eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) h
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) m
  have hxf := S.actual_right_response_eq_forward_forcing
    weight p q e rho xf j hm hunit hxfActual
  have hscaleLeft : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hkLeft : 0 < kLeft := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hcore :
      1 + g + h -
          (h * finitePathNatLift ((S.gap j).gapS weight) (m - 1) *
              finitePathNatLift (xf j) (m - 1) -
            (g + h) * finitePathNatLift (xf j) m) =
        (d + g + heff) / d := by
    by_cases hm1 : m = 1
    · have hx0 := hxf 0
      have hxlast := hxf (Fin.last m)
      have hx0' :
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho 0 t *
              xf j t = (S.gap j).gapC weight q e rho 0 := by
        simpa [sourceWrapForwardForcing, m, hm1] using hx0
      have hxlast' :
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
              (Fin.last m) t * xf j t =
            -((S.gap j).gapA p e (Fin.last m) +
              (S.gap j).gapC weight q e rho (Fin.last m)) := by
        simpa [sourceWrapForwardForcing, m, hm1] using hxlast
      simpa [eff, Aeff, heff, d, m] using
        (S.gap j).restricted_two_coordinate_right_diagonal_core_eq hm1
          weight p q e rho (xf j) hp hq he hrho hw
          (by simpa [SourceGapEmbedding.gapS, m] using hunit)
          hx0' hxlast' (scale := (weight (S.fork j) : ℝ)) (k := kLeft)
          (h := h) (g := g)
    · have hmLong : 1 < m := by omega
      have hfirst :
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho 0 t *
              xf j t = 0 := by
        have hx := hxf 0
        have h0pen : (0 : ℕ) ≠ m - 1 := by omega
        have h0last : (0 : ℕ) ≠ m := by omega
        simpa [sourceWrapForwardForcing, m, h0pen, h0last] using hx
      have hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t *
              xf j t = 0 := by
        intro i hi him
        have hipen : i.val ≠ m - 1 := by omega
        have hilast : i.val ≠ m := by omega
        simpa [sourceWrapForwardForcing, m, hipen, hilast] using hxf i
      have hpen :
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
              ⟨m - 1, by omega⟩ t * xf j t =
            (S.gap j).gapC weight q e rho ⟨m - 1, by omega⟩ := by
        simpa [sourceWrapForwardForcing, m] using hxf ⟨m - 1, by omega⟩
      have hterminal :
          ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
              (Fin.last m) t * xf j t =
            -((S.gap j).gapA p e (Fin.last m) +
              (S.gap j).gapC weight q e rho (Fin.last m)) := by
        have hne : m ≠ m - 1 := by omega
        simpa [sourceWrapForwardForcing, m, hne] using hxf (Fin.last m)
      simpa [eff, Aeff, heff, d, m] using
        (S.gap j).restricted_right_diagonal_core_eq hmLong
          weight p q e rho (xf j) hp hq he hrho hw hscaleLeft hkLeft
          (by simpa [SourceGapEmbedding.gapS, m] using hunit)
          hfirst hrows hpen hterminal (h := h) (g := g)
  have hprevEq :
      (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        finitePathPrev (Fin.last m) (by simpa [m] using hm) := by
    apply Fin.ext
    simp [finitePathPrev]
  have hlastEq : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp
  have hsLift :
      finitePathNatLift ((S.gap j).gapS weight) (m - 1) =
        (weight ((S.gap j).idx
          (finitePathPrev (Fin.last m) (by simpa [m] using hm))) : ℝ) := by
    rw [finitePathNatLift_of_lt (i := m - 1)
      ((S.gap j).gapS weight) (by omega), hprevEq]
    rfl
  have hxPrevLift : finitePathNatLift (xf j) (m - 1) =
      xf j (finitePathPrev (Fin.last m) (by simpa [m] using hm)) := by
    rw [finitePathNatLift_of_lt (i := m - 1) (xf j) (by omega), hprevEq]
  have hxLastLift : finitePathNatLift (xf j) m = xf j (Fin.last m) := by
    rw [finitePathNatLift_of_lt (i := m) (xf j) (by omega), hlastEq]
  have hcoreRaw :
      1 + g + h -
          (h * weight ((S.gap j).idx
              (finitePathPrev (Fin.last m) (by simpa [m] using hm))) *
              xf j (finitePathPrev (Fin.last m) (by simpa [m] using hm)) -
            (g + h) * xf j (Fin.last m)) =
        (d + g + heff) / d := by
    simpa [hsLift, hxPrevLift, hxLastLift] using hcore
  let Pnext : SourceWrapForkGap (S.gap r)
      (S.fork r) (S.fork (S.step r))
      ((S.gap j).idx (Fin.last m)) := by
    have heq :
        (S.gap (S.step.symm r)).idx
            (Fin.last (S.gapLength (S.step.symm r))) =
          (S.gap j).idx (Fin.last m) := by
      dsimp [r, m]
      rw [S.step.symm_apply_apply]
    exact heq ▸ S.wrap r
  have hdiag := sourceOrderedCurrentMatrix_fork_diagonal
    next weight back (p := p) (q := q) (e := e) (rho := rho)
    (r := S.fork r) (z := (S.gap j).idx (Fin.last m))
    (by simpa [r, m] using (S.wrap j).pre.fork_back)
    (by simpa [Pnext.post.first_eq] using Pnext.post.back_outside 0)
    (by simpa [Pnext.post.first_eq] using Pnext.post.fork_outside 0)
    (by simpa [r, m] using (S.wrap j).pre.terminal_ne_fork)
  have hpre := (S.wrap j).pre.fork_preGap_mul hm
    weight p q e rho hunit (xf j)
  change M (S.fork r) (S.fork r) = _ at hdiag
  change (∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i) = _ at hpre
  change M (S.fork r) (S.fork r) - k * weight (S.fork r) -
      ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i =
    (d + g + heff) / d
  have htarget :
      M (S.fork r) (S.fork r) - k * weight (S.fork r) -
          ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i =
        1 + g + h -
          (h * weight ((S.gap j).idx
              (finitePathPrev (Fin.last m) (by simpa [m] using hm))) *
              xf j (finitePathPrev (Fin.last m) (by simpa [m] using hm)) -
            (g + h) * xf j (Fin.last m)) := by
    rw [hdiag, hpre]
    dsimp [r, m, g, h, k]
    ring
  rw [htarget, hcoreRaw]

/-- Positivity is a corollary of exact boundary conservation plus positivity
of the two-port condensation state. -/
theorem positive_precedingCore_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxfActual : ∀ i, ∑ t,
      (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap j).idx i) (S.fork (S.step j))) :
    let r := S.step j
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let k := q (S.fork r) *
      (sourceForkNextCoeff next weight back rho (S.fork r) /
        e (next (S.fork r)))
    0 < M (S.fork r) (S.fork r) - k * weight (S.fork r) -
      ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i := by
  let r := S.step j
  let m := S.gapLength j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) kLeft
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) m)
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
  let heff := wrapCondensedH eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) h
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) m
  have hEq := S.positive_precedingCore_eq weight p q e rho xf j hm
    hp hq he hrho hw hunit hxfActual
  have hscaleLeft : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hkLeft : 0 < kLeft := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have heffPos : eff.StrictlyPositive := by
    exact natWrapPrefixState_pos
      (finitePathNatLift ((S.gap j).gapA p e))
      (finitePathNatLift ((S.gap j).gapC weight q e rho))
      (finitePathNatLift ((S.gap j).gapS weight))
      (fun _ => div_pos (hp _) (he _))
      (fun _ => mul_pos (hq _) (div_pos
        (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _)))
      (fun _ => (S.gap j).gapS_pos hw _)
      hscaleLeft hkLeft (m - 1)
  have hnextA : 0 < finitePathNatLift ((S.gap j).gapA p e) m := by
    unfold finitePathNatLift SourceGapEmbedding.gapA
    exact div_pos (hp _) (he _)
  have hedgeC : 0 < finitePathNatLift
      ((S.gap j).gapC weight q e rho) (m - 1) := by
    unfold finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hedgeS : 0 < finitePathNatLift
      ((S.gap j).gapS weight) (m - 1) := by
    exact (S.gap j).gapS_pos hw _
  have hh : 0 < h := by
    dsimp [h]
    exact mul_pos (hq _) (div_pos
      (sourceForkBackCoeff_pos next weight back hrho _ _) (he _))
  have hparams := wrap_condensed_parameters_pos
    (A₀ := eff.A)
    (A₁ := finitePathNatLift ((S.gap j).gapA p e) m)
    (c₀ := finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (s₀ := finitePathNatLift ((S.gap j).gapS weight) (m - 1))
    (scale := eff.scale) (k := eff.k) (h := h)
    heffPos.1 hnextA hedgeC hedgeS heffPos.2.1 heffPos.2.2 hh
  have hAeff : 0 < Aeff := by simpa [Aeff] using hparams.1
  have hheff : 0 < heff := by simpa [heff] using hparams.2.2.2
  have hcLast : 0 < finitePathNatLift
      ((S.gap j).gapC weight q e rho) m := by
    unfold finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hg : 0 < g := div_pos (hp _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hquot : 0 < (d + g + heff) / d := by
    apply div_pos
    · linarith
    · exact hd
  dsimp [r, m, M, kLeft, g, h, k, eff, Aeff, heff, d] at hEq hquot ⊢
  nlinarith

/-- The exact transported core plus nonnegative following trace gives the
right-core bound required by the oriented seam minor, for an arbitrary
following gap length. -/
theorem actual_positive_right_core_le_forkSchurSelf_sub_next
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    let r := S.step j
    let kLeft := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx (Fin.last (S.gapLength j))) /
          e ((S.gap j).idx (Fin.last (S.gapLength j))))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) kLeft
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) h
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + g + heff) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r := by
  let r := S.step j
  let m := S.gapLength j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) kLeft
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) m)
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
  let heff := wrapCondensedH eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) h
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) m
  have hEq := S.positive_precedingCore_eq weight p q e rho xf j hm
    hp hq he hrho hw (hunit j) (hxf j)
  have hfollow := (S.wrap r).actual_following_contribution_nonneg
    weight p q e rho hp hq he hrho hw (hunit r)
      (xf r) (yw r) (hxf r) (hyw r)
  have hsplit := S.forkSchurSelf_sub_next_eq_precedingCore_add_followingTrace
    weight p q e rho xf yw j
  dsimp [r, m, M, kLeft, g, h, k, eff, Aeff, heff, d] at hEq hfollow hsplit ⊢
  rw [hsplit]
  nlinarith

/-- Identity-trace companion of the right-core bound.  The scalar singleton
core is conserved exactly and an arbitrary following two-port contributes
only nonnegative slack. -/
theorem actual_singleton_right_core_le_forkSchurSelf_sub_next
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : S.gapLength j = 0)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    let r := S.step j
    let A := p ((S.gap j).idx 0) / e ((S.gap j).idx 0)
    let c := q ((S.gap j).idx 0) / e (S.fork r)
    let d := 1 + A + c
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx 0) / e ((S.gap j).idx 0))
    (d + g + h) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r := by
  let r := S.step j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let A := p ((S.gap j).idx 0) / e ((S.gap j).idx 0)
  let c := q ((S.gap j).idx 0) / e (S.fork r)
  let d := 1 + A + c
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx 0) / e ((S.gap j).idx 0))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  let Pnext : SourceWrapForkGap (S.gap r)
      (S.fork r) (S.fork (S.step r))
      ((S.gap j).idx (Fin.last (S.gapLength j))) := by
    have heq :
        (S.gap (S.step.symm r)).idx
            (Fin.last (S.gapLength (S.step.symm r))) =
          (S.gap j).idx (Fin.last (S.gapLength j)) := by
      dsimp [r]
      rw [S.step.symm_apply_apply]
    exact heq ▸ S.wrap r
  have hEq := SourceWrapForkGap.singleton_precedingCore_eq
    (P := S.wrap j) hm (Pnext := Pnext) weight p q e rho
      (xf j) (yw j) hp hq he (hunit j) (hxf j) (hyw j)
  have hfollow := (S.wrap r).actual_following_contribution_nonneg
    weight p q e rho hp hq he hrho hw (hunit r)
      (xf r) (yw r) (hxf r) (hyw r)
  have hsplit := S.forkSchurSelf_sub_next_eq_precedingCore_add_followingTrace
    weight p q e rho xf yw j
  dsimp [r, M, A, c, d, g, h, k] at hEq hfollow hsplit ⊢
  rw [hsplit]
  nlinarith

/-- The identity trace has the same left-core lower bound as a positive
two-port.  The local fractional-linear identity supplies the core, and the
entire predecessor enters through one length-free budget inequality. -/
theorem actual_singleton_left_core_le_forkSchurSelf
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : S.gapLength j = 0) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    let A := p ((S.gap j).idx 0) / e ((S.gap j).idx 0)
    let c := q ((S.gap j).idx 0) / e (S.fork (S.step j))
    let d := 1 + A + c
    let k := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e ((S.gap j).idx 0))
    let s : ℝ := weight (S.fork j)
    (d + k * s * (1 + c)) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  let pred := S.step.symm j
  let last := Fin.last (S.gapLength pred)
  let g := p (S.fork j) / e (S.fork j)
  let h := q (S.fork j) *
    (sourceForkBackCoeff next weight back rho (S.fork j)
      ((S.gap pred).idx last) / e ((S.gap pred).idx last))
  let A := p ((S.gap j).idx 0) / e ((S.gap j).idx 0)
  let c := q ((S.gap j).idx 0) / e (S.fork (S.step j))
  let d := 1 + A + c
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e ((S.gap j).idx 0))
  let s : ℝ := weight (S.fork j)
  have hpreceding := S.actual_preceding_correction_le_direct
    weight p q e rho xf j JFork hp hq he hrho hw hJFork hunit
      horder hpFork hpLast (by
        intro i
        simpa only [Equiv.apply_symm_apply] using
          hxf (S.step.symm j) i)
  have hlocal := SourceWrapForkGap.singleton_actual_left_group_eq
    (P := S.wrap j) hm weight p q e rho hp hq he (hunit j)
      (xf j) (yw j) (hxf j) (hyw j)
  have hexpand := S.forkSchurSelf_eq_left_group_add_preceding_budget
    weight p q e rho xf yw j
  rw [← (S.wrap j).post.first_eq] at hexpand
  dsimp [pred, last, g, h, A, c, d, k, s] at hpreceding hlocal hexpand ⊢
  rw [hexpand]
  nlinarith

/-- Oriented seam minor for the identity boundary trace.  This is obtained by
placing the two cyclic Schur lower bounds into the abstract port determinant;
no neighboring trace is opened or classified. -/
theorem actual_singleton_gap_oriented_seam_minor
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : S.gapLength j = 0) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j <
      (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
          S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  have hX := S.actual_singleton_right_core_le_forkSchurSelf_sub_next
    weight p q e rho xf yw j hm hp hq he hrho hw hunit hxf hyw
  have hBprev := S.actual_singleton_left_core_le_forkSchurSelf
    weight p q e rho xf yw j hm JFork hp hq he hrho hw hJFork
      hunit horder hpFork hpLast hxf hyw
  have hport := SourceWrapForkGap.singleton_actual_port_minor
    (P := S.wrap j) hm weight p q e rho hp hq he hrho hw (hunit j)
      (xf j) (yw j) (hxf j) (hyw j) hX hBprev
  rw [← S.forkSchurPrevCoefficient_step_eq_wrapPort weight p q e rho yw j,
    ← S.forkSchurNextCoefficient_eq_forwardPort weight p q e rho xf j] at hport
  exact hport

/-- Oriented seam minor for every positive central trace, with completely
arbitrary predecessor and successor trace lengths.  This is one application
of the two-port determinant invariant, not an enumeration of gap words. -/
theorem actual_positive_gap_oriented_seam_minor
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j <
      (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
          S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  have hxfSynthetic := S.actual_right_response_eq_forward_forcing
    weight p q e rho xf j hm (hunit j) (hxf j)
  have hywSynthetic := S.actual_left_response_eq_left_forcing
    weight p q e rho yw j (hyw j)
  apply S.forkSchurPrev_mul_next_lt_of_core_bounds
    weight p q e rho xf yw j hm hp hq he hrho hw (hunit j)
      hxfSynthetic hywSynthetic
  · exact S.actual_positive_right_core_le_forkSchurSelf_sub_next
      weight p q e rho xf yw j hm hp hq he hrho hw hunit hxf hyw
  · exact S.actual_positive_left_core_le_forkSchurSelf
      weight p q e rho xf yw j hm JFork hp hq he hrho hw hJFork
        hunit horder hpFork hpLast hxf (hyw j)

/-- Uniform oriented seam law for every boundary trace.  The proof has only
the algebraic identity element and the positive two-port semigroup; it does
not inspect a gap length or a neighboring word. -/
theorem actual_gap_oriented_seam_minor
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    S.forkSchurPrevCoefficient weight p q e rho yw (S.step j) *
        S.forkSchurNextCoefficient weight p q e rho xf j <
      (S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
          S.forkSchurNextCoefficient weight p q e rho xf (S.step j)) *
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  by_cases hm : S.gapLength j = 0
  · exact S.actual_singleton_gap_oriented_seam_minor
      weight p q e rho xf yw j hm JFork hp hq he hrho hw hJFork
        hunit horder hpFork hpLast hxf hyw
  · exact S.actual_positive_gap_oriented_seam_minor
      weight p q e rho xf yw j (Nat.pos_of_ne_zero hm) JFork
        hp hq he hrho hw hJFork hunit horder hpFork hpLast hxf hyw

/-- Positivity of the preceding transported core propagates through an
arbitrary following boundary trace.  This is the length-free replacement for
the former pair of neighboring-gap hypotheses. -/
theorem forkSchurSelf_sub_next_pos_of_actual_precedingCore
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hxf : ∀ i, ∑ t,
      (S.gap (S.step j)).restrictedCurrentMatrix weight p q e rho i t *
          xf (S.step j) t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap (S.step j)).idx i) (S.fork (S.step (S.step j))))
    (hyw : ∀ i, ∑ t,
      (S.gap (S.step j)).restrictedCurrentMatrix weight p q e rho i t *
          yw (S.step j) t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap (S.step j)).idx i) (S.fork (S.step j)))
    (hcore :
      let r := S.step j
      let M := currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e
      let k := q (S.fork r) *
        (sourceForkNextCoeff next weight back rho (S.fork r) /
          e (next (S.fork r)))
      0 < M (S.fork r) (S.fork r) - k * weight (S.fork r) -
        ∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i) :
    0 < S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
      S.forkSchurNextCoefficient weight p q e rho xf (S.step j) := by
  let r := S.step j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  have hfollow := (S.wrap r).actual_following_contribution_nonneg
    weight p q e rho hp hq he hrho hw hunit (xf r) (yw r) hxf hyw
  have hsplit := S.forkSchurSelf_sub_next_eq_precedingCore_add_followingTrace
    weight p q e rho xf yw j
  dsimp [r, M, k] at hcore hfollow hsplit ⊢
  rw [hsplit]
  exact add_pos_of_pos_of_nonneg hcore hfollow

/-- The singleton base followed by an arbitrary trace already satisfies the
uniform cyclic diagonal sign.  This is composition, not a neighboring-length
case: the following trace is consumed only through its abstract slack law. -/
theorem forkSchurSelf_sub_next_pos_of_singleton_preceding
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : S.gapLength j = 0)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    0 < S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
      S.forkSchurNextCoefficient weight p q e rho xf (S.step j) := by
  apply S.forkSchurSelf_sub_next_pos_of_actual_precedingCore
    weight p q e rho xf yw j hp hq he hrho hw (hunit (S.step j))
    (hxf (S.step j)) (hyw (S.step j))
  let Pnext : SourceWrapForkGap (S.gap (S.step j))
      (S.fork (S.step j)) (S.fork (S.step (S.step j)))
      ((S.gap j).idx (Fin.last (S.gapLength j))) := by
    have heq :
        (S.gap (S.step.symm (S.step j))).idx
            (Fin.last (S.gapLength (S.step.symm (S.step j)))) =
          (S.gap j).idx (Fin.last (S.gapLength j)) := by
      rw [S.step.symm_apply_apply]
    exact heq ▸ S.wrap (S.step j)
  exact SourceWrapForkGap.singleton_precedingCore_pos
    (P := S.wrap j) hm (Pnext := Pnext)
    weight p q e rho (xf j) (yw j) hp hq he hrho (hunit j)
    (hxf j) (hyw j)

/-- Every literal preceding trace, whether the identity-length base or an
iterated positive path, supplies the same strict cyclic diagonal margin. -/
theorem forkSchurSelf_sub_next_pos_of_actual_responses
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    0 < S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
      S.forkSchurNextCoefficient weight p q e rho xf (S.step j) := by
  by_cases hm : S.gapLength j = 0
  · exact S.forkSchurSelf_sub_next_pos_of_singleton_preceding
      weight p q e rho xf yw j hm hp hq he hrho hw hunit hxf hyw
  · apply S.forkSchurSelf_sub_next_pos_of_actual_precedingCore
      weight p q e rho xf yw j hp hq he hrho hw (hunit (S.step j))
      (hxf (S.step j)) (hyw (S.step j))
    exact S.positive_precedingCore_pos weight p q e rho xf j
      (Nat.pos_of_ne_zero hm) hp hq he hrho hw (hunit j) (hxf j)

/-- Length-uniform sign package for the genuine cyclic Schur row, stated
solely with actual adjacent-fork columns. -/
theorem forkSchur_cyclic_signs_of_actual_responses
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a)) :
    0 < S.forkSchurNextCoefficient weight p q e rho xf j ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j -
        S.forkSchurNextCoefficient weight p q e rho xf j ∧
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw j ∧
      S.forkSchurNextCoefficient weight p q e rho xf j ≤
        S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  have hnext := S.forkSchurNextCoefficient_pos_of_actual_response
    weight p q e rho xf j hp hq he hrho hw (hunit j) (hxf j)
  have hmargin := S.forkSchurSelf_sub_next_pos_of_actual_responses
    weight p q e rho xf yw (S.step.symm j) hp hq he hrho hw hunit hxf hyw
  rw [S.step.apply_symm_apply] at hmargin
  exact ⟨hnext, hmargin, by linarith, le_of_lt (by linarith)⟩

/-- The signed-seam combined cone is length-uniform once its local minor is
stated in actual boundary-port coordinates. -/
theorem forkSector_combined_cone_of_actual_responses
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
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
  have hsigns := fun a =>
    S.forkSchur_cyclic_signs_of_actual_responses weight p q e rho xf yw a
      hp hq he hrho hw hunit hxf hyw
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
    ring

/-- Positive determinant of the literal fork-sector matrix for arbitrary
paper-positive gap words, including identity-length traces. -/
theorem forkSectorMatrix_det_pos_of_actual_responses [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
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
    S.forkSector_combined_cone_of_actual_responses weight p q e rho xf yw
      J seamPred hp hq he hrho hw hunit hxf hyw hJ hprevOrdinary hresidual hlocal
  have hsigns := fun a =>
    S.forkSchur_cyclic_signs_of_actual_responses weight p q e rho xf yw a
      hp hq he hrho hw hunit hxf hyw
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

/-- A nonsingular actual-column fork sector kills the complete current
kernel without any gap-length or synthetic-forcing premise. -/
theorem globalCurrentSecantKernel_eq_zero_of_actual_forkSector_det [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
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
    exact SourceWrapGlobalColumnClosed.internal_coordinates_eq_negative_actual_responses_of_kernel
      (S.globalColumnClosed a) weight p q e rho hp hq he hrho hw x
        (xf a) (yw a) (hxf a) (hyw a) hker i
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

/-- Weak-gap analytic Type II_l closure.  Once source combinatorics supplies
the unique seam, ordinary predecessor signs, positive current residual, and
the oriented local minor, two positive stationary states have ratio one.
All gap responses and kernel reconstruction use literal columns. -/
theorem ratios_eq_one_of_weak_gap_actual_combined_cone [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (seamPred : Fin l)
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
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
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
    S.forkSectorMatrix_det_pos_of_actual_responses hl weight p q e rho xf yw
      J seamPred hp hq he hrho hw hunit hxf hyw hJ hprevOrdinary hresidual hlocal
  have hself : ∀ a,
      0 < S.forkSchurSelfCoefficient weight p q e rho xf yw a := fun a =>
    (S.forkSchur_cyclic_signs_of_actual_responses weight p q e rho xf yw a
      hp hq he hrho hw hunit hxf hyw).2.2.1
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
    S.globalCurrentSecantKernel_eq_zero_of_actual_forkSector_det hprevnext
      weight p q e rho (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r))
      he hrho hw xf yw hxf hyw hself hdet x hker
  apply ratios_eq_one_of_twoRootCurrentDelta_eq_zero
    (sourceProductExponent next weight back) (sourceStoich next weight back)
    (fun i => ne_of_gt (he i)) hbase hratio
  intro r
  exact congrFun hx r

end SourceCyclicNonemptyGapSystem

end TypeIIL
