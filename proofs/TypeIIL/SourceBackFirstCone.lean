module

public import proofs.TypeIIL.SourceBackFirstResidual
public import proofs.TypeIIL.SourceCyclicCombinedCone

@[expose] public section

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-! The three boundary generators of the back-first reduced fork row.  They
are defined directly from the two adjacent gap ports; later lemmas identify
them with the corresponding entries of `backFirstReducedForkMatrix`. -/

noncomputable def backFirstForkPrevCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let pred := S.step.symm j
  0 - ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap pred).idx i) * yw pred i

noncomputable def backFirstForkSelfCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let pred := S.step.symm j
  S.backFirstCurrentMatrix weight p q e rho (S.fork j) (S.fork j) -
    (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap pred).idx i) * xf pred i) -
    ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * yw j i

noncomputable def backFirstForkNextCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  0 - ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * xf j i

/-- The adaptive successor port is the positive back-first boundary
coefficient times the forward Green response. -/
theorem backFirstForkNextCoefficient_eq_boundary_response
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    S.backFirstForkNextCoefficient weight p q e rho xf j =
      (q (S.fork j) *
        ((rho ((S.gap (S.step.symm j)).idx
              (Fin.last (S.gapLength (S.step.symm j)))) *
            TypeII3.secantPoly (rho (next (S.fork j))) 1
              (weight (S.fork j))) /
          e (next (S.fork j)))) * xf j 0 := by
  have hpost := (S.wrap j).post.backFirst_fork_postGap_mul
    weight p q e rho (xf j)
  unfold backFirstForkNextCoefficient backFirstCurrentMatrix
  rw [hpost]
  ring

/-- The forward response itself is strictly positive at the left boundary.
This is gauge-independent because the internal gap block and its forcing are
unchanged. -/
theorem forwardResponse_zero_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i) :
    0 < xf j 0 := by
  have hF := S.forkSchurNextCoefficient_pos weight p q e rho xf j hm
    hp hq he hrho hw hunit hxf
  have hEq := S.forkSchurNextCoefficient_eq_boundary_response
    weight p q e rho xf j hm
  rw [hEq] at hF
  have hk : 0 < q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j))) :=
    mul_pos (hq _) (div_pos
      (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  nlinarith

theorem backFirstForkNextCoefficient_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hxf : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        sourceWrapForwardForcing ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) i) :
    0 < S.backFirstForkNextCoefficient weight p q e rho xf j := by
  rw [S.backFirstForkNextCoefficient_eq_boundary_response
    weight p q e rho xf j]
  exact mul_pos (mul_pos (hq _)
      (div_pos (mul_pos (hrho _)
        (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _))) (he _)))
    (S.forwardResponse_zero_pos weight p q e rho xf j hm hp hq he
      hrho hw hunit hxf)

/-- Back-first terminal transport makes every predecessor port nonpositive;
the old ambient-order seam has disappeared. -/
theorem backFirstForkPrevCoefficient_nonpos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (j : Fin l) :
    S.backFirstForkPrevCoefficient weight p q e rho yw j ≤ 0 := by
  let pred := S.step.symm j
  let G := S.gap pred
  let y : Fin (S.gapLength pred + 1) → ℝ := fun i => -yw pred i
  let b : Fin (S.gapLength pred + 1) → ℝ := fun i =>
    -sourceWrapLeftForcing (G.gapA p e) (weight (S.fork pred)) i
  have hJFork : 0 < p (S.fork j) - q (S.fork j) :=
    S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit j
  have hpLast := S.terminal_rate_eq_of_base_balance
    weight p q e hbase j (hunit pred)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    unfold b sourceWrapLeftForcing
    split
    · simp only [neg_neg]
      exact mul_nonneg
        (G.gapA_nonneg (fun r => le_of_lt (hp r)) he i)
        (by exact_mod_cast Nat.zero_le (weight (S.fork pred)))
    · simp
  have hsolve : ∀ i,
      ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * y t = b i := by
    intro i
    have h := hyw pred i
    unfold y b
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    rw [h]
  have hcorr := (S.wrap pred).pre.backFirst_fork_preGap_correction_nonpos
    (hgap pred) weight p q e rho (p (S.fork j) - q (S.fork j))
    (hunit pred)
    (by rw [S.step.apply_symm_apply]; ring)
    (by simpa [pred] using hpLast) hp (fun r => le_of_lt (hq r))
    (hq _) (hq _) he hrho hw hJFork y b hb hsolve
  calc
    S.backFirstForkPrevCoefficient weight p q e rho yw j =
        ∑ i, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e
          (S.fork j) ((S.gap pred).idx i) * y i := by
      simp [backFirstForkPrevCoefficient, backFirstCurrentMatrix, pred, y,
        Finset.sum_neg_distrib]
    _ ≤ 0 := by simpa [pred, G] using hcorr

/-- The terminal-basis shift turns the mixed forward response into a
nonnegative forcing.  Back-first terminal transport then bounds its entire
preceding-port correction by the direct degradation/back budget, with no
ambient coordinate-order premise. -/
theorem backFirst_forward_correction_le_direct
    {m : ℕ} {G : SourceGapEmbedding next back m} {fork : Fin n}
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hpFork : p fork = q fork + JFork)
    (hpLast : p (G.idx (Fin.last m)) =
      q (G.idx (Fin.last m)) + e fork + JFork)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hJFork : 0 < JFork)
    (xf : Fin (m + 1) → ℝ)
    (hxf : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        sourceWrapForwardForcing (G.gapA p e)
          (G.gapC weight q e rho) i) :
    ∑ j, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * xf j ≤
      p fork / e fork + q fork / e (G.idx (Fin.last m)) := by
  let last : Fin (m + 1) := Fin.last m
  let y : Fin (m + 1) → ℝ := fun i =>
    xf i + if i = last then 1 else 0
  let b : Fin (m + 1) → ℝ := fun i => if i = last then 1 else 0
  have hunitR : G.gapS weight (Fin.last m) = 1 := by
    simp [SourceGapEmbedding.gapS, hunit]
  have hsolveFinite : ∀ i,
      ∑ j, finiteSourcePathMatrix (G.gapA p e)
          (G.gapC weight q e rho) (G.gapS weight) i j * xf j =
        sourceWrapForwardForcing (G.gapA p e)
          (G.gapC weight q e rho) i := by
    simpa [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] using hxf
  have hyFinite := finiteSourcePath_forward_add_terminal_solve hm
    (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight) xf
    hunitR hsolveFinite
  have hySolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i := by
    intro i
    rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    simpa [y, b, last] using hyFinite i
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    dsimp [b]
    split_ifs <;> norm_num
  have hcorr := P.backFirst_fork_preGap_correction_nonpos hm
    weight p q e rho JFork hunit hpFork hpLast hp
    (fun r => le_of_lt (hq r)) (hq _) (hq _) he hrho hw hJFork
    y b hb hySolve
  rw [P.backFirst_fork_preGap_mul hm weight p q e rho hunit y] at hcorr
  rw [P.backFirst_fork_preGap_mul hm weight p q e rho hunit xf]
  have hprevne :
      finitePathPrev (Fin.last m) (by simpa using hm) ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [finitePathPrev, last] at hv
    omega
  change finitePathPrev (Fin.last m) (by simpa using hm) ≠
    Fin.last m at hprevne
  dsimp [y, last] at hcorr
  rw [ite_eq_right hprevne] at hcorr
  simp only [ite_true] at hcorr
  ring_nf at hcorr ⊢
  linarith

/-- Exact uneliminated diagonal of a back-first fork row. -/
theorem sourceBackFirstCurrentMatrix_fork_diagonal
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {r z : Fin n} (hr : back r = some z) (hz : z ≠ next r)
    (hrn : r ≠ next r) (hzr : z ≠ r) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e r r =
      1 + p r / e r + q r *
        (((rho z * TypeII3.secantPoly (rho (next r)) 1 (weight r)) /
              e (next r)) * weight r + 1 / e z) := by
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back hr hz]
  rw [sourceStoich_source_entry next weight back hrn (by
    intro x hx
    rw [hr] at hx
    injection hx with hxz
    simpa [hxz] using hzr.symm)]
  rw [sourceStoich_successor_entry next weight back hrn.symm (by
    intro x hx
    rw [hr] at hx
    injection hx with hxz
    simpa [hxz] using hz.symm)]
  rw [sourceStoich_back_entry next weight back hr hzr hz]
  simp
  left
  ring

/-- The adaptive Schur diagonal retains at least the identity margin over its
successor port.  The preceding mixed response is absorbed by the direct
degradation/back budget, while the following two-port budget is nonnegative. -/
theorem backFirstForkSelf_sub_next_ge_one
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (j : Fin l) :
    1 ≤ S.backFirstForkSelfCoefficient weight p q e rho xf yw j -
      S.backFirstForkNextCoefficient weight p q e rho xf j := by
  let pred := S.step.symm j
  let z := (S.gap pred).idx (Fin.last (S.gapLength pred))
  let k := q (S.fork j) *
    ((rho z * TypeII3.secantPoly (rho (next (S.fork j))) 1
      (weight (S.fork j))) / e (next (S.fork j)))
  let g := p (S.fork j) / e (S.fork j)
  let h := q (S.fork j) / e z
  have hJFork : 0 < p (S.fork j) - q (S.fork j) :=
    S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit j
  have hpLast := S.terminal_rate_eq_of_base_balance
    weight p q e hbase j (hunit pred)
  have hpre := backFirst_forward_correction_le_direct
    (P := (S.wrap pred).pre) (hgap pred) weight p q e rho
    (p (S.fork j) - q (S.fork j))
    (hunit pred) (by rw [S.step.apply_symm_apply]; ring)
    (by simpa [pred] using hpLast) hp hq he hrho hw hJFork (xf pred)
    (hxf pred)
  have hdiag := sourceBackFirstCurrentMatrix_fork_diagonal
    (next := next) (back := back) weight p q e rho
    (r := S.fork j) (z := z)
    (by simpa [pred, z] using S.back_fork j)
    (by simpa [pred, z] using (S.wrap j).post.back_ne_next)
    (by simpa [pred] using (S.wrap pred).pre.fork_ne_next)
    (by simpa [pred, z] using (S.wrap pred).pre.terminal_ne_fork)
  have hpostY := (S.wrap j).post.backFirst_fork_postGap_mul
    weight p q e rho (yw j)
  have hpostX := (S.wrap j).post.backFirst_fork_postGap_mul
    weight p q e rho (xf j)
  have hAr : ∀ i, 0 ≤ (S.gap j).gapA p e i :=
    (S.gap j).gapA_nonneg (fun r => le_of_lt (hp r)) he
  have hcr : ∀ i, 0 ≤ (S.gap j).gapC weight q e rho i :=
    (S.gap j).gapC_nonneg (fun r => le_of_lt (hq r)) he hrho hw
  have hsr : ∀ i, 1 ≤ (S.gap j).gapS weight i :=
    (S.gap j).gapS_one_le hw
  have hscale : 1 ≤ (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (mul_pos (hrho _)
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _))) (he _)))
  have hxfFinite : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) ((S.gap j).gapS weight) i t *
          xf j t = sourceWrapForwardForcing ((S.gap j).gapA p e)
            ((S.gap j).gapC weight q e rho) i := by
    intro i
    rw [← (S.gap j).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hxf j i
  have hywFinite : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap j).gapA p e)
          ((S.gap j).gapC weight q e rho) ((S.gap j).gapS weight) i t *
          yw j t = sourceWrapLeftForcing ((S.gap j).gapA p e)
            (weight (S.fork j)) i := by
    intro i
    rw [← (S.gap j).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hyw j i
  have hfollow := finiteSourcePath_literal_following_budget_nonneg
    (hgap j) ((S.gap j).gapA p e) ((S.gap j).gapC weight q e rho)
    ((S.gap j).gapS weight) (xf j) (yw j) hAr hcr hsr hscale hk
    (by simpa [SourceGapEmbedding.gapS] using hunit j) hxfFinite hywFinite
  have hstepPred : S.step pred = j := by
    simp [pred]
  rw [hstepPred] at hpre
  change
    (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap pred).idx i) * xf pred i) ≤ g + h at hpre
  change S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork j) = _ at hdiag
  have hdiag' : S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork j) = 1 + g + h +
        k * weight (S.fork j) := by
    rw [hdiag]
    dsimp [g, h, k]
    ring
  change (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * yw j i) = -k * yw j 0 at hpostY
  change (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * xf j i) = -k * xf j 0 at hpostX
  change 0 ≤ k * ((weight (S.fork j) : ℝ) + yw j 0 - xf j 0) at hfollow
  unfold backFirstForkSelfCoefficient backFirstForkNextCoefficient
  rw [hdiag', hpostY, hpostX]
  dsimp only [pred]
  linarith

end SourceCyclicNonemptyGapSystem

end TypeIIL
