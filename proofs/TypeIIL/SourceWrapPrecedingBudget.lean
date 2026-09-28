module

public import proofs.TypeIIL.SourceWrapLiteralColumns
public import proofs.TypeIIL.SourceForkGapAdapter

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- Adding the terminal basis vector to the exceptional right-fork response
turns its mixed endpoint forcing into a single nonnegative terminal forcing.
This is the elementary comparison shift hidden by the raw Schur column. -/
theorem finiteSourcePath_forward_add_terminal_solve
    {m : ℕ} (hm : 0 < m) (A c s x : Fin (m + 1) → ℝ)
    (hunit : s (Fin.last m) = 1)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * x j =
        sourceWrapForwardForcing A c i) :
    ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j *
          (x j + if j = Fin.last m then 1 else 0) =
        if i = Fin.last m then 1 else 0 := by
  intro i
  calc
    (∑ j, finiteSourcePathMatrix A c s i j *
        (x j + if j = Fin.last m then 1 else 0)) =
        (∑ j, finiteSourcePathMatrix A c s i j * x j) +
        ∑ j, finiteSourcePathMatrix A c s i j *
          (if j = Fin.last m then 1 else 0) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ = sourceWrapForwardForcing A c i +
        ∑ j, finiteSourcePathMatrix A c s i j *
          (if j = Fin.last m then 1 else 0) := by rw [hsolve i]
    _ = _ := by
      have hbasis :
          (∑ j, finiteSourcePathMatrix A c s i j *
            (if j = Fin.last m then 1 else 0)) =
            finiteSourcePathMatrix A c s i (Fin.last m) := by simp
      rw [hbasis]
      unfold finiteSourcePathMatrix
      by_cases hit : i = Fin.last m
      · subst i
        have hpos : 0 < (Fin.last m).val := by simpa using hm
        have hn : ¬(Fin.last m).val < m := by simp
        have hprevne : Fin.last m ≠ finitePathPrev (Fin.last m) hpos := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [finitePathPrev] at hv
          omega
        have hlastNotPen : (Fin.last m).val ≠ m - 1 := by
          simp
          omega
        have hlastVal : (Fin.last m).val = m := by simp
        rw [ite_eq_left rfl, dite_eq_left hpos, ite_eq_right hprevne, dite_eq_right hn]
        unfold sourceWrapForwardForcing
        rw [ite_eq_right hlastNotPen, ite_eq_left hlastVal, ite_eq_left rfl]
        rw [hunit]
        ring
      · have him : i.val ≠ m := by
          intro h
          apply hit
          apply Fin.ext
          simpa using h
        have hinext : i.val < m := by omega
        have hprevne (hp : 0 < i.val) :
            finitePathPrev i hp ≠ Fin.last m := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [finitePathPrev] at hv
          omega
        by_cases hipen : i.val = m - 1
        · have hnext : finitePathNext i hinext = Fin.last m := by
            apply Fin.ext
            dsimp [finitePathNext]
            omega
          have hnextTerm :
              (if h : i.val < m then
                if Fin.last m = finitePathNext i h then -c i else 0
              else 0) = -c i := by
            rw [dite_eq_left hinext]
            rw [ite_eq_left hnext.symm]
          have hprevTerm :
              (if h : 0 < i.val then
                if Fin.last m = finitePathPrev i h then
                  -(A i * s (finitePathPrev i h)) else 0
              else 0) = 0 := by
            by_cases hp : 0 < i.val
            · rw [dite_eq_left hp, ite_eq_right (Ne.symm (hprevne hp))]
            · rw [dite_eq_right hp]
          rw [ite_eq_right (Ne.symm hit)]
          rw [hprevTerm, hnextTerm]
          unfold sourceWrapForwardForcing
          rw [ite_eq_left hipen, ite_eq_right hit]
          ring
        · have hnext : finitePathNext i hinext ≠ Fin.last m := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [finitePathNext] at hv
            omega
          have hnextTerm :
              (if h : i.val < m then
                if Fin.last m = finitePathNext i h then -c i else 0
              else 0) = 0 := by
            rw [dite_eq_left hinext]
            rw [ite_eq_right (Ne.symm hnext)]
          have hprevTerm :
              (if h : 0 < i.val then
                if Fin.last m = finitePathPrev i h then
                  -(A i * s (finitePathPrev i h)) else 0
              else 0) = 0 := by
            by_cases hp : 0 < i.val
            · rw [dite_eq_left hp, ite_eq_right (Ne.symm (hprevne hp))]
            · rw [dite_eq_right hp]
          rw [ite_eq_right (Ne.symm hit)]
          rw [hprevTerm, hnextTerm]
          unfold sourceWrapForwardForcing
          rw [ite_eq_right hipen, ite_eq_right him, ite_eq_right hit]
          ring
/-- The mixed right-fork column cannot consume more than the direct diagonal
budget at the adjacent fork.  After the terminal-basis shift the claim is
exactly the already established nonnegative-forcing Green correction. -/
theorem SourcePreForkGap.forward_correction_le_direct_of_nonwrap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {fork : Fin n}
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (horder : (G.idx (Fin.last m)).val < (next fork).val)
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
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * xf j ≤
      p fork / e fork + q fork *
        (sourceForkBackCoeff next weight back rho fork
          (G.idx (Fin.last m)) / e (G.idx (Fin.last m))) := by
  let last : Fin (m + 1) := Fin.last m
  let y : Fin (m + 1) → ℝ := fun i => xf i + if i = last then 1 else 0
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
  have hcorr := P.fork_preGap_nonwrap_correction_nonpos hm
    weight p q e rho JFork hunit horder hpFork hpLast hp
    (fun r => le_of_lt (hq r)) (hq _) (hq _) he hrho hw hJFork
    y b hb hySolve
  rw [P.fork_preGap_mul hm weight p q e rho hunit y] at hcorr
  rw [P.fork_preGap_mul hm weight p q e rho hunit xf]
  have hprevne :
      finitePathPrev (Fin.last m) (by simpa using hm) ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [finitePathPrev, last] at hv
    omega
  change finitePathPrev (Fin.last m) (by simpa using hm) ≠ Fin.last m at hprevne
  dsimp [y, last] at hcorr
  rw [ite_eq_right hprevne] at hcorr
  simp only [ite_true] at hcorr
  ring_nf at hcorr ⊢
  linarith

/-- Singleton version of the preceding-gap budget.  Here the terminal basis
is the only internal coordinate; its shifted response is `1/d > 0`. -/
theorem SourcePreForkGap.singleton_forward_correction_le_direct
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back 0} {fork : Fin n}
    (P : SourcePreForkGap G fork)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (xf : Fin 1 → ℝ)
    (hxf : ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j =
      -(G.gapA p e 0 + G.gapC weight q e rho 0)) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * xf j ≤
      p fork / e fork + q fork *
        (sourceForkBackCoeff next weight back rho fork (G.idx 0) /
          e (G.idx 0)) := by
  have hunitR : G.gapS weight 0 = 1 := by
    simp [SourceGapEmbedding.gapS, hunit]
  have hrow := hxf
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix,
    Fin.sum_univ_one] at hrow
  unfold finiteSourcePathMatrix at hrow
  simp only [Fin.val_zero, lt_self_iff_false, dite_false, add_zero] at hrow
  simp only [ite_true] at hrow
  rw [hunitR] at hrow
  have hA : 0 < G.gapA p e 0 := div_pos (hp _) (he _)
  have hc : 0 < G.gapC weight q e rho 0 := by
    have hw0 : 0 < weight (G.idx 0) := by omega
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) hw0)
      (he _))
  have hd : 0 < 1 + G.gapA p e 0 + G.gapC weight q e rho 0 := by
    positivity
  have hy : 0 ≤ xf 0 + 1 := by
    have hone :
        (1 + G.gapA p e 0 + G.gapC weight q e rho 0) * (xf 0 + 1) = 1 := by
      nlinarith [hrow]
    have hprod : 0 <
        (1 + G.gapA p e 0 + G.gapC weight q e rho 0) * (xf 0 + 1) := by
      rw [hone]
      norm_num
    exact le_of_lt (pos_of_mul_pos_right hprod (le_of_lt hd))
  have hcorr := P.fork_singletonGap_correction_nonpos weight p q e rho
    hunit (le_of_lt (hp fork)) (le_of_lt (hq fork)) (he _) (he _) hrho
    (fun _ => xf 0 + 1) (by simpa using hy)
  rw [Fin.sum_univ_one] at hcorr ⊢
  rw [P.fork_singletonGap_entry weight p q e rho hunit] at hcorr ⊢
  ring_nf at hcorr ⊢
  linarith

end TypeIIL
