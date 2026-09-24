import proofs.TypeIIL.SourceBackFirstClosure
import problem_workspaces.RAF_full_type_II_l_closure.SingletonSpliceScratch

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

end SourceCyclicNonemptyGapSystem

namespace SourcePreForkGap

variable {n : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back 0} {fork : Fin n}

/-- Back-first terminal entry of the identity-length preceding trace. -/
theorem backFirst_fork_singletonGap_entry
    (P : SourcePreForkGap G fork)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e fork (G.idx 0) =
      -(p fork / e fork + q fork / e (G.idx 0)) := by
  have hterm : next (G.idx 0) = fork := by
    simpa using P.terminal_next
  have hback : back fork = some (G.idx 0) := by
    simpa using P.fork_back
  have hznext : G.idx 0 ≠ next fork := P.terminal_ne_fork_successor
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back hback hznext]
  have hNfork : sourceStoich next weight back fork (G.idx 0) = 1 := by
    have hs := sourceStoich_successor_entry next weight back
      (G.idx_ne_next 0).symm (by simp [G.nonfork 0])
    rw [hterm, hunit] at hs
    convert hs using 1
    norm_num
  have hNnext : sourceStoich next weight back (next fork) (G.idx 0) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact P.fork_successor_outside 0
    · simpa [hterm] using P.fork_ne_next.symm
    · intro x hx
      simp [G.nonfork 0] at hx
  have hNz : sourceStoich next weight back (G.idx 0) (G.idx 0) = -1 :=
    sourceStoich_source_entry next weight back (G.idx_ne_next 0)
      (by simp [G.nonfork 0])
  rw [ite_eq_right (P.fork_ne_idx 0), hNfork, hNnext, hNz]
  ring

end SourcePreForkGap

namespace SourceSingletonForkGap

variable {n : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back 0}
  {left right leftBack : Fin n}

/-- Direct successor feedthrough of the identity trace in the back-first
gauge. -/
theorem backFirst_left_right_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e left right =
      q left * ((rho leftBack *
        TypeII3.secantPoly (rho (G.idx 0)) 1 (weight left)) /
          e (G.idx 0)) := by
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back
    P.post.fork_back P.post.back_ne_next]
  have hterm : next (G.idx 0) = right := by simpa using P.pre.terminal_next
  have hLR : left ≠ right := by
    simpa [hterm] using P.post.fork_not_successor 0
  have hNleft : sourceStoich next weight back left right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hLR
      P.right_successor_ne_left.symm
    intro x hx
    rw [P.pre.fork_back] at hx
    injection hx with hx
    subst x
    exact P.post.fork_outside 0
  have hNz : sourceStoich next weight back leftBack right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · simpa [hterm] using P.post.back_not_successor 0
    · exact P.right_successor_ne_leftBack.symm
    · intro x hx
      rw [P.pre.fork_back] at hx
      injection hx with hx
      subst x
      exact P.post.back_outside 0
  have hNfirst : sourceStoich next weight back (G.idx 0) right = 1 :=
    sourceStoich_back_entry next weight back P.pre.fork_back
      P.pre.terminal_ne_fork P.pre.terminal_ne_fork_successor
  rw [ite_eq_right hLR, hNleft, P.post.first_eq.symm, hNfirst, hNz]
  ring

/-- Direct predecessor feedthrough of the identity trace in the back-first
gauge. -/
theorem backFirst_right_left_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e right left =
      q right / e (G.idx 0) * weight left := by
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back
    P.pre.fork_back P.pre.terminal_ne_fork_successor]
  have hterm : next (G.idx 0) = right := by simpa using P.pre.terminal_next
  have hnextLeft : next left = G.idx 0 := P.post.first_eq.symm
  have hLR : right ≠ left := by
    simpa [hterm] using (P.post.fork_not_successor 0).symm
  have hNright : sourceStoich next weight back right left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hLR
    · simpa [hnextLeft] using P.pre.terminal_ne_fork.symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      subst x
      simpa [hterm] using (P.post.back_not_successor 0).symm
  have hNnext : sourceStoich next weight back (next right) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_successor_ne_left
    · simpa [hnextLeft] using P.pre.terminal_ne_fork_successor.symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      subst x
      exact P.right_successor_ne_leftBack
  have hNz : sourceStoich next weight back (G.idx 0) left = weight left := by
    rw [← hnextLeft]
    apply sourceStoich_successor_entry next weight back
    · simpa [hnextLeft] using (P.post.fork_outside 0).symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      simpa [hnextLeft, hx] using (P.post.back_outside 0).symm
  simp only [show (Fin.last 0 : Fin 1) = 0 by rfl]
  rw [ite_eq_right hLR, hNright, hNz, hNnext]
  ring

end SourceSingletonForkGap

namespace SourceWrapForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m}
  {left right leftBack : Fin n}

/-- The identity trace has a strictly positive back-first successor port.
The proof exposes the transmission factor `1 / (1 + A + c)`. -/
theorem backFirst_singleton_actual_next_pos
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
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e left right -
        ∑ i, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
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
  let k := q left * ((rho leftBack *
    TypeII3.secantPoly (rho (G.idx 0)) 1 (weight left)) / e (G.idx 0))
  have hA : 0 < A := div_pos (hp _) (he _)
  have hc : 0 < c := div_pos (hq _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hk : 0 < k := mul_pos (hq _)
    (div_pos (mul_pos (hrho _)
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _))) (he _))
  have hsolve := hxf (0 : Fin 1)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] at hsolve
  rw [PS.internal_diagonal weight p q e rho hunit,
    PS.internal_right_entry weight p q e rho hunit] at hsolve
  have hxf0 : xf 0 = -(A + c) / d := by
    dsimp [A, c, d] at hsolve ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith
  have hdirect := PS.backFirst_left_right_entry weight p q e rho
  have hgap := P.post.backFirst_fork_postGap_mul weight p q e rho xf
  rw [← P.post.first_eq] at hgap
  change currentSecantKernelMatrixWith
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back) p q e left right = k at hdirect
  change (∑ i, currentSecantKernelMatrixWith
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back) p q e left (G.idx i) * xf i) =
        -k * xf 0 at hgap
  rw [hdirect, hgap, hxf0]
  have hid : k - (-k) * (-(A + c) / d) = k / d := by
    field_simp
    dsimp [d]
    ring
  rw [hid]
  exact div_pos hk hd

/-- The identity trace also obeys the same nonpositive predecessor transport
law as every extended path. -/
theorem backFirst_singleton_actual_prev_nonpos
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hpFork : p right = q right + JFork)
    (hpLast : p (G.idx (Fin.last m)) =
      q (G.idx (Fin.last m)) + e right + JFork)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hJFork : 0 < JFork)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (yw : Fin (m + 1) → ℝ)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) left) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e right left -
      ∑ i, currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e right (G.idx i) * yw i ≤ 0 := by
  subst m
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let g := p right / e right
  let h := q right / e (G.idx 0)
  let s : ℝ := weight left
  have hA : 0 < A := div_pos (hp _) (he _)
  have hc : 0 < c := div_pos (hq _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsolve := hyw (0 : Fin 1)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] at hsolve
  rw [PS.internal_diagonal weight p q e rho hunit,
    PS.internal_left_entry weight p q e rho] at hsolve
  have hyw0 : yw 0 = -(A * s) / d := by
    dsimp [A, c, d, s] at hsolve ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith
  have htransport := source_terminal_transport
    (eBack := e (G.idx 0)) (eFork := e right)
    (qLast := q (G.idx 0)) (qFork := q right)
    (JFork := JFork) (s := s) (he _) (he _) (hq _) (hq _) hJFork hs
  have htransport' : h * s * d ≤ (g + h) * (s * A) := by
    have hpLast0 : p (G.idx 0) = q (G.idx 0) + e right + JFork := by
      simpa using hpLast
    dsimp [h, g, d, c, A]
    rw [hpFork, hpLast0]
    simpa [mul_assoc] using htransport
  have hdirect := PS.backFirst_right_left_entry weight p q e rho
  have hgap := P.pre.backFirst_fork_singletonGap_entry weight p q e rho hunit
  change currentSecantKernelMatrixWith
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back) p q e right left = h * s at hdirect
  change currentSecantKernelMatrixWith
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back) p q e right (G.idx 0) =
        -(g + h) at hgap
  rw [Fin.sum_univ_one, hdirect, hgap, hyw0]
  have hscaled : h * s ≤ (g + h) * (s * A) / d :=
    (le_div_iff₀ hd).2 (by simpa [mul_assoc] using htransport')
  calc
    h * s - -(g + h) * (-(A * s) / d) =
        h * s - (g + h) * (s * A) / d := by ring
    _ ≤ 0 := sub_nonpos.mpr hscaled

/-- Direct back-first feedthrough is a Kronecker term: it is present exactly
for the identity trace and vanishes after any path extension. -/
theorem backFirst_left_right_entry_eq_directFeedthrough
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e left right =
      if m = 0 then q left * ((rho leftBack *
        TypeII3.secantPoly (rho (next left)) 1 (weight left)) /
          e (next left)) else 0 := by
  by_cases hm : m = 0
  · subst m
    let PS : SourceSingletonForkGap G left right leftBack :=
      { pre := P.pre
        post := P.post
        right_successor_ne_left := P.right_successor_ne_left
        right_successor_ne_leftBack := P.right_successor_ne_leftBack }
    rw [ite_eq_left rfl]
    have h := PS.backFirst_left_right_entry weight p q e rho
    simpa [P.post.first_eq] using h
  · rw [ite_eq_right hm]
    rw [sourceBackFirstCurrentMatrix_fork_entry next weight back
      P.post.fork_back P.post.back_ne_next]
    have hLR : left ≠ right := P.left_ne_right
    have hNleft : sourceStoich next weight back left right = 0 := by
      apply sourceStoich_eq_zero_of_off_support next weight back hLR
        P.right_successor_ne_left.symm
      intro z hz
      rw [P.pre.fork_back] at hz
      injection hz with hz
      subst z
      exact P.post.fork_outside (Fin.last m)
    have hNfirst : sourceStoich next weight back (next left) right = 0 := by
      rw [← P.post.first_eq]
      apply sourceStoich_eq_zero_of_off_support next weight back
      · exact P.pre.fork_ne_idx 0 |>.symm
      · exact P.pre.fork_successor_outside 0 |>.symm
      · intro z hz
        rw [P.pre.fork_back] at hz
        injection hz with hz
        subst z
        exact SourceWrapForkGap.first_ne_terminal G (Nat.pos_of_ne_zero hm)
    have hNback : sourceStoich next weight back leftBack right = 0 := by
      apply sourceStoich_eq_zero_of_off_support next weight back
      · exact P.right_ne_leftBack.symm
      · exact P.right_successor_ne_leftBack.symm
      · intro z hz
        rw [P.pre.fork_back] at hz
        injection hz with hz
        subst z
        exact P.post.back_outside (Fin.last m)
    rw [ite_eq_right hLR, hNleft, hNback, hNfirst]
    ring

/-- The forward response of the identity trace consumes no more than the
direct degradation/back budget. -/
theorem backFirst_singleton_forward_correction_le_direct
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (xf : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (G.idx i) right) :
    ∑ i, currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e right (G.idx i) * xf i ≤
      p right / e right + q right / e (G.idx (Fin.last m)) := by
  subst m
  let PS : SourceSingletonForkGap G left right leftBack :=
    { pre := P.pre
      post := P.post
      right_successor_ne_left := P.right_successor_ne_left
      right_successor_ne_leftBack := P.right_successor_ne_leftBack }
  let A := p (G.idx 0) / e (G.idx 0)
  let c := q (G.idx 0) / e right
  let d := 1 + A + c
  let g := p right / e right
  let h := q right / e (G.idx 0)
  have hA : 0 < A := div_pos (hp _) (he _)
  have hc : 0 < c := div_pos (hq _) (he _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hgh : 0 ≤ g + h := by
    exact add_nonneg (le_of_lt (div_pos (hp _) (he _)))
      (le_of_lt (div_pos (hq _) (he _)))
  have hsolve := hxf (0 : Fin 1)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] at hsolve
  rw [PS.internal_diagonal weight p q e rho hunit,
    PS.internal_right_entry weight p q e rho hunit] at hsolve
  have hxf0 : xf 0 = -(A + c) / d := by
    dsimp [A, c, d] at hsolve ⊢
    apply (eq_div_iff (ne_of_gt hd)).2
    linarith
  have hgap := P.pre.backFirst_fork_singletonGap_entry weight p q e rho hunit
  change currentSecantKernelMatrixWith
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back) p q e right (G.idx 0) =
        -(g + h) at hgap
  rw [Fin.sum_univ_one, hgap, hxf0]
  have hfrac : (A + c) / d ≤ 1 := by
    apply (div_le_one₀ hd).2
    dsimp [d]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfrac hgh
  calc
    -(g + h) * (-(A + c) / d) = (g + h) * ((A + c) / d) := by ring
    _ ≤ (g + h) * 1 := hmul
    _ = g + h := by ring

/-- A singleton preceding trace is still a passive Green block: nonnegative
forcing produces a nonnegative internal lift, while its back-first boundary
coefficient is nonpositive. -/
theorem backFirst_singleton_preGap_green_correction_nonpos
    (P : SourceWrapForkGap G left right leftBack) (hm : m = 0)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (y b : Fin (m + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    ∑ i, currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e right (G.idx i) * y i ≤ 0 := by
  subst m
  have hsolveFinite : ∀ i, ∑ j,
      finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
        (G.gapS weight) i j * y j = b i := by
    simpa [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] using hsolve
  have hy := zmatrix_solution_nonneg
    (finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
      (G.gapS weight))
    (finiteSourcePathWeight (G.gapS weight)) y b
    (finiteSourcePathMatrix_offdiag_nonpos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg (fun r => le_of_lt (hq r)) he hrho hw)
      (fun i => le_of_lt (G.gapS_pos hw i)))
    (finiteSourcePathWeight_pos (G.gapS_pos hw))
    (finiteSourcePathMatrix_mul_weight_pos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg (fun r => le_of_lt (hq r)) he hrho hw)
      (G.gapS_pos hw)) hb hsolveFinite
  have hentry := P.pre.backFirst_fork_singletonGap_entry
    weight p q e rho hunit
  rw [Fin.sum_univ_one, hentry]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (add_nonneg
      (le_of_lt (div_pos (hp _) (he _)))
      (le_of_lt (div_pos (hq _) (he _))))) (hy 0)

end SourceWrapForkGap

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-! Length-uniform boundary generators.  The direct fork-to-fork term is part
of the port; it is zero after a nontrivial path extension and is the required
feedthrough for a singleton block. -/

noncomputable def backFirstActualForkPrevCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  let pred := S.step.symm j
  S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork pred) -
    ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap pred).idx i) * yw pred i

noncomputable def backFirstActualForkSelfCoefficient
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

noncomputable def backFirstActualForkNextCoefficient
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork (S.step j)) -
    ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * xf j i

/-- Schur elimination against literal adjacent-fork columns produces the same
three-port row for every gap length. -/
theorem backFirstReducedForkMatrix_mulVec_eq_actual_three_term
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (v : Fin l → ℝ) (j : Fin l) :
    ∑ b, S.backFirstReducedForkMatrix weight p q e rho xf yw j b * v b =
      S.backFirstActualForkPrevCoefficient weight p q e rho yw j *
          v (S.step.symm j) +
        S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j * v j +
        S.backFirstActualForkNextCoefficient weight p q e rho xf j *
          v (S.step j) := by
  let M := S.backFirstCurrentMatrix weight p q e rho
  let pred := S.step.symm j
  have hpoint : ∀ a i,
      ∑ b,
          (M (S.fork j) ((S.gap a).idx i) *
              ((if b = a then yw a i else 0) +
                if b = S.step a then xf a i else 0)) * v b =
        M (S.fork j) ((S.gap a).idx i) *
          (yw a i * v a + xf a i * v (S.step a)) := by
    intro a i
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have htriple :
      ∑ b, (∑ a, ∑ i,
          M (S.fork j) ((S.gap a).idx i) *
            ((if b = a then yw a i else 0) +
              if b = S.step a then xf a i else 0)) * v b =
        ∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (yw a i * v a + xf a i * v (S.step a)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact hpoint a i
  have hjnext : j ≠ S.step j := by
    intro h
    exact (S.wrap j).left_ne_right (congrArg S.fork h)
  have hprevj : pred ≠ j := by
    intro h
    have hs := congrArg S.step h
    exact hjnext (by simpa [pred] using hs)
  have hFork :
      (∑ b, M (S.fork j) (S.fork b) * v b) =
        M (S.fork j) (S.fork pred) * v pred +
          M (S.fork j) (S.fork j) * v j +
          M (S.fork j) (S.fork (S.step j)) * v (S.step j) := by
    apply sum_eq_three_of_zero pred j (S.step j)
      hprevj (hprevnext j) hjnext
    intro b hbprev hbj hbnext
    dsimp only [M]
    rw [S.backFirst_fork_row_other_fork_entry_zero
      weight p q e rho j b hbj hbnext hbprev]
    ring
  have hGap :
      (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (yw a i * v a + xf a i * v (S.step a))) =
        (∑ i, M (S.fork j) ((S.gap pred).idx i) *
          (yw pred i * v pred + xf pred i * v j)) +
        ∑ i, M (S.fork j) ((S.gap j).idx i) *
          (yw j i * v j + xf j i * v (S.step j)) := by
    let f : Fin l → ℝ := fun a =>
      ∑ i, M (S.fork j) ((S.gap a).idx i) *
        (yw a i * v a + xf a i * v (S.step a))
    have hf : ∀ a, a ≠ pred → a ≠ j → f a = 0 := by
      intro a hapred haj
      apply Finset.sum_eq_zero
      intro i _
      dsimp only [M]
      rw [S.backFirst_fork_row_other_gap_entry_zero
        weight p q e rho j a i haj hapred]
      ring
    have hsum := sum_eq_two_of_zero pred j hprevj f hf
    change (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
        (yw a i * v a + xf a i * v (S.step a))) = _ at hsum
    dsimp only [f] at hsum
    rw [show S.step pred = j by simp [pred]] at hsum
    exact hsum
  unfold backFirstReducedForkMatrix
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  change (∑ b, M (S.fork j) (S.fork b) * v b) - _ = _
  rw [htriple, hFork, hGap]
  unfold backFirstActualForkPrevCoefficient
    backFirstActualForkSelfCoefficient backFirstActualForkNextCoefficient
  dsimp only [pred, M]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [sub_mul, Finset.sum_mul]
  ring_nf

/-- Direct feedthrough vanishes after a genuine path extension, so the
length-uniform successor generator reduces to the historical Green port. -/
theorem backFirstActualForkNextCoefficient_eq_of_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j) :
    S.backFirstActualForkNextCoefficient weight p q e rho xf j =
      S.backFirstForkNextCoefficient weight p q e rho xf j := by
  unfold backFirstActualForkNextCoefficient backFirstForkNextCoefficient
  rw [S.backFirst_fork_next_direct_zero weight p q e rho j hm]

/-- The successor port is strictly positive for every paper gap length. -/
theorem backFirstActualForkNextCoefficient_pos
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
    0 < S.backFirstActualForkNextCoefficient weight p q e rho xf j := by
  by_cases hm : S.gapLength j = 0
  · unfold backFirstActualForkNextCoefficient backFirstCurrentMatrix
    exact (S.wrap j).backFirst_singleton_actual_next_pos hm
      weight p q e rho hp hq he hrho hw hunit (xf j) hxf
  · rw [S.backFirstActualForkNextCoefficient_eq_of_pos weight p q e rho xf j
      (Nat.pos_of_ne_zero hm)]
    exact S.backFirstForkNextCoefficient_pos weight p q e rho xf j
      (Nat.pos_of_ne_zero hm) hp hq he hrho hw hunit
      (S.actual_right_response_eq_forward_forcing weight p q e rho xf j
        (Nat.pos_of_ne_zero hm) hunit hxf)

/-- On an extended preceding trace, the literal direct term is zero. -/
theorem backFirstActualForkPrevCoefficient_eq_of_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength (S.step.symm j)) :
    S.backFirstActualForkPrevCoefficient weight p q e rho yw j =
      S.backFirstForkPrevCoefficient weight p q e rho yw j := by
  unfold backFirstActualForkPrevCoefficient backFirstForkPrevCoefficient
  dsimp only
  rw [S.backFirst_fork_prev_direct_zero weight p q e rho j hm]

/-- Terminal transport for an extended preceding trace, requiring positivity
only of that trace rather than a global gap-length assumption. -/
theorem backFirstForkPrevCoefficient_nonpos_of_pred_pos
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
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
    (j : Fin l) (hm : 0 < S.gapLength (S.step.symm j)) :
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
  have hleft := S.actual_left_response_eq_left_forcing
    weight p q e rho yw pred (hyw pred)
  have hsolve : ∀ i,
      ∑ t, G.restrictedCurrentMatrix weight p q e rho i t * y t = b i := by
    intro i
    have h := hleft i
    unfold y b
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    rw [h]
  have hcorr := (S.wrap pred).pre.backFirst_fork_preGap_correction_nonpos
    (by simpa [pred] using hm) weight p q e rho
    (p (S.fork j) - q (S.fork j)) (hunit pred)
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

/-- The predecessor port is nonpositive for every paper gap length. -/
theorem backFirstActualForkPrevCoefficient_nonpos
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
    (hyw : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork a))
    (j : Fin l) :
    S.backFirstActualForkPrevCoefficient weight p q e rho yw j ≤ 0 := by
  let pred := S.step.symm j
  by_cases hm : S.gapLength pred = 0
  · have hJFork : 0 < p (S.fork j) - q (S.fork j) :=
      S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit j
    have hpLast := S.terminal_rate_eq_of_base_balance
      weight p q e hbase j (hunit pred)
    unfold backFirstActualForkPrevCoefficient backFirstCurrentMatrix
    have h := (S.wrap pred).backFirst_singleton_actual_prev_nonpos hm
      weight p q e rho (p (S.fork j) - q (S.fork j))
      (by rw [S.step.apply_symm_apply]; ring)
      (by simpa [pred] using hpLast) hp hq he hJFork (hunit pred)
      (yw pred) (hyw pred)
    simpa [pred] using h
  · rw [S.backFirstActualForkPrevCoefficient_eq_of_pos weight p q e rho yw j
      (by simpa [pred] using Nat.pos_of_ne_zero hm)]
    exact S.backFirstForkPrevCoefficient_nonpos_of_pred_pos
      weight p q e rho yw hbase hp hq he hrho hw hunit hyw j
      (by simpa [pred] using Nat.pos_of_ne_zero hm)

/-- Literal adjacent-fork response columns reconstruct the internal part of
the base current for every gap length.  This removes the synthetic forcing
interface, and with it the artificial positive-length hypothesis. -/
theorem backFirstActualGapLift_solve_defect
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
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
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t *
        S.backFirstGapLift p q xf yw a t =
      S.backFirstGapDefect weight p q e rho a i := by
  let MO := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let MB := S.backFirstCurrentMatrix weight p q e rho
  let G := S.gap a
  let P := S.wrap a
  have hrowEq : ∀ k, MB (G.idx i) k = MO (G.idx i) k := by
    intro k
    exact sourceBackFirstCurrentMatrix_nonfork_eq_ordered next weight back
      (G.nonfork i) k
  have hsum := sum_eq_embedding_sum_add_two G.idx (S.fork a)
    (S.fork (S.step a))
    (fun k => MO (G.idx i) k * (p k - q k))
    (fun j => P.post.fork_outside j)
    (fun j => P.pre.fork_ne_idx j) P.left_ne_right
    (fun k hkl hkr hkg => by
      have hz := (S.globalColumnClosed a).entry_zero
        weight p q e rho i k hkl hkr hkg
      change MO (G.idx i) k = 0 at hz
      change MO (G.idx i) k * (p k - q k) = 0
      rw [hz]
      ring)
  have hD : ∀ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t =
        MO (G.idx i) (G.idx t) := by
    intro t
    rfl
  have hywMO :
      ∑ t, MO (G.idx i) (G.idx t) * yw a t =
        MO (G.idx i) (S.fork a) := by
    change ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t *
        yw a t = currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          ((S.gap a).idx i) (S.fork a)
    exact hyw a i
  have hxfMO :
      ∑ t, MO (G.idx i) (G.idx t) * xf a t =
        MO (G.idx i) (S.fork (S.step a)) := by
    change ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t *
        xf a t = currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          ((S.gap a).idx i) (S.fork (S.step a))
    exact hxf a i
  unfold backFirstGapLift backFirstGapDefect
  simp_rw [hD]
  change _ = ∑ k, MB (G.idx i) k * (p k - q k)
  rw [show (∑ k, MB (G.idx i) k * (p k - q k)) =
      ∑ k, MO (G.idx i) k * (p k - q k) by
    apply Finset.sum_congr rfl
    intro k _
    rw [hrowEq k]]
  rw [hsum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hywMO, hxfMO]

/-- Every eliminated literal gap contributes a nonpositive fork correction,
uniformly down to the singleton boundary trace. -/
theorem backFirstActualGapCorrection_nonpos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
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
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (j a : Fin l) :
    S.backFirstGapCorrection weight p q e rho xf yw j a ≤ 0 := by
  by_cases haj : a = j
  · subst a
    unfold backFirstGapCorrection backFirstCurrentMatrix
    apply (S.wrap j).post.backFirst_fork_postGap_green_correction_nonpos
      weight p q e rho hp (fun r => le_of_lt (hq r)) he hrho hw
      (S.backFirstGapLift p q xf yw j)
      (S.backFirstGapDefect weight p q e rho j)
    · exact S.backFirstGapDefect_nonneg weight p q e rho hbase
        (fun r => le_of_lt (hq r)) he hrho hw j
    · exact S.backFirstActualGapLift_solve_defect weight p q e rho xf yw
        hxf hyw j
  · by_cases hapred : a = S.step.symm j
    · subst a
      let pred := S.step.symm j
      by_cases hm : S.gapLength pred = 0
      · have hcorr :=
          (S.wrap pred).backFirst_singleton_preGap_green_correction_nonpos hm
            weight p q e rho hp hq he hrho hw (hunit pred)
            (S.backFirstGapLift p q xf yw pred)
            (S.backFirstGapDefect weight p q e rho pred)
            (S.backFirstGapDefect_nonneg weight p q e rho hbase
              (fun r => le_of_lt (hq r)) he hrho hw pred)
            (S.backFirstActualGapLift_solve_defect weight p q e rho xf yw
              hxf hyw pred)
        simpa [backFirstGapCorrection, backFirstCurrentMatrix, pred] using hcorr
      · have hJFork : 0 < p (S.fork j) - q (S.fork j) :=
          S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit j
        have hpLast := S.terminal_rate_eq_of_base_balance
          weight p q e hbase j (hunit pred)
        have hcorr := (S.wrap pred).pre.backFirst_fork_preGap_correction_nonpos
          (Nat.pos_of_ne_zero hm) weight p q e rho
          (p (S.fork j) - q (S.fork j)) (hunit pred)
          (by rw [S.step.apply_symm_apply]; ring)
          (by simpa [pred] using hpLast) hp (fun r => le_of_lt (hq r))
          (hq _) (hq _) he hrho hw hJFork
          (S.backFirstGapLift p q xf yw pred)
          (S.backFirstGapDefect weight p q e rho pred)
          (S.backFirstGapDefect_nonneg weight p q e rho hbase
            (fun r => le_of_lt (hq r)) he hrho hw pred)
          (S.backFirstActualGapLift_solve_defect weight p q e rho xf yw
            hxf hyw pred)
        simpa [backFirstGapCorrection, backFirstCurrentMatrix, pred] using hcorr
    · unfold backFirstGapCorrection
      apply Finset.sum_nonpos
      intro i _
      rw [S.backFirst_fork_row_other_gap_entry_zero weight p q e rho
        j a i haj hapred]
      simp

/-- The positive fork-current vector is a strict supersolution for the
length-uniform reduced operator.  Gap elimination cannot consume the strict
fork defect because every Green correction is nonpositive. -/
theorem backFirstActualReducedForkMatrix_mul_baseCurrent_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
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
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (j : Fin l) :
    0 < ∑ b, S.backFirstReducedForkMatrix weight p q e rho xf yw j b *
      (p (S.fork b) - q (S.fork b)) := by
  rw [S.backFirstReducedForkMatrix_mul_baseCurrent weight p q e rho xf yw j]
  have hfork := S.backFirstForkDefect_pos weight p q e rho hbase hq he
    hrho hw j
  have hcorrection :
      ∑ a, S.backFirstGapCorrection weight p q e rho xf yw j a ≤ 0 := by
    apply Finset.sum_nonpos
    intro a _
    exact S.backFirstActualGapCorrection_nonpos weight p q e rho xf yw hxf hyw
      hbase hp hq he hrho hw hunit j a
  linarith

/-- The preceding forward correction is controlled by the same direct
degradation/back budget for every paper gap length.  For an extended trace
this is terminal transport; for the singleton trace it is the scalar
Green-function identity proved above. -/
theorem backFirst_actual_forward_correction_le_direct
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hxf : ∀ a i, ∑ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            ((S.gap a).idx i) (S.fork (S.step a)))
    (a : Fin l) :
    ∑ i, S.backFirstCurrentMatrix weight p q e rho
        (S.fork (S.step a)) ((S.gap a).idx i) * xf a i ≤
      p (S.fork (S.step a)) / e (S.fork (S.step a)) +
        q (S.fork (S.step a)) /
          e ((S.gap a).idx (Fin.last (S.gapLength a))) := by
  by_cases hm : S.gapLength a = 0
  · have hs := (S.wrap a).backFirst_singleton_forward_correction_le_direct hm
      weight p q e rho hp hq he (hunit a) (xf a) (hxf a)
    simpa [backFirstCurrentMatrix] using hs
  · have hmpos : 0 < S.gapLength a := Nat.pos_of_ne_zero hm
    have hJFork : 0 < p (S.fork (S.step a)) - q (S.fork (S.step a)) :=
      S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit
        (S.step a)
    have hpLast := S.terminal_rate_eq_of_base_balance
      weight p q e hbase (S.step a) (hunit (S.step.symm (S.step a)))
    rw [S.step.symm_apply_apply] at hpLast
    have hs := backFirst_forward_correction_le_direct
      (P := (S.wrap a).pre) hmpos weight p q e rho
      (p (S.fork (S.step a)) - q (S.fork (S.step a))) (hunit a)
      (by ring) (by simpa using hpLast) hp hq he hrho hw hJFork (xf a)
      (S.actual_right_response_eq_forward_forcing weight p q e rho xf a
        hmpos (hunit a) (hxf a))
    simpa [backFirstCurrentMatrix] using hs

/-- Length-uniform diagonal-margin generator.  Eliminating any passive gap,
including the singleton trace with direct feedthrough, leaves at least the
identity margin over the successor port. -/
theorem backFirstActualForkSelf_sub_next_ge_one
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
    (j : Fin l) :
    1 ≤ S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j -
      S.backFirstActualForkNextCoefficient weight p q e rho xf j := by
  let pred := S.step.symm j
  let z := (S.gap pred).idx (Fin.last (S.gapLength pred))
  let k := q (S.fork j) *
    ((rho z * TypeII3.secantPoly (rho (next (S.fork j))) 1
      (weight (S.fork j))) / e (next (S.fork j)))
  let g := p (S.fork j) / e (S.fork j)
  let h := q (S.fork j) / e z
  have hpre := S.backFirst_actual_forward_correction_le_direct
    weight p q e rho xf hbase hp hq he hrho hw hunit hxf pred
  have hstepPred : S.step pred = j := by simp [pred]
  rw [hstepPred] at hpre
  change
    (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap pred).idx i) * xf pred i) ≤ g + h at hpre
  have hdiag := sourceBackFirstCurrentMatrix_fork_diagonal
    (next := next) (back := back) weight p q e rho
    (r := S.fork j) (z := z)
    (by simpa [pred, z] using S.back_fork j)
    (by simpa [pred, z] using (S.wrap j).post.back_ne_next)
    (by simpa [pred] using (S.wrap pred).pre.fork_ne_next)
    (by simpa [pred, z] using (S.wrap pred).pre.terminal_ne_fork)
  change S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork j) = _ at hdiag
  have hdiag' : S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork j) = 1 + g + h +
        k * weight (S.fork j) := by
    rw [hdiag]
    dsimp [g, h, k]
    ring
  have hpostY := (S.wrap j).post.backFirst_fork_postGap_mul
    weight p q e rho (yw j)
  have hpostX := (S.wrap j).post.backFirst_fork_postGap_mul
    weight p q e rho (xf j)
  change (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * yw j i) = -k * yw j 0 at hpostY
  change (∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap j).idx i) * xf j i) = -k * xf j 0 at hpostX
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (mul_pos (hrho _)
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _))) (he _)))
  have hfollow := (S.wrap j).actual_following_budget_nonneg
    weight p q e rho hp hq he hrho hw (hunit j) (xf j) (yw j)
      (hxf j) (hyw j) hk
  change 0 ≤ k * ((weight (S.fork j) : ℝ) -
      (if S.gapLength j = 0 then 1 else 0) + yw j 0 - xf j 0) at hfollow
  have hdirect := (S.wrap j).backFirst_left_right_entry_eq_directFeedthrough
    weight p q e rho
  change S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork (S.step j)) =
        if S.gapLength j = 0 then k else 0 at hdirect
  unfold backFirstActualForkSelfCoefficient backFirstActualForkNextCoefficient
  rw [hdiag', hpostY, hpostX, hdirect]
  dsimp only [pred]
  by_cases hm : S.gapLength j = 0 <;>
    simp only [hm, ite_true, ite_false] at hfollow ⊢ <;>
    ring_nf at hfollow ⊢ <;> linarith

noncomputable def backFirstActualForkSectorAlpha
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  -S.backFirstActualForkPrevCoefficient weight p q e rho yw j /
    S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j

noncomputable def backFirstActualForkSectorGamma
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  S.backFirstActualForkNextCoefficient weight p q e rho xf j /
    S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j

noncomputable def backFirstActualForkSectorMatrix
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ) :
    Matrix (Fin l) (Fin l) ℝ :=
  cyclicSectorMatrix S.step
    (S.backFirstActualForkSectorAlpha weight p q e rho xf yw)
    (S.backFirstActualForkSectorGamma weight p q e rho xf yw)

theorem backFirstActualForkSectorAlpha_nonneg
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hprev : S.backFirstActualForkPrevCoefficient weight p q e rho yw j ≤ 0)
    (hself : 0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j) :
    0 ≤ S.backFirstActualForkSectorAlpha weight p q e rho xf yw j := by
  unfold backFirstActualForkSectorAlpha
  exact div_nonneg (neg_nonneg.mpr hprev) (le_of_lt hself)

theorem backFirstActualForkSectorGamma_pos_lt_one
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hnext : 0 < S.backFirstActualForkNextCoefficient weight p q e rho xf j)
    (hmargin : 1 ≤
      S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j -
        S.backFirstActualForkNextCoefficient weight p q e rho xf j) :
    0 < S.backFirstActualForkSectorGamma weight p q e rho xf yw j ∧
      S.backFirstActualForkSectorGamma weight p q e rho xf yw j < 1 := by
  have hself : 0 <
      S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j := by
    linarith
  have hnextSelf :
      S.backFirstActualForkNextCoefficient weight p q e rho xf j <
        S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j := by
    linarith
  unfold backFirstActualForkSectorGamma
  exact ⟨div_pos hnext hself, (div_lt_one hself).2 hnextSelf⟩

theorem backFirstActualForkSectorAlpha_lt_upper
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j)
    (hJprev : 0 < J (S.step.symm j))
    (hresidual : 0 <
      S.backFirstActualForkPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j) +
        S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j * J j +
        S.backFirstActualForkNextCoefficient weight p q e rho xf j *
          J (S.step j)) :
    S.backFirstActualForkSectorAlpha weight p q e rho xf yw j <
      cyclicSectorUpper S.step
        (S.backFirstActualForkSectorGamma weight p q e rho xf yw) J j := by
  unfold backFirstActualForkSectorAlpha backFirstActualForkSectorGamma
    cyclicSectorUpper
  apply (lt_div_iff₀ hJprev).2
  calc
    (-S.backFirstActualForkPrevCoefficient weight p q e rho yw j /
          S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j) *
        J (S.step.symm j) =
        (-S.backFirstActualForkPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j)) /
            S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j := by
              ring
    _ < J j +
        (S.backFirstActualForkNextCoefficient weight p q e rho xf j /
          S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j) *
            J (S.step j) := by
      apply (div_lt_iff₀ hself).2
      have hcancel :
          (J j +
              (S.backFirstActualForkNextCoefficient weight p q e rho xf j /
                S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j) *
                  J (S.step j)) *
              S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j =
            S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j * J j +
              S.backFirstActualForkNextCoefficient weight p q e rho xf j *
                J (S.step j) := by
        field_simp [ne_of_gt hself]
      rw [hcancel]
      nlinarith

/-- The normalized length-uniform fork operator has positive determinant.
There is no exceptional seam: nonnegative predecessor normalization and
`0 < gamma < 1` make the seam inequality automatic at any nominated row. -/
theorem backFirstActualForkSectorMatrix_det_pos [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
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
    (seam : Fin l) :
    0 < (S.backFirstActualForkSectorMatrix weight p q e rho xf yw).det := by
  let J : Fin l → ℝ := fun a => p (S.fork a) - q (S.fork a)
  have hJ : ∀ a, 0 < J a := by
    intro a
    exact S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit a
  have hnext : ∀ a,
      0 < S.backFirstActualForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstActualForkNextCoefficient_pos weight p q e rho xf a
      hp hq he hrho hw (hunit a) (hxf a)
  have hmargin : ∀ a, 1 ≤
      S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a -
        S.backFirstActualForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstActualForkSelf_sub_next_ge_one weight p q e rho xf yw
      hbase hp hq he hrho hw hunit hxf hyw a
  have hself : ∀ a,
      0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a := by
    intro a
    linarith [hnext a, hmargin a]
  have hprev : ∀ a,
      S.backFirstActualForkPrevCoefficient weight p q e rho yw a ≤ 0 := by
    intro a
    exact S.backFirstActualForkPrevCoefficient_nonpos weight p q e rho yw
      hbase hp hq he hrho hw hunit hyw a
  have hresidual : ∀ a, 0 <
      S.backFirstActualForkPrevCoefficient weight p q e rho yw a *
          J (S.step.symm a) +
        S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a * J a +
        S.backFirstActualForkNextCoefficient weight p q e rho xf a *
          J (S.step a) := by
    intro a
    have hred := S.backFirstActualReducedForkMatrix_mul_baseCurrent_pos
      weight p q e rho xf yw hxf hyw hbase hp hq he hrho hw hunit a
    have hthree := S.backFirstReducedForkMatrix_mulVec_eq_actual_three_term
      hprevnext weight p q e rho xf yw J a
    rw [hthree] at hred
    exact hred
  have hgamma : ∀ a,
      0 < S.backFirstActualForkSectorGamma weight p q e rho xf yw a ∧
        S.backFirstActualForkSectorGamma weight p q e rho xf yw a < 1 := by
    intro a
    exact S.backFirstActualForkSectorGamma_pos_lt_one weight p q e rho xf yw a
      (hnext a) (hmargin a)
  have halpha : ∀ a,
      0 ≤ S.backFirstActualForkSectorAlpha weight p q e rho xf yw a := by
    intro a
    exact S.backFirstActualForkSectorAlpha_nonneg weight p q e rho xf yw a
      (hprev a) (hself a)
  have halphaUpper : ∀ a,
      S.backFirstActualForkSectorAlpha weight p q e rho xf yw a <
        cyclicSectorUpper S.step
          (S.backFirstActualForkSectorGamma weight p q e rho xf yw) J a := by
    intro a
    exact S.backFirstActualForkSectorAlpha_lt_upper weight p q e rho xf yw J a
      (hself a) (hJ (S.step.symm a)) (hresidual a)
  have hlocal :
      (-S.backFirstActualForkSectorAlpha weight p q e rho xf yw seam) *
          S.backFirstActualForkSectorGamma weight p q e rho xf yw
            (S.cyclicIndexFrom seam (l - 1)) <
        1 - S.backFirstActualForkSectorGamma weight p q e rho xf yw seam := by
    rw [S.cyclicIndexFrom_pred_length (by omega)]
    have hleft :
        (-S.backFirstActualForkSectorAlpha weight p q e rho xf yw seam) *
            S.backFirstActualForkSectorGamma weight p q e rho xf yw
              (S.step.symm seam) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (halpha seam))
        (le_of_lt (hgamma (S.step.symm seam)).1)
    have hright :
        0 < 1 - S.backFirstActualForkSectorGamma weight p q e rho xf yw seam := by
      linarith [(hgamma seam).2]
    linarith
  simpa [backFirstActualForkSectorMatrix] using
    S.cyclicSectorMatrix_signed_seam_pos hl
      (S.backFirstActualForkSectorAlpha weight p q e rho xf yw)
      (S.backFirstActualForkSectorGamma weight p q e rho xf yw) J seam
      hgamma hJ (fun a _ => halpha a) halphaUpper hlocal

/-- Literal-column reconstruction is gauge invariant on internal rows.  It
works uniformly for singleton and extended gaps because the restricted Green
block is always nonsingular. -/
theorem backFirstActual_internal_coordinates_eq_negative_responses_of_kernel
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (x : Fin n → ℝ)
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
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))) := by
  intro a
  let G := S.gap a
  let P := S.wrap a
  let MO := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let MB := S.backFirstCurrentMatrix weight p q e rho
  let z : Fin (S.gapLength a + 1) → ℝ := fun i =>
    x (G.idx i) + yw a i * x (S.fork a) +
      xf a i * x (S.fork (S.step a))
  have hzero : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j = 0 := by
    intro i
    have hrowEq : ∀ k, MB (G.idx i) k = MO (G.idx i) k := by
      intro k
      exact sourceBackFirstCurrentMatrix_nonfork_eq_ordered next weight back
        (G.nonfork i) k
    have hsum := sum_eq_embedding_sum_add_two G.idx (S.fork a)
      (S.fork (S.step a)) (fun k => MO (G.idx i) k * x k)
      (fun j => P.post.fork_outside j)
      (fun j => P.pre.fork_ne_idx j) P.left_ne_right
      (fun k hkl hkr hkg => by
        have he0 := (S.globalColumnClosed a).entry_zero
          weight p q e rho i k hkl hkr hkg
        change MO (G.idx i) k = 0 at he0
        change MO (G.idx i) k * x k = 0
        rw [he0]
        ring)
    have hk := hker (G.idx i)
    change (∑ k, MB (G.idx i) k * x k) = 0 at hk
    have hrow :
        (∑ j, MO (G.idx i) (G.idx j) * x (G.idx j)) +
          MO (G.idx i) (S.fork a) * x (S.fork a) +
          MO (G.idx i) (S.fork (S.step a)) * x (S.fork (S.step a)) = 0 := by
      rw [← hsum]
      calc
        ∑ k, MO (G.idx i) k * x k =
            ∑ k, MB (G.idx i) k * x k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hrowEq k]
        _ = 0 := hk
    calc
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * z j =
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j *
            x (G.idx j)) +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw a j) *
            x (S.fork a) +
          (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf a j) *
            x (S.fork (S.step a)) := by
        dsimp [z]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [← mul_assoc]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = 0 := by
        rw [hyw a i, hxf a i]
        exact hrow
  have hz := G.restrictedCurrentMatrix_kernel_eq_zero weight p q e rho
    hp hq he hrho hw z hzero
  intro i
  have hi := hz i
  dsimp [z] at hi
  linarith

/-- Substituting literal-column reconstruction into a fork kernel row gives
the length-uniform three-port equation, including singleton feedthrough. -/
theorem backFirst_actual_fork_three_term_of_reconstruction
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hrec : ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))))
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    ∀ j : Fin l,
      S.backFirstActualForkPrevCoefficient weight p q e rho yw j *
          x (S.fork (S.step.symm j)) +
        S.backFirstActualForkSelfCoefficient weight p q e rho xf yw j *
          x (S.fork j) +
        S.backFirstActualForkNextCoefficient weight p q e rho xf j *
          x (S.fork (S.step j)) = 0 := by
  intro j
  let M := S.backFirstCurrentMatrix weight p q e rho
  let pred := S.step.symm j
  have hpre := sum_mul_negative_two_response
    (fun i => M (S.fork j) ((S.gap pred).idx i))
    (yw pred) (xf pred) (x (S.fork pred)) (x (S.fork j))
  have hpost := sum_mul_negative_two_response
    (fun i => M (S.fork j) ((S.gap j).idx i))
    (yw j) (xf j) (x (S.fork j)) (x (S.fork (S.step j)))
  have hsplit := S.backFirst_fork_kernel_row_split hprevnext
    weight p q e rho x hker j
  simp_rw [hrec] at hsplit
  simp only [S.step.apply_symm_apply] at hsplit
  change
    (∑ i, M (S.fork j) ((S.gap pred).idx i) *
      -(yw pred i * x (S.fork pred) + xf pred i * x (S.fork j))) = _ at hpre
  change
    (∑ i, M (S.fork j) ((S.gap j).idx i) *
      -(yw j i * x (S.fork j) + xf j i * x (S.fork (S.step j)))) = _ at hpost
  rw [hpre, hpost] at hsplit
  unfold backFirstActualForkPrevCoefficient backFirstActualForkSelfCoefficient
    backFirstActualForkNextCoefficient
  dsimp only [pred, M]
  linear_combination hsplit

/-- Positive determinant of the actual-column fork sector lifts through every
passive gap and kills the complete back-first current kernel. -/
theorem backFirstActualGlobalCurrentSecantKernel_eq_zero_of_sector_det
    [NeZero l]
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
      0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a)
    (hdet : 0 <
      (S.backFirstActualForkSectorMatrix weight p q e rho xf yw).det)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    x = 0 := by
  have hrec :=
    S.backFirstActual_internal_coordinates_eq_negative_responses_of_kernel
      weight p q e rho hp hq he hrho hw x xf yw hxf hyw hker
  have hraw := S.backFirst_actual_fork_three_term_of_reconstruction hprevnext
    weight p q e rho x xf yw hrec hker
  let z : Fin l → ℝ := fun a => x (S.fork a)
  have hsector : Matrix.mulVec
      (S.backFirstActualForkSectorMatrix weight p q e rho xf yw) z = 0 := by
    funext a
    change Matrix.mulVec
      (cyclicSectorMatrix S.step
        (S.backFirstActualForkSectorAlpha weight p q e rho xf yw)
        (S.backFirstActualForkSectorGamma weight p q e rho xf yw)) z a = 0
    rw [cyclicSectorMatrix_mulVec_apply]
    unfold backFirstActualForkSectorAlpha backFirstActualForkSectorGamma
    field_simp [ne_of_gt (hself a)]
    nlinarith [hraw a]
  have hz : z = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (ne_of_gt hdet) hsector
  have hfork : ∀ a : Fin l, x (S.fork a) = 0 := by
    intro a
    exact congrFun hz a
  funext k
  rcases S.cover k with ⟨a, rfl⟩ | ⟨a, i, rfl⟩
  · exact hfork a
  · rw [hrec a i, hfork a, hfork (S.step a)]
    simp

/-- Analytic source closure for every paper-legal gap length.  Two positive
stationary states generate a back-first current-kernel vector; passive
condensation and the cyclic determinant force every concentration ratio to
one. -/
theorem ratios_eq_one_of_backFirst_weak_gap [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
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
    (seam : Fin l) :
    ∀ i, rho i = 1 := by
  have hdet : 0 <
      (S.backFirstActualForkSectorMatrix weight p q e rho xf yw).det :=
    S.backFirstActualForkSectorMatrix_det_pos hl hprevnext weight p q e rho
      xf yw hbase hp hq he hrho hw hunit hxf hyw seam
  have hnext : ∀ a,
      0 < S.backFirstActualForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstActualForkNextCoefficient_pos weight p q e rho xf a
      hp hq he hrho hw (hunit a) (hxf a)
  have hmargin : ∀ a, 1 ≤
      S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a -
        S.backFirstActualForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstActualForkSelf_sub_next_ge_one weight p q e rho xf yw
      hbase hp hq he hrho hw hunit hxf hyw a
  have hself : ∀ a,
      0 < S.backFirstActualForkSelfCoefficient weight p q e rho xf yw a := by
    intro a
    linarith [hnext a, hmargin a]
  have hbackDistinct : ∀ r z, back r = some z → z ≠ next r := by
    intro r z hr
    rcases S.cover r with ⟨a, rfl⟩ | ⟨a, i, rfl⟩
    · rw [S.back_fork a] at hr
      injection hr with hz
      subst z
      simpa using (S.wrap a).post.back_ne_next
    · rw [(S.gap a).nonfork i] at hr
      contradiction
  let x : Fin n → ℝ :=
    twoRootCurrentDelta (sourceProductExponent next weight back) p q rho
  have hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0 := by
    intro r
    exact current_secant_kernel_row_with
      (sourceProductExponent next weight back)
      (sourceBackFirstSecantMatrix next weight back rho)
      (sourceStoich next weight back)
      (sourceBackFirstSecantMatrix_mul_ratio_sub_one next weight back rho
        hbackDistinct)
      (fun i => ne_of_gt (he i)) hbase hratio r
  have hx : x = 0 :=
    S.backFirstActualGlobalCurrentSecantKernel_eq_zero_of_sector_det hprevnext
      weight p q e rho (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r))
      he hrho hw xf yw hxf hyw hself hdet x hker
  apply ratios_eq_one_of_twoRootCurrentDelta_eq_zero
    (sourceProductExponent next weight back) (sourceStoich next weight back)
    (fun i => ne_of_gt (he i)) hbase hratio
  intro r
  exact congrFun hx r

/-- Witness-free length-uniform source theorem.  The two literal fork-column
responses are generated by the finite Green blocks, so only the stationary
equations and source-faithful cyclic structure remain in the interface. -/
theorem ratios_eq_one_of_backFirst_weak_gap_generated
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hbase : ∀ i,
      ∑ r, sourceStoich next weight back i r * (p r - q r) = e i)
    (hratio : ∀ i,
      ∑ r, sourceStoich next weight back i r *
          (rho r * p r -
            monomialRatio (sourceProductExponent next weight back) rho r * q r) =
        rho i * e i) :
    ∀ i, rho i = 1 := by
  let _ : NeZero l := ⟨by omega⟩
  obtain ⟨xf, yw, hxf, hyw⟩ := S.exists_actual_fork_column_responses
    weight p q e rho (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r))
      he hrho hw
  let seam : Fin l := ⟨0, by omega⟩
  exact S.ratios_eq_one_of_backFirst_weak_gap hl hprevnext
    weight p q e rho xf yw hp hq he hrho hw hunit hbase hratio hxf hyw seam

end SourceCyclicNonemptyGapSystem

end TypeIIL
