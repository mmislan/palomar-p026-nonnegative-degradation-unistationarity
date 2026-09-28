module

public import proofs.TypeIIL.SourceBackFirstCone

@[expose] public section

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- A back-first fork row has no coefficient in a nonadjacent fork column.
The proof is support-theoretic: the adaptive secant has only the back and
successor species ports, exactly as the rowwise product identity predicts. -/
theorem backFirst_fork_row_other_fork_entry_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j b : Fin l) (hbj : b ≠ j) (hbnext : b ≠ S.step j)
    (hbprev : b ≠ S.step.symm j) :
    S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork b) = 0 := by
  let pred := S.step.symm j
  let z := (S.gap pred).idx (Fin.last (S.gapLength pred))
  have hr : back (S.fork j) = some z := by
    simpa [pred, z] using S.back_fork j
  have hz : z ≠ next (S.fork j) := by
    simpa [pred, z] using (S.wrap j).post.back_ne_next
  have hrk : S.fork j ≠ S.fork b := S.fork.injective.ne hbj.symm
  have hzk : z ≠ S.fork b := by
    exact S.gap_point_ne_fork b pred (Fin.last (S.gapLength pred))
  have hstoFork : sourceStoich next weight back (S.fork j) (S.fork b) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hrk
    · rw [← (S.wrap b).post.first_eq]
      exact (S.gap_point_ne_fork j b 0).symm
    · intro z' hz'
      rw [S.back_fork b] at hz'
      injection hz' with hzz'
      subst z'
      exact (S.gap_point_ne_fork j (S.step.symm b)
        (Fin.last (S.gapLength (S.step.symm b)))).symm
  have hstoNext :
      sourceStoich next weight back (next (S.fork j)) (S.fork b) = 0 := by
    rw [← (S.wrap j).post.first_eq]
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact S.gap_point_ne_fork b j 0
    · rw [← (S.wrap b).post.first_eq]
      exact S.gap_point_ne_other_gap hbj.symm 0 0
    · intro z' hz'
      rw [S.back_fork b] at hz'
      injection hz' with hzz'
      subst z'
      have hpredb : S.step.symm b ≠ j := by
        intro h
        apply hbnext
        calc
          b = S.step (S.step.symm b) := (S.step.apply_symm_apply b).symm
          _ = S.step j := congrArg S.step h
      exact S.gap_point_ne_other_gap hpredb.symm 0
        (Fin.last (S.gapLength (S.step.symm b)))
  have hstoBack : sourceStoich next weight back z (S.fork b) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact hzk
    · rw [← (S.wrap b).post.first_eq]
      exact S.gap_point_ne_other_gap hbprev.symm
        (Fin.last (S.gapLength pred)) 0
    · intro z' hz'
      rw [S.back_fork b] at hz'
      injection hz' with hzz'
      subst z'
      have hpred : pred ≠ S.step.symm b := by
        intro h
        have hjb : j = b := by
          simpa [pred] using S.step.symm.injective h
        exact hbj hjb.symm
      exact S.gap_point_ne_other_gap hpred
        (Fin.last (S.gapLength pred))
        (Fin.last (S.gapLength (S.step.symm b)))
  unfold backFirstCurrentMatrix
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back hr hz]
  rw [ite_eq_right hrk, hstoFork, hstoNext, hstoBack]
  ring_nf

/-- The full back-first kernel row at a fork consists of three fork columns
and its two adjacent passive gap blocks. -/
theorem backFirst_fork_kernel_row_split
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    ∀ j : Fin l,
      S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) (S.fork (S.step.symm j)) *
            x (S.fork (S.step.symm j)) +
      S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) (S.fork j) * x (S.fork j) +
      S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) (S.fork (S.step j)) * x (S.fork (S.step j)) +
      (∑ i, S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) ((S.gap (S.step.symm j)).idx i) *
            x ((S.gap (S.step.symm j)).idx i)) +
      (∑ i, S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) ((S.gap j).idx i) * x ((S.gap j).idx i)) = 0 := by
  intro j
  let M := S.backFirstCurrentMatrix weight p q e rho
  have hjnext : j ≠ S.step j := by
    intro h
    exact (S.wrap j).left_ne_right (congrArg S.fork h)
  have hprevj : S.step.symm j ≠ j := by
    intro h
    have hs := congrArg S.step h
    exact hjnext (by simpa using hs)
  have hFork :
      (∑ b, M (S.fork j) (S.fork b) * x (S.fork b)) =
        M (S.fork j) (S.fork (S.step.symm j)) * x (S.fork (S.step.symm j)) +
        M (S.fork j) (S.fork j) * x (S.fork j) +
        M (S.fork j) (S.fork (S.step j)) * x (S.fork (S.step j)) := by
    apply sum_eq_three_of_zero (S.step.symm j) j (S.step j)
      hprevj (hprevnext j) hjnext
    intro b hbprev hbj hbnext
    have hzero := S.backFirst_fork_row_other_fork_entry_zero
      weight p q e rho j b hbj hbnext hbprev
    change M (S.fork j) (S.fork b) = 0 at hzero
    rw [hzero]
    ring
  have hGap :
      (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          x ((S.gap a).idx i)) =
        (∑ i, M (S.fork j) ((S.gap (S.step.symm j)).idx i) *
          x ((S.gap (S.step.symm j)).idx i)) +
        (∑ i, M (S.fork j) ((S.gap j).idx i) *
          x ((S.gap j).idx i)) := by
    apply sum_eq_two_of_zero (S.step.symm j) j hprevj
    intro a hapred haj
    apply Finset.sum_eq_zero
    intro i _
    have hzero := S.backFirst_fork_row_other_gap_entry_zero
      weight p q e rho j a i haj hapred
    change M (S.fork j) ((S.gap a).idx i) = 0 at hzero
    rw [hzero]
    ring
  have hfull := hker (S.fork j)
  change (∑ k, M (S.fork j) k * x k) = 0 at hfull
  rw [S.sum_eq_fork_sum_add_gap_sum
    (fun k => M (S.fork j) k * x k), hFork, hGap] at hfull
  simpa only [M, add_assoc] using hfull

/-- Across a nonempty following gap there is no direct fork-to-successor-fork
entry in the back-first gauge. -/
theorem backFirst_fork_next_direct_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j) :
    S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork (S.step j)) = 0 := by
  let P := S.wrap j
  let G := S.gap j
  have hLR : S.fork j ≠ S.fork (S.step j) := P.left_ne_right
  have hNleft :
      sourceStoich next weight back (S.fork j) (S.fork (S.step j)) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hLR
      P.right_successor_ne_left.symm
    intro z hz
    rw [P.pre.fork_back] at hz
    injection hz with hz
    subst z
    exact P.post.fork_outside (Fin.last (S.gapLength j))
  have hNfirst :
      sourceStoich next weight back ((S.gap j).idx 0)
        (S.fork (S.step j)) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      (P.pre.fork_ne_idx 0).symm (P.pre.fork_successor_outside 0).symm
    intro z hz
    rw [P.pre.fork_back] at hz
    injection hz with hz
    subst z
    exact SourceWrapForkGap.first_ne_terminal (S.gap j) hm
  have hNback : sourceStoich next weight back
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j))))
      (S.fork (S.step j)) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_ne_leftBack.symm P.right_successor_ne_leftBack.symm
    intro z hz
    rw [P.pre.fork_back] at hz
    injection hz with hz
    subst z
    exact P.post.back_outside (Fin.last (S.gapLength j))
  unfold backFirstCurrentMatrix
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back
    P.post.fork_back P.post.back_ne_next]
  rw [ite_eq_right hLR, hNleft, P.post.first_eq.symm, hNfirst, hNback]
  ring

/-- Across a nonempty preceding gap there is no direct fork-to-predecessor-
fork entry in the back-first gauge. -/
theorem backFirst_fork_prev_direct_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength (S.step.symm j)) :
    S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) (S.fork (S.step.symm j)) = 0 := by
  let pred := S.step.symm j
  let P := S.wrap pred
  have hstep : S.step pred = j := by simp [pred]
  have hRL : S.fork j ≠ S.fork pred := by
    rw [← hstep]
    exact P.left_ne_right.symm
  have hNright : sourceStoich next weight back (S.fork j) (S.fork pred) = 0 := by
    rw [← hstep]
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.left_ne_right.symm
      (by simpa [P.post.first_eq] using (P.pre.fork_ne_idx 0))
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact P.right_ne_leftBack
  have hNnext : sourceStoich next weight back (next (S.fork j))
      (S.fork pred) = 0 := by
    rw [← hstep]
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_successor_ne_left
      (by simpa [P.post.first_eq] using P.pre.fork_successor_outside 0)
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact P.right_successor_ne_leftBack
  have hNlast : sourceStoich next weight back
      ((S.gap pred).idx (Fin.last (S.gapLength pred))) (S.fork pred) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      (P.post.fork_outside (Fin.last (S.gapLength pred))).symm
      (by
        rw [← P.post.first_eq]
        exact (SourceWrapForkGap.first_ne_terminal (S.gap pred) hm).symm)
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact (P.post.back_outside (Fin.last (S.gapLength pred))).symm
  unfold backFirstCurrentMatrix
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back
    (by simpa [pred] using S.back_fork j)
    (by simpa [pred] using (S.wrap j).post.back_ne_next)]
  rw [ite_eq_right hRL, hNright, hNlast, hNnext]
  ring

/-- Eliminating the two passive adjacent gaps turns every back-first fork
kernel row into the uniform cyclic three-port equation `P·prev+B·self+F·next`.
There is no exceptional row. -/
theorem backFirst_fork_three_term_of_reconstruction
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hgap : ∀ a, 0 < S.gapLength a)
    (hrec : ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))))
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    ∀ j : Fin l,
      S.backFirstForkPrevCoefficient weight p q e rho yw j *
          x (S.fork (S.step.symm j)) +
        S.backFirstForkSelfCoefficient weight p q e rho xf yw j *
          x (S.fork j) +
        S.backFirstForkNextCoefficient weight p q e rho xf j *
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
  have hprevZero := S.backFirst_fork_prev_direct_zero
    weight p q e rho j (hgap pred)
  have hnextZero := S.backFirst_fork_next_direct_zero
    weight p q e rho j (hgap j)
  rw [hprevZero, hnextZero] at hsplit
  unfold backFirstForkPrevCoefficient backFirstForkSelfCoefficient
    backFirstForkNextCoefficient
  dsimp only [pred]
  linear_combination hsplit

/-- The abstract reduced fork matrix is exactly the same three-port generator
on every vector.  This is the docking identity between global Schur
elimination and the local coefficients. -/
theorem backFirstReducedForkMatrix_mulVec_eq_three_term
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hgap : ∀ a, 0 < S.gapLength a)
    (v : Fin l → ℝ) (j : Fin l) :
    ∑ b, S.backFirstReducedForkMatrix weight p q e rho xf yw j b * v b =
      S.backFirstForkPrevCoefficient weight p q e rho yw j *
          v (S.step.symm j) +
        S.backFirstForkSelfCoefficient weight p q e rho xf yw j * v j +
        S.backFirstForkNextCoefficient weight p q e rho xf j *
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
    have hzero := S.backFirst_fork_row_other_fork_entry_zero
      weight p q e rho j b hbj hbnext hbprev
    change M (S.fork j) (S.fork b) = 0 at hzero
    rw [hzero]
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
      have hzero := S.backFirst_fork_row_other_gap_entry_zero
        weight p q e rho j a i haj hapred
      change M (S.fork j) ((S.gap a).idx i) = 0 at hzero
      rw [hzero]
      ring
    have hsum := sum_eq_two_of_zero pred j hprevj f hf
    change (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
        (yw a i * v a + xf a i * v (S.step a))) = _ at hsum
    dsimp only [f] at hsum
    rw [show S.step pred = j by simp [pred]] at hsum
    exact hsum
  have hprevZero := S.backFirst_fork_prev_direct_zero
    weight p q e rho j (hgap pred)
  have hnextZero := S.backFirst_fork_next_direct_zero
    weight p q e rho j (hgap j)
  unfold backFirstReducedForkMatrix
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  change (∑ b, M (S.fork j) (S.fork b) * v b) - _ = _
  rw [htriple, hFork, hGap]
  change M (S.fork j) (S.fork pred) = 0 at hprevZero
  change M (S.fork j) (S.fork (S.step j)) = 0 at hnextZero
  rw [hprevZero, hnextZero]
  unfold backFirstForkPrevCoefficient backFirstForkSelfCoefficient
    backFirstForkNextCoefficient
  dsimp only [pred, M]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [sub_mul, Finset.sum_mul]
  ring_nf

/-! The reduced three-port generator is now normalized row by row.  Unlike the
ambient ordered gauge, the back-first gauge has no exceptional coefficient:
every predecessor port is nonpositive and every successor port lies strictly
below the positive diagonal. -/

noncomputable def backFirstForkSectorAlpha
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  -S.backFirstForkPrevCoefficient weight p q e rho yw j /
    S.backFirstForkSelfCoefficient weight p q e rho xf yw j

noncomputable def backFirstForkSectorGamma
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) : ℝ :=
  S.backFirstForkNextCoefficient weight p q e rho xf j /
    S.backFirstForkSelfCoefficient weight p q e rho xf yw j

noncomputable def backFirstForkSectorMatrix
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ) :
    Matrix (Fin l) (Fin l) ℝ :=
  cyclicSectorMatrix S.step
    (S.backFirstForkSectorAlpha weight p q e rho xf yw)
    (S.backFirstForkSectorGamma weight p q e rho xf yw)

theorem backFirstForkSectorAlpha_nonneg
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hprev : S.backFirstForkPrevCoefficient weight p q e rho yw j ≤ 0)
    (hself : 0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw j) :
    0 ≤ S.backFirstForkSectorAlpha weight p q e rho xf yw j := by
  unfold backFirstForkSectorAlpha
  exact div_nonneg (neg_nonneg.mpr hprev) (le_of_lt hself)

theorem backFirstForkSectorGamma_pos_lt_one
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l)
    (hnext : 0 < S.backFirstForkNextCoefficient weight p q e rho xf j)
    (hmargin : 1 ≤
      S.backFirstForkSelfCoefficient weight p q e rho xf yw j -
        S.backFirstForkNextCoefficient weight p q e rho xf j) :
    0 < S.backFirstForkSectorGamma weight p q e rho xf yw j ∧
      S.backFirstForkSectorGamma weight p q e rho xf yw j < 1 := by
  have hself : 0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw j := by
    linarith
  have hnextSelf : S.backFirstForkNextCoefficient weight p q e rho xf j <
      S.backFirstForkSelfCoefficient weight p q e rho xf yw j := by
    linarith
  unfold backFirstForkSectorGamma
  exact ⟨div_pos hnext hself, (div_lt_one hself).2 hnextSelf⟩

/-- A strict three-port residual on a positive comparison vector is exactly
the upper-face inequality needed by the cyclic determinant box. -/
theorem backFirstForkSectorAlpha_lt_upper
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (J : Fin l → ℝ) (j : Fin l)
    (hself : 0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw j)
    (hJprev : 0 < J (S.step.symm j))
    (hresidual : 0 <
      S.backFirstForkPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j) +
        S.backFirstForkSelfCoefficient weight p q e rho xf yw j * J j +
        S.backFirstForkNextCoefficient weight p q e rho xf j * J (S.step j)) :
    S.backFirstForkSectorAlpha weight p q e rho xf yw j <
      cyclicSectorUpper S.step
        (S.backFirstForkSectorGamma weight p q e rho xf yw) J j := by
  unfold backFirstForkSectorAlpha backFirstForkSectorGamma cyclicSectorUpper
  apply (lt_div_iff₀ hJprev).2
  calc
    (-S.backFirstForkPrevCoefficient weight p q e rho yw j /
          S.backFirstForkSelfCoefficient weight p q e rho xf yw j) *
        J (S.step.symm j) =
        (-S.backFirstForkPrevCoefficient weight p q e rho yw j *
          J (S.step.symm j)) /
            S.backFirstForkSelfCoefficient weight p q e rho xf yw j := by ring
    _ < J j +
        (S.backFirstForkNextCoefficient weight p q e rho xf j /
          S.backFirstForkSelfCoefficient weight p q e rho xf yw j) *
            J (S.step j) := by
      apply (div_lt_iff₀ hself).2
      have hcancel :
          (J j +
              (S.backFirstForkNextCoefficient weight p q e rho xf j /
                S.backFirstForkSelfCoefficient weight p q e rho xf yw j) *
                  J (S.step j)) *
              S.backFirstForkSelfCoefficient weight p q e rho xf yw j =
            S.backFirstForkSelfCoefficient weight p q e rho xf yw j * J j +
              S.backFirstForkNextCoefficient weight p q e rho xf j *
                J (S.step j) := by
        field_simp [ne_of_gt hself]
      rw [hcancel]
      nlinarith

/-- The back-first reduced fork operator has positive determinant.  The signed
seam theorem is used only as a determinant engine: because the adaptive gauge
makes every predecessor coefficient nonnegative after normalization, any row
may be nominated as the seam and its local inequality is automatic. -/
theorem backFirstForkSectorMatrix_det_pos [NeZero l]
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
    (hgap : ∀ a, 0 < S.gapLength a)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (seam : Fin l) :
    0 < (S.backFirstForkSectorMatrix weight p q e rho xf yw).det := by
  let J : Fin l → ℝ := fun a => p (S.fork a) - q (S.fork a)
  have hJ : ∀ a, 0 < J a := by
    intro a
    exact S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit a
  have hnext : ∀ a,
      0 < S.backFirstForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstForkNextCoefficient_pos weight p q e rho xf a (hgap a)
      hp hq he hrho hw (hunit a) (hxf a)
  have hmargin : ∀ a, 1 ≤
      S.backFirstForkSelfCoefficient weight p q e rho xf yw a -
        S.backFirstForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstForkSelf_sub_next_ge_one weight p q e rho xf yw hbase
      hp hq he hrho hw hunit hgap hxf hyw a
  have hself : ∀ a,
      0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw a := by
    intro a
    linarith [hnext a, hmargin a]
  have hprev : ∀ a,
      S.backFirstForkPrevCoefficient weight p q e rho yw a ≤ 0 := by
    intro a
    exact S.backFirstForkPrevCoefficient_nonpos weight p q e rho yw hbase
      hp hq he hrho hw hunit hgap hyw a
  have hresidual : ∀ a, 0 <
      S.backFirstForkPrevCoefficient weight p q e rho yw a *
          J (S.step.symm a) +
        S.backFirstForkSelfCoefficient weight p q e rho xf yw a * J a +
        S.backFirstForkNextCoefficient weight p q e rho xf a * J (S.step a) := by
    intro a
    have hred := S.backFirstReducedForkMatrix_mul_baseCurrent_pos
      weight p q e rho xf yw hxf hyw hbase hp hq he hrho hw hunit hgap a
    have hthree := S.backFirstReducedForkMatrix_mulVec_eq_three_term
      hprevnext weight p q e rho xf yw hgap J a
    rw [hthree] at hred
    exact hred
  have hgamma : ∀ a,
      0 < S.backFirstForkSectorGamma weight p q e rho xf yw a ∧
        S.backFirstForkSectorGamma weight p q e rho xf yw a < 1 := by
    intro a
    exact S.backFirstForkSectorGamma_pos_lt_one weight p q e rho xf yw a
      (hnext a) (hmargin a)
  have halpha : ∀ a,
      0 ≤ S.backFirstForkSectorAlpha weight p q e rho xf yw a := by
    intro a
    exact S.backFirstForkSectorAlpha_nonneg weight p q e rho xf yw a
      (hprev a) (hself a)
  have halphaUpper : ∀ a,
      S.backFirstForkSectorAlpha weight p q e rho xf yw a <
        cyclicSectorUpper S.step
          (S.backFirstForkSectorGamma weight p q e rho xf yw) J a := by
    intro a
    exact S.backFirstForkSectorAlpha_lt_upper weight p q e rho xf yw J a
      (hself a) (hJ (S.step.symm a)) (hresidual a)
  have hlocal :
      (-S.backFirstForkSectorAlpha weight p q e rho xf yw seam) *
          S.backFirstForkSectorGamma weight p q e rho xf yw
            (S.cyclicIndexFrom seam (l - 1)) <
        1 - S.backFirstForkSectorGamma weight p q e rho xf yw seam := by
    rw [S.cyclicIndexFrom_pred_length (by omega)]
    have hleft :
        (-S.backFirstForkSectorAlpha weight p q e rho xf yw seam) *
            S.backFirstForkSectorGamma weight p q e rho xf yw
              (S.step.symm seam) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (halpha seam))
        (le_of_lt (hgamma (S.step.symm seam)).1)
    have hright :
        0 < 1 - S.backFirstForkSectorGamma weight p q e rho xf yw seam := by
      linarith [(hgamma seam).2]
    linarith
  simpa [backFirstForkSectorMatrix] using
    S.cyclicSectorMatrix_signed_seam_pos hl
      (S.backFirstForkSectorAlpha weight p q e rho xf yw)
      (S.backFirstForkSectorGamma weight p q e rho xf yw) J seam
      hgamma hJ (fun a _ => halpha a) halphaUpper hlocal

/-- Gap reconstruction is gauge invariant.  Back-first and ordered secants
coincide on every nonfork row, so the same positive path inverse reconstructs
all internal coordinates from their two boundary fork values. -/
theorem backFirst_internal_coordinates_eq_negative_responses_of_kernel
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    ∀ (a : Fin l) (i : Fin (S.gapLength a + 1)),
      x ((S.gap a).idx i) =
        -(yw a i * x (S.fork a) + xf a i * x (S.fork (S.step a))) := by
  intro a
  let G := S.gap a
  let P := S.wrap a
  apply P.internal_coordinates_eq_negative_responses (hgap a)
    weight p q e rho hp hq he hrho hw (hunit a) x (xf a) (yw a)
      (hxf a) (hyw a)
  intro i
  let MO := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let MB := S.backFirstCurrentMatrix weight p q e rho
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
  change (∑ j, MO (G.idx i) (G.idx j) * x (G.idx j)) +
      MO (G.idx i) (S.fork a) * x (S.fork a) +
      MO (G.idx i) (S.fork (S.step a)) * x (S.fork (S.step a)) = 0
  rw [← hsum]
  calc
    ∑ k, MO (G.idx i) k * x k =
        ∑ k, MB (G.idx i) k * x k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hrowEq k]
    _ = 0 := hk

/-- Nonsingularity of the reduced back-first three-port operator lifts through
the passive gaps and kills the full current-secant kernel. -/
theorem backFirstGlobalCurrentSecantKernel_eq_zero_of_sector_det [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
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
      0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw a)
    (hdet : 0 <
      (S.backFirstForkSectorMatrix weight p q e rho xf yw).det)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      S.backFirstCurrentMatrix weight p q e rho r k * x k = 0) :
    x = 0 := by
  have hrec := S.backFirst_internal_coordinates_eq_negative_responses_of_kernel
    weight p q e rho hp hq he hrho hw hunit hgap x xf yw hxf hyw hker
  have hraw := S.backFirst_fork_three_term_of_reconstruction hprevnext
    weight p q e rho x xf yw hgap hrec hker
  let z : Fin l → ℝ := fun a => x (S.fork a)
  have hsector : Matrix.mulVec
      (S.backFirstForkSectorMatrix weight p q e rho xf yw) z = 0 := by
    funext a
    change Matrix.mulVec
      (cyclicSectorMatrix S.step
        (S.backFirstForkSectorAlpha weight p q e rho xf yw)
        (S.backFirstForkSectorGamma weight p q e rho xf yw)) z a = 0
    rw [cyclicSectorMatrix_mulVec_apply]
    unfold backFirstForkSectorAlpha backFirstForkSectorGamma
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

/-- Analytic source theorem for the strict-gap branch.  Two positive stationary
states generate an exact back-first current-kernel vector; the determinant and
Green-lift theorems force that vector to vanish, hence every concentration
ratio is one. -/
theorem ratios_eq_one_of_backFirst_strict_gap [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hgap : ∀ a, 0 < S.gapLength a)
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
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (seam : Fin l) :
    ∀ i, rho i = 1 := by
  have hdet : 0 <
      (S.backFirstForkSectorMatrix weight p q e rho xf yw).det :=
    S.backFirstForkSectorMatrix_det_pos hl hprevnext weight p q e rho xf yw
      hbase hp hq he hrho hw hunit hgap hxf hyw seam
  have hnext : ∀ a,
      0 < S.backFirstForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstForkNextCoefficient_pos weight p q e rho xf a (hgap a)
      hp hq he hrho hw (hunit a) (hxf a)
  have hmargin : ∀ a, 1 ≤
      S.backFirstForkSelfCoefficient weight p q e rho xf yw a -
        S.backFirstForkNextCoefficient weight p q e rho xf a := by
    intro a
    exact S.backFirstForkSelf_sub_next_ge_one weight p q e rho xf yw hbase
      hp hq he hrho hw hunit hgap hxf hyw a
  have hself : ∀ a,
      0 < S.backFirstForkSelfCoefficient weight p q e rho xf yw a := by
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
    S.backFirstGlobalCurrentSecantKernel_eq_zero_of_sector_det hprevnext
      weight p q e rho (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r))
      he hrho hw hunit hgap xf yw hxf hyw hself hdet x hker
  apply ratios_eq_one_of_twoRootCurrentDelta_eq_zero
    (sourceProductExponent next weight back) (sourceStoich next weight back)
    (fun i => ne_of_gt (he i)) hbase hratio
  intro r
  exact congrFun hx r

/-- Witness-free strict-gap theorem.  The two response columns are generated
by invertibility of each positive path block, so the statement exposes only
the stationary equations and the source-faithful cyclic structure. -/
theorem ratios_eq_one_of_backFirst_strict_gap_generated
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hgap : ∀ a, 0 < S.gapLength a)
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
  have hxfExists : ∀ a : Fin l,
      ∃ x : Fin (S.gapLength a + 1) → ℝ, ∀ i,
        ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * x t =
          sourceWrapForwardForcing ((S.gap a).gapA p e)
            ((S.gap a).gapC weight q e rho) i := by
    intro a
    exact (S.gap a).restricted_response_exists weight p q e rho
      (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
      (sourceWrapForwardForcing ((S.gap a).gapA p e)
        ((S.gap a).gapC weight q e rho))
  choose xf hxf using hxfExists
  have hywExists : ∀ a : Fin l,
      ∃ y : Fin (S.gapLength a + 1) → ℝ, ∀ i,
        ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * y t =
          sourceWrapLeftForcing ((S.gap a).gapA p e)
            (weight (S.fork a)) i := by
    intro a
    exact (S.gap a).restricted_response_exists weight p q e rho
      (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
      (sourceWrapLeftForcing ((S.gap a).gapA p e) (weight (S.fork a)))
  choose yw hyw using hywExists
  let seam : Fin l := ⟨0, by omega⟩
  exact S.ratios_eq_one_of_backFirst_strict_gap hl hprevnext
    weight p q e rho xf yw hgap hp hq he hrho hw hunit hbase hratio
      hxf hyw seam

end SourceCyclicNonemptyGapSystem

end TypeIIL
