import proofs.TypeIIL.SourceCyclicPartition

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

theorem sum_eq_two_of_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (f : α → ℝ)
    (hzero : ∀ x, x ≠ a → x ≠ b → f x = 0) :
    (∑ x, f x) = f a + f b := by
  let support : Finset α := {a, b}
  calc
    ∑ x, f x = ∑ x ∈ support, f x := by
      symm
      apply Finset.sum_subset (by simp [support])
      intro x _ hx
      apply hzero x
      · intro h
        apply hx
        simp [support, h]
      · intro h
        apply hx
        simp [support, h]
    _ = f a + f b := by simp [support, hab]

theorem sum_eq_three_of_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : α → ℝ)
    (hzero : ∀ x, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    (∑ x, f x) = f a + f b + f c := by
  let support : Finset α := {a, b, c}
  calc
    ∑ x, f x = ∑ x ∈ support, f x := by
      symm
      apply Finset.sum_subset (by simp [support])
      intro x _ hx
      apply hzero x
      · intro h
        apply hx
        simp [support, h]
      · intro h
        apply hx
        simp [support, h]
      · intro h
        apply hx
        simp [support, h]
    _ = f a + f b + f c := by
      simp [support, hab, hac, hbc]
      ring

/-- A literal fork row has no coefficient in a nonadjacent fork column.  This
is the first locality half of the fork-only Schur assembly. -/
theorem fork_row_other_fork_entry_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j b : Fin l) (hbj : b ≠ j) (hbnext : b ≠ S.step j)
    (hbprev : b ≠ S.step.symm j) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (S.fork j) (S.fork b) = 0 := by
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
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back hr hz]
  rw [ite_eq_right hrk, hstoFork, hstoNext, hstoBack]
  ring

/-- A literal fork row has no coefficient in a gap column outside its
preceding and following gaps. -/
theorem fork_row_other_gap_entry_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j a : Fin l) (i : Fin (S.gapLength a + 1))
    (haj : a ≠ j) (hapred : a ≠ S.step.symm j) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e
          (S.fork j) ((S.gap a).idx i) = 0 := by
  let pred := S.step.symm j
  let z := (S.gap pred).idx (Fin.last (S.gapLength pred))
  have hr : back (S.fork j) = some z := by
    simpa [pred, z] using S.back_fork j
  have hz : z ≠ next (S.fork j) := by
    simpa [pred, z] using (S.wrap j).post.back_ne_next
  have hstep : S.step a ≠ j := by
    intro h
    apply hapred
    apply S.step.injective
    simpa [pred] using h
  have hstoFork :
      sourceStoich next weight back (S.fork j) ((S.gap a).idx i) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (S.gap_point_ne_fork j a i).symm
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact (S.gap_point_ne_fork j a u).symm
      · rw [hu]
        exact S.fork.injective.ne hstep.symm
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hstoNext :
      sourceStoich next weight back (next (S.fork j)) ((S.gap a).idx i) = 0 := by
    rw [← (S.wrap j).post.first_eq]
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact S.gap_point_ne_other_gap haj.symm 0 i
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact S.gap_point_ne_other_gap haj.symm 0 u
      · rw [hu]
        exact S.gap_point_ne_fork (S.step a) j 0
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hstoBack : sourceStoich next weight back z ((S.gap a).idx i) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact S.gap_point_ne_other_gap hapred.symm
        (Fin.last (S.gapLength pred)) i
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact S.gap_point_ne_other_gap hapred.symm
          (Fin.last (S.gapLength pred)) u
      · rw [hu]
        exact S.gap_point_ne_fork (S.step a) pred
          (Fin.last (S.gapLength pred))
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hrk : S.fork j ≠ (S.gap a).idx i :=
    (S.gap_point_ne_fork j a i).symm
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back hr hz]
  rw [ite_eq_right hrk, hstoFork, hstoNext, hstoBack]
  ring

/-- Under the paper's distinct predecessor/successor condition, the full
kernel equation at a fork splits into exactly three fork columns and the two
adjacent gap blocks.  No Schur coefficient has yet been abstracted here. -/
theorem fork_kernel_row_split
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∀ j : Fin l,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
            (S.fork j) (S.fork (S.step.symm j)) * x (S.fork (S.step.symm j)) +
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
            (S.fork j) (S.fork j) * x (S.fork j) +
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
            (S.fork j) (S.fork (S.step j)) * x (S.fork (S.step j)) +
      (∑ i,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
              (S.fork j) ((S.gap (S.step.symm j)).idx i) *
                x ((S.gap (S.step.symm j)).idx i)) +
      (∑ i,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
              (S.fork j) ((S.gap j).idx i) * x ((S.gap j).idx i)) = 0 := by
  intro j
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  have hjnext : j ≠ S.step j := by
    intro h
    exact (S.wrap j).left_ne_right (congrArg S.fork h)
  have hprevj : S.step.symm j ≠ j := by
    intro h
    have := congrArg S.step h
    exact hjnext (by simpa using this)
  have hFork :
      (∑ b, M (S.fork j) (S.fork b) * x (S.fork b)) =
        M (S.fork j) (S.fork (S.step.symm j)) * x (S.fork (S.step.symm j)) +
        M (S.fork j) (S.fork j) * x (S.fork j) +
        M (S.fork j) (S.fork (S.step j)) * x (S.fork (S.step j)) := by
    apply sum_eq_three_of_zero (S.step.symm j) j (S.step j)
      hprevj (hprevnext j) hjnext
    intro b hbprev hbj hbnext
    have hzero := S.fork_row_other_fork_entry_zero
      weight p q e rho j b hbj hbnext hbprev
    change M (S.fork j) (S.fork b) = 0 at hzero
    rw [hzero]
    ring
  have hGap :
      (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) * x ((S.gap a).idx i)) =
        (∑ i, M (S.fork j) ((S.gap (S.step.symm j)).idx i) *
          x ((S.gap (S.step.symm j)).idx i)) +
        (∑ i, M (S.fork j) ((S.gap j).idx i) * x ((S.gap j).idx i)) := by
    apply sum_eq_two_of_zero (S.step.symm j) j hprevj
    intro a hapred haj
    apply Finset.sum_eq_zero
    intro i _
    have hzero := S.fork_row_other_gap_entry_zero
      weight p q e rho j a i haj hapred
    change M (S.fork j) ((S.gap a).idx i) = 0 at hzero
    rw [hzero]
    ring
  have hfull := hker (S.fork j)
  change (∑ k, M (S.fork j) k * x k) = 0 at hfull
  rw [S.sum_eq_fork_sum_add_gap_sum
    (fun k => M (S.fork j) k * x k), hFork, hGap] at hfull
  simpa only [M, add_assoc] using hfull

/-- Substituting the literal two-port reconstructions into a full fork kernel
row gives the exact fork-only Schur equation.  This performs global
elimination without introducing a matrix inverse. -/
theorem fork_kernel_row_eq_reduced_gap_system
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0)
    (hrec : ∀ a i, x ((S.gap a).idx i) =
      -(yw a i * x (S.fork a) +
        xf a i * x (S.fork (S.step a))))
    (j : Fin l) :
    (∑ b,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e (S.fork j) (S.fork b) *
        x (S.fork b)) +
      ∑ a, ∑ i,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
              (S.fork j) ((S.gap a).idx i) *
          (-(yw a i * x (S.fork a) +
            xf a i * x (S.fork (S.step a)))) = 0 := by
  classical
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  have hsplit := S.sum_eq_fork_sum_add_gap_sum
    (fun k => M (S.fork j) k * x k)
  have hj := hker (S.fork j)
  change (∑ k, M (S.fork j) k * x k) = 0 at hj
  rw [hsplit] at hj
  simp_rw [hrec] at hj
  change (∑ b, M (S.fork j) (S.fork b) * x (S.fork b)) +
      ∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
        (-(yw a i * x (S.fork a) +
          xf a i * x (S.fork (S.step a)))) = 0
  exact hj

/-- After substituting the two adjacent gap responses, a literal fork kernel
row is exactly a three-term cyclic equation.  The three displayed
coefficients are the genuine Schur predecessor, diagonal, and successor
entries. -/
theorem fork_kernel_row_reduced_three_term
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hprevnext : ∀ j : Fin l, S.step.symm j ≠ S.step j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0)
    (hrec : ∀ a i, x ((S.gap a).idx i) =
      -(yw a i * x (S.fork a) +
        xf a i * x (S.fork (S.step a))))
    (j : Fin l) :
    let M := currentSecantKernelMatrixWith
      (orderedMonomialSecantMatrix
        (sourceProductExponent next weight back) rho)
      (sourceStoich next weight back) p q e
    let pred := S.step.symm j
    let predecessorCoeff :=
      M (S.fork j) (S.fork pred) -
        ∑ i, M (S.fork j) ((S.gap pred).idx i) * yw pred i
    let diagonalCoeff :=
      M (S.fork j) (S.fork j) -
        ∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i -
        ∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i
    let successorCoeff :=
      M (S.fork j) (S.fork (S.step j)) -
        ∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i
    predecessorCoeff * x (S.fork pred) +
      diagonalCoeff * x (S.fork j) +
      successorCoeff * x (S.fork (S.step j)) = 0 := by
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let pred := S.step.symm j
  have hrow := S.fork_kernel_row_split hprevnext weight p q e rho x hker j
  change M (S.fork j) (S.fork pred) * x (S.fork pred) +
      M (S.fork j) (S.fork j) * x (S.fork j) +
      M (S.fork j) (S.fork (S.step j)) * x (S.fork (S.step j)) +
      (∑ i, M (S.fork j) ((S.gap pred).idx i) *
        x ((S.gap pred).idx i)) +
      (∑ i, M (S.fork j) ((S.gap j).idx i) *
        x ((S.gap j).idx i)) = 0 at hrow
  simp_rw [hrec] at hrow
  simp only [mul_neg, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib] at hrow
  rw [S.step.apply_symm_apply j] at hrow
  have hpredY :
      (∑ i, M (S.fork j) ((S.gap pred).idx i) * yw pred i) *
          x (S.fork pred) =
        ∑ i, M (S.fork j) ((S.gap pred).idx i) *
          (yw pred i * x (S.fork pred)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpredX :
      (∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i) *
          x (S.fork j) =
        ∑ i, M (S.fork j) ((S.gap pred).idx i) *
          (xf pred i * x (S.fork j)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hjY :
      (∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i) *
          x (S.fork j) =
        ∑ i, M (S.fork j) ((S.gap j).idx i) *
          (yw j i * x (S.fork j)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hjX :
      (∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i) *
          x (S.fork (S.step j)) =
        ∑ i, M (S.fork j) ((S.gap j).idx i) *
          (xf j i * x (S.fork (S.step j))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only
  change (M (S.fork j) (S.fork pred) -
        ∑ i, M (S.fork j) ((S.gap pred).idx i) * yw pred i) *
        x (S.fork pred) +
      (M (S.fork j) (S.fork j) -
        ∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i -
        ∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i) *
        x (S.fork j) +
      (M (S.fork j) (S.fork (S.step j)) -
        ∑ i, M (S.fork j) ((S.gap j).idx i) * xf j i) *
        x (S.fork (S.step j)) = 0
  ring_nf
  rw [hpredY, hpredX, hjY, hjX]
  ring_nf at hrow ⊢
  exact hrow

end SourceCyclicNonemptyGapSystem

end TypeIIL
