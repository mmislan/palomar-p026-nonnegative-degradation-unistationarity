module

public import proofs.TypeIIL.SourceWrapCondensation

@[expose] public section

namespace TypeIIL

/-- A literal nonempty source gap together with its adjacent left and right
forks.  The extra inequalities are precisely the off-support facts needed to
compute the two direct fork-to-fork entries. -/
structure SourceWrapForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (left right leftBack : Fin n) where
  pre : SourcePreForkGap G right
  post : SourcePostForkGap G left leftBack
  right_successor_ne_left : next right ≠ left
  right_successor_ne_leftBack : next right ≠ leftBack
  right_ne_leftBack : right ≠ leftBack

namespace SourceWrapForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m}
  {left right leftBack : Fin n}

theorem first_ne_terminal
    (G : SourceGapEmbedding next back m) (hm : 0 < m) :
    G.idx 0 ≠ G.idx (Fin.last m) := by
  apply G.idx.injective.ne
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

theorem left_ne_right
    (P : SourceWrapForkGap G left right leftBack) : left ≠ right := by
  intro h
  apply P.pre.fork_successor_outside (0 : Fin (m + 1))
  rw [← h]
  exact P.post.first_eq.symm

/-- The left fork column enters the first internal row with the literal
weighted predecessor coefficient. -/
theorem first_left_entry
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx 0) left =
      -(G.gapA p e 0 * weight left) := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork 0)]
  have hnextLeft : next left = G.idx 0 := P.post.first_eq.symm
  have hNself : sourceStoich next weight back (G.idx 0) left =
      weight left := by
    rw [← hnextLeft]
    apply sourceStoich_successor_entry next weight back
    · simpa [hnextLeft] using (P.post.fork_outside 0).symm
    · intro z hz
      rw [P.post.fork_back] at hz
      injection hz with hz
      subst z
      simpa [hnextLeft] using (P.post.back_outside 0).symm
  have hNnext : sourceStoich next weight back (next (G.idx 0)) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.post.fork_not_successor 0).symm
    · simpa [hnextLeft] using (G.idx_ne_next 0).symm
    · intro z hz
      rw [P.post.fork_back] at hz
      injection hz with hz
      subst z
      simpa using (P.post.back_not_successor 0).symm
  rw [ite_eq_right (P.post.fork_outside 0).symm, hNself, hNnext]
  unfold SourceGapEmbedding.gapA
  ring

/-- The terminal internal row sees the right fork through `-(A+c)` when
the source-minimal terminal reaction has unit successor weight. -/
theorem terminal_right_entry
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx (Fin.last m)) right =
      -(G.gapA p e (Fin.last m) +
        G.gapC weight q e rho (Fin.last m)) := by
  let last : Fin (m + 1) := Fin.last m
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork last)]
  have hNz : sourceStoich next weight back (G.idx last) right = 1 := by
    exact sourceStoich_back_entry next weight back P.pre.fork_back
      P.pre.terminal_ne_fork P.pre.terminal_ne_fork_successor
  have hNr : sourceStoich next weight back right right = -1 := by
    exact sourceStoich_source_entry next weight back P.pre.fork_ne_next
      (by
        intro z hz
        rw [P.pre.fork_back] at hz
        injection hz with hz
        subst z
        exact P.pre.terminal_ne_fork.symm)
  have hne : G.idx last ≠ right := P.pre.terminal_ne_fork
  have hterm : next (G.idx last) = right := P.pre.terminal_next
  rw [ite_eq_right hne, hNz, hterm, hNr]
  unfold SourceGapEmbedding.gapA SourceGapEmbedding.gapC
  rw [show weight (G.idx last) = 1 by simpa [last] using hunit]
  simp [TypeII3.secantPoly]
  rw [show next (G.idx (Fin.last m)) = right by exact P.pre.terminal_next]
  ring

/-- The terminal pivot itself is exactly the singleton diagonal `1+A+c`
under the same terminal-unit hypothesis. -/
theorem terminal_diagonal
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1) :
    G.restrictedCurrentMatrix weight p q e rho (Fin.last m) (Fin.last m) =
      1 + G.gapA p e (Fin.last m) +
        G.gapC weight q e rho (Fin.last m) := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
  unfold finiteSourcePathMatrix SourceGapEmbedding.gapS
  have hprev : ∀ h : 0 < (Fin.last m).val,
      Fin.last m ≠ finitePathPrev (Fin.last m) h := by
    intro h heq
    have hv := congrArg Fin.val heq
    dsimp [finitePathPrev] at hv
    omega
  rw [show weight (G.idx (Fin.last m)) = 1 by exact hunit]
  simp [hprev]

/-- Across a nonsingleton gap there is no direct left-to-right fork entry;
the positive forward entry is created only by eliminating the final two path
coordinates. -/
theorem left_right_entry_zero
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e left right = 0 := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back
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
  have hNfirst : sourceStoich next weight back (G.idx 0) right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      (P.pre.fork_ne_idx 0).symm (P.pre.fork_successor_outside 0).symm
    intro z hz
    rw [P.pre.fork_back] at hz
    injection hz with hz
    subst z
    exact first_ne_terminal G hm
  have hNback : sourceStoich next weight back leftBack right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_ne_leftBack.symm P.right_successor_ne_leftBack.symm
    intro z hz
    rw [P.pre.fork_back] at hz
    injection hz with hz
    subst z
    exact P.post.back_outside (Fin.last m)
  rw [ite_eq_right hLR, hNleft, P.post.first_eq.symm, hNfirst, hNback]
  ring

/-- Across a nonsingleton gap there is likewise no direct right-to-left fork
entry; the exceptional predecessor entry is created by the terminal
condensation. -/
theorem right_left_entry_zero
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e right left = 0 := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back
    P.pre.fork_back P.pre.terminal_ne_fork_successor]
  have hRL : right ≠ left := P.left_ne_right.symm
  have hNright : sourceStoich next weight back right left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hRL
      (by simpa [P.post.first_eq] using (P.pre.fork_ne_idx 0))
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact P.right_ne_leftBack
  have hNnext : sourceStoich next weight back (next right) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_successor_ne_left
      (by simpa [P.post.first_eq] using P.pre.fork_successor_outside 0)
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact P.right_successor_ne_leftBack
  have hNlast : sourceStoich next weight back (G.idx (Fin.last m)) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      (P.post.fork_outside (Fin.last m)).symm
      (by
        rw [← P.post.first_eq]
        exact (first_ne_terminal G hm).symm)
    intro z hz
    rw [P.post.fork_back] at hz
    injection hz with hz
    subst z
    exact (P.post.back_outside (Fin.last m)).symm
  rw [ite_eq_right hRL, hNright, hNnext, hNlast]
  ring

end SourceWrapForkGap

end TypeIIL
