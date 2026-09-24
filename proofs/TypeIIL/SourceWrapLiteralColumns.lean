import proofs.TypeIIL.SourceWrapResponseExistence
import proofs.TypeIIL.SourceWrapGapAdapter

namespace TypeIIL

/-- Apart from the first gap row, the literal left-fork column vanishes. -/
theorem SourceWrapForkGap.internal_left_entry_zero_of_pos
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (i : Fin (m + 1)) (hi : 0 < i.val) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx i) left = 0 := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork i)]
  have hself : sourceStoich next weight back (G.idx i) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.post.fork_outside i).symm
    · rw [← P.post.first_eq]
      intro h
      have hii : i = (0 : Fin (m + 1)) := G.idx.injective h
      exact (Nat.ne_of_gt hi) (by simpa using congrArg Fin.val hii)
    · intro z hz
      rw [P.post.fork_back] at hz
      injection hz with hz
      subst z
      exact (P.post.back_outside i).symm
  have hnext : sourceStoich next weight back (next (G.idx i)) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.post.fork_not_successor i).symm
    · intro h
      apply P.post.fork_outside i
      exact next.injective (Eq.symm h)
    · intro z hz
      rw [P.post.fork_back] at hz
      injection hz with hz
      subst z
      exact (P.post.back_not_successor i).symm
  rw [ite_eq_right (P.post.fork_outside i).symm, hself, hnext]
  ring

/-- The literal right-fork column is positive at the penultimate row. -/
theorem SourceWrapForkGap.penultimate_right_entry
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    let penultimate : Fin (m + 1) := ⟨m - 1, by omega⟩
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx penultimate) right =
      G.gapC weight q e rho penultimate := by
  dsimp only
  let penultimate : Fin (m + 1) := ⟨m - 1, by omega⟩
  let terminal : Fin (m + 1) := Fin.last m
  have hpt : penultimate ≠ terminal := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [penultimate, terminal] at hv
    omega
  have hstep : next (G.idx penultimate) = G.idx terminal := by
    let hbound : penultimate.val < m := by dsimp [penultimate]; omega
    have hs := G.idx_step penultimate hbound
    have hfin : finitePathNext penultimate hbound = terminal := by
      apply Fin.ext
      dsimp [finitePathNext, penultimate, terminal]
      omega
    exact hs.trans (congrArg G.idx hfin)
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back
    (G.nonfork penultimate)]
  have hself : sourceStoich next weight back (G.idx penultimate) right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.pre.fork_ne_idx penultimate).symm
    · exact (P.pre.fork_successor_outside penultimate).symm
    · intro z hz
      rw [P.pre.fork_back] at hz
      injection hz with hz
      subst z
      exact G.idx.injective.ne hpt
  have hnext : sourceStoich next weight back
      (next (G.idx penultimate)) right = 1 := by
    rw [hstep]
    exact sourceStoich_back_entry next weight back P.pre.fork_back
      P.pre.terminal_ne_fork P.pre.terminal_ne_fork_successor
  rw [ite_eq_right (P.pre.fork_ne_idx penultimate).symm, hself, hnext]
  unfold SourceGapEmbedding.gapC
  ring

/-- Before the penultimate coordinate, the literal right-fork column
vanishes.  Thus the only two nonzero entries of that column inside a long gap
are the penultimate and terminal entries. -/
theorem SourceWrapForkGap.internal_right_entry_zero_before_penultimate
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (i : Fin (m + 1)) (hi : i.val < m - 1) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx i) right = 0 := by
  have him : i.val < m := by omega
  let terminal : Fin (m + 1) := Fin.last m
  have hit : i ≠ terminal := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [terminal] at hv
    omega
  have hnextTerminal : next (G.idx i) ≠ G.idx terminal := by
    rw [G.idx_step i him]
    apply G.idx.injective.ne
    intro h
    have hv := congrArg Fin.val h
    dsimp [finitePathNext, terminal] at hv
    omega
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork i)]
  have hself : sourceStoich next weight back (G.idx i) right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.pre.fork_ne_idx i).symm
    · exact (P.pre.fork_successor_outside i).symm
    · intro z hz
      rw [P.pre.fork_back] at hz
      injection hz with hz
      subst z
      exact G.idx.injective.ne hit
  have hnext : sourceStoich next weight back (next (G.idx i)) right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · intro h
      have heq : G.idx i = G.idx terminal :=
        next.injective (h.trans P.pre.terminal_next.symm)
      exact hit (G.idx.injective heq)
    · rw [G.idx_step i him]
      exact (P.pre.fork_successor_outside (finitePathNext i him)).symm
    · intro z hz
      rw [P.pre.fork_back] at hz
      injection hz with hz
      subst z
      exact hnextTerminal
  rw [ite_eq_right (P.pre.fork_ne_idx i).symm, hself, hnext]
  ring

/-- The actual left-fork column restricted to the gap is exactly the forcing
used to construct the left Schur response. -/
theorem SourceWrapForkGap.internal_left_column_eq_forcing
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (i : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx i) left =
      sourceWrapLeftForcing (G.gapA p e) (weight left) i := by
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    rw [P.first_left_entry weight p q e rho]
    simp [sourceWrapLeftForcing]
  · have hipos : 0 < i.val := by omega
    rw [P.internal_left_entry_zero_of_pos weight p q e rho i hipos]
    simp [sourceWrapLeftForcing, hi]

/-- Under the terminal-unit consequence of source minimality, the actual
right-fork column restricted to a long gap is exactly the mixed forcing used
to construct the forward Schur response. -/
theorem SourceWrapForkGap.internal_right_column_eq_forcing
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1) (i : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx i) right =
      sourceWrapForwardForcing (G.gapA p e)
        (G.gapC weight q e rho) i := by
  by_cases hpen : i.val = m - 1
  · have hieq : i = ⟨m - 1, by omega⟩ := Fin.ext hpen
    rw [hieq]
    rw [P.penultimate_right_entry (by omega) weight p q e rho]
    simp [sourceWrapForwardForcing]
  · by_cases hterm : i.val = m
    · have hieq : i = Fin.last m := by
        apply Fin.ext
        simpa using hterm
      subst i
      rw [P.terminal_right_entry weight p q e rho hunit]
      have hmm1 : m ≠ m - 1 := by omega
      simp [sourceWrapForwardForcing, hmm1]
    · have hi : i.val < m - 1 := by
        have hil : i.val ≤ m := by omega
        omega
      rw [P.internal_right_entry_zero_before_penultimate weight p q e rho i hi]
      simp [sourceWrapForwardForcing, hpen, hterm]

end TypeIIL
