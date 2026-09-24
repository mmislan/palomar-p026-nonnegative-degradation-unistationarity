import proofs.TypeIIL.SourceGapAdapter

namespace TypeIIL

open scoped BigOperators

/-- A nonempty literal gap immediately preceding a fork.  The terminal gap
reaction feeds the fork, while the fork successor starts the next gap and is
therefore outside this embedding. -/
structure SourcePreForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (fork : Fin n) where
  terminal_next : next (G.idx (Fin.last m)) = fork
  fork_back : back fork = some (G.idx (Fin.last m))
  fork_successor_outside : ∀ i, next fork ≠ G.idx i
  fork_ne_next : fork ≠ next fork

namespace SourcePreForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m} {fork : Fin n}

theorem fork_ne_idx (P : SourcePreForkGap G fork) (i : Fin (m + 1)) :
    fork ≠ G.idx i := by
  intro h
  have hs : next (G.idx (Fin.last m)) = G.idx i := by
    simpa [h] using P.terminal_next
  rcases (G.successor_support (Fin.last m) i).mp hs with ⟨hlt, _⟩
  simp at hlt

theorem terminal_ne_fork_successor (P : SourcePreForkGap G fork) :
    G.idx (Fin.last m) ≠ next fork := by
  exact (P.fork_successor_outside (Fin.last m)).symm

theorem terminal_ne_fork (P : SourcePreForkGap G fork) :
    G.idx (Fin.last m) ≠ fork := by
  rw [← P.terminal_next]
  exact G.idx_ne_next (Fin.last m)

/-- Exact sparse action of a fork row on the preceding gap.  Source
minimality enters only through the terminal unit weight. -/
theorem fork_preGap_entry
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (j : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e fork (G.idx j) =
      if j = finitePathPrev (Fin.last m) (by simpa using hm) then
        (q fork *
          (sourceForkBackCoeff next weight back rho fork
            (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))) *
          weight (G.idx j)
      else if j = Fin.last m then
        -(p fork / e fork + q fork *
          (sourceForkBackCoeff next weight back rho fork
            (G.idx (Fin.last m)) / e (G.idx (Fin.last m))))
      else 0 := by
  let last : Fin (m + 1) := Fin.last m
  let prev : Fin (m + 1) := finitePathPrev last (by simpa [last] using hm)
  let z : Fin n := G.idx last
  have hznext : z ≠ next fork := by
    simpa [z, last] using P.terminal_ne_fork_successor
  have hzf : z ≠ fork := by
    simpa [z, last] using P.terminal_ne_fork
  have hforkz : back fork = some z := by simpa [z, last] using P.fork_back
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back hforkz hznext]
  by_cases hjlast : j = last
  · subst j
    have hprevlast : last ≠ prev := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [last, prev, finitePathPrev] at hv
      omega
    have hNfork : sourceStoich next weight back fork z = weight z := by
      have h := sourceStoich_successor_entry next weight back
        (k := z) (by simpa [z, last, P.terminal_next] using
          (G.idx_ne_next last).symm) (by
            intro x hx
            have hn := G.nonfork last
            rw [hn] at hx
            contradiction)
      simpa [z, last, P.terminal_next] using h
    have hNnext : sourceStoich next weight back (next fork) z = 0 := by
      apply sourceStoich_eq_zero_of_off_support next weight back
      · exact (P.fork_successor_outside last)
      · intro h
        apply P.fork_ne_next
        calc
          fork = next z := P.terminal_next.symm
          _ = next fork := h.symm
      · intro x hx
        have hn := G.nonfork last
        rw [hn] at hx
        contradiction
    have hNz : sourceStoich next weight back z z = -1 := by
      exact sourceStoich_source_entry next weight back (G.idx_ne_next last)
        (by
          intro x hx
          have hn := G.nonfork last
          rw [hn] at hx
          contradiction)
    rw [ite_eq_right (P.fork_ne_idx last), hNfork, hNnext, hNz]
    rw [ite_eq_right hprevlast, ite_eq_left rfl]
    rw [show weight z = 1 by simpa [z, last] using hunit]
    ring
  · by_cases hjprev : j = prev
    · subst j
      have hprevlast : prev ≠ last := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [last, prev, finitePathPrev] at hv
        omega
      have hstep : next (G.idx prev) = z := by
        simpa [z, last, prev] using G.idx_prev_step last (by simpa [last] using hm)
      have hNfork : sourceStoich next weight back fork (G.idx prev) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_ne_idx prev
        · simpa [hstep] using hzf.symm
        · intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction
      have hNnext :
          sourceStoich next weight back (next fork) (G.idx prev) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_successor_outside prev
        · simpa [hstep] using hznext.symm
        · intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction
      have hNz : sourceStoich next weight back z (G.idx prev) =
          weight (G.idx prev) := by
        have hnextne : next (G.idx prev) ≠ G.idx prev := by
          rw [hstep]
          exact (G.idx_prev_ne last (by simpa [last] using hm)).symm
        have hs := sourceStoich_successor_entry next weight back hnextne (by
          intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction)
        simpa [hstep] using hs
      rw [ite_eq_right (P.fork_ne_idx prev), hNfork, hNnext, hNz]
      rw [ite_eq_left rfl]
      ring
    · have hjz : G.idx j ≠ z := by
        intro h
        apply hjlast
        exact G.idx.injective (by simpa [z, last] using h)
      have hnextj_ne_fork : next (G.idx j) ≠ fork := by
        intro h
        have hsame : next (G.idx j) = next z := h.trans P.terminal_next.symm
        have := next.injective hsame
        exact hjz this
      have hnextj_ne_z : next (G.idx j) ≠ z := by
        intro h
        rcases (G.predecessor_support last j).mp (by simpa [z, last] using h)
          with ⟨hlast, hj⟩
        apply hjprev
        simpa [prev, last] using hj
      have hNfork : sourceStoich next weight back fork (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_ne_idx j
        · exact hnextj_ne_fork.symm
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      have hNnext : sourceStoich next weight back (next fork) (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_successor_outside j
        · intro h
          apply P.fork_ne_idx j
          exact next.injective h
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      have hNz : sourceStoich next weight back z (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact hjz.symm
        · exact hnextj_ne_z.symm
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      rw [ite_eq_right (P.fork_ne_idx j), hNfork, hNnext, hNz]
      simp [last, prev, hjlast, hjprev]

/-- Summed form of `fork_preGap_entry`: the preceding-gap contribution to a
fork row is exactly the terminal mixed Green functional. -/
theorem fork_preGap_mul
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (y : Fin (m + 1) → ℝ) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j =
      (q fork *
        (sourceForkBackCoeff next weight back rho fork
          (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))) *
          weight (G.idx (finitePathPrev (Fin.last m) (by simpa using hm))) *
            y (finitePathPrev (Fin.last m) (by simpa using hm)) -
        (p fork / e fork + q fork *
          (sourceForkBackCoeff next weight back rho fork
            (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))) *
          y (Fin.last m) := by
  simp_rw [P.fork_preGap_entry hm weight p q e rho hunit]
  have hne : finitePathPrev (Fin.last m) (by simpa using hm) ≠ Fin.last m := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [finitePathPrev] at hv
    omega
  let prev : Fin (m + 1) := finitePathPrev (Fin.last m) (by simpa using hm)
  let last : Fin (m + 1) := Fin.last m
  let A : Fin (m + 1) → ℝ := fun x =>
    (q fork *
      (sourceForkBackCoeff next weight back rho fork
        (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))) *
      weight (G.idx x) * y x
  let B : Fin (m + 1) → ℝ := fun x =>
    -(p fork / e fork + q fork *
      (sourceForkBackCoeff next weight back rho fork
        (G.idx (Fin.last m)) / e (G.idx (Fin.last m)))) * y x
  simp_rw [ite_mul, zero_mul]
  have hlp : last ≠ prev := by simpa [prev, last] using hne.symm
  have hsplit : ∀ x : Fin (m + 1),
      (if x = prev then A x else if x = last then B x else 0) =
        (if x = prev then A x else 0) + (if x = last then B x else 0) := by
    intro x
    by_cases hx : x = prev
    · subst x
      have hpl : prev ≠ last := by simpa [prev, last] using hne
      simp [hpl]
    · by_cases hxl : x = last <;> simp [hx, hxl, hlp]
  change (∑ x, if x = prev then A x else if x = last then B x else 0) = _
  calc
    (∑ x, if x = prev then A x else if x = last then B x else 0) =
        ∑ x, ((if x = prev then A x else 0) +
          (if x = last then B x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hsplit x
    _ = (∑ x, if x = prev then A x else 0) +
          ∑ x, if x = last then B x else 0 := Finset.sum_add_distrib
    _ = A prev + B last := by simp
    _ = _ := by
      dsimp [A, B, prev, last]
      ring

/-- The exact preceding-gap fork correction is nonpositive whenever the
source terminal transport inequality holds.  This is the literal docking of
the sparse fork row to the arbitrary-length Green theorem. -/
theorem fork_preGap_correction_nonpos
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (y b : Fin (m + 1) → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i)
    (htransport :
      let last : Fin (m + 1) := Fin.last m
      let prev : Fin (m + 1) := finitePathPrev last (by exact hm)
      let h := q fork *
        (sourceForkBackCoeff next weight back rho fork (G.idx last) /
          e (G.idx last))
      let g := p fork / e fork
      h * G.gapS weight prev *
          (1 + G.gapA p e last +
            G.gapC weight q e rho last * G.gapS weight last) ≤
        (g + h) *
          (G.gapA p e last * G.gapS weight prev)) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  rw [P.fork_preGap_mul hm weight p q e rho hunit y]
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  let last : Fin (m + 1) := Fin.last m
  let prev : Fin (m + 1) := finitePathPrev last (by simpa [last] using hm)
  let h := q fork *
    (sourceForkBackCoeff next weight back rho fork (G.idx last) /
      e (G.idx last))
  let g := p fork / e fork
  have hh : 0 ≤ h := by
    dsimp [h]
    exact mul_nonneg (hq fork) (div_nonneg
      (le_of_lt (sourceForkBackCoeff_pos next weight back hrho fork (G.idx last)))
      (le_of_lt (he (G.idx last))))
  have ht : 0 ≤ G.gapS weight prev := le_of_lt (G.gapS_pos hw prev)
  have hAlast : 0 < G.gapA p e last := by
    exact div_pos (hp (G.idx last)) (he (G.idx last))
  have hgreen := finiteSourcePath_terminal_mixed_boundary_nonpos hm
    (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
    (G.gapC_nonneg hq he hrho hw) (G.gapS_pos hw) hAlast hb hsolve
    hh ht (by simpa [last, prev, h, g] using htransport)
  simpa [last, prev, h, g, SourceGapEmbedding.gapS] using hgreen

/-- Away from the coordinate-order wrap, the ordered back coefficient is
one and the source current ledger supplies exactly the terminal transport
inequality required by `fork_preGap_correction_nonpos`. -/
theorem fork_preGap_nonwrap_transport
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (horder : (G.idx (Fin.last m)).val < (next fork).val)
    (hpFork : p fork = q fork + JFork)
    (hpLast : p (G.idx (Fin.last m)) =
      q (G.idx (Fin.last m)) + e fork + JFork)
    (hw : ∀ r, 0 < weight r)
    (heBack : 0 < e (G.idx (Fin.last m))) (heFork : 0 < e fork)
    (hqLast : 0 < q (G.idx (Fin.last m))) (hqFork : 0 < q fork)
    (hJFork : 0 < JFork) :
    let last : Fin (m + 1) := Fin.last m
    let prev : Fin (m + 1) := finitePathPrev last (by exact hm)
    let h := q fork *
      (sourceForkBackCoeff next weight back rho fork (G.idx last) /
        e (G.idx last))
    let g := p fork / e fork
    h * G.gapS weight prev *
        (1 + G.gapA p e last +
          G.gapC weight q e rho last * G.gapS weight last) ≤
      (g + h) * (G.gapA p e last * G.gapS weight prev) := by
  have hback : sourceForkBackCoeff next weight back rho fork
      (G.idx (Fin.last m)) = 1 :=
    sourceForkBackCoeff_eq_one_of_back_lt_next next weight back rho
      P.fork_back horder
  have hsource := source_terminal_transport
    (eBack := e (G.idx (Fin.last m))) (eFork := e fork)
    (qLast := q (G.idx (Fin.last m))) (qFork := q fork)
    (JFork := JFork)
    (s := G.gapS weight
      (finitePathPrev (Fin.last m) (by simpa using hm)))
    heBack heFork hqLast hqFork hJFork
    (le_of_lt (G.gapS_pos hw _))
  dsimp only
  rw [hback, hpFork]
  simp only [one_div]
  unfold SourceGapEmbedding.gapA SourceGapEmbedding.gapC
    SourceGapEmbedding.gapS
  rw [P.terminal_next, hunit, hpLast]
  simp [TypeII3.secantPoly] at hsource ⊢
  unfold SourceGapEmbedding.gapS at hsource
  convert hsource using 1
  all_goals ring_nf

/-- For every non-wrap gap immediately preceding a fork, the source current
ledger and the finite-path Green estimate force the complete fork-row Schur
correction on a nonnegative forcing column to be nonpositive. -/
theorem fork_preGap_nonwrap_correction_nonpos
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (horder : (G.idx (Fin.last m)).val < (next fork).val)
    (hpFork : p fork = q fork + JFork)
    (hpLast : p (G.idx (Fin.last m)) =
      q (G.idx (Fin.last m)) + e fork + JFork)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 ≤ q r)
    (hqLast : 0 < q (G.idx (Fin.last m))) (hqFork : 0 < q fork)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hJFork : 0 < JFork)
    (y b : Fin (m + 1) → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  apply P.fork_preGap_correction_nonpos hm weight p q e rho hunit
    hp hq he hrho hw y b hb hsolve
  exact P.fork_preGap_nonwrap_transport hm weight p q e rho JFork
    hunit horder hpFork hpLast hw (he _) (he _) hqLast hqFork hJFork

/-- When the preceding gap consists of only its terminal reaction, the two
supports in the fork row coalesce into a single strictly negative entry.
This case is separate from the mixed terminal functional, whose penultimate
coordinate exists only when `0 < m`. -/
theorem fork_singletonGap_entry
    {G : SourceGapEmbedding next back 0}
    (P : SourcePreForkGap G fork)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e fork (G.idx 0) =
      -(p fork / e fork + q fork *
        (sourceForkBackCoeff next weight back rho fork (G.idx 0) /
          e (G.idx 0))) := by
  have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
  have hterm : next (G.idx 0) = fork := by
    simpa [hlast] using P.terminal_next
  have hback : back fork = some (G.idx 0) := by
    simpa [hlast] using P.fork_back
  have hznext : G.idx 0 ≠ next fork := P.terminal_ne_fork_successor
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back hback
    hznext]
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

theorem fork_singletonGap_correction_nonpos
    {G : SourceGapEmbedding next back 0}
    (P : SourcePreForkGap G fork)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1)
    (hp : 0 ≤ p fork) (hq : 0 ≤ q fork)
    (heFork : 0 < e fork) (heGap : 0 < e (G.idx 0))
    (hrho : ∀ r, 0 < rho r) (y : Fin 1 → ℝ) (hy : 0 ≤ y 0) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  have hcoeff : 0 ≤ p fork / e fork + q fork *
      (sourceForkBackCoeff next weight back rho fork (G.idx 0) /
        e (G.idx 0)) := by
    exact add_nonneg (div_nonneg hp (le_of_lt heFork))
      (mul_nonneg hq (div_nonneg
        (le_of_lt (sourceForkBackCoeff_pos next weight back hrho fork (G.idx 0)))
        (le_of_lt heGap)))
  rw [Fin.sum_univ_one]
  rw [P.fork_singletonGap_entry weight p q e rho hunit]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff) hy

end SourcePreForkGap

/-- A nonempty literal gap immediately following a fork.  Its first reaction
is the fork successor; the fork and its back target lie outside the gap and
are not successors of reactions in the gap. -/
structure SourcePostForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (fork z : Fin n) where
  first_eq : G.idx 0 = next fork
  fork_back : back fork = some z
  fork_outside : ∀ i, fork ≠ G.idx i
  fork_not_successor : ∀ i, fork ≠ next (G.idx i)
  back_outside : ∀ i, z ≠ G.idx i
  back_not_successor : ∀ i, z ≠ next (G.idx i)

namespace SourcePostForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m} {fork z : Fin n}

theorem back_ne_next (P : SourcePostForkGap G fork z) : z ≠ next fork := by
  simpa [← P.first_eq] using P.back_outside (0 : Fin (m + 1))

/-- The fork row restricted to its following gap has exactly one entry: a
negative coefficient in the first gap coordinate. -/
theorem fork_postGap_entry
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e fork (G.idx j) =
      if j = 0 then
        -(q fork *
          (sourceForkNextCoeff next weight back rho fork / e (next fork)))
      else 0 := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back P.fork_back
    P.back_ne_next]
  have hNfork : sourceStoich next weight back fork (G.idx j) = 0 := by
    exact sourceStoich_eq_zero_of_off_support next weight back
      (P.fork_outside j) (P.fork_not_successor j)
      (by intro x hx; simp [G.nonfork j] at hx)
  have hNz : sourceStoich next weight back z (G.idx j) = 0 := by
    exact sourceStoich_eq_zero_of_off_support next weight back
      (P.back_outside j) (P.back_not_successor j)
      (by intro x hx; simp [G.nonfork j] at hx)
  have hNnext : sourceStoich next weight back (next fork) (G.idx j) =
      if j = 0 then -1 else 0 := by
    by_cases hj : j = 0
    · subst j
      rw [← P.first_eq]
      rw [sourceStoich_source_entry next weight back (G.idx_ne_next 0)
        (by intro x hx; simp [G.nonfork 0] at hx)]
      simp
    · rw [ite_eq_right hj]
      apply sourceStoich_eq_zero_of_off_support next weight back
      · intro h
        apply hj
        exact G.idx.injective (by simpa [P.first_eq] using h.symm)
      · intro h
        have hs : next (G.idx j) = G.idx 0 := by
          simpa [P.first_eq] using h.symm
        rcases (G.predecessor_support 0 j).mp hs with ⟨hzero, _⟩
        simp at hzero
      · intro x hx
        simp [G.nonfork j] at hx
  rw [ite_eq_right (P.fork_outside j), hNfork, hNnext, hNz]
  by_cases hj : j = 0 <;> simp [hj]

/-- Summed form of `fork_postGap_entry`. -/
theorem fork_postGap_mul
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (y : Fin (m + 1) → ℝ) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j =
      -(q fork *
          (sourceForkNextCoeff next weight back rho fork / e (next fork))) *
        y 0 := by
  simp_rw [P.fork_postGap_entry weight p q e rho]
  simp

/-- Hence the following-gap correction is nonpositive on every nonnegative
Green response. -/
theorem fork_postGap_correction_nonpos
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hq : 0 ≤ q fork) (he : 0 < e (next fork))
    (hrho : ∀ r, 0 < rho r) (hw : ∀ r, 0 < weight r)
    (y : Fin (m + 1) → ℝ) (hy : 0 ≤ y 0) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  rw [P.fork_postGap_mul weight p q e rho y]
  have hcoeff : 0 ≤ q fork *
      (sourceForkNextCoeff next weight back rho fork / e (next fork)) :=
    mul_nonneg hq (div_nonneg
      (le_of_lt (sourceForkNextCoeff_pos next weight back hrho hw fork))
      (le_of_lt he))
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff) hy

/-- The M-matrix certificate for the literal gap supplies the nonnegativity
premise in `fork_postGap_correction_nonpos` for every nonnegative forcing. -/
theorem fork_postGap_green_correction_nonpos
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (y b : Fin (m + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    ∑ j,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  have hy := zmatrix_solution_nonneg
    (finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
      (G.gapS weight))
    (finiteSourcePathWeight (G.gapS weight)) y b
    (finiteSourcePathMatrix_offdiag_nonpos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg hq he hrho hw)
      (fun i => le_of_lt (G.gapS_pos hw i)))
    (finiteSourcePathWeight_pos (G.gapS_pos hw))
    (finiteSourcePathMatrix_mul_weight_pos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg hq he hrho hw) (G.gapS_pos hw))
    hb hsolve
  exact P.fork_postGap_correction_nonpos weight p q e rho (hq fork)
    (he (next fork)) hrho hw y (hy 0)

end SourcePostForkGap

/-- A singleton gap with its adjacent left and right forks and the left
fork's (external) back target.  The last two fields are the only additional
off-support facts needed for the two direct fork-to-fork entries. -/
structure SourceSingletonForkGap
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back 0)
    (left right leftBack : Fin n) where
  pre : SourcePreForkGap G right
  post : SourcePostForkGap G left leftBack
  right_successor_ne_left : next right ≠ left
  right_successor_ne_leftBack : next right ≠ leftBack

namespace SourceSingletonForkGap

variable {n : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back 0}
  {left right leftBack : Fin n}

/-- The singleton internal block is the scalar `d = 1 + A + c`. -/
theorem internal_diagonal
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1) :
    G.restrictedCurrentMatrix weight p q e rho 0 0 =
      1 + p (G.idx 0) / e (G.idx 0) + q (G.idx 0) / e right := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
  unfold finiteSourcePathMatrix SourceGapEmbedding.gapA
    SourceGapEmbedding.gapC SourceGapEmbedding.gapS
  have hterm : next (G.idx 0) = right := by
    simpa using P.pre.terminal_next
  rw [hterm]
  simp [hunit, TypeII3.secantPoly]
  ring

/-- The left-fork column enters the singleton block through its weighted
successor coefficient. -/
theorem internal_left_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx 0) left =
      -(p (G.idx 0) / e (G.idx 0) * weight left) := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork 0)]
  have hnextLeft : next left = G.idx 0 := P.post.first_eq.symm
  have hNself : sourceStoich next weight back (G.idx 0) left =
      weight left := by
    rw [← hnextLeft]
    apply sourceStoich_successor_entry next weight back
    · simpa [hnextLeft] using (P.post.fork_outside 0).symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      simpa [hnextLeft, hx] using (P.post.back_outside 0).symm
  have hNnext : sourceStoich next weight back (next (G.idx 0)) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (P.post.fork_not_successor 0).symm
    · simpa [hnextLeft] using (G.idx_ne_next 0).symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      simpa [hx] using (P.post.back_not_successor 0).symm
  rw [ite_eq_right (P.post.fork_outside 0).symm, hNself, hNnext]
  ring

/-- The right-fork column is `-(A+c)`; the `+1` back product and the
terminal unit successor are both used here. -/
theorem internal_right_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx 0) = 1) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx 0) right =
      -(p (G.idx 0) / e (G.idx 0) + q (G.idx 0) / e right) := by
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork 0)]
  have hNz : sourceStoich next weight back (G.idx 0) right = 1 := by
    exact sourceStoich_back_entry next weight back P.pre.fork_back
      P.pre.terminal_ne_fork P.pre.terminal_ne_fork_successor
  have hNr : sourceStoich next weight back right right = -1 := by
    exact sourceStoich_source_entry next weight back P.pre.fork_ne_next
      (by
        intro x hx
        have htx : G.idx (Fin.last 0) = x := by
          exact Option.some.inj (P.pre.fork_back.symm.trans hx)
        intro hrx
        exact P.pre.terminal_ne_fork (htx.trans hrx.symm))
  have hne : G.idx 0 ≠ right := by simpa using P.pre.terminal_ne_fork
  have hterm : next (G.idx 0) = right := by simpa using P.pre.terminal_next
  rw [ite_eq_right hne, hNz, hterm, hNr, hunit]
  simp [TypeII3.secantPoly]
  ring

/-- Direct forward fork edge across the singleton gap. -/
theorem left_right_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e left right =
      q left *
        (sourceForkNextCoeff next weight back rho left / e (G.idx 0)) := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back
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
  have hNz : sourceStoich next weight back (G.idx 0) right = 1 :=
    sourceStoich_back_entry next weight back P.pre.fork_back
      P.pre.terminal_ne_fork P.pre.terminal_ne_fork_successor
  have hNback : sourceStoich next weight back leftBack right = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · simpa [hterm] using P.post.back_not_successor 0
    · exact P.right_successor_ne_leftBack.symm
    · intro x hx
      rw [P.pre.fork_back] at hx
      injection hx with hx
      subst x
      exact P.post.back_outside 0
  rw [ite_eq_right hLR, hNleft, P.post.first_eq.symm, hNz, hNback]
  ring

/-- Direct predecessor edge into the right fork. -/
theorem right_left_entry
    (P : SourceSingletonForkGap G left right leftBack)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e right left =
      q right *
        (sourceForkBackCoeff next weight back rho right (G.idx 0) /
          e (G.idx 0)) * weight left := by
  rw [sourceOrderedCurrentMatrix_fork_entry next weight back
    P.pre.fork_back P.pre.terminal_ne_fork_successor]
  have hterm : next (G.idx 0) = right := by simpa using P.pre.terminal_next
  have hnextLeft : next left = G.idx 0 := P.post.first_eq.symm
  have hLR : left ≠ right := by
    simpa [hterm] using P.post.fork_not_successor 0
  have hNright : sourceStoich next weight back right left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back hLR.symm
    · simpa [hnextLeft] using P.pre.terminal_ne_fork.symm
    · intro x hx
      rw [P.post.fork_back] at hx
      injection hx with hx
      subst x
      simpa [hterm] using (P.post.back_not_successor 0).symm
  have hNnext : sourceStoich next weight back (next right) left = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
      P.right_successor_ne_left
      (by simpa [hnextLeft] using P.pre.terminal_ne_fork_successor.symm)
    intro x hx
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
      subst x
      simpa [hnextLeft] using (P.post.back_outside 0).symm
  rw [ite_eq_right hLR.symm, hNright, hNnext]
  rw [show G.idx (Fin.last 0) = G.idx 0 by rfl, hNz]
  ring

end SourceSingletonForkGap

/-- Scalar Schur elimination of the singleton block gives the adjacent
forward coefficient exactly. -/
theorem singleton_schur_forward_eq
    {A c k d : ℝ} (hd : d = 1 + A + c) (hd0 : d ≠ 0) :
    k - (-k) * (-(A + c) / d) = k / d := by
  field_simp
  rw [hd]
  ring

/-- The same scalar elimination gives the exceptional predecessor
coefficient; this is the term whose independent upper bound is false. -/
theorem singleton_schur_wrap_eq
    {A c g h s d : ℝ} (hd : d = 1 + A + c) (hd0 : d ≠ 0) :
    h * s - (-(g + h)) * (-(A * s) / d) =
      s * (h * (1 + c) - g * A) / d := by
  field_simp
  rw [hd]
  ring

/-- The part of the left-fork diagonal supplied by the singleton gap after
elimination is the lower bound used for the preceding Schur diagonal. -/
theorem singleton_schur_left_diagonal_core_eq
    {A c k s d : ℝ} (hd : d = 1 + A + c) (hd0 : d ≠ 0) :
    1 + k * s - (-k) * (-(A * s) / d) =
      (d + k * s * (1 + c)) / d := by
  field_simp
  rw [hd]
  ring

/-- The right-fork diagonal core left after eliminating the singleton gap. -/
theorem singleton_schur_right_diagonal_core_eq
    {A c g h d : ℝ} (hd : d = 1 + A + c) (hd0 : d ≠ 0) :
    1 + g + h - (-(g + h)) * (-(A + c) / d) =
      (d + g + h) / d := by
  field_simp
  rw [hd]
  ring

/-- Exact positive numerator behind the singleton exceptional-wrap Schur
minor.  The potentially huge wrap term is cancelled jointly by the two
adjacent diagonal/forward contributions; no separate upper bound on it is
needed. -/
theorem singleton_wrap_core_margin_pos
    {A c g h k s d : ℝ}
    (hd : d = 1 + A + c)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hs : 0 < s) :
    0 < (d + g + h) * (d + k * s * (1 + c)) -
      s * (h * (1 + c) - g * A) * k := by
  have hdpos : 0 < d := by nlinarith
  have hinside : 0 < d + g + h + k * s * (1 + c) + k * s * g := by
    have hksc : 0 ≤ k * s * (1 + c) := by positivity
    have hksg : 0 ≤ k * s * g := by positivity
    nlinarith
  have hid :
      (d + g + h) * (d + k * s * (1 + c)) -
          s * (h * (1 + c) - g * A) * k =
        d * (d + g + h + k * s * (1 + c) + k * s * g) := by
    rw [hd]
    ring
  rw [hid]
  exact mul_pos hdpos hinside

/-- Endpoint lower bounds convert the singleton core identity into precisely
the raw two-edge inequality consumed by `CyclicClosureBound`. -/
theorem singleton_wrap_raw_two_edge_margin
    {A c g h k s d X Bprev Fprev W : ℝ}
    (hd : d = 1 + A + c)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hs : 0 < s)
    (hX : (d + g + h) / d ≤ X)
    (hBprev : (d + k * s * (1 + c)) / d ≤ Bprev)
    (hFprev : Fprev = k / d)
    (hW : W = s * (h * (1 + c) - g * A) / d) :
    W * Fprev < X * Bprev := by
  have hdpos : 0 < d := by nlinarith
  have hd2pos : 0 < d * d := mul_pos hdpos hdpos
  have hx0 : 0 < (d + g + h) / d := by
    exact div_pos (by nlinarith) hdpos
  have hb0 : 0 < (d + k * s * (1 + c)) / d := by
    have hksc : 0 ≤ k * s * (1 + c) := by positivity
    exact div_pos (by nlinarith) hdpos
  have hcore := singleton_wrap_core_margin_pos hd hA hc hg hh hk hs
  have hstrict :
      W * Fprev <
        ((d + g + h) / d) * ((d + k * s * (1 + c)) / d) := by
    calc
      W * Fprev =
          (s * (h * (1 + c) - g * A) * k) / (d * d) := by
            rw [hW, hFprev]
            ring
      _ < ((d + g + h) * (d + k * s * (1 + c))) / (d * d) := by
            apply (div_lt_div_iff_of_pos_right hd2pos).2
            linarith
      _ = ((d + g + h) / d) *
          ((d + k * s * (1 + c)) / d) := by ring
  calc
    W * Fprev <
        ((d + g + h) / d) * ((d + k * s * (1 + c)) / d) := hstrict
    _ ≤ X * ((d + k * s * (1 + c)) / d) :=
      mul_le_mul_of_nonneg_right hX (le_of_lt hb0)
    _ ≤ X * Bprev := by
      exact mul_le_mul_of_nonneg_left hBprev
        (le_trans (le_of_lt hx0) hX)

end TypeIIL
